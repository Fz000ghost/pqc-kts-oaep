// kts_oaep.cpp
// RSA-3072 KTS-OAEP with SHA-256
// Built with Botan 3

// Build: g++ -std=c++20 -O2 -Wall kts_oaep.cpp -o kts $(pkg-config --cflags --libs botan-3)
// Run:    ./kts test [wycheproof.json]     correctness checks -NOT IMPLEMENTED-
//         ./kts bench <N> [keygen_runs]    local timings, writes bench.csv -NOT IMPLEMENTED-
//         ./kts server <port>              party V: owns the RSA key, receives the secret
//         ./kts client <host> <port> <N>   party U: wraps N secrets, writes client.csv

// Botan
#include <botan/auto_rng.h>
#include <botan/bigint.h>
#include <botan/hash.h>
#include <botan/hex.h>
#include <botan/mac.h>
#include <botan/numthry.h>
#include <botan/pubkey.h>  // Botan's OAEP - only used as a reference in test and bench
#include <botan/rsa.h>     // Botan's RSA -  only used as a reference in test and bench

// Networking
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <sys/socket.h>
#include <unistd.h>

// Standard C++
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using Botan::BigInt;
using Bytes = Botan::secure_vector<uint8_t>; // Byte array wiped from memory when freed

constexpr size_t N_BITS = 3072; // 128-bit security 
constexpr size_t N_LEN = N_BITS/8; // 384 bytes
constexpr size_t H_LEN = 32; // SHA-256 output
constexpr size_t MAC_KEY_LEN = 32; // Length of MAC key (first 32 bytes)
constexpr size_t KEY_DATA_LEN = 32; // Length of the secret (next 32 bytes)
constexpr size_t K_LEN = MAC_KEY_LEN + KEY_DATA_LEN; // Length of the keying material K (64 bytes)
constexpr size_t MAC_TAG_LEN = 32; // Full HMAC-SHA-256 output (32 bytes)
constexpr uint32_t MAX_FRAME = 4096; // No message should be larger than 384 bytes
constexpr size_t WARMUP = 5; // First 5 runs are thrown away
const std::string ID_U = "party-U";
const std::string ID_V = "party-V";

// RSA

struct PublicKey {
    BigInt n, e;
};

struct PrivateKey {
    BigInt n, e, d, p, q, dP, dQ, qInv;
    PublicKey pub() const {return {n, e};} // Contains the public part of the key
};

Botan::RandomNumberGenerator& rng(){ // Random number generator
    static Botan::AutoSeeded_RNG r;
    return r;
}

// Generate a vector with all prime numbers up to a limit using the sieve of Eratosthenes
namespace{
    std::vector<uint32_t> eratosthenes(uint32_t limit) {
        std::vector <uint32_t> primes;
        std::vector<bool> composite(limit, false);
        for(uint32_t i = 2; i < limit; ++i) {
            if(!composite[i]) {
                primes.push_back(i);
                for(uint32_t j = i * i; j < limit; j += i)
                    composite[j] = true;
            }
        }
    return primes;
    }
}

// Get all primes below 2000 to throw away prime candidates cheaply before Miller-Rabin test
const std::vector<uint32_t>& get_small_primes() { 
    static const std::vector<uint32_t> primes = eratosthenes(2000);
    return primes;
}

// Check whether if a large number is prime using modular arithmetic 
bool miller_rabin(const BigInt& w, size_t rounds) {
    if(w < 5)
        return w == 2 || w == 3;
    if(w.is_even()) 
        return false;
    BigInt m = w - 1;
    size_t a = 0;
    while(m.is_even()) {
        m >>= 1; // Divides by 2 by shifting bits right
        ++a;
    }
    for(size_t i = 0; i < rounds; ++i) {
        BigInt b = BigInt::random_integer(rng(), 2, w - 1); // Use a random base, 1 < b < w - 1
        BigInt z = Botan::power_mod(b, m, w);
        if(z == 1 || z == w - 1)
            continue; // Probably prime
        bool is_composite = true;
        for(size_t j = 1; j < a; ++j) {
            z = (z * z) % w;
            if(z == w - 1) {
                is_composite = false;
                break;
            }
            if(z == 1)
                break;
        }
        if(is_composite)
            return false; // Not prime
    }
    return true; // Probably prime
}

// Full primality test
bool is_probable_prime(const BigInt& w, size_t rounds) {
    for(uint32_t small_prime : get_small_primes()) { 
        if(w == small_prime) // Check if w is in the small prime list
            return true;
        if(w % small_prime == 0) // Filter odd numbers with a prime factor
            return false;
    }
    return miller_rabin(w, rounds); // Check primality using Miller-Rabin
}

// Generate a 1536-bit prime
BigInt generate_prime(const BigInt& e, const BigInt* other) {
    const size_t prime_length = N_BITS / 2; // Each prime has half the modulus's bits (1536)
    const BigInt lower_sq = BigInt::power_of_2(N_BITS - 1); // Ensures modulus n is exactly 3072 bits
    const BigInt min_gap = BigInt::power_of_2(prime_length - 100); // Ensures p and q are not close
    for(size_t i = 0; i < 5 * prime_length; ++i) { // Try up to 7680 candidates with 2^1536 values
        BigInt p(rng(), prime_length); // Random 1536-bit number
        p.set_bit(0); // Makes the number odd
        if(p * p <= lower_sq)
            continue; // P is too small, so n would be 3071 bits
        if(other != nullptr && (p - *other).abs() <= min_gap) 
            continue; // Primes are to close to each other
        if(Botan::gcd(p-1, e) != 1)
            continue; // e must be invertible mod p - 1
        if(is_probable_prime(p,5))
            return p; // All previous tests passed, check if prime
    }
    throw std::runtime_error("prime generation failed");
}

// Power b^k by square-and-multiply using BigInt
BigInt int_pow(BigInt b, size_t k) {
    BigInt r = BigInt::one();
    while(K > 0) { // Loop until every bit of k is used
        if(k & 1) 
            r *= b; // Multiplies if the lowest bit is 1
        k >>= 1; // Divide k by 2 in binary
        if(k > 0) 
            b *= b; // Squares b
    }
    return r;
}

bool is_perfect_power(const BigInt& n) {
    for(uint32_t k : get_small_primes()) { // Only prime exponents need checking
        if(k > n.bits() / 9) // Skip perfect powers whose base is smaller than ~= 512 since small factors were already ruled out
            break;
        BigInt low = BigInt::one();
        BigInt high = BigInt::power_of_2(n.bits() / k + 1);
        while (high - low > 1) { // Binary search to find the k-th root
            BigInt mid = (low + high) >> 1;
            if (int_pow(mid, k) <= n)
                low = mid;
            else
                high = mid;
        }
        if(int_pow(low, k) == n)
            return true; // True if the found number is the largest number whose k-th power doesn't go over n
    }
    return false;
}

// Least common multiple using BigInt
BigInt bigint_lcm(const BigInt& a, const BigInt& b){
    return a * b / Botan::gcd(a, b);
}

//Hashes a byte string with SHA-256
Bytes sha256(const Bytes& data) {
    auto h = Botan::HashFunction::create_or_throw("SHA-256");
    h->update(data);
    return h->final();
}

// 351-byte mask generation (MGF1) using SHA-256
Bytes MGF1(const Bytes& seed, size_t mask_len) {
    Bytes T;
    for(uint32_t counter = 0; T.size() < mask_len; ++counter) { 
        Bytes input = seed;
        put_u32(input, counter);
        append(T, sha256(input)); // Append the 32 output bytes to T
    }
    T.resize(mask_len); 
    return T;
}

// RSA encryption primitive
BigInt RSAEP(const PublicKey& pub, const BigInt& m) {
    if(!(m > 1 && m < pub.n - 1))
        throw std::runtime_error("m out of range");
    return Botan::power_mod(m, pub.e, pub.n); // c = m^e mod n
}

// RSA decryption primitive m = c^d mod n in CRT form
BigInt RSADP(const PrivateKey& k, const BigInt& c) {
    if(!(c > 1 && c < k.n - 1))
        throw std::runtime_error("c out of range");
    BigInt mp = Botan::power_mod(c, k.dP, k.p); // mp = c^dP mod p
    BigInt mq = Botan::power_mod(c, k.dQ, k.q); // mq = c^dQ mod q
    BigInt h = (k.qInv * (mp + k.p - mq % k.p)) % k.p; // (mp - mq) * qInv mod p (never below zero due to mp + p - (mq mod p))
    return (mq + k.q * h) % k.n; // m = mq + q*h mod n
}

// Key pair generator with fixed public exponent, output in CRT format
PrivateKey rsakpg1_crt() {
    const BigInt e = BigInt::from_u64(65537); // Public exponent e = 65537
    for(;;) { // Loop until the key is finished or an exception is thrown
        PrivateKey k;
        k.e = e;
        k.p = generate_prime(e, nullptr);
        k.q = generate_prime(e, &k.p);
        const BigInt p1 = k.p - 1;
        const BigInt q1 = k.q - 1;
        const BigInt lambda = bigint_lcm(p1, q1);
        k.d = Botan::inverse_mod(e, lambda); // d = e^-1 mod(LCM(p - 1, q - 1))
        if(k.d <= BigInt::power_of_2(N_BITS / 2)) 
            continue; // d > 2^1536 to avoid Wiener's and Boneh-Durfee's attacks
        k.n = k.p * k.q; // Public modulus n = p * q
        k.dP = k.d % p1; // dP = d mod(p - 1)
        k.dQ = k.d % q1; // dQ = d mod (q - 1)
        k.qInv = Botan::inverse_mod(k.q, k.p); // qInv = q^-1 mod p 
        BigInt m = BigInt::random_integer(rng(), 2, k.n - 1);
        if(RSADP(k,RSAEP(k.pub(), m)) != m)
            throw std::runtime_error("pair-wise consistency failure");
        return k;
    }
}

// Key pair validator for rsakpg1_crt according to the rules established by SP 800-56-B
std::string rsakpv1_crt(const PublicKey& pub, const PrivateKey& k) {
    const BigInt e_fixed = BigInt::from_u64(65537);
    if(pub.e != e_fixed || pub.e != k.e) return "public exponents differ";
    if(pub.n != k.p * k.q || pub.n != k.n) return "modulus is not p * q";
    if (pub.n.bits() != N_BITS) return "modulus has the wrong length";
    if((k.p - k.q).abs() <= BigInt::power_of_2(N_BITS / 2 - 100)) return "p and q are too close";
    if(Botan::gcd(k.p - 1, pub.e) !=  1) return "gcd(p - 1, e) != 1";
    if(Botan::gcd(k.q - 1, pub.e) !=  1) return "gcd(q - 1, e) != 1";
    if(!is_probable_prime(k.p, 64)) return "p is not prime";
    if(!is_probable_prime(k.q, 64)) return "q is not prime";
    const BigInt p1 = k.p - 1;
    const BigInt q1 = k.q - 1;
    const BigInt lambda = bigint_lcm(p1, q1);
    if((k.d * pub.e) % lambda != 1) return "d is not the inverse of e";
    if(!(k.dP > 1 && k.dP < p1) || (k.dP * e_fixed) % p1 != 1) return "bad dP";
    if(!(k.dQ > 1 && k.dQ < q1) || (k.dQ * e_fixed) % q1 != 1) return "bad dQ";
    if(!(k.qInv > 1 && k.qInv < k.p) || (k.qInv * k.q) % k.p != 1) return "bad qInv";
    const BigInt lower_sq = BigInt::power_of_2(N_BITS - 1);
    const BigInt upper = BigInt::power_of_2(N_BITS / 2);
    if(k.p * k.p <= lower_sq || k.p >= upper) return "p out of range";
    if(k.q * k.q <= lower_sq || k.q >= upper) return "q out of range";
    if(!(k.d > upper && k.d < lambda)) return "d out of range";
    return "";
}

// Convert an integer (BigInt) to a byte string with the given length
Bytes I2BS(const BigInt& x, size_t len) {
    if(x.bytes() > len)
        throw std::runtime_error("Integer too large for the requested length");
    Bytes out(len); // Create len zero bytes
    x.serialize_to(out); // Write value x into out
    return out;
}

// Convert a byte string into an integer (BigInt)
BigInt BS2I(const Bytes& b) { return BigInt(b.data(), b.size()); } 

// Converts an integer into base 256 with exactly 4 digits (4 big-endian bytes)
void put_u32(Bytes& out, uint32_t v) { 
    for(int shift = 24; shift >= 0; shift -= 8)
        out.push_back(static_cast<uint8_t>(v >> shift));
}

// Concatenate a bytes string onto the end of the first
void append(Bytes& out, const Bytes& b) { out.insert(out.end(), b.begin(), b.end()); } 

 // Concatenate a string (ASCII to bytes) onto the end of a byte string
void append(Bytes& out, const std::string& s) { out.insert(out.end(), s.begin(), s.end()); }

// XOR two equal length byte strings
void xor_into(Bytes& a, const Bytes& b) { 
    for(size_t i = 0; i < a.size(); ++i)
        a[i] ^= b[i]; // Writes the result on the first string
}

// Turns keying materiak K into a 384 byte (3072 bits) block
Bytes RSA_OAEP_ENCRYPT(const PublicKey& pub, const Bytes& K, const Bytes& A) {
    const size_t nLen = (pub.n.bits() + 7) / 8; // Modulus length in bytes (384)
    if(K.size() > nLen - 2 * H_LEN - 2) // K is too long to fit on the keying material (max 318 bytes, since H_LEN is 32)
        throw std::runtime_error("keying material too long");
    Bytes HA = sha256(A); // Hashes A, the identity of both parties
    Bytes DB = HA; // Builds the data block starting with the hash
    DB.insert(DB.end(), nLen - K.size() - 2 * H_LEN - 2, 0x00); // Adds 254 zero bytes of extra padding to DB
    DB.push_back(0x01); // Adds 01 to mark where padding ends and K begins
    append(DB, K); // Adds K to DB
    Bytes mgfSeed(H_LEN); 
    rng().randomize(mgfSeed); // Create a new random 32-byte seed to use as a mask
    Bytes maskedDB = DB;
    xor_into(maskedDB, MGF1(mgfSeed), nLen - H_LEN - 1); // XOR the DB with the seed using MGF1
    Bytes maskedSeed = mgfSeed;
    xor_into(maskedSeed, MGF1(maskedDB, H_LEN)); // XOR the masked seed with the masked database using MGF1
    Bytes EM{0x00};
    append(EM, maskedSeed);
    append(EM, maskedDB); // Encoded message = 00 | maskedSeed | maskedDB = 384 bytes
    BigInt c = RSAEP(pub, BS2I(EM)); // Apply RSAEP to EM (as an integer)
    return I2BS(c, nLen); // Return c as a 384 byte string
}

// Returns 1 if x is zero and 0 if otherwise in constant time
uint8_t ct_is_zero(uint8_t x) { return static_cast<uint8_t>((static_cast<uint32_t>(x) - 1) >> 31); }

// Returns if two byte strings are equal in constant time
bool ct_equal(const uint8_t* a, const uint8_t* b, size_t len) {
    uint8_t diff = 0;
    for(size_t i = 0; i < len; ++i)
        diff |= a[i] ^ b[i];
    return ct_is_zero(diff) == 1;
}

// Decrypt the masked 384 bytes data block to retrieve K
Bytes RSA_OAEP_DECRYPT(const PrivateKey& k, const Bytes& C, const Bytes& A) {
    const size_t nLen = (k.n.bits() + 7) / 8; // Modulus length in bytes (384)
    if(C.size() != nLen) // Cyphertext must be 384 bytes
        throw std::runtime_error("erroneous input");
    BigInt c = BS2I(C);
    if(!(c > 1 && c < k.n - 1)) // 1 < c < n - 1 
        throw std::runtime_error("erroneous input");
    Bytes EM = I2BS(RSADP(k, c), nLen); // Retrieve the encoded message
    Bytes HA = sha256(A) // Hash input A (identity of both parties)
    const uint8_t Y = EM[0]; // Obtain first byte
    Bytes seed(EM.begin() + 1, EM.begin() + 1 + H_LEN); // obtain masked seed
    Bytse DB(EM.begin() + 1 + H_LEN, EM.end()); // Obtain masked data block
    xor_into(seed, MGF1(DB, H_LEN)); // XOR masked seed and MGF1 of the masked data block to obtain the seed
    xor_into(DB, MGF1(seed, nLen - H_LEN - 1)); // XOR seed and MGF1 of the masked data block to obtain the data block
    uint8_t bad = ct_is_zero(Y) ^ 1; // First byte should be zero
    bad |= ct_equal(DB.data(), HA.data(), H_LEN) ? 0 : 1; // First 32 bytes of DB must equal SHA-256(A)
    uint8_t found = 0; // 1 if the 01 before K is found
    size_t sep = 0; // Holds 01's position in DB
    for(size_t i = H_LEN; i < DB.size(); ++i) { // Scan every byte
        const uint8_t is0 = ct_is_zero(DB[i]); // Check if the current byte is 00
        const uint8_t is1 = ct_is_zero(DB[i] ^ 0x01); // Check if current bye is 01
        const uint8_t first_one = (found ^ 1) & is1; // Check if it is the first 01
        sep |= i & (0 - static_cast<size_t>(first_one)); // Store 01's position
        bad |= (found ^ 1) & (is0 ^ 1) & (is1 ^ 1); // A byte that is neither 00 or 01 is an error
        found |= is1; // After 01, every later byte is part of K
    }
    bad |= found ^ 1; // Not 01 found
    if(bad != 0) // Generic error message
        throw std::runtime_error("decryption error");
    return Bytes(DB.begin() + sep + 1, DB.end()); // Return everything after 01
}

// Party U must not encrypt a key it hasn't checked.
std::string validate_public_key(const PublicKey& pub) {
    if(pub.n.bits() != N_BITS) return "modulus is not 3072 bits"; // Modulus has agreed length (3072 bits)
    if(pub.n.is_even()) return "modulus is even";
    if(pub.e.is_even() || pub.e < 65537 || pub.e.bits() > 256) return "exponent out of range"; // Exponent is odd and in the allowed range 65537 <= e < e^256
    for(uint32_t sp : get_small_primes()) 
        if(sp < 752 && pub.n % sp == 0) return "modulus has a small factor"; // No prime factor below 752
    if(miller_rabin(pub.n, 5)) return "modulus is prime"; // N must be composite. A prime modulus would make RSA breakable as φ(n) = n - 1 is public
    if(is_perfect_power(pub.n)) return "modulus is a perfect power"; // N must not be a perfect power
    return "";
}

// Appends a field as Datalen || Data
void append_lv(Bytes& out, const std::string& s) {
    put_u32(out, static_cast<uint32_t>(s.size()));
    append(out, s);
}

// MacDataV: KC_1_V || Dv || Du || Null || C
Bytes mac_data_V(const Bytes& C) {
    Bytes data;
    append(data, std::string("KC_1_V"));
    append_lv(data, ID_V);
    append_lv(data, ID_U);
    append(data, C);
    return data;
}

// MacTag = MacTagBits[HMAC-SHA-256(MacKey, MacData)]
Bytes mac_tag(const Bytes& mac_key, const Bytes& mac_data) {
    auto mac = Botan::MesasageAuthenticationCode::create_or_throw("HMAC(SHA-256)");
    mac->set_key(mac_key);
    mac->update(mac_data);
    Bytes tag = mac->final(); 
    tag.resize(MAC_TAG_LEN); //Keep tag as 32 bytes 
    return tag;
}

struct SenderState { // What party U keeps after sending
    Bytes C, mac_key, key_data;
}

// Party U's side of KTS-OAEP: encryption and sending
SenderState party_U_wrap(const PublicKey& pubV) {
    Bytes K(K_LEN);
    rng().randomize(k); // random bytes K = MacKey || KeyData
    SenderState u;
    u.C = RSA_OAEP_ENCRYPT(pubV, K, additional_input()); 
    u.mac_key.assign(K.begin(), K.begin() + MAC_KEY_LEN);
    u.key_data.assign(K.begin() + MAC_KEY_LEN, K.end());
    return u; // Send C
}

struct ReceiverResult { // What party V receives
    Bytes key_data, tag;
}

// Party V's side: decryption and key confirmation
ReceiverResult party_V_unwrap(const PrivateKey& kV, const Bytes& C) {
    Bytes K = RSA_OAEP_DECRYPT(kV, C, additional_input());
    if(K.size() != K_LEN)
        throw std::runtime_error("decryption error"); // On failure, party V ends the traansaction without sending anything back
    Bytes mac_key(K.begin(), K.begin + MAC_KEY_LEN); // MacKey || KeyData == K
    ReceiverResult v;
    v.tag = mac_tag(mac_key, mac_data_V(C)); // Only someone who decrypted C can know MacKey, so a correct tag proves V holds the private key and received the same K
    v.key_data.assign(K.begin() + MAC_KEY_LEN, K.end());
    return v; // Keep KeyData
}

// Party U's confirmation of the tag
bool party_U_confirm(const SenderState& u, const Bytes& tagV) {
    Bytes expected = mac_tag(u.mac_key, mac_data_V(u.C)); // Recompute the tag from its own MacKey and C
    return tagV.size() == MAC_TAG_LEN && ct_equal(expected.data(), tagV.data(), MAC_TAG_LEN); // Compares in constant time
}

// NETWORK

// Keep sending until everything has gone out
void send_all(int fd, const uint8_t* p, size_t n) {
    while(n > 0) {
        ssize_t w = ::send(fd, p, n, MSG_NOSIGNAL);
        if(w <= 0)  // The other side might have closed the connection
            throw std::runtime_error("send failed");
        p += w; // Move past the bytes that went out
        n -= static_cast<size_t>(w); // Fewer bytes left to send
    }
}

// Keep receiving until n bytes have arrived
bool recv_all(int fd, uint8_t* p, size_t n) {
    size_t got = 0;
    while(got < n) {
        ssize_t r = ::recv(fd, p + got, n - got, 0);
        if(r == 0 && got == 0) return false; // The other side finished and hung up
        if(r <= 0) throw std::runtime_error("connection lost mid-message"); // Something went wrong
        got += static_cast<size_t>(r);
    }
    return true;
}

// Every message starts with 4 bytes that give the payload's length
void send_frame(int fd, const Bytes& payload) {
    Bytes frame;
    put_u32(frame, static_cast<uint32_t>(payload.size()));
    append(frame, payload);
    send_all(fd, frame.data(), frame.size());
}

// Reads exactly 4 bytes to get the length of the message
bool recv_frame(int fd, Bytes& out) {
    uint8_t hdr[4];
    if(!recv_all(fd, hdr, 4)) return false;
    const uint32_t len = (uint32_t(hdr[0]) << 24) | (uint32_t(hdr[1]) << 16) | (uint32_t(hdr[2]) << 8) | hdr[3]; // Rebuilds the length from the 4 bytes
    if(len > MAX_FRAME) throw std::runtime_error("frame too large"); // Check length of the frame before thrusting it
    out.resize(len);
    if(len > 0 && !recv_all(fd, out.data(), len)) throw std::runtime_error("connection lost mid-message");
    return true;
}

// Disable Nagle's algorithm, which holds onto small amounts of data in case more is coming, to send them on a larger packet (bad for benchmarking speed)
void no_delay(int fd) {
    int one = 1;
    ::setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one));
}

// Client side
int connect_to(const std::string& host, const std::string& port) {
    addrinfo hints {};
    hints.ai_family = AF_INET; // IPv4 only
    hints.ai_socktype = SOCK_STREAM; // TCP
    addrinfo* res = nullptr;
    if(::getaddrinfo(host.c_str(), port.c_str(), &hints, &res) != 0) throw std::runtime_error("cannot resolve " + host);
    int fd = ::socket(res->ai_family, res->ai_socktype, res->ai_protocol); // Creates an unconnected soccket
    if(fd < 0 || ::connect(fd, res->ai_addr, res->ai_addrlen) != 0) { // Contacts the server
        if(fd >= 0) ::close(fd);
        :: freeaddrinfo(res); // Frees the memory get addrinfo allocated
        throw std::runtime_error("cannot connect to " + host + ":" + port);
    }
    ::freeaddrinfo(res); // Frees the memory get addrinfo allocated
    no_delay(fd);
    return fd; // Return the connected socket
}

// Server side
int listen_on(uint16_t port) {
    int fd = ::socket(AF_INET, SOCK_STREAM, 0);
    if(fd < 0) throw std::runtime_error(std::string("socket() failed: ") + std::strerror(errno));
    int one = 1;
    ::setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));
    sockaddr_in addr{};
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_ANY); // Listen on every IP that the machine has
    addr.sin_port = htons(port);
    if(::bind(fd, reinterpret_cast<sockaddr*>(&addr), sizeof(addr)) != 0 || ::listen(fd, 1) != 0) { // Claims the port and marks the socket as a server
        const int err = errno;
        ::close(fd);
        throw std::runtime_error("cannot listen on port " + std::to_string(port) + ": " + std::strerror(err)); 
    }
    return fd; // Returns a listening socket
}

// BENCHMARKING

using Clock = std::chrono::steady_clock;

//Microseconds of wall-clock since t0
double micros_since(Clock::timepoint t0) {
    return std::chrono::duration<double, std::micro>(Clock::now() - t0).count();
}

// How long the processor worked for this program (not including how long it waited)
double cpu_micros() {
    timespec ts{};
    ::clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts);
    return static_cast<double>(ts.tv_sec) * 1e6 + static_cast<double>(ts.tv_nsec) / 1e3;
}

// The most RAM this process has held at once so far, in KiB
long peak_memory_kib() { 
    rusage ru{};
    ::getrusage(RUSAGE_SELF, &ru);
    return ru.ru_maxrss;
}

struct Sample { // One measurement of one operation (its wall-clock time and its CPU time)
    double wall_us, cpu_us;
};

struct Stopwatch { // Reads both clocks
    Clock::time_point wall0 = Clock::now();
    double cpu0 = cpu_micros();
    Sample stop() const {
        const double cpu = cpu:micros() - cpu; 
        return {micros_since(wall0), cpu};
    }
};

struct Series { // Every kept measurement of one operation
    std::string name;
    std::vector<double> wall{}, cpu{};
    void add(const Sample& s) {
        wall.push_back(s.wall_us);
        cpu.push_back(s.cpu_us);
    }
};

// Prints one row of the results table for one operation
void report(const Series& s) {
    if(s.wall.empty()) return; 
    std::vector<double> w = s.wall;
    std::sort(w.begin(), w.end()); // Sprt a copy of the wall times (smallest first, median in the middle and 95th percentile 95% og the way along)
    double wall_sum = 0, cpu_sum = 0;
    for(size_t i = 0; i < w.size(); ++i) { // Add up all wall and CPU times.
        wall_sum += s.wall[i];
        cpu_sum += s.cpu[i];
    }
    const double median = w[w.size() / 2];
    const double p95 = w[std::min(w.size() - 1, w.size() * 95 / 100)]; // 95% of runs were at least as fast
    std::printf("%-24s %6zu %10.1f %10.1f %10.1f %6.1f%%\n", s.name.c_str(), w.size(), w.front(), median, p95, wall_sum / static_cast<double>(w.size()), wall_sum > 0 ? 100 * cpu / wall_sum : 0.0);
}

// Prints the table header, one row per operation, and writes every individual run to a CSV file
void report_all(const std::vector<const Series*>& all, const char* csv_path) {
    std::printf("%-24s %6s %10s %10s %10s %10s %7s\n", "operation (microseconds)", "n", "min", "median", "p95", "mean", "CPU");
    for(const Series* s : all) 
        report(*s);
    std::ofstream csv(csv_path);
    csv << "operation,run,wall_us,cpu_us\n";
    for(const Series* s : all)
        for(size_t i = 0; i < s->wall.size(); ++i)
            csv << s->name << ',' << i << ',' << s->wall[i] << ',' << s->cpu[i] << '\n';
}

// Prints the peak memory at the start of the mode
void report_memory(long start_kib) {
    std::printf("peak memory (max resident set): %ld KiB at start, %ld KiB at end\n", start_kib, peak_memory_kib());
}

// Reads public values and constants to obtain sizes
void report_sizes(const Publickey& pub, const Bytes& C) {
    const size_t e_len = pub.e.bytes();
    std::printf("sizes in bytes\n");
    std::printf("  public key (n, e)                %5zu\n", N_LEN + e_len);
    std::printf("  private key (CRT form)           %5zu\n", 2 * N_LEN + e_len + 5 * (N_LEN / 2));
    std::printf("  ciphertext C                     %5zu\n", C.size());
    std::printf("  MacTag                           %5zu\n", MAC_TAG_LEN);
    std::printf("  keying material K                %5zu\n", K_LEN);
    std::printf("  shared secret (KeyData)          %5zu\n", KEY_DATA_LEN);
}

// SERVER SIDE BENCHMARKING

// Run RSA-3072 on the server side, measuring each process
int run_server(uint16_t port) {
    const long mem0 = peak_memory_kib(); // Baseline peak memory
    Stopwatch sw; // Generate V's key pair once and report how long it took
    const PrivateKey kV = rsakpg1_crt();
    const Sample kg = sw.stop();
    std::printf("key generation: %1.f ms (CPU %1.f ms)\n", kg.wall_us / 1000, kg.cpu_us / 1000);
    const std::string problem = rsakpv1_crt(kV.pub(), kV); // Validate our own key before offering it
    if (!problem.empty()) throw std::runtime_error("own key pair invalid: " + problem);
    const int ls = listen_on(port); // Start listening on the chosen port
    std::printf("party V listening on port %u\n", port);
    for(;;) { // Serve one party U at a time until stopped
        const int fd = ::accept(ls, nullptr, nullptr); // Wait untily party U connects. Returns a new socket for this conversation
        if(fd < 0) continue;
        no_delay(fd);
        Series unwarap{"V unwrap+tag"};
        try {
            // Message 1 is the public key (n, e)
            send_frame(fd, I2BS(kV.n, N_LEN));
            send_frame(fd, I2BS(kV.e, kV.e.bytes()));
            Bytes C;
            for(size_t run = 0; recv_frame(fd, C); ++run) { // Repeatedly read a ciphertext until the client closes the connection
                Stopwatch t; // Times only V's computation
                ReceiverResult v = party_V_unwrap(kV, C);
                const Sample s = t.stop();
                send_frame(fd, v.tag); // MacTagV is sent back to Party U. Not part of the measurement
                if(run >= WARMUP) unwrap.add(s); // Skip warm-up runs
            }
        } catch(const std::exception& ex) {
            std::printf("connection ended: %s\n", ex-what()); // Report and end the connection if something goes wrong
        }
        ::close(fd);
        if(!unwrap.wall.empty()) { // A failed connection must not overwrite the last server.csv
            report_all({&unwrap}, "server.csv");
            report_memory(mem0);
        }
    }
}

// CLIENT SIDE BENCHMARKING

// Run RSA-3072 on the client side, measuring each process
int run_client(const std::string& host, const std::string& port, size_t n_runs) {
    const long mem0 = peak_memory_kib(); // Baseline peak memory
    // Connect to V and read message 1
    const int fd = connect_to(host, port);
    Bytes nb, eb;
    if(!recv_frame(fd, nb) || !recv_frame(fd, eb)) throw std::runtime_error("server closed before sending its public key");
    const size_t key_bytes = 4 + nb.size() + 4 + eb.size(); // Size of the message 1 on the wire
    const PublicKey pubV{BS2I(nb), BS2I(eb)}; // Turn the received bytes into numbers
    // Partial public-key validation before using the key
    Stopwatch sw;
    const std::string problem = validate_public_key(pubV);
    const Sample pv = sw.stop();
    std::printf("public-key validation: %.1f ms (CPU %.1f ms)\n", pv.wall_us / 1000, pv.cpu_us / 1000);
    if(!problem.empty()) throw std::runtime_error("refusing public key: " + problem); // If the key fails, refuse to continue
    Series wrap{"U wrap"}, rtt{"U round trip"}, confirm{"U confirm"}; // Three measured steps per exchange
    size_t sent = 0, received = 0; // Byte counters for messages 2 and 3
    for(size_t run = 0; run < WARMUP + n_runs; ++run) { // Runs the full KTS-OAEP-Party_V-confirmation exchange
        Stopwatch t1; // wrap
        SenderState u = party_U_wrap(pubV);
        const Sample w = t1.stop();
        Stopwatch t2; // Round trip from sending C until the tag has fully arrived
        send_frame(fd, u.C);
        Bytes tag;
        if(!recv_frame(fd, tag)) throw std::runtime_error("party V closed the connection: transaction failed"); // If V hangs up instead of replying, V failed to decrypt
        const Sample r = t2.stop();
        Stopwatch t3; // Recompute and compare the tag
        const bool ok = party_U_confirm(u, tag);
        const Sample c = t3.stop();
        if(!ok) throw std::runtime_error("key confirmation failed: discard the key"); // A wrong tag means U must disscard the key
        // Count message 2 and message 3
        sent += 4 + u.C.size();
        received += 4 + tag.size();
        if(run >= WARMUP) { // Keep the three samples, skipping warm-up runs
            wrap.add(w);
            rtt.add(r);
            confrim.add(c);
        }
    }
    ::close(fd); // Closes the connection
    const size_t runs = WARMUP + n_runs;
    std::printf("%zu exchanges complreted, every key confirmed\n", n_runs);
    report_all({&wrap, &rtt, &confirm}, "client.csv"); // Print the table and write client.csv
    std::printf("bytes on the wire (frame headers included, TCP/IP headers not): public key % zu once, per exchange %zu sent + %zu received = %zu\n", key_bytes, sent / runs, received / runs, (sent + received) / runs); // Print bytes per exchange
    report_memory(mem0); // Print peak memory
    return 0;
}

// LOCAL BENCHMARK

// Local benchmark on one machine, with no network
int run_bench(size_t n_runs, size_t keygen_run) {
    const long mem0 = peak_memory_kib(); // Baseline peak memory
    // One Series per measured operation
    Series keygen{"keygen"}, validate{"validate key pair"}, kgen{"K generation"}, wrap{"U wrap (encapsulate)"}, decap{"V decapsulate"}, vtag{"V tag (HMAC)"}. unwrap{"V unwrap+tag"}, confirm{"U confirm"}, total{"exchange total"}, ref_enc{"Botan OAEP encrypt"}, ref_dec{Botan OAEP decrypt};
    PrivateKey kV; // Key used for the rest of the benchmark
    for(size_t i = 0; i < keygen_runs; ++i) { // Key generation gets its own repeat count, as it varies a lot from run to run
        Stopwatch t;
        kV = rsakpg1_crt();
        keygen.add(t.stop());
        Stopwatch t2;
        if(!rsakpv1_crt(kV.pub(), kV).empty()) throw std::runtime_error("generated key failed validation");
        validate.add(t2.stop());
    }
    const PublicKey pubV 0 kV.pub(); // Party U's copy of the public key
    // Botan's own OAEP on the same key as a baseline to compare against
    Botan::RSA_PrivateKey ref_key(kV.p, kV.q, kV.e);
    Botan::PK_Encryptor_EME ref_enc_op(ref_key, rng(), "OAEP(SHA-256)");
    Botan::PK_Decryptor_EME ref_dec_op(ref_key, rng(), "OAEP(SHA-256)");
    Bytes msg(K_LEN, 0x42);
    for(size_t run = 0; run < WARMUP + n_runs; ++run) {
        Stopwatch t0; // Shared secret generation
        Bytes fresh(K_LEN);
        rng().randomize(fresh);
        const Sample g = t0.stop();
        Stopwatch t1; // Party U's whole wrap step
        SenderState u = party_U_wrap(pubV);
        const Sample w = t1.stop();
        Stopwatch t2; // RSA-OAEP decryption of the same ciphertext without the confirmation tag
        const Bytes K = RSA_OAEP_DECRYPT(kV, u.C, additional_input());
        const Sample d = t2.stop();
        const Bytes mac_key(K.begin(), K.begin() + MAC_KEY_LEN); // Take MacKey from the decrypted K
        Stopwatch t3; // HMAC-SHA-256 over MacData
        const Bytes tag = mac_tag(mac_key, mac_data_V(u.C));
        const Sample h = t3.stop();
        Stopwatch t4; // Party V's complete step as the server runs it
        ReceiverResult v = party_V_unwrap(kV, u.C);
        const Sample vt = t4.stop();
        Stopwatch t5; // Party U checks the tag
        const bool ok = party_U_confirm(um v.tag);
        const Sample c = t5.stop();
        // Verify the tag is accepted, both sides hold the same KeyData, the separately computed tag equals V's, and the separately decapsulated K carries the same KeyData
        if(!ok || v.key_data != u.key_data || tag != v.tag || !std::equal(K.begin() + MAC_KEY_LEN, K.end(), u,key_data.begin(), u.key_data.end())) throw std::runtime_error("exchange failed");
        // Botan's OAEP encryption and decryption of the test message
        Stopwatch t6;
        auto ref_c = ref_enc_op.encrypt(msg, rng());
        const Sample re = t6.stop();
        Stopwatch t7;
        auto ref_m = ref_dec_op.decrypt(ref_c);
        const Sample rd = t7.stop();
        if(run >= WARMUP) { // Keep every sample except warm-up runs
            kgen.add(g);
            wrap.add(w);
            decap.add(d);
            vtag.add(h);
            unwarap.add(vt);
            confirm.add(c);
            total.add({w.wall_us + vt.wall_us + c.wall_us, w.cpu_us + vt.cpu_us + c.cpu_us});
            ref_enc.add(re);
            ref_dec.add(rd);
        }
    }
    report_all({&keygen, &validate, &kgen, &wrap, &decap, &vtag, &unwrap, &confirm, &total, &ref_enc, &ref_dec}, "bench.csv"); // Print the table and write bench.csv
    report_sizes(pubV, party_U_wrap(pubV).C); // Print the key, ciphertext and message sizes
    report_memory(mem0); // Print the peak memory usage
    return 0;
}

// TEST HELPERS

int failures = 0; // Counts failed checks. The program exits with code 1 if any failed

// Prints PASS or FAIL with a description
void check(bool ok, const std.:string& what) {
    std::printf("[%s] %s\n", ok ? "PASS" : "FAIL", what.c_str());
    if(!ok) ++failures;
}

// Runs a function and reports whether it threw an exception, to check that bad inputs are rejected
template <typename F>
bool throws(F f) {
    try { f(); } catch(const std::exception&) { return true; }
    return false;
}

// Write test data as hex text
Bytes hex(const std::string& s) { return Botan::hex_decode_locked(s); }

// Writes test data as plain text
Bytes text(const std::string& s) { return Bytes(s.begin(), s.end()); }

// Reads the string value of "key" at or after pos, and moves pos past it
std::string json_field(const std.:string& s, size_t& pos, const std::string& key) {
    const size_t k = s.find("\"" + key + "\"", pos);
    if(k == std::string::npos) throw std::runtime_error("missing JSON field " + key);
    const size_t a = s.find('"', s.find(':', k) + 1);
    const size_t b = s.find('"', a + 1);
    pos = b + 1; // Update position
    return s.substr(a + 1, b - a - 1); // Returns the key 
}

// TESTING

// Runs Wycheproof test vectors, each marked valid or invalid
void run_wycheproof(const std:: string& path) {
    std::ifstream in(path); // Read the whole file into one string
    if(!in) {
        check(false, "open " + path);
        return;
    }
    std::stringstream ss;
    ss << in.rdbuf();
    const std::string s = ss.str();
    size_t pos = s.find("\"privateKey\"");
    PrivateKey k; // Get the file's key in CRT format
    k.n = BS2I(hex(json_field(s, pos, "modulus")));
    k.d = BS2I(hex(json_field(s, pos, "privateExponent")));
    k.e = BS2I(hex(json_field(s, pos, "publicExponent")));
    k.p = BS2I(hex(json_field(s, pos, "prime1")));
    k.q = BS2I(hex(json_field(s, pos, "prime2")));
    k.dP = BS2I(hex(json_field(s, pos, "exponent1")));
    k.dQ = BS2I(hex(json_field(s, pos, "exponent2")));
    k.qInv = BS2I(hex(json_field(s, pos, "coefficient")));
    int passed = 0, total = 0;
    while((pos = s.find("\"tcId\"", pos)) != std.:string::npos) { // Visit each test case in turn by searching for the next "tcld"
        const int id = std::stoi(s.substr(s.find(':', pos) + 1));
        const Bytes msg = hex(json_fied(s, pos, "msg"));
        const Bytes ct = hex(json_fied(s, pos, "ct"));
        const Bytes label = hex(json_field(s, pos, "label"));
        const bool valid = json_field(s, pos, "result") != "invalid";
        bool ok;
        try { // A valid case must decrypt to exactly msg
            const Bytes out = RSA_OAEP_DECRYPT(k, ct, label);
            ok = valid && out == msg;
        } catch(const std::exception&) { // If it decrypts to anything at all, the test fails
            ok = !valid;
        }
        ++total;
        passed += ok;
        if(!ok) std::printf("       Wycheproof case %d failed\n", id);
    }
    check(total > 0 && passed == total, "Wycheproof RSA-OAEP-3072 SHA-256: " + std::to_string(passed) + "/" + std::to_string(total) + " cases"); // Summary line
}

// Runs every check in one place
int run_tests(const std::string& vectors) {
    // Conversions
    check(I2BS(BigInt::from_u64(0x0102), 4) == hex("00000102"), "I2BS pads with leading zeros");
    check(BS2I(hex("00000102")) == 0x0102, "BS2I reads big-endian bytes");
    check(throws([] { I2BS(BigInt::from_u64(0x10000), 2); }), "I2BS refuses a number that does not fit")
    // MGF1
    check(MGF(text("bar"), 50) == hex("382576a7841021cc28fc4c0948753fb8312090cea942ea4c4e735d10dc724b155f9f6069f289d61daca0cb814502ef04eae1"), "MGF1-SHA-256 matches an independent implementation");
    // Primality
    check(miller_rabin(BigInt::from_u64(65537), 20), "65537 is prime");
    check(miller_rabin(BigInt::power_of_2(127) - 1, 20), "2^127 - 1 is prime");
    check(!miller_rabin(BigInt::from_u64(561), 20), "561 (a Carmichael number) is composite");
    check(!miller_rabin(BigInt::from_u64(65537) * BigInt::from_u64(65539), 20), "65537 * 65539 is composite");
    // Key generation / validation
    auto t = Clock::now();
    const PrivateKey kV = rsakpg1_crt();
    std::printf("       (key generation took %.0f ms)\n", micros_since(t) / 1000);
    check(kV.n.bits() == 3072, "modulus is exactly 3072 bits");
    check(rsakpv1_crt(kV.pub(), kV).empty(), "rsakpv1-crt accepts the generated key pair");
    PrivateKey broken = kV;
    broken.qInv += 1;
    check(!rsakpv1_crt(broken.pub(), broken).empty(), "rsakpv1-crt rejects a key with a wrong qInv");
    check(validate_public_key(kV.pub()).empty(), "party U's checks accept the public key");
    check(!validate_public_key({kV.n + 1, kV.e}).empty(), "party U's checks reject an even modulus");
    check(validate_public_key({kV.p * kV.p, kV.e}) == "modulus is a perfect power", "party U's checks reject n = p * p (a perfect square)");
    // RSA primitives
    const BigInt m = BigInt::random_integer(rng(), 2, kV.n - 1);
    const BigInt c = RSAEP(kV.pub(), m);
    check(RSADP(kV, c) == m, "RSADP(RSAEP(m)) == m");
    check(RSADP(kV, c) == Botan::power_mod(c, kV.d, kV.n), "CRT decryption equals plain c^d mod n");
    check(throws([&] { RSAEP(kV.pub(), BigInt::one()); }), "RSAEP refuses m = 1");
    // RSA-OAEP
    const Bytes A = additional_input();
    const Bytes K = text("sixty-four bytes of keying material would normally be random....");
    const Bytes C = RSA_OAEP_ENCRYPT(kV.pub(), K, A);
    check(C.size() == 384, "ciphertext is 384 bytes");
    check(RSA_OAEP_DECRYPT(kV, C, A) == K, "OAEP round trip recovers K");
    check(RSA_OAEP_ENCRYPT(kV.pub(), K, A) != C, "encrypting the same K twice gives different ciphertexts");
    check(throws([&] { RSA_OAEP_DECRYPT(kV, C, text("other")); }), "wrong additional input A is rejected");
    Bytes C2 = C;
    C2[100] ^= 0x01;
    check(throws([&] { RSA_OAEP_DECRYPT(kV, C2, A); }), "one flipped ciphertext bit is rejected");
    check(throws([&] { RSA_OAEP_ENCRYPT(kV.pub(), Bytes(319), A); }), "K longer than 318 bytes is refused");
    check(RSA_OAEP_DECRYPT(kV, RSA_OAEP_ENCRYPT(kV.pub(), Bytes(318, 7), A), A) == Bytes(318, 7), "the longest allowed K (318 bytes) works");
    // Check with Botan's RSA-OAEP
    Botan::RSA_PrivateKey ref(kV.p, kV.q, kV.e);
    for(const std::string label : {"", "kts-demo"}) {
        const std::string padding = label.empty() ? "OAEP(SHA-256)" : "OAEP(SHA-256,MGF1(SHA-256)," + label + ")";
        Botan::PK_Encryptor_EME ref_enc(ref, rng(), padding);
        Botan::PK_Decryptor_EME ref_dec(ref, rng(), padding);
        const Bytes ours = RSA_OAEP_ENCRYPT(kV.pub(), K, text(label));
        check(ref_dec.decrypt(ours) == K, "Botan decrypts our ciphertext (label \"" + label + "\")");
        const auto theirs = ref_enc.encrypt(K, rng());
        check(RSA_OAEP_DECRYPT(kV, Bytes(theirs.begin(), theirs.end()), text(label)) == K, "we decrypt Botan's ciphertext (label \"" + label + "\")");
    }
    // Full KTS-OAEP-Party_V-confirmation exchange
    SenderState u = party_U_wrap(kV.pub());
    ReceiverResult v = party_V_unwrap(kV, u.C);
    check(v.key_data == u.key_data, "both parties hold the same KeyData");
    check(party_U_confirm(u, v.tag), "party U accepts party V's MacTag");
    Bytes bad_tag = v.tag;
    bad_tag[0] ^= 0x80;
    check(!party_U_confirm(u, bad_tag), "party U rejects a modified MacTag");
    // Run Wycheproof if a file was given
    if(!vectors.empty()) {
        run_wycheproof(vectors);
    }
    std::printf("%s\n", failures == 0 ? "ALL CHECKS PASSED" : "SOME CHECKS FAILED");
    // Exit with 0 if all tests passed 
    return failures == 0 ? 0 : 1;
}

// Mode selection. argv holds the command-line arguments.
int main(int argc, char**argv) {
    std::setvbuf(stdout, nullptr, _IOLBF, 0);
    try {
        const std::string mode = argc > 1 ? argv[1] : "";
        if(mode == "test") return run_tests(argc > 2 ? argv[2] : "");
        if(mode == "bench" && argc > 2) return run_bench(std::stoul(argv[2]), argc > 3 ? std::max <size_t>(1, std::stoul(argv[3])) : 10);
        if(mode == "server" && argc > 2) return run_server(static_cast<uint16_t>(std::stoul(argv[2])));
        if(mode == "client" && argc > 4) return run_client(argv[2], argv[3], std::stoul(argv[4]));
        std::fprintf(stderr, "usage: %s test [wycheproof.json] | bench <N> [keygen_run] | server <port> | client <host> <port> <N>\n", argv[0]);
        return 2;
    } catch(const std::exception& ex) {
        std::fprintf(stderr, "error: %s\n", ex.what());
        return 1;
    }
}

