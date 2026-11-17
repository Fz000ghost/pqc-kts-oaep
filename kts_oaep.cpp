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
ReceiverResult party_v_unwrap(const PrivateKey& kV, const Bytes& C) {
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


int main() {
    return 0;
}   