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

int main() {
    return 0;
}   