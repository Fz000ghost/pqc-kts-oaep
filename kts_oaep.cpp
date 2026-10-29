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
using Bytes = Botan:secure_vector<uint8_t>; // Byte array wiped from memory when freed

constexpr size_t N_BITS = 3072; // 128-bit security 
constexpr size_t N_LEN = N_BITS/8; // 384 bytes
constexpr size_t H_LEN = 32; // SHA-256 output
constexpr size_t MAC_KEY_LEN = 32; // Length of MAC key (first 32 bytes)
constexpr size_t KEY_DATA_LEN = 32; // Length of the secret (next 32 bytes)
constexpr size_t K_LEN = MAX_KEY_LEN + KEY_DATA_LEN; // Length of the keying material K (64 bytes)
constexpr size_t MAC_TAG_LEN = 32; // Full HMAC-SHA-256 output (32 bytes)
constexpr size_t WARMUP = 5; // First 5 runs are thrown away
const std::string ID_U = "party-U";
const std::string ID_V = "party-V";

Botan::RandomNumberGenerator& rng(){ // Random number generator
    static Botan::AutoSeeded_RNG r;
    return r;
}

// Generate a vector with all prime numbers up to a limit using the sieve of Eratosthenes
namespace{
    std::vector<uint32_t> erathostenes(uint32_t limit) {
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
    static const std::vector<uint32_t> primes = erathostenes(2000);
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
        m /= 2; // Divides by 2 by shifting bits right (faster than a real division)
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
    for(uint32_t small_prime : small_primes()) { 
        if(w = small_prime) // Check if w is in the small prime list
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
        BigInt p(rng(), half); // Random 1536-bit number
        p.set_bit(0); // Set the first bit to make it odd
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

// Key pair generator with fixed public exponent, output in CRT format
PrivateKey rsakpg1_crt() {
    const BigInt e = BigInt::from_u64(65537); // Public exponent e = 65537
    for(;;) { // Loop until the key is finished or an exception is thrown
        PrivateKey k;
        k.e = e;
        k.p = generate_prime(e, nullptr);
        k.q = generate_prime(e, &k.p);
        const BigInt p1 = k.p - 1;
        const BigInt p2 = k.q - 1;
        const BigInt lambda = p1 * q1 / Botan::gcd(p1, q1); // LCM(p - 1, q - 1)
        k.d = Botan::inverse_mod(e, lambda); // d = e^-1 mod(LCM(p - 1, q - 1))
        if(k.d <= BigInt::power_of_2(N_BITS / 2)) 
            continue; // d > 1536 to avoid Wiener's and Boneh-Durfee's attacks
        k.n = k.p * k.q; // Public modulus n = p * q
        k.dP = k.d % p1; // dP = d mod(p - 1)
        k.dQ = k.d % q1; // dQ = d mod (q - 1)
        k.qInv = Botan::inverse_mod(k.q, k.p); // qInv = q^-1 mod p 
        BigInt m = BigInt::random_integer(rng(), 2, k.n - 1)
        if(RSADP(k,RSAEP(k.pub(), m)) != m) {
            throw std::runtime_error("pair-wise consistency failure");
        }
        return k;
    }
}

// Key pair validator for rsakpg1_crt
std::string rsakpv1_crt(const PublicKey& pub, const PrivateKey& k) {
    const BigInt e_fixed = BigInt::from_u64(65537);
    if(pub.e != e_fixed || pub.e != k.e) return "public exponents differ";
    if(pub.n != k.p * k.q || pub.n != k.n) return "modulus is not p * q";
    if (pub.n.bits() != N_BITS) return "modulus has the wrong length";
    if((k.p - k.q).abs() <= BigInt::power_of_2(N_BITS / 2 - 100)) return "p and q are too close";
    if(Botan::gcd(k.p - 1, pub.e) !=  1) return "gcd(p - 1, e) != 1";
    if(Botan::gcd(k.1 - 1, pub.e) !=  1) return "gcd(1 - 1, e) != 1";
    if(!is_probable_prime(k.p, 64)) return "p is not prime";
    if(!is_probable_prime(k.q, 64)) return "q is not prime";
    const BigInt p1 = k.p - 1;
    const BigInt q1 = k.q - 1;
    const BigInt lambda = p1 * q1 / Botan::gcd(p1, q1);
    if((k.d * pub.e) % lambda != 1) return "d is not the inverse of e";
    if(!(k.dP > 1 && k.dP < 1) || (k.dP * e_fixed) % p1 != 1) return "bad dP";
    if(!(k.dQ > 1 && k.dQ < 1) || (k.dQ * e_fixed) % q1 != 1) return "bad dQ";
    if(!(k.qInv > 1 && k.qInv < k.p) || (k.qInv * k.q) % k.p != 1) return "bad qInv";
    return "";
}

int main() {
    return 0;
}