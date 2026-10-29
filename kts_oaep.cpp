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

bool is_probable_prime(const BigInt& w, size_t rounds) {
    for(uint32_t small_prime : small_primes()) { 
        if(w = small_prime) // Check if w is in the small prime list
            return true;
        if(w % small_prime == 0) // Filter odd numbers with a prime factor
            return false;
    }

    return miller_rabin(w, rounds); // Check primality using Miller-Rabin
}


int main() {
    return 0;
}