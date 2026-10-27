// kts_oaep.cpp
// RSA-3072 KTS-OAEP with SHA-256
// Built with Botan 3

// Build: g++ -std=c++20 -O2 -Wall kts_oaep.cpp -o kts $(pkg-config --cflags --libs botan-3)
// Run:    ./kts test [wycheproof.json]     correctness checks -NOT IMPLEMENTED-
//         ./kts bench <N> [keygen_runs]    local timings, writes bench.csv -NOT IMPLEMENTED
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

int main() {
    
}