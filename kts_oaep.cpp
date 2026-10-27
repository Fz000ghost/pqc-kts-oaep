#include <botan/hash.h>
#include <botan/hex.h>
#include <botan/version.h>
#include <iostream>

int main() {
    auto sha = Botan::HashFunction::create_or_throw("SHA-256");
    sha->update("abc");
    std::cout << Botan::version_string() << "\n"
              << "SHA-256(\"abc\") = " << Botan::hex_encode(sha->final(), false) << "\n";
}