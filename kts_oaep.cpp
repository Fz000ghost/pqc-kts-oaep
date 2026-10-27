// Build:  g++ -std=c++20 -O2 -Wall kts_oaep.cpp -o ping
// VM-V:   ./ping server 5000
// VM-U:   ./ping client 10.0.2.2 5000
#include <arpa/inet.h>
#include <netdb.h>
#include <sys/socket.h>
#include <unistd.h>
 
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
 
static void die(const char* what) {
    std::perror(what);
    std::exit(1);
}
 
static void server(int port) {
    int ls = socket(AF_INET, SOCK_STREAM, 0);
    int one = 1;
    setsockopt(ls, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);  // allow quick restarts
    sockaddr_in addr{};
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_ANY);
    addr.sin_port = htons(port);
    if (bind(ls, reinterpret_cast<sockaddr*>(&addr), sizeof addr) < 0) die("bind");
    if (listen(ls, 1) < 0) die("listen");
    std::printf("party V listening on port %d\n", port);
    for (;;) {
        int fd = accept(ls, nullptr, nullptr);
        if (fd < 0) continue;
        std::printf("party U connected\n");
        char buf[256];
        ssize_t n;
        while ((n = recv(fd, buf, sizeof buf, 0)) > 0) {  // echo every byte back
            std::printf("V received: %.*s\n", static_cast<int>(n), buf);
            send(fd, buf, n, MSG_NOSIGNAL);
        }
        close(fd);
        std::printf("party U disconnected\n");
    }
}
 
static void client(const char* host, const char* port) {
    addrinfo hints{}, *res = nullptr;
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_STREAM;
    if (getaddrinfo(host, port, &hints, &res) != 0) {
        std::fprintf(stderr, "cannot resolve %s\n", host);
        std::exit(1);
    }
    int fd = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
    if (fd < 0 || connect(fd, res->ai_addr, res->ai_addrlen) < 0) die("connect");
    freeaddrinfo(res);
 
    for (int i = 1; i <= 5; ++i) {
        std::string msg = "hello " + std::to_string(i) + " from party U";
        auto t0 = std::chrono::steady_clock::now();
        if (send(fd, msg.data(), msg.size(), MSG_NOSIGNAL) < 0) die("send");
        std::string echo(msg.size(), '\0');
        size_t got = 0;
        while (got < echo.size()) {  // TCP may deliver the echo in pieces
            ssize_t n = recv(fd, echo.data() + got, echo.size() - got, 0);
            if (n <= 0) die("recv");
            got += n;
        }
        double us = std::chrono::duration<double, std::micro>(std::chrono::steady_clock::now() - t0).count();
        std::printf("U got back: %s  (%s, round trip %.0f us)\n", echo.c_str(),
                    echo == msg ? "match" : "MISMATCH", us);
    }
    close(fd);
}
 
int main(int argc, char** argv) {
    if (argc == 3 && std::strcmp(argv[1], "server") == 0) server(std::atoi(argv[2]));
    else if (argc == 4 && std::strcmp(argv[1], "client") == 0) client(argv[2], argv[3]);
    else {
        std::fprintf(stderr, "usage: %s server <port> | client <host> <port>\n", argv[0]);
        return 2;
    }
}