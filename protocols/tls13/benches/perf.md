# Bulk performance

**Setup**
* 100 MB in 16 KB chunks
* encrypt
* decrypt
* System:
    * macOS 11.3, i7-1068NG7 @ 2.3GHz
    * rustc 1.51.0
* [bulk.rs](./bulk.rs)

## hacspec backend
```bash
cargo bench -p bertie --bench bulk -- --sample-size=10
```
### encrypt
* TLS_AES_128_GCM_SHA256_X25519: 16.283 s
* TLS_CHACHA20_POLY1305_SHA256_X25519: 134.82 s

### decrypt
* TLS_AES_128_GCM_SHA256_X25519: 16.213 s
* TLS_CHACHA20_POLY1305_SHA256_X25519: 134.35 s

## evercrypt backend
```bash
cargo bench -p bertie --bench bulk --features evercrypt-backend -- --sample-size=10
```
### encrypt
* TLS_AES_128_GCM_SHA256_X25519: 324.46 ms
    * 308.2 MB/s
* TLS_CHACHA20_POLY1305_SHA256_X25519: 365.76 ms
    * 273.4 MB/s

### decrypt
* TLS_AES_128_GCM_SHA256_X25519: 265.40 ms
* TLS_CHACHA20_POLY1305_SHA256_X25519: 308.00 ms

## Rustls
* AES_128_GCM_SHA256: 1919.46 MB/s
* CHACHA20-POLY1305: 1158.24 MB/s

## OpenSSL
* AES_128_GCM_SHA256: 2257.01 MB/s
* CHACHA20-POLY1305: 1317.08 MB/s

# Handshake performance

**Setup**
* ECDSA P256 SHA256 server certificate
* System:
    * macOS 11.3, i7-1068NG7 @ 2.3GHz
    * rustc 1.51.0
* *We don't sample fresh reandomness! This is cheating a little.*
* [handshake.rs](./handshake.rs)

## hacspec backend
### client
* TLS_AES_128_GCM_SHA256_X25519: 250.96 ms
* TLS_AES_128_GCM_SHA256_SECP256r1: 338.94 ms

### server
* TLS_AES_128_GCM_SHA256_X25519: 166.36 ms
* TLS_AES_128_GCM_SHA256_SECP256r1: 258.00 ms

## evercrypt backend
### client
* TLS_AES_128_GCM_SHA256_X25519: 1.1614 ms
* TLS_AES_128_GCM_SHA256_SECP256r1: 1.9532 ms

### server
* TLS_AES_128_GCM_SHA256_X25519: 471.85 us
* TLS_AES_128_GCM_SHA256_SECP256r1: 1.3668 ms

## Rustls & OpenSSL
### Client
It's not clear what curve is used here. The performance checks here also include the PKI checks.
* Rustls: ~3188 handshakes/s
* OpenSSL:  ~2253 handshakes/s

### Server
* Rustls: ~1346 handshakes/s
* OpenSSL:  ~1212 handshakes/s

# Links
* [rustls vs openssl](https://jbp.io/2019/07/01/rustls-vs-openssl-performance.html)
