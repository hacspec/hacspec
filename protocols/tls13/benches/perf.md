# Bulk performance

**Setup**
* 1024 1 MB chunks
* encrypt
* decrypt
* System:
    * macOS 11.3, i7-1068NG7 @ 2.3GHz
    * rustc 1.51.0
* [bulk.rs](./bulk.rs)

## hacspec backend
### encrypt
* TLS_AES_128_GCM_SHA256_X25519: 171.38 ms
* TLS_CHACHA20_POLY1305_SHA256_X25519: 1.3924 s

### decrypt
* TLS_AES_128_GCM_SHA256_X25519: 171.45 ms
* TLS_CHACHA20_POLY1305_SHA256_X25519: 1.4186 s

## evercrypt backend
### encrypt
* TLS_AES_128_GCM_SHA256_X25519: 6.3776 ms
* TLS_CHACHA20_POLY1305_SHA256_X25519: 7.9467 ms

### decrypt
* TLS_AES_128_GCM_SHA256_X25519: 5.8104 ms
* TLS_CHACHA20_POLY1305_SHA256_X25519: 6.8756 ms

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
* TLS_AES_128_GCM_SHA256_X25519: 295.62 ms
* TLS_AES_128_GCM_SHA256_SECP256r1:

### server
* TLS_AES_128_GCM_SHA256_X25519: 174.28 ms
* TLS_AES_128_GCM_SHA256_SECP256r1:

## evercrypt backend
### client
* TLS_AES_128_GCM_SHA256_X25519: 1.1614 ms
* TLS_AES_128_GCM_SHA256_SECP256r1:

### server
* TLS_AES_128_GCM_SHA256_X25519: 471.85 us
* TLS_AES_128_GCM_SHA256_SECP256r1:

# Links
* [rustls vs openssl](https://jbp.io/2019/07/01/rustls-vs-openssl-performance.html)
