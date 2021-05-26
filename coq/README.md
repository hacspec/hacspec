## Dependencies

The coq libraries uses `compcert` for machine signed and unsigned integer modulo arithmetic, and `coqprime` for finite field arithmetic on prime modulus (to support hacspec's `nat_mod p` type). These can be installed through `opam`:

```
opam install coq-compcert coq-coqprime
```