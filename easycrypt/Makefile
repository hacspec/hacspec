SRC=\
	Hacspec.ec \
	Hacspec_Chacha20.ec \
	Hacspec_Chacha20_reference.ec \
	Hacspec_Poly1305.ec \
	Hacspec_Poly1305_reference.ec

EASYCRYPT=easycrypt compile \
	-I Jasmin:eclib \
	-I . \
	-I ~/libjc/proof/crypto_core/keccakf160064bits \
	-I ~/libjc/proof/crypto_stream/chacha20 \
	-I ~/libjc/proof/crypto_onetimeauth/poly1305

%.eco: %.ec
	$(EASYCRYPT) $<

verify-all: $(addsuffix o,$(SRC))
