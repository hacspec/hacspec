SRC=Hacspec_Chacha20.ec Hacspec_Chacha20_expected.ec

EASYCRYPT=easycrypt compile \
	-I Jasmin:eclib \
	-I . \
	-I ~/libjc/proof/crypto_core/keccakf160064bits

Hacspec_Chacha20.eco: Hacspec_Chacha20.ec
	$(EASYCRYPT) -I ~/libjc/proof/crypto_stream/chacha20 $^

Hacspec_Chacha20_expected.eco: Hacspec_Chacha20_expected.ec
	$(EASYCRYPT) -I ~/libjc/proof/crypto_stream/chacha20 $^


verify-all: $(addsuffix o,$(SRC))
