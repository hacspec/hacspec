SRC=Hacspec_Chacha20.ec Hacspec_Chacha20_expected.ec

EASYCRYPT=easycrypt compile \
	-I Jasmin:eclib \
	-I . \
	-I ~/libjc/proof/crypto_core/keccakf160064bits \
	-I ~/libjc/proof/crypto_stream/chacha20

%.eco: %.ec
	$(EASYCRYPT) $<

verify-all: $(addsuffix o,$(SRC))
