SRC=Hacspec_Poly1305.ec



%.ec.checked: %.ec
	easycrypt compile \
		-I Jasmin:eclib \
		-I . \
		-I ~/libjc/proof/crypto_onetimeauth/poly1305 \
		-I ~/libjc/proof/crypto_core/keccakf160064bits \
		-I /usr/local/lib/easycrypt/theories/algebra \
		$^

verify-all: $(addsuffix .checked,$(SRC))
