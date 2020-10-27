SRC=Hacspec_Chacha20.ec



%.ec.checked: %.ec
	easycrypt compile $^

verify-all: $(addsuffix .checked,$(SRC))
