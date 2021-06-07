SRC = core_json.c
ARGS = -target 32bit -I include -prover z3v4.5
VFDEP = /usr/local/vfdeps-0e0aebc

verifast:
	verifast $(ARGS) $(SRC) -shared

vfide:
	DYLD_LIBRARY_PATH=$(VFDEP)/lib vfide $(ARGS) $(SRC) &
