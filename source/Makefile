SRC = core_json.c
ARGS = -target 32bit -I include
VFDEP = /usr/local/vfdeps-0e0aebc

verifast:
	verifast $(ARGS) $(SRC) -shared

vfide:
	DYLD_LIBRARY_PATH=$(VFDEP)/lib vfide $(ARGS) $(SRC) &
