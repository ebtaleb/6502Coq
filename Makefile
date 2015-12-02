OBJECTS = Coqlib.vo M6502_Reg.vo

all: Coqlib.vo M6502_Reg.vo

.v.vo:
	coqc $<

.SUFFIXES: .v .vo
.PHONY: all clean Util

clean:
	rm -f $(OBJECTS)
	rm -f *.*~ *.glob

