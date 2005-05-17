HCFLAGS = -Wall -O
#HCFLAGS = -Wall -O -prof -auto-all
# -ddump-simpl
# -ddump-minimal-imports
# -O
# 例外の発生場所を知るには
# compiling with -prof -auto-all and running with +RTS -xc

all: bench.exe

clean:
	rm *.hi *.o *.exe

.PHONY: all clean

bench.exe: Bench.hs
	ghc $(HCFLAGS) --make $< -o $@