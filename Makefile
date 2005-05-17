HCFLAGS = -Wall -O
#HCFLAGS = -Wall -O -prof -auto-all
# -ddump-simpl
# -ddump-minimal-imports
# -O
# 例外の発生場所を知るには
# compiling with -prof -auto-all and running with +RTS -xc

all: bench.exe test.exe

check.exe: Check.hs Hyperset.hs
	ghc $(HCFLAGS) --make $< -o $@

bench.exe: Bench.hs Hyperset.hs
	ghc $(HCFLAGS) --make $< -o $@

test.exe: Test.hs Hyperset.hs
	ghc $(HCFLAGS) --make $< -o $@

.PHONY: test clean doc

doc: Hyperset.hs
	haddock -o doc -h Hyperset.hs

test: test.exe
	./test.exe +RTS -xc -RTS

clean:
	rm *.hi *.o *.exe
