bench.exe: Bench.hs Hyperset.hs
	ghc -Wall -O -prof -auto-all --make $< -o $@
# -ddump-simpl
# -ddump-minimal-imports
# -O

check.exe: Check.hs Hyperset.hs
	ghc -Wall -prof -auto-all --make $< -o $@

# 例外の発生場所を知るには
# compiling with -prof -auto-all and running with +RTS -xc

test.exe: Test.hs Hyperset.hs
	ghc --make $< -o $@

.PHONY: test clean

test: test.exe
	./test.exe +RTS -xc -RTS

clean:
	rm *.hi *.o *.exe