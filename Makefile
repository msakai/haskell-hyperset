
bench.exe: Bench.hs Hyperset.hs
	ghc -O -ddump-simpl -prof -auto-all --make Bench.hs -o $@

test.exe: Test.hs Hyperset.hs
	ghc -prof -auto-all --make Test.hs -o $@

.PHONY: test clean

test: test.exe
	./test.exe +RTS -xc -RTS

clean:
	rm *.hi *.o *.exe