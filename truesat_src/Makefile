verify:
	dafny /compile:0 /vcsCores:24 /errorLimit:1 /trace *.dfy solver/*.dfy

verifysingle:
	dafny /timeLimit:50 /compile:0 /vcsCores:1 /errorLimit:1 /trace *.dfy solver/*.dfy

build:
	dafny /compileTarget:cs /compileVerbose:1 /spillTargetCode:1 /compile:2 /unicodeChar:0 truesat.dfy file_input.cs

clean:
	rm -f *.dll solver/*.dll *.dll.mdb solver/*.dll.mdb truesat.cs truesat.exe.mdb
