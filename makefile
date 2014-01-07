
default: src/Stlc.vo

%.vo: %.v
	coqc -I lib -I src $<

lib/Types.vo: lib/Smallstep.vo
lib/Smallstep.vo: lib/Imp.vo
lib/Imp.vo: lib/SfLib.vo
src/Stlc.vo: lib/Types.vo

clean:
	rm lib/*.vo src/*.vo lib/*.glob src/*.glob

