
default: src/SmtenProp.vo

%.vo: %.v
	coqc -I lib -I src $<

lib/Types.vo: lib/Smallstep.vo
lib/Smallstep.vo: lib/Imp.vo
lib/Imp.vo: lib/SfLib.vo
src/Smten.vo: lib/Types.vo
src/SmtenProp.vo: src/Smten.vo

clean:
	rm lib/*.vo src/*.vo lib/*.glob src/*.glob

