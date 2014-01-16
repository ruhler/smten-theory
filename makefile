
default: src/SmtenIO.vo src/SmtenS.vo src/Sat.vo

%.vo: %.v
	coqc -I lib -I src $<

lib/Smallstep.vo: lib/SfLib.vo
src/Smten.vo: lib/SfLib.vo
src/SmtenProp.vo: lib/Smallstep.vo src/Smten.vo
src/SmtenS1.vo: src/SmtenProp.vo
src/SmtenS.vo: src/SmtenS1.vo
src/SmtenIO.vo: src/SmtenS.vo
src/Sat.vo: lib/SfLib.vo

clean:
	rm lib/*.vo src/*.vo lib/*.glob src/*.glob

