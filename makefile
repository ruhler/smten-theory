
default: src/SmtenIO.vo src/SmimplS.vo

%.vo: %.v
	coqc -I lib -I src $<

src/Smten.vo: lib/SfLib.vo
src/SmtenProp.vo: lib/SfLib.vo src/Smten.vo
src/SmtenS1.vo: src/SmtenProp.vo
src/SmtenS.vo: src/SmtenS1.vo
src/SmtenIO.vo: src/SmtenS.vo
src/Sat.vo: lib/SfLib.vo

src/Smimpl.vo: lib/SfLib.vo src/Sat.vo
src/SmimplProp.vo: lib/SfLib.vo src/Smimpl.vo
src/SmimplS.vo: src/Smimpl.vo
src/SmimplIO.vo: src/SmimplS.vo

clean:
	rm lib/*.vo src/*.vo lib/*.glob src/*.glob

