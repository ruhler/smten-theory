
default: src/SmtenIO.vo src/SmimplS.vo src/SmtrgProp.vo

%.vo: %.v
	coqc -I lib -I src $<

src/Smten.vo: lib/SfLib.vo
src/SmtenProp.vo: lib/SfLib.vo src/Smten.vo
src/SmtenS1.vo: src/SmtenProp.vo
src/SmtenS.vo: src/SmtenS1.vo
src/SmtenIO.vo: src/SmtenS.vo
src/Sat.vo: lib/SfLib.vo

src/Smimpl.vo: lib/SfLib.vo src/Sat.vo
src/SmimplProp.vo: src/Smimpl.vo
src/SmimplS.vo: src/SmimplProp.vo
src/SmimplIO.vo: src/SmimplS.vo

src/Smtrg.vo: lib/SfLib.vo src/Sat.vo
src/SmirgProp.vo: src/Smrgl.vo

clean:
	rm lib/*.vo src/*.vo lib/*.glob src/*.glob

