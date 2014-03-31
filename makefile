
default: smten/SmtenIO.vo src/SmimplS.vo src/SmtrgProp.vo src/Approx.vo

%.vo: %.v
	coqc -I lib -I smten -I src $<

smten/Smten.vo: lib/SfLib.vo
smten/SmtenProp.vo: lib/SfLib.vo smten/Smten.vo
smten/SmtenS1.vo: smten/SmtenProp.vo
smten/SmtenS.vo: smten/SmtenS1.vo
smten/SmtenIO.vo: smten/SmtenS.vo

src/Sat.vo: lib/SfLib.vo

src/Smimpl.vo: lib/SfLib.vo src/Sat.vo
src/SmimplProp.vo: src/Smimpl.vo
src/SmimplS.vo: src/SmimplProp.vo
src/SmimplIO.vo: src/SmimplS.vo

src/Smtrg.vo: lib/SfLib.vo src/Sat.vo
src/SmirgProp.vo: src/Smrgl.vo

clean:
	rm lib/*.vo src/*.vo smten/*.vo lib/*.glob src/*.glob smten/*.glob

