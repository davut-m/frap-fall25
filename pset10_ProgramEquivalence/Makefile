.PHONY: rocq clean

ROCQ=rocq compile -q -R ../frap Frap -R . Pset10

rocq:
	$(ROCQ) Pset10Sig.v
	$(ROCQ) Pset10.v

clean:
	rm -f *.vo *.vok *.vos *.glob
