.PHONY: rocq clean

ROCQ=rocq compile -q -R ../frap Frap -R . Pset9

rocq:
	$(ROCQ) Pset9Sig.v
	$(ROCQ) Pset9.v

clean:
	rm -f *.vo *.vok *.vos *.glob