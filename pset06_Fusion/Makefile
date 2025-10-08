.PHONY: rocq clean

ROCQ=rocq compile -q -R ../frap Frap -R . Pset6

rocq:
	$(ROCQ) Pset6Sig.v
	$(ROCQ) Pset6.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .*.cache *.vok *.vos