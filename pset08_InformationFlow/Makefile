.PHONY: rocq clean

ROCQ=rocq compile -q -R ../frap Frap -R . Pset8

rocq:
	$(ROCQ) Pset8Sig.v
	$(ROCQ) Pset8.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .lia.cache .nia.cache *.vok *.vos
