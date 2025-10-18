.PHONY: rocq clean

ROCQ=rocq compile -q -R ../frap Frap -R . Pset7

rocq:
	$(ROCQ) Pset7Sig.v
	$(ROCQ) Pset7.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .lia.cache .nia.cache *.vok *.vos