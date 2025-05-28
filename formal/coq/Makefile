VOFILES=ExoCap.vo LambdaCap.vo IRQProof.vo StreamsProof.vo

all: $(VOFILES)

%.vo: %.v
	coqc $<

clean:
	rm -f $(VOFILES) *.glob *.vo *.vio
