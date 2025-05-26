VOFILES=ExoCap.vo

all: $(VOFILES)

%.vo: %.v
coqc $<

clean:
rm -f $(VOFILES) *.glob *.vo *.vio
