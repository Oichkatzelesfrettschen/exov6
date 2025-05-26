.PHONY: proof formal

proof:
	$(MAKE) -C coq all

formal:
	@if command -v coqc >/dev/null 2>&1; then \
	  $(MAKE) -C formal/coq all; \
	else \
		  echo "coqc not found; skipping Coq build"; \
	fi
	@if command -v tlc >/dev/null 2>&1; then \
		  tlc formal/tla/ExoCap.tla >/dev/null; \
	else \
		  echo "tlc not found; skipping TLA+ check"; \
	fi
