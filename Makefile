COQMF ?= coq_makefile
all: Makefile.coq
	$(MAKE) -f Makefile.coq
Makefile.coq: _CoqProject
	$(COQMF) -f _CoqProject -o Makefile.coq
clean:
	@if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	@rm -f Makefile.coq
.install: Makefile.coq
	$(MAKE) -f Makefile.coq install
install: .install
