.PHONY: all coq

all: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
