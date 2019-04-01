all: Makefile.coq
	@echo "# Building base-library"
	+@make -s -C base-library
	@echo "# Building template-coq"
	+@make -s -C template-coq/template-coq
	@echo "# Building coq-library-undecidability"
	+@make -s -C coq-library-undecidability
	@echo "# Building this project"
	+make -f Makefile.coq all

html: Makefile.coq
	+make -f Makefile.coq html
	rm -rf docs/website/*.html
	mv html/*.html docs/website
	rm -rf html	

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq CoqMakefile.conf

realclean: Makefile.coq
	+make -C template-coq/template-coqm clean
	+make -C base-library clean
	+make -C coq-library-undecidability clean
	+make -f Makefile.coq clean
	rm -f Makefile.coq CoqMakefile.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject > Makefile.coq

.PHONY: all html clean

#Costum alterations:

%.vo: Makefile.coq
	+make -f Makefile.coq $@

