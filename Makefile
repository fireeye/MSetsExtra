# File: Makefile
#
# Author: FireEye, Inc. - Formal Methods Team <formal-methods@fireeye.com>

COQINCLUDES=-I .
COQC=coqtop -q $(COQINCLUDES) -batch -compile
COQDOC=coqdoc
COQDEP=coqdep $(COQINCLUDES)
COQFILES=\
  MSetWithDups.v \
  MSetFoldWithAbort.v \
  MSetIntervals.v \
  MSetListWithDups.v


#######################################
########## GLOBAL RULES ###############

.DEFAULT_GOAL: all

.PHONY: all coqhtml coqtex clean doc


proof: $(COQFILES:.v=.vo)
doc: coqhtml coqtex doc/main.tex
all: proof doc



#######################################
########## COQ RULES ##################

%.vo %.glob: %.v
	$(COQC) $*

%.v.d: %.v
	$(COQDEP) "$<" > "$@" || ( RV=$$?; rm -f "$@"; exit $${RV} )

CLEAN_TARGETS := clean clean_doc clean_coq

ifeq (,$(filter $(CLEAN_TARGETS),$(MAKECMDGOALS)))
  -include $(addsuffix .d,$(COQFILES))
  .SECONDARY: $(addsuffix .d,$(COQFILES))
endif

#######################################
########## DOCUMENTATION  #############

coqhtml:
	mkdir -p coqdoc
	$(COQDOC) -toc --html -g -d coqdoc $(COQFILES)

coqtex:
	mkdir -p coqdoc
	$(COQDOC) -toc --latex -g -o coqdoc/mset_doc.tex $(COQFILES)
	cd coqdoc; pdflatex mset_doc.tex
	cd coqdoc; pdflatex mset_doc.tex

%.html: %.md 
	pandoc -N $< -o $@

%.pdf: %.md 
	pandoc -N $< -o $@

doc/mset.pdf: doc/mset.tex doc/mset.bib
	cd doc; pdflatex mset.tex
	cd doc; bibtex mset
	cd doc; pdflatex mset.tex
	cd doc; pdflatex mset.tex

#######################################
########## CLEANING RULES #############

clean_coq:
	rm -f $(COQFILES:.v=.v.d) $(COQFILES:.v=.vo) $(COQFILES:.v=.glob)

clean_doc:
	rm -rf coqdoc
	rm -f readme.html readme.pdf

clean_tex:
	cd doc; rm -f *.ps *~ *.dvi *.aux *.log *.idx *.toc *.nav *.out *.snm *.flc *.vrb *.bbl *.blg

clean: clean_coq clean_doc clean_tex
	rm -f *~
