CHAPTERS_SRC=$(wildcard chapters/*.lhs)
CHAPTERS_TEX=$(CHAPTERS_SRC:.lhs=.tex)

proposal.pdf: proposal.bib proposal.tex
	pdflatex proposal.tex
	bibtex proposal
	pdflatex proposal.tex
	pdflatex proposal.tex

# chapters/%.tex: chapters/%.lhs agda.lhs
# 	lhs2TeX --agda $< -o $@
# 
# .PHONY: clean
# clean:
# 	rm -f ${CHAPTERS_TEX}
# 	rm -f *.aux
# 	rm -f *.pdf

proposal.tex: root.lhs agda.lhs ${CHAPTERS_SRC}
	lhs2TeX --agda root.lhs -o proposal.tex

