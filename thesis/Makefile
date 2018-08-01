CHAPTERS_SRC=$(wildcard chapters/*.lhs)
CHAPTERS_TEX=$(CHAPTERS_SRC:.lhs=.tex)

thesis.pdf: thesis.bib thesis.tex
	pdflatex thesis.tex
	bibtex thesis
	pdflatex thesis.tex
	pdflatex thesis.tex

# chapters/%.tex: chapters/%.lhs agda.lhs
# 	lhs2TeX --agda $< -o $@
# 
# .PHONY: clean
# clean:
# 	rm -f ${CHAPTERS_TEX}
# 	rm -f *.aux
# 	rm -f *.pdf

thesis.tex: root.lhs agda.lhs localdefs.lhs ${CHAPTERS_SRC}
	lhs2TeX --agda root.lhs -o thesis.tex

.PHONY: quick
quick: thesis.tex
	pdflatex thesis.tex
