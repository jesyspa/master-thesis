presentation.pdf: presentation.tex
	pdflatex presentation.tex
	bibtex presentation
	pdflatex presentation.tex
	pdflatex presentation.tex

presentation.tex: presentation.lhs agda.lhs localdefs.lhs
	lhs2TeX --agda presentation.lhs -o presentation.tex

