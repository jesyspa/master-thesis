proposal.pdf: proposal.bib proposal.tex
	pdflatex proposal.tex
	bibtex proposal
	pdflatex proposal.tex
	pdflatex proposal.tex

proposal.tex: root.tex $(wildcard chapters/*.tex)
	lhs2TeX root.tex -o proposal.tex

