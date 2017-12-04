all:
	agda --latex Cubical.lagda
	cd latex && latexmk -xelatex Cubical.tex && evince Cubical.pdf

clean:
	rm -rf latex

