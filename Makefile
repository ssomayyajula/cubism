all:
	agda --latex Cubical.lagda
	cd latex && xelatex Cubical.tex && evince Cubical.pdf

clean:
	rm -rf latex

