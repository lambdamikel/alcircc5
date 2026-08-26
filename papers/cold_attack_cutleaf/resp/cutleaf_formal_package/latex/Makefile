.PHONY: all clean

all: cutleaf_residue_note.pdf

cutleaf_residue_note.pdf: cutleaf_residue_note.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error $<

clean:
	latexmk -C cutleaf_residue_note.tex
