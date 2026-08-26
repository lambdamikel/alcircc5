#!/bin/sh
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$ROOT/latex"
latexmk -pdf -interaction=nonstopmode -halt-on-error cutleaf_residue_note.tex
cp cutleaf_residue_note.pdf "$ROOT/cutleaf_residue_note.pdf"
echo "Built $ROOT/cutleaf_residue_note.pdf"
