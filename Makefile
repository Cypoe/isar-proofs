# Makefile for the ISAR mathematical stack, proofs, and website compilation

.PHONY: all lean check papers web jekyll clean help

all: lean check papers web jekyll

help:
	@echo "Available targets:"
	@echo "  lean     - Build the Lean 4 proof modules (lake build)"
	@echo "  check    - Validate that LaTeX blueprint matches Lean declarations"
	@echo "  papers   - Compile all 3 papers + the monograph PDF via Docker and copy to home_page"
	@echo "  web      - Build the interactive web blueprint (plasTeX)"
	@echo "  jekyll   - Build the Jekyll project home page"
	@echo "  all      - Build all targets (lean, check, papers, web, jekyll)"
	@echo "  clean    - Clean up build and LaTeX auxiliary files"

lean:
	lake build

check:
	lake exe checkdecls blueprint/lean_decls
	leanblueprint checkdecls

papers:
	docker run --rm -v "$(CURDIR):/doc" -w /doc/blueprint/src texlive/texlive latexmk print.tex print_paper_b.tex print_paper_c.tex print_monograph.tex
	python -c "import shutil; shutil.copy('blueprint/src/print.pdf', 'home_page/paper_a.pdf')"
	python -c "import shutil; shutil.copy('blueprint/src/print_paper_b.pdf', 'home_page/paper_b.pdf')"
	python -c "import shutil; shutil.copy('blueprint/src/print_paper_c.pdf', 'home_page/paper_c.pdf')"
	python -c "import shutil; shutil.copy('blueprint/src/print_monograph.pdf', 'home_page/blueprint_monograph.pdf')"

web:
	cd blueprint && plastex -c plastex.cfg src/web.tex

jekyll:
	cd home_page && bundle exec jekyll build

clean:
	lake clean
	cd blueprint/src && latexmk -C
	python -c "import glob, os; [os.remove(f) for ext in ('*.bbl', '*.blg', '*.run.xml') for f in glob.glob('blueprint/src/' + ext)]"
	python -c "import shutil; shutil.rmtree('home_page/_site', ignore_errors=True)"
