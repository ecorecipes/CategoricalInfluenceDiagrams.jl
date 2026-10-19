.PHONY: build cache audit check-certificates docs mdgen html pdf clean

LIB := CategoricalInfluenceDiagramsProofs
TITLE := Open Influence Diagrams: Proofs
AUTHOR := Simon Frost
# Modules in import (dependency) order, as in $(LIB).lean.
MD_FILES := Basic.md RewardKernel.md Category.md Context.md Syntax.md Interpretation.md \
	Obstruction.md Lens.md Certificate/Record.md Certificate/Json.md Certificate/Exact.md \
	Certificate/Check.md Certificate/Sound.md
JULIAMONO_DIR := $(abspath ../../fonts/JuliaMono)/
PANDOC_COMMON := --toc --toc-depth=2 --syntax-definition=lean.xml --syntax-highlighting=tango \
	--metadata title="$(TITLE)" --metadata author="$(AUTHOR)" --metadata date="2026-10-18"

# Build the default target; must be sorry-free and warning-free.
build:
	lake build --wfail

# Fetch prebuilt Mathlib oleans (run once per Mathlib revision).
cache:
	lake exe cache get

# Reject missing audit results, axioms outside propext, Classical.choice and Quot.sound, and
# source proof escape hatches; then run the synthetic guard regressions of the driver.
audit:
	@mkdir -p .lake
	@lake env lean Audit.lean > .lake/audit.log 2>&1 || { cat .lake/audit.log; exit 1; }
	@cat .lake/audit.log
	python3 scripts/audit.py .lake/audit.log
	python3 scripts/test_audit.py

# Decode and check every reward-certificate fixture (ADR 0019) and compare each outcome with
# certificate-fixtures/EXPECTED.md: positives accepted, negatives rejected at the stated stage.
check-certificates:
	lake build check_certificate --wfail
	python3 scripts/check_certificates.py

# Documents: $(LIB).md (mdgen), $(LIB).html (pandoc) and $(LIB).pdf (pandoc + lualatex),
# generated from the checked Lean source and committed. Fonts: STIX Two Text/Math and
# JuliaMono from ../../fonts/JuliaMono.
docs: mdgen html pdf

mdgen:
	rm -rf .mdgen
	lake exe mdgen $(LIB) .mdgen
	@for f in $(MD_FILES); do \
	  printf '\n\n<!-- $(LIB)/%s -->\n\n' "$${f%.md}.lean"; \
	  perl -0pe 's/\A(```lean\n(?:import [^\n]*\n)+```\n\n)(\# [^\n]*\n\n)/$$2$$1/' .mdgen/$$f; \
	done > $(LIB).md
	rm -rf .mdgen

html: $(LIB).md
	pandoc $(LIB).md -o $(LIB).html --standalone --mathjax --css=style.css $(PANDOC_COMMON)

pdf: $(LIB).md
	printf '\\newcommand{\\JuliaMonoDir}{%s}\n' "$(JULIAMONO_DIR)" > .fonts.tex
	pandoc $(LIB).md -o $(LIB).tex --standalone $(PANDOC_COMMON) \
		-V papersize=a4 -V geometry:margin=2.2cm -V colorlinks=true -V linkcolor=NavyBlue \
		-V urlcolor=NavyBlue -V toccolor=black -H .fonts.tex -H header.tex
	lualatex -interaction=nonstopmode -halt-on-error $(LIB).tex > latex-first.log
	lualatex -interaction=nonstopmode -halt-on-error $(LIB).tex > latex-second.log
	@if grep -q "Missing character" $(LIB).log; then \
	  grep "Missing character" $(LIB).log; exit 1; fi
	@echo "PDF built with no missing-character warnings."

clean:
	rm -rf .mdgen .fonts.tex
	rm -f $(LIB).aux $(LIB).log $(LIB).out $(LIB).toc $(LIB).tex latex-first.log latex-second.log
