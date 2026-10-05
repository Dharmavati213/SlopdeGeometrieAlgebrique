---
updated: 2026-10-03
---

# Translation pipeline

How the SGA 1 English was produced, so the next volume (or a review of SGA 2)
can reuse the method. The rules for the TeX itself are in
[`translation/CONVENTIONS.md`](../../translation/CONVENTIONS.md); this file
covers the steps around them. Edit in place and put your handle and the date on
changes.

## Source (claude-1003, 2026-10-03)

The French is never committed (`/source/` is gitignored; see
[`COPYRIGHT.md`](../../COPYRIGHT.md)). Fetch the SMF recomposition's
e-print from arXiv into `source/SGA<n>/SGA<n>_orig/`:

| Volume | arXiv | Body file |
| --- | --- | --- |
| SGA 1 | `math/0206203v2` | `smf_doc-math_3_01.tex` |
| SGA 2 | `math/0511279` | `smf_doc-math_4_01.tex` |

Translate the **corrected** branch: in `\ifthenelse{\boolean{orig}}{A}{B}`
(and SGA 2's `\sisi{A}{B}`) keep `B`. A misprint that survives in the
corrected branch is translated as printed and listed in the exposé's
README, not fixed.

## Chunk, translate, check, compile (claude-1003, 2026-10-03)

1. **Chunk.** Cut the body into pieces small enough for one agent (a section
   or two; SGA 1 used 33 chunks), by line range. The ranges are in
   `source/SGA1/chunks.txt` (`IV-1 6269 6828`, …), and the French pieces are in
   `source/SGA1/chunks/<Expose>-<k>.tex`. Each English piece becomes
   `translation/SGA1/Expose<N>/en-<k>.tex`.
2. **Translate** one chunk per agent, body fragment only, following
   `CONVENTIONS.md`.
3. **Check** structure mechanically:
   `source/SGA1/check_chunk.py FRENCH.tex ENGLISH.tex` compares labels,
   reference keys, citations, footnotes, diagrams, displayed equations and
   environments between the corrected French and the English, and flags
   leftovers that should have been dropped. Exit status 1 means look again.
4. **Compile** the fragment alone: `source/SGA1/compile_chunk.sh IX 2`
   (or `Front`). It prints TeX errors and the page count, and leaves a PDF
   you can read back with `pdftotext`. Undefined cross-references are
   expected in isolation.
5. **Second pass.** A different agent compares the chunk with the French
   sentence by sentence. The checker catches dropped labels, not dropped
   sentences.
6. **Whole volume.** `source/SGA1/coverage.py` compares labels, footnote
   counts and a rough word count per exposé against the French.
7. Build with `make -C translation/SGA1/Expose<N>` and update the exposé
   README (source line range, misprints, review state).

The scripts in steps 3, 4 and 6 exist only on the machine that ran the SGA 1
campaign, under the gitignored `source/`, with absolute paths. Getting them
into the repo is item 2 in [`priorities.md`](priorities.md). Until then, a
fresh clone has to rebuild them.

## Review state (claude-1003, 2026-10-03)

- SGA 1 I, II, III, VI: older English, compared sentence by sentence with
  the corrected French and fixed (2026-09-24).
- SGA 1 front matter, IV, V, VIII–XIII: translated chunk by chunk, each
  chunk re-checked by a second agent (2026-09-24). Scholarly proofreading
  still outstanding.
- SGA 2, all exposés: "Draft", with no recorded check against the French.
- SGA 3: French is the Gille–Polo PDF recomposition in gitignored
  `source/SGA3/` (no TeX); English is `translation/SGA3/`, one fragment per
  page range. Statement numbers are copied from the PDF
  (`\begin{proposition}{1.5.1}`). The October 2024 PDFs already include the
  errata lists; do not apply them again. Status: complete drafts, no
  independent sentence-level review yet.

## SGA 3 PDF pitfalls (2026-10-05)

- PDF text extraction loses coproduct signs, overbars, underlines and
  distinctions such as `G_L` versus `GL`. Render the page for notation;
  `pdftohtml -xml` shows glyph fonts and positions when rendering is ambiguous.
- Frobenius kernels in XV and XVII are a small left subscript, `{}_{F^n}(G)`,
  distinct from the relative Frobenius `F^n`; easily misread as Gothic `F_n`.
- Repeated footnote markers point to one note: keep the marker, print the
  text once. Starred notes and version note (0) offset the numbering.
- A statement that starts after a colon belongs to the page where it starts.
- Number suffixes can be uppercase (VIIB 5.2.4.A).
- Structural checks and a clean build do not catch a misplaced inverse in a
  dense identity (XVIII, Rule 4); only a second reader against the PDF did.

The per-exposé READMEs under `translation/SGA1/` also carry the table
"Found during the Lean formalization": places where SGA 1 is wrong or needs
an extra hypothesis, with the Lean declaration that proves the corrected
form. When a Lean agent finds one, it goes there.
