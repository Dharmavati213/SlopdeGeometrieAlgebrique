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
- SGA 3 (sga3-en, 2026-10-04): French is the Gille–Polo PDF recomposition
  in gitignored `source/SGA3/` (no TeX). English tree is
  `translation/SGA3/`. Each piece is a page range, checked against
  the PDF, then compiled. Statement numbers are copied
  from the PDF (`\begin{proposition}{1.5.1}`), because the numbering is
  not one LaTeX counter. Tome 1 and tome 3 PDFs dated October 2024
  already include the errata; do not apply those lists again.

## SGA 3 PDF checks (codex-sga3, 2026-10-04)

- A numbered statement following a colon belongs to the page where the
  statement starts. Treating it as the preceding sentence duplicated II.3.11.3.
- Repeated note markers are not repeated note text. I notes 24 and 26, II notes
  38 and 49, and IV note 57 refer more than once to one editorial footnote.
  Preserve the repeated marker and print its text once. Check the actual counter:
  starred original notes and version note (0) can offset ordinary numbering.
- PDF text extraction loses coproduct signs, overbars, underlining, and even
  distinctions such as G_L versus GL. Render the relevant pages for the notation.
- In XVII, the extracted `Fn(G)` is the left-subscript kernel notation
  `{}_{F^n}(G)`, with n a superscript on the small F; it is distinct from the
  relative Frobenius morphism `F^n`. When rendering is ambiguous, `pdftohtml
  -xml` exposes the glyph fonts and positions: here F is CMR7 and n is CMMI5,
  not a Gothic letter (codex-sga3-xxvi-finish-xvii, 2026-10-05).
- translation/SGA3/check_coverage.py and manifest.json provide a portable
  inventory and structural gate. Source heading coverage, note counts, and a
  successful build remain separate from sentence-level and mathematical review.
- amsbook chapter* already writes a contents entry; do not add it again.
  Manual section headings need a fresh hyperlink anchor. The combined SGA3 book
  uses chapterbib cbunit to keep repeated bibliography keys local to each exposé.

- Frobenius kernels in XV/XVII use a small LEFT subscript, `{}_{F^n}(G)`
  (or `{}_{F}G`), while the relative Frobenius morphism is `F^n`. The small
  roman F and the smaller exponent are easily misread as Gothic F_n.
  Check font size and position as well as rendered glyph shape; source XML
  can resolve this ambiguity (codex-sga3-xv-finish-xvi, 2026-10-05).
- Number suffixes can be uppercase (VIIB 5.2.4.A); preserve their case in
  source-heading extraction. Source ranges with no sentence beginning there
  can legitimately have no printed text (XVI pp.23–24); document the reason
  and use a no-op fragment rather than duplicating a continuation.
- When several translators share an exposé, designate one latexmk build owner.
  Its auxiliary files and cached diagnostics are shared; simultaneous builds
  can interfere even when fragment edits are disjoint. This was observed while
  finishing XVII (codex-sga3, 2026-10-05).
- Compare inverse positions independently in dense identities: XVIII Rule4
  passed structural checks and compilation with a misplaced inverse, caught
  by a second reader of source pp.7–12 and corrected before delivery
  (codex-sga3, 2026-10-05). Keep translator checks and independent review
  explicitly distinct in the README.

The per-exposé READMEs under `translation/SGA1/` also carry the table
"Found during the Lean formalization": places where SGA 1 is wrong or needs
an extra hypothesis, with the Lean declaration that proves the corrected
form. When a Lean agent finds one, it goes there.
