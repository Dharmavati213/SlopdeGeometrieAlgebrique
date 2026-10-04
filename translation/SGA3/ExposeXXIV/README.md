# SGA 3, XXIV

Automorphisms of reductive groups.

Author of the exposé: M. Demazure.

French source (local only): `source/SGA3/Exp24-13oct24.pdf` (54 pages),
the Gille–Polo recomposition.

| | |
| --- | --- |
| Status | Complete English draft; independent sentence-level review and scholarly proofreading remain outstanding. |
| Chunks | en-01.tex (pp. 1--8), en-02.tex (pp. 9--14), en-03.tex (pp. 15--20), en-04.tex (pp. 21--26), en-05.tex (pp. 27--32), en-06.tex (pp. 33--38), en-07.tex (pp. 39--46), en-08.tex (pp. 47--54) |

Typographical corrections made in the English are marked in the body
with `% typo:`. Build: `make -C translation/SGA3/ExposeXXIV`.

All eight fragments cover all 54 source PDF pages, including every statement,
proof, diagram, formula, editor note 0–50, the original starred note at 8.1,
and ten bibliography entries. The repeated marker for editor note 24 shares
one translated note body. The source numbering skips 8.1.1.

Validation (2026-10-04, codex-sga3-xxiv-xxvi): every French source page was
rendered and inspected. `make -C translation/SGA3/ExposeXXIV` succeeds
(43 main-text pages, 47 total); the source-heading/PDF gate
`check_coverage.py --expose XXIV --source-dir source/SGA3 --require-pdf` and
`git diff --check` pass. All 168 explicit labels are unique. English long
formulas, the equivalence/decomposition diagrams, long footnotes, appendix
and bibliography were inspected visually. No horizontal box overflow
remains; two vertical warnings of 1.61 pt and 1.79 pt have no clipping.
These checks are separate from independent mathematical/fidelity review.

Page boundaries are assigned by the starting page of each sentence.
Corollary 1.17 spans en-01/en-02; Proposition 3.13 spans en-03/en-04;
the proof of 4.2.4 spans en-04/en-05; Proposition 5.5 spans en-05/en-06.
The final sentence of en-02 ends on source p. 15; en-03 starts the next
sentence, “Reasoning as before ...”. All environments are closed at the
end of the exposé.

Apparent source slips retained verbatim and marked `% typo?:`:

- 1.0's transport-of-structure sentence changes G′ to G; section 2 calls
  X′ a subfunctor of G; 2.3 prints Isom(G,B;B′,B′).
- Editor note 18 prints A′ → product κ(s_i), with unprimed s_i.
  The conclusion of 3.11.4 calls the quasi-pinned group pinned.
- 4.2.3 reduces the “structure group of G” to T.
  5.9 prints the S-gr. subscript on Aut(G_0).
- In 6.2 the q=1 formula has ±x rather than ±xy, and the last q=3
  identity has E(1,x)E(1,−x). The proof of 6.3 cites 5.1 at its end.
  The bottom row of 6.6 has Aut(G), rather than Aut(B).
- The last sum in 7.1.4 has coefficient α(t)α(t′).
  Editor note 38 writes the fiber products over S.
  7.2.2 prints T′=T∩G, without a prime on G.
- 7.3.5 says G is semisimple where K appears to be intended, and its
  diagram has Z¹(G,h) in the bottom row.
- 7.4.3 retains its n=0 assertion and direction of conjugation;
  7.4.4–7.4.5 retain the entrywise n-th power formulas also for n=0.
- 8.1.3 calls Isom(P,Q) a sheaf of groups; the proof of 8.3 has
  unprimed P on the right; the final paragraph of 8.5 cites 8.2 while
  discussing a finiteness hypothesis absent from 8.2.

Obvious typography corrected with `% typo:` comments: the missing closing
parenthesis in the proof of 4.4.4, “H est lisse S” in 7.1.10, and the
publisher's visibly corrupted spelling Birkhäuser in the bibliography.
