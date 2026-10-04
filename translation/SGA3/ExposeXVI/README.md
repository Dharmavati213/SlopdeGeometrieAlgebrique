# SGA 3, XVI

Groups of unipotent rank zero.

Author of the exposé: M. Raynaud.

French source (local only): `source/SGA3/Expo16.pdf` (24 pages),
the Gille–Polo recomposition.

| | |
| --- | --- |
| Status | Complete compiled draft; independent scholarly proofreading remains outstanding. |
| Chunks | en-01.tex (pp. 1--6), en-02.tex (pp. 7--12), en-03.tex (pp. 13--17), en-04.tex (pp. 18--22), en-05.tex (pp. 23--24) |

Typographical corrections made in the English are marked in the body
with `% typo:`. Build: `make -C translation/SGA3/ExposeXVI`.

All 24 source PDF pages were rendered and read. Every sentence, proof,
formula, diagram and note is translated. The starting-page rule puts the
final sentence, begun on p. 22 and finished on p. 23, in en-04; p. 24 is
blank. Consequently en-05 contains only documented `\relax`, with no
printed text or duplication.

`make` and `check_coverage.py --expose XVI --source-dir source/SGA3
--require-pdf` pass. The PDF has 21 physical pages (17 body pages), all of
which were rendered and inspected, and 33 labels. The version note 0,
original starred author note, and editor note 1 are retained. There are
no box warnings or clipping. `git diff --check` passes. Structural coverage
does not certify sentence-level or mathematical fidelity.

Clear typography corrected, with body comments: missing outer closing
parentheses in 1.1(a) and 1.4(b), the extra closing parenthesis in the proof
of 1.8, `S-groupes. sorte que` in 2.4, and `on pout supposer` in 4.2.

Mathematical or uncertain source slips retained as printed:

- 1.6(ii) includes every positive n in the finiteness criterion; 1.6(iii)
  includes every positive invertible q. The proof of 1.7 says n-th power
  before the q-kernel sequence; the proof of 1.6(iii) cites `1.6 b)`.
- The proof of 1.9 says `F_t` contains the schematic closure in V;
  the proof of 1.10 labels its third part c); the proof of 1.3(b) cites
  `1.2 a)` and `EGA IV 15.5`.
- The proof of 2.2 prints `G ×_S G` as the first projection's domain;
  the proof of 2.4 calls a group over T of finite presentation over S.
- The proof of 3.2 prints `G ×_T H`; the density argument in 3.5 prints
  `i(S')` and the kernel subscript `n m_0`; the nonflat-center example
  prints `(t,u),(t,u')` on the left of the composition law.
- The proof of 4.1(d) cites `3.5 b)`; 4.2 assumes dimension 1;
  6.3 gives G, rather than H, in its local finite-type alternative;
  the proof of 6.4 calls V an open subset of T although the map has
  domain `T^N`.
