---
author: codex-sga3-xv-finish-xvi
date: 2026-10-05
area: SGA3 translation, XVII, XV, codex-sga3, codex-sga3-xxv-xxvi
kind: experience
---

# XVII pp. 37–50 complete; Frobenius kernel typography corrected

Completed only XVII/en-07–en-08, preserving all prose, formulas, diagrams,
editor notes 11–13, and inline bibliographic references. All source pages
37–50 rendered/read; p. 50 is blank. 32 labels added, no formal bibliography.
Source p. 37 first words complete the U'_1 lifting sentence owned by en-06;
en-07 starts “Proceeding as in the proof of 6.2.4 ...”. The en-06 worker
confirmed this exact ending, no open environment, and note counter 10.

The cumulative make passed with en-01–en-04 and the tail (33 physical pages);
all English physical pp. 23–33 rendered/inspected. Widened Frobenius and
restriction-of-scalars diagrams and separated arrow labels. No horizontal
overflow or clipping. The final kernel-notation QA used an isolated /tmp
wrapper while the middle worker populated en-05–en-06: ten tail pages,
all inspected, one harmless 1.87pt vertical warning on a footnote page.
The full source/PDF gate belongs to the original XVII owner after the
middle worker's build; tail headings had no missing labels in the partial gate.
Diff checks pass. No README, wrapper, style, commit, PR or French staging.

Retained source slips: 7.3.2 prints x^(ell^n)=0 in multiplicative notation;
A.2 prints pushout morphism (f,i) without a minus sign; A.3 omits the second
component gg' of the pair product; C.5 proof heading says “Proposition 5.1”.
One clear typo fixed/commented: missing closing parenthesis after X 4.8 b).

Critical typography: the small F before kernel groups is a LEFT subscript
with the iterate exponent on F: `{}_{F^n}(G)`, and `{}_{F}G` for n=1.
It is neither ordinary F_n nor Gothic F. Original XVII owner verified font
sizes/positions against source XML; high-resolution scans confirm it.
Relative Frobenius morphisms remain F^n. Aligned en-07 and also corrected
my earlier XV/en-08. XV rebuilt: full gate passes, now no overfull boxes;
its README updated. This supersedes the earlier log's harmless 1.9pt warning.

Build lock released to the middle worker, whose cumulative error had been
in en-05:56. No other worker's file edited. Root requested release of slot;
stopping with all owned fragments complete. Scholarly proofreading remains.
