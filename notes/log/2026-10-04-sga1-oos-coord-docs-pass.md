---
author: sga1-oos-coord
date: 2026-10-04
area: SGA1 IX X XI XII XIII, Foundations README, docs, out of scope
kind: experience
---

# Documenting wave 1: three checker passes found about 70 inaccurate claims

After the integration (`2026-10-04-sga1-oos-coord-wave1-integrated.md`), the out-of-scope table
in `lean/SGA/Foundations/README.md`, the IX–XIII rows of `docs/formalization.md`,
`docs/status.md` and the five exposé barrel docstrings were rewritten, then checked claim by claim
against the Lean by adversarial agents, fixed, and rechecked.

What the checkers caught, so the next writer avoids it:
- **Dropped hypotheses** were the most common error: `k` algebraically closed where SGA has
  separably closed, characteristic 0 and `#k ≤ 𝔠`, universe 0, locally noetherian, "existence part
  only" (XIII.5.5), "Galois" (prime-to-`p` coverings are tame only when Galois).
- **Wrong attribution**: one theorem cited for three cases (XIII.2.12 on `ℙ¹`), LPC credited to
  semialgebraic geometry (it uses branched coverings; only SLSC uses Tarski–Seidenberg).
- **Mathematical slips in prose**: my "a meromorphic function with one simple pole" (the theorem
  gives one pole of negative order; a single simple pole exists only in genus 0); "a smooth
  unirational variety is simply connected" without "proper" (𝔾_m is a counterexample).
- **Forecasts written as results**: "XIII.4.6 needs no resolution of singularities" is a route,
  not a theorem, while `AffineLineOpenInvarianceStatement` is open.
- **Statements left unnamed**: open `…Statement`s covered by a row's content but not named in it.

New in this pass: `SGA/SGA1/ExposeXII/StatementCorollaries.lean` proves three statements that had
become one-liners (`coveringFundamentalGroupStatement`, `separatingFunctionStatement`,
`Points.closureComparisonStatement_zero`). `RelativeAbhyankarStatement` is listed as in-scope open
work (docs/formalization.md); `HenselianEtaleCoveringsOfClosedFibreStatement` (SGA 4 XII 5.5) sits
in the out-of-scope XIII 1.4 row.

Final state: `lake build` 6368 jobs, `CheckSGA1Axioms.lean` 30067 declarations, no `sorry`.
Nothing committed.
