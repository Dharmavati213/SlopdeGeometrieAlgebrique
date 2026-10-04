---
author: sga1-oos
date: 2026-10-03
area: SGA1 X, XI, XII, XIII, Foundations README, out of scope
kind: handoff
---

# The out-of-scope SGA 1 items: XI.2.1 done, triage of the other eleven

The user asked to formalize the results listed as out of scope in
`lean/SGA/Foundations/README.md` (plus GAGA). I stopped for the day at the user's request after
one proof and a triage. Branch `formalization/sga1-out-of-scope`, committed locally, not pushed.

**Done.** XI.2.1's key step (`SerreLangStatement`) is proved without abelian-variety theory
(`serreLangStatement`, `lean/SGA/SGA1/ExposeXI/SerreLang.lean`; see
`2026-10-03-sga1-xi21-serre-lang.md`). README, docs and docstrings updated. SGA's XI.2.1 proper,
`π₁(A) ≅ lim_n K_n`, is still unstated (a canonical form typechecks in the triage scratch).

**Triage.** For each item one agent proposed routes and one critic tried to refute them. Full
JSON and the scratch Lean drafts (65 files, several of them compiled) are outside git, in
`~/.claude/projects/-home-site-Projects-SlopdeGeometrieAlgebrique/sga1-oos-triage-2026-10-03/`.
Estimates are the critics' revised ones. Verify before relying on them.

| Item | Verdict | First session worth doing |
| --- | --- | --- |
| X.2.9 | large, ~25k for all `k` | **Misclassified.** Over ℂ only the easy half of XII.5.2 is needed (π₁^et is a quotient of the completion of π₁^top, from XII.2.4 `connectedComparison` + V.6.9), not Riemann existence. Phase 1 (~2k): X.2.9 and X.2.12 for smooth proper `X` over ℂ, unconditionally. Char `p` needs curve lifting and the reduction to curves (X.2.10/2.11, Noether finiteness). |
| XI.1.4 | research-scale (Hodge symmetry) | Route E (~9–11k, 2–3 sessions): χ(𝒪) multiplicative in finite étale covers (no Riemann–Roch needed; dévissage), no regular forms on unirational `X`, étale covers of unirational are unirational, then XI.1.4 from a faithful `HodgeSymmetryZeroStatement`. |
| XII.5.1 | research-scale, ~80k | Session 1 (~5k): full faithfulness of Ψ, surjectivity of π̂₁(X(ℂ)) onto π₁^et(X), Riemann existence for 𝔸ⁿ, scheme-from-affine locality. The analytic heart (compact Riemann surfaces are algebraic) is 18–25k, with no Montel, Čech or ∂̄ in mathlib. |
| XII.5.2 singular | large, ~28k for the statement as written | **SGA only needs local path-connectedness + semilocal simple connectedness**, not strong local contractibility. Session (~3k): refactor to those, prove LPC for all `X` and the curve case, which gives XII.5.2 for singular curves from XII.5.1. |
| XII.4 GAGA | research-scale, ~75k | Not stated at all. Doable now: XII.3.1 (i)–(iv) via local rings (~2k); non-affine `X^an` by `LocallyRingedSpace.GlueData` for separated `X` (~3k); `(X^an)_red` = the existing reduced model, from the proved Rückert (~300). Theorem B on polydiscs and Oka coherence are the long poles. Stating XII.4.2 also needs `Rᵖf_*` sheaves, on both sides. |
| XIII 1.4 | large, ~15k (noetherian `Y`), ~22k in general | Staged route A (Stacks 0A3U chain, Gabber's H⁰): start with dim ≤ −1 for universally closed `f` (~1.7k), which makes XIII 1.8 dim ≤ −1 unconditional. A general `Y` needs absolute noetherian approximation. |
| XIII.4.3/4.4 | needs X.3.8 | Cheap pieces now (~1k, partly compiled in scratch `XIII.4.3-4.4/Group.lean`). Add `TameLiftingDVRStatement` as the X.3.8 target. The regular-base version (~5–8k) follows from it plus X.2.1. The critic says X.2.1 for normal proper `X` is ~0.5k from `formalAlgebraizable_of_stein` + Chow. |
| XIII §3 | needs PBC + SGA 4 XV, ~95k | Faithful statements (desingularization as a hypothesis, as in SGA), plus the finite and étale cases (~3k). |
| XIII.4.6 char 0 | large, ~15k | **Misclassified.** A resolution-free algebraic route exists: the Kummer cover for opens of 𝔸¹, a generic-fibre main lemma, induction on transcendence degree, then descent. The README's "needs Hironaka" is SGA's route, not a necessity. |
| XIII.2.13 | research-scale (Raynaud also needs Riemann existence) | Partial result (~1.5k, one session): every finite `p`-group is a quotient of π₁(𝔸¹_k), any `k` of char `p`. The two algebraic cores compile in scratch (`XIII.2.13/Theta.lean`, `Cocycle.lean`). |
| XIII.2.12 | research-scale, ~100k | Faithful statements compile in scratch (`XIII.2.12/Statement.lean`). `g = 0`, `n = 2` (π₁^{p'}(𝔾_m)) by the lattice method is ~3–4.5k. |

**Next**, in my order: the one-session items (XIII.2.13 `p`-groups, X.2.9 Phase 1, XII.5.2 LPC
refactor, XII.3.1 (i)–(iv), XIII.4.3/4.4 cheap pieces, XIII 1.4 dim ≤ −1). Then correct the
README rows for X.2.9, XII.5.2 and XIII.4.6 once the routes are proved, not before.
