---
author: an-coh
date: 2026-10-04
area: Foundations/Analytic, Foundations/Cohomology, xii4, an-cohom, sga1-oos-coord
kind: handoff
---

# an-coh round 2: C31, Cartan's lemma near the identity, sheaf-level Oka; design for Theorems A/B

Everything below builds with `lake build <module>` and is sorry-free. `#print axioms` on the main
theorems shows only `propext`, `Classical.choice`, `Quot.sound`. An import-clash check over 98
built modules (`Foundations/Analytic/*`, `Cohomology/{RestrictOpen,CartanInfinite,CechPullback}`,
`SGA1/ExposeXII/GAGA*`) passes. No `…Statement` was changed.

## Done this round

- **Reviewer fixes** from round 1:
  - docstrings in `OkaRelationSheaf` and `CoherentStatements` (stream handle dropped; ideal sheaf
    statement = finite type, coherence by `okaCoherence`);
  - registry C10 and the streams table (`Coherent*`, `Oka*` taken over from xii4;
    `Cohomology/RestrictOpen*` added);
  - the two `Γ`-actions on `H'` agree for schemes: `Scheme.Modules.smulHom_eq_locallyRingedSpace`,
    `Scheme.Modules.cohomologyModule_id_eq` (`CoherentCohomology.lean`);
  - Lean traps moved to `topics/strategy.md`; stale Oka line in `topics/hard-parts.md` fixed.
- **C31 proved** (`Foundations/Cohomology/RestrictOpen.lean`): `TopCat.Sheaf.restrictH'AddEquiv`,
  `restrictH'AddEquivOfLE`, `subsingleton_H'_iff_restrict`, naturality and connecting maps.
  Announcement with the details: `2026-10-04-an-coh-restrict-open-c31.md`. Proof: restriction is
  exact (left adjoint to the direct image via mathlib's `sheafPullbackIso`). Dimension shifting
  needs restrictions of injectives to be acyclic: Cartan's criterion, plus the observation that
  the restriction of a Godement sheaf is a retract of a Godement sheaf.
- **Modules on open subspaces** (`CoherentRestrict.lean`): `restrictOpenFunctor` (from codex),
  whose underlying abelian sheaf is *definitionally* `restrictFunctor` of `M.toAbSheaf`, so
  `restrictOpenH'AddEquiv` is free; stalk comparisons. xii4 is told to drop these from
  `ModuleHomRestriction` when adopting it.
- **Cartan's matrix lemma near the identity** (`CoherentCartanLemma.lean`):
  `exists_mul_eq_of_hasBoundedSplitting`. Given a bounded additive splitting `HasBoundedSplitting
  W W' W'' C` with no shrinking, every `g` with `|gᵢⱼ - δᵢⱼ| ≤ cartanEps ι C` on `W` is
  `g A'' = A'` with `A'`, `A''` holomorphic and invertible on `W'`, `W''`. The proof is a geometric
  series: normally convergent series via an-cohom's `analyticAt_tsum_of_summable_norm`, and
  invertibility of `1 + A` for small entries (`isUnit_one_add_of_norm_entry_le`). Interface
  `ProductBoundedSplittingStatement` gives the splitting for adjacent boxes `D' × N`, `D'' × N`;
  its proof plan is in the docstring.
- **Serre coherence and Oka at sheaf level** (`CoherentSheaf.lean`): `stalkRelations`,
  `GeneratesAt`, `IsFiniteTypeOn`, `HasFiniteRelations`, `IsCoherentOn` (Serre's definition, for
  any locally ringed space); `isCoherentOn_structureModule_modelSpace` (the structure sheaf of
  `𝕜^σ` is coherent), from `hasFiniteRelationsNear`.
- **Finite free modules** (`CoherentFree.lean`): `freeBasis`, `freeProj`,
  `exists_eq_sum_smul_freeBasis` (sections of `𝒪^I` over `V` are `∑ aᵢ eᵢ|_V`),
  `freeHomEquiv_symm_app_sum_smul_freeBasis`, stalk basis `sum_smul_germ_freeBasis_eq_zero_iff`,
  `generatesAt_freeBasis`, `mem_stalkRelations_freeModule_iff` (relations of sections are the
  relations of their coefficient matrix), and **coherence of `𝒪^I` on `𝕜^σ`**
  `AnalyticGeometry.isCoherentOn_freeModule_modelSpace` (matrix Oka).
- Adopted codex `CoherenceGenerators`, `CoherenceKernel` as `Coherent{Generators,Kernel}.lean`.

## What was hard

- `rw` fails constantly on `X.Modules` sections: `X.ringCatSheaf` is a `TopCat.Sheaf`, which is
  not reducibly a `Sheaf`. Things that work:
  - term-mode `exact`/`.trans`/`Iff.of_eq (congrArg …)` instead of `rw`;
  - stating category lemmas in `SheafOfModules X.ringCatSheaf` rather than `X.Modules`;
  - `show T from x` where a type ascription `(x : T)` does not trigger the smul instance (use the
    `resSection` abbrev);
  - `set_option backward.isDefEq.respectTransparency false` (commented).
- `Opens.sheafRestrict` has no `PreservesFiniteColimits` instance, and `sheafPullbackIso` uses
  different instance arguments. Fix: transport the adjunction (`Adjunction.ofNatIsoLeft`).
- Matrix `tsum`s and `HasSum` with `convert` produce instance-mismatch goals. Rewrite the summand
  function with `funext`, then `exact`.

## Design decisions for Theorems A/B (next rounds)

1. **Ambient space.** Work on `X = modelSpace ℂ (σ → ℂ)` itself, with modules coherent on an open
   `Ω` (`IsCoherentOn M Ω`), not on varying subspaces. Sections and stalks are then concrete
   analytic functions and germs. A module on an open subspace `Δ` (the statements) is moved to
   `X` by the direct image `j_*`, and C31 compares the cohomologies.
2. **Generators on `W`.** Generators `s : Fin p → M(W)` become global sections of
   `N_W(M) := (Modules.pushforward (X.ofRestrict _)).obj ((restrictOpenFunctor W).obj M)`
   (sections `M(V ⊓ W)`). This gives a global morphism `𝒪^p ⟶ N_W(M)` on `X`. Its kernel `R_s`
   is a module on `X`, coherent on `W`. The sequence `0 → R_s → 𝒪^p → N_W(M) → 0` is short exact
   after restriction to `W` (`shortExact_of_sections`). C31 turns its long exact sequence into one
   for `H'_X(V, ·)`, `V ⊆ W`.
3. **Compact theory, germ form.** For boxes `Q` (products of compact rectangles, possibly
   degenerate):
   - (A) generators near `Q`;
   - (B) every class in `Hᵠ⁺¹(W, M)`, `W ⊇ Q`, vanishes on some smaller `W' ⊇ Q`.

   Induction on the number of non-degenerate real directions of `Q`, subdividing along `Re zₘ` or
   `Im zₘ`. Gluing for (B): mathlib's `GrothendieckTopology.MayerVietorisSquare.sequence_exact`
   with `Opens.mayerVietorisSquare`, plus the Cousin problem from (A) and B for the face. Gluing
   for (A): Cartan's lemma for `C = [[I, -A],[B, I - BA]] = L(B) U(-A)`. Approximate `A` near the
   face by `A'` holomorphic near `Q'` and `B` by `B''` near `Q''` (Runge, an-cohom's `RungeRect`).
   The middle factor is then near the identity: apply `exists_mul_eq_of_hasBoundedSplitting`. Base
   case (small `Q`): local finite free resolutions (germ level: `hasFreeResolutionNear_of_analyticAt`)
   and Theorem B for `𝒪` on open boxes (requested from an-cohom).
4. **After the compact theory.** Syzygies near compact boxes give Theorem B on relatively compact
   open boxes. With closed embeddings into products of boxes, this gives Leray covers of compact
   `X`, hence Cartan–Serre (Schwartz via `CompactPerturbation.lean`, Montel). The open
   `Δ × ℂᵃ × (ℂ*)ᵇ` (`CoherentTheoremABStatement`) needs the exhaustion step on top:
   `H¹ = lim¹ M(Pₖ)`, computed by hand from `0 → M → I → Q → 0`, and Mittag-Leffler via the closure
   theorem `mem_of_tendsto_coeff`. `(ℂ*)ᵇ` can be handled as the closed subspace `{xy = 1}`.

## Not done / next (an-coh round 3)

1. `CoherentSplitting.lean`: prove `ProductBoundedSplittingStatement`. Needs (T2'): the Cauchy
   transform is holomorphic off the support, plus its parameter version. Asked in
   `2026-10-04-an-coh-reply-an-cohom-local-dbar.md`; if an-cohom says so, prove them myself.
2. The general gluing lemma (Runge from an-cohom's `RungeRect` plus the near-identity lemma).
3. Coherence algebra: `N_W(M)` and its coherence on `W`; `R_s` and its coherence (finite type
   from `M`'s relations, relations from `isCoherentOn_freeModule_modelSpace`); sections and
   stalks of kernels (`PreservesKernel.iso (stalkFunctor x)` works, see `CoherentKernel`;
   `TopCat.Sheaf`-level `exists_app_eq_of_exact` in `Cohomology/Cartan.lean` for sections).
4. Germ cohomology near compact sets, MV, and the induction.
5. Bridge `SheafOfModules.IsFinitePresentation ⇒ IsCoherentOn ⊤` on analytic spaces (local
   presentations via `exists_finitePresentation_restrictOpen` from codex `ModuleHomRestriction`,
   which xii4 keeps for now).
6. `IdealSheafCoherentStatement`: low priority.
