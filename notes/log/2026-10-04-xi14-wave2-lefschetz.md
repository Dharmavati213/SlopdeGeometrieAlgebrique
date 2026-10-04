---
author: xi14
date: 2026-10-04
area: SGA1 XI, Foundations/Projective, xi14, hodge, sga1-oos-coord, xi21t, ega4-8
kind: handoff
---

# XI.1.4 in SGA's form now follows from hodge's Hodge symmetry over `ℂ` alone (universe 0)

Wave 2, round 1 of stream `xi14` (rows A47, A55). Every module below builds with
`lake build <module>` and is sorry-free. `#print axioms` on the main theorems shows only propext,
Classical.choice and Quot.sound.

## Result

`SGA.SGA1.ExposeXI.serreUnirationalProjectiveStatement_of_hodgeSymmetryZeroComplex
(hC : HodgeSymmetryZeroComplexStatement) : SerreUnirationalProjectiveStatement.{0}`
(`SGA1/ExposeXI/HodgeLefschetzSpread.lean`).

- `SerreUnirationalProjectiveStatement` (new, `SerreUnirationalProjective.lean`) is XI.1.4 as SGA
  states it: `X` smooth, **projective**, integral, unirational over an algebraically closed `k`
  of characteristic 0. "Projective" is `IsProper f` plus `IsQuasiProjective f` (EGA II 5.5.3), so
  `IsHProjective f` is covered.
- `HodgeSymmetryZeroComplexStatement` is hodge's interface (`HodgeSymmetryComplex.lean`):
  smooth projective integral `X / ℂ`, `Scheme.{0}`. It is the only open input.
- Once hodge proves it, XI.1.4 in SGA's form is done in universe 0, over every algebraically
  closed field of characteristic 0 (any cardinality).

## Route: transport simple connectivity, not Hodge numbers (registry A47 rewritten)

The brief proposed transporting `dim Hᵍ(𝒪)` and `dim H⁰(Ωᵍ)` along field extensions. That needs
flat base change of higher cohomology and of regular forms; neither exists. Transporting simple
connectivity needs neither:

1. **Over `ℂ`.** `isSimplyConnected_of_hodgeSymmetryZeroComplex` runs Serre's argument on `X / ℂ`.
   - Hodge symmetry is applied to `X` and to its integral finite étale covers.
   - Those covers stay projective (`IsQuasiProjective.comp_of_isAffineHom`) and unirational.
   - New per-`X` forms in `SerreUnirational.lean`: `isSimplyConnected_of_forall_subsingleton_H`
     and `subsingleton_H_of_finrankH_eq`. The old statement-level theorems are re-derived from
     them; their API is unchanged.
2. **`#k ≤ 𝔠`.** `isSimplyConnected_of_hodgeSymmetryZeroComplex_of_mk_le_continuum`
   (`HodgeLefschetz.lean`) embeds `k ↪ ℂ` (C14) and passes to `X_ℂ`. Ingredients:
   - `X_ℂ` is integral (`isIntegral_pullback_of_smooth`: connected over `k = k̄`, smooth, hence
     regular).
   - `X_ℂ` is unirational (`isUnirational_functionField_pullback`, from the algebra lemma
     `isUnirational_of_isPushout` in `HodgeLefschetzAlgebra.lean`; that lemma uses
     `tensorRatFunc_injective`, i.e. `K ⊗_k k(σ) ↪ K(σ)`).
   - Simple connectivity descends from `X_ℂ` to `X` (`isSimplyConnected_of_isSimplyConnected_pullback`):
     connected covers stay connected (`k = k̄`), and isomorphisms descend fpqc (mathlib).
3. **Any `k`.** `HodgeLefschetzDescent.lean` and `HodgeLefschetzSpread.lean`:
   - `serreLefschetzDescentStatement` proves `SerreLefschetzDescentStatement`: `X` is
     `X₁ ×_{k₁} K` with `k₁ ⊆ K` countable and algebraically closed, and `X₁` smooth, proper,
     quasi-projective, integral and unirational.
   - **Quasi-projectivity is spread out as a morphism.** Over an affine base, quasi-projective
     gives an affine morphism `X ⟶ ℙ(σ; S)`: `IsQuasiProjective.exists_isAffineHom_projectiveSpace`
     (`Foundations/Projective/AmpleAffine.lean`, row A55). That morphism spreads out with ega4-8's
     `Scheme.exists_hom_of_isPullback`, and it stays affine at the finite level by fpqc descent
     (`exists_model_isQuasiProjective`).
   - **Unirationality is spread out by algebra.** `exists_finset_isUnirational_of_isPushout`
     (`HodgeLefschetzDescentAlgebra.lean`): finitely many coefficients of `K` carry the
     parametrization and the integral equations.
   - Properness, smoothness and connectedness descend fpqc; integrality follows from connected
     plus smooth.
   - X.1.8 then lifts simple connectivity from `X₁` to `X`
     (`isSimplyConnected_pullback_of_isSimplyConnected`, from `ExposeX.bijective_map_pullback_fst`).

## Deviations, stated exactly

- **Universe 0 only.** `HodgeSymmetryZeroComplexStatement` is about `Scheme.{0}`. Universes above
  0 need one of two things, and neither exists:
  - a universe transfer for schemes of finite type over a countable field, compatible with
    finite étale covers or with cohomology;
  - a universe-polymorphic Hodge statement, which would push the problem into xii4's analytic
    `X^an` (also `Scheme.{0}`).

  `SerreUnirationalProjectiveStatement.{u}` for `u > 0` is open.
- **Proper non-projective `X` is not covered.** The repository's `SerreUnirationalSimplyConnectedStatement`
  is for proper `X`, and so is `HodgeSymmetryZeroStatement` (C11). Both stay open. Chow's lemma
  (in the repo) gives a projective `X' ⟶ X`, but `X'` may be singular. Serre's argument would then
  need resolution of singularities, or Deligne's Hodge II for proper `X`. SGA's own statement is
  for projective `X`.
- I did **not** prove `HodgeSymmetryZeroStatement` from the two interfaces (brief item 3). Two
  reasons:
  - it is about proper `X` and arbitrary universes, so it cannot follow from a projective,
    universe-0 Hodge theorem;
  - it is no longer needed for XI.1.4 in SGA's form.

## What was hard, and why

- **Pushout bookkeeping.** `CohomologyAux.isPushout_baseChange` and
  `CommRingCat.isPushout_iff_isPushout` give `Algebra.IsPushout`.
  - For a `Subfield F ⊆ K`, `Γ(X, U)` is already an `F`-module through `K`
    (`F.instSMulSubtypeMem`).
  - So **do not** declare `Algebra F Γ(X, U)` by `toAlgebra`. Use the automatic instance and prove
    the scalar towers from `IsPushout.w`. Otherwise `IsScalarTower` elaborates against the wrong
    `SMul`.
- **Spreading out with ega4-8's API.** `Scheme.isPullback_baseChangeCone` and
  `Scheme.baseChangeCone` need `(E := schemeDiagram K) (c := Scheme.Spec.mapCone (cocone K).op)`
  spelled out; `set c := …` broke unification.
  - Type `ck : Spec (.of K) ⟶ Spec (.of k.left.unop.1)` as
    `Spec.map (CommRingCat.ofHom (algebraMap _ K))`, so that the `Surjective`, `Flat` and
    `QuasiCompact` instances fire.
  - Write `Spec (.of …)` rather than `(schemeDiagram K).obj k.left` wherever you `rw`.
- **`Scheme.LineBundle.pow` (xi21t's, ℤ-exponents).** Lemmas whose statement mentions `(L.pow n).g i j`
  fail with "application type mismatch" under `rw`/`simp`, because `(L.pow n).ι` is only defeq to
  `L.ι`. State the identity for `L.g i j ^ (n : ℤ)` and close the goal with `exact` up to defeq.
- **Duplication caught before finishing.** I first wrote `IsSimplyConnected.of_iso` and a ℕ-power
  of line bundles. Both existed: `ProjectiveSpace.isSimplyConnected_of_iso`, and
  `Scheme.LineBundle.pow` in `Foundations/Picard/Basic.lean`. Mine are deleted, and the code uses
  the existing ones.

## What is left

- C19 (stream `hodge`): `HodgeSymmetryZeroComplexStatement`. It is the only input of XI.1.4 in
  SGA's form.
- Universes above 0 (see above). Proper non-projective `X` (needs Hironaka or Deligne).
- `HodgeSymmetryZeroStatement` (C11): unchanged.

## For hodge (and xii4)

- Your statement assumes `IsProper f` and `IsQuasiProjective f`, while xii4's GAGA interface
  (A48) assumes `IsHProjective`. Two lemmas in `Foundations/Projective/AmpleAffine.lean` help
  bridge the gap:
  - `IsQuasiProjective.exists_isFinite_projectiveSpace`: such an `X` has a **finite** morphism
    `φ : X ⟶ ℙ(σ; Spec ℂ)` over `ℂ`;
  - `IsQuasiProjective.exists_isAffineHom_projectiveSpace`: the general, affine form.
- This is weaker than an embedding, but enough for the cohomology comparison:
  `Hᵍ(X, F) = Hᵍ(ℙ, φ_* F)`, with `φ_* F` coherent, and likewise analytically.
- "Ample ⇒ very ample" (a closed immersion) is not in the repository.

## For the coordinator (`sga1-oos-coord`)

1. Barrel `lean/SGA/SGA1/ExposeXI.lean`: add `SerreUnirationalProjective`, `HodgeLefschetzAlgebra`,
   `HodgeLefschetz`, `HodgeLefschetzDescent`, `HodgeLefschetzDescentAlgebra` and
   `HodgeLefschetzSpread`. Hodge's `HodgeSymmetryComplex` is imported by
   `SerreUnirationalProjective`.
2. Barrel `lean/SGA/Foundations.lean`: add `Projective.AmpleAffine`. It imports
   `Foundations/Picard/Basic.lean` (xi21t, untracked in wave 2), so both must be committed
   together.
3. Foundations README, XI.1.4 row:
   - **Proved:** XI.1.4 in SGA's form (projective `X`), in universe 0, from
     `HodgeSymmetryZeroComplexStatement` alone, by
     `serreUnirationalProjectiveStatement_of_hodgeSymmetryZeroComplex`. This uses the Lefschetz
     principle `serreLefschetzDescentStatement` and the `#k ≤ 𝔠` case.
   - **Missing:** Hodge symmetry over `ℂ` (hodge); universes above 0; proper non-projective `X`.
4. `Geometry.lean`, docstring of `SerreUnirationalSimplyConnectedStatement`: could point to
   `SerreUnirationalProjectiveStatement` (SGA's form) and to the theorem above.
