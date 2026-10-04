---
author: xi21t
date: 2026-10-04
area: SGA1 XI, Foundations/Picard, sga1-oos-coord
kind: handoff
---

# XI.2.1 reduced to the openness step of the theorem of the cube (wave 2, round 1)

Stream `xi21t`, registry rows A44, A46, A52, A54. Every module below builds with `lake build`, has
no `sorry`, and `#print axioms` on the main results lists only propext, Classical.choice and
Quot.sound. The interrupted attempt had left no Lean files, only row A46.

## State of XI.2.1

- `AbelianVarietyFundamentalGroupStatement` and `AbelianVarietyPrimaryComponentStatement` (both
  clauses, every characteristic) now follow from **one** open interface,
  `AlgebraicGeometry.CubeOpennessStatement` (`Foundations/Picard/Cube.lean`):
  `abelianVarietyFundamentalGroupStatement_of_cubeOpenness`,
  `abelianVarietyPrimaryComponentStatement_of_cubeOpenness` (`SGA1/ExposeXI/AbelianVarietyKernel.lean`).
- `CubeOpennessStatement`: `X`, `Y` proper geometrically integral, `W` locally of finite type over
  `k = k̄`, rational points `x₀, y₀, w₀`; a class on `(X ⊗ Y) ⊗ W` trivial on `{x₀} × Y × W`,
  `X × {y₀} × W` and on the fibre over `w₀` is trivial over `X × Y × U` for an open `U ∋ w₀`.
  This is the infinitesimal-and-formal heart of the theorem of the cube. Nothing else is assumed.
- Also stated: `TheoremOfTheCubeStatement` (Mumford §6, `Z` smooth). It implies the cube relation
  too, but is not needed and is not proved.

## What was built

1. `Foundations/Picard/Basic.lean` (A46): `Scheme.Pic.pullback f : Pic X →* Pic Y` and its
   functoriality; `LineBundle.pullback_tensor/_dual/_id`; trivial iff a unit section exists;
   `class_eq_one_of_top_le`, `class_pullback_eq_one_of_range_subset`, `Pic` of local schemes;
   `LineBundle.pow` and `class_pow`; `famLocus_eq_top_of_class_pow_eq_one` (on an integral scheme
   universally closed over a field, a section of a torsion line bundle vanishing nowhere at one
   point vanishes nowhere). Name trap: `Scheme.LineBundle.pow_one` shadows `_root_.pow_one`
   inside that namespace.
2. `Foundations/Picard/PoleDivisor.lean` (A52): `IsFractionRing.denIdeal` (principal over a UFD,
   commutes with localization), and `Scheme.exists_lineBundle_poleDivisor`: on an integral locally
   noetherian scheme with factorial stalks, the line bundle `𝒪(div_∞ f)` with the section `f`.
   (I chose the pole divisor over the prime divisor of the original plan: no heights needed.)
3. `Foundations/Picard/IntegralSubscheme.lean`: the vanishing-ideal subscheme of an irreducible
   closed set is integral.
4. `Foundations/Picard/Seesaw.lean`: `Γ(P, 𝒪) = k` for `P` proper geometrically integral over
   `k = k̄`; flat base change `Γ(P ×ₖ W, π⁻¹V) = Γ(W, V)`; `class_pullback_ι_eq_one_iff`;
   `class_eq_one_of_forall_trivial` (a line bundle on `P ×ₖ W` trivial along a section and over
   the preimages of an open cover of `W` is trivial; no cohomology).
5. `Foundations/Picard/FormalSections.lean`: `CohomologyAux.exists_section_sub_mem_of_compatible`,
   the theorem on formal functions in degree 0 for local sections of a coherent module (for
   `F = L.toModules 1` this lifts compatible local generators of a line bundle on the thickenings).
   Not used yet: it is the first brick of A54. `Foundations/Picard/KunnethAlgebra.lean`: the linear
   algebra of `H¹(K• ⊗ₖ C) = H¹(K•) ⊗ₖ C` (`LinearMap.exists_eq_sum_tmul_add_of_rTensor_eq_zero`,
   `LinearMap.eq_zero_of_sum_tmul_mem_range_rTensor`), the second brick.
6. `SGA1/ExposeXI/AbelianVarietyCube.lean`: `cubeClass`, `CubeRelation A` (Mumford §6 Cor. 2),
   `cubeRelation_of_proj`, `cubeRelation_of_theoremOfTheCube`, `picPullback_pow`,
   `picPullback_mulN` (`n_A^* c = c^{n(n+1)/2} ⊗ ((-1)^*c)^{n(n-1)/2}`).
7. `SGA1/ExposeXI/AbelianVarietyCubeOpenness.lean`: `cubeRelation_of_cubeOpenness`. The trick
   that avoids Mumford's semicontinuity and curves: the rational points `z` with `M_z` trivial
   form a **subgroup** (`M_z = Λ(t_z^*c ⊗ c⁻¹)`, `ker Λ` is translation invariant, `z ↦ t_z^*c ⊗ c⁻¹`
   is a crossed homomorphism); openness at `0` makes it contain a dense open, hence everything;
   openness at every rational point plus the gluing lemma then trivializes `M`.
8. `SGA1/ExposeXI/AbelianVarietyKernel.lean`: from `CubeRelation`, `n_A` is finite and surjective
   for every `n > 0`. No ample bundle: if a fibre of `n_A` had a positive-dimensional component
   `Z`, take closed points `x ≠ x'` of `Z` in an affine open, a pole-divisor line bundle `L` with a
   section through `x'` but not `x`; on `Z` (reduced, integral, proper) the relations from
   `picPullback_mulN` for `c` and `(-1)^*c` give `L|_Z^{a² - b²} = 1` with `a² - b² = n³ > 0`, so the
   section vanishes nowhere on `Z`: contradiction. Surjectivity: a locally quasi-finite
   endomorphism of an integral locally noetherian scheme fixing a point is dominant
   (`isDominant_of_locallyQuasiFinite_of_apply_eq`, coheight argument). Over any field `k`
   (`IsAlgClosed` omitted) given `CubeRelation`.

## What's left: proving `CubeOpennessStatement` (row A54)

Plan (Grothendieck's deformation argument):
1. Reduce `W` to an affine `Spec B ∋ w₀`, `m` the maximal ideal; `T = (X × Y) × Spec B` proper over
   `Spec B`; `L` with `L.class = c`.
2. Formal functions: `exists_section_sub_mem_of_compatible` with `F = L.toModules 1` and the
   product cover `Pᵢ × Q_j × Spec B` (`Pᵢ`, `Q_j` finite affine covers of `X`, `Y`; affine
   intersections since `X`, `Y` are separated) turns compatible local generators modulo `mⁿ⁺¹`
   into a global section `s` generating `L` along the closed fibre; the non-vanishing locus of `s`
   contains the closed fibre, and properness gives `U`.
3. The local generators modulo `mⁿ⁺¹` come from lifting: at each step the defect `s_{n,a} - s_{n,b}`
   modulo `mⁿ⁺²` is (after dividing by the local generator, a unit modulo `m`) a Čech 1-cocycle of
   `𝒪_{X×Y} ⊗ mⁿ⁺¹/mⁿ⁺²` on the product cover; it is a coboundary on both axes (the faces are
   trivial and `Γ(axis × Spec B/mⁿ⁺¹, 𝒪) = B/mⁿ⁺¹`, so generators there differ by liftable units).
4. The Künneth step (the real content): a Čech 1-cocycle of `𝒪` on the product cover of `X × Y`
   which is a coboundary on both axes is a coboundary. Proof: for each `V_j`, the slice is a
   cocycle of `Č(𝒰, 𝒪_X) ⊗ₖ Γ(V_j)` (`Γ(U × V) = Γ(U) ⊗ₖ Γ(V)`), so its class lies in
   `Ȟ¹(𝒰, 𝒪_X) ⊗ Γ(V_j)` (flatness over `k`); these glue to `Ȟ¹ ⊗ Γ(Y, 𝒪) = Ȟ¹` (finite-dimensional
   by `properFinitenessStatement` and Čech comparison), whose value at `y₀` is 0; so each slice
   is a coboundary; subtract, and the rest descends to a cocycle on `Y` (`Γ(X × V, 𝒪) = Γ(V)`,
   `isIso_app_snd_tensor`), a coboundary by the other axis.
Each step is concrete; 3 and 4 are the bulk (I estimate 1500–2500 lines). Do 4 first (riskiest).

API pointers for 4:
- the identification `Γ(X, P) ⊗ₖ Γ(Y, Q) ≅ Γ(X ×ₖ Y, p₁⁻¹P ⊓ p₂⁻¹Q)` for affine `P`, `Q`: apply
  `CohomologyAux.isPushout_app_of_isPullback` (`Foundations/Cohomology/FlatBaseChange.lean`) to the
  square `(p₁⁻¹P) → P`, `(p₁⁻¹P) → Y` over `Spec k` (paste mathlib's `isPullback_morphismRestrict`
  with the product square), then `Algebra.IsPushout`/`IsBaseChange` for the linear equivalence.
  The map itself is `a ⊗ b ↦ p₁^*a · p₂^*b` and is natural in `P` and `Q` for free.
- `K₀ = ∏ᵢ Γ(Pᵢ)`, `K₁ = ∏ᵢᵢ' Γ(Pᵢ ∩ Pᵢ')`, `K₂ = ∏ Γ(Pᵢᵢ'ᵢ'')`, `C = Γ(Q_j)`; finite products
  commute with `⊗`; `KunnethAlgebra` gives the decomposition `∑ eₜ ⊗ φₜ^j + coboundary` with unique
  `φₜ^j ∈ Γ(Q_j)`; uniqueness makes them glue (restriction `Γ(Q_j) → Γ(Q_j ∩ Q_j')` is natural),
  `Γ(Y, 𝒪) = k` makes them constant (`isIso_app_of_isProper_of_geometricallyIntegral`), and the
  `y₀`-axis hypothesis kills them.
- a basis `eₜ` of `Ȟ¹(𝒫, 𝒪_X)`: finite-dimensionality from `properFinitenessStatement`
  (`Foundations/Cohomology/ProperFiniteness.lean`) and `Scheme.Modules.cechHomologyLinearEquiv`
  (`AffineOpenVanishing.lean`; the repo's Čech complex is the ordered one,
  `TopCat.Presheaf.cechComplex`), or avoid it: only the span/independence hypotheses of
  `KunnethAlgebra` are needed, and a finite spanning family of cocycles modulo coboundaries can be
  extracted from any finite generating set of `Ȟ¹` as a `k`-module.

## What was hard

- `open MonObj` shadows `one_mul`, `mul_one`, `mul_assoc` (use `_root_.`); inside a declaration
  named `Scheme.LineBundle.foo`, `toUnit`, `trivial`, `pow_one` resolve to `LineBundle.toUnit`,
  `LineBundle.trivial`, `LineBundle.pow_one` (write `CartesianMonoidalCategory.toUnit`,
  `True.intro`, `_root_.pow_one`).
- Instance search failed for `IsIso ((snd A A).left.app V)` although the term was in context
  (different instance paths for the `Over` products); `@IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂` works.
- Lemmas about `(L.tensor M)` sections hit "motive is not type correct" because
  `(L.tensor M).U p` is not reducibly `L.U p.1 ⊓ M.U p.2`; I avoided tensor sections altogether
  (the `a² - b²` trick instead of a symmetric bundle).
- `StrictMono.monotone` needs a partial order; scheme points only carry a preorder.

## For the coordinator

- Barrels: `lean/SGA/Foundations.lean`: `Picard.Basic`, `Picard.Cube`, `Picard.PoleDivisor`,
  `Picard.IntegralSubscheme`, `Picard.Seesaw`, `Picard.FormalSections`, `Picard.KunnethAlgebra`; `lean/SGA/SGA1/ExposeXI.lean`:
  `AbelianVarietyCube`, `AbelianVarietyCubeOpenness`, `AbelianVarietyKernel`.
- Docs (`docs/`, Foundations README out-of-scope table, `TateModule.lean` docstring lines 59-60):
  XI.2.1 is now proved modulo `CubeOpennessStatement` only (the openness step of the theorem of
  the cube), in every characteristic.
- Dedupe: `ExposeX/TopologicallyFiniteReduction.lean` has a private `irreducibleSpace_subscheme`;
  `Scheme.IdealSheafData.isIntegral_vanishingIdeal_subscheme` (`Foundations/Picard/IntegralSubscheme.lean`)
  covers it.
