/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.GAGAProjective
import SGA.SGA1.ExposeXII.GAGAModules
import SGA.Foundations.Analytic.ModulesCohomology
import SGA.Foundations.Cohomology.CohomologicalDimension
import SGA.Foundations.Cohomology.Coherent
import SGA.Foundations.Cohomology.LongExactSequence
import SGA.Foundations.Cohomology.CechVanishing
import SGA.Foundations.Cohomology.ExtChase

/-!
# SGA 1, Exposé XII, 4.3 on `ℙⁿ`: from the twisting sheaves to all coherent sheaves

Serre's argument (GAGA, no. 12, proof of théorème 1; SGA 1 XII.4.2, step 1) reduces XII.4.3 for
coherent sheaves on `ℙⁿ_ℂ = Proj ℂ[x₀, …, xₙ]` to the twisting sheaves `𝒪(d)`:
a coherent `F` is a quotient of some `𝒪(-m)ᵏ` (`projectiveSpace.exists_epi_twist`), the kernel is
coherent, and descending induction on the degree with the four lemma on the long exact sequences
(which `F ↦ F^an` preserves, XII.1.3.1) gives bijectivity in every degree, starting above `n`,
where both sides vanish.

The analytic vanishing above `n` is deduced from Theorem B for the analytifications of coherent
sheaves on the standard affine opens `D₊(x_I)` of `ℙⁿ` and their intersections (Leray), which is
recorded as `ProjectiveSpaceAnalyticLerayStatement`. It follows from Cartan's Theorem B for coherent
analytic sheaves on `ℂᵃ × (ℂ*)ᵇ` (`AnalyticGeometry.CoherentTheoremABStatement`, an-coh), the
comparison of cohomology over an open with that of the restriction (registry row C31) and the
identification of `(D₊(xᵢ))^an` with `ℂⁿ`; none of these is assembled here.

## Main results

* `ProjectiveSpaceAnalyticLerayStatement` (statement only).
* `bijective_pullbackCohomologyMap_projectiveSpace`: XII.4.3 for every coherent `F` on `ℙⁿ_ℂ`,
  assuming `ProjectiveSpaceTwistComparisonStatement` and `ProjectiveSpaceAnalyticLerayStatement`.
  `ℙⁿ_ℂ` is written `Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ)`, definitionally
  `Proj (ProjectiveSpace.grading (Fin (n + 1)) ℂ)` (`proj_grading_eq_proj_homogeneousSubmodule`).

The diagram chases on long exact `Ext` sequences (four and five lemmas) are
`CategoryTheory.Abelian.ExtChase` (`SGA.Foundations.Cohomology.ExtChase`).
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace Abelian AlgebraicGeometry

namespace SGA.SGA1.ExposeXII

/-! ### Coherent sheaves on `ℙⁿ` -/

open LocallyRingedSpace.Modules AnalyticGluing

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `ℙ(σ)_ℂ` is spelled two ways: `Proj (ProjectiveSpace.grading σ ℂ)` (in
`ProjectiveSpaceTwistComparisonStatement` and `SGA.Foundations.Projective`) and
`Proj (MvPolynomial.homogeneousSubmodule σ ℂ)` (in `SGA.Foundations.Cohomology.ProjectiveSpace`,
whence in `ProjectiveSpaceAnalyticLerayStatement` and this file). They are equal by definition
(`ProjectiveSpace.grading σ ℂ` is defined as `MvPolynomial.homogeneousSubmodule σ ℂ`, with the same
graded algebra structure), and statements in one spelling apply to the other by `exact`. -/
lemma proj_grading_eq_proj_homogeneousSubmodule (σ : Type) :
    Proj (ProjectiveSpace.grading σ ℂ) = Proj (MvPolynomial.homogeneousSubmodule σ ℂ) :=
  rfl

/-- The `ℂ`-structure of `Proj ℂ[xᵢ : i ∈ σ]` written with `MvPolynomial.homogeneousSubmodule`
(as in `SGA.Foundations.Cohomology.ProjectiveSpace`); definitionally `projectiveSpaceOverC`. -/
instance projectiveSpaceOverC' (σ : Type) :
    (Proj (MvPolynomial.homogeneousSubmodule σ ℂ)).Over (Spec (.of ℂ)) :=
  projectiveSpaceOverC σ

instance (σ : Type) [Finite σ] :
    LocallyOfFiniteType (Proj (MvPolynomial.homogeneousSubmodule σ ℂ) ↘ Spec (.of ℂ)) :=
  inferInstanceAs (LocallyOfFiniteType (Proj (ProjectiveSpace.grading σ ℂ) ↘ Spec (.of ℂ)))

instance (σ : Type) [Finite σ] :
    IsSeparated (Proj (MvPolynomial.homogeneousSubmodule σ ℂ) ↘ Spec (.of ℂ)) :=
  inferInstanceAs (IsSeparated (Proj (ProjectiveSpace.grading σ ℂ) ↘ Spec (.of ℂ)))

/-- Theorem B for the analytifications of coherent sheaves on the standard affine opens of `ℙⁿ`
(statement only): for every coherent `𝒪`-module `F` on `ℙⁿ_ℂ = Proj ℂ[x₀, …, xₙ]`, `F^an` has no
higher cohomology on the inverse images `φ⁻¹(D₊(x_I))` of the finite intersections of the standard
affine opens `D₊(xᵢ)` (`TopCat.Sheaf.IsLerayAcyclic`). Each `φ⁻¹(D₊(x_I))` is `ℂᵃ × (ℂ*)ᵇ`
(`a + b = n`), so this follows from Cartan's Theorem B for coherent analytic sheaves there
(`AnalyticGeometry.CoherentTheoremABStatement`) together with the comparison of cohomology over an
open with that of the restricted sheaf (registry row C31) and the identification of
`(D₊(xᵢ))^an` with `ℂⁿ`. -/
def ProjectiveSpaceAnalyticLerayStatement : Prop :=
  ∀ (n : ℕ) (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ)).Modules),
    F.IsCoherent →
    TopCat.Sheaf.IsLerayAcyclic
      (fun i ↦ (Opens.map
        (toScheme (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ))).base).obj
          (projectiveSpace.stdCover (Fin (n + 1)) ℂ i))
      ((analytification (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ))).obj F).toAbSheaf

section ProjectiveSpace

variable {n : ℕ}

local notation "ℙ" => Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ)

/-- On `(ℙⁿ)^an`, `Hᵠ(F^an) = 0` for `q > n`, given Theorem B on the standard affine opens. -/
lemma subsingleton_H_analytification (hB : ProjectiveSpaceAnalyticLerayStatement)
    (F : (ℙ).Modules) [F.IsCoherent] {q : ℕ} (hq : n ≤ q) :
    Subsingleton (((analytification ℙ).obj F).H (q + 1)) := by
  let U : Fin (n + 1) → Opens (analyticSpace ℙ).carrier :=
    fun i ↦ (Opens.map (toScheme ℙ).base).obj (projectiveSpace.stdCover (Fin (n + 1)) ℂ i)
  have hF := hB n F ‹_›
  have h := (TopCat.Sheaf.cechComplex_exactAt_iff_subsingleton_H' U q
    ((analytification ℙ).obj F).toAbSheaf hF.subsingleton_H').mp
    (TopCat.Presheaf.cechComplex_exactAt_of_card_le _ U (by omega) (Nat.succ_pos q))
  have hU : ⨆ i, U i = ⊤ := TopCat.Sheaf.iSup_map_eq_top (toScheme ℙ).base
    (projectiveSpace.iSup_stdCover (Fin (n + 1)) ℂ)
  rw [hU] at h
  exact (CategoryTheory.Sheaf.H'.addEquivH isTerminalTop _ (q + 1)).symm.subsingleton

/-- On `ℙⁿ`, `Hᵠ(F) = 0` for `q > n` and `F` coherent (in the form of
`LocallyRingedSpace.Modules.H`). -/
lemma subsingleton_H_projectiveSpace (F : (ℙ).Modules) [hF : F.IsCoherent] {q : ℕ}
    (hq : n ≤ q) :
    Subsingleton (LocallyRingedSpace.Modules.H (X := (ℙ).toLocallyRingedSpace) F (q + 1)) := by
  have h : Subsingleton (F.toAbSheaf.H' (q + 1) ⊤) :=
    @projectiveSpace.H_subsingleton_of_lt (CommRingCat.of ℂ) n F hF.isQuasicoherent q hq
  exact (CategoryTheory.Sheaf.H'.addEquivH isTerminalTop _ (q + 1)).symm.subsingleton

/-- The comparison maps for the twisted free modules `𝒪(d)ᵏ`, from those for `𝒪(d)`. -/
lemma bijective_pullbackCohomologyMap_twist_unitBiproduct
    (hT : ProjectiveSpaceTwistComparisonStatement) (k : ℕ) (d : ℤ) (p : ℕ) :
    Function.Bijective (pullbackCohomologyMap (X := analyticSpace ℙ)
      (Y := (ℙ).toLocallyRingedSpace) (toScheme ℙ)
      ((projectiveSpace.twistingBundle (Fin (n + 1)) ℂ).twist
        (CohomologyAux.unitBiproduct ℙ k) d) p) := by
  let L := projectiveSpace.twistingBundle (Fin (n + 1)) ℂ
  let G : Fin k → (ℙ).Modules := fun _ ↦ L.twist (CohomologyAux.unitModule ℙ) d
  refine (bijective_pullbackCohomologyMap_iff_of_iso (toScheme ℙ)
    (L.twistBiproductIso d (fun _ : Fin k ↦ CohomologyAux.unitModule ℙ)) p).mpr ?_
  have htot : ∑ j, biproduct.π G j ≫ biproduct.ι G j = 𝟙 (⨁ G) := biproduct.total
  exact bijective_pullbackCohomologyMap_of_retract (toScheme ℙ) G
    (fun j ↦ biproduct.ι G j) (fun j ↦ biproduct.π G j) htot p (fun _ ↦ hT n d p)

/-- Serre's step, surjectivity: if `Hᵖ⁺¹(ℙⁿ, G) → Hᵖ⁺¹((ℙⁿ)^an, G^an)` is bijective for every
coherent `G`, then `Hᵖ(ℙⁿ, F) → Hᵖ((ℙⁿ)^an, F^an)` is onto for every coherent `F`. -/
lemma surjective_pullbackCohomologyMap_projectiveSpace_step
    (hT : ProjectiveSpaceTwistComparisonStatement) (p : ℕ)
    (hp : ∀ G : (ℙ).Modules, G.IsCoherent → Function.Bijective (pullbackCohomologyMap
      (X := analyticSpace ℙ) (Y := (ℙ).toLocallyRingedSpace) (toScheme ℙ) G (p + 1)))
    (F : (ℙ).Modules) [hF : F.IsCoherent] :
    Function.Surjective (pullbackCohomologyMap (X := analyticSpace ℙ)
      (Y := (ℙ).toLocallyRingedSpace) (toScheme ℙ) F p) := by
  obtain ⟨m, k, π, hπ⟩ := projectiveSpace.exists_epi_twist (σ := Fin (n + 1)) (A := ℂ)
    (projectiveSpace.IsStdFinite.of_isCoherent F)
  let S := ShortComplex.kernelSequence π
  have hS : S.ShortExact := CohomologyAux.shortExact_kernelSequence π
  have hX₂ : S.X₂.IsCoherent :=
    ((projectiveSpace.IsStdFinite.unitBiproduct k).twist (-(m : ℤ))).isCoherent
  have hX₃ : S.X₃.IsCoherent := hF
  have hX₁ : S.X₁.IsCoherent := projectiveSpace.isCoherent_X₁_of_shortExact hS
  have hab := shortExact_map_toAbFunctor (Z := (ℙ).toLocallyRingedSpace) hS
  have han := shortExact_map_toAbFunctor (Z := analyticSpace ℙ)
    (shortExact_analytification S hS)
  have hL := bijective_pullbackCohomologyMap_twist_unitBiproduct (n := n) hT k (-(m : ℤ))
  exact ExtChase.surjective₃ hab han
    (fun q ↦ pullbackCohomologyMap (toScheme ℙ) S.X₁ q)
    (fun q ↦ pullbackCohomologyMap (toScheme ℙ) S.X₂ q)
    (fun q ↦ pullbackCohomologyMap (toScheme ℙ) S.X₃ q)
    (fun _ x ↦ pullbackCohomologyMap_naturality (toScheme ℙ) S.f x)
    (fun _ x ↦ pullbackCohomologyMap_naturality (toScheme ℙ) S.g x)
    (fun q x ↦ pullbackCohomologyMap_comp_extClass (toScheme ℙ) hab han q x)
    p (hL p).2 (hp S.X₁ hX₁).2 (hL (p + 1)).1

/-- Serre's step, injectivity: if `Hᵖ⁺¹(ℙⁿ, G) → Hᵖ⁺¹((ℙⁿ)^an, G^an)` is bijective for every
coherent `G`, then `Hᵖ(ℙⁿ, F) → Hᵖ((ℙⁿ)^an, F^an)` is injective for every coherent `F`. -/
lemma injective_pullbackCohomologyMap_projectiveSpace_step
    (hT : ProjectiveSpaceTwistComparisonStatement) (p : ℕ)
    (hp : ∀ G : (ℙ).Modules, G.IsCoherent → Function.Bijective (pullbackCohomologyMap
      (X := analyticSpace ℙ) (Y := (ℙ).toLocallyRingedSpace) (toScheme ℙ) G (p + 1)))
    (F : (ℙ).Modules) [hF : F.IsCoherent] :
    Function.Injective (pullbackCohomologyMap (X := analyticSpace ℙ)
      (Y := (ℙ).toLocallyRingedSpace) (toScheme ℙ) F p) := by
  obtain ⟨m, k, π, hπ⟩ := projectiveSpace.exists_epi_twist (σ := Fin (n + 1)) (A := ℂ)
    (projectiveSpace.IsStdFinite.of_isCoherent F)
  let S := ShortComplex.kernelSequence π
  have hS : S.ShortExact := CohomologyAux.shortExact_kernelSequence π
  have hX₂ : S.X₂.IsCoherent :=
    ((projectiveSpace.IsStdFinite.unitBiproduct k).twist (-(m : ℤ))).isCoherent
  have hX₃ : S.X₃.IsCoherent := hF
  have hX₁ : S.X₁.IsCoherent := projectiveSpace.isCoherent_X₁_of_shortExact hS
  have hab := shortExact_map_toAbFunctor (Z := (ℙ).toLocallyRingedSpace) hS
  have han := shortExact_map_toAbFunctor (Z := analyticSpace ℙ)
    (shortExact_analytification S hS)
  have hL := bijective_pullbackCohomologyMap_twist_unitBiproduct (n := n) hT k (-(m : ℤ))
  exact ExtChase.injective₃ hab han
    (fun q ↦ pullbackCohomologyMap (toScheme ℙ) S.X₁ q)
    (fun q ↦ pullbackCohomologyMap (toScheme ℙ) S.X₂ q)
    (fun q ↦ pullbackCohomologyMap (toScheme ℙ) S.X₃ q)
    (fun _ x ↦ pullbackCohomologyMap_naturality (toScheme ℙ) S.f x)
    (fun _ x ↦ pullbackCohomologyMap_naturality (toScheme ℙ) S.g x)
    (fun q x ↦ pullbackCohomologyMap_comp_extClass (toScheme ℙ) hab han q x)
    p (hp S.X₁ hX₁).1 (hL p).1
    (surjective_pullbackCohomologyMap_projectiveSpace_step hT p hp S.X₁)

/-- **XII.4.3 for coherent sheaves on `ℙⁿ`** (Serre, GAGA, no. 12, théorème 1 for `ℙⁿ`), assuming
the case of the twisting sheaves `𝒪(d)` (`ProjectiveSpaceTwistComparisonStatement`) and Theorem B
for the analytifications of coherent sheaves on the standard affine opens
(`ProjectiveSpaceAnalyticLerayStatement`): for every coherent `𝒪`-module `F` on
`ℙⁿ_ℂ = Proj ℂ[x₀, …, xₙ]`, `Hᵖ(ℙⁿ, F) → Hᵖ((ℙⁿ)^an, F^an)` is bijective for every `p`.
Serre's descending induction on `p`: both sides vanish for `p > n`; resolve `F` by `𝒪(-m)ᵏ`. -/
theorem bijective_pullbackCohomologyMap_projectiveSpace
    (hT : ProjectiveSpaceTwistComparisonStatement) (hB : ProjectiveSpaceAnalyticLerayStatement)
    (F : (ℙ).Modules) [F.IsCoherent] (p : ℕ) :
    Function.Bijective (pullbackCohomologyMap (X := analyticSpace ℙ)
      (Y := (ℙ).toLocallyRingedSpace) (toScheme ℙ) F p) := by
  -- descending induction: `key d` covers the degrees `p` with `n + 1 ≤ p + d`
  suffices key : ∀ d p, n + 1 ≤ p + d → ∀ G : (ℙ).Modules, G.IsCoherent →
      Function.Bijective (pullbackCohomologyMap (X := analyticSpace ℙ)
        (Y := (ℙ).toLocallyRingedSpace) (toScheme ℙ) G p) from
    key (n + 1) p (by omega) F ‹_›
  intro d
  induction d with
  | zero =>
    intro p hp G hG
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have h₁ := subsingleton_H_projectiveSpace G (q := q) (by omega)
    have h₂ := subsingleton_H_analytification hB G (q := q) (by omega)
    exact ⟨fun a b _ ↦ h₁.elim a b, fun y ↦ ⟨0, h₂.elim _ _⟩⟩
  | succ d ih =>
    intro p hp G hG
    by_cases hpd : n + 1 ≤ p + d
    · exact ih p hpd G hG
    · have hp1 : ∀ G' : (ℙ).Modules, G'.IsCoherent → Function.Bijective
          (pullbackCohomologyMap (X := analyticSpace ℙ) (Y := (ℙ).toLocallyRingedSpace)
            (toScheme ℙ) G' (p + 1)) := fun G' hG' ↦ ih (p + 1) (by omega) G' hG'
      exact ⟨injective_pullbackCohomologyMap_projectiveSpace_step hT p hp1 G,
        surjective_pullbackCohomologyMap_projectiveSpace_step hT p hp1 G⟩

end ProjectiveSpace

end SGA.SGA1.ExposeXII
