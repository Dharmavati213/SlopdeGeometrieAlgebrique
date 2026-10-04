/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.CurveLiftFlat
import SGA.SGA1.ExposeIII.CurveLiftSmooth

/-!
# SGA 1, Exposé III, 7.4: the algebraized lift is a smooth proper curve

Let `A` be a complete noetherian local ring with maximal ideal `𝔪`, and `B` level `0` data over
`A₀ = A / 𝔪` (`CurveLift.Base`: a smooth `A₀`-scheme `X₀` with two affine charts, coordinates
`t`, `s` and the `H¹` condition) whose chart homomorphisms `A₀[t] → Γ(U₀)`, `A₀[s] → Γ(U₁)` are
finite and flat, with `X₀` smooth of relative dimension `n` over `A₀`. The algebraization
`p : Y ⟶ ℙ¹_A` of the formal lifts (`CurveLift.exists_algebraization_of_base`) is finite and flat,
so `f : Y ⟶ ℙ¹_A ⟶ Spec A` is proper and flat with closed fibre `X₀`, hence smooth of relative
dimension `n` (`CurveLift.smoothOfRelativeDimension_of_isPullback`). This is
`CurveLift.exists_smoothProper_of_base`; with the identification `A / 𝔪¹ = κ(A)`,
`CurveLift.exists_lift_of_base` has the form of `SGA.SGA1.ExposeIII.SmoothProperCurveLiftStatement`
for curves `X₀` which come with such level `0` data.

Also: `ℙ(σ; A) = Proj A[σ]` is flat (`CurveLift.flat_projToSpec`) and, for finite `σ`, proper
(`CurveLift.isProper_projToSpec`) over `Spec A`.

## References

* [SGA 1, III.7.2, III.7.4][SGA1].
-/

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
  AlgebraicGeometry.AmpleLift MvPolynomial IsLocalRing

namespace SGA.SGA1.ExposeIII.CurveLift

section ProjectiveSpace

variable (σ R : Type u) [CommRing R]

set_option backward.isDefEq.respectTransparency.types false in
/-- `ℙ(σ; R) = Proj R[σ]` is flat over `Spec R`: on the chart `D₊(xᵢ)` it is
`Spec R[xⱼ / xᵢ] ⟶ Spec R`. -/
theorem flat_projToSpec : Flat (projToSpec σ R) := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top
    (fun i : σ ↦ Proj.basicOpen (grading σ R) (MvPolynomial.X i)) (iSup_basicOpen_X σ R)
    fun i ↦ ?_
  have hι : (Proj.basicOpen (grading σ R) (MvPolynomial.X i)).ι =
      (Proj.basicOpenIsoSpec (grading σ R) (MvPolynomial.X i) (X_mem_grading i) one_pos).hom ≫
        Proj.awayι (grading σ R) (MvPolynomial.X i) (X_mem_grading i) one_pos := by
    rw [← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  rw [hι, Category.assoc, awayι_projToSpec,
    MorphismProperty.cancel_left_of_respectsIso (P := @Flat),
    HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom]
  have h : awayC (MvPolynomial.X i : MvPolynomial σ R) =
      (awayEquiv i
        (rfl : (MvPolynomial.X i : MvPolynomial σ R) = MvPolynomial.X i)).symm.toRingHom.comp
          (algebraMap R (MvPolynomial {j // j ≠ i} R)) := by
    refine RingHom.ext fun r ↦ ?_
    apply (awayEquiv i (rfl : (MvPolynomial.X i : MvPolynomial σ R) = MvPolynomial.X i)).injective
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, awayEquiv_awayC,
      MvPolynomial.algebraMap_eq]
  rw [h]
  exact RingHom.Flat.respectsIso.1 _ _ (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- `ℙ(σ; R) = Proj R[σ]` is proper over `Spec R` for finite `σ`. -/
theorem isProper_projToSpec [Finite σ] : IsProper (projToSpec σ R) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap R (grading σ R 0)))) :=
    isIso_SpecMap_iff.2 (bijective_algebraMap_grading_zero σ R)
  rw [projToSpec]
  infer_instance

end ProjectiveSpace

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

omit [IsLocalRing A] in
/-- The level `0` square: `X₀ = Y ×_A A₀` for the algebraization `p : Y ⟶ ℙ¹_A`. -/
lemma isPullback_algebraization {I : Ideal A} (B : Base I) {Y : Scheme.{u}}
    (p : Y ⟶ Proj (grading Two.{u} A))
    (e : pullback p (thickening.ι (projToSpec Two.{u} A) I 0) ≅ B.X)
    (he : e.hom ≫ (stage B 0).thickeningHom = pullback.snd _ _) :
    IsPullback (e.inv ≫ pullback.fst _ _) B.f (p ≫ projToSpec Two.{u} A)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1))))) := by
  have H1 := IsPullback.of_hasPullback p (thickening.ι (projToSpec Two.{u} A) I 0)
  have H2 := CohomologyAux.isPullback_thickening (A := CommRingCat.of A) I
    (projToSpec Two.{u} A) 0
  refine (H1.paste_vert H2).of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · have h0 : (stage B 0).thickeningHom ≫ thickeningSnd (projToSpec Two.{u} A) 0 = B.f :=
      Stage.thickeningHom_snd _
    rw [Iso.refl_hom, Category.comp_id, ← he]
    exact (Category.assoc _ _ _).trans (congrArg (fun g ↦ e.hom ≫ g) h0)
  · simp
  · simp

/-- **The algebraized lift of a curve with a finite flat morphism to `ℙ¹` is smooth and proper**
(SGA 1 III.7.4, from level `0` data): let `A` be a complete noetherian local ring with maximal
ideal `𝔪`, and `B` level `0` data over `A / 𝔪` (a smooth `A / 𝔪`-scheme `X₀` with two affine
charts `U₀`, `U₁` with affine intersection, coordinates `t`, `s` with `t s = 1` and the `H¹`
condition `CurveLift.Base.H1`) whose chart homomorphisms `(A/𝔪)[t] → Γ(U₀)`, `(A/𝔪)[s] → Γ(U₁)` are
finite and flat, and with `X₀` smooth of relative dimension `n` over `A / 𝔪`. Then there is a
proper `f : Y ⟶ Spec A`, smooth of relative dimension `n`, with closed fibre `X₀`:
`X₀ = Y ×_A A / 𝔪`. -/
theorem exists_smoothProper_of_base [IsAdicComplete (maximalIdeal A) A]
    (B : Base (maximalIdeal A)) (n : ℕ) [SmoothOfRelativeDimension n B.f]
    (hfin₀ : (chartHom {j : Two.{u} // j ≠ Two.zero} B.f B.U₀ B.t).Finite)
    (hfin₁ : (chartHom {j : Two.{u} // j ≠ Two.one} B.f B.U₁ B.s).Finite)
    (hfl₀ : (chartHom {j : Two.{u} // j ≠ Two.zero} B.f B.U₀ B.t).Flat)
    (hfl₁ : (chartHom {j : Two.{u} // j ≠ Two.one} B.f B.U₁ B.s).Flat) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)) (j : B.X ⟶ Y), SmoothOfRelativeDimension n f ∧
      IsProper f ∧ IsPullback j B.f f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (0 + 1))))) := by
  obtain ⟨Y, p, hp, hfl, e, he⟩ := exists_algebraization_of_base B hfin₀ hfin₁ hfl₀ hfl₁
  have H := isPullback_algebraization B p e he
  have : IsProper (projToSpec Two.{u} A) := isProper_projToSpec Two.{u} A
  have : Flat (projToSpec Two.{u} A) := flat_projToSpec Two.{u} A
  have : IsProper (p ≫ projToSpec Two.{u} A) := inferInstance
  have : Flat (p ≫ projToSpec Two.{u} A) := inferInstance
  have hmax : (RingHom.ker (CommRingCat.Hom.hom (CommRingCat.ofHom
      (Ideal.Quotient.mk (maximalIdeal A ^ (0 + 1)))))).IsMaximal := by
    rw [CommRingCat.hom_ofHom, Ideal.mk_ker, zero_add, pow_one]
    exact maximalIdeal.isMaximal A
  refine ⟨Y, p ≫ projToSpec Two.{u} A, _, ?_, inferInstance, H⟩
  exact smoothOfRelativeDimension_of_isPullback (R := CommRingCat.of A) _ _
    Ideal.Quotient.mk_surjective hmax H n

/-- The identification `A / 𝔪¹ = κ(A)`. -/
noncomputable def residueEquiv : A ⧸ maximalIdeal A ^ (0 + 1) ≃+* ResidueField A :=
  Ideal.quotEquivOfEq (by rw [zero_add, pow_one])

omit [IsNoetherianRing A] in
lemma residueEquiv_mk (a : A) :
    residueEquiv (Ideal.Quotient.mk (maximalIdeal A ^ (0 + 1)) a) = residue A a :=
  rfl

/-- **SGA 1 III.7.4 for a curve with level `0` data**: let `A` be a complete noetherian local
ring and `f₀ : X₀ ⟶ Spec κ(A)`; suppose that `X₀` over `A / 𝔪 ≅ κ(A)` is the scheme of level `0`
data `B` (`CurveLift.Base`, with the `H¹` condition) whose chart homomorphisms are finite and
flat, and that `f₀` is smooth of relative dimension `n`. Then `X₀` is the closed fibre of a proper
`f : X ⟶ Spec A`, smooth of relative dimension `n`, in the form of
`SGA.SGA1.ExposeIII.SmoothProperCurveLiftStatement`. -/
theorem exists_lift_of_base [IsAdicComplete (maximalIdeal A) A] (B : Base (maximalIdeal A))
    (f₀ : B.X ⟶ Spec (.of (ResidueField A)))
    (hf₀ : B.f = f₀ ≫ Spec.map (CommRingCat.ofHom residueEquiv.toRingHom)) (n : ℕ)
    [SmoothOfRelativeDimension n f₀]
    (hfin₀ : (chartHom {j : Two.{u} // j ≠ Two.zero} B.f B.U₀ B.t).Finite)
    (hfin₁ : (chartHom {j : Two.{u} // j ≠ Two.one} B.f B.U₁ B.s).Finite)
    (hfl₀ : (chartHom {j : Two.{u} // j ≠ Two.zero} B.f B.U₀ B.t).Flat)
    (hfl₁ : (chartHom {j : Two.{u} // j ≠ Two.one} B.f B.U₁ B.s).Flat) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), SmoothOfRelativeDimension n f ∧ IsProper f ∧
      ∃ e : pullback f (Spec.map (CommRingCat.ofHom (residue A))) ≅ B.X,
        e.hom ≫ f₀ = pullback.snd _ _ := by
  have hiso : IsIso (Spec.map (CommRingCat.ofHom residueEquiv.toRingHom :
      CommRingCat.of (A ⧸ maximalIdeal A ^ (0 + 1)) ⟶ CommRingCat.of (ResidueField A))) :=
    isIso_SpecMap_iff.2 residueEquiv.bijective
  have : SmoothOfRelativeDimension n B.f := by
    rw [hf₀]
    exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) _)
  obtain ⟨Y, f, j, hsm, hpr, H⟩ :=
    exists_smoothProper_of_base B n hfin₀ hfin₁ hfl₀ hfl₁
  have H' : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom (residue A))) := by
    refine H.of_iso (Iso.refl _) (Iso.refl _)
      (asIso (Spec.map (CommRingCat.ofHom residueEquiv.toRingHom))).symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · rw [hf₀, Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]
    · simp
    · rw [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id, IsIso.eq_inv_comp,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
  exact ⟨Y, f, hsm, hpr, H'.isoPullback.symm, IsPullback.isoPullback_inv_snd H'⟩

end SGA.SGA1.ExposeIII.CurveLift
