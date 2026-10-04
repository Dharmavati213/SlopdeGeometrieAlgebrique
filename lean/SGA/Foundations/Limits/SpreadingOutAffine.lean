/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.FiniteStability
import SGA.Foundations.Limits.SpreadingOut

/-!
# Spreading out affine schemes of finite presentation

The affine case of EGA IV 8.8.2 (ii) (Stacks 01ZM, from the algebra statement Stacks 05N9 / 00QO).

* `Algebra.FinitePresentation.exists_subalgebra_fg`: a finitely presented `A`-algebra `B` is
  `A ⊗_{A₀} B₀` for a finitely generated `R`-subalgebra `A₀ ⊆ A` and a finitely presented
  `A₀`-algebra `B₀` (the coefficients of a finite presentation generate `A₀`).
* `CommRingCat.exists_isPushout_of_isColimit_of_subalgebra`: along a filtered colimit
  `R = colim Rⱼ`, an `R`-algebra of the form `R ⊗_{A₀} B₀` with `A₀ ⊆ R` of finite type over `ℤ`
  is `R ⊗_{Rⱼ} (Rⱼ ⊗_{A₀} B₀)` for some `j`.
* `CommRingCat.exists_finitePresentation_isPushout_of_isColimit`: a finitely presented
  `R`-algebra is the base change of a finitely presented `Rⱼ`-algebra.
* `AlgebraicGeometry.Scheme.exists_isPullback_of_isLimit_of_isAffine_of_locallyOfFinitePresentation`
  (EGA IV 8.8.2 (ii), affine case): over the limit of a cofiltered diagram of affine schemes with
  affine transition maps, an affine scheme locally of finite presentation is the base change of an
  affine scheme locally of finite presentation over some member of the diagram.

The general case is in `SGA.Foundations.Limits.SpreadingOutGluing`.

## References

* [EGA IV₃, 8.8.2][EGA4]
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

universe u

open CategoryTheory Limits TensorProduct

section Algebra

/-- EGA IV 8.8.2 (noetherian models of finitely presented algebras, Stacks 00QO): a finitely
presented `A`-algebra `B` is `A ⊗_{A₀} B₀` for a finitely generated `R`-subalgebra `A₀ ⊆ A` and a
finitely presented `A₀`-algebra `B₀`. -/
theorem Algebra.FinitePresentation.exists_subalgebra_fg (R : Type*) [CommRing R] {A B : Type u}
    [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra.FinitePresentation A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ Algebra.FinitePresentation A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀) := by
  let P := Algebra.Presentation.ofFinitePresentation A B
  let A₀ := Algebra.adjoin R P.coeffs
  have : P.HasCoeffs A₀ := ⟨by simp [A₀]⟩
  exact ⟨A₀, (P.ModelOfHasCoeffs A₀:), inferInstance, inferInstance,
    ⟨P.finite_coeffs.toFinset, by simp [A₀]⟩, inferInstance,
    ⟨(P.tensorModelOfHasCoeffsEquiv A₀).symm⟩⟩

end Algebra

namespace CommRingCat

set_option backward.isDefEq.respectTransparency false in
/-- Let `R = colim Rⱼ` be a filtered colimit of commutative rings, `A₀ ⊆ R` a subring of finite
type over `ℤ`, `B₀` an `A₀`-algebra and `φ : R ⟶ B` with `B ≅ R ⊗_{A₀} B₀` as `R`-algebras. Then
`A₀ ⟶ R` factors through some `Rⱼ`, and `B ≅ R ⊗_{Rⱼ} (Rⱼ ⊗_{A₀} B₀)`: the square
`Rⱼ ⟶ R, Rⱼ ⟶ Rⱼ ⊗_{A₀} B₀, R ⟶ B, Rⱼ ⊗_{A₀} B₀ ⟶ B` is a pushout. -/
theorem exists_isPushout_of_isColimit_of_subalgebra {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} {c : Cocone F} (hc : IsColimit c) {B : CommRingCat.{u}}
    (φ : c.pt ⟶ B) (A₀ : Subalgebra ℤ c.pt) (hA₀ : A₀.FG) (B₀ : Type u) [CommRing B₀]
    [Algebra A₀ B₀] (e : B ≃+* c.pt ⊗[A₀] B₀)
    (he : ∀ x : c.pt, e (φ x) = x ⊗ₜ[A₀] (1 : B₀)) :
    ∃ (j : J) (_ : Algebra A₀ (F.obj j)) (ψ : of (F.obj j ⊗[A₀] B₀) ⟶ B),
      IsPushout (c.ι.app j) (ofHom (algebraMap (F.obj j) (F.obj j ⊗[A₀] B₀))) φ ψ := by
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  have : Algebra.FinitePresentation ℤ A₀ := Algebra.FinitePresentation.of_finiteType.mp this
  -- `A₀ ⟶ R` factors through some `Rⱼ`
  let Z : CommRingCat.{u} := .of (ULift.{u} ℤ)
  let f : Z ⟶ .of A₀ := ofHom ((algebraMap ℤ A₀).comp ULift.ringEquiv.toRingHom)
  have hf : f.hom.FinitePresentation :=
    (RingHom.finitePresentation_algebraMap.mpr ‹_›).comp
      (RingHom.FinitePresentation.of_bijective ULift.ringEquiv.bijective)
  let α : (Functor.const J).obj Z ⟶ F :=
    { app j := ofHom ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom)
      naturality j j' g := by ext; simp }
  obtain ⟨j, g', -, hg'⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit Z F α f c
    hc hf (ofHom A₀.val) (fun i ↦ by ext; simp [f, α])
  let : Algebra A₀ (F.obj j) := g'.hom.toAlgebra
  have hι (r : A₀) : c.ι.app j (algebraMap A₀ (F.obj j) r) = algebraMap A₀ c.pt r :=
    (congrArg (fun φ ↦ φ.hom r) hg').symm
  let ιj : F.obj j →ₐ[A₀] c.pt := { (c.ι.app j).hom with commutes' := hι }
  let m : F.obj j ⊗[A₀] B₀ →ₐ[A₀] c.pt ⊗[A₀] B₀ :=
    Algebra.TensorProduct.map ιj (AlgHom.id A₀ B₀)
  refine ⟨j, inferInstance, ofHom (e.symm.toRingHom.comp m.toRingHom), ?_⟩
  have t := CommRingCat.isPushout_tensorProduct A₀ (F.obj j) B₀
  have s := CommRingCat.isPushout_tensorProduct A₀ c.pt B₀
  have s' : IsPushout (ofHom (algebraMap A₀ (F.obj j)) ≫ c.ι.app j) (ofHom (algebraMap A₀ B₀))
      (ofHom (S := c.pt ⊗[A₀] B₀) Algebra.TensorProduct.includeLeftRingHom)
      (ofHom (S := F.obj j ⊗[A₀] B₀) Algebra.TensorProduct.includeRight.toRingHom ≫
        ofHom m.toRingHom) := by
    have e₁ : ofHom (algebraMap A₀ (F.obj j)) ≫ c.ι.app j = ofHom (algebraMap A₀ c.pt) := by
      ext r
      exact hι r
    have e₂ : ofHom (S := F.obj j ⊗[A₀] B₀) Algebra.TensorProduct.includeRight.toRingHom ≫
        ofHom m.toRingHom =
          ofHom (S := c.pt ⊗[A₀] B₀) Algebra.TensorProduct.includeRight.toRingHom := by
      ext b
      simp [m]
    rw [e₁, e₂]
    exact s
  have r := IsPushout.of_left s' (by ext x; simp [m, ιj]) t
  refine r.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm.toCommRingCatIso
    (by simp) (by simp; rfl) ?_ (by simp)
  ext x
  simp only [Iso.refl_hom, Category.id_comp, RingEquiv.toCommRingCatIso_hom, hom_comp,
    hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  change e.symm (x ⊗ₜ[A₀] (1 : B₀)) = φ.hom x
  rw [← he, RingEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2 (ii), affine case (Stacks 01ZM, 05N9): let `R = colim Rⱼ` be a filtered colimit
of commutative rings and `φ : R ⟶ B` of finite presentation. Then there are `j`, a finitely
presented `φⱼ : Rⱼ ⟶ Bⱼ` and `ψ : Bⱼ ⟶ B` such that the square `Rⱼ ⟶ R, Rⱼ ⟶ Bⱼ, R ⟶ B,
Bⱼ ⟶ B` is a pushout, i.e. `B ≅ R ⊗_{Rⱼ} Bⱼ`. -/
theorem exists_finitePresentation_isPushout_of_isColimit {J : Type u} [SmallCategory J]
    [IsFiltered J] {F : J ⥤ CommRingCat.{u}} {c : Cocone F} (hc : IsColimit c)
    {B : CommRingCat.{u}} (φ : c.pt ⟶ B) (hφ : φ.hom.FinitePresentation) :
    ∃ (j : J) (Bj : CommRingCat.{u}) (φj : F.obj j ⟶ Bj) (ψ : Bj ⟶ B),
      φj.hom.FinitePresentation ∧ IsPushout (c.ι.app j) φj φ ψ := by
  algebraize [φ.hom]
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, ⟨e⟩⟩ :=
    Algebra.FinitePresentation.exists_subalgebra_fg ℤ (A := c.pt) (B := B)
  obtain ⟨j, _, ψ, H⟩ := exists_isPushout_of_isColimit_of_subalgebra hc φ A₀ hA₀ B₀ e.toRingEquiv
    (fun x ↦ by
      change e (algebraMap c.pt B x) = _
      rw [AlgEquiv.commutes]
      rfl)
  exact ⟨j, _, _, ψ, RingHom.finitePresentation_algebraMap.mpr inferInstance, H⟩

end CommRingCat

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {E : I ⥤ Scheme.{u}} {c : Cone E}

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2 (ii), affine case (Stacks 01ZM): over the limit of a cofiltered diagram of affine
schemes with affine transition maps, every affine scheme `Y` locally of finite presentation over
the limit is the base change of an affine scheme locally of finite presentation over some member
of the diagram. -/
theorem Scheme.exists_isPullback_of_isLimit_of_isAffine_of_locallyOfFinitePresentation
    [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, IsAffine (E.obj i)]
    (hc : IsLimit c) {Y : Scheme.{u}} [IsAffine Y] (q : Y ⟶ c.pt)
    [LocallyOfFinitePresentation q] :
    ∃ (j : I) (Yj : Scheme.{u}) (qj : Yj ⟶ E.obj j) (e : Y ⟶ Yj),
      IsAffine Yj ∧ LocallyOfFinitePresentation qj ∧ IsPullback e q qj (c.π.app j) := by
  have hΓ := (nonempty_isColimit_Γ_mapCocone E c hc).some
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let φ : Γ(c.pt, ⊤) ⟶ Γ(Y, ⊤) := q.appTop
  have hφ : φ.hom.FinitePresentation := q.finitePresentation_appTop
  obtain ⟨j, Bj, φj, ψ, hφj, H⟩ :=
    CommRingCat.exists_finitePresentation_isPushout_of_isColimit hΓ φ hφ
  have hSpec := isPullback_SpecMap_of_isPushout _ _ _ _ H
  have : LocallyOfFinitePresentation (Spec.map φj) := HasRingHomProperty.Spec_iff.mpr hφj
  refine ⟨j.unop, Spec Bj, Spec.map φj ≫ (E.obj j.unop).isoSpec.inv, Y.isoSpec.hom ≫ Spec.map ψ,
    inferInstance, inferInstance, ?_⟩
  refine hSpec.flip.of_iso Y.isoSpec.symm (Iso.refl _) c.pt.isoSpec.symm
    (E.obj j.unop).isoSpec.symm (by simp) ?_ (by simp) ?_
  · simp only [Iso.symm_hom]
    exact Scheme.isoSpec_inv_naturality q
  · simp only [Iso.symm_hom]
    exact Scheme.isoSpec_inv_naturality (X := c.pt) (c.π.app j.unop)

end AlgebraicGeometry
