/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Smooth.NoetherianDescent
import SGA.Foundations.SpecStalkLimit

/-!
# Spreading out étale algebras along filtered colimits

Let `R = colim Rⱼ` be a filtered colimit of rings and `B` an étale `R`-algebra. Then `B` is the
base change of an étale `Rⱼ`-algebra for some `j` (EGA IV 8.8.2 and 17.7.8, Stacks 00U2 (8)
and 07RP). We deduce it from the existence of noetherian models of étale algebras
(`Algebra.Etale.exists_subalgebra_fg`): `B ≅ R ⊗_{A₀} B₀` with `A₀ ⊆ R` a subring of finite
type over `ℤ`, hence of finite presentation, so `A₀ ⟶ R` factors through some `Rⱼ`.

## Main results

* `CommRingCat.exists_etale_isPushout_of_isColimit`: the ring-theoretic statement.
* `AlgebraicGeometry.Scheme.exists_etale_isPullback_fromSpecStalkOfMem`: an affine scheme étale
  over `Spec 𝒪_{X,x}` is the base change of an affine scheme étale over an affine open
  neighbourhood of `x`.
-/

universe u

open CategoryTheory Limits TensorProduct

namespace CommRingCat

/-- EGA IV 8.8.2, 17.7.8: let `R = colim Rⱼ` be a filtered colimit of commutative rings and
`φ : R ⟶ B` étale. Then there are `j`, an étale `Rⱼ ⟶ Bⱼ` and `ψ : Bⱼ ⟶ B` such that the square
`Rⱼ ⟶ R, Rⱼ ⟶ Bⱼ, R ⟶ B, Bⱼ ⟶ B` is a pushout, i.e. `B ≅ R ⊗_{Rⱼ} Bⱼ`. -/
@[stacks 07RP]
theorem exists_etale_isPushout_of_isColimit {J : Type u} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} {c : Cocone F} (hc : IsColimit c) {B : CommRingCat.{u}}
    (φ : c.pt ⟶ B) (hφ : φ.hom.Etale) :
    ∃ (j : J) (Bj : CommRingCat.{u}) (φj : F.obj j ⟶ Bj) (ψ : Bj ⟶ B),
      φj.hom.Etale ∧ IsPushout (c.ι.app j) φj φ ψ := by
  algebraize [φ.hom]
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg (R := ℤ)
    (A := c.pt) (B := B)
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
  refine ⟨j, .of (F.obj j ⊗[A₀] B₀), ofHom (algebraMap (F.obj j) (F.obj j ⊗[A₀] B₀)),
    ofHom (e.symm.toRingHom.comp m.toRingHom),
    RingHom.etale_algebraMap.mpr inferInstance, ?_⟩
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
  refine r.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm.toRingEquiv.toCommRingCatIso
    (by simp) (by simp) ?_ (by simp)
  ext x
  have hx : (x ⊗ₜ[A₀] (1 : B₀) : c.pt ⊗[A₀] B₀) = algebraMap c.pt (c.pt ⊗[A₀] B₀) x := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  simp only [Iso.refl_hom, Category.id_comp, RingEquiv.toCommRingCatIso_hom, hom_comp,
    hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  change e.symm (x ⊗ₜ[A₀] (1 : B₀)) = φ.hom x
  rw [hx, AlgEquiv.commutes]
  rfl

end CommRingCat

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2, 17.7.8: an affine scheme `Y` étale over `Spec 𝒪_{X,x}` is the base change of an
affine scheme étale over some affine open neighbourhood `U` of `x`. -/
theorem Scheme.exists_etale_isPullback_fromSpecStalkOfMem {X : Scheme.{u}} (x : X)
    {Y : Scheme.{u}} [IsAffine Y] (q : Y ⟶ Spec (X.presheaf.stalk x)) [Etale q] :
    ∃ (U : X.AffineNhds x) (YU : Scheme.{u}) (qU : YU ⟶ U.1) (e : Y ⟶ YU),
      IsAffine YU ∧ Etale qU ∧ IsPullback e q qU (U.1.fromSpecStalkOfMem x U.2.2) := by
  let φ : X.presheaf.stalk x ⟶ Γ(Y, ⊤) := Spec.preimage (Y.isoSpec.inv ≫ q)
  have hφ : Spec.map φ = Y.isoSpec.inv ≫ q := Spec.map_preimage _
  have hφe : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]
    infer_instance
  obtain ⟨j, Bj, φj, ψ, hφj, H⟩ :=
    CommRingCat.exists_etale_isPushout_of_isColimit (X.isColimitGermCocone x) φ hφe
  let U := j.unop
  have hSpec := isPullback_SpecMap_of_isPushout _ _ _ _ H
  have : Etale (Spec.map φj) := HasRingHomProperty.Spec_iff.mpr hφj
  refine ⟨U, Spec Bj, Spec.map φj ≫ U.isAffineOpen.isoSpec.inv, Y.isoSpec.hom ≫ Spec.map ψ,
    inferInstance, inferInstance, ?_⟩
  refine hSpec.flip.of_iso Y.isoSpec.symm (Iso.refl _) (Iso.refl _) U.isAffineOpen.isoSpec.symm
    (by simp) (by simp [hφ]) (by simp) ?_
  simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
  rw [Iso.comp_inv_eq, IsAffineOpen.isoSpec_hom]
  exact (Scheme.Opens.fromSpecStalkOfMem_toSpecΓ U.1 x U.2.2).symm

end AlgebraicGeometry
