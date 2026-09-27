/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Group.Affine
import SGA.Foundations.Formal.EtaleCovering
import SGA.Foundations.Formal.FiniteEtale
import SGA.Foundations.Formal.Spf

/-!
# Étale coverings of affine schemes and of formal spectra

`Spec` is an anti-equivalence between finite étale `R`-algebras and étale coverings of `Spec R`
(`AlgebraicGeometry.Scheme.FiniteEtale.specEquivalence`), under which base change of schemes
corresponds to base change of algebras. Consequently, for a surjection `R → S` with nilpotent
kernel, `R` noetherian, base change `FEt(Spec R) ⥤ FEt(Spec S)` is an equivalence (SGA 1 I.8.3,
affine noetherian case), and for a noetherian ring `A` with an ideal `I` the étale coverings of
the formal scheme `Spf A = lim→ Spec (A ⧸ Iⁿ⁺¹)`, as compatible systems, are the étale coverings of
`Spec (A ⧸ I)` (SGA 1 I.8.4 for `Spf A`, `Spf.isEquivalence_formalFiniteEtale_toZero`).
-/

universe u

open CategoryTheory Limits Opposite TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable (R : CommRingCat.{u})

/-- `Spec` of a finite étale `R`-algebra, as an étale covering of `Spec R`. -/
noncomputable def specFunctor : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ⥤ (Spec R).FiniteEtale :=
  MorphismProperty.Comma.lift ((CommAlgCat.finiteEtale R).ι.op ⋙ algSpec R)
    (fun A ↦ by
      change finiteEtaleHom (Spec.map (CommRingCat.ofHom (algebraMap R A.unop)))
      refine ⟨?_, ?_⟩
      · rw [IsFinite.SpecMap_iff]
        exact RingHom.finite_algebraMap.mpr inferInstance
      · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
        exact RingHom.etale_algebraMap.mpr inferInstance)
    (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- `Spec` is fully faithful on finite étale algebras. -/
noncomputable def specFunctorFullyFaithful : (specFunctor R).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := MorphismProperty.Over.forget _ ⊤ _)
    ((ObjectProperty.fullyFaithfulι _).op.comp algSpec.fullyFaithful)

instance : (specFunctor R).Full := (specFunctorFullyFaithful R).full
instance : (specFunctor R).Faithful := (specFunctorFullyFaithful R).faithful

set_option backward.isDefEq.respectTransparency false in
instance : (specFunctor R).EssSurj where
  mem_essImage X := by
    let f : X.left ⟶ Spec R := X.hom
    have : IsFinite f := X.prop.1
    have : Etale f := X.prop.2
    have : IsAffine X.left := isAffine_of_isAffineHom f
    let φ : R ⟶ Γ(X.left, ⊤) := (Scheme.ΓSpecIso R).inv ≫ f.appTop
    let _ : Algebra R Γ(X.left, ⊤) := φ.hom.toAlgebra
    have hX : f = X.left.isoSpec.hom ≫ Spec.map φ := by
      have := (arrowIsoSpecΓOfIsAffine f).hom.w
      simp only [Arrow.mk_left, Arrow.mk_right, Arrow.isoMk_hom_left,
        arrowIsoSpecΓOfIsAffine, Arrow.isoMk_hom_right, Arrow.mk_hom,
        Scheme.isoSpec_Spec_hom] at this
      rw [Spec.map_comp, ← Category.assoc, this, Category.assoc, ← Spec.map_comp,
        Iso.inv_hom_id, Spec.map_id, Category.comp_id]
    have hφ : Spec.map φ = X.left.isoSpec.inv ≫ f := by rw [hX, Iso.inv_hom_id_assoc]
    have h₁ : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
    have h₂ : Etale (Spec.map φ) := by rw [hφ]; infer_instance
    rw [IsFinite.SpecMap_iff] at h₁
    rw [HasRingHomProperty.Spec_iff (P := @Etale)] at h₂
    have : Module.Finite R Γ(X.left, ⊤) := RingHom.finite_algebraMap.mp h₁
    have : Algebra.Etale R Γ(X.left, ⊤) := RingHom.etale_algebraMap.mp h₂
    exact ⟨Opposite.op (CommAlgCat.FiniteEtale.of R Γ(X.left, ⊤)),
      ⟨MorphismProperty.Over.isoMk X.left.isoSpec.symm (by
        change X.left.isoSpec.inv ≫ f = _
        rw [← hφ]
        rfl)⟩⟩

instance : (specFunctor R).IsEquivalence where

/-- Étale coverings of `Spec R` are the spectra of finite étale `R`-algebras (SGA 1 V.7, affine
case). -/
noncomputable def specEquivalence : (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ ≌ (Spec R).FiniteEtale :=
  (specFunctor R).asEquivalence

end AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {R S : CommRingCat.{u}} [Algebra R S]

/-- `Spec (S ⊗[R] B) ≅ Spec B ×_{Spec R} Spec S`. -/
noncomputable def specTensorIso (B : Type u) [CommRing B] [Algebra R B] :
    Spec (.of (S ⊗[R] B)) ≅ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  Scheme.Spec.mapIso (Algebra.TensorProduct.comm R B S).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso R B S).symm

@[reassoc (attr := simp)]
lemma specTensorIso_hom_fst (B : Type u) [CommRing B] [Algebra R B] :
    (specTensorIso (S := S) B).hom ≫ Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        B →+* S ⊗[R] B)) := by
  simp only [specTensorIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.op_hom,
    Category.assoc, pullbackSpecIso_inv_fst]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1

@[reassoc (attr := simp)]
lemma specTensorIso_hom_snd (B : Type u) [CommRing B] [Algebra R B] :
    (specTensorIso (S := S) B).hom ≫ Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] B))) := by
  simp only [specTensorIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.op_hom,
    Category.assoc, pullbackSpecIso_inv_snd]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1

end AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable (R S : CommRingCat.{u}) [Algebra R S]

/-- Base change of étale coverings of affine schemes is base change of finite étale algebras:
`Spec (S ⊗[R] B) = Spec B ×_{Spec R} Spec S`. -/
noncomputable def baseChangeSpecIso :
    (CommAlgCat.FiniteEtale.baseChange.{u} R S).op ⋙ specFunctor S ≅
      specFunctor R ⋙ FiniteEtale.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  NatIso.ofComponents (fun B ↦ MorphismProperty.Over.isoMk (specTensorIso (S := S) B.unop.obj)
    (specTensorIso_hom_snd _)) fun {B B'} f ↦ by
      ext1
      apply Limits.pullback.hom_ext
      · erw [Category.assoc, Category.assoc, specTensorIso_hom_fst,
          MorphismProperty.Comma.comp_left, Category.assoc,
          MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
        erw [specTensorIso_hom_fst_assoc]
        change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
        erw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
      · erw [Category.assoc, Category.assoc, specTensorIso_hom_snd,
          MorphismProperty.Comma.comp_left, Category.assoc,
          MorphismProperty.Over.pullback_map_left, pullback.lift_snd]
        erw [specTensorIso_hom_snd]
        change Spec.map _ ≫ Spec.map _ = Spec.map _
        erw [← Spec.map_comp]
        congr 1
        ext x
        change (Algebra.TensorProduct.map (AlgHom.id S S) f.unop.hom.hom) (algebraMap S _ x) =
          algebraMap S _ x
        exact AlgHom.commutes _ x

end AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable (R S : CommRingCat.{u}) [Algebra R S]

/-- Base change of étale coverings along `Spec S ⟶ Spec R` is an equivalence as soon as base
change of finite étale algebras `R → S` is. -/
theorem isEquivalence_pullback_spec [(CommAlgCat.FiniteEtale.baseChange.{u} R S).IsEquivalence] :
    (FiniteEtale.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).IsEquivalence := by
  let E := specEquivalence R
  have e : E.inverse ⋙ (CommAlgCat.FiniteEtale.baseChange.{u} R S).op ⋙ specFunctor S ≅
      FiniteEtale.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    Functor.isoWhiskerLeft E.inverse (baseChangeSpecIso R S) ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.counitIso _ ≪≫ Functor.leftUnitor _
  exact Functor.isEquivalence_of_iso e

end AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Spf

variable (A : Type u) [CommRing A] (I : Ideal A)

open Scheme in
/-- For `A` noetherian, the base change functors between étale coverings of the thickenings
`Spec (A ⧸ Iⁿ⁺¹)` are equivalences (SGA 1 I.8.3, affine noetherian case). -/
instance isEquivalence_finiteEtaleTower [IsNoetherianRing A] (n : ℕ) :
    (finiteEtaleTower (diagram A I) n).IsEquivalence := by
  let R := CommRingCat.of (A ⧸ I ^ (n + 1 + 1))
  let S := CommRingCat.of (A ⧸ I ^ (n + 1))
  let φ : R →+* S := Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
  let _ : Algebra R S := φ.toAlgebra
  have hS : Function.Surjective (algebraMap R S) :=
    Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
  have hK : RingHom.ker (algebraMap R S) ^ 2 = ⊥ := by
    change RingHom.ker φ ^ 2 = ⊥
    rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    rw [← pow_mul] at ha
    exact Ideal.pow_le_pow_right (by lia) ha
  have : IsAdicComplete (RingHom.ker (algebraMap R S)) R := .of_pow_eq_bot hK
  have : (CommAlgCat.FiniteEtale.baseChange.{u} R S).IsEquivalence :=
    CommAlgCat.FiniteEtale.isEquivalence_baseChange_of_surjective hS
  exact FiniteEtale.isEquivalence_pullback_spec R S

open Scheme in
/-- Étale coverings of `Spf A`, as compatible systems of étale coverings of the
`Spec (A ⧸ Iⁿ⁺¹)`, are the étale coverings of `Spec (A ⧸ I)` (SGA 1 I.8.4 for `Spf A`, `A`
noetherian). -/
theorem isEquivalence_formalFiniteEtale_toZero [IsNoetherianRing A] :
    (FormalFiniteEtale.toZero (diagram A I)).IsEquivalence :=
  TowerLimit.isEquivalence_π_zero

end AlgebraicGeometry.Spf
