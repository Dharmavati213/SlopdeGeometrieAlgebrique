/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupLoopOrbits
import SGA.Foundations.Formal.FiniteEtaleSpec

/-!
# Algebras of an étale covering over affine pieces, and base change

For an étale covering `E` of a scheme `U` and a morphism `κ : Spec R ⟶ U`, the base change
`E ×_U Spec R` is `Spec` of a finite étale `R`-algebra `algebraOf E κ` (through V.7,
`ExposeV.specEquivalence`), on which `Aut E` acts (`autHomOf`). If `κ'` factors as
`Spec R' ⟶ Spec R ⟶ U`, then `algebraOf E κ' ≅ R' ⊗[R] algebraOf E κ`, naturally in `E`
(`algebraFunctorBaseChangeIso`). This identifies, for the comparison of inertia groups with
loops (registry row C32), the algebra over the fraction field of the strict henselization with the
base change of the algebra of `E` over an affine open.

The base change of algebras is `CommAlgCat.FiniteEtale.baseChange`, and the comparison of
`Spec` of a tensor product with a fibre product is
`AlgebraicGeometry.Scheme.FiniteEtale.baseChangeSpecIso` (`SGA.Foundations.Formal.FiniteEtaleSpec`;
its category `(Spec R).FiniteEtale` is definitionally `ExposeV.FEt (Spec R)`).
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

namespace SGA.SGA1.ExposeXIII.LoopInertia

open ExposeV

variable {U : Scheme.{u}}

/-- The functor `E ↦ (algebra of E ×_U Spec R)ᵒᵖ`, from étale coverings of `U` to finite étale
`R`-algebras. -/
noncomputable abbrev algebraFunctor {R : CommRingCat.{u}} (κ : Spec R ⟶ U) :
    FEt U ⥤ (CommAlgCat.FiniteEtale.{u} R)ᵒᵖ :=
  FEt.pullback κ ⋙ (specEquivalence R).inverse

/-- The finite étale `R`-algebra of `E ×_U Spec R` (for a field this is
`TameGaloisAlgebra.pullbackAlgebra`). -/
noncomputable abbrev algebraOf (E : FEt U) {R : CommRingCat.{u}} (κ : Spec R ⟶ U) :
    CommAlgCat.FiniteEtale.{u} R :=
  ((algebraFunctor κ).obj E).unop

/-- **Base change of the algebra of a covering.** If `κ' = Spec R' ⟶ Spec R ⟶ U`, the algebras of
`E ×_U Spec R'` and of `E ×_U Spec R` are related by `R' ⊗[R] -`, naturally in `E`. -/
noncomputable def algebraFunctorBaseChangeIso {R R' : CommRingCat.{u}} [Algebra R R']
    (κ : Spec R ⟶ U) (κ' : Spec R' ⟶ U)
    (hκ : κ' = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ κ) :
    algebraFunctor κ ⋙ (CommAlgCat.FiniteEtale.baseChange.{u} R R').op ≅ algebraFunctor κ' :=
  ((Scheme.FiniteEtale.specFunctorFullyFaithful R').whiskeringRight (FEt U)).preimageIso
    (Functor.isoWhiskerLeft (algebraFunctor κ) (Scheme.FiniteEtale.baseChangeSpecIso R R') ≪≫
      Functor.isoWhiskerLeft (FEt.pullback κ)
        (Functor.isoWhiskerRight (specEquivalence R).counitIso
          (FEt.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R'))))) ≪≫
      (MorphismProperty.Over.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap R R'))) κ
        κ' hκ).symm ≪≫
      Functor.isoWhiskerLeft (FEt.pullback κ') (specEquivalence R').counitIso.symm)

/-- The action of `Aut E` on the algebra of `E ×_U Spec R` (by `g ↦ (g⁻¹)^*`; for a field this
is `TameGaloisAlgebra.autHom`). -/
noncomputable def autHomOf (E : FEt U) {R : CommRingCat.{u}} (κ : Spec R ⟶ U) :
    Aut E →* ((algebraOf E κ).obj ≃ₐ[R] (algebraOf E κ).obj) :=
  (AffineLinePGroups.autOpMulEquivAlgEquiv (algebraOf E κ)).toMonoidHom.comp
    ((MulEquiv.inv' _).toMonoidHom.comp ((algebraFunctor κ).mapAut E))

lemma autHomOf_apply (E : FEt U) {R : CommRingCat.{u}} (κ : Spec R ⟶ U) (g : Aut E)
    (c : (algebraOf E κ).obj) :
    autHomOf E κ g c = ((algebraFunctor κ).map (g⁻¹).hom).unop.hom.hom c :=
  rfl

variable {R R' : CommRingCat.{u}} [Algebra R R'] (κ : Spec R ⟶ U) (κ' : Spec R' ⟶ U)
  (hκ : κ' = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ κ) (E : FEt U)

/-- The ring map from the algebra of `E ×_U Spec R` to that of `E ×_U Spec R'`, through
`R' ⊗[R] -` (`algebraFunctorBaseChangeIso`). -/
noncomputable def algebraMapOfBaseChange :
    (algebraOf E κ).obj →+* (algebraOf E κ').obj :=
  ((algebraFunctorBaseChangeIso κ κ' hκ).inv.app E).unop.hom.hom.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := (algebraOf E κ).obj)).toRingHom

/-- `algebraMapOfBaseChange` is `Aut E`-equivariant. -/
lemma algebraMapOfBaseChange_autHomOf (g : Aut E) (c : (algebraOf E κ).obj) :
    algebraMapOfBaseChange κ κ' hκ E (autHomOf E κ g c) =
      autHomOf E κ' g (algebraMapOfBaseChange κ κ' hκ E c) := by
  have h := congrArg (fun f ↦ f.unop.hom.hom (Algebra.TensorProduct.includeRight c))
    ((algebraFunctorBaseChangeIso κ κ' hκ).inv.naturality (g⁻¹).hom)
  exact h.symm

/-- `algebraMapOfBaseChange` is compatible with the structure maps: on the image of `R` it is
`R → R'`. -/
lemma algebraMapOfBaseChange_algebraMap (r : R) :
    algebraMapOfBaseChange κ κ' hκ E (algebraMap R (algebraOf E κ).obj r) =
      algebraMap R' (algebraOf E κ').obj (algebraMap R R' r) := by
  change ((algebraFunctorBaseChangeIso κ κ' hκ).inv.app E).unop.hom.hom
      (Algebra.TensorProduct.includeRight (algebraMap R (algebraOf E κ).obj r)) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R R' (R' ⊗[R] (algebraOf E κ).obj)]
  exact (((algebraFunctorBaseChangeIso κ κ' hκ).inv.app E).unop.hom.hom).commutes _

/-- The `R'`-algebra isomorphism `R' ⊗[R] (algebra of E ×_U Spec R) ≃ (algebra of E ×_U Spec R')`
(`algebraFunctorBaseChangeIso`). -/
noncomputable def baseChangeAlgEquiv :
    (R' ⊗[R] (algebraOf E κ).obj) ≃ₐ[R'] (algebraOf E κ').obj :=
  CommAlgCat.algEquivOfIso ((ObjectProperty.ι _).mapIso
    ((algebraFunctorBaseChangeIso κ κ' hκ).app E).unop.symm)

lemma baseChangeAlgEquiv_tmul (c : (algebraOf E κ).obj) :
    baseChangeAlgEquiv κ κ' hκ E (1 ⊗ₜ c) = algebraMapOfBaseChange κ κ' hκ E c :=
  rfl

section Comp

variable {T : Scheme.{u}} (f : T ⟶ U) {R : CommRingCat.{u}} (κ : Spec R ⟶ T) (E : FEt U)

/-- The algebra of `E ×_U Spec R` along `κ ≫ f` is that of `(f^* E) ×_T Spec R`. -/
noncomputable def algebraFunctorCompIso :
    algebraFunctor (κ ≫ f) ≅ FEt.pullback f ⋙ algebraFunctor κ :=
  Functor.isoWhiskerRight (MorphismProperty.Over.pullbackComp κ f) (specEquivalence R).inverse

/-- The `R`-algebra isomorphism between the algebra of `E ×_U Spec R` (along `κ ≫ f`) and that of
`(f^* E) ×_T Spec R`. -/
noncomputable def compAlgEquiv :
    (algebraOf ((FEt.pullback f).obj E) κ).obj ≃ₐ[R] (algebraOf E (κ ≫ f)).obj :=
  CommAlgCat.algEquivOfIso ((ObjectProperty.ι _).mapIso
    ((algebraFunctorCompIso f κ).app E).unop)

/-- `compAlgEquiv` is `Aut E`-equivariant (`Aut E` acting on `f^* E` through `f^*`). -/
lemma compAlgEquiv_autHomOf (g : Aut E) (d : (algebraOf ((FEt.pullback f).obj E) κ).obj) :
    compAlgEquiv f κ E (autHomOf ((FEt.pullback f).obj E) κ ((FEt.pullback f).mapAut E g) d) =
      autHomOf E (κ ≫ f) g (compAlgEquiv f κ E d) := by
  have h := congrArg (fun φ ↦ φ.unop.hom.hom d)
    ((algebraFunctorCompIso f κ).hom.naturality (g⁻¹).hom)
  simp only [Functor.comp_map] at h
  have hinv : ((FEt.pullback f).mapAut E g)⁻¹ = (FEt.pullback f).mapAut E g⁻¹ :=
    (map_inv _ g).symm
  rw [autHomOf_apply, autHomOf_apply, hinv]
  exact h.symm

end Comp

section Chi

variable {T : Scheme.{u}} (f : T ⟶ U) {R R' : CommRingCat.{u}} [Algebra R R']
  (κ : Spec R' ⟶ T) (κR : Spec R ⟶ U)
  (hκ : κ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ κR) (E : FEt U)

/-- The ring map from the algebra of `E ×_U Spec R` to that of `(f^* E) ×_T Spec R'`, when
`κ ≫ f` factors through `Spec R' ⟶ Spec R ⟶ U` (`algebraMapOfBaseChange` followed by
`compAlgEquiv`). -/
noncomputable def algebraMapToPullback :
    (algebraOf E κR).obj →+* (algebraOf ((FEt.pullback f).obj E) κ).obj :=
  (compAlgEquiv f κ E).symm.toRingHom.comp (algebraMapOfBaseChange κR (κ ≫ f) hκ E)

/-- `algebraMapToPullback` on the image of `R` is `R → R'`. -/
lemma algebraMapToPullback_algebraMap (r : R) :
    algebraMapToPullback f κ κR hκ E (algebraMap R (algebraOf E κR).obj r) =
      algebraMap R' (algebraOf ((FEt.pullback f).obj E) κ).obj (algebraMap R R' r) := by
  simp only [algebraMapToPullback, RingHom.coe_comp, Function.comp_apply,
    algebraMapOfBaseChange_algebraMap]
  exact (compAlgEquiv f κ E).symm.commutes _

/-- `algebraMapToPullback` is `Aut E`-equivariant: `Aut E` acts on the algebra of
`(f^* E) ×_T Spec R'` through `f^*`. -/
lemma algebraMapToPullback_autHomOf (g : Aut E) (c : (algebraOf E κR).obj) :
    algebraMapToPullback f κ κR hκ E (autHomOf E κR g c) =
      autHomOf ((FEt.pullback f).obj E) κ ((FEt.pullback f).mapAut E g)
        (algebraMapToPullback f κ κR hκ E c) := by
  simp only [algebraMapToPullback, RingHom.coe_comp, Function.comp_apply,
    algebraMapOfBaseChange_autHomOf]
  change (compAlgEquiv f κ E).symm _ =
    autHomOf ((FEt.pullback f).obj E) κ ((FEt.pullback f).mapAut E g)
      ((compAlgEquiv f κ E).symm _)
  rw [AlgEquiv.symm_apply_eq, compAlgEquiv_autHomOf, AlgEquiv.apply_symm_apply]

end Chi

end SGA.SGA1.ExposeXIII.LoopInertia
