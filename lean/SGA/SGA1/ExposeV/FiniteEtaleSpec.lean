/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.CategoryTheory.Limits.MorphismProperty
import SGA.SGA1.ExposeV.FiniteEtaleGalois
import SGA.SGA1.ExposeV.GaloisEquivalence


/-!
# SGA 1, Exposé V, §7: étale coverings of a connected affine scheme

We define the category `FEt S` of étale coverings (finite étale `S`-schemes) of a
scheme `S`, as mathlib's `MorphismProperty.Over` for finite étale morphisms, and the functor
`geometricPoints a` of geometric points over a geometric point `a : Spec Ω ⟶ S`.

For `S = Spec R` we show that `Spec` is an equivalence between finite étale `R`-algebras and
étale coverings of `Spec R` (`specEquivalence`). Transporting the results of
`SGA.SGA1.ExposeV.FiniteEtaleGalois`, when `Spec R` is connected and `Ω` is algebraically
closed, `FEt (Spec R)` is a Galois category (`galoisCategory_spec`) with
fiber functor `geometricFiber R Ω`, whose underlying functor to sets is `geometricPoints`
(`geometricFiberInclIso`), and it is equivalent to the category of finite continuous
`π₁(Spec R, a)`-sets (`specEquivContAction`). This is V.7 for affine connected `S`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeV

/-- Finite étale morphisms of schemes, `@IsFinite ⊓ @Etale`. -/
def finiteEtaleHom : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale

lemma finiteEtaleHom_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteEtaleHom f ↔ IsFinite f ∧ Etale f := Iff.rfl

instance : (finiteEtaleHom.{u}).IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.inf

instance : (finiteEtaleHom.{u}).IsMultiplicative := MorphismProperty.IsMultiplicative.inf

instance : (finiteEtaleHom.{u}).HasOfPostcompProperty finiteEtaleHom where
  of_postcomp f g hg hfg := by
    have : IsFinite g := hg.1
    have : Etale g := hg.2
    have : IsFinite (f ≫ g) := hfg.1
    have : Etale (f ≫ g) := hfg.2
    exact ⟨IsFinite.of_comp f g, Etale.of_comp f g⟩

/-- V.7: the category `𝒞(S)` of étale coverings of a scheme `S`, i.e. of finite étale
`S`-schemes, with all `S`-morphisms. It is (definitionally)
`MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ S`. -/
abbrev FEt (S : Scheme.{u}) : Type (u + 1) := finiteEtaleHom.Over ⊤ S

example (S : Scheme.{u}) : FEt S = MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ S := rfl

example (S : Scheme.{u}) : HasFiniteLimits (FEt S) := inferInstance

section Affine

variable (R : CommRingCat.{u})

open CommAlgCat

/-- `Spec` of a finite étale `R`-algebra, as an étale covering of `Spec R`. -/
noncomputable def specFunctor : (FiniteEtale.{u} R)ᵒᵖ ⥤ FEt (Spec R) :=
  MorphismProperty.Comma.lift ((finiteEtale R).ι.op ⋙ algSpec R)
    (fun A ↦ by
      change finiteEtaleHom (Spec.map (CommRingCat.ofHom (algebraMap R A.unop)))
      refine ⟨?_, ?_⟩
      · rw [IsFinite.SpecMap_iff]
        exact RingHom.finite_algebraMap.mpr inferInstance
      · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
        exact RingHom.etale_algebraMap.mpr inferInstance)
    (fun _ ↦ trivial) (fun _ ↦ trivial)

/-- The functor `Spec` from finite étale `R`-algebras to étale coverings of `Spec R` is fully
faithful. -/
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
    exact ⟨Opposite.op (FiniteEtale.of R Γ(X.left, ⊤)),
      ⟨MorphismProperty.Over.isoMk X.left.isoSpec.symm (by
        change X.left.isoSpec.inv ≫ f = _
        rw [← hφ]
        rfl)⟩⟩

instance : (specFunctor R).IsEquivalence where

/-- V.7 (affine base): the étale coverings of `Spec R` are the spectra of finite étale
`R`-algebras. -/
noncomputable def specEquivalence : (FiniteEtale.{u} R)ᵒᵖ ≌ FEt (Spec R) :=
  (specFunctor R).asEquivalence

/-- The functor of geometric points of étale coverings of `S` over a point `a : W ⟶ S`
(for `W = Spec Ω` a geometric point): `X ↦ Hom_S(W, X)`. -/
def geometricPoints {S W : Scheme.{u}} (a : W ⟶ S) : FEt S ⥤ Type u :=
  MorphismProperty.Over.forget _ ⊤ S ⋙ coyoneda.obj (Opposite.op (Over.mk a))

variable (Ω : Type u) [Field Ω] [Algebra R Ω]

/-- The geometric point `Spec Ω ⟶ Spec R` defined by `R → Ω`. -/
noncomputable abbrev specPoint : Spec (CommRingCat.of Ω) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R Ω))

/-- The geometric points of `Spec A` over `Spec Ω → Spec R` are the `R`-algebra maps
`A → Ω`. -/
noncomputable def specGeometricPointsEquiv (A : FiniteEtale.{u} R) :
    (geometricPoints (specPoint R Ω)).obj ((specFunctor R).obj (Opposite.op A)) ≃
      (A →ₐ[R] Ω) :=
  ((algSpec.fullyFaithful (R := R)).homEquiv (X := Opposite.op (CommAlgCat.of R Ω))
    (Y := Opposite.op A.obj)).symm.trans
    { toFun := fun f ↦ f.unop.hom
      invFun := fun x ↦ (CommAlgCat.ofHom x).op
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- On `Spec` of finite étale algebras, the geometric points over `Spec Ω → Spec R` form the
fiber functor `A ↦ Hom_R(A, Ω)`. -/
noncomputable def specGeometricPointsIso :
    specFunctor R ⋙ geometricPoints (specPoint R Ω) ≅ fiberFunctor R Ω ⋙ FintypeCat.incl :=
  (NatIso.ofComponents (fun A ↦ (specGeometricPointsEquiv R Ω A.unop).symm.toIso)
    (fun {A B} f ↦ by
      ext (x : A.unop →ₐ[R] Ω)
      change (algSpec R).map (CommAlgCat.ofHom (x.comp f.unop.hom.hom)).op =
        (algSpec R).map (CommAlgCat.ofHom x).op ≫ (algSpec R).map f.unop.hom.op
      rw [← Functor.map_comp]
      rfl)).symm

variable [ConnectedSpace (PrimeSpectrum R)]

open PreGaloisCategory

/-- V.7 (affine connected base): the category of étale coverings of `Spec R` is a Galois
category. -/
instance galoisCategory_spec : GaloisCategory (FEt (Spec R)) :=
  galoisCategory_of_equivalence (specEquivalence R).symm

variable [IsSepClosed Ω]

/-- V.7: the fiber functor of the étale coverings of `Spec R` at the geometric point
`Spec Ω → Spec R`, with values in finite sets. By `geometricFiberInclIso` it is the functor
of geometric points over `Spec Ω → Spec R`. -/
noncomputable def geometricFiber : FEt (Spec R) ⥤ FintypeCat.{u} :=
  (specEquivalence R).inverse ⋙ fiberFunctor R Ω

instance : FiberFunctor (geometricFiber R Ω) :=
  fiberFunctor_comp_of_equivalence (specEquivalence R).symm (fiberFunctor R Ω)

/-- V.7: the fiber functor `F(X)` is the set of geometric points of `X` over `a`. -/
noncomputable def geometricFiberInclIso :
    geometricFiber R Ω ⋙ FintypeCat.incl ≅ geometricPoints (specPoint R Ω) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (specGeometricPointsIso R Ω).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (specEquivalence R).counitIso _ ≪≫ Functor.leftUnitor _

open scoped FintypeCatDiscrete in
/-- V.7: the fundamental group `π₁(Spec R, a)` is profinite and classifies the étale coverings
of `Spec R`: they are equivalent to finite sets with a continuous action of `π₁(Spec R, a)`. -/
noncomputable def specEquivContAction :
    FEt (Spec R) ≌ ContAction FintypeCat (Aut (geometricFiber R Ω)) :=
  (functorToContAction (geometricFiber R Ω)).asEquivalence

end Affine

end SGA.SGA1.ExposeV
