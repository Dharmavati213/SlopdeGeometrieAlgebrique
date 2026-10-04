/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannLocalChart
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Ring.Shrink
import Mathlib.Topology.Instances.Shrink
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Data.Countable.Small

/-!
# SGA 1, Exposé XII, 5.1: changing universes

`RiemannExistenceStatement.{u}` quantifies over `ℂ`-algebras `A : Type u`, while everything proved
here about the functor `Ψ` lives in universe `0` (schemes over `ℂ` are `Scheme.{0}`). A `ℂ`-algebra
of finite type is isomorphic to one in `Type` (a quotient of a polynomial ring), and the functor
`Ψ` is insensitive to such a change of universe:

* `TopCat.FiniteCovering.uliftEquivalence`: for a homeomorphism `X₀ ≃ₜ X`, `X₀ : Type`,
  `E₀ ↦ ULift E₀` is an equivalence between finite coverings of `X₀` and of `X` (every finite
  covering of `X` is small, `Shrink`);
* `UniverseTransport.liftFunctor`: for `e : A ≃ₐ[ℂ] A₀`, `A₀ : Type`, `S₀ ↦ ULift S₀` is an
  equivalence between finite étale `A₀`- and `A`-algebras;
* `UniverseTransport.liftFunctorCompPointsFunctorIso`: the two are intertwined by `Ψ`;
* `isEquivalence_pointsFunctor_iff_of_algEquiv` and **`riemannExistence_iff_zero`**:
  `RiemannExistenceStatement.{u} ↔ RiemannExistenceStatement.{0}`; together with
  `schemeRiemannExistence_iff`, the scheme form `SchemeRiemannExistenceStatement` gives the affine
  form in every universe (`riemannExistence_of_schemeRiemannExistence'`).
-/

noncomputable section

universe u

open CategoryTheory Topology Set Opposite

namespace TopCat.FiniteCovering

variable {X₀ : TopCat.{0}} {X : TopCat.{u}} (h : X₀ ≃ₜ X)

/-- The finite covering `ULift E₀ → X` of a finite covering `E₀ → X₀`, through `h : X₀ ≃ₜ X`. -/
def uliftObj (E₀ : FiniteCovering X₀) : FiniteCovering X :=
  ⟨Over.mk (TopCat.ofHom ⟨fun x : ULift.{u} E₀.obj.left ↦ h (E₀.obj.hom x.down),
      h.continuous.comp (E₀.obj.hom.hom.continuous.comp continuous_uliftDown)⟩),
    (E₀.isCoveringMap.homeomorph_comp h).comp_homeomorph Homeomorph.ulift, fun x ↦ by
      have : (fun y : ULift.{u} E₀.obj.left ↦ h (E₀.obj.hom y.down)) ⁻¹' {x} =
          ULift.down ⁻¹' (E₀.obj.hom ⁻¹' {h.symm x}) := by
        ext y
        exact h.toEquiv.eq_symm_apply.symm
      exact this ▸ (E₀.property.2 (h.symm x)).preimage ULift.down_injective.injOn⟩

lemma uliftObj_hom_apply (E₀ : FiniteCovering X₀) (x : (uliftObj h E₀).obj.left) :
    (uliftObj h E₀).obj.hom x = h (E₀.obj.hom (ULift.down x)) := rfl

/-- `E₀ ↦ ULift E₀`, from finite coverings of `X₀ : Type` to finite coverings of `X`, through
`h : X₀ ≃ₜ X`. -/
@[simps obj]
def uliftFunctor : FiniteCovering X₀ ⥤ FiniteCovering X where
  obj := uliftObj h
  map {E₀ F₀} f := ObjectProperty.homMk (Over.homMk (TopCat.ofHom
    ⟨fun x ↦ ULift.up (f.hom.left x.down), continuous_uliftUp.comp
      (f.hom.left.hom.continuous.comp continuous_uliftDown)⟩) (by
        ext x
        exact congrArg h (hom_left_apply f x.down)))

/-- `uliftFunctor` is fully faithful. -/
def uliftFunctorFullyFaithful : (uliftFunctor h).FullyFaithful where
  preimage {E₀ F₀} g := ObjectProperty.homMk (Over.homMk (TopCat.ofHom
    ⟨fun x ↦ (g.hom.left (ULift.up x)).down, continuous_uliftDown.comp
      (g.hom.left.hom.continuous.comp continuous_uliftUp)⟩) (by
        ext x
        exact h.injective (hom_left_apply g (ULift.up x))))

instance : (uliftFunctor h).Full := (uliftFunctorFullyFaithful h).full

instance : (uliftFunctor h).Faithful := (uliftFunctorFullyFaithful h).faithful

include h in
/-- The total space of a finite covering of `X ≃ₜ X₀` is small. -/
lemma small_left (E : FiniteCovering X) : Small.{0} E.obj.left := by
  have : Small.{0} X := small_map h.toEquiv.symm
  have (x : X) : Small.{0} {e // E.obj.hom e = x} :=
    have : Finite {e // E.obj.hom e = x} := (E.property.2 x).to_subtype
    Countable.toSmall _
  exact small_map (Equiv.sigmaFiberEquiv E.obj.hom).symm

/-- The finite covering `Shrink E → X₀` of a finite covering `E → X`. -/
def shrinkObj (E : FiniteCovering X) : FiniteCovering X₀ :=
  haveI := small_left h E
  ⟨Over.mk (TopCat.ofHom ⟨h.symm ∘ E.obj.hom ∘ (Shrink.homeomorph E.obj.left).symm,
      h.symm.continuous.comp (E.obj.hom.hom.continuous.comp
        (Shrink.homeomorph E.obj.left).symm.continuous)⟩),
    (E.isCoveringMap.homeomorph_comp h.symm).comp_homeomorph (Shrink.homeomorph E.obj.left).symm,
    fun x ↦ by
      have : (h.symm ∘ E.obj.hom ∘ (Shrink.homeomorph E.obj.left).symm) ⁻¹' {x} =
          (Shrink.homeomorph E.obj.left).symm ⁻¹' (E.obj.hom ⁻¹' {h x}) := by
        ext y
        exact h.symm.toEquiv.eq_symm_apply.symm
      exact this ▸ (E.property.2 (h x)).preimage
        (Shrink.homeomorph E.obj.left).symm.injective.injOn⟩

instance : (uliftFunctor h).EssSurj where
  mem_essImage E := by
    have := small_left h E
    refine ⟨shrinkObj h E, ⟨ObjectProperty.isoMk _ (Over.isoMk (TopCat.isoOfHomeo
      (Homeomorph.ulift.trans (Shrink.homeomorph E.obj.left).symm)) ?_)⟩⟩
    ext x
    exact (h.apply_symm_apply _).symm

instance : (uliftFunctor h).IsEquivalence where

end TopCat.FiniteCovering

namespace SGA.SGA1.ExposeXII

namespace UniverseTransport

open CommAlgCat

variable {A : Type u} [CommRing A] [Algebra ℂ A] {A₀ : Type} [CommRing A₀] [Algebra ℂ A₀]
  (e : A ≃ₐ[ℂ] A₀)

/-- `e`, as an isomorphism of `A`-algebras, `A₀` being an `A`-algebra through `e`. -/
abbrev baseAlgEquiv : letI := e.toRingHom.toAlgebra; A ≃ₐ[A] A₀ :=
  letI := e.toRingHom.toAlgebra
  AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun _ ↦ rfl

/-- `e.symm`, as an isomorphism of `A₀`-algebras, `A` being an `A₀`-algebra through `e.symm`. -/
abbrev baseAlgEquivSymm : letI := e.symm.toRingHom.toAlgebra; A₀ ≃ₐ[A₀] A :=
  letI := e.symm.toRingHom.toAlgebra
  AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv) fun _ ↦ rfl

/-- The `A`-algebra `ULift S₀` of a finite étale `A₀`-algebra `S₀` (through `e`); it is finite
étale. -/
def liftObj (S₀ : FiniteEtale.{0} A₀) : FiniteEtale.{u} A :=
  letI : Algebra A S₀ := ((algebraMap A₀ S₀).comp e.toRingHom).toAlgebra
  letI : Algebra A A₀ := e.toRingHom.toAlgebra
  haveI : IsScalarTower A A₀ S₀ := .of_algebraMap_eq fun _ ↦ rfl
  haveI : Algebra.Etale A A₀ := Algebra.Etale.of_equiv (baseAlgEquiv e)
  haveI : Module.Finite A A₀ := Module.Finite.equiv (baseAlgEquiv e).toLinearEquiv
  haveI : Algebra.Etale A S₀ := Algebra.Etale.comp A A₀ S₀
  haveI : Module.Finite A S₀ := Module.Finite.trans A₀ S₀
  haveI : Module.Finite A (ULift.{u} S₀) :=
    Module.Finite.equiv (ULift.algEquiv (R := A) (A := S₀)).symm.toLinearEquiv
  haveI : Algebra.Etale A (ULift.{u} S₀) := Algebra.Etale.of_equiv (ULift.algEquiv (R := A)).symm
  FiniteEtale.of A (ULift.{u} S₀)

lemma algebraMap_liftObj (S₀ : FiniteEtale.{0} A₀) (a : A) :
    algebraMap A (liftObj e S₀) a = ULift.up (algebraMap A₀ S₀ (e a)) := rfl

/-- `ULift f`, as a ring map. -/
def liftRingHom {S₀ T₀ : FiniteEtale.{0} A₀} (f : S₀ ⟶ T₀) :
    (liftObj e S₀).obj →+* (liftObj e T₀).obj :=
  (ULift.ringEquiv (R := T₀.obj)).symm.toRingHom.comp
    (f.hom.hom.toRingHom.comp (ULift.ringEquiv (R := S₀.obj)).toRingHom)

/-- `ULift f`, as a morphism of `A`-algebras. -/
def liftMap {S₀ T₀ : FiniteEtale.{0} A₀} (f : S₀ ⟶ T₀) :
    (liftObj e S₀).obj →ₐ[A] (liftObj e T₀).obj :=
  { toRingHom := liftRingHom e f
    commutes' := fun a ↦ congrArg ULift.up (f.hom.hom.commutes (e a)) }

/-- `S₀ ↦ ULift S₀`, from finite étale `A₀`-algebras to finite étale `A`-algebras. -/
@[simps obj]
def liftFunctor : FiniteEtale.{0} A₀ ⥤ FiniteEtale.{u} A where
  obj := liftObj e
  map {S₀ T₀} f := ObjectProperty.homMk
    (ConcreteCategory.ofHom (liftMap e f) : (liftObj e S₀).obj ⟶ (liftObj e T₀).obj)

/-- The preimage of a morphism `ULift S₀ → ULift T₀` of `A`-algebras. -/
def unliftMap {S₀ T₀ : FiniteEtale.{0} A₀} (g : (liftObj e S₀).obj →ₐ[A] (liftObj e T₀).obj) :
    S₀.obj →ₐ[A₀] T₀.obj where
  toRingHom := (ULift.ringEquiv (R := T₀.obj)).toRingHom.comp
    (g.toRingHom.comp (ULift.ringEquiv (R := S₀.obj)).symm.toRingHom)
  commutes' a₀ := by
    obtain ⟨a, rfl⟩ := e.surjective a₀
    exact congrArg ULift.down (g.commutes a)

/-- `liftFunctor` is fully faithful. -/
def liftFunctorFullyFaithful : (liftFunctor e).FullyFaithful where
  preimage {S₀ T₀} g := ObjectProperty.homMk
    (ConcreteCategory.ofHom (unliftMap e g.hom.hom) : S₀.obj ⟶ T₀.obj)
  map_preimage _ := rfl
  preimage_map _ := by
    ext
    rfl

instance : (liftFunctor e).Full := (liftFunctorFullyFaithful e).full

instance : (liftFunctor e).Faithful := (liftFunctorFullyFaithful e).faithful

/-- The finite étale `A₀`-algebra `Shrink S` of a finite étale `A`-algebra `S` (through
`e.symm`). -/
def shrinkObj (S : FiniteEtale.{u} A) : FiniteEtale.{0} A₀ :=
  haveI : Small.{0} A := small_map e.toEquiv
  haveI : Small.{0} S := Module.Finite.small A S
  letI : Algebra A₀ S := ((algebraMap A S).comp e.symm.toRingHom).toAlgebra
  letI : Algebra A₀ A := e.symm.toRingHom.toAlgebra
  haveI : IsScalarTower A₀ A S := .of_algebraMap_eq fun _ ↦ rfl
  haveI : Algebra.Etale A₀ A := Algebra.Etale.of_equiv (baseAlgEquivSymm e)
  haveI : Module.Finite A₀ A := Module.Finite.equiv (baseAlgEquivSymm e).toLinearEquiv
  haveI : Algebra.Etale A₀ S := Algebra.Etale.comp A₀ A S
  haveI : Module.Finite A₀ S := Module.Finite.trans A S
  @FiniteEtale.of A₀ _ (Shrink.{0} S) _ _
    (Module.Finite.equiv (Shrink.algEquiv A₀ S).symm.toLinearEquiv)
    (Algebra.Etale.of_equiv (Shrink.algEquiv A₀ S).symm)

/-- `ULift (Shrink S) ≃ S`, as `A`-algebras. -/
def liftObjShrinkObjAlgEquiv (S : FiniteEtale.{u} A) :
    (liftObj e (shrinkObj e S)).obj ≃ₐ[A] S.obj :=
  haveI : Small.{0} A := small_map e.toEquiv
  haveI : Small.{0} S := Module.Finite.small A S
  { toRingEquiv := (ULift.ringEquiv (R := (shrinkObj e S).obj)).trans (Shrink.ringEquiv S)
    commutes' := fun a ↦ by
      change (equivShrink S).symm (equivShrink S (algebraMap A S (e.symm (e a)))) = _
      rw [Equiv.symm_apply_apply, AlgEquiv.symm_apply_apply] }

/-- `ULift (Shrink S) ≅ S`. -/
def liftObjShrinkObjIso (S : FiniteEtale.{u} A) : liftObj e (shrinkObj e S) ≅ S :=
  ObjectProperty.isoMk _
    { hom := ConcreteCategory.ofHom (liftObjShrinkObjAlgEquiv e S).toAlgHom
      inv := ConcreteCategory.ofHom (liftObjShrinkObjAlgEquiv e S).symm.toAlgHom
      hom_inv_id := by
        ext x
        exact (liftObjShrinkObjAlgEquiv e S).symm_apply_apply x
      inv_hom_id := by
        ext x
        exact (liftObjShrinkObjAlgEquiv e S).apply_symm_apply x }

instance : (liftFunctor e).EssSurj where
  mem_essImage S := ⟨shrinkObj e S, ⟨liftObjShrinkObjIso e S⟩⟩

instance : (liftFunctor e).IsEquivalence where

/-! ### Compatibility with `Ψ` -/

/-- `ULift S₀ ≃ S₀` as `ℂ`-algebras (through `A` and `A₀`). -/
def liftObjAlgEquiv (S₀ : FiniteEtale.{0} A₀) :
    letI := algebraOfFiniteEtale ℂ A (liftObj e S₀)
    letI := algebraOfFiniteEtale ℂ A₀ S₀
    (liftObj e S₀).obj ≃ₐ[ℂ] S₀.obj :=
  letI := algebraOfFiniteEtale ℂ A (liftObj e S₀)
  letI := algebraOfFiniteEtale ℂ A₀ S₀
  { toRingEquiv := ULift.ringEquiv (R := S₀.obj)
    commutes' := fun c ↦ by
      change algebraMap A₀ S₀ (e (algebraMap ℂ A c)) = algebraMap A₀ S₀ (algebraMap ℂ A₀ c)
      rw [AlgEquiv.commutes] }

/-- The covering `S(ℂ)` of `ULift S₀` is `ULift (S₀(ℂ))`. -/
def pointsFunctorObjLiftIso (S₀ : FiniteEtale.{0} A₀) :
    (pointsFunctor ℂ A).obj (op (liftObj e S₀)) ≅
      (TopCat.FiniteCovering.uliftFunctor (X₀ := TopCat.of (Points ℂ A₀))
        (X := TopCat.of (Points ℂ A)) (Points.homeomorph e)).obj
        ((pointsFunctor ℂ A₀).obj (op S₀)) :=
  letI := algebraOfFiniteEtale ℂ A (liftObj e S₀)
  letI := algebraOfFiniteEtale ℂ A₀ S₀
  ObjectProperty.isoMk _ (Over.isoMk (TopCat.isoOfHomeo
    ((Points.homeomorph (liftObjAlgEquiv e S₀)).symm.trans Homeomorph.ulift.symm)) (by
      ext χ
      rfl))

/-- `Ψ` intertwines `liftFunctor` and `TopCat.FiniteCovering.uliftFunctor`. -/
def liftFunctorCompPointsFunctorIso :
    (liftFunctor e).op ⋙ pointsFunctor ℂ A ≅
      pointsFunctor ℂ A₀ ⋙ TopCat.FiniteCovering.uliftFunctor (X₀ := TopCat.of (Points ℂ A₀))
        (X := TopCat.of (Points ℂ A)) (Points.homeomorph e) :=
  NatIso.ofComponents (fun S₀ ↦ pointsFunctorObjLiftIso e S₀.unop) fun f ↦ by
    ext χ
    rfl

end UniverseTransport

/-- XII.5.1 is invariant under isomorphisms of `ℂ`-algebras across universes: for
`e : A ≃ₐ[ℂ] A₀`, `A₀ : Type`, the functor `Ψ` is an equivalence for `A` if and only if it is one
for `A₀`. -/
theorem isEquivalence_pointsFunctor_iff_of_algEquiv {A : Type u} [CommRing A] [Algebra ℂ A]
    {A₀ : Type} [CommRing A₀] [Algebra ℂ A₀] (e : A ≃ₐ[ℂ] A₀) :
    (pointsFunctor ℂ A).IsEquivalence ↔ (pointsFunctor ℂ A₀).IsEquivalence := by
  let L := TopCat.FiniteCovering.uliftFunctor (X₀ := TopCat.of (Points ℂ A₀))
    (X := TopCat.of (Points ℂ A)) (Points.homeomorph e)
  have hiso := UniverseTransport.liftFunctorCompPointsFunctorIso e
  constructor
  · intro _
    have : (pointsFunctor ℂ A₀ ⋙ L).IsEquivalence :=
      (Functor.isEquivalence_iff_of_iso hiso).mp inferInstance
    exact Functor.isEquivalence_of_comp_right _ L
  · intro _
    have : ((UniverseTransport.liftFunctor e).op ⋙ pointsFunctor ℂ A).IsEquivalence :=
      (Functor.isEquivalence_iff_of_iso hiso).mpr inferInstance
    exact Functor.isEquivalence_of_comp_left (UniverseTransport.liftFunctor e).op _

/-- XII.5.1: the affine form of the Riemann existence theorem in universe `u` is equivalent to
the affine form in universe `0` (every `ℂ`-algebra of finite type is isomorphic to one in
`Type`). -/
theorem riemannExistence_iff_zero :
    RiemannExistenceStatement.{u} ↔ RiemannExistenceStatement.{0} := by
  constructor
  · intro H A _ _ _
    have : Algebra.FiniteType ℂ (ULift.{u} A) :=
      Algebra.FiniteType.equiv inferInstance (ULift.algEquiv (R := ℂ) (A := A)).symm
    exact (isEquivalence_pointsFunctor_iff_of_algEquiv
      (ULift.algEquiv (R := ℂ) (A := A))).mp (H (ULift.{u} A))
  · intro H A _ _ _
    obtain ⟨P, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton ℂ A
    exact (isEquivalence_pointsFunctor_iff_of_algEquiv e).mpr (H P.eval.obj)

/-- XII.5.1: the scheme form of the Riemann existence theorem implies the affine form in every
universe. -/
theorem riemannExistence_of_schemeRiemannExistence' (H : SchemeRiemannExistenceStatement) :
    RiemannExistenceStatement.{u} :=
  riemannExistence_iff_zero.mpr (riemannExistence_of_schemeRiemannExistence H)

end SGA.SGA1.ExposeXII
