/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannLocalAffine
import SGA.SGA1.ExposeXII.FundamentalGroupQuotient
import SGA.SGA1.ExposeV.ExactFunctors

/-!
# SGA 1, Exposé XII, 5.1: formal reductions of the Riemann existence theorem

For `X` connected and locally of finite type over `ℂ`, with `X(ℂ)` semilocally simply connected
(`X(ℂ)` is always locally path-connected, by the instance
`SchemePoints.locallyPathConnectedSpace`), the functor `Ψ : Y ↦ Y(ℂ)` is fully faithful
(`SGA.SGA1.ExposeXII.RiemannFull`) and induces a surjection `π̂₁(X(ℂ), x) ↠ π₁(X, x)`
(`SGA.SGA1.ExposeXII.FundamentalGroupQuotient`). By Galois theory (V.6.10):

* `isEquivalence_schemePointsFunctor_iff_injective`: XII.5.1 holds for `X` if and only if that
  surjection is injective;
* `isEquivalence_schemePointsFunctor_of_forall_isConnected`: XII.5.1 holds for `X` as soon as
  every *connected* finite covering of `X(ℂ)` comes from a finite étale covering of `X` (`Ψ`
  preserves finite sums, every finite covering being a finite sum of connected ones); and the
  affine version `isEquivalence_pointsFunctor_of_forall_isConnected`.
-/

noncomputable section

universe u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits PreGaloisCategory Topology AlgebraicGeometry

namespace SGA.SGA1.ExposeXII

section Galois

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] {D : Type v₁} [Category.{v₂} D]
  [GaloisCategory D]

/-- A functor of Galois categories preserving finite sums is essentially surjective as soon as
every connected object is in its essential image (every object being a finite sum of connected
objects). -/
theorem essSurj_of_forall_isConnected (H : C ⥤ D) [PreservesFiniteCoproducts H]
    (h : ∀ Y : D, IsConnected Y → H.essImage Y) : H.EssSurj where
  mem_essImage Y := by
    obtain ⟨ι, _, f, e, hc⟩ := has_decomp_connected_components' Y
    choose X hX using fun i ↦ h (f i) (hc i)
    exact ⟨∐ X, ⟨PreservesCoproduct.iso H X ≪≫ Sigma.mapIso (fun i ↦ (hX i).some) ≪≫ e⟩⟩

end Galois

section Scheme

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [ConnectedSpace X] [SemilocallySimplyConnectedSpace (SchemePoints ℂ X)]

/-- XII.5.1 and XII.5.2: for `X` connected, locally of finite type over `ℂ`, with `X(ℂ)`
semilocally simply connected, and `x ∈ X(ℂ)`, the Riemann existence theorem
holds for `X` (`Ψ` is an equivalence) if and only if the surjection
`π̂₁(X(ℂ), x) ↠ π₁(X, x)` (`surjective_autWhiskerLeft_schemePointsFunctor`) is injective
(V.6.10). -/
theorem isEquivalence_schemePointsFunctor_iff_injective (x : SchemePoints ℂ X) :
    haveI : ConnectedSpace (SchemePoints ℂ X) := SchemePoints.connectedComparison X ‹_›
    haveI : PathConnectedSpace (SchemePoints ℂ X) := .of_locallyPathConnectedSpace
    (schemePointsFunctor ℂ X).IsEquivalence ↔
      Function.Injective (SGA.SGA1.ExposeX.autWhiskerLeft (schemePointsFunctor ℂ X)
        (schemePointsFunctorCompFiberIso ℂ x)) := by
  have : ConnectedSpace (SchemePoints ℂ X) := SchemePoints.connectedComparison X ‹_›
  have : PathConnectedSpace (SchemePoints ℂ X) := .of_locallyPathConnectedSpace
  have hs := surjective_autWhiskerLeft_schemePointsFunctor X x
  refine ⟨fun _ ↦ (ExposeX.autWhiskerLeft_bijective_of_isEquivalence _ _).1, fun hi ↦ ?_⟩
  have : FiberFunctor (schemePointsFunctor ℂ X ⋙ TopCat.FiniteCovering.fiber x) :=
    .of_iso (schemePointsFunctorCompFiberIso ℂ x).symm
  have h10 := (ExposeV.bijective_autWhiskerLeft_tfae (schemePointsFunctor ℂ X)
    (TopCat.FiniteCovering.fiber x)).out 1 2
  refine h10.mp ?_
  have key (σ : Aut (TopCat.FiniteCovering.fiber (X := TopCat.of (SchemePoints ℂ X)) x)) :
      ExposeX.autWhiskerLeft (schemePointsFunctor ℂ X) (schemePointsFunctorCompFiberIso ℂ x) σ =
        (schemePointsFunctorCompFiberIso ℂ x).conjAut
          (ExposeV.autWhiskerLeft (schemePointsFunctor ℂ X) (TopCat.FiniteCovering.fiber x) σ) := by
    ext Y y
    rfl
  have hfun : ⇑(ExposeV.autWhiskerLeft (schemePointsFunctor ℂ X) (TopCat.FiniteCovering.fiber x)) =
      (schemePointsFunctorCompFiberIso ℂ x).conjAut.symm ∘
        ⇑(ExposeX.autWhiskerLeft (schemePointsFunctor ℂ X)
          (schemePointsFunctorCompFiberIso ℂ x)) := by
    funext σ
    rw [Function.comp_apply, MulEquiv.eq_symm_apply, key]
  rw [hfun]
  exact (MulEquiv.bijective _).comp ⟨hi, hs⟩

/-- XII.5.1 from its connected case: for `X` connected, locally of finite type over `ℂ`, with
`X(ℂ)` semilocally simply connected, if every connected finite
covering of `X(ℂ)` is isomorphic to `Y(ℂ)` for a finite étale covering `Y` of `X`, then `Ψ` is an
equivalence of categories. -/
theorem isEquivalence_schemePointsFunctor_of_forall_isConnected
    (h : haveI : ConnectedSpace (SchemePoints ℂ X) := SchemePoints.connectedComparison X ‹_›
      haveI : PathConnectedSpace (SchemePoints ℂ X) := .of_locallyPathConnectedSpace
      ∀ E : TopCat.FiniteCovering (TopCat.of (SchemePoints ℂ X)), IsConnected E →
        (schemePointsFunctor ℂ X).essImage E) :
    (schemePointsFunctor ℂ X).IsEquivalence := by
  have : ConnectedSpace (SchemePoints ℂ X) := SchemePoints.connectedComparison X ‹_›
  have : PathConnectedSpace (SchemePoints ℂ X) := .of_locallyPathConnectedSpace
  let x : SchemePoints ℂ X := Classical.arbitrary _
  have : FiberFunctor (schemePointsFunctor ℂ X ⋙ TopCat.FiniteCovering.fiber x) :=
    .of_iso (schemePointsFunctorCompFiberIso ℂ x).symm
  have := (ExposeV.exact_of_fiberFunctor_comp (schemePointsFunctor ℂ X)
    (TopCat.FiniteCovering.fiber x)).2
  have := essSurj_of_forall_isConnected (schemePointsFunctor ℂ X) h
  exact { }

end Scheme

section Affine

open CommAlgCat

variable (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
  [ConnectedSpace (PrimeSpectrum A)] [SemilocallySimplyConnectedSpace (Points ℂ A)]

/-- XII.5.1 from its connected case, affine form: for `A` of finite type over `ℂ` with
`X = Spec A` connected and `X(ℂ)` semilocally simply connected, if
every connected finite covering of `X(ℂ)` is isomorphic to `S(ℂ)` for a finite étale
`A`-algebra `S`, then `Ψ` is an equivalence of categories. (Stated for `A : Type`.) -/
theorem isEquivalence_pointsFunctor_of_forall_isConnected
    (h : haveI : ConnectedSpace (Points ℂ A) := Points.connectedComparison A ‹_›
      haveI : PathConnectedSpace (Points ℂ A) := .of_locallyPathConnectedSpace
      ∀ E : TopCat.FiniteCovering (TopCat.of (Points ℂ A)), IsConnected E →
        (pointsFunctor ℂ A).essImage E) :
    (pointsFunctor ℂ A).IsEquivalence := by
  have : ConnectedSpace (Points ℂ A) := Points.connectedComparison A ‹_›
  have : PathConnectedSpace (Points ℂ A) := .of_locallyPathConnectedSpace
  let x : Points ℂ A := Classical.arbitrary _
  let := x.toRingHom.toAlgebra
  have : FiberFunctor (pointsFunctor ℂ A ⋙ TopCat.FiniteCovering.fiber x) :=
    .of_iso (pointsFunctorCompFiberIso ℂ A x).symm
  have := (ExposeV.exact_of_fiberFunctor_comp (pointsFunctor ℂ A)
    (TopCat.FiniteCovering.fiber x)).2
  have := essSurj_of_forall_isConnected (pointsFunctor ℂ A) h
  exact { }

end Affine

end SGA.SGA1.ExposeXII
