/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.FundamentalGroupQuotient
import SGA.SGA1.ExposeV.ExactFunctors
import Mathlib.Analysis.Convex.Contractible

/-!
# SGA 1, Exposé XII, 5.1 when `X(ℂ)` is simply connected; affine space

If `X(ℂ)` is simply connected, the Riemann existence theorem XII.5.1 for `X` holds without any
analysis: the profinite completion of `π₁(X(ℂ))` is trivial, and the functor
`Ψ : Y ↦ Y(ℂ)` preserves connectedness (XII.2.4), so by V.6.10 it is an equivalence. In
particular XII.5.1 holds for affine space `𝔸ⁿ_ℂ`, and every finite étale covering of `𝔸ⁿ_ℂ` is
trivial: `π₁(𝔸ⁿ_ℂ) = 1`.

* `isEquivalence_of_subsingleton_aut`: V.6.10 for a target with trivial fundamental group;
* `TopCat.FiniteCovering.subsingleton_aut_fiber`: for `X` simply connected and locally
  path-connected, the automorphism group of the fibre functor of finite coverings is trivial;
* `isEquivalence_schemePointsFunctor_of_simplyConnectedSpace`,
  `isEquivalence_pointsFunctor_of_simplyConnectedSpace`: XII.5.1 when `X(ℂ)` is simply connected
  (`X(ℂ)` is locally path-connected by xii52's instance `SchemePoints.locallyPathConnectedSpace`);
* `riemannExistence_mvPolynomial`: XII.5.1 for `X = 𝔸ⁿ_ℂ = Spec ℂ[x₁, …, xₙ]`, and
  `subsingleton_aut_etaleFiber_mvPolynomial`: its étale fundamental group is trivial. This is a
  transcendental proof, over `ℂ` only. For `n = 1` the algebraic statement, over any algebraically
  closed field of characteristic `0`, is `SGA.SGA1.ExposeXIII.aut_eq_one_affineLine` (XIII.2.12
  with `g = 0`, `n = 1`); for `n ≥ 2` it would follow algebraically from it by induction with
  `SGA.SGA1.ExposeXIII.bijective_map_prod_affineLine_of_isNormalScheme` (XIII.4.6), which is not
  done here.
-/

noncomputable section

universe u₁ u₂ v₁ v₂ w u

open CategoryTheory PreGaloisCategory Topology

namespace SGA.SGA1.ExposeXII

section Galois

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] {D : Type v₁} [Category.{v₂} D]
  [GaloisCategory D] (H : C ⥤ D) (F' : D ⥤ FintypeCat.{w}) [FiberFunctor F']
  [FiberFunctor (H ⋙ F')]

/-- V.6.10 for a Galois category with trivial fundamental group: if `Aut F'` is trivial and `H`
transforms connected objects into connected objects, then `H` is an equivalence. (The
homomorphism `Aut F' → Aut (H ⋙ F')` is then surjective by V.6.9, and injective since its source
is trivial.) -/
theorem isEquivalence_of_subsingleton_aut [Subsingleton (Aut F')] [PreservesIsConnected H] :
    H.IsEquivalence := by
  have h9 := (ExposeV.surjective_autWhiskerLeft_tfae H F').out 2 1
  have h10 := (ExposeV.bijective_autWhiskerLeft_tfae H F').out 1 2
  exact h10.mp ⟨fun _ _ _ ↦ Subsingleton.elim _ _, h9.mp inferInstance⟩

end Galois

end SGA.SGA1.ExposeXII

namespace TopCat.FiniteCovering

variable {X : TopCat.{u}} [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]

/-- For `X` simply connected and locally path-connected, the fundamental group of the Galois
category of finite coverings of `X` (the profinite completion of `π₁(X, x) = 1`) is trivial. -/
theorem subsingleton_aut_fiber (x : X) : Subsingleton (Aut (fiber x)) := by
  suffices h : ∀ σ : Aut (fiber x), σ = 1 from ⟨fun σ τ ↦ (h σ).trans (h τ).symm⟩
  intro σ
  obtain ⟨c, rfl⟩ := (autFiberEquiv x).symm.surjective σ
  refine Aut.ext (NatTrans.ext (funext fun E ↦ FintypeCat.hom_ext _ _ fun e ↦ ?_))
  change ((autFiberEquiv x).symm c).hom.app E e = e
  rw [autFiberEquiv_symm_apply_hom_app]
  obtain ⟨g, hg, -⟩ := ProfiniteGrp.ProfiniteCompletion.exists_smul_eq_smul
    ((monodromyAction x).obj E) ((monodromyAction x).obj E) c
  rw [hg, Subsingleton.elim g 1, one_smul]

end TopCat.FiniteCovering

namespace SGA.SGA1.ExposeXII

open AlgebraicGeometry

section Scheme

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [SimplyConnectedSpace (SchemePoints ℂ X)]

/-- XII.5.1 when `X(ℂ)` is simply connected: for `X` locally of finite type over `ℂ` with `X(ℂ)`
simply connected, the functor `Ψ : Y ↦ Y(ℂ)` from finite étale coverings of `X` to finite
coverings of `X(ℂ)` is an equivalence of categories. -/
theorem isEquivalence_schemePointsFunctor_of_simplyConnectedSpace :
    (schemePointsFunctor ℂ X).IsEquivalence := by
  have : ConnectedSpace X := (SchemePoints.connectedSpace_iff' X).mp inferInstance
  let x : SchemePoints ℂ X := Classical.arbitrary _
  have : FiberFunctor (schemePointsFunctor ℂ X ⋙ TopCat.FiniteCovering.fiber x) :=
    .of_iso (schemePointsFunctorCompFiberIso ℂ x).symm
  have : PreservesIsConnected (schemePointsFunctor ℂ X) :=
    ⟨fun {Y} _ ↦ isConnected_schemePointsFunctor_obj X Y⟩
  have := TopCat.FiniteCovering.subsingleton_aut_fiber (X := TopCat.of (SchemePoints ℂ X)) x
  exact isEquivalence_of_subsingleton_aut _ (TopCat.FiniteCovering.fiber x)

/-- XII.5.2 when `X(ℂ)` is simply connected: the étale fundamental group of `X` is trivial
(`X` is simply connected in the sense of Exposé V), for `X` locally of finite type over `ℂ` with
`X(ℂ)` simply connected. -/
theorem subsingleton_etaleFundamentalGroup_of_simplyConnectedSpace (x : SchemePoints ℂ X) :
    Subsingleton (ExposeV.etaleFundamentalGroup ℂ x.1) :=
  have := isEquivalence_schemePointsFunctor_of_simplyConnectedSpace X
  have := TopCat.FiniteCovering.subsingleton_aut_fiber (X := TopCat.of (SchemePoints ℂ X)) x
  (etaleFundamentalGroupEquivAutFiber ℂ x).toEquiv.subsingleton

end Scheme

section Affine

open CommAlgCat

variable (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
  [SimplyConnectedSpace (Points ℂ A)]

/-- XII.5.1, affine case, when `X(ℂ)` is simply connected: for `A` of finite type over `ℂ` with
`X(ℂ)` simply connected, `X = Spec A`, the functor `Ψ` from finite étale `A`-algebras to finite
coverings of `X(ℂ)` is an equivalence of categories. (Stated for `A : Type`, universe `0`.) -/
theorem isEquivalence_pointsFunctor_of_simplyConnectedSpace :
    (pointsFunctor ℂ A).IsEquivalence := by
  have : ConnectedSpace (PrimeSpectrum A) := Points.connectedSpace_iff'.mp inferInstance
  let x : Points ℂ A := Classical.arbitrary _
  let := x.toRingHom.toAlgebra
  have : FiberFunctor (pointsFunctor ℂ A ⋙ TopCat.FiniteCovering.fiber x) :=
    .of_iso (pointsFunctorCompFiberIso ℂ A x).symm
  have : PreservesIsConnected (pointsFunctor ℂ A) :=
    ⟨fun {S} _ ↦ isConnected_pointsFunctor_obj A S⟩
  have := TopCat.FiniteCovering.subsingleton_aut_fiber (X := TopCat.of (Points ℂ A)) x
  exact isEquivalence_of_subsingleton_aut _ (TopCat.FiniteCovering.fiber x)

end Affine

section AffineSpace

variable (n : ℕ)

/-- `𝔸ⁿ(ℂ) = ℂⁿ` is simply connected. -/
instance simplyConnectedSpace_points_mvPolynomial :
    SimplyConnectedSpace (Points ℂ (MvPolynomial (Fin n) ℂ)) :=
  have := (Points.homeomorphMvPolynomial (K := ℂ) (Fin n)).contractibleSpace
  inferInstance


/-- XII.5.1 for affine space `𝔸ⁿ_ℂ = Spec ℂ[x₁, …, xₙ]`: the functor `Ψ` from finite étale
`ℂ[x₁, …, xₙ]`-algebras to finite coverings of `ℂⁿ` is an equivalence of categories (`ℂⁿ` being
simply connected). -/
theorem riemannExistence_mvPolynomial : (pointsFunctor ℂ (MvPolynomial (Fin n) ℂ)).IsEquivalence :=
  isEquivalence_pointsFunctor_of_simplyConnectedSpace _

/-- `π₁(𝔸ⁿ_ℂ) = 1`: the étale fundamental group of `Spec ℂ[x₁, …, xₙ]` (the automorphism group
of the fibre functor of finite étale `ℂ[x₁, …, xₙ]`-algebras at any `ℂ`-point) is trivial.
Transcendental proof, over `ℂ` (`ℂⁿ` is simply connected). For `n = 1` this is also
`SGA.SGA1.ExposeXIII.aut_eq_one_affineLine` (XIII.2.12 with `g = 0`, `n = 1`, proved
algebraically over any algebraically closed field of characteristic `0`); the case `n ≥ 2` is
not proved algebraically in this repository. -/
theorem subsingleton_aut_etaleFiber_mvPolynomial (x : Points ℂ (MvPolynomial (Fin n) ℂ)) :
    Subsingleton (Aut (etaleFiber ℂ (MvPolynomial (Fin n) ℂ) x)) :=
  have := riemannExistence_mvPolynomial n
  have := TopCat.FiniteCovering.subsingleton_aut_fiber
    (X := TopCat.of (Points ℂ (MvPolynomial (Fin n) ℂ))) x
  (autContinuousMulEquiv (pointsFunctor ℂ _) (pointsFunctorCompFiberIso ℂ _ x)).symm.toEquiv
    |>.subsingleton

end AffineSpace

end SGA.SGA1.ExposeXII
