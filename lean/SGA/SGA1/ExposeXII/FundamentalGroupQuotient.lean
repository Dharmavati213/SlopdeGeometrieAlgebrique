/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.FundamentalGroup
import SGA.SGA1.ExposeX.GaloisFunctors
import SGA.SGA1.ExposeV.QuotientHasQuotients
import SGA.Foundations.Topology.PathConnectedHelpers
import SGA.Foundations.Topology.FiniteCoveringMonodromy
import SGA.SGA1.ExposeXII.LocalTopologyLPC

/-!
# SGA 1, Exposé XII, 5.2: `π₁(X, x)` is a quotient of `π̂₁(X(ℂ), x)`

XII.5.2 says that for `X` connected and locally of finite type over `ℂ`, the étale fundamental
group `π₁(X, x)` is the profinite completion of `π₁(X(ℂ), x)`. One half of it needs no Riemann
existence: the homomorphism `π̂₁(X(ℂ), x) → π₁(X, x)` induced by the functor
`Ψ : Y ↦ Y(ℂ)` (`schemePointsFunctor`) from finite étale coverings of `X` to finite coverings of
`X(ℂ)` is surjective. By V.6.9 this amounts to `Ψ` preserving connectedness, which is XII.2.4
(`SchemePoints.connectedComparison`) applied to the coverings, together with the fact that a
finite covering is a connected object of the Galois category of finite coverings if and only if
its total space is connected (`TopCat.FiniteCovering.isConnected_iff_connectedSpace`).
(Fullness of `Ψ`, step 1) of the proof of XII.5.1, is in `SGA.SGA1.ExposeXII.RiemannFull`.)

Here `π̂₁(X(ℂ), x)` is the automorphism group of the fibre functor of finite coverings of `X(ℂ)`
at `x`, which is the profinite completion of `π₁(X(ℂ), x)` (`TopCat.FiniteCovering.autFiberEquiv`),
and `π₁(X, x)` is `ExposeV.etaleFundamentalGroup ℂ x.1`.

* `surjective_autWhiskerLeft_schemePointsFunctor`: surjectivity for `X` connected with `X(ℂ)`
  semilocally simply connected (`X(ℂ)` is always locally path-connected: xii52's instance
  `SchemePoints.locallyPathConnectedSpace`, `SGA.SGA1.ExposeXII.LocalTopologyLPC`);
* `surjective_autWhiskerLeft_schemePointsFunctor_of_smooth`: unconditional for `X` smooth over
  `ℂ`;
* the affine versions, for `X = Spec A` with `A : Type` (`pointsFunctor`, fibre functors of finite
  étale `A`-algebras): `surjective_autWhiskerLeft_pointsFunctor`,
  `surjective_autWhiskerLeft_pointsFunctor_of_smooth`.
-/

noncomputable section

universe u

open CategoryTheory Topology Set PreGaloisCategory

namespace TopCat.FiniteCovering

variable {X : TopCat.{u}}

variable [PathConnectedSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]

/-- A finite covering of `X` whose total space is path-connected (and nonempty) is a connected
object of the Galois category of finite coverings of `X`. -/
theorem isConnected_of_pathConnectedSpace (E : FiniteCovering X)
    [PathConnectedSpace E.obj.left] : IsConnected E := by
  let x : X := Classical.arbitrary X
  have : Nonempty ((fiber x).obj E) := by
    obtain ⟨e⟩ : Nonempty E.obj.left := inferInstance
    let γ : Path.Homotopic.Quotient (E.obj.hom e) x := .mk (PathConnectedSpace.somePath _ _)
    exact ⟨E.isCoveringMap.monodromy γ ⟨e, rfl⟩⟩
  have : MulAction.IsPretransitive (Aut (fiber x)) ((fiber x).obj E) := ⟨fun e₁ e₂ ↦ by
    obtain ⟨γ, hγ⟩ := exists_monodromy_eq x E e₁ e₂
    refine ⟨(autFiberEquiv x).symm (ProfiniteGrp.ProfiniteCompletion.etaFn _ γ), ?_⟩
    change ((autFiberEquiv x).symm _).hom.app E e₁ = e₂
    rw [autFiberEquiv_symm_apply_hom_app, ProfiniteGrp.ProfiniteCompletion.etaFn_smul,
      monodromyAction_smul]
    exact hγ⟩
  exact SGA.SGA1.ExposeX.isConnected_of_isPretransitive (fiber x) E

/-- A finite covering of `X` whose total space is connected and locally path-connected is a
connected object of the Galois category of finite coverings of `X`. -/
theorem isConnected_of_connectedSpace (E : FiniteCovering X) [ConnectedSpace E.obj.left]
    [LocallyPathConnectedSpace E.obj.left] : IsConnected E :=
  have : PathConnectedSpace E.obj.left := .of_locallyPathConnectedSpace
  isConnected_of_pathConnectedSpace E

/-- A connected object of the Galois category of finite coverings of `X` has a connected (indeed
path-connected) total space: the monodromy action on a fibre is transitive, and paths lift. -/
theorem connectedSpace_of_isConnected (E : FiniteCovering X) [IsConnected E] :
    ConnectedSpace E.obj.left := by
  let x : X := Classical.arbitrary X
  obtain ⟨e₀⟩ := nonempty_fiber_of_isConnected (fiber x) E
  have hjoin (e₁ e₂ : E.obj.hom ⁻¹' {x}) : Joined e₁.1 e₂.1 := by
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut (fiber x))
      (show (fiber x).obj E from e₁) (show (fiber x).obj E from e₂)
    obtain ⟨c, rfl⟩ := (autFiberEquiv x).symm.surjective σ
    obtain ⟨g, hg, -⟩ := ProfiniteGrp.ProfiniteCompletion.exists_smul_eq_smul
      ((monodromyAction x).obj E) ((monodromyAction x).obj E) c
    have hm : E.isCoveringMap.monodromy g e₁ = e₂ := by
      refine (monodromyAction_smul x E g e₁).symm.trans ?_
      refine (hg e₁).symm.trans ?_
      exact (autFiberEquiv_symm_apply_hom_app x c E e₁).symm.trans hσ
    rw [← hm]
    exact ⟨(E.isCoveringMap.liftPathQuotient g e₁).out⟩
  have hjoin' (e : E.obj.left) : Joined e e₀.1 := by
    let γ : Path.Homotopic.Quotient (E.obj.hom e) x := .mk (PathConnectedSpace.somePath _ _)
    have h₁ : Joined e (E.isCoveringMap.monodromy γ ⟨e, rfl⟩).1 :=
      ⟨(E.isCoveringMap.liftPathQuotient γ ⟨e, rfl⟩).out⟩
    exact h₁.trans (hjoin _ e₀)
  have : PathConnectedSpace E.obj.left :=
    ⟨⟨e₀.1⟩, fun a b ↦ (hjoin' a).trans (hjoin' b).symm⟩
  infer_instance

/-- A finite covering of `X` is a connected object of the Galois category of finite coverings if
and only if its total space is connected. -/
theorem isConnected_iff_connectedSpace (E : FiniteCovering X) :
    IsConnected E ↔ ConnectedSpace E.obj.left := by
  refine ⟨fun _ ↦ connectedSpace_of_isConnected E, fun _ ↦ ?_⟩
  have := E.isCoveringMap.isLocalHomeomorph.locallyPathConnectedSpace
  exact isConnected_of_connectedSpace E

end TopCat.FiniteCovering

namespace SGA.SGA1.ExposeXII

open AlgebraicGeometry

section Scheme

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]

/-- XII.2.4 for the finite étale coverings of `X`: if `Y` is connected, so is `Y(ℂ)`, the total
space of the finite covering `Ψ(Y)`. -/
theorem connectedSpace_schemePointsFunctor_obj (Y : FiniteEtaleCovering X)
    [ConnectedSpace Y.left] : ConnectedSpace ((schemePointsFunctor ℂ X).obj Y).obj.left := by
  let := overOfCovering ℂ X Y
  have : IsFinite Y.hom' := Y.prop.1
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (Y.hom' ≫ X ↘ Spec (.of ℂ))
    infer_instance
  exact SchemePoints.connectedComparison Y.left ‹_›

/-- XII.5.1, XII.5.2: for `X(ℂ)` path-connected and semilocally simply connected, the functor
`Ψ : Y ↦ Y(ℂ)` sends connected finite étale coverings of `X` to connected finite coverings of
`X(ℂ)` (XII.2.4; `Y(ℂ)` is locally path-connected, being locally homeomorphic to `X(ℂ)`). -/
theorem isConnected_schemePointsFunctor_obj [PathConnectedSpace (SchemePoints ℂ X)]
    [SemilocallySimplyConnectedSpace (SchemePoints ℂ X)] (Y : FiniteEtaleCovering X)
    [IsConnected Y] : IsConnected ((schemePointsFunctor ℂ X).obj Y) :=
  have := ExposeV.FEt.connectedSpace_of_isConnected Y
  have := connectedSpace_schemePointsFunctor_obj X Y
  have := ((schemePointsFunctor ℂ X).obj Y).isCoveringMap.isLocalHomeomorph
    |>.locallyPathConnectedSpace
  TopCat.FiniteCovering.isConnected_of_connectedSpace _

/-- XII.5.2, surjectivity: for `X` connected and locally of finite type over `ℂ`, with `X(ℂ)`
semilocally simply connected, and `x ∈ X(ℂ)`, the homomorphism
`π̂₁(X(ℂ), x) → π₁(X, x)` induced by the functor `Ψ : Y ↦ Y(ℂ)` is surjective (V.6.9 with
XII.2.4). Here `π̂₁(X(ℂ), x)` is the automorphism group of the fibre functor at `x` of finite
coverings of `X(ℂ)`, the profinite completion of `π₁(X(ℂ), x)`
(`TopCat.FiniteCovering.autFiberEquiv`), and `π₁(X, x)` is `ExposeV.etaleFundamentalGroup ℂ x.1`.
(`X(ℂ)` is locally path-connected by the instance `SchemePoints.locallyPathConnectedSpace`.) -/
theorem surjective_autWhiskerLeft_schemePointsFunctor [ConnectedSpace X]
    [SemilocallySimplyConnectedSpace (SchemePoints ℂ X)] (x : SchemePoints ℂ X) :
    haveI : ConnectedSpace (SchemePoints ℂ X) := SchemePoints.connectedComparison X ‹_›
    haveI : PathConnectedSpace (SchemePoints ℂ X) := .of_locallyPathConnectedSpace
    Function.Surjective (SGA.SGA1.ExposeX.autWhiskerLeft (schemePointsFunctor ℂ X)
      (schemePointsFunctorCompFiberIso ℂ x)) := by
  have : ConnectedSpace (SchemePoints ℂ X) := SchemePoints.connectedComparison X ‹_›
  have : PathConnectedSpace (SchemePoints ℂ X) := .of_locallyPathConnectedSpace
  exact ExposeX.autWhiskerLeft_surjective_of_isConnected _ _ fun Y _ ↦
    isConnected_schemePointsFunctor_obj X Y

/-- XII.5.2, surjectivity, smooth case: for `X` connected and smooth over `ℂ` and `x ∈ X(ℂ)`, the
homomorphism `π̂₁(X(ℂ), x) → π₁(X, x)` induced by the functor `Ψ : Y ↦ Y(ℂ)` is surjective
(`X(ℂ)` is locally homeomorphic to `ℂⁿ`). -/
theorem surjective_autWhiskerLeft_schemePointsFunctor_of_smooth [Smooth (X ↘ Spec (.of ℂ))]
    [ConnectedSpace X] (x : SchemePoints ℂ X) :
    haveI : ConnectedSpace (SchemePoints ℂ X) := SchemePoints.connectedComparison X ‹_›
    haveI := SchemePoints.stronglyLocallyContractibleSpace_of_smooth (𝕜 := ℂ) X
    haveI : PathConnectedSpace (SchemePoints ℂ X) := .of_locallyPathConnectedSpace
    Function.Surjective (SGA.SGA1.ExposeX.autWhiskerLeft (schemePointsFunctor ℂ X)
      (schemePointsFunctorCompFiberIso ℂ x)) :=
  have := SchemePoints.stronglyLocallyContractibleSpace_of_smooth (𝕜 := ℂ) X
  surjective_autWhiskerLeft_schemePointsFunctor X x

end Scheme

/-! ### The affine case -/

section Affine

open CommAlgCat

variable (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

/-- XII.2.4 for finite étale `A`-algebras: if `Spec S` is connected, so is `S(ℂ)`, the total
space of the finite covering `Ψ(S)`. -/
theorem connectedSpace_pointsFunctor_obj (S : FiniteEtale A) [ConnectedSpace (PrimeSpectrum S)] :
    ConnectedSpace ((pointsFunctor ℂ A).obj (Opposite.op S)).obj.left := by
  let := algebraOfFiniteEtale ℂ A S
  have := isScalarTower_of_finiteEtale ℂ A S
  have : Algebra.FiniteType ℂ S := .trans (S := A) inferInstance inferInstance
  exact Points.connectedComparison S ‹_›

variable [ConnectedSpace (PrimeSpectrum A)]

/-- XII.5.1, XII.5.2, affine case: for `X(ℂ)` path-connected and semilocally simply connected,
`X = Spec A`, the functor `Ψ : S ↦ S(ℂ)` sends connected finite étale `A`-algebras to connected
finite coverings of `X(ℂ)` (XII.2.4). -/
theorem isConnected_pointsFunctor_obj [PathConnectedSpace (Points ℂ A)]
    [SemilocallySimplyConnectedSpace (Points ℂ A)]
    (S : (FiniteEtale A)ᵒᵖ) [IsConnected S] : IsConnected ((pointsFunctor ℂ A).obj S) :=
  have := (ExposeV.isConnected_op_iff_connectedSpace A S.unop).mp ‹_›
  have := connectedSpace_pointsFunctor_obj A S.unop
  have := ((pointsFunctor ℂ A).obj S).isCoveringMap.isLocalHomeomorph
    |>.locallyPathConnectedSpace
  TopCat.FiniteCovering.isConnected_of_connectedSpace _

/-- XII.5.2, surjectivity, affine case: for `X = Spec A` connected, `A` of finite type over `ℂ`,
with `X(ℂ)` semilocally simply connected, and `x ∈ X(ℂ)`, the homomorphism
`π̂₁(X(ℂ), x) → π₁(X, x)` induced by `Ψ` is surjective (V.6.9 with XII.2.4). (`X(ℂ)` is locally
path-connected by the instance `Points.locallyPathConnectedSpace`.) Stated for `A : Type`
(universe `0`), where the fibre functors of finite étale `A`-algebras at `ℂ`-points are fibre
functors. -/
theorem surjective_autWhiskerLeft_pointsFunctor
    [SemilocallySimplyConnectedSpace (Points ℂ A)] (x : Points ℂ A) :
    haveI : ConnectedSpace (Points ℂ A) := Points.connectedComparison A ‹_›
    haveI : PathConnectedSpace (Points ℂ A) := .of_locallyPathConnectedSpace
    Function.Surjective (SGA.SGA1.ExposeX.autWhiskerLeft (pointsFunctor ℂ A)
      (pointsFunctorCompFiberIso ℂ A x)) := by
  have : ConnectedSpace (Points ℂ A) := Points.connectedComparison A ‹_›
  have : PathConnectedSpace (Points ℂ A) := .of_locallyPathConnectedSpace
  let := x.toRingHom.toAlgebra
  exact ExposeX.autWhiskerLeft_surjective_of_isConnected _ _ fun S _ ↦
    isConnected_pointsFunctor_obj A S

/-- XII.5.2, surjectivity, affine smooth case: for `A` smooth over `ℂ` with `Spec A` connected
and `x ∈ X(ℂ)`, the homomorphism `π̂₁(X(ℂ), x) → π₁(X, x)` induced by `Ψ` is surjective
(`A : Type`). -/
theorem surjective_autWhiskerLeft_pointsFunctor_of_smooth [Algebra.Smooth ℂ A] (x : Points ℂ A) :
    haveI : ConnectedSpace (Points ℂ A) := Points.connectedComparison A ‹_›
    haveI := Points.stronglyLocallyContractibleSpace_of_smooth (𝕜 := ℂ) (A := A)
    haveI : PathConnectedSpace (Points ℂ A) := .of_locallyPathConnectedSpace
    Function.Surjective (SGA.SGA1.ExposeX.autWhiskerLeft (pointsFunctor ℂ A)
      (pointsFunctorCompFiberIso ℂ A x)) :=
  have := Points.stronglyLocallyContractibleSpace_of_smooth (𝕜 := ℂ) (A := A)
  surjective_autWhiskerLeft_pointsFunctor A x

end Affine

end SGA.SGA1.ExposeXII
