/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.FundamentalGroupQuotient
import SGA.SGA1.ExposeXII.LocalTopologySLSC
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupInertia

/-!
# XII.5.2 as a homomorphism `π₁(X(ℂ), x) → π₁(X, x)`

For `X` locally of finite type over `ℂ` and `x ∈ X(ℂ)`, a loop `γ` at `x` in `X(ℂ)` acts on the
fibre at `x` of every étale covering `Y → X` (the points of `Y(ℂ)` over `x`) by the monodromy of
the covering `Y(ℂ) → X(ℂ)` along `γ`, naturally in `Y`. This is an element of the étale
fundamental group `π₁(X, x)` (V.7), and XII.5.2 says that the resulting homomorphism
`π₁(X(ℂ), x) → π₁(X, x)` identifies `π₁(X, x)` with the profinite completion of `π₁(X(ℂ), x)`.
The repository proves that identification as an abstract isomorphism
(`ExposeXII.nonempty_etaleFundamentalGroup_continuousMulEquiv`); XIII.2.12 needs to know where
given loops go, so this file defines the homomorphism itself.

* `monodromyAut x : π₁(T, x) →* Aut (fiber x)`: monodromy, as automorphisms of the fibre functor
  of finite coverings of a space `T` (mathlib's `PreGaloisCategory.toAut`);
* `comparisonHom X x : π₁(X(ℂ), x) →* π₁(X, x)`, the composite with the homomorphism
  `Aut (fiber x) → π₁(X, x)` induced by `Ψ : Y ↦ Y(ℂ)` (`ExposeX.autWhiskerLeft`); it is defined
  without the Riemann existence theorem, and `comparisonHom_smul` describes its action on fibres;
* if `Ψ` is an equivalence (XII.5.1) and `X(ℂ)` is path-connected, `comparisonHom X x` is the
  profinite completion map up to an isomorphism of topological groups
  (`comparisonHom_eq_comp_etaHom`); hence `isProLSurfaceGroup_comparisonHom`: elements of
  `π₁(X(ℂ), x)` presenting it by generators and one relation (*) have images presenting the
  maximal pro-`L` quotient of `π₁(X, x)`.
-/

universe u

noncomputable section

open CategoryTheory AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeXIII

section Monodromy

open TopCat TopCat.FiniteCovering

variable {T : TopCat.{u}} (x : T)

/-- The monodromy action of `π₁(T, x)` on the fibres at `x` of finite coverings of `T`. -/
instance fiberMulAction (E : FiniteCovering T) :
    MulAction (_root_.FundamentalGroup T x) ((fiber x).obj E) :=
  inferInstanceAs (MulAction (_root_.FundamentalGroup T x) ((monodromyAction x).obj E).V)

/-- The monodromy action, for the space `TopCat.of A` (found by instance search for points of
`A` itself). -/
instance fiberMulAction' (A : Type u) [TopologicalSpace A] (a : A)
    (E : FiniteCovering (TopCat.of A)) :
    MulAction (_root_.FundamentalGroup A a) ((fiber (X := TopCat.of A) a).obj E) :=
  fiberMulAction (T := TopCat.of A) a E

lemma fiber_smul_eq_monodromy (E : FiniteCovering T) (γ : _root_.FundamentalGroup T x)
    (e : (fiber x).obj E) : γ • e = E.isCoveringMap.monodromy γ e :=
  rfl

instance : IsNaturalSMul (fiber x) (_root_.FundamentalGroup T x) where
  naturality γ E F f e :=
    Subtype.ext (E.isCoveringMap.apply_monodromy F.isCoveringMap f.hom.left.hom
      (hom_left_apply f) γ e)

/-- The monodromy, as a homomorphism from `π₁(T, x)` to the automorphisms of the fibre functor
at `x` of finite coverings of `T`. -/
def monodromyAut : _root_.FundamentalGroup T x →* Aut (fiber x) :=
  toAut (fiber x) (_root_.FundamentalGroup T x)

lemma monodromyAut_hom_app (γ : _root_.FundamentalGroup T x) (E : FiniteCovering T)
    (e : (fiber x).obj E) : (monodromyAut x γ).hom.app E e = γ • e :=
  rfl

/-- On a path-connected, locally path-connected, semilocally simply connected space, the
monodromy is the completion map followed by `TopCat.FiniteCovering.autFiberEquiv`. -/
lemma monodromyAut_eq [PathConnectedSpace T] [LocallyPathConnectedSpace T]
    [SemilocallySimplyConnectedSpace T] (γ : _root_.FundamentalGroup T x) :
    monodromyAut x γ = (autFiberEquiv x).symm
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (_root_.FundamentalGroup T x)) γ) := by
  ext E e
  rw [monodromyAut_hom_app, autFiberEquiv_symm_apply_hom_app]
  exact (ProfiniteGrp.ProfiniteCompletion.etaFn_smul ((monodromyAction x).obj E) γ e).symm

end Monodromy

section Comparison

open ExposeXII

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  (x : SchemePoints ℂ X)

/-- XII.5.2: the comparison homomorphism `π₁(X(ℂ), x) → π₁(X, x)`. A loop `γ` acts on the fibre
at `x` of an étale covering `Y` of `X` (the geometric points of `Y` over `x`, i.e. the points of
`Y(ℂ)` over `x`, `schemePointsFunctorCompFiberIso`) by the monodromy of the covering
`Y(ℂ) → X(ℂ)` along `γ` (`comparisonHom_smul`). Defined without the Riemann existence theorem. -/
def comparisonHom :
    _root_.FundamentalGroup (SchemePoints ℂ X) x →* ExposeV.etaleFundamentalGroup ℂ x.1 :=
  (ExposeX.autWhiskerLeft (schemePointsFunctor ℂ X) (schemePointsFunctorCompFiberIso ℂ x)).comp
    (monodromyAut (T := TopCat.of (SchemePoints ℂ X)) x)

omit [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] in
/-- The action of `comparisonHom X x γ` on the fibre at `x` of an étale covering `Y`: transported
to the points of `Y(ℂ)` over `x`, it is the monodromy along `γ`. -/
lemma comparisonHom_smul (γ : _root_.FundamentalGroup (SchemePoints ℂ X) x)
    (Y : ExposeV.FEt X) (y : (ExposeV.FEt.fiber ℂ x.1).obj Y) :
    comparisonHom X x γ • y = (schemePointsFunctorCompFiberIso ℂ x).hom.app Y
      (γ • show (TopCat.FiniteCovering.fiber (X := TopCat.of (SchemePoints ℂ X)) x).obj
          ((schemePointsFunctor ℂ X).obj Y) from
        (schemePointsFunctorCompFiberIso ℂ x).inv.app Y y) :=
  rfl

variable [(schemePointsFunctor ℂ X).IsEquivalence] [PathConnectedSpace (SchemePoints ℂ X)]

omit [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [PathConnectedSpace (SchemePoints ℂ X)] in
/-- Under XII.5.1, the homomorphism `Aut (fiber x) → π₁(X, x)` induced by `Ψ` is an isomorphism
of topological groups (`ExposeXII.etaleFundamentalGroupEquivAutFiber`). -/
lemma autWhiskerLeft_eq_etaleFundamentalGroupEquivAutFiber_symm
    (σ : Aut (TopCat.FiniteCovering.fiber (X := TopCat.of (SchemePoints ℂ X)) x)) :
    ExposeX.autWhiskerLeft (schemePointsFunctor ℂ X) (schemePointsFunctorCompFiberIso ℂ x) σ =
      (etaleFundamentalGroupEquivAutFiber ℂ x).symm σ :=
  rfl

/-- Under XII.5.1 (`Ψ` an equivalence) and for `X(ℂ)` path-connected, the comparison homomorphism
is the completion map `π₁(X(ℂ), x) → π̂₁(X(ℂ), x)` followed by an isomorphism of topological
groups `π̂₁(X(ℂ), x) ≃ₜ* π₁(X, x)`. -/
theorem comparisonHom_eq_comp_etaHom :
    ∃ ψ : ProfiniteGrp.ProfiniteCompletion.completion
        (GrpCat.of (_root_.FundamentalGroup (SchemePoints ℂ X) x)) ≃ₜ*
        ExposeV.etaleFundamentalGroup ℂ x.1,
      ∀ γ, comparisonHom X x γ =
        ψ (ProfiniteGrp.ProfiniteCompletion.etaFn
          (GrpCat.of (_root_.FundamentalGroup (SchemePoints ℂ X) x)) γ) := by
  refine ⟨(TopCat.FiniteCovering.autFiberEquiv (X := TopCat.of (SchemePoints ℂ X)) x).symm.trans
    (etaleFundamentalGroupEquivAutFiber ℂ x).symm, fun γ ↦ ?_⟩
  change ExposeX.autWhiskerLeft _ _ (monodromyAut (T := TopCat.of (SchemePoints ℂ X)) x γ) = _
  rw [monodromyAut_eq (T := TopCat.of (SchemePoints ℂ X))]
  rfl

/-- **XIII.2.12 over `ℂ`, group structure, from the topology.** Under XII.5.1 (`Ψ` an
equivalence) and for `X(ℂ)` path-connected: if `xᵢ, yᵢ, σⱼ ∈ π₁(X(ℂ), x)` generate it, satisfy
the relation (*) and can be sent to any family of a finite group satisfying (*) (a presentation of
`π₁(X(ℂ), x)` by these generators and the one relation (*), at least towards finite groups),
then their images under `comparisonHom` present the maximal pro-`L` quotient of `π₁(X, x)`
(`IsProLSurfaceGroup L`), for every set of primes `L`. -/
theorem isProLSurfaceGroup_comparisonHom (L : Set ℕ) {g n : ℕ}
    (a b : Fin g → _root_.FundamentalGroup (SchemePoints ℂ X) x)
    (c : Fin n → _root_.FundamentalGroup (SchemePoints ℂ X) x) (hrel : surfaceWord a b c = 1)
    (hgen : Subgroup.closure (Set.range a ∪ Set.range b ∪ Set.range c) = ⊤)
    (hpres : ∀ (G : Type) [Group G], IsLGroup L G →
      ∀ (a' b' : Fin g → G) (c' : Fin n → G), surfaceWord a' b' c' = 1 →
        ∃ f : _root_.FundamentalGroup (SchemePoints ℂ X) x →* G, ⇑f ∘ a = a' ∧ ⇑f ∘ b = b' ∧
          ⇑f ∘ c = c') :
    IsProLSurfaceGroup.{0} L (comparisonHom X x ∘ a) (comparisonHom X x ∘ b)
      (comparisonHom X x ∘ c) := by
  obtain ⟨ψ, hψ⟩ := comparisonHom_eq_comp_etaHom X x
  have h := (isProLSurfaceGroup_etaFn L a b c hrel hgen hpres).map ψ
  have e : ⇑(comparisonHom X x) = ψ ∘ ProfiniteGrp.ProfiniteCompletion.etaFn
      (GrpCat.of (_root_.FundamentalGroup (SchemePoints ℂ X) x)) := funext hψ
  rw [e]
  exact h

end Comparison

end SGA.SGA1.ExposeXIII
