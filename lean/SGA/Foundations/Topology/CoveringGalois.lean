/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.FiniteCovering
import SGA.Foundations.Topology.GaloisCategoryEquivalence
import SGA.Foundations.Topology.ProfiniteCompletionGalois

/-!
# Finite coverings form a Galois category

Let `X` be a path-connected, locally path-connected, semilocally simply connected space. By the
classification of coverings (`TopCat.FiniteCovering.equivalenceAction`), finite coverings of `X`
are equivalent to finite `π₁(X, x)`-sets, compatibly with the fibre functor at `x`. Hence:

* `TopCat.FiniteCovering X` is a Galois category and the fibre functor at any point is a fibre
  functor;
* the fundamental group of this Galois category at `x`, i.e. the automorphism group of the fibre
  functor at `x`, is the profinite completion of `π₁(X, x)`
  (`TopCat.FiniteCovering.autFiberEquiv`).

## References

* [SGA 1, Exposé V and Exposé XII, §5][sga1]
* [A. Hatcher, *Algebraic Topology*, §1.3][hatcher02]
-/

noncomputable section

open CategoryTheory PreGaloisCategory

universe u

namespace TopCat.FiniteCovering

variable {X : TopCat.{u}} [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- The finite coverings of a path-connected, locally path-connected, semilocally simply connected
space form a pre-Galois category. -/
instance : PreGaloisCategory (FiniteCovering X) :=
  .of_equivalence (equivalenceAction (Classical.arbitrary X))

/-- The fibre functor at any point is a fibre functor. -/
instance (x : X) : FiberFunctor (fiber x) :=
  have := FiberFunctor.comp_isEquivalence (monodromyAction x)
    (Action.forget FintypeCat.{u} (FundamentalGroup X x))
  .of_iso (monodromyActionCompForgetIso x)

/-- The finite coverings of a path-connected, locally path-connected, semilocally simply connected
space form a Galois category. -/
instance : GaloisCategory (FiniteCovering X) where
  hasFiberFunctor := ⟨fiber (Classical.arbitrary X), inferInstance⟩

variable (x : X)

/-- The fundamental group of the Galois category of finite coverings at `x` (the automorphism
group of the fibre functor at `x`) is the profinite completion of the fundamental group
`π₁(X, x)`, as a topological group. -/
def autFiberEquiv :
    Aut (fiber x) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (FundamentalGroup X x)) :=
  (autContinuousMulEquivOfIsEquivalence (monodromyAction x)
    (monodromyActionCompForgetIso x)).symm.trans
    (ProfiniteGrp.ProfiniteCompletion.autForgetEquiv _)

/-- The element of `Aut (fiber x)` given by an element `σ` of the profinite completion of
`π₁(X, x)` acts on the fibre of a finite covering through a finite quotient of `π₁(X, x)`,
i.e. by monodromy along any loop with the same image as `σ` in that quotient. -/
lemma autFiberEquiv_symm_apply_hom_app
    (σ : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X x)))
    (E : FiniteCovering X) (e : (fiber x).obj E) :
    ((autFiberEquiv x).symm σ).hom.app E e = σ • (show ((monodromyAction x).obj E).V from e) :=
  rfl

instance (E : FiniteCovering X) :
    MulAction (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X x)))
      ((fiber x).obj E) :=
  ProfiniteGrp.ProfiniteCompletion.mulActionAction ((monodromyAction x).obj E)

/-- The profinite completion of `π₁(X, x)`, acting on the fibres at `x` through the monodromy
action, is a fundamental group of the fibre functor at `x`; `toAutMulEquiv` then gives the
canonical isomorphism with `Aut (fiber x)`. -/
instance isFundamentalGroup :
    IsFundamentalGroup (fiber x)
      (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup X x))) where
  naturality σ _ _ f e :=
    IsNaturalSMul.naturality (F := Action.forget FintypeCat.{u} (FundamentalGroup X x)) σ
      ((monodromyAction x).map f) e
  transitive_of_isGalois E _ := by
    refine ⟨fun a b ↦ ?_⟩
    obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (Aut (fiber x)) a b
    exact ⟨autFiberEquiv x τ, by
      rw [← hτ]
      change ((autFiberEquiv x).symm (autFiberEquiv x τ)).hom.app E a = _
      rw [ContinuousMulEquiv.symm_apply_apply]
      rfl⟩
  continuous_smul E := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    exact ProfiniteGrp.ProfiniteCompletion.isOpen_stabilizer ((monodromyAction x).obj E)
  non_trivial' σ h := by
    have : (autFiberEquiv x).symm σ = 1 := by
      ext E e
      exact h E e
    simpa using congrArg (autFiberEquiv x) this

end TopCat.FiniteCovering

namespace TopCat.FiniteCovering

variable (X : TopCat.{u}) [ConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- For `X` connected, locally path-connected and semilocally simply connected, the automorphism
group of the fibre functor of finite coverings at `x` is isomorphic, as a topological group, to
the profinite completion of `π₁(X, x)`. -/
theorem nonempty_autFiber_continuousMulEquiv (x : X) :
    Nonempty (Aut (fiber x) ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (FundamentalGroup X x))) :=
  have : PathConnectedSpace X := .of_locallyPathConnectedSpace
  ⟨autFiberEquiv x⟩

end TopCat.FiniteCovering
