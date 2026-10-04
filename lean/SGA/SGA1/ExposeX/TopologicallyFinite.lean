/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Pro.TopologicallyFG
import SGA.SGA1.ExposeX.Semicontinuity
import SGA.SGA1.ExposeXIII.AffineLineFundamentalGroup
import SGA.SGA1.ExposeV.FundamentalGroupBasePoint
import SGA.SGA1.ExposeXI.FundamentalGroupCohomology
import SGA.SGA1.ExposeX.BaseChangeAlgClosed

/-!
# SGA 1, Exposé X, 2.9 and 2.12: topological finite generation of `π₁`

X.2.9 says that the fundamental group of a proper connected scheme over an algebraically closed
field is topologically finitely generated (`TopologicallyFiniteStatement`, in
`SGA.SGA1.ExposeX.Semicontinuity`), and X.2.12 (Lang–Serre) deduces that such a scheme has only
finitely many principal coverings with a given finite group.

This file connects the two formulations of "topologically finitely generated" used in the
project, `∃ S, S.Finite ∧ (Subgroup.closure S).topologicalClosure = ⊤` (the form of
`TopologicallyFiniteStatement`) and `ExposeXIII.IsTopologicallyFG` (a `Finset` generating a dense
subgroup), and records the formal facts used to prove X.2.9 in special cases:

* `isTopologicallyFG_iff`: the two formulations agree;
* `isTopologicallyFG_etaleFundamentalGroup_iff`: over a connected scheme, being topologically
  finitely generated does not depend on the geometric point (change of base point,
  `ExposeV.etaleFundamentalGroup.nonempty_continuousMulEquiv`);
* `topologicallyFiniteStatement_iff`: `TopologicallyFiniteStatement` in terms of
  `IsTopologicallyFG`;
* `isTopologicallyFG_etaleFundamentalGroup_of_pullback`: topological finite generation goes down
  from `X_K` to `X` for an extension `K/k` of algebraically closed fields (from X.1.8,
  `bijective_map_pullback_fst`);
* `finite_principalH1_of_isTopologicallyFG`: X.2.12 for a single connected scheme whose `π₁` is
  topologically finitely generated: finitely many principal coverings with a given finite group,
  up to isomorphism (through XI.5 `(*)`, `ExposeXI.principalCoveringH1Equiv`);
  `finite_principalH1_of_topologicallyFiniteStatement` is X.2.12 from X.2.9. The homomorphism
  form is `ExposeXIII.finite_continuousMonoidHom_of_isTopologicallyFG` (and
  `finite_setOf_continuous_monoidHom_of_statement`).

X.2.9 is proved in characteristic `0` for `#k ≤ 𝔠`, in universe `0`, in
`SGA.SGA1.ExposeX.TopologicallyFiniteCharZero` (special cases with a more direct proof are in
`SGA.SGA1.ExposeX.TopologicallyFiniteComplex`); SGA's reduction to curves is in
`SGA.SGA1.ExposeX.TopologicallyFiniteReduction`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeX

/-- The two formulations of topological finite generation agree. -/
theorem isTopologicallyFG_iff {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ExposeXIII.IsTopologicallyFG G ↔
      ∃ S : Set G, S.Finite ∧ (Subgroup.closure S).topologicalClosure = ⊤ :=
  Subgroup.exists_finset_dense_closure_iff

/-- An isomorphism of topological groups preserves topological finite generation. -/
theorem isTopologicallyFG_congr {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] (e : G ≃ₜ* H) :
    ExposeXIII.IsTopologicallyFG G ↔ ExposeXIII.IsTopologicallyFG H :=
  ⟨fun h ↦ h.of_surjective e.toMulEquiv.toMonoidHom e.continuous e.surjective,
    fun h ↦ h.of_surjective e.symm.toMulEquiv.toMonoidHom e.symm.continuous e.symm.surjective⟩

/-- Over a connected scheme, the fundamental group at one geometric point is topologically
finitely generated if and only if it is at any other (by the change of base point,
`ExposeV.etaleFundamentalGroup.nonempty_continuousMulEquiv`). -/
theorem isTopologicallyFG_etaleFundamentalGroup_iff {S : Scheme.{u}} [ConnectedSpace S]
    (Ω Ω' : Type u) [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    (s : Spec (.of Ω) ⟶ S) (s' : Spec (.of Ω') ⟶ S) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω s) ↔
      ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω' s') :=
  have ⟨e⟩ := ExposeV.etaleFundamentalGroup.nonempty_continuousMulEquiv Ω Ω' s s'
  isTopologicallyFG_congr e

/-- X.2.9 (`TopologicallyFiniteStatement`), stated with `ExposeXIII.IsTopologicallyFG`. -/
theorem topologicallyFiniteStatement_iff :
    TopologicallyFiniteStatement.{u} ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] ⦃X : Scheme.{u}⦄ (s : X ⟶ Spec (.of k))
        [IsProper s] [ConnectedSpace X] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (x : Spec (.of Ω) ⟶ X), ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) :=
  forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
      forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
        isTopologicallyFG_iff.symm

/-- Topological finite generation of `π₁` goes down along an extension of algebraically closed
fields: if `X` is proper and connected over `k = k̄` and `K ⊇ k` is algebraically closed, and
`π₁(X_K)` is topologically finitely generated at one geometric point, then `π₁(X)` is, at every
geometric point. (`X_K` is connected, `geometricallyConnected_of_isAlgClosed`, and
`π₁(X_K) ≅ π₁(X)` by X.1.8, `bijective_map_pullback_fst`.) -/
theorem isTopologicallyFG_etaleFundamentalGroup_of_pullback (k K : Type u) [Field k]
    [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsProper s] [ConnectedSpace X] {Ω' : Type u} [Field Ω']
    [IsSepClosed Ω']
    (y : Spec (.of Ω') ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (h : ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω' y))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω x) := by
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hX := h.of_surjective _
    (ExposeV.etaleFundamentalGroup.continuous_map Ω' (pullback.fst s ρ) y)
    (bijective_map_pullback_fst k K s Ω' y).2
  exact (isTopologicallyFG_etaleFundamentalGroup_iff _ Ω _ x).mp hX

/-- **X.2.12** (Lang–Serre) for one scheme: if `S` is connected and `π₁(S, s)` is topologically
finitely generated, then for every finite group `G` there are only finitely many principal
coverings of `S` with group `G` up to isomorphism (`ExposeXI.PrincipalH1`; through XI.5 `(*)`,
`ExposeXI.principalCoveringH1Equiv`, they correspond to continuous homomorphisms `π₁ → G` up to
conjugation, of which there are finitely many). -/
theorem finite_principalH1_of_isTopologicallyFG {S : Scheme.{u}} [ConnectedSpace S] (Ω : Type u)
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (h : ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω s))
    (G : Type u) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] :
    Finite (ExposeXI.PrincipalH1 (ExposeV.FEt.fiber Ω s) G) := by
  have := ExposeXIII.finite_continuousMonoidHom_of_isTopologicallyFG h G
  have : Finite {ρ : ExposeV.etaleFundamentalGroup Ω s →* G // Continuous ρ} :=
    Finite.of_injective (fun ρ ↦ (⟨ρ.1, ρ.2⟩ : ContinuousMonoidHom _ G)) fun ρ ρ' h ↦
      Subtype.ext (congrArg ContinuousMonoidHom.toMonoidHom h)
  have : Finite (ExposeXI.ContHomConj G (ExposeV.etaleFundamentalGroup Ω s)) := Quotient.finite _
  exact Finite.of_equiv _ (ExposeXI.principalCoveringH1Equiv S Ω s G).symm

/-- **X.2.12** (Lang–Serre) from X.2.9: if `TopologicallyFiniteStatement` holds, a proper
connected scheme over an algebraically closed field has, for every finite group `G`, only
finitely many principal coverings with group `G` up to isomorphism. -/
theorem finite_principalH1_of_topologicallyFiniteStatement (h : TopologicallyFiniteStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [IsProper s]
    [ConnectedSpace X] (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (G : Type u) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] :
    Finite (ExposeXI.PrincipalH1 (ExposeV.FEt.fiber Ω x) G) :=
  finite_principalH1_of_isTopologicallyFG Ω x (topologicallyFiniteStatement_iff.mp h k s Ω x) G

end SGA.SGA1.ExposeX
