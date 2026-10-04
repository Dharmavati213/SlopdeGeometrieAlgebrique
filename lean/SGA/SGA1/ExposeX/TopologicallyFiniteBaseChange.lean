/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.TopologicallyFinite

/-!
# SGA 1, Exposé X, 2.9: invariance under extension of the algebraically closed base field

For `X` proper and connected over an algebraically closed field `k` and an algebraically closed
extension `K ⊇ k`, X.1.8 identifies `π₁(X_K)` with `π₁(X)` (`bijective_map_pullback_fst`).
So `π₁(X)` is topologically finitely generated if and only if `π₁(X_K)` is
(`isTopologicallyFG_etaleFundamentalGroup_pullback_iff`). The direction `π₁(X_K) ⇒ π₁(X)` is
`isTopologicallyFG_etaleFundamentalGroup_of_pullback` (`SGA.SGA1.ExposeX.TopologicallyFinite`);
the direction `π₁(X) ⇒ π₁(X_K)` proved here is the one needed to descend X.2.9 for curves to a
countable algebraically closed field of definition.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeX

/-- X.1.8, consequence: topological finite generation of `π₁` goes up along an extension of
algebraically closed fields: if `X` is proper and connected over `k = k̄`, `K ⊇ k` is
algebraically closed and `π₁(X)` is topologically finitely generated (at some geometric point),
then so is `π₁(X_K)`, at every geometric point. The map
`π₁(X_K) → π₁(X)` is a continuous bijective homomorphism of compact Hausdorff groups (X.1.8),
hence a homeomorphism. -/
theorem isTopologicallyFG_etaleFundamentalGroup_pullback_of_isTopologicallyFG (k K : Type u)
    [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsProper s] [ConnectedSpace X] {Ω₀ : Type u} [Field Ω₀]
    [IsSepClosed Ω₀] (x : Spec (.of Ω₀) ⟶ X)
    (h : ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω₀ x))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (y : Spec (.of Ω) ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω y) := by
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hX : ExposeXIII.IsTopologicallyFG
      (ExposeV.etaleFundamentalGroup Ω (y ≫ pullback.fst s ρ)) :=
    (isTopologicallyFG_etaleFundamentalGroup_iff Ω₀ Ω x _).mp h
  let φ := ExposeV.etaleFundamentalGroup.map Ω (pullback.fst s ρ) y
  have hφ : Continuous φ := ExposeV.etaleFundamentalGroup.continuous_map Ω (pullback.fst s ρ) y
  have hb := bijective_map_pullback_fst k K s Ω y
  let e := Equiv.ofBijective φ hb
  let E : ExposeV.etaleFundamentalGroup Ω y ≃ₜ*
      ExposeV.etaleFundamentalGroup Ω (y ≫ pullback.fst s ρ) :=
    { toMulEquiv := MulEquiv.ofBijective φ hb
      continuous_toFun := hφ
      continuous_invFun := (hφ.homeoOfEquivCompactToT2 (f := e)).symm.continuous }
  exact (isTopologicallyFG_congr E).mpr hX

/-- X.1.8, consequence: topological finite generation of `π₁` is invariant under extension of
the algebraically closed base field: for `X` proper and connected over `k = k̄` and `K ⊇ k`
algebraically closed, `π₁(X)` is topologically finitely
generated if and only if `π₁(X_K)` is (at any geometric points). -/
theorem isTopologicallyFG_etaleFundamentalGroup_pullback_iff (k K : Type u)
    [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsProper s] [ConnectedSpace X] {Ω₀ : Type u} [Field Ω₀]
    [IsSepClosed Ω₀] (x : Spec (.of Ω₀) ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (y : Spec (.of Ω) ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω y) ↔
      ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω₀ x) :=
  ⟨fun h ↦ isTopologicallyFG_etaleFundamentalGroup_of_pullback k K s y h Ω₀ x,
    fun h ↦ isTopologicallyFG_etaleFundamentalGroup_pullback_of_isTopologicallyFG k K s x h Ω y⟩

end SGA.SGA1.ExposeX
