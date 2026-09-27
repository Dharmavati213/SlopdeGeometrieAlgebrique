/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeV.GaloisCategories
import SGA.SGA1.ExposeV.FundamentalGroupField

/-!
# SGA 1, Exposé V, §7: change of geometric point

V.7: over a connected scheme `S`, the fiber functors `F_a`, `F_{a'}` at two geometric points (with
values in separably closed fields, possibly of different characteristics) are isomorphic (V.5.7).
The isomorphisms `F_a ≅ F_{a'}` form the set `π₁(S; a, a')` of classes of paths from `a` to `a'`
(`etalePaths`), and each of them induces an isomorphism of topological groups
`π₁(S, a) ≃ₜ* π₁(S, a')` (`etaleFundamentalGroup.continuousMulEquivOfPath`). The groupoid
structure is the one of V.5.7 (`SGA.SGA1.ExposeV.GaloisCategories`).

For a field `k`, combined with V.8.1 this identifies the automorphism group of any fiber functor
of the étale coverings of `Spec k` with the absolute Galois group of `k`
(`nonempty_aut_continuousMulEquiv_absoluteGaloisGroup`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeV

variable {S : Scheme.{u}} (Ω Ω' : Type u) [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']

/-- V.7: the set `π₁(S; a, a')` of classes of paths from the geometric point `a` to the geometric
point `a'`: the isomorphisms of fiber functors `F_a ≅ F_{a'}`. -/
abbrev etalePaths (s : Spec (CommRingCat.of Ω) ⟶ S) (s' : Spec (CommRingCat.of Ω') ⟶ S) :
    Type (u + 1) :=
  FEt.fiber Ω s ≅ FEt.fiber Ω' s'

/-- V.7: over a connected base, there is a path between any two geometric points. -/
theorem etalePaths.nonempty [ConnectedSpace S]
    (s : Spec (CommRingCat.of Ω) ⟶ S) (s' : Spec (CommRingCat.of Ω') ⟶ S) :
    Nonempty (etalePaths Ω Ω' s s') :=
  nonempty_iso_of_fiberFunctor _ _

/-- V.7: a path `γ` from `a` to `a'` induces an isomorphism of topological groups
`π₁(S, a) ≃ₜ* π₁(S, a')`, `σ ↦ γ σ γ⁻¹`. -/
noncomputable def etaleFundamentalGroup.continuousMulEquivOfPath
    {s : Spec (CommRingCat.of Ω) ⟶ S} {s' : Spec (CommRingCat.of Ω') ⟶ S}
    (γ : etalePaths Ω Ω' s s') : etaleFundamentalGroup Ω s ≃ₜ* etaleFundamentalGroup Ω' s' :=
  conjAutContinuousMulEquiv γ

/-- V.7: over a connected base, the fundamental groups at any two geometric points are
isomorphic as topological groups. -/
theorem etaleFundamentalGroup.nonempty_continuousMulEquiv [ConnectedSpace S]
    (s : Spec (CommRingCat.of Ω) ⟶ S) (s' : Spec (CommRingCat.of Ω') ⟶ S) :
    Nonempty (etaleFundamentalGroup Ω s ≃ₜ* etaleFundamentalGroup Ω' s') :=
  (etalePaths.nonempty Ω Ω' s s').map (etaleFundamentalGroup.continuousMulEquivOfPath Ω Ω')

/-- V.7, V.8.1: for a field `k`, the automorphism group of any fiber functor of the étale
coverings of `Spec k` is isomorphic, as a topological group, to the absolute Galois group of
`k`. -/
theorem nonempty_aut_continuousMulEquiv_absoluteGaloisGroup (k : Type u) [Field k]
    (F : FEt (Spec (CommRingCat.of k)) ⥤ FintypeCat.{u}) [FiberFunctor F] :
    Nonempty (Aut F ≃ₜ* Field.absoluteGaloisGroup k) :=
  (nonempty_iso_of_fiberFunctor F (FEt.fiber (AlgebraicClosure k)
    (specPoint (CommRingCat.of k) (AlgebraicClosure k)))).map fun φ ↦
      (conjAutContinuousMulEquiv φ).trans (etaleFundamentalGroupEquivAbsoluteGaloisGroup k)

/-- V.8.1: for a field `k` and any geometric point `a : Spec Ω → Spec k`, `π₁(Spec k, a)` is
isomorphic to the absolute Galois group of `k`. -/
theorem etaleFundamentalGroup.nonempty_continuousMulEquiv_absoluteGaloisGroup (k : Type u)
    [Field k] (s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k)) :
    Nonempty (etaleFundamentalGroup Ω s ≃ₜ* Field.absoluteGaloisGroup k) :=
  nonempty_aut_continuousMulEquiv_absoluteGaloisGroup k _

end SGA.SGA1.ExposeV
