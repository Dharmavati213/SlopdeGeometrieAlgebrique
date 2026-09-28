/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.LocalDualityFiniteFree
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Right exactness of the top-degree local-duality target

The original target is naturally Hom of the original module-valued Ext.
In degree zero, the canonical Ext--Hom comparison makes the first functor
left exact; Hom into the injective coefficient makes the composite right
exact. These are actual functors, not replacement objectwise values.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The linear-map-valued target agrees naturally with categorical Hom
of the unchanged original Ext functor. -/
def localDualityTargetIsoHom (J : Ideal R) (P : ModuleCat.{u} R) (j n : ℕ) :
    localDualityTargetFunctor J P j n ≅
      ((_root_.Ext R (ModuleCat.{u} R) j).flip.obj P).rightOp ⋙
        (linearYoneda R (ModuleCat.{u} R)).obj ((_root_.localCohomology J n).obj P) :=
  NatIso.ofComponents (fun M =>
    (ModuleCat.homLinearEquiv (R := R) (S := R)
      (M := moduleExtValue M P j) (N := (_root_.localCohomology J n).obj P)).symm.toModuleIso)
    (by intro M N f; rfl)

/-- Injectivity of the actual coefficient makes the actual top-degree
target right exact, using the canonical degree-zero Ext comparison. -/
theorem localDualityTarget_preservesFiniteColimits (J : Ideal R) (P : ModuleCat.{u} R)
    (n : ℕ) [Injective ((_root_.localCohomology J n).obj P)] :
    PreservesFiniteColimits (localDualityTargetFunctor J P 0 n) := by
  let H := (_root_.Ext R (ModuleCat.{u} R) 0).flip.obj P
  let D := (linearYoneda R (ModuleCat.{u} R)).obj ((_root_.localCohomology J n).obj P)
  have : PreservesFiniteLimits H := preservesFiniteLimits_of_natIso (extZeroIsoHom P).symm
  have : PreservesFiniteColimits H.rightOp := preservesFiniteColimits_rightOp H
  have : PreservesFiniteColimits D := Functor.preservesFiniteColimits_of_preservesHomology D
  have : PreservesFiniteColimits (H.rightOp ⋙ D) := inferInstance
  exact preservesFiniteColimits_of_natIso (localDualityTargetIsoHom J P 0 n).symm

end SGA.SGA2.ExposeV
