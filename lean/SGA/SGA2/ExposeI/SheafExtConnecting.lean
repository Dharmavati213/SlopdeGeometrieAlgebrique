/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.SheafExtLocalComparison
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Connecting maps of local Ext

A short exact sequence of coefficient sheaves induces connecting maps on
Ext of ordinary restrictions to every open. Transporting those maps along
the evaluation equivalences gives the connecting maps of the local Ext
presheaf. This is the remaining connecting-map compatibility of I.1.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

instance (U : Opens X) : PreservesFiniteLimits (iShriek_open U) := by
  have := (openExtensionByZeroAdjunction U).isRightAdjoint
  infer_instance

instance (U : Opens X) : PreservesFiniteColimits (iShriek_open U) := by
  have : (iShriek_open U).PreservesHomology := inferInstance
  infer_instance

/-- Restriction to an open is exact, so it carries short exact sequences of
abelian sheaves to short exact sequences on the open. -/
theorem restrictToOpen_map_shortExact (U : Opens X)
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact) :
    (S.map (iShriek_open U)).ShortExact :=
  hS.map_of_exact (iShriek_open U)

/-- The covariant Ext connecting map on an open, for a short exact sequence
of ambient coefficient sheaves. -/
def localExtδ (F : Sheaf AddCommGrpCat.{u} X)
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
    (U : Opens X) (n : ℕ) :
    Ext (restrictToOpen F U) (restrictToOpen S.X₃ U) n →+
      Ext (restrictToOpen F U) (restrictToOpen S.X₁ U) (n + 1) :=
  (restrictToOpen_map_shortExact U hS).extClass.postcomp
    (restrictToOpen F U) (show n + 1 = n + 1 from rfl)



end SGA.SGA2.ExposeI
