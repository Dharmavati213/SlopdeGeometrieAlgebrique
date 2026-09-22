/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.InternalHomBifunctor
import SGA.SGA2.ExposeI.SheafExtRestriction
import SGA.SGA2.ExposeI.OpenInclusionLeray
import SGA.SGA2.ExposeI.ClosedAsLocallyClosed
import SGA.SGA2.ExposeI.RingedSpaceSupportHom

/-!
# Concrete checks for the remaining Exposé I identities

These drive the new first-variable Hom maps, nested-open Ext restriction,
the open-support Leray identification, and the closed-as-locally-closed
specialization, on the empty space and on singleton opens of a point.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

/-- First-variable precomposition of the identity is the identity, on every
abelian sheaf. -/
theorem abelianSheafHomPrecomp_id_top (X : TopCat.{u})
    (F : Sheaf AddCommGrpCat.{u} X) :
    abelianSheafHomPrecomp (Opens.grothendieckTopology X) (𝟙 F) = 𝟙 _ :=
  abelianSheafHomPrecomp_id (J := Opens.grothendieckTopology X) (F := F)

/-- Nested-open restriction along an inclusion of nested opens is functorial. -/
theorem localExtRestriction_comp_top (X : TopCat.{u})
    (F G : Sheaf AddCommGrpCat.{u} X) {U V W : Opens X}
    (hUV : U ≤ V) (hVW : V ≤ W) (n : ℕ)
    (x : Ext.{u} (restrictToOpen F W) (restrictToOpen G W) n) :
    localExtRestriction F G hUV n (localExtRestriction F G hVW n x) =
      localExtRestriction F G (hUV.trans hVW) n x :=
  localExtRestriction_comp F G hUV hVW n x

/-- The canonical closed witness has the original closed set as underlying set. -/
theorem ofClosed_asSet_univ (X : TopCat.{u}) :
    (LocallyClosedIn.ofClosed (⊤ : Closeds X)).asSet = (Set.univ : Set X) := by
  simp

/-- Open-support Grothendieck/Leray sequence is the locally closed sequence
of the open witness. -/
theorem grothendieckSpectralSequenceOfOpenSupport_eq_locallyClosed
    {X : TopCat.{u}} (U : Opens X) {F : Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) :
    grothendieckSpectralSequenceOfOpenSupport U I =
      locallyClosedTruncationSpectralSequence (LocallyClosedIn.ofOpen U) I :=
  rfl

end SGA.SGA2.ExposeI
