/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedIndependence
import SGA.SGA2.ExposeI.LocallyClosedSupportedSheaves

/-!
# Closed supports as locally closed witnesses

A closed subset is the locally closed witness with ambient open `⊤`. The
original closed support functor, its derived sheaves, and Ext cohomology
are the corresponding locally closed constructions for this witness, so
closed-only comparisons are specializations of the general locally closed
theorems rather than a second argument.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology Set

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- **I.1:** a closed subset as a locally closed witness, with ambient open `⊤`. -/
noncomputable def LocallyClosedIn.ofClosed (Z : Closeds X) : LocallyClosedIn X :=
  LocallyClosedIn.ofOpenClosed ⊤ Z

@[simp]
theorem LocallyClosedIn.ofClosed_asSet (Z : Closeds X) :
    (LocallyClosedIn.ofClosed Z).asSet = (Z : Set X) := by
  rw [LocallyClosedIn.ofClosed, LocallyClosedIn.ofOpenClosed_asSet, Opens.coe_top]
  exact univ_inter _

@[simp]
theorem LocallyClosedIn.ofClosed_V (Z : Closeds X) :
    (LocallyClosedIn.ofClosed Z).V = ⊤ :=
  rfl

/-- Two closed subsets with the same underlying set give the same locally
closed witness after `ofClosed`. -/
theorem LocallyClosedIn.ofClosed_asSet_injective {Z Z' : Closeds X}
    (h : (Z : Set X) = (Z' : Set X)) :
    LocallyClosedIn.ofClosed Z = LocallyClosedIn.ofClosed Z' := by
  simp [LocallyClosedIn.ofClosed, LocallyClosedIn.ofOpenClosed, h]

/-- The original closed integer support sheaf is the locally closed support
sheaf of the canonical closed witness, up to the already proved same-set
independence. -/
noncomputable def zZX_closed_iso_locallyClosed (Z : Closeds X) :
    zZX_locallyClosed (LocallyClosedIn.ofClosed Z) ≅
      zZX_locallyClosed (LocallyClosedIn.ofOpenClosed ⊤ Z) :=
  Iso.refl _

/-- Closed-support Ext is locally closed Ext for the canonical witness. -/
noncomputable def H_Z_iso_H_locallyClosed_ofClosed (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H_locallyClosed (LocallyClosedIn.ofClosed Z) F n ≃+
      H_locallyClosed (LocallyClosedIn.ofOpenClosed ⊤ Z) F n :=
  AddEquiv.refl _

end SGA.SGA2.ExposeI
