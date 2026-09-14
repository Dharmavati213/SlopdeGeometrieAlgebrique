/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Topology.Connected.Basic

/-!
# SGA 2, X: connectedness inputs for the fundamental group

Exposé X applies Lefschetz-type theorems to the fundamental group. We record
basic connectedness facts used when comparing π₀ of a space and of an open.
-/

namespace SGA.SGA2.ExposeX

variable {X : Type*} [TopologicalSpace X]

/-- The empty set is not connected. -/
theorem not_isConnected_empty : ¬ IsConnected (∅ : Set X) :=
  fun h ↦ Set.not_nonempty_empty h.1

/-- Connected sets are nonempty. -/
theorem nonempty_of_isConnected {s : Set X} (hs : IsConnected s) : s.Nonempty :=
  hs.1

/-- On a connected space, the universe is connected. -/
theorem univ_isConnected [ConnectedSpace X] : IsConnected (Set.univ : Set X) :=
  _root_.isConnected_univ

/-- Image of a connected set under a continuous map is connected. -/
theorem isConnected_image {Y : Type*} [TopologicalSpace Y] {s : Set X}
    (hs : IsConnected s) {f : X → Y} (hf : Continuous f) :
    IsConnected (f '' s) :=
  hs.image f hf.continuousOn

end SGA.SGA2.ExposeX
