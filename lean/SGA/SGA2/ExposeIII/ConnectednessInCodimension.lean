/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.SchemeConnectedComponents
import SGA.SGA2.ExposeIII.AntifilterConnectedness
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# SGA 2, III.3.7: connectedness in codimension

If depth is at least two whenever the local dimension is at least `d`, then
removing a closed set of codimension at least `d` does not change connected
components. This is Hartshorne's theorem III.3.6 applied along that closed
set, and is the geometric content of III.3.7.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- Local Krull dimension of the structure stalk. -/
def structureStalkDim (X : Scheme.{u}) (x : X) : WithBot ℕ∞ :=
  ringKrullDim (X.presheaf.stalk x)

/-- A closed set has local dimension at least `d` at every point. -/
def HasMinDim (Z : Closeds X) (d : ℕ) : Prop :=
  ∀ x : X, x ∈ Z → (d : WithBot ℕ∞) ≤ structureStalkDim X x

/-- **III.3.7, connectedness of complements:** under the depth/dimension
hypothesis, a closed set of local dimension at least `d` may be removed
without changing connected components. -/
theorem III_3_7_complement [IsLocallyNoetherian X] (Z : Closeds X) (d : ℕ)
    (hdepth : ∀ x : X, (d : WithBot ℕ∞) ≤ structureStalkDim X x →
      (2 : ℕ∞) ≤ structureStalkDepth X x)
    (hZ : ∀ x : X, x ∈ Z → (d : WithBot ℕ∞) ≤ structureStalkDim X x) :
    Function.Bijective (schemeConnectedComponentsMap (Scheme.Opens.ι Z.compl)) :=
  schemeConnectedComponents_bijective_of_stalkDepth Z fun x hx =>
    hdepth x (hZ x hx)

/-- The same statement for a closed set of local dimension at least `d`. -/
theorem III_3_7_of_minDim [IsLocallyNoetherian X] (Z : Closeds X) (d : ℕ)
    (hdepth : ∀ x : X, (d : WithBot ℕ∞) ≤ structureStalkDim X x →
      (2 : ℕ∞) ≤ structureStalkDepth X x)
    (hZ : HasMinDim (X := X) Z d) :
    Function.Bijective (schemeConnectedComponentsMap (Scheme.Opens.ι Z.compl)) :=
  III_3_7_complement Z d hdepth hZ

/-- **III.3.10 argument:** if removing a closed set does not induce a
bijection on connected components, then some point of the closed set has
depth `< 2`. -/
theorem III_3_10_depth_lt_two [IsLocallyNoetherian X] (Z : Closeds X)
    (hdisc : ¬ Function.Bijective
      (schemeConnectedComponentsMap (Scheme.Opens.ι Z.compl))) :
    ¬ ∀ x : X, x ∈ Z → (2 : ℕ∞) ≤ structureStalkDepth X x :=
  fun h => hdisc (schemeConnectedComponents_bijective_of_stalkDepth Z h)

end SGA.SGA2.ExposeIII
