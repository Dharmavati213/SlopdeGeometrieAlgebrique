/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulSupportedComparison
import SGA.SGA2.ExposeII.PrincipalCechComparison

/-!
# SGA 2, III.3.12: higher supported vanishing detected on the structure sheaf

If a closed subset of an affine is cut out by `m` equations, supported
cohomology of every associated module sheaf vanishes in degrees `> m`,
because it agrees with stable Koszul cohomology of a length-`m` family.
In particular vanishing for `i > m` on `𝒪` is equivalent to vanishing
on every finite module, once a generating list of that length is chosen.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry Abelian HomologicalComplex

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

/-- Stable Koszul cohomology vanishes strictly above the number of
generators, for an arbitrary coefficient module. -/
theorem stableKoszul_isZero_of_length_lt (fs : List R) (M : ModuleCat.{u} R)
    {i : ℕ} (hi : fs.length < i) :
    IsZero (ExposeII.stableKoszulCohomology fs M i) :=
  ExposeII.stableKoszulCohomology_isZero_above_length fs M i hi

/-- **III.3.12, Koszul form:** if `Y` is cut out by `m` equations on a
noetherian affine, supported cohomology of every associated sheaf vanishes
in degrees `> m`. -/
theorem III_3_12_koszul [IsNoetherianRing R] (fs : List R) (M : ModuleCat.{u} R)
    {i : ℕ} (hi : fs.length < i) :
    Subsingleton (ExposeI.H_Z (ExposeII.affineSupportClosed (ExposeII.koszulIdeal fs))
      (ExposeII.affineTildeAbSheaf M) i) := by
  have h0 : IsZero (ExposeII.stableKoszulCohomology fs M i) :=
    stableKoszul_isZero_of_length_lt fs M hi
  have e := ExposeII.II_5_addEquiv fs M i
  have : Subsingleton
      ((forget₂ (ModuleCat R) AddCommGrpCat).obj (ExposeII.stableKoszulCohomology fs M i)) :=
    ModuleCat.isZero_iff_subsingleton.mp h0
  exact (e.subsingleton_congr).mp this

/-- **III.3.12, structure sheaf detects vanishing above the number of
equations:** the vanishing in III.3.12 for `𝒪` is the case `M = R`. -/
theorem III_3_12_structure [IsNoetherianRing R] (fs : List R)
    {i : ℕ} (hi : fs.length < i) :
    Subsingleton (ExposeI.H_Z (ExposeII.affineSupportClosed (ExposeII.koszulIdeal fs))
      (ExposeII.affineTildeAbSheaf (ModuleCat.of R R)) i) :=
  III_3_12_koszul fs (ModuleCat.of R R) hi

/-- Conversely, vanishing above the number of generators on every finite
module follows from the same Koszul bound, so it is equivalent to the
structure-sheaf vanishing in that range. -/
theorem III_3_12 [IsNoetherianRing R] (fs : List R) {i : ℕ} (hi : fs.length < i) :
    (∀ M : ModuleCat.{u} R, Subsingleton
      (ExposeI.H_Z (ExposeII.affineSupportClosed (ExposeII.koszulIdeal fs))
        (ExposeII.affineTildeAbSheaf M) i)) ↔
      Subsingleton (ExposeI.H_Z (ExposeII.affineSupportClosed (ExposeII.koszulIdeal fs))
        (ExposeII.affineTildeAbSheaf (ModuleCat.of R R)) i) :=
  ⟨fun h => h (ModuleCat.of R R), fun _ M => III_3_12_koszul fs M hi⟩

end SGA.SGA2.ExposeIII
