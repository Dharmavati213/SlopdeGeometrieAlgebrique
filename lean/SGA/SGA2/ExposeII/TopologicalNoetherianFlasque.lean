/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.InjectiveFlasque
import SGA.SGA2.ExposeII.KoszulSupportedComparison
import SGA.SGA2.ExposeI.FlasqueVanishingCriterion
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# SGA 2, II.10: flasqueness versus Koszul vanishing

Over a noetherian ring the associated sheaf of an injective module is
flasque. Combined with II.5, positive-degree stable Koszul cohomology of
every finite family then vanishes on injective coefficients, which is the
equivalence of II.10 on a noetherian spectrum.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

/-- **II.10, noetherian ring:** injective associated sheaves are flasque, so
by II.5 every positive stable Koszul group of an injective module vanishes. -/
theorem II_10_koszul_vanishing_of_injective [IsNoetherianRing R]
    (fs : List R) (E : ModuleCat.{u} R) [Injective E] {i : ℕ} (hi : 0 < i) :
    Subsingleton (ExposeI.H_Z (affineSupportClosed (koszulIdeal fs))
      (affineTildeAbSheaf E) i) := by
  have : TopCat.Sheaf.IsFlasque (affineTildeAbSheaf E) :=
    affineTildeAbSheaf_isFlasque_of_injective E
  have hpos : 0 < i := hi
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one.mpr hpos
  exact ExposeI.H_Z_pos_subsingleton_of_isFlasque
    (affineSupportClosed (koszulIdeal fs)) (affineTildeAbSheaf E) k

/-- **II.10, converse on a noetherian spectrum:** if associated sheaves of
injectives are flasque, then the Koszul vanishing of II.9 holds for every
finite family. -/
theorem II_10_flasque_implies_koszul [IsNoetherianRing R]
    (hfl : ∀ (E : ModuleCat.{u} R), Injective E →
      TopCat.Sheaf.IsFlasque (affineTildeAbSheaf E))
    (fs : List R) (E : ModuleCat.{u} R) [Injective E] {i : ℕ} (hi : 0 < i) :
    IsZero (stableKoszulCohomology fs E i) := by
  have : TopCat.Sheaf.IsFlasque (affineTildeAbSheaf E) := hfl E inferInstance
  have e := II_5_addEquiv fs E i
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one.mpr hi
  have hsub : Subsingleton (ExposeI.H_Z (affineSupportClosed (koszulIdeal fs))
      (affineTildeAbSheaf E) (k + 1)) :=
    ExposeI.H_Z_pos_subsingleton_of_isFlasque _ _ k
  have : Subsingleton
      ((forget₂ (ModuleCat R) AddCommGrpCat).obj (stableKoszulCohomology fs E (k + 1))) :=
    (e.subsingleton_congr).mpr hsub
  exact ModuleCat.isZero_iff_subsingleton.mpr this

/-- A noetherian ring has noetherian spectrum, so II.10 applies. -/
theorem primeSpectrum_noetherian [IsNoetherianRing R] :
    NoetherianSpace (PrimeSpectrum R) :=
  inferInstance

end SGA.SGA2.ExposeII
