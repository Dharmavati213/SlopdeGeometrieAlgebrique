/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.LocalParameters
import SGA.SGA2.ExposeV.KoszulAnnihilatorVanishing
import SGA.SGA2.ExposeII.KoszulLocalCohomology

/-!
# V.3.1(i): vanishing above the actual module dimension

Over any noetherian local ring, lift a parameter system from the actual
annihilator quotient and prepend finite generators of the annihilator.
The resulting ideal has maximal radical. Above the module dimension its
original consecutive-power Hom--Koszul transition is zero, so its actual
cohomology colimit is zero. The canonical Koszul and radical comparisons
give the claim for the unchanged ideal-power local cohomology.
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R]

/-- The original ideal of a concatenated list is the sum of the two
original list ideals. -/
theorem koszulIdeal_append (gs fs : List R) :
    koszulIdeal (gs ++ fs) = koszulIdeal gs ⊔ koszulIdeal fs := by
  simp only [koszulIdeal, ← Ideal.span_union]
  congr 1
  ext x
  simp

variable [IsNoetherianRing R] [IsLocalRing R]

/-- **V.3.1(i), upper vanishing.** Local cohomology of a finite module
vanishes above its actual support dimension over every noetherian local
ring, without completeness or regularity assumptions. -/
theorem localRing_localCohomology_isZero_of_gt_moduleDim
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (n : ℕ) (hdim : Module.supportDim R M = n) (i : ℕ) (hi : n < i) :
    IsZero ((_root_.localCohomology (maximalIdeal R) i).obj M) := by
  classical
  obtain ⟨fs, hlen, hrad⟩ := exists_moduleParameters M n hdim
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (Module.annihilator R M)
  let gs := s.toList
  have hgs : koszulIdeal gs = Module.annihilator R M := by
    simpa [koszulIdeal, gs] using hs
  have hann : ∀ f ∈ gs, f ∈ Module.annihilator R M := by
    intro f hf
    rw [← hgs]
    exact Ideal.subset_span hf
  have hr : (maximalIdeal R).radical = (koszulIdeal (gs ++ fs)).radical := by
    rw [koszulIdeal_append, hgs, sup_comm, hrad]
    exact Ideal.IsPrime.radical inferInstance
  let e := (localCohomology.isoOfSameRadical hr i).app M ≪≫
    (localCohomologyIsoStableKoszul (gs ++ fs) i).app M
  exact (stableKoszulCohomology_isZero_of_annihilating_prefix M gs fs hann i (hlen ▸ hi)).of_iso e

end SGA.SGA2.ExposeV
