/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.AffineOpenCohomologyVanishing
import SGA.SGA2.ExposeII.AffineRelativeSequence
import SGA.SGA2.ExposeII.AffineCohomologyComparison
import SGA.SGA2.ExposeV.LocalRingTopNonvanishing

/-!
# V.3.4: affine-complement vanishing and the punctured local spectrum

The original affine comparison and relative sequence turn genuine affine
vanishing on the complement into vanishing of algebraic local cohomology
above degree one. Original top nonvanishing then bounds the local dimension.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry IsLocalRing
open SGA.SGA2.ExposeI SGA.SGA2.ExposeII SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} [IsNoetherianRing R]

/-- If the actual complement of `V(J)` is affine, original local cohomology
with support in `J` vanishes above degree one for every coefficient module. -/
theorem localCohomology_isZero_of_affineComplement (J : Ideal R)
    (hJ : IsAffineOpen (affineSupportComplement J)) (M : ModuleCat.{u} R) (n : ℕ) :
    IsZero ((_root_.localCohomology J (n + 2)).obj M) := by
  have hzero : Subsingleton
      (H (restrictToOpen (affineTildeAbSheaf M) (affineSupportClosed J).compl) (n + 1)) :=
    affineOpen_H_pos_subsingleton (tilde M) (affineSupportComplement J) hJ n
  let e := (affineLocalCohomologyAddEquiv J M (n + 2)).trans
    (affineSupportedCohomologyEquivOpen M (affineSupportClosed J) n)
  exact ModuleCat.isZero_iff_subsingleton.mpr e.injective.subsingleton

/-- **V.3.4, local step.** A noetherian local ring with affine punctured
spectrum has Krull dimension at most one, by actual top nonvanishing. -/
theorem localRing_ringKrullDim_le_one_of_affinePuncturedSpectrum [IsLocalRing R]
    (hR : IsAffineOpen (affineSupportComplement (maximalIdeal R))) :
    ringKrullDim R ≤ 1 := by
  let n := (LTSeries.longestOf (PrimeSpectrum R)).length
  have hd : ringKrullDim R = n := Order.krullDim_eq_length_of_finiteDimensionalOrder
  suffices hn : n ≤ 1 by
    rw [hd]
    exact_mod_cast hn
  by_contra hn
  have hn2 : 2 ≤ n := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn2
  have hMk : Module.supportDim R (ModuleCat.of R R) = n :=
    (Module.supportDim_self_eq_ringKrullDim R).trans hd
  have hne := localRing_topLocalCohomology_nontrivial n (ModuleCat.of R R) hMk
  have hz : IsZero ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R)) := by
    rw [hk, Nat.add_comm 2 k]
    exact localCohomology_isZero_of_affineComplement (maximalIdeal R) hR _ k
  exact not_nontrivial_iff_subsingleton.mpr (ModuleCat.isZero_iff_subsingleton.mp hz) hne

end SGA.SGA2.ExposeV
