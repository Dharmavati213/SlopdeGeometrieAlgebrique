/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.LocalParameters
import SGA.SGA2.ExposeII.KoszulLocalCohomology
import SGA.SGA2.ExposeII.PrincipalCechComparison

/-!
# Local-cohomology vanishing above the local ring dimension

Actual dimension-length parameters, radical invariance, and the original
Koszul comparison prove the bound for every noetherian local ring and
every coefficient module. No regularity or completeness is assumed.
The sharper bound by the dimension of the coefficient module is separate.
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Local cohomology supported on the radical of a finitely generated ideal
vanishes above the actual length of its given generator list. -/
theorem localCohomology_isZero_of_radical_parameters (I : Ideal R) (fs : List R)
    (hfs : I.radical = (koszulIdeal fs).radical)
    (M : ModuleCat.{u} R) (i : ℕ) (hi : fs.length < i) :
    IsZero ((_root_.localCohomology I i).obj M) := by
  let e := (localCohomology.isoOfSameRadical hfs i).app M ≪≫
    (localCohomologyIsoStableKoszul fs i).app M
  exact (stableKoszulCohomology_isZero_above_length fs M i hi).of_iso e

/-- **V.3.1(i), ring-dimension bound over every noetherian local base.**
The coefficient module need not be finite. -/
theorem localRing_localCohomology_isZero_of_gt [IsLocalRing R]
    (n : ℕ) (hdim : ringKrullDim R = n)
    (M : ModuleCat.{u} R) (i : ℕ) (hi : n < i) :
    IsZero ((_root_.localCohomology (maximalIdeal R) i).obj M) := by
  obtain ⟨fs, hlen, hrad⟩ := exists_localParameters n hdim
  exact localCohomology_isZero_of_radical_parameters (maximalIdeal R) fs
    (by simpa only [Ideal.IsPrime.radical] using hrad.symm) M i (hlen ▸ hi)

end SGA.SGA2.ExposeV
