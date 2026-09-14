/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.AffineComplementLocalization
import SGA.SGA2.ExposeV.AffineComplementVanishing
import SGA.SGA2.ExposeV.ClosedComponentGenericPoint
import Mathlib.AlgebraicGeometry.Properties

/-!
# V.3.4: codimension of a closed subset with affine complement

At each original component generic point, the actual punctured localization
is affine. The proved local dimension bound therefore gives height at most
one, and the literal infimum of structure-stalk dimensions gives the source's
codimension of that component.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry IsLocalRing TopologicalSpace
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

/-- The source's codimension of a subset of the affine spectrum: the infimum
of the dimensions of its actual local structure rings. -/
def affineSubsetCodimension (Z : Set (Spec R)) : WithBot ℕ∞ :=
  ⨅ p ∈ Z, ringKrullDim ((Spec R).presheaf.stalk p)

/-- Actual affine structure-stalk dimension is the original prime's height. -/
theorem affineStructureStalk_ringKrullDim (p : PrimeSpectrum R) :
    ringKrullDim ((Spec R).presheaf.stalk p) = p.asIdeal.height := by
  let : Algebra R ((Spec R).presheaf.stalk p) := StructureSheaf.stalkAlgebra R p
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R p
  exact IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal _

/-- The source's literal stalk-dimension codimension of the closure of a
prime is its height, because that prime belongs to its closure and has
minimal height there. -/
theorem affineSubsetCodimension_zeroLocus_prime (p : PrimeSpectrum R) :
    affineSubsetCodimension (R := R) (PrimeSpectrum.zeroLocus (p.asIdeal : Set R)) =
      p.asIdeal.height := by
  apply le_antisymm
  · exact (iInf₂_le p (show p ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set R)
      from fun _ hx => hx)).trans
      (affineStructureStalk_ringKrullDim p).le
  · apply le_iInf₂
    intro q hq
    rw [affineStructureStalk_ringKrullDim q]
    exact_mod_cast Ideal.height_mono hq

variable [IsNoetherianRing R]

/-- **V.3.4, component generic points.** Every minimal prime of an ideal
whose actual open complement is affine has height at most one. -/
theorem minimalPrime_height_le_one_of_affineComplement (J : Ideal R)
    (hJ : IsAffineOpen (affineSupportComplement J))
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ J.minimalPrimes) :
    p.asIdeal.height ≤ 1 := by
  have hlocal := localRing_ringKrullDim_le_one_of_affinePuncturedSpectrum
    (isAffineOpen_puncturedSpectrum_at_minimalPrime J hJ p hp)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
    (Localization.AtPrime p.asIdeal)] at hlocal
  exact_mod_cast hlocal

/-- **V.3.4, original component codimension.** The actual closed component
defined by each minimal prime has codimension at most one in the original
affine spectrum, measured using its actual structure-stalk rings. -/
theorem component_codimension_le_one_of_affineComplement (J : Ideal R)
    (hJ : IsAffineOpen (affineSupportComplement J))
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ J.minimalPrimes) :
    affineSubsetCodimension (R := R) (PrimeSpectrum.zeroLocus (p.asIdeal : Set R)) ≤ 1 := by
  rw [affineSubsetCodimension_zeroLocus_prime]
  exact_mod_cast minimalPrime_height_le_one_of_affineComplement J hJ p hp

/-- **V.3.4, actual irreducible components of `V(J)`.** The original
component's image in the ambient spectrum has codimension at most one. -/
theorem irreducibleComponent_zeroLocus_codimension_le_one (J : Ideal R)
    (hJ : IsAffineOpen (affineSupportComplement J))
    (C : Set (PrimeSpectrum.zeroLocus (J : Set R)))
    (hC : C ∈ irreducibleComponents (PrimeSpectrum.zeroLocus (J : Set R))) :
    affineSubsetCodimension (R := R) (Subtype.val '' C) ≤ 1 := by
  obtain ⟨p, hp, hCp⟩ := closedComponent_exists_minimalPrime J C hC
  rw [hCp]
  exact component_codimension_le_one_of_affineComplement J hJ p hp

/-- **V.3.4.** Every actual irreducible component of any closed subset
with affine complement in a noetherian affine spectrum has codimension
at most one, using the literal infimum of original structure-stalk dimensions. -/
theorem irreducibleComponent_codimension_le_one_of_affineComplement
    (Y : Closeds (Spec R)) (hY : IsAffineOpen Y.compl)
    (C : Set Y) (hC : C ∈ irreducibleComponents Y) :
    affineSubsetCodimension (R := R) (Subtype.val '' C) ≤ 1 := by
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (Y : Set (Spec R))).mp Y.isClosed
  have hYJ : Y = affineSupportClosed J := Closeds.ext hJ
  subst Y
  exact irreducibleComponent_zeroLocus_codimension_le_one J hY C hC

end SGA.SGA2.ExposeV
