/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.AffineDepth
import SGA.SGA2.ExposeIII.AffineClopens
import SGA.SGA2.ExposeII.AffineCohomologyVanishing
import SGA.SGA2.ExposeI.RelativeCohomologySections

/-!
# Hartogs extension on noetherian affine schemes

The actual relative cohomology sequence turns the affine depth criterion
into restriction criteria. In particular, depth at least two is equivalent
to unique extension of actual associated-sheaf sections from the complement
of the closed support.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

section Sections

variable {X : TopCat.{u}}

private def openHZeroSectionsEquiv (Z : Closeds X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ExposeI.H (ExposeI.restrictToOpen F Z.compl) 0 ≃+
      F.presheaf.obj (op Z.compl) :=
  (CategoryTheory.Sheaf.H.equiv₀ (ExposeI.restrictToOpen F Z.compl) isTerminalTop).trans
    (ExposeI.restrictToOpenSectionsIso Z.compl F).addCommGroupIsoToAddEquiv

private theorem restriction_zero_square (Z : Closeds X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (F.presheaf.map (homOfLE le_top : Z.compl ⟶ ⊤).op : _ → _) ∘
      (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop) =
    (openHZeroSectionsEquiv Z F) ∘ ExposeI.relativeRestriction Z F 0 := by
  funext x
  exact (ExposeI.relativeRestriction_zero_sections Z F x).symm

/-- Degree-zero relative restriction is injective exactly when actual
restriction of global sections is injective. -/
theorem globalRestriction_injective_iff_relativeRestriction (Z : Closeds X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Function.Injective (F.presheaf.map (homOfLE le_top : Z.compl ⟶ ⊤).op) ↔
      Function.Injective (ExposeI.relativeRestriction Z F 0) := by
  rw [← (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop).toEquiv.injective_comp
    (F.presheaf.map (homOfLE le_top : Z.compl ⟶ ⊤).op)]
  erw [restriction_zero_square Z F]
  exact Equiv.comp_injective _ (openHZeroSectionsEquiv Z F).toEquiv

/-- Degree-zero relative restriction is bijective exactly when actual
restriction of global sections is bijective. -/
theorem globalRestriction_bijective_iff_relativeRestriction (Z : Closeds X)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Function.Bijective (F.presheaf.map (homOfLE le_top : Z.compl ⟶ ⊤).op) ↔
      Function.Bijective (ExposeI.relativeRestriction Z F 0) := by
  rw [← (CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop).toEquiv.bijective_comp
    (F.presheaf.map (homOfLE le_top : Z.compl ⟶ ⊤).op)]
  erw [restriction_zero_square Z F]
  exact Equiv.comp_bijective _ (openHZeroSectionsEquiv Z F).toEquiv

end Sections

variable {R : CommRingCat.{u}} [IsNoetherianRing R]

/-- Actual restriction from the affine scheme to the complement of `V(I)`. -/
def affineRestriction (I : Ideal R) (M : ModuleCat.{u} R) :
    (affineTildeAbSheaf M).presheaf.obj (op ⊤) ⟶
      (affineTildeAbSheaf M).presheaf.obj (op (affineSupportComplement I)) :=
  (affineTildeAbSheaf M).presheaf.map
    (homOfLE le_top : affineSupportComplement I ⟶ ⊤).op

/-- **III.3.4, affine restriction criterion:** a positive depth threshold
is equivalent to bijective relative restrictions below the threshold and
injective restriction at its last degree. -/
theorem succ_le_depth_iff_relativeRestriction (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ depth I M ↔
      ((∀ i : ℕ, i < n → Function.Bijective
          (ExposeI.relativeRestriction (affineSupportClosed I) (affineTildeAbSheaf M) i)) ∧
        Function.Injective
          (ExposeI.relativeRestriction (affineSupportClosed I) (affineTildeAbSheaf M) n)) := by
  rw [le_depth_iff_affine_H_Z_vanishes]
  simpa only [Nat.lt_succ_iff] using
    ExposeI.supported_vanishing_iff_relativeRestriction
      (affineSupportClosed I) (affineTildeAbSheaf M) n

/-- Depth at least one is exactly uniqueness of extension from the open complement. -/
theorem one_le_depth_iff_affineRestriction_injective (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    (1 : ℕ∞) ≤ depth I M ↔ Function.Injective (affineRestriction I M) := by
  have h := succ_le_depth_iff_relativeRestriction I M 0
  simp only [Nat.not_lt_zero, false_implies, implies_true, true_and] at h
  exact h.trans (globalRestriction_injective_iff_relativeRestriction
    (affineSupportClosed I) (affineTildeAbSheaf M)).symm

/-- **Affine Hartogs:** depth at least two is exactly unique extension of
all actual sections from `Spec R \ V(I)` to `Spec R`. -/
theorem two_le_depth_iff_affineRestriction_bijective (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    (2 : ℕ∞) ≤ depth I M ↔ Function.Bijective (affineRestriction I M) := by
  have hz := affineTildeAb_H_pos_subsingleton M 0
  have hi : Function.Injective
      (ExposeI.relativeRestriction (affineSupportClosed I) (affineTildeAbSheaf M) 1) :=
    Function.injective_of_subsingleton _
  have h := succ_le_depth_iff_relativeRestriction I M 1
  simp only [Nat.lt_one_iff, forall_eq, and_iff_left hi] at h
  exact h.trans (globalRestriction_bijective_iff_relativeRestriction
    (affineSupportClosed I) (affineTildeAbSheaf M)).symm

/-- Every section extends uniquely across a depth-at-least-two closed subset. -/
theorem affineRestriction_bijective_of_two_le_depth (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] (h : (2 : ℕ∞) ≤ depth I M) :
    Function.Bijective (affineRestriction I M) :=
  (two_le_depth_iff_affineRestriction_bijective I M).mp h

/-- The actual restriction map, packaged as an additive equivalence. -/
def affineHartogsEquiv (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (h : (2 : ℕ∞) ≤ depth I M) :
    (affineTildeAbSheaf M).presheaf.obj (op ⊤) ≃+
      (affineTildeAbSheaf M).presheaf.obj (op (affineSupportComplement I)) :=
  AddEquiv.ofBijective (affineRestriction I M).hom
    (affineRestriction_bijective_of_two_le_depth I M h)

/-- The localized depth condition along the closed support gives Hartogs extension. -/
theorem affineRestriction_bijective_of_localDepth (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (h : ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      (2 : ℕ∞) ≤ localDepth M p) : Function.Bijective (affineRestriction I M) :=
  affineRestriction_bijective_of_two_le_depth I M
    ((le_depth_iff_forall_localDepth I M 2).mpr h)

/-- **III.3.4:** over a noetherian local ring, the positive-threshold depth,
restriction, residue-module Ext, and supported-cohomology criteria agree. -/
theorem example_3_4 [IsLocalRing R] (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (((n + 1 : ℕ) : ℕ∞) ≤ depth (IsLocalRing.maximalIdeal R) M ↔
      ((∀ i : ℕ, i < n → Function.Bijective (ExposeI.relativeRestriction
        (affineSupportClosed (IsLocalRing.maximalIdeal R)) (affineTildeAbSheaf M) i)) ∧
      Function.Injective (ExposeI.relativeRestriction
        (affineSupportClosed (IsLocalRing.maximalIdeal R)) (affineTildeAbSheaf M) n))) ∧
    (((n + 1 : ℕ) : ℕ∞) ≤ depth (IsLocalRing.maximalIdeal R) M ↔
      ∀ i < n + 1, Subsingleton (Abelian.Ext
        (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) M i)) ∧
    (((n + 1 : ℕ) : ℕ∞) ≤ depth (IsLocalRing.maximalIdeal R) M ↔
      ∀ i < n + 1, Subsingleton (ExposeI.H_Z
        (affineSupportClosed (IsLocalRing.maximalIdeal R)) (affineTildeAbSheaf M) i)) := by
  have h := le_depth_iff_affine_H_Z_vanishes (IsLocalRing.maximalIdeal R) M (n + 1)
  exact ⟨succ_le_depth_iff_relativeRestriction _ M n,
    h.trans (affine_H_Z_vanishes_iff_quotient_ext _ M (n + 1)), h⟩

/-- The actual structure-sheaf restriction is bijective under the Hartogs
depth hypothesis on the structure module. -/
theorem affineStructureRestriction_bijective (I : Ideal R)
    (h : (2 : ℕ∞) ≤ depth I (ModuleCat.of R R)) :
    Function.Bijective ((Spec R).presheaf.map
      (homOfLE le_top : affineSupportComplement I ⟶ ⊤).op) :=
  affineRestriction_bijective_of_two_le_depth I (ModuleCat.of R R) h

/-- The actual global restriction is an isomorphism of rings, not only of
additive groups. This is the affine algebraic input to III.3.6. -/
def affineStructureHartogsRingEquiv (I : Ideal R)
    (h : (2 : ℕ∞) ≤ depth I (ModuleCat.of R R)) :
    (Spec R).presheaf.obj (op ⊤) ≃+*
      (Spec R).presheaf.obj (op (affineSupportComplement I)) :=
  RingEquiv.ofBijective ((Spec R).presheaf.map
    (homOfLE le_top : affineSupportComplement I ⟶ ⊤).op).hom
    (affineStructureRestriction_bijective I h)

/-- The local structure-module depth condition along `V(I)` gives the
actual ring-valued restriction isomorphism used in connectedness arguments. -/
def affineStructureHartogsRingEquivOfLocalDepth (I : Ideal R)
    (h : ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      (2 : ℕ∞) ≤ localDepth (ModuleCat.of R R) p) :
    (Spec R).presheaf.obj (op ⊤) ≃+*
      (Spec R).presheaf.obj (op (affineSupportComplement I)) :=
  affineStructureHartogsRingEquiv I ((le_depth_iff_forall_localDepth I (ModuleCat.of R R) 2).mpr h)

/-- **III.3.6, affine connectedness consequence:** removing a closed subset
of structure-module depth at least two preserves and reflects connectedness.
The proof uses the actual structure-sheaf ring restriction and genuine
clopen characteristic sections. -/
theorem affine_connected_iff_of_two_le_depth (I : Ideal R)
    (h : (2 : ℕ∞) ≤ depth I (ModuleCat.of R R)) :
    ConnectedSpace (Spec R) ↔ ConnectedSpace (affineSupportComplement I) :=
  connected_spectrum_iff_of_restriction_bijective (affineSupportComplement I)
    (affineStructureRestriction_bijective I h)

/-- The affine connectedness theorem stated with local structure-module
depth at every point of the closed support, as in III.3.6. This proves the
connectedness equivalence, not yet the full connected-component bijection. -/
theorem affine_connected_iff_of_localDepth (I : Ideal R)
    (h : ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      (2 : ℕ∞) ≤ localDepth (ModuleCat.of R R) p) :
    ConnectedSpace (Spec R) ↔ ConnectedSpace (affineSupportComplement I) :=
  affine_connected_iff_of_two_le_depth I
    ((le_depth_iff_forall_localDepth I (ModuleCat.of R R) 2).mpr h)

/-- The corresponding preconnectedness statement also handles empty schemes. -/
theorem affine_preconnected_iff_of_two_le_depth (I : Ideal R)
    (h : (2 : ℕ∞) ≤ depth I (ModuleCat.of R R)) :
    PreconnectedSpace (Spec R) ↔ PreconnectedSpace (affineSupportComplement I) :=
  preconnected_spectrum_iff_of_restriction_bijective (affineSupportComplement I)
    (affineStructureRestriction_bijective I h)

end SGA.SGA2.ExposeIII
