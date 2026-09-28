/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.PowerSeriesResidueContinuous

/-!
# Gluing the actual residue pairings

The original positive Koszul quotient stages, with their original product
transition maps, have the genuine continuous dual as their colimit. The
map is the explicit product-residue pairing at every stage. Injectivity
uses finite-stage nondegeneracy; surjectivity uses continuity and the
perfect finite-stage pairings, not an abstract uniqueness theorem.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K]

/-- Positive stages of the original coordinate Koszul quotient diagram. -/
def powerSeriesPositiveQuotientDiagram (d : ℕ) :
    ℕ ⥤ ModuleCat.{u} (MvPowerSeries (Fin d) K) :=
  positivePowerIndex ⋙ koszulTopQuotientDiagram (powerSeriesCoordinates K d)
    (ModuleCat.of (MvPowerSeries (Fin d) K) (MvPowerSeries (Fin d) K))

/-- The original Koszul quotient stage maps to the continuous dual by the
explicit residue pairing. -/
def powerSeriesResidueStage (d r : ℕ) :
    (powerSeriesPositiveQuotientDiagram K d).obj r ⟶ powerSeriesContinuousDual K d :=
  (powerSeriesKoszulQuotientIso K d (r + 1)).hom ≫ powerSeriesResidueToContinuous K d r

@[simp]
theorem powerSeriesResidueStage_mk (d r : ℕ) (f a : MvPowerSeries (Fin d) K) :
    powerSeriesResidueStage K d r (Submodule.Quotient.mk f) a =
      MvPowerSeries.coeff (powerSeriesResidueExponent d r) (f * a) := by
  exact powerSeriesResidueToContinuous_mk K d r f a

/-- The genuine product transition preserves the functional on every
original power series argument. -/
@[reassoc]
theorem powerSeriesResidueStage_transition (d : ℕ) {r s : ℕ} (h : r ≤ s) :
    (powerSeriesPositiveQuotientDiagram K d).map (homOfLE h) ≫ powerSeriesResidueStage K d s =
      powerSeriesResidueStage K d r := by
  let : TopologicalSpace (MvPowerSeries (Fin d) K) :=
    (maximalIdeal (MvPowerSeries (Fin d) K)).adicTopology
  let : TopologicalSpace K := ⊥
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ x
  apply ContinuousLinearMap.ext
  intro a
  change powerSeriesResidueStage K d s
    (Submodule.Quotient.mk
      (((powerSeriesCoordinates K d).map (fun x => x ^ ((s + 1) - (r + 1)))).prod * f)) a =
    powerSeriesResidueStage K d r (Submodule.Quotient.mk f) a
  rw [powerSeriesResidueStage_mk, powerSeriesResidueStage_mk, mul_assoc]
  exact powerSeriesResidue_transition_coeff K d h (f * a)

/-- The actual finite residues glue on the original diagram. -/
def powerSeriesResidueCocone (d : ℕ) : Cocone (powerSeriesPositiveQuotientDiagram K d) where
  pt := powerSeriesContinuousDual K d
  ι :=
    { app := powerSeriesResidueStage K d
      naturality := fun r s f => by
        have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
        rw [hf]
        change _ = _ ≫ 𝟙 _
        rw [Category.comp_id]
        exact powerSeriesResidueStage_transition K d (leOfHom f) }

/-- The explicit glued map, on the actual categorical colimit. -/
def powerSeriesResidueColimitMap (d : ℕ) :
    colimit (powerSeriesPositiveQuotientDiagram K d) ⟶ powerSeriesContinuousDual K d :=
  colimit.desc _ (powerSeriesResidueCocone K d)

@[reassoc (attr := simp)]
theorem powerSeriesResidueColimitMap_ι (d r : ℕ) :
    colimit.ι (powerSeriesPositiveQuotientDiagram K d) r ≫ powerSeriesResidueColimitMap K d =
      powerSeriesResidueStage K d r := colimit.ι_desc _ r

/-- The explicit glued residue map is injective by the original finite
quotient pairing, using genuine filtered-colimit representatives. -/
theorem powerSeriesResidueColimitMap_injective (d : ℕ) :
    Function.Injective (powerSeriesResidueColimitMap K d) := by
  have : PreservesFilteredColimitsOfSize.{0, 0}
      (forget (ModuleCat.{u} (MvPowerSeries (Fin d) K))) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, 0} _
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨r, y, rfl⟩ := Concrete.colimit_exists_rep (powerSeriesPositiveQuotientDiagram K d) x
  have hy : y = 0 := by
    apply (powerSeriesKoszulQuotientIso K d (r + 1)).toLinearEquiv.injective
    apply powerSeriesResidueToContinuous_injective K d r
    change powerSeriesResidueStage K d r y =
      powerSeriesResidueToContinuous K d r ((powerSeriesKoszulQuotientIso K d (r + 1)).hom 0)
    rw [map_zero, map_zero]
    change (colimit.ι (powerSeriesPositiveQuotientDiagram K d) r ≫
      powerSeriesResidueColimitMap K d) y = 0 at hx
    rwa [powerSeriesResidueColimitMap_ι] at hx
  rw [hy, map_zero]

/-- Continuity and perfect finite-stage pairings prove surjectivity of the
explicit glued map, without any choice of an abstract representing isomorphism. -/
theorem powerSeriesResidueColimitMap_surjective (d : ℕ) :
    Function.Surjective (powerSeriesResidueColimitMap K d) := by
  intro φ
  obtain ⟨r, x, hx⟩ := powerSeriesContinuousDual_exists_residue_stage K d φ
  refine ⟨colimit.ι (powerSeriesPositiveQuotientDiagram K d) r
    ((powerSeriesKoszulQuotientIso K d (r + 1)).inv x), ?_⟩
  change (colimit.ι (powerSeriesPositiveQuotientDiagram K d) r ≫
    powerSeriesResidueColimitMap K d) _ = φ
  rw [powerSeriesResidueColimitMap_ι]
  change powerSeriesResidueToContinuous K d r
    ((powerSeriesKoszulQuotientIso K d (r + 1)).hom
      ((powerSeriesKoszulQuotientIso K d (r + 1)).inv x)) = φ
  simpa using hx

/-- The explicit residue isomorphism from the original coordinate-power
colimit to the actual continuous dual, with original ring-linear structure. -/
def powerSeriesResidueColimitIso (d : ℕ) :
    colimit (powerSeriesPositiveQuotientDiagram K d) ≅ powerSeriesContinuousDual K d :=
  (LinearEquiv.ofBijective (powerSeriesResidueColimitMap K d).hom
    ⟨powerSeriesResidueColimitMap_injective K d,
      powerSeriesResidueColimitMap_surjective K d⟩).toModuleIso

@[simp]
theorem powerSeriesResidueColimitIso_hom (d : ℕ) :
    (powerSeriesResidueColimitIso K d).hom = powerSeriesResidueColimitMap K d := rfl

end SGA.SGA2.ExposeIV
