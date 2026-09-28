/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.LocalCohomologyScalarChange
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.KrullDimension.Module

/-!
# V, formula (19): the actual surjective change of local rings

For a surjective homomorphism of noetherian local rings, maximal-ideal local
cohomology agrees with scalar restriction of local cohomology over the target.
The comparison is linear over the source ring, retains arbitrary coefficient
modules, and does not assume flatness. Extended length and finite length of
these original local-cohomology modules are consequently unchanged.

This proves the algebraic comparison used after V.3.2; it does not claim the
general ringed-space spectral sequence of that lemma or Cohen's theorem.
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S]
variable (σ : R →+* S) (hσ : Function.Surjective σ)

include hσ

/-- Restriction along a surjective ring map preserves the actual submodule
lattice, hence extended length, for an arbitrary target-ring module. -/
theorem restrictScalars_length_of_surjective (M : ModuleCat.{u} S) :
    Module.length R ((ModuleCat.restrictScalars σ).obj M) = Module.length S M := by
  let : RingHomSurjective σ := ⟨hσ⟩
  let f : (ModuleCat.restrictScalars σ).obj M →ₛₗ[σ] M :=
    { toFun := fun x ↦ x, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f Function.bijective_id)]

/-- Finite length is unchanged under actual restriction of scalars. -/
theorem restrictScalars_finiteLength_iff_of_surjective (M : ModuleCat.{u} S) :
    IsFiniteLength R ((ModuleCat.restrictScalars σ).obj M) ↔ IsFiniteLength S M := by
  rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff,
    restrictScalars_length_of_surjective σ hσ]

/-- Finite generation is unchanged under a surjective restriction of scalars. -/
theorem restrictScalars_finite_iff_of_surjective (M : ModuleCat.{u} S) :
    Module.Finite R ((ModuleCat.restrictScalars σ).obj M) ↔ Module.Finite S M := by
  let : RingHomSurjective σ := ⟨hσ⟩
  let f : (ModuleCat.restrictScalars σ).obj M →ₛₗ[σ] M :=
    { toFun := fun x ↦ x, map_add' := by intros; rfl, map_smul' := by intros; rfl }
  exact f.finite_iff_of_bijective Function.bijective_id

omit hσ in
/-- The annihilator of the unchanged module is the actual contracted ideal. -/
theorem restrictScalars_annihilator (M : ModuleCat.{u} S) :
    Module.annihilator R ((ModuleCat.restrictScalars σ).obj M) =
      (Module.annihilator S M).comap σ := by
  ext r
  rfl

/-- **V, formula (21):** the original annihilator quotients are isomorphic
by the ring map induced from the given surjection. -/
def restrictScalarsAnnihilatorQuotientEquiv (M : ModuleCat.{u} S) :
    (R ⧸ Module.annihilator R ((ModuleCat.restrictScalars σ).obj M)) ≃+*
      (S ⧸ Module.annihilator S M) :=
  (Ideal.quotEquivOfEq (restrictScalars_annihilator σ M)).trans
    (RingEquiv.ofBijective (Ideal.quotientMap (Module.annihilator S M) σ le_rfl)
      ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective hσ⟩)

/-- The actual finite module has the same support dimension over either
ring, as asserted after formula (21). -/
theorem restrictScalars_supportDim_of_surjective (M : ModuleCat.{u} S) [Module.Finite S M] :
    Module.supportDim R ((ModuleCat.restrictScalars σ).obj M) = Module.supportDim S M := by
  have : Module.Finite R ((ModuleCat.restrictScalars σ).obj M) :=
    (restrictScalars_finite_iff_of_surjective σ hσ M).mpr inferInstance
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  exact ringKrullDim_eq_of_ringEquiv (restrictScalarsAnnihilatorQuotientEquiv σ hσ M)

variable [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]

/-- **V, formula (19):** the original maximal-ideal local cohomology over
the source ring is scalar restriction of the original target-ring value. -/
def localRing_localCohomologyScalarChangeIso (M : ModuleCat.{u} S) (i : ℕ) :
    (_root_.localCohomology (maximalIdeal R) i).obj ((ModuleCat.restrictScalars σ).obj M) ≅
      (ModuleCat.restrictScalars σ).obj ((_root_.localCohomology (maximalIdeal S) i).obj M) := by
  simpa only [map_maximalIdeal_of_surjective σ hσ] using
    (localCohomologyScalarChangeIso σ (maximalIdeal R) M i).symm

/-- The original local-cohomology values have the same extended length
on either side of a surjective change of local rings. -/
theorem localRing_localCohomology_length_eq_of_surjective (M : ModuleCat.{u} S) (i : ℕ) :
    Module.length R
        ((_root_.localCohomology (maximalIdeal R) i).obj ((ModuleCat.restrictScalars σ).obj M)) =
      Module.length S ((_root_.localCohomology (maximalIdeal S) i).obj M) :=
  (localRing_localCohomologyScalarChangeIso σ hσ M i).toLinearEquiv.length_eq.trans
    (restrictScalars_length_of_surjective σ hσ _)

/-- The finite-length condition in V.3.5 is unchanged by its surjective
local-ring reduction, on the original local-cohomology modules. -/
theorem localRing_localCohomology_finiteLength_iff_of_surjective
    (M : ModuleCat.{u} S) (i : ℕ) :
    IsFiniteLength R
        ((_root_.localCohomology (maximalIdeal R) i).obj ((ModuleCat.restrictScalars σ).obj M)) ↔
      IsFiniteLength S ((_root_.localCohomology (maximalIdeal S) i).obj M) := by
  rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff,
    localRing_localCohomology_length_eq_of_surjective σ hσ M i]

end SGA.SGA2.ExposeV
