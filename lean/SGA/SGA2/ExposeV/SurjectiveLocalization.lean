/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.SurjectiveScalarChange
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Prime localization across a quotient map

The original local ring map induced by a surjection is surjective. The
original localized coefficient modules agree after restriction along that
map, and the corresponding prime quotients have equal Krull dimensions.
These are the algebraic transport steps in the reduction of V.3.5.
-/

noncomputable section
universe u
open CategoryTheory IsLocalRing

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S]
variable (σ : R →+* S) (hσ : Function.Surjective σ)

include hσ

/-- The actual induced map on local rings is surjective. -/
theorem localRingHom_surjective (q : Ideal S) [q.IsPrime] :
    Function.Surjective (Localization.localRingHom (q.comap σ) q σ rfl) := by
  intro z
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl z
  obtain ⟨b, rfl⟩ := hσ a
  obtain ⟨t, ht⟩ := hσ s.val
  let t' : (q.comap σ).primeCompl := ⟨t, by
    change σ t ∉ q
    rw [ht]
    exact s.property⟩
  refine ⟨IsLocalization.mk' _ b t', ?_⟩
  rw [Localization.localRingHom_mk']
  congr 1
  exact Subtype.ext ht

/-- The quotient by a contracted ideal is the original target quotient. -/
def surjectivePrimeQuotientEquiv (q : Ideal S) :
    (R ⧸ q.comap σ) ≃+* (S ⧸ q) :=
  RingEquiv.ofBijective (Ideal.quotientMap q σ le_rfl)
    ⟨Ideal.quotientMap_injective, Ideal.quotientMap_surjective hσ⟩

/-- In particular the dimensions of the corresponding point closures agree. -/
theorem ringKrullDim_quotient_comap_of_surjective (q : Ideal S) :
    ringKrullDim (R ⧸ q.comap σ) = ringKrullDim (S ⧸ q) :=
  ringKrullDim_eq_of_ringEquiv (surjectivePrimeQuotientEquiv σ hσ q)

/-- Localizing an original target module at a prime and restricting scalars
agrees with localizing its restriction at the contracted prime. -/
def localizedRestrictScalarsIso (q : Ideal S) [q.IsPrime] (M : ModuleCat.{u} S) :
    ((ModuleCat.restrictScalars σ).obj M).localizedModule (q.comap σ).primeCompl ≅
      (ModuleCat.restrictScalars (Localization.localRingHom (q.comap σ) q σ rfl)).obj
        (M.localizedModule q.primeCompl) := by
  let p := q.comap σ
  let τ := Localization.localRingHom p q σ rfl
  let N := (ModuleCat.restrictScalars τ).obj (M.localizedModule q.primeCompl)
  letI : Module R N := Module.compHom N (algebraMap R (Localization.AtPrime p))
  haveI : IsScalarTower R (Localization.AtPrime p) N :=
    IsScalarTower.of_compHom R (Localization.AtPrime p) N
  have hsmul (r : R) (y : N) : r • y = σ r • (show M.localizedModule q.primeCompl from y) := by
    change τ (algebraMap R (Localization.AtPrime p) r) •
      (show M.localizedModule q.primeCompl from y) = _
    rw [Localization.localRingHom_to_map, IsScalarTower.algebraMap_smul]
  let f : (ModuleCat.restrictScalars σ).obj M →ₗ[R] N :=
    { toFun := M.localizedModuleMkLinearMap q.primeCompl
      map_add' := by intros; apply map_add
      map_smul' := by
        intro r x
        change M.localizedModuleMkLinearMap q.primeCompl (σ r • x) =
          r • (show N from M.localizedModuleMkLinearMap q.primeCompl x)
        rw [map_smul, hsmul] }
  haveI : IsLocalizedModule p.primeCompl f :=
    { map_units := by
        intro s
        rw [Module.End.isUnit_iff]
        change Function.Bijective (fun y : N ↦ (s.val : R) • y)
        simp_rw [hsmul]
        exact (Module.End.isUnit_iff _).mp
          (IsLocalizedModule.map_units (M.localizedModuleMkLinearMap q.primeCompl)
            (⟨σ s.val, show σ s.val ∉ q from s.property⟩ : q.primeCompl))
      surj := by
        intro y
        obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj q.primeCompl
          (M.localizedModuleMkLinearMap q.primeCompl) y
        obtain ⟨t, ht⟩ := hσ s.val
        refine ⟨⟨x, ⟨t, ?_⟩⟩, ?_⟩
        · change σ t ∉ q
          rw [ht]
          exact s.property
        · change t • y = f x
          rw [hsmul, ht]
          exact hs
      exists_of_eq := by
        intro x y hxy
        obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq
          (S := q.primeCompl) (f := M.localizedModuleMkLinearMap q.primeCompl) hxy
        obtain ⟨t, ht⟩ := hσ s.val
        refine ⟨⟨t, ?_⟩, ?_⟩
        · change σ t ∉ q
          rw [ht]
          exact s.property
        · change σ t • x = σ t • y
          rw [ht]
          exact hs }
  exact (LinearEquiv.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
    (IsLocalizedModule.linearEquiv p.primeCompl
      (((ModuleCat.restrictScalars σ).obj M).localizedModuleMkLinearMap p.primeCompl)
      f)).toModuleIso

/-- The comparison sends the image of each original element to its image
in the target localization. -/
@[simp]
theorem localizedRestrictScalarsIso_hom_mk (q : Ideal S) [q.IsPrime]
    (M : ModuleCat.{u} S) (x : M) :
    (localizedRestrictScalarsIso σ hσ q M).hom
        (((ModuleCat.restrictScalars σ).obj M).localizedModuleMkLinearMap
          (q.comap σ).primeCompl x) = M.localizedModuleMkLinearMap q.primeCompl x := by
  simp [localizedRestrictScalarsIso, LinearEquiv.extendScalarsOfIsLocalization]

omit hσ in
/-- Outside the closed image of the quotient map the actual localized
coefficient module is zero, without finite-generation assumptions. -/
theorem localizedRestrictScalars_isZero_of_ker_not_le (M : ModuleCat.{u} S)
    (p : PrimeSpectrum R) (hp : ¬ RingHom.ker σ ≤ p.asIdeal) :
    Limits.IsZero (((ModuleCat.restrictScalars σ).obj M).localizedModule p.asIdeal.primeCompl) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  apply (Equiv.subsingleton_congr
    (equivShrink (LocalizedModule p.asIdeal.primeCompl
      ((ModuleCat.restrictScalars σ).obj M)))).mp
  apply Module.notMem_support_iff.mp
  intro hmem
  apply hp
  apply le_trans _ (Module.annihilator_le_of_mem_support hmem)
  rw [restrictScalars_annihilator]
  exact Ideal.ker_le_comap σ

/-- A target point is closed exactly when its image point is closed. -/
theorem comap_eq_maximalIdeal_iff_of_surjective [IsLocalRing R] [IsLocalRing S]
    (q : Ideal S) : q.comap σ = maximalIdeal R ↔ q = maximalIdeal S := by
  have : IsLocalHom σ := IsLocalHom.of_surjective σ hσ
  rw [← IsLocalRing.maximalIdeal_comap σ]
  exact (Ideal.comap_injective_of_surjective σ hσ).eq_iff

end SGA.SGA2.ExposeV
