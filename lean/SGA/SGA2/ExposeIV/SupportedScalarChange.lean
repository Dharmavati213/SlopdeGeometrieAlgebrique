/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedModuleTorsion
import SGA.SGA2.ExposeIV.SupportedRestrictedHom
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Actual support under restriction and extension of scalars

For a finitely generated ideal, support is equivalent to elementwise
ideal-power torsion without noetherianity of the whole ring. This permits
actual scalar-change functors on supported modules, including completion,
without inserting noetherianity of the completed ring as an extra hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Limits ModuleCat TensorProduct
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Only the support ideal, not the entire ring, must be finitely generated. -/
theorem finite_support_pow_annihilator_of_fg (J : Ideal R) (hJ : J.FG)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    ∃ n : ℕ, J ^ n ≤ Module.annihilator R M := by
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hM
  exact Ideal.exists_pow_le_of_le_radical_of_fg hM hJ

/-- The arbitrary-module support/torsion equivalence only needs a finite ideal. -/
theorem powerTorsion_eq_top_iff_support_of_fg (J : Ideal R) (hJ : J.FG)
    (M : Type u) [AddCommGroup M] [Module R M] :
    powerTorsion J M = ⊤ ↔ Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R) := by
  refine ⟨support_subset_zeroLocus_of_powerTorsion_eq_top J M, fun hM => ?_⟩
  apply top_unique
  intro x _
  let N : Submodule R M := Submodule.span R {x}
  have hN := (Module.support_subset_of_injective N.subtype N.subtype_injective).trans hM
  obtain ⟨n, hn⟩ := finite_support_pow_annihilator_of_fg J hJ N hN
  refine (mem_powerTorsion_iff J M x).mpr ⟨n, fun r hr => ?_⟩
  exact congrArg Subtype.val (Module.mem_annihilator.mp (hn hr)
    (⟨x, Submodule.mem_span_singleton_self x⟩ : N))

/-- Restriction along the actual ring map identifies power torsion for `J`
with power torsion for its mapped ideal. -/
theorem powerTorsion_restrictScalars_iff (f : R →+* S) (J : Ideal R)
    (M : ModuleCat.{u} S) :
    powerTorsion J ((restrictScalars f).obj M) = ⊤ ↔
      powerTorsion (J.map f) M = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro x _
    have hx : x ∈ powerTorsion J ((restrictScalars f).obj M) := by rw [h]; trivial
    obtain ⟨n, hn⟩ := (mem_powerTorsion_iff J ((restrictScalars f).obj M) x).mp hx
    have hAnn : (J ^ n).map f ≤ Ideal.torsionOf S M x := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      exact hn r hr
    refine (mem_powerTorsion_iff (J.map f) M x).mpr ⟨n, fun s hs => ?_⟩
    apply hAnn
    rwa [Ideal.map_pow]
  · intro h
    apply top_unique
    intro x _
    have hx : x ∈ powerTorsion (J.map f) M := by rw [h]; trivial
    obtain ⟨n, hn⟩ := (mem_powerTorsion_iff (J.map f) M x).mp hx
    refine (mem_powerTorsion_iff J ((restrictScalars f).obj M) x).mpr
      ⟨n, fun r hr => ?_⟩
    apply hn (f r)
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f hr

/-- The actual support condition is equivalent under restriction, for a
finitely generated ideal, without finiteness of either the algebra or module. -/
theorem supported_restrictScalars_iff (f : R →+* S) (J : Ideal R) (hJ : J.FG)
    (M : ModuleCat.{u} S) :
    supportedModuleProperty J ((restrictScalars f).obj M) ↔
      supportedModuleProperty (J.map f) M := by
  rw [supportedModuleProperty, supportedModuleProperty,
    ← powerTorsion_eq_top_iff_support_of_fg J hJ,
    ← powerTorsion_eq_top_iff_support_of_fg (J.map f) (hJ.map f)]
  exact powerTorsion_restrictScalars_iff f J M

/-- Actual scalar extension preserves support, with the mapped ideal. -/
theorem supported_extendScalars (f : R →+* S) (J : Ideal R) (hJ : J.FG)
    (M : ModuleCat.{u} R) (hM : supportedModuleProperty J M) :
    supportedModuleProperty (J.map f) ((extendScalars f).obj M) := by
  let := f.toAlgebra
  apply support_subset_zeroLocus_of_powerTorsion_eq_top
  apply top_unique
  intro z hz
  clear hz
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | tmul a x =>
    change S at a
    have ht := (powerTorsion_eq_top_iff_support_of_fg J hJ M).mpr hM
    have hx : x ∈ powerTorsion J M := by rw [ht]; trivial
    obtain ⟨n, hn⟩ := (mem_powerTorsion_iff J M x).mp hx
    have hAnn : (J ^ n).map f ≤
        Ideal.torsionOf S ((extendScalars f).obj M) ((1 : S) ⊗ₜ[R] x) := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      change f r • (1 ⊗ₜ[R] x : S ⊗[R] M) = 0
      change algebraMap R S r • (1 ⊗ₜ[R] x : S ⊗[R] M) = 0
      rw [algebraMap_smul, ← TensorProduct.tmul_smul, hn r hr, TensorProduct.tmul_zero]
    have hy : ((1 : S) ⊗ₜ[R] x : (extendScalars f).obj M) ∈
        powerTorsion (J.map f) ((extendScalars f).obj M) := by
      refine (mem_powerTorsion_iff _ _ _).mpr ⟨n, fun s hs => ?_⟩
      apply hAnn
      rwa [Ideal.map_pow]
    have ha := Submodule.smul_mem (R := S)
      (powerTorsion (J.map f) ((extendScalars f).obj M)) a hy
    change (((a : S) * (1 : S)) ⊗ₜ[R] x : S ⊗[R] M) ∈ _ at ha
    simpa only [mul_one] using ha

/-- Restriction of scalars on the actual full categories of supported modules. -/
def supportedRestrictScalars (f : R →+* S) (J : Ideal R) (hJ : J.FG) :
    SupportedModuleCat (J.map f) ⥤ SupportedModuleCat J :=
  (supportedModuleProperty J).lift
    ((supportedModuleProperty (J.map f)).ι ⋙ restrictScalars f)
    (fun M => (supported_restrictScalars_iff f J hJ M.obj).mpr M.property)

/-- Extension of scalars on the actual full categories of supported modules. -/
def supportedExtendScalars (f : R →+* S) (J : Ideal R) (hJ : J.FG) :
    SupportedModuleCat J ⥤ SupportedModuleCat (J.map f) :=
  (supportedModuleProperty (J.map f)).lift
    ((supportedModuleProperty J).ι ⋙ extendScalars f)
    (fun M => supported_extendScalars f J hJ M.obj M.property)

/-- The supported adjunction is the restriction of the original tensor/restriction
adjunction, not a separately postulated Hom equivalence. -/
def supportedExtendRestrictScalarsAdj (f : R →+* S) (J : Ideal R) (hJ : J.FG) :
    supportedExtendScalars f J hJ ⊣ supportedRestrictScalars f J hJ :=
  (extendRestrictScalarsAdj f).restrictFullyFaithful
    (supportedModuleProperty J).fullyFaithfulι
    (supportedModuleProperty (J.map f)).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- The supported unit is literally the original scalar-extension unit. -/
@[simp] theorem supportedExtendRestrictScalarsAdj_unit_hom
    (f : R →+* S) (J : Ideal R) (hJ : J.FG) (M : SupportedModuleCat J) :
    ((supportedExtendRestrictScalarsAdj f J hJ).unit.app M).hom =
      (extendRestrictScalarsAdj f).unit.app M.obj := by
  change (supportedModuleProperty J).ι.map
    ((supportedExtendRestrictScalarsAdj f J hJ).unit.app M) = _
  simp only [supportedExtendRestrictScalarsAdj,
    Adjunction.map_restrictFullyFaithful_unit_app, Iso.refl_hom,
    NatTrans.id_app]
  rfl

/-- The supported counit is literally the original scalar-extension counit. -/
@[simp] theorem supportedExtendRestrictScalarsAdj_counit_hom
    (f : R →+* S) (J : Ideal R) (hJ : J.FG)
    (M : SupportedModuleCat (J.map f)) :
    ((supportedExtendRestrictScalarsAdj f J hJ).counit.app M).hom =
      (extendRestrictScalarsAdj f).counit.app M.obj := by
  change (supportedModuleProperty (J.map f)).ι.map
    ((supportedExtendRestrictScalarsAdj f J hJ).counit.app M) = _
  simp only [supportedExtendRestrictScalarsAdj,
    Adjunction.map_restrictFullyFaithful_counit_app, Iso.refl_inv,
    NatTrans.id_app]
  change 𝟙 _ ≫ (extendScalars f).map (𝟙 ((restrictScalars f).obj M.obj)) ≫
    (extendRestrictScalarsAdj f).counit.app M.obj = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

end SGA.SGA2.ExposeIV
