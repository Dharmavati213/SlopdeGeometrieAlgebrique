/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Valuation.ValuationRing
import SGA.SGA1.ExposeIV.TorOne

/-!
# SGA 1, Exposé IV, §1: sorites on flat modules

The definition of flatness is mathlib's `Module.Flat`. The criteria by `Tor₁` and by ideals
at the beginning of IV.1 are in `SGA.SGA1.ExposeIV.TorOne`; the permanence properties (direct
sums, direct factors, projective modules, tensor products, change of base, transitivity) are
in mathlib and recorded here. We prove IV.1.1 (flat quotients in short exact sequences),
IV.1.2 (localization) and IV.1.3 (flatness and torsion).
-/

universe u v

namespace SGA.SGA1.ExposeIV

open TensorProduct LinearMap Function

variable {A : Type u} [CommRing A]

section Sorites

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

/-- IV.1: a direct sum of modules is flat if and only if each summand is. -/
theorem flat_directSum_iff {ι : Type v} (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] : Module.Flat A (DirectSum ι M) ↔ ∀ i, Module.Flat A (M i) :=
  Module.Flat.directSum_iff

/-- IV.1: a direct factor of a flat module is flat. -/
theorem flat_of_retract [Module.Flat A M] (i : N →ₗ[A] M) (r : M →ₗ[A] N)
    (h : r ∘ₗ i = LinearMap.id) : Module.Flat A N :=
  Module.Flat.of_retract i r h

/-- IV.1: a projective (in particular a free) module is flat. -/
theorem flat_of_projective [Module.Projective A M] : Module.Flat A M := inferInstance

/-- IV.1: the tensor product of two flat modules is flat. -/
theorem flat_tensorProduct [Module.Flat A M] [Module.Flat A N] : Module.Flat A (M ⊗[A] N) :=
  inferInstance

/-- IV.1: flatness is preserved by change of base. -/
theorem flat_baseChange (B : Type*) [CommRing B] [Algebra A B] [Module.Flat A M] :
    Module.Flat B (B ⊗[A] M) := inferInstance

/-- IV.1: transitivity of flatness. -/
theorem flat_trans (B : Type*) [CommRing B] [Algebra A B] [Module B M] [IsScalarTower A B M]
    [Module.Flat A B] [Module.Flat B M] : Module.Flat A M :=
  Module.Flat.trans A B M

/-- IV.1: a localization `S⁻¹A` is flat over `A`. -/
theorem flat_localization (S : Submonoid A) : Module.Flat A (Localization S) :=
  IsLocalization.flat _ S

end Sorites

section ShortExact

variable {M' M M'' : Type*} [AddCommGroup M'] [Module A M'] [AddCommGroup M] [Module A M]
  [AddCommGroup M''] [Module A M''] (f : M' →ₗ[A] M) (g : M →ₗ[A] M'')
  (hf : Injective f) (hfg : Exact f g) (hg : Surjective g)

include hf hfg hg

/-- IV.1.1 (i): a short exact sequence `0 → M' → M → M'' → 0` with `M''` flat stays exact after
tensoring with any module `N`. -/
theorem rTensor_shortExact_of_flat [Module.Flat A M''] (N : Type*) [AddCommGroup N]
    [Module A N] :
    Injective (f.rTensor N) ∧ Exact (f.rTensor N) (g.rTensor N) ∧ Surjective (g.rTensor N) :=
  ⟨(LinearMap.lTensor_inj_iff_rTensor_inj (M := N) (f := f)).1
      (LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hfg N),
    _root_.rTensor_exact N hfg hg, LinearMap.rTensor_surjective N hg⟩

/-- IV.1.1 (ii): in a short exact sequence `0 → M' → M → M'' → 0` with `M''` flat, `M` is flat
if and only if `M'` is. -/
theorem flat_iff_flat_of_flat_quotient [Module.Flat A M''] :
    Module.Flat A M ↔ Module.Flat A M' := by
  simp_rw [Module.Flat.iff_lTensor_injective']
  refine ⟨fun hM I ↦ ?_, fun hM' I ↦ ?_⟩
  · -- `M' ⊗ I → M ⊗ I → M ⊗ A` is injective and equals `M' ⊗ I → M' ⊗ A → M ⊗ A`
    have : (f.rTensor A) ∘ₗ (I.subtype.lTensor M') = (I.subtype.lTensor M) ∘ₗ (f.rTensor I) := by
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    have h := (hM I).comp (rTensor_shortExact_of_flat f g hf hfg hg I).1
    rw [← LinearMap.coe_comp, ← this, LinearMap.coe_comp] at h
    exact h.of_comp
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : g.rTensor I x = 0 := by
      apply Module.Flat.lTensor_preserves_injective_linearMap (M := M'') I.subtype
        Subtype.val_injective
      rw [map_zero, ← rTensor_lTensor_apply, hx, map_zero]
    obtain ⟨y, rfl⟩ := (_root_.rTensor_exact I hfg hg x).1 hx'
    have hy : I.subtype.lTensor M' y = 0 := by
      apply (rTensor_shortExact_of_flat f g hf hfg hg A).1
      rw [map_zero, rTensor_lTensor_apply, hx]
    rw [(injective_iff_map_eq_zero _).1 (hM' I) y hy, map_zero]

end ShortExact

section Localization

variable {B : Type*} [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- IV.1.2 (i): if the `B`-module `M` is `A`-flat, so is every localization `T⁻¹M` at a
multiplicative subset `T` of `B` (stated for any localization map `M → Mₜ`). -/
theorem flat_of_isLocalizedModule (T : Submonoid B) {Mₜ : Type*} [AddCommGroup Mₜ]
    [Module A Mₜ] [Module B Mₜ] [IsScalarTower A B Mₜ] (g : M →ₗ[B] Mₜ) [IsLocalizedModule T g]
    [Module.Flat A M] : Module.Flat A Mₜ := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N
  have hM := Module.Flat.iff_lTensor_injectiveₛ.1 ‹Module.Flat A M› N
  rw [← AlgebraTensorModule.coe_lTensor (A := B)] at hM ⊢
  rw [← IsLocalizedModule.map_lTensor B T N.subtype g]
  exact IsLocalizedModule.map_injective T _ _ _ hM

/-- IV.1.2 (i): the localization `T⁻¹M` of an `A`-flat `B`-module is `A`-flat. -/
theorem flat_localizedModule (T : Submonoid B) [Module.Flat A M] :
    Module.Flat A (LocalizedModule T M) :=
  flat_of_isLocalizedModule T (LocalizedModule.mkLinearMap T M)

/-- IV.1.2 (i), second part: for a module over a localization `S⁻¹A`, flatness over `S⁻¹A`
and over `A` agree. -/
theorem flat_iff_flat_of_isLocalization (S : Submonoid A) (Aₛ : Type*) [CommRing Aₛ]
    [Algebra A Aₛ] [IsLocalization S Aₛ] {N : Type*} [AddCommGroup N] [Module A N] [Module Aₛ N]
    [IsScalarTower A Aₛ N] : Module.Flat Aₛ N ↔ Module.Flat A N :=
  Module.flat_iff_of_isLocalization Aₛ S N

/-- IV.1.2 (ii): a `B`-module `M` is `A`-flat as soon as its localizations at all maximal
ideals of `B` are. -/
theorem flat_of_flat_localizedModule_maximal
    (h : ∀ (n : Ideal B) [n.IsMaximal], Module.Flat A (LocalizedModule n.primeCompl M)) :
    Module.Flat A M :=
  Module.flat_of_isLocalized_maximal B M (fun n _ ↦ LocalizedModule n.primeCompl M)
    (fun n _ ↦ LocalizedModule.mkLinearMap n.primeCompl M) h

end Localization

section Torsion

variable {M : Type*} [AddCommGroup M] [Module A M]

/-- IV.1.3 (i): an element of `A` which is not a zero divisor is not a zero divisor on a flat
module. -/
theorem isSMulRegular_of_flat [Module.Flat A M] {x : A} (hx : x ∈ nonZeroDivisors A) :
    IsSMulRegular M x :=
  Module.Flat.isSMulRegular_of_nonZeroDivisors hx

/-- IV.1.3 (i): a flat module over an integral domain is torsion-free. -/
theorem torsion_eq_bot_of_flat [Module.Flat A M] : Submodule.torsion A M = ⊥ :=
  Module.Flat.torsion_eq_bot

/-- IV.1.3 (ii): over an integral domain whose localizations at maximal ideals are principal
(for instance a Dedekind domain), a module is flat if and only if it is torsion-free. -/
theorem flat_iff_torsion_eq_bot [IsDomain A]
    (h : ∀ (m : Ideal A) [m.IsMaximal], IsPrincipalIdealRing (Localization m.primeCompl)) :
    Module.Flat A M ↔ Submodule.torsion A M = ⊥ :=
  Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal fun m _ ↦
    have := h m
    inferInstance

end Torsion

end SGA.SGA1.ExposeIV
