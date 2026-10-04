/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.AdicCompletion.LocalRing
import SGA.Foundations.HenselizationNoetherian

/-!
# Completing a flat local extension with `𝔪_R C = 𝔪_C`

Let `R` be a noetherian local ring and `C` a local `R`-algebra, flat over `R`, with
`𝔪_R C = 𝔪_C`; `C` need not be noetherian. Then the `𝔪_C`-adic completion `Ĉ` of `C` is a complete
noetherian local ring, flat over `R`, with `𝔪_R Ĉ = 𝔪_Ĉ` and the same residue field as `C`
(`IsLocalRing.isNoetherianRing_adicCompletion_of_map_maximalIdeal_eq`,
`IsLocalRing.flat_adicCompletion_of_flat`, `IsLocalRing.map_maximalIdeal_adicCompletion`). That `Ĉ`
is local and complete, and has the residue field of `C`, is mathlib
(`AdicCompletion.isLocalRing_of_fg`, `AdicCompletion.isAdicComplete_of_fg`,
`AdicCompletion.residueField_map_bijective_of_fg`), since `𝔪_C = 𝔪_R C` is finitely generated.

This is the last step of EGA 0_III 10.3.1 ("gonflements", Bourbaki, *Algèbre commutative* IX,
Appendice): to get a complete noetherian flat local extension of `R` with residue field `K`, it
suffices to find a (possibly non-noetherian) local `C` flat over `R` with `𝔪_R C = 𝔪_C` and
residue field `K`.

The proof is the one of `IsLocalRing.StrictHenselization.isNoetherianRing`
(`SGA.Foundations.HenselizationNoetherian`, Stacks 06LJ), where `C` is a strict henselization:
`Ĉ` is complete with finitely generated maximal ideal and residue field a field, hence noetherian
(Stacks 05GH, `Ideal.isNoetherianRing_of_isAdicComplete`), and `Ĉ / 𝔪ⁿĈ = C / 𝔪ⁿC` is flat over
`R / 𝔪ⁿ`, so `Ĉ` is flat over `R` by the local flatness criterion
(`Module.Flat.of_forall_flat_quotient_pow`, EGA 0_III 10.2.2).
-/

universe u

open IsLocalRing TensorProduct

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {C : Type u} [CommRing C] [IsLocalRing C] [Algebra R C]

omit [IsNoetherianRing R] in
lemma isLocalHom_of_map_maximalIdeal_eq
    (hm : (maximalIdeal R).map (algebraMap R C) = maximalIdeal C) :
    IsLocalHom (algebraMap R C) :=
  ((local_hom_TFAE (algebraMap R C)).out 3 1).mp hm.le

lemma maximalIdeal_fg_of_map_maximalIdeal_eq
    (hm : (maximalIdeal R).map (algebraMap R C) = maximalIdeal C) : (maximalIdeal C).FG := by
  rw [← hm]
  exact Ideal.FG.map (IsNoetherian.noetherian (maximalIdeal R)) _

/-- The completion `Ĉ` of a local `R`-algebra `C` with `𝔪_R C = 𝔪_C` (`R` noetherian) is a
noetherian ring. -/
theorem isNoetherianRing_adicCompletion_of_map_maximalIdeal_eq
    (hm : (maximalIdeal R).map (algebraMap R C) = maximalIdeal C) :
    IsNoetherianRing (AdicCompletion (maximalIdeal C) C) := by
  have hfg := maximalIdeal_fg_of_map_maximalIdeal_eq hm
  let Ĉ := AdicCompletion (maximalIdeal C) C
  have := AdicCompletion.isLocalRing_of_fg hfg
  have := AdicCompletion.isAdicComplete_of_fg hfg
  have hfg' : (maximalIdeal Ĉ).FG := by
    rw [AdicCompletion.maximalIdeal_eq_map_of_fg hfg]
    exact Ideal.FG.map hfg _
  have : IsNoetherianRing (Ĉ ⧸ maximalIdeal Ĉ) :=
    inferInstanceAs (IsNoetherianRing (ResidueField Ĉ))
  exact Ideal.isNoetherianRing_of_isAdicComplete _ hfg'

/-- The completion `Ĉ` of a local `R`-algebra `C`, flat over the noetherian local ring `R`, with
`𝔪_R C = 𝔪_C`, is flat over `R` (local flatness criterion). -/
theorem flat_adicCompletion_of_flat [Module.Flat R C]
    (hm : (maximalIdeal R).map (algebraMap R C) = maximalIdeal C) :
    Module.Flat R (AdicCompletion (maximalIdeal C) C) := by
  have hfg := maximalIdeal_fg_of_map_maximalIdeal_eq hm
  have := isLocalHom_of_map_maximalIdeal_eq hm
  let Ĉ := AdicCompletion (maximalIdeal C) C
  have := AdicCompletion.isLocalRing_of_fg hfg
  have := AdicCompletion.algebraMap_isLocalHom_of_fg hfg
  have := isNoetherianRing_adicCompletion_of_map_maximalIdeal_eq hm
  refine Module.Flat.of_forall_flat_quotient_pow (B := Ĉ) (maximalIdeal R) ?_ fun n ↦ ?_
  · have : IsLocalHom (algebraMap R Ĉ) :=
      inferInstanceAs (IsLocalHom ((algebraMap C Ĉ).comp (algebraMap R C)))
    have h : (maximalIdeal R).map (algebraMap R Ĉ) ≤ maximalIdeal Ĉ :=
      ((local_hom_TFAE (algebraMap R Ĉ)).out 1 3).mp this
    exact h.trans (maximalIdeal_le_jacobson _)
  · set q : Ideal R := maximalIdeal R ^ n
    have hq : q.map (algebraMap R C) = maximalIdeal C ^ n := by
      rw [Ideal.map_pow, hm]
    let ι : C →ₗ[R] Ĉ := (IsScalarTower.toAlgHom R C Ĉ).toLinearMap
    have hresĈ : (maximalIdeal C ^ n • (⊤ : Submodule C Ĉ)).restrictScalars R =
        q • (⊤ : Submodule R Ĉ) := by
      rw [← hq, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
    have hresC : (maximalIdeal C ^ n • (⊤ : Submodule C C)).restrictScalars R =
        q • (⊤ : Submodule R C) := by
      rw [← hq, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
    have hker (y : Ĉ) : y ∈ q • (⊤ : Submodule R Ĉ) ↔
        AdicCompletion.eval (maximalIdeal C) C n y = 0 := by
      rw [← hresĈ, Submodule.restrictScalars_mem, AdicCompletion.pow_smul_top_eq_ker_eval hfg,
        LinearMap.mem_ker]
    have hmemC (c : C) : c ∈ q • (⊤ : Submodule R C) ↔
        c ∈ maximalIdeal C ^ n • (⊤ : Submodule C C) := by
      rw [← hresC, Submodule.restrictScalars_mem]
    have hle : q • (⊤ : Submodule R C) ≤ (q • (⊤ : Submodule R Ĉ)).comap ι :=
      Submodule.smul_top_le_comap_smul_top q ι
    let μ := Submodule.mapQ _ _ ι hle
    have hμ : Function.Bijective μ := by
      constructor
      · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro z hz
        obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, hker] at hz
        rw [Submodule.Quotient.mk_eq_zero, hmemC]
        change AdicCompletion.eval _ C n (AdicCompletion.of _ C c) = 0 at hz
        rw [AdicCompletion.eval_of, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] at hz
        exact hz
      · intro z
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
          (AdicCompletion.eval (maximalIdeal C) C n y)
        refine ⟨Submodule.Quotient.mk c, ?_⟩
        rw [Submodule.mapQ_apply, Submodule.Quotient.eq, hker, map_sub]
        change AdicCompletion.eval _ C n (AdicCompletion.of _ C c) - _ = 0
        rw [AdicCompletion.eval_of, Submodule.mkQ_apply, hc, sub_self]
    let φ : (R ⧸ q) ⊗[R] C →ₗ[R ⧸ q] (R ⧸ q) ⊗[R] Ĉ :=
      AlgebraTensorModule.lTensor (R ⧸ q) (R ⧸ q) ι
    have hφ : Function.Bijective φ := by
      have hcomm : ⇑(quotTensorEquivQuotSMul Ĉ q) ∘ φ = μ ∘ (quotTensorEquivQuotSMul C q) := by
        funext z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul r c =>
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
          simp [φ, μ, ι]
        | add x y hx hy =>
          simp only [Function.comp_apply, map_add] at hx hy ⊢
          rw [hx, hy]
      have : Function.Bijective (⇑(quotTensorEquivQuotSMul Ĉ q) ∘ φ) := by
        rw [hcomm]
        exact hμ.comp (quotTensorEquivQuotSMul C q).bijective
      exact (Function.Bijective.of_comp_iff' (quotTensorEquivQuotSMul Ĉ q).bijective _).mp this
    exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective φ hφ).symm

/-- `𝔪_R Ĉ = 𝔪_Ĉ` for the completion `Ĉ` of a local `R`-algebra `C` with `𝔪_R C = 𝔪_C` (`R`
noetherian local). (That `Ĉ` is complete is mathlib's `AdicCompletion.isAdicComplete_of_fg`.) -/
theorem map_maximalIdeal_adicCompletion
    (hm : (maximalIdeal R).map (algebraMap R C) = maximalIdeal C) :
    letI := AdicCompletion.isLocalRing_of_fg (maximalIdeal_fg_of_map_maximalIdeal_eq hm)
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal C) C)) =
      maximalIdeal (AdicCompletion (maximalIdeal C) C) := by
  have hfg := maximalIdeal_fg_of_map_maximalIdeal_eq hm
  let := AdicCompletion.isLocalRing_of_fg hfg
  rw [AdicCompletion.maximalIdeal_eq_map_of_fg hfg, ← hm, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- The residue field of the completion `Ĉ` is that of `C`, as rings (a wrapper around mathlib's
`AdicCompletion.residueField_map_bijective_of_fg`). -/
noncomputable def residueFieldAdicCompletionEquiv
    (hm : (maximalIdeal R).map (algebraMap R C) = maximalIdeal C) :
    letI := AdicCompletion.isLocalRing_of_fg (maximalIdeal_fg_of_map_maximalIdeal_eq hm)
    ResidueField C ≃+* ResidueField (AdicCompletion (maximalIdeal C) C) :=
  letI := AdicCompletion.isLocalRing_of_fg (maximalIdeal_fg_of_map_maximalIdeal_eq hm)
  have := AdicCompletion.algebraMap_isLocalHom_of_fg
    (maximalIdeal_fg_of_map_maximalIdeal_eq hm)
  RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective_of_fg
    (maximalIdeal_fg_of_map_maximalIdeal_eq hm))

end IsLocalRing
