/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.FiniteProjectiveDimension
import Mathlib.RingTheory.Regular.Free
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Projective dimension after reduction by a regular element

Reduction of a short exact sequence modulo an element remains short exact
when that element is regular on the last module. The maps are linear over
the actual quotient ring. Applying this to finite free covers proves that
reduction by an element regular on both the ring and a finite module does
not increase projective dimension, now measured over the quotient ring.
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing
open scoped Pointwise

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The original reduction map, with its quotient-ring linearity. -/
def regularElementQuotientMap (x : R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    QuotSMulTop x M →ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x N :=
  (QuotSMulTop.map x f.hom).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

@[simp]
theorem regularElementQuotientMap_mk (x : R) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (m : M) :
    regularElementQuotientMap x f (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (f m) := rfl

/-- Regularity on the last term preserves the injection under reduction. -/
theorem regularElementQuotientMap_injective (x : R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hx : IsSMulRegular S.X₃ x) :
    Function.Injective (regularElementQuotientMap x S.f) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro q hq
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (x • (⊤ : Submodule R S.X₁)) q
  have hm : S.f m ∈ x • (⊤ : Submodule R S.X₂) :=
    (Submodule.Quotient.mk_eq_zero _).mp hq
  obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
  have hgy : S.g y = 0 := hx.right_eq_zero_of_smul (by
    rw [← S.g.hom.map_smul, hy]
    exact S.moduleCat_zero_apply m)
  obtain ⟨z, hz⟩ := (S.moduleCat_exact_iff.mp hS.exact) y hgy
  have hmz : m = x • z := hS.moduleCat_injective_f (by
    rw [S.f.hom.map_smul, hz, hy])
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hmz ▸
    Submodule.smul_mem_pointwise_smul z x ⊤ trivial)

/-- Reduction of an actual short complex, over the actual quotient ring. -/
def regularElementQuotientShortComplex (x : R)
    (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} (R ⧸ Ideal.span {x})) :=
  ShortComplex.moduleCatMk (regularElementQuotientMap x S.f)
    (regularElementQuotientMap x S.g) (by
      apply LinearMap.ext
      intro q
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (x • (⊤ : Submodule R S.X₁)) q
      change Submodule.Quotient.mk (S.g (S.f m)) = 0
      rw [S.moduleCat_zero_apply, Submodule.Quotient.mk_zero])

/-- The reduced sequence is short exact if the last term is regular. -/
theorem regularElementQuotientShortComplex_shortExact (x : R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hx : IsSMulRegular S.X₃ x) :
    (regularElementQuotientShortComplex x S).ShortExact := by
  have hinj := regularElementQuotientMap_injective x S hS hx
  have hsurj := QuotSMulTop.map_surjective x hS.moduleCat_surjective_g
  have : Mono (regularElementQuotientShortComplex x S).f :=
    (ModuleCat.mono_iff_injective _).mpr hinj
  have : Epi (regularElementQuotientShortComplex x S).g :=
    (ModuleCat.epi_iff_surjective _).mpr hsurj
  refine ⟨?_⟩
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  exact QuotSMulTop.map_exact x
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
    hS.moduleCat_surjective_g

variable [IsNoetherianRing R] [IsLocalRing R]

/-- A finite module's projective-dimension bound survives reduction by an
element regular on the ring and the module. The result is over `R/(x)`,
not the original ring. No regular-local hypothesis is used. -/
theorem quotient_hasProjectiveDimensionLE_of_regularElement (n : ℕ)
    (M : ModuleCat.{u} R) [Module.Finite R M]
    [HasProjectiveDimensionLE M n] (x : R) (hxR : IsSMulRegular R x)
    (hxM : IsSMulRegular M x) :
    HasProjectiveDimensionLE
      (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) n := by
  induction n generalizing M with
  | zero =>
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr inferInstance
    have : Module.Projective R M := inferInstance
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp inferInstance
  | succ n ih =>
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    let S := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have hK : HasProjectiveDimensionLE S.X₁ n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
    have hxP : IsSMulRegular P x := Module.Flat.isSMulRegular_of_isRegular
      ((Commute.isRegular_iff (fun y ↦ mul_comm x y)).mpr hxR)
    have hxK : IsSMulRegular S.X₁ x := hxP.submodule (LinearMap.ker f) x
    have hQK := ih S.X₁ hxK
    have hQP : HasProjectiveDimensionLT
        (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x P)) (n + 1 + 1) := inferInstance
    exact (regularElementQuotientShortComplex_shortExact x S hS hxM).hasProjectiveDimensionLT_X₃
      (n + 1) hQK hQP

end SGA.SGA2.ExposeV
