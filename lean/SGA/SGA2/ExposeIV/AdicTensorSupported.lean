/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.AdicTensorNilpotent
import SGA.SGA2.ExposeIV.SupportedLocallyArtinian
import SGA.SGA2.ExposeIV.LocalArtinianSupport

/-!
# Tensoring arbitrary supported modules with the completed ring

The actual map `M → Â ⊗ M`, `x ↦ 1 ⊗ x`, is bijective for every module
supported on `V(J)`, with no finite generation assumption on `M`. The finite
nilpotent-stage comparison supplies surjectivity on pure tensors; flatness
of the actual completed ring supplies injectivity through cyclic submodules.
This is tensoring with the completed ring, not completing the module itself.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TensorProduct

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

omit [IsNoetherianRing R] in
private theorem cyclic_support_of_support (x : M)
    (hM : Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    Module.support R (Submodule.span R {x}) ⊆ PrimeSpectrum.zeroLocus (J : Set R) :=
  (Module.support_subset_of_injective (Submodule.span R {x}).subtype
    (Submodule.span R {x}).subtype_injective).trans hM

/-- The actual scalar-extension map is injective on arbitrary supported
modules. Only the cyclic submodule of the tested element is finite. -/
theorem adicTensorUnit_injective_of_support
    (hM : Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    Function.Injective (adicTensorUnit J M) := by
  rw [← LinearMap.ker_eq_bot]
  apply bot_unique
  intro x hx
  change adicTensorUnit J M x = 0 at hx
  let N : Submodule R M := Submodule.span R {x}
  let y : N := ⟨x, Submodule.mem_span_singleton_self x⟩
  have hu := (adicTensorUnit_bijective_of_finite_of_support J N
    (cyclic_support_of_support J M x hM)).1
  have ht := Module.Flat.lTensor_preserves_injective_linearMap
    (M := AdicCompletion J R) N.subtype N.subtype_injective
  have he : adicTensorUnit J N y = 0 := by
    apply ht
    simpa only [adicTensorUnit_apply, LinearMap.lTensor_tmul, Submodule.subtype_apply,
      map_zero] using hx
  have hy : y = 0 := hu (he.trans (map_zero (adicTensorUnit J N)).symm)
  exact congrArg Subtype.val hy

/-- Every pure tensor comes from an actual element, by applying the finite
nilpotent-stage comparison only to its original cyclic submodule. -/
theorem adicTensorUnit_surjective_of_support
    (hM : Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    Function.Surjective (adicTensorUnit J M) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a x =>
    let N : Submodule R M := Submodule.span R {x}
    let y : N := ⟨x, Submodule.mem_span_singleton_self x⟩
    obtain ⟨w, hw⟩ := (adicTensorUnit_bijective_of_finite_of_support J N
      (cyclic_support_of_support J M x hM)).2 (a ⊗ₜ[R] y)
    refine ⟨w.val, ?_⟩
    exact congrArg (N.subtype.lTensor (AdicCompletion J R)) hw
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add _ x y⟩

/-- **IV.4.5, arbitrary supported-module tensor assertion.** The original
map is bijective without finite generation of the module. -/
theorem adicTensorUnit_bijective_of_support
    (hM : Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    Function.Bijective (adicTensorUnit J M) :=
  ⟨adicTensorUnit_injective_of_support J M hM,
    adicTensorUnit_surjective_of_support J M hM⟩

/-- The canonical linear identification with actual scalar extension. -/
def supportedAdicTensorEquiv
    (hM : Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    M ≃ₗ[R] AdicCompletion J R ⊗[R] M :=
  LinearEquiv.ofBijective (adicTensorUnit J M) (adicTensorUnit_bijective_of_support J M hM)

@[simp]
theorem supportedAdicTensorEquiv_apply
    (hM : Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)) (x : M) :
    supportedAdicTensorEquiv J M hM x = 1 ⊗ₜ[R] x := rfl

omit [IsNoetherianRing R] in
/-- Naturality is equality for the original linear map and actual tensor map. -/
theorem adicTensorUnit_naturality {N : Type u} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (f.lTensor (AdicCompletion J R)).comp (adicTensorUnit J M) =
      (adicTensorUnit J N).comp f := by
  ext x
  rfl

/-- In particular the original canonical representing module, which need
not be finitely generated, is unchanged as an underlying module by scalar extension. -/
def supportedFunctorColimitAdicTensorEquiv
    (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive] :
    supportedFunctorColimit J T ≃ₗ[R]
      AdicCompletion J R ⊗[R] supportedFunctorColimit J T :=
  supportedAdicTensorEquiv J _ (supportedFunctorColimit_support J T)

/-- **SGA 2, IV.4.5.** For an arbitrary locally Artinian module over a
noetherian local ring, the source's canonical map `x ↦ x ⊗ 1` is an isomorphism.
The module itself is not assumed finite or complete. -/
def localArtinianTensorCompletionEquiv [IsLocalRing R]
    (hM : ModuleLocallyArtinian (R := R) M) :
    M ≃ₗ[R] M ⊗[R] AdicCompletion (IsLocalRing.maximalIdeal R) R :=
  (supportedAdicTensorEquiv (IsLocalRing.maximalIdeal R) M
    (support_maximalIdeal_of_moduleLocallyArtinian M hM)).trans
      (TensorProduct.comm R _ _)

@[simp]
theorem localArtinianTensorCompletionEquiv_apply [IsLocalRing R]
    (hM : ModuleLocallyArtinian (R := R) M) (x : M) :
    localArtinianTensorCompletionEquiv M hM x = x ⊗ₜ[R] 1 := rfl

end SGA.SGA2.ExposeIV
