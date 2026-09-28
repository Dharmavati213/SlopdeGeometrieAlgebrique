/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.LocalInjectiveEnvelopes

/-!
# Actual Hom cogeneration by a supported dualizing module

A supported dualizing module over a noetherian local ring cogenerates not
only supported modules, but all modules. For a nonzero element, its actual
cyclic submodule has a residue-field quotient that detects its generator.
The residue-field embedding into the coefficient then extends by injectivity.

Consequently the original evaluation into double Hom is injective and the
original contravariant Hom reflects isomorphisms, with no finiteness or
support hypotheses on its source modules. The actual double-Hom triangle
then shows that reflexivity of a dual implies reflexivity of its source.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The triangle identity for the original evaluations, with an arbitrary
coefficient module and without reflexivity assumptions. -/
theorem moduleBidualEvaluation_triangle (H X : ModuleCat.{u} R) :
    moduleBidualEvaluation H ((moduleHomDual H).obj (op X)) ≫
      (moduleHomDual H).map (moduleBidualEvaluation H X).op =
        𝟙 ((moduleHomDual H).obj (op X)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

section Local

variable [IsLocalRing R]

/-- Any injective module containing the actual residue field separates
elements of every module. Only the cyclic submodule is used. -/
theorem exists_hom_apply_ne_zero_of_injective_residue (H : ModuleCat.{u} R)
    [Injective H]
    (i : ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R) ⟶ H)
    (hi : Function.Injective i.hom) (X : ModuleCat.{u} R) (x : X) (hx : x ≠ 0) :
    ∃ f : X ⟶ H, f x ≠ 0 := by
  let m := IsLocalRing.maximalIdeal R
  let a : R →ₗ[R] X := LinearMap.toSpanSingleton R X x
  let I : Ideal R := a.ker
  have hI : I ≠ ⊤ := by
    intro h
    have hz : a 1 = 0 := (LinearMap.mem_ker).mp
      (show (1 : R) ∈ I by rw [h]; trivial)
    exact hx (by simpa [a] using hz)
  let q : (R ⧸ I) →ₗ[R] R ⧸ m :=
    I.liftQ m.mkQ (by rw [Submodule.ker_mkQ]; exact IsLocalRing.le_maximalIdeal hI)
  let c : ModuleCat.of R a.range ⟶ X := ModuleCat.ofHom a.range.subtype
  have : Mono c := (ModuleCat.mono_iff_injective c).mpr a.range.subtype_injective
  let g : ModuleCat.of R a.range ⟶ H :=
    ModuleCat.ofHom (q ∘ₗ a.quotKerEquivRange.symm.toLinearMap) ≫ i
  obtain ⟨f, hf⟩ := Injective.factors g c
  refine ⟨f, ?_⟩
  have hy : a 1 ∈ a.range := ⟨1, rfl⟩
  have he := congrArg (fun k : ModuleCat.of R a.range ⟶ H ↦ k ⟨a 1, hy⟩) hf
  have heval : f x = i (m.mkQ 1) := by
    change f (a 1) = i (q (a.quotKerEquivRange.symm ⟨a 1, hy⟩)) at he
    rw [LinearMap.quotKerEquivRange_symm_apply_image] at he
    simpa only [q, Submodule.mkQ_apply, Submodule.liftQ_apply,
      a, LinearMap.toSpanSingleton_apply_one] using he
  rw [heval]
  intro hz
  have hm : m.mkQ 1 = 0 := hi (hz.trans (map_zero i.hom).symm)
  have hm1 : (1 : R) ∈ m := (Submodule.Quotient.mk_eq_zero m).mp hm
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem m hm1 isUnit_one)

variable [IsNoetherianRing R] {H : ModuleCat.{u} R}

/-- A supported dualizing module is an actual cogenerator on all modules,
including arbitrary non-finite supported modules. -/
theorem SupportedDualizingModule.exists_hom_apply_ne_zero
    (hH : SupportedDualizingModule H) (X : ModuleCat.{u} R) (x : X) (hx : x ≠ 0) :
    ∃ f : X ⟶ H, f x ≠ 0 := by
  obtain ⟨hI, i, hi⟩ := (supportedDualizingModule_iff_injective_essential_residue H).mp hH
  have := hI
  exact exists_hom_apply_ne_zero_of_injective_residue H i hi.1 X x hx

/-- The original canonical bidual evaluation is injective on every module. -/
theorem SupportedDualizingModule.moduleBidualEvaluation_injective
    (hH : SupportedDualizingModule H) (X : ModuleCat.{u} R) :
    Function.Injective (moduleBidualEvaluation H X).hom := by
  rw [← LinearMap.ker_eq_bot]
  apply bot_unique
  intro x hx
  change moduleBidualEvaluation H X x = 0 at hx
  change x = 0
  by_contra hx0
  obtain ⟨f, hf⟩ := hH.exists_hom_apply_ne_zero X x hx0
  exact hf (congrArg (fun k : (moduleHomBidual H).obj X ↦ k.hom f) hx)

/-- Categorical monicity of the original evaluation, without finiteness. -/
theorem SupportedDualizingModule.moduleBidualEvaluation_mono
    (hH : SupportedDualizingModule H) (X : ModuleCat.{u} R) :
    Mono (moduleBidualEvaluation H X) :=
  (ModuleCat.mono_iff_injective _).mpr (hH.moduleBidualEvaluation_injective X)

/-- Surjectivity of dual restriction forces injectivity of the original map. -/
theorem SupportedDualizingModule.injective_of_dual_surjective
    (hH : SupportedDualizingModule H) {X Y : ModuleCat.{u} R} (f : X ⟶ Y)
    (hf : Function.Surjective ((moduleHomDual H).map f.op).hom) :
    Function.Injective f.hom := by
  rw [← LinearMap.ker_eq_bot]
  apply bot_unique
  intro x hx
  change f x = 0 at hx
  change x = 0
  by_contra hx0
  obtain ⟨g, hg⟩ := hH.exists_hom_apply_ne_zero X x hx0
  obtain ⟨k, hk⟩ := hf g
  have he := congrArg (fun l : X ⟶ H ↦ l x) hk
  exact hg (he.symm.trans (by
    change ModuleCat.Hom.hom k (f x) = 0
    rw [hx]
    exact map_zero (ModuleCat.Hom.hom k)))

/-- Injectivity of dual restriction forces surjectivity of the original
map, detected on the actual quotient by its image. -/
theorem SupportedDualizingModule.surjective_of_dual_injective
    (hH : SupportedDualizingModule H) {X Y : ModuleCat.{u} R} (f : X ⟶ Y)
    (hf : Function.Injective ((moduleHomDual H).map f.op).hom) :
    Function.Surjective f.hom := by
  intro y
  by_contra hy
  let N := f.hom.range
  have hqy : N.mkQ y ≠ 0 := by
    intro hz
    exact hy ((Submodule.Quotient.mk_eq_zero N).mp hz)
  obtain ⟨g, hg⟩ := hH.exists_hom_apply_ne_zero (ModuleCat.of R (Y ⧸ N)) (N.mkQ y) hqy
  let k : Y ⟶ H := ModuleCat.ofHom N.mkQ ≫ g
  have hk : (moduleHomDual H).map f.op k = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change g (N.mkQ (f x)) = 0
    have hz : N.mkQ (f x) = 0 :=
      (Submodule.Quotient.mk_eq_zero N).mpr (show f x ∈ N from ⟨x, rfl⟩)
    rw [hz]
    exact map_zero g.hom
  have hk0 : k = 0 := hf (hk.trans (map_zero ((moduleHomDual H).map f.op).hom).symm)
  exact hg (congrArg (fun l : Y ⟶ H ↦ l y) hk0)

/-- The actual contravariant Hom reflects isomorphisms on all modules. -/
theorem SupportedDualizingModule.isIso_of_moduleHomDual_map
    (hH : SupportedDualizingModule H) {X Y : ModuleCat.{u} R} (f : X ⟶ Y)
    [IsIso ((moduleHomDual H).map f.op)] : IsIso f := by
  have hf := (ConcreteCategory.isIso_iff_bijective ((moduleHomDual H).map f.op)).mp
    (inferInstance : IsIso ((moduleHomDual H).map f.op))
  exact (ConcreteCategory.isIso_iff_bijective f).mpr
    ⟨hH.injective_of_dual_surjective f hf.2, hH.surjective_of_dual_injective f hf.1⟩

/-- Reflexivity of the actual dual implies reflexivity of the source.
No support hypothesis on the double dual is silently required. -/
theorem SupportedDualizingModule.moduleBidualEvaluation_isIso_of_dual
    (hH : SupportedDualizingModule H) (X : ModuleCat.{u} R)
    [IsIso (moduleBidualEvaluation H ((moduleHomDual H).obj (op X)))] :
    IsIso (moduleBidualEvaluation H X) := by
  have : IsIso ((moduleHomDual H).map (moduleBidualEvaluation H X).op) :=
    isIso_of_hom_comp_eq_id _ (moduleBidualEvaluation_triangle H X)
  exact hH.isIso_of_moduleHomDual_map (moduleBidualEvaluation H X)

end Local

end SGA.SGA2.ExposeIV
