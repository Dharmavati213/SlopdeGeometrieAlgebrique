/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.Completion

/-!
# SGA 1, Exposé III, 2.1 for rings which need not be complete

Theorem III.2.1 is stated for local homomorphisms `A → B` of noetherian local rings (with finite
residue extension), which need not be complete; `formallySmooth_tfae'` proves it for complete
rings. Here we remove the completeness assumption for the implication (iv) ⇒ (iii) used in the
proof of III.3.1, (iii) ⇒ (i):

* `LocalArtinianLiftingProperty.completion`: the lifting property (iv) for local artinian rings
  finite over `A` passes from `A → B` to the completions `Â → B̂` (a local artinian ring finite over
  `Â` is killed by a power of `𝔪̂`, hence is finite over `A`, and maps from `B̂` into it are the
  same as maps from `B`);
* `adicFormallySmooth_iff_localArtinianLiftingProperty`: III.2.1, (iii) ⇔ (iv);
* `AdicFormallySmooth.of_isLocalization`: the lifting property (iii) over a localization `R_M`
  of `R` implies it over `R`, since `M` becomes invertible in every test ring.
-/

universe u

open IsLocalRing

namespace SGA.SGA1.ExposeIII

/-- The maximal ideal of a local artinian ring is nilpotent. -/
lemma exists_pow_maximalIdeal_eq_bot (C : Type*) [CommRing C] [IsLocalRing C]
    [IsArtinianRing C] : ∃ N : ℕ, maximalIdeal C ^ N = ⊥ := by
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
  exact ⟨N, hN⟩

/-- A local homomorphism into a local ring whose maximal ideal has vanishing `N`-th power kills
the `N`-th power of the maximal ideal. -/
lemma pow_maximalIdeal_le_ker {R C F : Type*} [CommRing R] [IsLocalRing R] [CommRing C]
    [IsLocalRing C] [FunLike F R C] [RingHomClass F R C] (g : F) [IsLocalHom g] {N : ℕ}
    (hN : maximalIdeal C ^ N = ⊥) : maximalIdeal R ^ N ≤ RingHom.ker g := by
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, eq_bot_iff, ← hN]
  exact Ideal.pow_right_mono
    (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ Ideal.mem_comap.mpr <| (mem_maximalIdeal _).mpr
      fun hu ↦ (mem_maximalIdeal _).mp ha (isUnit_of_map_unit g a hu)) N

section Completion

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

local notation "Â" => AdicCompletion (maximalIdeal A) A

variable {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]

local notation "B̂" => AdicCompletion (maximalIdeal B) B

attribute [local instance] completionAlgebra

/-- III.2.1 (iv) passes to the completions: if every local `A`-homomorphism `B → C ⧸ J`, with
`C` local artinian finite over `A`, lifts to `C`, then the same holds for `Â → B̂`. -/
theorem LocalArtinianLiftingProperty.completion (h : LocalArtinianLiftingProperty A B) :
    LocalArtinianLiftingProperty Â B̂ := by
  intro C _ _ _ _ _ J hJ f hf
  let : Algebra A C := ((algebraMap Â C).comp (algebraMap A Â)).toAlgebra
  have : IsScalarTower A Â C := .of_algebraMap_eq' rfl
  obtain ⟨N, hN⟩ := exists_pow_maximalIdeal_eq_bot C
  -- `Â → C` is local, hence kills `𝔪̂ᴺ`
  have : IsLocalHom (algebraMap Â C) := ⟨fun a ha ↦ by
    have h1 : IsUnit (f (algebraMap Â B̂ a)) := by
      rw [f.commutes, IsScalarTower.algebraMap_apply Â C (C ⧸ J)]
      exact ha.map _
    exact isUnit_of_map_unit (algebraMap Â B̂) a (isUnit_of_map_unit f _ h1)⟩
  have hÂN : maximalIdeal Â ^ N ≤ RingHom.ker (algebraMap Â C) :=
    pow_maximalIdeal_le_ker _ hN
  -- `C` is finite over `A`
  have hsmul (â : Â) (c : C) : ∃ a : A, â • c = a • c := by
    obtain ⟨a, ha⟩ := surjective_algebraMap_completion A N (Ideal.Quotient.mk _ â)
    rw [RingHom.comp_apply, Ideal.Quotient.eq] at ha
    have hmem : â - algebraMap A Â a ∈ maximalIdeal Â ^ N := by
      rw [← neg_sub]; exact neg_mem ha
    refine ⟨a, ?_⟩
    rw [← algebraMap_smul Â a c, ← sub_eq_zero, ← sub_smul, Algebra.smul_def,
      RingHom.mem_ker.mp (hÂN hmem), zero_mul]
  have : Module.Finite A C := by
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Â) (M := C)
    suffices H : ∀ c ∈ Submodule.span Â (s : Set C), c ∈ Submodule.span A (s : Set C) from
      ⟨⟨s, eq_top_iff.mpr fun c _ ↦ H c (hs ▸ trivial)⟩⟩
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul â x _ hx =>
      obtain ⟨a, ha⟩ := hsmul â x
      rw [ha]
      exact Submodule.smul_mem _ a hx
  -- restrict `f` to `B` and lift
  let f₀ : B →ₐ[A] C ⧸ J := (f.restrictScalars A).comp (IsScalarTower.toAlgHom A B B̂)
  have hf₀ : IsLocalHom f₀ := ⟨fun b hb ↦
    isUnit_of_map_unit (algebraMap B B̂) b (isUnit_of_map_unit f _ hb)⟩
  obtain ⟨g, hg⟩ := h J hJ f₀ hf₀
  have : IsLocalHom g := ⟨fun b hb ↦ by
    have := hb.map (Ideal.Quotient.mkₐ A J)
    rw [← AlgHom.comp_apply, hg] at this
    exact isUnit_of_map_unit f₀ b this⟩
  have hgN : maximalIdeal B ^ N ≤ RingHom.ker g := pow_maximalIdeal_le_ker g hN
  -- extend `g` to `B̂`
  let ĝ : B̂ →+* C := (Ideal.Quotient.lift (maximalIdeal B ^ N) (g : B →+* C)
    fun b hb ↦ hgN hb).comp
      (AdicCompletion.evalₐ (maximalIdeal B) N : B̂ →+* B ⧸ maximalIdeal B ^ N)
  have hĝ (b : B) : ĝ (algebraMap B B̂ b) = g b := by
    simp only [ĝ, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, AdicCompletion.evalₐ_of]
    rfl
  have hĝN : maximalIdeal B̂ ^ N ≤ RingHom.ker ĝ := by
    intro x hx
    rw [AdicCompletion.maximalIdeal_eq_map, ← SGA.SGA1.ExposeIV.ker_evalₐ_eq_pow _
      (maximalIdeal B).fg_of_isNoetherianRing N] at hx
    rw [RingHom.mem_ker, RingHom.comp_apply]
    change Ideal.Quotient.lift _ _ _ (AdicCompletion.evalₐ (maximalIdeal B) N x) = 0
    rw [RingHom.mem_ker.mp hx, map_zero]
  -- `ĝ` is `Â`-linear
  have key : ĝ.comp (algebraMap Â B̂) = algebraMap Â C := by
    refine ringHom_ext_completion A ?_ (K := N) ?_ hÂN
    · ext a
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply A Â B̂, IsScalarTower.algebraMap_apply A B B̂, hĝ,
        g.commutes, ← IsScalarTower.algebraMap_apply A Â C]
    · intro x hx
      rw [RingHom.mem_ker, RingHom.comp_apply]
      refine hĝN ?_
      have hle : (maximalIdeal Â ^ N).map (algebraMap Â B̂) ≤ maximalIdeal B̂ ^ N := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (map_maximalIdeal_completion_le A B) N
      exact hle (Ideal.mem_map_of_mem _ hx)
  -- `ĝ` lifts `f`
  have hfN : maximalIdeal B̂ ^ N ≤ RingHom.ker (f : B̂ →+* C ⧸ J) := by
    have hfm : (maximalIdeal B̂).map (f : B̂ →+* C ⧸ J) ≤
        (maximalIdeal C).map (Ideal.Quotient.mk J) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (f x)
      rw [Ideal.mem_comap, RingHom.coe_coe, ← hc]
      refine Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr fun hu ↦ ?_)
      exact (mem_maximalIdeal _).mp hx (isUnit_of_map_unit f x (hc ▸ hu.map _))
    rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, eq_bot_iff]
    refine (Ideal.pow_right_mono hfm N).trans ?_
    rw [← Ideal.map_pow, hN, Ideal.map_bot]
  have key₂ : (Ideal.Quotient.mk J).comp ĝ = (f : B̂ →+* C ⧸ J) := by
    refine ringHom_ext_completion B ?_ (K := N) ?_ hfN
    · ext b
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [hĝ]
      exact congr($hg b)
    · intro x hx
      rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.mem_ker.mp (hĝN hx), map_zero]
  exact ⟨{ ĝ with commutes' := fun x ↦ congr($key x) }, AlgHom.ext fun x ↦ congr($key₂ x)⟩

/-- III.2.1, (iv) ⇒ (iii), for noetherian local rings which need not be complete: if `B` has the
lifting property for local artinian rings finite over `A`, then `B` is formally smooth over `A`
for the `𝔪_B`-adic topology. As in SGA the proof goes through the completions (III.2.1 for
`Â → B̂`, `formallySmooth_tfae'`). -/
theorem adicFormallySmooth_of_localArtinianLiftingProperty [Module.Finite A (ResidueField B)]
    (h : LocalArtinianLiftingProperty A B) : AdicFormallySmooth A (maximalIdeal B) := by
  have := finite_residueField_completion A B
  exact (formallySmoothLocal_completion_iff A B).mp h.completion.sqZero.formallySmoothLocal

/-- III.2.1, (iii) ⇔ (iv), for local homomorphisms of noetherian local rings (not necessarily
complete) with finite residue extension. -/
theorem adicFormallySmooth_iff_localArtinianLiftingProperty [Module.Finite A (ResidueField B)] :
    AdicFormallySmooth A (maximalIdeal B) ↔ LocalArtinianLiftingProperty A B :=
  ⟨fun h ↦ h.completeLiftingProperty.localArtinianLiftingProperty,
    adicFormallySmooth_of_localArtinianLiftingProperty⟩

end Completion

/-- The adic lifting property over a localization `R_M` of `R` implies it over `R`: the elements
of `M` become units in `C ⧸ J`, hence in `C` since `J` is nilpotent, so every test `R`-algebra `C`
is an `R_M`-algebra. -/
theorem AdicFormallySmooth.of_isLocalization {R Rₘ B : Type u} [CommRing R] [CommRing Rₘ]
    [CommRing B] [Algebra R Rₘ] [Algebra Rₘ B] [Algebra R B] [IsScalarTower R Rₘ B]
    (M : Submonoid R) [IsLocalization M Rₘ] {I : Ideal B} (h : AdicFormallySmooth Rₘ I) :
    AdicFormallySmooth R I := by
  intro C _ _ J hJ f hf
  have hunit (m : M) : IsUnit (algebraMap R C m) := by
    refine AdicFormallySmooth.isUnit_of_isUnit_mk hJ ?_
    rw [Ideal.Quotient.mk_algebraMap, ← f.commutes, IsScalarTower.algebraMap_apply R Rₘ B]
    exact ((IsLocalization.map_units Rₘ m).map (algebraMap Rₘ B)).map f
  let : Algebra Rₘ C := (IsLocalization.lift hunit).toAlgebra
  have : IsScalarTower R Rₘ C := .of_algebraMap_eq fun r ↦ (IsLocalization.lift_eq hunit r).symm
  have hf' : (f : B →+* C ⧸ J).comp (algebraMap Rₘ B) = algebraMap Rₘ (C ⧸ J) := by
    refine IsLocalization.ringHom_ext M (RingHom.ext fun r ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [← IsScalarTower.algebraMap_apply, f.commutes, ← IsScalarTower.algebraMap_apply]
  obtain ⟨g, hg⟩ := h J hJ { (f : B →+* C ⧸ J) with commutes' := fun x ↦ congr($hf' x) } hf
  exact ⟨g.restrictScalars R, AlgHom.ext fun x ↦ congr($hg x)⟩

end SGA.SGA1.ExposeIII
