/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.FlatResidueExtension
import SGA.Foundations.CommAlg.FlatResidueExtensionCompletion

/-!
# Realizing residue field extensions by flat local extensions: the framework

EGA 0_III 10.3.1 is proved by realizing the residue field extension `k ⊆ K` step by step
(transcendental, separable algebraic, purely inseparable). This file sets up the bookkeeping.

Fix a field `K`. For a local ring `A` and a ring map `φ : ResidueField A →+* K`, a subfield
`E ⊆ K` is *realized* over `(A, φ)` (`IsLocalRing.Realizes A φ E`) if there is a local
`A`-algebra `C`, flat over `A`, with `𝔪_A C = 𝔪_C`, and a ring map
`ι : ResidueField C →+* K` extending `φ` with image `E`.

* `IsLocalRing.realizes_self`: the image of `φ` is realized by `A` itself.
* `IsLocalRing.Realizes.trans`: realizations compose.
* `IsLocalRing.exists_of_realizes_top`: if `K` itself is realized over `(A, k → K)`, with `A`
  noetherian, then the conclusion of `IsLocalRing.FlatResidueExtensionStatement` holds for
  `A` and `K` (the completion step, `SGA.Foundations.CommAlg.FlatResidueExtensionCompletion`).
-/

universe u

open IsLocalRing

namespace IsLocalRing

variable {K : Type u} [Field K]

/-- The subfield `E ⊆ K` is realized over the local ring `A`, relative to
`φ : ResidueField A →+* K`: there is a local `A`-algebra `C`, flat over `A`, with `𝔪_A C = 𝔪_C`,
and a ring map `ι : ResidueField C →+* K` with `ι (c̄) = φ (ā)` for `c` the image of `a ∈ A`, whose
image is `E`. -/
def Realizes (A : Type u) [CommRing A] [IsLocalRing A] (φ : ResidueField A →+* K)
    (E : Subfield K) : Prop :=
  ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : Algebra A C),
    Module.Flat A C ∧ (maximalIdeal A).map (algebraMap A C) = maximalIdeal C ∧
      ∃ ι : ResidueField C →+* K,
        (∀ a : A, ι (residue C (algebraMap A C a)) = φ (residue A a)) ∧ ι.fieldRange = E

/-- The image of `φ` is realized by `A` itself. -/
lemma realizes_self (A : Type u) [CommRing A] [IsLocalRing A] (φ : ResidueField A →+* K) :
    Realizes A φ φ.fieldRange :=
  ⟨A, inferInstance, inferInstance, Algebra.id A, inferInstance,
    by rw [Algebra.algebraMap_self, Ideal.map_id], φ, fun _ ↦ rfl, rfl⟩

/-- Realizations compose: if `E` is realized over `(A, φ)`, and `E'` is realized over every
`(C, ι)` with image `E`, then `E'` is realized over `(A, φ)`. -/
theorem Realizes.trans {A : Type u} [CommRing A] [IsLocalRing A] {φ : ResidueField A →+* K}
    {E E' : Subfield K} (h : Realizes A φ E)
    (h' : ∀ (C : Type u) [CommRing C] [IsLocalRing C] (ι : ResidueField C →+* K),
      ι.fieldRange = E → Realizes C ι E') :
    Realizes A φ E' := by
  obtain ⟨C, _, _, _, hflat, hm, ι, hι, hrange⟩ := h
  obtain ⟨D, _, _, _, hflat', hm', ι', hι', hrange'⟩ := h' C ι hrange
  let _ : Algebra A D := ((algebraMap C D).comp (algebraMap A C)).toAlgebra
  have : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨D, inferInstance, inferInstance, inferInstance, Module.Flat.trans A C D, ?_, ι',
    fun a ↦ ?_, hrange'⟩
  · rw [IsScalarTower.algebraMap_eq A C D, ← Ideal.map_map, hm, hm']
  · rw [IsScalarTower.algebraMap_apply A C D, hι', hι]

/-- If `K` itself is realized over the noetherian local ring `A`, relative to the structure map
`k → K`, then `A` has a flat local extension `B` which is a complete noetherian local ring with
`𝔪_A B = 𝔪_B` and residue field `K` over `k` (the conclusion of
`IsLocalRing.FlatResidueExtensionStatement`). -/
theorem exists_of_realizes_top (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra (ResidueField A) K] (h : Realizes A (algebraMap (ResidueField A) K) ⊤) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B)
      (_ : IsAdicComplete (maximalIdeal B) B) (_ : Algebra A B) (_ : IsLocalHom (algebraMap A B)),
      Module.Flat A B ∧ (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ∧
        Nonempty (ResidueField B ≃ₐ[ResidueField A] K) := by
  obtain ⟨C, _, _, _, hflat, hm, ι, hι, hrange⟩ := h
  have hfg := maximalIdeal_fg_of_map_maximalIdeal_eq hm
  let _ := AdicCompletion.isLocalRing_of_fg hfg
  have := isLocalHom_of_map_maximalIdeal_eq hm
  have := AdicCompletion.algebraMap_isLocalHom_of_fg hfg
  have hloc : IsLocalHom (algebraMap A (AdicCompletion (maximalIdeal C) C)) :=
    inferInstanceAs (IsLocalHom ((algebraMap C _).comp (algebraMap A C)))
  have hbij : Function.Bijective ι :=
    ⟨ι.injective, fun y ↦ by
      have : y ∈ ι.fieldRange := hrange ▸ Subfield.mem_top y
      exact this⟩
  let eC : ResidueField C ≃+* K := RingEquiv.ofBijective ι hbij
  let e : ResidueField (AdicCompletion (maximalIdeal C) C) ≃+* K :=
    (residueFieldAdicCompletionEquiv hm).symm.trans eC
  have he : ∀ x : ResidueField A,
      e (algebraMap (ResidueField A) (ResidueField (AdicCompletion (maximalIdeal C) C)) x) =
        algebraMap (ResidueField A) K x := by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    rw [ResidueField.algebraMap_residue, IsScalarTower.algebraMap_apply A C, ← hι a]
    simp only [e, eC, RingEquiv.trans_apply, RingEquiv.ofBijective_apply]
    congr 1
    rw [RingEquiv.symm_apply_eq]
    rfl
  refine ⟨AdicCompletion (maximalIdeal C) C, inferInstance, inferInstance,
    isNoetherianRing_adicCompletion_of_map_maximalIdeal_eq hm,
    AdicCompletion.isAdicComplete_of_fg hfg, inferInstance, hloc, flat_adicCompletion_of_flat hm,
    map_maximalIdeal_adicCompletion hm, ⟨AlgEquiv.ofRingEquiv (f := e) he⟩⟩

end IsLocalRing
