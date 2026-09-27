/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import SGA.SGA1.ExposeII.Generalities

/-!
# SGA 1, Exposé II, §4 (4.1–4.8): differential properties of smooth morphisms

For a tower `R → A → B` (SGA: `S`, `Y`, `X`, affine case) there is the exact sequence (4.2 bis)
`B ⊗_A Ω¹_{A/R} → Ω¹_{B/R} → Ω¹_{B/A} → 0`; its first map is mathlib's
`KaehlerDifferential.mapBaseChange R A B`. This file proves, in the affine setting:

* II.4.1: unramified gives a surjective first map, étale a bijective one, and conversely;
* II.4.2, II.4.3, II.4.4: if `B` is (formally) smooth over `A`, the first map is a split
  injection and `Ω¹_{B/A}` is projective, of rank the relative dimension;
* II.4.5: the differential criterion of smoothness of `A → B` for `A` smooth over `R`,
  globally (split injectivity) and at a point (injectivity on residue fields);
* II.4.6: a morphism of smooth `R`-algebras is étale iff it induces an isomorphism on `Ω¹`;
* II.4.7: the same criterion stated with the tangent map;
* II.4.8: `g : R[t₁,…,tₙ] → B` with `B` smooth is étale iff the `dgᵢ` form a basis of `Ω¹_{B/R}`.

The statements "at `x`" of SGA are the statements for the local ring `B = 𝒪_x`, which is
essentially of finite presentation; the global statements are about algebras.
-/

universe u

open Algebra KaehlerDifferential TensorProduct

namespace SGA.SGA1.ExposeII

variable (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
  [Algebra R B] [IsScalarTower R A B]

/-- II, formula (4.2 bis): the sequence `B ⊗_A Ω¹_{A/R} → Ω¹_{B/R} → Ω¹_{B/A} → 0` is exact
(mathlib). -/
theorem exact_mapBaseChange_map_and_surjective :
    Function.Exact (mapBaseChange R A B) (map R A B B) ∧ Function.Surjective (map R A B B) :=
  ⟨exact_mapBaseChange_map R A B, map_surjective R A B⟩

/-- II.4.1: if `B` is unramified over `A`, then `B ⊗_A Ω¹_{A/R} → Ω¹_{B/R}` is surjective. -/
theorem mapBaseChange_surjective [FormallyUnramified A B] :
    Function.Surjective (mapBaseChange R A B) := fun x ↦
  (exact_mapBaseChange_map R A B x).mp (Subsingleton.elim _ _)

/-- II.4.1: if `B` is étale over `A`, then `B ⊗_A Ω¹_{A/R} → Ω¹_{B/R}` is an isomorphism. -/
theorem mapBaseChange_bijective [FormallyEtale A B] :
    Function.Bijective (mapBaseChange R A B) :=
  (tensorKaehlerEquivOfFormallyEtale R A B).bijective

/-- II.4.1, converse in the unramified case: if `B ⊗_A Ω¹_{A/R} → Ω¹_{B/R}` is surjective,
then `B` is formally unramified over `A` (no finiteness is needed for this). -/
theorem formallyUnramified_of_mapBaseChange_surjective
    (h : Function.Surjective (mapBaseChange R A B)) : FormallyUnramified A B := by
  rw [formallyUnramified_iff]
  refine subsingleton_of_forall_eq 0 fun ω ↦ ?_
  obtain ⟨ω, rfl⟩ := map_surjective R A B ω
  obtain ⟨ω, rfl⟩ := h ω
  exact (exact_mapBaseChange_map R A B).apply_apply_eq_zero ω

/-- II.4.3 (i) (and II.4.2 for polynomial rings): if `B` is formally smooth over `A`, then
`B ⊗_A Ω¹_{A/R} → Ω¹_{B/R}` is injective. -/
theorem mapBaseChange_injective [FormallySmooth A B] :
    Function.Injective (mapBaseChange R A B) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (H1Cotangent.exact_δ_mapBaseChange R A B x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

/-- II.4.2: for `B = A[t₁,…,tₙ]` the sequence `0 → B ⊗_A Ω¹_{A/R} → Ω¹_{B/R} → Ω¹_{B/A} → 0` is
exact, and `Ω¹_{B/A}` is free on the `dtᵢ` (`KaehlerDifferential.mvPolynomialBasis`). -/
theorem mapBaseChange_injective_mvPolynomial (σ : Type u) :
    Function.Injective (mapBaseChange R A (MvPolynomial σ A)) :=
  mapBaseChange_injective R A _

/-- II.4.3 (ii): if `B` is formally smooth over `A`, then `Ω¹_{B/A}` is projective (mathlib),
hence free when `B` is local and essentially of finite type. -/
theorem free_kaehler_of_formallySmooth [FormallySmooth A B] [IsLocalRing B] [EssFiniteType A B] :
    Module.Free B Ω[B⁄A] :=
  Module.free_of_flat_of_isLocalRing

/-- II.4.3 (ii): the rank of `Ω¹_{B/A}` is the relative dimension, i.e. the number of
variables of a polynomial ring over which `B` is étale (see also
`finrank_kaehler_of_formallyEtale`). -/
theorem finrank_kaehler_of_isStandardSmoothOfRelativeDimension [Nontrivial B] (n : ℕ)
    [IsStandardSmoothOfRelativeDimension n A B] : Module.finrank B Ω[B⁄A] = n :=
  Module.finrank_eq_of_rank_eq (IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)

/-- II.4.4: if `B` is formally smooth over `A`, then `B ⊗_A Ω¹_{A/R} → Ω¹_{B/R}` is injective
with image a direct factor: it has a `B`-linear retraction. -/
theorem exists_retraction_mapBaseChange [FormallySmooth A B] :
    ∃ l : Ω[B⁄R] →ₗ[B] B ⊗[A] Ω[A⁄R], l ∘ₗ mapBaseChange R A B = LinearMap.id := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (map R A B B) LinearMap.id
    (map_surjective R A B)
  have h := exact_mapBaseChange_map R A B
  exact ⟨_, ((h.splitInjectiveEquiv (map_surjective R A B)).symm
    (h.splitSurjectiveEquiv (mapBaseChange_injective R A B) ⟨s, hs⟩)).2⟩

/-- II.4, the discussion of universally injective maps, (ii) ⇔ (iv) (mathlib): a map from a
finite module to a finite free module over a local ring is a split injection iff it is
injective on the fibres at the closed point. -/
theorem splitInjective_iff_lTensor_residueField_injective {M N : Type*} [IsLocalRing B]
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] [Module.Finite B M]
    [Module.Finite B N] [Module.Free B N] (l : M →ₗ[B] N) :
    (∃ l', l' ∘ₗ l = LinearMap.id) ↔ Function.Injective (l.lTensor (IsLocalRing.ResidueField B)) :=
  IsLocalRing.split_injective_iff_lTensor_residueField_injective l

/-- II.4.5, sufficiency (global form): if `B` is formally smooth over `R` and
`B ⊗_A Ω¹_{A/R} → Ω¹_{B/R}` is a split injection, then `B` is formally smooth over `A`. -/
theorem formallySmooth_of_retraction [FormallySmooth R B]
    (h : ∃ l : Ω[B⁄R] →ₗ[B] B ⊗[A] Ω[A⁄R], l ∘ₗ mapBaseChange R A B = LinearMap.id) :
    FormallySmooth A B := by
  obtain ⟨l, hl⟩ := h
  have hinj : Function.Injective (mapBaseChange R A B) :=
    Function.LeftInverse.injective (g := l) fun x ↦ LinearMap.congr_fun hl x
  have h := exact_mapBaseChange_map R A B
  obtain ⟨s, hs⟩ := (h.splitSurjectiveEquiv hinj).symm
    (h.splitInjectiveEquiv (map_surjective R A B) ⟨l, hl⟩)
  refine ⟨Module.Projective.of_split s (map R A B B) hs, subsingleton_of_forall_eq 0 fun y ↦ ?_⟩
  have hδ : H1Cotangent.δ R A B y = 0 := hinj <| by
    rw [map_zero]
    exact (H1Cotangent.exact_δ_mapBaseChange R A B).apply_apply_eq_zero y
  obtain ⟨z, rfl⟩ := (H1Cotangent.exact_map_δ R A B y).mp hδ
  rw [Subsingleton.elim z 0, map_zero]

/-- II.4.5 (global form): if `A` is formally smooth over `R`, then `B` is formally smooth
over `A` iff it is formally smooth over `R` and `B ⊗_A Ω¹_{A/R} → Ω¹_{B/R}` is a split
injection. -/
theorem formallySmooth_iff_formallySmooth_and_retraction [FormallySmooth R A] :
    FormallySmooth A B ↔ FormallySmooth R B ∧
      ∃ l : Ω[B⁄R] →ₗ[B] B ⊗[A] Ω[A⁄R], l ∘ₗ mapBaseChange R A B = LinearMap.id :=
  ⟨fun _ ↦ ⟨.comp R A B, exists_retraction_mapBaseChange R A B⟩,
    fun ⟨_, h⟩ ↦ formallySmooth_of_retraction R A B h⟩

/-- II.4.5 (at a point): let `B` be local with `Ω¹_{B/R}` finite free (e.g. `B = 𝒪_x` with `X`
smooth over `S` at `x`) and `Ω¹_{A/R}` finite. If `A` is formally smooth over `R`, then `B` is
formally smooth over `A` iff it is formally smooth over `R` and
`B ⊗_A Ω¹_{A/R} → Ω¹_{B/R}` is injective on the fibres at the closed point, i.e. universally
injective. -/
theorem formallySmooth_iff_formallySmooth_and_lTensor_injective [FormallySmooth R A]
    [IsLocalRing B] [Module.Finite A Ω[A⁄R]] [Module.Finite B Ω[B⁄R]] [Module.Free B Ω[B⁄R]] :
    FormallySmooth A B ↔ FormallySmooth R B ∧
      Function.Injective ((mapBaseChange R A B).lTensor (IsLocalRing.ResidueField B)) := by
  rw [formallySmooth_iff_formallySmooth_and_retraction R A B,
    splitInjective_iff_lTensor_residueField_injective]

/-- II.4.7: in II.4.5 the injectivity on fibres is the surjectivity of the tangent map, the
dual of the map induced on the fibres of `Ω¹` at the closed point. -/
theorem formallySmooth_iff_formallySmooth_and_tangentMap_surjective [FormallySmooth R A]
    [IsLocalRing B] [Module.Finite A Ω[A⁄R]] [Module.Finite B Ω[B⁄R]] [Module.Free B Ω[B⁄R]] :
    FormallySmooth A B ↔ FormallySmooth R B ∧
      Function.Surjective ((mapBaseChange R A B).baseChange
        (IsLocalRing.ResidueField B)).dualMap := by
  rw [formallySmooth_iff_formallySmooth_and_lTensor_injective R A B,
    LinearMap.dualMap_surjective_iff]
  rfl

/-- II.4.6 (formal form): for `A` and `B` formally smooth over `R`, `B` is formally étale over
`A` iff `B ⊗_A Ω¹_{A/R} → Ω¹_{B/R}` is an isomorphism. -/
theorem formallyEtale_iff_mapBaseChange_bijective [FormallySmooth R A] [FormallySmooth R B] :
    FormallyEtale A B ↔ Function.Bijective (mapBaseChange R A B) := by
  refine ⟨fun _ ↦ mapBaseChange_bijective R A B, fun h ↦ ?_⟩
  have := formallyUnramified_of_mapBaseChange_surjective R A B h.2
  have := formallySmooth_of_retraction R A B
    ⟨(LinearEquiv.ofBijective _ h).symm.toLinearMap,
      LinearMap.ext fun x ↦ (LinearEquiv.ofBijective _ h).symm_apply_apply x⟩
  exact .of_formallyUnramified_and_formallySmooth

/-- II.4.6: a morphism `A → B` of smooth `R`-algebras is étale iff
`B ⊗_A Ω¹_{A/R} → Ω¹_{B/R}` is an isomorphism. -/
theorem etale_iff_mapBaseChange_bijective [Smooth R A] [Smooth R B] :
    Etale A B ↔ Function.Bijective (mapBaseChange R A B) := by
  have : FinitePresentation A B := .of_restrict_scalars_finitePresentation R A B
  rw [← formallyEtale_iff_mapBaseChange_bijective]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨inferInstance, inferInstance⟩⟩

section Polynomial

variable {R B}
variable {ι : Type*} [Algebra (MvPolynomial ι R) B] [IsScalarTower R (MvPolynomial ι R) B]

/-- The first map of (4.2 bis) for `A = R[tᵢ]`, in the basis `dtᵢ`: it is the linear
combination of the `dgᵢ`, where `gᵢ` is the image of `tᵢ`. -/
private lemma mapBaseChange_comp_basis :
    (mapBaseChange R (MvPolynomial ι R) B) ∘ₗ
        ((mvPolynomialBasis R ι).baseChange B).repr.symm.toLinearMap =
      Finsupp.linearCombination B (fun i ↦ D R B (algebraMap (MvPolynomial ι R) B (.X i))) := by
  ext i
  simp

/-- II.4.8 (formal form): let `B` be formally smooth over `R` and let `R[t₁,…,tₙ] → B` send
`tᵢ` to `gᵢ`. Then `B` is formally étale over `R[t₁,…,tₙ]` iff the `dgᵢ` form a basis of
`Ω¹_{B/R}`. -/
theorem formallyEtale_mvPolynomial_iff [FormallySmooth R B] :
    FormallyEtale (MvPolynomial ι R) B ↔
      LinearIndependent B (fun i ↦ D R B (algebraMap (MvPolynomial ι R) B (.X i))) ∧
        Submodule.span B (Set.range fun i ↦ D R B (algebraMap (MvPolynomial ι R) B (.X i))) =
          ⊤ := by
  rw [formallyEtale_iff_mapBaseChange_bijective R (MvPolynomial ι R) B,
    ← Function.Bijective.of_comp_iff _ ((mvPolynomialBasis R ι).baseChange B).repr.symm.bijective,
    show ⇑(mapBaseChange R (MvPolynomial ι R) B) ∘
        ⇑((mvPolynomialBasis R ι).baseChange B).repr.symm = _ from
      congrArg DFunLike.coe mapBaseChange_comp_basis, LinearIndependent, Function.Bijective,
    ← LinearMap.range_eq_top, Finsupp.range_linearCombination]

/-- II.4.8: let `B` be smooth over `R` and let `R[t₁,…,tₙ] → B` send `tᵢ` to `gᵢ`. Then `B` is
étale over `R[t₁,…,tₙ]` iff the `dgᵢ` form a basis of `Ω¹_{B/R}`. -/
theorem etale_mvPolynomial_iff [Finite ι] [Smooth R B] :
    Etale (MvPolynomial ι R) B ↔
      LinearIndependent B (fun i ↦ D R B (algebraMap (MvPolynomial ι R) B (.X i))) ∧
        Submodule.span B (Set.range fun i ↦ D R B (algebraMap (MvPolynomial ι R) B (.X i))) =
          ⊤ := by
  have : FinitePresentation (MvPolynomial ι R) B :=
    .of_restrict_scalars_finitePresentation R (MvPolynomial ι R) B
  rw [← formallyEtale_mvPolynomial_iff]
  exact ⟨fun h ↦ h.formallyEtale, fun h ↦ ⟨h, inferInstance⟩⟩

/-- II.4.8, "or, which comes to the same thing": let `B = 𝒪_x` be local, essentially of finite
type and formally smooth over `R`, and let `R[t₁,…,tₙ] → B` send `tᵢ` to `gᵢ`. Then `B` is
formally étale over `R[t₁,…,tₙ]` (i.e. `g` is étale at `x`) iff the `dgᵢ(x)` form a basis of
the fibre `Ω¹_{X/S}(x) = κ(x) ⊗ Ω¹_{B/R}`. -/
theorem formallyEtale_mvPolynomial_iff_residueField [FormallySmooth R B] [IsLocalRing B]
    [EssFiniteType R B] :
    FormallyEtale (MvPolynomial ι R) B ↔
      LinearIndependent (IsLocalRing.ResidueField B) (fun i ↦
        (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] D R B (algebraMap (MvPolynomial ι R) B (.X i))) ∧
      Submodule.span (IsLocalRing.ResidueField B) (Set.range fun i ↦
        (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] D R B (algebraMap (MvPolynomial ι R) B (.X i))) =
          ⊤ := by
  rw [formallyEtale_mvPolynomial_iff]
  constructor
  · rintro ⟨hli, hsp⟩
    let b := (Module.Basis.mk hli hsp.ge).baseChange (IsLocalRing.ResidueField B)
    have hb (i : ι) : b i = (1 : IsLocalRing.ResidueField B) ⊗ₜ[B]
        D R B (algebraMap (MvPolynomial ι R) B (.X i)) := by
      simp [b]
    rw [← funext hb]
    exact ⟨b.linearIndependent, b.span_eq⟩
  · rintro ⟨hli, hsp⟩
    obtain ⟨b, hb⟩ := Module.exists_basis_of_basis_baseChange
      (fun i ↦ D R B (algebraMap (MvPolynomial ι R) B (.X i))) hli hsp
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
    rw [← funext hb]
    exact ⟨b.linearIndependent, b.span_eq⟩

end Polynomial

end SGA.SGA1.ExposeII
