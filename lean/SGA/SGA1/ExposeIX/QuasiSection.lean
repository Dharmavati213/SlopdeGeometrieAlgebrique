/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.QuasiSection
import SGA.SGA1.ExposeIX.UniversallyOpenDescent

/-!
# SGA 1, Exposé IX, 4.9: quasi-sections of universally open morphisms

SGA proves IX.4.9 (a surjective universally open morphism of finite type over a locally
noetherian base is an effective descent morphism for étale separated schemes of finite type)
using quasi-sections of universally open morphisms (EGA IV 14.3.13, 14.5.4).
`SGA.SGA1.ExposeIX.UniversallyOpenDescent` formalizes the rest of the argument, with the
quasi-sections as a hypothesis (`QuasiSectionStatement`). Here we prove that statement
(`quasiSectionStatement`), hence IX.4.9 (`effectiveDescentOfUniversallyOpenStatement`).

Let `A` be a noetherian local domain and `g : X ⟶ Spec A` universally open and locally of finite
type, with a point over the closed point. On an affine open `Spec B` of `X` meeting the closed
fibre, `Spec B → Spec A` is open; pick a prime `P` of `B` which is a closed point of the closed
fibre. The algebraic statement `Algebra.exists_quasiFiniteAt_quotient_of_isOpenMap` gives a prime
`Q ⊆ P` with `Q ∩ A = 0` and `B/Q` quasi-finite over `A` at `P/Q`. Then `Z = Spec (B/Q)` is an
integral scheme mapping to `X`, dominant over `Spec A`, quasi-finite at `P/Q`, which lies over
the closed point.

Only the openness of `g` (not its universal openness) is used, and `Z` is an integral closed
subscheme of an affine open of `X`, as in EGA.
-/

universe u

open CategoryTheory IsLocalRing

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

/-- If the `R`-algebra `S` is quasi-finite at a prime `q` (`Algebra.QuasiFiniteAt`), then
`Spec S ⟶ Spec R` is quasi-finite at `q`. -/
lemma quasiFiniteAt_Spec_map_algebraMap {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) [Algebra.QuasiFiniteAt R q.asIdeal] :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).QuasiFiniteAt q := by
  let := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
  have : Algebra.QuasiFinite (Localization.AtPrime (q.asIdeal.under R))
      (Localization.AtPrime q.asIdeal) := .of_restrictScalars R _ _
  have key : (Spec.map (CommRingCat.ofHom (algebraMap R S))).QuasiFiniteAt q ↔
      Algebra.QuasiFinite (Localization.AtPrime (q.asIdeal.under R))
        (Localization.AtPrime q.asIdeal) := by
    rw [← RingHom.quasiFinite_algebraMap]
    exact RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso ..)
  exact key.mpr this

/-- EGA IV 14.5.4 (quasi-sections), in the form used in the proof of IX.4.9
(`QuasiSectionStatement`): let `A` be a noetherian local domain and `g : X ⟶ Spec A` universally
open and locally of finite type, with nonempty closed fibre. There are an integral scheme `Z`
and `i : Z ⟶ X` such that `i ≫ g` is locally of finite type and dominant and is quasi-finite at
a point of `Z` over the closed point. (`Z` is an integral closed subscheme of an affine open
of `X`.) -/
theorem quasiSectionStatement : QuasiSectionStatement.{u} := by
  intro A _ _ _ _ X g _ _ ⟨x, hx⟩
  -- An affine open `U ∋ x`, and `Spec Γ(X, U) ⟶ Spec A` written as `Spec.map φ`.
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ g)
  let B := Γ(X, U)
  let : Algebra A B := φ.hom.toAlgebra
  -- `B` is of finite type over `A` and `Spec B → Spec A` is open.
  have hft : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
  have : Algebra.FiniteType A B :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft
  have hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap A B)) := by
    have : IsOpenMap (hU.fromSpec ≫ g) :=
      g.isOpenMap.comp hU.fromSpec.isOpenEmbedding.isOpenMap
    rw [← hφ] at this
    exact this
  -- The point `x` as a prime of `B`: it lies over the maximal ideal of `A`.
  let x' : Spec Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  have hx' : x'.asIdeal.comap (algebraMap A B) = maximalIdeal A := by
    have h1 : (Spec.map φ) x' = g x := by
      calc (Spec.map φ) x' = (hU.fromSpec ≫ g) x' :=
            congrArg (fun f : Spec Γ(X, U) ⟶ Spec (.of A) ↦ f x') hφ
        _ = g (hU.fromSpec x') := rfl
        _ = g x := by rw [hU.fromSpec_primeIdealOf ⟨x, hxU⟩]
    exact congrArg PrimeSpectrum.asIdeal (h1.trans hx)
  -- A closed point `P` of the closed fibre of `Spec B → Spec A`.
  set I := (maximalIdeal A).map (algebraMap A B)
  have hIx : I ≤ x'.asIdeal := Ideal.map_le_iff_le_comap.mpr hx'.ge
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top x'.2.ne_top hIx
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (B ⧸ I)
  set P := M.comap (Ideal.Quotient.mk I)
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hIP : I ≤ P := fun y hy ↦ by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
    exact M.zero_mem
  have hPA : P.comap (algebraMap A B) = maximalIdeal A :=
    ((maximalIdeal.isMaximal A).eq_of_le (Ideal.comap_isPrime _ _).ne_top
      (Ideal.map_le_iff_le_comap.mp hIP)).symm
  have : P.LiesOver (maximalIdeal A) := ⟨by rw [Ideal.under_def, hPA]⟩
  have hPmax : (P.map (Ideal.Quotient.mk I)).IsMaximal := by
    rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  -- The algebraic quasi-section.
  obtain ⟨Q, _, z, hQP, hQA, hzP, hqf⟩ :=
    Algebra.exists_quasiFiniteAt_quotient_of_isOpenMap hopen P hPmax
  refine ⟨Spec (.of (B ⧸ Q)), inferInstance,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q)) ≫ hU.fromSpec, z, ?_⟩
  have hcomp : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q)) ≫ hU.fromSpec) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap A (B ⧸ Q))) := by
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    rfl
  rw [hcomp]
  refine ⟨?_, ?_, ?_, quasiFiniteAt_Spec_map_algebraMap z⟩
  · -- locally of finite type
    have : Algebra.FiniteType A (B ⧸ Q) :=
      .of_surjective (Ideal.Quotient.mkₐ A Q) Ideal.Quotient.mk_surjective
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr this
  · -- dominant: the generic point of `Spec (B/Q)` maps to the generic point of `Spec A`
    refine ⟨?_⟩
    let η : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
    let η' : Spec (.of (B ⧸ Q)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (B ⧸ Q))
    have hgen : (Spec.map (CommRingCat.ofHom (algebraMap A (B ⧸ Q)))) η' = η := by
      apply PrimeSpectrum.ext
      change (⊥ : Ideal (B ⧸ Q)).comap (algebraMap A (B ⧸ Q)) = ⊥
      rw [IsScalarTower.algebraMap_eq A B (B ⧸ Q), ← Ideal.comap_comap,
        ← RingHom.ker_eq_comap_bot, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, hQA]
    have hη : η ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (B ⧸ Q)))) := ⟨η', hgen⟩
    intro w
    refine closure_mono (Set.singleton_subset_iff.mpr hη) ?_
    exact specializes_iff_mem_closure.mp
      ((PrimeSpectrum.le_iff_specializes η w).mp bot_le)
  · -- `z` lies over the closed point
    apply PrimeSpectrum.ext
    change z.asIdeal.comap (algebraMap A (B ⧸ Q)) = maximalIdeal A
    rw [IsScalarTower.algebraMap_eq A B (B ⧸ Q), ← Ideal.comap_comap,
      Ideal.Quotient.algebraMap_eq, hzP, hPA]

/-- IX.4.9: over a locally noetherian `S`, a surjective, universally open morphism of finite type
`g : S' ⟶ S` (locally of finite type and quasi-compact) is an effective descent morphism for étale
separated schemes of finite type. -/
theorem effectiveDescentOfUniversallyOpenStatement :
    EffectiveDescentOfUniversallyOpenStatement.{u} :=
  effectiveDescentOfUniversallyOpen quasiSectionStatement

end SGA.SGA1.ExposeIX
