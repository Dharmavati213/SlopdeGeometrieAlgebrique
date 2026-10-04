/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

/-!
# Quasi-sections of open morphisms: the algebraic part

Let `A` be a noetherian local domain and `B` an `A`-algebra of finite type such that
`Spec B → Spec A` is open. For every prime `P` of `B` which is a closed point of the closed
fibre, there is a prime `Q ⊆ P` of `B` with `Q ∩ A = 0` such that `Spec (B/Q) → Spec A` is
quasi-finite at `P/Q` (`Algebra.exists_quasiFiniteAt_quotient_of_isOpenMap`). Geometrically:
the integral closed subscheme `Z = V(Q)` of `Spec B` dominates `Spec A`, passes through `P`, and
`P` is isolated in the closed fibre of `Z`. This is EGA IV 14.5.4 ("quasi-sections") in the
affine case; it is the input of SGA 1 IX.4.9.

## Proof

Let `d = dim A` and let `n` be the height of `P` in the closed fibre `B/𝔪B`.

* An open map from a noetherian quasi-sober space to a `T₀` space lifts generizations
  (`IsOpenMap.generalizingMap_of_noetherianSpace`), so `A → B` has going down and
  `ht P = d + n` (`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`).
* Choose `s ⊆ P`, `#s ≤ n`, whose image in `B/𝔪B` generates an ideal of which `P` is a minimal
  prime (Krull's height theorem, converse form). Then `P` is minimal over `𝔪B + (s)`.
* Some minimal prime `Q ⊆ P` of `(s)` meets `A` in `0`. Otherwise a product `a ≠ 0` of nonzero
  elements of the `Q ∩ A` lies in every prime between `(s)` and `P`; with `t ⊆ A` lifting a
  system of parameters of `A/aA` (`#t = dim A/aA ≤ d - 1`), `P` is minimal over `tB + (s)`, so
  `d + n = ht P ≤ #t + #s ≤ d - 1 + n`, a contradiction.
* `P/Q` is minimal and maximal among the primes of `B/Q` containing `𝔪`, hence isolated in the
  closed fibre of `Spec (B/Q)`, i.e. `B/Q` is quasi-finite over `A` at `P/Q`.

EGA states 14.5.4 for universally open morphisms; here only the openness of `Spec B → Spec A`
is used.

## Main results

* `IsOpenMap.generalizingMap_of_noetherianSpace`: generizations lift along an open continuous map
  from a noetherian quasi-sober space to a `T₀` space;
* `Algebra.hasGoingDown_of_isOpenMap`: if `B` is noetherian and `Spec B → Spec A` is open, `B` has
  going down over `A`;
* `Algebra.exists_mem_minimalPrimes_le_comap_eq_bot`: the dimension count above;
* `Algebra.isOpen_singleton_fiber_of_mem_minimalPrimes`: a prime minimal and maximal over `𝔪_A C`
  is isolated in the closed fibre;
* `Algebra.exists_quasiFiniteAt_quotient` (going down) and
  `Algebra.exists_quasiFiniteAt_quotient_of_isOpenMap` (open map): the quasi-section.

## References

* [EGA IV₃, 14.5.4], [EGA IV₃, 14.3.13]
* [Stacks, Tag 00ON] (height of a prime under going down: `ht P = ht p + ht (P/pB)`)
* Krull's height theorem and its converse (mathlib, `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`)
-/

open IsLocalRing Topology TopologicalSpace

section Topology

/-- Generizations lift along an open continuous map from a noetherian quasi-sober space to a
`T₀` space: if `y ⤳ f x`, there is `x' ⤳ x` with `f x' = y`. -/
theorem IsOpenMap.generalizingMap_of_noetherianSpace {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [NoetherianSpace X] [QuasiSober X] [T0Space Y] {f : X → Y}
    (hfc : Continuous f) (hf : IsOpenMap f) : GeneralizingMap f := by
  intro x y h
  -- `x` lies in the closure of the fibre `f ⁻¹' {y}`.
  have hcl : x ∈ closure (f ⁻¹' {y}) := by
    rw [mem_closure_iff]
    intro U hU hxU
    obtain ⟨x', hx'U, hx'⟩ := (specializes_iff_forall_open.mp h) (f '' U) (hf U hU) ⟨x, hxU, rfl⟩
    exact ⟨x', hx'U, hx'⟩
  -- The fibre is the finite union of the images of its irreducible components.
  set S := f ⁻¹' {y}
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := S)
  have hS : S = ⋃ Z ∈ irreducibleComponents S, ((↑) : S → X) '' Z := by
    ext w
    simp only [Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hw
      have : (⟨w, hw⟩ : S) ∈ ⋃₀ irreducibleComponents S := by
        rw [sUnion_irreducibleComponents]; trivial
      obtain ⟨Z, hZ, hwZ⟩ := Set.mem_sUnion.mp this
      exact ⟨Z, hZ, ⟨w, hw⟩, hwZ, rfl⟩
    · rintro ⟨Z, -, v, -, rfl⟩
      exact v.2
  rw [hS, hfin.closure_biUnion] at hcl
  obtain ⟨Z, hZ, hxZ⟩ := Set.mem_iUnion₂.mp hcl
  have hirr : IsIrreducible (((↑) : S → X) '' Z) :=
    hZ.1.image _ continuous_subtype_val.continuousOn
  set ξ := hirr.genericPoint
  have hξ : IsGenericPoint ξ (closure (((↑) : S → X) '' Z)) :=
    hirr.isGenericPoint_genericPoint_closure
  refine ⟨ξ, hξ.specializes hxZ, ?_⟩
  -- `f ξ = y`: they specialize to each other.
  obtain ⟨z, hz⟩ := hZ.1.nonempty
  have h₁ : f ξ ⤳ y := by
    have := (hξ.specializes (subset_closure ⟨z, hz, rfl⟩)).map hfc
    rwa [show f z = y from z.2] at this
  have h₂ : y ⤳ f ξ := by
    rw [specializes_iff_mem_closure]
    refine hfc.closure_preimage_subset {y} ?_
    refine closure_mono ?_ hξ.mem
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  exact (h₁.antisymm h₂).eq

end Topology

namespace Algebra

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- If `Spec B → Spec A` is open and `B` is noetherian, `B` has going down over `A`. -/
theorem hasGoingDown_of_isOpenMap [IsNoetherianRing B]
    (h : IsOpenMap (PrimeSpectrum.comap (algebraMap A B))) : Algebra.HasGoingDown A B :=
  Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mpr
    (h.generalizingMap_of_noetherianSpace (PrimeSpectrum.continuous_comap _))

section QuasiSection

variable [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsNoetherianRing B]

/-- The key step of EGA IV 14.5.4. Let `A` be a noetherian local domain and `B` a noetherian
`A`-algebra with going down, `P` a prime of `B` over `𝔪_A`, and `s ⊆ B` a finite set with
`(s) ⊆ P`, such that the image of `P` in the closed fibre `B/𝔪B` is a minimal prime of the ideal
generated by `s` there and `#s` is at most the height of that image. Then some minimal prime
`Q ⊆ P` of `(s)` meets `A` in `0`. -/
theorem exists_mem_minimalPrimes_le_comap_eq_bot [Algebra.HasGoingDown A B]
    (P : Ideal B) [P.IsPrime] [P.LiesOver (maximalIdeal A)] (s : Finset B)
    (hsP : Ideal.span (s : Set B) ≤ P)
    (hP : P.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B))) ∈
      ((Ideal.span (s : Set B)).map
        (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).minimalPrimes)
    (hcard : (s.card : ℕ∞) ≤
      (P.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).height) :
    ∃ Q ∈ (Ideal.span (s : Set B)).minimalPrimes, Q ≤ P ∧
      Q.comap (algebraMap A B) = ⊥ := by
  classical
  set I := (maximalIdeal A).map (algebraMap A B)
  set Pb := P.map (Ideal.Quotient.mk I)
  by_contra H
  push Not at H
  -- The minimal primes of `(s)` below `P`, and a nonzero `a₀ ∈ A` lying in all of them.
  set M := {Q ∈ (Ideal.span (s : Set B)).minimalPrimes | Q ≤ P}
  have hMfin : M.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun Q hQ ↦ hQ.1
  have hex : ∀ Q ∈ M, ∃ a : A, a ≠ 0 ∧ algebraMap A B a ∈ Q := by
    intro Q hQ
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (H Q hQ.1 hQ.2)
    exact ⟨a, ha0, ha⟩
  choose! a ha0 haQ using hex
  set a₀ := ∏ Q ∈ hMfin.toFinset, a Q
  have ha₀0 : a₀ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun Q hQ ↦ ha0 Q (hMfin.mem_toFinset.mp hQ)
  have ha₀Q : ∀ Q ∈ M, algebraMap A B a₀ ∈ Q := fun Q hQ ↦ by
    rw [map_prod]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (hMfin.mem_toFinset.mpr hQ)) (haQ Q hQ)
  -- Every prime between `(s)` and `P` contains `a₀`.
  have ha₀q : ∀ q : Ideal B, q.IsPrime → Ideal.span (s : Set B) ≤ q → q ≤ P →
      algebraMap A B a₀ ∈ q := by
    intro q hq hsq hqP
    obtain ⟨Q, hQ, hQq⟩ := Ideal.exists_minimalPrimes_le hsq
    exact hQq (ha₀Q Q ⟨hQ, hQq.trans hqP⟩)
  have hPA : P.comap (algebraMap A B) = maximalIdeal A := by
    rw [← Ideal.under_def, ← Ideal.over_def P (maximalIdeal A)]
  have ha₀m : a₀ ∈ maximalIdeal A := by
    rw [← hPA, Ideal.mem_comap]
    exact ha₀q P inferInstance hsP le_rfl
  -- A system of parameters `t` of `A/a₀A`.
  set J := Ideal.span {a₀}
  have hJm : J ≤ maximalIdeal A := (Ideal.span_singleton_le_iff_mem _).mpr ha₀m
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top hJm
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (A ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hmJ : maximalIdeal (A ⧸ J) = (maximalIdeal A).map (Ideal.Quotient.mk J) := by
    have : ((maximalIdeal A).map (Ideal.Quotient.mk J)).IsMaximal :=
      (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
        (maximalIdeal.isMaximal A)).resolve_left
          (Ideal.isPrime_map_quotientMk_of_isPrime hJm).ne_top
    exact (IsLocalRing.eq_maximalIdeal this).symm
  obtain ⟨tb, htb, htbcard⟩ :=
    (maximalIdeal (A ⧸ J)).exists_finset_card_eq_height_of_isNoetherianRing
  let lift : A ⧸ J → A := Function.surjInv Ideal.Quotient.mk_surjective
  set t := tb.image lift
  have ht : t.image (Ideal.Quotient.mk J) = tb := by
    rw [Finset.image_image]
    convert Finset.image_id (s := tb)
    ext x
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective x
  have hmt : maximalIdeal A ∈ (J ⊔ Ideal.span (t : Set A)).minimalPrimes := by
    refine Ideal.mem_minimalPrimes_sup hJm ?_
    rw [← hmJ, Ideal.map_span, ← Finset.coe_image, ht]
    exact htb
  -- `P` is minimal over `(t) B + (s)`.
  have hP₁ : P ∈ ((J ⊔ Ideal.span (t : Set A)).map (algebraMap A B) ⊔
      Ideal.span (s : Set B)).minimalPrimes :=
    Ideal.map_sup_mem_minimalPrimes_of_map_quotientMk_mem_minimalPrimes hmt hsP hP
  have hP₂ : P ∈ ((Ideal.span (t : Set A)).map (algebraMap A B) ⊔
      Ideal.span (s : Set B)).minimalPrimes := by
    refine ⟨⟨inferInstance, le_trans (sup_le_sup_right (Ideal.map_mono le_sup_right) _) hP₁.1.2⟩,
      fun q ⟨hq, hqle⟩ hqP ↦ hP₁.2 ⟨hq, ?_⟩ hqP⟩
    rw [sup_le_iff] at hqle ⊢
    refine ⟨?_, hqle.2⟩
    rw [Ideal.map_sup, sup_le_iff]
    refine ⟨?_, hqle.1⟩
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact ha₀q q hq hqle.2 hqP
  -- Counting generators.
  have hspan : (Ideal.span (t : Set A)).map (algebraMap A B) ⊔ Ideal.span (s : Set B) =
      Ideal.span ((t.image (algebraMap A B) ∪ s : Finset B) : Set B) := by
    simp only [Ideal.map_span, Finset.coe_union, Finset.coe_image, Ideal.span_union]
  rw [hspan] at hP₂
  have hle : P.height ≤ ((t.image (algebraMap A B) ∪ s).card : ℕ∞) :=
    Ideal.height_le_card_of_mem_minimalPrimes_span_finset hP₂
  have hcard' : ((t.image (algebraMap A B) ∪ s).card : ℕ∞) ≤ tb.card + s.card := by
    norm_cast
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_image_le.trans Finset.card_image_le) _)
  have hgd : P.height = (maximalIdeal A).height + Pb.height :=
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) P
  -- `dim A/a₀A + 1 ≤ dim A`.
  have hdim : (maximalIdeal (A ⧸ J)).height + 1 ≤ (maximalIdeal A).height := by
    have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (R := A)
      (mem_nonZeroDivisors_of_ne_zero ha₀0)
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at h
    exact_mod_cast h
  have hPbfin : Pb.height ≠ ⊤ := by
    have : Pb.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime (Ideal.map_le_iff_le_comap.mpr
      hPA.ge)
    exact Ideal.height_ne_top_of_isPrime
  have key : (maximalIdeal (A ⧸ J)).height + Pb.height + 1 ≤
      (maximalIdeal (A ⧸ J)).height + Pb.height := by
    calc (maximalIdeal (A ⧸ J)).height + Pb.height + 1
        = (maximalIdeal (A ⧸ J)).height + 1 + Pb.height := by ring
      _ ≤ (maximalIdeal A).height + Pb.height := by gcongr
      _ = P.height := hgd.symm
      _ ≤ tb.card + s.card := hle.trans hcard'
      _ ≤ (maximalIdeal (A ⧸ J)).height + Pb.height := by
        rw [htbcard]; gcongr
  have hfin : (maximalIdeal (A ⧸ J)).height + Pb.height ≠ ⊤ := by
    rw [← htbcard]
    exact WithTop.add_ne_top.mpr ⟨ENat.natCast_ne_top _, hPbfin⟩
  exact absurd key (by
    rw [ENat.add_one_le_iff hfin]
    exact lt_irrefl _)

omit [IsDomain A] [IsNoetherianRing A] [IsNoetherianRing B] in
/-- Let `C` be a noetherian `A`-algebra, `A` local. A prime `z` of `C` over `𝔪_A` which is both
minimal and maximal among the primes of `C` containing `𝔪_A C` is isolated in the closed fibre of
`Spec C → Spec A`. -/
theorem isOpen_singleton_fiber_of_mem_minimalPrimes {C : Type*} [CommRing C] [Algebra A C]
    [IsNoetherianRing C] (z : PrimeSpectrum C)
    (hz : z.asIdeal.comap (algebraMap A C) = maximalIdeal A)
    (hmin : z.asIdeal ∈ ((maximalIdeal A).map (algebraMap A C)).minimalPrimes)
    (hmax : ∀ y : Ideal C, y.IsPrime → z.asIdeal ≤ y → y = z.asIdeal) :
    IsOpen (X := PrimeSpectrum.comap (algebraMap A C) ⁻¹' {z.comap (algebraMap A C)})
      {⟨z, rfl⟩} := by
  classical
  set IC := (maximalIdeal A).map (algebraMap A C)
  set T := IC.minimalPrimes \ {z.asIdeal}
  have hTfin : T.Finite := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ IC).sdiff
  -- An element `f₀ ∉ z` lying in every other minimal prime of `𝔪_A C`.
  have hex : ∀ p ∈ T, ∃ f ∈ p, f ∉ z.asIdeal := by
    intro p hp
    by_contra h
    push Not at h
    exact hp.2 (le_antisymm h (hmin.2 hp.1.1 h))
  choose! f hfp hfz using hex
  set f₀ := ∏ p ∈ hTfin.toFinset, f p
  have hf₀z : f₀ ∉ z.asIdeal := by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨p, hp, hfp'⟩
    exact hfz p (hTfin.mem_toFinset.mp hp) hfp'
  have hf₀p : ∀ p ∈ T, f₀ ∈ p := fun p hp ↦
    Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (hTfin.mem_toFinset.mpr hp)) (hfp p hp)
  -- The singleton is the trace of the basic open `D(f₀)`.
  convert (PrimeSpectrum.isOpen_basicOpen (a := f₀)).preimage continuous_subtype_val using 1
  ext ⟨w, hw⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage, SetLike.mem_coe,
    PrimeSpectrum.mem_basicOpen]
  constructor
  · intro h
    obtain rfl : w = z := congrArg Subtype.val h
    exact hf₀z
  · intro hfw
    have hwm : w.asIdeal.comap (algebraMap A C) = maximalIdeal A :=
      (congrArg PrimeSpectrum.asIdeal hw).trans hz
    have hIw : IC ≤ w.asIdeal := Ideal.map_le_iff_le_comap.mpr hwm.ge
    obtain ⟨p, hp, hpw⟩ := Ideal.exists_minimalPrimes_le hIw
    by_cases hpz : p = z.asIdeal
    · exact Subtype.ext (PrimeSpectrum.ext (hmax w.asIdeal w.2 (hpz ▸ hpw)))
    · exact absurd (hpw (hf₀p p ⟨hp, hpz⟩)) hfw

omit [IsNoetherianRing B] in
/-- EGA IV 14.5.4 (quasi-sections), affine form. Let `A` be a noetherian local domain, `B` an
`A`-algebra of finite type with going down (e.g. `Spec B → Spec A` open,
`Algebra.hasGoingDown_of_isOpenMap`), and `P` a prime of `B` over `𝔪_A` which is a closed point
of the closed fibre (`P/𝔪B` maximal in `B/𝔪B`). There is a prime `Q ⊆ P` of `B` with
`Q ∩ A = 0` such that `B/Q` is quasi-finite over `A` at the prime `z = P/Q`. -/
theorem exists_quasiFiniteAt_quotient [Algebra.FiniteType A B] [Algebra.HasGoingDown A B]
    (P : Ideal B) [P.IsPrime] [P.LiesOver (maximalIdeal A)]
    (hPmax : (P.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).IsMaximal) :
    ∃ (Q : Ideal B) (_ : Q.IsPrime) (z : PrimeSpectrum (B ⧸ Q)), Q ≤ P ∧
      Q.comap (algebraMap A B) = ⊥ ∧ z.asIdeal.comap (Ideal.Quotient.mk Q) = P ∧
      Algebra.QuasiFiniteAt A z.asIdeal := by
  classical
  have := Algebra.FiniteType.isNoetherianRing A B
  set I := (maximalIdeal A).map (algebraMap A B)
  set Pb := P.map (Ideal.Quotient.mk I)
  have hPA : P.comap (algebraMap A B) = maximalIdeal A := by
    rw [← Ideal.under_def, ← Ideal.over_def P (maximalIdeal A)]
  have hIP : I ≤ P := Ideal.map_le_iff_le_comap.mpr hPA.ge
  have : Pb.IsPrime := hPmax.isPrime
  -- Lift a system of parameters of the closed fibre at `P`.
  obtain ⟨sb, hsb, hsbcard⟩ := Pb.exists_finset_card_eq_height_of_isNoetherianRing
  let lift : B ⧸ I → B := Function.surjInv Ideal.Quotient.mk_surjective
  set s := sb.image lift
  have hs : s.image (Ideal.Quotient.mk I) = sb := by
    rw [Finset.image_image]
    convert Finset.image_id (s := sb)
    ext x
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective x
  have hmap : (Ideal.span (s : Set B)).map (Ideal.Quotient.mk I) =
      Ideal.span (sb : Set (B ⧸ I)) := by
    rw [Ideal.map_span, ← Finset.coe_image, hs]
  have hsP : Ideal.span (s : Set B) ≤ P := by
    rw [Ideal.span_le]
    intro x hx
    have : Ideal.Quotient.mk I x ∈ Pb :=
      hsb.1.2 (Ideal.subset_span (hs ▸ Finset.mem_image_of_mem _ hx))
    exact (Ideal.mem_quotient_iff_mem hIP).mp this
  have hP : Pb ∈ ((Ideal.span (s : Set B)).map (Ideal.Quotient.mk I)).minimalPrimes :=
    hmap ▸ hsb
  have hcard : (s.card : ℕ∞) ≤ Pb.height := by
    rw [← hsbcard]
    exact_mod_cast Finset.card_image_le
  obtain ⟨Q, hQ, hQP, hQA⟩ := exists_mem_minimalPrimes_le_comap_eq_bot P s hsP hP hcard
  have : Q.IsPrime := hQ.1.1
  have hzP : (P.map (Ideal.Quotient.mk Q)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hQP
  let z : PrimeSpectrum (B ⧸ Q) := ⟨_, hzP⟩
  have hzB : z.asIdeal.comap (Ideal.Quotient.mk Q) = P := Ideal.comap_map_mk hQP
  have hPmin : P ∈ (I ⊔ Ideal.span (s : Set B)).minimalPrimes := Ideal.mem_minimalPrimes_sup hIP hP
  have : Algebra.FiniteType A (B ⧸ Q) :=
    .of_surjective (Ideal.Quotient.mkₐ A Q) Ideal.Quotient.mk_surjective
  refine ⟨Q, inferInstance, z, hQP, hQA, hzB, ?_⟩
  refine Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber z ?_
  have halg : algebraMap A (B ⧸ Q) = (Ideal.Quotient.mk Q).comp (algebraMap A B) :=
    IsScalarTower.algebraMap_eq A B (B ⧸ Q)
  have hz : z.asIdeal.comap (algebraMap A (B ⧸ Q)) = maximalIdeal A := by
    rw [halg, ← Ideal.comap_comap, hzB, hPA]
  have hQy : ∀ y : Ideal (B ⧸ Q), Q ≤ y.comap (Ideal.Quotient.mk Q) := fun y x hx ↦ by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact y.zero_mem
  refine isOpen_singleton_fiber_of_mem_minimalPrimes z hz ?_ ?_
  · -- `z` is a minimal prime of `𝔪_A (B/Q)`.
    refine ⟨⟨hzP, Ideal.map_le_iff_le_comap.mpr hz.ge⟩, fun y ⟨hy, hIy⟩ hyz ↦ ?_⟩
    have hyB : P ≤ y.comap (Ideal.Quotient.mk Q) := by
      refine hPmin.2 ⟨Ideal.comap_isPrime _ _, sup_le ?_ ((hQ.1.2).trans (hQy y))⟩
        ((Ideal.comap_mono hyz).trans hzB.le)
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← halg]
      exact Ideal.map_le_iff_le_comap.mp hIy
    calc z.asIdeal = P.map (Ideal.Quotient.mk Q) := rfl
      _ ≤ (y.comap (Ideal.Quotient.mk Q)).map (Ideal.Quotient.mk Q) := Ideal.map_mono hyB
      _ = y := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective y
  · -- `z` is maximal among the primes of `B/Q` over `𝔪_A`.
    intro y hy hzy
    set yB := y.comap (Ideal.Quotient.mk Q)
    have hPyB : P ≤ yB := hzB.ge.trans (Ideal.comap_mono hzy)
    have hyBprime : yB.IsPrime := Ideal.comap_isPrime _ _
    have hIyB : I ≤ yB := hIP.trans hPyB
    have hne : yB.map (Ideal.Quotient.mk I) ≠ ⊤ :=
      (Ideal.isPrime_map_quotientMk_of_isPrime hIyB).ne_top
    have heq : Pb = yB.map (Ideal.Quotient.mk I) := hPmax.eq_of_le hne (Ideal.map_mono hPyB)
    have hyBP : yB = P := by
      rw [← Ideal.comap_map_mk hIyB, ← heq, Ideal.comap_map_mk hIP]
    calc y = yB.map (Ideal.Quotient.mk Q) :=
          (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective y).symm
      _ = z.asIdeal := by rw [hyBP]

omit [IsNoetherianRing B] in
/-- EGA IV 14.5.4 (quasi-sections), affine form, for `Spec B → Spec A` open: let `A` be a
noetherian local domain, `B` an `A`-algebra of finite type with `Spec B → Spec A` open, and `P` a
prime of `B` over `𝔪_A` with `P/𝔪B` maximal in `B/𝔪B`. There is a prime `Q ⊆ P` of `B` with
`Q ∩ A = 0` such that `B/Q` is quasi-finite over `A` at `z = P/Q`. -/
theorem exists_quasiFiniteAt_quotient_of_isOpenMap [Algebra.FiniteType A B]
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap A B)))
    (P : Ideal B) [P.IsPrime] [P.LiesOver (maximalIdeal A)]
    (hPmax : (P.map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).IsMaximal) :
    ∃ (Q : Ideal B) (_ : Q.IsPrime) (z : PrimeSpectrum (B ⧸ Q)), Q ≤ P ∧
      Q.comap (algebraMap A B) = ⊥ ∧ z.asIdeal.comap (Ideal.Quotient.mk Q) = P ∧
      Algebra.QuasiFiniteAt A z.asIdeal := by
  have := Algebra.FiniteType.isNoetherianRing A B
  have := hasGoingDown_of_isOpenMap hopen
  exact exists_quasiFiniteAt_quotient P hPmax

end QuasiSection

end Algebra
