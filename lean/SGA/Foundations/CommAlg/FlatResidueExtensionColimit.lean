/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Colimit.Ring
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Sequential colimits of flat local algebras

Let `A` be a ring and `G 0 → G 1 → G 2 → ⋯` a sequence of `A`-algebras. This file builds the
colimit `IsLocalRing.SeqColimit.Colim G f` (a `Ring.DirectLimit` over `ℕ`) and proves:

* `SeqColimit.flat`: if every `G n` is flat over `A`, so is the colimit (equational criterion of
  flatness: a relation in the colimit holds at some stage, where it is trivial);
* `SeqColimit.isLocalRing`, `SeqColimit.maximalIdeal_eq`, `SeqColimit.ker_lift`: if `A` is local
  and every `G n` is local with `𝔪_A G n = 𝔪_{G n}`, equal to the kernel of a ring map
  `π n : G n → K` to a field, compatible with the transition maps, then the colimit is local,
  `𝔪_A C = 𝔪_C`, and the induced map `C → K` has kernel `𝔪_C` and image the union of the images.

This is the limit step of the gonflements of EGA 0_III 10.3.1 (Bourbaki, *Algèbre commutative*
IX, Appendice).
-/

universe u

open IsLocalRing

noncomputable section

namespace IsLocalRing.SeqColimit

variable {A : Type u} [CommRing A] (G : ℕ → Type u) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
  (f : ∀ n, G n →ₐ[A] G (n + 1))

/-- The composite `G m → G n` of the transition maps (`m ≤ n`). -/
def mapLE {m n : ℕ} (h : m ≤ n) : G m →ₐ[A] G n :=
  Nat.leRecOn h (fun {k} g ↦ (f k).comp g) (AlgHom.id A (G m))

lemma mapLE_apply {m n : ℕ} (h : m ≤ n) (x : G m) :
    mapLE G f h x = Nat.leRecOn h (fun {k} ↦ f k) x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp [mapLE, Nat.leRecOn_self]
  | succ d ih =>
    rw [mapLE, Nat.leRecOn_succ le_self_add, ← mapLE, AlgHom.comp_apply, ih,
      Nat.leRecOn_succ le_self_add]

lemma mapLE_self (m : ℕ) (x : G m) : mapLE G f (le_refl m) x = x := by
  rw [mapLE_apply, Nat.leRecOn_self]

lemma mapLE_trans {k m n : ℕ} (h₁ : k ≤ m) (h₂ : m ≤ n) (x : G k) :
    mapLE G f h₂ (mapLE G f h₁ x) = mapLE G f (h₁.trans h₂) x := by
  rw [mapLE_apply, mapLE_apply, mapLE_apply, Nat.leRecOn_trans h₁ h₂]

lemma mapLE_succ {m : ℕ} (x : G m) : mapLE G f (Nat.le_succ m) x = f m x := by
  rw [mapLE_apply, Nat.leRecOn_succ (le_refl m), Nat.leRecOn_self]

/-- The composite maps, as ring maps. -/
def mapLEHom (m n : ℕ) (h : m ≤ n) : G m →+* G n := (mapLE G f h).toRingHom

instance directedSystem : DirectedSystem G fun m n h ↦ mapLEHom G f m n h where
  map_self _ x := mapLE_self G f _ x
  map_map _ _ _ h₁ h₂ x := mapLE_trans G f h₁ h₂ x

/-- The colimit of the sequence. -/
abbrev Colim : Type u := Ring.DirectLimit G fun m n h ↦ mapLEHom G f m n h

/-- The map from the `n`-th stage to the colimit. -/
def ofStage (n : ℕ) : G n →+* Colim G f := Ring.DirectLimit.of _ _ n

lemma ofStage_mapLE {m n : ℕ} (h : m ≤ n) (x : G m) :
    ofStage G f n (mapLE G f h x) = ofStage G f m x :=
  Ring.DirectLimit.of_f (G := G) (f := fun m n h ↦ mapLEHom G f m n h) h x

lemma ofStage_succ (n : ℕ) (x : G n) : ofStage G f (n + 1) (f n x) = ofStage G f n x := by
  rw [← mapLE_succ G f x, ofStage_mapLE]

instance : Algebra A (Colim G f) := ((ofStage G f 0).comp (algebraMap A (G 0))).toAlgebra

lemma algebraMap_colim (n : ℕ) :
    algebraMap A (Colim G f) = (ofStage G f n).comp (algebraMap A (G n)) := by
  ext r
  change ofStage G f 0 (algebraMap A _ r) = ofStage G f n (algebraMap A _ r)
  rw [← (mapLE G f (Nat.zero_le n)).commutes r, ofStage_mapLE]

/-- The map from the `n`-th stage to the colimit, as an `A`-algebra map. -/
def ofStageAlg (n : ℕ) : G n →ₐ[A] Colim G f :=
  { ofStage G f n with
    commutes' := fun r ↦ (RingHom.congr_fun (algebraMap_colim G f n) r).symm }

lemma ofStageAlg_apply (n : ℕ) (x : G n) : ofStageAlg G f n x = ofStage G f n x := rfl

lemma exists_ofStage (z : Colim G f) : ∃ n x, ofStage G f n x = z :=
  Ring.DirectLimit.exists_of z

/-- Finitely many elements of the colimit come from a common stage. -/
lemma exists_level {l : ℕ} (x : Fin l → Colim G f) :
    ∃ n, ∃ w : Fin l → G n, ∀ i, ofStage G f n (w i) = x i := by
  choose n w hw using fun i ↦ exists_ofStage G f (x i)
  refine ⟨Finset.univ.sup n, fun i ↦ mapLE G f (Finset.le_sup (Finset.mem_univ i)) (w i),
    fun i ↦ ?_⟩
  rw [ofStage_mapLE, hw]

/-- A sequential colimit of flat `A`-algebras is flat (equational criterion of flatness). -/
theorem flat (hflat : ∀ n, Module.Flat A (G n)) : Module.Flat A (Colim G f) := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l c x} hcx ↦ ?_
  obtain ⟨n, w, hw⟩ := exists_level G f x
  have hsm : ∀ i, ofStage G f n (c i • w i) = c i • x i := fun i ↦ by
    rw [← ofStageAlg_apply, _root_.map_smul, ofStageAlg_apply, hw]
  have h0 : ofStage G f n (∑ i, c i • w i) = 0 := by
    rw [map_sum]
    simp_rw [hsm]
    exact hcx
  obtain ⟨m, hnm, hm⟩ := Ring.DirectLimit.of.zero_exact h0
  have hrel : ∑ i, c i • mapLE G f hnm (w i) = 0 := by
    rw [← hm]
    change _ = mapLE G f hnm _
    rw [map_sum]
    simp only [_root_.map_smul]
  have := hflat m
  obtain ⟨κ, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨κ, a, fun j ↦ ofStageAlg G f m (y j), fun i ↦ ?_, ha⟩
  have hyi : mapLE G f hnm (w i) = ∑ j, a i j • y j := hy i
  rw [← hw i, ← ofStage_mapLE G f hnm, ← ofStageAlg_apply, hyi, map_sum]
  simp only [_root_.map_smul]

/-! ### The map to a field, and local rings -/

variable {K : Type u} [Field K] (π : ∀ n, G n →+* K)
  (hπ : ∀ n x, π (n + 1) (f n x) = π n x)

include hπ in
lemma π_mapLE {m n : ℕ} (h : m ≤ n) (x : G m) : π n (mapLE G f h x) = π m x := by
  induction n, h using Nat.le_induction with
  | base => rw [mapLE_self]
  | succ n hmn ih => rw [← mapLE_trans G f hmn (Nat.le_succ n), mapLE_succ, hπ, ih]

/-- The map from the colimit to `K` induced by the `π n`. -/
def lift : Colim G f →+* K :=
  Ring.DirectLimit.lift _ _ _ π fun _ _ h x ↦ π_mapLE G f π hπ h x

lemma lift_ofStage (n : ℕ) (x : G n) : lift G f π hπ (ofStage G f n x) = π n x :=
  Ring.DirectLimit.lift_of ..

variable {G f π}

/-- The image of the colimit in `K` is the union of the images of the stages. -/
lemma mem_range_lift {y : K} : y ∈ (lift G f π hπ).range ↔ ∃ n x, π n x = y := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨n, x, rfl⟩ := exists_ofStage G f z
    exact ⟨n, x, (lift_ofStage G f π hπ n x).symm⟩
  · rintro ⟨n, x, rfl⟩
    exact ⟨ofStage G f n x, lift_ofStage G f π hπ n x⟩

variable [IsLocalRing A] (hker : ∀ n, RingHom.ker (π n) = (maximalIdeal A).map (algebraMap A (G n)))
  (hunit : ∀ n (x : G n), π n x ≠ 0 → IsUnit x)

include hker in
lemma ker_lift : RingHom.ker (lift G f π hπ) = (maximalIdeal A).map (algebraMap A (Colim G f)) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨n, w, rfl⟩ := exists_ofStage G f z
    rw [RingHom.mem_ker, lift_ofStage] at hz
    have hw : w ∈ (maximalIdeal A).map (algebraMap A (G n)) := by
      rw [← hker n]
      exact hz
    rw [algebraMap_colim G f n, ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hw
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have h0 : algebraMap A (G 0) r ∈ RingHom.ker (π 0) := by
      rw [hker 0]
      exact Ideal.mem_map_of_mem _ hr
    rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_colim G f 0, RingHom.comp_apply,
      lift_ofStage]
    exact h0

include hπ hker hunit in
/-- The colimit is local if the stages are, in the sense of `hker` and `hunit`. -/
theorem isLocalRing : IsLocalRing (Colim G f) := by
  have hM : ((maximalIdeal A).map (algebraMap A (Colim G f))).IsPrime := by
    rw [← ker_lift hπ hker]
    exact RingHom.ker_isPrime _
  have hnu : ∀ z, z ∉ (maximalIdeal A).map (algebraMap A (Colim G f)) → IsUnit z := by
    intro z hz
    obtain ⟨n, w, rfl⟩ := exists_ofStage G f z
    refine (hunit n w fun h ↦ hz ?_).map _
    rw [← ker_lift hπ hker, RingHom.mem_ker, lift_ofStage]
    exact h
  refine .of_unique_max_ideal ⟨_, ⟨hM.ne_top, fun I hlt ↦ ?_⟩, fun I hI ↦ ?_⟩
  · obtain ⟨z, hzI, hzM⟩ := SetLike.exists_of_lt hlt
    exact Ideal.eq_top_of_isUnit_mem _ hzI (hnu z hzM)
  · by_contra hne
    obtain ⟨z, hzI, hzM⟩ : ∃ z ∈ I, z ∉ (maximalIdeal A).map (algebraMap A (Colim G f)) := by
      by_contra h
      exact hne (hI.eq_of_le hM.ne_top fun z hz ↦ by
        by_contra hzM
        exact h ⟨z, hz, hzM⟩)
    exact hI.ne_top (Ideal.eq_top_of_isUnit_mem _ hzI (hnu z hzM))

include hπ hker hunit in
/-- `𝔪_A C = 𝔪_C` for the colimit. -/
theorem maximalIdeal_eq :
    letI := isLocalRing hπ hker hunit
    maximalIdeal (Colim G f) = (maximalIdeal A).map (algebraMap A (Colim G f)) := by
  let _ := isLocalRing hπ hker hunit
  have hM : ((maximalIdeal A).map (algebraMap A (Colim G f))).IsMaximal := by
    refine ⟨⟨?_, fun I hlt ↦ ?_⟩⟩
    · rw [← ker_lift hπ hker]
      exact (RingHom.ker_isPrime _).ne_top
    · obtain ⟨z, hzI, hzM⟩ := SetLike.exists_of_lt hlt
      obtain ⟨n, w, rfl⟩ := exists_ofStage G f z
      refine Ideal.eq_top_of_isUnit_mem _ hzI ((hunit n w fun h ↦ hzM ?_).map _)
      rw [← ker_lift hπ hker, RingHom.mem_ker, lift_ofStage]
      exact h
  exact (IsLocalRing.eq_maximalIdeal hM).symm

end IsLocalRing.SeqColimit

end
