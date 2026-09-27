/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# Complete modules over adic rings

Basic facts on modules over a ring `A` which is complete for the `I`-adic topology, used for
noetherian adic rings and formal schemes (EGA 0_I §7, Matsumura, *Commutative ring theory*, §8).

## Main results

* `IsPrecomplete.of_finite`, `IsAdicComplete.of_finite`: finite modules over a complete
  (noetherian) ring are complete.
* `Module.Finite.of_isHausdorff_of_finite_quotient`: if `M` is `I`-adically separated and
  `M ⧸ I M` is finite, then `M` is finite (Matsumura, Thm. 8.4).
* `isAdicComplete_iff_of_pow_le`, `isAdicComplete_iff_of_radical_eq`: completeness only depends on
  the ideal of definition up to `Iᵏ ⊆ J`, `Jˡ ⊆ I` (for noetherian rings: up to radical).
-/

universe u v

open TensorProduct

variable {A : Type u} [CommRing A] (I : Ideal A)
variable (M : Type v) [AddCommGroup M] [Module A M]

/-- A finite module over an `I`-adically precomplete ring is `I`-adically precomplete. -/
theorem IsPrecomplete.of_finite [IsPrecomplete I A] [Module.Finite A M] : IsPrecomplete I M := by
  have hA : Function.Surjective (AdicCompletion.of I A) := AdicCompletion.of_surjective I A
  refine AdicCompletion.of_surjective_iff.mp fun x ↦ ?_
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M x
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r m =>
    obtain ⟨a, rfl⟩ := hA r
    exact ⟨a • m, by rw [AdicCompletion.ofTensorProduct_tmul, map_smul]; rfl⟩
  | add s t hs ht =>
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩

/-- A finite module over an `I`-adically complete noetherian ring is `I`-adically complete. -/
theorem IsAdicComplete.of_finite [IsNoetherianRing A] [IsAdicComplete I A] [Module.Finite A M] :
    IsAdicComplete I M where
  toIsHausdorff := .of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  toIsPrecomplete := .of_finite I M

variable {I M}

/-- Nakayama's lemma for complete modules (Matsumura, *Commutative ring theory*, Thm. 8.4):
if `A` is `I`-adically complete, `M` is `I`-adically separated and `M ⧸ I M` is a finite
`A`-module, then `M` is a finite `A`-module. -/
theorem Module.Finite.of_isHausdorff_of_finite_quotient [IsPrecomplete I A] [IsHausdorff I M]
    [Module.Finite A (M ⧸ (I • ⊤ : Submodule A M))] : Module.Finite A M := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' A (M ⧸ (I • ⊤ : Submodule A M))
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (Submodule.mkQ (I • ⊤ : Submodule A M)) g
    (Submodule.mkQ_surjective _)
  have : IsPrecomplete I (Fin n → A) := .of_finite I _
  have hsurj : Function.Surjective f :=
    surjective_of_mkQ_comp_surjective (I := I) (by rw [hf]; exact hg)
  exact Module.Finite.of_surjective f hsurj

/-! ### Changing the ideal of definition -/

section ChangeIdeal

variable {J : Ideal A}

lemma smul_top_mono_of_pow_le {k : ℕ} (hk : I ^ k ≤ J) (n : ℕ) :
    (I ^ (k * n) • ⊤ : Submodule A M) ≤ J ^ n • ⊤ :=
  Submodule.smul_mono_left (by rw [pow_mul]; exact Ideal.pow_right_mono hk n)

/-- If `I ^ k ⊆ J`, a module which is `J`-adically separated is `I`-adically separated. -/
theorem IsHausdorff.of_pow_le {k : ℕ} (hk : I ^ k ≤ J) [IsHausdorff J M] : IsHausdorff I M := by
  refine ⟨fun x hx ↦ IsHausdorff.haus ‹_› x fun n ↦ ?_⟩
  have := hx (k * n)
  rw [SModEq.zero] at this ⊢
  exact smul_top_mono_of_pow_le hk n this

/-- If `I ^ k ⊆ J` and `J ^ l ⊆ I`, a module which is `I`-adically precomplete is `J`-adically
precomplete. -/
theorem IsPrecomplete.of_pow_le {k l : ℕ} (hk : I ^ k ≤ J) (hl : J ^ l ≤ I) [IsPrecomplete I M] :
    IsPrecomplete J M := by
  have hk' : I ^ (k + 1) ≤ J := (Ideal.pow_le_pow_right k.le_succ).trans hk
  have hl' : J ^ (l + 1) ≤ I := (Ideal.pow_le_pow_right l.le_succ).trans hl
  refine isPrecomplete_iff.mpr fun f hf ↦ ?_
  obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹_› (f := fun n ↦ f ((l + 1) * n)) fun {m n} hmn ↦
    (hf (Nat.mul_le_mul_left _ hmn)).mono (smul_top_mono_of_pow_le hl' m)
  refine ⟨L, fun n ↦ ?_⟩
  have h₁ : f n ≡ f ((l + 1) * ((k + 1) * n)) [SMOD (J ^ n • ⊤ : Submodule A M)] :=
    hf ((Nat.le_mul_of_pos_left n (Nat.succ_pos k)).trans
      (Nat.le_mul_of_pos_left _ (Nat.succ_pos l)))
  exact h₁.trans ((hL ((k + 1) * n)).mono (smul_top_mono_of_pow_le hk' n))

/-- The `I`-adic and `J`-adic completeness agree when `I ^ k ⊆ J` and `J ^ l ⊆ I`, i.e. when `I`
and `J` define the same topology: completeness only depends on the ideal of definition up to
this equivalence (EGA 0_I, §7.1). -/
theorem IsAdicComplete.of_pow_le {k l : ℕ} (hk : I ^ k ≤ J) (hl : J ^ l ≤ I)
    [IsAdicComplete I M] : IsAdicComplete J M where
  toIsHausdorff := .of_pow_le hl
  toIsPrecomplete := .of_pow_le hk hl

theorem isAdicComplete_iff_of_pow_le {k l : ℕ} (hk : I ^ k ≤ J) (hl : J ^ l ≤ I) :
    IsAdicComplete I M ↔ IsAdicComplete J M :=
  ⟨fun _ ↦ .of_pow_le hk hl, fun _ ↦ .of_pow_le hl hk⟩

/-- Over a noetherian ring, `I`-adic and `J`-adic completeness agree when `I` and `J` have the
same radical. -/
theorem isAdicComplete_iff_of_radical_eq [IsNoetherianRing A] (h : I.radical = J.radical) :
    IsAdicComplete I M ↔ IsAdicComplete J M := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (h ▸ Ideal.le_radical)
    (IsNoetherian.noetherian I)
  obtain ⟨l, hl⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (h.symm ▸ Ideal.le_radical)
    (IsNoetherian.noetherian J)
  exact isAdicComplete_iff_of_pow_le hk hl

end ChangeIdeal

/-! ### Nilpotent ideals -/

/-- Every module is complete for a nilpotent ideal. -/
theorem IsAdicComplete.of_pow_eq_bot {m : ℕ} (hm : I ^ m = ⊥) : IsAdicComplete I M := by
  have hle (n : ℕ) (hn : m ≤ n) : (I ^ n • ⊤ : Submodule A M) = ⊥ := by
    refine eq_bot_iff.mpr ((Submodule.smul_mono_left (Ideal.pow_le_pow_right hn)).trans ?_)
    rw [hm, Submodule.bot_smul]
  refine { toIsHausdorff := ⟨fun x hx ↦ ?_⟩, toIsPrecomplete := ⟨fun {f} hf ↦ ⟨f m, fun n ↦ ?_⟩⟩ }
  · have := hx m
    rwa [SModEq.zero, hle m le_rfl, Submodule.mem_bot] at this
  · rcases le_total n m with h | h
    · exact hf h
    · have := (hf h).symm
      rw [SModEq, Submodule.Quotient.eq, hle m le_rfl, Submodule.mem_bot, sub_eq_zero] at this
      rw [this]
