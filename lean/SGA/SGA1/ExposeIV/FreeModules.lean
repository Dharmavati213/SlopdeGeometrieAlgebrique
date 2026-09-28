/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import SGA.SGA1.ExposeIV.Graded

/-!
# SGA 1, Exposé IV, §4: relations with free modules

IV.4.1: if `I` is nilpotent, or if `A` is noetherian, `I` lies in the Jacobson radical and `M` is
finite, then `M` is free if and only if `M/IM` is free over `A/I` and `Tor₁^A(M, A/I) = 0`.
IV.4.2 replaces the `Tor₁` condition by the bijectivity of
`gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)`, and IV.4.3 specializes to `A/I` a field. IV.4.4 is
proved over a local domain, and in the generalization to reduced local rings left to the reader.
-/

universe u v

namespace SGA.SGA1.ExposeIV

open TensorProduct LinearMap Function

variable {A : Type u} [CommRing A] (I : Ideal A) {M : Type v} [AddCommGroup M] [Module A M]

section Nakayama

variable {N : Type*} [AddCommGroup N] [Module A N]

/-- Nakayama's lemma for a nilpotent ideal: `N' ⊔ I P = P` forces `N' ⊇ P`. -/
lemma le_of_le_sup_smul_of_isNilpotent (hI : IsNilpotent I) {N' P : Submodule A N}
    (h : P ≤ N' ⊔ I • P) : P ≤ N' := by
  have key (j : ℕ) : P ≤ N' ⊔ I ^ j • P := by
    induction j with
    | zero => simp
    | succ j ih =>
      calc P ≤ N' ⊔ I ^ j • P := ih
        _ ≤ N' ⊔ I ^ j • (N' ⊔ I • P) := sup_le_sup_left (Submodule.smul_mono le_rfl h) _
        _ ≤ N' ⊔ I ^ (j + 1) • P := by
          rw [Submodule.smul_sup, pow_succ, mul_smul, ← sup_assoc]
          exact sup_le_sup_right (sup_le le_rfl Submodule.smul_le_right) _
  obtain ⟨k, hk⟩ := hI
  simpa [hk] using key k

end Nakayama

section Construction

/-- Lifting a basis of `M/IM` gives a map `A^(ι) → M` which is bijective modulo `I`. -/
lemma exists_lTensor_linearCombination_bijective {ι : Type*}
    (b : Module.Basis ι (A ⧸ I) ((A ⧸ I) ⊗[A] M)) :
    ∃ e : ι → M, Bijective ((Finsupp.linearCombination A e).lTensor (A ⧸ I)) := by
  classical
  have hmk := TensorProduct.mk_surjective A M (A ⧸ I) Ideal.Quotient.mk_surjective
  choose e he using fun i ↦ hmk (b i)
  refine ⟨e, ?_⟩
  have h := Finsupp.linearCombination_one_tmul A (A ⧸ I) M ι (v := e)
  have hb : Finsupp.linearCombination (A ⧸ I) (fun i ↦ (1 : A ⧸ I) ⊗ₜ[A] e i) =
      Finsupp.linearCombination (A ⧸ I) b := by
    congr 1
    exact funext he
  rw [hb, ← Module.Basis.coe_repr_symm] at h
  have : ⇑((Finsupp.linearCombination A e).lTensor (A ⧸ I)) =
      b.repr.symm ∘ (finsuppScalarRight A A (A ⧸ I) ι) := by
    ext x
    have := congr($h (finsuppScalarRight A A (A ⧸ I) ι x))
    simpa using this.symm
  rw [this]
  exact b.repr.symm.bijective.comp (LinearEquiv.bijective _)

/-- A map `f : N → M` which is surjective modulo `I` is surjective, when Nakayama's lemma holds
for `M`. -/
lemma surjective_of_lTensor_surjective {N : Type*} [AddCommGroup N] [Module A N]
    (hM : ∀ N : Submodule A M, ⊤ ≤ N ⊔ I • ⊤ → ⊤ ≤ N) (f : N →ₗ[A] M)
    (hf : Surjective (f.lTensor (A ⧸ I))) : Surjective f := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine hM _ fun m _ ↦ ?_
  obtain ⟨z, hz⟩ := hf ((1 : A ⧸ I) ⊗ₜ m)
  obtain ⟨y, rfl⟩ := TensorProduct.mk_surjective A N (A ⧸ I) Ideal.Quotient.mk_surjective z
  have hmem : m - f y ∈ I • (⊤ : Submodule A M) := by
    rw [← LinearMap.ker_tensorProductMk, LinearMap.mem_ker, map_sub]
    simp only [TensorProduct.mk_apply] at hz ⊢
    rw [← hz, lTensor_tmul, sub_self]
  exact Submodule.mem_sup.2 ⟨f y, ⟨y, rfl⟩, m - f y, hmem, add_sub_cancel _ _⟩

/-- The construction in the proof of IV.4.1: lift a basis of `M/IM` to a map `A^(ι) → M`; it is
surjective by Nakayama, and its kernel `R` satisfies `R = IR` when `Tor₁^A(M, A/I) = 0`. -/
private theorem free_of_basis {ι : Type*} (b : Module.Basis ι (A ⧸ I) ((A ⧸ I) ⊗[A] M))
    (hT : TorOneVanishes A M (A ⧸ I))
    (hM : ∀ N : Submodule A M, ⊤ ≤ N ⊔ I • ⊤ → ⊤ ≤ N)
    (hL : ∀ R : Submodule A (ι →₀ A), R ≤ I • R → R = ⊥) : Module.Free A M := by
  obtain ⟨e, hf⟩ := exists_lTensor_linearCombination_bijective I b
  let f : (ι →₀ A) →ₗ[A] M := Finsupp.linearCombination A e
  have hsurj : Surjective f := surjective_of_lTensor_surjective I hM f hf.2
  -- the kernel `R` of `f` satisfies `R ⊆ I R`, hence vanishes
  let R := LinearMap.ker f
  have hR : Injective (R.subtype.lTensor (A ⧸ I)) := by
    rw [LinearMap.lTensor_inj_iff_rTensor_inj]
    exact (torOneVanishes_iff_rTensor_injective (N := A ⧸ I) R.subtype f R.injective_subtype
      (LinearMap.exact_subtype_ker_map f) hsurj).1 hT
  have hRI : R ≤ I • R := by
    intro r hr
    have h1 : (1 : A ⧸ I) ⊗ₜ[A] (⟨r, hr⟩ : R) = 0 := by
      apply hR
      rw [map_zero, lTensor_tmul, Submodule.subtype_apply]
      apply hf.1
      rw [map_zero, lTensor_tmul, LinearMap.mem_ker.1 hr, tmul_zero]
    have h2 : (⟨r, hr⟩ : R) ∈ I • (⊤ : Submodule A R) := by
      rw [← LinearMap.ker_tensorProductMk]
      exact h1
    have := Submodule.mem_map_of_mem (f := R.subtype) h2
    rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at this
  have hinj : Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact hL R hRI
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

end Construction

section Criteria

/-- IV.4.1 (a): for a nilpotent ideal `I`, `M` is free if and only if `M/IM` is free over `A/I`
and `Tor₁^A(M, A/I) = 0`. -/
theorem free_iff_of_isNilpotent (hI : IsNilpotent I) :
    Module.Free A M ↔ Module.Free (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧ TorOneVanishes A M (A ⧸ I) := by
  refine ⟨fun _ ↦ ⟨inferInstance, torOneVanishes_of_flat _⟩, fun ⟨hF, hT⟩ ↦ ?_⟩
  refine free_of_basis I (Module.Free.chooseBasis (A ⧸ I) ((A ⧸ I) ⊗[A] M)) hT
    (fun N h ↦ le_of_le_sup_smul_of_isNilpotent I hI h) fun R h ↦ ?_
  exact eq_bot_iff.2 (le_of_le_sup_smul_of_isNilpotent I hI (by simpa using h))

/-- IV.4.1 (b): for `A` noetherian, `I` in the Jacobson radical and `M` finite, `M` is free if
and only if `M/IM` is free over `A/I` and `Tor₁^A(M, A/I) = 0`. -/
theorem free_iff_of_le_jacobson [IsNoetherianRing A] [Module.Finite A M]
    (hI : I ≤ Ideal.jacobson ⊥) :
    Module.Free A M ↔ Module.Free (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧ TorOneVanishes A M (A ⧸ I) := by
  refine ⟨fun _ ↦ ⟨inferInstance, torOneVanishes_of_flat _⟩, fun ⟨hF, hT⟩ ↦ ?_⟩
  let b := Module.Free.chooseBasis (A ⧸ I) ((A ⧸ I) ⊗[A] M)
  have : Finite (Module.Free.ChooseBasisIndex (A ⧸ I) ((A ⧸ I) ⊗[A] M)) := inferInstance
  refine free_of_basis I b hT
    (fun N h ↦ Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI h)
    fun R h ↦ Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I R (IsNoetherian.noetherian R) h hI

/-- Krull: a finite module over a noetherian ring is `I`-adically separated for `I` in the
Jacobson radical. -/
lemma eq_zero_of_forall_mem_pow_smul_of_le_jacobson [IsNoetherianRing A]
    (hI : I ≤ Ideal.jacobson ⊥) {X : Type*} [AddCommGroup X] [Module A X] [Module.Finite A X]
    {x : X} (hx : ∀ k, x ∈ I ^ k • (⊤ : Submodule A X)) : x = 0 := by
  have hmem : x ∈ ⨅ k, I ^ k • (⊤ : Submodule A X) := Submodule.mem_iInf _ |>.2 hx
  rwa [Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _ hI, Submodule.mem_bot] at hmem

/-- IV.4.2 (a): for a nilpotent ideal `I`, one may replace `Tor₁^A(M, A/I) = 0` in IV.4.1 by the
bijectivity of `gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)`. -/
theorem free_iff_grMapInjective_of_isNilpotent (hI : IsNilpotent I) :
    Module.Free A M ↔ Module.Free (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧ GrMapInjective I M := by
  refine ⟨fun _ ↦ ⟨inferInstance, grMapInjective_of_torOneVanishes fun n _ ↦
    torOneVanishes_of_flat _⟩, fun ⟨hF, hG⟩ ↦ ?_⟩
  have hT := torOneVanishes_of_grMapInjective_of_isNilpotent hI hG 1
  rw [pow_one] at hT
  exact (free_iff_of_isNilpotent I hI).2 ⟨hF, hT⟩

/-- IV.4.2 (b): for `A` noetherian, `I` in the Jacobson radical and `M` finite, one may replace
`Tor₁^A(M, A/I) = 0` in IV.4.1 by the bijectivity of `gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)`. -/
theorem free_iff_grMapInjective_of_le_jacobson [IsNoetherianRing A] [Module.Finite A M]
    (hI : I ≤ Ideal.jacobson ⊥) :
    Module.Free A M ↔ Module.Free (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧ GrMapInjective I M := by
  refine ⟨fun _ ↦ ⟨inferInstance, grMapInjective_of_torOneVanishes fun n _ ↦
    torOneVanishes_of_flat _⟩, fun ⟨hF, hG⟩ ↦ ?_⟩
  have hT := torOneVanishes_of_grMapInjective hG 1 fun y hy ↦
    eq_zero_of_forall_mem_pow_smul_of_le_jacobson I hI hy
  rw [pow_one] at hT
  exact (free_iff_of_le_jacobson I hI).2 ⟨hF, hT⟩

/-- A module over the field `A/I` is free. -/
lemma free_quotient_of_isMaximal [I.IsMaximal] (N : Type*) [AddCommGroup N]
    [Module (A ⧸ I) N] : Module.Free (A ⧸ I) N := by
  let := Ideal.Quotient.field I
  infer_instance

variable (M)

/-- IV.4.3 (a): if `A/I` is a field and `I` is nilpotent (e.g. `A` artinian local), the following
are equivalent for an arbitrary module `M`: free, projective, flat, `Tor₁^A(M, A/I) = 0`, and the
bijectivity of `gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)`. -/
theorem free_tfae_of_isNilpotent [I.IsMaximal] (hI : IsNilpotent I) : List.TFAE
    [Module.Free A M, Module.Projective A M, Module.Flat A M, TorOneVanishes A M (A ⧸ I),
      GrMapInjective I M] := by
  have hF := free_quotient_of_isMaximal I ((A ⧸ I) ⊗[A] M)
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 → 3 := fun _ ↦ inferInstance
  tfae_have 3 → 4 := fun _ ↦ torOneVanishes_of_flat _
  tfae_have 4 → 1 := fun hT ↦ (free_iff_of_isNilpotent I hI).2 ⟨hF, hT⟩
  tfae_have 1 ↔ 5 := by
    rw [free_iff_grMapInjective_of_isNilpotent I hI]
    exact ⟨And.right, fun h ↦ ⟨hF, h⟩⟩
  tfae_finish

/-- IV.4.3 (b): if `A` is noetherian, `A/I` is a field, `I` lies in the Jacobson radical (so `A`
is local with maximal ideal `I`) and `M` is finite, the following are equivalent: free,
projective, flat, `Tor₁^A(M, A/I) = 0`, and the bijectivity of
`gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)`. -/
theorem free_tfae_of_le_jacobson [IsNoetherianRing A] [Module.Finite A M] [I.IsMaximal]
    (hI : I ≤ Ideal.jacobson ⊥) : List.TFAE
    [Module.Free A M, Module.Projective A M, Module.Flat A M, TorOneVanishes A M (A ⧸ I),
      GrMapInjective I M] := by
  have hF := free_quotient_of_isMaximal I ((A ⧸ I) ⊗[A] M)
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 → 3 := fun _ ↦ inferInstance
  tfae_have 3 → 4 := fun _ ↦ torOneVanishes_of_flat _
  tfae_have 4 → 1 := fun hT ↦ (free_iff_of_le_jacobson I hI).2 ⟨hF, hT⟩
  tfae_have 1 ↔ 5 := by
    rw [free_iff_grMapInjective_of_le_jacobson I hI]
    exact ⟨And.right, fun h ↦ ⟨hF, h⟩⟩
  tfae_finish

end Criteria

section Domain

open IsLocalRing Module

variable (M) in
/-- IV.4.4: over a noetherian local integral domain `A` with residue field `k = A/𝔪` and field of
fractions `K`, a finite module `M` is free if and only if `M ⊗_A K` and `M ⊗_A k` have the same
dimension. -/
theorem free_iff_finrank_eq [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [Module.Finite A M] :
    Module.Free A M ↔ finrank (FractionRing A) (FractionRing A ⊗[A] M) =
      finrank (A ⧸ maximalIdeal A) ((A ⧸ maximalIdeal A) ⊗[A] M) := by
  let := Ideal.Quotient.field (maximalIdeal A)
  constructor
  · intro _
    rw [Module.finrank_baseChange, Module.finrank_baseChange]
  · intro h
    let b := Module.finBasis (A ⧸ maximalIdeal A) ((A ⧸ maximalIdeal A) ⊗[A] M)
    obtain ⟨e, hf⟩ := exists_lTensor_linearCombination_bijective (maximalIdeal A) b
    let f := Finsupp.linearCombination A e
    have hsurj : Surjective f := surjective_of_lTensor_surjective (maximalIdeal A)
      (fun N h ↦ Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
        (maximalIdeal_le_jacobson _) h) f hf.2
    -- over `K`, `K^n → M ⊗ K` is a surjection between spaces of the same dimension
    have hK : Injective (f.baseChange (FractionRing A)) := by
      rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
      · simpa [LinearMap.baseChange_eq_ltensor] using
          LinearMap.lTensor_surjective (FractionRing A) hsurj
      · rw [Module.finrank_baseChange, Module.finrank_finsupp_self, Fintype.card_fin, h]
    have hinj : Injective f := by
      rw [injective_iff_map_eq_zero]
      intro r hr
      apply Module.Flat.tensorProduct_mk_injective A (Fin _ →₀ A) (FractionRing A)
      apply hK
      simp [LinearMap.baseChange_tmul, hr]
    exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

variable (M) in
/-- IV.4.4, the generalization left to the reader: over a local ring `A` without nilpotent
elements, a finite module `M` is free if and only if its rank at every minimal prime `𝔭`,
`dim_{κ(𝔭)} M ⊗_A κ(𝔭)`, equals `dim_k M ⊗_A k` (`k = A/𝔪`). SGA assumes `A` noetherian, which
is not needed. (For a minimal prime `𝔭` of a reduced ring, `A_𝔭 = κ(𝔭)` is a field.) -/
theorem free_iff_forall_minimalPrimes_finrank_eq [IsLocalRing A] [IsReduced A]
    [Module.Finite A M] :
    Module.Free A M ↔ ∀ (p : Ideal A) [p.IsPrime], p ∈ minimalPrimes A →
      finrank p.ResidueField (p.ResidueField ⊗[A] M) =
      finrank (A ⧸ maximalIdeal A) ((A ⧸ maximalIdeal A) ⊗[A] M) := by
  let := Ideal.Quotient.field (maximalIdeal A)
  constructor
  · intro _ p _ _
    rw [Module.finrank_baseChange, Module.finrank_baseChange]
  · intro h
    let b := Module.finBasis (A ⧸ maximalIdeal A) ((A ⧸ maximalIdeal A) ⊗[A] M)
    obtain ⟨e, hf⟩ := exists_lTensor_linearCombination_bijective (maximalIdeal A) b
    let f := Finsupp.linearCombination A e
    have hsurj : Surjective f := surjective_of_lTensor_surjective (maximalIdeal A)
      (fun N h ↦ Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
        (maximalIdeal_le_jacobson _) h) f hf.2
    -- at a minimal prime, `κ(𝔭)^n → M ⊗ κ(𝔭)` is a surjection between spaces of equal dimension
    have hmem (r : Fin (finrank (A ⧸ maximalIdeal A) ((A ⧸ maximalIdeal A) ⊗[A] M)) →₀ A)
        (hr : f r = 0) (i) (p : Ideal A) [p.IsPrime] (hp : p ∈ minimalPrimes A) : r i ∈ p := by
      have hK : Injective (f.baseChange p.ResidueField) := by
        rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
        · simpa [LinearMap.baseChange_eq_ltensor] using
            LinearMap.lTensor_surjective p.ResidueField hsurj
        · rw [Module.finrank_baseChange, Module.finrank_finsupp_self, Fintype.card_fin, h p hp]
      have h1 : (1 : p.ResidueField) ⊗ₜ[A] r = 0 := hK (by simp [LinearMap.baseChange_tmul, hr])
      have h2 := congr($(congrArg (finsuppScalarRight A p.ResidueField p.ResidueField _) h1) i)
      rw [finsuppScalarRight_apply_tmul_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply,
        Algebra.smul_def, mul_one] at h2
      exact (Ideal.algebraMap_residueField_eq_zero).1 h2
    have hinj : Injective f := by
      rw [injective_iff_map_eq_zero]
      intro r hr
      ext i
      have : r i ∈ sInf (minimalPrimes A) := Submodule.mem_sInf.2 fun p hp ↦ by
        have : Ideal.IsPrime (p : Ideal A) := hp.1.1
        exact hmem r hr i p hp
      rw [minimalPrimes, Ideal.sInf_minimalPrimes] at this
      exact (mem_nilradical.1 this).eq_zero
    exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

end Domain

end SGA.SGA1.ExposeIV
