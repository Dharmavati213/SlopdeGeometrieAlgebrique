/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.Finite.Basic
import SGA.SGA1.ExposeXI.AbelianVarietyQuotient

/-!
# SGA 1, Exposé XI.2.1: the `ℓ`-primary component of `π₁(A)` is `T_ℓ(A)`

XI.2.1 ends: "hence for every prime number `ℓ`, the `ℓ`-primary component of `π₁(A)` is
canonically isomorphic to `T_ℓ(A) = lim_r K_{ℓ^r}`" (`AbelianVarietyPrimaryComponentStatement`).
This file states it and derives it from the first part (`AbelianVarietyFundamentalGroupConclusion`):

* `primaryComponent P ℓ`: the `ℓ`-primary elements of a topological group `P`, those `x` with
  some `x^{ℓ^r}` in every open subgroup (for a discrete torsion group these are the elements of
  `ℓ`-power order, mathlib's `CommGroup.primaryComponent`). Continuous homomorphisms preserve
  them (`image_primaryComponent_subset`). In a compact commutative group they form a closed set
  (`isClosed_primaryComponent`), and the subgroup they generate for all `ℓ` meets every coset of
  an open subgroup (`exists_mem_inv_mul_mem_of_primaryComponent_subset`): the group is the product
  of its `ℓ`-primary components;
* `tateModuleAt G ℓ`: `T_ℓ(G) = lim_r K_{ℓ^r}`; the projection `T(G) → T_ℓ(G)`,
  `x ↦ (x_{ℓ^r})_r` (`tateModuleToAt`), and its section `tateModuleOfAt` onto the `ℓ`-primary
  component of `T(G)` (`range_tateModuleOfAt`). For `n = ℓ^v m` with `ℓ ∤ m`, the `n`-th component
  of the image of `y` is `y_v^c` with `c m ≡ 1 mod ℓ^v` (`c = m^{φ(ℓ^v) - 1}`, Euler);
* `exists_primePow_lift` (every characteristic): by Serre–Lang, every point `y` of the fibre of
  an étale covering `Y` is reached from a lift of some `(ℓ^a)_A` through the pull-back of `Y`
  along `m_A`, `ℓ ∤ m`, on whose fibre `π₁(A, 0)` acts through `τ ↦ τ^m`. Hence two `ℓ`-primary
  elements of `π₁(A, 0)` which agree on all lifts of the `(ℓ^r)_A` are equal
  (`eq_of_forall_primePow_lift`), and the isomorphism of the `ℓ`-primary clause is unique: it is
  `T_ℓ(A) → T(A) → π₁(A, 0)` (`eq_tateModuleToFundamentalGroup_comp_tateModuleOfAt`);
* `abelianVarietyPrimaryComponent_of_conclusion`: the first part of XI.2.1 implies its
  `ℓ`-primary form. Hence the `ℓ`-primary form in characteristic `0`
  (`abelianVarietyPrimaryComponent_of_charZero`) and from SGA's cited fact that `n_A` is an
  isogeny (`abelianVarietyPrimaryComponentStatement_of_mulNIsogeny`).

The `ℓ`-primary form for `ℓ` invertible in `k` is proved with no further input in
`TateModulePrimeToP`. The converse (all the `ℓ`-primary clauses imply the first part) and SGA's
`T(A) = ∏_ℓ T_ℓ(A)` are in `TateModuleProduct`.
-/

universe u v

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  PreGaloisCategory

namespace SGA.SGA1.ExposeXI

section PrimaryComponent

variable (P : Type*) [Group P] [TopologicalSpace P]

/-- The `ℓ`-primary elements of a topological group `P`: the `x` such that, for every open
subgroup `U`, some `x^{ℓ^r}` lies in `U`. For a profinite abelian group `P` these form its
`ℓ`-primary component (the `ℓ`-Sylow subgroup, `lim (P/U)_ℓ`). -/
def primaryComponent (ℓ : ℕ) : Set P :=
  {x | ∀ U : OpenSubgroup P, ∃ r : ℕ, x ^ ℓ ^ r ∈ U}

variable {P}

/-- Continuous homomorphisms preserve the `ℓ`-primary elements. -/
lemma image_primaryComponent_subset {Q : Type*} [Group Q] [TopologicalSpace Q] (f : P →* Q)
    (hf : Continuous f) (ℓ : ℕ) : f '' primaryComponent P ℓ ⊆ primaryComponent Q ℓ := by
  rintro _ ⟨x, hx, rfl⟩ U
  obtain ⟨r, hr⟩ := hx (U.comap f hf)
  exact ⟨r, by rwa [OpenSubgroup.mem_comap, map_pow] at hr⟩

/-- Isomorphisms of topological groups preserve the `ℓ`-primary elements. -/
lemma image_primaryComponent {Q : Type*} [Group Q] [TopologicalSpace Q] (e : P ≃ₜ* Q)
    (ℓ : ℕ) : e '' primaryComponent P ℓ = primaryComponent Q ℓ := by
  refine (image_primaryComponent_subset (e : P →* Q) e.continuous ℓ).antisymm
    fun y hy ↦ ⟨e.symm y, ?_, by simp⟩
  exact image_primaryComponent_subset (e.symm : Q →* P) e.symm.continuous ℓ ⟨y, hy, rfl⟩

omit [TopologicalSpace P] in
/-- If `x^a` and `x^b` lie in a subgroup `H`, so does `x^{gcd(a, b)}` (Bézout). -/
private lemma pow_gcd_mem (H : Subgroup P) {x : P} {a b : ℕ} (ha : x ^ a ∈ H)
    (hb : x ^ b ∈ H) : x ^ Nat.gcd a b ∈ H := by
  have : x ^ Nat.gcd a b = (x ^ a) ^ Nat.gcdA a b * (x ^ b) ^ Nat.gcdB a b := by
    rw [← zpow_natCast, ← zpow_natCast x a, ← zpow_natCast x b, ← zpow_mul, ← zpow_mul,
      ← zpow_add, Nat.gcd_eq_gcd_ab]
  rw [this]
  exact H.mul_mem (H.zpow_mem ha _) (H.zpow_mem hb _)

/-- In a commutative topological group `P` acting on `X`, two `ℓ`-primary elements whose `m`-th
powers agree at a point `x` with open stabilizer agree at `x`, for `m` prime to `ℓ`. -/
lemma smul_eq_of_pow_smul_eq {X : Type*} [MulAction P X] (hcomm : ∀ a b : P, a * b = b * a)
    {x : X} (hx : IsOpen (MulAction.stabilizer P x : Set P)) {ℓ m : ℕ} (hm : m.Coprime ℓ)
    {σ τ : P} (hσ : σ ∈ primaryComponent P ℓ) (hτ : τ ∈ primaryComponent P ℓ)
    (h : σ ^ m • x = τ ^ m • x) : σ • x = τ • x := by
  let H := MulAction.stabilizer P x
  obtain ⟨b₁, hb₁⟩ := hσ ⟨H, hx⟩
  obtain ⟨b₂, hb₂⟩ := hτ ⟨H, hx⟩
  have hδ (n : ℕ) : (σ⁻¹ * τ) ^ n = (σ ^ n)⁻¹ * τ ^ n := by
    rw [Commute.mul_pow (hcomm σ⁻¹ τ) n, inv_pow]
  have h₁ : (σ⁻¹ * τ) ^ m ∈ H := by
    rw [hδ, MulAction.mem_stabilizer_iff, mul_smul, ← h, ← mul_smul, inv_mul_cancel, one_smul]
  have h₂ : (σ⁻¹ * τ) ^ ℓ ^ (b₁ + b₂) ∈ H := by
    rw [hδ, pow_add, pow_mul, pow_mul']
    exact H.mul_mem (H.inv_mem (H.pow_mem hb₁ _)) (H.pow_mem hb₂ _)
  have h₃ := pow_gcd_mem H h₁ h₂
  rw [(hm.pow_right (b₁ + b₂)).gcd_eq_one, pow_one] at h₃
  have : σ⁻¹ • τ • x = x := by rw [← mul_smul]; exact h₃
  exact (inv_smul_eq_iff.mp this).symm

section Compact

variable [IsTopologicalGroup P] [CompactSpace P] (hcomm : ∀ a b : P, a * b = b * a)
include hcomm

/-- In a compact commutative group the open subgroups are normal of finite index. -/
private lemma normal_and_index_ne_zero (U : OpenSubgroup P) :
    (U : Subgroup P).Normal ∧ (U : Subgroup P).index ≠ 0 := by
  have : Finite (P ⧸ (U : Subgroup P)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  exact ⟨⟨fun n hn g ↦ by rwa [hcomm g n, mul_inv_cancel_right]⟩,
    Subgroup.index_ne_zero_of_finite⟩

/-- In a compact commutative group, an `ℓ`-primary element `x` satisfies `x^{ℓ^v} ∈ U` for every
open subgroup `U`, where `ℓ^v` is the `ℓ`-part of the (finite) index of `U`. -/
lemma pow_mem_of_mem_primaryComponent {ℓ : ℕ} (hℓ : ℓ.Prime) {x : P}
    (hx : x ∈ primaryComponent P ℓ) (U : OpenSubgroup P) :
    x ^ ℓ ^ (U : Subgroup P).index.factorization ℓ ∈ U := by
  obtain ⟨_, hd⟩ := normal_and_index_ne_zero hcomm U
  obtain ⟨r, hr⟩ := hx U
  have h := pow_gcd_mem (U : Subgroup P) hr ((U : Subgroup P).pow_index_mem x)
  obtain ⟨j, -, hjeq⟩ :=
    (Nat.dvd_prime_pow hℓ).mp (Nat.gcd_dvd_left (ℓ ^ r) (U : Subgroup P).index)
  have hjv : j ≤ (U : Subgroup P).index.factorization ℓ :=
    (hℓ.pow_dvd_iff_le_factorization hd).mp (hjeq ▸ Nat.gcd_dvd_right _ _)
  rw [hjeq] at h
  rw [← Nat.sub_add_cancel hjv, pow_add, pow_mul']
  exact (U : Subgroup P).pow_mem h _

/-- In a compact commutative group the `ℓ`-primary elements form a closed set. -/
lemma isClosed_primaryComponent {ℓ : ℕ} (hℓ : ℓ.Prime) : IsClosed (primaryComponent P ℓ) := by
  have : primaryComponent P ℓ = ⋂ U : OpenSubgroup P,
      (fun x : P ↦ x ^ ℓ ^ (U : Subgroup P).index.factorization ℓ) ⁻¹' (U : Set P) := by
    ext x
    exact ⟨fun hx ↦ Set.mem_iInter.mpr fun U ↦ pow_mem_of_mem_primaryComponent hcomm hℓ hx U,
      fun hx U ↦ ⟨_, Set.mem_iInter.mp hx U⟩⟩
  rw [this]
  exact isClosed_iInter fun U ↦ U.isClosed.preimage (continuous_pow _)

/-- In a compact commutative group, an element `σ` with `σ^{ℓ^v}` in an open subgroup `U` is
congruent modulo `U` to an `ℓ`-primary element. For finitely many open subgroups `V`, the power
`σ^e`, with `e ≡ 1 mod ℓ^v` divisible by the prime-to-`ℓ` parts of their indices, is
`ℓ`-primary modulo each `V`; then compactness. -/
lemma exists_mem_primaryComponent_inv_mul_mem {ℓ : ℕ} (hℓ : ℓ.Prime) {σ : P}
    (U : OpenSubgroup P) {v : ℕ} (hv : σ ^ ℓ ^ v ∈ U) :
    ∃ τ ∈ primaryComponent P ℓ, σ⁻¹ * τ ∈ U := by
  let C : OpenSubgroup P → Set P := fun V ↦
    (fun x : P ↦ x ^ ℓ ^ (V : Subgroup P).index.factorization ℓ) ⁻¹' (V : Set P)
  have hC (V : OpenSubgroup P) : IsClosed (C V) := V.isClosed.preimage (continuous_pow _)
  let D : Set P := (fun x : P ↦ σ⁻¹ * x) ⁻¹' (U : Set P)
  have hD : IsCompact D := (U.isClosed.preimage (continuous_const_mul σ⁻¹)).isCompact
  have hDC (u : Finset (OpenSubgroup P)) : (D ∩ ⋂ V ∈ u, C V).Nonempty := by
    obtain ⟨M, hMdef⟩ : ∃ M, ∏ V ∈ u, ordCompl[ℓ] (V : Subgroup P).index = M := ⟨_, rfl⟩
    have hM : M.Coprime ℓ := hMdef ▸ Nat.Coprime.prod_left fun V _ ↦
      (Nat.coprime_ordCompl hℓ (normal_and_index_ne_zero hcomm V).2).symm
    obtain ⟨e, hedef⟩ : ∃ e, M ^ Nat.totient (ℓ ^ v) = e := ⟨_, rfl⟩
    have he : e ≡ 1 [MOD ℓ ^ v] := hedef ▸ Nat.ModEq.pow_totient (hM.pow_right v)
    have hMe : M ∣ e := hedef ▸ dvd_pow_self M (Nat.totient_pos.mpr (pow_pos hℓ.pos v)).ne'
    have he1 : 1 ≤ e := by
      rw [← hedef]
      refine Nat.one_le_pow _ _ (Nat.pos_of_ne_zero ?_)
      rintro rfl
      exact hℓ.one_lt.ne' ((Nat.coprime_zero_left _).mp hM)
    refine ⟨σ ^ e, ?_, Set.mem_iInter₂.mpr fun V hV ↦ ?_⟩
    · -- `σ^e ≡ σ` modulo `U`, since `e ≡ 1 mod ℓ^v`
      obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' he1).mp he.symm
      change σ⁻¹ * σ ^ e ∈ U
      rw [← Nat.sub_add_cancel he1, pow_succ', inv_mul_cancel_left, ht, pow_mul]
      exact pow_mem hv t
    · -- `σ^{e ℓ^w}` is a power of `σ^{[P : V]}`, where `ℓ^w` is the `ℓ`-part of `[P : V]`
      obtain ⟨hn, -⟩ := normal_and_index_ne_zero hcomm V
      have hVM : ordCompl[ℓ] (V : Subgroup P).index ∣ M :=
        hMdef ▸ Finset.dvd_prod_of_mem
          (fun V : OpenSubgroup P ↦ ordCompl[ℓ] (V : Subgroup P).index) hV
      have hdvd : (V : Subgroup P).index ∣ e * ℓ ^ (V : Subgroup P).index.factorization ℓ := by
        conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (V : Subgroup P).index ℓ]
        rw [mul_comm e]
        exact mul_dvd_mul_left _ (hVM.trans hMe)
      obtain ⟨s, hs⟩ := hdvd
      change (σ ^ e) ^ ℓ ^ (V : Subgroup P).index.factorization ℓ ∈ V
      rw [← pow_mul, hs, pow_mul]
      exact (V : Subgroup P).pow_mem ((V : Subgroup P).pow_index_mem σ) s
  obtain ⟨τ, hτD, hτC⟩ := hD.inter_iInter_nonempty C hC hDC
  exact ⟨τ, fun V ↦ ⟨_, Set.mem_iInter.mp hτC V⟩, hτD⟩

/-- A compact commutative group is the product of its `ℓ`-primary components, in the following
form: a subgroup `H` containing the `ℓ`-primary elements for every prime `ℓ` meets every coset
`σ U` of an open subgroup `U` (so `H` is dense). By induction on `N` with `σ^N ∈ U`: write
`N = ℓ^v m` with `ℓ ∤ m` and `σ = σ₁ σ₂` with `σ₁^{ℓ^v}, σ₂^m ∈ U` (Bézout). -/
lemma exists_mem_inv_mul_mem_of_primaryComponent_subset (H : Subgroup P)
    (hH : ∀ ℓ : ℕ, ℓ.Prime → primaryComponent P ℓ ⊆ H) (σ : P) (U : OpenSubgroup P) :
    ∃ ρ ∈ H, σ⁻¹ * ρ ∈ U := by
  obtain ⟨_, hd⟩ := normal_and_index_ne_zero hcomm U
  suffices key : ∀ N : ℕ, 0 < N → ∀ σ : P, σ ^ N ∈ U → ∃ ρ ∈ H, σ⁻¹ * ρ ∈ U from
    key _ (Nat.pos_of_ne_zero hd) σ ((U : Subgroup P).pow_index_mem σ)
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN σ hσ
  rcases Nat.lt_or_ge N 2 with h1 | h2
  · obtain rfl : N = 1 := by omega
    exact ⟨1, H.one_mem, by rw [_root_.mul_one]; exact inv_mem (by simpa using hσ)⟩
  set ℓ := N.minFac
  have hℓ : ℓ.Prime := Nat.minFac_prime (by omega)
  obtain ⟨v, hvdef⟩ : ∃ v, N.factorization ℓ = v := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m, ordCompl[ℓ] N = m := ⟨_, rfl⟩
  have hNm : ℓ ^ v * m = N := by rw [← hvdef, ← hmdef]; exact Nat.ordProj_mul_ordCompl_eq_self N ℓ
  have hv : 0 < v := hvdef ▸ hℓ.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd N)
  have hm0 : 0 < m := hmdef ▸ Nat.ordCompl_pos ℓ (by omega)
  have hmN : m < N := by
    rw [← hNm]
    exact lt_mul_left hm0 (Nat.one_lt_pow hv.ne' hℓ.one_lt)
  have hcop : Nat.Coprime (ℓ ^ v) m :=
    hmdef ▸ (Nat.coprime_ordCompl hℓ (by omega)).pow_left v
  obtain ⟨α, β, hαβ⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  -- `σ = σ₁ σ₂` with `σ₁ = σ^{β m}`, `σ₂ = σ^{α ℓ^v}`
  have hpow (γ : ℤ) (a b : ℕ) (hab : a * b = N) :
      (σ ^ (γ * a)) ^ b = (σ ^ N) ^ γ := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast σ N, ← zpow_mul, ← hab]
    congr 1
    push_cast
    ring
  have h₁ : (σ ^ (β * (m : ℤ))) ^ ℓ ^ v ∈ U := by
    rw [hpow β m (ℓ ^ v) (by rw [mul_comm, hNm])]
    exact zpow_mem hσ β
  have h₂ : (σ ^ (α * ((ℓ ^ v : ℕ) : ℤ))) ^ m ∈ U := by
    rw [hpow α (ℓ ^ v) m hNm]
    exact zpow_mem hσ α
  obtain ⟨τ, hτ, hτU⟩ := exists_mem_primaryComponent_inv_mul_mem hcomm hℓ U h₁
  obtain ⟨ρ, hρ, hρU⟩ := ih m hmN hm0 _ h₂
  refine ⟨τ * ρ, H.mul_mem (hH ℓ hℓ hτ) hρ, ?_⟩
  have hσ12 : σ = σ ^ (β * (m : ℤ)) * σ ^ (α * ((ℓ ^ v : ℕ) : ℤ)) := by
    rw [← zpow_add, add_comm, hαβ, zpow_one]
  have : σ⁻¹ * (τ * ρ) =
      ((σ ^ (β * (m : ℤ)))⁻¹ * τ) * ((σ ^ (α * ((ℓ ^ v : ℕ) : ℤ)))⁻¹ * ρ) := by
    conv_lhs => rw [hσ12]
    rw [mul_inv_rev, _root_.mul_assoc, ← _root_.mul_assoc _ τ ρ,
      ← _root_.mul_assoc (σ ^ (α * _))⁻¹, hcomm (σ ^ (α * _))⁻¹]
    simp only [_root_.mul_assoc]
  rw [this]
  exact mul_mem hτU hρU

end Compact

end PrimaryComponent

section TateModuleAt

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  (G : C) [GrpObj G] [IsCommMonObj G]

/-- XI.2.1: `T_ℓ(G) = lim_r K_{ℓ^r}`, the families `(y_r)_{r ≥ 0}` of `ℓ^r`-torsion points with
`y_{r+1}^ℓ = y_r`, with the subspace topology of the product of the discrete groups `K_{ℓ^r}`. -/
def tateModuleAt (ℓ : ℕ) : Subgroup ((r : ℕ) → torsionPoints G (ℓ ^ r)) where
  carrier := {y | ∀ r, ((y (r + 1) : 𝟙_ C ⟶ G)) ^ ℓ = y r}
  mul_mem' := by
    intro a b ha hb r
    simp only [Pi.mul_apply, Subgroup.coe_mul, mul_pow, ha r, hb r]
  one_mem' := by intro r; simp
  inv_mem' := by
    intro a ha r
    simp only [Pi.inv_apply, Subgroup.coe_inv, inv_pow, ha r]

variable {G}

lemma pow_tateModuleAt {ℓ : ℕ} (y : tateModuleAt G ℓ) (r a : ℕ) :
    ((y.1 (r + a) : 𝟙_ C ⟶ G)) ^ (ℓ ^ a) = y.1 r := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', pow_mul, ← ih]
    exact congrArg (· ^ ℓ ^ a) (y.2 (r + a))

lemma pow_tateModuleAt_self {ℓ : ℕ} (y : tateModuleAt G ℓ) (r : ℕ) :
    ((y.1 r : 𝟙_ C ⟶ G)) ^ (ℓ ^ r) = 1 :=
  (mem_torsionPoints G).mp (y.1 r).2

lemma tateModule_apply_congr (x : tateModule G) {a b : ℕ+} (h : a = b) :
    ((x.1 a : 𝟙_ C ⟶ G)) = x.1 b := by
  subst h
  rfl

lemma tateModuleAt_apply_congr {ℓ : ℕ} (y : tateModuleAt G ℓ) {a b : ℕ} (h : a = b) :
    ((y.1 a : 𝟙_ C ⟶ G)) = y.1 b := by
  subst h
  rfl

/-- The component `y_0 ∈ K_1` of `y ∈ T_ℓ(G)` is trivial. -/
lemma tateModuleAt_apply_zero {ℓ : ℕ} (y : tateModuleAt G ℓ) : y.1 0 = 1 := by
  apply Subtype.ext
  have : ((y.1 0 : 𝟙_ C ⟶ G)) ^ 1 = 1 := pow_tateModuleAt_self y 0
  rwa [pow_one] at this

variable {ℓ : ℕ}

/-- If every `K_{ℓ^r}` is finite, `T_ℓ(G)` is compact. -/
lemma compactSpace_tateModuleAt (hfin : ∀ r : ℕ, Finite (torsionPoints G (ℓ ^ r))) :
    CompactSpace (tateModuleAt G ℓ) := by
  have hcl : IsClosed (tateModuleAt G ℓ : Set ((r : ℕ) → torsionPoints G (ℓ ^ r))) := by
    have : (tateModuleAt G ℓ : Set ((r : ℕ) → torsionPoints G (ℓ ^ r))) = ⋂ r : ℕ,
        (fun y : (r : ℕ) → torsionPoints G (ℓ ^ r) ↦ (y (r + 1), y r)) ⁻¹'
          {q | (q.1 : 𝟙_ C ⟶ G) ^ ℓ = q.2} := by
      ext y
      simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
      rfl
    rw [this]
    exact isClosed_iInter fun r ↦ (isClosed_discrete _).preimage
      ((continuous_apply _).prodMk (continuous_apply _))
  exact isCompact_iff_compactSpace.mp hcl.isCompact

/-- If every point of `G` has an `ℓ`-th root, every `a ∈ K_{ℓ^r}` is the `r`-th component of an
element of `T_ℓ(G)`: choose successive `ℓ`-th roots `L_s` of `a` (`L_s^{ℓ^s} = a`) and take
`y_s = L_s^{ℓ^r}`. -/
lemma exists_tateModuleAt_apply_eq (hdiv : ∀ a : 𝟙_ C ⟶ G, ∃ b, b ^ ℓ = a) (r : ℕ)
    (a : torsionPoints G (ℓ ^ r)) : ∃ y : tateModuleAt G ℓ, y.1 r = a := by
  choose d hd using hdiv
  let L : ℕ → (𝟙_ C ⟶ G) := fun s ↦ Nat.rec (a : 𝟙_ C ⟶ G) (fun _ b ↦ d b) s
  have hL (s : ℕ) : L s ^ ℓ ^ s = a := by
    induction s with
    | zero => simp [L]
    | succ s ih =>
      rw [pow_succ', pow_mul]
      exact (congrArg (· ^ ℓ ^ s) (hd (L s))).trans ih
  refine ⟨⟨fun s ↦ ⟨L s ^ ℓ ^ r, ?_⟩, fun s ↦ ?_⟩, Subtype.ext (hL r)⟩
  · rw [mem_torsionPoints, pow_right_comm, hL, (mem_torsionPoints G).mp a.2]
  · change (L (s + 1) ^ ℓ ^ r) ^ ℓ = L s ^ ℓ ^ r
    rw [pow_right_comm]
    exact congrArg (· ^ ℓ ^ r) (hd (L s))

private lemma coe_toPNat_pow (hℓ : 0 < ℓ) (r : ℕ) : ((ℓ.toPNat hℓ ^ r : ℕ+) : ℕ) = ℓ ^ r :=
  rfl

/-- The projection `T(G) → T_ℓ(G)`, `x ↦ (x_{ℓ^r})_r`. -/
def tateModuleToAt (hℓ : 0 < ℓ) : tateModule G →* tateModuleAt G ℓ where
  toFun x := ⟨fun r ↦ x.1 (ℓ.toPNat hℓ ^ r), fun r ↦
    (congrArg (· ^ ℓ) (tateModule_apply_congr x (pow_succ (ℓ.toPNat hℓ) r))).trans
      (pow_tateModule x (ℓ.toPNat hℓ ^ r) (ℓ.toPNat hℓ))⟩
  map_one' := Subtype.ext (funext fun _ ↦ rfl)
  map_mul' _ _ := Subtype.ext (funext fun _ ↦ rfl)

lemma tateModuleToAt_apply (hℓ : 0 < ℓ) (x : tateModule G) (r : ℕ) :
    ((tateModuleToAt hℓ x).1 r : 𝟙_ C ⟶ G) = x.1 (ℓ.toPNat hℓ ^ r) :=
  rfl

lemma continuous_tateModuleToAt (hℓ : 0 < ℓ) : Continuous (tateModuleToAt (G := G) hℓ) := by
  refine continuous_induced_rng.mpr (continuous_pi fun r ↦ ?_)
  exact (continuous_apply (A := fun n : ℕ+ ↦ torsionPoints G n) (ℓ.toPNat hℓ ^ r)).comp
    continuous_subtype_val

/-- For `n = ℓ^v m` with `ℓ ∤ m`, the exponent `m^{φ(ℓ^v) - 1}`, an inverse of `m` modulo
`ℓ^v` (`primeToInv_mul_modEq`). -/
def primeToInv (ℓ n : ℕ) : ℕ := (ordCompl[ℓ] n) ^ (Nat.totient (ℓ ^ n.factorization ℓ) - 1)

lemma primeToInv_mul_modEq (hℓ : ℓ.Prime) {n : ℕ} (hn : n ≠ 0) :
    primeToInv ℓ n * ordCompl[ℓ] n ≡ 1 [MOD ℓ ^ n.factorization ℓ] := by
  rw [primeToInv, ← pow_succ,
    Nat.sub_add_cancel (Nat.totient_pos.mpr (pow_pos hℓ.pos _))]
  exact Nat.ModEq.pow_totient ((Nat.coprime_ordCompl hℓ hn).symm.pow_right _)

/-- The `n`-th component of the section `T_ℓ(G) → T(G)`: `y_v^c` for `n = ℓ^v m`, `ℓ ∤ m` and
`c m ≡ 1 mod ℓ^v`. -/
def tateModuleOfAtFun (y : tateModuleAt G ℓ) (n : ℕ+) : torsionPoints G n :=
  ⟨(y.1 ((n : ℕ).factorization ℓ) : 𝟙_ C ⟶ G) ^ primeToInv ℓ n, by
    rw [mem_torsionPoints, pow_right_comm]
    have : (y.1 ((n : ℕ).factorization ℓ) : 𝟙_ C ⟶ G) ^
        (ℓ ^ (n : ℕ).factorization ℓ * ordCompl[ℓ] (n : ℕ)) = 1 := by
      rw [pow_mul, pow_tateModuleAt_self, one_pow]
    rw [Nat.ordProj_mul_ordCompl_eq_self] at this
    rw [this, one_pow]⟩

lemma coe_tateModuleOfAtFun (y : tateModuleAt G ℓ) (n : ℕ+) :
    (tateModuleOfAtFun y n : 𝟙_ C ⟶ G) =
      (y.1 ((n : ℕ).factorization ℓ) : 𝟙_ C ⟶ G) ^ primeToInv ℓ n :=
  rfl

lemma pow_tateModuleOfAtFun (hℓ : ℓ.Prime) (y : tateModuleAt G ℓ) (n s : ℕ+) :
    (tateModuleOfAtFun y (n * s) : 𝟙_ C ⟶ G) ^ (s : ℕ) = tateModuleOfAtFun y n := by
  have hn : (n : ℕ) ≠ 0 := n.ne_zero
  have hs : (s : ℕ) ≠ 0 := s.ne_zero
  obtain ⟨v, hv₀⟩ : ∃ v, (n : ℕ).factorization ℓ = v := ⟨_, rfl⟩
  obtain ⟨a, ha₀⟩ : ∃ a, (s : ℕ).factorization ℓ = a := ⟨_, rfl⟩
  obtain ⟨m, hm₀⟩ : ∃ m, ordCompl[ℓ] (n : ℕ) = m := ⟨_, rfl⟩
  obtain ⟨m', hm'₀⟩ : ∃ m', ordCompl[ℓ] (s : ℕ) = m' := ⟨_, rfl⟩
  obtain ⟨c, hc₀⟩ : ∃ c, primeToInv ℓ n = c := ⟨_, rfl⟩
  obtain ⟨c', hc'₀⟩ : ∃ c', primeToInv ℓ (n * s : ℕ+) = c' := ⟨_, rfl⟩
  have hv : ((n * s : ℕ+) : ℕ).factorization ℓ = v + a := by
    rw [PNat.mul_coe, Nat.factorization_mul hn hs, Finsupp.add_apply, hv₀, ha₀]
  have hs' : (s : ℕ) = ℓ ^ a * m' := by
    rw [← ha₀, ← hm'₀, Nat.ordProj_mul_ordCompl_eq_self]
  -- `c` and `c'` are inverses of `m` and `m m'` modulo `ℓ^v` and `ℓ^{v+a}`
  have hcm : c * m ≡ 1 [MOD ℓ ^ v] := by
    rw [← hc₀, ← hm₀, ← hv₀]
    exact primeToInv_mul_modEq hℓ hn
  have hc' : c' * (m * m') ≡ 1 [MOD ℓ ^ (v + a)] := by
    rw [← hv, ← hc'₀, ← hm₀, ← hm'₀, ← Nat.ordCompl_mul, ← PNat.mul_coe]
    exact primeToInv_mul_modEq hℓ (n * s).ne_zero
  have hcop : Nat.Coprime (ℓ ^ v) m := by
    rw [← hm₀]
    exact (Nat.coprime_ordCompl hℓ hn).pow_left _
  rw [coe_tateModuleOfAtFun, coe_tateModuleOfAtFun, tateModuleAt_apply_congr y hv, hv₀, hc₀,
    hc'₀, hs', ← pow_mul, show c' * (ℓ ^ a * m') = ℓ ^ a * (c' * m') by ring, pow_mul,
    pow_tateModuleAt y v a]
  refine pow_eq_pow_of_modEq (Nat.ModEq.cancel_right_of_coprime hcop ?_)
    (pow_tateModuleAt_self y v)
  have h₂ := hc'.of_dvd (pow_dvd_pow ℓ (Nat.le_add_right v a))
  rw [show c' * m' * m = c' * (m * m') by ring]
  exact h₂.trans hcm.symm

/-- The section `T_ℓ(G) → T(G)` of the projection `tateModuleToAt`, onto the `ℓ`-primary
component of `T(G)` (`range_tateModuleOfAt`): `y ↦ (y_v^c)_n` for `n = ℓ^v m`, `ℓ ∤ m`,
`c m ≡ 1 mod ℓ^v`. -/
def tateModuleOfAt (hℓ : ℓ.Prime) : tateModuleAt G ℓ →* tateModule G where
  toFun y := ⟨tateModuleOfAtFun y, pow_tateModuleOfAtFun hℓ y⟩
  map_one' := Subtype.ext (funext fun n ↦ Subtype.ext (by
    change ((1 : 𝟙_ C ⟶ G)) ^ primeToInv ℓ n = 1
    exact one_pow _))
  map_mul' y y' := Subtype.ext (funext fun n ↦ Subtype.ext (by
    change ((y.1 _ : 𝟙_ C ⟶ G) * y'.1 _) ^ primeToInv ℓ n =
      (y.1 _ : 𝟙_ C ⟶ G) ^ primeToInv ℓ n * (y'.1 _ : 𝟙_ C ⟶ G) ^ primeToInv ℓ n
    exact mul_pow _ _ _))

lemma coe_tateModuleOfAt_apply (hℓ : ℓ.Prime) (y : tateModuleAt G ℓ) (n : ℕ+) :
    ((tateModuleOfAt hℓ y).1 n : 𝟙_ C ⟶ G) =
      (y.1 ((n : ℕ).factorization ℓ) : 𝟙_ C ⟶ G) ^ primeToInv ℓ n :=
  rfl

/-- The image of `tateModuleOfAt` has trivial components at the `n` prime to `ℓ`. -/
lemma coe_tateModuleOfAt_apply_of_not_dvd (hℓ : ℓ.Prime) (y : tateModuleAt G ℓ) {n : ℕ+}
    (hn : ¬ ℓ ∣ n) : ((tateModuleOfAt hℓ y).1 n : 𝟙_ C ⟶ G) = 1 := by
  rw [coe_tateModuleOfAt_apply,
    tateModuleAt_apply_congr y (Nat.factorization_eq_zero_of_not_dvd hn), tateModuleAt_apply_zero,
    OneMemClass.coe_one, one_pow]

/-- The `ℓ^r`-th component of the image of `y` under `tateModuleOfAt` is `y_r`. -/
lemma coe_tateModuleOfAt_apply_toPNat_pow (hℓ : ℓ.Prime) (y : tateModuleAt G ℓ) (r : ℕ) :
    ((tateModuleOfAt hℓ y).1 (ℓ.toPNat hℓ.pos ^ r) : 𝟙_ C ⟶ G) = y.1 r := by
  have hv : (PNat.val (ℓ.toPNat hℓ.pos ^ r)).factorization ℓ = r := by
    change (ℓ ^ r).factorization ℓ = r
    rw [hℓ.factorization_pow, Finsupp.single_eq_same]
  have hc : primeToInv ℓ (PNat.val (ℓ.toPNat hℓ.pos ^ r)) = 1 := by
    rw [primeToInv, hv]
    change (ℓ ^ r / ℓ ^ r) ^ _ = 1
    rw [Nat.div_self (pow_pos hℓ.pos r), one_pow]
  rw [coe_tateModuleOfAt_apply, hc, pow_one, tateModuleAt_apply_congr y hv]

/-- `tateModuleOfAt` is a section of `tateModuleToAt`. -/
lemma tateModuleToAt_tateModuleOfAt (hℓ : ℓ.Prime) (y : tateModuleAt G ℓ) :
    tateModuleToAt hℓ.pos (tateModuleOfAt hℓ y) = y :=
  Subtype.ext (funext fun r ↦ Subtype.ext (coe_tateModuleOfAt_apply_toPNat_pow hℓ y r))

/-- The `n`-th component of the `ℓ`-primary part of `x ∈ T(G)` is a power of `x_n`: for
`n = ℓ^v m` with `ℓ ∤ m`, it is `x_{ℓ^v}^c = x_n^{m c}`. -/
lemma exists_coe_tateModuleOfAt_tateModuleToAt_apply_eq_pow (hℓ : ℓ.Prime) (x : tateModule G)
    (n : ℕ+) : ∃ e : ℕ, ((tateModuleOfAt hℓ (tateModuleToAt hℓ.pos x)).1 n : 𝟙_ C ⟶ G) =
      (x.1 n : 𝟙_ C ⟶ G) ^ e := by
  refine ⟨ordCompl[ℓ] (n : ℕ) * primeToInv ℓ n, ?_⟩
  let m : ℕ+ := ⟨ordCompl[ℓ] (n : ℕ), Nat.ordCompl_pos ℓ n.ne_zero⟩
  have hnm : ℓ.toPNat hℓ.pos ^ ((n : ℕ).factorization ℓ) * m = n :=
    PNat.eq (Nat.ordProj_mul_ordCompl_eq_self (n : ℕ) ℓ)
  have h := pow_tateModule x (ℓ.toPNat hℓ.pos ^ ((n : ℕ).factorization ℓ)) m
  rw [tateModule_apply_congr x hnm] at h
  rw [coe_tateModuleOfAt_apply, tateModuleToAt_apply, pow_mul, ← h]
  rfl

lemma continuous_tateModuleOfAt (hℓ : ℓ.Prime) : Continuous (tateModuleOfAt (G := G) hℓ) := by
  refine continuous_induced_rng.mpr (continuous_pi fun n ↦ ?_)
  let f : torsionPoints G (ℓ ^ (n : ℕ).factorization ℓ) → torsionPoints G n := fun a ↦
    ⟨(a : 𝟙_ C ⟶ G) ^ primeToInv ℓ n, by
      rw [mem_torsionPoints, pow_right_comm]
      have : (a : 𝟙_ C ⟶ G) ^ (ℓ ^ (n : ℕ).factorization ℓ * ordCompl[ℓ] (n : ℕ)) = 1 := by
        rw [pow_mul, (mem_torsionPoints G).mp a.2, one_pow]
      rw [Nat.ordProj_mul_ordCompl_eq_self] at this
      rw [this, one_pow]⟩
  change Continuous fun y : tateModuleAt G ℓ ↦ f (y.1 ((n : ℕ).factorization ℓ))
  have hf : Continuous f := continuous_of_discreteTopology
  exact hf.comp
    ((continuous_apply (A := fun r : ℕ ↦ torsionPoints G (ℓ ^ r))
      ((n : ℕ).factorization ℓ)).comp continuous_subtype_val)

/-- `tateModuleOfAt` is a homeomorphism onto its image. -/
lemma isEmbedding_tateModuleOfAt (hℓ : ℓ.Prime) :
    Topology.IsEmbedding (tateModuleOfAt (G := G) hℓ) :=
  Function.LeftInverse.isEmbedding (f := tateModuleToAt hℓ.pos)
    (tateModuleToAt_tateModuleOfAt hℓ) (continuous_tateModuleToAt hℓ.pos)
    (continuous_tateModuleOfAt hℓ)

/-! ### The `ℓ`-primary component of `T(G)` -/

/-- The open subgroup of `T(G)` of the families with `x_N = 1`. -/
def tateModuleKer (N : ℕ+) : OpenSubgroup (tateModule G) where
  toSubgroup :=
    ((Pi.evalMonoidHom (fun n : ℕ+ ↦ torsionPoints G n) N).comp (tateModule G).subtype).ker
  isOpen' := by
    have hc : Continuous fun x : tateModule G ↦ x.1 N :=
      (continuous_apply N).comp continuous_subtype_val
    exact (isOpen_discrete {1}).preimage hc

lemma mem_tateModuleKer {N : ℕ+} {x : tateModule G} : x ∈ tateModuleKer N ↔ x.1 N = 1 :=
  Iff.rfl

lemma coe_tateModule_pow_apply (x : tateModule G) (k : ℕ) (n : ℕ+) :
    (((x ^ k).1 n : torsionPoints G n) : 𝟙_ C ⟶ G) = (x.1 n : 𝟙_ C ⟶ G) ^ k := by
  simp [Pi.pow_apply]

/-- Every open subgroup of `T(G)` contains the families with `x_N = 1`, for some `N`. -/
lemma exists_tateModuleKer_le (U : OpenSubgroup (tateModule G)) :
    ∃ N : ℕ+, ∀ x : tateModule G, x.1 N = 1 → x ∈ U := by
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp U.isOpen
  have h1V : (1 : (n : ℕ+) → torsionPoints G n) ∈ V := by
    have : (1 : tateModule G) ∈ (U : Set (tateModule G)) := U.one_mem
    rw [← hVU] at this
    exact this
  obtain ⟨I, u, hu, hIV⟩ := isOpen_pi_iff.mp hV 1 h1V
  refine ⟨∏ n ∈ I, n, fun x hx ↦ ?_⟩
  have hxI : x.1 ∈ (I : Set ℕ+).pi u := fun n hn ↦ by
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem (fun n : ℕ+ ↦ n) hn
    have : x.1 n = 1 := by
      apply Subtype.ext
      rw [← pow_tateModule x n t, ← tateModule_apply_congr x ht, hx]
      simp
    rw [this]
    exact (hu n hn).2
  have : x.1 ∈ V := hIV hxI
  rw [← SetLike.mem_coe, ← hVU]
  exact this

/-- An element of `T(G)` is `ℓ`-primary iff each of its components has `ℓ`-power order. -/
lemma mem_primaryComponent_tateModule_iff (x : tateModule G) :
    x ∈ primaryComponent (tateModule G) ℓ ↔
      ∀ n : ℕ+, ∃ s : ℕ, (x.1 n : 𝟙_ C ⟶ G) ^ ℓ ^ s = 1 := by
  refine ⟨fun hx n ↦ ?_, fun hx U ↦ ?_⟩
  · obtain ⟨s, hs⟩ := hx (tateModuleKer n)
    refine ⟨s, ?_⟩
    rw [← coe_tateModule_pow_apply, mem_tateModuleKer.mp hs]
    rfl
  · obtain ⟨N, hN⟩ := exists_tateModuleKer_le U
    obtain ⟨s, hs⟩ := hx N
    exact ⟨s, hN _ (Subtype.ext (by rw [coe_tateModule_pow_apply, hs]; rfl))⟩

variable (hℓ : ℓ.Prime)
include hℓ

lemma tateModuleOfAt_mem_primaryComponent (y : tateModuleAt G ℓ) :
    tateModuleOfAt hℓ y ∈ primaryComponent (tateModule G) ℓ := by
  refine (mem_primaryComponent_tateModule_iff _).mpr fun n ↦ ⟨(n : ℕ).factorization ℓ, ?_⟩
  rw [coe_tateModuleOfAt_apply, pow_right_comm, pow_tateModuleAt_self, one_pow]

/-- An `ℓ`-primary element of `T(G)` whose components `x_{ℓ^r}` are trivial is trivial: for
`n = ℓ^v m`, `x_n^m = x_{ℓ^v} = 1` and `x_n` has `ℓ`-power order. -/
lemma eq_one_of_mem_primaryComponent {x : tateModule G}
    (hx : x ∈ primaryComponent (tateModule G) ℓ) (h : tateModuleToAt hℓ.pos x = 1) : x = 1 := by
  refine Subtype.ext (funext fun n ↦ Subtype.ext ?_)
  have hn : (n : ℕ) ≠ 0 := n.ne_zero
  obtain ⟨s, hs⟩ := (mem_primaryComponent_tateModule_iff x).mp hx n
  let m : ℕ+ := ⟨ordCompl[ℓ] (n : ℕ), Nat.pos_of_ne_zero (Nat.ordCompl_pos ℓ hn).ne'⟩
  have hnm : ℓ.toPNat hℓ.pos ^ ((n : ℕ).factorization ℓ) * m = n :=
    PNat.eq (Nat.ordProj_mul_ordCompl_eq_self (n : ℕ) ℓ)
  have hm : (x.1 n : 𝟙_ C ⟶ G) ^ (m : ℕ) = 1 := by
    rw [← tateModule_apply_congr x hnm, pow_tateModule]
    have := congrArg (fun z : tateModuleAt G ℓ ↦ (z.1 ((n : ℕ).factorization ℓ) : 𝟙_ C ⟶ G)) h
    exact this
  have hcop : Nat.Coprime (m : ℕ) (ℓ ^ s) := (Nat.coprime_ordCompl hℓ hn).symm.pow_right s
  have := pow_gcd_eq_one.mpr ⟨hm, hs⟩
  rw [hcop, pow_one] at this
  exact this

/-- The section `T_ℓ(G) → T(G)` maps onto the `ℓ`-primary component of `T(G)`. -/
lemma range_tateModuleOfAt :
    Set.range (tateModuleOfAt (G := G) hℓ) = primaryComponent (tateModule G) ℓ := by
  refine (Set.range_subset_iff.mpr (tateModuleOfAt_mem_primaryComponent hℓ)).antisymm
    fun x hx ↦ ⟨tateModuleToAt hℓ.pos x, ?_⟩
  set z := tateModuleOfAt hℓ (tateModuleToAt hℓ.pos x)
  have hz : x * z⁻¹ ∈ primaryComponent (tateModule G) ℓ := by
    refine (mem_primaryComponent_tateModule_iff _).mpr fun n ↦ ?_
    obtain ⟨s₁, hs₁⟩ := (mem_primaryComponent_tateModule_iff x).mp hx n
    obtain ⟨s₂, hs₂⟩ := (mem_primaryComponent_tateModule_iff z).mp
      (tateModuleOfAt_mem_primaryComponent hℓ _) n
    refine ⟨s₁ + s₂, ?_⟩
    change ((x.1 n : 𝟙_ C ⟶ G) * (z.1 n : 𝟙_ C ⟶ G)⁻¹) ^ ℓ ^ (s₁ + s₂) = 1
    rw [mul_pow, inv_pow, pow_add, pow_mul, hs₁, one_pow, pow_mul', hs₂, one_pow, inv_one,
      _root_.mul_one]
  have h1 : tateModuleToAt hℓ.pos (x * z⁻¹) = 1 := by
    rw [map_mul, map_inv, tateModuleToAt_tateModuleOfAt, mul_inv_cancel]
  exact (mul_inv_eq_one.mp (eq_one_of_mem_primaryComponent hℓ hz h1)).symm

end TateModuleAt

section Statements

/-- The conclusion of the `ℓ`-primary part of XI.2.1 for a commutative group scheme `A` over `k`:
an isomorphism of topological groups `ψ` from `T_ℓ(A)` onto the `ℓ`-primary component of
`π₁(A, 0)` (a topological embedding with image the `ℓ`-primary elements), such that for every
étale covering `Y ⟶ A`, every `r`, every lift `g : A ⟶ Y` of `(ℓ^r)_A` and every `z ∈ T_ℓ(A)`,
`ψ z` maps the point `g(0)` of the fibre of `Y` at `0` to `g(z_r)`. This property pins `ψ` down
(for an abelian variety: `eq_tateModuleToFundamentalGroup_comp_tateModuleOfAt`). -/
def AbelianVarietyPrimaryComponentConclusion (k : Type u) [Field k] (A : Over (Spec (.of k)))
    [GrpObj A] [IsCommMonObj A] (ℓ : ℕ) : Prop :=
  ∃ ψ : tateModuleAt A ℓ →* ExposeV.etaleFundamentalGroup k (unitSection A),
    Topology.IsEmbedding ψ ∧ Set.range ψ = primaryComponent _ ℓ ∧
    ∀ (Y : ExposeV.FEt A.left) (r : ℕ) (g : A.left ⟶ Y.left),
      g ≫ Y.hom = (mulN A (ℓ ^ r)).left →
      ∀ (y : (ExposeV.FEt.fiber k (unitSection A)).obj Y),
        ExposeV.FEt.fiberPoint k y = unitSection A ≫ g →
        ∀ z : tateModuleAt A ℓ, ExposeV.FEt.fiberPoint k (ψ z • y) = pointLeft A (z.1 r) ≫ g

/-- XI.2.1, last clause: for an abelian variety `A` over an algebraically closed field `k` and
a prime number `ℓ`, the `ℓ`-primary component of `π₁(A)` (at the origin) is canonically
isomorphic to `T_ℓ(A) = lim_r K_{ℓ^r}` (`tateModuleAt`).

The `ℓ`-primary component is the set of `σ ∈ π₁(A, 0)` with some `σ^{ℓ^r}` in every open
subgroup (`primaryComponent`); "canonically isomorphic" is made precise as in
`AbelianVarietyFundamentalGroupConclusion`: `z ∈ T_ℓ(A)` acts by `g(0) ↦ g(z_r)` for every lift
`g` of `(ℓ^r)_A` through an étale covering (`AbelianVarietyPrimaryComponentConclusion`); this
determines the isomorphism (`eq_tateModuleToFundamentalGroup_comp_tateModuleOfAt`).

It is equivalent to the first part of XI.2.1: it follows from it
(`abelianVarietyPrimaryComponentStatement_of_fundamentalGroup`) and implies it
(`abelianVarietyFundamentalGroupStatement_iff_primaryComponentStatement`, `TateModuleProduct`).
Proved in characteristic `0` (`abelianVarietyPrimaryComponent_of_charZero`), for every `ℓ`
invertible in `k` with no further input (`abelianVarietyPrimaryComponent_of_natCast_ne_zero`,
`TateModulePrimeToP`), and from SGA's cited fact that `n_A` is an isogeny
(`abelianVarietyPrimaryComponentStatement_of_mulNIsogeny`). Open: `ℓ = p = char k > 0`, which by
`TateModuleProduct` is equivalent to the first part of XI.2.1 in characteristic `p`. -/
def AbelianVarietyPrimaryComponentStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left] (ℓ : ℕ), ℓ.Prime →
    haveI := isCommMonObj_of_smooth A
    AbelianVarietyPrimaryComponentConclusion k A ℓ

end Statements

section Uniqueness

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Over (Spec (.of k))} [GrpObj A]
  [IsProper A.hom] [IsReduced A.left] [ConnectedSpace A.left] {ℓ : ℕ}

/-- The canonical map sends `T_ℓ(A)` into the `ℓ`-primary component of `π₁(A, 0)`. -/
lemma tateModuleToFundamentalGroup_tateModuleOfAt_mem [IsCommMonObj A] (hℓ : ℓ.Prime)
    (z : tateModuleAt A ℓ) :
    tateModuleToFundamentalGroup A (tateModuleOfAt hℓ z) ∈ primaryComponent _ ℓ :=
  image_primaryComponent_subset _ (continuous_tateModuleToFundamentalGroup A) ℓ
    ⟨_, tateModuleOfAt_mem_primaryComponent hℓ z, rfl⟩

/-- The map `T_ℓ(A) → T(A) → π₁(A, 0)` sends `z` to the automorphism of the fibre functor which
maps `g(0)` to `g(z_r)`, for every lift `g : A ⟶ Y` of `(ℓ^r)_A` through an étale covering. -/
lemma fiberPoint_tateModuleToFundamentalGroup_tateModuleOfAt_smul [IsCommMonObj A] (hℓ : ℓ.Prime)
    (z : tateModuleAt A ℓ) {Y : ExposeV.FEt A.left} (y : (originFiber A).obj Y) (r : ℕ)
    {g : A.left ⟶ Y.left} (hg : g ≫ Y.hom = (mulN A (ℓ ^ r)).left)
    (hg0 : unitSection A ≫ g = ExposeV.FEt.fiberPoint k y) :
    ExposeV.FEt.fiberPoint k (tateModuleToFundamentalGroup A (tateModuleOfAt hℓ z) • y) =
      pointLeft A (z.1 r) ≫ g := by
  rw [fiberPoint_tateModuleToFundamentalGroup_smul _ y (ℓ.toPNat hℓ.pos ^ r)
    (by rw [coe_toPNat_pow]; exact hg) hg0, coe_tateModuleOfAt_apply_toPNat_pow]

/-- Serre–Lang, `ℓ`-adic form (every characteristic). Let `y` be a point of the fibre at the
origin of an étale covering `Y`. By Serre–Lang some `N_A` lifts through `Y` at `y`; write
`N = ℓ^a m` with `ℓ ∤ m`. On the pull-back `Y' = m_A^* Y` the morphism `(ℓ^a)_A` lifts, by `g'`,
and the projection `e` from the fibre of `Y'` to that of `Y` maps `y' = g'(0)` to `y` and
`τ • w` to `τ^m • e(w)` (`pointedMap_mulN`). -/
theorem exists_primePow_lift (hℓ : ℓ.Prime) (Y : ExposeV.FEt A.left)
    (y : (originFiber A).obj Y) :
    ∃ (a m : ℕ) (Y' : ExposeV.FEt A.left) (g' : A.left ⟶ Y'.left)
      (y' : (originFiber A).obj Y') (e : (originFiber A).obj Y' → (originFiber A).obj Y),
      m.Coprime ℓ ∧ g' ≫ Y'.hom = (mulN A (ℓ ^ a)).left ∧
      ExposeV.FEt.fiberPoint k y' = unitSection A ≫ g' ∧ e y' = y ∧
      ∀ (τ : ExposeV.etaleFundamentalGroup k (unitSection A)) (w : (originFiber A).obj Y'),
        e (τ • w) = τ ^ m • e w := by
  let F := originFiber A
  obtain ⟨g, hg, hg0⟩ := mulNLifts_liftDegree Y y
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ+, liftDegree Y = N := ⟨_, rfl⟩
  rw [hNdef] at hg
  obtain ⟨a, ha⟩ : ∃ a, (N : ℕ).factorization ℓ = a := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, ordCompl[ℓ] (N : ℕ) = m := ⟨_, rfl⟩
  have hN : ℓ ^ a * m = (N : ℕ) := by rw [← ha, ← hm]; exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hm0 : unitSection A ≫ (mulN A m).left = unitSection A := unit_comp_mulN_left A m
  have ha0 : unitSection A ≫ (mulN A (ℓ ^ a)).left = unitSection A := unit_comp_mulN_left A _
  -- the pull-back `Y'` of `Y` along `m_A`, on whose fibre `π₁` acts through `τ ↦ τ^m`
  let Y' := (ExposeV.FEt.pullback (mulN A m).left).obj Y
  let E := ExposeV.FEt.pullbackFiberIso k (mulN A m).left (unitSection A) ≪≫
    ExposeV.FEt.fiberCongr k hm0
  have hEz : E.hom.app Y (E.inv.app Y y) = y := FintypeCat.inv_hom_id_apply (E.app Y) y
  have hfib (w : F.obj Y') : ExposeV.FEt.fiberPoint k (E.hom.app Y w) =
      ExposeV.FEt.fiberPoint k w ≫ ExposeV.FEt.proj (mulN A m).left Y := by
    change ExposeV.FEt.fiberPoint k ((ExposeV.FEt.fiberCongr k hm0).hom.app Y
      ((ExposeV.FEt.pullbackFiberIso k (mulN A m).left (unitSection A)).hom.app Y w)) = _
    rw [ExposeV.FEt.fiberPoint_fiberCongr, ExposeV.FEt.fiberPoint_pullbackFiberIso]
  have hact (τ : ExposeV.etaleFundamentalGroup k (unitSection A)) (w : F.obj Y') :
      E.hom.app Y (τ • w) = τ ^ m • E.hom.app Y w := by
    rw [← pointedMap_mulN A m hm0 τ]
    change _ = E.hom.app Y (τ • E.inv.app Y (E.hom.app Y w))
    exact (congrArg (fun x ↦ E.hom.app Y (τ • x)) (FintypeCat.hom_inv_id_apply (E.app Y) w)).symm
  -- the lift `g' = (g, (ℓ^a)_A)` of `(ℓ^a)_A` through `Y'`
  let q : Y.left ⟶ A.left := Y.hom
  have hw : g ≫ q = (mulN A (ℓ ^ a)).left ≫ (mulN A m).left := by
    change g ≫ Y.hom = _
    rw [hg, mulN_left_comp_mulN_left, hN]
  let g' : A.left ⟶ Y'.left := pullback.lift g (mulN A (ℓ ^ a)).left hw
  have hg'1 : g' ≫ ExposeV.FEt.proj (mulN A m).left Y = g := pullback.lift_fst _ _ _
  have hg' : g' ≫ Y'.hom = (mulN A (ℓ ^ a)).left := pullback.lift_snd _ _ _
  refine ⟨a, m, Y', g', E.inv.app Y y, E.hom.app Y, ?_, hg', ?_, hEz, hact⟩
  · rw [← hm]
    exact (Nat.coprime_ordCompl hℓ N.ne_zero).symm
  · symm
    apply pullback.hom_ext
    · change (unitSection A ≫ g') ≫ ExposeV.FEt.proj (mulN A m).left Y =
        ExposeV.FEt.fiberPoint k (E.inv.app Y y) ≫ ExposeV.FEt.proj (mulN A m).left Y
      rw [← hfib, hEz, Category.assoc, hg'1, hg0]
    · change (unitSection A ≫ g') ≫ Y'.hom = ExposeV.FEt.fiberPoint k (E.inv.app Y y) ≫ Y'.hom
      rw [ExposeV.FEt.fiberPoint_comp, Category.assoc, hg', ha0]

/-- Two `ℓ`-primary elements of `π₁(A, 0)` which agree on the points `g(0)`, for all lifts `g` of
the `(ℓ^r)_A` through étale coverings, are equal (every characteristic): by
`exists_primePow_lift`, their `m`-th powers agree on every point, for some `m` prime to `ℓ`. -/
theorem eq_of_forall_primePow_lift (hℓ : ℓ.Prime)
    {σ τ : ExposeV.etaleFundamentalGroup k (unitSection A)} (hσ : σ ∈ primaryComponent _ ℓ)
    (hτ : τ ∈ primaryComponent _ ℓ)
    (h : ∀ (Y : ExposeV.FEt A.left) (r : ℕ) (g : A.left ⟶ Y.left),
      g ≫ Y.hom = (mulN A (ℓ ^ r)).left → ∀ y : (originFiber A).obj Y,
      ExposeV.FEt.fiberPoint k y = unitSection A ≫ g → σ • y = τ • y) : σ = τ := by
  ext Y y
  obtain ⟨a, m, Y', g', y', e, hm, hg', hy', rfl, he⟩ := exists_primePow_lift hℓ Y y
  exact smul_eq_of_pow_smul_eq (mul_comm_of_monObj A) (stabilizer_isOpen _ (e y')) hm hσ hτ
    (by rw [← he, ← he, h Y' a g' hg' y' hy'])

/-- XI.2.1, last clause, uniqueness: a map `ψ : T_ℓ(A) → π₁(A, 0)` with values in the
`ℓ`-primary component and with the property of `AbelianVarietyPrimaryComponentConclusion` is
`T_ℓ(A) → T(A) → π₁(A, 0)` (`tateModuleOfAt` followed by the canonical map). -/
theorem eq_tateModuleToFundamentalGroup_comp_tateModuleOfAt [IsCommMonObj A] (hℓ : ℓ.Prime)
    (ψ : tateModuleAt A ℓ → ExposeV.etaleFundamentalGroup k (unitSection A))
    (hψℓ : ∀ z, ψ z ∈ primaryComponent _ ℓ)
    (hψ : ∀ (Y : ExposeV.FEt A.left) (r : ℕ) (g : A.left ⟶ Y.left),
      g ≫ Y.hom = (mulN A (ℓ ^ r)).left → ∀ (y : (originFiber A).obj Y),
        ExposeV.FEt.fiberPoint k y = unitSection A ≫ g →
        ∀ z : tateModuleAt A ℓ, ExposeV.FEt.fiberPoint k (ψ z • y) = pointLeft A (z.1 r) ≫ g) :
    ψ = (tateModuleToFundamentalGroup A).comp (tateModuleOfAt hℓ) := by
  funext z
  refine eq_of_forall_primePow_lift hℓ (hψℓ z)
    (tateModuleToFundamentalGroup_tateModuleOfAt_mem hℓ z) fun Y r g hg y hy ↦ ?_
  apply ExposeV.FEt.fiber_ext_point
  rw [hψ Y r g hg y hy z]
  exact (fiberPoint_tateModuleToFundamentalGroup_tateModuleOfAt_smul hℓ z y r hg hy.symm).symm

end Uniqueness

section Proofs

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A]

/-- XI.2.1: the `ℓ`-primary form follows from the first part. The isomorphism is
`T_ℓ(A) → T(A) ≅ π₁(A, 0)`, through the section `tateModuleOfAt` onto the `ℓ`-primary
component of `T(A)`. -/
theorem abelianVarietyPrimaryComponent_of_conclusion
    (h : AbelianVarietyFundamentalGroupConclusion k A) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    AbelianVarietyPrimaryComponentConclusion k A ℓ := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨(φ : tateModule A →* _).comp (tateModuleOfAt hℓ),
    φ.toHomeomorph.isEmbedding.comp (isEmbedding_tateModuleOfAt hℓ), ?_,
    fun Y r g hg y hy z ↦ ?_⟩
  · rw [MonoidHom.coe_comp, Set.range_comp, range_tateModuleOfAt hℓ]
    exact image_primaryComponent φ ℓ
  · change ExposeV.FEt.fiberPoint k (φ (tateModuleOfAt hℓ z) • y) = _
    rw [hφ Y (ℓ.toPNat hℓ.pos ^ r) g (by rw [coe_toPNat_pow]; exact hg) y hy,
      coe_tateModuleOfAt_apply_toPNat_pow]

end Proofs

/-- XI.2.1, `ℓ`-primary form, in characteristic `0`. -/
theorem abelianVarietyPrimaryComponent_of_charZero (k : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] (A : Over (Spec (.of k))) [GrpObj A] [IsProper A.hom] [Smooth A.hom]
    [ConnectedSpace A.left] {ℓ : ℕ} (hℓ : ℓ.Prime) :
    haveI := isCommMonObj_of_smooth A
    AbelianVarietyPrimaryComponentConclusion k A ℓ := by
  have := isCommMonObj_of_smooth A
  exact abelianVarietyPrimaryComponent_of_conclusion (exists_tateModule_equiv_of_charZero k A) hℓ

/-- XI.2.1, `ℓ`-primary form, from the first part. -/
theorem abelianVarietyPrimaryComponentStatement_of_fundamentalGroup
    (h : AbelianVarietyFundamentalGroupStatement.{u}) :
    AbelianVarietyPrimaryComponentStatement.{u} := by
  intro k _ _ A _ _ _ _ ℓ hℓ
  have := isCommMonObj_of_smooth A
  exact abelianVarietyPrimaryComponent_of_conclusion (h k A) hℓ

/-- XI.2.1, `ℓ`-primary form, from SGA's cited fact that `n_A` is an isogeny. -/
theorem abelianVarietyPrimaryComponentStatement_of_mulNIsogeny (h : MulNIsogenyStatement.{u}) :
    AbelianVarietyPrimaryComponentStatement.{u} :=
  abelianVarietyPrimaryComponentStatement_of_fundamentalGroup
    (abelianVarietyFundamentalGroupStatement_of_mulNIsogeny h)

end SGA.SGA1.ExposeXI
