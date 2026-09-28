/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import SGA.Foundations.Ramification.Inertia

/-!
# The tame character of an inertia group

Let a group `G` act on a noetherian domain `B` by ring automorphisms, let `P` be a maximal ideal
of `B` and `π ∈ P - P²` with `P = (π) + P²` (`Ideal.IsLocalUniformizer`; such `π` exist when `B`
is a Dedekind domain and `P ≠ 0`, `Ideal.exists_isLocalUniformizer`). An element `σ` of the
inertia group `I_P = P.inertia G` stabilizes `P` and acts trivially on `B/P`, hence acts on the
one-dimensional `B/P`-vector space `P/P²` by a scalar `θ(σ)`: `σ π ≡ θ(σ) π mod P²`.

* `Ideal.tameCharacter`: the homomorphism `θ : I_P →* (B/P)ˣ` (Serre, *Local fields*, IV §2,
  Prop. 7);
* `Ideal.isPGroup_ker_tameCharacter`: its kernel is a `p`-group, `p` the characteristic exponent
  of `B/P` (Serre, IV §2, Cor. 1–3). The proof does not use the separability of the residue
  extension, as indicated in SGA 1 XIII 2.0: if `σ` acts trivially on `P/P²`, it acts trivially on
  every `Pᵗ/Pᵗ⁺¹`, and then `σ^ℓ = 1` with `ℓ` prime to `p` forces `σ = 1`
  (`Ideal.smul_eq_self_of_sub_mem_pow_succ`, using Krull's intersection theorem);
* `Ideal.exists_isPGroup_isCyclic_quotient_inertia`: `I_P` is an extension of a cyclic group of
  order prime to `p` by a normal `p`-group (Serre, IV §2, Cor. 4; SGA 1 XIII 2.0);
* `Ideal.tameCharacter_injective`, `Ideal.isCyclic_inertia`: if `|I_P|` is prime to `p`, then
  `θ` is injective and `I_P` is cyclic; `Ideal.inertiaEquivRootsOfUnity`: `θ` then identifies
  `I_P` with the group of `|I_P|`-th roots of unity of `B/P` (SGA 1 X.3). In the Galois case
  `|I_P|` is then the ramification index (`Ideal.card_inertia_eq_ramificationIdx_of_isSeparable`).
-/

open scoped Pointwise

namespace Ideal

section Filtration

variable {B G : Type*} [CommRing B] [Monoid G] [MulSemiringAction G B]

/-- `σⁿ x - x = Σ_{i < n} σⁱ (σ x - x)`. -/
lemma pow_smul_sub_eq_sum (σ : G) (x : B) (n : ℕ) :
    (σ ^ n) • x - x = ∑ i ∈ Finset.range n, (σ ^ i) • (σ • x - x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, smul_sub, ← mul_smul, ← pow_succ]
    ring

/-- Let `I` be a maximal ideal with `⋂ Iᵗ = 0` and `σ` an element acting on `B` with
`(σ - 1)(Iᵗ) ⊆ Iᵗ⁺¹` for all `t`. If `σ^ℓ = 1` for some `ℓ` prime to the characteristic of `B/I`,
then `σ` acts trivially. -/
theorem smul_eq_self_of_sub_mem_pow_succ (I : Ideal B) [I.IsMaximal] (hI : ⨅ t : ℕ, I ^ t = ⊥)
    (σ : G) (hσ : ∀ t : ℕ, ∀ x ∈ I ^ t, σ • x - x ∈ I ^ (t + 1)) {ℓ : ℕ} (hℓ : σ ^ ℓ = 1)
    (hℓI : (ℓ : B) ∉ I) (x : B) : σ • x = x := by
  have hpres (t : ℕ) (i : ℕ) (y : B) (hy : y ∈ I ^ t) : (σ ^ i) • y ∈ I ^ t := by
    induction i with
    | zero => simpa using hy
    | succ i ih =>
      rw [pow_succ', mul_smul]
      have := I.pow_le_pow_right (Nat.le_succ t) (hσ t _ ih)
      simpa using add_mem this ih
  have hiter (t : ℕ) (y : B) (hy : y ∈ I ^ t) (i : ℕ) : (σ ^ i) • y - y ∈ I ^ (t + 1) := by
    induction i with
    | zero => simp
    | succ i ih =>
      have h := hσ t _ (hpres t i y hy)
      rw [pow_succ' σ i, mul_smul]
      convert add_mem h ih using 1
      ring
  obtain ⟨a, i, hi, hai⟩ := Ideal.IsMaximal.exists_inv inferInstance hℓI
  have key (t : ℕ) (x : B) : σ • x - x ∈ I ^ t := by
    induction t generalizing x with
    | zero => simp
    | succ t ih =>
      set y := σ • x - x
      have hy : y ∈ I ^ t := ih x
      have hsum : ∑ j ∈ Finset.range ℓ, ((σ ^ j) • y - y) ∈ I ^ (t + 1) :=
        Ideal.sum_mem _ fun j _ ↦ hiter t y hy j
      rw [Finset.sum_sub_distrib, ← pow_smul_sub_eq_sum, hℓ, one_smul, sub_self,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, zero_sub, neg_mem_iff] at hsum
      have : y = a * (ℓ * y) + i * y := by linear_combination (-y) * hai
      rw [this, pow_succ']
      exact add_mem (mul_mem_left _ _ (by rwa [pow_succ'] at hsum)) (Ideal.mul_mem_mul hi hy)
  have : σ • x - x ∈ ⨅ t : ℕ, I ^ t := Submodule.mem_iInf _ |>.mpr fun t ↦ key t x
  rwa [hI, Ideal.mem_bot, sub_eq_zero] at this

end Filtration

section TameCharacter

variable {B G : Type*} [CommRing B] [Group G] [MulSemiringAction G B] {P : Ideal B}

lemma smul_mem_of_mem_inertia {σ : G} (hσ : σ ∈ P.inertia G) {x : B} (hx : x ∈ P) :
    σ • x ∈ P := by
  simpa using add_mem (hσ x) hx

lemma smul_mem_pow_of_mem_inertia {σ : G} (hσ : σ ∈ P.inertia G) (n : ℕ) {x : B}
    (hx : x ∈ P ^ n) : σ • x ∈ P ^ n := by
  have : (P ^ n).map (MulSemiringAction.toRingHom G B σ) ≤ P ^ n := by
    rw [Ideal.map_pow]
    gcongr
    exact Ideal.map_le_iff_le_comap.mpr fun y hy ↦ smul_mem_of_mem_inertia hσ hy
  exact this (Ideal.mem_map_of_mem _ hx)

variable (P) in
/-- `π` is a local uniformizer at the maximal ideal `P`: `π ∈ P - P²` and `P = (π) + P²`, i.e. the
image of `π` generates the cotangent space `P/P²`. When `B_P` is a discrete valuation ring, these
are the elements whose image in `B_P` is a uniformizer. -/
structure IsLocalUniformizer (π : B) : Prop where
  mem : π ∈ P
  notMem_sq : π ∉ P ^ 2
  le_span_sup : P ≤ Ideal.span {π} ⊔ P ^ 2

/-- In a Dedekind domain every nonzero prime has a local uniformizer. -/
theorem exists_isLocalUniformizer [IsDedekindDomain B] (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ π, P.IsLocalUniformizer π := by
  obtain ⟨π, hπ, hπ2⟩ := SetLike.exists_of_lt (by simpa using Ideal.pow_succ_lt_pow hP 1)
  refine ⟨π, hπ, hπ2, ?_⟩
  have hlt : P ^ (1 + 1) < Ideal.span {π} ⊔ P ^ 2 :=
    lt_of_le_of_ne le_sup_right fun h ↦
      hπ2 (h ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self π))
  have hle : Ideal.span {π} ⊔ P ^ 2 ≤ P ^ 1 := by
    rw [pow_one]
    exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hπ) (Ideal.pow_le_self two_ne_zero)
  rw [Ideal.eq_prime_pow_of_succ_lt_of_le hP hlt hle, pow_one]

variable (G P) in
/-- The wild inertia group of `P` (the group `H₁` of SGA 1 XIII 2.0): the elements of the
inertia group acting trivially on `P/P²`. When `B_P` is a discrete valuation ring, these are the
`σ` with `σπ/π ≡ 1` modulo `P` for every uniformizer `π`. -/
def wildInertia : Subgroup G where
  carrier := {σ | σ ∈ P.inertia G ∧ ∀ x ∈ P, σ • x - x ∈ P ^ 2}
  mul_mem' {σ τ} hσ hτ := by
    refine ⟨mul_mem hσ.1 hτ.1, fun x hx ↦ ?_⟩
    have e : (σ * τ) • x - x = σ • (τ • x - x) + (σ • x - x) := by
      rw [mul_smul, smul_sub]
      ring
    rw [e]
    exact add_mem (smul_mem_pow_of_mem_inertia hσ.1 2 (hτ.2 x hx)) (hσ.2 x hx)
  one_mem' := ⟨one_mem _, fun x _ ↦ by simp⟩
  inv_mem' {σ} hσ := by
    refine ⟨inv_mem hσ.1, fun x hx ↦ ?_⟩
    have e : σ⁻¹ • x - x = -(σ⁻¹ • (σ • x - x)) := by
      rw [smul_sub, inv_smul_smul]
      ring
    rw [e, neg_mem_iff]
    exact smul_mem_pow_of_mem_inertia (inv_mem hσ.1) 2 (hσ.2 x hx)

lemma mem_wildInertia_iff {σ : G} :
    σ ∈ wildInertia G P ↔ σ ∈ P.inertia G ∧ ∀ x ∈ P, σ • x - x ∈ P ^ 2 :=
  Iff.rfl

lemma wildInertia_le_inertia : wildInertia G P ≤ P.inertia G :=
  fun _ h ↦ h.1

lemma conj_mem_wildInertia {σ : G} (hσ : σ ∈ wildInertia G P) (g : G) :
    g * σ * g⁻¹ ∈ wildInertia G (g • P) := by
  have key (x : B) : (g * σ * g⁻¹) • x - x = g • (σ • (g⁻¹ • x) - g⁻¹ • x) := by
    rw [smul_sub, mul_smul, mul_smul, smul_inv_smul]
  have hmem (y : B) : y ∈ P → g • y ∈ g • P := Ideal.smul_mem_pointwise_smul g y P
  refine ⟨fun x ↦ ?_, fun x hx ↦ ?_⟩
  · rw [key]
    exact hmem _ (hσ.1 _)
  · rw [key]
    have hx' : g⁻¹ • x ∈ P := Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp hx
    have : g • (P ^ 2) = (g • P) ^ 2 := by
      rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def, Ideal.map_pow]
    rw [← this]
    exact Ideal.smul_mem_pointwise_smul g _ _ (hσ.2 _ hx')

variable [P.IsMaximal] {π : B}

/-- A multiple `a π` of a local uniformizer lies in `P²` only if `a ∈ P`. -/
lemma IsLocalUniformizer.mem_of_mul_mem_sq (h : P.IsLocalUniformizer π) {a : B}
    (ha : a * π ∈ P ^ 2) : a ∈ P := by
  by_contra hna
  obtain ⟨b, i, hi, hbi⟩ := Ideal.IsMaximal.exists_inv inferInstance hna
  apply h.notMem_sq
  have : π = b * (a * π) + i * π := by linear_combination (-π) * hbi
  rw [this, sq]
  exact add_mem (mul_mem_left _ _ (by rwa [sq] at ha)) (Ideal.mul_mem_mul hi h.mem)

omit [P.IsMaximal] in
lemma IsLocalUniformizer.exists_smul_sub_mem_sq (h : P.IsLocalUniformizer π) {σ : G}
    (hσ : σ ∈ P.inertia G) : ∃ a : B, σ • π - a * π ∈ P ^ 2 := by
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    Submodule.mem_sup.mp (h.le_span_sup (smul_mem_of_mem_inertia hσ h.mem))
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  exact ⟨a, by rw [← hyz]; simpa using hz⟩

/-- For `σ` in the inertia group, `θ(σ) ∈ B/P` with `σ π ≡ θ(σ) π mod P²`. -/
noncomputable def IsLocalUniformizer.tameCharacterFun (h : P.IsLocalUniformizer π)
    (σ : P.inertia G) : B ⧸ P :=
  Ideal.Quotient.mk P (h.exists_smul_sub_mem_sq σ.2).choose

lemma IsLocalUniformizer.tameCharacterFun_eq_mk_iff (h : P.IsLocalUniformizer π)
    (σ : P.inertia G) (a : B) :
    h.tameCharacterFun σ = Ideal.Quotient.mk P a ↔ (σ : G) • π - a * π ∈ P ^ 2 := by
  have hspec := (h.exists_smul_sub_mem_sq σ.2).choose_spec
  set a₀ := (h.exists_smul_sub_mem_sq σ.2).choose
  rw [tameCharacterFun, Ideal.Quotient.eq]
  constructor
  · intro ha
    have : (a₀ - a) * π ∈ P ^ 2 := by rw [sq]; exact Ideal.mul_mem_mul ha h.mem
    convert add_mem hspec this using 1
    ring
  · intro ha
    refine h.mem_of_mul_mem_sq ?_
    convert sub_mem ha hspec using 1
    ring

variable (G) in
/-- The tame character `θ : I_P →* (B/P)ˣ`: `σ π ≡ θ(σ) π mod P²` (Serre, *Local fields*, IV §2,
Prop. 7). -/
noncomputable def IsLocalUniformizer.tameCharacter (h : P.IsLocalUniformizer π) :
    P.inertia G →* (B ⧸ P)ˣ :=
  MonoidHom.toHomUnits
    { toFun := h.tameCharacterFun
      map_one' := by
        rw [← map_one (Ideal.Quotient.mk P), h.tameCharacterFun_eq_mk_iff]
        simp
      map_mul' σ τ := by
        obtain ⟨a, ha⟩ := h.exists_smul_sub_mem_sq σ.2
        obtain ⟨b, hb⟩ := h.exists_smul_sub_mem_sq τ.2
        have hσ := (h.tameCharacterFun_eq_mk_iff σ a).mpr ha
        have hτ := (h.tameCharacterFun_eq_mk_iff τ b).mpr hb
        have hσb : Ideal.Quotient.mk P ((σ : G) • b) = Ideal.Quotient.mk P b :=
          Ideal.Quotient.eq.mpr (σ.2 b)
        rw [hσ, hτ, ← map_mul, h.tameCharacterFun_eq_mk_iff]
        -- `στ π = σ(b π + q_τ) = σ(b) (a π + q_σ) + σ(q_τ)`
        have e : ((σ * τ : P.inertia G) : G) • π - a * b * π =
            ((σ : G) • b) * ((σ : G) • π - a * π) + (σ : G) • ((τ : G) • π - b * π) +
              ((σ : G) • b - b) * a * π := by
          simp only [Subgroup.coe_mul, mul_smul, smul_sub, smul_mul']
          ring
        rw [e]
        refine add_mem (add_mem (mul_mem_left _ _ ha) (smul_mem_pow_of_mem_inertia σ.2 2 hb)) ?_
        rw [mul_assoc, sq]
        exact Ideal.mul_mem_mul (σ.2 b) (mul_mem_left _ _ h.mem) }

lemma IsLocalUniformizer.tameCharacter_eq_mk_iff (h : P.IsLocalUniformizer π)
    (σ : P.inertia G) (a : B) :
    (h.tameCharacter G σ : B ⧸ P) = Ideal.Quotient.mk P a ↔ (σ : G) • π - a * π ∈ P ^ 2 :=
  h.tameCharacterFun_eq_mk_iff σ a

/-- `σ` is in the kernel of the tame character if and only if it acts trivially on `P/P²`. -/
lemma IsLocalUniformizer.mem_ker_tameCharacter_iff (h : P.IsLocalUniformizer π)
    (σ : P.inertia G) : σ ∈ (h.tameCharacter G).ker ↔ ∀ x ∈ P, (σ : G) • x - x ∈ P ^ 2 := by
  rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one, ← map_one (Ideal.Quotient.mk P),
    h.tameCharacter_eq_mk_iff, one_mul]
  refine ⟨fun hπ x hx ↦ ?_, fun H ↦ H π h.mem⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (h.le_span_sup hx)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have e : (σ : G) • (c * π + z) - (c * π + z) =
      (σ : G) • c * ((σ : G) • π - π) + ((σ : G) • c - c) * π + ((σ : G) • z - z) := by
    rw [smul_add, smul_mul']
    ring
  rw [e, sq]
  refine add_mem (add_mem (mul_mem_left _ _ (by rwa [← sq])) (Ideal.mul_mem_mul (σ.2 c) h.mem))
    (sub_mem (by rw [← sq]; exact smul_mem_pow_of_mem_inertia σ.2 2 hz) (by rwa [← sq]))

/-- The kernel of the tame character is the wild inertia group. -/
lemma IsLocalUniformizer.wildInertia_subgroupOf (h : P.IsLocalUniformizer π) :
    (wildInertia G P).subgroupOf (P.inertia G) = (h.tameCharacter G).ker := by
  ext σ
  rw [Subgroup.mem_subgroupOf, h.mem_ker_tameCharacter_iff]
  exact ⟨fun hσ ↦ hσ.2, fun hσ ↦ ⟨σ.2, hσ⟩⟩

/-- An element of the kernel of the tame character satisfies `(σ - 1)(Pᵗ) ⊆ Pᵗ⁺¹` for all `t`. -/
lemma IsLocalUniformizer.sub_mem_pow_succ_of_mem_ker (h : P.IsLocalUniformizer π)
    {σ : P.inertia G} (hσ : σ ∈ (h.tameCharacter G).ker) (t : ℕ) :
    ∀ x ∈ P ^ t, (σ : G) • x - x ∈ P ^ (t + 1) := by
  rw [h.mem_ker_tameCharacter_iff] at hσ
  induction t with
  | zero => intro x _; simpa using σ.2 x
  | succ t ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      have e : (σ : G) • (y * z) - y * z =
          (σ : G) • y * ((σ : G) • z - z) + ((σ : G) • y - y) * z := by
        rw [smul_mul']
        ring
      rw [e]
      refine add_mem ?_ ?_
      · have := Ideal.mul_mem_mul (smul_mem_pow_of_mem_inertia σ.2 t hy) (hσ z hz)
        rwa [← pow_add] at this
      · have := Ideal.mul_mem_mul (ih y hy) hz
        rwa [← pow_succ] at this
    · intro x y hx hy
      rw [smul_add]
      convert add_mem hx hy using 1
      ring

variable (G) in
/-- The injection `I_P / ker θ → B/P` induced by the tame character. -/
noncomputable def IsLocalUniformizer.kerLiftTameCharacter (h : P.IsLocalUniformizer π) :
    P.inertia G ⧸ (h.tameCharacter G).ker →* B ⧸ P :=
  (Units.coeHom (B ⧸ P)).comp (QuotientGroup.kerLift (h.tameCharacter G))

lemma IsLocalUniformizer.kerLiftTameCharacter_injective (h : P.IsLocalUniformizer π) :
    Function.Injective (h.kerLiftTameCharacter G) :=
  Units.val_injective.comp (QuotientGroup.kerLift_injective _)

variable [IsNoetherianRing B] [IsDomain B] [FaithfulSMul G B]

/-- An element of the kernel of the tame character of order prime to the residue characteristic
is trivial. -/
theorem IsLocalUniformizer.eq_one_of_mem_ker (h : P.IsLocalUniformizer π) {σ : P.inertia G}
    (hσ : σ ∈ (h.tameCharacter G).ker) {ℓ : ℕ} (hℓ : σ ^ ℓ = 1) (hℓP : (ℓ : B ⧸ P) ≠ 0) :
    σ = 1 := by
  have hI : ⨅ t : ℕ, P ^ t = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain P (Ideal.IsMaximal.ne_top ‹_›)
  have hℓ' : (σ : G) ^ ℓ = 1 := by rw [← Subgroup.coe_pow, hℓ, Subgroup.coe_one]
  have hℓI : (ℓ : B) ∉ P := by
    rwa [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  have := smul_eq_self_of_sub_mem_pow_succ P hI (σ : G) (h.sub_mem_pow_succ_of_mem_ker hσ) hℓ' hℓI
  exact Subtype.ext (eq_of_smul_eq_smul (α := B) fun x ↦ by rw [this, Subgroup.coe_one, one_smul])

variable [Finite G]

/-- The kernel of the tame character is a `p`-group, `p` the characteristic exponent of `B/P`
(Serre, *Local fields*, IV §2, Cor. 3; SGA 1 XIII 2.0 without separability of `B/P`). -/
theorem IsLocalUniformizer.isPGroup_ker_tameCharacter (h : P.IsLocalUniformizer π) :
    IsPGroup (ringExpChar (B ⧸ P)) (h.tameCharacter G).ker := by
  intro σ
  have hn : orderOf (σ : P.inertia G) ≠ 0 := (orderOf_pos _).ne'
  have hq : ExpChar (B ⧸ P) (ringExpChar (B ⧸ P)) := inferInstance
  generalize ringExpChar (B ⧸ P) = q at hq ⊢
  cases hq with
  | zero =>
    refine ⟨0, Subtype.ext ?_⟩
    rw [pow_zero, pow_one]
    exact h.eq_one_of_mem_ker σ.2 (pow_orderOf_eq_one _) (Nat.cast_ne_zero.mpr hn)
  | prime hprime =>
    obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hprime.ne_one
    refine ⟨k, Subtype.ext ?_⟩
    have hmem : (σ : P.inertia G) ^ q ^ k ∈ (h.tameCharacter G).ker := pow_mem σ.2 _
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    refine h.eq_one_of_mem_ker hmem ?_ ((CharP.cast_eq_zero_iff (B ⧸ P) q m).not.mpr hm)
    rw [← pow_mul, ← hnm, pow_orderOf_eq_one]

omit [IsNoetherianRing B] [IsDomain B] [FaithfulSMul G B] in
/-- The quotient of the inertia group by the kernel of the tame character is cyclic. -/
theorem IsLocalUniformizer.isCyclic_quotient_ker (h : P.IsLocalUniformizer π) :
    IsCyclic (P.inertia G ⧸ (h.tameCharacter G).ker) :=
  isCyclic_of_injective_ringHom _ (h.kerLiftTameCharacter_injective (G := G))

omit [IsNoetherianRing B] [IsDomain B] [FaithfulSMul G B] in
/-- The quotient of the inertia group by the kernel of the tame character has order prime to the
residue characteristic. -/
theorem IsLocalUniformizer.natCast_card_quotient_ker_ne_zero (h : P.IsLocalUniformizer π) :
    ((Nat.card (P.inertia G ⧸ (h.tameCharacter G).ker) : ℕ) : B ⧸ P) ≠ 0 := by
  have := h.isCyclic_quotient_ker (G := G)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P.inertia G ⧸ (h.tameCharacter G).ker)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg,
    ← orderOf_injective _ h.kerLiftTameCharacter_injective g]
  have : NeZero (orderOf (h.kerLiftTameCharacter G g)) := ⟨by
    rw [orderOf_injective _ h.kerLiftTameCharacter_injective g]
    exact (orderOf_pos g).ne'⟩
  exact (IsPrimitiveRoot.orderOf _).neZero'.out

variable (G P) in
/-- XIII 2.0 (Serre, *Local fields*, IV §2, Cor. 4, without separability of the residue
extension): the inertia group is an extension of a cyclic group of order prime to the residue
characteristic by a normal `p`-group, `p` the characteristic exponent of `B/P`. -/
theorem exists_isPGroup_isCyclic_quotient_inertia (hπ : ∃ π, P.IsLocalUniformizer π) :
    ∃ (W : Subgroup (P.inertia G)) (_ : W.Normal), IsPGroup (ringExpChar (B ⧸ P)) W ∧
      IsCyclic (P.inertia G ⧸ W) ∧ ((Nat.card (P.inertia G ⧸ W) : ℕ) : B ⧸ P) ≠ 0 := by
  obtain ⟨π, h⟩ := hπ
  exact ⟨_, inferInstance, h.isPGroup_ker_tameCharacter, h.isCyclic_quotient_ker,
    h.natCast_card_quotient_ker_ne_zero⟩

omit [Finite G] in
/-- If the inertia group has order prime to the residue characteristic, the tame character is
injective. -/
theorem IsLocalUniformizer.tameCharacter_injective (h : P.IsLocalUniformizer π)
    (hcard : ((Nat.card (P.inertia G) : ℕ) : B ⧸ P) ≠ 0) :
    Function.Injective (h.tameCharacter G) := by
  rw [injective_iff_map_eq_one]
  exact fun σ hσ ↦ h.eq_one_of_mem_ker hσ pow_card_eq_one' hcard

variable (G P) in
/-- A tame inertia group (of order prime to the residue characteristic) is cyclic. -/
theorem isCyclic_inertia (hπ : ∃ π, P.IsLocalUniformizer π)
    (hcard : ((Nat.card (P.inertia G) : ℕ) : B ⧸ P) ≠ 0) : IsCyclic (P.inertia G) := by
  obtain ⟨π, h⟩ := hπ
  exact isCyclic_of_injective_ringHom ((Units.coeHom (B ⧸ P)).comp (h.tameCharacter G))
    (Units.val_injective.comp (h.tameCharacter_injective hcard))

/-- X.3: if the inertia group `I_P` has order `n` prime to the residue characteristic, the tame
character identifies it with the group `μ_n(B/P)` of `n`-th roots of unity of `B/P`. -/
noncomputable def IsLocalUniformizer.inertiaEquivRootsOfUnity (h : P.IsLocalUniformizer π)
    (hcard : ((Nat.card (P.inertia G) : ℕ) : B ⧸ P) ≠ 0) :
    P.inertia G ≃* rootsOfUnity (Nat.card (P.inertia G)) (B ⧸ P) :=
  MulEquiv.ofBijective ((h.tameCharacter G).codRestrict _ fun σ ↦ by
      rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one])
    (Function.Injective.bijective_of_nat_card_le
      (fun σ τ hστ ↦ h.tameCharacter_injective hcard (congrArg Subtype.val hστ))
      (card_rootsOfUnity _ _))

@[simp]
lemma IsLocalUniformizer.coe_inertiaEquivRootsOfUnity_apply (h : P.IsLocalUniformizer π)
    (hcard : ((Nat.card (P.inertia G) : ℕ) : B ⧸ P) ≠ 0) (σ : P.inertia G) :
    ((h.inertiaEquivRootsOfUnity hcard σ : (B ⧸ P)ˣ) : B ⧸ P) = h.tameCharacter G σ :=
  rfl

omit [IsNoetherianRing B] [IsDomain B] [FaithfulSMul G B] in
/-- The index of the wild inertia group in the inertia group is prime to the residue
characteristic. -/
theorem natCast_relIndex_wildInertia_ne_zero (hπ : ∃ π, P.IsLocalUniformizer π) :
    (((wildInertia G P).relIndex (P.inertia G) : ℕ) : B ⧸ P) ≠ 0 := by
  obtain ⟨π, h⟩ := hπ
  rw [Subgroup.relIndex, h.wildInertia_subgroupOf, Subgroup.index]
  exact h.natCast_card_quotient_ker_ne_zero

/-- The wild inertia group is a `p`-group, `p` the characteristic exponent of `B/P`. -/
theorem isPGroup_wildInertia (hπ : ∃ π, P.IsLocalUniformizer π) :
    IsPGroup (ringExpChar (B ⧸ P)) (wildInertia G P) := by
  obtain ⟨π, h⟩ := hπ
  have hW := h.isPGroup_ker_tameCharacter (G := G)
  rw [← h.wildInertia_subgroupOf] at hW
  exact hW.of_equiv (Subgroup.subgroupOfEquivOfLe wildInertia_le_inertia)

/-- A subgroup `K` of `G` meets the inertia group in a subgroup of index prime to the residue
characteristic if and only if it contains the wild inertia group. -/
theorem natCast_relIndex_inertia_ne_zero_iff (hπ : ∃ π, P.IsLocalUniformizer π)
    (K : Subgroup G) :
    ((K.relIndex (P.inertia G) : ℕ) : B ⧸ P) ≠ 0 ↔ wildInertia G P ≤ K := by
  obtain ⟨π, h⟩ := hπ
  set I := P.inertia G
  set W' := (wildInertia G P).subgroupOf I
  set K' := K.subgroupOf I
  have hker : W' = (h.tameCharacter G).ker := h.wildInertia_subgroupOf
  have hW'normal : W'.Normal := by rw [hker]; infer_instance
  have hWle : (wildInertia G P ≤ K) ↔ W' ≤ K' := by
    refine ⟨fun hle σ hσ ↦ Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_subgroupOf.mp hσ)),
      fun hle σ hσ ↦ ?_⟩
    have : (⟨σ, wildInertia_le_inertia hσ⟩ : I) ∈ K' :=
      hle (Subgroup.mem_subgroupOf.mpr hσ)
    exact Subgroup.mem_subgroupOf.mp this
  have hW : ((W'.index : ℕ) : B ⧸ P) ≠ 0 := natCast_relIndex_wildInertia_ne_zero ⟨π, h⟩
  rw [hWle, Subgroup.relIndex]
  refine ⟨fun hK ↦ ?_, fun hle ↦ ?_⟩
  · have hpW : IsPGroup (ringExpChar (B ⧸ P)) W' := by
      rw [hker]; exact h.isPGroup_ker_tameCharacter
    have hq : ExpChar (B ⧸ P) (ringExpChar (B ⧸ P)) := inferInstance
    generalize ringExpChar (B ⧸ P) = q at hq hpW
    cases hq with
    | zero =>
      intro σ hσ
      obtain ⟨k, hk⟩ := hpW ⟨σ, hσ⟩
      rw [one_pow, pow_one] at hk
      rw [show σ = 1 from congrArg Subtype.val hk]
      exact one_mem _
    | prime hprime =>
      have : Fact q.Prime := ⟨hprime⟩
      have hndvd : ¬ q ∣ Nat.card (I ⧸ K') := by
        rwa [← Subgroup.index, ← CharP.cast_eq_zero_iff (B ⧸ P) q]
      obtain ⟨x, hx⟩ := hpW.nonempty_fixed_point_of_prime_not_dvd_card (I ⧸ K') hndvd
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      intro w hw
      have hw' : g * w⁻¹ * g⁻¹ ∈ W' := hW'normal.conj_mem _ (inv_mem hw) g
      have hfix := hx ⟨_, hw'⟩
      change ((g * w⁻¹ * g⁻¹ : I) • (g : I ⧸ K')) = g at hfix
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at hfix
      simpa [mul_assoc] using hfix
  · obtain ⟨c, hc⟩ := Subgroup.index_dvd_of_le hle
    intro h0
    rw [hc, Nat.cast_mul, h0, zero_mul] at hW
    exact hW rfl

end TameCharacter

end Ideal
