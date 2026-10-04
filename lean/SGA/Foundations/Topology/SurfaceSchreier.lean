/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.SurfaceRibbonPerm
import Mathlib.GroupTheory.GroupAction.Period
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.ZMod.Defs

/-!
# The Schreier ribbon graph of an action

Let a group `F` act on a set `Φ` and let `σ₀, …, σₙ ∈ F`. The *Schreier graph* has the vertices
`ψ ∈ Φ` and an edge `(ψ, i)` from `ψ` to `σᵢ⁻¹ • ψ` for each `ψ` and `i`. Its darts are
`((ψ, i), true)` (the start of `(ψ, i)`, at `ψ`) and `((ψ, i), false)` (its end, at `σᵢ⁻¹ • ψ`).
With the rotation `Ribbon.Schreier.rot σ` (at `ψ`, the darts in the cyclic order
`in n, out n, in (n - 1), out (n - 1), …, in 0, out 0`, where `out i = ((ψ, i), true)` and
`in i = ((σᵢ • ψ, i), false)`), it is a ribbon graph whose faces are

* for each `i` and each orbit of `σᵢ`, the cycle of the darts `out i` at the points of the orbit;
* for each orbit of `τ = σ₀ ⋯ σₙ`, a cycle of darts `in` of length `(n + 1)` times the orbit
  length.

This is the ribbon graph of the covering of the sphere minus `n + 2` points defined by the action,
with `σ₀, …, σₙ, τ⁻¹` the loops around the punctures: its faces correspond to the points over the
punctures (`Ribbon.Schreier.isRibbon`).

## References

* [W. Magnus, A. Karrass, D. Solitar, *Combinatorial Group Theory*, §2.3][magnus1966]
* [B. Mohar, C. Thomassen, *Graphs on Surfaces*, §3.2][mohar2001]
-/

open Function Fin.CommRing

namespace Ribbon.Schreier

variable {F : Type*} [Group F] {Φ : Type*} [MulAction F Φ] {n : ℕ} (σ : Fin (n + 1) → F)

/-- The darts of the Schreier graph. -/
abbrev Dart (Φ : Type*) (n : ℕ) := (Φ × Fin (n + 1)) × Bool

/-- The vertex of a dart. -/
def vtx : Dart Φ n → Φ
  | ((ψ, _), true) => ψ
  | ((ψ, i), false) => (σ i)⁻¹ • ψ

/-- The rotation, as a function. -/
def rotFun : Dart Φ n → Dart Φ n
  | ((ψ, i), false) => (((σ i)⁻¹ • ψ, i), true)
  | ((ψ, i), true) => ((σ (i - 1) • ψ, i - 1), false)

/-- The inverse of the rotation. -/
def rotInv : Dart Φ n → Dart Φ n
  | ((ψ, i), true) => ((σ i • ψ, i), false)
  | ((ψ, i), false) => (((σ i)⁻¹ • ψ, i + 1), true)

/-- **The rotation of the Schreier graph**: at each vertex, the darts in the cyclic order
`in n, out n, in (n - 1), out (n - 1), …, in 0, out 0`. -/
def rot : Equiv.Perm (Dart Φ n) where
  toFun := rotFun σ
  invFun := rotInv σ
  left_inv d := by
    rcases d with ⟨⟨ψ, i⟩, _ | _⟩ <;> simp [rotFun, rotInv]
  right_inv d := by
    rcases d with ⟨⟨ψ, i⟩, _ | _⟩ <;> simp [rotFun, rotInv]

@[simp] lemma rot_true (ψ : Φ) (i : Fin (n + 1)) :
    rot σ ((ψ, i), true) = ((σ (i - 1) • ψ, i - 1), false) := rfl

@[simp] lemma rot_false (ψ : Φ) (i : Fin (n + 1)) :
    rot σ ((ψ, i), false) = (((σ i)⁻¹ • ψ, i), true) := rfl

@[simp] lemma vtx_true (ψ : Φ) (i : Fin (n + 1)) : vtx σ ((ψ, i), true) = ψ := rfl

@[simp] lemma vtx_false (ψ : Φ) (i : Fin (n + 1)) : vtx σ ((ψ, i), false) = (σ i)⁻¹ • ψ := rfl

@[simp] lemma vtx_rot (d : Dart Φ n) : vtx σ (rot σ d) = vtx σ d := by
  rcases d with ⟨⟨ψ, i⟩, _ | _⟩ <;> simp

lemma vtx_rot_zpow (d : Dart Φ n) (k : ℤ) : vtx σ ((rot σ ^ k) d) = vtx σ d := by
  have h : ∀ d : Dart Φ n, vtx σ ((rot σ)⁻¹ d) = vtx σ d := fun d ↦ by
    conv_rhs => rw [← (rot σ).apply_symm_apply d]
    rw [vtx_rot]
    rfl
  induction k using Int.induction_on generalizing d with
  | zero => simp
  | succ k ih => rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply, vtx_rot, ih]
  | pred k ih => rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply,
      h, ih]

lemma vtx_eq_of_sameCycle {d d' : Dart Φ n} (h : (rot σ).SameCycle d d') :
    vtx σ d = vtx σ d' := by
  obtain ⟨k, rfl⟩ := h
  rw [vtx_rot_zpow]

/-- All darts at `ψ` lie in the cycle of `out 0 = ((ψ, 0), true)`. -/
lemma sameCycle_rot_iff {ψ : Φ} {d : Dart Φ n} :
    (rot σ).SameCycle ((ψ, 0), true) d ↔ vtx σ d = ψ := by
  refine ⟨fun h ↦ (vtx_eq_of_sameCycle σ h).symm, fun h ↦ ?_⟩
  -- `out i ~ out (i - 1)`
  have step : ∀ i : Fin (n + 1), (rot σ).SameCycle ((ψ, i), true) ((ψ, i - 1), true) := by
    intro i
    refine ⟨2, ?_⟩
    rw [zpow_two, Equiv.Perm.mul_apply]
    simp
  have hout : ∀ k : ℕ, (rot σ).SameCycle ((ψ, 0), true) ((ψ, -(k : Fin (n + 1))), true) := by
    intro k
    induction k with
    | zero => simpa using Equiv.Perm.SameCycle.refl _ _
    | succ k ih =>
      have := step (-(k : Fin (n + 1)))
      rw [show -(k : Fin (n + 1)) - 1 = -((k + 1 : ℕ) : Fin (n + 1)) by push_cast; ring] at this
      exact ih.trans this
  have hout' : ∀ j : Fin (n + 1), (rot σ).SameCycle ((ψ, 0), true) ((ψ, j), true) := by
    intro j
    have := hout (-j).val
    rwa [Fin.cast_val_eq_self, neg_neg] at this
  rcases d with ⟨⟨ψ', j⟩, _ | _⟩
  · -- `in j` at `ψ`
    simp only [vtx_false] at h
    have h' : ψ' = σ j • ψ := by rw [← h, smul_inv_smul]
    subst h'
    refine (hout' j).trans ⟨-1, ?_⟩
    rw [zpow_neg_one]
    apply (rot σ).injective
    simp
  · simp only [vtx_true] at h
    subst h
    exact hout' j

/-- The face permutation of the Schreier graph on the darts `out`: `out i ψ ↦ out i (σᵢ⁻¹ • ψ)`. -/
@[simp] lemma facePerm_true (ψ : Φ) (i : Fin (n + 1)) :
    facePerm (rot σ) ((ψ, i), true) = (((σ i)⁻¹ • ψ, i), true) := rfl

/-- The face permutation on the darts `in`: `in i ψ ↦ in (i - 1) (σᵢ • ψ)`, where
`in i ψ = ((σᵢ • ψ, i), false)`. -/
@[simp] lemma facePerm_false (ψ : Φ) (i : Fin (n + 1)) :
    facePerm (rot σ) ((ψ, i), false) = ((σ (i - 1) • ψ, i - 1), false) := rfl

lemma facePerm_iterate_true (ψ : Φ) (i : Fin (n + 1)) (k : ℕ) :
    (facePerm (rot σ))^[k] ((ψ, i), true) = ((((σ i)⁻¹) ^ k • ψ, i), true) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply', ih, facePerm_true, pow_succ', mul_smul]

lemma facePerm_false_snd (e : Dart Φ n) (he : e.2 = false) :
    (facePerm (rot σ) e).2 = false ∧ (facePerm (rot σ) e).1.2 = e.1.2 - 1 := by
  obtain ⟨⟨ψ, i⟩, b⟩ := e
  simp only at he
  subst he
  exact ⟨rfl, rfl⟩

lemma facePerm_iterate_false_snd (d : Dart Φ n) (hd : d.2 = false) (k : ℕ) :
    ((facePerm (rot σ))^[k] d).2 = false ∧
      ((facePerm (rot σ))^[k] d).1.2 = d.1.2 - (k : Fin (n + 1)) := by
  induction k with
  | zero => simpa using hd
  | succ k ih =>
    rw [iterate_succ_apply']
    obtain ⟨h1, h2⟩ := facePerm_false_snd σ _ ih.1
    refine ⟨h1, ?_⟩
    rw [h2, ih.2]
    push_cast
    ring

/-- The darts `in`: `in i ψ = ((σᵢ • ψ, i), false)`, at the vertex `ψ`. -/
def inn (i : Fin (n + 1)) (ψ : Φ) : Dart Φ n := ((σ i • ψ, i), false)

@[simp] lemma facePerm_inn (i : Fin (n + 1)) (ψ : Φ) :
    facePerm (rot σ) (inn σ i ψ) = inn σ (i - 1) (σ i • ψ) := rfl

@[simp] lemma vtx_inn (i : Fin (n + 1)) (ψ : Φ) : vtx σ (inn σ i ψ) = ψ := by
  simp [inn]

/-- The product `σ₀ ⋯ σᵢ` of the first `i + 1` elements. -/
def prefixProd (i : ℕ) : F := ((List.ofFn σ).take (i + 1)).prod

lemma prefixProd_zero : prefixProd σ 0 = σ 0 := by
  simp [prefixProd, List.ofFn_succ]

lemma prefixProd_succ (i : ℕ) (hi : i + 1 < n + 1) :
    prefixProd σ (i + 1) = prefixProd σ i * σ ⟨i + 1, hi⟩ := by
  rw [prefixProd, prefixProd, List.take_add_one, List.prod_append, List.getElem?_ofFn]
  simp [hi]

/-- The product `τ = σ₀ ⋯ σₙ`. -/
def tau : F := (List.ofFn σ).prod

lemma prefixProd_last : prefixProd σ n = tau σ := by
  simp [prefixProd, tau, List.take_of_length_le]

omit [MulAction F Φ] in
lemma fin_mk_succ_sub_one (i : ℕ) (hi : i + 1 < n + 1) :
    (⟨i + 1, hi⟩ : Fin (n + 1)) - 1 = ⟨i, by omega⟩ := by
  rw [sub_eq_iff_eq_add]
  ext
  rw [Fin.val_add_one_of_lt (by rw [Fin.lt_def]; simp; omega)]

omit [MulAction F Φ] in
lemma fin_zero_sub_one : (0 : Fin (n + 1)) - 1 = Fin.last n := by
  rw [sub_eq_iff_eq_add, Fin.last_add_one]

/-- Going `i + 1` steps around a face from `in i ψ` gives `in n ((σ₀ ⋯ σᵢ) • ψ)`. -/
lemma facePerm_iterate_inn (i : ℕ) (hi : i < n + 1) (ψ : Φ) :
    (facePerm (rot σ))^[i + 1] (inn σ ⟨i, hi⟩ ψ) =
      inn σ (Fin.last n) (prefixProd σ i • ψ) := by
  induction i generalizing ψ with
  | zero =>
    rw [iterate_one, facePerm_inn, prefixProd_zero, Fin.mk_zero, fin_zero_sub_one]
  | succ i ih =>
    rw [iterate_succ_apply, facePerm_inn, fin_mk_succ_sub_one i hi, ih (by omega),
      prefixProd_succ σ i hi, mul_smul]

/-- Going once around the face of `in n ψ` (`n + 1` steps) gives `in n (τ • ψ)`. -/
lemma facePerm_iterate_inn_last (ψ : Φ) :
    (facePerm (rot σ))^[n + 1] (inn σ (Fin.last n) ψ) = inn σ (Fin.last n) (tau σ • ψ) := by
  rw [← prefixProd_last]
  exact facePerm_iterate_inn σ n (Nat.lt_succ_self n) ψ

lemma facePerm_iterate_inn_mul (ψ : Φ) (q : ℕ) :
    (facePerm (rot σ))^[(n + 1) * q] (inn σ (Fin.last n) ψ) =
      inn σ (Fin.last n) (tau σ ^ q • ψ) := by
  induction q generalizing ψ with
  | zero => simp
  | succ q ih =>
    rw [mul_add, mul_one, iterate_add_apply, facePerm_iterate_inn_last, ih, ← mul_smul,
      ← pow_succ]

lemma inn_injective (i : Fin (n + 1)) : Injective (inn σ i : Φ → Dart Φ n) := by
  intro ψ ψ' h
  simp only [inn, Prod.mk.injEq, and_true] at h
  exact smul_left_cancel _ h

lemma inn_inv_smul (i : Fin (n + 1)) (w : Φ) : inn σ i ((σ i)⁻¹ • w) = ((w, i), false) := by
  simp [inn]

/-! ### Orbits of one element -/

/-- `ψ'` lies in the orbit of `ψ` under the powers of `g`. -/
def SameOrbit (g : F) (ψ ψ' : Φ) : Prop := ∃ k : ℤ, g ^ k • ψ = ψ'

omit [MulAction F Φ] in
lemma SameOrbit.symm {g : F} {ψ ψ' : Φ} [MulAction F Φ] (h : SameOrbit g ψ ψ') :
    SameOrbit g ψ' ψ := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨-k, by rw [← mul_smul, ← zpow_add, neg_add_cancel, zpow_zero, one_smul]⟩

lemma SameOrbit.trans {g : F} {ψ ψ' ψ'' : Φ} (h : SameOrbit g ψ ψ') (h' : SameOrbit g ψ' ψ'') :
    SameOrbit g ψ ψ'' := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨k', rfl⟩ := h'
  exact ⟨k' + k, by rw [zpow_add, mul_smul]⟩

lemma sameOrbit_iff_orbitRel {g : F} {ψ ψ' : Φ} :
    SameOrbit g ψ ψ' ↔ MulAction.orbitRel (Subgroup.zpowers g) Φ ψ' ψ := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨g ^ k, Subgroup.zpow_mem_zpowers g k⟩, rfl⟩
  · rintro ⟨⟨h, hh⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ⟨k, rfl⟩

section Finite

variable [Finite Φ]

lemma period_pos (g : F) (ψ : Φ) : 0 < MulAction.period g ψ :=
  minimalPeriod_perm_pos (MulAction.toPerm g) ψ

/-- In a finite set, the orbit of `ψ` under the powers of `g` is reached by natural powers of
any `g'` with `g'⁻¹ = g` or `g' = g`. -/
lemma exists_pow_eq_of_sameOrbit {g : F} {ψ ψ' : Φ} (h : SameOrbit g ψ ψ') :
    ∃ m : ℕ, g⁻¹ ^ m • ψ = ψ' := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨((-k) % (MulAction.period g⁻¹ ψ : ℤ)).toNat, ?_⟩
  have hP : (0 : ℤ) < MulAction.period g⁻¹ ψ := by exact_mod_cast period_pos g⁻¹ ψ
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hP.ne'),
    MulAction.zpow_mod_period_smul, inv_zpow', neg_neg]

lemma exists_pow_eq_of_sameOrbit' {g : F} {ψ ψ' : Φ} (h : SameOrbit g ψ ψ') :
    ∃ m : ℕ, g ^ m • ψ = ψ' := by
  obtain ⟨m, hm⟩ := exists_pow_eq_of_sameOrbit (g := g⁻¹) (ψ := ψ) (ψ' := ψ') (by
    obtain ⟨k, rfl⟩ := h
    exact ⟨-k, by rw [inv_zpow', neg_neg]⟩)
  exact ⟨m, by rwa [inv_inv] at hm⟩

/-- The quotient of `Φ` by the orbits of the powers of `g`. -/
abbrev OrbitQuot (g : F) (Φ : Type*) [MulAction F Φ] :=
  Quotient (MulAction.orbitRel (Subgroup.zpowers g) Φ)

open Classical in
/-- A list of representatives of the orbits of the powers of `g` (one point in each orbit). -/
noncomputable def orbitReps (g : F) : List Φ :=
  letI := Fintype.ofFinite (OrbitQuot g Φ)
  (Finset.univ : Finset (OrbitQuot g Φ)).toList.map Quotient.out

lemma orbitReps_nodup (g : F) : (orbitReps g : List Φ).Nodup := by
  classical
  unfold orbitReps
  exact (Finset.nodup_toList _).map fun q q' h ↦ Quotient.out_inj.mp h

lemma exists_mem_orbitReps (g : F) (ψ : Φ) : ∃ r ∈ (orbitReps g : List Φ), SameOrbit g r ψ := by
  classical
  refine ⟨(Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) Φ) ψ).out, ?_, ?_⟩
  · unfold orbitReps
    exact List.mem_map.mpr ⟨_, Finset.mem_toList.mpr (@Finset.mem_univ _ (Fintype.ofFinite _) _),
      rfl⟩
  · refine (sameOrbit_iff_orbitRel.mpr ?_).symm
    exact Quotient.exact (Quotient.out_eq _)

lemma eq_of_mem_orbitReps {g : F} {r r' : Φ} (hr : r ∈ (orbitReps g : List Φ))
    (hr' : r' ∈ (orbitReps g : List Φ)) (h : SameOrbit g r r') : r = r' := by
  classical
  unfold orbitReps at hr hr'
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp hr
  obtain ⟨q', -, rfl⟩ := List.mem_map.mp hr'
  have h' : (Quotient.mk _ q'.out : OrbitQuot g Φ) = Quotient.mk _ q.out :=
    Quotient.sound (sameOrbit_iff_orbitRel.mp h)
  rw [Quotient.out_eq, Quotient.out_eq] at h'
  rw [h']

/-! ### The faces -/

omit [Finite Φ] in
lemma sameCycle_facePerm_of_iterate (d : Dart Φ n) (k : ℕ) :
    (facePerm (rot σ)).SameCycle d ((facePerm (rot σ))^[k] d) :=
  ⟨k, by rw [zpow_natCast, Equiv.Perm.iterate_eq_pow]⟩

lemma exists_iterate_of_sameCycle {d d' : Dart Φ n} (h : (facePerm (rot σ)).SameCycle d d') :
    ∃ k : ℕ, (facePerm (rot σ))^[k] d = d' := by
  obtain ⟨k, -, hk⟩ := h.exists_pow_eq'
  exact ⟨k, by rw [Equiv.Perm.iterate_eq_pow, hk]⟩

lemma eq_of_sameCycle_true {ψ : Φ} {i : Fin (n + 1)} {d : Dart Φ n}
    (h : (facePerm (rot σ)).SameCycle ((ψ, i), true) d) :
    ∃ ψ', d = ((ψ', i), true) ∧ SameOrbit (σ i) ψ ψ' := by
  obtain ⟨k, rfl⟩ := exists_iterate_of_sameCycle σ h
  rw [facePerm_iterate_true]
  exact ⟨_, rfl, ⟨-k, by rw [zpow_neg, zpow_natCast, inv_pow]⟩⟩

lemma sameCycle_true_of_sameOrbit {ψ ψ' : Φ} {i : Fin (n + 1)} (h : SameOrbit (σ i) ψ ψ') :
    (facePerm (rot σ)).SameCycle ((ψ, i), true) ((ψ', i), true) := by
  obtain ⟨m, rfl⟩ := exists_pow_eq_of_sameOrbit h
  have := sameCycle_facePerm_of_iterate σ ((ψ, i), true) m
  rwa [facePerm_iterate_true] at this

lemma sameOrbit_of_sameCycle_inn {ψ ψ' : Φ}
    (h : (facePerm (rot σ)).SameCycle (inn σ (Fin.last n) ψ) (inn σ (Fin.last n) ψ')) :
    SameOrbit (tau σ) ψ ψ' := by
  obtain ⟨k, hk⟩ := exists_iterate_of_sameCycle σ h
  have hcol := (facePerm_iterate_false_snd σ (inn σ (Fin.last n) ψ) rfl k).2
  rw [hk] at hcol
  simp only [inn] at hcol
  obtain ⟨q, rfl⟩ := (Fin.natCast_eq_zero).mp (sub_eq_self.mp hcol.symm)
  rw [facePerm_iterate_inn_mul] at hk
  exact ⟨q, by rw [zpow_natCast]; exact inn_injective σ _ hk⟩

lemma sameCycle_inn_of_sameOrbit {ψ ψ' : Φ} (h : SameOrbit (tau σ) ψ ψ') :
    (facePerm (rot σ)).SameCycle (inn σ (Fin.last n) ψ) (inn σ (Fin.last n) ψ') := by
  obtain ⟨m, rfl⟩ := exists_pow_eq_of_sameOrbit' h
  have := sameCycle_facePerm_of_iterate σ (inn σ (Fin.last n) ψ) ((n + 1) * m)
  rwa [facePerm_iterate_inn_mul] at this

omit [Finite Φ] in
lemma exists_sameCycle_inn (d : Dart Φ n) (hd : d.2 = false) :
    ∃ u, (facePerm (rot σ)).SameCycle (inn σ (Fin.last n) u) d := by
  obtain ⟨⟨w, ⟨i, hi⟩⟩, b⟩ := d
  simp only at hd
  subst hd
  rw [← inn_inv_smul σ ⟨i, hi⟩ w]
  have := sameCycle_facePerm_of_iterate σ (inn σ ⟨i, hi⟩ ((σ ⟨i, hi⟩)⁻¹ • w)) (i + 1)
  rw [facePerm_iterate_inn] at this
  exact ⟨_, this.symm⟩

variable [DecidableEq Φ]

/-- **The faces of the Schreier graph**, one dart in each face: `out i ψ = ((ψ, i), true)` for each
`i` and each representative `ψ` of an orbit of `σᵢ`, and `in n ψ` for each representative `ψ` of
an orbit of `τ = σ₀ ⋯ σₙ`. -/
noncomputable def faceDarts : List (Dart Φ n) :=
  ((List.finRange (n + 1)).flatMap (fun i ↦ (orbitReps (σ i)).map fun ψ ↦ ((ψ, i), true)) ++
    (orbitReps (tau σ)).map (inn σ (Fin.last n))).dedup

lemma mem_faceDarts {d : Dart Φ n} : d ∈ faceDarts σ ↔
    (∃ i, ∃ ψ ∈ (orbitReps (σ i) : List Φ), d = ((ψ, i), true)) ∨
      ∃ ψ ∈ (orbitReps (tau σ) : List Φ), d = inn σ (Fin.last n) ψ := by
  simp only [faceDarts, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_finRange,
    true_and, List.mem_map]
  constructor
  · rintro (⟨i, ψ, hψ, rfl⟩ | ⟨ψ, hψ, rfl⟩)
    · exact Or.inl ⟨i, ψ, hψ, rfl⟩
    · exact Or.inr ⟨ψ, hψ, rfl⟩
  · rintro (⟨i, ψ, hψ, rfl⟩ | ⟨ψ, hψ, rfl⟩)
    · exact Or.inl ⟨i, ψ, hψ, rfl⟩
    · exact Or.inr ⟨ψ, hψ, rfl⟩

lemma exists_mem_faceDarts (d : Dart Φ n) :
    ∃ f ∈ faceDarts σ, (facePerm (rot σ)).SameCycle f d := by
  obtain ⟨⟨ψ, i⟩, b⟩ := d
  cases b
  · obtain ⟨u, hu⟩ := exists_sameCycle_inn σ ((ψ, i), false) rfl
    obtain ⟨r, hr, hru⟩ := exists_mem_orbitReps (tau σ) u
    exact ⟨_, (mem_faceDarts σ).mpr (Or.inr ⟨r, hr, rfl⟩),
      (sameCycle_inn_of_sameOrbit σ hru).trans hu⟩
  · obtain ⟨r, hr, hrψ⟩ := exists_mem_orbitReps (σ i) ψ
    exact ⟨_, (mem_faceDarts σ).mpr (Or.inl ⟨i, r, hr, rfl⟩), sameCycle_true_of_sameOrbit σ hrψ⟩

lemma eq_of_mem_faceDarts {d d' : Dart Φ n} (hd : d ∈ faceDarts σ) (hd' : d' ∈ faceDarts σ)
    (h : (facePerm (rot σ)).SameCycle d d') : d = d' := by
  rcases (mem_faceDarts σ).mp hd with ⟨i, r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;>
    rcases (mem_faceDarts σ).mp hd' with ⟨i', r', hr', rfl⟩ | ⟨r', hr', rfl⟩
  · obtain ⟨ψ', h', hψ'⟩ := eq_of_sameCycle_true σ h
    simp only [Prod.mk.injEq, and_true] at h'
    obtain ⟨rfl, rfl⟩ := h'
    rw [eq_of_mem_orbitReps hr hr' hψ']
  · obtain ⟨ψ', h', -⟩ := eq_of_sameCycle_true σ h
    simp [inn] at h'
  · obtain ⟨ψ', h', -⟩ := eq_of_sameCycle_true σ h.symm
    simp [inn] at h'
  · rw [eq_of_mem_orbitReps hr hr' (sameOrbit_of_sameCycle_inn σ h)]

/-- **The Schreier graph is a ribbon graph**: for a list `Φl` of all points of `Φ` (without
repetitions), the rotations at the points of `Φl` and the faces through `Ribbon.Schreier.faceDarts`
form a ribbon graph. -/
theorem isRibbon {Φl : List Φ} (hΦl : Φl.Nodup) (hall : ∀ ψ, ψ ∈ Φl) :
    IsRibbon (Φl.map fun ψ ↦ cyc (rot σ) ((ψ, 0), true))
      ((faceDarts σ).map (cyc (facePerm (rot σ)))) := by
  have := isRibbon_of_perm (rot σ) (Vr := Φl.map fun ψ ↦ ((ψ, 0), true)) (Fr := faceDarts σ)
    (fun d ↦ ⟨((vtx σ d, 0), true), List.mem_map_of_mem (hall _),
      (sameCycle_rot_iff σ).mpr rfl⟩)
    (hΦl.map fun ψ ψ' h ↦ by simpa using h)
    (fun v hv w hw h ↦ by
      obtain ⟨ψ, -, rfl⟩ := List.mem_map.mp hv
      obtain ⟨ψ', -, rfl⟩ := List.mem_map.mp hw
      have := (sameCycle_rot_iff σ).mp h
      simp only [vtx_true] at this
      rw [this])
    (exists_mem_faceDarts σ) (List.nodup_dedup _) (fun v hv w hw h ↦ eq_of_mem_faceDarts σ hv hw h)
  simpa [List.map_map, Function.comp_def] using this

end Finite

end Ribbon.Schreier
