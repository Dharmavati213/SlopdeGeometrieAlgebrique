/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Cech
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Exactness of Čech complexes of "quasi-coherent" presheaves for standard covers

Let `P` be a presheaf of abelian groups on a space `X` whose sections are modules over a
commutative ring `R`, with `R`-linear restriction maps. Let `U₁, …, Uₙ` be opens and
`f₁, …, fₙ ∈ R` such that, for every finite intersection `U_y` of the `Uᵢ`, the restriction
`P(U_y) → P(U_k ∩ U_y)` is a localization at `f_k` (as for a quasi-coherent sheaf and the standard
opens `Uᵢ = D(fᵢ)`). Suppose that `g ∈ √(f₁, …, fₙ)` acts invertibly on all `P(U_y)` (as for
`U = ⋃ D(fᵢ) = D(g)`). Then the Čech complex of `P` for `(Uᵢ)` is exact in positive degrees
(the algebra behind Stacks Project, Tag 01X9; cf. EGA III §1.2–1.3).

The proof is the usual one: after inverting `f_k`, the cover contains the whole space, so
`c ↦ c_{k,-}` is a contracting homotopy (`TopCat.Presheaf.cechD_cons`); clearing denominators
shows that `f_kᴺ • c` is a coboundary for every cocycle `c`, and `g ∈ √(f₁, …, fₙ)` then gives
that `c` itself is a coboundary.
-/

universe w v u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

variable {X : TopCat.{u}} (P : TopCat.Presheaf AddCommGrpCat.{v} X) {R : Type*} [CommRing R]
  [∀ V : Opens X, Module R (P.obj (op V))]
  (hlin : ∀ ⦃V W : Opens X⦄ (h : W ≤ V) (r : R) (s : P.obj (op V)),
    P.map (homOfLE h).op (r • s) = r • P.map (homOfLE h).op s)

/-- A restriction map, as an `R`-linear map. -/
noncomputable def resₗ {V W : Opens X} (h : W ≤ V) : P.obj (op V) →ₗ[R] P.obj (op W) where
  toFun := P.map (homOfLE h).op
  map_add' := map_add _
  map_smul' := hlin h

@[simp]
lemma resₗ_apply {V W : Opens X} (h : W ≤ V) (s : P.obj (op V)) :
    resₗ P hlin h s = P.map (homOfLE h).op s :=
  rfl

variable {ι : Type w} (U : ι → Opens X)

include hlin in
lemma cechD_smul (m : ℕ) (r : R) (c : CechCochain U P m) :
    cechD U P m (r • c) = r • cechD U P m c := by
  funext x
  simp only [cechD_apply, Pi.smul_apply, hlin, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _

/-- The Čech differential, as an `R`-linear map. -/
noncomputable def cechDₗ (m : ℕ) : CechCochain U P m →ₗ[R] CechCochain U P (m + 1) where
  toFun := cechD U P m
  map_add' := map_add _
  map_smul' := cechD_smul P hlin U m

lemma cechDₗ_apply (m : ℕ) (c : CechCochain U P m) : cechDₗ P hlin U m c = cechD U P m c :=
  rfl

variable {P} in
include hlin in
/-- Clearing denominators in the contracting homotopy: if every restriction
`P(U_y) → P(U_k ∩ U_y)` is a localization at `a`, then `aᴺ • c` is a coboundary for every
positive-degree cocycle `c`. -/
lemma exists_pow_smul_eq_cechD [Finite ι] (a : R) (k : ι)
    (hloc : ∀ {m : ℕ} (y : Fin (m + 1) → ι),
      IsLocalizedModule.Away a (resₗ P hlin (cechOpen_cons_le U k y)))
    {p : ℕ} (c : CechCochain U P (p + 1)) (hc : cechD U P (p + 1) c = 0) :
    ∃ (e : ℕ) (b : CechCochain U P p), cechD U P p b = a ^ e • c := by
  have : Fintype ι := Fintype.ofFinite ι
  classical
  -- lifts of `c_{k, y}` after multiplying by a power of `a`
  choose e b hb using fun y : Fin (p + 1) → ι ↦
    IsLocalizedModule.Away.surj (resₗ P hlin (cechOpen_cons_le U k y)) a (c (Fin.cons k y))
  let E := Finset.univ.sup e
  let b' : CechCochain U P p := fun y ↦ a ^ (E - e y) • b y
  have hb' (y : Fin (p + 1) → ι) : resₗ P hlin (cechOpen_cons_le U k y) (b' y) =
      a ^ E • c (Fin.cons k y) := by
    rw [LinearMap.map_smul, ← hb, smul_smul, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ y))]
  -- the defect `d b' - aᴱ c` vanishes after restriction to `U_k`
  have hδ (x : Fin (p + 2) → ι) : resₗ P hlin (cechOpen_cons_le U k x)
      (cechD U P p b' x - a ^ E • c x) = resₗ P hlin (cechOpen_cons_le U k x) 0 := by
    have hcone := (cechD_cons U P k c x).symm.trans (congrFun hc (Fin.cons k x))
    rw [Pi.zero_apply, sub_eq_zero] at hcone
    rw [map_zero, map_sub, LinearMap.map_smul, resₗ_apply, resₗ_apply, hcone, cechD_apply,
      map_sum, Finset.smul_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_zsmul, map_map_apply, smul_comm, ← hlin, ← hb', resₗ_apply, map_map_apply]
  choose e' he' using fun x ↦ IsLocalizedModule.Away.exists_of_eq a (hδ x)
  let E' := Finset.univ.sup e'
  refine ⟨E' + E, a ^ E' • b', funext fun x ↦ ?_⟩
  have hx := he' x
  rw [smul_zero, smul_sub, sub_eq_zero] at hx
  have hx' : a ^ E' • cechD U P p b' x = a ^ E' • a ^ E • c x := by
    obtain ⟨d, hd⟩ : ∃ d, E' = d + e' x :=
      ⟨E' - e' x, (Nat.sub_add_cancel (Finset.le_sup (f := e') (Finset.mem_univ x))).symm⟩
    rw [hd, pow_add, mul_smul, mul_smul, hx]
  rw [cechD_smul P hlin, Pi.smul_apply, hx', pow_add, mul_smul]
  rfl

variable {P} in
include hlin in
/-- **Exactness of Čech complexes for standard covers** (cf. Stacks Tag 01X9). Let
`f : Fin n → R` and `g ∈ √(f)`. Assume that `g` acts invertibly on every `P(U_x)` and that each
restriction `P(U_y) → P(U_k ∩ U_y)` is a localization at `f k`. Then the Čech complex of `P` for
`U` is exact in positive degrees. -/
theorem cechComplex_exactAt_of_isLocalizedModule {n : ℕ} (U : Fin n → Opens X) (f : Fin n → R)
    (g : R) (hg : g ∈ (Ideal.span (Set.range f)).radical)
    (hunit : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
      IsUnit (algebraMap R (Module.End R (P.obj (op (cechOpen U x)))) g))
    (hloc : ∀ {m : ℕ} (k : Fin n) (y : Fin (m + 1) → Fin n),
      IsLocalizedModule.Away (f k) (resₗ P hlin (cechOpen_cons_le U k y)))
    (p : ℕ) : (cechComplex U P).ExactAt (p + 1) := by
  rw [cechComplex_exactAt_succ_iff]
  intro c hc
  let N := LinearMap.range (cechDₗ P hlin U p)
  let T : Ideal R := N.colon {c}
  have hfT (k : Fin n) : f k ∈ T.radical := by
    obtain ⟨e, b, hb⟩ := exists_pow_smul_eq_cechD hlin U (f k) k (hloc k) c hc
    exact ⟨e, Submodule.mem_colon_singleton.mpr (show f k ^ e • c ∈ N from ⟨b, hb⟩)⟩
  have hgT : g ∈ T.radical := by
    have h := Ideal.radical_mono (Ideal.span_le.mpr (Set.range_subset_iff.mpr hfT)) hg
    rwa [Ideal.radical_idem] at h
  obtain ⟨m, hm⟩ := hgT
  obtain ⟨b, hb⟩ := Submodule.mem_colon_singleton.mp hm
  -- `g ^ m` acts bijectively on Čech cochains
  have hbij {q : ℕ} (x : Fin (q + 1) → Fin n) :
      Function.Bijective fun s : P.obj (op (cechOpen U x)) ↦ g ^ m • s := by
    have := ((hunit x).pow m)
    rw [← map_pow, Module.End.isUnit_iff] at this
    exact this
  choose b' hb' using fun x ↦ (hbij x).2 (b x)
  refine ⟨b', funext fun x ↦ (hbij x).1 ?_⟩
  change g ^ m • cechD U P p b' x = g ^ m • c x
  rw [← Pi.smul_apply, ← cechD_smul P hlin, show g ^ m • b' = b from funext hb']
  exact congrFun hb x

end TopCat.Presheaf
