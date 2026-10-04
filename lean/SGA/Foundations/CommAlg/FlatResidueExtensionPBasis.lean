/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.FlatResidueExtensionFree
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.PowerBasis
import Mathlib.Order.Zorn
import Mathlib.Data.Set.Finite.Lattice

/-!
# `p`-bases of fields of characteristic `p`

Let `ψ : F →+* L` be a map of fields of characteristic `p > 0` such that every `p`-th power of
`L` lies in its image (for example `F ⊆ L` with `L^p ⊆ F`, or `F = L = k` with `ψ` the Frobenius).
A subset `S ⊆ L` is a *`p`-basis* of `L` over `F` (EGA 0_IV 21.1.9; Matsumura, *Commutative ring
theory*, §26) if the monomials `s^e = ∏ s^{e_s}` with all `e_s < p` form a basis of `L` over
`ψ(F)`. We state this without subfields: the evaluation `AdjoinRoots p (a|_S) → L`, `c ↦ ψ c`,
`Y_s ↦ s` (`PBasis.evalRoots`, where `ψ (a s) = s^p`) is bijective. Since `AdjoinRoots p (a|_S)`
is free over `F` on the monomials `Y^e` (`e_s < p`), this is the classical definition.

## Main results

* `PBasis.exists_bijective_evalRoots`: `p`-bases exist. By Zorn's lemma there is a maximal
  `p`-independent set `S`; if `x ∉ ψ(F)(S)` then `X^p - x^p` is irreducible over `ψ(F)(S)`, so
  `S ∪ {x}` is still `p`-independent; hence `ψ(F)(S) = L`.
* `PBasis.bijective_evalRootsOf`: the same for any other choice of the `p`-th roots data.
* `exists_isPBasis`: the absolute case, every field `k` of characteristic `p` has a `p`-basis
  over `k^p` (EGA 0_IV 21.4.1).

These are used for the purely inseparable step of EGA 0_III 10.3.1
(`SGA.Foundations.CommAlg.FlatResidueExtensionInseparable`).
-/

open MvPolynomial AdjoinRoots

noncomputable section

universe w

variable {k : Type w} [Field k] (p : ℕ) [ExpChar k p]

/-! ### Existence of `p`-bases

We prove the existence of relative `p`-bases in the following generality, which covers both the
absolute case (`L = F = k`, `ψ` the Frobenius) and the relative case of an extension `F ⊆ L` with
`L^p ⊆ F`. Let `ψ : F →+* L` be a map of fields of characteristic `p` such that every `p`-th power
of `L` lies in its image, with a chosen `a : L → F`, `ψ (a y) = y^p`. For `S ⊆ L` let
`AdjoinRoots p (a|_S) → L`, `c ↦ ψ c`, `Y_s ↦ s` be the evaluation (`PBasis.evalRoots`); `S` is
`p`-independent if it is injective. By Zorn's lemma there is `S` for which it is bijective
(`PBasis.exists_bijective_evalRoots`). -/

namespace PBasis

variable {F L : Type*} [Field F] [Field L] (ψ : F →+* L) (a : L → F)
  (ha : ∀ y, ψ (a y) = y ^ p ^ 1)

/-- The evaluation `AdjoinRoots p b → L`, `c ↦ ψ c`, `Y_s ↦ s`, for a family `b : S → F` with
`ψ (b s) = s^p`. -/
def evalRootsOf (S : Set L) (b : S → F) (hb : ∀ s, ψ (b s) = (s : L) ^ p ^ 1) :
    AdjoinRoots (p ^ 1) b →+* L :=
  Ideal.Quotient.lift _ (eval₂Hom ψ Subtype.val) fun z hz ↦ by
    have : ideal (p ^ 1) b ≤ RingHom.ker (eval₂Hom ψ (Subtype.val : S → L)) := by
      rw [ideal, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂Hom, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
        hb, sub_self]
    exact this hz

lemma evalRootsOf_mk (S : Set L) (b : S → F) (hb : ∀ s, ψ (b s) = (s : L) ^ p ^ 1)
    (P : MvPolynomial S F) : evalRootsOf p ψ S b hb (mk _ _ P) = eval₂ ψ Subtype.val P := rfl

/-- The evaluation `AdjoinRoots p (a|_S) → L`, `c ↦ ψ c`, `Y_s ↦ s`. -/
def evalRoots (S : Set L) : AdjoinRoots (p ^ 1) (fun s : S ↦ a s) →+* L :=
  evalRootsOf p ψ S (fun s : S ↦ a s) fun s ↦ ha s

/-- Bijectivity of the evaluation does not depend on the choice of the family `b`. -/
lemma bijective_evalRootsOf {S : Set L} (h : Function.Bijective (evalRoots p ψ a ha S))
    (b : S → F) (hb : ∀ s, ψ (b s) = (s : L) ^ p ^ 1) :
    Function.Bijective (evalRootsOf p ψ S b hb) := by
  obtain rfl : b = fun s : S ↦ a s := funext fun s ↦ ψ.injective (by rw [hb, ha])
  exact h

lemma evalRoots_mk (S : Set L) (P : MvPolynomial S F) :
    evalRoots p ψ a ha S (mk _ _ P) = eval₂ ψ Subtype.val P := rfl

lemma evalRoots_root (S : Set L) (s : S) : evalRoots p ψ a ha S (root _ _ s) = s := by
  rw [root, evalRoots_mk, eval₂_X]

lemma evalRoots_algebraMap (S : Set L) (c : F) :
    evalRoots p ψ a ha S (algebraMap F _ c) = ψ c := by
  rw [← AlgHom.commutes (mk _ _), evalRoots_mk, algebraMap_eq, eval₂_C]

/-- `S ⊆ L` is `p`-independent (relative to `ψ`): the evaluation `AdjoinRoots p (a|_S) → L` is
injective. -/
def Independent (S : Set L) : Prop := Function.Injective (evalRoots p ψ a ha S)

/-- For `S ⊆ T`, the inclusion `AdjoinRoots q (a|_S) → AdjoinRoots q (a|_T)`. -/
def inclusionMap {S T : Set L} (h : S ⊆ T) (q : ℕ) :
    AdjoinRoots q (fun s : S ↦ a s) →ₐ[F] AdjoinRoots q (fun s : T ↦ a s) :=
  Ideal.quotientMapₐ _ (rename (Set.inclusion h)) (by
    rw [ideal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, Ideal.mem_comap, map_sub, map_pow, rename_X, rename_C]
    exact Ideal.subset_span ⟨Set.inclusion h i, rfl⟩)

omit [Field L] in
lemma inclusionMap_mk {S T : Set L} (h : S ⊆ T) (q : ℕ) (P : MvPolynomial S F) :
    inclusionMap a h q (mk q _ P) = mk q _ (rename (Set.inclusion h) P) := rfl

omit [Field L] in
lemma inclusionMap_root {S T : Set L} (h : S ⊆ T) (q : ℕ) (i : S) :
    inclusionMap a h q (root q _ i) = root q _ (Set.inclusion h i) := by
  rw [root, inclusionMap_mk, rename_X]

lemma evalRoots_inclusionMap {S T : Set L} (h : S ⊆ T)
    (z : AdjoinRoots (p ^ 1) (fun s : S ↦ a s)) :
    evalRoots p ψ a ha T (inclusionMap a h (p ^ 1) z) = evalRoots p ψ a ha S z := by
  obtain ⟨P, rfl⟩ := mk_surjective _ _ z
  rw [inclusionMap_mk, evalRoots_mk, evalRoots_mk, eval₂_rename]
  rfl

lemma independent_empty : Independent p ψ a ha ∅ := by
  rw [Independent, injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨P, rfl⟩ := mk_surjective _ _ z
  have hC : mk (p ^ 1) (fun s : (∅ : Set L) ↦ a s) P = algebraMap F _ (coeff 0 P) := by
    conv_lhs => rw [eq_C_of_isEmpty P, ← algebraMap_eq, AlgHom.commutes]
  rw [hC, evalRoots_algebraMap] at hz
  rw [hC, (injective_iff_map_eq_zero ψ).mp ψ.injective _ hz, map_zero]

lemma independent_sUnion {c : Set (Set L)} (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (h : ∀ S ∈ c, Independent p ψ a ha S) : Independent p ψ a ha (⋃₀ c) := by
  rw [Independent, injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨P, rfl⟩ := mk_surjective _ _ z
  obtain ⟨s, P', rfl⟩ := exists_finset_rename P
  obtain ⟨T, hTc, hsT⟩ := hc.directedOn.exists_mem_subset_of_finite_of_subset_sUnion hne
    (s.finite_toSet.image Subtype.val) (by rintro _ ⟨x, _, rfl⟩; exact x.2)
  have hT : T ⊆ ⋃₀ c := Set.subset_sUnion_of_mem hTc
  let g : s → T := fun x ↦ ⟨x.1.1, hsT ⟨x.1, x.2, rfl⟩⟩
  have hP : rename (Subtype.val : s → ⋃₀ c) P' = rename (Set.inclusion hT) (rename g P') := by
    rw [rename_rename]
    rfl
  rw [hP, ← inclusionMap_mk] at hz ⊢
  rw [evalRoots_inclusionMap] at hz
  rw [h T hTc (hz.trans (map_zero _).symm), map_zero]

variable [ExpChar L p]

/-- The subfield `ψ(F)(S)` of `L`: the image of `AdjoinRoots p (a|_S) → L`. -/
def rangeSubfield (S : Set L) : Subfield L :=
  { (evalRoots p ψ a ha S).range with
    inv_mem' := fun y hy ↦ by
      obtain ⟨t, rfl⟩ := hy
      set G := evalRoots p ψ a ha S
      by_cases ht : G t = 0
      · rw [ht, inv_zero]
        exact ⟨0, map_zero G⟩
      · refine ⟨t ^ (p - 1) * algebraMap F _ (a (G t)⁻¹), ?_⟩
        have hp1 : 1 ≤ p := expChar_pos L p
        have : (G t)⁻¹ ^ p ^ 1 = (G t)⁻¹ ^ (p - 1) * (G t)⁻¹ := by
          rw [← pow_succ, Nat.sub_add_cancel hp1]
          exact congrArg (fun m ↦ (G t)⁻¹ ^ m) (pow_one p)
        rw [map_mul, map_pow, evalRoots_algebraMap, ha, this, ← mul_assoc,
          ← mul_pow, mul_inv_cancel₀ ht, one_pow, one_mul] }

/-- The key step: if `S` is `p`-independent and `x ∉ ψ(F)(S)`, then `S ∪ {x}` is
`p`-independent, because `X^p - x^p` is irreducible over `ψ(F)(S)`. -/
lemma independent_insert (hp : p.Prime) {S : Set L} (hS : Independent p ψ a ha S) {x : L}
    (hx : x ∉ rangeSubfield p ψ a ha S) : Independent p ψ a ha (insert x S) := by
  set G := evalRoots p ψ a ha S
  set G' := evalRoots p ψ a ha (insert x S)
  set ι := inclusionMap a (Set.subset_insert x S) (p ^ 1)
  set Yx : AdjoinRoots (p ^ 1) (fun s : ↥(insert x S) ↦ a s) := root _ _ ⟨x, Set.mem_insert x S⟩
  -- every element is `∑_{j < p} ι(t_j) Y_x^j`
  have hdec : ∀ z, ∃ t : Fin p → AdjoinRoots (p ^ 1) (fun s : S ↦ a s),
      z = ∑ j, ι (t j) * Yx ^ (j : ℕ) := by
    let _ : Algebra (AdjoinRoots (p ^ 1) (fun s : S ↦ a s))
        (AdjoinRoots (p ^ 1) (fun s : ↥(insert x S) ↦ a s)) := ι.toRingHom.toAlgebra
    let M := Submodule.span (AdjoinRoots (p ^ 1) (fun s : S ↦ a s))
      (Set.range fun j : Fin p ↦ Yx ^ (j : ℕ))
    have h1 : (1 : AdjoinRoots (p ^ 1) (fun s : ↥(insert x S) ↦ a s)) ∈ M :=
      Submodule.subset_span ⟨⟨0, hp.pos⟩, pow_zero _⟩
    have hsmul : ∀ r m, m ∈ M → ι r * m ∈ M := fun r m hm ↦ M.smul_mem r hm
    have hX : ∀ m ∈ M, ∀ v : ↥(insert x S),
        m * root (p ^ 1) (fun s : ↥(insert x S) ↦ a s) v ∈ M := by
      intro m hm v
      induction hm using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        rcases v with ⟨v, hv⟩
        rcases Set.mem_insert_iff.mp hv with rfl | hvS
        · by_cases hj : (j : ℕ) + 1 < p
          · exact Submodule.subset_span ⟨⟨j + 1, hj⟩, pow_succ Yx j⟩
          · have hjp : (j : ℕ) + 1 = p := by omega
            have hroot : Yx ^ p = ι (algebraMap F _ (a v)) := by
              rw [AlgHom.commutes]
              exact (congrArg (fun m ↦ Yx ^ m) (pow_one p)).symm.trans
                (root_pow (p ^ 1) (fun s : ↥(insert v S) ↦ a s) ⟨v, hv⟩)
            have : Yx ^ (j : ℕ) * Yx = ι (algebraMap F _ (a v)) * 1 := by
              rw [mul_one, ← hroot, ← pow_succ, hjp]
            change Yx ^ (j : ℕ) * Yx ∈ M
            rw [this]
            exact hsmul _ _ h1
        · have hmem : ι (root (p ^ 1) (fun s : S ↦ a s) ⟨v, hvS⟩) =
              root (p ^ 1) (fun s : ↥(insert x S) ↦ a s) ⟨v, hv⟩ :=
            inclusionMap_root a (Set.subset_insert x S) (p ^ 1) ⟨v, hvS⟩
          rw [← hmem, mul_comm]
          exact hsmul _ _ (Submodule.subset_span ⟨j, rfl⟩)
      | zero => rw [zero_mul]; exact zero_mem _
      | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
      | smul r a _ ha => rw [smul_mul_assoc]; exact M.smul_mem r ha
    have hall : ∀ z, z ∈ M := by
      intro z
      obtain ⟨P, rfl⟩ := mk_surjective _ _ z
      induction P using MvPolynomial.induction_on with
      | C c =>
        have : mk (p ^ 1) _ (C c) = ι (algebraMap F _ c) * 1 := by
          rw [mul_one, AlgHom.commutes, ← algebraMap_eq, AlgHom.commutes]
        rw [this]
        exact hsmul _ _ h1
      | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
      | mul_X P v hP => rw [map_mul]; exact hX _ hP v
    intro z
    obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp (hall z)
    exact ⟨t, ht.symm⟩
  -- `1, x, …, x^{p-1}` are linearly independent over `ψ(F)(S)`
  set L' := rangeSubfield p ψ a ha S
  have hxp : x ^ p ∈ L' :=
    ⟨algebraMap F _ (a x), by rw [evalRoots_algebraMap, ha, pow_one]⟩
  have hirr : Irreducible (Polynomial.X ^ p - Polynomial.C (⟨x ^ p, hxp⟩ : L')) := by
    refine X_pow_sub_C_irreducible_of_prime hp fun b hb ↦ hx ?_
    have hb' : (b : L) ^ p = x ^ p := congrArg Subtype.val hb
    have : (b : L) = x := frobenius_inj L p (by simpa [frobenius_def] using hb')
    exact this ▸ b.2
  have hmin : minpoly L' x = Polynomial.X ^ p - Polynomial.C (⟨x ^ p, hxp⟩ : L') :=
    (minpoly.eq_of_irreducible_of_monic hirr
      (by rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]; exact sub_self _)
      (Polynomial.monic_X_pow_sub_C _ hp.ne_zero)).symm
  have hdeg : (minpoly L' x).natDegree = p := by rw [hmin, Polynomial.natDegree_X_pow_sub_C]
  have hli : LinearIndependent L' fun j : Fin p ↦ x ^ (j : ℕ) := by
    have := (linearIndependent_pow (K := L') x).comp (Fin.cast hdeg.symm) (Fin.cast_injective _)
    simpa [Function.comp_def] using this
  -- conclusion
  rw [Independent, injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨t, rfl⟩ := hdec z
  have hG : G' (∑ j, ι (t j) * Yx ^ (j : ℕ)) = ∑ j, G (t j) * x ^ (j : ℕ) := by
    simp only [map_sum, map_mul, map_pow, G', ι, evalRoots_inclusionMap, Yx, evalRoots_root]
    rfl
  rw [hG] at hz
  have ht0 := Fintype.linearIndependent_iff.mp hli (fun j ↦ ⟨G (t j), t j, rfl⟩) hz
  have : ∀ j, t j = 0 := fun j ↦
    (injective_iff_map_eq_zero G).mp hS _ (congrArg Subtype.val (ht0 j))
  simp [this]

/-- Existence of relative `p`-bases: there is `S ⊆ L` such that `AdjoinRoots p (a|_S) → L`,
`c ↦ ψ c`, `Y_s ↦ s` is bijective. -/
theorem exists_bijective_evalRoots (hp : p.Prime) :
    ∃ S : Set L, Function.Bijective (evalRoots p ψ a ha S) := by
  obtain ⟨S, -, hS⟩ := zorn_subset_nonempty {S : Set L | Independent p ψ a ha S}
    (fun c hcS hc hne ↦ ⟨⋃₀ c, independent_sUnion p ψ a ha hc hne hcS,
      fun s hs ↦ Set.subset_sUnion_of_mem hs⟩) ∅ (independent_empty p ψ a ha)
  refine ⟨S, hS.prop, fun y ↦ ?_⟩
  by_contra hy
  have hy' : y ∉ rangeSubfield p ψ a ha S := fun ⟨z, hz⟩ ↦ hy ⟨z, hz⟩
  have hyS : y ∈ S := hS.mem_of_prop_insert (independent_insert p ψ a ha hp hS.prop hy')
  exact hy ⟨root _ _ ⟨y, hyS⟩, evalRoots_root _ _ _ _ _ _⟩

end PBasis

/-- `S ⊆ k` is a `p`-basis of `k` (over `k^p`; EGA 0_IV 21.1.9, Matsumura §26): the monomials
`s^e` with all `e_s < p` form a basis of `k` over `k^p`, i.e. the ring map
`AdjoinRoots p S → k`, `c ↦ c^p`, `Y_s ↦ s` is bijective. -/
def IsPBasis (S : Set k) : Prop :=
  Function.Bijective (PBasis.evalRoots p (iterateFrobenius k p 1) id (fun _ ↦ rfl) S)

/-- Every field of characteristic `p` has a `p`-basis (EGA 0_IV 21.4.1; Matsumura, *Commutative
ring theory*, Theorem 26.5). -/
theorem exists_isPBasis (hp : p.Prime) : ∃ S : Set k, IsPBasis p S :=
  PBasis.exists_bijective_evalRoots p (iterateFrobenius k p 1) id (fun _ ↦ rfl) hp
