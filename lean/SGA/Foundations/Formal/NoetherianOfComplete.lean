/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic
import SGA.Foundations.Formal.AdicRing

/-!
# Complete rings with noetherian reduction are noetherian

Let `R` be a ring, complete and separated for the `I`-adic topology, with `I` finitely generated.
If `R ⧸ I` is noetherian, so is `R` (`Ideal.isNoetherianRing_of_isAdicComplete`; Stacks,
Tag 05GH). Consequently (EGA 0_I, 7.2.8) a ring `R`, complete and separated for the `I`-adic
topology, is noetherian if and only if `R ⧸ I` is noetherian and `I ⧸ I²` is a finite
`R ⧸ I`-module (`Ideal.isNoetherianRing_iff_of_isAdicComplete`).

The proof follows the usual one through the associated graded ring, phrased with polynomials:
if `I = (t₁, …, tᵣ)`, the graded pieces `Iⁿ ⧸ Iⁿ⁺¹` are the images of the homogeneous
polynomials of degree `n` in `(R ⧸ I)[X₁, …, Xᵣ]` under `X ↦ t`. For an ideal `J`, the
homogeneous polynomials whose value lies in `J` modulo `Iⁿ⁺¹` generate an ideal of the noetherian
ring `(R ⧸ I)[X]`; finitely many homogeneous generators give elements `x₁, …, xₛ` of `J`, and
successive approximation, using completeness, shows that they generate `J`.
-/

universe u

open MvPolynomial

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

lemma homogeneousComponent_mul_of_isHomogeneous {g : MvPolynomial σ R} {d : ℕ}
    (hg : g.IsHomogeneous d) (Q : MvPolynomial σ R) (m : ℕ) :
    homogeneousComponent m (Q * g) =
      if d ≤ m then homogeneousComponent (m - d) Q * g else 0 := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent Q, Finset.sum_mul, map_sum]
  have h (k : ℕ) : homogeneousComponent m (homogeneousComponent k Q * g) =
      if k + d = m then homogeneousComponent k Q * g else 0 := by
    split_ifs with hk
    · exact homogeneousComponent_of_mem (by rw [← hk]; exact
        (homogeneousComponent_isHomogeneous k Q).mul hg) |>.trans (ite_eq_left rfl)
    · exact (homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous k Q).mul hg)).trans
        (ite_eq_right (Ne.symm hk))
  simp only [h]
  split_ifs with hdm
  · rw [Finset.sum_eq_single (m - d)]
    · rw [ite_eq_left (Nat.sub_add_cancel hdm)]
    · intro k _ hk
      rw [ite_eq_right]
      lia
    · intro hk
      rw [ite_eq_left (Nat.sub_add_cancel hdm)]
      rw [Finset.mem_range, not_lt] at hk
      rw [homogeneousComponent_eq_zero _ _ (by lia), zero_mul]
  · exact Finset.sum_eq_zero fun k _ ↦ ite_eq_right (by lia)

end MvPolynomial

namespace MvPolynomial

variable {σ R S : Type*} [CommSemiring R] [CommSemiring S]

lemma map_homogeneousComponent (f : R →+* S) (k : ℕ) (p : MvPolynomial σ R) :
    map f (homogeneousComponent k p) = homogeneousComponent k (map f p) := by
  ext x
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

/-- A homogeneous polynomial has a homogeneous lift along a surjection of coefficient rings. -/
lemma exists_isHomogeneous_map_eq {f : R →+* S} (hf : Function.Surjective f) {k : ℕ}
    {Q : MvPolynomial σ S} (hQ : Q.IsHomogeneous k) :
    ∃ Q' : MvPolynomial σ R, Q'.IsHomogeneous k ∧ map f Q' = Q := by
  obtain ⟨Q'', rfl⟩ := map_surjective f hf Q
  refine ⟨homogeneousComponent k Q'', homogeneousComponent_isHomogeneous k Q'', ?_⟩
  rw [map_homogeneousComponent, homogeneousComponent_eq_self hQ]

end MvPolynomial

namespace Ideal

variable {R : Type u} [CommRing R] {I : Ideal R} {r : ℕ} {t : Fin r → R}

lemma eval_mem_pow_of_isHomogeneous (ht : Ideal.span (Set.range t) = I)
    {p : MvPolynomial (Fin r) R} {m : ℕ} (hp : p.IsHomogeneous m) : p.eval t ∈ I ^ m := by
  rw [← ht]
  exact (Ideal.mem_span_pow_iff_exists_isHomogeneous t _).mpr ⟨p, hp, rfl⟩

lemma eval_mem_pow_succ_of_isHomogeneous (ht : Ideal.span (Set.range t) = I)
    {p : MvPolynomial (Fin r) R} {m : ℕ} (hp : p.IsHomogeneous m) (hI : ∀ x, p.coeff x ∈ I) :
    p.eval t ∈ I ^ (m + 1) := by
  classical
  rw [p.as_sum, map_sum]
  refine Ideal.sum_mem _ fun x hx ↦ ?_
  rw [eval_monomial, pow_succ']
  refine Ideal.mul_mem_mul (hI x) ?_
  have hdeg : x.degree = m := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp hx)
  have := eval_mem_pow_of_isHomogeneous ht (isHomogeneous_monomial (1 : R) hdeg)
  simpa [eval_monomial] using this

end Ideal

namespace Ideal

variable {R : Type u} [CommRing R] {I : Ideal R} {r : ℕ} {t : Fin r → R}

open Ideal.Quotient in
/-- The graded approximation step: for finitely many homogeneous polynomials `g ∈ G` of degrees
`d g` whose values are `≡ y g ∈ J` modulo `I ^ (d g + 1)` and which generate the ideal of all
such homogeneous polynomials, every `z ∈ J ∩ Iᵐ` is `≡ ∑ q g * y g` modulo `Iᵐ⁺¹` with
`q g ∈ I ^ (m - d g)`. -/
lemma exists_approx (ht : Ideal.span (Set.range t) = I) (J : Ideal R)
    (G : Finset (MvPolynomial (Fin r) (R ⧸ I))) (d : MvPolynomial (Fin r) (R ⧸ I) → ℕ)
    (P' : MvPolynomial (Fin r) (R ⧸ I) → MvPolynomial (Fin r) R)
    (y : MvPolynomial (Fin r) (R ⧸ I) → R)
    (hP'hom : ∀ g ∈ G, (P' g).IsHomogeneous (d g))
    (hP'map : ∀ g ∈ G, MvPolynomial.map (mk I) (P' g) = g)
    (hy : ∀ g ∈ G, (P' g).eval t - y g ∈ I ^ (d g + 1))
    (hspan : ∀ (m : ℕ) (Z' : MvPolynomial (Fin r) R), Z'.IsHomogeneous m → Z'.eval t ∈ J →
      MvPolynomial.map (mk I) Z' ∈ Ideal.span (G : Set (MvPolynomial (Fin r) (R ⧸ I))))
    (m : ℕ) (z : R) (hzJ : z ∈ J) (hzI : z ∈ I ^ m) :
    ∃ q : MvPolynomial (Fin r) (R ⧸ I) → R, (∀ g, q g ∈ I ^ (m - d g)) ∧
      (∀ g, m < d g → q g = 0) ∧ z - ∑ g ∈ G, q g * y g ∈ I ^ (m + 1) := by
  classical
  obtain ⟨Z', hZ'hom, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous t z).mp (ht ▸ hzI)
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp (hspan m Z' hZ'hom hzJ)
  -- the homogeneous components of degree `m`
  have hP : MvPolynomial.map (mk I) Z' = ∑ g ∈ G,
      if d g ≤ m then homogeneousComponent (m - d g) (f g) * g else 0 := by
    rw [← homogeneousComponent_eq_self (hZ'hom.map (mk I)), ← hf, map_sum]
    refine Finset.sum_congr rfl fun g hg ↦ ?_
    have hgh : g.IsHomogeneous (d g) := by
      have := (hP'hom g hg).map (mk I)
      rwa [hP'map g hg] at this
    rw [smul_eq_mul, homogeneousComponent_mul_of_isHomogeneous hgh]
  -- homogeneous lifts of the coefficients
  have hlift (g : MvPolynomial (Fin r) (R ⧸ I)) : ∃ Q' : MvPolynomial (Fin r) R,
      Q'.IsHomogeneous (m - d g) ∧
        MvPolynomial.map (mk I) Q' = homogeneousComponent (m - d g) (f g) :=
    exists_isHomogeneous_map_eq Ideal.Quotient.mk_surjective
      (homogeneousComponent_isHomogeneous _ _)
  choose Q' hQ'hom hQ'map using hlift
  let q : MvPolynomial (Fin r) (R ⧸ I) → R := fun g ↦ if d g ≤ m then (Q' g).eval t else 0
  refine ⟨q, fun g ↦ ?_, fun g hg ↦ ite_eq_right (by lia), ?_⟩
  · simp only [q]
    split_ifs
    · exact eval_mem_pow_of_isHomogeneous ht (hQ'hom g)
    · exact zero_mem _
  -- the difference `D'` has coefficients in `I`
  let D' : MvPolynomial (Fin r) R :=
    Z' - ∑ g ∈ G, if d g ≤ m then Q' g * P' g else 0
  have hD'hom : D'.IsHomogeneous m := by
    refine hZ'hom.sub (IsHomogeneous.sum _ _ _ fun g hg ↦ ?_)
    split_ifs with hdm
    · have := (hQ'hom g).mul (hP'hom g hg)
      rwa [Nat.sub_add_cancel hdm] at this
    · exact isHomogeneous_zero _ _ _
  have hD'coeff (x) : D'.coeff x ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map]
    simp only [D', map_sub, map_sum]
    rw [hP, sub_eq_zero.mpr]
    · simp
    refine Finset.sum_congr rfl fun g hg ↦ ?_
    split_ifs
    · rw [map_mul, hQ'map, hP'map g hg]
    · simp
  have hD := eval_mem_pow_succ_of_isHomogeneous ht hD'hom hD'coeff
  have key : Z'.eval t - ∑ g ∈ G, q g * y g = D'.eval t +
      ∑ g ∈ G, if d g ≤ m then (Q' g).eval t * ((P' g).eval t - y g) else 0 := by
    simp only [D', q, map_sub, map_sum]
    rw [sub_add_eq_add_sub, sub_eq_sub_iff_add_eq_add, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    split_ifs
    · rw [map_mul]
      ring
    · simp
  rw [key]
  refine add_mem hD (Ideal.sum_mem _ fun g hg ↦ ?_)
  split_ifs with hdm
  · have := Ideal.mul_mem_mul (eval_mem_pow_of_isHomogeneous ht (hQ'hom g)) (hy g hg)
    rwa [← pow_add, show m - d g + (d g + 1) = m + 1 by lia] at this
  · exact zero_mem _

end Ideal

namespace Ideal

variable {R : Type u} [CommRing R]

lemma mem_pow_of_smodEq {I : Ideal R} {n : ℕ} {x y : R}
    (h : x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)]) : x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  exact h

/-- A ring which is complete and separated for the `I`-adic topology, with `I` finitely
generated and `R ⧸ I` noetherian, is noetherian (Stacks, Tag 05GH). -/
theorem isNoetherianRing_of_isAdicComplete (I : Ideal R) (hI : I.FG) [IsAdicComplete I R]
    [IsNoetherianRing (R ⧸ I)] : IsNoetherianRing R := by
  classical
  obtain ⟨r, t, ht⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  refine ⟨fun J ↦ ?_⟩
  let π := Ideal.Quotient.mk I
  let Gen : Set (MvPolynomial (Fin r) (R ⧸ I)) := {P | ∃ (m : ℕ) (P' : MvPolynomial (Fin r) R),
    P'.IsHomogeneous m ∧ MvPolynomial.map π P' = P ∧ ∃ y ∈ J, P'.eval t - y ∈ I ^ (m + 1)}
  obtain ⟨G, hGsub, hGspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset Gen).mp
      (IsNoetherian.noetherian (R := MvPolynomial (Fin r) (R ⧸ I)) (Ideal.span Gen))
  have hG : ∀ g ∈ G, ∃ (m : ℕ) (P' : MvPolynomial (Fin r) R),
      P'.IsHomogeneous m ∧ MvPolynomial.map π P' = g ∧ ∃ y ∈ J, P'.eval t - y ∈ I ^ (m + 1) :=
    fun g hg ↦ hGsub hg
  choose! d P' hP'hom hP'map y hyJ hy using hG
  have hspan (m : ℕ) (Z' : MvPolynomial (Fin r) R) (hZ' : Z'.IsHomogeneous m)
      (hzJ : Z'.eval t ∈ J) : MvPolynomial.map π Z' ∈ Ideal.span (G : Set _) := by
    change _ ∈ Submodule.span _ _
    rw [← hGspan]
    exact Submodule.subset_span ⟨m, Z', hZ', rfl, _, hzJ, by simp⟩
  have step := exists_approx ht J G d P' y hP'hom hP'map hy hspan
  choose! Q hQI hQzero hQrem using step
  refine ⟨G.image y, le_antisymm ?_ fun z hz ↦ ?_⟩
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    exact hyJ g hg
  -- successive approximation of `z`
  let zs : ℕ → R := fun m ↦ Nat.rec z (fun m zm ↦ zm - ∑ g ∈ G, Q m zm g * y g) m
  have hzs (m : ℕ) : zs m ∈ J ∧ zs m ∈ I ^ m := by
    induction m with
    | zero => exact ⟨hz, by simp⟩
    | succ m ih =>
      refine ⟨sub_mem ih.1 (Ideal.sum_mem _ fun g hg ↦ Ideal.mul_mem_left _ _ (hyJ g hg)), ?_⟩
      exact hQrem m (zs m) ih.1 ih.2
  let c : ℕ → MvPolynomial (Fin r) (R ⧸ I) → R := fun M g ↦ ∑ m ∈ Finset.range M, Q m (zs m) g
  have hc (M : ℕ) : z - ∑ g ∈ G, c M g * y g = zs M := by
    induction M with
    | zero => simp [c, zs]
    | succ M ih =>
      simp only [c, Finset.sum_range_succ, add_mul, Finset.sum_add_distrib]
      rw [← sub_sub, ih]
  have hcauchy (g : MvPolynomial (Fin r) (R ⧸ I)) {M N : ℕ} (hMN : M ≤ N) :
      c N g - c M g ∈ I ^ (M - d g) := by
    simp only [c]
    rw [← Finset.sum_range_add_sum_Ico _ hMN, add_sub_cancel_left]
    refine Ideal.sum_mem _ fun m hm ↦ ?_
    rw [Finset.mem_Ico] at hm
    exact Ideal.pow_le_pow_right (by lia) (hQI m (zs m) (hzs m).1 (hzs m).2 g)
  have hlim (g : MvPolynomial (Fin r) (R ⧸ I)) : ∃ L : R, ∀ n,
      c (n + d g) g ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    refine IsPrecomplete.prec inferInstance fun {m n} hmn ↦ ?_
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
    have := hcauchy g (show m + d g ≤ n + d g by lia)
    rwa [Nat.add_sub_cancel] at this
  choose L hL using hlim
  have hzero : z - ∑ g ∈ G, L g * y g = 0 := by
    refine IsHausdorff.haus' (I := I) _ fun n ↦ ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    let M := n + G.sup d
    have hdecomp : z - ∑ g ∈ G, L g * y g =
        zs M + ∑ g ∈ G, (c M g - L g) * y g := by
      rw [← hc M]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hdecomp]
    refine add_mem (Ideal.pow_le_pow_right (by lia) (hzs M).2)
      (Ideal.sum_mem _ fun g hg ↦ Ideal.mul_mem_right _ _ ?_)
    have hdg : d g ≤ G.sup d := Finset.le_sup hg
    have h₁ := hcauchy g (show n + d g ≤ M by lia)
    rw [Nat.add_sub_cancel] at h₁
    have h₂ := mem_pow_of_smodEq (hL g n)
    have := add_mem h₁ h₂
    rwa [sub_add_sub_cancel] at this
  rw [sub_eq_zero] at hzero
  rw [hzero]
  refine Ideal.sum_mem _ fun g hg ↦ Ideal.mul_mem_left _ _ (Submodule.subset_span ?_)
  exact Finset.mem_coe.mpr (Finset.mem_image_of_mem y hg)

/-- A submodule of an `I`-adically separated module is `I`-adically separated. -/
theorem _root_.IsHausdorff.submodule {M : Type*} [AddCommGroup M] [Module R M] (I : Ideal R)
    [IsHausdorff I M] (N : Submodule R M) : IsHausdorff I N := by
  refine ⟨fun x hx ↦ Subtype.ext (IsHausdorff.haus' (I := I) (x : M) fun n ↦ ?_)⟩
  have h := hx n
  rw [SModEq.zero] at h ⊢
  have h' := Submodule.mem_map_of_mem (f := N.subtype) h
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at h'
  exact Submodule.smul_mono le_rfl le_top h'

/-- Let `R` be complete and separated for the `I`-adic topology. If `R ⧸ I` is noetherian and
`I ⧸ I²` is a finite `R ⧸ I`-module, then `R` is noetherian (EGA 0_I, 7.2.8). -/
theorem isNoetherianRing_of_isAdicComplete_of_cotangent (I : Ideal R) [IsAdicComplete I R]
    [IsNoetherianRing (R ⧸ I)] [Module.Finite (R ⧸ I) I.Cotangent] : IsNoetherianRing R := by
  have : Module.Finite R I.Cotangent := Module.Finite.trans (R ⧸ I) I.Cotangent
  have : Module.Finite R (I ⧸ (I • ⊤ : Submodule R I)) := this
  have : IsHausdorff I I := IsHausdorff.submodule I I
  have : Module.Finite R I := Module.Finite.of_isHausdorff_of_finite_quotient (I := I)
  exact isNoetherianRing_of_isAdicComplete I (Module.Finite.iff_fg.mp this)

/-- A ring `R`, complete and separated for the `I`-adic topology, is noetherian if and only if
`R ⧸ I` is noetherian and `I ⧸ I²` is a finite `R ⧸ I`-module (EGA 0_I, 7.2.8). -/
theorem isNoetherianRing_iff_of_isAdicComplete (I : Ideal R) [IsAdicComplete I R] :
    IsNoetherianRing R ↔ IsNoetherianRing (R ⧸ I) ∧ Module.Finite (R ⧸ I) I.Cotangent := by
  refine ⟨fun _ ↦ ⟨inferInstance, ?_⟩, fun ⟨_, _⟩ ↦
    isNoetherianRing_of_isAdicComplete_of_cotangent I⟩
  have : Module.Finite R I := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian I)
  have : Module.Finite R I.Cotangent :=
    Module.Finite.of_surjective I.toCotangent (Submodule.mkQ_surjective _)
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) I.Cotangent

end Ideal
