/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.OkaRelations
import SGA.Foundations.Analytic.OkaPolynomial
import Mathlib.Data.Fintype.Sum

/-!
# Spreading finite analytic germ data

A finite family of analytic germs has representatives on a common neighborhood, and a
finite family of equalities of germs holds on a common smaller neighborhood. These are
the finite-data shrinking steps needed to turn simultaneous Weierstrass preparation
into equations of analytic sections in the Oka coherence argument.
-/

noncomputable section

-- Sections and stalks of `analyticPresheaf` are `CommRingCat` objects whose carriers are the
-- subalgebras `analyticSections`; unifying their two ring structures needs this option.
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Filter Opposite
open scoped Topology Polynomial

namespace AnalyticGeometry

variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {ι : Type*} [Finite ι]

omit [CompleteSpace 𝕜] in
/-- Finitely many analytic germs have analytic representatives on one neighborhood. -/
theorem exists_common_analytic_sections (x : E)
    (s : ι → (analyticPresheaf 𝕜 E).stalk x) :
    ∃ (U : Opens E) (hx : x ∈ U) (f : ι → analyticSections 𝕜 U),
      ∀ i, (analyticPresheaf 𝕜 E).germ U x hx (f i) = s i := by
  classical
  choose U hxU f hf using fun i ↦ (analyticPresheaf 𝕜 E).exists_germ_eq (s i)
  have hn : ∀ᶠ y in 𝓝 x, ∀ i, y ∈ U i :=
    eventually_all.mpr fun i ↦ (U i).isOpen.mem_nhds (hxU i)
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp hn
  let W : Opens E := ⟨V, hVo⟩
  have hWU (i : ι) : W ≤ U i := fun _ hy ↦ hV hy i
  refine ⟨W, hxV, fun i ↦ analyticRestrict (hWU i) (f i), fun i ↦ ?_⟩
  exact ((analyticPresheaf 𝕜 E).germ_res_apply (homOfLE (hWU i)) x hxV (f i)).trans (hf i)

omit [CompleteSpace 𝕜] in
/-- Finitely many polynomials over an analytic stalk lift to polynomials of analytic
sections on one neighborhood, preserving the degree bounds, zero polynomials, and monicity.
This keeps the Weierstrass polynomial data valid at every point of the neighborhood. -/
theorem exists_common_polynomial_sections (x : E)
    (P : ι → ((analyticPresheaf 𝕜 E).stalk x)[X]) :
    ∃ (U : Opens E) (hx : x ∈ U) (Q : ι → (analyticSections 𝕜 U)[X]),
      ∀ i, (Q i).map ((analyticPresheaf 𝕜 E).germ U x hx).hom = P i ∧
        (Q i).natDegree ≤ (P i).natDegree ∧ (P i = 0 → Q i = 0) ∧
        ((P i).Monic → (Q i).Monic) := by
  classical
  let κ := Σ i, Fin ((P i).natDegree + 1)
  obtain ⟨U, hxU, t, ht⟩ := exists_common_analytic_sections x
    (fun j : κ ↦ (P j.1).coeff j.2)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let γ : analyticSections 𝕜 U →+* (analyticPresheaf 𝕜 E).stalk x :=
    ((analyticPresheaf 𝕜 E).germ U x hxU).hom
  let c (i : ι) (j : Fin ((P i).natDegree + 1)) : analyticSections 𝕜 U :=
    if (P i).coeff j = 0 then 0 else if (P i).coeff j = 1 then 1 else t ⟨i, j⟩
  have hc (i : ι) (j : Fin ((P i).natDegree + 1)) : γ (c i j) = (P i).coeff j := by
    dsimp only [c]
    split_ifs with h0 h1
    · rw [map_zero, h0]
    · rw [map_one, h1]
    · exact ht ⟨i, j⟩
  let Q (i : ι) : (analyticSections 𝕜 U)[X] := Polynomial.ofFn ((P i).natDegree + 1) (c i)
  have hQdeg (i : ι) : (Q i).natDegree ≤ (P i).natDegree :=
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) (c i))
  refine ⟨U, hxU, Q, fun i ↦ ⟨?_, hQdeg i, ?_, ?_⟩⟩
  · ext j
    change ((Q i).map γ).coeff j = (P i).coeff j
    rw [Polynomial.coeff_map]
    by_cases hj : j < (P i).natDegree + 1
    · change γ ((Polynomial.ofFn _ (c i)).coeff j) = _
      rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
      exact hc i ⟨j, hj⟩
    · change γ ((Polynomial.ofFn _ (c i)).coeff j) = _
      rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hj), map_zero,
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  · intro hi
    have hc0 : c i = 0 := by
      funext j
      simp [c, hi]
    change Polynomial.ofFn _ (c i) = 0
    rw [hc0, map_zero]
  · intro hi
    have htop : (Q i).coeff (P i).natDegree = 1 := by
      change (Polynomial.ofFn _ (c i)).coeff (P i).natDegree = 1
      rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)]
      simp [c, hi.coeff_natDegree]
    have hdeg : (Q i).natDegree = (P i).natDegree :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (hQdeg i) (htop ▸ one_ne_zero)
    change (Q i).coeff (Q i).natDegree = 1
    rw [hdeg, htop]

/-- Finitely many identities of analytic germs hold as identities of sections after
one common shrinking. -/
theorem exists_common_restrict_eq_of_germ_eq {U : Opens E} (x : U)
    (f g : ι → analyticSections 𝕜 U)
    (hfg : ∀ i, (analyticPresheaf 𝕜 E).germ U x x.2 (f i) =
      (analyticPresheaf 𝕜 E).germ U x x.2 (g i)) :
    ∃ (V : Opens E) (hVU : V ≤ U), (x : E) ∈ V ∧
      ∀ i, analyticRestrict hVU (f i) = analyticRestrict hVU (g i) := by
  have heq (i : ι) : extendByZero (f i).1 =ᶠ[𝓝 (x : E)] extendByZero (g i).1 := by
    apply (germOf_eq_germOf_iff ((f i).2 x) ((g i).2 x)).mp
    exact (germ_eq_germOf U x.2 (f i)).symm.trans
      ((hfg i).trans (germ_eq_germOf U x.2 (g i)))
  have hn : ∀ᶠ y in 𝓝 (x : E), y ∈ U ∧
      ∀ i, extendByZero (f i).1 y = extendByZero (g i).1 y := by
    filter_upwards [U.isOpen.mem_nhds x.2, eventually_all.mpr heq] with y hy hyeq
    exact ⟨hy, hyeq⟩
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp hn
  let W : Opens E := ⟨V, hVo⟩
  have hWU : W ≤ U := fun _ hy ↦ (hV hy).1
  refine ⟨W, hWU, hxV, fun i ↦ ?_⟩
  apply Subtype.ext
  funext y
  have h := (hV y.2).2 i
  simpa only [extendByZero_of_mem _ (hWU y.2), analyticRestrict_apply] using h

/-- Simultaneously realizing the zero germs as zero sections. -/
theorem exists_common_restrict_zero_of_germ_zero {U : Opens E} (x : U)
    (f : ι → analyticSections 𝕜 U)
    (hf : ∀ i, (analyticPresheaf 𝕜 E).germ U x x.2 (f i) = 0) :
    ∃ (V : Opens E) (hVU : V ≤ U), (x : E) ∈ V ∧
      ∀ i, analyticRestrict hVU (f i) = 0 := by
  obtain ⟨V, hVU, hxV, heq⟩ := exists_common_restrict_eq_of_germ_eq x f (fun _ ↦ 0)
    (fun i ↦ by
      change ((analyticPresheaf 𝕜 E).germ U x x.2).hom (f i) =
        ((analyticPresheaf 𝕜 E).germ U x x.2).hom 0
      rw [map_zero]
      exact hf i)
  exact ⟨V, hVU, hxV, fun i ↦ by simpa only [map_zero] using heq i⟩

/-- Finitely many units of the analytic local ring can be represented by invertible
analytic sections on one neighborhood, with their inverses defined there as well. -/
theorem exists_common_analytic_units (x : E)
    (u : ι → ((analyticPresheaf 𝕜 E).stalk x)ˣ) :
    ∃ (U : Opens E) (hx : x ∈ U) (v : ι → (analyticSections 𝕜 U)ˣ),
      ∀ i, (analyticPresheaf 𝕜 E).germ U x hx (v i : analyticSections 𝕜 U) = u i := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨U, hxU, t, ht⟩ := exists_common_analytic_sections x
    (Sum.elim (fun i ↦ (u i : (analyticPresheaf 𝕜 E).stalk x))
      (fun i ↦ (↑(u i)⁻¹ : (analyticPresheaf 𝕜 E).stalk x)))
  let f (i : ι) := t (Sum.inl i)
  let g (i : ι) := t (Sum.inr i)
  have hfg (i : ι) :
      (analyticPresheaf 𝕜 E).germ U x hxU (f i * g i) =
        (analyticPresheaf 𝕜 E).germ U x hxU 1 := by
    change ((analyticPresheaf 𝕜 E).germ U x hxU).hom (f i * g i) =
      ((analyticPresheaf 𝕜 E).germ U x hxU).hom 1
    rw [map_mul, map_one, show ((analyticPresheaf 𝕜 E).germ U x hxU).hom (f i) = u i from
      ht (Sum.inl i), show ((analyticPresheaf 𝕜 E).germ U x hxU).hom (g i) = ↑(u i)⁻¹ from
        ht (Sum.inr i), Units.mul_inv]
  obtain ⟨V, hVU, hxV, heq⟩ := exists_common_restrict_eq_of_germ_eq ⟨x, hxU⟩
    (fun i ↦ f i * g i) (fun _ ↦ 1) hfg
  have hmul (i : ι) : analyticRestrict hVU (f i) * analyticRestrict hVU (g i) = 1 := by
    simpa only [map_mul, map_one] using heq i
  let v (i : ι) : (analyticSections 𝕜 V)ˣ :=
    ⟨analyticRestrict hVU (f i), analyticRestrict hVU (g i), hmul i,
      by rw [mul_comm]; exact hmul i⟩
  refine ⟨V, hxV, v, fun i ↦ ?_⟩
  exact ((analyticPresheaf 𝕜 E).germ_res_apply (homOfLE hVU) x hxV (f i)).trans (ht (Sum.inl i))

end AnalyticGeometry
