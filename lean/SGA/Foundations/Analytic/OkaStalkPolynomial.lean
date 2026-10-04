/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.OkaReduction
import SGA.Foundations.Analytic.LocalModelHom

/-!
# Polynomials over the base stalk in an analytic coordinate neighborhood

An analytic polynomial in the last coordinate with coefficients in the stalk of the
base defines an actual analytic germ on the product. We compare this map with convergent
power series after translating both coordinates to the point. This relates the algebraic
Weierstrass reduction to relation germs on neighborhoods in the Oka coherence argument.
-/

noncomputable section

universe u

open MvPowerSeries Filter
open scoped Polynomial

namespace AnalyticGeometry

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {σ : Type u} [Fintype σ]

/-- Projection away from the last coordinate. -/
def baseCoordinates (x : Option σ → 𝕜) : σ → 𝕜 := fun i ↦ x (some i)

omit [CompleteSpace 𝕜] in
lemma analyticAt_baseCoordinates (x : Option σ → 𝕜) :
    AnalyticAt 𝕜 (baseCoordinates : (Option σ → 𝕜) → (σ → 𝕜)) x :=
  AnalyticAt.pi fun i ↦ analyticAt_apply (some i) x

/-- Pullback from the base stalk along the coordinate projection. -/
def baseStalkPullback (x : Option σ → 𝕜) :
    (analyticPresheaf 𝕜 (σ → 𝕜)).stalk (baseCoordinates x) →+*
      (analyticPresheaf 𝕜 (Option σ → 𝕜)).stalk x :=
  stalkPullback baseCoordinates (analyticAt_baseCoordinates x)

/-- The germ of the last coordinate. -/
def lastCoordinateGerm (x : Option σ → 𝕜) :
    (analyticPresheaf 𝕜 (Option σ → 𝕜)).stalk x :=
  germOf (fun z ↦ z none) (analyticAt_apply none x)

/-- Evaluation of polynomials with coefficients in the base stalk as analytic germs. -/
def polynomialStalkEval (x : Option σ → 𝕜) :
    ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk (baseCoordinates x))[X] →+*
      (analyticPresheaf 𝕜 (Option σ → 𝕜)).stalk x :=
  Polynomial.eval₂RingHom (baseStalkPullback x) (lastCoordinateGerm x)

lemma baseStalkPullback_convergentStalkEquiv (x : Option σ → 𝕜) (f : convergent σ 𝕜) :
    baseStalkPullback x (convergentStalkEquiv (baseCoordinates x) f) =
      convergentStalkEquiv x (renameSomeHom f) := by
  rw [convergentStalkEquiv_apply, convergentToStalk_apply]
  change stalkPullback baseCoordinates (analyticAt_baseCoordinates x) _ = _
  rw [stalkPullback_germOf, convergentStalkEquiv_apply, convergentToStalk_apply]
  apply germOf_congr
  exact Eventually.of_forall fun z ↦ (tsumEval_rename_some f.1 (z - x)).symm

lemma convergentStalkEquiv_lastCoordinate (x : Option σ → 𝕜) :
    convergentStalkEquiv x
        ((⟨MvPowerSeries.X none, X_mem_convergent none⟩ : convergent (Option σ) 𝕜) +
          algebraMap 𝕜 (convergent (Option σ) 𝕜) (x none)) = lastCoordinateGerm x := by
  rw [map_add, convergentStalkEquiv_algebraMap, convergentStalkEquiv_apply,
    convergentToStalk_apply, ← germOf_add]
  apply germOf_congr
  exact Eventually.of_forall fun z ↦ by simp [tsumEval_X]

/-- Analytic evaluation of a polynomial agrees with its translated convergent power
series. Both sides use the actual germs of the base coefficients and last coordinate. -/
theorem polynomialStalkEval_map_convergentStalkEquiv (x : Option σ → 𝕜)
    (P : (convergent σ 𝕜)[X]) :
    polynomialStalkEval x (P.map (convergentStalkEquiv (baseCoordinates x)).toRingHom) =
      convergentStalkEquiv x
        (polyY (P.taylor (algebraMap 𝕜 (convergent σ 𝕜) (x none)))) := by
  let ψ : (convergent σ 𝕜)[X] →+* (analyticPresheaf 𝕜 (Option σ → 𝕜)).stalk x :=
    (polynomialStalkEval x).comp
      (Polynomial.mapRingHom (convergentStalkEquiv (baseCoordinates x)).toRingHom)
  let φ : (convergent σ 𝕜)[X] →+* (analyticPresheaf 𝕜 (Option σ → 𝕜)).stalk x :=
    (convergentStalkEquiv x).toRingHom.comp
      ((Polynomial.aeval (⟨MvPowerSeries.X none, X_mem_convergent none⟩ :
        convergent (Option σ) 𝕜)).toRingHom.comp
          (Polynomial.taylorAlgHom (algebraMap 𝕜 (convergent σ 𝕜) (x none))).toRingHom)
  have h : ψ = φ := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [ψ, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        polynomialStalkEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      change baseStalkPullback x (convergentStalkEquiv (baseCoordinates x) c) =
        convergentStalkEquiv x
          ((Polynomial.aeval _ : (convergent σ 𝕜)[X] →ₐ[convergent σ 𝕜]
            convergent (Option σ) 𝕜) ((Polynomial.C c).taylor _))
      rw [Polynomial.taylor_C, Polynomial.aeval_C]
      exact baseStalkPullback_convergentStalkEquiv x c
    · simp only [ψ, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        polynomialStalkEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      change lastCoordinateGerm x = convergentStalkEquiv x
        ((Polynomial.aeval _ : (convergent σ 𝕜)[X] →ₐ[convergent σ 𝕜]
          convergent (Option σ) 𝕜) (Polynomial.X.taylor _))
      rw [Polynomial.taylor_X, map_add, Polynomial.aeval_X, Polynomial.aeval_C,
        ← IsScalarTower.algebraMap_apply]
      exact (convergentStalkEquiv_lastCoordinate x).symm
  exact RingHom.congr_fun h P

/-- Recenter the coefficients and the last variable of a polynomial at the analytic point. -/
def polynomialStalkSeriesEquiv (x : Option σ → 𝕜) :
    ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk (baseCoordinates x))[X] ≃+*
      (convergent σ 𝕜)[X] :=
  (Polynomial.mapEquiv (convergentStalkEquiv (baseCoordinates x)).symm).trans
    (Polynomial.taylorEquiv (algebraMap 𝕜 (convergent σ 𝕜) (x none))).toRingEquiv

lemma polynomialStalkEval_eq_series (x : Option σ → 𝕜)
    (P : ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk (baseCoordinates x))[X]) :
    polynomialStalkEval x P =
      convergentStalkEquiv x (polyY (polynomialStalkSeriesEquiv x P)) := by
  obtain ⟨Q, rfl⟩ := (Polynomial.mapEquiv (convergentStalkEquiv (baseCoordinates x))).surjective P
  have hseries : polynomialStalkSeriesEquiv x
      ((Polynomial.mapEquiv (convergentStalkEquiv (baseCoordinates x))) Q) =
        Q.taylor (algebraMap 𝕜 (convergent σ 𝕜) (x none)) := by
    change Polynomial.taylor _
      ((Polynomial.mapEquiv (convergentStalkEquiv (baseCoordinates x))).symm
        ((Polynomial.mapEquiv (convergentStalkEquiv (baseCoordinates x))) Q)) = _
    rw [RingEquiv.symm_apply_apply]
  rw [hseries]
  exact polynomialStalkEval_map_convergentStalkEquiv x Q

/-- A polynomial with analytic coefficients at the base is determined by its germ
as a function of all the coordinates. -/
theorem polynomialStalkEval_injective (x : Option σ → 𝕜) :
    Function.Injective (polynomialStalkEval x) := by
  intro P Q h
  rw [polynomialStalkEval_eq_series, polynomialStalkEval_eq_series] at h
  exact (polynomialStalkSeriesEquiv x).injective
    (polyY_injective ((convergentStalkEquiv x).injective h))

lemma natDegree_polynomialStalkSeriesEquiv (x : Option σ → 𝕜)
    (P : ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk (baseCoordinates x))[X]) :
    (polynomialStalkSeriesEquiv x P).natDegree = P.natDegree := by
  change (Polynomial.taylor _
    (P.map (convergentStalkEquiv (baseCoordinates x)).symm.toRingHom)).natDegree = _
  rw [Polynomial.natDegree_taylor, Polynomial.natDegree_map_eq_of_injective
    (convergentStalkEquiv (baseCoordinates x)).symm.injective]

lemma monic_polynomialStalkSeriesEquiv (x : Option σ → 𝕜)
    (P : ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk (baseCoordinates x))[X]) (hP : P.Monic) :
    (polynomialStalkSeriesEquiv x P).Monic := by
  have hm := hP.map (convergentStalkEquiv (baseCoordinates x)).symm.toRingHom
  change (Polynomial.taylor _
    (P.map (convergentStalkEquiv (baseCoordinates x)).symm.toRingHom)).Monic
  simpa only [Polynomial.Monic, Polynomial.leadingCoeff_taylor] using hm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- At every point of a coordinate neighborhood, relations among analytic polynomials
with a monic coefficient are generated by elementary relations and polynomial relations
of uniformly bounded degree. The bound depends only on the polynomial degrees, not on
the point or the chosen analytic relation. -/
theorem exists_bounded_stalkPolynomial_relation_reduction
    (x : Option σ → 𝕜)
    (P : ι → ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk (baseCoordinates x))[X])
    (j : ι) (hP : (P j).Monic) (μ : ℕ) (hdeg : ∀ i, (P i).natDegree ≤ μ)
    (a : ι → (analyticPresheaf 𝕜 (Option σ → 𝕜)).stalk x)
    (ha : a ∈ relationModule (fun i ↦ polynomialStalkEval x (P i))) :
    ∃ (q : ι → (analyticPresheaf 𝕜 (Option σ → 𝕜)).stalk x)
      (s : (analyticPresheaf 𝕜 (Option σ → 𝕜)).stalk x)
      (R : ι → ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk (baseCoordinates x))[X]),
      (∀ i, (R i).natDegree ≤ 2 * μ) ∧
      (fun i ↦ polynomialStalkEval x (R i)) ∈
        relationModule (fun i ↦ polynomialStalkEval x (P i)) ∧
      a = (∑ i, q i • elementaryRelation (fun l ↦ polynomialStalkEval x (P l)) j i) +
        s • (fun i ↦ polynomialStalkEval x (R i)) := by
  let e := convergentStalkEquiv x
  let E := polynomialStalkSeriesEquiv x
  have hcoeff (i : ι) : e.symm (polynomialStalkEval x (P i)) = polyY (E (P i)) := by
    rw [polynomialStalkEval_eq_series]
    exact e.symm_apply_apply _
  have hcoeff' (i : ι) : e (polyY (E (P i))) = polynomialStalkEval x (P i) :=
    (polynomialStalkEval_eq_series x (P i)).symm
  have has : (fun i ↦ e.symm (a i)) ∈ relationModule (fun i ↦ polyY (E (P i))) := by
    have hm : (fun i ↦ e.symm (a i)) ∈
        relationModule (fun i ↦ e.symm (polynomialStalkEval x (P i))) :=
      map_mem_relationModule e.symm.toRingHom _ _ ha
    simpa only [hcoeff] using hm
  have hdegs (i : ι) : (E (P i)).natDegree ≤ μ := by
    rw [natDegree_polynomialStalkSeriesEquiv]
    exact hdeg i
  obtain ⟨q, s, R, hRdeg, hRrel, hEq⟩ :=
    exists_bounded_polynomial_relation_reduction (fun i ↦ E (P i)) j
      (monic_polynomialStalkSeriesEquiv x (P j) hP) μ hdegs (fun i ↦ e.symm (a i)) has
  have heval (i : ι) : polynomialStalkEval x (E.symm (R i)) = e (polyY (R i)) := by
    rw [polynomialStalkEval_eq_series]
    change e (polyY (E (E.symm (R i)))) = _
    rw [E.apply_symm_apply]
  refine ⟨fun i ↦ e (q i), e s, fun i ↦ E.symm (R i), ?_, ?_, ?_⟩
  · intro i
    have hd := natDegree_polynomialStalkSeriesEquiv x (E.symm (R i))
    change (E (E.symm (R i))).natDegree = _ at hd
    rw [E.apply_symm_apply] at hd
    exact hd ▸ hRdeg i
  · have hm : (fun i ↦ e (polyY (R i))) ∈
        relationModule (fun i ↦ e (polyY (E (P i)))) :=
      map_mem_relationModule e.toRingHom _ _ hRrel
    simpa only [hcoeff', heval] using hm
  · ext i
    have h := congrArg (fun z : ι → convergent (Option σ) 𝕜 ↦ e (z i)) hEq
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      map_add, map_sum, map_mul, RingEquiv.apply_symm_apply] at h ⊢
    rw [heval]
    have hel (k : ι) :
        e (elementaryRelation (fun l ↦ polyY (E (P l))) j k i) =
          elementaryRelation (fun l ↦ polynomialStalkEval x (P l)) j k i := by
      have he : e (elementaryRelation (fun l ↦ polyY (E (P l))) j k i) =
          elementaryRelation (fun l ↦ e (polyY (E (P l)))) j k i :=
        map_elementaryRelation e.toRingHom (fun l ↦ polyY (E (P l))) j k i
      simpa only [hcoeff'] using he
    simpa only [hel] using h

open Classical in
/-- Generators of the lower-dimensional coefficient-equation kernel, together with
the elementary relations, generate the full analytic relation module at the point.
This is the local algebra step in the dimension induction for Oka coherence. -/
theorem relationModule_eq_span_of_coefficient_generators
    (x : Option σ → 𝕜)
    (P : ι → ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk (baseCoordinates x))[X])
    (j : ι) (hP : (P j).Monic) (μ : ℕ) (hdeg : ∀ i, (P i).natDegree ≤ μ)
    {κ : Type*} [Finite κ]
    (B : κ → ι → Fin (2 * μ + 1) → (analyticPresheaf 𝕜 (σ → 𝕜)).stalk (baseCoordinates x))
    (hB : (Polynomial.boundedRelationEquations P (2 * μ) μ).ker =
      Submodule.span ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk (baseCoordinates x)) (Set.range B)) :
    relationModule (fun i ↦ polynomialStalkEval x (P i)) =
      Submodule.span ((analyticPresheaf 𝕜 (Option σ → 𝕜)).stalk x)
        (Set.range (Sum.elim
          (fun i ↦ elementaryRelation (fun l ↦ polynomialStalkEval x (P l)) j i)
          (fun k i ↦ polynomialStalkEval x (Polynomial.ofFn (2 * μ + 1) (B k i))))) := by
  classical
  let f := fun i ↦ polynomialStalkEval x (P i)
  let G := Sum.elim (fun i ↦ elementaryRelation f j i)
    (fun k i ↦ polynomialStalkEval x (Polynomial.ofFn (2 * μ + 1) (B k i)))
  let L := Submodule.span ((analyticPresheaf 𝕜 (Option σ → 𝕜)).stalk x) (Set.range G)
  change relationModule f = L
  apply le_antisymm
  · intro a ha
    obtain ⟨q, s, R, hRdeg, hRrel, hEq⟩ :=
      exists_bounded_stalkPolynomial_relation_reduction x P j hP μ hdeg a ha
    have hRpoly : R ∈ relationModule P := by
      rw [mem_relationModule]
      apply polynomialStalkEval_injective x
      simp only [map_sum, map_mul, map_zero]
      exact (mem_relationModule _ _).mp hRrel
    have hmem := Polynomial.eval_relation_mem_span_of_coefficient_generators
      (polynomialStalkEval x) P (2 * μ) μ hdeg B hB R hRdeg hRpoly
    have hRL : (fun i ↦ polynomialStalkEval x (R i)) ∈ L := by
      apply Submodule.span_mono ?_ hmem
      rintro _ ⟨k, rfl⟩
      exact ⟨Sum.inr k, rfl⟩
    rw [hEq]
    apply L.add_mem
    · apply L.sum_mem
      intro i hi
      apply L.smul_mem
      exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · exact L.smul_mem s hRL
  · apply Submodule.span_le.mpr
    rintro _ ⟨i | k, rfl⟩
    · exact elementaryRelation_mem f j i
    · have hk : B k ∈ (Polynomial.boundedRelationEquations P (2 * μ) μ).ker := by
        rw [hB]
        exact Submodule.subset_span ⟨k, rfl⟩
      rw [Polynomial.mem_ker_boundedRelationEquations_iff P (2 * μ) μ hdeg] at hk
      exact map_mem_relationModule (polynomialStalkEval x) P _ hk

end AnalyticGeometry
