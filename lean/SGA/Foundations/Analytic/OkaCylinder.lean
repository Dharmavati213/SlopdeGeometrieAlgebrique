/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.OkaAnalyticPolynomial

/-!
# Uniform analytic relation generators for polynomial coefficients

Finite generators of the coefficient-equation kernel on a base neighborhood give one
finite family of analytic relation sections on the entire coordinate cylinder, generating
the relation module at every point. This is the uniform part of the Weierstrass induction
in Oka coherence, with the lower-dimensional coefficient-kernel hypothesis explicit.
-/

noncomputable section

-- Sections and stalks of `analyticPresheaf` are `CommRingCat` objects whose carriers are the
-- subalgebras `analyticSections`; unifying their two ring structures needs this option.
set_option backward.isDefEq.respectTransparency false

universe u

open TopologicalSpace
open scoped Polynomial

namespace AnalyticGeometry

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {σ : Type u} [Fintype σ] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Finite κ]

open Classical in
/-- Analytic relation generators obtained from bounded polynomial coefficient vectors. -/
def polynomialRelationGenerators (U : Opens (σ → 𝕜)) (P : ι → (analyticSections 𝕜 U)[X])
    (j : ι) (μ : ℕ) (B : κ → ι → Fin (2 * μ + 1) → analyticSections 𝕜 U) :
    ι ⊕ κ → ι → analyticSections 𝕜 (coordinateCylinder U) :=
  Sum.elim (fun i ↦ elementaryRelation (fun l ↦ analyticPolynomialSection U (P l)) j i)
    (fun k i ↦ analyticPolynomialSection U (Polynomial.ofFn (2 * μ + 1) (B k i)))

open Classical in
/-- The same analytic sections generate the relation germs at every point of the
cylinder when the coefficient equations have the given generators on the base. -/
theorem polynomialRelationGenerators_span_germs
    (U : Opens (σ → 𝕜)) (P : ι → (analyticSections 𝕜 U)[X]) (j : ι) (hP : (P j).Monic)
    (μ : ℕ) (hdeg : ∀ i, (P i).natDegree ≤ μ)
    (B : κ → ι → Fin (2 * μ + 1) → analyticSections 𝕜 U)
    (hB : ∀ y : U,
      (Polynomial.boundedRelationEquations
        (fun i ↦ (P i).map ((analyticPresheaf 𝕜 (σ → 𝕜)).germ U y y.2).hom) (2 * μ) μ).ker =
      Submodule.span ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk (y : σ → 𝕜))
        (Set.range (fun k i l ↦ (analyticPresheaf 𝕜 (σ → 𝕜)).germ U y y.2 (B k i l))))
    (x : coordinateCylinder U) :
    relationModule (fun i ↦ (analyticPresheaf 𝕜 (Option σ → 𝕜)).germ
      (coordinateCylinder U) x x.2 (analyticPolynomialSection U (P i))) =
      Submodule.span ((analyticPresheaf 𝕜 (Option σ → 𝕜)).stalk (x : Option σ → 𝕜))
        (Set.range (fun k i ↦ (analyticPresheaf 𝕜 (Option σ → 𝕜)).germ
          (coordinateCylinder U) x x.2 (polynomialRelationGenerators U P j μ B k i))) := by
  classical
  let γ : analyticSections 𝕜 (coordinateCylinder U) →+*
      (analyticPresheaf 𝕜 (Option σ → 𝕜)).stalk (x : Option σ → 𝕜) :=
    ((analyticPresheaf 𝕜 (Option σ → 𝕜)).germ (coordinateCylinder U) x x.2).hom
  let δ : analyticSections 𝕜 U →+*
      (analyticPresheaf 𝕜 (σ → 𝕜)).stalk (baseCoordinates (x : Option σ → 𝕜)) :=
    ((analyticPresheaf 𝕜 (σ → 𝕜)).germ U (baseCoordinates (x : Option σ → 𝕜)) x.2).hom
  have hgerm (Q : (analyticSections 𝕜 U)[X]) : γ (analyticPolynomialSection U Q) =
      polynomialStalkEval (x : Option σ → 𝕜) (Q.map δ) :=
    analyticPolynomialSection_germ U x Q
  have hgens : (fun k i ↦ γ (polynomialRelationGenerators U P j μ B k i)) =
      Sum.elim
        (fun i ↦ elementaryRelation (fun l ↦ polynomialStalkEval (x : Option σ → 𝕜)
          ((P l).map δ)) j i)
        (fun k i ↦ polynomialStalkEval (x : Option σ → 𝕜)
          (Polynomial.ofFn (2 * μ + 1) (fun l ↦ δ (B k i l)))) := by
    funext k i
    rcases k with k | k
    · change γ (elementaryRelation (fun l ↦ analyticPolynomialSection U (P l)) j k i) = _
      rw [map_elementaryRelation, Sum.elim_inl]
      simp only [hgerm]
    · change γ (analyticPolynomialSection U (Polynomial.ofFn (2 * μ + 1) (B k i))) = _
      rw [hgerm, Sum.elim_inr]
      congr 1
      convert Polynomial.map_ofFn δ (2 * μ + 1) (B k i)
      rfl
  have hp := relationModule_eq_span_of_coefficient_generators (x : Option σ → 𝕜)
    (fun i ↦ (P i).map δ) j (hP.map δ) μ
    (fun i ↦ Polynomial.natDegree_map_le.trans (hdeg i))
    (fun k i l ↦ δ (B k i l)) (hB ⟨baseCoordinates (x : Option σ → 𝕜), x.2⟩)
  change relationModule (fun i ↦ γ (analyticPolynomialSection U (P i))) =
    Submodule.span _ (Set.range (fun k i ↦ γ (polynomialRelationGenerators U P j μ B k i)))
  simp only [hgerm, hgens]
  exact hp

end AnalyticGeometry
