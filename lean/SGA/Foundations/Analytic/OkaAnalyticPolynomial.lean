/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.OkaStalkPolynomial

/-!
# Analytic polynomial sections on coordinate cylinders

Polynomials in one coordinate with analytic coefficients on the base define analytic
sections on the corresponding cylinder. Taking their germs agrees with the actual
base-stalk polynomial evaluation map. This makes the bounded polynomial relation
generators usable as sections on a common neighborhood in the Oka coherence proof.
-/

noncomputable section

-- Sections and stalks of `analyticPresheaf` are `CommRingCat` objects whose carriers are the
-- subalgebras `analyticSections`; unifying their two ring structures needs this option.
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Filter Opposite MvPowerSeries
open scoped Topology Polynomial

namespace AnalyticGeometry

variable {𝕜 E : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma germ_ofAnalyticOnNhd {U : Opens E} (F : E → 𝕜)
    (hF : ∀ y ∈ U, AnalyticAt 𝕜 F y) (x : U) :
    (analyticPresheaf 𝕜 E).germ U x x.2 (ofAnalyticOnNhd F hF) = germOf F (hF x x.2) := by
  rw [germ_eq_germOf]
  apply germOf_congr
  filter_upwards [U.isOpen.mem_nhds x.2] with y hy
  rw [extendByZero_of_mem _ hy]
  rfl

variable {σ : Type u} [Fintype σ]

omit [CompleteSpace 𝕜] [Fintype σ] in
lemma continuous_baseCoordinates :
    Continuous (baseCoordinates : (Option σ → 𝕜) → (σ → 𝕜)) :=
  continuous_pi fun i ↦ continuous_apply (some i)

/-- The cylinder over an open subset in the base coordinates. -/
def coordinateCylinder (U : Opens (σ → 𝕜)) : Opens (Option σ → 𝕜) :=
  ⟨baseCoordinates ⁻¹' (U : Set (σ → 𝕜)), U.isOpen.preimage continuous_baseCoordinates⟩

omit [CompleteSpace 𝕜] [Fintype σ] in
@[simp] lemma mem_coordinateCylinder (U : Opens (σ → 𝕜)) (x : Option σ → 𝕜) :
    x ∈ coordinateCylinder U ↔ baseCoordinates x ∈ U := Iff.rfl

/-- Pullback of analytic sections from the base to the cylinder. -/
def baseSectionsPullback (U : Opens (σ → 𝕜)) :
    analyticSections 𝕜 U →ₐ[𝕜] analyticSections 𝕜 (coordinateCylinder U) where
  toFun f := ⟨fun z ↦ f.1 ⟨baseCoordinates (z : Option σ → 𝕜), z.2⟩, by
    apply isAnalyticOn_of_forall (coordinateCylinder U).isOpen
    intro z
    have hf : AnalyticAt 𝕜 (extendByZero f.1) (baseCoordinates (z : Option σ → 𝕜)) :=
      f.2 ⟨baseCoordinates (z : Option σ → 𝕜), z.2⟩
    refine ⟨fun y ↦ extendByZero f.1 (baseCoordinates y),
      hf.comp (analyticAt_baseCoordinates (z : Option σ → 𝕜)), ?_⟩
    exact Eventually.of_forall fun y hy ↦ (extendByZero_of_mem f.1 hy).symm⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

omit [CompleteSpace 𝕜] in
@[simp]
lemma baseSectionsPullback_apply (U : Opens (σ → 𝕜)) (f : analyticSections 𝕜 U)
    (x : coordinateCylinder U) :
    (baseSectionsPullback U f).1 x = f.1 ⟨baseCoordinates (x : Option σ → 𝕜), x.2⟩ := rfl

/-- The last coordinate as an analytic section on a cylinder. -/
def lastCoordinateSection (U : Opens (σ → 𝕜)) : analyticSections 𝕜 (coordinateCylinder U) :=
  ofAnalyticOnNhd (fun z ↦ z none) (fun z _ ↦ analyticAt_apply none z)

/-- Evaluation of polynomials of analytic sections as analytic sections on the cylinder. -/
def analyticPolynomialSection (U : Opens (σ → 𝕜)) :
    (analyticSections 𝕜 U)[X] →+* analyticSections 𝕜 (coordinateCylinder U) :=
  Polynomial.eval₂RingHom (baseSectionsPullback U).toRingHom (lastCoordinateSection U)

lemma baseSectionsPullback_germ (U : Opens (σ → 𝕜)) (x : coordinateCylinder U)
    (f : analyticSections 𝕜 U) :
    (analyticPresheaf 𝕜 (Option σ → 𝕜)).germ (coordinateCylinder U) x x.2
        (baseSectionsPullback U f) =
      baseStalkPullback (x : Option σ → 𝕜)
        ((analyticPresheaf 𝕜 (σ → 𝕜)).germ U (baseCoordinates (x : Option σ → 𝕜)) x.2 f) := by
  rw [germ_eq_germOf U x.2 f]
  change _ = stalkPullback baseCoordinates (analyticAt_baseCoordinates (x : Option σ → 𝕜)) _
  rw [stalkPullback_germOf]
  rw [germ_eq_germOf]
  apply germOf_congr
  filter_upwards [(coordinateCylinder U).isOpen.mem_nhds x.2] with y hy
  rw [extendByZero_of_mem _ hy, baseSectionsPullback_apply]
  exact (extendByZero_of_mem f.1 (show baseCoordinates y ∈ U from hy)).symm

lemma lastCoordinateSection_germ (U : Opens (σ → 𝕜)) (x : coordinateCylinder U) :
    (analyticPresheaf 𝕜 (Option σ → 𝕜)).germ (coordinateCylinder U) x x.2
        (lastCoordinateSection U) = lastCoordinateGerm (x : Option σ → 𝕜) :=
  germ_ofAnalyticOnNhd _ _ x

/-- Taking the germ of an analytic polynomial section is the polynomial evaluation
of the germs of its coefficients. -/
theorem analyticPolynomialSection_germ (U : Opens (σ → 𝕜)) (x : coordinateCylinder U)
    (P : (analyticSections 𝕜 U)[X]) :
    (analyticPresheaf 𝕜 (Option σ → 𝕜)).germ (coordinateCylinder U) x x.2
        (analyticPolynomialSection U P) =
      polynomialStalkEval (x : Option σ → 𝕜)
        (P.map ((analyticPresheaf 𝕜 (σ → 𝕜)).germ U
          (baseCoordinates (x : Option σ → 𝕜)) x.2).hom) := by
  let γ : analyticSections 𝕜 (coordinateCylinder U) →+*
      (analyticPresheaf 𝕜 (Option σ → 𝕜)).stalk (x : Option σ → 𝕜) :=
    ((analyticPresheaf 𝕜 (Option σ → 𝕜)).germ (coordinateCylinder U) x x.2).hom
  let δ : analyticSections 𝕜 U →+*
      (analyticPresheaf 𝕜 (σ → 𝕜)).stalk (baseCoordinates (x : Option σ → 𝕜)) :=
    ((analyticPresheaf 𝕜 (σ → 𝕜)).germ U (baseCoordinates (x : Option σ → 𝕜)) x.2).hom
  have h : γ.comp (analyticPolynomialSection U) =
      (polynomialStalkEval (x : Option σ → 𝕜)).comp (Polynomial.mapRingHom δ) := by
    apply Polynomial.ringHom_ext
    · intro f
      change γ (Polynomial.eval₂ _ _ (Polynomial.C f)) =
        Polynomial.eval₂ _ _ ((Polynomial.C f).map δ)
      rw [Polynomial.eval₂_C, Polynomial.map_C, Polynomial.eval₂_C]
      exact baseSectionsPullback_germ U x f
    · change γ (Polynomial.eval₂ _ _ Polynomial.X) =
        Polynomial.eval₂ _ _ (Polynomial.X.map δ)
      rw [Polynomial.eval₂_X, Polynomial.map_X, Polynomial.eval₂_X]
      exact lastCoordinateSection_germ U x
  exact RingHom.congr_fun h P

end AnalyticGeometry
