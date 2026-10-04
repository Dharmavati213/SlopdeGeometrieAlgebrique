/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Projective.GradedQuotient
import SGA.Foundations.Projective.ProjBaseChange
import SGA.Foundations.Projective.ProjectiveSpaceHom
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The projective plane curve through two elements of a field

Let `k ⊆ K` be fields and `x, y ∈ K`. The homogeneous polynomials `P(X₀, X₁, X₂)` over `k` with
`P(1, x, y) = 0` form a homogeneous prime ideal `𝔭` of `k[X₀, X₁, X₂]` (`PlaneCurve.ideal`): the
kernel of the graded homomorphism `k[X₀, X₁, X₂] → K[T]`, `Xᵢ ↦ (1, x, y)ᵢ T`. This file studies
`D = Proj (k[X₀, X₁, X₂] ⧸ 𝔭)` (`AlgebraicGeometry.planeCurve k x y`). Geometrically, `D` is the
closure in `ℙ²_k` of the point `(1 : x : y)`; it has dimension `trdeg_k k(x, y)`, so it is a
curve only when that transcendence degree is `1`, and it then has function field `k(x, y)`. None
of these three facts is formalized here: no closed immersion into `ℙ²_k`, no dimension and no
function field are computed.

`D` is the plane model of this formalization's planned route to the curve case of X.2.9 in
characteristic `p`: a finite birational morphism from a normal curve onto `D`, a lift of `D` to
characteristic `0`, and pinching (`SGA.SGA1.ExposeIX.PinchingCurve`) to pass from `D` back to the
curve. This is not SGA's route: SGA's proof of X.2.6 in characteristic `p` lifts the smooth curve
itself to `W(k)` (III.7.4) and applies X.2.3, with no plane model. The route is not finished;
this file only constructs `D` and the facts listed below.

* `AlgebraicGeometry.planeCurve k x y`: the scheme `Proj (k[X₀, X₁, X₂] ⧸ 𝔭)`, with the proper
  structure morphism `PlaneCurve.toSpec`;
* `PlaneCurve.chartHom`: the ring homomorphism `Γ(D₊(X₀)) = (k[X₀, X₁, X₂] ⧸ 𝔭)_(X₀) → K`,
  `P / X₀ⁿ ↦ P(1, x, y)`; it is injective (`PlaneCurve.chartHom_injective`) with image `k[x, y]`
  (`PlaneCurve.range_chartAlgHom`);
* `PlaneCurve.genericPt`: the point `(0)`; it is the generic point
  (`PlaneCurve.isGenericPoint_genericPt`), so `D` is irreducible, and it lies in `D₊(X₀)`
  (`PlaneCurve.genericPt_mem_basicOpen`);
* `PlaneCurve.kPoint`: the `K`-point `(1 : x : y)` over `k` (`PlaneCurve.kPoint_toSpec`), lying
  over the generic point (`PlaneCurve.kPoint_apply`).

## References

* [R. Hartshorne, *Algebraic Geometry*, I.2 and II.2][Hartshorne]
-/

universe u v

open CategoryTheory MvPolynomial HomogeneousLocalization AlgebraicGeometry ProjectiveSpace

namespace AlgebraicGeometry.PlaneCurve

variable (k : Type u) [Field k] {K : Type v} [Field K] [Algebra k K] (x y : K)

/-- The coordinates `(1, x, y)`. -/
def coords : Fin 3 → K := ![1, x, y]

/-- The homomorphism `k[X₀, X₁, X₂] → K[T]`, `Xᵢ ↦ (1, x, y)ᵢ T`. -/
noncomputable def homogeneousEval : MvPolynomial (Fin 3) k →+* MvPolynomial Unit K :=
  eval₂Hom (C.comp (algebraMap k K)) fun i ↦ C (coords x y i) * X ()

lemma homogeneousEval_of_isHomogeneous {P : MvPolynomial (Fin 3) k} {n : ℕ}
    (hP : P.IsHomogeneous n) :
    homogeneousEval k x y P = X () ^ n * C (aeval (coords x y) P) := by
  rw [homogeneousEval, coe_eval₂Hom]
  have : (fun i ↦ C (coords x y i) * X () : Fin 3 → MvPolynomial Unit K) =
      fun i ↦ X () * C (coords x y i) := funext fun _ ↦ mul_comm _ _
  rw [this, hP.eval₂_mul_left, aeval_def, eval₂_comp_left]
  rfl

/-- `k[X₀, X₁, X₂] → K[T]` as a graded homomorphism. -/
noncomputable def homogeneousEvalGraded : grading (Fin 3) k →+*ᵍ grading Unit K where
  toRingHom := homogeneousEval k x y
  map_mem {n P} hP := by
    rw [mem_grading] at hP ⊢
    have := hP.eval₂ (C.comp (algebraMap k K)) (fun i ↦ C (coords x y i) * X ())
      (fun r ↦ isHomogeneous_C _ _)
      (fun i ↦ by simpa using (isHomogeneous_C _ _).mul (isHomogeneous_X K ()))
    rw [one_mul] at this
    exact this

/-- The homogeneous prime ideal of the plane curve through `(1 : x : y)`: the homogeneous
polynomials vanishing at `(1, x, y)`. -/
noncomputable def ideal : HomogeneousIdeal (grading (Fin 3) k) :=
  (⊥ : HomogeneousIdeal (grading Unit K)).comap (homogeneousEvalGraded k x y)

lemma toIdeal_ideal : (ideal k x y).toIdeal = RingHom.ker (homogeneousEval k x y) := by
  ext P
  rw [ideal, HomogeneousIdeal.toIdeal_comap, Ideal.mem_comap, RingHom.mem_ker]
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot]
  rfl

instance isPrime_ideal : (ideal k x y).toIdeal.IsPrime := by
  rw [toIdeal_ideal]
  exact RingHom.ker_isPrime _

lemma aeval_coords_eq_zero_of_mem {P : MvPolynomial (Fin 3) k} (hP : P ∈ (ideal k x y).toIdeal) :
    aeval (coords x y) P = 0 := by
  rw [toIdeal_ideal, RingHom.mem_ker] at hP
  have := congrArg (MvPolynomial.eval fun _ ↦ (1 : K)) hP
  rw [homogeneousEval, coe_eval₂Hom, map_zero, ← coe_eval₂Hom, ← RingHom.comp_apply,
    MvPolynomial.comp_eval₂Hom] at this
  rw [← this, aeval_def]
  congr 1
  · ext r
    simp
  · ext i
    simp

/-- The class of `X₀` in `k[X₀, X₁, X₂] ⧸ 𝔭`. -/
noncomputable abbrev X₀ : MvPolynomial (Fin 3) k ⧸ (ideal k x y).toIdeal :=
  Ideal.Quotient.mk _ (X 0)

lemma X₀_mem : X₀ k x y ∈ (ideal k x y).quotientGrading 1 :=
  HomogeneousIdeal.mk_mem_quotientGrading (X_mem_grading 0)

/-- The evaluation `k[X₀, X₁, X₂] ⧸ 𝔭 → K`, `P ↦ P(1, x, y)`. -/
noncomputable def evalOne : MvPolynomial (Fin 3) k ⧸ (ideal k x y).toIdeal →+* K :=
  Ideal.Quotient.lift _ (aeval (coords x y)).toRingHom fun _ hP ↦
    aeval_coords_eq_zero_of_mem k x y hP

lemma evalOne_mk (P : MvPolynomial (Fin 3) k) :
    evalOne k x y (Ideal.Quotient.mk _ P) = aeval (coords x y) P :=
  rfl

lemma isUnit_evalOne_X₀ : IsUnit (evalOne k x y (X₀ k x y)) := by
  rw [evalOne_mk, aeval_X]
  simp [coords]

/-- The ring homomorphism `Γ(D₊(X₀)) = (k[X₀, X₁, X₂] ⧸ 𝔭)_(X₀) → K`, `P / X₀ⁿ ↦ P(1, x, y)`. -/
noncomputable def chartHom : Away (ideal k x y).quotientGrading (X₀ k x y) →+* K :=
  (IsLocalization.Away.lift (S := Localization.Away (X₀ k x y)) (X₀ k x y)
    (isUnit_evalOne_X₀ k x y)).comp (algebraMap _ _)

lemma chartHom_mk (n : ℕ) (a : MvPolynomial (Fin 3) k ⧸ (ideal k x y).toIdeal)
    (ha : a ∈ (ideal k x y).quotientGrading (n • 1)) (P : MvPolynomial (Fin 3) k)
    (hPa : Ideal.Quotient.mk _ P = a) :
    chartHom k x y (Away.mk _ (X₀_mem k x y) n a ha) = aeval (coords x y) P := by
  change (IsLocalization.Away.lift (S := Localization.Away (X₀ k x y)) (X₀ k x y)
    (isUnit_evalOne_X₀ k x y)) (Away.mk _ (X₀_mem k x y) n _ ha).val = _
  rw [Away.val_mk, Localization.mk_eq_mk']
  subst hPa
  refine (IsLocalization.lift_mk'_spec (M := Submonoid.powers (X₀ k x y))
    (S := Localization.Away (X₀ k x y)) _ _ _ ⟨X₀ k x y ^ n, n, rfl⟩).mpr ?_
  simp [evalOne_mk, coords]

/-- `Γ(D₊(X₀)) → K` is injective: a homogeneous `P` of degree `n` with `P(1, x, y) = 0` maps to
`Tⁿ P(1, x, y) = 0` in `K[T]`, hence lies in `𝔭`. -/
lemma chartHom_injective : Function.Injective (chartHom k x y) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (X₀_mem k x y) z
  have ha' : ∃ P ∈ grading (Fin 3) k (n • 1),
      (Ideal.Quotient.mkₐ k (ideal k x y).toIdeal).toLinearMap P = a := ha
  obtain ⟨P, hP, hPa⟩ := ha'
  have hPa' : Ideal.Quotient.mk _ P = a := hPa
  have hP' : P.IsHomogeneous n := by simpa using mem_grading.mp hP
  rw [chartHom_mk k x y n a ha P hPa'] at hz
  have hmem : P ∈ (ideal k x y).toIdeal := by
    rw [toIdeal_ideal, RingHom.mem_ker, homogeneousEval_of_isHomogeneous k x y hP', hz, map_zero,
      mul_zero]
  have ha0 : a = 0 := hPa' ▸ Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  ext
  simp [ha0, Localization.mk_zero]

lemma evalOne_X₀ : evalOne k x y (X₀ k x y) = 1 := by
  rw [evalOne_mk, aeval_X]
  simp [coords]

lemma X₀_ne_zero : X₀ k x y ≠ 0 := fun h ↦ by
  simpa [h] using evalOne_X₀ k x y

instance : IsDomain (MvPolynomial (Fin 3) k ⧸ (ideal k x y).toIdeal) :=
  Ideal.Quotient.isDomain _

/-- The structure map `k → (k[X₀, X₁, X₂] ⧸ 𝔭)₀` is bijective. -/
lemma bijective_algebraMap_quotientGrading_zero :
    Function.Bijective (algebraMap k ((ideal k x y).quotientGrading 0)) := by
  refine ⟨fun r s hrs ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · have h := congrArg (fun z : (ideal k x y).quotientGrading 0 ↦ evalOne k x y (z : _)) hrs
    have e (t : k) : evalOne k x y ((algebraMap k ((ideal k x y).quotientGrading 0) t : _)) =
        algebraMap k K t := by
      change evalOne k x y (Ideal.Quotient.mk _ (C t)) = _
      rw [evalOne_mk, aeval_C]
    exact (algebraMap k K).injective ((e r).symm.trans (h.trans (e s)))
  · obtain ⟨P, hP, rfl⟩ := ha
    have hP' : P.IsHomogeneous 0 := mem_grading.mp hP
    obtain ⟨r, rfl⟩ : ∃ r, P = C r := ⟨P.coeff 0, (totalDegree_eq_zero_iff_eq_C.mp
      (by simpa using hP'.totalDegree_le))⟩
    exact ⟨r, Subtype.ext (by simp)⟩

end AlgebraicGeometry.PlaneCurve

namespace AlgebraicGeometry

open PlaneCurve

variable (k : Type u) [Field k] {K : Type u} [Field K] [Algebra k K] (x y : K)

/-- The projective plane curve through `(1 : x : y)`, `Proj (k[X₀, X₁, X₂] ⧸ 𝔭)` (a curve when
`trdeg_k k(x, y) = 1`). -/
noncomputable abbrev planeCurve : Scheme.{u} :=
  Proj (PlaneCurve.ideal k x y).quotientGrading

namespace PlaneCurve

/-- The structure morphism of the plane curve. -/
noncomputable def toSpec : planeCurve k x y ⟶ Spec (.of k) :=
  Proj.toSpecBase (PlaneCurve.ideal k x y).quotientGrading

instance : IsScalarTower k ((ideal k x y).quotientGrading 0)
    (MvPolynomial (Fin 3) k ⧸ (ideal k x y).toIdeal) :=
  ⟨fun r a b ↦ by
    change ((r • a : (ideal k x y).quotientGrading 0) : _) * b = r • ((a : _) * b)
    rw [Submodule.coe_smul, smul_mul_assoc]⟩

instance : Algebra.FiniteType ((ideal k x y).quotientGrading 0)
    (MvPolynomial (Fin 3) k ⧸ (ideal k x y).toIdeal) :=
  Algebra.FiniteType.of_restrictScalars_finiteType k _ _

instance isProper_toSpec : IsProper (toSpec k x y) := by
  have : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap k ((ideal k x y).quotientGrading 0)))) :=
    isIso_SpecMap_iff.mpr (bijective_algebraMap_quotientGrading_zero k x y)
  rw [toSpec, Proj.toSpecBase, MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)]
  infer_instance

/-- The generic point `(0)` of the plane curve. -/
noncomputable def genericPt : planeCurve k x y where
  asHomogeneousIdeal := ⊥
  isPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]
    exact Ideal.isPrime_bot
  not_irrelevant_le h := by
    have hX : X₀ k x y ∈ HomogeneousIdeal.irrelevant (ideal k x y).quotientGrading := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne _ (X₀_mem k x y) one_ne_zero]
    have := h hX
    rw [← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at this
    exact X₀_ne_zero k x y this

lemma isGenericPoint_genericPt : IsGenericPoint (genericPt k x y) ⊤ := by
  refine Set.eq_univ_of_forall fun p ↦ ?_
  exact (ProjectiveSpectrum.le_iff_mem_closure (ideal k x y).quotientGrading
    (genericPt k x y) p).mp (bot_le (a := p.asHomogeneousIdeal))

instance : IrreducibleSpace (planeCurve k x y) :=
  (irreducibleSpace_def _).mpr (isGenericPoint_genericPt k x y).isIrreducible

lemma genericPt_mem_basicOpen : genericPt k x y ∈ Proj.basicOpen _ (X₀ k x y) := by
  rw [Proj.mem_basicOpen]
  intro h
  rw [← HomogeneousIdeal.mem_iff] at h
  change X₀ k x y ∈ (⊥ : HomogeneousIdeal (ideal k x y).quotientGrading).toIdeal at h
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h
  exact X₀_ne_zero k x y h

/-- The point `(1 : x : y)` of the plane curve with values in `K`. -/
noncomputable def kPoint : Spec (.of K) ⟶ planeCurve k x y :=
  Spec.map (CommRingCat.ofHom (chartHom k x y)) ≫
    Proj.awayι _ (X₀ k x y) (X₀_mem k x y) one_pos

lemma chartHom_algebraMap (r : k) :
    chartHom k x y (algebraMap k (Away (ideal k x y).quotientGrading (X₀ k x y)) r) =
      algebraMap k K r := by
  change (IsLocalization.Away.lift (S := Localization.Away (X₀ k x y)) (X₀ k x y)
    (isUnit_evalOne_X₀ k x y))
      (algebraMap k (Away (ideal k x y).quotientGrading (X₀ k x y)) r).val = _
  rw [HomogeneousLocalization.val_algebraMap,
    IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 3) k ⧸ (ideal k x y).toIdeal),
    IsLocalization.Away.lift, IsLocalization.lift_eq]
  change evalOne k x y (Ideal.Quotient.mk _ (C r)) = _
  rw [evalOne_mk, aeval_C]

/-- `Γ(D₊(X₀)) → K` as a `k`-algebra homomorphism. -/
noncomputable def chartAlgHom : Away (ideal k x y).quotientGrading (X₀ k x y) →ₐ[k] K :=
  { chartHom k x y with commutes' := chartHom_algebraMap k x y }

lemma chartAlgHom_apply (z : Away (ideal k x y).quotientGrading (X₀ k x y)) :
    chartAlgHom k x y z = chartHom k x y z :=
  rfl

/-- The image of `Γ(D₊(X₀))` in `K` is `k[x, y]`. -/
lemma range_chartAlgHom : (chartAlgHom k x y).range = Algebra.adjoin k {x, y} := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨z, rfl⟩
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (X₀_mem k x y) z
    have ha' : ∃ P ∈ grading (Fin 3) k (n • 1),
        (Ideal.Quotient.mkₐ k (ideal k x y).toIdeal).toLinearMap P = a := ha
    obtain ⟨P, -, hPa⟩ := ha'
    change chartHom k x y _ ∈ _
    rw [chartHom_mk k x y n a ha P hPa]
    have hP : aeval (coords x y) P ∈ Algebra.adjoin k (Set.range (coords x y)) := by
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact ⟨P, rfl⟩
    refine Algebra.adjoin_le ?_ hP
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact one_mem _
    · exact Algebra.subset_adjoin (by simp [coords])
    · exact Algebra.subset_adjoin (by simp [coords])
  · rw [Algebra.adjoin_le_iff]
    rintro z (hz | hz)
    · rw [hz]
      refine ⟨Away.mk _ (X₀_mem k x y) 1 (Ideal.Quotient.mk _ (X 1))
        (HomogeneousIdeal.mk_mem_quotientGrading (by simpa using X_mem_grading 1)), ?_⟩
      change chartHom k x y _ = _
      rw [chartHom_mk k x y 1 _ _ (X 1) rfl, aeval_X]
      rfl
    · rw [Set.mem_singleton_iff.mp hz]
      refine ⟨Away.mk _ (X₀_mem k x y) 1 (Ideal.Quotient.mk _ (X 2))
        (HomogeneousIdeal.mk_mem_quotientGrading (by simpa using X_mem_grading 2)), ?_⟩
      change chartHom k x y _ = _
      rw [chartHom_mk k x y 1 _ _ (X 2) rfl, aeval_X]
      rfl

lemma kPoint_toSpec : kPoint k x y ≫ toSpec k x y =
    Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  rw [kPoint, Category.assoc, toSpec, Proj.awayι_toSpecBase, ← Spec.map_comp]
  congr 1
  ext r
  exact chartHom_algebraMap k x y r

/-- The `K`-point `(1 : x : y)` lies over the generic point of the plane curve. -/
lemma kPoint_apply (t : Spec (.of K)) : kPoint k x y t = genericPt k x y := by
  set ι := Proj.awayι (ideal k x y).quotientGrading (X₀ k x y) (X₀_mem k x y) one_pos
  set s := Spec.map (CommRingCat.ofHom (chartHom k x y))
  -- the image of `t` in `Spec Γ(D₊(X₀))` is the zero ideal, which specializes to every point
  have h0 (q : Spec (.of (Away (ideal k x y).quotientGrading (X₀ k x y)))) : s t ⤳ q := by
    refine (PrimeSpectrum.le_iff_specializes (s t) q).mp fun a ha ↦ ?_
    change chartHom k x y a ∈ t.asIdeal at ha
    have : (t.asIdeal : Ideal K).IsPrime := PrimeSpectrum.isPrime t
    rw [Ideal.eq_bot_of_prime t.asIdeal, Ideal.mem_bot] at ha
    rw [(injective_iff_map_eq_zero _).mp (chartHom_injective k x y) a ha]
    exact zero_mem _
  obtain ⟨q₀, hq₀⟩ : genericPt k x y ∈ Set.range ι := by
    rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]
    exact genericPt_mem_basicOpen k x y
  have hsp : kPoint k x y t ⤳ genericPt k x y := by
    rw [← hq₀]
    exact (h0 q₀).map ι.continuous
  have hg : IsGenericPoint (kPoint k x y t) ⊤ := by
    refine Set.eq_univ_of_forall fun p ↦ ?_
    exact specializes_iff_mem_closure.mp
      (hsp.trans ((isGenericPoint_genericPt k x y).specializes (Set.mem_univ p)))
  exact hg.eq (isGenericPoint_genericPt k x y)

end PlaneCurve

end AlgebraicGeometry
