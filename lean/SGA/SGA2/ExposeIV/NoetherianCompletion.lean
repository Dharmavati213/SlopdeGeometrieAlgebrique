/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Noetherianity of the actual adic completion

A surjective ring map induces a surjective map on completions with respect
to an ideal and its image. Applying this to polynomial evaluation at finite
generators presents the actual completion as a quotient of a finite-variable
power series ring. No closedness or finite generation of arbitrary ideals
in the completed ring is assumed.
-/

noncomputable section
universe u v

namespace SGA.SGA2.ExposeIV

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- The actual ring-valued completion evaluations retain the original transitions. -/
theorem completion_eval_transition (I : Ideal A) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on I A with
  | _ x =>
    simpa using AdicCompletion.Ideal.mk_eq_mk I h x

/-- The map on the original power quotients induced by a ring map. -/
def completionQuotientRingMap (I : Ideal A) (f : A →+* B) (n : ℕ) :
    A ⧸ I ^ n →+* B ⧸ (I.map f) ^ n :=
  Ideal.quotientMap _ f (Ideal.map_le_iff_le_comap.mp (by rw [Ideal.map_pow]))

@[simp]
theorem completionQuotientRingMap_mk (I : Ideal A) (f : A →+* B) (n : ℕ) (a : A) :
    completionQuotientRingMap I f n (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (f a) := rfl

/-- The original quotient maps commute with the power-filtration transitions. -/
theorem completionQuotientRingMap_transition (I : Ideal A) (f : A →+* B)
    {m n : ℕ} (h : m ≤ n) (x : A ⧸ I ^ n) :
    Ideal.Quotient.factorPow (I.map f) h (completionQuotientRingMap I f n x) =
      completionQuotientRingMap I f m (Ideal.Quotient.factorPow I h x) := by
  induction x using Quotient.inductionOn'
  rfl

/-- Compatibility of the actual induced quotient maps with completion evaluations. -/
theorem completionQuotientRingMap_eval_compatible (I : Ideal A) (f : A →+* B)
    {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (I.map f) h).comp
        ((completionQuotientRingMap I f n).comp (AdicCompletion.evalₐ I n).toRingHom) =
      (completionQuotientRingMap I f m).comp (AdicCompletion.evalₐ I m).toRingHom := by
  ext x
  simp only [RingHom.comp_apply, completionQuotientRingMap_transition]
  exact congrArg (completionQuotientRingMap I f _) (completion_eval_transition I h x)

/-- The genuine induced ring map between the actual completions. -/
def completionRingMap (I : Ideal A) (f : A →+* B) :
    AdicCompletion I A →+* AdicCompletion (I.map f) B :=
  AdicCompletion.liftRingHom (I.map f)
    (fun n => (completionQuotientRingMap I f n).comp (AdicCompletion.evalₐ I n).toRingHom)
    (completionQuotientRingMap_eval_compatible I f)

/-- Its evaluations are the original induced quotient maps. -/
@[simp]
theorem completionRingMap_eval (I : Ideal A) (f : A →+* B) (n : ℕ)
    (x : AdicCompletion I A) :
    AdicCompletion.evalₐ (I.map f) n (completionRingMap I f x) =
      completionQuotientRingMap I f n (AdicCompletion.evalₐ I n x) := by
  exact AdicCompletion.evalₐ_liftRingHom _ _
    (completionQuotientRingMap_eval_compatible I f) n x

/-- The induced map retains the original map on original ring elements. -/
@[simp]
theorem completionRingMap_of (I : Ideal A) (f : A →+* B) (a : A) :
    completionRingMap I f (AdicCompletion.of I A a) =
      AdicCompletion.of (I.map f) B (f a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  simp

/-- Naturality for the actual ring maps to completion. -/
theorem completionRingMap_comp_algebraMap (I : Ideal A) (f : A →+* B) :
    (completionRingMap I f).comp (algebraMap A (AdicCompletion I A)) =
      (algebraMap B (AdicCompletion (I.map f) B)).comp f :=
  RingHom.ext (completionRingMap_of I f)

/-- The defining ideal on the completed source maps to the defining ideal
on the completed target, with the actual scalar-change ring maps. -/
theorem completionRingMap_ideal_map (I : Ideal A) (f : A →+* B) :
    (I.map (algebraMap A (AdicCompletion I A))).map (completionRingMap I f) =
      (I.map f).map (algebraMap B (AdicCompletion (I.map f) B)) := by
  rw [Ideal.map_map, completionRingMap_comp_algebraMap, ← Ideal.map_map]

/-- Every residue of the actual completion modulo its defining ideal has
an original ring representative. -/
theorem completion_residue_algebraMap_surjective (I : Ideal A) (hI : I.FG) :
    Function.Surjective ((Ideal.Quotient.mk
      (I.map (algebraMap A (AdicCompletion I A)))).comp
        (algebraMap A (AdicCompletion I A))) := by
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I x)
  refine ⟨a, ?_⟩
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [← AdicCompletion.ker_evalOneₐ_eq_map I hI, RingHom.mem_ker]
  change AdicCompletion.evalOneₐ I (AdicCompletion.of I A a - x) = 0
  rw [map_sub, AdicCompletion.evalOneₐ_of, ha, sub_self]

/-- Completion preserves a surjective ring map for a finitely generated
defining ideal. Surjectivity follows from genuine completeness and the
proved original residue map, not from assumed closure of an image. -/
theorem completionRingMap_surjective (I : Ideal A) (hI : I.FG)
    (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (completionRingMap I f) := by
  let K := I.map (algebraMap A (AdicCompletion I A))
  have : IsAdicComplete K (AdicCompletion I A) := AdicCompletion.isAdicComplete_self I hI
  have : IsAdicComplete ((I.map f).map (algebraMap B (AdicCompletion (I.map f) B)))
      (AdicCompletion (I.map f) B) := AdicCompletion.isAdicComplete_self _ (hI.map f)
  have hK : K.map (completionRingMap I f) =
      (I.map f).map (algebraMap B (AdicCompletion (I.map f) B)) :=
    completionRingMap_ideal_map I f
  have : IsHausdorff (K.map (completionRingMap I f)) (AdicCompletion (I.map f) B) := by
    rw [hK]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := K) (completionRingMap I f)
  have hres := (completion_residue_algebraMap_surjective (I.map f) (hI.map f)).comp hf
  rw [← hK] at hres
  intro q
  obtain ⟨a, ha⟩ := hres q
  refine ⟨AdicCompletion.of I A a, ?_⟩
  simpa only [Function.comp_apply, RingHom.comp_apply, completionRingMap_of,
    AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] using ha

/-- Actual noetherianity descends along the genuine completion map. -/
theorem completion_isNoetherian_of_surjective (I : Ideal A) (hI : I.FG)
    (f : A →+* B) (hf : Function.Surjective f)
    [IsNoetherianRing (AdicCompletion I A)] :
    IsNoetherianRing (AdicCompletion (I.map f) B) :=
  isNoetherianRing_of_surjective (AdicCompletion I A) _ (completionRingMap I f)
    (completionRingMap_surjective I hI f hf)

/-- Evaluation sends the variable ideal to the ideal generated by the
specified actual coefficients. -/
theorem polynomial_variableIdeal_map_eval {σ : Type*} (s : σ → A) :
    (MvPolynomial.idealOfVars σ A).map (MvPolynomial.eval₂Hom (RingHom.id A) s) =
      Ideal.span (Set.range s) := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
  have h : (MvPolynomial.eval₂Hom (RingHom.id A) s) ∘ MvPolynomial.X = s := by
    funext i
    exact MvPolynomial.eval₂Hom_X' (RingHom.id A) s i
  rw [h]

/-- The actual completion of a noetherian ring is noetherian for every
ideal. A finite-variable power series ring supplies a genuine noetherian
source for the proved completion surjection. -/
theorem adicCompletion_isNoetherianRing [IsNoetherianRing A] (I : Ideal A) :
    IsNoetherianRing (AdicCompletion I A) := by
  obtain ⟨n, s, hs⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  let P := MvPolynomial (Fin n) A
  let K := MvPolynomial.idealOfVars (Fin n) A
  let f : P →+* A := MvPolynomial.eval₂Hom (RingHom.id A) s
  have hf : Function.Surjective f := fun a => ⟨MvPolynomial.C a,
    MvPolynomial.eval₂Hom_C _ _ _⟩
  have hmap : K.map f = I := (polynomial_variableIdeal_map_eval s).trans hs
  have : IsNoetherianRing (AdicCompletion K P) :=
    isNoetherianRing_of_ringEquiv (MvPowerSeries (Fin n) A)
      (MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) A).toRingEquiv
  rw [← hmap]
  exact completion_isNoetherian_of_surjective K (MvPolynomial.idealOfVars_fg _ _) f hf

attribute [instance] adicCompletion_isNoetherianRing

end SGA.SGA2.ExposeIV
