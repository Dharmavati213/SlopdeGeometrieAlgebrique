/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.PrincipalOpen

/-!
# The presentation of a localization

For `A = 𝕜[x₁, …, xₙ]/(g)` and `p ∈ 𝕜[x]`, the algebra `𝕜[x₁, …, xₙ, t]/(g, t p - 1)`
(`PresentedAlgebra (localizationPolys g p)`) is the localization `A_p`
(`isLocalization_away_localizationAlgHom`). Together with `principalOpenIso`, this identifies the
analytification of a principal open subset `D(p) ⊆ Spec A` with the open subspace `{p ≠ 0}` of
`Spec(A)^an`, for any presentation of the localization.

Reference: Stacks Project, Tag 00R4 (the standard presentation of `A_f`).
-/

noncomputable section

open MvPolynomial

namespace AnalyticGeometry

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n k : ℕ}
  (g : Fin k → MvPolynomial (Fin n) 𝕜) (p : MvPolynomial (Fin n) 𝕜)

/-- The class of `p` in `A = 𝕜[x]/(g)`. -/
abbrev classOfPoly : PresentedAlgebra g := Ideal.Quotient.mk _ p

/-- The values of the variables `x₁, …, xₙ, t` in `A_p`. -/
def localizationValues : Fin (n + 1) → Localization.Away (classOfPoly g p) :=
  Fin.snoc (fun j ↦ algebraMap (PresentedAlgebra g) _ (Ideal.Quotient.mk _ (X j)))
    (IsLocalization.Away.invSelf (classOfPoly g p))

omit [CompleteSpace 𝕜] in
lemma aeval_localizationValues_rename (q : MvPolynomial (Fin n) 𝕜) :
    aeval (localizationValues g p) (rename Fin.castSucc q) =
      algebraMap (PresentedAlgebra g) _ (Ideal.Quotient.mk _ q) := by
  rw [aeval_rename]
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C, show (Ideal.Quotient.mk _ (C c) : PresentedAlgebra g) = algebraMap 𝕜 _ c from rfl,
      ← IsScalarTower.algebraMap_apply]
  | add q₁ q₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | mul_X q j h =>
    simp only [map_mul, aeval_X, Function.comp_apply]
    rw [h]
    simp only [localizationValues, Fin.snoc_castSucc]

/-- The homomorphism `𝕜[x, t]/(g, t p - 1) → A_p`. -/
def presentationToLocalization :
    PresentedAlgebra (localizationPolys g p) →ₐ[𝕜] Localization.Away (classOfPoly g p) :=
  Ideal.Quotient.liftₐ _ (aeval (localizationValues g p)) fun a ha ↦ by
    have : Ideal.span (Set.range (localizationPolys g p)) ≤
        RingHom.ker (aeval (R := 𝕜) (localizationValues g p)) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      induction i using Fin.lastCases with
      | last =>
        rw [localizationPolys_last, map_sub, map_mul, aeval_X, aeval_localizationValues_rename,
          map_one, localizationValues, Fin.snoc_last, mul_comm,
          IsLocalization.Away.mul_invSelf, sub_self]
      | cast j =>
        rw [localizationPolys_castSucc, aeval_localizationValues_rename,
          (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩) :
            Ideal.Quotient.mk (Ideal.span (Set.range g)) (g j) = 0), map_zero]
    exact this ha

omit [CompleteSpace 𝕜] in
lemma localizationAlgHom_mul_X_last :
    localizationAlgHom g p (classOfPoly g p) * Ideal.Quotient.mk _ (X (Fin.last n)) = 1 := by
  rw [localizationAlgHom_mk, ← map_mul, mul_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _),
    ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← localizationPolys_last g p]
  exact Ideal.subset_span ⟨_, rfl⟩

omit [CompleteSpace 𝕜] in
lemma isUnit_localizationAlgHom : IsUnit (localizationAlgHom g p (classOfPoly g p)) :=
  IsUnit.of_mul_eq_one _ (localizationAlgHom_mul_X_last g p)

/-- The homomorphism `A_p → 𝕜[x, t]/(g, t p - 1)`. -/
def localizationToPresentation :
    Localization.Away (classOfPoly g p) →+* PresentedAlgebra (localizationPolys g p) :=
  IsLocalization.Away.lift (classOfPoly g p) (g := (localizationAlgHom g p).toRingHom)
    (isUnit_localizationAlgHom g p)

omit [CompleteSpace 𝕜] in
lemma localizationToPresentation_algebraMap (a : PresentedAlgebra g) :
    localizationToPresentation g p (algebraMap _ _ a) = localizationAlgHom g p a :=
  IsLocalization.Away.lift_eq _ _ a

omit [CompleteSpace 𝕜] in
lemma presentationToLocalization_localizationAlgHom (a : PresentedAlgebra g) :
    presentationToLocalization g p (localizationAlgHom g p a) = algebraMap _ _ a := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [localizationAlgHom_mk]
  exact aeval_localizationValues_rename g p q

omit [CompleteSpace 𝕜] in
lemma presentationToLocalization_comp_localizationToPresentation :
    (presentationToLocalization g p).toRingHom.comp (localizationToPresentation g p) =
      RingHom.id _ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (classOfPoly g p)) (RingHom.ext fun a ↦ ?_)
  simp only [RingHom.comp_apply, localizationToPresentation_algebraMap, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, presentationToLocalization_localizationAlgHom, RingHom.id_apply]

omit [CompleteSpace 𝕜] in
lemma localizationToPresentation_comp_presentationToLocalization :
    (localizationToPresentation g p).comp (presentationToLocalization g p).toRingHom =
      RingHom.id _ := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c ↦ ?_) fun i ↦ ?_)
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply]
    rw [show (Ideal.Quotient.mk _ (C c) : PresentedAlgebra (localizationPolys g p)) =
      algebraMap 𝕜 _ c from rfl, AlgHom.commutes, IsScalarTower.algebraMap_apply 𝕜
        (PresentedAlgebra g) (Localization.Away (classOfPoly g p)),
      localizationToPresentation_algebraMap, AlgHom.commutes]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply]
    induction i using Fin.lastCases with
    | last =>
      change localizationToPresentation g p (aeval (localizationValues g p) (X (Fin.last n))) = _
      rw [aeval_X, localizationValues, Fin.snoc_last]
      have h := isUnit_localizationAlgHom g p
      have key := congrArg (localizationToPresentation g p)
        (IsLocalization.Away.mul_invSelf (S := Localization.Away (classOfPoly g p))
          (classOfPoly g p))
      rw [map_mul, localizationToPresentation_algebraMap, map_one] at key
      exact h.mul_left_cancel (key.trans (localizationAlgHom_mul_X_last g p).symm)
    | cast j =>
      change localizationToPresentation g p (aeval (localizationValues g p) (X j.castSucc)) = _
      rw [aeval_X, localizationValues, Fin.snoc_castSucc, localizationToPresentation_algebraMap,
        localizationAlgHom_mk, rename_X]

omit [CompleteSpace 𝕜] in
/-- `𝕜[x, t]/(g, t p - 1)` is the localization `A_p` of `A = 𝕜[x]/(g)` (via
`localizationAlgHom`). -/
theorem isLocalization_away_localizationAlgHom :
    letI := (localizationAlgHom g p).toRingHom.toAlgebra
    IsLocalization.Away (classOfPoly g p) (PresentedAlgebra (localizationPolys g p)) := by
  let := (localizationAlgHom g p).toRingHom.toAlgebra
  let e : Localization.Away (classOfPoly g p) ≃ₐ[PresentedAlgebra g]
      PresentedAlgebra (localizationPolys g p) :=
    { toRingEquiv := RingEquiv.ofRingHom (localizationToPresentation g p)
        (presentationToLocalization g p).toRingHom
        (localizationToPresentation_comp_presentationToLocalization g p)
        (presentationToLocalization_comp_localizationToPresentation g p)
      commutes' := localizationToPresentation_algebraMap g p }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (classOfPoly g p)) e

end AnalyticGeometry
