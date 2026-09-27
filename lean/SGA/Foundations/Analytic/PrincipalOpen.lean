/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Analytic.OpenSubspace
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Analytification of principal open subsets

Let `A = 𝕜[x₁, …, xₙ]/(g)` and `p ∈ 𝕜[x]`. The localization `A_p` is presented as
`𝕜[x₁, …, xₙ, t]/(g, t p - 1)` (`localizationPolys g p`). Its analytification is isomorphic to
the open subspace `{p ≠ 0}` of `Spec(A)^an`, i.e. to the local model `Z(g) ∩ {p ≠ 0}`
(`principalOpenIso`): mutually inverse morphisms are the projection `(x, t) ↦ x` and
`x ↦ (x, 1/p(x))`. Consequently the morphism `Spec(A_p)^an → Spec(A)^an` induced by
`A → A_p` is an open immersion onto `φ⁻¹(D(p))` (`isOpenImmersion_analytificationMap_localization`,
`range_analytificationMap_localization`).
-/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Filter Topology

namespace AnalyticGeometry

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n k : ℕ}
  (g : Fin k → MvPolynomial (Fin n) 𝕜) (p : MvPolynomial (Fin n) 𝕜)

/-- The presentation `(g, t p - 1)` of the localization `A_p`, in the variables `x₁, …, xₙ, t`. -/
def localizationPolys : Fin (k + 1) → MvPolynomial (Fin (n + 1)) 𝕜 :=
  Fin.snoc (fun i ↦ MvPolynomial.rename Fin.castSucc (g i))
    (MvPolynomial.X (Fin.last n) * MvPolynomial.rename Fin.castSucc p - 1)

omit [CompleteSpace 𝕜] in
@[simp] lemma localizationPolys_castSucc (i : Fin k) :
    localizationPolys g p i.castSucc = MvPolynomial.rename Fin.castSucc (g i) := by
  simp [localizationPolys]

omit [CompleteSpace 𝕜] in
@[simp] lemma localizationPolys_last :
    localizationPolys g p (Fin.last k) =
      MvPolynomial.X (Fin.last n) * MvPolynomial.rename Fin.castSucc p - 1 := by
  simp [localizationPolys]

omit [CompleteSpace 𝕜] in
lemma isOpen_eval_ne_zero : IsOpen {z : Fin n → 𝕜 | MvPolynomial.eval z p ≠ 0} :=
  isOpen_ne_fun (MvPolynomial.continuous_eval p) continuous_const

/-- The local model `Z(g) ∩ {p ≠ 0}`. -/
abbrev principalModel : LocalModelData 𝕜 (Fin n → 𝕜) :=
  (polynomialModel g).restrictU _ (isOpen_eval_ne_zero p)

omit [CompleteSpace 𝕜] in
lemma eval_localizationPolys_last (w : Fin (n + 1) → 𝕜) :
    MvPolynomial.eval w (localizationPolys g p (Fin.last k)) =
      w (Fin.last n) * MvPolynomial.eval (fun i ↦ w i.castSucc) p - 1 := by
  simp [MvPolynomial.eval_rename, Function.comp_def]

omit [CompleteSpace 𝕜] in
lemma eval_localizationPolys_castSucc (w : Fin (n + 1) → 𝕜) (i : Fin k) :
    MvPolynomial.eval w (localizationPolys g p i.castSucc) =
      MvPolynomial.eval (fun j ↦ w j.castSucc) (g i) := by
  simp [MvPolynomial.eval_rename, Function.comp_def]

/-- The projection `Z(g, t p - 1) → Z(g) ∩ {p ≠ 0}`, `(x, t) ↦ x`. -/
def localizationProj :
    LocalModelData.AnalyticMap (polynomialModel (localizationPolys g p)) (principalModel g p) where
  toFun w i := w i.castSucc
  analyticAt _ _ := AnalyticAt.pi fun _ ↦ MvPowerSeries.analyticAt_apply _ _
  mapsTo y hy := by
    refine ⟨trivial, fun h0 ↦ ?_⟩
    have := hy.2 (Fin.last k)
    change MvPolynomial.eval (y : Fin (n + 1) → 𝕜) (localizationPolys g p (Fin.last k)) = 0
      at this
    rw [eval_localizationPolys_last] at this
    rw [h0, mul_zero, zero_sub, neg_eq_zero] at this
    exact one_ne_zero this
  mem_ideal y i := by
    rw [stalkPullback_germOf]
    have e : (fun w ↦ (principalModel g p).f i (fun j ↦ w j.castSucc)) =
        fun w ↦ (polynomialModel (localizationPolys g p)).f i.castSucc w := by
      funext w
      exact (eval_localizationPolys_castSucc g p w i).symm
    rw [germOf_congr _ (Filter.EventuallyEq.of_eq e)]
    exact Ideal.subset_span ⟨i.castSucc, rfl⟩

/-- The section `Z(g) ∩ {p ≠ 0} → Z(g, t p - 1)`, `x ↦ (x, 1/p(x))`. -/
def localizationSection :
    LocalModelData.AnalyticMap (principalModel g p) (polynomialModel (localizationPolys g p)) where
  toFun z := Fin.snoc z (MvPolynomial.eval z p)⁻¹
  analyticAt y hy := by
    refine AnalyticAt.pi fun i ↦ ?_
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact (analyticAt_eval_mvPolynomial p y).inv hy.1.2
    | cast j =>
      simp only [Fin.snoc_castSucc]
      exact MvPowerSeries.analyticAt_apply j y
  mapsTo _ _ := trivial
  mem_ideal y i := by
    rw [stalkPullback_germOf]
    induction i using Fin.lastCases with
    | last =>
      have hp : ∀ᶠ z in 𝓝 (y : Fin n → 𝕜), MvPolynomial.eval z p ≠ 0 :=
        (isOpen_eval_ne_zero p).mem_nhds (LocalModelData.mem_U _ y).2
      have e : (fun z ↦ (polynomialModel (localizationPolys g p)).f (Fin.last k)
          (Fin.snoc z (MvPolynomial.eval z p)⁻¹)) =ᶠ[𝓝 (y : Fin n → 𝕜)] fun _ ↦ 0 := by
        filter_upwards [hp] with z hz
        change MvPolynomial.eval _ (localizationPolys g p (Fin.last k)) = 0
        rw [eval_localizationPolys_last]
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [inv_mul_cancel₀ hz, sub_self]
      rw [germOf_congr _ e, germOf_zero]
      exact Ideal.zero_mem _
    | cast j =>
      have e : (fun z ↦ (polynomialModel (localizationPolys g p)).f j.castSucc
          (Fin.snoc z (MvPolynomial.eval z p)⁻¹)) = fun z ↦ (principalModel g p).f j z := by
        funext z
        change MvPolynomial.eval _ (localizationPolys g p j.castSucc) = _
        rw [eval_localizationPolys_castSucc]
        simp only [Fin.snoc_castSucc]
        rfl
      rw [germOf_congr _ (Filter.EventuallyEq.of_eq e)]
      exact Ideal.subset_span ⟨j, rfl⟩

lemma localizationProj_comp_section :
    ((localizationProj g p).comp (localizationSection g p)).toHom =
      (LocalModelData.AnalyticMap.id (principalModel g p)).toHom := by
  refine LocalModelData.AnalyticMap.toHom_eq_of_sub_mem _ _ fun y j ↦ ?_
  have e : (fun z ↦ ((localizationProj g p).comp (localizationSection g p)).toFun z j -
      (LocalModelData.AnalyticMap.id (principalModel g p)).toFun z j) = fun _ ↦ 0 := by
    funext z
    simp [localizationProj, localizationSection, LocalModelData.AnalyticMap.comp,
      LocalModelData.AnalyticMap.id]
  rw [germOf_congr _ (Filter.EventuallyEq.of_eq e), germOf_zero]
  exact Ideal.zero_mem _

lemma localizationSection_comp_proj :
    ((localizationSection g p).comp (localizationProj g p)).toHom =
      (LocalModelData.AnalyticMap.id (polynomialModel (localizationPolys g p))).toHom := by
  refine LocalModelData.AnalyticMap.toHom_eq_of_sub_mem _ _ fun y j ↦ ?_
  induction j using Fin.lastCases with
  | cast j =>
    have e : (fun z ↦ ((localizationSection g p).comp (localizationProj g p)).toFun z j.castSucc -
        (LocalModelData.AnalyticMap.id (polynomialModel (localizationPolys g p))).toFun z
          j.castSucc) = fun _ ↦ 0 := by
      funext z
      simp [localizationProj, localizationSection, LocalModelData.AnalyticMap.comp,
        LocalModelData.AnalyticMap.id]
    rw [germOf_congr _ (Filter.EventuallyEq.of_eq e), germOf_zero]
    exact Ideal.zero_mem _
  | last =>
    /- `1/p(x) - t = -(t p(x) - 1)/p(x)` lies in the ideal. -/
    have hpy : MvPolynomial.eval (fun i ↦ (y : Fin (n + 1) → 𝕜) i.castSucc) p ≠ 0 :=
      ((localizationProj g p).mapsTo y y.2).2
    have hP : AnalyticAt 𝕜 (fun w : Fin (n + 1) → 𝕜 ↦
        MvPolynomial.eval (fun i ↦ w i.castSucc) p) y :=
      (analyticAt_eval_mvPolynomial p _).comp
        (AnalyticAt.pi fun _ ↦ MvPowerSeries.analyticAt_apply _ _)
    have hinv : AnalyticAt 𝕜 (fun w : Fin (n + 1) → 𝕜 ↦
        -(MvPolynomial.eval (fun i ↦ w i.castSucc) p)⁻¹) y := (hP.inv hpy).neg
    have hF : AnalyticAt 𝕜 (fun w ↦ MvPolynomial.eval w (localizationPolys g p (Fin.last k)))
        (y : Fin (n + 1) → 𝕜) := analyticAt_eval_mvPolynomial _ _
    have e : (fun z ↦ ((localizationSection g p).comp (localizationProj g p)).toFun z
        (Fin.last n) -
          (LocalModelData.AnalyticMap.id (polynomialModel (localizationPolys g p))).toFun z
            (Fin.last n)) =ᶠ[𝓝 (y : Fin (n + 1) → 𝕜)]
        (fun w ↦ MvPolynomial.eval w (localizationPolys g p (Fin.last k))) *
          fun w ↦ -(MvPolynomial.eval (fun i ↦ w i.castSucc) p)⁻¹ := by
      filter_upwards [hP.continuousAt.eventually_ne hpy] with w hw
      simp only [LocalModelData.AnalyticMap.comp, localizationSection, localizationProj,
        LocalModelData.AnalyticMap.id, Function.comp_apply, Fin.snoc_last, id, Pi.mul_apply]
      rw [eval_localizationPolys_last]
      field_simp
      ring
    rw [germOf_congr _ e, germOf_mul hF hinv]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Fin.last k, rfl⟩)

/-- **Principal open subsets**: `Spec(A_p)^an` is isomorphic to the local model
`Z(g) ∩ {p ≠ 0}`, the open subspace of `Spec(A)^an` where `p` does not vanish. -/
def principalOpenIso :
    analytification (localizationPolys g p) ≅ (principalModel g p).toLocallyRingedSpace where
  hom := (localizationProj g p).toHom
  inv := (localizationSection g p).toHom
  hom_inv_id := by
    rw [← LocalModelData.AnalyticMap.toHom_comp, localizationSection_comp_proj,
      LocalModelData.AnalyticMap.toHom_id]
  inv_hom_id := by
    rw [← LocalModelData.AnalyticMap.toHom_comp, localizationProj_comp_section,
      LocalModelData.AnalyticMap.toHom_id]

/-- The localization map `A = 𝕜[x]/(g) → A_p = 𝕜[x, t]/(g, t p - 1)`. -/
def localizationAlgHom :
    PresentedAlgebra g →ₐ[𝕜] PresentedAlgebra (localizationPolys g p) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ 𝕜 _).comp (MvPolynomial.rename Fin.castSucc))
    fun a ha ↦ by
      have : Ideal.span (Set.range g) ≤ RingHom.ker
          ((Ideal.Quotient.mkₐ 𝕜 (Ideal.span (Set.range (localizationPolys g p)))).comp
            (MvPolynomial.rename Fin.castSucc)) := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker]
        change Ideal.Quotient.mk _ (MvPolynomial.rename Fin.castSucc (g i)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem,
          ← localizationPolys_castSucc g p i]
        exact Ideal.subset_span ⟨i.castSucc, rfl⟩
      exact this ha

omit [CompleteSpace 𝕜] in
lemma localizationAlgHom_mk (q : MvPolynomial (Fin n) 𝕜) :
    localizationAlgHom g p (Ideal.Quotient.mk _ q) =
      Ideal.Quotient.mk _ (MvPolynomial.rename Fin.castSucc q) := rfl

/-- The morphism `Spec(A_p)^an → Spec(A)^an` induced by the localization map is the isomorphism
`principalOpenIso` followed by the inclusion of the open subspace `{p ≠ 0}`. -/
theorem analytificationMap_localization :
    analytificationMap g (localizationPolys g p) (localizationAlgHom g p) =
      (principalOpenIso g p).hom ≫
        ((polynomialModel g).inclusionMap _ (isOpen_eval_ne_zero p)).toHom := by
  have hPg : ∀ i, MvPolynomial.aeval (fun j ↦ MvPolynomial.X (R := 𝕜) j.castSucc) (g i) ∈
      Ideal.span (Set.range (localizationPolys g p)) := fun i ↦ by
    have : MvPolynomial.aeval (fun j ↦ MvPolynomial.X (R := 𝕜) j.castSucc) (g i) =
        localizationPolys g p i.castSucc := by
      rw [localizationPolys_castSucc, MvPolynomial.rename_eq_aeval]
      rfl
    rw [this]
    exact Ideal.subset_span ⟨i.castSucc, rfl⟩
  rw [← polyAnalyticMap_toHom_eq (localizationAlgHom g p) _ (fun i ↦ by
    rw [localizationAlgHom_mk, MvPolynomial.rename_X]) hPg]
  change _ = (localizationProj g p).toHom ≫ _
  rw [← LocalModelData.AnalyticMap.toHom_comp]
  refine LocalModelData.AnalyticMap.toHom_eq_of_sub_mem _ _ fun y j ↦ ?_
  have e : (fun z ↦ (polyAnalyticMap g (localizationPolys g p) _ hPg).toFun z j -
      (((polynomialModel g).inclusionMap _ (isOpen_eval_ne_zero p)).comp
        (localizationProj g p)).toFun z j) = fun _ ↦ 0 := by
    funext z
    simp [polyAnalyticMap, localizationProj, LocalModelData.inclusionMap,
      LocalModelData.AnalyticMap.comp]
  rw [germOf_congr _ (Filter.EventuallyEq.of_eq e), germOf_zero]
  exact Ideal.zero_mem _

/-- `Spec(A_p)^an → Spec(A)^an` is an open immersion. -/
theorem isOpenImmersion_analytificationMap_localization :
    LocallyRingedSpace.IsOpenImmersion
      (analytificationMap g (localizationPolys g p) (localizationAlgHom g p)) := by
  have := (polynomialModel g).isOpenImmersion_inclusion _ (isOpen_eval_ne_zero p)
  rw [analytificationMap_localization]
  infer_instance

/-- The image of `Spec(A_p)^an → Spec(A)^an` is the set of points where `p` does not vanish,
i.e. the inverse image `φ⁻¹(D(p))` of the principal open subset `D(p) ⊆ Spec A`
(`eval_ne_zero_iff_notMem_toSpec`). -/
theorem mem_range_analytificationMap_localization (x : (polynomialModel g).zeroSet) :
    x ∈ Set.range (analytificationMap g (localizationPolys g p) (localizationAlgHom g p)).base ↔
      MvPolynomial.eval (x : Fin n → 𝕜) p ≠ 0 := by
  rw [analytificationMap_localization]
  constructor
  · rintro ⟨w, rfl⟩
    exact ((localizationProj g p).mapsTo w w.2).2
  · intro hx
    refine ⟨(principalOpenIso g p).inv.base ⟨x.1, ⟨trivial, hx⟩, x.2.2⟩, ?_⟩
    change (((principalOpenIso g p).inv ≫ (principalOpenIso g p).hom) ≫ _).base _ = _
    rw [Iso.inv_hom_id, Category.id_comp]
    rfl

/-- A point `x ∈ Z(g)` lies over the principal open subset `D(p) ⊆ Spec A` if and only if
`p(x) ≠ 0`. -/
lemma eval_ne_zero_iff_notMem_toSpec (x : (polynomialModel g).zeroSet) :
    MvPolynomial.eval (x : Fin n → 𝕜) p ≠ 0 ↔
      (Ideal.Quotient.mk _ p : PresentedAlgebra g) ∉ ((toSpec g).base x).asIdeal := by
  rw [toSpec_base_asIdeal, RingHom.mem_ker, evalPoint_mk]

end AnalyticGeometry
