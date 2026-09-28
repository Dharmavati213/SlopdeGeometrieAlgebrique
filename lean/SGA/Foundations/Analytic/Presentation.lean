/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.LocalModelHom
import SGA.Foundations.Analytic.Hadamard
import SGA.Foundations.Analytic.Analytification
import SGA.Foundations.Analytic.Flatness

/-!
# Morphisms into local models only depend on classes; independence of the presentation

For a local model `D ⊆ 𝕜ⁿ`, the morphism `Z(D') → Z(D)` induced by an analytic map `Φ` only
depends on the classes of the components of `Φ` modulo the ideal of `D'`
(`AnalyticMap.toHom_eq_of_sub_mem`), by Hadamard's lemma. Consequently the analytification
`Spec(A)^an` of a finitely presented algebra `A` does not depend, up to isomorphism, on the chosen
presentation `A ≅ 𝕜[x]/(g)` (`analytificationIso`), functorially in `A` (`analytificationMap`,
[SGA 1, XII.1.1–1.2]).
-/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Filter Topology

namespace AnalyticGeometry

namespace LocalModelData

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n : ℕ}
  {E' : Type} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

omit [CompleteSpace 𝕜] in
lemma analyticAt_apply_comp {Φ : E' → Fin n → 𝕜} {y : E'} (hΦ : AnalyticAt 𝕜 Φ y) (j : Fin n) :
    AnalyticAt 𝕜 (fun z ↦ Φ z j) y :=
  (MvPowerSeries.analyticAt_apply j _).comp hΦ

/-- **Hadamard**: if the components of `Φ, Ψ : E' → 𝕜ⁿ` agree at `y ∈ Z(D')` modulo the ideal of
`D'`, then so do `H ∘ Φ` and `H ∘ Ψ`, for every `H` analytic at `Φ(y)`. -/
lemma classOf_comp_eq_of_sub_mem (D' : LocalModelData 𝕜 E') (y : D'.zeroSet)
    {Φ Ψ : E' → Fin n → 𝕜} (hΦ : AnalyticAt 𝕜 Φ y) (hΨ : AnalyticAt 𝕜 Ψ y)
    (h : ∀ j, germOf (fun z ↦ Φ z j - Ψ z j)
      ((analyticAt_apply_comp hΦ j).sub (analyticAt_apply_comp hΨ j)) ∈
        D'.ideal y (D'.mem_U y))
    {G : (Fin n → 𝕜) → 𝕜} (hG : AnalyticAt 𝕜 G (Φ y)) (hG' : AnalyticAt 𝕜 G (Ψ y)) :
    D'.classOf y (fun z ↦ G (Φ z)) (hG.comp hΦ) = D'.classOf y (fun z ↦ G (Ψ z)) (hG'.comp hΨ) := by
  rw [classOf, classOf, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  have hc : Ψ y = Φ y := by
    funext j
    have h₁ := (mem_maximalIdeal_stalk_iff _).mp (D'.ideal_le_maximalIdeal y (h j))
    rw [evalStalk_germOf, sub_eq_zero] at h₁
    exact h₁.symm
  set c : Fin n → 𝕜 := Φ y
  obtain ⟨H, hH, hGH⟩ := exists_hadamard G hG
  have hpair : AnalyticAt 𝕜 (fun z ↦ (Φ z, Ψ z)) y := hΦ.prod hΨ
  have hpair' : Tendsto (fun z ↦ (Φ z, Ψ z)) (𝓝 (y : E')) (𝓝 (c, c)) := by
    have := hpair.continuousAt.tendsto
    rwa [hc] at this
  have hHy : ∀ j, AnalyticAt 𝕜 (fun z ↦ H j (Φ z, Ψ z)) y := fun j ↦
    (hH j).comp_of_eq hpair (by rw [hc])
  have heq : germOf (fun z ↦ G (Φ z)) (hG.comp hΦ) - germOf (fun z ↦ G (Ψ z)) (hG'.comp hΨ) =
      ∑ j, germOf (fun z ↦ Φ z j - Ψ z j)
        ((analyticAt_apply_comp hΦ j).sub (analyticAt_apply_comp hΨ j)) *
        germOf _ (hHy j) := by
    have hev : (fun z ↦ G (Φ z)) - (fun z ↦ G (Ψ z)) =ᶠ[𝓝 (y : E')]
        fun z ↦ ∑ j, (Φ z j - Ψ z j) * H j (Φ z, Ψ z) := by
      filter_upwards [hpair'.eventually hGH] with z hz
      exact hz
    rw [← germOf_sub, germOf_congr _ hev,
      germOf_sum (g := fun j z ↦ (Φ z j - Ψ z j) * H j (Φ z, Ψ z))
        Finset.univ fun j ↦ ((analyticAt_apply_comp hΦ j).sub
          (analyticAt_apply_comp hΨ j)).mul (hHy j)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    exact germOf_mul _ _
  rw [heq]
  exact Submodule.sum_mem _ fun j _ ↦ Ideal.mul_mem_right _ _ (h j)

namespace AnalyticMap

variable {D' : LocalModelData 𝕜 E'} {D : LocalModelData 𝕜 (Fin n → 𝕜)}

lemma analyticAt_component (Φ : AnalyticMap D' D) (y : D'.zeroSet) (j : Fin n) :
    AnalyticAt 𝕜 (fun z ↦ Φ.toFun z j) y :=
  analyticAt_apply_comp (Φ.analyticAt y y.2) j

/-- **Morphisms into a local model depend only on the classes of the components.** If the
components of `Φ` and `Ψ` agree modulo the ideal of `D'`, the induced morphisms agree. -/
theorem toHom_eq_of_sub_mem (Φ Ψ : AnalyticMap D' D)
    (h : ∀ (y : D'.zeroSet) (j : Fin n),
      germOf (fun z ↦ Φ.toFun z j - Ψ.toFun z j)
        ((Φ.analyticAt_component y j).sub (Ψ.analyticAt_component y j)) ∈
          D'.ideal y (D'.mem_U y)) :
    Φ.toHom = Ψ.toHom := by
  have hpt : ∀ y : D'.zeroSet, Φ.pointMap y = Ψ.pointMap y := fun y ↦ by
    apply Subtype.ext
    funext j
    have h₁ := (mem_maximalIdeal_stalk_iff _).mp (D'.ideal_le_maximalIdeal y (h y j))
    rw [evalStalk_germOf, sub_eq_zero] at h₁
    exact h₁
  refine hom_ext hpt fun W s y hf hg ↦ ?_
  obtain ⟨V, hyV, G, hG, hsG⟩ := exists_classOf_eq s ⟨_, hf⟩
  have hyV' : Ψ.pointMap y ∈ V := by
    rw [← hpt y]
    exact hyV
  rw [toHom_c_app_apply, toHom_c_app_apply, hsG (Φ.pointMap y) hf hyV,
    hsG (Ψ.pointMap y) hg hyV', fiberMap_classOf, fiberMap_classOf]
  exact classOf_comp_eq_of_sub_mem D' y (Φ.analyticAt y y.2) (Ψ.analyticAt y y.2) (h y)
    (hG _ hyV) (hG _ hyV')

end AnalyticMap

end LocalModelData

/-! ### Polynomial maps between affine analytifications -/

section Polynomial

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n k n' k' : ℕ}

omit [CompleteSpace 𝕜] in
lemma eval_aeval_mvPolynomial (P : Fin n → MvPolynomial (Fin n') 𝕜) (p : MvPolynomial (Fin n) 𝕜)
    (z : Fin n' → 𝕜) :
    MvPolynomial.eval z (MvPolynomial.aeval P p) =
      MvPolynomial.eval (fun i ↦ MvPolynomial.eval z (P i)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The germ at a point of `Z(g')` of a polynomial of the ideal `(g')` lies in the ideal of the
local model. -/
lemma germOf_eval_mem_ideal (g' : Fin k' → MvPolynomial (Fin n') 𝕜)
    (y : (polynomialModel g').zeroSet) {q : MvPolynomial (Fin n') 𝕜}
    (hq : q ∈ Ideal.span (Set.range g')) :
    germOf (fun z ↦ MvPolynomial.eval z q) (analyticAt_eval_mvPolynomial q y) ∈
      (polynomialModel g').ideal y ((polynomialModel g').mem_U y) := by
  rw [ideal_eq_map g' y, ← polyGermHom_apply]
  exact Ideal.mem_map_of_mem _ hq

variable (g : Fin k → MvPolynomial (Fin n) 𝕜) (g' : Fin k' → MvPolynomial (Fin n') 𝕜)

/-- The analytic map `Z(g') → Z(g)` given by polynomials `P` sending the equations `g` into the
ideal `(g')`. -/
def polyAnalyticMap (P : Fin n → MvPolynomial (Fin n') 𝕜)
    (hP : ∀ i, MvPolynomial.aeval P (g i) ∈ Ideal.span (Set.range g')) :
    LocalModelData.AnalyticMap (polynomialModel g') (polynomialModel g) where
  toFun z i := MvPolynomial.eval z (P i)
  analyticAt y _ := AnalyticAt.pi fun i ↦ analyticAt_eval_mvPolynomial (P i) y
  mapsTo _ _ := trivial
  mem_ideal y i := by
    rw [stalkPullback_germOf]
    have e : (fun z ↦ (polynomialModel g).f i (fun j ↦ MvPolynomial.eval z (P j))) =
        fun z ↦ MvPolynomial.eval z (MvPolynomial.aeval P (g i)) := by
      funext z
      rw [eval_aeval_mvPolynomial]
      rfl
    rw [germOf_congr _ (Filter.EventuallyEq.of_eq e)]
    exact germOf_eval_mem_ideal g' y (hP i)

variable {g g'}

/-- Polynomials lifting the images `e(xᵢ)` of the coordinates under an algebra map
`e : 𝕜[x]/(g) → 𝕜[x']/(g')`. -/
def liftPoly (e : PresentedAlgebra g →ₐ[𝕜] PresentedAlgebra g') (i : Fin n) :
    MvPolynomial (Fin n') 𝕜 :=
  (Ideal.Quotient.mk_surjective (e (Ideal.Quotient.mk _ (MvPolynomial.X i)))).choose

omit [CompleteSpace 𝕜] in
lemma mk_liftPoly (e : PresentedAlgebra g →ₐ[𝕜] PresentedAlgebra g') (i : Fin n) :
    Ideal.Quotient.mk _ (liftPoly e i) = e (Ideal.Quotient.mk _ (MvPolynomial.X i)) :=
  (Ideal.Quotient.mk_surjective _).choose_spec

omit [CompleteSpace 𝕜] in
lemma mk_aeval_liftPoly (e : PresentedAlgebra g →ₐ[𝕜] PresentedAlgebra g')
    (p : MvPolynomial (Fin n) 𝕜) :
    Ideal.Quotient.mk _ (MvPolynomial.aeval (liftPoly e) p) = e (Ideal.Quotient.mk _ p) := by
  have : (Ideal.Quotient.mkₐ 𝕜 (Ideal.span (Set.range g'))).comp
      (MvPolynomial.aeval (liftPoly e)) = e.comp (Ideal.Quotient.mkₐ 𝕜 _) :=
    MvPolynomial.algHom_ext fun i ↦ by
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
      exact (Ideal.Quotient.mk_surjective _).choose_spec
  exact congr($this p)

omit [CompleteSpace 𝕜] in
lemma aeval_liftPoly_mem (e : PresentedAlgebra g →ₐ[𝕜] PresentedAlgebra g') (i : Fin k) :
    MvPolynomial.aeval (liftPoly e) (g i) ∈ Ideal.span (Set.range g') := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, mk_aeval_liftPoly]
  have h0 : Ideal.Quotient.mk (Ideal.span (Set.range g)) (g i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  rw [h0, map_zero]

variable (g g') in
/-- **XII.1.2 (affine case)**: an algebra homomorphism `e : A → A'` of finitely presented
algebras induces a morphism `Spec(A')^an → Spec(A)^an`, given by polynomials lifting `e`. -/
def analytificationMap (e : PresentedAlgebra g →ₐ[𝕜] PresentedAlgebra g') :
    analytification g' ⟶ analytification g :=
  (polyAnalyticMap g g' (liftPoly e) (aeval_liftPoly_mem e)).toHom

/-- The morphism does not depend on the choice of polynomials lifting `e`. -/
lemma polyAnalyticMap_toHom_eq (e : PresentedAlgebra g →ₐ[𝕜] PresentedAlgebra g')
    (P : Fin n → MvPolynomial (Fin n') 𝕜)
    (hP : ∀ i, Ideal.Quotient.mk _ (P i) = e (Ideal.Quotient.mk _ (MvPolynomial.X i)))
    (hPg : ∀ i, MvPolynomial.aeval P (g i) ∈ Ideal.span (Set.range g')) :
    (polyAnalyticMap g g' P hPg).toHom = analytificationMap g g' e := by
  refine LocalModelData.AnalyticMap.toHom_eq_of_sub_mem _ _ fun y j ↦ ?_
  have h : P j - liftPoly e j ∈ Ideal.span (Set.range g') := by
    rw [← Ideal.Quotient.eq, hP]
    exact (Ideal.Quotient.mk_surjective _).choose_spec.symm
  have e₁ : (fun z ↦ (polyAnalyticMap g g' P hPg).toFun z j -
      (polyAnalyticMap g g' (liftPoly e) (aeval_liftPoly_mem e)).toFun z j) =
      fun z ↦ MvPolynomial.eval z (P j - liftPoly e j) := by
    funext z
    simp [polyAnalyticMap]
  rw [germOf_congr _ (Filter.EventuallyEq.of_eq e₁)]
  exact germOf_eval_mem_ideal g' y h

variable (g) in
lemma analytificationMap_id : analytificationMap g g (AlgHom.id 𝕜 _) = 𝟙 _ := by
  have hX : ∀ i, MvPolynomial.aeval MvPolynomial.X (g i) ∈ Ideal.span (Set.range g) := fun i ↦ by
    rw [MvPolynomial.aeval_X_left_apply]
    exact Ideal.subset_span ⟨i, rfl⟩
  rw [← polyAnalyticMap_toHom_eq _ MvPolynomial.X (fun _ ↦ rfl) hX,
    ← LocalModelData.AnalyticMap.toHom_id]
  refine LocalModelData.AnalyticMap.toHom_eq_of_sub_mem _ _ fun y j ↦ ?_
  have e₁ : (fun z ↦ (polyAnalyticMap g g MvPolynomial.X hX).toFun z j -
      (LocalModelData.AnalyticMap.id (polynomialModel g)).toFun z j) = fun _ ↦ 0 := by
    funext z
    simp [polyAnalyticMap, LocalModelData.AnalyticMap.id]
  rw [germOf_congr _ (Filter.EventuallyEq.of_eq e₁), germOf_zero]
  exact zero_mem _

lemma analytificationMap_comp {n'' k'' : ℕ} {g'' : Fin k'' → MvPolynomial (Fin n'') 𝕜}
    (e₁ : PresentedAlgebra g →ₐ[𝕜] PresentedAlgebra g')
    (e₂ : PresentedAlgebra g' →ₐ[𝕜] PresentedAlgebra g'') :
    analytificationMap g g'' (e₂.comp e₁) =
      analytificationMap g' g'' e₂ ≫ analytificationMap g g' e₁ := by
  rw [analytificationMap, analytificationMap, analytificationMap,
    ← LocalModelData.AnalyticMap.toHom_comp]
  refine LocalModelData.AnalyticMap.toHom_eq_of_sub_mem _ _ fun y j ↦ ?_
  have h : liftPoly (e₂.comp e₁) j - MvPolynomial.aeval (liftPoly e₂) (liftPoly e₁ j) ∈
      Ideal.span (Set.range g'') := by
    rw [← Ideal.Quotient.eq, mk_aeval_liftPoly, mk_liftPoly, mk_liftPoly, AlgHom.comp_apply]
  have e₀ : (fun z ↦ (polyAnalyticMap g g'' (liftPoly (e₂.comp e₁))
      (aeval_liftPoly_mem _)).toFun z j -
      ((polyAnalyticMap g g' (liftPoly e₁) (aeval_liftPoly_mem e₁)).comp
        (polyAnalyticMap g' g'' (liftPoly e₂) (aeval_liftPoly_mem e₂))).toFun z j) =
      fun z ↦ MvPolynomial.eval z
        (liftPoly (e₂.comp e₁) j - MvPolynomial.aeval (liftPoly e₂) (liftPoly e₁ j)) := by
    funext z
    simp only [polyAnalyticMap, LocalModelData.AnalyticMap.comp, Function.comp_apply, map_sub,
      eval_aeval_mvPolynomial]
  rw [germOf_congr _ (Filter.EventuallyEq.of_eq e₀)]
  exact germOf_eval_mem_ideal g'' y h

/-- The pullback along `analytificationMap e` of the section defined by a polynomial `p` is the
section defined by `p ∘ P`. -/
lemma algebraToSections_comp_analytificationMap
    (e : PresentedAlgebra g →ₐ[𝕜] PresentedAlgebra g') :
    CommRingCat.ofHom (algebraToSections g) ≫
        LocallyRingedSpace.Γ.map (analytificationMap g g' e).op =
      CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom (algebraToSections g') := by
  refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun p ↦ ?_))
  change (analytificationMap g g' e).c.app (op ⊤) (polynomialSection p) =
    algebraToSections g' (e (Ideal.Quotient.mk _ p))
  rw [← mk_aeval_liftPoly, algebraToSections_mk]
  apply Subtype.ext
  funext y
  change (polyAnalyticMap g g' (liftPoly e) (aeval_liftPoly_mem e)).fiberMap y.1
    ((polynomialModel g).classOf _ (fun z ↦ MvPolynomial.eval z p) _) =
      (polynomialModel g').classOf y.1 _ _
  rw [LocalModelData.AnalyticMap.fiberMap_classOf]
  refine (polynomialModel g').classOf_congr _ (Filter.Eventually.of_forall fun z ↦ ?_)
  simp only [polyAnalyticMap, eval_aeval_mvPolynomial]

/-- **XII.1.2 (affine case)**: the square formed by `analytificationMap e`, `Spec e` and the
canonical morphisms `φ` commutes. -/
theorem analytificationMap_comp_toSpec (e : PresentedAlgebra g →ₐ[𝕜] PresentedAlgebra g') :
    analytificationMap g g' e ≫ toSpec g =
      toSpec g' ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom e.toRingHom) := by
  have nat : analytificationMap g g' e ≫ (analytification g).toΓSpec =
      (analytification g').toΓSpec ≫ Spec.locallyRingedSpaceMap
        (LocallyRingedSpace.Γ.map (analytificationMap g g' e).op) :=
    identityToΓSpec.naturality (analytificationMap g g' e)
  calc analytificationMap g g' e ≫ toSpec g
      = (analytificationMap g g' e ≫ (analytification g).toΓSpec) ≫
          Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraToSections g)) :=
        (Category.assoc _ _ _).symm
    _ = ((analytification g').toΓSpec ≫ Spec.locallyRingedSpaceMap
          (LocallyRingedSpace.Γ.map (analytificationMap g g' e).op)) ≫
          Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraToSections g)) :=
        congrArg (· ≫ _) nat
    _ = (analytification g').toΓSpec ≫ Spec.locallyRingedSpaceMap
          (CommRingCat.ofHom (algebraToSections g) ≫
            LocallyRingedSpace.Γ.map (analytificationMap g g' e).op) := by
        rw [Category.assoc, Spec.locallyRingedSpaceMap_comp]
        rfl
    _ = (analytification g').toΓSpec ≫ Spec.locallyRingedSpaceMap
          (CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom (algebraToSections g')) := by
        rw [algebraToSections_comp_analytificationMap]
        rfl
    _ = toSpec g' ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom e.toRingHom) := by
        rw [toSpec, Category.assoc]
        exact congrArg _ (Spec.locallyRingedSpaceMap_comp _ _)

/-- **Independence of the presentation**: isomorphic finitely presented algebras have isomorphic
analytifications. -/
def analytificationIso (e : PresentedAlgebra g ≃ₐ[𝕜] PresentedAlgebra g') :
    analytification g ≅ analytification g' where
  hom := analytificationMap g' g (e.symm : PresentedAlgebra g' →ₐ[𝕜] PresentedAlgebra g)
  inv := analytificationMap g g' (e : PresentedAlgebra g →ₐ[𝕜] PresentedAlgebra g')
  hom_inv_id := by
    rw [← analytificationMap_comp]
    convert analytificationMap_id g
    ext a
    simp
  inv_hom_id := by
    rw [← analytificationMap_comp]
    convert analytificationMap_id g'
    ext a
    simp

end Polynomial

end AnalyticGeometry
