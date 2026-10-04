/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.Analytic
import SGA.SGA1.ExposeXII.AnalyticAffine

/-!
# SGA 1, Exposé XII, 1.1: the reduced analytic space and `X^an`

For `A = 𝕜[x]/(g)` and `X = Spec A`, we compare the reduced analytic space `(X^an)_red` of
`Analytic.lean` (the space `X(𝕜)` with its sheaf of analytic functions) with the analytic space
`X^an` of `SGA.Foundations.Analytic` (the local model `Z(g)` with structure sheaf
`(𝒪/(g))|_{Z(g)}`):

* `reducedBase g : X(𝕜) ≃ₜ Z(g)` identifies the underlying spaces;
* `reducedComparison g : (X^an)_red ⟶ X^an` is the morphism of locally ringed spaces which is the
  identity on points and sends a section of `𝒪_{X^an}` to the function of its values;
* it is compatible with the canonical morphisms to `X` (`reducedComparison_comp_toSpec`).

For `𝕜 = ℂ`, `(X^an)_red` is the reduction of `X^an`: that the kernel of
`𝒪_{X^an, x} → 𝒪_{(X^an)_red, x}` is the nilradical is Rückert's Nullstellensatz, which is
formalized (`AffineAnalytification.rueckertNullstellensatz`, `ClosureComparison.lean`). The
identification of `(X^an)_red` with the reduction of `X^an` (stalk maps surjective, with kernel
the nilradical) is in `AnalyticGluingReduced.lean` (`surjective_stalkMap_reducedComparison`,
`ker_stalkMap_reducedComparison`).
-/

noncomputable section

open CategoryTheory Topology Set Opposite Filter AlgebraicGeometry AnalyticGeometry
open TopologicalSpace (Opens)

namespace SGA.SGA1.ExposeXII

namespace AffineAnalytification

open SchemePoints

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {n k : ℕ}
  (g : Fin k → MvPolynomial (Fin n) 𝕜)

attribute [local instance] SchemePoints.specOver SchemePoints.sectionsAlgebra

/-- `Γ(Spec A, ⊤) ≅ A`, as a `𝕜`-algebra isomorphism (the case `R = A` of
`SchemePoints.ΓSpecAlgEquiv`). -/
abbrev ΓSpecAlgEquiv : Γ(Spec (.of (PresentedAlgebra g)), ⊤) ≃ₐ[𝕜] PresentedAlgebra g :=
  SchemePoints.ΓSpecAlgEquiv (PresentedAlgebra g)

/-- The coordinate functions `xᵢ`, as global sections of `𝒪_{Spec A}`. -/
def coordSection (i : Fin n) : Γ(Spec (.of (PresentedAlgebra g)), ⊤) :=
  (ΓSpecAlgEquiv g).symm (Ideal.Quotient.mk _ (MvPolynomial.X i))

lemma homeomorphPoints_chart (φ : Points 𝕜 Γ(Spec (.of (PresentedAlgebra g)), ⊤)) :
    homeomorphPoints (chart (isAffineOpen_top _) φ) = φ :=
  homeomorphPoints.apply_symm_apply φ

/-- XII.1.1: the underlying space `Z(g)` of `Spec(A)^an` is the space of `𝕜`-points of `Spec A`. -/
def reducedBase : SchemePoints 𝕜 (Spec (.of (PresentedAlgebra g))) ≃ₜ (polynomialModel g).zeroSet :=
  homeomorphPoints.trans ((Points.homeomorph (ΓSpecAlgEquiv g)).symm.trans (pointsHomeomorph g))

lemma reducedBase_apply (p : SchemePoints 𝕜 (Spec (.of (PresentedAlgebra g)))) (i : Fin n) :
    (reducedBase g p : Fin n → 𝕜) i = eval (isAffineOpen_top _) (coordSection g i) p := by
  obtain ⟨φ, rfl⟩ := exists_chart_eq (isAffineOpen_top _) p trivial
  rw [eval_chart]
  simp only [reducedBase, Homeomorph.trans_apply, homeomorphPoints_chart]
  rfl

/-- The continuous map `X(𝕜) → Z(g)`. -/
def reducedBaseHom :
    TopCat.of (SchemePoints 𝕜 (Spec (.of (PresentedAlgebra g)))) ⟶
      TopCat.of (polynomialModel g).zeroSet :=
  TopCat.ofHom ⟨reducedBase g, (reducedBase g).continuous⟩

variable [CompleteSpace 𝕜]

/-- The values of a section of `𝒪_{X^an}` over `W`, as an analytic function on the corresponding
open subset of `X(𝕜)`. -/
def reducedSectionHom (W : Opens (TopCat.of (polynomialModel g).zeroSet)) :
    (polynomialModel g).presheaf.obj (op W) →+*
      analyticSubring 𝕜 (Spec (.of (PresentedAlgebra g)))
        ((Opens.map (reducedBaseHom g)).obj W) where
  toFun t := ⟨fun z ↦ (polynomialModel g).evalFiber _ (t.1 ⟨reducedBase g z.1, z.2⟩), fun z ↦ by
    obtain ⟨V, hqV, G, hG, htG⟩ := LocalModelData.exists_classOf_eq t ⟨reducedBase g z.1, z.2⟩
    have hfun (y : SchemePoints 𝕜 (Spec (.of (PresentedAlgebra g)))) :
        (fun i ↦ eval (isAffineOpen_top _) (coordSection g i) y) =
          ((reducedBase g y : (polynomialModel g).zeroSet) : Fin n → 𝕜) :=
      funext fun i ↦ (reducedBase_apply g y i).symm
    refine ⟨⊤, isAffineOpen_top _, trivial, n, coordSection g, G, ?_, ?_⟩
    · rw [hfun]
      exact hG _ hqV
    · have hopen : IsOpen ((reducedBase g) ⁻¹' ((W : Set _) ∩ V)) :=
        (W.2.inter V.2).preimage (reducedBase g).continuous
      filter_upwards [hopen.mem_nhds ⟨z.2, hqV⟩] with y hy
      rw [extend_of_mem _ hy.1, hfun]
      simp only
      rw [htG _ hy.1 hy.2, LocalModelData.evalFiber_classOf]⟩
  map_one' := Subtype.ext (funext fun _ ↦ map_one _)
  map_mul' _ _ := Subtype.ext (funext fun _ ↦ map_mul _ _ _)
  map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _)

/-- The comparison `(X^an)_red → X^an` as a morphism of ringed spaces: the identity on points
(`reducedBase`), and the evaluation of sections of `𝒪_{X^an}` as analytic functions. -/
def reducedComparisonHom :
    (SchemePoints.analytification 𝕜 (Spec (.of (PresentedAlgebra g)))).toPresheafedSpace.Hom
      (analytification g).toPresheafedSpace where
  base := reducedBaseHom g
  c :=
    { app W := CommRingCat.ofHom (reducedSectionHom g W.unop)
      naturality _ _ _ := rfl }

/-- XII.1.1: the canonical morphism `(X^an)_red → X^an` from the reduced analytic space of
`X = Spec A` (the sheaf of analytic functions on `X(𝕜)`) to the analytic space `Spec(A)^an`
(the local model `Z(g)` with structure sheaf `(𝒪/(g))|_{Z(g)}`): it is the identity on points and
sends a section to the function of its values. -/
def reducedComparison :
    SchemePoints.analytification 𝕜 (Spec (.of (PresentedAlgebra g))) ⟶ analytification g :=
  ⟨reducedComparisonHom g, fun y ↦ by
    refine ⟨fun t ht ↦ ?_⟩
    obtain ⟨W, hyW, s, rfl⟩ := (analytification g).presheaf.exists_germ_eq t
    rw [PresheafedSpace.stalkMap_germ_apply] at ht
    have h₁ := (isUnit_stalk_iff 𝕜 _ _).mp ht
    erw [evalHom_germ] at h₁
    have h₂ : IsUnit (s.1 ⟨reducedBase g y, hyW⟩) :=
      ((polynomialModel g).isUnit_fiber_iff _).mpr h₁
    have h₃ : (polynomialModel g).stalkIso (reducedBase g y)
        ((polynomialModel g).presheaf.germ W (reducedBase g y) hyW s) =
          s.1 ⟨reducedBase g y, hyW⟩ :=
      (polynomialModel g).stalkToFiber_germ W _ hyW s
    exact (MulEquiv.isUnit_map ((polynomialModel g).stalkIso _).toMulEquiv).mp (h₃ ▸ h₂)⟩

omit [CompleteSpace 𝕜] in
lemma ΓSpecIso_inv_eq (a : PresentedAlgebra g) :
    (Scheme.ΓSpecIso (.of (PresentedAlgebra g))).inv a = (ΓSpecAlgEquiv g).symm a := by
  rw [AlgEquiv.eq_symm_apply]
  exact (Scheme.ΓSpecIso (.of (PresentedAlgebra g))).inv_hom_id_apply a

omit [CompleteSpace 𝕜] in
lemma eval_reducedBase_eq_value (p : MvPolynomial (Fin n) 𝕜)
    (q : SchemePoints 𝕜 (Spec (.of (PresentedAlgebra g)))) :
    MvPolynomial.eval ((reducedBase g q : (polynomialModel g).zeroSet) : Fin n → 𝕜) p =
      value ((Scheme.ΓSpecIso (.of (PresentedAlgebra g))).inv (Ideal.Quotient.mk _ p)) q
        trivial := by
  obtain ⟨φ, rfl⟩ := exists_chart_eq (isAffineOpen_top _) q trivial
  have h := value_chart (isAffineOpen_top _) le_rfl
    ((Scheme.ΓSpecIso (.of (PresentedAlgebra g))).inv (Ideal.Quotient.mk _ p)) φ
  have hs : (homOfLE (le_rfl : (⊤ : (Spec (.of (PresentedAlgebra g))).Opens) ≤ ⊤)) = 𝟙 ⊤ :=
    Subsingleton.elim _ _
  rw [hs, op_id, CategoryTheory.Functor.map_id] at h
  erw [h]
  rw [← evalPoint_mk]
  simp only [reducedBase, Homeomorph.trans_apply, homeomorphPoints_chart,
    evalPoint_pointsHomeomorph]
  rw [CommRingCat.id_apply, ΓSpecIso_inv_eq]
  rfl

/-- XII.1.1: the comparison `(X^an)_red → X^an` is compatible with the canonical morphisms to `X`:
`φ ∘ (X^an)_red → X^an` is the canonical morphism of the reduced space. -/
theorem reducedComparison_comp_toSpec :
    reducedComparison g ≫ toSpec g = toSchemeHom 𝕜 (Spec (.of (PresentedAlgebra g))) := by
  let Y := SchemePoints.analytification 𝕜 (Spec (.of (PresentedAlgebra g)))
  let adj := ΓSpec.locallyRingedSpaceAdjunction
  let f₂ : Y ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of (PresentedAlgebra g)) :=
    toSchemeHom 𝕜 (Spec (.of (PresentedAlgebra g)))
  have h₂ : f₂ = adj.homEquiv Y _ ((adj.homEquiv Y _).symm f₂) :=
    ((adj.homEquiv Y _).apply_symm_apply f₂).symm
  change _ = f₂
  rw [LocalModelData.comp_toSpec, h₂]
  erw [← ΓSpec.locallyRingedSpaceAdjunction_homEquiv_apply']
  congr 1
  erw [Adjunction.homEquiv_counit]
  apply Quiver.Hom.unop_inj
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Subtype.ext
  funext z
  change (polynomialModel g).evalFiber _ ((polynomialSection p).1 ⟨reducedBase g z.1, trivial⟩) =
    value (X := Spec (.of (PresentedAlgebra g)))
      ((Scheme.ΓSpecIso (.of (PresentedAlgebra g))).inv (Ideal.Quotient.mk _ p)) z.1 trivial
  rw [polynomialSection_apply, LocalModelData.evalFiber_classOf]
  exact eval_reducedBase_eq_value g p z.1

@[simp] lemma reducedComparison_base_apply (y : SchemePoints 𝕜 (Spec (.of (PresentedAlgebra g)))) :
    (reducedComparison g).base y = reducedBase g y := rfl

end AffineAnalytification

end SGA.SGA1.ExposeXII
