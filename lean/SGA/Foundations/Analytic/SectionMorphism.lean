/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Presentation

/-!
# Morphisms into local models defined by sections

Let `Z(D') ⊆ E'` and `Z(D) ⊆ 𝕜ⁿ` be local models. Global sections `s₁, …, sₙ` of `𝒪_{Z(D')}`
which "satisfy the equations of `D`" define a morphism of locally ringed spaces
`Z(D') → Z(D)` (`SectionData.toHom`): near each point `y`, lift the germs `sᵢ(y)` to analytic
functions `Ψᵢ` on `E'`; the point `y` is sent to `(Ψᵢ(y))ᵢ = (sᵢ(y)(y))ᵢ`, and the class of a germ
`G` at the image point is sent to the class of `G ∘ Ψ`. By Hadamard's lemma
(`classOf_comp_eq_of_sub_mem`) this does not depend on the chosen lifts
(`SectionData.fiberMap_classOf_eq`), which makes the construction local on `Z(D')` even though the
sections need not lift globally to `E'`.

Together with `LocalModelData.eq_of_coordPullback` this gives the universal property of local
models in `𝕜ⁿ` (`SGA/Foundations/Analytic/UniversalProperty.lean`).
-/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Filter Topology IsLocalRing

namespace AnalyticGeometry

namespace LocalModelData

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E' : Type} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {n : ℕ}

/-! ### Constants -/

section Constants

variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (D : LocalModelData 𝕜 E)

/-- The constant functions, in the stalks of a local model. -/
def constFiber (x : D.zeroSet) : 𝕜 →+* D.Fiber x where
  toFun c := D.classOf x (fun _ ↦ c) analyticAt_const
  map_one' := D.classOf_one x
  map_mul' a b := (D.classOf_mul (x := x) (g := fun _ ↦ a) (h := fun _ ↦ b) analyticAt_const
    analyticAt_const)
  map_zero' := D.classOf_zero x
  map_add' a b := (D.classOf_add (x := x) (g := fun _ ↦ a) (h := fun _ ↦ b) analyticAt_const
    analyticAt_const)

lemma constFiber_apply (x : D.zeroSet) (c : 𝕜) :
    D.constFiber x c = D.classOf x (fun _ ↦ c) analyticAt_const := rfl

/-- The constant sections of a local model. -/
def constSection (W : Opens (TopCat.of D.zeroSet)) (c : 𝕜) : D.presheaf.obj (op W) :=
  D.classSectionOn (fun _ ↦ c) W fun _ _ ↦ analyticAt_const

@[simp] lemma constSection_apply (W : Opens (TopCat.of D.zeroSet)) (c : 𝕜) (y : W) :
    (D.constSection W c).1 y = D.constFiber y c := rfl

/-- The constant sections, as a ring homomorphism `𝕜 → Γ(W, 𝒪_Z)`. -/
def constSectionHom (W : Opens (TopCat.of D.zeroSet)) : 𝕜 →+* D.presheaf.obj (op W) where
  toFun := D.constSection W
  map_one' := Subtype.ext (funext fun y ↦ map_one (D.constFiber y))
  map_mul' a b := Subtype.ext (funext fun y ↦ map_mul (D.constFiber y) a b)
  map_zero' := Subtype.ext (funext fun y ↦ map_zero (D.constFiber y))
  map_add' a b := Subtype.ext (funext fun y ↦ map_add (D.constFiber y) a b)

@[simp] lemma constSectionHom_apply (W : Opens (TopCat.of D.zeroSet)) (c : 𝕜) :
    D.constSectionHom W c = D.constSection W c := rfl

/-- The value at a point of a polynomial expression in sections. -/
lemma eval₂Hom_constSectionHom_apply {n : ℕ} {W : Opens (TopCat.of D.zeroSet)}
    (s : Fin n → D.presheaf.obj (op W)) (p : MvPolynomial (Fin n) 𝕜) (y : W) :
    (MvPolynomial.eval₂Hom (D.constSectionHom W) s p).1 y =
      MvPolynomial.eval₂ (D.constFiber y) (fun i ↦ (s i).1 y) p := by
  have : (D.evalAt y ⟨W, y.2⟩).hom.comp (MvPolynomial.eval₂Hom (D.constSectionHom W) s) =
      MvPolynomial.eval₂Hom (D.constFiber y) (fun i ↦ (s i).1 y) :=
    MvPolynomial.ringHom_ext
      (fun c ↦ by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]; rfl)
      (fun i ↦ by rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']; rfl)
  exact congr($this p)

lemma sub_constFiber_mem_maximalIdeal (x : D.zeroSet) (t : D.Fiber x) :
    t - D.constFiber x (D.evalFiber x t) ∈ maximalIdeal (D.Fiber x) := by
  rw [mem_maximalIdeal_fiber_iff, map_sub, sub_eq_zero]
  exact (D.evalFiber_classOf x (fun _ ↦ D.evalFiber x t) analyticAt_const).symm

end Constants

/-! ### Chosen representatives -/

section Representatives

variable (D' : LocalModelData 𝕜 E')

/-- A chosen analytic function representing an element of `𝒪_{Z,y} = 𝒪_{E,y}/(f)`. -/
def rep (y : D'.zeroSet) (t : D'.Fiber y) : E' → 𝕜 :=
  (D'.classOf_surjective y t).choose

lemma analyticAt_rep (y : D'.zeroSet) (t : D'.Fiber y) :
    AnalyticAt 𝕜 (D'.rep y t) (y : E') :=
  (D'.classOf_surjective y t).choose_spec.choose

@[simp] lemma classOf_rep (y : D'.zeroSet) (t : D'.Fiber y) :
    D'.classOf y (D'.rep y t) (D'.analyticAt_rep y t) = t :=
  (D'.classOf_surjective y t).choose_spec.choose_spec

lemma rep_apply_self (y : D'.zeroSet) (t : D'.Fiber y) :
    D'.rep y t y = D'.evalFiber y t := by
  conv_rhs => rw [← D'.classOf_rep y t]
  rw [evalFiber_classOf]

/-- Chosen analytic representatives `E' → 𝕜ⁿ` of a family of elements of `𝒪_{Z,y}`. -/
def repVec (y : D'.zeroSet) (c : Fin n → D'.Fiber y) : E' → Fin n → 𝕜 :=
  fun z i ↦ D'.rep y (c i) z

lemma analyticAt_repVec (y : D'.zeroSet) (c : Fin n → D'.Fiber y) :
    AnalyticAt 𝕜 (D'.repVec y c) (y : E') :=
  AnalyticAt.pi fun i ↦ D'.analyticAt_rep y (c i)

lemma repVec_apply_self (y : D'.zeroSet) (c : Fin n → D'.Fiber y) (i : Fin n) :
    D'.repVec y c y i = D'.evalFiber y (c i) :=
  D'.rep_apply_self y (c i)

lemma classOf_repVec (y : D'.zeroSet) (c : Fin n → D'.Fiber y) (i : Fin n) :
    D'.classOf y (fun z ↦ D'.repVec y c z i) (analyticAt_apply_comp (D'.analyticAt_repVec y c) i) =
      c i :=
  D'.classOf_rep y (c i)

/-- **Substitution does not depend on the lifts**: if the components of `Φ, Ψ : E' → 𝕜ⁿ` have the
same classes in `𝒪_{Z,y}`, then so do `G ∘ Φ` and `G ∘ Ψ` (Hadamard's lemma). -/
lemma classOf_comp_eq_of_classOf_eq {y : D'.zeroSet} {Φ Ψ : E' → Fin n → 𝕜}
    (hΦ : AnalyticAt 𝕜 Φ (y : E')) (hΨ : AnalyticAt 𝕜 Ψ (y : E'))
    (h : ∀ j, D'.classOf y (fun z ↦ Φ z j) (analyticAt_apply_comp hΦ j) =
      D'.classOf y (fun z ↦ Ψ z j) (analyticAt_apply_comp hΨ j))
    {G : (Fin n → 𝕜) → 𝕜} (hG : AnalyticAt 𝕜 G (Φ y)) (hG' : AnalyticAt 𝕜 G (Ψ y)) :
    D'.classOf y (fun z ↦ G (Φ z)) (hG.comp hΦ) =
      D'.classOf y (fun z ↦ G (Ψ z)) (hG'.comp hΨ) := by
  refine classOf_comp_eq_of_sub_mem D' y hΦ hΨ (fun j ↦ ?_) hG hG'
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h₁ := germOf_sub (analyticAt_apply_comp hΦ j) (analyticAt_apply_comp hΨ j)
  change Ideal.Quotient.mk _ (germOf ((fun z ↦ Φ z j) - fun z ↦ Ψ z j) _) = 0
  rw [h₁, map_sub, sub_eq_zero]
  exact h j

/-- The class of `p ∘ Ψ`, for a polynomial `p`, is `p` evaluated at the classes of the
components of `Ψ`. -/
lemma classOf_eval_comp {y : D'.zeroSet} {Ψ : E' → Fin n → 𝕜} (hΨ : AnalyticAt 𝕜 Ψ (y : E'))
    (p : MvPolynomial (Fin n) 𝕜) :
    D'.classOf y (fun z ↦ MvPolynomial.eval (Ψ z) p)
        ((analyticAt_eval_mvPolynomial p (Ψ y)).comp hΨ) =
      MvPolynomial.eval₂ (D'.constFiber y)
        (fun i ↦ D'.classOf y (fun z ↦ Ψ z i) (analyticAt_apply_comp hΨ i)) p := by
  have key : ((Ideal.Quotient.mk (D'.ideal y (D'.mem_U y))).comp
      ((stalkPullback Ψ hΨ).comp (polyGermHom (Ψ y)))) =
      MvPolynomial.eval₂Hom (D'.constFiber y)
        (fun i ↦ D'.classOf y (fun z ↦ Ψ z i) (analyticAt_apply_comp hΨ i)) := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, RingHom.comp_apply, polyGermHom_apply,
        stalkPullback_germOf]
      exact D'.classOf_congr _ (Eventually.of_forall fun z ↦ by simp)
    · rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, RingHom.comp_apply, polyGermHom_apply,
        stalkPullback_germOf]
      exact D'.classOf_congr _ (Eventually.of_forall fun z ↦ by simp)
  have := congr($key p)
  rw [RingHom.comp_apply, RingHom.comp_apply, polyGermHom_apply, stalkPullback_germOf] at this
  exact this

/-- The values of a section of `𝒪_Z` define a continuous function on `Z`. -/
lemma continuous_evalFiber_section {W : Opens (TopCat.of D'.zeroSet)} (t : D'.presheaf.obj (op W)) :
    Continuous fun y : W ↦ D'.evalFiber y (t.1 y) := by
  rw [continuous_iff_continuousAt]
  intro y
  obtain ⟨V, hyV, G, hG, htG⟩ := exists_classOf_eq t y
  have hV : IsOpen ((↑) ⁻¹' (V : Set D'.zeroSet) : Set W) := V.2.preimage continuous_subtype_val
  have hev : (fun y' : W ↦ G y') =ᶠ[𝓝 y] fun y' ↦ D'.evalFiber y' (t.1 y') := by
    filter_upwards [hV.mem_nhds hyV] with y' hy'
    rw [htG y' y'.2 hy', evalFiber_classOf]
  have hc : ContinuousAt (fun y' : W ↦ G ((y' : D'.zeroSet) : E')) y :=
    ContinuousAt.comp (g := G) (f := fun y' : W ↦ ((y' : D'.zeroSet) : E'))
      (hG y hyV).continuousAt (continuous_subtype_val.comp continuous_subtype_val).continuousAt
  exact hc.congr hev

end Representatives

/-! ### Morphisms defined by sections -/

variable (D' : LocalModelData 𝕜 E') (D : LocalModelData 𝕜 (Fin n → 𝕜))

/-- The data of a morphism `Z(D') → Z(D) ⊆ 𝕜ⁿ`: global sections `s₁, …, sₙ` of `𝒪_{Z(D')}` (the
pullbacks of the coordinates), whose values lie in the domain `U` of `D`, and which satisfy the
equations of `D`: at every point `y`, `f_j ∘ Ψ` vanishes in `𝒪_{Z(D'),y}` for (chosen) lifts `Ψ`
of the germs `sᵢ(y)`. -/
@[ext]
structure SectionData where
  /-- The sections `sᵢ`. -/
  sec : Fin n → D'.presheaf.obj (op ⊤)
  mapsTo : ∀ y : D'.zeroSet, (fun i ↦ D'.evalFiber y ((sec i).1 ⟨y, trivial⟩)) ∈ D.U
  classOf_f : ∀ (y : D'.zeroSet) (j : Fin D.k)
    (hj : AnalyticAt 𝕜 (D.f j) (D'.repVec y (fun i ↦ (sec i).1 ⟨y, trivial⟩) y)),
    D'.classOf y (fun z ↦ D.f j (D'.repVec y (fun i ↦ (sec i).1 ⟨y, trivial⟩) z))
      (hj.comp (D'.analyticAt_repVec y _)) = 0

namespace SectionData

variable {D' D} (S : SectionData D' D)

/-- The germs `sᵢ(y)`. -/
def vals (y : D'.zeroSet) (i : Fin n) : D'.Fiber y := (S.sec i).1 ⟨y, trivial⟩

/-- The chosen lift near `y` of the germs `sᵢ(y)`. -/
def lift (y : D'.zeroSet) : E' → Fin n → 𝕜 := D'.repVec y (S.vals y)

lemma analyticAt_lift (y : D'.zeroSet) : AnalyticAt 𝕜 (S.lift y) (y : E') :=
  D'.analyticAt_repVec y _

lemma lift_apply_self (y : D'.zeroSet) (i : Fin n) :
    S.lift y y i = D'.evalFiber y (S.vals y i) :=
  D'.repVec_apply_self y _ i

lemma lift_self_mem_U (y : D'.zeroSet) : S.lift y y ∈ D.U := by
  convert S.mapsTo y using 1
  funext i
  exact S.lift_apply_self y i

lemma analyticAt_f (y : D'.zeroSet) (j : Fin D.k) : AnalyticAt 𝕜 (D.f j) (S.lift y y) :=
  D.analyticAt_f j _ (S.lift_self_mem_U y)

lemma lift_self_mem_zeroSet (y : D'.zeroSet) : S.lift y y ∈ D.zeroSet := by
  refine ⟨S.lift_self_mem_U y, fun j ↦ ?_⟩
  have h := congrArg (D'.evalFiber y) (S.classOf_f y j (S.analyticAt_f y j))
  rwa [evalFiber_classOf, map_zero] at h

/-- The map on points: `y ↦ (sᵢ(y)(y))ᵢ`. -/
abbrev pointMap (y : D'.zeroSet) : D.zeroSet := ⟨S.lift y y, S.lift_self_mem_zeroSet y⟩

lemma pointMap_apply (y : D'.zeroSet) (i : Fin n) :
    (S.pointMap y : Fin n → 𝕜) i = D'.evalFiber y ((S.sec i).1 ⟨y, trivial⟩) :=
  S.lift_apply_self y i

lemma continuous_pointMap : Continuous S.pointMap := by
  refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
  have h := D'.continuous_evalFiber_section (S.sec i)
  have h₂ : Continuous fun y : D'.zeroSet ↦ D'.evalFiber y ((S.sec i).1 ⟨y, trivial⟩) :=
    h.comp (f := fun y : D'.zeroSet ↦ (⟨y, trivial⟩ : (⊤ : Opens (TopCat.of D'.zeroSet))))
      (continuous_id.subtype_mk _)
  exact h₂.congr fun y ↦ (S.lift_apply_self y i).symm

/-- The map on points, as a morphism of topological spaces. -/
def base : TopCat.of D'.zeroSet ⟶ TopCat.of D.zeroSet :=
  TopCat.ofHom ⟨S.pointMap, S.continuous_pointMap⟩

/-- Substitution of the germs `sᵢ(y)`: `𝒪_{Z(D),f(y)} → 𝒪_{Z(D'),y}`, `[G] ↦ [G ∘ Ψ]`. -/
def fiberMap (y : D'.zeroSet) : D.Fiber (S.pointMap y) →+* D'.Fiber y :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (stalkPullback (S.lift y) (S.analyticAt_lift y))) fun a ha ↦ by
      have : D.ideal (S.pointMap y) (D.mem_U _) ≤ RingHom.ker
          ((Ideal.Quotient.mk (D'.ideal y (D'.mem_U y))).comp
            (stalkPullback (S.lift y) (S.analyticAt_lift y))) := by
        refine Ideal.span_le.mpr ?_
        rintro _ ⟨j, rfl⟩
        refine RingHom.mem_ker.mpr ((congrArg (Ideal.Quotient.mk _) (stalkPullback_germOf
          (S.lift y) (S.analyticAt_lift y) (D.f j) (S.analyticAt_f y j))).trans ?_)
        exact S.classOf_f y j (S.analyticAt_f y j)
      exact RingHom.mem_ker.mp (this ha)

lemma fiberMap_classOf (y : D'.zeroSet) (G : (Fin n → 𝕜) → 𝕜)
    (hG : AnalyticAt 𝕜 G (S.pointMap y : Fin n → 𝕜)) :
    S.fiberMap y (D.classOf (S.pointMap y) G hG) =
      D'.classOf y (fun z ↦ G (S.lift y z))
        (AnalyticAt.comp (g := G) (f := S.lift y) hG (S.analyticAt_lift y)) := by
  rw [fiberMap, classOf, Ideal.Quotient.lift_mk, RingHom.comp_apply, stalkPullback_germOf]
  rfl

/-- The substitution does not depend on the lifts of the germs `sᵢ(y)`. -/
lemma fiberMap_classOf_eq {y : D'.zeroSet} {Ψ : E' → Fin n → 𝕜} (hΨ : AnalyticAt 𝕜 Ψ (y : E'))
    (hΨs : ∀ i, D'.classOf y (fun z ↦ Ψ z i) (analyticAt_apply_comp hΨ i) =
      (S.sec i).1 ⟨y, trivial⟩)
    (G : (Fin n → 𝕜) → 𝕜) (hG : AnalyticAt 𝕜 G (S.pointMap y : Fin n → 𝕜))
    (hG' : AnalyticAt 𝕜 G (Ψ y)) :
    S.fiberMap y (D.classOf (S.pointMap y) G hG) =
      D'.classOf y (fun z ↦ G (Ψ z)) (hG'.comp hΨ) := by
  rw [fiberMap_classOf]
  refine D'.classOf_comp_eq_of_classOf_eq (S.analyticAt_lift y) hΨ (fun j ↦ ?_) hG hG'
  rw [hΨs]
  exact D'.classOf_repVec y _ j

lemma evalFiber_fiberMap (y : D'.zeroSet) (t : D.Fiber (S.pointMap y)) :
    D'.evalFiber y (S.fiberMap y t) = D.evalFiber (S.pointMap y) t := by
  obtain ⟨G, hG, rfl⟩ := D.classOf_surjective _ t
  rw [fiberMap_classOf, evalFiber_classOf, evalFiber_classOf]

instance isLocalHom_fiberMap (y : D'.zeroSet) : IsLocalHom (S.fiberMap y) := by
  refine ⟨fun t ht ↦ ?_⟩
  rw [isUnit_fiber_iff] at ht ⊢
  rwa [evalFiber_fiberMap] at ht

lemma fiberMap_constFiber (y : D'.zeroSet) (c : 𝕜) :
    S.fiberMap y (D.constFiber (S.pointMap y) c) = D'.constFiber y c :=
  S.fiberMap_classOf y _ analyticAt_const

/-- The pullback of a section is a section. -/
lemma localPredicate_pullback (W : Opens (TopCat.of D.zeroSet)) (s : D.presheaf.obj (op W)) :
    D'.localPredicate.pred (X := TopCat.of D'.zeroSet)
      (U := (Opens.map S.base).obj W)
      (fun y ↦ S.fiberMap y.1 (s.1 ⟨S.pointMap y.1, y.2⟩)) := by
  intro y
  obtain ⟨V, hxV, G, hG, hsG⟩ := exists_classOf_eq s ⟨S.pointMap y.1, y.2⟩
  choose V' hyV' Ψ hΨ hΨs using fun i ↦ exists_classOf_eq (S.sec i) ⟨y.1, trivial⟩
  let N : Opens (TopCat.of D'.zeroSet) :=
    ⟨(⋂ i, (V' i : Set D'.zeroSet)) ∩ S.pointMap ⁻¹' (V : Set D.zeroSet),
      (isOpen_iInter_of_finite fun i ↦ (V' i).2).inter (V.2.preimage S.continuous_pointMap)⟩
  have hN : ∀ q ∈ N, ∀ i, q ∈ V' i := fun q hq i ↦ Set.mem_iInter.mp hq.1 i
  let Ψv : E' → Fin n → 𝕜 := fun z i ↦ Ψ i z
  have hΨv : ∀ q ∈ N, AnalyticAt 𝕜 Ψv ((q : D'.zeroSet) : E') := fun q hq ↦
    AnalyticAt.pi fun i ↦ hΨ i q (hN q hq i)
  have hΨvs : ∀ (q : D'.zeroSet) (hq : q ∈ N) (i : Fin n),
      D'.classOf q (fun z ↦ Ψv z i) (analyticAt_apply_comp (hΨv q hq) i) =
        (S.sec i).1 ⟨q, trivial⟩ := fun q hq i ↦ (hΨs i q trivial (hN q hq i)).symm
  have hpt : ∀ (q : D'.zeroSet) (hq : q ∈ N), Ψv q = S.pointMap q := fun q hq ↦ by
    funext i
    rw [pointMap_apply, ← hΨvs q hq i, evalFiber_classOf]
  have hGΨ : ∀ (q : D'.zeroSet) (hq : q ∈ N), AnalyticAt 𝕜 (fun z ↦ G (Ψv z)) (q : E') :=
    fun q hq ↦ (hG _ hq.2).comp_of_eq (hΨv q hq) (hpt q hq)
  refine ⟨N ⊓ (Opens.map S.base).obj W, ⟨⟨Set.mem_iInter.mpr hyV', hxV⟩, y.2⟩,
    homOfLE inf_le_right, fun z ↦ G (Ψv z), fun q ↦ hGΨ q.1 q.2.1, fun q ↦ ?_⟩
  have h₁ := hsG (S.pointMap q.1) q.2.2 q.2.1.2
  dsimp only
  change S.fiberMap q.1 (s.1 ⟨S.pointMap q.1, q.2.2⟩) = _
  rw [h₁]
  have hG' : AnalyticAt 𝕜 G (Ψv q.1) := by rw [hpt q.1 q.2.1]; exact hG _ q.2.1.2
  exact S.fiberMap_classOf_eq (hΨv q.1 q.2.1) (hΨvs q.1 q.2.1) G _ hG'

/-- The pullback of sections along the morphism defined by `S`. -/
def sectionMap (W : Opens (TopCat.of D.zeroSet)) :
    D.presheaf.obj (op W) ⟶ D'.presheaf.obj (op ((Opens.map S.base).obj W)) :=
  CommRingCat.ofHom
    { toFun s := ⟨fun y ↦ S.fiberMap y.1 (s.1 ⟨S.pointMap y.1, y.2⟩),
        S.localPredicate_pullback W s⟩
      map_one' := Subtype.ext (funext fun _ ↦ map_one _)
      map_mul' _ _ := Subtype.ext (funext fun _ ↦ map_mul _ _ _)
      map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
      map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _) }

/-- The morphism of ringed spaces `Z(D') → Z(D)` defined by `S`. -/
def toPresheafedSpaceHom :
    D'.toLocallyRingedSpace.toPresheafedSpace.Hom D.toLocallyRingedSpace.toPresheafedSpace where
  base := S.base
  c :=
    { app W := S.sectionMap W.unop
      naturality _ _ _ := rfl }

lemma stalkToFiber_stalkMap (y : D'.zeroSet) (t : D.presheaf.stalk (S.pointMap y)) :
    D'.stalkToFiber y (S.toPresheafedSpaceHom.stalkMap y t) =
      S.fiberMap y (D.stalkToFiber (S.pointMap y) t) := by
  obtain ⟨W, hW, s, rfl⟩ := D.presheaf.exists_germ_eq t
  erw [AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply]
  rw [stalkToFiber_germ]
  exact D'.stalkToFiber_germ _ y hW _

/-- **The morphism of local models defined by sections**: `n` sections of `𝒪_{Z(D')}` satisfying
the equations of `D ⊆ 𝕜ⁿ` define a morphism of locally ringed spaces `Z(D') → Z(D)`. -/
def toHom : D'.toLocallyRingedSpace ⟶ D.toLocallyRingedSpace :=
  ⟨S.toPresheafedSpaceHom, fun y ↦ by
    refine ⟨fun t ht ↦ ?_⟩
    have h₁ : IsUnit (D'.stalkToFiber y (S.toPresheafedSpaceHom.stalkMap y t)) :=
      ht.map (D'.stalkToFiber y).hom
    have h₁' : IsUnit (S.fiberMap y (D.stalkToFiber (S.pointMap y) t)) := by
      convert h₁ using 1
      exact (S.stalkToFiber_stalkMap y t).symm
    have h₂ : IsUnit (D.stalkToFiber (S.pointMap y) t) :=
      (S.isLocalHom_fiberMap y).map_nonunit _ h₁'
    exact (MulEquiv.isUnit_map (D.stalkIso (S.pointMap y)).toMulEquiv).mp h₂⟩

@[simp] lemma toHom_base_apply (y : D'.zeroSet) : S.toHom.base y = S.pointMap y := rfl

lemma toHom_c_app_apply (W : Opens (TopCat.of D.zeroSet)) (s : D.presheaf.obj (op W))
    (y : D'.zeroSet) (hy : S.toHom.base y ∈ W) :
    (S.toHom.c.app (op W) s).1 ⟨y, hy⟩ = S.fiberMap y (s.1 ⟨S.pointMap y, hy⟩) := rfl

end SectionData

end LocalModelData

end AnalyticGeometry
