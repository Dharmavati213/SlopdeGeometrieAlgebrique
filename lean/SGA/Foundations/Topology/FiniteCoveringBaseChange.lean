/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.FiniteCovering

/-!
# Base change of finite coverings along continuous maps

For a covering map `p : E → X` and a continuous map `f : Y → X`, the first projection of the fibre
product `Function.Pullback f p = {(y, e) | f y = p e}` is a covering map with the same fibres
(`IsCoveringMap.pullbackFst`, `Function.Pullback.fstPreimageEquiv`). This gives the base change
functor `TopCat.FiniteCovering.baseChange f : FiniteCovering X ⥤ FiniteCovering Y`.

## References

* [A. Hatcher, *Algebraic Topology*, §1.3][hatcher02] (pullback of a covering space)
-/

noncomputable section

universe u

open CategoryTheory Topology Set

section Pullback

variable {E X Y : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
  {p : E → X} {f : Y → X}

omit [TopologicalSpace X] in
@[fun_prop]
lemma Function.Pullback.continuous_fst : Continuous (Function.Pullback.fst : f.Pullback p → Y) :=
  (_root_.continuous_fst.comp continuous_subtype_val : Continuous fun q : f.Pullback p ↦ q.1.1)

omit [TopologicalSpace X] in
@[fun_prop]
lemma Function.Pullback.continuous_snd : Continuous (Function.Pullback.snd : f.Pullback p → E) :=
  (_root_.continuous_snd.comp continuous_subtype_val : Continuous fun q : f.Pullback p ↦ q.1.2)

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of an evenly covered neighbourhood: if `f y` is evenly covered by `p` with fibre
`I`, then `y` is evenly covered by the projection `Y ×_X E → Y` with fibre `I`. -/
theorem IsEvenlyCovered.pullbackFst (hf : Continuous f) {y : Y} {I : Type*}
    [TopologicalSpace I] (h : IsEvenlyCovered p (f y) I) :
    IsEvenlyCovered (Function.Pullback.fst : f.Pullback p → Y) y I := by
  obtain ⟨inst, U, hxU, hU, hpU, H, hH⟩ := h
  have hmem (q : f.Pullback p) (hq : f q.1.1 ∈ U) : q.1.2 ∈ p ⁻¹' U := by
    rw [mem_preimage, ← q.2]
    exact hq
  refine ⟨inst, f ⁻¹' U, hxU, hU.preimage hf, (hU.preimage hf).preimage (by fun_prop),
    { toFun q := (⟨q.1.1.1, q.2⟩, (H ⟨q.1.1.2, hmem q.1 q.2⟩).2)
      invFun yi := ⟨⟨(yi.1.1, H.symm (⟨f yi.1.1, yi.1.2⟩, yi.2)), by simp [← hH]⟩, yi.1.2⟩
      left_inv q := ?_
      right_inv yi := ?_
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }, fun _ ↦ rfl⟩
  · obtain ⟨⟨⟨y', e⟩, hq⟩, hy'⟩ := q
    have h1 : (H ⟨e, hmem _ hy'⟩).1 = ⟨f y', hy'⟩ := Subtype.ext (by rw [hH]; exact hq.symm)
    have h2 : H.symm (⟨f y', hy'⟩, (H ⟨e, hmem _ hy'⟩).2) = ⟨e, hmem _ hy'⟩ := by
      rw [← h1, Prod.mk.eta, Homeomorph.symm_apply_apply]
    ext
    · rfl
    · exact congrArg Subtype.val h2
  · obtain ⟨⟨y', hy'⟩, i⟩ := yi
    have h3 : H (H.symm (⟨f y', hy'⟩, i)) = (⟨f y', hy'⟩, i) := H.apply_symm_apply _
    refine Prod.ext rfl ?_
    change (H ⟨(H.symm (⟨f y', hy'⟩, i)).1, _⟩).2 = i
    rw [Subtype.coe_eta, h3]

/-- The pullback of a covering map along a continuous map is a covering map: the first projection
`Y ×_X E = {(y, e) | f y = p e} → Y`. -/
theorem IsCoveringMap.pullbackFst (hp : IsCoveringMap p) (hf : Continuous f) :
    IsCoveringMap (Function.Pullback.fst : f.Pullback p → Y) := fun y ↦
  ((hp (f y)).pullbackFst hf).to_isEvenlyCovered_preimage

/-- The fibre of the first projection of `Y ×_X E` over `y` is the fibre of `p` over `f y`. -/
def Function.Pullback.fstPreimageEquiv (p : E → X) (f : Y → X) (y : Y) :
    ((Function.Pullback.fst : f.Pullback p → Y) ⁻¹' {y}) ≃ (p ⁻¹' {f y}) where
  toFun q := ⟨q.1.1.2, by
    have h : q.1.1.1 = y := q.2
    simp only [mem_preimage, mem_singleton_iff, ← q.1.2, h]⟩
  invFun e := ⟨⟨(y, e.1), e.2.symm⟩, rfl⟩
  left_inv q := by
    obtain ⟨⟨⟨y', e⟩, hq⟩, hy'⟩ := q
    have h : y' = y := hy'
    subst h
    rfl
  right_inv _ := rfl

end Pullback

namespace TopCat.FiniteCovering

variable {X Y Z : TopCat.{u}}

/-- The pullback of a finite covering `p : E → X` along `f : Y → X`. -/
def baseChangeObj (f : Y ⟶ X) (E : FiniteCovering X) : FiniteCovering Y :=
  ⟨Over.mk (TopCat.ofHom ⟨fun q : (⇑f).Pullback E.obj.hom ↦ q.1.1, by fun_prop⟩),
    E.isCoveringMap.pullbackFst f.hom.continuous, fun y ↦ by
      have := (E.property.2 (f y)).to_subtype
      exact Set.finite_coe_iff.mp
        (Finite.of_equiv _ (Function.Pullback.fstPreimageEquiv E.obj.hom f y).symm)⟩

/-- Base change of finite coverings along a continuous map `f : Y → X`. -/
def baseChange (f : Y ⟶ X) : FiniteCovering X ⥤ FiniteCovering Y where
  obj E := baseChangeObj f E
  map {E F} g := ObjectProperty.homMk (Over.homMk (TopCat.ofHom
    ⟨fun q : (⇑f).Pullback E.obj.hom ↦ (⟨(q.1.1, g.hom.left q.1.2), by
        rw [q.2, hom_left_apply]⟩ : (⇑f).Pullback F.obj.hom), by fun_prop⟩))
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
lemma baseChange_obj_hom_apply (f : Y ⟶ X) (E : FiniteCovering X)
    (q : ((baseChange f).obj E).obj.left) : ((baseChange f).obj E).obj.hom q = q.1.1 := rfl

/-- A point of the pullback, from a point `y` and a point `e` of `E` with `f y = p e`. -/
def baseChangeMk (f : Y ⟶ X) (E : FiniteCovering X) (y : Y) (e : E.obj.left)
    (h : f y = E.obj.hom e) : ((baseChange f).obj E).obj.left :=
  (⟨(y, e), h⟩ : (⇑f).Pullback E.obj.hom)

/-- The projection of the pullback to the total space of `E`. -/
def baseChangeSnd (f : Y ⟶ X) (E : FiniteCovering X) :
    ((baseChange f).obj E).obj.left ⟶ E.obj.left :=
  TopCat.ofHom ⟨fun q : (⇑f).Pullback E.obj.hom ↦ q.1.2, by fun_prop⟩

lemma baseChangeSnd_apply (f : Y ⟶ X) (E : FiniteCovering X)
    (q : ((baseChange f).obj E).obj.left) :
    baseChangeSnd f E q = (q : (⇑f).Pullback E.obj.hom).1.2 := rfl

lemma hom_baseChangeSnd (f : Y ⟶ X) (E : FiniteCovering X)
    (q : ((baseChange f).obj E).obj.left) :
    E.obj.hom (baseChangeSnd f E q) = f (((baseChange f).obj E).obj.hom q) :=
  (q : (⇑f).Pullback E.obj.hom).2.symm

@[simp]
lemma hom_baseChangeMk (f : Y ⟶ X) (E : FiniteCovering X) (y : Y) (e : E.obj.left)
    (h : f y = E.obj.hom e) : ((baseChange f).obj E).obj.hom (baseChangeMk f E y e h) = y := rfl

@[simp]
lemma baseChangeSnd_baseChangeMk (f : Y ⟶ X) (E : FiniteCovering X) (y : Y) (e : E.obj.left)
    (h : f y = E.obj.hom e) : baseChangeSnd f E (baseChangeMk f E y e h) = e := rfl

/-- Two points of the pullback are equal if they have the same images in `Y` and in `E`. -/
lemma baseChange_ext {f : Y ⟶ X} {E : FiniteCovering X} {q q' : ((baseChange f).obj E).obj.left}
    (h₁ : ((baseChange f).obj E).obj.hom q = ((baseChange f).obj E).obj.hom q')
    (h₂ : baseChangeSnd f E q = baseChangeSnd f E q') : q = q' :=
  Subtype.ext (Prod.ext h₁ h₂)

lemma eq_baseChangeMk (f : Y ⟶ X) (E : FiniteCovering X) (q : ((baseChange f).obj E).obj.left) :
    q = baseChangeMk f E (((baseChange f).obj E).obj.hom q) (baseChangeSnd f E q)
      (hom_baseChangeSnd f E q).symm :=
  rfl

end TopCat.FiniteCovering
