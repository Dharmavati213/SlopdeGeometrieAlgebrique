/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.LocalModel
import Mathlib.Analysis.Analytic.Composition

/-!
# Morphisms of local models induced by analytic maps

Let `D = (U, f)` be a local model in `E` and `D' = (U', f')` a local model in `E'`. An analytic map
`Φ : E' → E`, defined near `Z' = Z(f')`, with `Φ(Z') ⊆ U` and such that the germs of `fᵢ ∘ Φ` lie in
the ideal `(f')`, induces a morphism of locally ringed spaces `Z' → Z`: on points it is `Φ`, and it
pulls back the class of an analytic function `G` to the class of `G ∘ Φ`
(`LocalModelData.AnalyticMap.toHom`; [Grauert–Remmert, *Coherent analytic sheaves*, §1.1]).

## Main definitions

* `AnalyticGeometry.stalkPullback`: `𝒪_{E,Φ(y)} → 𝒪_{E',y}`, `[G] ↦ [G ∘ Φ]`.
* `AnalyticGeometry.LocalModelData.AnalyticMap D' D`: analytic maps between the ambient spaces
  compatible with the equations.
* `AnalyticGeometry.LocalModelData.AnalyticMap.toHom`: the induced morphism of locally ringed
  spaces.
-/

universe u

noncomputable section

open CategoryTheory Topology TopologicalSpace Opposite Filter CategoryTheory.Limits

namespace AnalyticGeometry

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E E' : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E']
  [NormedSpace 𝕜 E']

/-! ### Pullback of germs -/

section Pullback

variable (Φ : E' → E) {y : E'} (hΦ : AnalyticAt 𝕜 Φ y) {y' : E}

/-- A representative of a germ. -/
def germRep {x : E} (t : (analyticPresheaf 𝕜 E).stalk x) : E → 𝕜 :=
  (exists_germOf_eq t).choose

lemma analyticAt_germRep {x : E} (t : (analyticPresheaf 𝕜 E).stalk x) :
    AnalyticAt 𝕜 (germRep t) x :=
  (exists_germOf_eq t).choose_spec.choose

lemma germOf_germRep {x : E} (t : (analyticPresheaf 𝕜 E).stalk x) :
    germOf (germRep t) (analyticAt_germRep t) = t :=
  (exists_germOf_eq t).choose_spec.choose_spec

lemma germRep_germOf {x : E} (G : E → 𝕜) (hG : AnalyticAt 𝕜 G x) :
    germRep (germOf G hG) =ᶠ[𝓝 x] G :=
  (germOf_eq_germOf_iff _ hG).mp (germOf_germRep _)

include hΦ in
lemma analyticAt_comp_germRep
    (t : (analyticPresheaf 𝕜 E).stalk (Φ y)) :
    AnalyticAt 𝕜 (fun z ↦ germRep t (Φ z)) y :=
  (analyticAt_germRep t).comp hΦ

/-- The pullback of a germ along an analytic map (underlying function of `stalkPullback`). -/
def stalkPullbackFun (t : (analyticPresheaf 𝕜 E).stalk (Φ y)) :
    (analyticPresheaf 𝕜 E').stalk y :=
  germOf _ (analyticAt_comp_germRep Φ hΦ t)

lemma stalkPullbackFun_germOf (G : E → 𝕜) (hG : AnalyticAt 𝕜 G (Φ y)) :
    stalkPullbackFun Φ hΦ (germOf G hG) = germOf (fun z ↦ G (Φ z)) (hG.comp hΦ) :=
  germOf_congr _ ((germRep_germOf G hG).comp_tendsto hΦ.continuousAt.tendsto)

/-- The pullback of germs along an analytic map: `𝒪_{E,Φ(y)} → 𝒪_{E',y}`, `[G] ↦ [G ∘ Φ]`. -/
def stalkPullback :
    (analyticPresheaf 𝕜 E).stalk (Φ y) →+*
      (analyticPresheaf 𝕜 E').stalk y where
  toFun := stalkPullbackFun Φ hΦ
  map_one' := by
    rw [← germOf_one, stalkPullbackFun_germOf]
    exact germOf_one
  map_mul' s t := by
    induction s using germOf_induction with
    | h G hG =>
    induction t using germOf_induction with
    | h H hH =>
    rw [← germOf_mul, stalkPullbackFun_germOf, stalkPullbackFun_germOf, stalkPullbackFun_germOf,
      ← germOf_mul]
    rfl
  map_zero' := by
    rw [← germOf_zero, stalkPullbackFun_germOf]
    exact germOf_zero
  map_add' s t := by
    induction s using germOf_induction with
    | h G hG =>
    induction t using germOf_induction with
    | h H hH =>
    rw [← germOf_add, stalkPullbackFun_germOf, stalkPullbackFun_germOf, stalkPullbackFun_germOf,
      ← germOf_add]
    rfl

lemma stalkPullback_germOf (G : E → 𝕜) (hG : AnalyticAt 𝕜 G (Φ y)) :
    stalkPullback Φ hΦ (germOf G hG) = germOf (fun z ↦ G (Φ z)) (hG.comp hΦ) :=
  stalkPullbackFun_germOf Φ hΦ G hG

lemma stalkPullback_comp {E'' : Type u} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    (Ψ : E'' → E') {z : E''} (hΨ : AnalyticAt 𝕜 Ψ z) (hΦ' : AnalyticAt 𝕜 Φ (Ψ z))
    (t : (analyticPresheaf 𝕜 E).stalk (Φ (Ψ z))) :
    stalkPullback Ψ hΨ (stalkPullback Φ hΦ' t) = stalkPullback (Φ ∘ Ψ) (hΦ'.comp hΨ) t := by
  induction t using germOf_induction with
  | h G hG => rw [stalkPullback_germOf, stalkPullback_germOf, stalkPullback_germOf]; rfl

lemma stalkPullback_id (t : (analyticPresheaf 𝕜 E).stalk y') :
    stalkPullback (id : E → E) (analyticAt_id (z := y')) t = t := by
  induction t using germOf_induction with
  | h G hG => rw [stalkPullback_germOf]; rfl

lemma evalStalk_stalkPullback (t : (analyticPresheaf 𝕜 E).stalk (Φ y)) :
    evalStalk y (stalkPullback Φ hΦ t) = evalStalk (Φ y) t := by
  induction t using germOf_induction with
  | h G hG => rw [stalkPullback_germOf, evalStalk_germOf, evalStalk_germOf]

end Pullback

/-! ### Analytic maps between local models -/

namespace LocalModelData

/-- Morphisms between local models are determined by their values on points and by the classes
they assign to sections. -/
lemma hom_ext {D' : LocalModelData 𝕜 E'} {D : LocalModelData 𝕜 E}
    {f g : D'.toLocallyRingedSpace ⟶ D.toLocallyRingedSpace}
    (hb : ∀ y, f.base y = g.base y)
    (hs : ∀ (W : Opens (TopCat.of D.zeroSet)) (s : D.presheaf.obj (op W)) (y : D'.zeroSet)
      (hf : f.base y ∈ W) (hg : g.base y ∈ W),
      (f.c.app (op W) s).1 ⟨y, hf⟩ = (g.c.app (op W) s).1 ⟨y, hg⟩) : f = g := by
  apply AlgebraicGeometry.LocallyRingedSpace.Hom.ext'
  have hb' : f.base = g.base := TopCat.ext hb
  refine AlgebraicGeometry.PresheafedSpace.ext _ _ hb' ?_
  ext W s
  apply Subtype.ext
  funext y
  rw [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app, CommRingCat.comp_apply]
  exact (presheaf_map_apply D' _ (f.c.app (op W) s) y).trans (hs W s y.1 _ y.2)

/-- Near each point, a section of the structure sheaf is the class of one analytic function. -/
lemma exists_classOf_eq {D : LocalModelData 𝕜 E} {W : Opens (TopCat.of D.zeroSet)}
    (s : D.presheaf.obj (op W)) (p : W) :
    ∃ (V : Opens (TopCat.of D.zeroSet)) (_ : p.1 ∈ V) (G : E → 𝕜)
      (hG : ∀ q ∈ V, AnalyticAt 𝕜 G ((q : D.zeroSet) : E)),
      ∀ (q : D.zeroSet) (hqW : q ∈ W) (hqV : q ∈ V), s.1 ⟨q, hqW⟩ = D.classOf q G (hG q hqV) := by
  obtain ⟨V, hpV, i, G, hG, hsG⟩ := s.2 p
  exact ⟨V, hpV, G, fun q hq ↦ hG ⟨q, hq⟩, fun q hqW hqV ↦ hsG ⟨q, hqV⟩⟩

/-- An analytic map `Φ : E' → E` from the ambient space of a local model `D'` to that of `D`,
analytic near `Z(D')`, with `Φ(Z(D')) ⊆ U(D)` and pulling back the equations of `D` into the ideal
of `D'`. -/
structure AnalyticMap (D' : LocalModelData 𝕜 E') (D : LocalModelData 𝕜 E) where
  /-- The underlying map of ambient spaces. -/
  toFun : E' → E
  analyticAt : ∀ y ∈ D'.zeroSet, AnalyticAt 𝕜 toFun y
  mapsTo : ∀ y ∈ D'.zeroSet, toFun y ∈ D.U
  mem_ideal : ∀ (y : D'.zeroSet) (i : Fin D.k),
    stalkPullback toFun (analyticAt y y.2)
      (germOf (D.f i) (D.analyticAt_f i _ (mapsTo y y.2))) ∈ D'.ideal y (D'.mem_U y)

namespace AnalyticMap

variable {D' : LocalModelData 𝕜 E'} {D : LocalModelData 𝕜 E} (Φ : AnalyticMap D' D)

lemma mem_zeroSet (y : D'.zeroSet) : Φ.toFun y ∈ D.zeroSet := by
  refine ⟨Φ.mapsTo y y.2, fun i ↦ ?_⟩
  have h := (mem_maximalIdeal_stalk_iff _).mp (D'.ideal_le_maximalIdeal y (Φ.mem_ideal y i))
  rwa [evalStalk_stalkPullback, evalStalk_germOf] at h

/-- The map `Z(D') → Z(D)` on points. -/
abbrev pointMap (y : D'.zeroSet) : D.zeroSet := ⟨Φ.toFun y, Φ.mem_zeroSet y⟩

@[simp] lemma coe_pointMap (y : D'.zeroSet) : (Φ.pointMap y : E) = Φ.toFun y := rfl

lemma continuous_pointMap : Continuous Φ.pointMap := by
  refine Continuous.subtype_mk ?_ _
  rw [continuous_iff_continuousAt]
  intro y
  exact ((Φ.analyticAt y y.2).continuousAt).comp continuous_subtype_val.continuousAt

/-- The map on points, as a morphism of topological spaces. -/
def base : TopCat.of D'.zeroSet ⟶ TopCat.of D.zeroSet :=
  TopCat.ofHom ⟨Φ.pointMap, Φ.continuous_pointMap⟩

/-- The pullback `𝒪_{E,Φ(y)}/(f) → 𝒪_{E',y}/(f')`. -/
def fiberMap (y : D'.zeroSet) : D.Fiber (Φ.pointMap y) →+* D'.Fiber y :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (stalkPullback Φ.toFun (Φ.analyticAt y y.2)))
    fun a ha ↦ by
      have : D.ideal (Φ.pointMap y) (D.mem_U _) ≤ RingHom.ker
          ((Ideal.Quotient.mk (D'.ideal y (D'.mem_U y))).comp
            (stalkPullback Φ.toFun (Φ.analyticAt y y.2))) := by
        refine Ideal.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Φ.mem_ideal y i)
      exact RingHom.mem_ker.mp (this ha)

lemma fiberMap_classOf (y : D'.zeroSet) (G : E → 𝕜) (hG : AnalyticAt 𝕜 G (Φ.toFun y)) :
    Φ.fiberMap y (D.classOf (Φ.pointMap y) G hG) =
      D'.classOf y (fun z ↦ G (Φ.toFun z)) (hG.comp (Φ.analyticAt y y.2)) := by
  rw [fiberMap, classOf, Ideal.Quotient.lift_mk, RingHom.comp_apply, stalkPullback_germOf]
  rfl

lemma evalFiber_fiberMap (y : D'.zeroSet) (t : D.Fiber (Φ.pointMap y)) :
    D'.evalFiber y (Φ.fiberMap y t) = D.evalFiber (Φ.pointMap y) t := by
  obtain ⟨G, hG, rfl⟩ := D.classOf_surjective _ t
  rw [fiberMap_classOf, evalFiber_classOf, evalFiber_classOf]

instance isLocalHom_fiberMap (y : D'.zeroSet) : IsLocalHom (Φ.fiberMap y) := by
  refine ⟨fun t ht ↦ ?_⟩
  rw [isUnit_fiber_iff] at ht ⊢
  rwa [evalFiber_fiberMap] at ht

/-- The pullback of sections along `Φ`. -/
def sectionMap (W : Opens (TopCat.of D.zeroSet)) :
    D.presheaf.obj (op W) ⟶ D'.presheaf.obj (op ((Opens.map Φ.base).obj W)) :=
  CommRingCat.ofHom
    { toFun s := ⟨fun y ↦ Φ.fiberMap y.1 (s.1 ⟨Φ.pointMap y.1, y.2⟩), by
        intro y
        obtain ⟨V, hxV, i, G, hG, hsG⟩ := s.2 ⟨Φ.pointMap y.1, y.2⟩
        refine ⟨(Opens.map Φ.base).obj V, hxV, (Opens.map Φ.base).map i,
          fun z ↦ G (Φ.toFun z), fun z ↦ AnalyticAt.comp (g := G) (f := Φ.toFun)
            (hG ⟨Φ.pointMap z.1, z.2⟩) (Φ.analyticAt z.1 z.1.2), fun z ↦ ?_⟩
        have h := hsG ⟨Φ.pointMap z.1, z.2⟩
        dsimp only at h ⊢
        exact (congrArg (Φ.fiberMap z.1) h).trans (fiberMap_classOf _ _ _ _)⟩
      map_one' := Subtype.ext (funext fun _ ↦ map_one _)
      map_mul' _ _ := Subtype.ext (funext fun _ ↦ map_mul _ _ _)
      map_zero' := Subtype.ext (funext fun _ ↦ map_zero _)
      map_add' _ _ := Subtype.ext (funext fun _ ↦ map_add _ _ _) }

lemma sectionMap_apply (W : Opens (TopCat.of D.zeroSet)) (s : D.presheaf.obj (op W))
    (y : (Opens.map Φ.base).obj W) :
    (Φ.sectionMap W s).1 y = Φ.fiberMap y.1 (s.1 ⟨Φ.pointMap y.1, y.2⟩) := rfl

/-- The morphism of ringed spaces `Z(D') → Z(D)` induced by `Φ`. -/
def toPresheafedSpaceHom :
    D'.toLocallyRingedSpace.toPresheafedSpace.Hom D.toLocallyRingedSpace.toPresheafedSpace where
  base := Φ.base
  c :=
    { app W := Φ.sectionMap W.unop
      naturality _ _ _ := rfl }

lemma stalkToFiber_stalkMap (y : D'.zeroSet)
    (t : D.presheaf.stalk (Φ.pointMap y)) :
    D'.stalkToFiber y (Φ.toPresheafedSpaceHom.stalkMap y t) =
      Φ.fiberMap y (D.stalkToFiber (Φ.pointMap y) t) := by
  obtain ⟨W, hW, s, rfl⟩ := D.presheaf.exists_germ_eq t
  erw [AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply]
  rw [stalkToFiber_germ]
  exact D'.stalkToFiber_germ _ y hW _

/-- **Morphisms of local models**: an analytic map compatible with the equations induces a
morphism of locally ringed spaces `Z(D') → Z(D)`. -/
def toHom : D'.toLocallyRingedSpace ⟶ D.toLocallyRingedSpace :=
  ⟨Φ.toPresheafedSpaceHom, fun y ↦ by
    refine ⟨fun t ht ↦ ?_⟩
    have h₁ : IsUnit (D'.stalkToFiber y (Φ.toPresheafedSpaceHom.stalkMap y t)) :=
      ht.map (D'.stalkToFiber y).hom
    have h₁' : IsUnit (Φ.fiberMap y (D.stalkToFiber (Φ.pointMap y) t)) := by
      convert h₁ using 1
      exact (Φ.stalkToFiber_stalkMap y t).symm
    have h₂ : IsUnit (D.stalkToFiber (Φ.pointMap y) t) :=
      (Φ.isLocalHom_fiberMap y).map_nonunit _ h₁'
    exact (MulEquiv.isUnit_map (D.stalkIso (Φ.pointMap y)).toMulEquiv).mp h₂⟩

@[simp] lemma toHom_base_apply (y : D'.zeroSet) : Φ.toHom.base y = Φ.pointMap y := rfl

lemma toHom_c_app_apply (W : Opens (TopCat.of D.zeroSet)) (s : D.presheaf.obj (op W))
    (y : D'.zeroSet) (hy : Φ.toHom.base y ∈ W) :
    (Φ.toHom.c.app (op W) s).1 ⟨y, hy⟩ = Φ.fiberMap y (s.1 ⟨Φ.pointMap y, hy⟩) := rfl

/-- The identity map of the ambient space. -/
def id (D : LocalModelData 𝕜 E) : AnalyticMap D D where
  toFun := _root_.id
  analyticAt _ _ := analyticAt_id
  mapsTo _ hy := hy.1
  mem_ideal y i := by
    rw [stalkPullback_germOf]
    exact Ideal.subset_span ⟨i, rfl⟩

/-- Composition of analytic maps between local models. -/
def comp {E'' : Type u} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {D'' : LocalModelData 𝕜 E''} (Ψ : AnalyticMap D' D) (Φ : AnalyticMap D'' D') :
    AnalyticMap D'' D where
  toFun := Ψ.toFun ∘ Φ.toFun
  analyticAt y hy := (Ψ.analyticAt _ (Φ.mem_zeroSet ⟨y, hy⟩)).comp (Φ.analyticAt y hy)
  mapsTo y hy := Ψ.mapsTo _ (Φ.mem_zeroSet ⟨y, hy⟩)
  mem_ideal y i := by
    have hmap : (D'.ideal (Φ.pointMap y) (D'.mem_U _)).map
        (stalkPullback Φ.toFun (Φ.analyticAt y y.2)) ≤ D''.ideal y (D''.mem_U y) := by
      rw [Ideal.map_le_iff_le_comap]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      exact Φ.mem_ideal y j
    rw [← stalkPullback_comp (hΨ := Φ.analyticAt y y.2)
      (hΦ' := Ψ.analyticAt _ (Φ.mem_zeroSet y))]
    exact hmap (Ideal.mem_map_of_mem _ (Ψ.mem_ideal (Φ.pointMap y) i))

lemma toHom_id (D : LocalModelData 𝕜 E) : (AnalyticMap.id D).toHom = 𝟙 _ := by
  refine hom_ext (fun _ ↦ rfl) fun W s y hf hg ↦ ?_
  obtain ⟨V, hyV, G, hG, hsG⟩ := exists_classOf_eq s ⟨y, hf⟩
  have h₁ : (AnalyticMap.id D).fiberMap y (s.1 ⟨y, hf⟩) = D.classOf y G (hG y hyV) := by
    rw [hsG y hf hyV]
    exact fiberMap_classOf _ y G _
  have h₂ : ((𝟙 D.toLocallyRingedSpace : D.toLocallyRingedSpace ⟶ _).c.app (op W) s).1
      ⟨y, hg⟩ = s.1 ⟨y, hg⟩ := rfl
  exact h₁.trans ((hsG y hg hyV).symm.trans h₂.symm)

lemma toHom_comp {E'' : Type u} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {D'' : LocalModelData 𝕜 E''} (Ψ : AnalyticMap D' D) (Φ : AnalyticMap D'' D') :
    (Ψ.comp Φ).toHom = Φ.toHom ≫ Ψ.toHom := by
  refine hom_ext (fun _ ↦ rfl) fun W s y hf hg ↦ ?_
  obtain ⟨V, hyV, G, hG, hsG⟩ := exists_classOf_eq s ⟨_, hf⟩
  have h₁ : ((Ψ.comp Φ).toHom.c.app (op W) s).1 ⟨y, hf⟩ =
      D''.classOf y (fun z ↦ G (Ψ.toFun (Φ.toFun z)))
        (AnalyticAt.comp (g := G) (f := (Ψ.comp Φ).toFun) (hG _ hyV)
          ((Ψ.comp Φ).analyticAt y y.2)) := by
    change (Ψ.comp Φ).fiberMap y (s.1 ⟨_, hf⟩) = _
    rw [hsG _ hf hyV]
    exact fiberMap_classOf _ y G _
  have h₂ : ((Φ.toHom ≫ Ψ.toHom).c.app (op W) s).1 ⟨y, hg⟩ =
      Φ.fiberMap y (Ψ.fiberMap (Φ.pointMap y) (s.1 ⟨Ψ.pointMap (Φ.pointMap y), hg⟩)) := rfl
  have h₃ : Φ.fiberMap y (Ψ.fiberMap (Φ.pointMap y) (s.1 ⟨Ψ.pointMap (Φ.pointMap y), hg⟩)) =
      D''.classOf y (fun z ↦ G (Ψ.toFun (Φ.toFun z)))
        (AnalyticAt.comp (g := G) (f := (Ψ.comp Φ).toFun) (hG _ hyV)
          ((Ψ.comp Φ).analyticAt y y.2)) := by
    rw [hsG (Ψ.pointMap (Φ.pointMap y)) hg hyV, fiberMap_classOf, fiberMap_classOf]
  exact h₁.trans (h₃.symm.trans h₂.symm)

end AnalyticMap

end LocalModelData

end AnalyticGeometry
