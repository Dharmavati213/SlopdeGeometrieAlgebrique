/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Etale.Torsor

/-!
# The presheaf of local `H¹`

For a presheaf of groups `G` on a site `(C, J)`, the restriction of torsors along the functors
`Over.map f : Over V ⥤ Over U` makes `U ↦ H¹(C/U, G|U)` a presheaf of pointed sets
`H1.presheaf J G` on `C` (`Torsor.overMapId` and `Torsor.overMapComp` give the functoriality).
Every torsor is locally trivial, so every section of this presheaf is locally the distinguished
point (`H1.exists_covering_map_eq_trivialClass`), and any two torsors are locally isomorphic
(`H1.exists_covering_map_eq`). The sheafification of its composition with a continuous functor
is the first higher direct image (`SGA.Foundations.Etale.HigherDirectImage`).

## References

* [J. Giraud, *Cohomologie non abélienne*, V 2][giraud1971]
* [SGA 4, Exposé XII, 5][sga4]
-/

universe w v' u' v u

open CategoryTheory Opposite Limits

-- The fibers of the restrictions of torsors are only definitionally equal to the expected ones
-- after unfolding `Torsor.overMap`; this is needed to rewrite their components.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat.{w}}

namespace Torsor

variable {U V W : C} (P : Torsor (J.over U) (PresheafOfGroups.over G U))

lemma obj_map_congr {Y₁ Y₂ : Over U} (a b : Y₁ ⟶ Y₂) (h : a.left = b.left)
    (x : P.obj.obj (op Y₂)) : P.obj.map a.op x = P.obj.map b.op x := by
  rw [Over.OverMorphism.ext h]

lemma obj_map_map {Y₁ Y₂ Y₃ : Over U} (a : Y₁ ⟶ Y₂) (b : Y₂ ⟶ Y₃) (x : P.obj.obj (op Y₃)) :
    P.obj.map a.op (P.obj.map b.op x) = P.obj.map (a ≫ b).op x := by
  rw [op_comp, Functor.map_comp_apply]

lemma obj_map_eq_self {Y : Over U} (e : Y ⟶ Y) (h : e.left = 𝟙 _) (x : P.obj.obj (op Y)) :
    P.obj.map e.op x = x := by
  rw [Over.OverMorphism.ext (h.trans (Over.id_left Y).symm), op_id, Functor.map_id_apply]

lemma obj_map_comp_congr {Y₁ Y₂ Y₃ Y₂' : Over U} (a : Y₁ ⟶ Y₂) (b : Y₂ ⟶ Y₃) (a' : Y₁ ⟶ Y₂')
    (b' : Y₂' ⟶ Y₃) (h : a.left ≫ b.left = a'.left ≫ b'.left) :
    P.obj.map b.op ≫ P.obj.map a.op = P.obj.map b'.op ≫ P.obj.map a'.op := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
    Over.OverMorphism.ext (by simpa using h : (a ≫ b).left = (a' ≫ b').left)]

/-- The identification `P.overMap f ⟶ P.overMap f'` for `f = f'`. -/
@[simps]
def overMapCongrHom {f f' : V ⟶ U} (h : f = f') : P.overMap f ⟶ P.overMap f' where
  hom :=
    { app Y := P.obj.map (Over.homMk (𝟙 Y.unop.left) (by simp [h]) :
          (Over.map f').obj Y.unop ⟶ (Over.map f).obj Y.unop).op
      naturality Y₁ Y₂ b := obj_map_comp_congr P _ _ _ _ (by simp) }
  map_smul Y a x := (P.map_smul' (Over.homMk (𝟙 Y.unop.left) (by simp [h]) :
    (Over.map f').obj Y.unop ⟶ (Over.map f).obj Y.unop).op a x).trans
      (congr_arg (· • _) (by simp))

/-- The identification `P.overMap (𝟙 U) ⟶ P`. -/
@[simps]
def overMapIdHom : P.overMap (𝟙 U) ⟶ P where
  hom :=
    { app Y := P.obj.map (Over.homMk (𝟙 Y.unop.left) (by simp) :
          Y.unop ⟶ (Over.map (𝟙 U)).obj Y.unop).op
      naturality Y₁ Y₂ b := obj_map_comp_congr P _ _ b.unop _ (by simp) }
  map_smul Y a x := (P.map_smul' (Over.homMk (𝟙 Y.unop.left) (by simp) :
    Y.unop ⟶ (Over.map (𝟙 U)).obj Y.unop).op a x).trans (congr_arg (· • _) (by simp))

/-- The identification `P ⟶ P.overMap (𝟙 U)`. -/
@[simps]
def toOverMapId : P ⟶ P.overMap (𝟙 U) where
  hom :=
    { app Y := P.obj.map (Over.homMk (𝟙 Y.unop.left) (by simp) :
          (Over.map (𝟙 U)).obj Y.unop ⟶ Y.unop).op
      naturality Y₁ Y₂ b := obj_map_comp_congr P _ b.unop _ _ (by simp) }
  map_smul Y a x := (P.map_smul' (Over.homMk (𝟙 Y.unop.left) (by simp) :
    (Over.map (𝟙 U)).obj Y.unop ⟶ Y.unop).op a x).trans (congr_arg (· • _) (by simp))

/-- The identification `P.overMap (g ≫ f) ⟶ (P.overMap f).overMap g`. -/
@[simps]
def overMapCompHom (f : V ⟶ U) (g : W ⟶ V) : P.overMap (g ≫ f) ⟶ (P.overMap f).overMap g where
  hom :=
    { app Y := P.obj.map (Over.homMk (𝟙 Y.unop.left) (by simp) :
          (Over.map f).obj ((Over.map g).obj Y.unop) ⟶ (Over.map (g ≫ f)).obj Y.unop).op
      naturality Y₁ Y₂ b := obj_map_comp_congr P _ _ _ _ (by simp) }
  map_smul Y a x := (P.map_smul' (Over.homMk (𝟙 Y.unop.left) (by simp) :
    (Over.map f).obj ((Over.map g).obj Y.unop) ⟶ (Over.map (g ≫ f)).obj Y.unop).op a x).trans
      (congr_arg (· • _) (by simp))

/-- The identification `(P.overMap f).overMap g ⟶ P.overMap (g ≫ f)`. -/
@[simps]
def overMapCompInv (f : V ⟶ U) (g : W ⟶ V) : (P.overMap f).overMap g ⟶ P.overMap (g ≫ f) where
  hom :=
    { app Y := P.obj.map (Over.homMk (𝟙 Y.unop.left) (by simp) :
          (Over.map (g ≫ f)).obj Y.unop ⟶ (Over.map f).obj ((Over.map g).obj Y.unop)).op
      naturality Y₁ Y₂ b := obj_map_comp_congr P _ _ _ _ (by simp) }
  map_smul Y a x := (P.map_smul' (Over.homMk (𝟙 Y.unop.left) (by simp) :
    (Over.map (g ≫ f)).obj Y.unop ⟶ (Over.map f).obj ((Over.map g).obj Y.unop)).op a x).trans
      (congr_arg (· • _) (by simp))

/-- Normalizes the components of the identifications between restrictions of a torsor. -/
macro "torsor_restrict_ext" : tactic => `(tactic| (
  ext Y x
  simp only [TypeCat.Fun.toFun_apply, comp_hom, NatTrans.comp_app, types_comp_apply, id_hom,
    NatTrans.id_app, types_id_apply, overMap_obj, Functor.comp_map, Functor.op_map,
    Quiver.Hom.unop_op, overMapCongrHom_hom_app, overMapIdHom_hom_app, toOverMapId_hom_app,
    overMapCompHom_hom_app, overMapCompInv_hom_app, overMapFunctor_map_hom_app]
  repeat erw [obj_map_map]))

/-- `P.overMap f ≅ P.overMap f'` for `f = f'`. -/
@[simps]
def overMapCongr {f f' : V ⟶ U} (h : f = f') : P.overMap f ≅ P.overMap f' where
  hom := P.overMapCongrHom h
  inv := P.overMapCongrHom h.symm
  hom_inv_id := by torsor_restrict_ext; exact obj_map_eq_self _ _ (by simp) _
  inv_hom_id := by torsor_restrict_ext; exact obj_map_eq_self _ _ (by simp) _

/-- The restriction of a torsor on `Over U` along `Over.map (𝟙 U)` is isomorphic to it. -/
@[simps]
def overMapId : P.overMap (𝟙 U) ≅ P where
  hom := P.overMapIdHom
  inv := P.toOverMapId
  hom_inv_id := by torsor_restrict_ext; exact obj_map_eq_self _ _ (by simp) _
  inv_hom_id := by torsor_restrict_ext; exact obj_map_eq_self _ _ (by simp) _

/-- Restricting a torsor on `Over U` along `Over.map (g ≫ f)` is the same as restricting it
along `Over.map f` and then `Over.map g`. -/
@[simps]
def overMapComp (f : V ⟶ U) (g : W ⟶ V) : P.overMap (g ≫ f) ≅ (P.overMap f).overMap g where
  hom := P.overMapCompHom f g
  inv := P.overMapCompInv f g
  hom_inv_id := by torsor_restrict_ext; exact obj_map_eq_self _ _ (by simp) _
  inv_hom_id := by torsor_restrict_ext; exact obj_map_eq_self _ _ (by simp) _

variable (J G)

/-- `P.overMap f ≅ P.overMap f'` for `f = f'`, naturally in `P`. -/
@[simps!]
def overMapFunctorCongr {f f' : V ⟶ U} (h : f = f') :
    overMapFunctor J G f ≅ overMapFunctor J G f' :=
  NatIso.ofComponents (fun P ↦ P.overMapCongr h) fun {P Q} φ ↦ by
    torsor_restrict_ext
    exact (NatTrans.naturality_apply φ.hom _ _).symm

/-- `P.overMap (𝟙 U) ≅ P`, naturally in `P`. -/
@[simps!]
def overMapFunctorId (U : C) : overMapFunctor J G (𝟙 U) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun P ↦ P.overMapId) fun {P Q} φ ↦ by
    torsor_restrict_ext
    exact (NatTrans.naturality_apply φ.hom _ _).symm

/-- `P.overMap (g ≫ f) ≅ (P.overMap f).overMap g`, naturally in `P`. -/
@[simps!]
def overMapFunctorComp (f : V ⟶ U) (g : W ⟶ V) :
    overMapFunctor J G (g ≫ f) ≅ overMapFunctor J G f ⋙ overMapFunctor J G g :=
  NatIso.ofComponents (fun P ↦ P.overMapComp f g) fun {P Q} φ ↦ by
    torsor_restrict_ext
    exact (NatTrans.naturality_apply φ.hom _ _).symm

end Torsor

namespace H1

variable (J G)

/-- The presheaf `U ↦ H¹(C/U, G|U)` of isomorphism classes of torsors over the objects of `C`,
for the restriction of torsors along the functors `Over.map f`. -/
noncomputable def presheaf : Cᵒᵖ ⥤ Type _ where
  obj U := H1 (J.over U.unop) (PresheafOfGroups.over G U.unop)
  map {U V} f := ↾(H1.restrict (J.over V.unop) (Over.map f.unop) :
    H1 (J.over U.unop) (PresheafOfGroups.over G U.unop) →
      H1 (J.over V.unop) (PresheafOfGroups.over G V.unop))
  map_id U := by
    ext c
    obtain ⟨P, rfl⟩ := mk_surjective c
    exact (Torsor.class_eq_class_iff _ _).2 ⟨P.overMapId⟩
  map_comp {U V W} f g := by
    ext c
    obtain ⟨P, rfl⟩ := mk_surjective c
    exact (Torsor.class_eq_class_iff _ _).2 ⟨P.overMapComp f.unop g.unop⟩

variable {J G}

@[simp]
lemma presheaf_map_class {U V : C} (f : V ⟶ U)
    (P : Torsor (J.over U) (PresheafOfGroups.over G U)) :
    (presheaf J G).map f.op P.class = (P.overMap f).class :=
  rfl

variable (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))

include hG in
lemma isSheaf_over (U : C) :
    Presieve.IsSheaf (J.over U) (PresheafOfGroups.over G U ⋙ CategoryTheory.forget GrpCat) :=
  (Over.forget U).op_comp_isSheaf_of_isSheaf_type (J.over U) hG

/-- The distinguished point of `H¹(C/U, G|U)`. -/
noncomputable def presheafTrivialClass (U : C) : (presheaf J G).obj (op U) :=
  trivialClass (J.over U) (PresheafOfGroups.over G U) (isSheaf_over hG U)

/-- The restriction of the trivial torsor is the trivial torsor. -/
@[simps]
def overMapTrivialIso {U V : C} (f : V ⟶ U) :
    (Torsor.trivial (J.over U) (PresheafOfGroups.over G U) (isSheaf_over hG U)).overMap f ≅
      Torsor.trivial (J.over V) (PresheafOfGroups.over G V) (isSheaf_over hG V) where
  hom :=
    { hom := 𝟙 _
      map_smul Y g x := rfl }
  inv :=
    { hom := 𝟙 _
      map_smul Y g x := rfl }

lemma presheaf_map_trivialClass {U V : C} (f : V ⟶ U) :
    (presheaf J G).map f.op (presheafTrivialClass hG U) = presheafTrivialClass hG V :=
  (Torsor.class_eq_class_iff _ _).2 ⟨overMapTrivialIso hG f⟩

/-- Every class in `H¹(C/U, G|U)` is locally trivial. -/
theorem exists_covering_map_eq_trivialClass {U : C} (c : (presheaf J G).obj (op U)) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      (presheaf J G).map f.op c = presheafTrivialClass hG V := by
  obtain ⟨P, rfl⟩ := mk_surjective c
  refine ⟨Sieve.overEquiv _ (P.nonemptySieve (Over.mk (𝟙 U))),
    (GrothendieckTopology.mem_over_iff J (P.nonemptySieve (Over.mk (𝟙 U)))).1
      (P.nonemptySieve_mem (Over.mk (𝟙 U))), fun V f hf ↦ ?_⟩
  rw [presheaf_map_class]
  obtain ⟨x⟩ := (Sieve.overEquiv_iff (P.nonemptySieve (Over.mk (𝟙 U))) (f := f)).1 hf
  exact (Torsor.class_eq_trivialClass_iff_of_isTerminal (Over.mkIdTerminal (X := V)) _ _).2
    ⟨P.obj.map (Over.homMk (𝟙 V) (by simp) :
      (Over.map f).obj (Over.mk (𝟙 V)) ⟶ Over.mk (f ≫ 𝟙 U)).op x⟩

include hG in
/-- Any two torsors over `U` are locally isomorphic. -/
theorem exists_covering_map_eq {U : C} (c c' : (presheaf J G).obj (op U)) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      (presheaf J G).map f.op c = (presheaf J G).map f.op c' := by
  obtain ⟨R, hR, h⟩ := exists_covering_map_eq_trivialClass hG c
  obtain ⟨R', hR', h'⟩ := exists_covering_map_eq_trivialClass hG c'
  exact ⟨R ⊓ R', J.intersection_covering hR hR', fun V f hf ↦ (h f hf.1).trans (h' f hf.2).symm⟩

end H1

end CategoryTheory
