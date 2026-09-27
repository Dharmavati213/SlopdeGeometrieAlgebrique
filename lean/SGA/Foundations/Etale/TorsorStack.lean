/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import SGA.Foundations.Etale.TorsorCech
import SGA.Foundations.Etale.TorsorPresheaf

/-!
# The stack of torsors

For a presheaf of groups `G` on a site `(C, J)`, the categories `Tors(C/U, G|U)` of torsors on the
sites `C/U`, with the restriction functors along the functors `Over.map f`, form a pseudofunctor
`Torsor.stack J G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat` (Giraud II 2.3.2, III 1.4.2). The
coherence isomorphisms are the identifications `Torsor.overMapFunctorId` and
`Torsor.overMapFunctorComp`, whose coherence is checked on the functor categories
(`Torsor.overMapFunctor_assoc`, `Torsor.overMapFunctor_id_comp`, `Torsor.overMapFunctor_comp_id`).

For a descent datum `D` of torsors relative to a family `f i : X i ⟶ S`, the gluing isomorphisms
give transfer maps between the sections of the `D.obj i` (`Torsor.StackDescent.transfer`), which
satisfy the cocycle conditions. For a covering family, the functor from torsors over `S` to descent
data is fully faithful (`Torsor.full_toDescentData`, `Torsor.faithful_toDescentData`): torsors
satisfy descent of morphisms, i.e. the stack of torsors is a prestack (`Torsor.isPrestack_stack`,
Giraud III 1.4.1). Effectivity of descent is proved in `SGA.Foundations.Etale.TorsorDescent`.

## References

* [J. Giraud, *Cohomologie non abélienne*, II 2.3.2 and III 1.4][giraud1971]
* [Stacks Project, Tag 04UK](https://stacks.math.columbia.edu/tag/04UK)
-/

universe t w v u

open CategoryTheory Opposite Limits Bicategory Pseudofunctor

-- See the comment in `SGA.Foundations.Etale.TorsorPresheaf`.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Torsor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w})
  {U V W T : C}

/-- The identification of restrictions along equal morphisms is the `eqToIso`. -/
lemma overMapFunctorCongr_eq_eqToIso {f f' : V ⟶ U} (h : f = f') :
    overMapFunctorCongr J G h = eqToIso (by rw [h]) := by
  subst h
  ext : 2
  torsor_restrict_ext
  exact obj_map_eq_self _ _ (by simp) _

/-- Associativity of the identifications `Torsor.overMapFunctorComp`. -/
lemma overMapFunctor_assoc (f : V ⟶ U) (g : W ⟶ V) (h : T ⟶ W) :
    (overMapFunctorComp J G (g ≫ f) h).hom ≫
      Functor.whiskerRight (overMapFunctorComp J G f g).hom (overMapFunctor J G h) ≫
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (overMapFunctor J G f) (overMapFunctorComp J G g h).inv ≫
            (overMapFunctorComp J G f (h ≫ g)).inv =
      (overMapFunctorCongr J G (Category.assoc h g f).symm).hom := by
  ext P : 2
  torsor_restrict_ext
  simp only [overMapFunctorCongr_hom_app_hom_app]
  exact obj_map_congr _ _ _ (by simp) _

/-- Left unitality of the identifications `Torsor.overMapFunctorComp`. -/
lemma overMapFunctor_id_comp (f : V ⟶ U) :
    (overMapFunctorComp J G (𝟙 U) f).hom ≫
      Functor.whiskerRight (overMapFunctorId J G U).hom (overMapFunctor J G f) ≫
        (Functor.leftUnitor _).hom =
      (overMapFunctorCongr J G (Category.comp_id f)).hom := by
  ext P : 2
  torsor_restrict_ext
  simp only [overMapFunctorCongr_hom_app_hom_app]
  exact obj_map_congr _ _ _ (by simp) _

/-- Right unitality of the identifications `Torsor.overMapFunctorComp`. -/
lemma overMapFunctor_comp_id (f : V ⟶ U) :
    (overMapFunctorComp J G f (𝟙 V)).hom ≫
      Functor.whiskerLeft (overMapFunctor J G f) (overMapFunctorId J G V).hom ≫
        (Functor.rightUnitor _).hom =
      (overMapFunctorCongr J G (Category.id_comp f)).hom := by
  ext P : 2
  torsor_restrict_ext
  simp only [overMapFunctorCongr_hom_app_hom_app]
  exact obj_map_congr _ _ _ (by simp) _

/-- The stack of `G`-torsors: the pseudofunctor `U ↦ Tors(C/U, G|U)` on `Cᵒᵖ`, with the restriction
functors along the `Over.map f`. -/
def stack : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{max u v w, max u v (w + 1)} :=
  LocallyDiscrete.mkPseudofunctor
    (fun U ↦ Cat.of (Torsor (J.over U.unop) (PresheafOfGroups.over G U.unop)))
    (fun f ↦ (overMapFunctor J G f.unop).toCatHom)
    (fun U ↦ Cat.Hom.isoMk (overMapFunctorId J G U.unop))
    (fun f g ↦ Cat.Hom.isoMk (overMapFunctorComp J G f.unop g.unop))
    (fun f g h ↦ by
      ext1
      simpa [overMapFunctorCongr_eq_eqToIso] using!
        overMapFunctor_assoc J G f.unop g.unop h.unop)
    (fun f ↦ by
      ext1
      simpa [overMapFunctorCongr_eq_eqToIso] using! overMapFunctor_id_comp J G f.unop)
    (fun f ↦ by
      ext1
      simpa [overMapFunctorCongr_eq_eqToIso] using! overMapFunctor_comp_id J G f.unop)

variable {J G}

section Stack

@[simp]
lemma stack_map_obj {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (P : (stack J G).obj a) :
    ((stack J G).map f).toFunctor.obj P = P.overMap f.as.unop :=
  rfl

@[simp]
lemma stack_map_map_hom_app {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) {P Q : (stack J G).obj a}
    (φ : P ⟶ Q) (Y : (Over b.as.unop)ᵒᵖ) :
    (((stack J G).map f).toFunctor.map φ).hom.app Y = φ.hom.app ((Over.map f.as.unop).op.obj Y) :=
  rfl

lemma stack_mapComp'_hom_app {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c)
    (h : f ≫ g = fg) (P : (stack J G).obj a) (Y : (Over c.as.unop)ᵒᵖ) :
    (((stack J G).mapComp' f g fg h).hom.toNatTrans.app P).hom.app Y =
      P.obj.map (Over.homMk (𝟙 Y.unop.left) (by subst h; simp) :
        (Over.map f.as.unop).obj ((Over.map g.as.unop).obj Y.unop) ⟶
          (Over.map fg.as.unop).obj Y.unop).op := by
  subst h
  rw [mapComp'_eq_mapComp]
  rfl

lemma stack_mapComp'_inv_app {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c)
    (h : f ≫ g = fg) (P : (stack J G).obj a) (Y : (Over c.as.unop)ᵒᵖ) :
    (((stack J G).mapComp' f g fg h).inv.toNatTrans.app P).hom.app Y =
      P.obj.map (Over.homMk (𝟙 Y.unop.left) (by subst h; simp) :
        (Over.map fg.as.unop).obj Y.unop ⟶
          (Over.map f.as.unop).obj ((Over.map g.as.unop).obj Y.unop)).op := by
  subst h
  rw [mapComp'_eq_mapComp]
  rfl

@[simp]
lemma stack_comp_hom {a : LocallyDiscrete Cᵒᵖ} {P Q R : (stack J G).obj a} (φ : P ⟶ Q)
    (ψ : Q ⟶ R) : Hom.hom (φ ≫ ψ) = φ.hom ≫ ψ.hom :=
  rfl

@[simp]
lemma stack_id_hom {a : LocallyDiscrete Cᵒᵖ} (P : (stack J G).obj a) : Hom.hom (𝟙 P) = 𝟙 _ :=
  rfl

lemma hom_app_congr {K : GrothendieckTopology C} {H : Cᵒᵖ ⥤ GrpCat.{w}} {P Q : Torsor K H}
    {φ ψ : P ⟶ Q} (h : φ = ψ) (W : Cᵒᵖ) (z : P.obj.obj W) : φ.hom.app W z = ψ.hom.app W z := by
  rw [h]

end Stack

section Descent

variable {S : C} {ι : Type t} {X : ι → C} {f : ∀ i, X i ⟶ S}

namespace StackDescent

variable (D : (stack J G).DescentData f)

lemma hom_eq {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    D.hom q f₁ f₂ hf₁ hf₂ = D.hom (f₁ ≫ f i₁) f₁ f₂ rfl (hf₂.trans hf₁.symm) := by
  subst hf₁
  rfl

lemma hom_congr {Y : C} {q q' : Y ⟶ S} (e : q = q') {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    D.hom q f₁ f₂ hf₁ hf₂ = D.hom q' f₁ f₂ (hf₁.trans e) (hf₂.trans e) := by
  subst e
  rfl

/-- The torsor `D.obj i` of a descent datum for the stack of torsors. -/
abbrev tors (i : ι) : Torsor (J.over (X i)) (PresheafOfGroups.over G (X i)) :=
  D.obj i

/-- The transfer map `D_{i₁}(a₁) → D_{i₂}(a₂)` of a descent datum `D` of torsors, for
`a₁ : Y ⟶ X i₁` and `a₂ : Y ⟶ X i₂` with `a₁ ≫ f i₁ = a₂ ≫ f i₂`: the component at the final
object of `C/Y` of the gluing isomorphism `D.hom`. -/
def transfer {Y : C} {i₁ i₂ : ι} (a₁ : Y ⟶ X i₁) (a₂ : Y ⟶ X i₂) (h : a₁ ≫ f i₁ = a₂ ≫ f i₂)
    (z : (tors D i₁).obj.obj (op (Over.mk a₁))) : (tors D i₂).obj.obj (op (Over.mk a₂)) :=
  (tors D i₂).obj.map (Over.homMk (𝟙 Y) (by simp) :
      Over.mk a₂ ⟶ (Over.map a₂).obj (Over.mk (𝟙 Y))).op
    ((D.hom (a₁ ≫ f i₁) a₁ a₂ rfl h.symm).hom.app (op (Over.mk (𝟙 Y)))
      ((tors D i₁).obj.map (Over.homMk (𝟙 Y) (by simp) :
        (Over.map a₁).obj (Over.mk (𝟙 Y)) ⟶ Over.mk a₁).op z))

/-- The components of the gluing isomorphisms of a descent datum are transfer maps. -/
lemma hom_hom_app {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (W : Over Y)
    (z : (tors D i₁).obj.obj (op (Over.mk (W.hom ≫ f₁)))) :
    (D.hom q f₁ f₂ hf₁ hf₂).hom.app (op W) z =
      transfer D (W.hom ≫ f₁) (W.hom ≫ f₂) (by simp [hf₁, hf₂]) z := by
  have H := hom_app_congr (D.pullHom_hom W.hom q (W.hom ≫ q) rfl f₁ f₂ hf₁ hf₂ (W.hom ≫ f₁)
    (W.hom ≫ f₂) rfl rfl) (op (Over.mk (𝟙 W.left)))
  simp only [LocallyDiscreteOpToCat.pullHom, stack_comp_hom, NatTrans.comp_app, types_comp_apply,
    stack_mapComp'_hom_app, stack_mapComp'_inv_app, stack_map_map_hom_app] at H
  let m : (Over.map W.hom).obj (Over.mk (𝟙 W.left)) ⟶ W := Over.homMk (𝟙 W.left) (by simp)
  have nat := NatTrans.naturality_apply (D.hom q f₁ f₂ hf₁ hf₂).hom m.op z
  unfold transfer
  rw [hom_congr D (show (W.hom ≫ f₁) ≫ f i₁ = W.hom ≫ q by simp [hf₁])]
  erw [← H, obj_map_map (D.obj i₁), obj_map_congr (D.obj i₁) _ ((Over.map f₁).map m) ?_ z, nat]
  · erw [obj_map_map, obj_map_map]
    refine (obj_map_eq_self (D.obj i₂) _ ?_ _).symm
    simp [m]
  · simp [m]

lemma transfer_self {Y : C} {i : ι} (a : Y ⟶ X i) (z : (tors D i).obj.obj (op (Over.mk a))) :
    transfer D a a rfl z = z := by
  unfold transfer
  rw [D.hom_self (a ≫ f i) a rfl]
  change (tors D i).obj.map _ ((tors D i).obj.map _ z) = z
  rw [obj_map_map]
  exact obj_map_eq_self _ _ (by simp) _

lemma transfer_trans {Y : C} {i₁ i₂ i₃ : ι} (a₁ : Y ⟶ X i₁) (a₂ : Y ⟶ X i₂) (a₃ : Y ⟶ X i₃)
    (h₁₂ : a₁ ≫ f i₁ = a₂ ≫ f i₂) (h₂₃ : a₂ ≫ f i₂ = a₃ ≫ f i₃)
    (z : (tors D i₁).obj.obj (op (Over.mk a₁))) :
    transfer D a₂ a₃ h₂₃ (transfer D a₁ a₂ h₁₂ z) = transfer D a₁ a₃ (h₁₂.trans h₂₃) z := by
  have H := hom_app_congr (D.hom_comp (a₁ ≫ f i₁) a₁ a₂ a₃ rfl h₁₂.symm
    (h₂₃.symm.trans h₁₂.symm)) (op (Over.mk (𝟙 Y)))
  simp only [stack_comp_hom, NatTrans.comp_app, types_comp_apply] at H
  unfold transfer
  rw [hom_congr D (show a₂ ≫ f i₂ = a₁ ≫ f i₁ from h₁₂.symm)]
  erw [obj_map_map (tors D i₂), obj_map_eq_self (tors D i₂) _ (by simp), H]

lemma transfer_naturality {Y Y' : C} (φ : Y' ⟶ Y) {i₁ i₂ : ι} (a₁ : Y ⟶ X i₁)
    (a₂ : Y ⟶ X i₂) (h : a₁ ≫ f i₁ = a₂ ≫ f i₂) (z : (tors D i₁).obj.obj (op (Over.mk a₁))) :
    (tors D i₂).obj.map (Over.homMk φ : Over.mk (φ ≫ a₂) ⟶ Over.mk a₂).op (transfer D a₁ a₂ h z) =
      transfer D (φ ≫ a₁) (φ ≫ a₂) (by simp [h])
        ((tors D i₁).obj.map (Over.homMk φ : Over.mk (φ ≫ a₁) ⟶ Over.mk a₁).op z) := by
  let n : Over.mk φ ⟶ Over.mk (𝟙 Y) := Over.homMk φ
  let k : (Over.map a₁).obj (Over.mk (𝟙 Y)) ⟶ Over.mk a₁ := Over.homMk (𝟙 Y) (by simp)
  have nat := NatTrans.naturality_apply (D.hom (a₁ ≫ f i₁) a₁ a₂ rfl h.symm).hom n.op
    ((tors D i₁).obj.map k.op z)
  have H := hom_hom_app D (a₁ ≫ f i₁) a₁ a₂ rfl h.symm (Over.mk φ)
    ((tors D i₁).obj.map (Over.homMk φ : Over.mk (φ ≫ a₁) ⟶ Over.mk a₁).op z)
  have e : (tors D i₁).obj.map ((Over.map a₁).map n).op ((tors D i₁).obj.map k.op z) =
      (tors D i₁).obj.map (Over.homMk φ : Over.mk (φ ≫ a₁) ⟶ Over.mk a₁).op z := by
    rw [obj_map_map]
    exact obj_map_congr _ _ _ (by simp [n, k]) _
  erw [← H, ← e, nat]
  unfold transfer
  erw [obj_map_map (tors D i₂)]
  exact obj_map_congr _ _ _ (by simp [n]) _

lemma transfer_smul {Y : C} {i₁ i₂ : ι} (a₁ : Y ⟶ X i₁) (a₂ : Y ⟶ X i₂)
    (h : a₁ ≫ f i₁ = a₂ ≫ f i₂) (g : (PresheafOfGroups.over G (X i₁)).obj (op (Over.mk a₁)))
    (z : (tors D i₁).obj.obj (op (Over.mk a₁))) :
    transfer D a₁ a₂ h (g • z) =
      (show (PresheafOfGroups.over G (X i₂)).obj (op (Over.mk a₂)) from g) •
        transfer D a₁ a₂ h z := by
  unfold transfer
  simp only [map_smul', hom_map_smul]
  congr 1
  simp

variable {D} in
/-- Morphisms of descent data commute with the transfer maps. -/
lemma transfer_hom {D' : (stack J G).DescentData f} (ψ : D ⟶ D') {Y : C} {i₁ i₂ : ι}
    (a₁ : Y ⟶ X i₁) (a₂ : Y ⟶ X i₂) (h : a₁ ≫ f i₁ = a₂ ≫ f i₂)
    (z : (tors D i₁).obj.obj (op (Over.mk a₁))) :
    transfer D' a₁ a₂ h ((ψ.hom i₁).hom.app (op (Over.mk a₁)) z) =
      (ψ.hom i₂).hom.app (op (Over.mk a₂)) (transfer D a₁ a₂ h z) := by
  let k₁ : (Over.map a₁).obj (Over.mk (𝟙 Y)) ⟶ Over.mk a₁ := Over.homMk (𝟙 Y) (by simp)
  let k₂ : Over.mk a₂ ⟶ (Over.map a₂).obj (Over.mk (𝟙 Y)) := Over.homMk (𝟙 Y) (by simp)
  have H := hom_app_congr (ψ.comm (a₁ ≫ f i₁) a₁ a₂ rfl h.symm) (op (Over.mk (𝟙 Y)))
    ((tors D i₁).obj.map k₁.op z)
  simp only [stack_comp_hom, NatTrans.comp_app, types_comp_apply, stack_map_map_hom_app] at H
  have n₁ := NatTrans.naturality_apply (ψ.hom i₁).hom k₁.op z
  have n₂ := NatTrans.naturality_apply (ψ.hom i₂).hom k₂.op
    ((D.hom (a₁ ≫ f i₁) a₁ a₂ rfl h.symm).hom.app (op (Over.mk (𝟙 Y)))
      ((tors D i₁).obj.map k₁.op z))
  unfold transfer
  erw [← n₁, H, n₂]
  rfl

lemma toDescentData_obj_hom_hom_app (P : Torsor (J.over S) (PresheafOfGroups.over G S)) {Y : C}
    (q : Y ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (W : (Over Y)ᵒᵖ) :
    ((((stack J G).toDescentData f).obj P).hom q f₁ f₂ hf₁ hf₂).hom.app W =
      P.obj.map (Over.homMk (𝟙 W.unop.left) (by simp [hf₁, hf₂]) :
        (Over.map (f i₂)).obj ((Over.map f₂).obj W.unop) ⟶
          (Over.map (f i₁)).obj ((Over.map f₁).obj W.unop)).op := by
  change ((((stack J G).mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc
      (by rw [← hf₁]; rfl)).inv.toNatTrans.app (P : (stack J G).obj (.mk (op S))) ≫
    ((stack J G).mapComp' (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc
      (by rw [← hf₂]; rfl)).hom.toNatTrans.app (P : (stack J G).obj (.mk (op S))))).hom.app W = _
  rw [stack_comp_hom, NatTrans.comp_app, stack_mapComp'_inv_app, stack_mapComp'_hom_app,
    ← Functor.map_comp, ← op_comp]
  congr 2
  ext
  simp

/-- The transfer maps of the descent datum of a torsor are restrictions. -/
lemma transfer_toDescentData (P : Torsor (J.over S) (PresheafOfGroups.over G S)) {Y : C}
    {i₁ i₂ : ι} (a₁ : Y ⟶ X i₁) (a₂ : Y ⟶ X i₂) (h : a₁ ≫ f i₁ = a₂ ≫ f i₂)
    (z : P.obj.obj (op (Over.mk (a₁ ≫ f i₁)))) :
    transfer (((stack J G).toDescentData f).obj P) a₁ a₂ h z =
      P.obj.map (Over.homMk (𝟙 Y) (by simp [h]) : Over.mk (a₂ ≫ f i₂) ⟶ Over.mk (a₁ ≫ f i₁)).op
        z := by
  unfold transfer
  erw [toDescentData_obj_hom_hom_app, obj_map_map P, obj_map_map P]
  exact obj_map_congr _ _ _ (by simp) _

end StackDescent

variable (f) in
/-- The objects `Over.mk (f i)` of `C/S` cover the final object for a covering family `f`. -/
lemma coversTop_over (hf : Sieve.ofArrows X f ∈ J S) :
    (J.over S).CoversTop (fun i ↦ Over.mk (f i)) := by
  intro T
  rw [GrothendieckTopology.mem_over_iff]
  refine J.superset_covering ?_ (J.pullback_stable T.hom hf)
  intro Z g hg
  obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  rw [Sieve.overEquiv_iff]
  exact ⟨i, ⟨Over.homMk a ha.symm⟩⟩

/-- The identification `V ≅ (Over.map (f i)).obj (Over.mk a.left)` for `a : V ⟶ Over.mk (f i)`. -/
abbrev toOverMap {V : Over S} {i : ι} (a : V ⟶ Over.mk (f i)) :
    V ⟶ (Over.map (f i)).obj (Over.mk a.left) :=
  Over.homMk (𝟙 V.left) (by simpa using Over.w a)

/-- The identification `(Over.map (f i)).obj (Over.mk a.left) ≅ V` for `a : V ⟶ Over.mk (f i)`. -/
abbrev fromOverMap {V : Over S} {i : ι} (a : V ⟶ Over.mk (f i)) :
    (Over.map (f i)).obj (Over.mk a.left) ⟶ V :=
  Over.homMk (𝟙 V.left) (by simpa using (Over.w a).symm)

lemma hom_app_eq_of_left_id {U : C} {P Q : Torsor (J.over U) (PresheafOfGroups.over G U)}
    (φ : P ⟶ Q) {V M : Over U} (e : V ⟶ M) (e' : M ⟶ V) (he : e.left ≫ e'.left = 𝟙 _)
    (w : P.obj.obj (op V)) :
    φ.hom.app (op V) w = Q.obj.map e.op (φ.hom.app (op M) (P.obj.map e'.op w)) := by
  rw [NatTrans.naturality_apply φ.hom e'.op w, obj_map_map, obj_map_eq_self _ _ (by simpa using he)]

variable (f) in
/-- Descent of morphisms for torsors: morphisms of torsors which agree after restriction to a
covering family are equal. -/
lemma hom_ext_of_covering (hf : Sieve.ofArrows X f ∈ J S)
    {P Q : Torsor (J.over S) (PresheafOfGroups.over G S)} {φ ψ : P ⟶ Q}
    (h : ∀ i, (overMapFunctor J G (f i)).map φ = (overMapFunctor J G (f i)).map ψ) : φ = ψ := by
  ext T x
  refine (Q.isSheaf _ (coversTop_over f hf T.unop)).isSeparatedFor.ext fun V g hg ↦ ?_
  obtain ⟨i, ⟨a⟩⟩ := hg
  have hi := hom_app_congr (h i) (op (Over.mk a.left))
  simp only [TypeCat.Fun.toFun_apply]
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply,
    hom_app_eq_of_left_id φ (toOverMap a) (fromOverMap a) (by simp),
    hom_app_eq_of_left_id ψ (toOverMap a) (fromOverMap a) (by simp)]
  exact congrArg _ (hi _)

section Full

variable {P Q : Torsor (J.over S) (PresheafOfGroups.over G S)}
  (ψ : ((stack J G).toDescentData f).obj P ⟶ ((stack J G).toDescentData f).obj Q)

/-- The local values of the morphism of torsors glued from a morphism of descent data. -/
def fullAux {T : Over S} (x : P.obj.obj (op T)) ⦃V : Over S⦄ (t : V ⟶ T) (i : ι)
    (a : V ⟶ Over.mk (f i)) : Q.obj.obj (op V) :=
  Q.obj.map (toOverMap a).op
    ((ψ.hom i).hom.app (op (Over.mk a.left)) (P.obj.map (fromOverMap a ≫ t).op x))

lemma fullAux_indep {T : Over S} (x : P.obj.obj (op T)) ⦃V : Over S⦄ (t : V ⟶ T) (i j : ι)
    (a : V ⟶ Over.mk (f i)) (b : V ⟶ Over.mk (f j)) :
    fullAux ψ x t i a = fullAux ψ x t j b := by
  have h : a.left ≫ f i = b.left ≫ f j := by simpa using (Over.w a).trans (Over.w b).symm
  have H := StackDescent.transfer_hom ψ a.left b.left h (P.obj.map (fromOverMap a ≫ t).op x)
  rw [StackDescent.transfer_toDescentData, StackDescent.transfer_toDescentData] at H
  erw [obj_map_map P, obj_map_congr P _ (fromOverMap b ≫ t) (by simp) x] at H
  unfold fullAux
  erw [← H, obj_map_map Q]
  exact obj_map_congr _ _ _ (by simp) _

lemma fullAux_naturality {T : Over S} (x : P.obj.obj (op T)) ⦃V V' : Over S⦄ (φ : V' ⟶ V)
    (t : V ⟶ T) (i : ι) (a : V ⟶ Over.mk (f i)) :
    Q.obj.map φ.op (fullAux ψ x t i a) = fullAux ψ x (φ ≫ t) i (φ ≫ a) := by
  let n : Over.mk (φ ≫ a).left ⟶ Over.mk a.left := Over.homMk φ.left (by simp)
  have nat := NatTrans.naturality_apply (ψ.hom i).hom n.op (P.obj.map (fromOverMap a ≫ t).op x)
  have e : P.obj.map ((Over.map (f i)).map n).op (P.obj.map (fromOverMap a ≫ t).op x) =
      P.obj.map (fromOverMap (φ ≫ a) ≫ φ ≫ t).op x := by
    rw [obj_map_map]
    exact obj_map_congr _ _ _ (by simp [n]) _
  unfold fullAux
  erw [← e, nat, obj_map_map Q, obj_map_map Q]
  exact obj_map_congr _ _ _ (by simp [n]) _

lemma fullAux_smul {T : Over S} (x : P.obj.obj (op T)) (g : (PresheafOfGroups.over G S).obj (op T))
    ⦃V : Over S⦄ (t : V ⟶ T) (i : ι) (a : V ⟶ Over.mk (f i)) :
    fullAux ψ (g • x) t i a = (PresheafOfGroups.over G S).map t.op g • fullAux ψ x t i a := by
  unfold fullAux
  simp only [map_smul', hom_map_smul]
  congr 1
  rw [← GrpCat.comp_apply, ← Functor.map_comp, ← op_comp,
    show toOverMap a ≫ fromOverMap a ≫ t = t by ext; simp]

variable (hf : Sieve.ofArrows X f ∈ J S)
include hf

lemma existsUnique_full {T : Over S} (x : P.obj.obj (op T)) :
    ∃! y : Q.obj.obj (op T), ∀ ⦃V : Over S⦄ (t : V ⟶ T) (i : ι) (a : V ⟶ Over.mk (f i)),
      Q.obj.map t.op y = fullAux ψ x t i a :=
  (coversTop_over f hf).existsUnique_glue Q.isSheaf _ (fullAux_indep ψ x) (fullAux_naturality ψ x)

/-- The morphism of torsors glued from a morphism of descent data. -/
noncomputable def fullHom : P ⟶ Q where
  hom :=
    { app T := ↾fun x ↦ (existsUnique_full ψ hf (T := T.unop) x).exists.choose
      naturality T T' g := by
        ext x
        refine (existsUnique_full ψ hf (T := T'.unop) (P.obj.map g x)).unique
          (existsUnique_full ψ hf (P.obj.map g x)).exists.choose_spec ?_
        intro V t i a
        change Q.obj.map t.op (Q.obj.map g (existsUnique_full ψ hf (T := T.unop) x).exists.choose) =
          _
        rw [← Functor.map_comp_apply, show g ≫ t.op = (t ≫ g.unop).op from rfl,
          (existsUnique_full ψ hf (T := T.unop) x).exists.choose_spec (t ≫ g.unop) i a]
        unfold fullAux
        rw [← Category.assoc, op_comp, Functor.map_comp_apply]
        rfl }
  map_smul T g x := by
    refine (existsUnique_full ψ hf (T := T.unop) (g • x)).unique
      (existsUnique_full ψ hf (g • x)).exists.choose_spec ?_
    intro V t i a
    change Q.obj.map t.op (g • (existsUnique_full ψ hf (T := T.unop) x).exists.choose) = _
    rw [map_smul', (existsUnique_full ψ hf (T := T.unop) x).exists.choose_spec t i a, fullAux_smul]

lemma fullHom_hom_app {T : Over S} (x : P.obj.obj (op T)) ⦃V : Over S⦄ (t : V ⟶ T) (i : ι)
    (a : V ⟶ Over.mk (f i)) :
    Q.obj.map t.op ((fullHom ψ hf).hom.app (op T) x) = fullAux ψ x t i a :=
  (existsUnique_full ψ hf x).exists.choose_spec t i a

lemma toDescentData_map_fullHom : ((stack J G).toDescentData f).map (fullHom ψ hf) = ψ := by
  ext i : 1
  apply Torsor.hom_ext
  ext Z w
  have H := fullHom_hom_app ψ hf w (𝟙 _) i (Over.homMk Z.unop.hom)
  rw [op_id, Functor.map_id_apply] at H
  simp only [TypeCat.Fun.toFun_apply]
  erw [H]
  unfold fullAux
  erw [obj_map_eq_self Q _ (by simp), obj_map_eq_self P _ (by simp)]
  rfl

end Full

variable (f) in
lemma full_toDescentData (hf : Sieve.ofArrows X f ∈ J S) :
    ((stack J G).toDescentData f).Full :=
  ⟨fun ψ ↦ ⟨fullHom ψ hf, toDescentData_map_fullHom ψ hf⟩⟩

variable (f) in
lemma faithful_toDescentData (hf : Sieve.ofArrows X f ∈ J S) :
    ((stack J G).toDescentData f).Faithful :=
  ⟨fun {_ _} _ _ h ↦ hom_ext_of_covering f hf fun i ↦ congrArg (fun φ ↦ φ.hom i) h⟩

end Descent

variable (J G) in
/-- Descent of morphisms for torsors: the stack of torsors is a prestack (Giraud III 1.4.1). -/
instance isPrestack_stack : (stack J G).IsPrestack J :=
  Pseudofunctor.IsPrestack.of_isPrestackFor fun S R hR ↦ by
    have hf : Sieve.ofArrows _ (fun g : R.arrows.category ↦ g.obj.hom) ∈ J S := by
      rwa [Sieve.ofArrows_category]
    have := full_toDescentData (G := G) _ hf
    have := faithful_toDescentData (G := G) _ hf
    exact ⟨⟨.ofFullyFaithful _⟩⟩

end CategoryTheory.Torsor
