/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Monoidal.Grp
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Sites.LocallySurjective
import SGA.Foundations.Etale.Points
import SGA.Foundations.Etale.Torsor

/-!
# Inverse images of sheaves of groups and of torsors

Let `L : Sh(C, J) ⥤ Sh(D, K)` be a functor between categories of sheaves of sets which preserves
finite limits and epimorphisms, for instance the inverse image functor of a morphism of sites
(such as `Scheme.etalePullback h` for a morphism of schemes `h`). Since `L` preserves finite
products, it maps group objects to group objects and actions to actions
(`MonObjAction.map`). Hence:

* a sheaf of groups `G` on `C` (a group object `PresheafOfGroups.toSheaf G` in the category of
  sheaves of sets) has an image `PresheafOfGroups.map L G`, a sheaf of groups on `D` whose
  underlying sheaf of sets is `L(G)`;
* a `G`-torsor `P` has an image `Torsor.map L P`, a torsor under `L(G)` with underlying sheaf
  `L(P)`: the conditions that `G × P ⟶ P × P`, `(g, x) ↦ (g • x, x)` is an isomorphism and that
  `P ⟶ *` is an epimorphism (`Torsor.isIso_lift_action_smul_snd`, `Torsor.epi_toUnit`) are
  preserved by `L`, and they characterize torsors (`Torsor.ofAction`);
* this induces `H1.mapSheaf L : H¹(C, G) ⟶ H¹(D, L(G))`.

For a morphism of schemes `h : X' ⟶ X` this gives the inverse image `h^* G` of a sheaf of groups
on the small étale site (`Scheme.etalePullbackGroup`), the inverse image `h^* P` of torsors
(`Scheme.etalePullbackTorsor`) and the map `H¹(X_et, G) ⟶ H¹(X'_et, h^* G)`
(`Scheme.H1.etalePullback`).

## References

* [J. Giraud, *Cohomologie non abélienne*, III 1.4.6 and V 1.5][giraud1971]
* [SGA 4, Exposé IV, 5.1][sga4]
-/

universe w v u v' u'

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Limits MonObj

-- The category of sheaves has two monoidal structures which are not reducibly defeq: the one of
-- the full monoidal subcategory, and the one underlying its cartesian monoidal structure. We use
-- the latter, as group objects are defined for cartesian monoidal categories.
attribute [local instance high] SemiCartesianMonoidalCategory.toMonoidalCategory

namespace CategoryTheory

section Action

variable {D : Type*} [Category* D] [CartesianMonoidalCategory D]
  {E : Type*} [Category* E] [CartesianMonoidalCategory E]

/-- A left action of a monoid object `M` on an object `X` of a cartesian monoidal category. -/
structure MonObjAction (M : D) [MonObj M] (X : D) where
  /-- The action morphism. -/
  smul : M ⊗ X ⟶ X
  one_smul : η ▷ X ≫ smul = (λ_ X).hom
  mul_smul : μ ▷ X ≫ smul = (α_ M M X).hom ≫ M ◁ smul ≫ smul

open Functor.LaxMonoidal Functor.OplaxMonoidal in
/-- The image of an action under a monoidal functor. -/
def MonObjAction.map (F : D ⥤ E) [F.Monoidal] {M X : D} [MonObj M] (a : MonObjAction M X) :
    letI := Functor.monObjObj (F := F) (X := M)
    MonObjAction (F.obj M) (F.obj X) :=
  letI := Functor.monObjObj (F := F) (X := M)
  { smul := Functor.LaxMonoidal.μ F M X ≫ F.map a.smul
    one_smul := by
      rw [Functor.obj.η_def, comp_whiskerRight, Category.assoc,
        Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp, a.one_smul,
        Functor.LaxMonoidal.left_unitality]
    mul_smul := by
      rw [Functor.obj.μ_def, comp_whiskerRight, Category.assoc,
        Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp, a.mul_smul]
      simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc,
        Functor.LaxMonoidal.μ_natural_right_assoc]
      rw [← Functor.LaxMonoidal.associativity_assoc] }

end Action

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace PresheafOfGroups

variable (G : Cᵒᵖ ⥤ GrpCat.{w}) (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))

/-- The underlying sheaf of sets of a sheaf of groups. -/
def toSheaf : Sheaf J (Type w) :=
  ⟨G ⋙ CategoryTheory.forget GrpCat, (isSheaf_iff_isSheaf_of_type _ _).2 hG⟩

/-- The group object structure on the underlying sheaf of sets of a sheaf of groups. -/
instance grpObj : GrpObj (toSheaf G hG) where
  one := ObjectProperty.homMk
    { app U := ↾fun _ ↦ (1 : G.obj U)
      naturality U V f := by
        ext x
        exact (map_one (G.map f).hom).symm }
  mul := ObjectProperty.homMk
    { app U := ↾fun (x : G.obj U × G.obj U) ↦ (x.1 * x.2 : G.obj U)
      naturality U V f := by
        ext ⟨a, b⟩
        exact (map_mul (G.map f).hom (show G.obj U from a) b).symm }
  inv := ObjectProperty.homMk
    { app U := ↾fun (x : G.obj U) ↦ (x⁻¹ : G.obj U)
      naturality U V f := by
        ext x
        exact (map_inv (G.map f).hom (show G.obj U from x)).symm }
  one_mul := by
    ext U x
    exact _root_.one_mul (M := G.obj U) x.2
  mul_one := by
    ext U x
    exact _root_.mul_one (M := G.obj U) x.1
  mul_assoc := by
    ext U x
    exact _root_.mul_assoc (G := G.obj U) x.1.1 x.1.2 x.2
  left_inv := by
    ext U x
    exact inv_mul_cancel (G := G.obj U) x
  right_inv := by
    ext U x
    exact mul_inv_cancel (G := G.obj U) x

end PresheafOfGroups

namespace Sheaf

variable (F : Sheaf J (Type w)) [GrpObj F]

omit [GrpObj F] in
lemma hom_app_congr {F' : Sheaf J (Type w)} {f g : F ⟶ F'} (h : f = g) (U : Cᵒᵖ) (x : F.obj.obj U) :
    f.hom.app U x = g.hom.app U x := by
  rw [h]

/-- The group structure on the sections of a group object in sheaves of sets. -/
@[reducible]
def groupSections (U : Cᵒᵖ) : Group (F.obj.obj U) where
  mul a b := (μ[F]).hom.app U (a, b)
  one := (η[F]).hom.app U PUnit.unit
  inv a := (ι[F]).hom.app U a
  mul_assoc a b c := by
    have := hom_app_congr _ (MonObj.mul_assoc F) U ((a, b), c)
    exact this
  one_mul a := by
    have := hom_app_congr _ (MonObj.one_mul F) U (PUnit.unit, a)
    exact this
  mul_one a := by
    have := hom_app_congr _ (MonObj.mul_one F) U (a, PUnit.unit)
    exact this
  inv_mul_cancel a := by
    have := hom_app_congr _ (GrpObj.left_inv F) U a
    exact this

lemma mul_def (U : Cᵒᵖ) (a b : F.obj.obj U) :
    letI := groupSections F U
    a * b = (μ[F]).hom.app U (a, b) :=
  rfl

/-- The presheaf of groups of sections of a group object in sheaves of sets. -/
def grpPresheaf : Cᵒᵖ ⥤ GrpCat.{w} where
  obj U := letI := groupSections F U; GrpCat.of (F.obj.obj U)
  map {U V} f := letI := groupSections F U; letI := groupSections F V
    GrpCat.ofHom
      { toFun := F.obj.map f
        map_one' := (NatTrans.naturality_apply (η[F]).hom f PUnit.unit).symm
        map_mul' a b := (NatTrans.naturality_apply (μ[F]).hom f
          (show (F ⊗ F).obj.obj U from (a, b))).symm }
  map_id U := GrpCat.ext fun a ↦ Functor.map_id_apply F.obj U a
  map_comp f g := GrpCat.ext fun a ↦ Functor.map_comp_apply F.obj f g a

lemma grpPresheaf_comp_forget : grpPresheaf F ⋙ CategoryTheory.forget GrpCat = F.obj :=
  rfl

lemma isSheaf_grpPresheaf :
    Presieve.IsSheaf J (grpPresheaf F ⋙ CategoryTheory.forget GrpCat) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 F.property

end Sheaf

namespace Torsor

variable {G : Cᵒᵖ ⥤ GrpCat.{w}} (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
  (P : Torsor J G)

/-- The action of `G` on a `G`-torsor, as a morphism of sheaves of sets. -/
def action : MonObjAction (PresheafOfGroups.toSheaf G hG) P.toSheaf where
  smul := ObjectProperty.homMk
    { app U := ↾fun (x : G.obj U × P.obj.obj U) ↦ (x.1 • x.2 : P.obj.obj U)
      naturality U V f := by
        ext ⟨g, x⟩
        exact (P.map_smul' f g x).symm }
  one_smul := by
    ext U ⟨⟨⟩, x⟩
    exact _root_.one_smul (G.obj U) (show P.obj.obj U from x)
  mul_smul := by
    ext U ⟨⟨g, h⟩, x⟩
    exact (smul_smul (show G.obj U from g) h (show P.obj.obj U from x)).symm

/-- The inverse of `(g, x) ↦ (g • x, x)` for a torsor. -/
noncomputable def diffHom : P.toSheaf ⊗ P.toSheaf ⟶ PresheafOfGroups.toSheaf G hG ⊗ P.toSheaf :=
  ObjectProperty.homMk
    { app U := ↾fun (x : P.obj.obj U × P.obj.obj U) ↦
        ((P.diff x.2 x.1, x.2) : G.obj U × P.obj.obj U)
      naturality U V f := by
        ext ⟨y, x⟩
        exact _root_.Prod.ext (P.map_diff f x y).symm rfl }

lemma isIso_lift_action_smul_snd :
    IsIso (lift (P.action hG).smul (snd (PresheafOfGroups.toSheaf G hG) P.toSheaf)) := by
  refine ⟨⟨P.diffHom hG, ?_, ?_⟩⟩
  · apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    refine ConcreteCategory.hom_ext _ _ fun ⟨g, x⟩ ↦ ?_
    change ((P.diff (show P.obj.obj U from x) ((show G.obj U from g) • (show P.obj.obj U from x)),
      x) : G.obj U × P.obj.obj U) = (g, x)
    rw [P.diff_smul_self]
    rfl
  · apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    refine ConcreteCategory.hom_ext _ _ fun ⟨y, x⟩ ↦ ?_
    change ((P.diff (show P.obj.obj U from x) (show P.obj.obj U from y) •
      (show P.obj.obj U from x), x) : P.obj.obj U × P.obj.obj U) = (y, x)
    rw [P.diff_smul]
    rfl

lemma epi_toUnit [HasSheafify J (Type w)] : Epi (toUnit P.toSheaf) := by
  rw [← Sheaf.isLocallySurjective_iff_epi]
  refine ⟨fun {U} _ ↦ J.superset_covering (fun V f hf ↦ ?_) (P.nonemptySieve_mem U)⟩
  exact ⟨hf.some, rfl⟩

variable {F : Sheaf J (Type w)} [GrpObj F] {X : Sheaf J (Type w)} (a : MonObjAction F X)

omit hG P [GrpObj F] in
lemma bijective_hom_app_of_isIso {Y Z : Sheaf J (Type w)} (φ : Y ⟶ Z) [IsIso φ] (U : Cᵒᵖ) :
    Function.Bijective (φ.hom.app U) := by
  rw [← isIso_iff_bijective]
  have : IsIso φ.hom := (inferInstance : IsIso ((sheafToPresheaf J (Type w)).map φ))
  infer_instance

omit hG P in
/-- The torsor under the sections of a group object `F` in sheaves of sets given by an action of
`F` on `X` such that `(g, x) ↦ (g • x, x)` is an isomorphism and `X ⟶ *` is an epimorphism. -/
noncomputable def ofAction [HasSheafify J (Type w)] (ha : IsIso (lift a.smul (snd F X)))
    (hX : Epi (toUnit X)) : Torsor J (Sheaf.grpPresheaf F) where
  obj := X.obj
  isSheaf := (isSheaf_iff_isSheaf_of_type _ _).1 X.property
  smul U g x := a.smul.hom.app U (show (F ⊗ X).obj.obj U from (g, x))
  one_smul U x :=
    Sheaf.hom_app_congr _ a.one_smul U (show (𝟙_ _ ⊗ X).obj.obj U from (PUnit.unit, x))
  mul_smul U g h x := (Sheaf.hom_app_congr _ a.mul_smul U
    (show ((F ⊗ F) ⊗ X).obj.obj U from ((g, h), x)))
  map_smul f g x :=
    (NatTrans.naturality_apply a.smul.hom f (show (F ⊗ X).obj.obj _ from (g, x))).symm
  existsUnique_smul U x y := by
    obtain ⟨⟨g, x'⟩, hgx⟩ := (bijective_hom_app_of_isIso (lift a.smul (snd F X)) U).2
      (show (X ⊗ X).obj.obj U from (y, x))
    have hx' : x' = x := congr_arg _root_.Prod.snd hgx
    subst hx'
    refine ⟨g, congr_arg _root_.Prod.fst hgx, fun g' hg' ↦ ?_⟩
    have := (bijective_hom_app_of_isIso (lift a.smul (snd F X)) U).1
      (a₁ := show (F ⊗ X).obj.obj U from (g', x')) (a₂ := (g, x'))
      (_root_.Prod.ext (hg'.trans (congr_arg _root_.Prod.fst hgx).symm) rfl)
    exact congr_arg _root_.Prod.fst this
  locallyNonempty U := by
    have := (Sheaf.isLocallySurjective_iff_epi (toUnit X)).2 hX
    refine ⟨_, Presheaf.imageSieve_mem J (toUnit X).hom
      (show (𝟙_ (Sheaf J (Type w))).obj.obj (op U) from PUnit.unit), fun V f hf ↦ ?_⟩
    obtain ⟨t, -⟩ := hf
    exact ⟨t⟩

end Torsor

section Map

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]

namespace PresheafOfGroups

variable (G : Cᵒᵖ ⥤ GrpCat.{w}) (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))

/-- The group object structure on the image of a sheaf of groups under a functor preserving
finite limits. -/
@[reducible]
noncomputable def mapGrpObj : GrpObj (L.obj (toSheaf G hG)) :=
  letI := Functor.Monoidal.ofChosenFiniteProducts L
  Functor.grpObjObj

/-- The image of a sheaf of groups under a functor `L` between categories of sheaves of sets
which preserves finite limits: the sheaf of groups `L(G)`. -/
noncomputable def map : Dᵒᵖ ⥤ GrpCat.{w} :=
  letI := mapGrpObj L G hG
  Sheaf.grpPresheaf (L.obj (toSheaf G hG))

lemma isSheaf_map : Presieve.IsSheaf K (map L G hG ⋙ CategoryTheory.forget GrpCat) :=
  letI := mapGrpObj L G hG
  Sheaf.isSheaf_grpPresheaf _

end PresheafOfGroups

namespace Torsor

variable {G : Cᵒᵖ ⥤ GrpCat.{w}} (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
  [L.PreservesEpimorphisms] [HasSheafify J (Type w)] [HasSheafify K (Type w)]

/-- The image of a torsor under a functor `L` between categories of sheaves of sets which
preserves finite limits and epimorphisms (for instance the inverse image along a morphism of
sites): a torsor under `L(G)`. -/
noncomputable def map (P : Torsor J G) : Torsor K (PresheafOfGroups.map L G hG) :=
  letI := Functor.Monoidal.ofChosenFiniteProducts L
  letI := PresheafOfGroups.mapGrpObj L G hG
  ofAction ((P.action hG).map L) (by
    have := P.isIso_lift_action_smul_snd hG
    have e : lift (Functor.LaxMonoidal.μ L _ _ ≫ L.map (P.action hG).smul)
        (snd (L.obj (PresheafOfGroups.toSheaf G hG)) (L.obj P.toSheaf)) =
          Functor.LaxMonoidal.μ L _ _ ≫
            L.map (lift (P.action hG).smul (snd (PresheafOfGroups.toSheaf G hG) P.toSheaf)) ≫
              inv (Functor.LaxMonoidal.μ L P.toSheaf P.toSheaf) := by
      rw [← Functor.Monoidal.lift_μ, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        comp_lift, Functor.Monoidal.μ_snd]
    exact e ▸ inferInstance) (by
    have := P.epi_toUnit
    have e : toUnit (L.obj P.toSheaf) = L.map (toUnit P.toSheaf) ≫ inv (Functor.LaxMonoidal.ε L) :=
      by rw [← Functor.Monoidal.toUnit_ε_assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance)

/-- The image under `L` of a morphism of torsors. -/
noncomputable def mapHom {P Q : Torsor J G} (φ : P ⟶ Q) : map L hG P ⟶ map L hG Q where
  hom := (L.map (ObjectProperty.homMk φ.hom : P.toSheaf ⟶ Q.toSheaf)).hom
  map_smul U g x := by
    let := Functor.Monoidal.ofChosenFiniteProducts L
    let := PresheafOfGroups.mapGrpObj L G hG
    let φ' : P.toSheaf ⟶ Q.toSheaf := ObjectProperty.homMk φ.hom
    have e : (P.action hG).smul ≫ φ' =
        (PresheafOfGroups.toSheaf G hG) ◁ φ' ≫ (Q.action hG).smul := by
      ext U ⟨g, x⟩
      exact φ.map_smul U g x
    have e' : ((P.action hG).map L).smul ≫ L.map φ' =
        L.obj (PresheafOfGroups.toSheaf G hG) ◁ L.map φ' ≫
          ((Q.action hG).map L).smul := by
      simp only [MonObjAction.map, Category.assoc]
      rw [← L.map_comp, e, L.map_comp]
      exact (Functor.LaxMonoidal.μ_natural_right_assoc L _ φ' _).symm
    exact Sheaf.hom_app_congr _ e' U (show _ ⊗ _ from (g, x))

end Torsor

namespace H1

variable {G : Cᵒᵖ ⥤ GrpCat.{w}} (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
  [L.PreservesEpimorphisms] [HasSheafify J (Type w)] [HasSheafify K (Type w)]

/-- The map `H¹(J, G) ⟶ H¹(K, L(G))` induced by a functor `L` between categories of sheaves of
sets preserving finite limits and epimorphisms. -/
noncomputable def mapSheaf : H1 J G → H1 K (PresheafOfGroups.map L G hG) :=
  _root_.Quotient.map (Torsor.map L hG) fun _ _ ⟨e⟩ ↦
    ⟨@asIso _ _ _ _ (Torsor.mapHom L hG e.hom) (Torsor.isIso _)⟩

@[simp]
lemma mapSheaf_class (P : Torsor J G) : mapSheaf L hG P.class = (Torsor.map L hG P).class :=
  rfl

end H1

end Map

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X X' : Scheme.{u}} (h : X' ⟶ X) {G : X.Etaleᵒᵖ ⥤ GrpCat.{u}}
  (hG : Presieve.IsSheaf X.smallEtaleTopology (G ⋙ CategoryTheory.forget GrpCat))

/-- The inverse image `h^* G` of a sheaf of groups on the small étale site along a morphism of
schemes `h : X' ⟶ X`. -/
noncomputable abbrev etalePullbackGroup : X'.Etaleᵒᵖ ⥤ GrpCat.{u} :=
  PresheafOfGroups.map (etalePullback h) G hG

lemma isSheaf_etalePullbackGroup :
    Presieve.IsSheaf X'.smallEtaleTopology
      (etalePullbackGroup h hG ⋙ CategoryTheory.forget GrpCat) :=
  PresheafOfGroups.isSheaf_map _ _ _

/-- The inverse image `h^* P` of a torsor on the small étale site along a morphism of schemes
`h : X' ⟶ X`: a torsor under `h^* G` whose underlying sheaf of sets is `h^* P`. -/
noncomputable abbrev etalePullbackTorsor (P : Torsor X.smallEtaleTopology G) :
    Torsor X'.smallEtaleTopology (etalePullbackGroup h hG) :=
  Torsor.map (etalePullback h) hG P

lemma etalePullbackTorsor_obj (P : Torsor X.smallEtaleTopology G) :
    (etalePullbackTorsor h hG P).obj = ((etalePullback h).obj P.toSheaf).obj :=
  rfl

/-- The map `H¹(X_et, G) ⟶ H¹(X'_et, h^* G)` induced by the inverse image of torsors. -/
noncomputable abbrev H1.etalePullback :
    H1 X.smallEtaleTopology G → H1 X'.smallEtaleTopology (etalePullbackGroup h hG) :=
  H1.mapSheaf (Scheme.etalePullback h) hG

end AlgebraicGeometry.Scheme
