/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.CategoryTheory.Sites.Over

/-!
# Torsors under a sheaf of groups on a site

Let `G : Cᵒᵖ ⥤ GrpCat` be a presheaf of groups on a site `(C, J)`. A (left) `G`-torsor is a
sheaf of sets `P` with an action of `G` such that each `G(U)` acts simply transitively on
`P(U)` whenever `P(U)` is nonempty, and such that `P` has sections locally
(`CategoryTheory.Torsor`).

* Morphisms of torsors are the `G`-equivariant morphisms of sheaves; they are all isomorphisms
  (`Torsor.isIso`), so torsors form a groupoid.
* When `G` is a sheaf, `G` acting on itself by left translations is the trivial torsor
  `Torsor.trivial`, and a torsor is trivial if and only if it has a global section
  (`Torsor.nonempty_iso_trivial_iff`).
* Torsors can be restricted along continuous and cocontinuous functors
  (`Torsor.restrict`), for instance along `Over.forget U : Over U ⥤ C` (`Torsor.over`) and
  along `Over.map f`.
* `H1 J G` is the pointed set of isomorphism classes of `G`-torsors, and `H1.restrict` its
  functoriality.

## References

* [J. Giraud, *Cohomologie non abélienne*, III 1.4][giraud1971]
* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
-/

universe w v' u' v u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w})

/-- A (left) torsor under a presheaf of groups `G` on the site `(C, J)` (Giraud III 1.4.1): a
sheaf of sets `P` with an action of `G` which is simply transitive on each `P(U)`, and which is
locally nonempty. -/
structure Torsor where
  /-- The underlying sheaf of sets. -/
  obj : Cᵒᵖ ⥤ Type w
  isSheaf : Presieve.IsSheaf J obj
  /-- The action of `G`. -/
  smul (U : Cᵒᵖ) : G.obj U → obj.obj U → obj.obj U
  one_smul (U : Cᵒᵖ) (x : obj.obj U) : smul U 1 x = x
  mul_smul (U : Cᵒᵖ) (g h : G.obj U) (x : obj.obj U) : smul U (g * h) x = smul U g (smul U h x)
  map_smul {U V : Cᵒᵖ} (f : U ⟶ V) (g : G.obj U) (x : obj.obj U) :
    obj.map f (smul U g x) = smul V (G.map f g) (obj.map f x)
  existsUnique_smul (U : Cᵒᵖ) (x y : obj.obj U) : ∃! g : G.obj U, smul U g x = y
  locallyNonempty (U : C) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Nonempty (obj.obj (op V))

/-- The sieve of morphisms `V ⟶ U` such that `F(V)` is nonempty, for a presheaf of sets `F`. -/
def _root_.CategoryTheory.Functor.nonemptySieve' (F : Cᵒᵖ ⥤ Type w) (U : C) : Sieve U where
  arrows V _ := Nonempty (F.obj (op V))
  downward_closed {_ _} _ h g := ⟨F.map g.op h.some⟩

namespace Torsor

variable {J G}

instance (P : Torsor J G) (U : Cᵒᵖ) : MulAction (G.obj U) (P.obj.obj U) where
  smul := P.smul U
  one_smul := P.one_smul U
  mul_smul := P.mul_smul U

section Action

variable (P : Torsor J G)

lemma smul_def {U : Cᵒᵖ} (g : G.obj U) (x : P.obj.obj U) : g • x = P.smul U g x :=
  rfl

@[simp]
lemma map_smul' {U V : Cᵒᵖ} (f : U ⟶ V) (g : G.obj U) (x : P.obj.obj U) :
    P.obj.map f (g • x) = G.map f g • P.obj.map f x :=
  P.map_smul f g x

lemma existsUnique_smul' {U : Cᵒᵖ} (x y : P.obj.obj U) : ∃! g : G.obj U, g • x = y :=
  P.existsUnique_smul U x y

instance (U : Cᵒᵖ) : MulAction.IsPretransitive (G.obj U) (P.obj.obj U) :=
  ⟨fun x y ↦ (P.existsUnique_smul' x y).exists⟩

lemma eq_one_of_smul_eq {U : Cᵒᵖ} {g : G.obj U} {x : P.obj.obj U} (h : g • x = x) : g = 1 :=
  (P.existsUnique_smul' x x).unique h (_root_.one_smul _ x)

lemma smul_left_injective {U : Cᵒᵖ} (x : P.obj.obj U) :
    Function.Injective (fun g : G.obj U ↦ g • x) := fun _ h hgh ↦
  (P.existsUnique_smul' x (h • x)).unique hgh rfl

/-- The unique `g` with `g • x = y`. -/
noncomputable def diff {U : Cᵒᵖ} (x y : P.obj.obj U) : G.obj U :=
  (P.existsUnique_smul' x y).exists.choose

@[simp]
lemma diff_smul {U : Cᵒᵖ} (x y : P.obj.obj U) : P.diff x y • x = y :=
  (P.existsUnique_smul' x y).exists.choose_spec

lemma diff_eq_iff {U : Cᵒᵖ} {x y : P.obj.obj U} {g : G.obj U} : P.diff x y = g ↔ g • x = y :=
  ⟨fun h ↦ h ▸ P.diff_smul x y,
    fun h ↦ (P.existsUnique_smul' x y).unique (P.diff_smul x y) h⟩

@[simp]
lemma diff_self {U : Cᵒᵖ} (x : P.obj.obj U) : P.diff x x = 1 :=
  P.diff_eq_iff.2 (_root_.one_smul _ x)

lemma diff_smul_self {U : Cᵒᵖ} (x : P.obj.obj U) (g : G.obj U) : P.diff x (g • x) = g :=
  P.diff_eq_iff.2 rfl

@[simp]
lemma diff_smul_right {U : Cᵒᵖ} (x y : P.obj.obj U) (g : G.obj U) :
    P.diff x (g • y) = g * P.diff x y :=
  P.diff_eq_iff.2 (by rw [← smul_smul, diff_smul])

@[simp]
lemma diff_smul_left {U : Cᵒᵖ} (x y : P.obj.obj U) (g : G.obj U) :
    P.diff (g • x) y = P.diff x y * g⁻¹ :=
  P.diff_eq_iff.2 (by rw [smul_smul, inv_mul_cancel_right, diff_smul])

lemma diff_mul_diff {U : Cᵒᵖ} (x y z : P.obj.obj U) : P.diff y z * P.diff x y = P.diff x z :=
  (P.diff_eq_iff.2 (by rw [← smul_smul, diff_smul, diff_smul])).symm

lemma map_diff {U V : Cᵒᵖ} (f : U ⟶ V) (x y : P.obj.obj U) :
    G.map f (P.diff x y) = P.diff (P.obj.map f x) (P.obj.map f y) :=
  (P.diff_eq_iff.2 (by rw [← map_smul', diff_smul])).symm

/-- The sieve of morphisms `V ⟶ U` such that `P(V)` is nonempty. -/
abbrev nonemptySieve (U : C) : Sieve U := P.obj.nonemptySieve' U

lemma nonemptySieve_mem (U : C) : P.nonemptySieve U ∈ J U := by
  obtain ⟨R, hR, hne⟩ := P.locallyNonempty U
  exact J.superset_covering (fun _ f hf ↦ hne f hf) hR

end Action

/-- Morphisms of torsors: `G`-equivariant morphisms of sheaves. -/
@[ext]
structure Hom (P Q : Torsor J G) where
  /-- The underlying morphism of presheaves. -/
  hom : P.obj ⟶ Q.obj
  map_smul (U : Cᵒᵖ) (g : G.obj U) (x : P.obj.obj U) :
    hom.app U (g • x) = g • hom.app U x

instance : Category (Torsor J G) where
  Hom := Hom
  id P := ⟨𝟙 _, fun _ _ _ ↦ rfl⟩
  comp φ ψ := ⟨φ.hom ≫ ψ.hom, fun U g x ↦ by simp [φ.map_smul, ψ.map_smul]⟩

@[ext]
lemma hom_ext {P Q : Torsor J G} {φ ψ : P ⟶ Q} (h : φ.hom = ψ.hom) : φ = ψ :=
  Hom.ext h

@[simp]
lemma id_hom (P : Torsor J G) : Hom.hom (𝟙 P) = 𝟙 _ := rfl

@[simp]
lemma comp_hom {P Q R : Torsor J G} (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    (φ ≫ ψ).hom = φ.hom ≫ ψ.hom := rfl

@[simp]
lemma hom_map_smul {P Q : Torsor J G} (φ : P ⟶ Q) {U : Cᵒᵖ} (g : G.obj U) (x : P.obj.obj U) :
    φ.hom.app U (g • x) = g • φ.hom.app U x :=
  φ.map_smul U g x

variable {P Q : Torsor J G} (φ : P ⟶ Q)

lemma hom_app_injective (U : Cᵒᵖ) : Function.Injective (φ.hom.app U) := by
  intro x y hxy
  rw [← P.diff_smul x y] at hxy ⊢
  rw [hom_map_smul] at hxy
  rw [Q.eq_one_of_smul_eq hxy.symm, _root_.one_smul]

lemma hom_app_surjective (U : C) : Function.Surjective (φ.hom.app (op U)) := by
  intro z
  let p : ∀ ⦃V : C⦄ (f : V ⟶ U), P.nonemptySieve U f → P.obj.obj (op V) :=
    fun _ _ hf ↦ hf.some
  let x : Presieve.FamilyOfElements P.obj (P.nonemptySieve U).arrows := fun _ f hf ↦
    Q.diff (φ.hom.app _ (p f hf)) (Q.obj.map f.op z) • p f hf
  have hx : ∀ ⦃V : C⦄ (f : V ⟶ U) (hf : P.nonemptySieve U f),
      φ.hom.app (op V) (x f hf) = Q.obj.map f.op z :=
    fun _ f hf ↦ by simp [x]
  have hcomp : x.Compatible := by
    intro Y₁ Y₂ Z a b f₁ f₂ h₁ h₂ comm
    apply hom_app_injective φ (op Z)
    simp only [NatTrans.naturality_apply, hx]
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      comm]
  obtain ⟨t, ht, -⟩ := P.isSheaf _ (P.nonemptySieve_mem U) x hcomp
  refine ⟨t, (Q.isSheaf _ (P.nonemptySieve_mem U)).isSeparatedFor.ext fun V f hf ↦ ?_⟩
  rw [← NatTrans.naturality_apply, ht f hf, hx]

lemma hom_app_bijective (U : Cᵒᵖ) : Function.Bijective (φ.hom.app U) :=
  ⟨hom_app_injective φ U, hom_app_surjective φ U.unop⟩

/-- Every morphism of torsors is an isomorphism (Giraud III 1.4.5): torsors form a groupoid. -/
instance isIso (φ : P ⟶ Q) : IsIso φ := by
  have : ∀ U, IsIso (φ.hom.app U) := fun U ↦ (isIso_iff_bijective _).2 (hom_app_bijective φ U)
  have : IsIso φ.hom := NatIso.isIso_of_isIso_app _
  refine ⟨⟨inv φ.hom, fun U g y ↦ ?_⟩, ?_, ?_⟩
  · apply hom_app_injective φ U
    have h (z : Q.obj.obj U) : φ.hom.app U ((inv φ.hom).app U z) = z := by
      simp
    rw [hom_map_smul, h, h]
  · ext1
    exact IsIso.hom_inv_id φ.hom
  · ext1
    exact IsIso.inv_hom_id φ.hom

/-- The underlying sheaf of sets of a torsor. -/
def toSheaf (P : Torsor J G) : Sheaf J (Type w) :=
  ⟨P.obj, (isSheaf_iff_isSheaf_of_type _ _).2 P.isSheaf⟩

/-- The forgetful functor from torsors to sheaves of sets. -/
@[simps]
def forget : Torsor J G ⥤ Sheaf J (Type w) where
  obj P := P.toSheaf
  map φ := ObjectProperty.homMk φ.hom

instance : (forget (J := J) (G := G)).Faithful where
  map_injective h := by
    ext1
    exact Sheaf.hom_ext_iff.1 h

section Trivial

variable (J G)

/-- The trivial torsor: `G` acting on itself by left translations. -/
@[simps obj]
def trivial (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat)) : Torsor J G where
  obj := G ⋙ CategoryTheory.forget GrpCat
  isSheaf := hG
  smul U := fun (g x : G.obj U) ↦ g * x
  one_smul U := fun (x : G.obj U) ↦ one_mul x
  mul_smul U := fun (g h x : G.obj U) ↦ mul_assoc g h x
  map_smul f := fun g x ↦ map_mul (G.map f).hom g x
  existsUnique_smul U := fun (x y : G.obj U) ↦
    ⟨y * x⁻¹, inv_mul_cancel_right y x, fun (g : G.obj U) (hg : g * x = y) ↦ by simp [← hg]⟩
  locallyNonempty U := ⟨⊤, J.top_mem U, fun _ _ _ ↦ ⟨(1 : G.obj _)⟩⟩

variable {J G}

lemma trivial_smul (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat)) {U : Cᵒᵖ}
    (g : G.obj U) (x : (trivial J G hG).obj.obj U) :
    g • x = (show (trivial J G hG).obj.obj U from g * (show G.obj U from x)) :=
  rfl

/-- The morphism from the trivial torsor attached to a global section `p` of `P`:
`g ↦ g • p`. -/
@[simps]
def homOfSection (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
    (P : Torsor J G) (p : P.obj.sections) : trivial J G hG ⟶ P where
  hom :=
    { app U := ↾fun (g : G.obj U) ↦ g • p.1 U
      naturality U V f := by
        ext (g : G.obj U)
        change G.map f g • p.1 V = P.obj.map f (g • p.1 U)
        rw [map_smul', p.2 f] }
  map_smul U g h := (smul_smul g (show G.obj U from h) (p.1 U)).symm

/-- The global section `φ(1)` of `P` attached to a morphism `φ` from the trivial torsor. -/
def sectionOfHom (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
    {P : Torsor J G} (φ : trivial J G hG ⟶ P) : P.obj.sections :=
  ⟨fun U ↦ φ.hom.app U (show (trivial J G hG).obj.obj U from (1 : G.obj U)), fun {U V} f ↦ by
    change P.obj.map f (φ.hom.app U _) = φ.hom.app V _
    rw [← NatTrans.naturality_apply]
    exact congr_arg (φ.hom.app V) (map_one (G.map f).hom)⟩

/-- Morphisms from the trivial torsor to `P` correspond to global sections of `P`. -/
def homTrivialEquiv (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
    (P : Torsor J G) : (trivial J G hG ⟶ P) ≃ P.obj.sections where
  toFun := sectionOfHom hG
  invFun := homOfSection hG P
  left_inv φ := by
    ext U (g : G.obj U)
    change g • φ.hom.app U (show (trivial J G hG).obj.obj U from (1 : G.obj U)) = φ.hom.app U g
    rw [← hom_map_smul]
    exact congr_arg (φ.hom.app U) (mul_one g)
  right_inv p := by
    ext U
    exact _root_.one_smul _ (p.1 U)

/-- A torsor is trivial if and only if it has a global section (Giraud III 1.4.3). -/
theorem nonempty_iso_trivial_iff (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
    (P : Torsor J G) :
    Nonempty (P ≅ trivial J G hG) ↔ Nonempty P.obj.sections :=
  ⟨fun ⟨e⟩ ↦ ⟨homTrivialEquiv hG P e.inv⟩,
    fun ⟨p⟩ ↦ ⟨(asIso (homOfSection hG P p)).symm⟩⟩

/-- Every torsor is locally trivial: its restriction to the objects `V` of the covering sieve
`P.nonemptySieve U` has a section. -/
lemma nonempty_of_nonemptySieve (P : Torsor J G) {U V : C} {f : V ⟶ U}
    (hf : P.nonemptySieve U f) : Nonempty (P.obj.obj (op V)) :=
  hf

end Trivial

end Torsor

section Terminal

variable {X : C}

/-- For a terminal object `X`, the global sections of a presheaf of sets are its sections
over `X`. -/
@[simps]
def _root_.CategoryTheory.Functor.sectionsEquivOfIsTerminal (hX : Limits.IsTerminal X)
    (F : Cᵒᵖ ⥤ Type w) : F.sections ≃ F.obj (op X) where
  toFun s := s.1 (op X)
  invFun x := ⟨fun U ↦ F.map (hX.from U.unop).op x, fun {U V} f ↦ by
    dsimp only
    rw [← Functor.map_comp_apply]
    exact congr_arg (fun g ↦ F.map g x) (Quiver.Hom.unop_inj (hX.hom_ext _ _))⟩
  left_inv s := Subtype.ext (funext fun U ↦ s.2 (hX.from U.unop).op)
  right_inv x := by
    dsimp
    rw [hX.hom_ext (hX.from X) (𝟙 X), op_id, Functor.map_id_apply]

variable {J G}

/-- A torsor is trivial if and only if it has a section over the terminal object. -/
theorem Torsor.nonempty_iso_trivial_iff_of_isTerminal (hX : Limits.IsTerminal X)
    (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat)) (P : Torsor J G) :
    Nonempty (P ≅ trivial J G hG) ↔ Nonempty (P.obj.obj (op X)) := by
  rw [nonempty_iso_trivial_iff]
  exact (Functor.sectionsEquivOfIsTerminal hX P.obj).nonempty_congr

end Terminal

section H1

/-- The cohomology set `H¹(G)` of a presheaf of groups on a site: the set of isomorphism
classes of `G`-torsors (Giraud III 2.4). -/
def H1 : Type _ := _root_.Quotient (isIsomorphicSetoid (Torsor J G))

variable {J G}

/-- The class of a torsor in `H¹`. -/
def Torsor.class (P : Torsor J G) : H1 J G := _root_.Quotient.mk _ P

lemma Torsor.class_eq_class_iff (P Q : Torsor J G) : P.class = Q.class ↔ Nonempty (P ≅ Q) :=
  _root_.Quotient.eq

lemma H1.mk_surjective : Function.Surjective (Torsor.class : Torsor J G → H1 J G) :=
  _root_.Quotient.mk_surjective

variable (J G) in
/-- The distinguished point of `H¹(G)`: the class of the trivial torsor. -/
def H1.trivialClass (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat)) : H1 J G :=
  (Torsor.trivial J G hG).class

/-- A torsor has the trivial class in `H¹` if and only if it has a global section. -/
theorem Torsor.class_eq_trivialClass_iff
    (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat)) (P : Torsor J G) :
    P.class = H1.trivialClass J G hG ↔ Nonempty P.obj.sections := by
  rw [← Torsor.nonempty_iso_trivial_iff hG P]
  exact _root_.Quotient.eq

/-- A torsor has the trivial class in `H¹` if and only if it has a section over the terminal
object. -/
theorem Torsor.class_eq_trivialClass_iff_of_isTerminal {X : C} (hX : Limits.IsTerminal X)
    (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat)) (P : Torsor J G) :
    P.class = H1.trivialClass J G hG ↔ Nonempty (P.obj.obj (op X)) := by
  rw [← Torsor.nonempty_iso_trivial_iff_of_isTerminal hX hG P]
  exact _root_.Quotient.eq

end H1

section Restrict

variable {J G} {D : Type u'} [Category.{v'} D] (K : GrothendieckTopology D) (F : D ⥤ C)
  [F.IsContinuous K J] [F.IsCocontinuous K J]

namespace Torsor

/-- The restriction of a torsor along a continuous and cocontinuous functor `F : D ⥤ C`: a
torsor under `F.op ⋙ G`. -/
@[simps obj]
def restrict (P : Torsor J G) : Torsor K (F.op ⋙ G) where
  obj := F.op ⋙ P.obj
  isSheaf := F.op_comp_isSheaf_of_isSheaf_type K P.isSheaf
  smul U := P.smul (F.op.obj U)
  one_smul U := P.one_smul (F.op.obj U)
  mul_smul U := P.mul_smul (F.op.obj U)
  map_smul f := P.map_smul (F.op.map f)
  existsUnique_smul U := P.existsUnique_smul (F.op.obj U)
  locallyNonempty V :=
    ⟨(P.nonemptySieve (F.obj V)).functorPullback F,
      F.cover_lift K J (P.nonemptySieve_mem (F.obj V)), fun _ _ hf ↦ hf⟩

@[simp]
lemma restrict_smul (P : Torsor J G) {U : Dᵒᵖ} (g : G.obj (F.op.obj U))
    (x : P.obj.obj (F.op.obj U)) :
    (g • x : (P.restrict K F).obj.obj U) = (g • x : P.obj.obj (F.op.obj U)) :=
  rfl

/-- Restriction of torsors along `F`, as a functor. -/
@[simps obj]
def restrictFunctor : Torsor J G ⥤ Torsor K (F.op ⋙ G) where
  obj P := P.restrict K F
  map φ :=
    { hom := Functor.whiskerLeft F.op φ.hom
      map_smul U g x := φ.map_smul (F.op.obj U) g x }

@[simp]
lemma restrictFunctor_map_hom_app {P Q : Torsor J G} (φ : P ⟶ Q) (U : Dᵒᵖ) :
    ((restrictFunctor K F).map φ).hom.app U = φ.hom.app (F.op.obj U) :=
  rfl

end Torsor

/-- The map `H¹(C, G) ⟶ H¹(D, F.op ⋙ G)` induced by restriction along `F`. -/
def H1.restrict : H1 J G → H1 K (F.op ⋙ G) :=
  _root_.Quotient.map (Torsor.restrict K F) fun _ _ ⟨e⟩ ↦ ⟨(Torsor.restrictFunctor K F).mapIso e⟩

@[simp]
lemma H1.restrict_class (P : Torsor J G) :
    H1.restrict K F P.class = (P.restrict K F).class :=
  rfl

end Restrict

section Over

variable {J}

/-- The restriction of a presheaf of groups to the category `Over U`. -/
abbrev PresheafOfGroups.over (G : Cᵒᵖ ⥤ GrpCat.{w}) (U : C) : (Over U)ᵒᵖ ⥤ GrpCat.{w} :=
  (Over.forget U).op ⋙ G

variable {G}

/-- The restriction `P|U` of a torsor to the site `Over U`. -/
abbrev Torsor.over (P : Torsor J G) (U : C) : Torsor (J.over U) (PresheafOfGroups.over G U) :=
  P.restrict (J.over U) (Over.forget U)

namespace Torsor

variable {U V : C} (f : V ⟶ U)

/-- The restriction of torsors on `Over U` along `Over.map f : Over V ⥤ Over U`. (This is
`P.restrict (J.over V) (Over.map f)`, with the group `G|V` instead of `(Over.map f).op ⋙ G|U`.) -/
@[simps obj]
def overMap (P : Torsor (J.over U) (PresheafOfGroups.over G U)) :
    Torsor (J.over V) (PresheafOfGroups.over G V) where
  obj := (Over.map f).op ⋙ P.obj
  isSheaf := (P.restrict (J.over V) (Over.map f)).isSheaf
  smul Y := P.smul ((Over.map f).op.obj Y)
  one_smul Y := P.one_smul ((Over.map f).op.obj Y)
  mul_smul Y := P.mul_smul ((Over.map f).op.obj Y)
  map_smul g := P.map_smul ((Over.map f).op.map g)
  existsUnique_smul Y := P.existsUnique_smul ((Over.map f).op.obj Y)
  locallyNonempty Y := (P.restrict (J.over V) (Over.map f)).locallyNonempty Y

@[simp]
lemma overMap_smul (P : Torsor (J.over U) (PresheafOfGroups.over G U)) {Y : (Over V)ᵒᵖ}
    (g : (PresheafOfGroups.over G V).obj Y) (x : (P.overMap f).obj.obj Y) :
    g • x = ((show (PresheafOfGroups.over G U).obj ((Over.map f).op.obj Y) from g) •
      (show P.obj.obj ((Over.map f).op.obj Y) from x) : P.obj.obj ((Over.map f).op.obj Y)) :=
  rfl

variable (J G) in
/-- Restriction of torsors along `Over.map f`, as a functor. -/
@[simps obj]
def overMapFunctor :
    Torsor (J.over U) (PresheafOfGroups.over G U) ⥤ Torsor (J.over V) (PresheafOfGroups.over G V)
    where
  obj P := P.overMap f
  map φ :=
    { hom := Functor.whiskerLeft (Over.map f).op φ.hom
      map_smul Y g x := φ.map_smul ((Over.map f).op.obj Y) g x }

@[simp]
lemma overMapFunctor_map_hom_app {P Q : Torsor (J.over U) (PresheafOfGroups.over G U)}
    (φ : P ⟶ Q) (Y : (Over V)ᵒᵖ) :
    ((overMapFunctor J G f).map φ).hom.app Y = φ.hom.app ((Over.map f).op.obj Y) :=
  rfl

end Torsor

end Over

end CategoryTheory
