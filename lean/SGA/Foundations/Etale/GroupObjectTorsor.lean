/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import SGA.Foundations.Etale.TorsorProduct

/-!
# Torsors under group objects, and torsors under group schemes

Let `C` be a cartesian monoidal category with a subcanonical Grothendieck topology `K`, `G` a
group object of `C` and `X` an object with an action of `G`. Then `X` is a `G`-torsor for `K`
(`IsTorsorObj`) if the morphism `G × X ⟶ X × X`, `(g, x) ↦ (g • x, x)`, is an isomorphism and
`X` has sections locally for `K`. Its functor of points is then a torsor under the sheaf of
groups `Hom(-, G)` (`IsTorsorObj.torsor`), which gives its class in `H¹(K, G)`; the class is
trivial if and only if `X` has a global section (`IsTorsorObj.class_eq_trivialClass_iff`), and
isomorphic torsors have the same class. When `G` is commutative, `H¹(K, G)` is a commutative
group (`H1.commGroupOfGrpObj`).

For a scheme `S`, this applies to group schemes over `S` (group objects of `Over S`) and the fpqc
topology: an `S`-scheme `P` with an action of `G` which is faithfully flat and quasi-compact over
`S` and such that `G ×_S P ⟶ P ×_S P` is an isomorphism is an fpqc `G`-torsor
(`AlgebraicGeometry.Scheme.isTorsorObj_of_flat`).

## References

* [SGA 3, Exposé IV, 5.1][sga3]
* [J. Giraud, *Cohomologie non abélienne*, III 1.4][giraud1971]
* [Stacks Project, Tag 0497](https://stacks.math.columbia.edu/tag/0497)
-/

universe v u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (K : GrothendieckTopology C) (G : C) [GrpObj G] (X : C) [ModObj G X]

/-- An object `X` with an action of a group object `G` is a `G`-torsor for the topology `K` if
`(g, x) ↦ (g • x, x)` is an isomorphism `G × X ≅ X × X` and `X` has sections locally. -/
structure IsTorsorObj : Prop where
  isIso_leftSMul : IsIso (ModObj.leftSMul G X)
  locallyNonempty (U : C) : ∃ R ∈ K U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Nonempty (V ⟶ X)

variable {K G X}

/-- The local sections condition of `IsTorsorObj` follows from the existence of sections on a
covering of the final object. -/
lemma IsTorsorObj.locallyNonempty_of_covering
    (h : Sieve.ofObjects (fun _ : Unit ↦ X) (𝟙_ C) ∈ K (𝟙_ C)) (U : C) :
    ∃ R ∈ K U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Nonempty (V ⟶ X) :=
  ⟨_, K.pullback_stable (toUnit U) h, fun _ _ ⟨_, ⟨a⟩⟩ ↦ ⟨a⟩⟩

variable (G) in
lemma isSheaf_yonedaGrpObj [K.Subcanonical] :
    Presieve.IsSheaf K (yonedaGrpObj G ⋙ CategoryTheory.forget GrpCat) :=
  haveI : (yonedaGrpObj G ⋙ CategoryTheory.forget GrpCat).IsRepresentable :=
    ⟨G, ⟨yonedaGrpObjRepresentableBy G⟩⟩
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

variable [K.Subcanonical]

/-- The functor of points of a torsor object, a torsor under the sheaf of groups `Hom(-, G)`. -/
def IsTorsorObj.torsor (h : IsTorsorObj K G X) : Torsor K (yonedaGrpObj G) where
  obj := yoneda.obj X
  isSheaf := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  smul U g x := (show U.unop ⟶ G from g) • (show U.unop ⟶ X from x)
  one_smul U x := one_smul (U.unop ⟶ G) (show U.unop ⟶ X from x)
  mul_smul U g g' x := mul_smul (show U.unop ⟶ G from g) (show U.unop ⟶ G from g')
    (show U.unop ⟶ X from x)
  map_smul f g x := ModObj.comp_smul f.unop g x
  existsUnique_smul U x y :=
    (ModObj.isIso_leftSMul_iff.1 h.isIso_leftSMul) U.unop x y
  locallyNonempty := h.locallyNonempty

lemma IsTorsorObj.torsor_obj (h : IsTorsorObj K G X) : h.torsor.obj = yoneda.obj X :=
  rfl

/-- The class in `H¹(K, G)` of a torsor object. -/
abbrev IsTorsorObj.class (h : IsTorsorObj K G X) : H1 K (yonedaGrpObj G) :=
  h.torsor.class

/-- A torsor object has the trivial class if and only if it has a global section. -/
lemma IsTorsorObj.class_eq_trivialClass_iff (h : IsTorsorObj K G X) :
    h.class = H1.trivialClass K (yonedaGrpObj G) (isSheaf_yonedaGrpObj G) ↔
      Nonempty (𝟙_ C ⟶ X) :=
  Torsor.class_eq_trivialClass_iff_of_isTerminal isTerminalTensorUnit _ h.torsor

/-- An equivariant morphism of torsor objects gives a morphism of torsors of points. -/
def IsTorsorObj.homOfIsModHom {Y : C} [ModObj G Y] (hX : IsTorsorObj K G X)
    (hY : IsTorsorObj K G Y) (f : X ⟶ Y) [IsModHom G f] : hX.torsor ⟶ hY.torsor where
  hom := yoneda.map f
  map_smul _ g x := IsModHom.map_smul f g x

/-- Torsor objects related by an equivariant morphism have the same class. -/
lemma IsTorsorObj.class_eq_of_isModHom {Y : C} [ModObj G Y] (hX : IsTorsorObj K G X)
    (hY : IsTorsorObj K G Y) (f : X ⟶ Y) [IsModHom G f] : hX.class = hY.class :=
  (Torsor.class_eq_class_iff _ _).2 ⟨asIso (hX.homOfIsModHom hY f)⟩

/-- Conversely, torsor objects with the same class are related by an equivariant
isomorphism. -/
lemma IsTorsorObj.exists_isModHom_of_class_eq {Y : C} [ModObj G Y] (hX : IsTorsorObj K G X)
    (hY : IsTorsorObj K G Y) (e : hX.class = hY.class) :
    ∃ (f : X ≅ Y), IsModHom G f.hom := by
  obtain ⟨φ⟩ := (Torsor.class_eq_class_iff _ _).1 e
  let f : X ⟶ Y := Yoneda.fullyFaithful.preimage φ.hom.hom
  let g : Y ⟶ X := Yoneda.fullyFaithful.preimage φ.inv.hom
  have hf : yoneda.map f = φ.hom.hom := Yoneda.fullyFaithful.map_preimage _
  have hg : yoneda.map g = φ.inv.hom := Yoneda.fullyFaithful.map_preimage _
  refine ⟨⟨f, g, ?_, ?_⟩, ⟨?_⟩⟩
  · apply Yoneda.fullyFaithful.map_injective
    rw [Functor.map_comp, hf, hg, Functor.map_id]
    exact congr_arg Torsor.Hom.hom φ.hom_inv_id
  · apply Yoneda.fullyFaithful.map_injective
    rw [Functor.map_comp, hf, hg, Functor.map_id]
    exact congr_arg Torsor.Hom.hom φ.inv_hom_id
  · have key := φ.hom.map_smul (op (G ⊗ X)) (fst G X) (snd G X)
    rw [← hf] at key
    change (fst G X • snd G X) ≫ f = fst G X • (snd G X ≫ f) at key
    have e : lift (fst G X) (snd G X ≫ f) = G ◁ f := by ext <;> simp
    simp only [Hom.smul_def, lift_fst_snd, Category.id_comp] at key
    rw [e] at key
    exact key

/-- The sheaf of groups `Hom(-, G)` is commutative when `G` is. -/
lemma isCommutative_yonedaGrpObj [BraidedCategory C] [IsCommMonObj G] :
    PresheafOfGroups.IsCommutative (yonedaGrpObj G) := fun U a b ↦ by
  let _ := Hom.commGroup (X := U.unop) (G := G)
  exact mul_comm (G := U.unop ⟶ G) a b

/-- For a commutative group object `G`, `H¹(K, G)` is a commutative group. -/
@[instance_reducible]
noncomputable def H1.commGroupOfGrpObj [BraidedCategory C] [IsCommMonObj G] :
    CommGroup (H1 K (yonedaGrpObj G)) :=
  H1.commGroup isCommutative_yonedaGrpObj (isSheaf_yonedaGrpObj G)

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {G P : Over S} [GrpObj G] [ModObj G P]

/-- An `S`-scheme `P` with an action of a group scheme `G` over `S`, which is flat, surjective
and quasi-compact over `S` and such that `G ×_S P ⟶ P ×_S P`, `(g, x) ↦ (g • x, x)`, is an
isomorphism, is a `G`-torsor for the fpqc topology (SGA 3 IV 5.1.1). -/
theorem isTorsorObj_of_flat [Flat P.hom] [Surjective P.hom] [QuasiCompact P.hom]
    (h : IsIso (ModObj.leftSMul G P)) : IsTorsorObj (fpqcTopology.over S) G P := by
  refine ⟨h, IsTorsorObj.locallyNonempty_of_covering ?_⟩
  rw [GrothendieckTopology.mem_over_iff]
  refine (fpqcTopology).superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck (Hom.singleton_mem_fpqcPrecoverage P.hom))
  rintro W g ⟨Z, a, b, ⟨⟩, rfl⟩
  rw [Sieve.overEquiv_iff]
  exact ⟨(), ⟨Over.homMk a⟩⟩

end AlgebraicGeometry.Scheme
