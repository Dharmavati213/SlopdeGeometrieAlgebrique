/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Etale.ChangeOfGroup

/-!
# Products of torsors and the group structure on `H¹` of an abelian sheaf

For torsors `P` under `G` and `Q` under `H`, the product `P × Q` is a torsor under `G × H`
(`Torsor.prod`). When `G` is commutative, the multiplication `G × G ⟶ G` and the inversion
`G ⟶ G` are morphisms of sheaves of groups, and changing the structure group along them gives
the contracted product `P ∧ Q` and the inverse torsor; this makes `H¹(G)` a commutative group
(`H1.commGroup`) with neutral element the class of the trivial torsor.

## References

* [J. Giraud, *Cohomologie non abélienne*, III 3.4][giraud1971]
* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
-/

universe w v u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Prod

variable (F₁ F₂ : Cᵒᵖ ⥤ Type w)

/-- The product of two presheaves of sets. -/
abbrev Presieve.prodFunctor : Cᵒᵖ ⥤ Type w where
  obj U := F₁.obj U × F₂.obj U
  map f := ↾(_root_.Prod.map (F₁.map f) (F₂.map f))

variable {F₁ F₂}

lemma Presieve.isSheaf_prodFunctor (h₁ : Presieve.IsSheaf J F₁) (h₂ : Presieve.IsSheaf J F₂) :
    Presieve.IsSheaf J (Presieve.prodFunctor F₁ F₂) := by
  intro T R hR x hx
  let x₁ : Presieve.FamilyOfElements F₁ R := fun V f hf ↦ (x f hf).1
  let x₂ : Presieve.FamilyOfElements F₂ R := fun V f hf ↦ (x f hf).2
  have hx₁ : x₁.Compatible := fun _ _ _ g₁ g₂ _ _ hf₁ hf₂ w ↦ by
    have := congr_arg _root_.Prod.fst (hx g₁ g₂ hf₁ hf₂ w)
    exact this
  have hx₂ : x₂.Compatible := fun _ _ _ g₁ g₂ _ _ hf₁ hf₂ w ↦ by
    have := congr_arg _root_.Prod.snd (hx g₁ g₂ hf₁ hf₂ w)
    exact this
  obtain ⟨s₁, hs₁, hs₁'⟩ := h₁ R hR x₁ hx₁
  obtain ⟨s₂, hs₂, hs₂'⟩ := h₂ R hR x₂ hx₂
  refine ⟨(s₁, s₂), fun V f hf ↦ _root_.Prod.ext (hs₁ f hf) (hs₂ f hf),
    fun s hs ↦ _root_.Prod.ext ?_ ?_⟩
  · exact hs₁' s.1 fun V f hf ↦ congr_arg _root_.Prod.fst (hs f hf)
  · exact hs₂' s.2 fun V f hf ↦ congr_arg _root_.Prod.snd (hs f hf)

end Prod

namespace PresheafOfGroups

variable (G H K L : Cᵒᵖ ⥤ GrpCat.{w})

/-- The product of two presheaves of groups. -/
@[simps]
def prod : Cᵒᵖ ⥤ GrpCat.{w} where
  obj U := GrpCat.of (G.obj U × H.obj U)
  map f := GrpCat.ofHom ((G.map f).hom.prodMap (H.map f).hom)

variable {G H K L}

lemma isSheaf_prod (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
    (hH : Presieve.IsSheaf J (H ⋙ CategoryTheory.forget GrpCat)) :
    Presieve.IsSheaf J (prod G H ⋙ CategoryTheory.forget GrpCat) :=
  Presieve.isSheaf_prodFunctor (F₁ := G ⋙ CategoryTheory.forget GrpCat)
    (F₂ := H ⋙ CategoryTheory.forget GrpCat) hG hH

/-- The product of two morphisms of presheaves of groups. -/
@[simps]
def prodMap (φ : G ⟶ K) (ψ : H ⟶ L) : prod G H ⟶ prod K L where
  app U := GrpCat.ofHom ((φ.app U).hom.prodMap (ψ.app U).hom)
  naturality U V f := by
    ext x
    exact _root_.Prod.ext (NatTrans.naturality_apply φ f x.1) (NatTrans.naturality_apply ψ f x.2)

variable (G H) in
lemma prodMap_id : prodMap (𝟙 G) (𝟙 H) = 𝟙 (prod G H) := by
  ext U x
  rfl

/-- The symmetry `G × H ⟶ H × G`. -/
@[simps]
def prodSwap : prod G H ⟶ prod H G where
  app U := GrpCat.ofHom (MulEquiv.prodComm.toMonoidHom)

/-- The associativity `G × (H × K) ⟶ (G × H) × K`. -/
@[simps]
def prodAssoc : prod G (prod H K) ⟶ prod (prod G H) K where
  app U := GrpCat.ofHom (MulEquiv.prodAssoc.symm.toMonoidHom)

/-- A presheaf of commutative groups. -/
def IsCommutative (G : Cᵒᵖ ⥤ GrpCat.{w}) : Prop :=
  ∀ (U : Cᵒᵖ) (a b : G.obj U), a * b = b * a

variable (hc : IsCommutative G)

/-- The multiplication `G × G ⟶ G` of a presheaf of commutative groups. -/
@[simps]
def mulHom : prod G G ⟶ G where
  app U := GrpCat.ofHom
    { toFun p := p.1 * p.2
      map_one' := mul_one 1
      map_mul' p q := by
        change (p.1 * q.1) * (p.2 * q.2) = (p.1 * p.2) * (q.1 * q.2)
        rw [mul_assoc, ← mul_assoc q.1, hc U q.1 p.2, mul_assoc, mul_assoc] }
  naturality U V f := by
    ext ⟨a, b⟩
    exact (map_mul (G.map f).hom a b).symm

/-- The inversion `G ⟶ G` of a presheaf of commutative groups. -/
@[simps]
def invHom : G ⟶ G where
  app U := GrpCat.ofHom
    { toFun a := a⁻¹
      map_one' := inv_one
      map_mul' a b := by
        rw [mul_inv_rev, hc U] }
  naturality U V f := by
    ext a
    exact (map_inv (G.map f).hom a).symm

end PresheafOfGroups

namespace Torsor

open PresheafOfGroups

variable {G H K L : Cᵒᵖ ⥤ GrpCat.{w}}

/-- The product of a `G`-torsor and an `H`-torsor, a torsor under `G × H`. -/
def prod (P : Torsor J G) (Q : Torsor J H) : Torsor J (PresheafOfGroups.prod G H) where
  obj := Presieve.prodFunctor P.obj Q.obj
  isSheaf := Presieve.isSheaf_prodFunctor P.isSheaf Q.isSheaf
  smul _ g x := (g.1 • x.1, g.2 • x.2)
  one_smul _ x := _root_.Prod.ext (_root_.one_smul _ x.1) (_root_.one_smul _ x.2)
  mul_smul _ g h x := _root_.Prod.ext (smul_smul g.1 h.1 x.1).symm (smul_smul g.2 h.2 x.2).symm
  map_smul f g x := _root_.Prod.ext (P.map_smul' f g.1 x.1) (Q.map_smul' f g.2 x.2)
  existsUnique_smul _ x y := ⟨(P.diff x.1 y.1, Q.diff x.2 y.2),
    _root_.Prod.ext (P.diff_smul _ _) (Q.diff_smul _ _), fun g hg ↦ _root_.Prod.ext
      (P.diff_eq_iff.2 (show g.1 • x.1 = y.1 from congr_arg _root_.Prod.fst hg)).symm
      (Q.diff_eq_iff.2 (show g.2 • x.2 = y.2 from congr_arg _root_.Prod.snd hg)).symm⟩
  locallyNonempty U := ⟨P.nonemptySieve U ⊓ Q.nonemptySieve U,
    J.intersection_covering (P.nonemptySieve_mem U) (Q.nonemptySieve_mem U),
    fun _ _ hf ↦ ⟨(hf.1.some, hf.2.some)⟩⟩

lemma prod_obj (P : Torsor J G) (Q : Torsor J H) :
    (P.prod Q).obj = Presieve.prodFunctor P.obj Q.obj :=
  rfl

/-- The product of two equivariant morphisms. -/
def HomOver.prodMap {φ : G ⟶ K} {ψ : H ⟶ L} {P : Torsor J G} {Q : Torsor J H}
    {P' : Torsor J K} {Q' : Torsor J L} (a : HomOver φ P P') (b : HomOver ψ Q Q') :
    HomOver (PresheafOfGroups.prodMap φ ψ) (P.prod Q) (P'.prod Q') where
  hom :=
    { app U := ↾fun (x : P.obj.obj U × Q.obj.obj U) ↦
        ((a.hom.app U x.1, b.hom.app U x.2) : P'.obj.obj U × Q'.obj.obj U)
      naturality U V f := by
        ext (x : P.obj.obj U × Q.obj.obj U)
        change ((a.hom.app V (P.obj.map f x.1), b.hom.app V (Q.obj.map f x.2)) :
            P'.obj.obj V × Q'.obj.obj V) = (P'.obj.map f (a.hom.app U x.1),
              Q'.obj.map f (b.hom.app U x.2))
        rw [NatTrans.naturality_apply, NatTrans.naturality_apply] }
  map_smul U g x := _root_.Prod.ext (a.map_smul U g.1 x.1) (b.map_smul U g.2 x.2)

/-- Transport an equivariant morphism along an equality of morphisms of groups. -/
def HomOver.congr {φ φ' : G ⟶ H} (h : φ = φ') {P : Torsor J G} {Q : Torsor J H}
    (a : HomOver φ P Q) : HomOver φ' P Q where
  hom := a.hom
  map_smul U g x := by rw [← h]; exact a.map_smul U g x

/-- The symmetry `P × Q ⟶ Q × P`. -/
def prodSwapHomOver (P : Torsor J G) (Q : Torsor J H) :
    HomOver PresheafOfGroups.prodSwap (P.prod Q) (Q.prod P) where
  hom := { app U := ↾fun (x : P.obj.obj U × Q.obj.obj U) ↦ (x.swap : Q.obj.obj U × P.obj.obj U) }
  map_smul U g x := rfl

/-- The associativity `P × (Q × R) ⟶ (P × Q) × R`. -/
def prodAssocHomOver (P : Torsor J G) (Q : Torsor J H) (R : Torsor J K) :
    HomOver PresheafOfGroups.prodAssoc (P.prod (Q.prod R)) ((P.prod Q).prod R) where
  hom := { app U := ↾fun (x : P.obj.obj U × (Q.obj.obj U × R.obj.obj U)) ↦
    (((x.1, x.2.1), x.2.2) : (P.obj.obj U × Q.obj.obj U) × R.obj.obj U) }
  map_smul U g x := rfl

/-- The product of two morphisms of torsors. -/
def prodHom {P P' : Torsor J G} {Q Q' : Torsor J H} (e₁ : P ⟶ P') (e₂ : Q ⟶ Q') :
    P.prod Q ⟶ P'.prod Q' :=
  HomOver.toHom (HomOver.congr (PresheafOfGroups.prodMap_id G H)
    (HomOver.prodMap (HomOver.ofHom e₁) (HomOver.ofHom e₂)))

section Mul

variable {G : Cᵒᵖ ⥤ GrpCat.{w}} (hc : IsCommutative G)
  (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))

/-- The contracted product `P ∧ Q` of two torsors under a commutative sheaf of groups: the
change of group of `P × Q` along the multiplication `G × G ⟶ G`. -/
noncomputable def mul (P Q : Torsor J G) : Torsor J G :=
  (P.prod Q).changeGroup (mulHom hc) hG

/-- The inverse of a torsor under a commutative sheaf of groups: the change of group along the
inversion `G ⟶ G`. -/
noncomputable def inv (P : Torsor J G) : Torsor J G :=
  P.changeGroup (invHom hc) hG

/-- The contracted product of isomorphic torsors are isomorphic. -/
noncomputable def mulIso {P P' Q Q' : Torsor J G} (e₁ : P ≅ P') (e₂ : Q ≅ Q') :
    mul hc hG P Q ≅ mul hc hG P' Q' :=
  changeGroupIsoOfHomOver hG
    ((toChangeGroup (mulHom hc) hG (P'.prod Q')).homComp (prodHom e₁.hom e₂.hom))

lemma nonempty_mul_comm_iso (P Q : Torsor J G) : Nonempty (mul hc hG P Q ≅ mul hc hG Q P) := by
  have h : PresheafOfGroups.prodSwap ≫ mulHom hc = mulHom hc := by
    ext U x
    exact hc U x.2 x.1
  exact ⟨changeGroupIsoOfHomOver hG (HomOver.congr h
    ((prodSwapHomOver P Q).comp (toChangeGroup (mulHom hc) hG (Q.prod P))))⟩

omit hG in
include hc in
lemma smul_smul_comm (P : Torsor J G) {U : Cᵒᵖ} (a b y : G.obj U) (z : P.obj.obj U) :
    (a * y) • b • z = (a * b) • y • z := by
  rw [smul_smul, smul_smul, mul_assoc, mul_assoc, hc U y b]

/-- The action map `G × P ⟶ P`, a `mul`-equivariant morphism from `G × P`. -/
def trivialProdHomOver (P : Torsor J G) :
    HomOver (mulHom hc) ((trivial J G hG).prod P) P where
  hom :=
    { app U := ↾fun (x : G.obj U × P.obj.obj U) ↦ x.1 • x.2
      naturality U V f := by
        ext (x : G.obj U × P.obj.obj U)
        exact (P.map_smul' f x.1 x.2).symm }
  map_smul U g x := smul_smul_comm hc P g.1 g.2 x.1 x.2

lemma nonempty_trivial_mul_iso (P : Torsor J G) :
    Nonempty (mul hc hG (trivial J G hG) P ≅ P) :=
  ⟨changeGroupIsoOfHomOver hG (trivialProdHomOver hc hG P)⟩

lemma nonempty_mul_assoc_iso (P Q R : Torsor J G) :
    Nonempty (mul hc hG (mul hc hG P Q) R ≅ mul hc hG P (mul hc hG Q R)) := by
  let a : HomOver (PresheafOfGroups.prodAssoc ≫
      (PresheafOfGroups.prodMap (mulHom hc) (𝟙 G) ≫ mulHom hc))
      (P.prod (Q.prod R)) (mul hc hG (mul hc hG P Q) R) :=
    (prodAssocHomOver P Q R).comp ((HomOver.prodMap (toChangeGroup (mulHom hc) hG (P.prod Q))
      (HomOver.ofHom (𝟙 R))).comp (toChangeGroup (mulHom hc) hG _))
  let b : HomOver (PresheafOfGroups.prodMap (𝟙 G) (mulHom hc) ≫ mulHom hc)
      (P.prod (Q.prod R)) (mul hc hG P (mul hc hG Q R)) :=
    (HomOver.prodMap (HomOver.ofHom (𝟙 P)) (toChangeGroup (mulHom hc) hG (Q.prod R))).comp
      (toChangeGroup (mulHom hc) hG _)
  have h : PresheafOfGroups.prodMap (𝟙 G) (mulHom hc) ≫ mulHom hc =
      PresheafOfGroups.prodAssoc ≫
        (PresheafOfGroups.prodMap (mulHom hc) (𝟙 G) ≫ mulHom hc) := by
    ext U x
    exact (mul_assoc _ _ _).symm
  exact ⟨(changeGroupIsoOfHomOver hG a).symm ≪≫ changeGroupIsoOfHomOver hG (b.congr h)⟩

omit hG in
include hc in
lemma mul_mul_inv_comm {U : Cᵒᵖ} (a b d : G.obj U) : b * d * a⁻¹ = a⁻¹ * b * d := by
  rw [hc U a⁻¹ b, mul_assoc, mul_assoc, hc U d a⁻¹]

/-- The map `(x, y) ↦ y / x` from `P × P` to `G`. -/
noncomputable def diffHomOver (P : Torsor J G) :
    HomOver (PresheafOfGroups.prodMap (invHom hc) (𝟙 G) ≫ mulHom hc) (P.prod P)
      (trivial J G hG) where
  hom :=
    { app U := ↾fun (x : P.obj.obj U × P.obj.obj U) ↦ (P.diff x.1 x.2 : G.obj U)
      naturality U V f := by
        ext (x : P.obj.obj U × P.obj.obj U)
        exact (P.map_diff f x.1 x.2).symm }
  map_smul U g x := by
    change P.diff (g.1 • x.1) (g.2 • x.2) = (g.1⁻¹ * g.2) * P.diff x.1 x.2
    rw [diff_smul_left, diff_smul_right]
    exact mul_mul_inv_comm hc g.1 g.2 _

lemma nonempty_inv_mul_iso (P : Torsor J G) :
    Nonempty (mul hc hG (inv hc hG P) P ≅ trivial J G hG) := by
  let a : HomOver (PresheafOfGroups.prodMap (invHom hc) (𝟙 G) ≫ mulHom hc) (P.prod P)
      (mul hc hG (inv hc hG P) P) :=
    (HomOver.prodMap (toChangeGroup (invHom hc) hG P) (HomOver.ofHom (𝟙 P))).comp
      (toChangeGroup (mulHom hc) hG _)
  exact ⟨(changeGroupIsoOfHomOver hG a).symm ≪≫ changeGroupIsoOfHomOver hG (diffHomOver hc hG P)⟩

end Mul

end Torsor

namespace H1

open PresheafOfGroups

variable {G : Cᵒᵖ ⥤ GrpCat.{w}} (hc : IsCommutative G)
  (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))

/-- The product on `H¹(G)` for a commutative sheaf of groups `G`, induced by the contracted
product of torsors. -/
noncomputable def mul : H1 J G → H1 J G → H1 J G :=
  _root_.Quotient.map₂ (Torsor.mul hc hG) fun _ _ ⟨e₁⟩ _ _ ⟨e₂⟩ ↦ ⟨Torsor.mulIso hc hG e₁ e₂⟩

lemma mul_class (P Q : Torsor J G) :
    mul hc hG P.class Q.class = (Torsor.mul hc hG P Q).class :=
  rfl

/-- The group structure on `H¹(G)` for a commutative sheaf of groups `G`: the product is
induced by the contracted product of torsors, the neutral element is the class of the trivial
torsor. -/
@[instance_reducible]
noncomputable def commGroup : CommGroup (H1 J G) where
  mul := mul hc hG
  one := trivialClass J G hG
  inv := map (invHom hc) hG
  mul_assoc a b c := by
    obtain ⟨P, rfl⟩ := mk_surjective a
    obtain ⟨Q, rfl⟩ := mk_surjective b
    obtain ⟨R, rfl⟩ := mk_surjective c
    exact (Torsor.class_eq_class_iff _ _).2 (Torsor.nonempty_mul_assoc_iso hc hG P Q R)
  one_mul a := by
    obtain ⟨P, rfl⟩ := mk_surjective a
    exact (Torsor.class_eq_class_iff _ _).2 (Torsor.nonempty_trivial_mul_iso hc hG P)
  mul_one a := by
    obtain ⟨P, rfl⟩ := mk_surjective a
    obtain ⟨e₁⟩ := Torsor.nonempty_mul_comm_iso hc hG P (Torsor.trivial J G hG)
    obtain ⟨e₂⟩ := Torsor.nonempty_trivial_mul_iso hc hG P
    exact (Torsor.class_eq_class_iff _ _).2 ⟨e₁ ≪≫ e₂⟩
  inv_mul_cancel a := by
    obtain ⟨P, rfl⟩ := mk_surjective a
    exact (Torsor.class_eq_class_iff _ _).2 (Torsor.nonempty_inv_mul_iso hc hG P)
  mul_comm a b := by
    obtain ⟨P, rfl⟩ := mk_surjective a
    obtain ⟨Q, rfl⟩ := mk_surjective b
    exact (Torsor.class_eq_class_iff _ _).2 (Torsor.nonempty_mul_comm_iso hc hG P Q)

end H1

end CategoryTheory
