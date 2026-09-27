/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Etale.TorsorStack

/-!
# Effective descent for torsors

Let `G` be a sheaf of groups on a site `(C, J)`, and `f i : X i ⟶ S` a covering family. Every
descent datum `D` for the stack of `G`-torsors (`Torsor.stack J G`) relative to `f` is effective:
the sections of the glued torsor over `T` are the families of sections of the `D.obj i` over all
`V ⟶ T` which lie over some `X i`, compatible with the gluing isomorphisms of `D` and natural in
`V` (`Torsor.StackDescent.GlueSection`). These form a sheaf
(`Torsor.StackDescent.isSheaf_gluePresheaf`), on which `G` acts simply transitively, so they
define a torsor `Torsor.StackDescent.glue`, whose descent datum is isomorphic to `D`
(`Torsor.StackDescent.toDescentDataGlueIso`).

Together with the descent of morphisms (`Torsor.isPrestack_stack`), this shows that the torsors
under a sheaf of groups form a stack (`Torsor.isStack_stack`, Giraud III 1.4.2).

## References

* [J. Giraud, *Cohomologie non abélienne*, III 1.4.2][giraud1971]
* [Stacks Project, Tag 04UK](https://stacks.math.columbia.edu/tag/04UK)
-/

universe t w v u

open CategoryTheory Opposite Limits Bicategory Pseudofunctor

-- See the comment in `SGA.Foundations.Etale.TorsorPresheaf`.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat.{w}}
  {S : C} {ι : Type t} {X : ι → C} {f : ∀ i, X i ⟶ S}

namespace StackDescent

lemma left_comp_eq {V : Over S} {i j : ι} (a : V ⟶ Over.mk (f i)) (b : V ⟶ Over.mk (f j)) :
    a.left ≫ f i = b.left ≫ f j := by
  simpa using (Over.w a).trans (Over.w b).symm

variable (D : (stack J G).DescentData f)

/-- The sections over `T` of the torsor glued from a descent datum `D`: families of sections
`val t i a` of `D.obj i` over all `V` with `t : V ⟶ T` and `a : V ⟶ X i` over `S`, compatible with
the transfer maps and natural in `V`. -/
@[ext]
structure GlueSection (T : Over S) where
  /-- The components of the section. -/
  val ⦃V : Over S⦄ (t : V ⟶ T) (i : ι) (a : V ⟶ Over.mk (f i)) :
    (tors D i).obj.obj (op (Over.mk a.left))
  val_transfer ⦃V : Over S⦄ (t : V ⟶ T) (i j : ι) (a : V ⟶ Over.mk (f i))
    (b : V ⟶ Over.mk (f j)) :
    transfer D a.left b.left (left_comp_eq a b) (val t i a) = val t j b
  val_naturality ⦃V V' : Over S⦄ (φ : V' ⟶ V) (t : V ⟶ T) (i : ι) (a : V ⟶ Over.mk (f i)) :
    (tors D i).obj.map (Over.homMk φ.left (by simp) : Over.mk (φ ≫ a).left ⟶ Over.mk a.left).op
      (val t i a) = val (φ ≫ t) i (φ ≫ a)

variable {D}

lemma transfer_congr {Y : C} {i₁ i₂ : ι} {a₁ a₁' : Y ⟶ X i₁} {a₂ a₂' : Y ⟶ X i₂}
    (e₁ : a₁ = a₁') (e₂ : a₂ = a₂') (h : a₁ ≫ f i₁ = a₂ ≫ f i₂)
    (z : (tors D i₁).obj.obj (op (Over.mk a₁))) :
    transfer D a₁' a₂' (by rw [← e₁, ← e₂, h])
      ((tors D i₁).obj.map (Over.homMk (𝟙 Y) (by simp [e₁]) :
        Over.mk a₁' ⟶ Over.mk a₁).op z) =
      (tors D i₂).obj.map (Over.homMk (𝟙 Y) (by simp [e₂]) : Over.mk a₂' ⟶ Over.mk a₂).op
        (transfer D a₁ a₂ h z) := by
  subst e₁ e₂
  rw [obj_map_eq_self _ _ (by simp), obj_map_eq_self _ _ (by simp)]

namespace GlueSection

lemma val_congr {T : Over S} (s : GlueSection D T) {V : Over S} (t : V ⟶ T) {i : ι}
    {a a' : V ⟶ Over.mk (f i)} (h : a = a') :
    s.val t i a' = (tors D i).obj.map (Over.homMk (𝟙 V.left) (by simp [h]) :
      Over.mk a'.left ⟶ Over.mk a.left).op (s.val t i a) := by
  subst h
  exact (obj_map_eq_self _ _ (by simp) _).symm

/-- The restriction of a section along `g : T' ⟶ T`. -/
@[simps]
def restrict {T T' : Over S} (g : T' ⟶ T) (s : GlueSection D T) : GlueSection D T' where
  val V t i a := s.val (t ≫ g) i a
  val_transfer V t i j a b := s.val_transfer _ i j a b
  val_naturality V V' φ t i a := by rw [s.val_naturality, Category.assoc]

/-- The action of `G(T)` on the sections over `T`. -/
@[simps]
def smul {T : Over S} (c : (PresheafOfGroups.over G S).obj (op T)) (s : GlueSection D T) :
    GlueSection D T where
  val V t i a := (show (PresheafOfGroups.over G (X i)).obj (op (Over.mk a.left)) from
    (PresheafOfGroups.over G S).map t.op c) • s.val t i a
  val_transfer V t i j a b := by
    rw [transfer_smul, s.val_transfer]
  val_naturality V V' φ t i a := by
    rw [map_smul', s.val_naturality]
    congr 1
    change (G.map _ ≫ G.map _) c = G.map _ c
    rw [← G.map_comp]
    rfl

lemma one_smul' {T : Over S} (s : GlueSection D T) : smul 1 s = s := by
  ext V t i a
  simp only [GlueSection.smul_val]
  erw [map_one]
  exact _root_.one_smul _ _

lemma mul_smul' {T : Over S} (c c' : (PresheafOfGroups.over G S).obj (op T))
    (s : GlueSection D T) : smul (c * c') s = smul c (smul c' s) := by
  ext V t i a
  simp only [GlueSection.smul_val]
  erw [map_mul]
  exact (smul_smul _ _ _).symm

lemma restrict_smul {T T' : Over S} (g : T' ⟶ T) (c : (PresheafOfGroups.over G S).obj (op T))
    (s : GlueSection D T) :
    (smul c s).restrict g = smul ((PresheafOfGroups.over G S).map g.op c) (s.restrict g) := by
  ext V t i a
  simp only [restrict_val, smul_val, op_comp, Functor.map_comp]
  rfl

end GlueSection

variable (D) in
/-- The presheaf of sections of the torsor glued from a descent datum. -/
@[simps obj]
def gluePresheaf : (Over S)ᵒᵖ ⥤ Type (max u v w t) where
  obj T := GlueSection D T.unop
  map g := ↾(GlueSection.restrict g.unop)
  map_id T := by
    ext s V t i a
    simp
  map_comp g g' := by
    ext s V t i a
    simp

@[simp]
lemma gluePresheaf_map_val {T T' : Over S} (g : T' ⟶ T) (s : GlueSection D T) ⦃V : Over S⦄
    (t : V ⟶ T') (i : ι) (a : V ⟶ Over.mk (f i)) :
    ((gluePresheaf D).map g.op s : GlueSection D T').val t i a = s.val (t ≫ g) i a :=
  rfl

/-- The structure morphism `(Over.map (f i)).obj Z ⟶ Over.mk (f i)`. -/
abbrev structMap {i : ι} (Z : Over (X i)) : (Over.map (f i)).obj Z ⟶ Over.mk (f i) :=
  Over.homMk Z.hom

/-- The morphism `(Over.map (f i)).obj Z ⟶ V` attached to `k : Z ⟶ Over.mk a.left`. -/
abbrev liftMap {V : Over S} {i : ι} (a : V ⟶ Over.mk (f i)) {Z : Over (X i)}
    (k : Z ⟶ Over.mk a.left) : (Over.map (f i)).obj Z ⟶ V :=
  (Over.map (f i)).map k ≫ fromOverMap a

namespace GlueSection

/-- The restriction of a component of a section along `k : Z ⟶ Over.mk a.left`. -/
lemma map_val {T : Over S} (s : GlueSection D T) {V : Over S} (t : V ⟶ T) {i : ι}
    (a : V ⟶ Over.mk (f i)) {Z : Over (X i)} (k : Z ⟶ Over.mk a.left) :
    (tors D i).obj.map k.op (s.val t i a) = s.val (liftMap a k ≫ t) i (structMap Z) := by
  have h₁ := s.val_naturality (liftMap a k) t i a
  have h₂ := s.val_congr (liftMap a k ≫ t) (show liftMap a k ≫ a = structMap Z by
    ext; simpa using Over.w k)
  rw [h₂, ← h₁, obj_map_map]
  exact obj_map_congr _ _ _ (by simp) _

/-- Components of a section over isomorphic objects with the same underlying object. -/
lemma val_eq_map {T : Over S} (s : GlueSection D T) {V V' : Over S} (e : V' ⟶ V)
    (t : V ⟶ T) {i : ι} (a : V ⟶ Over.mk (f i)) (a' : V' ⟶ Over.mk (f i))
    (ha : e.left ≫ a.left = a'.left) :
    s.val (e ≫ t) i a' = (tors D i).obj.map (Over.homMk e.left ha :
      Over.mk a'.left ⟶ Over.mk a.left).op (s.val t i a) := by
  rw [s.val_congr (e ≫ t) (show e ≫ a = a' by ext; simp [ha]), ← s.val_naturality,
    obj_map_map]
  exact obj_map_congr _ _ _ (by simp) _

lemma val_eq_of_eq {T : Over S} (s : GlueSection D T) {V : Over S} {t t' : V ⟶ T} (h : t = t')
    (i : ι) (a : V ⟶ Over.mk (f i)) : s.val t i a = s.val t' i a := by
  rw [h]

end GlueSection

section Sheaf

variable {T : Over S} {R : Sieve T} (x : Presieve.FamilyOfElements (gluePresheaf D) R.arrows)

/-- The value at `structMap Z` of the family `x` over `m : (Over.map (f i)).obj Z ⟶ T`. -/
def famVal {i : ι} {Z : Over (X i)} (m : (Over.map (f i)).obj Z ⟶ T) (hm : R m) :
    (tors D i).obj.obj (op Z) :=
  (x m hm).val (𝟙 _) i (structMap Z)

lemma famVal_congr {i : ι} {Z : Over (X i)} {m m' : (Over.map (f i)).obj Z ⟶ T} (h : m = m')
    (hm : R m) (hm' : R m') : famVal x m hm = famVal x m' hm' := by
  subst h
  rfl

variable {x}

lemma famVal_map (hx : x.Compatible) {i : ι} {Z W : Over (X i)}
    (m : (Over.map (f i)).obj Z ⟶ T) (hm : R m) (g : W ⟶ Z) :
    (tors D i).obj.map g.op (famVal x m hm) =
      famVal x ((Over.map (f i)).map g ≫ m) (R.downward_closed hm _) := by
  have e := hx.to_sieveCompatible m ((Over.map (f i)).map g) hm
  unfold famVal
  rw [e]
  erw [GlueSection.map_val (x m hm) (𝟙 _) (structMap Z) g]
  exact (x m hm).val_eq_of_eq (by ext; simp) _ _

variable (R) in
/-- The sieve on `Over.mk a.left` of the morphisms whose image in `C/S` is in `R`. -/
abbrev localSieve {V : Over S} (t : V ⟶ T) {i : ι} (a : V ⟶ Over.mk (f i)) :
    Sieve (Over.mk a.left) :=
  (R.pullback (fromOverMap a ≫ t)).functorPullback (Over.map (f i))

lemma localSieve_mem (hR : R ∈ J.over S T) {V : Over S} (t : V ⟶ T) {i : ι}
    (a : V ⟶ Over.mk (f i)) : localSieve R t a ∈ J.over (X i) (Over.mk a.left) :=
  (Over.map (f i)).cover_lift (J.over (X i)) (J.over S) ((J.over S).pullback_stable _ hR)

variable (x) in
/-- The family of sections of `D.obj i` over the local sieve. -/
def localFamily {V : Over S} (t : V ⟶ T) {i : ι} (a : V ⟶ Over.mk (f i)) :
    Presieve.FamilyOfElements (tors D i).obj (localSieve R t a).arrows :=
  fun _ k hk ↦ famVal x ((Over.map (f i)).map k ≫ fromOverMap a ≫ t) hk

lemma localFamily_compatible (hx : x.Compatible) {V : Over S} (t : V ⟶ T) {i : ι}
    (a : V ⟶ Over.mk (f i)) : (localFamily x t a).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro W Z k g hk
  unfold localFamily
  rw [famVal_map hx]
  exact famVal_congr x (by simp) _ _

/-- The components of the section glued from a compatible family. -/
noncomputable def glueVal (hx : x.Compatible) (hR : R ∈ J.over S T) {V : Over S} (t : V ⟶ T)
    {i : ι} (a : V ⟶ Over.mk (f i)) : (tors D i).obj.obj (op (Over.mk a.left)) :=
  ((tors D i).isSheaf _ (localSieve_mem hR t a)).amalgamate _ (localFamily_compatible hx t a)

lemma map_glueVal (hx : x.Compatible) (hR : R ∈ J.over S T) {V : Over S} (t : V ⟶ T)
    {i : ι} (a : V ⟶ Over.mk (f i)) {Z : Over (X i)} (k : Z ⟶ Over.mk a.left)
    (hk : R ((Over.map (f i)).map k ≫ fromOverMap a ≫ t)) :
    (tors D i).obj.map k.op (glueVal hx hR t a) =
      famVal x ((Over.map (f i)).map k ≫ fromOverMap a ≫ t) hk :=
  ((tors D i).isSheaf _ (localSieve_mem hR t a)).valid_glue _ k hk

lemma glueVal_ext (hR : R ∈ J.over S T) {V : Over S} (t : V ⟶ T) {i : ι}
    (a : V ⟶ Over.mk (f i)) {y y' : (tors D i).obj.obj (op (Over.mk a.left))}
    (h : ∀ ⦃Z : Over (X i)⦄ (k : Z ⟶ Over.mk a.left),
      R ((Over.map (f i)).map k ≫ fromOverMap a ≫ t) →
        (tors D i).obj.map k.op y = (tors D i).obj.map k.op y') : y = y' :=
  ((tors D i).isSheaf _ (localSieve_mem hR t a)).isSeparatedFor.ext fun _ k hk ↦ h k hk

lemma glueVal_naturality (hx : x.Compatible) (hR : R ∈ J.over S T) {V V' : Over S}
    (φ : V' ⟶ V) (t : V ⟶ T) (i : ι) (a : V ⟶ Over.mk (f i)) :
    (tors D i).obj.map (Over.homMk φ.left (by simp) :
      Over.mk (φ ≫ a).left ⟶ Over.mk a.left).op (glueVal hx hR t a) =
        glueVal hx hR (φ ≫ t) (φ ≫ a) := by
  refine glueVal_ext hR (φ ≫ t) (φ ≫ a) fun Z k hk ↦ ?_
  have e : (Over.map (f i)).map (k ≫ (Over.homMk φ.left (by simp) :
      Over.mk (φ ≫ a).left ⟶ Over.mk a.left)) ≫ fromOverMap a ≫ t =
      (Over.map (f i)).map k ≫ fromOverMap (φ ≫ a) ≫ φ ≫ t := by
    ext
    simp
  rw [obj_map_map, map_glueVal hx hR t a _ (e ▸ hk), map_glueVal hx hR _ _ k hk]
  exact famVal_congr x e _ _

lemma glueVal_transfer (hx : x.Compatible) (hR : R ∈ J.over S T) {V : Over S} (t : V ⟶ T)
    (i j : ι) (a : V ⟶ Over.mk (f i)) (b : V ⟶ Over.mk (f j)) :
    transfer D a.left b.left (left_comp_eq a b) (glueVal hx hR t a) = glueVal hx hR t b := by
  refine glueVal_ext hR t b fun Z k hk ↦ ?_
  have hZ : k.left ≫ b.left = Z.hom := by simpa using Over.w k
  have hab := left_comp_eq a b
  let k' : Over.mk (k.left ≫ a.left) ⟶ Over.mk a.left := Over.homMk k.left
  let idl : Z ⟶ Over.mk (k.left ≫ b.left) := Over.homMk (𝟙 _) (by simp [hZ])
  let ma := (Over.map (f i)).map k' ≫ fromOverMap a ≫ t
  let mb := (Over.map (f j)).map k ≫ fromOverMap b ≫ t
  let e : (Over.map (f j)).obj Z ⟶ (Over.map (f i)).obj (Over.mk (k.left ≫ a.left)) :=
    Over.homMk (𝟙 _) (by simp [← hZ, hab])
  let e' : (Over.map (f i)).obj (Over.mk (k.left ≫ a.left)) ⟶ (Over.map (f j)).obj Z :=
    Over.homMk (𝟙 _) (by simp [← hZ, hab])
  have hma : R ma := by
    have : ma = e' ≫ mb := by ext; simp [ma, mb, e', k']
    rw [this]
    exact R.downward_closed hk e'
  let b' : (Over.map (f i)).obj (Over.mk (k.left ≫ a.left)) ⟶ Over.mk (f j) :=
    Over.homMk (k.left ≫ b.left) (by simp [hab])
  have h1 : (tors D j).obj.map k.op (transfer D a.left b.left hab (glueVal hx hR t a)) =
      (tors D j).obj.map idl.op ((tors D j).obj.map (Over.homMk k.left :
        Over.mk (k.left ≫ b.left) ⟶ Over.mk b.left).op (transfer D a.left b.left hab
          (glueVal hx hR t a))) := by
    rw [obj_map_map]
    exact obj_map_congr _ _ _ (by simp [idl]) _
  have h4 := (x ma hma).val_transfer (𝟙 _) i j (structMap (f := f) (Over.mk (k.left ≫ a.left))) b'
  have h6 := hx.to_sieveCompatible ma e hma
  have h8 := (x ma hma).map_val (𝟙 _) b' idl
  have hmb : mb = e ≫ ma := by ext; simp [ma, mb, e, k']
  rw [h1, transfer_naturality]
  erw [map_glueVal hx hR t a k' hma, map_glueVal hx hR t b k hk,
    famVal_congr x hmb hk (R.downward_closed hma e)]
  unfold famVal
  erw [h4, h8, h6, gluePresheaf_map_val]
  exact (x ma hma).val_eq_of_eq (by ext; simp [idl, e, b']) _ _

/-- The section glued from a compatible family. -/
noncomputable def glueSection (hx : x.Compatible) (hR : R ∈ J.over S T) : GlueSection D T where
  val _ t _ a := glueVal hx hR t a
  val_transfer _ t i j a b := glueVal_transfer hx hR t i j a b
  val_naturality _ _ φ t i a := glueVal_naturality hx hR φ t i a

lemma glueVal_eq (hR : R ∈ J.over S T) (s : GlueSection D T)
    (hs : ∀ ⦃W : Over S⦄ (g : W ⟶ T) (hg : R g), s.restrict g = x g hg) (hx : x.Compatible)
    {V : Over S} (t : V ⟶ T) (i : ι) (a : V ⟶ Over.mk (f i)) :
    s.val t i a = glueVal hx hR t a := by
  refine glueVal_ext hR t a fun Z k hk ↦ ?_
  rw [map_glueVal hx hR t a k hk, s.map_val]
  unfold famVal
  rw [← hs _ hk, GlueSection.restrict_val]
  exact s.val_eq_of_eq (by simp) _ _

lemma glueVal_restrict (hx : x.Compatible) (hR : R ∈ J.over S T) {W : Over S} (g : W ⟶ T)
    (hg : R g) {V : Over S} (t : V ⟶ W) (i : ι) (a : V ⟶ Over.mk (f i)) :
    glueVal hx hR (t ≫ g) a = (x g hg).val t i a := by
  refine glueVal_ext hR (t ≫ g) a fun Z k hk ↦ ?_
  have e := hx.to_sieveCompatible g (liftMap a k ≫ t) hg
  rw [map_glueVal hx hR _ a k hk, (x g hg).map_val]
  unfold famVal
  have e' : x ((Over.map (f i)).map k ≫ fromOverMap a ≫ t ≫ g) hk =
      x ((liftMap a k ≫ t) ≫ g) (R.downward_closed hg _) := by
    congr 1
    simp [liftMap]
  rw [e', e, gluePresheaf_map_val]
  exact (x g hg).val_eq_of_eq (by simp) _ _

end Sheaf

lemma isSheaf_gluePresheaf : Presieve.IsSheaf (J.over S) (gluePresheaf D) := by
  intro T R hR x hx
  refine ⟨glueSection hx hR, fun W g hg ↦ ?_, fun s hs ↦ ?_⟩
  · change (glueSection hx hR).restrict g = x g hg
    refine GlueSection.ext ?_
    funext V t i a
    exact glueVal_restrict hx hR g hg t i a
  · refine GlueSection.ext ?_
    funext V t i a
    exact glueVal_eq hR s (fun W g hg ↦ hs g hg) hx t i a

section Torsor

variable (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
  (hf : Sieve.ofArrows X f ∈ J S)

include hG hf in
lemma existsUnique_glueSection_smul {T : Over S} (s s' : GlueSection D T) :
    ∃! c : (PresheafOfGroups.over G S).obj (op T), GlueSection.smul c s = s' := by
  have H := (coversTop_over f hf).existsUnique_glue (H1.isSheaf_over hG S) (T := T)
    (fun V t i a ↦ (show (PresheafOfGroups.over G S).obj (op V) from
      (tors D i).diff (U := op (Over.mk a.left)) (s.val t i a) (s'.val t i a)))
    (fun V t i j a b ↦ by
      change (tors D i).diff (s.val t i a) (s'.val t i a) =
        (tors D j).diff (s.val t j b) (s'.val t j b)
      rw [← s.val_transfer t i j a b, ← s'.val_transfer t i j a b, eq_comm, diff_eq_iff]
      rw [← transfer_smul, diff_smul])
    (fun V V' φ t i a ↦ by
      change _ = (tors D i).diff (s.val (φ ≫ t) i (φ ≫ a)) (s'.val (φ ≫ t) i (φ ≫ a))
      rw [← s.val_naturality, ← s'.val_naturality, ← map_diff]
      rfl)
  obtain ⟨c, hc, hc'⟩ := H
  refine ⟨c, ?_, fun c' hc'' ↦ hc' c' fun V t i a ↦ ?_⟩
  · refine GlueSection.ext ?_
    funext V t i a
    simp only [GlueSection.smul_val]
    have := hc t i a
    change (PresheafOfGroups.over G S).map t.op c = _ at this
    rw [this]
    exact diff_smul _ _ _
  · have := congr_arg (fun r : GlueSection D T ↦ r.val t i a) hc''
    simp only [GlueSection.smul_val] at this
    exact ((tors D i).diff_eq_iff.2 this).symm

/-- The section over `V` generated by a section `e` of `D.obj i` over `Over.mk a.left`. -/
def ofSection {V : Over S} {i : ι} (a : V ⟶ Over.mk (f i))
    (e : (tors D i).obj.obj (op (Over.mk a.left))) : GlueSection D V where
  val V' t' j b := transfer D (t'.left ≫ a.left) b.left (by simpa using left_comp_eq (t' ≫ a) b)
    ((tors D i).obj.map (Over.homMk t'.left : Over.mk (t'.left ≫ a.left) ⟶ Over.mk a.left).op e)
  val_transfer V' t' j k b c := transfer_trans _ _ _ _ _ _ _
  val_naturality V' V'' φ t' j b := by
    erw [transfer_naturality]
    have e₁ : φ.left ≫ t'.left ≫ a.left = (φ ≫ t').left ≫ a.left := by simp
    have e₂ : φ.left ≫ b.left = (φ ≫ b).left := by simp
    have H := transfer_congr (D := D) e₁ e₂ (by simpa using left_comp_eq (φ ≫ t' ≫ a) (φ ≫ b))
      ((tors D i).obj.map (Over.homMk φ.left (by simp) :
        Over.mk (φ.left ≫ t'.left ≫ a.left) ⟶ Over.mk (t'.left ≫ a.left)).op
          ((tors D i).obj.map (Over.homMk t'.left :
            Over.mk (t'.left ≫ a.left) ⟶ Over.mk a.left).op e))
    refine (obj_map_eq_self (tors D j) _ (by simp) _).symm.trans (H.symm.trans ?_)
    congr 1
    rw [obj_map_map, obj_map_map]
    exact obj_map_congr _ _ _ (by simp) _

variable (D) in
include hf in
lemma locallyNonempty_glue (T : Over S) :
    ∃ R ∈ J.over S T, ∀ ⦃V : Over S⦄ (g : V ⟶ T), R g → Nonempty (GlueSection D V) := by
  let R : Sieve T :=
    { arrows V _ := ∃ (i : ι) (a : V ⟶ Over.mk (f i)),
        Nonempty ((tors D i).obj.obj (op (Over.mk a.left)))
      downward_closed := by
        rintro V W g ⟨i, a, ⟨e⟩⟩ h
        exact ⟨i, h ≫ a, ⟨(tors D i).obj.map (Over.homMk h.left (by simp) :
          Over.mk (h ≫ a).left ⟶ Over.mk a.left).op e⟩⟩ }
  refine ⟨R, ?_, fun V g ⟨i, a, ⟨e⟩⟩ ↦ ⟨ofSection a e⟩⟩
  rw [GrothendieckTopology.mem_over_iff]
  refine J.transitive (J.pullback_stable T.hom hf) _ fun Z m hm ↦ ?_
  obtain ⟨i, c, hc⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hm
  have hN := (tors D i).nonemptySieve_mem (Over.mk c)
  rw [GrothendieckTopology.mem_over_iff] at hN
  refine J.superset_covering ?_ hN
  intro W h hh
  rw [Sieve.overEquiv_iff] at hh
  change Sieve.overEquiv T R (h ≫ m)
  rw [Sieve.overEquiv_iff]
  exact ⟨i, Over.homMk (h ≫ c) (by simp [hc]), hh⟩

variable (D) in
/-- The torsor structure on the presheaf of sections glued from a descent datum. -/
noncomputable def glueIsTorsorOf :
    IsTorsorOf (J.over S) (PresheafOfGroups.over G S) (gluePresheaf D) where
  isSheaf := isSheaf_gluePresheaf
  smul _ c s := GlueSection.smul c s
  one_smul _ s := GlueSection.one_smul' s
  mul_smul _ c c' s := GlueSection.mul_smul' c c' s
  map_smul g c s := GlueSection.restrict_smul g.unop c s
  existsUnique_smul _ s s' := existsUnique_glueSection_smul hG hf s s'
  locallyNonempty T := locallyNonempty_glue D hf T

variable (D) in
/-- The torsor glued from a descent datum for a covering family. -/
noncomputable def glue : Torsor (J.over S) (PresheafOfGroups.over G S) :=
  ofLarge (glueIsTorsorOf D hG hf)

namespace GlueSection

/-- The value of a section over `(Over.map (f i)).obj Z` at its structure morphism. -/
def eval {i : ι} {Z : Over (X i)} (s : GlueSection D ((Over.map (f i)).obj Z)) :
    (tors D i).obj.obj (op Z) :=
  s.val (𝟙 _) i (structMap Z)

lemma eval_restrict {i : ι} {Z W : Over (X i)} (s : GlueSection D ((Over.map (f i)).obj Z))
    (g : W ⟶ Z) : (s.restrict ((Over.map (f i)).map g)).eval = (tors D i).obj.map g.op s.eval := by
  unfold eval
  erw [s.map_val (𝟙 _) (structMap Z) g]
  exact s.val_eq_of_eq (by ext; simp) _ _

lemma eval_smul {i : ι} {Z : Over (X i)} (s : GlueSection D ((Over.map (f i)).obj Z))
    (c : (PresheafOfGroups.over G (X i)).obj (op Z)) :
    (smul (show (PresheafOfGroups.over G S).obj (op ((Over.map (f i)).obj Z)) from c) s).eval =
      c • s.eval := by
  unfold eval
  simp only [smul_val]
  erw [op_id, Functor.map_id]
  rfl

end GlueSection

variable (D) in
/-- The comparison morphism from the restriction of the glued torsor to `D.obj i`. -/
noncomputable def glueToObj (i : ι) : (glue D hG hf).overMap (f i) ⟶ tors D i where
  hom :=
    { app Z := ↾fun p ↦ ((ofLargeEquiv (glueIsTorsorOf D hG hf) _).symm p).eval
      naturality Z W g := by
        ext p
        obtain ⟨x, rfl⟩ := (ofLargeEquiv (glueIsTorsorOf D hG hf) _).surjective p
        change GlueSection.eval ((ofLargeEquiv (glueIsTorsorOf D hG hf)
          ((Over.map (f i)).op.obj W)).symm
          ((ofLarge (glueIsTorsorOf D hG hf)).obj.map ((Over.map (f i)).op.map g)
            (ofLargeEquiv _ ((Over.map (f i)).op.obj Z) x))) = (tors D i).obj.map g
              (GlueSection.eval ((ofLargeEquiv (glueIsTorsorOf D hG hf)
                ((Over.map (f i)).op.obj Z)).symm (ofLargeEquiv _ _ x)))
        rw [← ofLargeEquiv_naturality, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        exact GlueSection.eval_restrict x g.unop }
  map_smul Z c p := by
    obtain ⟨x, rfl⟩ := (ofLargeEquiv (glueIsTorsorOf D hG hf) _).surjective p
    change GlueSection.eval ((ofLargeEquiv (glueIsTorsorOf D hG hf)
      ((Over.map (f i)).op.obj Z)).symm
      ((show (PresheafOfGroups.over G S).obj ((Over.map (f i)).op.obj Z) from c) •
        ofLargeEquiv _ ((Over.map (f i)).op.obj Z) x)) = c • GlueSection.eval
        ((ofLargeEquiv (glueIsTorsorOf D hG hf) ((Over.map (f i)).op.obj Z)).symm
          (ofLargeEquiv _ _ x))
    rw [← ofLargeEquiv_smul, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact GlueSection.eval_smul x c

lemma glueToObj_hom_app (i : ι) (Z : (Over (X i))ᵒᵖ)
    (x : GlueSection D ((Over.map (f i)).obj Z.unop)) :
    (glueToObj D hG hf i).hom.app Z (ofLargeEquiv (glueIsTorsorOf D hG hf) _ x) = x.eval := by
  change GlueSection.eval ((ofLargeEquiv (glueIsTorsorOf D hG hf) _).symm
    (ofLargeEquiv (glueIsTorsorOf D hG hf) _ x)) = _
  rw [Equiv.symm_apply_apply]

variable (D) in
/-- The descent datum of the glued torsor is isomorphic to `D`. -/
noncomputable def toDescentDataGlueIso :
    ((stack J G).toDescentData f).obj (glue D hG hf) ≅ D :=
  Pseudofunctor.DescentData.isoMk
    (fun i ↦ @asIso _ _ _ _ (glueToObj D hG hf i) (Torsor.isIso (glueToObj D hG hf i)))
    (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
      apply Torsor.hom_ext
      ext W p
      simp only [TypeCat.Fun.toFun_apply, stack_comp_hom, NatTrans.comp_app, types_comp_apply,
        stack_map_map_hom_app, asIso_hom]
      obtain ⟨x, rfl⟩ := (ofLargeEquiv (glueIsTorsorOf D hG hf)
        ((Over.map (f i₁)).op.obj ((Over.map f₁).op.obj W))).surjective p
      erw [toDescentData_obj_hom_hom_app, ← ofLargeEquiv_naturality, glueToObj_hom_app,
        glueToObj_hom_app, hom_hom_app]
      unfold GlueSection.eval
      rw [gluePresheaf_map_val]
      let b : (Over.map (f i₁)).obj ((Over.map f₁).obj W.unop) ⟶ Over.mk (f i₂) :=
        Over.homMk (W.unop.hom ≫ f₂) (by simp [hf₁, hf₂])
      erw [x.val_transfer (𝟙 _) i₁ i₂ (structMap (f := f) ((Over.map f₁).obj W.unop)) b,
        Category.id_comp]
      have H := x.val_eq_map (Over.homMk (𝟙 (unop W).left) (by simp [hf₁, hf₂]) :
        (Over.map (f i₂)).obj ((Over.map f₂).obj W.unop) ⟶
          (Over.map (f i₁)).obj ((Over.map f₁).obj W.unop)) (𝟙 _) b
            (structMap (f := f) ((Over.map f₂).obj W.unop)) (by simp [b])
      rw [Category.comp_id] at H
      erw [H]
      exact (obj_map_eq_self _ _ (by simp) _).symm)

end Torsor

end StackDescent

open StackDescent in
variable (f) in
lemma essSurj_toDescentData (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
    (hf : Sieve.ofArrows X f ∈ J S) : ((stack J G).toDescentData f).EssSurj :=
  ⟨fun D ↦ ⟨glue D hG hf, ⟨toDescentDataGlueIso D hG hf⟩⟩⟩

/-- Effectivity of descent for torsors (Giraud III 1.4.2): the torsors under a sheaf of groups
form a stack. -/
theorem isStack_stack (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat)) :
    (stack J G).IsStack J :=
  Pseudofunctor.IsStack.of_isStackFor fun S R hR ↦ by
    have hf : Sieve.ofArrows _ (fun g : R.arrows.category ↦ g.obj.hom) ∈ J S := by
      rwa [Sieve.ofArrows_category]
    have := full_toDescentData (G := G) _ hf
    have := faithful_toDescentData (G := G) _ hf
    have := essSurj_toDescentData _ hG hf
    rw [Pseudofunctor.isStackFor_iff]
    exact { }

end CategoryTheory.Torsor
