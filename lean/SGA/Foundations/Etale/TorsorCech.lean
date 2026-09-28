/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1
import SGA.Foundations.Etale.ChangeOfGroup

/-!
# Torsors and Čech cocycles

Let `U : I → C` be a family of objects of a site `(C, J)` which covers the final object
(`J.CoversTop U`), and `G` a sheaf of groups. A `G`-torsor `P` with sections `e i` over the
`U i` defines a `1`-cocycle (`Torsor.cocycle`): `γ i j a b` is the element `g` with
`g • e j|b = e i|a`. Its class in mathlib's `PresheafOfGroups.H1 G U` does not depend on the
sections (`Torsor.cocycle_isCohomologous`) and is invariant under isomorphism.

Conversely every cocycle defines a torsor (`PresheafOfGroups.OneCocycle.torsor`), and we obtain
a bijection between the isomorphism classes of torsors trivialized by the `U i` and
`PresheafOfGroups.H1 G U` (`H1.trivializedByEquiv`).

## References

* [J. Giraud, *Cohomologie non abélienne*, III 3.6][giraud1971]
* [J. Frenkel, *Cohomologie non abélienne et espaces fibrés*][frenkel1957]
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
-/

universe w'' w' w v u

open CategoryTheory Opposite Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat.{w}}
  {I : Type w'} {U : I → C}

section Glue

variable {F : Cᵒᵖ ⥤ Type w''}

/-- Gluing along a family of objects covering the final object: a family of sections
`y t i a` of a sheaf `F` over all `V` with maps `t : V ⟶ T` and `a : V ⟶ U i`, which does not
depend on `(i, a)` and is natural in `V`, comes from a unique section over `T`. -/
lemma GrothendieckTopology.CoversTop.existsUnique_glue (hU : J.CoversTop U)
    (hF : Presieve.IsSheaf J F) {T : C}
    (y : ∀ ⦃V : C⦄ (_ : V ⟶ T) (i : I) (_ : V ⟶ U i), F.obj (op V))
    (hy : ∀ ⦃V : C⦄ (t : V ⟶ T) (i j : I) (a : V ⟶ U i) (b : V ⟶ U j), y t i a = y t j b)
    (hy' : ∀ ⦃V V' : C⦄ (φ : V' ⟶ V) (t : V ⟶ T) (i : I) (a : V ⟶ U i),
      F.map φ.op (y t i a) = y (φ ≫ t) i (φ ≫ a)) :
    ∃! s : F.obj (op T), ∀ ⦃V : C⦄ (t : V ⟶ T) (i : I) (a : V ⟶ U i), F.map t.op s = y t i a := by
  let x : Presieve.FamilyOfElements F (Sieve.ofObjects U T).arrows :=
    fun V t ht ↦ y t ht.choose ht.choose_spec.some
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    change F.map g₁.op (y f₁ _ _) = F.map g₂.op (y f₂ _ _)
    rw [hy', hy', hy (g₁ ≫ f₁) _ h₂.choose _ (g₂ ≫ h₂.choose_spec.some), w]
  obtain ⟨s, hs, hs'⟩ := hF _ (hU T) x hx
  refine ⟨s, fun V t i a ↦ (hs t ⟨i, ⟨a⟩⟩).trans (hy _ _ _ _ _), fun s' hs'' ↦ hs' s' ?_⟩
  intro V t ht
  exact hs'' t _ _

end Glue

namespace Torsor

variable (P : Torsor J G)

lemma diff_hom_app {Q : Torsor J G} (φ : P ⟶ Q) {T : Cᵒᵖ} (x y : P.obj.obj T) :
    Q.diff (φ.hom.app T x) (φ.hom.app T y) = P.diff x y :=
  Q.diff_eq_iff.2 (by rw [← hom_map_smul, diff_smul])

variable (e : ∀ i, P.obj.obj (op (U i)))

/-- The `1`-cocycle of a torsor `P` with sections `e i` over the `U i`: `γ i j a b` is the
element `g` such that `g • e j|b = e i|a`. -/
noncomputable def cocycle : PresheafOfGroups.OneCocycle G U where
  ev i j T a b := P.diff (P.obj.map b.op (e j)) (P.obj.map a.op (e i))
  ev_precomp i j T T' φ a b := by
    rw [P.map_diff, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
  ev_trans i j k T a b c := P.diff_mul_diff _ _ _

lemma cocycle_ev (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    (P.cocycle e).ev i j a b = P.diff (P.obj.map b.op (e j)) (P.obj.map a.op (e i)) :=
  rfl

/-- The cocycles attached to two families of sections are cohomologous. -/
lemma cocycle_isCohomologous (e' : ∀ i, P.obj.obj (op (U i))) :
    (P.cocycle e).IsCohomologous (P.cocycle e') := by
  refine ⟨fun i ↦ P.diff (e i) (e' i), fun i j T a b ↦ ?_⟩
  simp only [cocycle_ev, P.map_diff, P.diff_mul_diff]

/-- Isomorphic torsors have the same cocycles. -/
lemma cocycle_hom_ev {Q : Torsor J G} (φ : P ⟶ Q) (i j : I) {T : C} (a : T ⟶ U i)
    (b : T ⟶ U j) :
    (Q.cocycle (fun i ↦ φ.hom.app _ (e i))).ev i j a b = (P.cocycle e).ev i j a b := by
  simp only [cocycle_ev, ← NatTrans.naturality_apply φ.hom, diff_hom_app]

lemma cocycle_hom_isCohomologous {Q : Torsor J G} (φ : P ⟶ Q) :
    (Q.cocycle (fun i ↦ φ.hom.app _ (e i))).IsCohomologous (P.cocycle e) :=
  ⟨1, fun i j T a b ↦ by simp [cocycle_hom_ev]⟩

section HomOfCohomologous

variable {P} {Q : Torsor J G} (e' : ∀ i, Q.obj.obj (op (U i)))
  (α : PresheafOfGroups.ZeroCochain G U)

/-- The local values of the morphism `P ⟶ Q` attached to cohomologous cocycles: if
`x|t = g • e i|a`, it is `(g * α(i)|a⁻¹) • e' i|a`. -/
noncomputable def homOfCohomologousAux {T : C} (x : P.obj.obj (op T)) ⦃V : C⦄ (t : V ⟶ T)
    (i : I) (a : V ⟶ U i) : Q.obj.obj (op V) :=
  (P.diff (P.obj.map a.op (e i)) (P.obj.map t.op x) * (G.map a.op (α i))⁻¹) •
    Q.obj.map a.op (e' i)

variable {e e' α}
variable (hα : PresheafOfGroups.OneCohomologyRelation (P.cocycle e).toOneCochain
  (Q.cocycle e').toOneCochain α)
include hα

lemma homOfCohomologousAux_indep {T : C} (x : P.obj.obj (op T)) ⦃V : C⦄ (t : V ⟶ T)
    (i j : I) (a : V ⟶ U i) (b : V ⟶ U j) :
    homOfCohomologousAux e e' α x t i a = homOfCohomologousAux e e' α x t j b := by
  have h := hα i j a b
  simp only [cocycle_ev] at h
  unfold homOfCohomologousAux
  rw [← Q.diff_smul (Q.obj.map b.op (e' j)) (Q.obj.map a.op (e' i)), smul_smul]
  congr 1
  rw [← P.diff_mul_diff (P.obj.map b.op (e j)) (P.obj.map a.op (e i)) (P.obj.map t.op x),
    mul_assoc, mul_assoc]
  congr 1
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_assoc, mul_inv_cancel, mul_one]

omit hα in
lemma homOfCohomologousAux_naturality {T : C} (x : P.obj.obj (op T)) ⦃V V' : C⦄ (φ : V' ⟶ V)
    (t : V ⟶ T) (i : I) (a : V ⟶ U i) :
    Q.obj.map φ.op (homOfCohomologousAux e e' α x t i a) =
      homOfCohomologousAux e e' α x (φ ≫ t) i (φ ≫ a) := by
  simp only [homOfCohomologousAux, map_smul', map_mul, map_inv, P.map_diff,
    ← Functor.map_comp_apply, ← op_comp]

variable (hU : J.CoversTop U)
include hU

lemma existsUnique_homOfCohomologous {T : C} (x : P.obj.obj (op T)) :
    ∃! y : Q.obj.obj (op T), ∀ ⦃V : C⦄ (t : V ⟶ T) (i : I) (a : V ⟶ U i),
      Q.obj.map t.op y = homOfCohomologousAux e e' α x t i a :=
  hU.existsUnique_glue Q.isSheaf _ (homOfCohomologousAux_indep hα x)
    (homOfCohomologousAux_naturality x)

/-- The morphism of torsors `P ⟶ Q` attached to cohomologous cocycles. -/
noncomputable def homOfCohomologous : P ⟶ Q where
  hom :=
    { app T := ↾fun x ↦ (existsUnique_homOfCohomologous hα hU (T := T.unop) x).exists.choose
      naturality T T' f := by
        ext x
        refine (existsUnique_homOfCohomologous hα hU (T := T'.unop) (P.obj.map f x)).unique
          (existsUnique_homOfCohomologous hα hU (P.obj.map f x)).exists.choose_spec ?_
        intro V t i a
        change Q.obj.map t.op (Q.obj.map f
          (existsUnique_homOfCohomologous hα hU (T := T.unop) x).exists.choose) = _
        rw [← Functor.map_comp_apply, show f ≫ t.op = (t ≫ f.unop).op from rfl,
          (existsUnique_homOfCohomologous hα hU (T := T.unop) x).exists.choose_spec
            (t ≫ f.unop) i a]
        unfold homOfCohomologousAux
        rw [op_comp, Functor.map_comp_apply]
        rfl }
  map_smul T g x := by
    refine (existsUnique_homOfCohomologous hα hU (T := T.unop) (g • x)).unique
      (existsUnique_homOfCohomologous hα hU (g • x)).exists.choose_spec ?_
    intro V t i a
    change Q.obj.map t.op (g • (existsUnique_homOfCohomologous hα hU (T := T.unop) x).exists.choose)
      = _
    rw [map_smul', (existsUnique_homOfCohomologous hα hU (T := T.unop) x).exists.choose_spec t i a]
    unfold homOfCohomologousAux
    rw [smul_smul, map_smul', diff_smul_right, mul_assoc]

end HomOfCohomologous

/-- Two torsors whose cocycles are cohomologous are isomorphic. -/
lemma nonempty_iso_of_isCohomologous (hU : J.CoversTop U) {Q : Torsor J G}
    (e' : ∀ i, Q.obj.obj (op (U i))) (h : (P.cocycle e).IsCohomologous (Q.cocycle e')) :
    Nonempty (P ≅ Q) :=
  ⟨asIso (homOfCohomologous h.choose_spec hU)⟩

end Torsor

namespace PresheafOfGroups.OneCocycle

variable (γ : PresheafOfGroups.OneCocycle G U)

/-- The sections over `T` of the torsor attached to a cocycle `γ`: families `s t i a` in `G(V)`,
for `t : V ⟶ T` and `a : V ⟶ U i` (the coordinate of a section in the trivialization over
`U i`), with `s t j b = s t i a * γ i j a b`, natural in `V`. -/
@[ext]
structure TorsorSection (T : C) where
  /-- The coordinates of the section. -/
  val ⦃V : C⦄ (t : V ⟶ T) (i : I) (a : V ⟶ U i) : G.obj (op V)
  val_cocycle ⦃V : C⦄ (t : V ⟶ T) (i j : I) (a : V ⟶ U i) (b : V ⟶ U j) :
    val t j b = val t i a * γ.ev i j a b
  val_naturality ⦃V V' : C⦄ (φ : V' ⟶ V) (t : V ⟶ T) (i : I) (a : V ⟶ U i) :
    G.map φ.op (val t i a) = val (φ ≫ t) i (φ ≫ a)

namespace TorsorSection

variable {γ}

/-- The restriction of a section along `f : T' ⟶ T`. -/
@[simps]
def restrict {T T' : C} (f : T' ⟶ T) (s : TorsorSection γ T) : TorsorSection γ T' where
  val V t i a := s.val (t ≫ f) i a
  val_cocycle V t i j a b := s.val_cocycle _ i j a b
  val_naturality V V' φ t i a := by rw [s.val_naturality, Category.assoc]

/-- The action of `G(T)` on the sections over `T`. -/
@[simps]
def smul {T : C} (g : G.obj (op T)) (s : TorsorSection γ T) : TorsorSection γ T where
  val V t i a := G.map t.op g * s.val t i a
  val_cocycle V t i j a b := by rw [s.val_cocycle t i j a b, mul_assoc]
  val_naturality V V' φ t i a := by
    rw [map_mul, s.val_naturality, ← GrpCat.comp_apply, ← G.map_comp, ← op_comp]

lemma one_smul' {T : C} (s : TorsorSection γ T) : smul 1 s = s := by
  apply TorsorSection.ext
  funext V t i a
  simp

lemma mul_smul' {T : C} (g g' : G.obj (op T)) (s : TorsorSection γ T) :
    smul (g * g') s = smul g (smul g' s) := by
  apply TorsorSection.ext
  funext V t i a
  simp [mul_assoc]

lemma restrict_smul {T T' : C} (f : T' ⟶ T) (g : G.obj (op T)) (s : TorsorSection γ T) :
    (smul g s).restrict f = smul (G.map f.op g) (s.restrict f) := by
  apply TorsorSection.ext
  funext V t i a
  simp only [restrict_val, smul_val, op_comp, G.map_comp, GrpCat.comp_apply]

variable (γ) in
/-- The canonical section over `U i`, whose coordinate in the trivialization over `U j` is
`γ i j`. -/
@[simps]
def canonical (i : I) : TorsorSection γ (U i) where
  val _ t j b := γ.ev i j t b
  val_cocycle _ t j k b c := (γ.ev_trans i j k t b c).symm
  val_naturality _ _ φ t j b := γ.ev_precomp i j φ t b

end TorsorSection

/-- The presheaf of sections of the torsor attached to a cocycle `γ` (in a larger universe). -/
@[simps obj]
def torsorPresheaf : Cᵒᵖ ⥤ Type (max u v w w') where
  obj T := TorsorSection γ T.unop
  map f := ↾(TorsorSection.restrict f.unop)
  map_id T := by
    ext s V t i a
    simp
  map_comp f g := by
    ext s V t i a
    simp

@[simp]
lemma torsorPresheaf_map_val {T T' : C} (f : T' ⟶ T) (s : TorsorSection γ T) ⦃V : C⦄
    (t : V ⟶ T') (i : I) (a : V ⟶ U i) :
    ((γ.torsorPresheaf.map f.op s : TorsorSection γ T')).val t i a = s.val (t ≫ f) i a :=
  rfl

variable (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
include hG

lemma isSheaf_torsorPresheaf : Presieve.IsSheaf J γ.torsorPresheaf := by
  intro T R hR x hx
  have hx' := hx.to_sieveCompatible
  let xs : ∀ ⦃W : C⦄ (f : W ⟶ T), R f → TorsorSection γ W := fun W f hf ↦ x f hf
  have hxs : ∀ ⦃W W' : C⦄ (f : W ⟶ T) (g : W' ⟶ W) (hf : R f),
      xs (g ≫ f) (R.downward_closed hf g) = (xs f hf).restrict g :=
    fun W W' f g hf ↦ hx' f g hf
  have key : ∀ ⦃V : C⦄ (t : V ⟶ T) (i : I) (a : V ⟶ U i), ∃! g : G.obj (op V),
      ∀ ⦃W : C⦄ (h : W ⟶ V) (hh : R (h ≫ t)),
        G.map h.op g = (xs (h ≫ t) hh).val (𝟙 W) i (h ≫ a) := by
    intro V t i a
    refine hG (R.pullback t) (J.pullback_stable t hR)
      (fun W h hh ↦ (xs (h ≫ t) hh).val (𝟙 W) i (h ≫ a)) ?_
    intro W₁ W₂ Z g₁ g₂ h₁ h₂ hh₁ hh₂ w
    change G.map g₁.op ((xs (h₁ ≫ t) hh₁).val (𝟙 W₁) i (h₁ ≫ a)) =
      G.map g₂.op ((xs (h₂ ≫ t) hh₂).val (𝟙 W₂) i (h₂ ≫ a))
    rw [TorsorSection.val_naturality, TorsorSection.val_naturality, Category.comp_id,
      Category.comp_id]
    have e₁ := hxs (h₁ ≫ t) g₁ hh₁
    have e₂ := hxs (h₂ ≫ t) g₂ hh₂
    have e₃ : xs (g₁ ≫ h₁ ≫ t) (R.downward_closed hh₁ g₁) =
        xs (g₂ ≫ h₂ ≫ t) (R.downward_closed hh₂ g₂) := by
      simp only [← Category.assoc, w]
    have := congr_arg (fun r : TorsorSection γ Z ↦ r.val (𝟙 Z) i (g₁ ≫ h₁ ≫ a))
      (e₁.symm.trans (e₃.trans e₂))
    simp only [TorsorSection.restrict_val, Category.id_comp] at this
    rw [this, ← Category.assoc g₁, w, Category.assoc]
  choose g hg hg' using key
  let s : TorsorSection γ T :=
    { val := g
      val_cocycle V t i j a b := by
        refine (hg' t j b _ fun W h hh ↦ ?_).symm
        rw [map_mul, hg t i a h hh, TorsorSection.val_cocycle _ (𝟙 W) i j (h ≫ a) (h ≫ b),
          ← γ.ev_precomp]
      val_naturality V V' φ t i a := by
        refine hg' (φ ≫ t) i (φ ≫ a) _ fun W h hh ↦ ?_
        rw [← GrpCat.comp_apply, ← G.map_comp, ← op_comp,
          hg t i a (h ≫ φ) (by simpa using hh)]
        simp only [Category.assoc] }
  refine ⟨s, fun W f hf ↦ ?_, fun s' hs' ↦ ?_⟩
  · change s.restrict f = xs f hf
    apply TorsorSection.ext
    funext V t i a
    change g (t ≫ f) i a = (xs f hf).val t i a
    have := hg (t ≫ f) i a (𝟙 V) (by simpa using R.downward_closed hf t)
    rw [op_id, G.map_id] at this
    refine this.trans ?_
    have e := hxs f t hf
    simp only [Category.id_comp]
    rw [e]
    simp
  · let s'' : TorsorSection γ T := s'
    have hs'' : ∀ ⦃W : C⦄ (f : W ⟶ T) (hf : R f), s''.restrict f = xs f hf :=
      fun W f hf ↦ hs' f hf
    change s'' = s
    apply TorsorSection.ext
    funext V t i a
    refine hg' t i a _ fun W h hh ↦ ?_
    rw [TorsorSection.val_naturality, ← hs'' (h ≫ t) hh]
    simp

variable (hU : J.CoversTop U)
include hU

lemma existsUnique_torsorSection_smul {T : C} (s s' : TorsorSection γ T) :
    ∃! g : G.obj (op T), TorsorSection.smul g s = s' := by
  have H := hU.existsUnique_glue hG (T := T)
    (fun V t i a ↦ (s'.val t i a * (s.val t i a)⁻¹ : G.obj (op V)))
    (fun V t i j a b ↦ by
      change s'.val t i a * (s.val t i a)⁻¹ = s'.val t j b * (s.val t j b)⁻¹
      rw [s'.val_cocycle t i j a b, s.val_cocycle t i j a b]
      group)
    (fun V V' φ t i a ↦ by
      change G.map φ.op (s'.val t i a * (s.val t i a)⁻¹) = _
      rw [map_mul, map_inv, s.val_naturality, s'.val_naturality])
  obtain ⟨g, hg, hg'⟩ := H
  refine ⟨g, ?_, fun g' hg'' ↦ hg' g' fun V t i a ↦ ?_⟩
  · apply TorsorSection.ext
    funext V t i a
    change G.map t.op g * s.val t i a = s'.val t i a
    have := hg t i a
    change G.map t.op g = _ at this
    rw [this, inv_mul_cancel_right]
  · have := congr_arg (fun r : TorsorSection γ T ↦ r.val t i a) hg''
    change G.map t.op g' * s.val t i a = s'.val t i a at this
    change G.map t.op g' = _
    rw [← this, mul_inv_cancel_right]

/-- The torsor structure on the presheaf of sections attached to a cocycle. -/
noncomputable def torsorIsTorsorOf : Torsor.IsTorsorOf J G γ.torsorPresheaf where
  isSheaf := γ.isSheaf_torsorPresheaf hG
  smul _ g s := TorsorSection.smul g s
  one_smul T s := TorsorSection.one_smul' (T := T.unop) s
  mul_smul T g g' s := TorsorSection.mul_smul' (T := T.unop) g g' s
  map_smul f g s := TorsorSection.restrict_smul (T := _) f.unop g s
  existsUnique_smul _ s s' := γ.existsUnique_torsorSection_smul hG hU s s'
  locallyNonempty T := ⟨Sieve.ofObjects U T, hU T, fun _ _ ⟨i, ⟨a⟩⟩ ↦
    ⟨(TorsorSection.canonical γ i).restrict a⟩⟩

/-- The torsor attached to a `1`-cocycle `γ` of a sheaf of groups on a family of objects
covering the final object. -/
noncomputable def torsor : Torsor J G :=
  Torsor.ofLarge (γ.torsorIsTorsorOf hG hU)

/-- The canonical section of `γ.torsor` over `U i`. -/
noncomputable def torsorSection (i : I) : (γ.torsor hG hU).obj.obj (op (U i)) :=
  Torsor.ofLargeEquiv _ _ (TorsorSection.canonical γ i)

/-- The cocycle of `γ.torsor` with respect to its canonical sections is `γ`. -/
lemma torsor_cocycle_ev (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    ((γ.torsor hG hU).cocycle (γ.torsorSection hG hU)).ev i j a b = γ.ev i j a b := by
  rw [Torsor.cocycle_ev, Torsor.diff_eq_iff]
  let h := γ.torsorIsTorsorOf hG hU
  have h₁ := Torsor.ofLargeEquiv_naturality h b.op (TorsorSection.canonical γ j)
  have h₂ := Torsor.ofLargeEquiv_naturality h a.op (TorsorSection.canonical γ i)
  have h₃ := Torsor.ofLargeEquiv_smul h (γ.ev i j a b)
    ((TorsorSection.canonical γ j).restrict b)
  refine (congr_arg (γ.ev i j a b • ·) h₁.symm).trans (h₃.symm.trans (Eq.trans ?_ h₂))
  congr 1
  apply TorsorSection.ext
  funext V t k c
  change G.map t.op (γ.ev i j a b) * γ.ev j k (t ≫ b) c = γ.ev i k (t ≫ a) c
  rw [γ.ev_precomp, γ.ev_trans]

lemma torsor_cocycle_isCohomologous :
    ((γ.torsor hG hU).cocycle (γ.torsorSection hG hU)).IsCohomologous γ :=
  ⟨1, fun i j T a b ↦ by simp [torsor_cocycle_ev]⟩

end PresheafOfGroups.OneCocycle

namespace Torsor

variable (P : Torsor J G)

/-- The Čech class in `PresheafOfGroups.H1 G U` of a torsor which has sections over the
`U i`. -/
noncomputable def cechClass (hP : ∀ i, Nonempty (P.obj.obj (op (U i)))) :
    PresheafOfGroups.H1 G U :=
  (P.cocycle fun i ↦ (hP i).some).class

lemma cechClass_eq (hP : ∀ i, Nonempty (P.obj.obj (op (U i)))) (e : ∀ i, P.obj.obj (op (U i))) :
    P.cechClass hP = (P.cocycle e).class :=
  PresheafOfGroups.OneCocycle.IsCohomologous.class_eq (P.cocycle_isCohomologous _ e)

lemma cechClass_eq_of_iso {Q : Torsor J G} (φ : P ⟶ Q)
    (hP : ∀ i, Nonempty (P.obj.obj (op (U i)))) (hQ : ∀ i, Nonempty (Q.obj.obj (op (U i)))) :
    P.cechClass hP = Q.cechClass hQ := by
  rw [cechClass_eq P hP (fun i ↦ (hP i).some), cechClass_eq Q hQ (fun i ↦ φ.hom.app _ (hP i).some)]
  exact ((P.cocycle_hom_isCohomologous _ φ).class_eq).symm

end Torsor

namespace H1

variable (U) in
/-- A class in `H¹` is trivialized by the family `U` if a torsor in this class has sections over
all the `U i`. -/
def IsTrivializedBy (c : H1 J G) : Prop :=
  ∃ P : Torsor J G, P.class = c ∧ ∀ i, Nonempty (P.obj.obj (op (U i)))

lemma isTrivializedBy_class_iff (P : Torsor J G) :
    P.class.IsTrivializedBy U ↔ ∀ i, Nonempty (P.obj.obj (op (U i))) := by
  refine ⟨fun ⟨Q, hQ, hQU⟩ i ↦ ?_, fun h ↦ ⟨P, rfl, h⟩⟩
  obtain ⟨e⟩ := (Torsor.class_eq_class_iff _ _).1 hQ
  exact ⟨e.hom.hom.app _ (hQU i).some⟩

/-- The Čech class of a class in `H¹` trivialized by `U`. -/
noncomputable def toCech (c : {c : H1 J G // c.IsTrivializedBy U}) : PresheafOfGroups.H1 G U :=
  c.2.choose.cechClass c.2.choose_spec.2

lemma toCech_eq (c : {c : H1 J G // c.IsTrivializedBy U}) (P : Torsor J G) (hP : P.class = c.1)
    (hPU : ∀ i, Nonempty (P.obj.obj (op (U i)))) : toCech c = P.cechClass hPU := by
  obtain ⟨e⟩ := (Torsor.class_eq_class_iff _ _).1 (c.2.choose_spec.1.trans hP.symm)
  exact Torsor.cechClass_eq_of_iso _ e.hom _ _

variable (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat)) (hU : J.CoversTop U)

/-- The class in `H¹` of the torsor attached to a cocycle. -/
noncomputable def ofCech : PresheafOfGroups.H1 G U → {c : H1 J G // c.IsTrivializedBy U} :=
  Quot.lift
    (fun γ ↦ ⟨(γ.torsor hG hU).class, γ.torsor hG hU, rfl, fun i ↦ ⟨γ.torsorSection hG hU i⟩⟩)
    (fun γ γ' h ↦ Subtype.ext ((Torsor.class_eq_class_iff _ _).2
      (Torsor.nonempty_iso_of_isCohomologous _ _ hU (γ'.torsorSection hG hU)
        ((PresheafOfGroups.OneCocycle.equivalence_isCohomologous G U).trans
          ((PresheafOfGroups.OneCocycle.equivalence_isCohomologous G U).trans
            (γ.torsor_cocycle_isCohomologous hG hU) h)
          ((PresheafOfGroups.OneCocycle.equivalence_isCohomologous G U).symm
            (γ'.torsor_cocycle_isCohomologous hG hU))))))

lemma ofCech_class (γ : PresheafOfGroups.OneCocycle G U) :
    (ofCech hG hU γ.class).1 = (γ.torsor hG hU).class :=
  rfl

/-- The classes of torsors trivialized by a family `U` covering the final object are in
bijection with the Čech cohomology `PresheafOfGroups.H1 G U` (Giraud III 3.6.5). -/
noncomputable def trivializedByEquiv :
    {c : H1 J G // c.IsTrivializedBy U} ≃ PresheafOfGroups.H1 G U where
  toFun := toCech
  invFun := ofCech hG hU
  left_inv c := by
    obtain ⟨hP, hPU⟩ := c.2.choose_spec
    apply Subtype.ext
    refine Eq.trans ?_ hP
    change (((c.2.choose.cocycle fun i ↦ (hPU i).some)).torsor hG hU).class = c.2.choose.class
    exact (Torsor.class_eq_class_iff _ _).2
      (Torsor.nonempty_iso_of_isCohomologous _ _ hU (fun i ↦ (hPU i).some)
        (PresheafOfGroups.OneCocycle.torsor_cocycle_isCohomologous _ hG hU))
  right_inv := Quot.ind fun γ ↦ by
    change toCech (ofCech hG hU γ.class) = γ.class
    rw [toCech_eq _ (γ.torsor hG hU) (ofCech_class hG hU γ).symm
      (fun i ↦ ⟨γ.torsorSection hG hU i⟩), Torsor.cechClass_eq _ _ (γ.torsorSection hG hU)]
    exact (γ.torsor_cocycle_isCohomologous hG hU).class_eq

lemma trivializedByEquiv_apply (P : Torsor J G) (e : ∀ i, P.obj.obj (op (U i))) :
    trivializedByEquiv hG hU ⟨P.class, P, rfl, fun i ↦ ⟨e i⟩⟩ = (P.cocycle e).class := by
  change toCech _ = _
  rw [toCech_eq _ P rfl (fun i ↦ ⟨e i⟩), Torsor.cechClass_eq _ _ e]

end H1

end CategoryTheory
