/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.Tactic.Group
import SGA.Foundations.Etale.Torsor

/-!
# Change of the structure group of a torsor

Let `φ : G ⟶ H` be a morphism of presheaves of groups on a site `(C, J)`, with `H` a sheaf.
Every `G`-torsor `P` gives an `H`-torsor `φ_* P = P ∧^G H` (`Torsor.changeGroup`), which we
realize as the sheaf of maps `u : P ⟶ H` with `u (g • x) = u x * φ(g)⁻¹` (a sheaf of sets in a
larger universe, shrunk back with `FunctorToTypes.shrink`). It comes with a `φ`-equivariant
map `P ⟶ φ_* P`, and it is characterized by the property that an `H`-torsor `Q` is isomorphic
to `φ_* P` as soon as there is a `φ`-equivariant morphism `P ⟶ Q`
(`Torsor.nonempty_changeGroup_iso`). This gives the map `H1.map φ : H¹(G) ⟶ H¹(H)`.

We also give `Torsor.ofLarge`, which builds a torsor from a sheaf of sets in an arbitrary
universe satisfying the torsor axioms.

## References

* [J. Giraud, *Cohomologie non abélienne*, III 1.3 and 1.4.6][giraud1971]
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
-/

universe w' w v u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {G H K : Cᵒᵖ ⥤ GrpCat.{w}}

namespace Torsor

section OfLarge

variable (J G) (P : Cᵒᵖ ⥤ Type w')

/-- The data and axioms of a torsor under `G`, on a presheaf of sets in an arbitrary
universe. -/
structure IsTorsorOf where
  isSheaf : Presieve.IsSheaf J P
  /-- The action of `G`. -/
  smul (U : Cᵒᵖ) : G.obj U → P.obj U → P.obj U
  one_smul (U : Cᵒᵖ) (x : P.obj U) : smul U 1 x = x
  mul_smul (U : Cᵒᵖ) (g h : G.obj U) (x : P.obj U) : smul U (g * h) x = smul U g (smul U h x)
  map_smul {U V : Cᵒᵖ} (f : U ⟶ V) (g : G.obj U) (x : P.obj U) :
    P.map f (smul U g x) = smul V (G.map f g) (P.map f x)
  existsUnique_smul (U : Cᵒᵖ) (x y : P.obj U) : ∃! g : G.obj U, smul U g x = y
  locallyNonempty (U : C) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f → Nonempty (P.obj (op V))

variable {J G P}

lemma IsTorsorOf.small (h : IsTorsorOf J G P) : FunctorToTypes.Small.{w} P := fun U ↦ by
  by_cases hU : Nonempty (P.obj U)
  · obtain ⟨x⟩ := hU
    exact small_of_surjective (f := fun g : G.obj U ↦ h.smul U g x)
      (fun y ↦ (h.existsUnique_smul U x y).exists)
  · exact small_of_injective (f := fun x : P.obj U ↦ ((hU ⟨x⟩).elim : PEmpty.{w + 1}))
      (fun x _ _ ↦ (hU ⟨x⟩).elim)

/-- The torsor, in the universe of `G`, obtained by shrinking a presheaf of sets with a torsor
structure. -/
noncomputable def ofLarge (h : IsTorsorOf J G P) : Torsor J G :=
  haveI := h.small
  { obj := FunctorToTypes.shrink.{w} P
    isSheaf := Presieve.isSheaf_of_nat_equiv (fun X ↦ equivShrink.{w} (P.obj (op X)))
      (fun X Y f x ↦ by simp) h.isSheaf
    smul U g x := equivShrink _ (h.smul U g ((equivShrink _).symm x))
    one_smul U x := by simp [h.one_smul]
    mul_smul U g g' x := by simp [h.mul_smul]
    map_smul f g x := by simp [h.map_smul]
    existsUnique_smul U x y := by
      obtain ⟨g, hg, hg'⟩ := h.existsUnique_smul U ((equivShrink _).symm x)
        ((equivShrink _).symm y)
      refine ⟨g, by simp [hg], fun g' hg'' ↦ hg' g' ?_⟩
      rw [← hg'', Equiv.symm_apply_apply]
    locallyNonempty U := by
      obtain ⟨R, hR, hne⟩ := h.locallyNonempty U
      exact ⟨R, hR, fun V f hf ↦ ⟨equivShrink _ (hne f hf).some⟩⟩ }

variable (h : IsTorsorOf J G P)

/-- The identification of the sections of `ofLarge h` with those of `P`. -/
noncomputable def ofLargeEquiv (U : Cᵒᵖ) : P.obj U ≃ (ofLarge h).obj.obj U :=
  haveI := h.small
  equivShrink _

lemma ofLargeEquiv_smul {U : Cᵒᵖ} (g : G.obj U) (x : P.obj U) :
    ofLargeEquiv h U (h.smul U g x) = g • ofLargeEquiv h U x := by
  have := h.small
  change _ = equivShrink.{w} _ (h.smul U g ((equivShrink.{w} _).symm (equivShrink.{w} _ x)))
  rw [Equiv.symm_apply_apply]
  rfl

lemma ofLargeEquiv_naturality {U V : Cᵒᵖ} (f : U ⟶ V) (x : P.obj U) :
    ofLargeEquiv h V (P.map f x) = (ofLarge h).obj.map f (ofLargeEquiv h U x) := by
  have := h.small
  change _ = equivShrink.{w} _ (P.map f ((equivShrink.{w} _).symm (equivShrink.{w} _ x)))
  rw [Equiv.symm_apply_apply]
  rfl

end OfLarge

section HomOver

variable (φ : G ⟶ H)

/-- A `φ`-equivariant morphism from a `G`-torsor to an `H`-torsor. -/
@[ext]
structure HomOver (P : Torsor J G) (Q : Torsor J H) where
  /-- The underlying morphism of presheaves. -/
  hom : P.obj ⟶ Q.obj
  map_smul (U : Cᵒᵖ) (g : G.obj U) (x : P.obj.obj U) :
    hom.app U (g • x) = φ.app U g • hom.app U x

attribute [simp] HomOver.map_smul

/-- The composition of equivariant morphisms. -/
@[simps]
def HomOver.comp {φ : G ⟶ H} {ψ : H ⟶ K} {P : Torsor J G} {Q : Torsor J H} {R : Torsor J K}
    (a : HomOver φ P Q) (b : HomOver ψ Q R) : HomOver (φ ≫ ψ) P R where
  hom := a.hom ≫ b.hom
  map_smul U g x := by simp

/-- A morphism of torsors is an `𝟙`-equivariant morphism. -/
@[simps]
def HomOver.ofHom {P Q : Torsor J G} (a : P ⟶ Q) : HomOver (𝟙 G) P Q where
  hom := a.hom
  map_smul U g x := by simp

/-- An `𝟙`-equivariant morphism is a morphism of torsors. -/
@[simps]
def HomOver.toHom {P Q : Torsor J G} (a : HomOver (𝟙 G) P Q) : P ⟶ Q where
  hom := a.hom
  map_smul U g x := by simp

end HomOver

section ChangeGroup

variable (φ : G ⟶ H) (P : Torsor J G)

/-- A section of `presheafHom P.obj (H ⋙ forget GrpCat)` evaluated as an `H`-valued map. -/
def evalHom {T : C} (u : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T))
    (Y : Over T) (x : P.obj.obj (op Y.left)) : H.obj (op Y.left) :=
  u.app (op Y) x

lemma evalHom_naturality {T : C}
    (u : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T)) {Y Y' : Over T}
    (a : Y' ⟶ Y) (x : P.obj.obj (op Y.left)) :
    evalHom P u Y' (P.obj.map a.left.op x) = H.map a.left.op (evalHom P u Y x) :=
  NatTrans.naturality_apply u a.op x

lemma evalHom_map {T T' : C} (f : T' ⟶ T)
    (u : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T)) (Y : Over T')
    (x : P.obj.obj (op Y.left)) :
    evalHom P ((presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).map f.op u) Y x =
      evalHom P u ((Over.map f).obj Y) x :=
  rfl

/-- The subpresheaf of `presheafHom P (H ⋙ forget GrpCat)` of the maps `u` with
`u (g • x) = u x * φ(g)⁻¹`. -/
def changeGroupSubfunctor : Subfunctor (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)) where
  obj T := {u | ∀ (Y : Over T.unop) (g : G.obj (op Y.left)) (x : P.obj.obj (op Y.left)),
      evalHom P u Y (g • x) = evalHom P u Y x * (φ.app (op Y.left) g)⁻¹}
  map {_ _} f _ hu Y g x := hu ((Over.map f.unop).obj Y) g x

/-- Constructor for sections of `presheafHom P.obj (H ⋙ forget GrpCat)` from natural
families of `H`-valued maps. -/
def mkHom {T : C} (F : ∀ Y : Over T, P.obj.obj (op Y.left) → H.obj (op Y.left))
    (hF : ∀ {Y Y' : Over T} (a : Y' ⟶ Y) (x : P.obj.obj (op Y.left)),
      F Y' (P.obj.map a.left.op x) = H.map a.left.op (F Y x)) :
    (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T) where
  app Y := ↾(F Y.unop)
  naturality Y₁ Y₂ a := by
    ext x
    exact hF a.unop x

@[simp]
lemma evalHom_mkHom {T : C} (F : ∀ Y : Over T, P.obj.obj (op Y.left) → H.obj (op Y.left))
    (hF : ∀ {Y Y' : Over T} (a : Y' ⟶ Y) (x : P.obj.obj (op Y.left)),
      F Y' (P.obj.map a.left.op x) = H.map a.left.op (F Y x)) (Y : Over T)
    (x : P.obj.obj (op Y.left)) :
    evalHom P (mkHom P F hF) Y x = F Y x :=
  rfl

lemma presheafHom_ext {T : C}
    {u u' : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T)}
    (h : ∀ (Y : Over T) (x : P.obj.obj (op Y.left)), evalHom P u Y x = evalHom P u' Y x) :
    u = u' := by
  apply NatTrans.ext
  funext Y
  ext x
  exact h Y.unop x

lemma evalHom_naturality' {T : C}
    (u : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T)) {Y Y' : Over T}
    (a : Y'.left ⟶ Y.left) (ha : a ≫ Y.hom = Y'.hom) (x : P.obj.obj (op Y.left)) :
    evalHom P u Y' (P.obj.map a.op x) = H.map a.op (evalHom P u Y x) :=
  evalHom_naturality P u (Over.homMk a ha : Y' ⟶ Y) x

lemma mem_changeGroupSubfunctor_iff {T : C}
    (u : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T)) :
    u ∈ (changeGroupSubfunctor φ P).obj (op T) ↔
      ∀ (Y : Over T) (g : G.obj (op Y.left)) (x : P.obj.obj (op Y.left)),
        evalHom P u Y (g • x) = evalHom P u Y x * (φ.app (op Y.left) g)⁻¹ :=
  Iff.rfl

/-- The action of `H` on the sections of `presheafHom P.obj (H ⋙ forget GrpCat)` by left
multiplication on the values. -/
def homSMul {T : C} (h : H.obj (op T))
    (u : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T)) :
    (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T) :=
  mkHom P (fun Y x ↦ H.map Y.hom.op h * evalHom P u Y x) (fun {Y Y'} a x ↦ by
    rw [evalHom_naturality, map_mul, ← GrpCat.comp_apply, ← H.map_comp, ← op_comp, Over.w a])

@[simp]
lemma evalHom_homSMul {T : C} (h : H.obj (op T))
    (u : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T)) (Y : Over T)
    (x : P.obj.obj (op Y.left)) :
    evalHom P (homSMul P h u) Y x = H.map Y.hom.op h * evalHom P u Y x :=
  rfl

/-- The section `y ↦ φ(g)` with `y = g • x|Y`, attached to a section `x` of `P`. -/
noncomputable def homOfPoint {T : C} (x : P.obj.obj (op T)) :
    (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T) :=
  mkHom P (fun Y y ↦ φ.app (op Y.left) (P.diff y (P.obj.map Y.hom.op x))) (fun {Y Y'} a y ↦ by
    rw [← NatTrans.naturality_apply φ, P.map_diff, ← Functor.map_comp_apply, ← op_comp, Over.w a])

@[simp]
lemma evalHom_homOfPoint {T : C} (x : P.obj.obj (op T)) (Y : Over T)
    (y : P.obj.obj (op Y.left)) :
    evalHom P (homOfPoint φ P x) Y y = φ.app (op Y.left) (P.diff y (P.obj.map Y.hom.op x)) :=
  rfl

lemma homOfPoint_mem {T : C} (x : P.obj.obj (op T)) :
    homOfPoint φ P x ∈ (changeGroupSubfunctor φ P).obj (op T) := by
  intro Y g y
  simp [map_mul]

/-- The difference `u' x * (u x)⁻¹` of two sections of `changeGroupSubfunctor φ P`, which does
not depend on `x`. -/
def homDiff {T : C} (u u' : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T))
    (Y : Over T) (x : P.obj.obj (op Y.left)) : H.obj (op Y.left) :=
  evalHom P u' Y x * (evalHom P u Y x)⁻¹

lemma homDiff_naturality {T : C}
    (u u' : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T))
    {Y Y' : Over T} (a : Y'.left ⟶ Y.left) (ha : a ≫ Y.hom = Y'.hom)
    (x : P.obj.obj (op Y.left)) :
    H.map a.op (homDiff P u u' Y x) = homDiff P u u' Y' (P.obj.map a.op x) := by
  simp [homDiff, evalHom_naturality' P _ a ha]

lemma homDiff_mk_congr {T Z : C} {k k' : Z ⟶ T} (hk : k = k')
    (u u' : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T))
    (x : P.obj.obj (op Z)) :
    homDiff P u u' (Over.mk k) x = homDiff P u u' (Over.mk k') x := by
  subst hk
  rfl

variable {φ P}

lemma homSMul_mem {T : C} (h : H.obj (op T))
    {u : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T)}
    (hu : u ∈ (changeGroupSubfunctor φ P).obj (op T)) :
    homSMul P h u ∈ (changeGroupSubfunctor φ P).obj (op T) := by
  intro Y g x
  simp [hu Y g x, mul_assoc]

lemma homDiff_indep {T : C}
    {u u' : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T)}
    (hu : u ∈ (changeGroupSubfunctor φ P).obj (op T))
    (hu' : u' ∈ (changeGroupSubfunctor φ P).obj (op T)) (Y : Over T)
    (x y : P.obj.obj (op Y.left)) : homDiff P u u' Y x = homDiff P u u' Y y := by
  rw [← P.diff_smul x y, homDiff, homDiff, hu Y, hu' Y]
  group

lemma isSheaf_changeGroupSubfunctor (hH : Presieve.IsSheaf J (H ⋙ CategoryTheory.forget GrpCat)) :
    Presieve.IsSheaf J (changeGroupSubfunctor φ P).toFunctor := by
  have hHom : Presieve.IsSheaf J (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (Presheaf.IsSheaf.hom _ _ ((isSheaf_iff_isSheaf_of_type _ _).2 hH))
  rw [Subfunctor.isSheaf_iff _ hHom]
  intro T u hu Y g x
  apply (hH _ (J.pullback_stable Y.hom hu)).isSeparatedFor.ext
  intro Z a ha
  have h := ha (Over.mk (𝟙 Z)) (G.map a.op g) (P.obj.map a.op x)
  change evalHom P u ((Over.map (a ≫ Y.hom)).obj (Over.mk (𝟙 Z))) _ =
    evalHom P u ((Over.map (a ≫ Y.hom)).obj (Over.mk (𝟙 Z))) _ * _ at h
  have e₁ := evalHom_naturality' P u (Y' := (Over.map (a ≫ Y.hom)).obj (Over.mk (𝟙 Z)))
    a (by simp) (g • x)
  have e₂ := evalHom_naturality' P u (Y' := (Over.map (a ≫ Y.hom)).obj (Over.mk (𝟙 Z)))
    a (by simp) x
  change H.map a.op _ = H.map a.op _
  rw [← e₁, map_mul, ← e₂, map_smul', h, map_inv, ← NatTrans.naturality_apply φ]
  rfl

lemma existsUnique_homSMul (hH : Presieve.IsSheaf J (H ⋙ CategoryTheory.forget GrpCat))
    {T : C} {u u' : (presheafHom P.obj (H ⋙ CategoryTheory.forget GrpCat)).obj (op T)}
    (hu : u ∈ (changeGroupSubfunctor φ P).obj (op T))
    (hu' : u' ∈ (changeGroupSubfunctor φ P).obj (op T)) :
    ∃! h : H.obj (op T), homSMul P h u = u' := by
  let S := P.nonemptySieve T
  let d : Presieve.FamilyOfElements (H ⋙ CategoryTheory.forget GrpCat) S.arrows :=
    fun V f hf ↦ homDiff P u u' (Over.mk f) hf.some
  have hd : d.Compatible := by
    intro Z₁ Z₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    change H.map g₁.op (homDiff P u u' (Over.mk f₁) _) =
      H.map g₂.op (homDiff P u u' (Over.mk f₂) _)
    rw [homDiff_naturality P u u' (Y := Over.mk f₁) (Y' := Over.mk (g₁ ≫ f₁)) g₁ rfl,
      homDiff_naturality P u u' (Y := Over.mk f₂) (Y' := Over.mk (g₂ ≫ f₂)) g₂ rfl,
      homDiff_mk_congr P w]
    exact homDiff_indep hu hu' _ _ _
  have hS := P.nonemptySieve_mem T
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨h, hh, -⟩ := hH S hS d hd
    refine ⟨h, presheafHom_ext P fun Y x ↦ ?_⟩
    have hY : S Y.hom := ⟨x⟩
    have := hh Y.hom hY
    change H.map Y.hom.op h = homDiff P u u' (Over.mk Y.hom) hY.some at this
    rw [evalHom_homSMul, this, homDiff_indep hu hu' (Over.mk Y.hom) _ x]
    change homDiff P u u' Y x * _ = _
    simp [homDiff]
  · intro h₁ h₂ e₁ e₂
    apply (hH S hS).isSeparatedFor.ext
    intro V f hf
    have k₁ := congr_arg (fun v ↦ evalHom P v (Over.mk f) hf.some) e₁
    have k₂ := congr_arg (fun v ↦ evalHom P v (Over.mk f) hf.some) e₂
    simp only [evalHom_homSMul] at k₁ k₂
    have := mul_right_cancel (k₁.trans k₂.symm)
    exact this

variable (φ P) in
/-- The torsor structure on the sheaf of maps `u : P ⟶ H` with `u (g • x) = u x * φ(g)⁻¹`. -/
noncomputable def changeGroupIsTorsorOf
    (hH : Presieve.IsSheaf J (H ⋙ CategoryTheory.forget GrpCat)) :
    IsTorsorOf J H (changeGroupSubfunctor φ P).toFunctor where
  isSheaf := isSheaf_changeGroupSubfunctor hH
  smul U h u := ⟨homSMul P h u.1, homSMul_mem h u.2⟩
  one_smul U u := Subtype.ext (presheafHom_ext P fun Y x ↦ by simp)
  mul_smul U h h' u := Subtype.ext (presheafHom_ext P fun Y x ↦ by simp [mul_assoc])
  map_smul {U V} f h u := Subtype.ext (presheafHom_ext P fun Y x ↦ by
    have : H.map ((Over.map f.unop).obj Y).hom.op h = H.map Y.hom.op (H.map f h) := by
      rw [← GrpCat.comp_apply, ← H.map_comp]
      rfl
    exact congr_arg (· * evalHom P u.1 ((Over.map f.unop).obj Y) x) this)
  existsUnique_smul U u u' := by
    obtain ⟨h, hh, hh'⟩ := existsUnique_homSMul hH u.2 u'.2
    exact ⟨h, Subtype.ext hh, fun h' e ↦ hh' h' (congr_arg Subtype.val e)⟩
  locallyNonempty U := ⟨P.nonemptySieve U, P.nonemptySieve_mem U,
    fun V f hf ↦ ⟨⟨homOfPoint φ P hf.some, homOfPoint_mem φ P _⟩⟩⟩

variable (φ) in
/-- The change of the structure group of a torsor along `φ : G ⟶ H`: the `H`-torsor
`φ_* P = P ∧^G H`. -/
noncomputable def changeGroup (hH : Presieve.IsSheaf J (H ⋙ CategoryTheory.forget GrpCat))
    (P : Torsor J G) : Torsor J H :=
  ofLarge (changeGroupIsTorsorOf φ P hH)

variable (φ) in
/-- The canonical `φ`-equivariant morphism `P ⟶ φ_* P`, sending `x` to the map
`y ↦ φ(g)` where `y = g • x`. -/
noncomputable def toChangeGroup (hH : Presieve.IsSheaf J (H ⋙ CategoryTheory.forget GrpCat))
    (P : Torsor J G) : HomOver φ P (P.changeGroup φ hH) where
  hom :=
    { app U := ↾fun x ↦ ofLargeEquiv (changeGroupIsTorsorOf φ P hH) U
        ⟨homOfPoint φ P (T := U.unop) x, homOfPoint_mem φ P _⟩
      naturality U V f := by
        ext x
        refine Eq.trans ?_ (ofLargeEquiv_naturality _ f _)
        change ofLargeEquiv (changeGroupIsTorsorOf φ P hH) V
          ⟨homOfPoint φ P (T := V.unop) (P.obj.map f x), homOfPoint_mem φ P _⟩ = _
        congr 1
        apply Subtype.ext
        refine presheafHom_ext P fun Y y ↦ ?_
        change φ.app _ (P.diff y (P.obj.map Y.hom.op (P.obj.map f x))) =
          φ.app _ (P.diff y (P.obj.map (Y.hom ≫ f.unop).op x))
        rw [op_comp, Functor.map_comp_apply]
        rfl }
  map_smul U g x := by
    refine Eq.trans ?_ (ofLargeEquiv_smul _ (φ.app U g) _)
    change ofLargeEquiv (changeGroupIsTorsorOf φ P hH) U _ = _
    congr 1
    apply Subtype.ext
    refine presheafHom_ext P fun Y y ↦ ?_
    change φ.app _ (P.diff y (P.obj.map Y.hom.op (g • x))) =
      H.map Y.hom.op (φ.app U g) * φ.app _ (P.diff y (P.obj.map Y.hom.op x))
    rw [map_smul', diff_smul_right, map_mul, NatTrans.naturality_apply φ]

variable {Q : Torsor J H}

/-- The map `Q ⟶ φ_* P` attached to a `φ`-equivariant morphism `ψ : P ⟶ Q`: it sends `q` to
the map `x ↦ h` where `q = h • ψ x`. -/
noncomputable def homOfHomOver (hH : Presieve.IsSheaf J (H ⋙ CategoryTheory.forget GrpCat))
    (ψ : HomOver φ P Q) : Q ⟶ P.changeGroup φ hH where
  hom :=
    { app U := ↾fun q ↦ ofLargeEquiv (changeGroupIsTorsorOf φ P hH) U
        ⟨mkHom P (T := U.unop) (fun Y x ↦ Q.diff (ψ.hom.app _ x) (Q.obj.map Y.hom.op q))
          (fun {Y Y'} a x ↦ by
            rw [NatTrans.naturality_apply, Q.map_diff, ← Functor.map_comp_apply, ← op_comp,
              Over.w a]),
          fun Y g x ↦ by simp⟩
      naturality U V f := by
        ext q
        refine Eq.trans ?_ (ofLargeEquiv_naturality _ f _)
        change ofLargeEquiv (changeGroupIsTorsorOf φ P hH) V ⟨mkHom P (T := V.unop)
          (fun Y x ↦ Q.diff (ψ.hom.app _ x) (Q.obj.map Y.hom.op (Q.obj.map f q))) _, _⟩ = _
        congr 1
        apply Subtype.ext
        refine presheafHom_ext P fun Y y ↦ ?_
        change Q.diff _ (Q.obj.map Y.hom.op (Q.obj.map f q)) =
          Q.diff _ (Q.obj.map (Y.hom ≫ f.unop).op q)
        rw [op_comp, Functor.map_comp_apply]
        rfl }
  map_smul U h q := by
    refine Eq.trans ?_ (ofLargeEquiv_smul _ h _)
    change ofLargeEquiv (changeGroupIsTorsorOf φ P hH) U _ = _
    congr 1
    apply Subtype.ext
    refine presheafHom_ext P fun Y y ↦ ?_
    change Q.diff _ (Q.obj.map Y.hom.op (h • q)) = H.map Y.hom.op h * Q.diff _ _
    rw [map_smul', diff_smul_right]

/-- An `H`-torsor with a `φ`-equivariant morphism from `P` is isomorphic to `φ_* P`. -/
noncomputable def changeGroupIsoOfHomOver
    (hH : Presieve.IsSheaf J (H ⋙ CategoryTheory.forget GrpCat)) (ψ : HomOver φ P Q) :
    P.changeGroup φ hH ≅ Q :=
  (asIso (homOfHomOver hH ψ)).symm

/-- A `φ`-equivariant morphism followed by a morphism of torsors. -/
@[simps]
def HomOver.compHom {Q' : Torsor J H} (a : HomOver φ P Q) (b : Q ⟶ Q') : HomOver φ P Q' where
  hom := a.hom ≫ b.hom
  map_smul U g x := by simp

/-- A morphism of torsors followed by a `φ`-equivariant morphism. -/
@[simps]
def HomOver.homComp {P' : Torsor J G} (b : P' ⟶ P) (a : HomOver φ P Q) : HomOver φ P' Q where
  hom := b.hom ≫ a.hom
  map_smul U g x := by simp

lemma nonempty_changeGroup_iso_iff (hH : Presieve.IsSheaf J (H ⋙ CategoryTheory.forget GrpCat)) :
    Nonempty (P.changeGroup φ hH ≅ Q) ↔ Nonempty (HomOver φ P Q) :=
  ⟨fun ⟨e⟩ ↦ ⟨(toChangeGroup φ hH P).compHom e.hom⟩,
    fun ⟨ψ⟩ ↦ ⟨changeGroupIsoOfHomOver hH ψ⟩⟩

end ChangeGroup

section H1Map

variable (φ : G ⟶ H) (hH : Presieve.IsSheaf J (H ⋙ CategoryTheory.forget GrpCat))

variable {φ hH} {P : Torsor J G}

/-- The value of an equivariant morphism to the trivial torsor, as an element of `H`. -/
def HomOver.val (ψ : HomOver φ P (trivial J H hH)) {U : Cᵒᵖ} (x : P.obj.obj U) : H.obj U :=
  ψ.hom.app U x

lemma HomOver.val_smul (ψ : HomOver φ P (trivial J H hH)) {U : Cᵒᵖ} (g : G.obj U)
    (x : P.obj.obj U) : ψ.val (g • x) = φ.app U g * ψ.val x :=
  ψ.map_smul U g x

lemma HomOver.val_naturality (ψ : HomOver φ P (trivial J H hH)) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : P.obj.obj U) : ψ.val (P.obj.map f x) = H.map f (ψ.val x) :=
  NatTrans.naturality_apply ψ.hom f x

variable (φ hH)

/-- The `φ`-equivariant morphism `G ⟶ H` between trivial torsors. -/
@[simps]
def trivialHomOver (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat)) :
    HomOver φ (trivial J G hG) (trivial J H hH) where
  hom := Functor.whiskerRight φ (CategoryTheory.forget GrpCat)
  map_smul U g x := map_mul (φ.app U).hom g x

end H1Map

end Torsor

namespace H1

variable (φ : G ⟶ H) (hH : Presieve.IsSheaf J (H ⋙ CategoryTheory.forget GrpCat))

/-- The map `H¹(G) ⟶ H¹(H)` induced by a morphism of sheaves of groups `φ : G ⟶ H`. -/
noncomputable def map : H1 J G → H1 J H :=
  _root_.Quotient.map (Torsor.changeGroup φ hH) fun _ P' ⟨e⟩ ↦
    ⟨Torsor.changeGroupIsoOfHomOver hH ((Torsor.toChangeGroup φ hH P').homComp e.hom)⟩

lemma map_class (P : Torsor J G) : map φ hH P.class = (P.changeGroup φ hH).class :=
  rfl

lemma map_class_eq_class_iff (P : Torsor J G) (Q : Torsor J H) :
    map φ hH P.class = Q.class ↔ Nonempty (Torsor.HomOver φ P Q) := by
  rw [map_class, Torsor.class_eq_class_iff, Torsor.nonempty_changeGroup_iso_iff]

lemma map_trivialClass (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat)) :
    map φ hH (trivialClass J G hG) = trivialClass J H hH :=
  (map_class_eq_class_iff φ hH _ _).2 ⟨Torsor.trivialHomOver φ hH hG⟩

lemma map_id (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat)) (c : H1 J G) :
    map (𝟙 G) hG c = c := by
  obtain ⟨P, rfl⟩ := mk_surjective c
  exact (map_class_eq_class_iff _ _ _ _).2 ⟨Torsor.HomOver.ofHom (𝟙 P)⟩

lemma map_map (ψ : H ⟶ K) (hK : Presieve.IsSheaf J (K ⋙ CategoryTheory.forget GrpCat))
    (c : H1 J G) : map ψ hK (map φ hH c) = map (φ ≫ ψ) hK c := by
  obtain ⟨P, rfl⟩ := mk_surjective c
  rw [map_class, map_class, map_class, Torsor.class_eq_class_iff]
  exact ⟨(Torsor.changeGroupIsoOfHomOver hK
    ((Torsor.toChangeGroup φ hH P).comp (Torsor.toChangeGroup ψ hK _))).symm⟩

end H1

end CategoryTheory
