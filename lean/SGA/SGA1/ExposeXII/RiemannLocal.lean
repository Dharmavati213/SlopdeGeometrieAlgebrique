/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannFull
import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# SGA 1, Exposé XII, 5.1: the Riemann existence theorem is local on `X`

SGA reduces XII.5.1 to the affine case by full faithfulness of `Ψ : Y ↦ Y(ℂ)` (step 1) of the
proof): finite étale coverings of `X` glue along open covers, and so do finite coverings of
`X(ℂ)`. Here we glue a finite covering `E` of `X(ℂ)` from *local models* over a family of
affine opens of `X` forming a basis of the topology (`RiemannLocal.AffineOpenBasis`; e.g. all
affine opens, those contained in a member of an open cover, or basic opens): for every `U` in
the family, a finite étale `π_U : Y_U → U` with an open embedding `φ_U : Y_U(ℂ) → E` onto the
part of `E` over `U(ℂ)`, compatible with the projections (`RiemannLocal.LocalModels`).

* The transition morphisms `Y_U → Y_V` for `U ⊆ V` come from `SchemePoints.exists_hom_map_eq`
  (step 1) of XII.5.1), are unique by `SchemePoints.eq_of_forall_comp_eq`, and make the squares
  over `U → V` cartesian (`SchemePoints.isIso_of_bijective_map`), so they form a relative gluing
  datum (mathlib's `Scheme.Cover.RelativeGluingData`, Stacks 01LH) over the directed cover of `X`
  by the family (`RiemannLocal.AffineOpenBasis.cover`).
* The glued `Y → X` is finite étale (both properties are local on the target), and
  `Ψ(Y) ≅ E` (`RiemannLocal.LocalModels.mem_essImage`): the map `E → Y(ℂ)` given locally by
  `φ_U⁻¹` is a continuous bijection over `X(ℂ)`, hence a homeomorphism (it is a local
  homeomorphism, both projections being covering maps).

The affine input (local models from the affine form of XII.5.1 for `Γ(X, U)`) and the resulting
reduction of `SchemeRiemannExistenceStatement` to `RiemannExistenceStatement` are in
`SGA.SGA1.ExposeXII.RiemannLocalChart`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology Set AlgebraicGeometry

namespace SGA.SGA1.ExposeXII

namespace RiemannLocal

/-- A family of affine opens of `X` (a predicate `P` on opens) forming a basis of the topology:
every neighbourhood of a point contains a member of the family containing the point. E.g. all
affine opens (`AffineOpenBasis.top`), the affine opens contained in some member of an open cover,
or the basic opens `D(g)` of an affine scheme. Local models are glued over such a family. -/
structure AffineOpenBasis (X : Scheme.{u}) where
  /-- The opens of the family. -/
  P : X.Opens → Prop
  isAffineOpen : ∀ {U}, P U → IsAffineOpen U
  exists_le : ∀ {x : X} {W : X.Opens}, x ∈ W → ∃ U, P U ∧ x ∈ U ∧ U ≤ W

namespace AffineOpenBasis

/-- All affine opens. -/
def top (X : Scheme.{u}) : AffineOpenBasis X where
  P U := IsAffineOpen U
  isAffineOpen h := h
  exists_le {x W} hxW := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
    exact ⟨U, hU, hxU, hUW⟩

variable {X : Scheme.{u}} (B : AffineOpenBasis X)

/-- The index type: the opens of the family. -/
abbrev I : Type u := {U : X.Opens // B.P U}

lemma exists_mem (x : X) : ∃ U, B.P U ∧ x ∈ U :=
  let ⟨U, hU, hxU, _⟩ := B.exists_le (W := ⊤) (show x ∈ (⊤ : X.Opens) from trivial)
  ⟨U, hU, hxU⟩

/-- Every point of `X` lies in a member of the family, as an element of the index type. -/
lemma exists_mem_I (x : X) : ∃ U : B.I, x ∈ U.1 :=
  let ⟨U, hU, h⟩ := B.exists_mem x
  ⟨⟨U, hU⟩, h⟩

lemma exists_le_of_mem {x : X} {U V : X.Opens} (hxU : x ∈ U) (hxV : x ∈ V) :
    ∃ W : B.I, x ∈ W.1 ∧ W.1 ≤ U ∧ W.1 ≤ V := by
  obtain ⟨W, hW, hxW, hWUV⟩ := B.exists_le (W := U ⊓ V) ⟨hxU, hxV⟩
  exact ⟨⟨W, hW⟩, hxW, fun z hz ↦ (hWUV hz).1, fun z hz ↦ (hWUV hz).2⟩

lemma isBasis : TopologicalSpace.Opens.IsBasis (range fun U : B.I ↦ U.1.ι.opensRange) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro W x hxW
  obtain ⟨V, hV, hxV, hVW⟩ := B.exists_le hxW
  exact ⟨V, ⟨⟨V, hV⟩, Scheme.Opens.opensRange_ι _⟩, hxV, hVW⟩

/-- The open cover of `X` by the opens of the family. -/
@[simps I₀ X f]
def cover : X.OpenCover where
  I₀ := B.I
  X U := U.1
  f U := U.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨U, hU, hxU⟩ := B.exists_mem x
    exact ⟨⟨U, hU⟩, by simpa using hxU⟩

instance : Preorder B.cover.I₀ := inferInstanceAs <| Preorder B.I

-- As in mathlib's `Scheme.Cover.ColimitGluingData`: `B.cover.I₀` is `B.I` only up to unfolding,
-- and the `homOfLE` simp lemmas are only found with backward `defeq` attributes.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance : Scheme.Cover.LocallyDirected B.cover :=
  .ofIsBasisOpensRange (by intros; simp; rfl) B.isBasis

@[simp]
lemma cover_trans {U V : B.I} (h : U ≤ V) :
    Scheme.Cover.trans B.cover (homOfLE h) = X.homOfLE h := rfl

end AffineOpenBasis

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]

/-- The `ℂ`-structure of a scheme `Y` over `X`, through `f : Y ⟶ X`. -/
abbrev overVia {Y : Scheme.{0}} (f : Y ⟶ X) : Y.Over (Spec (.of ℂ)) :=
  .ofHom (f ≫ X ↘ Spec (.of ℂ))

lemma isOverVia {Y : Scheme.{0}} (f : Y ⟶ X) :
    letI := overVia f
    f.IsOver (Spec (.of ℂ)) :=
  letI := overVia f
  ⟨rfl⟩

variable (B : AffineOpenBasis X) (E : TopCat.FiniteCovering (TopCat.of (SchemePoints ℂ X)))

/-- Local models of a finite covering `E` of `X(ℂ)` over the affine opens of a family `B`: for
every `U` in `B`, a finite étale `π_U : Y_U → U` and an open embedding `φ_U : Y_U(ℂ) → E` whose
image is the part of `E` over `U(ℂ)`, compatible with the projections to `X(ℂ)`. (The
`ℂ`-structure of `Y_U` is the one through `Y_U → U ⊆ X`.) -/
structure LocalModels where
  /-- The finite étale covering `Y_U` of `U`. -/
  Y : B.I → Scheme.{0}
  /-- Its projection to `U`. -/
  π : ∀ U, Y U ⟶ U.1.toScheme
  isFinite : ∀ U, IsFinite (π U)
  etale : ∀ U, Etale (π U)
  /-- The identification of `Y_U(ℂ)` with the part of `E` over `U(ℂ)`. -/
  φ : ∀ U, letI := overVia (π U ≫ U.1.ι); SchemePoints ℂ (Y U) → E.obj.left
  isOpenEmbedding : ∀ U, letI := overVia (π U ≫ U.1.ι); IsOpenEmbedding (φ U)
  range_φ : ∀ U, range (φ U) = E.obj.hom ⁻¹' {x | x.pt ∈ U.1}
  hom_φ : ∀ U, letI := overVia (π U ≫ U.1.ι); haveI := isOverVia (π U ≫ U.1.ι);
    ∀ y, E.obj.hom (φ U y) = SchemePoints.map (π U ≫ U.1.ι) y

namespace LocalModels

variable {B E} (M : LocalModels B E)

/-- The `ℂ`-structure of `Y_U`. -/
abbrev instOverY (U : B.I) : (M.Y U).Over (Spec (.of ℂ)) := overVia (M.π U ≫ U.1.ι)

/-- The `ℂ`-structure of an open `U` of `X`. -/
abbrev instOverOpens (U : X.Opens) : U.toScheme.Over (Spec (.of ℂ)) := overVia U.ι

attribute [local instance] instOverY instOverOpens

instance (U : X.Opens) : U.ι.IsOver (Spec (.of ℂ)) := isOverVia U.ι

instance (U : B.I) : (M.π U).IsOver (Spec (.of ℂ)) :=
  ⟨(Category.assoc _ _ _).symm⟩

instance (U : B.I) : (M.π U ≫ U.1.ι).IsOver (Spec (.of ℂ)) :=
  isOverVia (M.π U ≫ U.1.ι)

instance {U V : X.Opens} (h : U ≤ V) : (X.homOfLE h).IsOver (Spec (.of ℂ)) := ⟨by
  change X.homOfLE h ≫ V.ι ≫ X ↘ Spec (.of ℂ) = U.ι ≫ X ↘ Spec (.of ℂ)
  rw [← Category.assoc, Scheme.homOfLE_ι]⟩

instance (U : B.I) : IsFinite (M.π U) := M.isFinite U

instance (U : B.I) : Etale (M.π U) := M.etale U

lemma val_hom_φ (U : B.I) (y : SchemePoints ℂ (M.Y U)) :
    (E.obj.hom (M.φ U y)).1 = y.1 ≫ M.π U ≫ U.1.ι :=
  congrArg Subtype.val (M.hom_φ U y)

lemma mem_range_φ {U : B.I} {e : E.obj.left} (he : (E.obj.hom e).pt ∈ U.1) :
    e ∈ range (M.φ U) := by
  rw [M.range_φ U]
  exact he

lemma pt_hom_φ_mem (U : B.I) (y : SchemePoints ℂ (M.Y U)) :
    (E.obj.hom (M.φ U y)).pt ∈ U.1 := by
  have := M.range_φ U ▸ mem_range_self (f := M.φ U) y
  exact this

lemma φ_injective (U : B.I) : Function.Injective (M.φ U) :=
  (M.isOpenEmbedding U).injective

lemma isOver_of_comp_eq {U V : B.I} (h : U ≤ V) (g : M.Y U ⟶ M.Y V)
    (hg : g ≫ M.π V = M.π U ≫ X.homOfLE h) : g.IsOver (Spec (.of ℂ)) := ⟨by
  change g ≫ (M.π V ≫ V.1.ι) ≫ X ↘ Spec (.of ℂ) = (M.π U ≫ U.1.ι) ≫ X ↘ Spec (.of ℂ)
  rw [← Category.assoc, ← Category.assoc, hg, Category.assoc, Category.assoc,
    Scheme.homOfLE_ι_assoc, Category.assoc]⟩

variable [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]

instance (U : X.Opens) : LocallyOfFiniteType (U.toScheme ↘ Spec (.of ℂ)) := by
  change LocallyOfFiniteType (U.ι ≫ X ↘ Spec (.of ℂ))
  infer_instance

instance (U : B.I) : LocallyOfFiniteType (M.Y U ↘ Spec (.of ℂ)) := by
  change LocallyOfFiniteType ((M.π U ≫ U.1.ι) ≫ X ↘ Spec (.of ℂ))
  infer_instance

/-- Morphisms between local models over `ℂ` are determined by their effect on `E`. -/
lemma eq_of_φ_map_eq {U V : B.I} (a b : M.Y U ⟶ M.Y V) [a.IsOver (Spec (.of ℂ))]
    [b.IsOver (Spec (.of ℂ))] (hab : a ≫ M.π V = b ≫ M.π V)
    (h : ∀ y, M.φ V (SchemePoints.map a y) = M.φ V (SchemePoints.map b y)) : a = b :=
  SchemePoints.eq_of_forall_comp_eq (K := ℂ) (M.π V) a b hab fun y ↦
    congrArg Subtype.val (M.φ_injective V (h y))

/-- XII.5.1, proof of 2): the transition morphisms of the local models, from step 1)
(`SchemePoints.exists_hom_map_eq`). -/
theorem exists_trans {U V : B.I} (h : U ≤ V) :
    ∃ g : M.Y U ⟶ M.Y V, g ≫ M.π V = M.π U ≫ X.homOfLE h ∧
      ∃ _ : g.IsOver (Spec (.of ℂ)), ∀ y, M.φ V (SchemePoints.map g y) = M.φ U y := by
  have hmem (y : SchemePoints ℂ (M.Y U)) : M.φ U y ∈ range (M.φ V) :=
    M.mem_range_φ (h (M.pt_hom_φ_mem U y))
  choose u hu using hmem
  have hcont : Continuous u :=
    (M.isOpenEmbedding V).isEmbedding.continuous_iff.mpr (by
      have : M.φ V ∘ u = M.φ U := funext hu
      rw [this]
      exact (M.isOpenEmbedding U).continuous)
  have hpu (y : SchemePoints ℂ (M.Y U)) :
      SchemePoints.map (M.π V) (u y) = SchemePoints.map (M.π U ≫ X.homOfLE h) y := by
    refine SchemePoints.ext ((cancel_mono V.1.ι).mp ?_)
    change (u y).1 ≫ M.π V ≫ V.1.ι = y.1 ≫ M.π U ≫ X.homOfLE h ≫ V.1.ι
    rw [Scheme.homOfLE_ι, ← M.val_hom_φ, ← M.val_hom_φ, hu]
  obtain ⟨g, hg, _, hgu⟩ := SchemePoints.exists_hom_map_eq (M.π U ≫ X.homOfLE h) (M.π V) u
    hcont hpu
  exact ⟨g, hg, inferInstance, fun y ↦ by rw [hgu, hu]⟩

/-- The transition morphism `Y_U → Y_V` of the local models, for `U ⊆ V`. -/
def trans {U V : B.I} (h : U ≤ V) : M.Y U ⟶ M.Y V := (M.exists_trans h).choose

@[reassoc]
lemma trans_π {U V : B.I} (h : U ≤ V) : M.trans h ≫ M.π V = M.π U ≫ X.homOfLE h :=
  (M.exists_trans h).choose_spec.1

instance {U V : B.I} (h : U ≤ V) : (M.trans h).IsOver (Spec (.of ℂ)) :=
  M.isOver_of_comp_eq h _ (M.trans_π h)

lemma φ_map_trans {U V : B.I} (h : U ≤ V) (y : SchemePoints ℂ (M.Y U)) :
    M.φ V (SchemePoints.map (M.trans h) y) = M.φ U y := by
  obtain ⟨_, h'⟩ := (M.exists_trans h).choose_spec.2
  exact h' y

lemma trans_refl (U : B.I) : M.trans (le_refl U) = 𝟙 _ := by
  refine M.eq_of_φ_map_eq _ _ ?_ fun y ↦ ?_
  · rw [trans_π, Category.id_comp, X.homOfLE_rfl, Category.comp_id]
  · rw [φ_map_trans, SchemePoints.map_id, id]

lemma trans_trans {U V W : B.I} (h₁ : U ≤ V) (h₂ : V ≤ W) :
    M.trans h₁ ≫ M.trans h₂ = M.trans (h₁.trans h₂) := by
  refine M.eq_of_φ_map_eq _ _ ?_ fun y ↦ ?_
  · rw [Category.assoc, trans_π, trans_π_assoc, trans_π, Scheme.homOfLE_homOfLE]
  · rw [SchemePoints.map_comp, Function.comp_apply, φ_map_trans, φ_map_trans, φ_map_trans]

section Pullback

attribute [local instance] SchemePoints.pullbackOver SchemePoints.isOver_pullback_fst
  SchemePoints.isOver_pullback_snd

/-- XII.5.1, proof of 2): the local models restrict to each other: for `U ⊆ V`, the square
`Y_U → Y_V` over `U → V` is cartesian. The comparison map `Y_U → Y_V ×_V U` is a morphism of
finite étale `U`-schemes which is bijective on `ℂ`-points (both are identified with the part of
`E` over `U(ℂ)`), hence an isomorphism (`SchemePoints.isIso_of_bijective_map`). -/
theorem isPullback_trans {U V : B.I} (h : U ≤ V) :
    IsPullback (M.trans h) (M.π U) (M.π V) (X.homOfLE h) := by
  let c : M.Y U ⟶ pullback (M.π V) (X.homOfLE h) := pullback.lift (M.trans h) (M.π U) (M.trans_π h)
  have hc : ExposeV.finiteEtaleHom c := by
    have h₁ : ExposeV.finiteEtaleHom (c ≫ pullback.snd (M.π V) (X.homOfLE h)) := by
      rw [pullback.lift_snd]
      exact ⟨M.isFinite U, M.etale U⟩
    have h₂ : ExposeV.finiteEtaleHom (pullback.snd (M.π V) (X.homOfLE h)) :=
      ExposeV.finiteEtaleHom.pullback_snd _ _ ⟨M.isFinite V, M.etale V⟩
    exact MorphismProperty.of_postcomp _ _ _ h₂ h₁
  have : IsFinite c := hc.1
  have : Etale c := hc.2
  have : c.IsOver (Spec (.of ℂ)) := ⟨by
    change c ≫ pullback.fst _ _ ≫ (M.Y V) ↘ Spec (.of ℂ) = (M.Y U) ↘ Spec (.of ℂ)
    rw [pullback.lift_fst_assoc, comp_over]⟩
  have : LocallyOfFiniteType (pullback (M.π V) (X.homOfLE h) ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (pullback.fst (M.π V) (X.homOfLE h) ≫ (M.Y V) ↘ Spec (.of ℂ))
    infer_instance
  have hfst (y : SchemePoints ℂ (M.Y U)) :
      SchemePoints.map (pullback.fst _ _) (SchemePoints.map c y) =
        SchemePoints.map (M.trans h) y :=
    SchemePoints.ext (by
      change (y.1 ≫ c) ≫ pullback.fst _ _ = y.1 ≫ M.trans h
      rw [Category.assoc, pullback.lift_fst])
  have hsnd (y : SchemePoints ℂ (M.Y U)) :
      SchemePoints.map (pullback.snd _ _) (SchemePoints.map c y) = SchemePoints.map (M.π U) y :=
    SchemePoints.ext (by
      change (y.1 ≫ c) ≫ pullback.snd _ _ = y.1 ≫ M.π U
      rw [Category.assoc, pullback.lift_snd])
  have hbij : Function.Bijective (SchemePoints.map (K := ℂ) c) := by
    constructor
    · intro y y' hyy'
      apply M.φ_injective U
      rw [← M.φ_map_trans h y, ← M.φ_map_trans h y', ← hfst, ← hfst, hyy']
    · intro r
      let a := SchemePoints.map (pullback.fst (M.π V) (X.homOfLE h)) r
      let b := SchemePoints.map (pullback.snd (M.π V) (X.homOfLE h)) r
      have hab : E.obj.hom (M.φ V a) = SchemePoints.map U.1.ι b := by
        rw [M.hom_φ V a]
        refine SchemePoints.ext ?_
        change (r.1 ≫ pullback.fst _ _) ≫ M.π V ≫ V.1.ι = (r.1 ≫ pullback.snd _ _) ≫ U.1.ι
        rw [Category.assoc, pullback.condition_assoc, Scheme.homOfLE_ι, Category.assoc]
      obtain ⟨y, hy⟩ := M.mem_range_φ (U := U) (e := M.φ V a) (by
        rw [hab, SchemePoints.pt_map]
        change U.1.ι b.pt ∈ (U.1 : Set X)
        rw [← Scheme.Opens.range_ι]
        exact mem_range_self _)
      have hya : SchemePoints.map (M.trans h) y = a :=
        M.φ_injective V (by rw [M.φ_map_trans, hy])
      have hyb : SchemePoints.map (M.π U) y = b := by
        apply SchemePoints.map_injective U.1.ι
        rw [← Function.comp_apply (f := SchemePoints.map U.1.ι), ← SchemePoints.map_comp,
          ← M.hom_φ U y, hy, hab]
      refine ⟨y, (SchemePoints.pullbackEquiv (K := ℂ) (M.π V) (X.homOfLE h)).injective ?_⟩
      refine Subtype.ext (Prod.ext ?_ ?_)
      · exact (hfst y).trans hya
      · exact (hsnd y).trans hyb
  have : IsIso c := SchemePoints.isIso_of_bijective_map c hbij
  exact IsPullback.of_iso_pullback ⟨M.trans_π h⟩ (asIso c) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

end Pullback

/-- The local models as a diagram over the affine opens of `X`. -/
@[simps]
def functor : B.cover.I₀ ⥤ Scheme.{0} where
  obj U := M.Y U
  map f := M.trans (leOfHom f)
  map_id U := M.trans_refl U
  map_comp _ _ := (M.trans_trans _ _).symm

/-- The projections `Y_U → U`, as a natural transformation. -/
@[simps]
def natTrans : M.functor ⟶ B.cover.functorOfLocallyDirected where
  app U := M.π U
  naturality _ _ f := M.trans_π (leOfHom f)

/-- XII.5.1, proof of 2): the local models form a relative gluing datum over the directed cover of
`X` by its affine opens (Stacks 01LH). -/
def gluingData : B.cover.RelativeGluingData where
  functor := M.functor
  natTrans := M.natTrans
  equifibered _ _ f := M.isPullback_trans (leOfHom f)

-- As in mathlib's `Scheme.Cover.ColimitGluingData.glued`: the index types of the cover and of its
-- pullback only agree up to unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- A property local on the target holds for the glued morphism `Y → X` if it holds for every
`π_U`. -/
lemma toBase_of_forall (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hP : ∀ U, P (M.π U)) : P M.gluingData.toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) B.cover]
  intro U
  rw [Scheme.Cover.pullbackHom,
    ← (M.gluingData.isPullback_natTrans_ι_toBase U).flip.isoPullback_inv_snd,
    P.cancel_left_of_respectsIso]
  exact hP U

-- `IsZariskiLocalAtTarget (@IsFinite ⊓ @Etale)` is only found with this option (as in
-- `ExposeV.FEt.finiteEtale_sigmaDesc`).
set_option backward.isDefEq.respectTransparency false in
/-- XII.5.1, proof of 2): the finite étale covering of `X` glued from the local models. -/
def glued : FiniteEtaleCovering X :=
  MorphismProperty.Over.mk ⊤ M.gluingData.toBase <|
    have : IsZariskiLocalAtTarget ExposeV.finiteEtaleHom.{0} :=
      inferInstanceAs (IsZariskiLocalAtTarget (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{0}))
    M.toBase_of_forall _ fun U ↦ ⟨M.isFinite U, M.etale U⟩

section Comparison

/-- The `ℂ`-structure of the glued scheme `Y` (through `Y → X`). -/
abbrev instOverGlued : M.gluingData.glued.Over (Spec (.of ℂ)) := overOfCovering ℂ X M.glued

attribute [local instance] instOverGlued

/-- The open immersion `Y_U → Y` into the glued scheme. -/
abbrev ι (U : B.I) : M.Y U ⟶ M.gluingData.glued := colimit.ι M.gluingData.functor U

@[reassoc]
lemma ι_toBase (U : B.I) : M.ι U ≫ M.gluingData.toBase = M.π U ≫ U.1.ι :=
  M.gluingData.ι_toBase U

instance (U : B.I) : (M.ι U).IsOver (Spec (.of ℂ)) := ⟨by
  change M.ι U ≫ M.gluingData.toBase ≫ X ↘ Spec (.of ℂ) = (M.π U ≫ U.1.ι) ≫ X ↘ Spec (.of ℂ)
  rw [ι_toBase_assoc, Category.assoc]⟩

instance : M.gluingData.toBase.IsOver (Spec (.of ℂ)) := ⟨rfl⟩

lemma map_ι_map_trans {U V : B.I} (h : U ≤ V) (y : SchemePoints ℂ (M.Y U)) :
    SchemePoints.map (M.ι V) (SchemePoints.map (M.trans h) y) = SchemePoints.map (M.ι U) y :=
  SchemePoints.ext (by
    change (y.1 ≫ M.trans h) ≫ M.ι V = y.1 ≫ M.ι U
    rw [Category.assoc]
    exact congrArg (y.1 ≫ ·) (colimit.w M.gluingData.functor (homOfLE h)))

lemma map_toBase_map_ι (U : B.I) (y : SchemePoints ℂ (M.Y U)) :
    SchemePoints.map M.gluingData.toBase (SchemePoints.map (M.ι U) y) = E.obj.hom (M.φ U y) :=
  SchemePoints.ext (by
    rw [M.val_hom_φ]
    change (y.1 ≫ M.ι U) ≫ M.gluingData.toBase = _
    rw [Category.assoc, ι_toBase])

/-- Points of different local models with the same image in `E` have the same image in the
glued scheme. -/
lemma map_ι_eq_of_φ_eq {U V : B.I} (a : SchemePoints ℂ (M.Y U))
    (b : SchemePoints ℂ (M.Y V)) (hab : M.φ U a = M.φ V b) :
    SchemePoints.map (M.ι U) a = SchemePoints.map (M.ι V) b := by
  obtain ⟨W, hxW, hWU, hWV⟩ := B.exists_le_of_mem (M.pt_hom_φ_mem U a)
    (hab ▸ M.pt_hom_φ_mem V b)
  obtain ⟨c, hc⟩ := M.mem_range_φ (U := W) hxW
  have hca : SchemePoints.map (M.trans (U := W) (V := U) hWU) c = a :=
    M.φ_injective U (by rw [M.φ_map_trans, hc])
  have hcb : SchemePoints.map (M.trans (U := W) (V := V) hWV) c = b :=
    M.φ_injective V (by rw [M.φ_map_trans, hc, hab])
  rw [← hca, ← hcb, map_ι_map_trans, map_ι_map_trans]

omit [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] in
lemma toHomeomorph_symm_eq (U : B.I) {e : E.obj.left} (he : e ∈ range (M.φ U))
    {y : SchemePoints ℂ (M.Y U)} (hy : M.φ U y = e) :
    (M.isOpenEmbedding U).isEmbedding.toHomeomorph.symm ⟨e, he⟩ = y := by
  subst hy
  exact IsEmbedding.toHomeomorph_symm_apply _ _

/-- The map `E → Y(ℂ)` on the part of `E` over `U(ℂ)`. -/
def localMap (U : B.I) : C(range (M.φ U), SchemePoints ℂ M.gluingData.glued) :=
  ⟨SchemePoints.map (M.ι U) ∘ (M.isOpenEmbedding U).isEmbedding.toHomeomorph.symm,
    (SchemePoints.continuous_map _).comp
      (M.isOpenEmbedding U).isEmbedding.toHomeomorph.symm.continuous⟩

lemma localMap_apply (U : B.I) {e : E.obj.left} (he : e ∈ range (M.φ U))
    {y : SchemePoints ℂ (M.Y U)} (hy : M.φ U y = e) :
    M.localMap U ⟨e, he⟩ = SchemePoints.map (M.ι U) y := by
  change SchemePoints.map (M.ι U) ((M.isOpenEmbedding U).isEmbedding.toHomeomorph.symm ⟨e, he⟩) = _
  rw [M.toHomeomorph_symm_eq U he hy]

/-- XII.5.1, proof of 2): the map `E → Y(ℂ)`, given over `U(ℂ)` by `φ_U⁻¹` followed by
`Y_U(ℂ) → Y(ℂ)`. -/
def toGlued : C(E.obj.left, SchemePoints ℂ M.gluingData.glued) :=
  ContinuousMap.liftCover (fun U : B.I ↦ range (M.φ U)) M.localMap
    (fun U V e heU heV ↦ by
      rcases id heU with ⟨a, ha⟩
      rcases id heV with ⟨b, hb⟩
      rw [M.localMap_apply U heU ha, M.localMap_apply V heV hb]
      exact M.map_ι_eq_of_φ_eq a b (ha.trans hb.symm))
    (fun e ↦ by
      obtain ⟨U, hxU⟩ := B.exists_mem_I (E.obj.hom e).pt
      exact ⟨U, (M.isOpenEmbedding U).isOpen_range.mem_nhds (M.mem_range_φ hxU)⟩)

lemma toGlued_φ (U : B.I) (y : SchemePoints ℂ (M.Y U)) :
    M.toGlued (M.φ U y) = SchemePoints.map (M.ι U) y :=
  (ContinuousMap.liftCover_coe (S := fun U : B.I ↦ range (M.φ U)) (φ := M.localMap)
    (i := U) ⟨M.φ U y, mem_range_self y⟩).trans (M.localMap_apply U _ rfl)

lemma map_toBase_toGlued (e : E.obj.left) :
    SchemePoints.map M.gluingData.toBase (M.toGlued e) = E.obj.hom e := by
  obtain ⟨U, hxU⟩ := B.exists_mem_I (E.obj.hom e).pt
  obtain ⟨y, rfl⟩ := M.mem_range_φ hxU
  rw [toGlued_φ, map_toBase_map_ι]

-- As in mathlib's `Scheme.Cover.ColimitGluingData`: the diagram's index type is `B.cover.I₀`,
-- which is `B.I` only up to unfolding.
set_option backward.isDefEq.respectTransparency.types false in
instance (U : B.I) : IsOpenImmersion (M.ι U) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι M.gluingData.functor U))

instance : LocallyOfFiniteType (M.gluingData.glued ↘ Spec (.of ℂ)) := by
  have : IsFinite M.gluingData.toBase := M.glued.prop.1
  change LocallyOfFiniteType (M.gluingData.toBase ≫ X ↘ Spec (.of ℂ))
  infer_instance

lemma toGlued_bijective : Function.Bijective M.toGlued := by
  constructor
  · intro e e' hee'
    have hx : E.obj.hom e = E.obj.hom e' := by
      rw [← map_toBase_toGlued, ← map_toBase_toGlued, hee']
    obtain ⟨U, hxU⟩ := B.exists_mem_I (E.obj.hom e).pt
    obtain ⟨y, rfl⟩ := M.mem_range_φ hxU
    obtain ⟨y', rfl⟩ := M.mem_range_φ (hx ▸ hxU)
    rw [toGlued_φ, toGlued_φ] at hee'
    rw [SchemePoints.map_injective (M.ι U) hee']
  · intro r
    obtain ⟨U, hxU⟩ := B.exists_mem_I (SchemePoints.map M.gluingData.toBase r).pt
    have h₁ : r.pt ∈ M.gluingData.toBase ⁻¹' range (B.cover.f U) := by
      change M.gluingData.toBase r.pt ∈ range U.1.ι
      rw [Scheme.Opens.range_ι]
      exact hxU
    have hr : r.pt ∈ range (M.ι U) := M.gluingData.preimage_toBase_eq_range_ι U ▸ h₁
    obtain ⟨y, rfl⟩ := SchemePoints.exists_map_eq (M.ι U) r hr
    exact ⟨M.φ U y, M.toGlued_φ U y⟩

/-- XII.5.1, proof of 2): `E → Y(ℂ)` is a homeomorphism (a bijective local homeomorphism, the
projections to `X(ℂ)` being covering maps). -/
def toGluedHomeomorph : E.obj.left ≃ₜ SchemePoints ℂ M.gluingData.glued :=
  have hcov : IsCoveringMap (SchemePoints.map (K := ℂ) M.gluingData.toBase) :=
    ((schemePointsFunctor ℂ X).obj M.glued).isCoveringMap
  have hloc : IsLocalHomeomorph M.toGlued := by
    refine IsLocalHomeomorph.of_comp (g := SchemePoints.map (K := ℂ) M.gluingData.toBase) ?_
      hcov.isLocalHomeomorph M.toGlued.continuous
    have : SchemePoints.map (K := ℂ) M.gluingData.toBase ∘ M.toGlued = E.obj.hom :=
      funext M.map_toBase_toGlued
    rw [this]
    exact E.isCoveringMap.isLocalHomeomorph
  (Equiv.ofBijective _ M.toGlued_bijective).toHomeomorphOfContinuousOpen M.toGlued.continuous
    hloc.isOpenMap

lemma toGluedHomeomorph_apply (e : E.obj.left) : M.toGluedHomeomorph e = M.toGlued e := rfl

/-- XII.5.1, proof of 2): the glued covering `Y` of `X` satisfies `Ψ(Y) ≅ E`. -/
def isoGlued : (schemePointsFunctor ℂ X).obj M.glued ≅ E :=
  ObjectProperty.isoMk _ (Over.isoMk (TopCat.isoOfHomeo M.toGluedHomeomorph.symm) (by
    refine TopCat.hom_ext (ContinuousMap.ext fun r ↦ ?_)
    obtain ⟨e, rfl⟩ := M.toGluedHomeomorph.surjective r
    change E.obj.hom (M.toGluedHomeomorph.symm (M.toGluedHomeomorph e)) =
      SchemePoints.map M.gluingData.toBase (M.toGluedHomeomorph e)
    rw [Homeomorph.symm_apply_apply, toGluedHomeomorph_apply, map_toBase_toGlued]))

include M in
/-- XII.5.1, proof of 2): a finite covering of `X(ℂ)` with local models over the affine opens of
`X` is in the essential image of `Ψ`. -/
theorem mem_essImage : (schemePointsFunctor ℂ X).essImage E := ⟨M.glued, ⟨M.isoGlued⟩⟩

end Comparison

end LocalModels

/-- XII.5.1, proof of 2): if every finite covering of `X(ℂ)` has local models over a family `B`
of affine opens of `X`, then `Ψ` is an equivalence of categories for `X` (it is fully faithful
by step 1)). -/
theorem isEquivalence_schemePointsFunctor_of_localModels
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (B : AffineOpenBasis X)
    (H : ∀ E : TopCat.FiniteCovering (TopCat.of (SchemePoints ℂ X)), Nonempty (LocalModels B E)) :
    (schemePointsFunctor ℂ X).IsEquivalence where
  essSurj := ⟨fun E ↦ (H E).some.mem_essImage⟩

end RiemannLocal

end SGA.SGA1.ExposeXII
