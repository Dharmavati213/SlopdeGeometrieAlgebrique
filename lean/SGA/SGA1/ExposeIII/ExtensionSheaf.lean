/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.Schemes
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# SGA 1, Exposé III, §5: the sheaf of extensions

Let `f : X → Y` and `p : Y' → Y` be morphisms of schemes, `i : Y'₀ → Y'` a morphism and
`g₀ : Y'₀ → X` a `Y`-morphism. For an open `U ⊆ Y'`, an *extension* of `g₀` over `U` is a
`Y`-morphism `g : U → X` whose restriction to `i⁻¹ U` is `g₀` (`Extension`). SGA 1 III.5.1
observes that `U ↦ {extensions over U}` is a sheaf of sets on `Y'`; this is
`isSheaf_extensionPresheaf`. It rests on gluing morphisms of schemes defined on the members of an
open cover of an open subscheme (`glueOpensOfLE`). By base change, extensions of `g₀` are
extensions of a section of `X ×_Y Y' → Y'` (`extensionEquivSection`); the torsor structure of
III.5.1–5.2 is set up for sections in `DerivationSheaf.lean` and `ExtensionTorsor.lean`.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SGA.SGA1.ExposeIII

section Gluing

variable {Z X : Scheme.{u}}

/-- The open cover of an open subscheme `W` of `Z` by opens `U j ≤ W` whose union is `W`. -/
noncomputable def openCoverOfLE {J : Type*} (U : J → Z.Opens) {W : Z.Opens}
    (hU : ∀ j, U j ≤ W) (hW : W ≤ ⨆ j, U j) : W.toScheme.OpenCover :=
  Scheme.Cover.mkOfCovers J (fun j ↦ (U j).toScheme) (fun j ↦ Z.homOfLE (hU j)) fun x ↦ by
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hW x.2)
    exact ⟨j, ⟨x.1, hj⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms on opens `U j` covering an open `W`, which agree on the pairwise intersections,
glue to a morphism on `W`. -/
noncomputable def glueOpensOfLE {J : Type*} (U : J → Z.Opens) {W : Z.Opens}
    (hU : ∀ j, U j ≤ W) (hW : W ≤ ⨆ j, U j) (g : ∀ j, (U j).toScheme ⟶ X)
    (hg : ∀ j k, Z.homOfLE (inf_le_left : U j ⊓ U k ≤ U j) ≫ g j =
      Z.homOfLE inf_le_right ≫ g k) : W.toScheme ⟶ X :=
  (openCoverOfLE U hU hW).glueMorphisms g fun j k ↦ by
    have hP := isPullback_opens_inf_le (hU j) (hU k)
    change pullback.fst (Z.homOfLE (hU j)) (Z.homOfLE (hU k)) ≫ g j =
      pullback.snd (Z.homOfLE (hU j)) (Z.homOfLE (hU k)) ≫ g k
    rw [← cancel_epi hP.isoPullback.hom, hP.isoPullback_hom_fst_assoc,
      hP.isoPullback_hom_snd_assoc]
    exact hg j k

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma homOfLE_glueOpensOfLE {J : Type*} (U : J → Z.Opens) {W : Z.Opens}
    (hU : ∀ j, U j ≤ W) (hW : W ≤ ⨆ j, U j) (g : ∀ j, (U j).toScheme ⟶ X)
    (hg : ∀ j k, Z.homOfLE (inf_le_left : U j ⊓ U k ≤ U j) ≫ g j =
      Z.homOfLE inf_le_right ≫ g k) (j : J) :
    Z.homOfLE (hU j) ≫ glueOpensOfLE U hU hW g hg = g j :=
  (openCoverOfLE U hU hW).ι_glueMorphisms _ _ j

/-- Two morphisms on an open `W` which agree on the members of an open cover of `W` are equal. -/
lemma hom_ext_of_le_iSup {J : Type*} (U : J → Z.Opens) {W : Z.Opens}
    (hU : ∀ j, U j ≤ W) (hW : W ≤ ⨆ j, U j) {g g' : W.toScheme ⟶ X}
    (h : ∀ j, Z.homOfLE (hU j) ≫ g = Z.homOfLE (hU j) ≫ g') : g = g' :=
  (openCoverOfLE U hU hW).hom_ext _ _ h

end Gluing

section Extensions

variable {X Y Y' Y'₀ : Scheme.{u}} (f : X ⟶ Y) (p : Y' ⟶ Y) (i : Y'₀ ⟶ Y') (g₀ : Y'₀ ⟶ X)

/-- III.5.1: an extension of `g₀ : Y'₀ → X` over an open `U` of `Y'`, i.e. a `Y`-morphism
`U → X` whose restriction to `i⁻¹ U` is `g₀`. -/
@[ext]
structure Extension (U : Y'.Opens) where
  /-- The morphism `U → X`. -/
  hom : U.toScheme ⟶ X
  hom_comp : hom ≫ f = U.ι ≫ p
  hom_extends : (i ∣_ U) ≫ hom = (i ⁻¹ᵁ U).ι ≫ g₀

variable {f p i g₀}

/-- The restriction of an extension to a smaller open. -/
noncomputable def Extension.restrict {U V : Y'.Opens} (h : V ≤ U) (g : Extension f p i g₀ U) :
    Extension f p i g₀ V where
  hom := Y'.homOfLE h ≫ g.hom
  hom_comp := by rw [Category.assoc, g.hom_comp, Scheme.homOfLE_ι_assoc]
  hom_extends := by rw [morphismRestrict_homOfLE_assoc, g.hom_extends, Scheme.homOfLE_ι_assoc]

@[simp]
lemma Extension.restrict_hom {U V : Y'.Opens} (h : V ≤ U) (g : Extension f p i g₀ U) :
    (g.restrict h).hom = Y'.homOfLE h ≫ g.hom :=
  rfl

lemma Extension.restrict_rfl {U : Y'.Opens} (g : Extension f p i g₀ U) : g.restrict le_rfl = g :=
  Extension.ext (by simp [Scheme.homOfLE_rfl])

lemma Extension.restrict_restrict {U V W : Y'.Opens} (h : V ≤ U) (h' : W ≤ V)
    (g : Extension f p i g₀ U) : (g.restrict h).restrict h' = g.restrict (h'.trans h) :=
  Extension.ext (by simp [Scheme.homOfLE_homOfLE_assoc])

/-- A global extension, as a morphism `Y' → X`. -/
noncomputable def Extension.toHom (g : Extension f p i g₀ ⊤) : Y' ⟶ X := Y'.topIso.inv ≫ g.hom

@[reassoc (attr := simp)]
lemma Extension.toHom_comp (g : Extension f p i g₀ ⊤) : g.toHom ≫ f = p := by
  rw [Extension.toHom, Category.assoc, g.hom_comp, ← Category.assoc, Scheme.toIso_inv_ι,
    Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma Extension.comp_toHom (g : Extension f p i g₀ ⊤) : i ≫ g.toHom = g₀ := by
  have : IsIso (i ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso Y'₀.topIso.hom)
  rw [← cancel_epi (i ⁻¹ᵁ ⊤).ι, ← g.hom_extends, Extension.toHom, ← Category.assoc,
    ← morphismRestrict_ι, Category.assoc, ← Category.assoc (⊤ : Y'.Opens).ι,
    Scheme.ι_toIso_inv, Category.id_comp]

/-- Extensions of `g₀ : Y'₀ → X` along `p : Y' → Y` are the extensions of the corresponding
section `Y'₀ → X ×_Y Y'` of the base change `X ×_Y Y' → Y'`: this reduces III.5.1 to sections. -/
noncomputable def extensionEquivSection (hg₀ : g₀ ≫ f = i ≫ p) (U : Y'.Opens) :
    Extension f p i g₀ U ≃
      Extension (pullback.snd f p) (𝟙 Y') i (pullback.lift g₀ i hg₀) U where
  toFun g :=
    { hom := pullback.lift g.hom U.ι g.hom_comp
      hom_comp := by rw [pullback.lift_snd, Category.comp_id]
      hom_extends := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, g.hom_extends, Category.assoc, pullback.lift_fst]
        · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd,
            morphismRestrict_ι] }
  invFun s :=
    { hom := s.hom ≫ pullback.fst f p
      hom_comp := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, s.hom_comp, Category.comp_id]
      hom_extends := by rw [← Category.assoc, s.hom_extends, Category.assoc, pullback.lift_fst] }
  left_inv g := Extension.ext (pullback.lift_fst _ _ _)
  right_inv s := Extension.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
    (by rw [pullback.lift_snd, s.hom_comp, Category.comp_id]))

variable (f p i g₀)

/-- III.5.1: the presheaf of sets `U ↦ {extensions of g₀ over U}` on `Y'`. -/
noncomputable def extensionPresheaf : TopCat.Presheaf (Type u) Y' where
  obj U := Extension f p i g₀ U.unop
  map h := TypeCat.ofHom fun g ↦ g.restrict h.unop.le
  map_id _ := TypeCat.homEquiv.injective (funext fun g ↦ g.restrict_rfl)
  map_comp h h' := TypeCat.homEquiv.injective
    (funext fun g ↦ (g.restrict_restrict h.unop.le h'.unop.le).symm)

set_option backward.isDefEq.respectTransparency false in
/-- III.5.1: the extensions of `g₀` form a sheaf of sets on `Y'`. -/
theorem isSheaf_extensionPresheaf : (extensionPresheaf f p i g₀).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types]
  intro J U sf hsf
  have hU : ∀ j, U j ≤ ⨆ k, U k := le_iSup U
  have hg : ∀ j k, Y'.homOfLE (inf_le_left : U j ⊓ U k ≤ U j) ≫ (sf j).hom =
      Y'.homOfLE inf_le_right ≫ (sf k).hom := fun j k ↦ congrArg Extension.hom (hsf j k)
  let g := glueOpensOfLE U hU le_rfl (fun j ↦ (sf j).hom) hg
  have hgj (j : J) : Y'.homOfLE (hU j) ≫ g = (sf j).hom := homOfLE_glueOpensOfLE _ _ _ _ _ j
  have h₁ : g ≫ f = Scheme.Opens.ι (⨆ k, U k) ≫ p := hom_ext_of_le_iSup U hU le_rfl fun j ↦ by
    rw [reassoc_of% hgj j, (sf j).hom_comp, Scheme.homOfLE_ι_assoc]
  have h₂ : (i ∣_ ⨆ k, U k) ≫ g = Scheme.Opens.ι (i ⁻¹ᵁ ⨆ k, U k) ≫ g₀ := by
    refine hom_ext_of_le_iSup (fun j ↦ i ⁻¹ᵁ U j) (fun j ↦ i.preimage_mono (hU j)) ?_ fun j ↦ ?_
    · intro x hx
      obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hx
      exact Opens.mem_iSup.mpr ⟨k, hk⟩
    · rw [← morphismRestrict_homOfLE_assoc i _ _ (hU j), hgj j, (sf j).hom_extends,
        Scheme.homOfLE_ι_assoc]
  refine ⟨⟨g, h₁, h₂⟩, fun j ↦ Extension.ext (hgj j), fun g' hg' ↦ Extension.ext ?_⟩
  refine hom_ext_of_le_iSup U hU le_rfl fun j ↦ ?_
  exact (congrArg Extension.hom (hg' j)).trans (hgj j).symm

end Extensions

end SGA.SGA1.ExposeIII
