/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.Filtered.Final

/-!
# `Spec 𝒪_{X,x}` as the limit of the affine open neighbourhoods of `x`

For a point `x` of a scheme `X`, the local scheme `Spec 𝒪_{X,x}` is the cofiltered limit of the
affine open neighbourhoods of `x`, with affine transition maps (EGA IV 8.2.2, Stacks 01ZB and
0CUE). More generally, for a morphism `p : Z ⟶ X`, the fibre product `Z ×_X Spec 𝒪_{X,x}` is the
limit of the open subschemes `p⁻¹(U)`, `U` running over the affine open neighbourhoods of `x`.
Together with the results of `Mathlib.AlgebraicGeometry.AffineTransitionLimit`, this is the
basis of the "spreading out" arguments of EGA IV 8 over neighbourhoods of a point.

## Main definitions and results

* `AlgebraicGeometry.Scheme.AffineNhds x`: the affine open neighbourhoods of `x`, a cofiltered
  preorder.
* `AlgebraicGeometry.Scheme.isColimitGermCocone`: `𝒪_{X,x}` is the colimit of `Γ(X, U)`.
* `AlgebraicGeometry.Scheme.isLimitStalkCone`: `Spec 𝒪_{X,x}` is the limit of the `U`.
* `AlgebraicGeometry.Scheme.isLimitPreimageCone`: `Z ×_X Spec 𝒪_{X,x}` is the limit of the
  `p⁻¹(U)`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}} (x : X)

/-- The affine open neighbourhoods of a point `x` of a scheme, ordered by inclusion. -/
abbrev AffineNhds : Type u := {U : X.Opens // IsAffineOpen U ∧ x ∈ U}

instance : Nonempty (X.AffineNhds x) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
  exact ⟨⟨U, hU, hxU⟩⟩

instance : IsCodirectedOrder (X.AffineNhds x) where
  directed U V := by
    obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ U.1 ⊓ V.1 from ⟨U.2.2, V.2.2⟩)
    exact ⟨⟨W, hW, hxW⟩, hWUV.trans inf_le_left, hWUV.trans inf_le_right⟩

instance : IsCofiltered (X.AffineNhds x) := inferInstance

namespace AffineNhds

variable {x}

lemma isAffineOpen (U : X.AffineNhds x) : IsAffineOpen U.1 := U.2.1

lemma mem (U : X.AffineNhds x) : x ∈ U.1 := U.2.2

instance (U : X.AffineNhds x) : IsAffine U.1 := U.isAffineOpen

/-- The inclusion of affine open neighbourhoods into open neighbourhoods. -/
def toOpenNhds : X.AffineNhds x ⥤ OpenNhds x where
  obj U := ⟨U.1, U.2.2⟩
  map f := homOfLE (leOfHom f)

instance : (toOpenNhds (x := x)).Full where
  map_surjective f := ⟨homOfLE (leOfHom f), rfl⟩

instance : (toOpenNhds (x := x)).Faithful where

instance : (toOpenNhds (x := x)).op.Final :=
  Functor.final_of_exists_of_isFiltered_of_fullyFaithful _ fun V ↦ by
    obtain ⟨U, hU, hxU, hUV⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens V.unop.2
    exact ⟨op ⟨U, hU, hxU⟩, ⟨(homOfLE hUV).op⟩⟩

end AffineNhds

/-- The diagram of sections `U ↦ Γ(X, U)` over the affine open neighbourhoods of `x`. -/
abbrev sectionsDiagram : (X.AffineNhds x)ᵒᵖ ⥤ CommRingCat.{u} :=
  AffineNhds.toOpenNhds.op ⋙ (OpenNhds.inclusion x).op ⋙ X.presheaf

/-- The cocone of germs `Γ(X, U) ⟶ 𝒪_{X,x}`. -/
noncomputable abbrev germCocone : Cocone (X.sectionsDiagram x) :=
  (colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf)).whisker AffineNhds.toOpenNhds.op

/-- The stalk `𝒪_{X,x}` is the colimit of the sections over the affine open neighbourhoods
of `x`. -/
noncomputable def isColimitGermCocone : IsColimit (X.germCocone x) :=
  (Functor.Final.isColimitWhiskerEquiv _ _).symm (colimit.isColimit _)

@[simp]
lemma germCocone_ι_app (U : (X.AffineNhds x)ᵒᵖ) :
    (X.germCocone x).ι.app U = X.presheaf.germ U.unop.1 x U.unop.2.2 := rfl

/-- The diagram of the affine open neighbourhoods `U` of `x`, as open subschemes. -/
@[simps]
noncomputable abbrev affineNhdsDiagram : X.AffineNhds x ⥤ Scheme.{u} where
  obj U := U.1
  map {U V} f := X.homOfLE (U := U.1) (V := V.1) (leOfHom f)

instance {U V : X.AffineNhds x} (f : U ⟶ V) : IsAffineHom ((X.affineNhdsDiagram x).map f) :=
  inferInstanceAs (IsAffineHom (X.homOfLE (U := U.1) (V := V.1) (leOfHom f)))

/-- The cone over the affine open neighbourhoods of `x` with vertex `Spec 𝒪_{X,x}`. -/
noncomputable def stalkCone : Cone (X.affineNhdsDiagram x) where
  pt := Spec (X.presheaf.stalk x)
  π :=
    { app U := U.1.fromSpecStalkOfMem x U.2.2
      naturality U V f := by
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map, affineNhdsDiagram_obj,
          affineNhdsDiagram_map]
        rw [Category.id_comp, ← cancel_mono V.1.ι]
        simp }

@[simp]
lemma stalkCone_pt : (X.stalkCone x).pt = Spec (X.presheaf.stalk x) := rfl

@[simp]
lemma stalkCone_π_app (U : X.AffineNhds x) :
    (X.stalkCone x).π.app U = U.1.fromSpecStalkOfMem x U.2.2 := rfl

/-- (Implementation) The diagram of the affine open neighbourhoods of `x` is isomorphic to the
diagram of the spectra of their rings of sections. -/
noncomputable def affineNhdsDiagramIsoSpec :
    X.affineNhdsDiagram x ≅ (X.sectionsDiagram x).rightOp ⋙ Scheme.Spec :=
  NatIso.ofComponents (fun U ↦ U.isAffineOpen.isoSpec) fun {U V} f ↦ by
    exact (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map U.1 V.1 (leOfHom f)).symm

/-- (Implementation) `Spec 𝒪_{X,x}` is the limit of the `Spec Γ(X, U)`. -/
noncomputable def isLimitSpecGermCone :
    IsLimit (Scheme.Spec.mapCone (coneRightOpOfCocone (X.germCocone x))) :=
  isLimitOfPreserves _ (isLimitConeRightOpOfCocone _ (X.isColimitGermCocone x))

/-- (Implementation) Comparison of the two limit cones. -/
noncomputable def stalkConeIso : Scheme.Spec.mapCone (coneRightOpOfCocone (X.germCocone x)) ≅
    (Cone.postcompose (X.affineNhdsDiagramIsoSpec x).hom).obj (X.stalkCone x) :=
  Cone.ext (Iso.refl _) fun U ↦
    (Scheme.Opens.fromSpecStalkOfMem_toSpecΓ U.1 x U.2.2).symm.trans (Category.id_comp _).symm

/-- EGA IV 8.2.2: `Spec 𝒪_{X,x}` is the limit of the affine open neighbourhoods of `x`. -/
@[stacks 01ZB]
noncomputable def isLimitStalkCone : IsLimit (X.stalkCone x) :=
  (IsLimit.postcomposeHomEquiv (X.affineNhdsDiagramIsoSpec x) _)
    ((X.isLimitSpecGermCone x).ofIsoLimit (X.stalkConeIso x))

section Preimage

variable {Z : Scheme.{u}} (p : Z ⟶ X)

/-- The diagram of the preimages `p⁻¹(U)` of the affine open neighbourhoods `U` of `x`. -/
@[simps]
noncomputable abbrev preimageDiagram : X.AffineNhds x ⥤ Scheme.{u} where
  obj U := p ⁻¹ᵁ U.1
  map {U V} f := Z.homOfLE (p.preimage_mono (leOfHom f : U.1 ≤ V.1))

/-- The restrictions `p⁻¹(U) ⟶ U` of `p`. -/
@[simps]
noncomputable def preimageDiagramι : preimageDiagram x p ⟶ X.affineNhdsDiagram x where
  app U := p ∣_ U.1
  naturality U V f := by
    rw [← cancel_mono V.1.ι]
    simp

lemma isPullback_preimageDiagram_map {U V : X.AffineNhds x} (f : U ⟶ V) :
    IsPullback (p ∣_ U.1) ((preimageDiagram x p).map f) (X.homOfLE (leOfHom f : U.1 ≤ V.1))
      (p ∣_ V.1) :=
  IsOpenImmersion.isPullback _ _ _ _ (by rw [← cancel_mono V.1.ι]; simp) (by
    simp only [Scheme.opensRange_homOfLE]
    rw [← Scheme.Hom.comp_preimage, morphismRestrict_ι, Scheme.Hom.comp_preimage])

instance {U V : X.AffineNhds x} (f : U ⟶ V) : IsAffineHom ((preimageDiagram x p).map f) :=
  MorphismProperty.of_isPullback (isPullback_preimageDiagram_map x p f)
    (inferInstance : IsAffineHom (X.homOfLE (leOfHom f : U.1 ≤ V.1)))

instance [QuasiCompact p] (U : X.AffineNhds x) : CompactSpace ((preimageDiagram x p).obj U) :=
  isCompact_iff_compactSpace.mp
    (QuasiCompact.isCompact_preimage (f := p) _ U.1.2 U.isAffineOpen.isCompact)

instance [QuasiSeparated p] (U : X.AffineNhds x) :
    QuasiSeparatedSpace ((preimageDiagram x p).obj U) :=
  quasiSeparatedSpace_of_quasiSeparated (p ∣_ U.1)

lemma range_pullback_fst_subset (U : X.AffineNhds x) :
    Set.range (pullback.fst p (X.fromSpecStalk x)) ⊆ Set.range (p ⁻¹ᵁ U.1).ι := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  change (pullback.fst p (X.fromSpecStalk x) ≫ p) z ∈ U.1
  rw [pullback.condition, Scheme.Hom.comp_apply]
  have h := Set.mem_range_self (f := X.fromSpecStalk x) (pullback.snd p (X.fromSpecStalk x) z)
  rw [range_fromSpecStalk] at h
  exact Specializes.mem_open h U.1.2 U.2.2

/-- The cone over the preimages `p⁻¹(U)` with vertex `Z ×_X Spec 𝒪_{X,x}`. -/
noncomputable abbrev preimageCone : Cone (preimageDiagram x p) where
  pt := pullback p (X.fromSpecStalk x)
  π :=
    { app U := IsOpenImmersion.lift (p ⁻¹ᵁ U.1).ι _ (range_pullback_fst_subset x p U)
      naturality U V f := by
        rw [← cancel_mono (p ⁻¹ᵁ V.1).ι]
        simp }

@[reassoc (attr := simp)]
lemma preimageCone_π_app_ι (U : X.AffineNhds x) :
    (preimageCone x p).π.app U ≫ (p ⁻¹ᵁ U.1).ι = pullback.fst p (X.fromSpecStalk x) :=
  IsOpenImmersion.lift_fac _ _ _

lemma preimageCone_pt : (preimageCone x p).pt = pullback p (X.fromSpecStalk x) := rfl

lemma isPullback_preimageCone_π_app (U : X.AffineNhds x) :
    IsPullback ((preimageCone x p).π.app U) (pullback.snd p (X.fromSpecStalk x)) (p ∣_ U.1)
      (U.1.fromSpecStalkOfMem x U.2.2) := by
  refine IsPullback.of_right (h₁₂ := (p ⁻¹ᵁ U.1).ι) (v₁₃ := p) (h₂₂ := U.1.ι) ?_ ?_
    (isPullback_morphismRestrict p U.1).flip
  · simpa using IsPullback.of_hasPullback p (X.fromSpecStalk x)
  · rw [← cancel_mono U.1.ι]
    simp [pullback.condition]

attribute [local instance] IsCofiltered.isConnected in
/-- EGA IV 8.2.2 (relative form): for `p : Z ⟶ X`, the fibre product `Z ×_X Spec 𝒪_{X,x}` is
the limit of the preimages `p⁻¹(U)` of the affine open neighbourhoods `U` of `x`. -/
noncomputable def isLimitPreimageCone : IsLimit (preimageCone x p) :=
  isLimitOfIsPullbackOfIsConnected (preimageDiagramι x p) (preimageCone x p) (X.stalkCone x)
    { hom := pullback.snd p (X.fromSpecStalk x)
      w U := by
        rw [← cancel_mono U.1.ι]
        simp [pullback.condition] }
    (fun U ↦ isPullback_preimageCone_π_app x p U) (X.isLimitStalkCone x)

variable {x p} {Zx : Scheme.{u}} {k : Zx ⟶ Z} {q : Zx ⟶ Spec (X.presheaf.stalk x)}

lemma range_subset_of_isPullback (h : IsPullback k q p (X.fromSpecStalk x)) (U : X.AffineNhds x) :
    Set.range k ⊆ Set.range (p ⁻¹ᵁ U.1).ι := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  change (k ≫ p) z ∈ U.1
  rw [h.w, Scheme.Hom.comp_apply]
  have h' := Set.mem_range_self (f := X.fromSpecStalk x) (q z)
  rw [range_fromSpecStalk] at h'
  exact Specializes.mem_open h' U.1.2 U.2.2

variable (x p) in
/-- The cone over the preimages `p⁻¹(U)` defined by any cartesian square
`Z_x ⟶ Z` over `Spec 𝒪_{X,x} ⟶ X`. -/
noncomputable abbrev preimageConeOfIsPullback (h : IsPullback k q p (X.fromSpecStalk x)) :
    Cone (preimageDiagram x p) where
  pt := Zx
  π :=
    { app U := IsOpenImmersion.lift (p ⁻¹ᵁ U.1).ι k (range_subset_of_isPullback h U)
      naturality U V f := by
        rw [← cancel_mono (p ⁻¹ᵁ V.1).ι]
        simp }

@[reassoc (attr := simp)]
lemma preimageConeOfIsPullback_π_app_ι (h : IsPullback k q p (X.fromSpecStalk x))
    (U : X.AffineNhds x) :
    (preimageConeOfIsPullback x p h).π.app U ≫ (p ⁻¹ᵁ U.1).ι = k :=
  IsOpenImmersion.lift_fac _ _ _

/-- EGA IV 8.2.2 (relative form, for any cartesian square): if `Z_x ⟶ Z` is a base change of
`Spec 𝒪_{X,x} ⟶ X` along `p : Z ⟶ X`, then `Z_x` is the limit of the preimages `p⁻¹(U)`. -/
noncomputable def isLimitPreimageConeOfIsPullback (h : IsPullback k q p (X.fromSpecStalk x)) :
    IsLimit (preimageConeOfIsPullback x p h) :=
  IsLimit.ofIsoLimit (isLimitPreimageCone x p) (Cone.ext h.isoPullback.symm fun U ↦ by
    rw [← cancel_mono (p ⁻¹ᵁ U.1).ι]
    simp)

variable (x p) in
/-- The natural transformation from the diagram of preimages `p⁻¹(U)` to the constant diagram
on `B`, given by `r : Z ⟶ B`. -/
@[simps]
noncomputable def preimageDiagramTo {B : Scheme.{u}} (r : Z ⟶ B) :
    preimageDiagram x p ⟶ (Functor.const (X.AffineNhds x)).obj B where
  app U := (p ⁻¹ᵁ U.1).ι ≫ r
  naturality U V f := by simp

end Preimage

end Scheme

end AlgebraicGeometry
