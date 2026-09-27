/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import SGA.SGA1.ExposeV.FiniteQuotientProperties

/-!
# SGA 1, Exposé V, Cor. V.1.8: quotient of a scheme affine over a base

Let `f : X ⟶ Z` be affine and let a finite group `G` act on the right on `X` by
`Z`-automorphisms. Then `G` acts admissibly, and the quotient is `Spec_Z (f_* 𝒪_X)^G`: it is
glued from the `Spec Γ(X, f⁻¹ U)^G`, `U ⊆ Z` affine, by mathlib's relative gluing of
quasi-coherent algebras (`AffineZariskiSite.relativeGluingData`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace SGA.SGA1.ExposeV

section Localization

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] {G : Type*} [Finite G]

/-- Invariants commute with localization away from an invariant element. -/
theorem isLocalization_away_invariants (σ : G → A →+* A) (σ' : G → A' →+* A')
    (hσ' : ∀ g x, σ' g (algebraMap A A' x) = algebraMap A A' (σ g x))
    (R : Subring A) (hR : ∀ x, x ∈ R ↔ ∀ g, σ g x = x)
    (R' : Subring A') (hR' : ∀ x, x ∈ R' ↔ ∀ g, σ' g x = x)
    (a : R) [IsLocalization.Away (a : A) A'] :
    letI : Algebra R R' := ((algebraMap A A').restrict R R' fun x hx ↦ (hR' _).mpr fun g ↦ by
      rw [hσ', (hR x).mp hx g]).toAlgebra
    IsLocalization.Away a R' := by
  let _ : Algebra R R' := ((algebraMap A A').restrict R R' fun x hx ↦ (hR' _).mpr fun g ↦ by
      rw [hσ', (hR x).mp hx g]).toAlgebra
  let L := Localization.Away a
  have hunit : IsUnit (algebraMap A A' (a : A)) := IsLocalization.Away.algebraMap_isUnit _
  let φ' : L →+* A' := IsLocalization.Away.lift a (g := (algebraMap A A').comp R.subtype) hunit
  have : IsLocalization.Away (R.subtype a) A' := ‹IsLocalization.Away (a : A) A'›
  obtain ⟨hinj, hsurj⟩ := injective_and_invariants_of_away (R' := L) (A' := A') R.subtype σ
    (fun g r ↦ ((hR r).mp r.2 g)) Subtype.val_injective
    (fun x hx ↦ ⟨⟨x, (hR x).mpr hx⟩, rfl⟩) a φ' (fun x ↦ IsLocalization.Away.lift_eq _ _ x)
    σ' hσ'
  have hmem : ∀ x, φ' x ∈ R' := by
    intro x
    rw [hR']
    intro g
    have : (σ' g).comp φ' = φ' := IsLocalization.ringHom_ext (Submonoid.powers a) <| by
      ext r
      have hφr : φ' (algebraMap R L r) = algebraMap A A' r :=
        IsLocalization.Away.lift_eq (x := a) (S := L) hunit r
      change σ' g (φ' (algebraMap R L r)) = φ' (algebraMap R L r)
      rw [hφr, hσ']
      exact congr_arg _ ((hR r).mp r.2 g)
    exact congr($this x)
  let e : L ≃+* R' := RingEquiv.ofBijective (φ'.codRestrict R' hmem)
    ⟨fun x y h ↦ hinj (congr_arg Subtype.val h), fun y ↦ by
      obtain ⟨x, hx⟩ := hsurj y ((hR' y).mp y.2)
      exact ⟨x, Subtype.ext hx⟩⟩
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers a)
    { e with commutes' := fun r ↦ Subtype.ext (IsLocalization.Away.lift_eq _ _ r) }

end Localization

variable {G : Type*} {X Z : Scheme.{u}} {T : G → (X ⟶ X)} {f : X ⟶ Z} (hTf : ∀ g, T g ≫ f = f)

/-- The subring `Γ(X, f⁻¹ U)^G` of invariant sections over the preimage of `U`. -/
def invariantSubring (U : Z.Opens) : Subring Γ(X, f ⁻¹ᵁ U) where
  carrier := {s | ∀ g, (T g).appLE (f ⁻¹ᵁ U) (f ⁻¹ᵁ U)
    (preimage_le_preimage_of_comp_eq (hTf g) U) s = s}
  mul_mem' ha hb g := by rw [map_mul, ha g, hb g]
  one_mem' g := map_one _
  add_mem' ha hb g := by rw [map_add, ha g, hb g]
  zero_mem' g := map_zero _
  neg_mem' ha g := by rw [map_neg, ha g]

lemma mem_invariantSubring {U : Z.Opens} {s : Γ(X, f ⁻¹ᵁ U)} :
    s ∈ invariantSubring hTf U ↔ ∀ g, (T g).appLE (f ⁻¹ᵁ U) (f ⁻¹ᵁ U)
      (preimage_le_preimage_of_comp_eq (hTf g) U) s = s := Iff.rfl

lemma res_mem_invariantSubring {U V : Z.Opens} (h : V ≤ U) {s : Γ(X, f ⁻¹ᵁ U)}
    (hs : s ∈ invariantSubring hTf U) :
    X.presheaf.map (homOfLE (f.preimage_mono h)).op s ∈ invariantSubring hTf V := fun g ↦ by
  rw [appLE_res_eq (hTp := hTf) h g s, hs g]

lemma app_mem_invariantSubring (U : Z.Opens) (r : Γ(Z, U)) :
    f.app U r ∈ invariantSubring hTf U := fun g ↦ by
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom (hTf g) _ _ _ le_rfl]

/-- The presheaf of rings `U ↦ Γ(X, f⁻¹ U)^G` on the affine opens of `Z`. -/
noncomputable def invariantDiagram : Z.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (invariantSubring hTf U.unop.1)
  map {U V} i := CommRingCat.ofHom <|
    (X.presheaf.map (homOfLE (f.preimage_mono
      (Scheme.AffineZariskiSite.toOpens_mono i.unop.le))).op).hom.restrict _ _
      fun _ hs ↦ res_mem_invariantSubring hTf (Scheme.AffineZariskiSite.toOpens_mono i.unop.le) hs
  map_id U := by
    ext x
    change X.presheaf.map (homOfLE _).op x.1 = x.1
    rw [Subsingleton.elim (homOfLE _) (𝟙 _), op_id, X.presheaf.map_id]
    rfl
  map_comp i j := by
    ext x
    change X.presheaf.map _ x.1 = X.presheaf.map _ (X.presheaf.map _ x.1)
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

/-- The structure map `𝒪_Z → (f_* 𝒪_X)^G` on affine opens. -/
noncomputable def invariantDiagramMap :
    (Scheme.AffineZariskiSite.toOpensFunctor Z).op ⋙ Z.presheaf ⟶ invariantDiagram hTf where
  app U := CommRingCat.ofHom <| (f.app U.unop.1).hom.codRestrict _
    (app_mem_invariantSubring hTf U.unop.1)
  naturality U V i := by
    ext x
    apply Subtype.ext
    exact congr($(f.naturality ((Scheme.AffineZariskiSite.toOpensFunctor Z).map i.unop).op) x)

set_option backward.isDefEq.respectTransparency.types false in
lemma coequifibered_invariantDiagramMap [IsAffineHom f] [Finite G] :
    (invariantDiagramMap hTf).Coequifibered := by
  refine Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mpr fun U r ↦ ?_
  let A := Γ(X, f ⁻¹ᵁ U.1)
  let A' := Γ(X, f ⁻¹ᵁ Z.basicOpen r)
  let i : f ⁻¹ᵁ Z.basicOpen r ⟶ f ⁻¹ᵁ U.1 := homOfLE (f.preimage_mono (Z.basicOpen_le r))
  let _ : Algebra A A' := (X.presheaf.map i.op).hom.toAlgebra
  have : IsLocalization.Away (f.app U.1 r) A' :=
    (U.2.preimage f).isLocalization_of_eq_basicOpen (f.app U.1 r) i
      (Scheme.preimage_basicOpen f r)
  exact isLocalization_away_invariants (A := A) (A' := A') (G := G)
    (fun g ↦ ((T g).appLE (f ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
      (preimage_le_preimage_of_comp_eq (hTf g) U.1)).hom)
    (fun g ↦ ((T g).appLE (f ⁻¹ᵁ Z.basicOpen r) (f ⁻¹ᵁ Z.basicOpen r)
      (preimage_le_preimage_of_comp_eq (hTf g) _)).hom)
    (fun g x ↦ appLE_res_eq (hTp := hTf) (Z.basicOpen_le r) g x)
    (invariantSubring hTf U.1) (fun _ ↦ Iff.rfl) (invariantSubring hTf (Z.basicOpen r))
    (fun _ ↦ Iff.rfl) ⟨f.app U.1 r, app_mem_invariantSubring hTf U.1 r⟩

section BasicOpen

variable {G : Type*} [Finite G] {X Y : Scheme.{u}} {T : G → (X ⟶ X)} {p : X ⟶ Y}
  {hTp : ∀ g, T g ≫ p = p}

/-- If `V` is an affine open with affine preimage satisfying V.1.3's condition, so does every
basic open `D(s) ⊆ V` (V.1.2: invariants commute with localization). -/
lemma SectionsAreInvariant.basicOpen {V : Y.Opens} (hV : IsAffineOpen V)
    (hpV : IsAffineOpen (p ⁻¹ᵁ V)) (h : SectionsAreInvariant T p hTp V) (s : Γ(Y, V)) :
    SectionsAreInvariant T p hTp (Y.basicOpen s) := by
  have := hV.isLocalization_basicOpen s
  let i : p ⁻¹ᵁ Y.basicOpen s ⟶ p ⁻¹ᵁ V := homOfLE (p.preimage_mono (Y.basicOpen_le s))
  let _ : Algebra Γ(X, p ⁻¹ᵁ V) Γ(X, p ⁻¹ᵁ Y.basicOpen s) := (X.presheaf.map i.op).hom.toAlgebra
  have : IsLocalization.Away (p.app V s) Γ(X, p ⁻¹ᵁ Y.basicOpen s) :=
    hpV.isLocalization_of_eq_basicOpen (p.app V s) i (Scheme.preimage_basicOpen p s)
  exact injective_and_invariants_of_away (p.app V).hom
    (fun g ↦ ((T g).appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) (preimage_le_preimage_of_comp_eq (hTp g) V)).hom)
    (fun g r ↦ by
      change ((T g).appLE _ _ _) (p.app V r) = p.app V r
      rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
        appLE_congr_hom (hTp g) _ _ _ le_rfl])
    h.1 h.2 s (p.app (Y.basicOpen s)).hom (fun x ↦ app_res_eq (Y.basicOpen_le s) x)
    (fun g ↦ ((T g).appLE (p ⁻¹ᵁ Y.basicOpen s) (p ⁻¹ᵁ Y.basicOpen s)
      (preimage_le_preimage_of_comp_eq (hTp g) _)).hom)
    (fun g x ↦ appLE_res_eq (hTp := hTp) (Y.basicOpen_le s) g x)

end BasicOpen

section Glue

variable [IsAffineHom f] [Finite G]

open Scheme.AffineZariskiSite

/-- The relative gluing data of the affine schemes `Spec Γ(X, f⁻¹ U)^G`. -/
noncomputable def quotientGlueData := relativeGluingData (coequifibered_invariantDiagramMap hTf)

instance : ((quotientGlueData hTf).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- Cor. V.1.8: the quotient `X/G = Spec_Z (f_* 𝒪_X)^G`. -/
noncomputable def quotientScheme : Scheme.{u} := (quotientGlueData hTf).glued

/-- The cover of `X/G` by the `Spec Γ(X, f⁻¹ U)^G`. -/
noncomputable def quotientOpenCover : (quotientScheme hTf).OpenCover :=
  (quotientGlueData hTf).cover

/-- The structure morphism `X/G ⟶ Z`. -/
noncomputable def fromQuotient : quotientScheme hTf ⟶ Z := (quotientGlueData hTf).toBase

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The quotient morphism `X ⟶ X/G`. -/
noncomputable def toQuotient : X ⟶ quotientScheme hTf :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((directedCover Z).pullback₁ f)
    (fun U ↦ (pullbackRestrictIsoRestrict f _).hom ≫
      (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (invariantSubring hTf U.1).subtype) ≫
        (quotientOpenCover hTf).f U) fun {U V : Z.AffineZariskiSite} i ↦ by
  have : (pullbackRestrictIsoRestrict f U.1).inv ≫
      Scheme.Cover.trans ((directedCover Z).pullback₁ f) i ≫
      (pullbackRestrictIsoRestrict f V.1).hom = X.homOfLE
        (f.preimage_mono (toOpens_mono i.1.1)) := by
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp +instances [Scheme.Cover.trans, Scheme.Cover.locallyDirectedPullbackCover]
  rw [← Iso.inv_comp_eq, reassoc_of% this, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Spec.map_comp_assoc]
  dsimp [quotientOpenCover]
  rw [← colimit.w (quotientGlueData hTf).functor i]
  dsimp [quotientGlueData, relativeGluingData]
  rw [← Spec.map_comp_assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma ι_toQuotient (U : Z.AffineZariskiSite) :
    (f ⁻¹ᵁ U.1).ι ≫ toQuotient hTf = (f ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (invariantSubring hTf U.1).subtype) ≫
        (quotientOpenCover hTf).f U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict f U.1).hom, ← Category.assoc]
  trans ((directedCover Z).pullback₁ f).f U ≫ toQuotient hTf
  · congr 1; simp
  delta toQuotient
  generalize_proofs _ _ _ _ H
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected _ _ H _

@[reassoc]
lemma ι_fromQuotient (U : Z.AffineZariskiSite) :
    (quotientOpenCover hTf).f U ≫ fromQuotient hTf =
      Spec.map ((invariantDiagramMap hTf).app (.op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma fromQuotient_preimage (U : Z.AffineZariskiSite) :
    fromQuotient hTf ⁻¹ᵁ U.1 = ((quotientOpenCover hTf).f U).opensRange := by
  simpa using! (quotientGlueData hTf).toBase_preimage_eq_opensRange_ι U

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma toQuotient_fromQuotient : toQuotient hTf ≫ fromQuotient hTf = f := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Z) f.base.1)) _ _ fun U ↦ ?_
  refine (ι_toQuotient_assoc hTf ⟨U.1, U.2⟩ _).trans ?_
  rw [ι_fromQuotient, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f.app _) ≫ U.2.fromSpec = (f ⁻¹ᵁ U.1).ι ≫ _
  simp

set_option backward.isDefEq.respectTransparency false in
lemma comp_toQuotient (g : G) : T g ≫ toQuotient hTf = toQuotient hTf := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Z) f.base.1)) _ _ fun U ↦ ?_
  change (f ⁻¹ᵁ U.1).ι ≫ T g ≫ toQuotient hTf = (f ⁻¹ᵁ U.1).ι ≫ toQuotient hTf
  have hle := preimage_le_preimage_of_comp_eq (hTf g) U.1
  rw [← Scheme.Hom.resLE_comp_ι_assoc (T g) hle, ι_toQuotient hTf ⟨U.1, U.2⟩,
    ← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, ← Spec.map_comp_assoc]
  congr 3
  ext x
  exact x.2 g

set_option backward.isDefEq.respectTransparency.types false in
instance : IsAffineHom (fromQuotient hTf) where
  isAffine_preimage U hU := by
    rw [fromQuotient_preimage hTf ⟨U, hU⟩]
    have : IsAffine ((quotientOpenCover hTf).X ⟨U, hU⟩) := inferInstanceAs (IsAffine (Spec _))
    exact isAffineOpen_opensRange _

instance : IsAffineHom (toQuotient hTf) := by
  apply MorphismProperty.of_postcomp (W := @IsAffineHom) (W' := @IsSeparated) _ (fromQuotient hTf)
  · infer_instance
  · rw [toQuotient_fromQuotient]
    infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- The sections of `X/G` over the preimage of an affine open `U` of `Z` are `Γ(X, f⁻¹ U)^G`. -/
noncomputable def quotientObjIso {U : Z.Opens} (hU : IsAffineOpen U) :
    Γ(quotientScheme hTf, fromQuotient hTf ⁻¹ᵁ U) ≅ .of (invariantSubring hTf U) :=
  (quotientScheme hTf).presheaf.mapIso (eqToIso
    (by simpa using! (fromQuotient_preimage hTf ⟨U, hU⟩).symm)).op ≪≫
  ((quotientOpenCover hTf).f ⟨U, hU⟩).appIso ⊤ ≪≫ Scheme.ΓSpecIso _

set_option backward.isDefEq.respectTransparency false in
lemma toQuotient_app_preimage (U : Z.affineOpens) :
    (toQuotient hTf).app (fromQuotient hTf ⁻¹ᵁ ↑U) =
      (quotientObjIso hTf U.2).hom ≫
      CommRingCat.ofHom (invariantSubring hTf U.1).subtype ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op := by
  dsimp [quotientObjIso]
  change _ = (quotientScheme hTf).presheaf.map (eqToHom (by simp [fromQuotient_preimage]; rfl)).op ≫
      (((quotientOpenCover hTf).f ⟨U.1, U.2⟩).appIso _).hom ≫
      (Scheme.ΓSpecIso _).hom ≫
      CommRingCat.ofHom (invariantSubring hTf U.1).subtype ≫
      X.presheaf.map (eqToHom (by simp [← Scheme.Hom.comp_preimage])).op
  have H : toQuotient hTf ⁻¹ᵁ fromQuotient hTf ⁻¹ᵁ U =
      (f ⁻¹ᵁ U.1).ι ''ᵁ (((f ⁻¹ᵁ U.1).ι ≫ toQuotient hTf) ⁻¹ᵁ fromQuotient hTf ⁻¹ᵁ U) := by
    simp [← Scheme.Hom.comp_preimage]
  convert! congr($(Scheme.Hom.congr_app (ι_toQuotient hTf ⟨U.1, U.2⟩) (fromQuotient hTf ⁻¹ᵁ U)) ≫
    X.presheaf.map (eqToHom H).op) using 1
  · simp [Scheme.Hom.app_eq_appLE]
  dsimp
  simp only [eqToHom_op, Scheme.Hom.appIso_hom, Category.assoc, Scheme.Hom.naturality_assoc,
    eqToHom_unop, ← Functor.map_comp_assoc, eqToHom_map (TopologicalSpace.Opens.map _),
    eqToHom_trans]
  congr 1
  rw [← IsIso.eq_inv_comp, ← Functor.map_inv, inv_eqToHom]
  simp [← Functor.map_comp, Scheme.Opens.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality_assoc (CommRingCat.ofHom _)]
  rfl

omit [IsAffineHom f] [Finite G] in
lemma sectionsAreInvariant_iff_of_eq {Y : Scheme.{u}} {p : X ⟶ Y} {hTp : ∀ g, T g ≫ p = p}
    {V : Y.Opens} {E : X.Opens} (hE : E = p ⁻¹ᵁ V) :
    SectionsAreInvariant T p hTp V ↔ (Function.Injective (p.appLE V E hE.le) ∧
      ∀ s : Γ(X, E), (∀ g, (T g).appLE E E (hE ▸ preimage_le_preimage_of_comp_eq (hTp g) V) s = s)
        → ∃ t, p.appLE V E hE.le t = s) := by
  subst hE
  rw [Scheme.Hom.appLE_eq_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- V.1.3's hypothesis for `X ⟶ X/G` over the preimage of an affine open of `Z`. -/
lemma sectionsAreInvariant_toQuotient_preimage (U : Z.affineOpens) :
    SectionsAreInvariant T (toQuotient hTf) (comp_toQuotient hTf) (fromQuotient hTf ⁻¹ᵁ U) := by
  have hE : f ⁻¹ᵁ U.1 = toQuotient hTf ⁻¹ᵁ fromQuotient hTf ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, toQuotient_fromQuotient]
  have happ : (toQuotient hTf).appLE (fromQuotient hTf ⁻¹ᵁ U) (f ⁻¹ᵁ U.1) hE.le =
      (quotientObjIso hTf U.2).hom ≫ CommRingCat.ofHom (invariantSubring hTf U.1).subtype := by
    rw [Scheme.Hom.appLE, toQuotient_app_preimage, Category.assoc, Category.assoc,
      ← Functor.map_comp, Subsingleton.elim (_ ≫ _) (𝟙 _), X.presheaf.map_id]
    rfl
  rw [sectionsAreInvariant_iff_of_eq hE, happ]
  refine ⟨fun a b hab ↦ (quotientObjIso hTf U.2).commRingCatIsoToRingEquiv.injective
    (Subtype.val_injective hab), fun s hs ↦ ⟨(quotientObjIso hTf U.2).inv ⟨s, hs⟩, ?_⟩⟩
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id_assoc]
  rfl

/-- Cor. V.1.8: `X ⟶ X/G` satisfies the condition `𝒪_{X/G} = p_*(𝒪_X)^G` of V.1.3 over every
open of `X/G`. -/
theorem sectionsAreInvariant_toQuotient (W : (quotientScheme hTf).Opens) :
    SectionsAreInvariant T (toQuotient hTf) (comp_toQuotient hTf) W := by
  refine sectionsAreInvariant_of_basis (fun y N hyN ↦ ?_) W
  obtain ⟨U, hU, hyU⟩ := exists_isAffineOpen_mem (fromQuotient hTf y)
  have hV : IsAffineOpen (fromQuotient hTf ⁻¹ᵁ U) := hU.preimage _
  obtain ⟨s, hsN, hys⟩ := hV.exists_basicOpen_le ⟨y, hyN⟩ hyU
  exact ⟨_, hsN, hys, (sectionsAreInvariant_toQuotient_preimage hTf ⟨U, hU⟩).basicOpen hV
    (hV.preimage _) s⟩

include hTf in
/-- Cor. V.1.8: if `X` is affine over `Z` and `G` acts by `Z`-automorphisms, then `G` acts
admissibly. -/
theorem isAdmissible_of_isAffineHom : IsAdmissible T :=
  ⟨_, toQuotient hTf, comp_toQuotient hTf, inferInstance, sectionsAreInvariant_toQuotient hTf⟩

/-- Cor. V.1.8: `X/G = Spec_Z (f_* 𝒪_X)^G` is the quotient of `X` by `G`. Its sections over the
preimage of an affine open `U ⊆ Z` are `Γ(X, f⁻¹ U)^G` (`quotientObjIso`). -/
theorem isQuotient_toQuotient [Group G] (hT : IsRightAction T) :
    IsQuotient T (toQuotient hTf) :=
  isQuotient_of_sectionsAreInvariant hT fun U _ ↦ sectionsAreInvariant_toQuotient hTf U

end Glue

section Subgroup

variable {G : Type*} [Group G] [Finite G] {X : Scheme.{u}} {T : G → (X ⟶ X)}

/-- Cor. V.1.7 (the first one): if `G` acts admissibly on `X`, so does every subgroup `H`, hence
`X/H` exists. As in SGA, `X` is affine over `Y = X/G` and `H` acts by `Y`-automorphisms, so
Cor. V.1.8 applies. -/
theorem IsAdmissible.subgroup (h : IsAdmissible T) (H : Subgroup G) :
    IsAdmissible fun h : H ↦ T h := by
  obtain ⟨Y, p, hTp, _, -⟩ := h
  exact isAdmissible_of_isAffineHom (f := p) fun g ↦ hTp g

end Subgroup

end SGA.SGA1.ExposeV
