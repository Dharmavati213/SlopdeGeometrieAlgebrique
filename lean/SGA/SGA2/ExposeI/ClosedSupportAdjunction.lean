/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.SupportedSheafSections
import SGA.SGA2.ExposeI.LocallyClosedIndependence
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# The extraordinary inverse image of a closed inclusion

The construction uses the original kernel `underlineGammaZ`, evaluated on
maximal ambient extensions of opens in the closed subset.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology
open CategoryTheory.Functor
open scoped ConcreteCategory

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- The maximal ambient open with prescribed intersection with a closed subset. -/
def closedOpenExtension (Z : Closeds X) : Opens (TopCat.of (Z : Set X)) ⥤ Opens X :=
  (show IsInducing (closedInclusion Z) from IsInducing.subtypeVal).functor

theorem closedOpenExtension_preimage (Z : Closeds X) (U : Opens (TopCat.of (Z : Set X))) :
    (Opens.map (closedInclusion Z)).obj ((closedOpenExtension Z).obj U) = U :=
  IsInducing.subtypeVal.map_functorObj U

theorem closedOpenExtension_le_iff (Z : Closeds X)
    {U : Opens (TopCat.of (Z : Set X))} {V : Opens X} :
    V ≤ (closedOpenExtension Z).obj U ↔ (Opens.map (closedInclusion Z)).obj V ≤ U :=
  IsInducing.subtypeVal.le_functorObj_iff

theorem closedOpenExtension_inf (Z : Closeds X)
    (U V : Opens (TopCat.of (Z : Set X))) :
    (closedOpenExtension Z).obj (U ⊓ V) =
      (closedOpenExtension Z).obj U ⊓ (closedOpenExtension Z).obj V :=
  IsInducing.subtypeVal.opensGI.gc.u_inf

theorem closedOpenExtension_compl_le (Z : Closeds X)
    (U : Opens (TopCat.of (Z : Set X))) : Z.compl ≤ (closedOpenExtension Z).obj U := by
  apply (closedOpenExtension_le_iff Z).mpr
  intro x hx
  exact False.elim (hx x.property)

theorem closedOpenExtension_mem (Z : Closeds X)
    (U : Opens (TopCat.of (Z : Set X))) (x : X) (hx : x ∈ Z) :
    x ∈ (closedOpenExtension Z).obj U ↔ (⟨x, hx⟩ : Z) ∈ U :=
  (show IsInducing (closedInclusion Z) from IsInducing.subtypeVal).mem_functorObj_iff
    U (x := ⟨x, hx⟩)

/-- The maximal extension of a restricted ambient open adds only the complement. -/
theorem closedOpenExtension_preimage_eq (Z : Closeds X) (U : Opens X) :
    (closedOpenExtension Z).obj ((Opens.map (closedInclusion Z)).obj U) = U ⊔ Z.compl := by
  apply le_antisymm
  · intro x hx
    by_cases hz : x ∈ Z
    · exact Or.inl ((closedOpenExtension_mem Z _ x hz).mp hx)
    · exact Or.inr hz
  · exact sup_le ((closedOpenExtension_le_iff Z).mpr le_rfl)
      (closedOpenExtension_compl_le Z _)

/-- Evaluation of the original support kernel respects relative excision. -/
def underlineGammaZRestrictionIso (F : Sheaf AddCommGrpCat.{u} X) (Z : Closeds X)
    {V' V : Opens X} (hV : V' ≤ V) (hcover : V ≤ V' ⊔ (V ⊓ Z.compl)) :
    (underlineGammaZ F Z).presheaf.obj (op V) ≅
      (underlineGammaZ F Z).presheaf.obj (op V') :=
  ((underlineGammaZSectionsEquiv F Z V).trans
    ((gammaZSections_restrict_addEquiv_of_cover F hV hcover).trans
      (underlineGammaZSectionsEquiv F Z V').symm)).toAddCommGrpIso

theorem underlineGammaZRestrictionIso_hom (F : Sheaf AddCommGrpCat.{u} X) (Z : Closeds X)
    {V' V : Opens X} (hV : V' ≤ V) (hcover : V ≤ V' ⊔ (V ⊓ Z.compl)) :
    (underlineGammaZRestrictionIso F Z hV hcover).hom =
      (underlineGammaZ F Z).presheaf.map (homOfLE hV).op := by
  ext s
  apply (underlineGammaZSectionsEquiv F Z V').injective
  change (underlineGammaZSectionsEquiv F Z V')
    ((underlineGammaZSectionsEquiv F Z V').symm
      (gammaZSections_restrict_addEquiv_of_cover F hV hcover
        (underlineGammaZSectionsEquiv F Z V s))) = _
  rw [AddEquiv.apply_symm_apply]
  exact (underlineGammaZSectionsEquiv_restrict F Z (homOfLE hV) s).symm

private theorem closedOpenExtension_iSup_cover (Z : Closeds X) {ι : Type u}
    (U : ι → Opens (TopCat.of (Z : Set X))) :
    (closedOpenExtension Z).obj (iSup U) ≤
      (⨆ i, (closedOpenExtension Z).obj (U i)) ⊔
        ((closedOpenExtension Z).obj (iSup U) ⊓ Z.compl) := by
  intro x hx
  by_cases hz : x ∈ Z
  · left
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp ((closedOpenExtension_mem Z _ x hz).mp hx)
    exact Opens.mem_iSup.mpr ⟨i, (closedOpenExtension_mem Z _ x hz).mpr hi⟩
  · exact Or.inr ⟨hx, hz⟩

private theorem closedSupportPresheaf_isSheaf (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Presheaf.IsSheaf ((closedOpenExtension Z).op ⋙ (underlineGammaZ F Z).presheaf) := by
  apply (Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U sf hc
  let K := underlineGammaZ F Z
  let V : ι → Opens X := fun i => (closedOpenExtension Z).obj (U i)
  have hc' : Presheaf.IsCompatible K.presheaf V sf := by
    intro i j
    have h := hc i j
    change K.presheaf.map ((closedOpenExtension Z).map ((U i).infLELeft (U j))).op
        (sf i) = K.presheaf.map
          ((closedOpenExtension Z).map ((U i).infLERight (U j))).op (sf j) at h
    have he := closedOpenExtension_inf Z (U i) (U j)
    have hleft : (closedOpenExtension Z).map ((U i).infLELeft (U j)) =
        eqToHom he ≫ (V i).infLELeft (V j) := Subsingleton.elim _ _
    have hright : (closedOpenExtension Z).map ((U i).infLERight (U j)) =
        eqToHom he ≫ (V i).infLERight (V j) := Subsingleton.elim _ _
    rw [hleft, hright, op_comp, op_comp, Functor.map_comp, Functor.map_comp,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact (ConcreteCategory.bijective_of_isIso (K.presheaf.map (eqToHom he).op)).1 h
  obtain ⟨s, hs, huniq⟩ := K.existsUnique_gluing V sf hc'
  have hle : iSup V ≤ (closedOpenExtension Z).obj (iSup U) :=
    iSup_le fun i => ((closedOpenExtension Z).map (Opens.leSupr U i)).le
  let e := underlineGammaZRestrictionIso F Z hle (closedOpenExtension_iSup_cover Z U)
  have he : e.hom = K.presheaf.map (homOfLE hle).op :=
    underlineGammaZRestrictionIso_hom F Z hle (closedOpenExtension_iSup_cover Z U)
  have hfac (i : ι) :
      K.presheaf.map ((closedOpenExtension Z).map (Opens.leSupr U i)).op =
        e.hom ≫ K.presheaf.map (Opens.leSupr V i).op := by
    rw [he, ← Functor.map_comp]
    congr 1
  refine ⟨e.inv s, ?_, ?_⟩
  · intro i
    change K.presheaf.map ((closedOpenExtension Z).map (Opens.leSupr U i)).op (e.inv s) = _
    rw [hfac, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
    exact hs i
  · intro t ht
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    rw [Iso.inv_hom_id_apply]
    apply huniq
    intro i
    rw [← ConcreteCategory.comp_apply, ← hfac]
    exact ht i

/-- Extraordinary inverse image for a closed inclusion, evaluated using the
original support kernel. -/
def iUpperShriek_closed (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X)) where
  obj F := ⟨(closedOpenExtension Z).op ⋙ (underlineGammaZ F Z).presheaf,
    closedSupportPresheaf_isSheaf Z F⟩
  map f := ⟨Functor.whiskerLeft (closedOpenExtension Z).op (underlineGammaZMap f Z).hom⟩
  map_id F := by
    apply CategoryTheory.Sheaf.hom_ext
    change Functor.whiskerLeft _ ((underlineGammaZFunctor Z).map (𝟙 F)).hom = _
    exact congrArg (fun f => Functor.whiskerLeft (closedOpenExtension Z).op f.hom)
      ((underlineGammaZFunctor Z).map_id F)
  map_comp f g := by
    apply CategoryTheory.Sheaf.hom_ext
    change Functor.whiskerLeft _ ((underlineGammaZFunctor Z).map (f ≫ g)).hom = _
    rw [Functor.map_comp]
    rfl

/-- Every morphism out of closed extension by zero has image supported on the
closed subset. -/
theorem closedPushforward_comp_toComplement (Z : Closeds X)
    (A : Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X)))
    {F : Sheaf AddCommGrpCat.{u} X} (f : (iBang_closed Z).obj A ⟶ F) :
    f ≫ toComplementPushforward F Z = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply (cancel_mono (complementPushforwardSectionsIso F Z U.unop).hom).mp
  change (f.hom.app U ≫ (toComplementPushforward F Z).hom.app U) ≫ _ = 0 ≫ _
  rw [Category.assoc, toComplementPushforward_comp_sectionsIso, zero_comp]
  change f.hom.app U ≫ F.presheaf.map
    (homOfLE (inf_le_left : U.unop ⊓ Z.compl ≤ U.unop)).op = 0
  rw [← f.hom.naturality]
  have hempty : (Opens.map (closedInclusion Z)).obj (U.unop ⊓ Z.compl) = ⊥ := by
    ext z
    exact ⟨fun hz => (hz.2 z.property).elim, False.elim⟩
  have hz := (IsZero.iff_id_eq_zero _).mpr ((A.isTerminalOfEqEmpty hempty).hom_ext _ _)
  have hfzero : f.hom.app (op (U.unop ⊓ Z.compl)) = 0 := hz.eq_of_src _ _
  rw [hfzero, comp_zero]

/-- The kernel universal property for an arbitrary sheaf on the closed subset. -/
def closedKernelHomEquiv (Z : Closeds X)
    (A : Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X)))
    (F : Sheaf AddCommGrpCat.{u} X) :
    ((iBang_closed Z).obj A ⟶ F) ≃ ((iBang_closed Z).obj A ⟶ underlineGammaZ F Z) where
  toFun f := kernel.lift _ f (closedPushforward_comp_toComplement Z A f)
  invFun g := g ≫ underlineGammaZ_ι F Z
  left_inv f := kernel.lift_ι _ _ _
  right_inv g := by apply (cancel_mono (underlineGammaZ_ι F Z)).mp; simp

private def closedPresheafAdjunction (Z : Closeds X) :
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Opens.map (closedInclusion Z)).op ⊣
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj (closedOpenExtension Z).op :=
  ((show IsInducing (closedInclusion Z) from IsInducing.subtypeVal).adjunction.op).whiskerLeft
    AddCommGrpCat.{u}

/-- The right adjunction on open sets induces the Hom comparison into the
original support kernel. -/
def closedKernelNaiveHomEquiv (Z : Closeds X)
    (A : Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X)))
    (F : Sheaf AddCommGrpCat.{u} X) :
    ((iBang_closed Z).obj A ⟶ underlineGammaZ F Z) ≃
      (A ⟶ (iUpperShriek_closed Z).obj F) where
  toFun f := ⟨(closedPresheafAdjunction Z).homEquiv _ _ f.hom⟩
  invFun g := ⟨((closedPresheafAdjunction Z).homEquiv _ _).symm g.hom⟩
  left_inv f := by
    apply CategoryTheory.Sheaf.hom_ext
    exact Equiv.symm_apply_apply _ f.hom
  right_inv g := by
    apply CategoryTheory.Sheaf.hom_ext
    exact Equiv.apply_symm_apply _ g.hom

/-- The actual closed extension-by-zero / extraordinary inverse-image Hom
equivalence for arbitrary abelian coefficient sheaves. -/
def closedSupportHomAdjunctionEquiv (Z : Closeds X)
    (A : Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X)))
    (F : Sheaf AddCommGrpCat.{u} X) :
    ((iBang_closed Z).obj A ⟶ F) ≃ (A ⟶ (iUpperShriek_closed Z).obj F) :=
  (closedKernelHomEquiv Z A F).trans (closedKernelNaiveHomEquiv Z A F)

theorem closedSupportHomAdjunctionEquiv_symm_naturality_left (Z : Closeds X)
    {A B : Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X))}
    {F : Sheaf AddCommGrpCat.{u} X} (f : A ⟶ B)
    (g : B ⟶ (iUpperShriek_closed Z).obj F) :
    (closedSupportHomAdjunctionEquiv Z A F).symm (f ≫ g) =
      (iBang_closed Z).map f ≫ (closedSupportHomAdjunctionEquiv Z B F).symm g := by
  change (closedKernelNaiveHomEquiv Z A F).symm (f ≫ g) ≫ underlineGammaZ_ι F Z = _
  have h : (closedKernelNaiveHomEquiv Z A F).symm (f ≫ g) =
      (iBang_closed Z).map f ≫ (closedKernelNaiveHomEquiv Z B F).symm g := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (closedPresheafAdjunction Z).homEquiv_naturality_left_symm f.hom g.hom
  rw [h, Category.assoc]
  rfl

theorem closedSupportHomAdjunctionEquiv_naturality_right (Z : Closeds X)
    (A : Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X)))
    {F G : Sheaf AddCommGrpCat.{u} X} (f : (iBang_closed Z).obj A ⟶ F) (g : F ⟶ G) :
    closedSupportHomAdjunctionEquiv Z A G (f ≫ g) =
      closedSupportHomAdjunctionEquiv Z A F f ≫ (iUpperShriek_closed Z).map g := by
  have h : closedKernelHomEquiv Z A G (f ≫ g) =
      closedKernelHomEquiv Z A F f ≫ underlineGammaZMap g Z := by
    apply (cancel_mono (underlineGammaZ_ι G Z)).mp
    simp [closedKernelHomEquiv, Category.assoc]
  change closedKernelNaiveHomEquiv Z A G (closedKernelHomEquiv Z A G (f ≫ g)) = _
  rw [h]
  apply CategoryTheory.Sheaf.hom_ext
  exact (closedPresheafAdjunction Z).homEquiv_naturality_right
    (closedKernelHomEquiv Z A F f).hom (underlineGammaZMap g Z).hom

/-- Closed extension by zero is left adjoint to the genuine extraordinary
inverse image for arbitrary abelian sheaves. -/
def closedSupportAdjunction (Z : Closeds X) : iBang_closed Z ⊣ iUpperShriek_closed Z :=
  Adjunction.mkOfHomEquiv
    { homEquiv := closedSupportHomAdjunctionEquiv Z
      homEquiv_naturality_left_symm := closedSupportHomAdjunctionEquiv_symm_naturality_left Z
      homEquiv_naturality_right := closedSupportHomAdjunctionEquiv_naturality_right Z _ }

/-- The comparison with the original support kernel is ordinary restriction
from the maximal ambient extension. -/
def closedSupportPushforwardToKernel (Z : Closeds X) :
    iUpperShriek_closed Z ⋙ iBang_closed Z ⟶ underlineGammaZFunctor Z where
  app F := ⟨
    { app U := (underlineGammaZ F Z).presheaf.map
        (homOfLE ((closedOpenExtension_le_iff Z).mpr le_rfl) :
          U.unop ⟶ (closedOpenExtension Z).obj ((Opens.map (closedInclusion Z)).obj U.unop)).op
      naturality U V f := by
        change (underlineGammaZ F Z).presheaf.map _ ≫
          (underlineGammaZ F Z).presheaf.map _ =
            (underlineGammaZ F Z).presheaf.map _ ≫ (underlineGammaZ F Z).presheaf.map _
        simp only [← Functor.map_comp]
        congr 1 }⟩
  naturality F G f := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact ((underlineGammaZMap f Z).hom.naturality _).symm

instance closedSupportPushforwardToKernel_app_isIso (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) : IsIso ((closedSupportPushforwardToKernel Z).app F) := by
  have : ∀ U, IsIso (((closedSupportPushforwardToKernel Z).app F).hom.app U) := by
    intro U
    have hle : U.unop ≤
        (closedOpenExtension Z).obj ((Opens.map (closedInclusion Z)).obj U.unop) :=
      (closedOpenExtension_le_iff Z).mpr le_rfl
    have hcover : (closedOpenExtension Z).obj ((Opens.map (closedInclusion Z)).obj U.unop) ≤
        U.unop ⊔ ((closedOpenExtension Z).obj
          ((Opens.map (closedInclusion Z)).obj U.unop) ⊓ Z.compl) := by
      rw [closedOpenExtension_preimage_eq]
      exact sup_le le_sup_left (fun x hx => Or.inr ⟨Or.inr hx, hx⟩)
    change IsIso ((underlineGammaZ F Z).presheaf.map (homOfLE hle).op)
    rw [← underlineGammaZRestrictionIso_hom F Z hle hcover]
    infer_instance
  have : IsIso ((closedSupportPushforwardToKernel Z).app F).hom :=
    NatIso.isIso_of_isIso_app _
  refine ⟨⟨⟨inv ((closedSupportPushforwardToKernel Z).app F).hom⟩, ?_, ?_⟩⟩
  · apply CategoryTheory.Sheaf.hom_ext
    exact IsIso.hom_inv_id _
  · apply CategoryTheory.Sheaf.hom_ext
    exact IsIso.inv_hom_id _

/-- Pushing forward the genuine extraordinary inverse image recovers the
unchanged original support kernel, naturally in arbitrary coefficients. -/
def closedSupportPushforwardIso (Z : Closeds X) :
    iUpperShriek_closed Z ⋙ iBang_closed Z ≅ underlineGammaZFunctor Z :=
  NatIso.ofComponents (fun F => asIso ((closedSupportPushforwardToKernel Z).app F))
    (fun f => (closedSupportPushforwardToKernel Z).naturality f)

/-- Under the kernel comparison, the actual adjunction counit is the
unchanged inclusion of supported sections into the coefficient sheaf. -/
theorem closedSupportAdjunction_counit_app (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (closedSupportAdjunction Z).counit.app F =
      (closedSupportPushforwardIso Z).hom.app F ≫ underlineGammaZ_ι F Z := by
  change (closedKernelNaiveHomEquiv Z ((iUpperShriek_closed Z).obj F) F).symm (𝟙 _) ≫
    underlineGammaZ_ι F Z = _
  congr 1

private instance closedPresheafAdjunction_unit_isIso (Z : Closeds X) :
    IsIso (closedPresheafAdjunction Z).unit := by
  have : ∀ P, IsIso ((closedPresheafAdjunction Z).unit.app P) := by
    intro P
    have : ∀ U, IsIso (((closedPresheafAdjunction Z).unit.app P).app U) := by
      intro U
      change IsIso (P.map
        (((show IsInducing (closedInclusion Z) from IsInducing.subtypeVal).adjunction.counit.app
          U.unop).op))
      have h : ((show IsInducing (closedInclusion Z) from
          IsInducing.subtypeVal).adjunction.counit.app U.unop) =
          eqToHom (closedOpenExtension_preimage Z U.unop) :=
        Subsingleton.elim _ _
      rw [h]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- Closed pushforward is fully faithful, for arbitrary abelian sheaves. -/
def fullyFaithfulIBangClosed (Z : Closeds X) : (iBang_closed Z).FullyFaithful where
  preimage f := ⟨(closedPresheafAdjunction Z).fullyFaithfulLOfIsIsoUnit.preimage f.hom⟩
  map_preimage f := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (closedPresheafAdjunction Z).fullyFaithfulLOfIsIsoUnit.map_preimage f.hom
  preimage_map f := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (closedPresheafAdjunction Z).fullyFaithfulLOfIsIsoUnit.preimage_map f.hom

instance iBang_closed_full (Z : Closeds X) : (iBang_closed Z).Full :=
  (fullyFaithfulIBangClosed Z).full

instance iBang_closed_faithful (Z : Closeds X) : (iBang_closed Z).Faithful :=
  (fullyFaithfulIBangClosed Z).faithful

/-- The extraordinary inverse image is canonically the ordinary closed
pullback of the original support kernel. -/
def closedSupportPullbackIso (Z : Closeds X) :
    iUpperShriek_closed Z ≅
      underlineGammaZFunctor Z ⋙ Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z) :=
  (Functor.rightUnitor _).symm ≪≫
    isoWhiskerLeft (iUpperShriek_closed Z)
      (asIso (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (closedInclusion Z)).counit).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (closedSupportPushforwardIso Z)
      (Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z))

/-- The same genuine adjunction with extraordinary inverse image expressed
literally as closed pullback of the original support kernel. -/
def closedSupportPullbackAdjunction (Z : Closeds X) :
    iBang_closed Z ⊣
      underlineGammaZFunctor Z ⋙ Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z) :=
  (closedSupportAdjunction Z).ofNatIsoRight (closedSupportPullbackIso Z)

/-- Extraordinary inverse image for the given locally closed immersion. -/
def iUpperShriek_locallyClosed (W : LocallyClosedIn X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} (TopCat.of (W.ZV : Set W.V)) :=
  iShriek_open W.V ⋙ iUpperShriek_closed (X := (Opens.toTopCat X).obj W.V) W.ZV

/-- The actual composite locally closed extension by zero has the expected
extraordinary inverse-image right adjoint. -/
def locallyClosedSupportAdjunction (W : LocallyClosedIn X) :
    iBang_locallyClosed W ⊣ iUpperShriek_locallyClosed W :=
  (closedSupportAdjunction (X := (Opens.toTopCat X).obj W.V) W.ZV).comp
    (openExtensionByZeroAdjunction W.V)

instance iBang_closed_isLeftAdjoint (Z : Closeds X) : (iBang_closed Z).IsLeftAdjoint :=
  (closedSupportAdjunction Z).isLeftAdjoint

instance iUpperShriek_closed_isRightAdjoint (Z : Closeds X) :
    (iUpperShriek_closed Z).IsRightAdjoint :=
  (closedSupportAdjunction Z).isRightAdjoint

instance iUpperShriek_closed_additive (Z : Closeds X) : (iUpperShriek_closed Z).Additive :=
  (closedSupportAdjunction Z).right_adjoint_additive

/-- Closed extension by zero is exact for arbitrary abelian sheaves. -/
instance iBang_closed_preservesHomology (Z : Closeds X) : (iBang_closed Z).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels (iBang_closed Z)

theorem iBang_closed_shortExact (Z : Closeds X)
    (S : ShortComplex (Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X))))
    (hS : S.ShortExact) : (S.map (iBang_closed Z)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map (iBang_closed Z)

/-- Extraordinary closed inverse image preserves injective sheaves. -/
instance iUpperShriek_closed_preservesInjectiveObjects (Z : Closeds X) :
    (iUpperShriek_closed Z).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (closedSupportAdjunction Z)

/-- Extraordinary locally closed inverse image preserves injective sheaves. -/
instance iUpperShriek_locallyClosed_preservesInjectiveObjects (W : LocallyClosedIn X) :
    (iUpperShriek_locallyClosed W).PreservesInjectiveObjects :=
  inferInstanceAs (iShriek_open W.V ⋙
    iUpperShriek_closed (X := (Opens.toTopCat X).obj W.V) W.ZV).PreservesInjectiveObjects

end SGA.SGA2.ExposeI
