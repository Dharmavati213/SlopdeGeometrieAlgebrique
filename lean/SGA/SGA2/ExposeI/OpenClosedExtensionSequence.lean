/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.OpenExtensionCounit
import SGA.SGA2.ExposeI.LocallyClosedSupportCohomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # The arbitrary-coefficient open–closed extension sequence

The maps are the original open extension/restriction counit and closed
pullback/direct-image unit. The cokernel identification is proved using
their adjunctions and the genuine classification of closed-supported sheaves.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

section Reflection
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive]
  (adj : L ⊣ R) {A B : C} (f : A ⟶ B)

include adj in
private theorem reflective_map_cokernelπ_isIso (hA : IsZero (L.obj A)) :
    IsIso (L.map (cokernel.π f)) := by
  let := adj.isLeftAdjoint
  let hc := isColimitCoforkMapOfIsColimit' L (cokernel.condition f) (cokernelIsCokernel f)
  exact CokernelCofork.IsColimit.isIso_π _ hc (hA.eq_of_src _ _)

/-- A cokernel lying in a reflective subcategory is the reflected target
when the source becomes zero under the reflector. -/
private def reflectiveCokernelIso (hA : IsZero (L.obj A))
    (hQ : IsIso (adj.unit.app (cokernel f))) :
    cokernel f ≅ R.obj (L.obj B) := by
  letI := hQ
  letI := reflective_map_cokernelπ_isIso adj f hA
  exact asIso (adj.unit.app (cokernel f)) ≪≫ (R.mapIso (asIso (L.map (cokernel.π f)))).symm

private theorem reflectiveCokernelIso_fac (hA : IsZero (L.obj A))
    (hQ : IsIso (adj.unit.app (cokernel f))) :
    cokernel.π f ≫ (reflectiveCokernelIso adj f hA hQ).hom = adj.unit.app B := by
  let := reflective_map_cokernelπ_isIso adj f hA
  change cokernel.π f ≫ (adj.unit.app (cokernel f) ≫ R.map (inv (L.map (cokernel.π f)))) = _
  have hn := adj.unit.naturality (cokernel.π f)
  change cokernel.π f ≫ adj.unit.app (cokernel f) =
    adj.unit.app B ≫ R.map (L.map (cokernel.π f)) at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← R.map_comp, IsIso.hom_inv_id, R.map_id]
  exact Category.comp_id _

private def reflectiveUnit_cokernel (hA : IsZero (L.obj A))
    (hQ : IsIso (adj.unit.app (cokernel f))) (w : f ≫ adj.unit.app B = 0) :
    IsColimit (CokernelCofork.ofπ (adj.unit.app B) w) := by
  let e := reflectiveCokernelIso adj f hA hQ
  have he : cokernel.π f ≫ e.hom = adj.unit.app B := reflectiveCokernelIso_fac adj f hA hQ
  have : Epi (adj.unit.app B) := by rw [← he]; infer_instance
  exact CokernelCofork.IsColimit.ofπ' _ _ (fun g hg =>
    ⟨e.inv ≫ cokernel.desc f g hg, by rw [← he]; simp⟩)

end Reflection

variable {X : TopCat.{u}}

/-- A closed direct image is genuinely zero after restriction to its open
complement, for every coefficient sheaf on the closed subset. -/
theorem restrictClosedPushforward_isZero (Z : Closeds X)
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X))) :
    IsZero (restrictToOpen ((iBang_closed Z).obj G) Z.compl) := by
  apply IsZero.of_iso (Y := Z.compl.sheafRestrict.obj ((iBang_closed Z).obj G)) _
    ((openPullbackSheafRestrictIso Z.compl).app _)
  apply IsZero.of_full_of_faithful_of_isZero
    (sheafToPresheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj Z.compl))
      AddCommGrpCat.{u})
  apply Functor.isZero
  intro V
  change IsZero (G.obj.obj (op ((Opens.map (closedInclusion Z)).obj
    (Z.compl.isOpenEmbedding.functor.obj V.unop))))
  have he : (Opens.map (closedInclusion Z)).obj
      (Z.compl.isOpenEmbedding.functor.obj V.unop) = ⊥ := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      change y.val = x.val at hxy
      have hx : x.val ∈ Z.compl := by rw [← hxy]; exact y.property
      exact (hx x.property).elim
    · exact False.elim
  exact (IsZero.iff_id_eq_zero _).mpr ((G.isTerminalOfEqEmpty he).hom_ext _ _)

/-- Ordinary closed pullback of an arbitrary open extension by zero on the
complement is zero. Both Hom adjunctions are the actual original adjunctions. -/
theorem closedPullbackOpenExtension_isZero (Z : Closeds X)
    (G : Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj Z.compl)) :
    IsZero ((Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z)).obj
      ((iBang_open Z.compl).obj G)) := by
  let Q := (Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z)).obj
    ((iBang_open Z.compl).obj G)
  let e := ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (closedInclusion Z)).homAddEquiv
    ((iBang_open Z.compl).obj G) Q).trans
      ((openExtensionByZeroAdjunction Z.compl).homAddEquiv G ((iBang_closed Z).obj Q))
  apply (IsZero.iff_id_eq_zero _).mpr
  apply e.injective
  exact (restrictClosedPushforward_isZero Z Q).eq_of_tgt _ _

/-- The two original canonical maps have zero composite. -/
theorem openClosedExtension_comp (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    (openExtensionByZeroAdjunction Z.compl).counit.app F ≫
      (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (closedInclusion Z)).unit.app F = 0 := by
  apply ((openExtensionByZeroAdjunction Z.compl).homAddEquiv _ _).injective
  exact (restrictClosedPushforward_isZero Z
    ((Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z)).obj F)).eq_of_tgt _ _

/-- The cokernel of the original open counit has zero ordinary restriction
to that open: the restricted counit is a monic split epimorphism. -/
theorem openExtensionCounit_cokernel_restrict_isZero (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    IsZero (restrictToOpen (cokernel ((openExtensionByZeroAdjunction U).counit.app F)) U) := by
  let c := (openExtensionByZeroAdjunction U).counit.app F
  have : Mono c := openExtensionByZero_counit_mono U F
  have : Mono ((iShriek_open U).map c) := inferInstance
  have ht := (openExtensionByZeroAdjunction U).right_triangle_components F
  have : Epi ((iShriek_open U).map c) := epi_of_epi_fac ht
  exact (isZero_cokernel_of_epi ((iShriek_open U).map c)).of_iso
    (PreservesCokernel.iso (iShriek_open U) c)

/-- If a sheaf vanishes on the complement, its actual closed adjunction
unit is an isomorphism (not just an unspecified object comparison). -/
theorem closedPullback_unit_isIso_of_restrict_isZero (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (hF : IsZero (restrictToOpen F Z.compl)) :
    IsIso ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (closedInclusion Z)).unit.app F) := by
  let := underlineGammaZ_ι_isIso_of_restrict_isZero Z F hF
  let e : F ≅ (iBang_closed Z).obj
      ((Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z)).obj F) :=
    (asIso (underlineGammaZ_ι F Z)).symm ≪≫ ((closedSupportPushforwardIso Z).app F).symm ≪≫
      (iBang_closed Z).mapIso ((closedSupportPullbackIso Z).app F) ≪≫
      (iBang_closed Z).mapIso ((Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z)).mapIso
        (asIso (underlineGammaZ_ι F Z)))
  exact (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (closedInclusion Z)).isIso_unit_app_of_iso e

/-- The canonical closed unit is the actual cokernel of the original open
extension-by-zero counit. -/
def openClosedExtensionIsCokernel (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    IsColimit (CokernelCofork.ofπ
      ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (closedInclusion Z)).unit.app F)
      (openClosedExtension_comp Z F)) :=
  reflectiveUnit_cokernel
    (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (closedInclusion Z))
    ((openExtensionByZeroAdjunction Z.compl).counit.app F)
    (closedPullbackOpenExtension_isZero Z (restrictToOpen F Z.compl))
    (closedPullback_unit_isIso_of_restrict_isZero Z _
      (openExtensionCounit_cokernel_restrict_isZero Z.compl F))
    (openClosedExtension_comp Z F)

/-- The original arbitrary-coefficient open–closed extension sequence. -/
def openClosedExtensionSequence (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk ((openExtensionByZeroAdjunction Z.compl).counit.app F)
    ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (closedInclusion Z)).unit.app F)
    (openClosedExtension_comp Z F)

/-- **I.1, (17), `Z = X` case, arbitrary coefficients:** the canonical
sequence `0 → j_!j^*F → F → i_*i^*F → 0` is short exact. -/
theorem openClosedExtensionSequence_shortExact (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) : (openClosedExtensionSequence Z F).ShortExact where
  exact := (openClosedExtensionSequence Z F).exact_of_g_is_cokernel
    (openClosedExtensionIsCokernel Z F)
  mono_f := openExtensionByZero_counit_mono Z.compl F
  epi_g := Cofork.IsColimit.epi (openClosedExtensionIsCokernel Z F)

/-- Every actual coefficient morphism induces the canonical morphism of
the extension sequences, by naturality of the original unit and counit. -/
def openClosedExtensionSequenceMap (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    openClosedExtensionSequence Z F ⟶ openClosedExtensionSequence Z G where
  τ₁ := (iBang_open Z.compl).map ((iShriek_open Z.compl).map f)
  τ₂ := f
  τ₃ := (iBang_closed Z).map ((Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z)).map f)
  comm₁₂ := (openExtensionByZeroAdjunction Z.compl).counit.naturality f
  comm₂₃ := (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (closedInclusion Z)).unit.naturality f

/-- The original short exact sequences are functorial in arbitrary coefficients. -/
def openClosedExtensionSequenceFunctor (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X ⥤ ShortComplex (Sheaf AddCommGrpCat.{u} X) where
  obj F := openClosedExtensionSequence Z F
  map f := openClosedExtensionSequenceMap Z f
  map_id F := by ext <;> simp [openClosedExtensionSequenceMap, openClosedExtensionSequence]
  map_comp f g := by ext <;> simp [openClosedExtensionSequenceMap, CategoryTheory.Functor.map_comp]

end SGA.SGA2.ExposeI
