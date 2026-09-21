/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleClosedSupportObject
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Supported module sheaves preserve injectives

The left adjoint to the actual supported-section sheaf is the sheafification
of the pointwise quotient by the module presheaf extended by zero from the
open complement. This quotient preserves monomorphisms: on each open its
relation submodule is either zero or the whole module. Sheafification also
preserves monomorphisms. The proved adjunction therefore shows that supported
sections of an injective module sheaf are injective, as required in VI.1.5.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (Z : Closeds X)

/-- The sectionwise quotient by sections in the complement of the closed support. -/
def moduleSupportQuotientPresheaf (F : PresheafOfModules.{u} R.obj) :
    PresheafOfModules.{u} R.obj where
  obj U := ModuleCat.of (R.obj.obj U) (F.obj U ⧸ (moduleOpenSubpresheaf F Z.compl).obj U)
  map {U V} i := ModuleCat.semilinearMapAddEquiv _ _ _
    (((moduleOpenSubpresheaf F Z.compl).obj U).mapQ
      ((moduleOpenSubpresheaf F Z.compl).obj V) (F.restrictₛₗ i)
        ((moduleOpenSubpresheaf F Z.compl).map i))
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      change ((moduleOpenSubpresheaf F Z.compl).obj U).mkQ (F.map (𝟙 U) x) =
        ((moduleOpenSubpresheaf F Z.compl).obj U).mkQ x
      exact congrArg ((moduleOpenSubpresheaf F Z.compl).obj U).mkQ
        (ConcreteCategory.congr_hom (F.presheaf.map_id U) x)
  map_comp i j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk (F.map (i ≫ j) x) =
        Submodule.Quotient.mk (F.map j (F.map i x))
      rw [F.map_comp_apply]

/-- The actual induced coefficient map on the pointwise quotients. -/
def moduleSupportQuotientMap {F G : PresheafOfModules.{u} R.obj} (a : F ⟶ G) :
    moduleSupportQuotientPresheaf R Z F ⟶ moduleSupportQuotientPresheaf R Z G where
  app U := ModuleCat.ofHom
    (((moduleOpenSubpresheaf F Z.compl).obj U).mapQ
      ((moduleOpenSubpresheaf G Z.compl).obj U) (a.app U).hom (by
        intro x hx
        rcases (moduleOpenSubpresheaf_mem_iff R _ _ _ _).mp hx with rfl | hU
        · exact (moduleOpenSubpresheaf_mem_iff R _ _ _ _).mpr (Or.inl (map_zero _))
        · exact mem_moduleOpenSubpresheaf _ _ hU _))
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      change Submodule.Quotient.mk (a.app V (F.map i x)) =
        Submodule.Quotient.mk (G.map i (a.app U x))
      rw [PresheafOfModules.naturality_apply]

/-- The pointwise support quotient, functorial in the original module presheaf. -/
def moduleSupportQuotientFunctor :
    PresheafOfModules.{u} R.obj ⥤ PresheafOfModules.{u} R.obj where
  obj F := moduleSupportQuotientPresheaf R Z F
  map a := moduleSupportQuotientMap R Z a
  map_id F := by
    ext U q
    induction q using Submodule.Quotient.induction_on with | _ x => rfl
  map_comp a b := by
    ext U q
    induction q using Submodule.Quotient.induction_on with | _ x => rfl

/-- Pointwise support quotients preserve actual monomorphisms. -/
instance moduleSupportQuotientFunctor_preservesMonomorphisms :
    (moduleSupportQuotientFunctor R Z).PreservesMonomorphisms where
  preserves a ha := by
    apply PresheafOfModules.mono_of_injective
    intro U q q' h
    induction q using Submodule.Quotient.induction_on with | _ x =>
      induction q' using Submodule.Quotient.induction_on with | _ y =>
        change Submodule.Quotient.mk (a.app U x) = Submodule.Quotient.mk (a.app U y) at h
        apply (Submodule.Quotient.eq' _).mpr
        apply (moduleOpenSubpresheaf_mem_iff R _ _ _ _).mpr
        rcases (moduleOpenSubpresheaf_mem_iff R _ _ _ _).mp
          ((Submodule.Quotient.eq' _).mp h) with hxy | hU
        · apply Or.inl
          apply PresheafOfModules.injective_of_mono a U
          rw [map_add, map_neg, hxy, map_zero]
        · exact Or.inr hU

/-- Sheafification of the actual pointwise quotient. -/
def moduleSupportQuotientSheafFunctor : SheafOfModules.{u} R ⥤ SheafOfModules.{u} R :=
  SheafOfModules.forget R ⋙ moduleSupportQuotientFunctor R Z ⋙
    PresheafOfModules.sheafification (𝟙 R.obj)

instance moduleSupportQuotientSheafFunctor_preservesMonomorphisms :
    (moduleSupportQuotientSheafFunctor R Z).PreservesMonomorphisms := by
  dsimp [moduleSupportQuotientSheafFunctor]
  infer_instance

/-- A quotient morphism has supported values. -/
def moduleSupportQuotientHomToSupported (F G : SheafOfModules.{u} R)
    (φ : moduleSupportQuotientPresheaf R Z F.val ⟶ G.val) :
    F ⟶ moduleGammaZSheaf R Z G :=
  ⟨
    { app U := ModuleCat.ofHom (X := F.val.obj U) (Y := (moduleGammaZSheaf R Z G).val.obj U)
        { toFun x :=
            ⟨φ.app U (Submodule.Quotient.mk x), by
              change G.val.map (homOfLE (inf_le_left : U.unop ⊓ Z.compl ≤ U.unop)).op
                (φ.app U (Submodule.Quotient.mk x)) = 0
              rw [← PresheafOfModules.naturality_apply]
              change φ.app (op (U.unop ⊓ Z.compl))
                (Submodule.Quotient.mk (F.val.map (homOfLE inf_le_left).op x)) = 0
              rw [(Submodule.Quotient.mk_eq_zero _).mpr
                (mem_moduleOpenSubpresheaf _ _ inf_le_right _), map_zero]⟩
          map_add' x y := by
            apply Subtype.ext
            change φ.app U (Submodule.Quotient.mk (x + y)) =
              φ.app U (Submodule.Quotient.mk x) + φ.app U (Submodule.Quotient.mk y)
            rw [Submodule.Quotient.mk_add, map_add]
          map_smul' r x := by
            apply Subtype.ext
            change φ.app U (Submodule.Quotient.mk (r • x)) =
              r • φ.app U (Submodule.Quotient.mk x)
            rw [Submodule.Quotient.mk_smul, (φ.app U).hom.map_smul] }
      naturality {U V} i := by
        ext x
        apply Subtype.ext
        exact PresheafOfModules.naturality_apply φ i (Submodule.Quotient.mk x) }⟩

/-- A map with actually supported values annihilates the complement relation submodules. -/
theorem moduleSupportedHom_kills_complement (F G : SheafOfModules.{u} R)
    (φ : F ⟶ moduleGammaZSheaf R Z G) (U : (Opens X)ᵒᵖ) :
    (moduleOpenSubpresheaf F.val Z.compl).obj U ≤
      LinearMap.ker (((φ ≫ moduleGammaZSheafι R Z G).val.app U).hom) := by
  intro x hx
  rcases (moduleOpenSubpresheaf_mem_iff R _ _ _ _).mp hx with rfl | hU
  · exact map_zero _
  · exact moduleGammaZSheaf_section_eq_zero R Z G hU (φ.val.app U x)

/-- Descent of a supported-valued map through the actual support quotient. -/
def moduleSupportQuotientHomOfSupported (F G : SheafOfModules.{u} R)
    (φ : F ⟶ moduleGammaZSheaf R Z G) :
    moduleSupportQuotientPresheaf R Z F.val ⟶ G.val where
  app U := ModuleCat.ofHom (((moduleOpenSubpresheaf F.val Z.compl).obj U).liftQ
    ((φ ≫ moduleGammaZSheafι R Z G).val.app U).hom
      (moduleSupportedHom_kills_complement R Z F G φ U))
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      exact PresheafOfModules.naturality_apply (φ ≫ moduleGammaZSheafι R Z G).val i x

/-- The support quotient is left adjoint to the original supported coefficient module sheaf. -/
def moduleSupportQuotientHomEquiv (F G : SheafOfModules.{u} R) :
    (moduleSupportQuotientPresheaf R Z F.val ⟶ G.val) ≃ (F ⟶ moduleGammaZSheaf R Z G) where
  toFun := moduleSupportQuotientHomToSupported R Z F G
  invFun := moduleSupportQuotientHomOfSupported R Z F G
  left_inv φ := by
    ext U q
    induction q using Submodule.Quotient.induction_on with | _ x => rfl
  right_inv φ := by ext U x; rfl

/-- The quotient/sheafification Hom representation uses the actual support-section module. -/
def moduleSupportQuotientSheafHomEquiv (F G : SheafOfModules.{u} R) :
    ((moduleSupportQuotientSheafFunctor R Z).obj F ⟶ G) ≃ (F ⟶ moduleGammaZSheaf R Z G) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
    (moduleSupportQuotientHomEquiv R Z F G)

/-- The genuine support quotient is a mono-preserving left adjoint of supported sections. -/
def moduleSupportQuotientSheafAdjunction :
    moduleSupportQuotientSheafFunctor R Z ⊣ moduleGammaZSheafFunctor R Z :=
  Adjunction.mkOfHomEquiv
    { homEquiv := moduleSupportQuotientSheafHomEquiv R Z
      homEquiv_naturality_left_symm := by
        intro F G H a φ
        apply (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).injective
        change (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _
            ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm _) =
          (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _
            ((PresheafOfModules.sheafification (𝟙 R.obj)).map
              (moduleSupportQuotientMap R Z a.val) ≫
                (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm _)
        rw [Adjunction.homEquiv_naturality_left]
        simp only [PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
          Equiv.apply_symm_apply]
        ext U q
        induction q using Submodule.Quotient.induction_on with | _ x => rfl
      homEquiv_naturality_right := by
        intro F G H a φ
        ext U x
        rfl }

/-- **I.1.4 / VI.1.5:** the actual supported-module sheaf functor preserves injective objects. -/
instance moduleGammaZSheafFunctor_preservesInjectiveObjects :
    (moduleGammaZSheafFunctor R Z).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (moduleSupportQuotientSheafAdjunction R Z)

end SGA.SGA2.ExposeVI
