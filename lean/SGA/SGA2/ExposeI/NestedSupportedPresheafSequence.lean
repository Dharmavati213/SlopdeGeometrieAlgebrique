/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.NestedSupportSections
import SGA.SGA2.ExposeI.LocallyClosedSupportedSheaves
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# The genuine nested supported-section presheaf sequence

The original ambient locally closed supported sheaves have sections
`Γ_Z(V ∩ U,F)`. Actual inclusion and restriction on these groups are
natural in the ambient open and in coefficients. Their exactness is
proved on sections and gives the sheaf sequence of I.1.9.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- Actual sections with support on intersection with the open witness. -/
def gammaIntersectionPresheafFunctor (Z : Closeds X) (V : Opens X) :
    Sheaf AddCommGrpCat.{u} X ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  gammaZSectionsPresheafFunctor Z ⋙
    (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openIntersectionFunctor V).op

/-- The original locally closed supported sheaf has exactly this presheaf. -/
def openClosedSupportedPresheafIso (Z : Closeds X) (V : Opens X) :
    underlineGammaLocallyClosedFunctor (LocallyClosedIn.ofOpenClosed V Z) ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
        gammaIntersectionPresheafFunctor Z V :=
  underlineGammaLocallyClosedPresheafFunctorIso (LocallyClosedIn.ofOpenClosed V Z) ≪≫
    locallyClosedAmbientPresheafIso (LocallyClosedIn.ofOpenClosed V Z) Z rfl

/-- Actual inclusion of supported-section presheaves. -/
def nestedSupportedPresheafInclusion {A B : Closeds X} (h : A ≤ B) (V : Opens X) :
    gammaIntersectionPresheafFunctor A V ⟶ gammaIntersectionPresheafFunctor B V where
  app F :=
    { app U := AddCommGrpCat.ofHom (nestedSupportSectionsInclusion h (V ⊓ U.unop) F)
      naturality _ _ _ := by ext s; rfl }
  naturality _ _ _ := by ext U s; rfl

/-- Actual restriction to the locally closed difference. -/
def nestedSupportedPresheafRestriction (A B : Closeds X) (V : Opens X) :
    gammaIntersectionPresheafFunctor B V ⟶
      gammaIntersectionPresheafFunctor B (V ⊓ A.compl) where
  app F :=
    { app U := AddCommGrpCat.ofHom (gammaZSectionsRestriction F B
        (homOfLE (inf_le_inf_right U.unop inf_le_left)))
      naturality _ _ _ := by
        ext s
        apply Subtype.ext
        change F.presheaf.map _ (F.presheaf.map _ s.val) =
          F.presheaf.map _ (F.presheaf.map _ s.val)
        rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
          ← Functor.map_comp, ← Functor.map_comp]
        rfl }
  naturality _ _ f := by
    ext U s
    apply Subtype.ext
    exact (f.hom.naturality_apply _ s.val).symm

private theorem nestedSections_exact_reindex {A B : Closeds X} (h : A ≤ B)
    (V D : Opens X) (hD : D ≤ V) (heq : D = V ⊓ A.compl)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Function.Exact (nestedSupportSectionsInclusion h V F)
      (gammaZSectionsRestriction F B (homOfLE hD)) := by
  subst D
  exact nestedSupportSections_exact h V F

private theorem nestedSections_surjective_reindex {A B : Closeds X} (h : A ≤ B)
    (V D : Opens X) (hD : D ≤ V) (heq : D = V ⊓ A.compl)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    Function.Surjective (gammaZSectionsRestriction F B (homOfLE hD)) := by
  subst D
  exact nestedSupportSectionsRestriction_surjective h V F

/-- Exactness holds on every actual ambient open. -/
theorem nestedSupportedPresheaf_exact_app {A B : Closeds X} (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (U : (Opens X)ᵒᵖ) :
    Function.Exact (((nestedSupportedPresheafInclusion h V).app F).app U)
      (((nestedSupportedPresheafRestriction A B V).app F).app U) :=
  nestedSections_exact_reindex h (V ⊓ U.unop) ((V ⊓ A.compl) ⊓ U.unop)
    (inf_le_inf_right U.unop inf_le_left) (inf_right_comm _ _ _) F

/-- The composite is zero on the original supported sections. -/
theorem nestedSupportedPresheaf_comp {A B : Closeds X} (h : A ≤ B) (V : Opens X) :
    nestedSupportedPresheafInclusion h V ≫ nestedSupportedPresheafRestriction A B V = 0 := by
  ext F U s
  exact (nestedSupportedPresheaf_exact_app h V F U _).mpr ⟨s, rfl⟩

/-- The actual presheaf short complex, natural in coefficients. -/
def nestedSupportedPresheafSequence {A B : Closeds X} (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.mk ((nestedSupportedPresheafInclusion h V).app F)
    ((nestedSupportedPresheafRestriction A B V).app F)
    (congrArg (fun α => α.app F) (nestedSupportedPresheaf_comp h V))

/-- Exactness of the actual supported-section presheaf sequence. -/
theorem nestedSupportedPresheafSequence_exact {A B : Closeds X} (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) : (nestedSupportedPresheafSequence h V F).Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply Functor.isZero
  intro U
  have hx := (ShortComplex.ab_exact_iff_function_exact
    ((nestedSupportedPresheafSequence h V F).map
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U))).mpr
        (nestedSupportedPresheaf_exact_app h V F U)
  exact ((ShortComplex.exact_iff_isZero_homology _).mp hx).of_iso
    ((nestedSupportedPresheafSequence h V F).mapHomologyIso
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U)).symm

/-- No distinct supported sections are identified by increasing support. -/
instance nestedSupportedPresheafInclusion_mono {A B : Closeds X} (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) : Mono ((nestedSupportedPresheafInclusion h V).app F) := by
  have : ∀ U, Mono (((nestedSupportedPresheafInclusion h V).app F).app U) := fun U =>
    (AddCommGrpCat.mono_iff_injective _).mpr
      (nestedSupportSectionsInclusion_injective h (V ⊓ U.unop) F)
  exact NatTrans.mono_of_mono_app _

/-- Flasqueness gives sectionwise, hence presheaf, surjectivity. -/
theorem nestedSupportedPresheafRestriction_epi {A B : Closeds X} (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    Epi ((nestedSupportedPresheafRestriction A B V).app F) := by
  have : ∀ U, Epi (((nestedSupportedPresheafRestriction A B V).app F).app U) := fun U =>
    (AddCommGrpCat.epi_iff_surjective _).mpr
      (nestedSections_surjective_reindex h (V ⊓ U.unop) ((V ⊓ A.compl) ⊓ U.unop)
        (inf_le_inf_right U.unop inf_le_left) (inf_right_comm _ _ _) F)
  exact NatTrans.epi_of_epi_app _

/-- The genuine nested presheaf sequence is short exact on flasque coefficients. -/
theorem nestedSupportedPresheafSequence_shortExact {A B : Closeds X} (h : A ≤ B)
    (V : Opens X) (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    (nestedSupportedPresheafSequence h V F).ShortExact where
  exact := nestedSupportedPresheafSequence_exact h V F
  mono_f := inferInstanceAs (Mono ((nestedSupportedPresheafInclusion h V).app F))
  epi_g := nestedSupportedPresheafRestriction_epi h V F

end SGA.SGA2.ExposeI
