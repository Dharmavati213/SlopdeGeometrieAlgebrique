/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.SupportedSheafSections
import Mathlib.Algebra.Homology.HomologySequence

/-!
# The supported-sheaf sequence on flasque coefficients

The original unit `F → j_* j^* F` is sectionwise surjective for flasque `F`.
Consequently its actual kernel gives a short exact sequence. Applying this
degreewise to an injective resolution gives the short exact sequence of
complexes used to compute the original derived supported sheaves.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Restrict to the open complement and then push forward, using the original
pullback and pushforward functors. -/
def complementPushforwardFunctor (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X :=
  Sheaf.pullback AddCommGrpCat.{u} (complementInclusion Z) ⋙
    Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)

instance (Z : Closeds X) : (complementPushforwardFunctor Z).Additive := by
  dsimp [complementPushforwardFunctor, complementInclusion]
  infer_instance

/-- The original kernel inclusion, naturally in the coefficient sheaf. -/
def supportedSheafInclusion (Z : Closeds X) : underlineGammaZFunctor Z ⟶ 𝟭 _ where
  app F := underlineGammaZ_ι F Z
  naturality _ _ φ := underlineGammaZMap_comp_ι φ Z

/-- The original complement unit, as a natural transformation. -/
def complementPushforwardUnit (Z : Closeds X) : 𝟭 _ ⟶ complementPushforwardFunctor Z :=
  (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (complementInclusion Z)).unit

/-- The original complement unit is surjective on sections for flasque
coefficients. -/
instance toComplementPushforward_app_epi_of_isFlasque (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (U : (Opens X)ᵒᵖ) :
    Epi ((toComplementPushforward F Z).hom.app U) := by
  have : Epi (restrictToComplement F Z U.unop) := by
    dsimp [restrictToComplement]
    infer_instance
  have : Epi ((toComplementPushforward F Z).hom.app U ≫
      (complementPushforwardSectionsIso F Z U.unop).hom) := by
    rw [toComplementPushforward_comp_sectionsIso]
    infer_instance
  exact (epi_comp_iff_of_isIso ((toComplementPushforward F Z).hom.app U)
    (complementPushforwardSectionsIso F Z U.unop).hom).mp this

instance toComplementPushforward_epi_of_isFlasque (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    Epi (toComplementPushforward F Z) := by
  have : Epi (toComplementPushforward F Z).hom := NatTrans.epi_of_epi_app _
  exact (sheafToPresheaf (Opens.grothendieckTopology X)
    AddCommGrpCat.{u}).epi_of_epi_map this

/-- The actual supported-sheaf sequence, without any surjectivity assumption. -/
def supportedSheafSequence (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (underlineGammaZ_ι F Z) (toComplementPushforward F Z)
    (kernel.condition _)

/-- The supported-sheaf sequence is short exact on flasque coefficients. -/
theorem supportedSheafSequence_shortExact (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    (supportedSheafSequence Z F).ShortExact where
  exact := ShortComplex.exact_kernel _
  mono_f := by dsimp [supportedSheafSequence, underlineGammaZ_ι]; infer_instance
  epi_g := by dsimp [supportedSheafSequence]; infer_instance

/-- Apply the original supported-sheaf sequence degreewise to a complex. -/
def supportedSheafComplexSequence (Z : Closeds X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ) :
    ShortComplex (CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ) :=
  ShortComplex.mk
    (((supportedSheafInclusion Z).mapHomologicalComplex (ComplexShape.up ℕ)).app K)
    (((complementPushforwardUnit Z).mapHomologicalComplex (ComplexShape.up ℕ)).app K)
    (by ext i; exact kernel.condition _)

/-- The actual supported-sheaf complex sequence of an injective resolution
is short exact. -/
theorem supportedSheafComplexSequence_shortExact (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    (supportedSheafComplexSequence Z I.cocomplex).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  have : IsFlasque (I.cocomplex.X n) := isFlasque_of_injective _
  exact supportedSheafSequence_shortExact Z (I.cocomplex.X n)

end SGA.SGA2.ExposeI
