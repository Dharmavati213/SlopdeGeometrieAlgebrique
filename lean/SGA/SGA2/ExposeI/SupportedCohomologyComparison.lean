/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.ClosedSupportHom
import SGA.SGA2.ExposeI.FlasqueResolution
import SGA.SGA2.ExposeI.ExtRightDerived

/-!
# Supported cohomology as the right-derived supported-section functor

The closed-support Hom representation identifies actual supported sections
with the preadditive coyoneda functor of the actual object `zZX_closed Z`.
Deriving that natural isomorphism and comparing derived Hom with Ext identifies
the original right-derived section functors with the existing Ext-defined
`H_Z`. In particular flasque and injective sheaves have zero positive-degree
`H_Z`, with no comparison or acyclicity assumption.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- The additive closed-support Hom comparison as an isomorphism of coefficient
functors. This uses the actual closed pushforward `zZX_closed Z`. -/
def closedSupportHomFunctorIso (Z : Closeds X) :
    preadditiveCoyoneda.obj (op (zZX_closed Z)) ≅ gammaZSectionsFunctor Z ⊤ :=
  NatIso.ofComponents (fun F => (closedSupportHomEquiv Z F).toAddCommGrpIso)
    (fun f => by
      ext φ
      exact closedSupportHomEquiv_naturality Z f φ)

/-- **SGA 2, I.2.1 / I.2.3 bis:** actual right-derived supported sections
are naturally the existing Ext-defined supported cohomology functor. -/
def derivedGammaZSectionsIsoH_Z (Z : Closeds X) (n : ℕ) :
    derivedGammaZSections Z ⊤ n ≅ extFunctorObj (zZX_closed Z) n :=
  (rightDerivedFunctorIso (closedSupportHomFunctorIso Z) n).symm ≪≫
    rightDerivedCoyonedaNatIsoExt (zZX_closed Z) n

/-- The supported cohomology comparison on an individual coefficient sheaf. -/
def derivedGammaZSectionsObjIsoH_Z (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (derivedGammaZSections Z ⊤ n).obj F ≅ AddCommGrpCat.of (H_Z Z F n) :=
  (derivedGammaZSectionsIsoH_Z Z n).app F

/-- Naturality of the comparison against the preexisting maps on `H_Z`. -/
theorem derivedGammaZSectionsObjIsoH_Z_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ) :
    (derivedGammaZSections Z ⊤ n).map f ≫ (derivedGammaZSectionsObjIsoH_Z Z G n).hom =
      (derivedGammaZSectionsObjIsoH_Z Z F n).hom ≫ AddCommGrpCat.ofHom (H_Z_map Z f n) :=
  (derivedGammaZSectionsIsoH_Z Z n).hom.naturality f

/-- Degree zero of the existing supported cohomology is actual supported sections. -/
def H_Z_zero_gammaZ_addEquiv (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    H_Z Z F 0 ≃+ gammaZ F Z :=
  (H_Z_zero_addEquiv Z F).trans (closedSupportHomEquiv Z F)

/-- Flasque sheaves are acyclic for the original Ext-defined supported cohomology. -/
theorem H_Z_pos_isZero_of_isFlasque (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (n : ℕ) :
    IsZero (AddCommGrpCat.of (H_Z Z F (n + 1))) :=
  IsZero.of_iso (derivedGammaZSections_isZero_of_isFlasque Z ⊤ F n)
    (derivedGammaZSectionsObjIsoH_Z Z F (n + 1)).symm

/-- Elementwise vanishing for supported cohomology of flasque sheaves. -/
theorem H_Z_pos_subsingleton_of_isFlasque (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (n : ℕ) :
    Subsingleton (H_Z Z F (n + 1)) :=
  AddCommGrpCat.isZero_iff_subsingleton.mp (H_Z_pos_isZero_of_isFlasque Z F n)

/-- Injective sheaves have zero positive-degree Ext-defined supported cohomology. -/
theorem H_Z_pos_isZero_of_injective (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] (n : ℕ) :
    IsZero (AddCommGrpCat.of (H_Z Z F (n + 1))) :=
  IsZero.of_iso (derivedGammaZSections_isZero_of_injective Z ⊤ F n)
    (derivedGammaZSectionsObjIsoH_Z Z F (n + 1)).symm

/-- Flasque sheaves have zero positive supported cohomology after restriction
to any open, for every closed support in that open. -/
theorem H_Z_pos_restrict_subsingleton_of_isFlasque
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (U : Opens X)
    (Z : Closeds ((Opens.toTopCat X).obj U)) (n : ℕ) :
    Subsingleton (H_Z Z (restrictToOpen F U) (n + 1)) := by
  have : IsFlasque (restrictToOpen F U) :=
    isFlasque_pullback_of_isOpenEmbedding U.isOpenEmbedding F
  exact H_Z_pos_subsingleton_of_isFlasque Z _ n

end SGA.SGA2.ExposeI
