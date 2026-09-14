/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalSpectralObject
import SGA.SGA2.ExposeI.HomologicalSpectralObject
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# The actual spectral sequence attached to the supported truncation object

We apply the genuine derived-category Hom functor from the constant integer
sheaf to the supported truncation spectral object, using the proved
homological-functor bridge. Mathlib's spectral-object construction then gives
all pages, all differentials, and the homology-to-next-page isomorphisms.

The companion `LocalToGlobalE2` identifies its actual E₂ terms with ordinary
cohomology of `derivedUnderlineGammaZ`. `LocalToGlobalConvergence` proves a
finite abutment filtration and convergence to original `H_Z`. These comparisons
handle the size change from the explicitly constructed standard derived category.
The full functorial statement I.2.6 still requires E₂ comparison naturality and
compatibility of coefficient maps with all pages and next-page homology.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

local instance supportedGlobalHom_hasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

/-- Actual derived-category Hom from the original constant integer sheaf.
The shifts of this functor are the cohomological Hom functors. -/
def supportedDerivedGlobalHom :
    DerivedCategory (Sheaf AddCommGrpCat.{u} X) ⥤ AddCommGrpCat.{u + 1} :=
  preadditiveCoyoneda.obj
    (op ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X)))

instance supportedDerivedGlobalHom_isHomological :
    (supportedDerivedGlobalHom (X := X)).IsHomological := by
  dsimp [supportedDerivedGlobalHom]
  infer_instance

instance supportedDerivedGlobalHom_shiftSequence :
    (supportedDerivedGlobalHom (X := X)).ShiftSequence ℤ := by
  dsimp [supportedDerivedGlobalHom]
  infer_instance

/-- The actual abelian spectral object obtained from the supported canonical
truncations by cohomological derived Hom from the constant integer sheaf. -/
def supportedLocalToGlobalAbelianSpectralObject (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    Abelian.SpectralObject AddCommGrpCat.{u + 1} EInt :=
  homologicalSpectralObject (supportedLocalToGlobalTriangulatedSpectralObject Z I)
    supportedDerivedGlobalHom

/-- The genuine spectral sequence of supported canonical truncations and
derived Hom, including all differentials and all successive homology
isomorphisms. E₂ and convergence comparisons are proved in the companion files. -/
def supportedTruncationSpectralSequence (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  (supportedLocalToGlobalAbelianSpectralObject Z I).E₂SpectralSequence

end SGA.SGA2.ExposeI
