/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalSpectralSequence
import SGA.SGA2.ExposeI.DerivedTruncationHomology
import Mathlib.Algebra.Homology.SpectralObject.FirstPage

/-!
# The actual E₂ terms of the supported truncation spectral sequence

The canonical single-degree truncation is identified with the single complex
of the original derived supported sheaf. Derived-category Hom from the
constant integer sheaf then identifies its actual E₂ groups with the existing
ordinary sheaf cohomology groups, including the universe-size comparison.
No E₂ identification or convergence data is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex
open ComposableArrows

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

local instance supportedE2_hasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

/-- The large-universe derived Hom from the constant sheaf is the existing
small-universe ordinary sheaf cohomology when evaluated on a sheaf. -/
def supportedDerivedGlobalHomSingleEquiv (G : Sheaf AddCommGrpCat.{u} X) (p : ℕ) :
    ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X) ⟶
      ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj G)⟦(p : ℤ)⟧) ≃+
        H G p :=
  (Abelian.Ext.homAddEquiv (X := constantZ X) (Y := G) (n := p)).symm

/-- The single-degree interval in the actual supported truncation spectral
object is the single complex of the original derived supported sheaf. -/
def supportedE2TruncationIso (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (q : ℕ) :
    (supportedLocalToGlobalTriangulatedSpectralObject Z I).ω₁.obj
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) by
          exact WithBotTop.coe_le_coe.mpr (by lia)))) ≅
      (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).obj
        ((derivedUnderlineGammaZ Z q).obj F) :=
  derivedSingleDegreeTruncationIsoSingle (supportedDerivedObject Z I) (q : ℤ) ≪≫
    (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).mapIso
      (supportedDerivedObjectHomologyIso Z I q)

/-- Shifting a sheaf in degree `q` by `p + q` gives its degree-zero single
complex shifted by `p`. -/
def supportedSingleTotalShiftIso (G : Sheaf AddCommGrpCat.{u} X) (p q : ℤ) :
    ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) q).obj G)⟦p + q⟧ ≅
      ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj G)⟦p⟧ :=
  ((DerivedCategory.singleFunctors (Sheaf AddCommGrpCat.{u} X)).shiftIso
    (p + q) (-p) q (by lia)).app G ≪≫
    (((DerivedCategory.singleFunctors (Sheaf AddCommGrpCat.{u} X)).shiftIso
      p (-p) 0 (by lia)).app G).symm

/-- The shifted truncation isomorphism used in the E₂ comparison. -/
def supportedE2TotalShiftIso (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (p q : ℕ) :=
  (shiftFunctor (DerivedCategory (Sheaf AddCommGrpCat.{u} X))
    ((p : ℤ) + (q : ℤ))).mapIso (supportedE2TruncationIso Z I q) ≪≫
      supportedSingleTotalShiftIso ((derivedUnderlineGammaZ Z q).obj F) (p : ℤ) (q : ℤ)

/-- The canonical first-page interval isomorphism used in the E₂ comparison. -/
def supportedE2FirstPageIso (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (p q : ℕ) :=
  (supportedLocalToGlobalAbelianSpectralObject Z I).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂Cohomological ((p : ℤ), (q : ℤ))
    (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl

/-- The actual E₂ term is actual ordinary cohomology of the original derived
supported sheaf. This identifies terms of the already constructed spectral
sequence, rather than defining a replacement E₂ page. -/
def supportedTruncationSpectralSequenceE2Equiv (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (p q : ℕ) :
    ((supportedTruncationSpectralSequence Z I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      H ((derivedUnderlineGammaZ Z q).obj F) p := by
  let eHom := (preadditiveCoyoneda.obj
    (op ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj
      (constantZ X)))).mapIso (supportedE2TotalShiftIso Z I p q)
  exact (supportedE2FirstPageIso Z I p q).addCommGroupIsoToAddEquiv.trans
    (eHom.addCommGroupIsoToAddEquiv.trans
      (supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaZ Z q).obj F) p))

end SGA.SGA2.ExposeI
