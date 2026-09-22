/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleLocallyClosedSupportSpectralSequence
import SGA.SGA2.ExposeVI.ModuleEndofunctorSpectralAbutmentNaturality

/-!
# SGA 2, VI.1.6.3: original locally closed E₂ and abutment coefficient maps

The actual spectral maps induce the original module Ext maps of derived
locally supported coefficients on E₂, and the original locally supported
Ext maps on the total. Both statements use the unchanged comparison maps.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (W : ExposeI.LocallyClosedIn X)
  (F : SheafOfModules.{u} R) {G H : SheafOfModules.{u} R}
  {I : InjectiveResolution G} {J : InjectiveResolution H}

-- Keep the proved generic comparisons opaque while specializing their original maps.
attribute [local irreducible] moduleEndofunctorSpectralSequence
  moduleEndofunctorSpectralSequenceMap moduleEndofunctorSpectralSequenceE2Equiv
  moduleEndofunctorSpectralComparedAbutmentEquiv

/-- The actual locally closed E₂ morphism is Ext of the original derived Γ_W map. -/
theorem moduleLocallyClosedSupportSpectralSequenceE2Equiv_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p q : ℕ)
    (x : ((moduleLocallyClosedSupportSpectralSequence R W F I).page 2).X ((p : ℤ), (q : ℤ))) :
    moduleLocallyClosedSupportSpectralSequenceE2Equiv R W F J p q
        (((moduleLocallyClosedSupportSpectralSequenceMap R W F α).hom 2).f
          ((p : ℤ), (q : ℤ)) x) =
      (Abelian.extFunctorObj F p).map ((derivedModuleGammaLocallyClosedSheaf R W q).map a)
        (moduleLocallyClosedSupportSpectralSequenceE2Equiv R W F I p q x) :=
  moduleEndofunctorSpectralSequenceE2Equiv_naturality R
    (moduleGammaLocallyClosedSheafFunctor R W) F (I := I) (J := J) a α hα p q x

/-- The actual total-interval map, including its action on the canonical finite filtration. -/
abbrev moduleLocallyClosedSupportSpectralTotalMap (α : I.cocomplex ⟶ J.cocomplex) (n : ℤ) :=
  moduleEndofunctorSpectralTotalMap R (moduleGammaLocallyClosedSheafFunctor R W) F α n

/-- The unchanged abutment comparison carries the total map to original supported Ext. -/
theorem moduleLocallyClosedSupportSpectralAbutmentEquiv_naturality
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (n : ℕ)
    (x : moduleLocallyClosedSupportSpectralTotal R W F I n) :
    moduleLocallyClosedSupportSpectralAbutmentEquiv R W F J n
        (moduleLocallyClosedSupportSpectralTotalMap R W F α n x) =
      (moduleLocallyClosedSupportedExtFunctor R F W n).map a
        (moduleLocallyClosedSupportSpectralAbutmentEquiv R W F I n x) :=
  moduleEndofunctorSpectralComparedAbutmentEquiv_naturality R
    (moduleGammaLocallyClosedSheafFunctor R W) F
    (moduleLocallyClosedSupportedExtFunctor R F W n) n
    (moduleLocallyClosedSupportedExtViaSupportedSheafIso R F W n).symm
    (I := I) (J := J) a α hα x

end SGA.SGA2.ExposeVI
