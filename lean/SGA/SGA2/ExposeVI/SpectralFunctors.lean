/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedExt
import SGA.SGA2.ExposeVI.ModuleHomInjectiveFlasque
import SGA.SGA2.ExposeI.OpenInclusionLeray
import SGA.SGA2.ExposeI.LocalToGlobalE2

/-!
# SGA 2, VI.1.6: three spectral functors abutting to supported Ext

The initial terms are supported cohomology of sheaf Ext, ordinary cohomology
of supported sheaf Ext, and Ext against derived supported coefficients.
On injective coefficients the first page degenerates in positive Hom-degree
by VI.1.5, and the abutment is the original supported Ext.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- **VI.1.6.1 initial term:** supported cohomology of sheaf Ext. -/
abbrev VI_1_6_1_E2 (F G : SheafOfModules.{u} R) (Z : Closeds X) (p q : ℕ) :=
  ExposeI.H_Z Z ((moduleSheafExtAbFunctor R F q).obj G) p

/-- **VI.1.6.2 initial term:** ordinary cohomology of supported sheaf Ext. -/
abbrev VI_1_6_2_E2 (F G : SheafOfModules.{u} R) (W : ExposeI.LocallyClosedIn X)
    (p q : ℕ) :=
  ExposeI.H ((moduleLocallyClosedSheafExtFunctor R F W q).obj G) p

/-- **VI.1.6 abutment:** the original supported Ext groups. -/
abbrev VI_1_6_abutment (F G : SheafOfModules.{u} R) (Z : Closeds X) (n : ℕ) :=
  (moduleSupportedExtFunctor R F Z n).obj G

/-- The Hom sheaf of an injective is flasque, hence acyclic for supported
sections: VI.1.6.1 in Hom-degree zero is the abutment in every degree. -/
theorem VI_1_6_1_deg0_isZero_succ_of_injective (F G : SheafOfModules.{u} R)
    [Injective G] (Z : Closeds X) (p : ℕ) :
    IsZero ((moduleSupportedExtFunctor R F Z (p + 1)).obj G) :=
  moduleSupportedExt_isZero_of_injective R F G Z p

/-- **VI.1.6.2 as a Grothendieck sequence:** local-to-global for the
supported Hom sheaf is the truncation sequence of I.2.6, applied after
the Hom functor. Its E₂ terms in degree zero of the support functor are
ordinary cohomology of the Hom sheaf. -/
def VI_1_6_2_grothendieck (Z : Closeds X)
    {G : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution G) :
    E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  ExposeI.grothendieckSpectralSequenceOfSupportedSheaf Z I

end SGA.SGA2.ExposeVI
