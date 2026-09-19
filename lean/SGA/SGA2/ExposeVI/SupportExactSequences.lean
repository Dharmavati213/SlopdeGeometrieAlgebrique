/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedHom
import SGA.SGA2.ExposeI.NestedSupportCohomology
import SGA.SGA2.ExposeI.RelativeCohomologySequence

/-!
# SGA 2, VI.1.7–VI.1.9: nested-support exact sequences of Hom

The nested integer-support sequence of Exposé I, applied to the sheaf of
local linear maps, gives the long exact sequence of VI.1.8. The closed/open
case VI.1.9 is the relative sequence of I.2.9 on the same Hom sheaf.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- **VI.1.8, exactness at the middle:** the nested-support sequence of the
Hom sheaf is exact in every degree. -/
theorem VI_1_8_exact_middle {A B : Closeds X} (h : A ≤ B)
    (F G : SheafOfModules.{u} R) (n : ℕ) :
    Function.Exact
      (ExposeI.nestedSupportCohomologyMap h ⊤
        (moduleSheafHomAb (Opens.grothendieckTopology X) F G) n)
      (ExposeI.nestedSupportCohomologyRestriction A B ⊤
        (moduleSheafHomAb (Opens.grothendieckTopology X) F G) n) :=
  ExposeI.nestedSupportCohomology_exact_middle h ⊤
    (moduleSheafHomAb (Opens.grothendieckTopology X) F G) n

/-- **VI.1.8, exactness at the difference.** -/
theorem VI_1_8_exact_difference {A B : Closeds X} (h : A ≤ B)
    (F G : SheafOfModules.{u} R) (n : ℕ) :
    Function.Exact
      (ExposeI.nestedSupportCohomologyRestriction A B ⊤
        (moduleSheafHomAb (Opens.grothendieckTopology X) F G) n)
      (ExposeI.nestedSupportCohomologyBoundary h ⊤
        (moduleSheafHomAb (Opens.grothendieckTopology X) F G) n) :=
  ExposeI.nestedSupportCohomology_exact_difference h ⊤
    (moduleSheafHomAb (Opens.grothendieckTopology X) F G) n

/-- **VI.1.8, exactness at the next closed-in-middle group.** -/
theorem VI_1_8_exact_left {A B : Closeds X} (h : A ≤ B)
    (F G : SheafOfModules.{u} R) (n : ℕ) :
    Function.Exact
      (ExposeI.nestedSupportCohomologyBoundary h ⊤
        (moduleSheafHomAb (Opens.grothendieckTopology X) F G) n)
      (ExposeI.nestedSupportCohomologyMap h ⊤
        (moduleSheafHomAb (Opens.grothendieckTopology X) F G) (n + 1)) :=
  ExposeI.nestedSupportCohomology_exact_left h ⊤
    (moduleSheafHomAb (Opens.grothendieckTopology X) F G) n

/-- **VI.1.9:** the closed/open relative sequence of the Hom sheaf. -/
theorem VI_1_9_exact (Z : Closeds X) (F G : SheafOfModules.{u} R) (n : ℕ) :
    (ExposeI.relativeCohomologySequence Z
      (moduleSheafHomAb (Opens.grothendieckTopology X) F G) n).Exact :=
  ExposeI.relativeCohomologySequence_exact Z
    (moduleSheafHomAb (Opens.grothendieckTopology X) F G) n

/-- Degree zero of VI.1.8 starts injectively. -/
theorem VI_1_8_zero_injective {A B : Closeds X} (h : A ≤ B)
    (F G : SheafOfModules.{u} R) :
    Function.Injective
      (ExposeI.nestedSupportCohomologyMap h ⊤
        (moduleSheafHomAb (Opens.grothendieckTopology X) F G) 0) :=
  ExposeI.nestedSupportCohomologyMap_zero_injective h ⊤
    (moduleSheafHomAb (Opens.grothendieckTopology X) F G)

end SGA.SGA2.ExposeVI
