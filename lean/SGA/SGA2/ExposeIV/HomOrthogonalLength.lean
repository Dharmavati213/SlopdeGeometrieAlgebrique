/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedHomOrthogonality

/-!
# SGA 2, IV §5: length and colength of actual orthogonals

The already proved orthogonal order anti-isomorphism identifies the actual
submodule and quotient intervals. Module length is the height of the actual
submodule lattice, so this gives both source identities directly. The result
also holds for infinite lengths, without an extra Artinian hypothesis.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

/-- An actual submodule order anti-isomorphism exchanges length and colength. -/
theorem submodule_length_eq_quotient_length_of_orderAntiIso
    {M D : Type u} [AddCommGroup M] [AddCommGroup D] [Module R M] [Module R D]
    (e : Submodule R M ≃o (Submodule R D)ᵒᵈ) (N : Submodule R M) :
    Module.length R N = Module.length R (D ⧸ OrderDual.ofDual (e N)) := by
  rw [Module.length_submodule, Module.length_quotient]
  exact (Order.height_orderIso e N).symm

/-- The other interval gives quotient length equal to the orthogonal length. -/
theorem quotient_length_eq_submodule_length_of_orderAntiIso
    {M D : Type u} [AddCommGroup M] [AddCommGroup D] [Module R M] [Module R D]
    (e : Submodule R M ≃o (Submodule R D)ᵒᵈ) (N : Submodule R M) :
    Module.length R (M ⧸ N) =
      Module.length R (OrderDual.ofDual (e N) : Submodule R D) := by
  rw [Module.length_quotient, Module.length_submodule]
  exact (Order.coheight_orderIso e N).symm

/-- **IV §5:** length of an actual submodule equals colength of its original
Hom orthogonal. No replacement annihilator or alternative dual is used. -/
theorem homOrthogonal_length_eq_colength (J : Ideal R) (H : ModuleCat.{u} R)
    (hfin : FiniteSupportedHomValues J H) (hbid : SupportedModuleBiduality J H)
    (M : ModuleCat.{u} R) [Module.Finite R M] (hSupp : supportedModuleProperty J M)
    (N : Submodule R M) :
    Module.length R N =
      Module.length R (((moduleHomDual H).obj (op M)) ⧸ homOrthogonal H M N) :=
  submodule_length_eq_quotient_length_of_orderAntiIso
    (supportedHomOrthogonalOrderIso J H hfin hbid M hSupp) N

/-- **IV §5:** colength of an actual submodule equals length of its original
Hom orthogonal. -/
theorem homOrthogonal_colength_eq_length (J : Ideal R) (H : ModuleCat.{u} R)
    (hfin : FiniteSupportedHomValues J H) (hbid : SupportedModuleBiduality J H)
    (M : ModuleCat.{u} R) [Module.Finite R M] (hSupp : supportedModuleProperty J M)
    (N : Submodule R M) :
    Module.length R (M ⧸ N) = Module.length R (homOrthogonal H M N) :=
  quotient_length_eq_submodule_length_of_orderAntiIso
    (supportedHomOrthogonalOrderIso J H hfin hbid M hSupp) N

variable [IsNoetherianRing R]
variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- **IV §5 for the original functor:** length of `N` is colength of its
actual canonical-evaluation orthogonal in the original value `T(M)`. -/
theorem supportedFunctorOrthogonal_length_eq_colength
    (h : SupportedFunctorDuality J T) (M : SupportedFGModuleCat J)
    (N : Submodule R M.obj) :
    Module.length R N = Module.length R
      ((supportedFunctorValue J T M) ⧸
        OrderDual.ofDual (supportedFunctorOrthogonalOrderIso J T h M N)) :=
  submodule_length_eq_quotient_length_of_orderAntiIso
    (supportedFunctorOrthogonalOrderIso J T h M) N

/-- **IV §5 for the original functor:** colength of `N` is length of its
actual orthogonal in the unchanged original functor value. -/
theorem supportedFunctorOrthogonal_colength_eq_length
    (h : SupportedFunctorDuality J T) (M : SupportedFGModuleCat J)
    (N : Submodule R M.obj) :
    Module.length R (M.obj ⧸ N) =
      Module.length R (OrderDual.ofDual (supportedFunctorOrthogonalOrderIso J T h M N) :
        Submodule R (supportedFunctorValue J T M)) :=
  quotient_length_eq_submodule_length_of_orderAntiIso
    (supportedFunctorOrthogonalOrderIso J T h M) N

end SGA.SGA2.ExposeIV
