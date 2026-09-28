/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.DerivedSupportedSheafOne
import SGA.SGA2.ExposeI.SupportedSheafDimensionShift

/-!
# Comparison with the existing supported-cohomology sheaf model

The original right-derived kernel-sheaf functor is naturally isomorphic to
the existing `sheafH_Z_n` model in every degree. Neither the original kernel
nor the model is redefined. This transfers the sheafification theorem and
flasque acyclicity to the existing model.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Cokernels of the original complement units, with the actual induced maps. -/
def complementPushforwardCokernelFunctor (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X where
  obj F := cokernel (toComplementPushforward F Z)
  map {F G} f := cokernel.map (toComplementPushforward F Z) (toComplementPushforward G Z)
    f ((complementPushforwardFunctor Z).map f)
    ((complementPushforwardUnit Z).naturality f).symm
  map_id F := by
    apply (cancel_epi (cokernel.π (toComplementPushforward F Z))).mp
    simp only [CategoryTheory.Functor.map_id, cokernel.π_desc, Category.comp_id]
    exact Category.id_comp _
  map_comp {F G H} f g := by
    apply (cancel_epi (cokernel.π (toComplementPushforward F Z))).mp
    simp [Functor.map_comp, Category.assoc]

/-- The existing kernel/cokernel/derived-pushforward model, now functorial
in the coefficient sheaf using its actual maps. -/
def sheafH_ZFunctor (Z : Closeds X) : ℕ →
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X
  | 0 => underlineGammaZFunctor Z
  | 1 => complementPushforwardCokernelFunctor Z
  | n + 2 => Sheaf.pullback AddCommGrpCat.{u} (complementInclusion Z) ⋙
      (Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)).rightDerived (n + 1)

/-- The functorial packaging has precisely the pre-existing objects. -/
theorem sheafH_ZFunctor_obj (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (sheafH_ZFunctor Z n).obj F = sheafH_Z_n Z F n := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

/-- **I.2.11:** the original derived supported sheaves and the existing model
are naturally isomorphic in all degrees. -/
def derivedUnderlineGammaZIsoModel (Z : Closeds X) : ∀ n : ℕ,
    derivedUnderlineGammaZ Z n ≅ sheafH_ZFunctor Z n
  | 0 => derivedUnderlineGammaZZeroIso Z
  | 1 => NatIso.ofComponents (fun F ↦ derivedSupportedSheafOneObjIso Z F)
      (fun f ↦ derivedSupportedSheafOneObjIso_hom_naturality Z f)
  | n + 2 => derivedSupportedSheafHigherIso Z n

/-- Objectwise comparison with the unchanged `sheafH_Z_n`. -/
def derivedUnderlineGammaZObjIsoModel (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (derivedUnderlineGammaZ Z n).obj F ≅ sheafH_Z_n Z F n :=
  (derivedUnderlineGammaZIsoModel Z n).app F ≪≫ eqToIso (sheafH_ZFunctor_obj Z F n)

/-- **I.2.4 / I.2.11:** the existing model is naturally the sheafification
of the actual local supported-cohomology presheaf. -/
def sheafH_ZFunctorSheafificationIso (Z : Closeds X) (n : ℕ) :
    supportedCohomologyPresheafFunctor Z n ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
        sheafH_ZFunctor Z n :=
  supportedCohomologySheafificationIso Z n ≪≫ derivedUnderlineGammaZIsoModel Z n

/-- The sheafification comparison stated with the original model objects. -/
def sheafH_Z_nSheafificationIso (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        ((supportedCohomologyPresheafFunctor Z n).obj F) ≅ sheafH_Z_n Z F n :=
  (sheafH_ZFunctorSheafificationIso Z n).app F ≪≫ eqToIso (sheafH_ZFunctor_obj Z F n)

/-- **I.2.12, closed support:** the unchanged model vanishes in every positive
degree on flasque sheaves, by its proved original-derived comparison. -/
theorem sheafH_Z_n_isZero_of_isFlasque (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (n : ℕ) :
    IsZero (sheafH_Z_n Z F (n + 1)) :=
  (derivedUnderlineGammaZ_isZero_of_isFlasque Z F n).of_iso
    (derivedUnderlineGammaZObjIsoModel Z F (n + 1)).symm

/-- Injective coefficients are acyclic also for the unchanged model. -/
theorem sheafH_Z_n_isZero_of_injective (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] (n : ℕ) :
    IsZero (sheafH_Z_n Z F (n + 1)) :=
  (derivedUnderlineGammaZ_isZero_of_injective Z F n).of_iso
    (derivedUnderlineGammaZObjIsoModel Z F (n + 1)).symm

end SGA.SGA2.ExposeI
