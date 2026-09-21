/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.DerivedSupportedSheafOne

/-!
# Naturality of the canonical degree-zero derived comparison

For a natural transformation of additive left-exact functors, the actual
zeroth derived map becomes the original map under the canonical comparison.
-/

noncomputable section

open CategoryTheory Limits

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

/-- The degree-zero comparison is natural in the additive left-exact functor. -/
@[reassoc]
theorem toRightDerivedZero_natTrans
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasInjectiveResolutions C] {P Q : C ⥤ D} [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteLimits Q] (α : P ⟶ Q) (F : C) :
    P.toRightDerivedZero.app F ≫ (α.rightDerived 0).app F =
      α.app F ≫ Q.toRightDerivedZero.app F := by
  let I := injectiveResolution F
  have hP : P.toRightDerivedZero.app F =
      (resolutionZeroHomologyIso P I).hom ≫ (I.isoRightDerivedObj P 0).inv := by
    simpa only [resolutionZeroHomologyIso, Iso.trans_hom, asIso_hom, Category.assoc]
      using I.toRightDerivedZero_eq P
  have hQ : Q.toRightDerivedZero.app F =
      (resolutionZeroHomologyIso Q I).hom ≫ (I.isoRightDerivedObj Q 0).inv := by
    simpa only [resolutionZeroHomologyIso, Iso.trans_hom, asIso_hom, Category.assoc]
      using I.toRightDerivedZero_eq Q
  rw [hP, hQ, I.rightDerived_app_eq α 0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (resolutionZeroHomologyIso_hom_natTrans_assoc α I _).symm

/-- The original degree-zero isomorphism preserves every functor map. -/
@[reassoc]
theorem rightDerivedZeroIsoSelf_natTrans
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasInjectiveResolutions C] {P Q : C ⥤ D} [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteLimits Q] (α : P ⟶ Q) (F : C) :
    (α.rightDerived 0).app F ≫ Q.rightDerivedZeroIsoSelf.hom.app F =
      P.rightDerivedZeroIsoSelf.hom.app F ≫ α.app F := by
  apply (cancel_epi (P.toRightDerivedZero.app F)).mp
  rw [← Category.assoc, toRightDerivedZero_natTrans α F]
  simp only [Category.assoc, Functor.rightDerivedZeroIsoSelf_inv_hom_id_app,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id_app_assoc, Category.comp_id]

end SGA.SGA2.ExposeI
