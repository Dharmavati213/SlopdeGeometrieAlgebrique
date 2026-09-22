/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.HomComplexPrecomposition
import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-!
# V.1.3: Ext from the actual Hom complex of two injective resolutions

The source differential is normalized by the explicit degreewise sign before
passing to the ordinary Hom complex of the second resolution. This actual
augmentation is proved to be a quasi-isomorphism, and its homology map gives
the comparison with Mathlib's Ext. The degreewise formula retains the original
resolution augmentation and explicitly displays the necessary sign.
-/

noncomputable section
universe w v u
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X Y : C} (I : InjectiveResolution X) (J : InjectiveResolution Y)

/-- The ordinary complex `Hom(X, J)` with the unsigned target differential. -/
def injectiveOrdinaryHomComplex (X : C) (J : InjectiveResolution Y) :
    CochainComplex AddCommGrpCat ℤ :=
  ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex _).obj J.cochainComplex

/-- The actual augmentation from the displayed source Hom complex to the
ordinary complex `Hom(X, J)`, with the required sign normalization. -/
def sourceInjectiveHomAugmentation :
    sourceHomComplex I.cochainComplex J.cochainComplex ⟶ injectiveOrdinaryHomComplex X J :=
  sourceHomPrecomp I.ι' J.cochainComplex ≫
    (sourceHomComplexIso ((singleFunctor C 0).obj X) J.cochainComplex).hom ≫
      (ExposeI.homComplexFromSingleIso X J.cochainComplex).hom

/-- On the original graded morphisms this is precisely the resolution
augmentation, multiplied by `(-1)^(n(n+1)/2)`. -/
theorem sourceInjectiveHomAugmentation_f (n : ℤ)
    (z : Cochain I.cochainComplex J.cochainComplex n) :
    (sourceInjectiveHomAugmentation I J).f n z =
      sourceHomSign n • (I.ι.f 0 ≫ (I.cochainComplexXIso 0 0 rfl).inv ≫
        z.v 0 n (zero_add n)) := by
  change Cochain.fromSingleEquiv (zero_add n)
      (sourceHomSign n • (Cochain.ofHom I.ι').comp z (zero_add n)) = _
  simp [Cochain.fromSingleEquiv, Cochain.zero_cochain_comp_v,
    InjectiveResolution.ι'_f_zero, Category.assoc]

/-- In degree zero no sign correction is needed. -/
theorem sourceInjectiveHomAugmentation_f_zero
    (z : Cochain I.cochainComplex J.cochainComplex 0) :
    (sourceInjectiveHomAugmentation I J).f 0 z =
      I.ι.f 0 ≫ (I.cochainComplexXIso 0 0 rfl).inv ≫ z.v 0 0 (zero_add 0) := by
  simp [sourceInjectiveHomAugmentation_f]

/-- The actual sign-normalized augmentation is a quasi-isomorphism. -/
instance sourceInjectiveHomAugmentation_quasiIso :
    QuasiIso (sourceInjectiveHomAugmentation I J) := by
  dsimp [sourceInjectiveHomAugmentation]
  infer_instance

variable [HasExt.{w} C]

/-- The ordinary Hom-complex computation using the specified resolution of
the second argument and Mathlib's canonical Ext comparison. -/
def injectiveOrdinaryHomologyExtAddEquiv (X : C) (J : InjectiveResolution Y) (n : ℕ) :
    (injectiveOrdinaryHomComplex X J).homology (n : ℤ) ≃+ Abelian.Ext X Y n :=
  ((homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) (n : ℤ)).mapIso
    (ExposeI.homComplexFromSingleIso X J.cochainComplex).symm).addCommGroupIsoToAddEquiv.trans
      ((HomComplex.homologyAddEquiv ((singleFunctor C 0).obj X) J.cochainComplex n).trans
        J.extAddEquivCohomologyClass.symm)

/-- **V.1.3**, with the explicit source sign convention: the actual Hom
complex of the two given injective resolutions computes Ext. -/
def sourceInjectiveHomologyExtAddEquiv (n : ℕ) :
    (sourceHomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ) ≃+
      Abelian.Ext X Y n :=
  (asIso (homologyMap (sourceInjectiveHomAugmentation I J) (n : ℤ))).addCommGroupIsoToAddEquiv.trans
    (injectiveOrdinaryHomologyExtAddEquiv X J n)

/-- The double-resolution comparison uses the actual augmentation homology
map, not a separately chosen isomorphism between the resulting groups. -/
theorem sourceInjectiveHomologyExtAddEquiv_augmentation (n : ℕ)
    (z : (sourceHomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    sourceInjectiveHomologyExtAddEquiv I J n z =
      injectiveOrdinaryHomologyExtAddEquiv X J n
        ((homologyMap (sourceInjectiveHomAugmentation I J) (n : ℤ)) z) := rfl

/-- The standard-sign Hom complex of the same two actual resolutions also
computes Ext, through the inverse of the specified sign normalization. -/
def injectiveHomologyExtAddEquiv (n : ℕ) :
    (HomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ) ≃+
      Abelian.Ext X Y n :=
  ((homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) (n : ℤ)).mapIso
    (sourceHomComplexIso I.cochainComplex J.cochainComplex).symm).addCommGroupIsoToAddEquiv.trans
      (sourceInjectiveHomologyExtAddEquiv I J n)

/-- The source comparison is the standard comparison after sign normalization. -/
theorem sourceInjectiveHomologyExtAddEquiv_eq_normalized
    (J : InjectiveResolution Y) (I : InjectiveResolution X) (n : ℕ)
    (x : (sourceHomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    sourceInjectiveHomologyExtAddEquiv I J n x =
      injectiveHomologyExtAddEquiv I J n
        (homologyMap (sourceHomComplexIso I.cochainComplex J.cochainComplex).hom (n : ℤ) x) := by
  let e := (homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) (n : ℤ)).mapIso
    (sourceHomComplexIso I.cochainComplex J.cochainComplex)
  exact (congrArg (sourceInjectiveHomologyExtAddEquiv I J n)
    (ConcreteCategory.congr_hom e.hom_inv_id x)).symm

end SGA.SGA2.ExposeV
