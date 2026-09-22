/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.SheafFunctorSpectralNaturality
import SGA.SGA2.ExposeI.LocallyClosedCohomology

/-!
# Ambient locally closed E₂ comparison and its original coefficient maps

This composes the actual closed-support E₂ comparison on an open witness
with the original locally closed Ext adjunction. Naturality is proved before
specializing the coefficient functors, so concrete internal-Hom constructions
remain opaque during elaboration.
-/

noncomputable section

universe u v w

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} {C : Type v} [Category.{w} C] [Abelian C]
  [HasInjectiveResolutions C] (W : ExposeI.LocallyClosedIn X)
  (T : C ⥤ Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj W.V)) [T.Additive]
  (S : C ⥤ Sheaf AddCommGrpCat.{u} X) (q : ℕ)
  (e : T.rightDerived q ≅ S ⋙ ExposeI.iShriek_open W.V)

/-- The actual E₂ page identifies with original ambient locally supported cohomology. -/
def locallyClosedSpectralE2Equiv {G : C} (I : InjectiveResolution G) (p : ℕ) :
    ((sheafFunctorSpectralSequence T W.ZV I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      ExposeI.H_locallyClosed W (S.obj G) p :=
  (sheafFunctorSpectralSequenceE2ComparedEquiv T W.ZV
    (S ⋙ ExposeI.iShriek_open W.V) q e I p).trans
      (ExposeI.locallyClosedSupportExtEquiv W (S.obj G) p).symm

/-- Restricting the ambient comparison gives the unchanged comparison on the open witness. -/
theorem locallyClosedSpectralE2Equiv_restrict {G : C} (I : InjectiveResolution G) (p : ℕ)
    (x : ((sheafFunctorSpectralSequence T W.ZV I).page 2).X ((p : ℤ), (q : ℤ))) :
    ExposeI.locallyClosedSupportExtEquiv W (S.obj G) p
        (locallyClosedSpectralE2Equiv W T S q e I p x) =
      sheafFunctorSpectralSequenceE2ComparedEquiv T W.ZV
        (S ⋙ ExposeI.iShriek_open W.V) q e I p x :=
  (ExposeI.locallyClosedSupportExtEquiv W (S.obj G) p).apply_symm_apply _

/-- The actual ambient E₂ morphism is the original locally supported cohomology map. -/
theorem locallyClosedSpectralE2Equiv_naturality {G H : C}
    (I : InjectiveResolution G) (J : InjectiveResolution H)
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p : ℕ)
    (x : ((sheafFunctorSpectralSequence T W.ZV I).page 2).X ((p : ℤ), (q : ℤ))) :
    locallyClosedSpectralE2Equiv W T S q e J p
        (((sheafFunctorSpectralSequenceMap T W.ZV α).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      (locallyClosedSpectralE2Equiv W T S q e I p x).comp
        (Abelian.Ext.mk₀ (S.map a)) (add_zero p) := by
  apply (ExposeI.locallyClosedSupportExtEquiv W (S.obj H) p).injective
  rw [locallyClosedSpectralE2Equiv_restrict, ExposeI.locallyClosedSupportExtEquiv_naturality,
    locallyClosedSpectralE2Equiv_restrict]
  have h := sheafFunctorSpectralSequenceE2ComparedEquiv_naturality T W.ZV
    (S ⋙ ExposeI.iShriek_open W.V) q e (I := I) (J := J) a α hα p x
  simpa only [Functor.comp_map, Functor.comp_obj, ExposeI.restrictToOpen,
    ExposeI.iShriek_open] using h

end SGA.SGA2.ExposeVI
