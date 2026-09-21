/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleSheafHomSpectralPresentation
import SGA.SGA2.ExposeVI.ModuleHomInjectiveFlasque
import SGA.SGA2.ExposeVI.ModuleSupportIndependence
import SGA.SGA2.ExposeVI.SheafFunctorSpectralNaturality

/-!
# SGA 2, VI.1.6.1 for arbitrary locally closed support

Restrict the actual module Hom resolution to the open neighbourhood of the
support and apply the genuine truncation spectral construction there. Exact
restriction identifies its cohomology sheaves with the restrictions of the
original sheaf Ext. The original locally closed Ext adjunction identifies E₂
with ambient locally supported cohomology. Flasqueness and the supported-Hom
comparison give the original locally supported module Ext as the abutment.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (F : SheafOfModules.{u} R)
  (W : ExposeI.LocallyClosedIn X)

/-- The original local linear Hom functor restricted to the open support neighbourhood. -/
def moduleSheafHomOnSupportFunctor :
    SheafOfModules.{u} R ⥤ Sheaf AddCommGrpCat.{u} ((Opens.toTopCat X).obj W.V) :=
  moduleSheafHomTopFunctor R F ⋙ ExposeI.iShriek_open W.V

instance : (moduleSheafHomOnSupportFunctor R F W).Additive := by
  dsimp [moduleSheafHomOnSupportFunctor]
  infer_instance

/-- Exact open restriction retains the original ambient sheaf Ext functor. -/
def moduleSheafHomOnSupportRightDerivedIso (q : ℕ) :
    (moduleSheafHomOnSupportFunctor R F W).rightDerived q ≅
      moduleSheafExtAbFunctor R F q ⋙ ExposeI.iShriek_open W.V := by
  letI := (ExposeI.openExtensionByZeroAdjunction W.V).isRightAdjoint
  have : (ExposeI.iShriek_open W.V).PreservesHomology := inferInstance
  exact ExposeI.rightDerivedPostcomposeIso (moduleSheafHomTopFunctor R F)
      (ExposeI.iShriek_open W.V) q ≪≫
    Functor.isoWhiskerRight (moduleSheafHomTopRightDerivedIso R F q) (ExposeI.iShriek_open W.V)

/-- The actual restricted sheaf Hom complex still uses the original ambient module resolution. -/
abbrev moduleLocallyClosedSheafHomResolutionInt {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) :=
  sheafFunctorResolutionInt (moduleSheafHomOnSupportFunctor R F W) I

/-- Every actual restricted Hom term is flasque. -/
instance {G : SheafOfModules.{u} R} (I : InjectiveResolution G) (n : ℤ) :
    ExposeI.IsFlasque ((moduleLocallyClosedSheafHomResolutionInt R F W I).X n) := by
  have : ExposeI.IsFlasque
      ((moduleSheafHomTopFunctor R F).obj (I.cochainComplex.X n)) :=
    moduleSheafHomAb_isFlasque_of_injective R F (I.cochainComplex.X n)
  exact ExposeI.isFlasque_pullback_of_isOpenEmbedding W.V.isOpenEmbedding _

/-- **VI.1.6.1, locally closed:** actual pages, differentials and next-page homology. -/
abbrev moduleLocallyClosedSheafExtSpectralSequence {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) :=
  sheafFunctorSpectralSequence (moduleSheafHomOnSupportFunctor R F W) W.ZV I

/-- The actual E₂ term computed as closed-support cohomology on the chosen neighbourhood. -/
def moduleLocallyClosedSheafExtRestrictedE2Equiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (p q : ℕ) :=
  sheafFunctorSpectralSequenceE2ComparedEquiv (moduleSheafHomOnSupportFunctor R F W) W.ZV
    (moduleSheafExtAbFunctor R F q ⋙ ExposeI.iShriek_open W.V) q
    (moduleSheafHomOnSupportRightDerivedIso R F W q) I p

/-- **VI.1.6.1, locally closed E₂:** ambient supported cohomology of original sheaf Ext. -/
def moduleLocallyClosedSheafExtSpectralSequenceE2Equiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (p q : ℕ) :
    ((moduleLocallyClosedSheafExtSpectralSequence R F W I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      ExposeI.H_locallyClosed W ((moduleSheafExtAbFunctor R F q).obj G) p :=
  (moduleLocallyClosedSheafExtRestrictedE2Equiv R F W I p q).trans
    (ExposeI.locallyClosedSupportExtEquiv W ((moduleSheafExtAbFunctor R F q).obj G) p).symm

/-- The ambient E₂ comparison reduces to its original comparison on the neighbourhood. -/
theorem moduleLocallyClosedSheafExtSpectralSequenceE2Equiv_restrict
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) (p q : ℕ)
    (x : ((moduleLocallyClosedSheafExtSpectralSequence R F W I).page 2).X ((p : ℤ), (q : ℤ))) :
    ExposeI.locallyClosedSupportExtEquiv W ((moduleSheafExtAbFunctor R F q).obj G) p
        (moduleLocallyClosedSheafExtSpectralSequenceE2Equiv R F W I p q x) =
      moduleLocallyClosedSheafExtRestrictedE2Equiv R F W I p q x :=
  (ExposeI.locallyClosedSupportExtEquiv W
    ((moduleSheafExtAbFunctor R F q).obj G) p).apply_symm_apply _

-- Preserve the proved page and comparison constructions during concrete specialization.
attribute [local irreducible] sheafFunctorSpectralSequence
  sheafFunctorSpectralSequenceMap sheafFunctorSpectralSequenceE2ComparedEquiv

private theorem moduleLocallyClosedSheafExtRestrictedE2Equiv_apply
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) (p q : ℕ)
    (x : ((moduleLocallyClosedSheafExtSpectralSequence R F W I).page 2).X ((p : ℤ), (q : ℤ))) :
    moduleLocallyClosedSheafExtRestrictedE2Equiv R F W I p q x =
      sheafFunctorSpectralSequenceE2ComparedEquiv (moduleSheafHomOnSupportFunctor R F W) W.ZV
        (moduleSheafExtAbFunctor R F q ⋙ ExposeI.iShriek_open W.V) q
        (moduleSheafHomOnSupportRightDerivedIso R F W q) I p x := rfl

/-- All original locally supported E₂ maps are the original sheaf Ext coefficient maps. -/
theorem moduleLocallyClosedSheafExtSpectralSequenceE2Equiv_naturality
    {G H : SheafOfModules.{u} R} (I : InjectiveResolution G) (J : InjectiveResolution H)
    (a : G ⟶ H) (α : I.cocomplex ⟶ J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 = a ≫ J.ι.f 0) (p q : ℕ)
    (x : ((moduleLocallyClosedSheafExtSpectralSequence R F W I).page 2).X ((p : ℤ), (q : ℤ))) :
    moduleLocallyClosedSheafExtSpectralSequenceE2Equiv R F W J p q
        (((sheafFunctorSpectralSequenceMap
          (moduleSheafHomOnSupportFunctor R F W) W.ZV α).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      (moduleLocallyClosedSheafExtSpectralSequenceE2Equiv R F W I p q x).comp
        (Abelian.Ext.mk₀ ((moduleSheafExtAbFunctor R F q).map a)) (add_zero p) := by
  apply (ExposeI.locallyClosedSupportExtEquiv W
    ((moduleSheafExtAbFunctor R F q).obj H) p).injective
  rw [moduleLocallyClosedSheafExtSpectralSequenceE2Equiv_restrict,
    ExposeI.locallyClosedSupportExtEquiv_naturality,
    moduleLocallyClosedSheafExtSpectralSequenceE2Equiv_restrict]
  rw [moduleLocallyClosedSheafExtRestrictedE2Equiv_apply,
    moduleLocallyClosedSheafExtRestrictedE2Equiv_apply]
  have h :=
    sheafFunctorSpectralSequenceE2ComparedEquiv_naturality
      (moduleSheafHomOnSupportFunctor R F W) W.ZV
      (moduleSheafExtAbFunctor R F q ⋙ ExposeI.iShriek_open W.V) q
      (moduleSheafHomOnSupportRightDerivedIso R F W q)
      (X := (Opens.toTopCat X).obj W.V) (C := SheafOfModules.{u} R)
      (G := G) (H := H) (I := I) (J := J) a α hα p x
  simpa only [Functor.comp_map, Functor.comp_obj, ExposeI.restrictToOpen,
    ExposeI.iShriek_open] using h

/-- Supported sections of the restricted Hom are the actual original locally supported Hom. -/
def moduleSheafHomOnSupportCompositeIso :
    moduleSheafHomOnSupportFunctor R F W ⋙ ExposeI.gammaZSectionsFunctor W.ZV ⊤ ≅
      moduleLocallyClosedSupportedHomFunctor R F W :=
  Functor.associator (moduleSheafHomTopFunctor R F) (ExposeI.iShriek_open W.V)
      (ExposeI.gammaZSectionsFunctor W.ZV ⊤) ≪≫
    Functor.isoWhiskerRight (moduleSheafHomTopFunctorIso R F)
      (ExposeI.gammaLocallyClosedFunctor W) ≪≫
    (moduleLocallyClosedSupportedHomGammaIso R F W).symm

/-- The actual total group with its canonical image filtration. -/
abbrev moduleLocallyClosedSheafExtSpectralTotal {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℤ) :=
  sheafFunctorSpectralTotal (moduleSheafHomOnSupportFunctor R F W) W.ZV I n

/-- **VI.1.6.1, locally closed abutment:** unchanged original supported module Ext. -/
def moduleLocallyClosedSheafExtSpectralAbutmentEquiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleLocallyClosedSheafExtSpectralTotal R F W I n ≃+
      (moduleLocallyClosedSupportedExtFunctor R F W n).obj G := by
  let e := (ExposeI.rightDerivedFunctorIso (moduleSheafHomOnSupportCompositeIso R F W) n).app G
  exact (sheafFunctorSpectralAbutmentEquiv
    (moduleSheafHomOnSupportFunctor R F W) W.ZV I n).trans e.addCommGroupIsoToAddEquiv

/-- The genuine finite increasing filtration of locally supported Ext's actual total. -/
abbrev moduleLocallyClosedSheafExtSpectralFiniteFiltration {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :=
  sheafFunctorSpectralFiniteFiltration (moduleSheafHomOnSupportFunctor R F W) W.ZV I n

@[simp]
theorem moduleLocallyClosedSheafExtSpectralFiniteFiltration_zero {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleLocallyClosedSheafExtSpectralFiniteFiltration R F W I n 0 = ⊥ :=
  sheafFunctorSpectralFiniteFiltration_zero (moduleSheafHomOnSupportFunctor R F W) W.ZV I n

@[simp]
theorem moduleLocallyClosedSheafExtSpectralFiniteFiltration_last {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleLocallyClosedSheafExtSpectralFiniteFiltration R F W I n (Fin.last (n + 1)) = ⊤ :=
  sheafFunctorSpectralFiniteFiltration_last (moduleSheafHomOnSupportFunctor R F W) W.ZV I n

/-- The genuine consecutive total-filtration quotients. -/
abbrev moduleLocallyClosedSheafExtSpectralGradedPiece {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n q : ℤ) :=
  sheafFunctorSpectralGradedPiece (moduleSheafHomOnSupportFunctor R F W) W.ZV I n q

/-- **VI.1.6.1, locally closed convergence:** stable pages are genuine graded quotients. -/
def moduleLocallyClosedSheafExtSpectralStablePageIsoGraded {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) (q : Fin (n + 1)) (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((moduleLocallyClosedSheafExtSpectralSequence R F W I).page r).X ((n : ℤ) - q, q) ≅
      moduleLocallyClosedSheafExtSpectralGradedPiece R F W I n q :=
  sheafFunctorSpectralStablePageIsoGraded
    (moduleSheafHomOnSupportFunctor R F W) W.ZV I n q r hr

/-- The entire locally supported spectral sequence is functorial in the original coefficient. -/
abbrev moduleLocallyClosedSheafExtSpectralSequenceFunctor :=
  sheafFunctorSpectralSequenceFunctor (moduleSheafHomOnSupportFunctor R F W) W.ZV

/-- Canonical change of ambient module-injective resolution on all actual pages. -/
abbrev moduleLocallyClosedSheafExtSpectralSequenceResolutionIso {G : SheafOfModules.{u} R}
    (I J : InjectiveResolution G) :=
  sheafFunctorSpectralSequenceResolutionIso (moduleSheafHomOnSupportFunctor R F W) W.ZV I J

end SGA.SGA2.ExposeVI
