/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.RingedModulePushforwardSpectralSequence
import SGA.SGA2.ExposeI.NaturalTransformationCohomology
import SGA.SGA2.ExposeI.DerivedTruncationNaturality

/-!
# V.3.2: retained scalars on the original E₂ truncation comparison

The original homology identification of the direct-image resolution with
the higher module direct image respects the actual global scalar action.
Naturality of the original normalized truncation comparison then retains
those scalars on its single-degree interval.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {R : Sheaf RingCat.{u} X} {S : Sheaf RingCat.{u} Y}
  (φ : S ⟶ (Sheaf.pushforward RingCat f).obj R)

local instance e2ScalarsHasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} Y) :=
  HasDerivedCategory.standard _

/-- The unchanged higher-direct-image homology comparison retains the original scalars. -/
@[reassoc]
theorem ringedModulePushforwardDerivedObjectHomologyIso_scalar
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M) (q : ℕ)
    (r : S.obj.obj (op (⊤ : Opens Y))) :
    (DerivedCategory.homologyFunctor (Sheaf AddCommGrpCat.{u} Y) (q : ℤ)).map
        (ringedModulePushforwardDerivedScalarRingHom f φ I r) ≫
        (ringedModulePushforwardDerivedObjectHomologyIso f φ I q).hom =
      (ringedModulePushforwardDerivedObjectHomologyIso f φ I q).hom ≫
        moduleUnderlyingGlobalScalarHom S ((derivedRingedModulePushforward f φ q).obj M) r := by
  let a := moduleUnderlyingComplexGlobalScalar S (ringedModulePushforwardResolutionInt f φ I) r
  have hQ := (DerivedCategory.homologyFunctorFactors (Sheaf AddCommGrpCat.{u} Y)
    (q : ℤ)).hom.naturality a
  simp only [Functor.comp_map] at hQ
  have hI := ExposeI.injectiveResolutionIntHomologyIso_natTrans
    (Functor.whiskerLeft (ringedModulePushforward f φ) (moduleUnderlyingGlobalScalar S r)) I q
  have hP := ExposeI.rightDerivedPostcomposeIso_natTrans
    (ringedModulePushforward f φ) (moduleUnderlyingGlobalScalar S r) M q
  dsimp only [ringedModulePushforwardDerivedObjectHomologyIso, Iso.trans_hom, Iso.app_hom]
  change (DerivedCategory.homologyFunctor (Sheaf AddCommGrpCat.{u} Y) (q : ℤ)).map
      (DerivedCategory.Q.map a) ≫ _ = _
  erw [← Category.assoc, hQ, Category.assoc]
  simp only [Category.assoc]
  apply (cancel_epi ((DerivedCategory.homologyFunctorFactors (Sheaf AddCommGrpCat.{u} Y)
    (q : ℤ)).hom.app (ringedModulePushforwardAdditiveResolutionInt f φ I))).mpr
  erw [← Category.assoc, hI, Category.assoc, hP]
  rfl

/-- The existing E₂ single-degree truncation isomorphism intertwines actual global scalars. -/
@[reassoc]
theorem ringedModulePushforwardE2TruncationIso_scalar
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M) (q : ℕ)
    (r : S.obj.obj (op (⊤ : Opens Y))) :
    ExposeI.derivedSingleDegreeTruncationMap (q : ℤ)
        (ringedModulePushforwardDerivedScalarRingHom f φ I r) ≫
        (ringedModulePushforwardE2TruncationIso f φ I q).hom =
      (ringedModulePushforwardE2TruncationIso f φ I q).hom ≫
        (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} Y) (q : ℤ)).map
          (moduleUnderlyingGlobalScalarHom S ((derivedRingedModulePushforward f φ q).obj M) r) := by
  dsimp only [ringedModulePushforwardE2TruncationIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [ExposeI.derivedSingleDegreeTruncationIsoSingle_naturality_assoc,
    ← Functor.map_comp, ringedModulePushforwardDerivedObjectHomologyIso_scalar,
    Functor.map_comp, Category.assoc]

end SGA.SGA2.ExposeV
