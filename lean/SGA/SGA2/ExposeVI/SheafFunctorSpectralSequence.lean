/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalE2
import SGA.SGA2.ExposeI.InjectiveResolutionIntCohomology
import SGA.SGA2.ExposeI.FlasqueComplexDerivedHom
import SGA.SGA2.ExposeI.SpectralObjectConvergence

/-!
# The supported-cohomology spectral sequence of a sheaf-valued derived functor

For an additive functor to abelian sheaves, canonical truncations of its
mapped injective resolution give actual pages and differentials, E₂ terms
`H_Zᵖ(RᑫT)`, and a finite first-quadrant filtration of derived supported Hom.
If the mapped resolution has flasque terms, this total is the original
right-derived composite `T ⋙ Γ_Z`. The flasque hypothesis is required only
for this comparison, and is supplied explicitly in the applications.
-/

noncomputable section

universe u v w

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat
open ComposableArrows

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} {C : Type v} [Category.{w} C] [Abelian C]
  [HasInjectiveResolutions C] (T : C ⥤ Sheaf AddCommGrpCat.{u} X) [T.Additive]

/-- The site-sheaf and topological-sheaf presentations have the same right-derived
functor. Keeping this generic comparison opaque avoids unfolding a concrete
internal-Hom functor while checking the identical abelian-category instances. -/
def sheafFunctorRightDerivedPresentationIso
    (S : C ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [S.Additive] (n : ℕ) :
    (show C ⥤ Sheaf AddCommGrpCat.{u} X from S).rightDerived n ≅ S.rightDerived n :=
  Iso.refl _

/-- The actual integer-indexed mapped injective resolution. -/
def sheafFunctorResolutionInt {G : C}
    (I : InjectiveResolution G) : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ :=
  (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex

instance {G : C} (I : InjectiveResolution G) :
    (sheafFunctorResolutionInt T I).IsStrictlyGE 0 := by
  dsimp [sheafFunctorResolutionInt]
  infer_instance

local instance : HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard _

/-- The genuine derived object represented by the mapped injective resolution. -/
def sheafFunctorDerivedObject {G : C}
    (I : InjectiveResolution G) : DerivedCategory (Sheaf AddCommGrpCat.{u} X) :=
  DerivedCategory.Q.obj (sheafFunctorResolutionInt T I)

instance {G : C} (I : InjectiveResolution G) :
    (sheafFunctorDerivedObject T I).IsGE 0 := by
  dsimp [sheafFunctorDerivedObject]
  infer_instance

/-- Its cohomology sheaves are the original right-derived functor values. -/
def sheafFunctorDerivedHomologyIso {G : C}
    (I : InjectiveResolution G) (q : ℕ) :
    (DerivedCategory.homologyFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).obj
        (sheafFunctorDerivedObject T I) ≅ (T.rightDerived q).obj G :=
  (DerivedCategory.homologyFunctorFactors (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).app
      (sheafFunctorResolutionInt T I) ≪≫
    ExposeI.injectiveResolutionIntHomologyIso
      (T) I q

/-- The genuine truncation spectral object of the mapped resolution. -/
def sheafFunctorSpectralTriangulatedSpectralObject {G : C}
    (I : InjectiveResolution G) :
    Triangulated.SpectralObject (DerivedCategory (Sheaf AddCommGrpCat.{u} X)) EInt :=
  (DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} X)).spectralObject
    (sheafFunctorDerivedObject T I)

variable (Z : Closeds X)

/-- Derived Hom from the original integer sheaf representing supported sections. -/
def sheafFunctorDerivedSupportedHom :
    DerivedCategory (Sheaf AddCommGrpCat.{u} X) ⥤ AddCommGrpCat.{u + 1} :=
  preadditiveCoyoneda.obj
    (op ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj
      (ExposeI.zZX_closed Z)))

instance : (sheafFunctorDerivedSupportedHom Z).IsHomological := by
  dsimp [sheafFunctorDerivedSupportedHom]
  infer_instance

instance : (sheafFunctorDerivedSupportedHom Z).ShiftSequence ℤ := by
  dsimp [sheafFunctorDerivedSupportedHom]
  infer_instance

/-- The actual abelian spectral object of the mapped resolution. -/
def sheafFunctorSpectralAbelianSpectralObject {G : C}
    (I : InjectiveResolution G) : Abelian.SpectralObject AddCommGrpCat.{u + 1} EInt :=
  ExposeI.homologicalSpectralObject (sheafFunctorSpectralTriangulatedSpectralObject T I)
    (sheafFunctorDerivedSupportedHom Z)

/-- all actual pages, differentials and homology-to-next-page isomorphisms. -/
def sheafFunctorSpectralSequence {G : C}
    (I : InjectiveResolution G) : E₂CohomologicalSpectralSequence AddCommGrpCat.{u + 1} :=
  (sheafFunctorSpectralAbelianSpectralObject T Z I).E₂SpectralSequence

/-- The one-degree truncation is the original derived value placed in its actual degree. -/
def sheafFunctorSpectralE2TruncationIso {G : C}
    (I : InjectiveResolution G) (q : ℕ) :
    (sheafFunctorSpectralTriangulatedSpectralObject T I).ω₁.obj
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) by
          exact WithBotTop.coe_le_coe.mpr (by lia)))) ≅
      (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).obj
        ((T.rightDerived q).obj G) :=
  ExposeI.derivedSingleDegreeTruncationIsoSingle (sheafFunctorDerivedObject T I)
      (q : ℤ) ≪≫
    (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).mapIso
      (sheafFunctorDerivedHomologyIso T I q)

/-- The actual first-page interval comparison used by the E₂ identification. -/
def sheafFunctorSpectralE2FirstPageIso {G : C}
    (I : InjectiveResolution G) (p q : ℕ) :=
  (sheafFunctorSpectralAbelianSpectralObject T Z I).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂Cohomological
    ((p : ℤ), (q : ℤ)) (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl

/-- The original E₂ truncation comparison with the total shift made explicit. -/
def sheafFunctorSpectralE2TotalShiftIso {G : C}
    (I : InjectiveResolution G) (p q : ℕ) :=
  (shiftFunctor (DerivedCategory (Sheaf AddCommGrpCat.{u} X))
      ((p : ℤ) + (q : ℤ))).mapIso (sheafFunctorSpectralE2TruncationIso T I q) ≪≫
    ExposeI.supportedSingleTotalShiftIso ((T.rightDerived q).obj G)
      (p : ℤ) (q : ℤ)

/-- Actual E₂ page terms are supported cohomology of the original derived values. -/
def sheafFunctorSpectralSequenceE2Equiv {G : C}
    (I : InjectiveResolution G) (p q : ℕ) :
    ((sheafFunctorSpectralSequence T Z I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      ExposeI.H_Z Z ((T.rightDerived q).obj G) p := by
  let eHom := (sheafFunctorDerivedSupportedHom Z).mapIso
    (sheafFunctorSpectralE2TotalShiftIso T I p q)
  exact (sheafFunctorSpectralE2FirstPageIso T Z I p q).addCommGroupIsoToAddEquiv.trans
    (eHom.addCommGroupIsoToAddEquiv.trans (Abelian.Ext.homAddEquiv
      (X := ExposeI.zZX_closed Z) (Y := (T.rightDerived q).obj G)
      (n := p)).symm)

/-- The same E₂ comparison for a functor declared in the site-sheaf presentation.
The explicit presentation comparison prevents expensive unfolding of concrete functors. -/
def sheafFunctorSpectralSequenceE2SiteEquiv
    (S : C ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [S.Additive] {G : C} (I : InjectiveResolution G) (p q : ℕ) :
    ((sheafFunctorSpectralSequence S Z I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      ExposeI.H_Z Z ((S.rightDerived q).obj G) p :=
  (sheafFunctorSpectralSequenceE2Equiv S Z I p q).trans
    (((Abelian.extFunctorObj (ExposeI.zZX_closed Z) p).mapIso
      ((sheafFunctorRightDerivedPresentationIso S q).app G)).addCommGroupIsoToAddEquiv)

/-- The unchanged E₂ comparison followed by a specified natural identification
of the original right-derived values. -/
def sheafFunctorSpectralSequenceE2ComparedEquiv
    (U : C ⥤ Sheaf AddCommGrpCat.{u} X) (q : ℕ) (e : T.rightDerived q ≅ U)
    {G : C} (I : InjectiveResolution G) (p : ℕ) :
    ((sheafFunctorSpectralSequence T Z I).page 2).X ((p : ℤ), (q : ℤ)) ≃+
      ExposeI.H_Z Z (U.obj G) p :=
  let eH := (Abelian.extFunctorObj (ExposeI.zZX_closed Z) p).mapIso (e.app G)
  (sheafFunctorSpectralSequenceE2Equiv T Z I p q).trans eH.addCommGroupIsoToAddEquiv

/-- Connectiveness and standard t-structure orthogonality imply first-quadrant support. -/
instance sheafFunctorSpectralAbelianSpectralObject_isFirstQuadrant
    {G : C} (I : InjectiveResolution G) :
    (sheafFunctorSpectralAbelianSpectralObject T Z I).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    let t := DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} X)
    have h := t.isZero_eTruncLT_obj_obj (sheafFunctorDerivedObject T I) 0 j hj
    have h' := (t.eTruncGE.obj i).map_isZero h
    exact ((sheafFunctorDerivedSupportedHom Z).shift n).map_isZero h'
  isZero₂ i j hij n hi := by
    let t := DerivedCategory.TStructure.t (C := Sheaf AddCommGrpCat.{u} X)
    have hni : ((n + 1 : ℤ) : EInt) ≤ i := by
      induction i using WithBotTop.rec with
      | bot => simp at hi
      | coe i =>
        simp only [WithBotTop.coe_le_coe, WithBotTop.coe_lt_coe] at *
        lia
      | top => exact le_top
    have hge := t.isGE_eTruncGE_obj_obj (n + 1) i hni
      ((t.eTruncLT.obj j).obj (sheafFunctorDerivedObject T I))
    have hshift := t.isGE_shift
      ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj
        (sheafFunctorDerivedObject T I))) (n + 1) n 1 (by lia)
    change IsZero (AddCommGrpCat.of
      (((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (ExposeI.zZX_closed Z)) ⟶
        ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj
          (sheafFunctorDerivedObject T I)))⟦n⟧))
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact ⟨fun a b ↦ (t.zero a 0 1).trans (t.zero b 0 1).symm⟩

/-- The actual total interval of the constructed spectral object. -/
def sheafFunctorSpectralTotal {G : C}
    (I : InjectiveResolution G) (n : ℤ) : AddCommGrpCat.{u + 1} :=
  ExposeI.SpectralObjectConvergence.total (sheafFunctorSpectralAbelianSpectralObject T Z I) n

/-- Flasque mapped terms identify the actual total with the original derived composite. -/
def sheafFunctorSpectralAbutmentEquiv {G : C}
    (I : InjectiveResolution G)
    [∀ j, ExposeI.IsFlasque ((sheafFunctorResolutionInt T I).X j)] (n : ℕ) :
    sheafFunctorSpectralTotal T Z I n ≃+
      ((T ⋙ ExposeI.gammaZSectionsFunctor Z ⊤).rightDerived n).obj G :=
  (ExposeI.flasqueGammaComplexDerivedHomEquiv Z (sheafFunctorResolutionInt T I)
    0 n).symm.trans
      (ExposeI.injectiveResolutionIntHomologyIso (T ⋙ ExposeI.gammaZSectionsFunctor Z ⊤)
        I n).addCommGroupIsoToAddEquiv

/-- The finite increasing filtration of the actual total group. -/
def sheafFunctorSpectralFiniteFiltration {G : C}
    (I : InjectiveResolution G) (n : ℕ) :
    Fin (n + 2) →o Subobject (sheafFunctorSpectralTotal T Z I n) :=
  ExposeI.SpectralObjectConvergence.finiteFiltration
    (sheafFunctorSpectralAbelianSpectralObject T Z I) n

omit [HasInjectiveResolutions C] in
@[simp]
theorem sheafFunctorSpectralFiniteFiltration_zero {G : C}
    (I : InjectiveResolution G) (n : ℕ) :
    sheafFunctorSpectralFiniteFiltration T Z I n 0 = ⊥ :=
  ExposeI.SpectralObjectConvergence.finiteFiltration_zero _ n

omit [HasInjectiveResolutions C] in
@[simp]
theorem sheafFunctorSpectralFiniteFiltration_last {G : C}
    (I : InjectiveResolution G) (n : ℕ) :
    sheafFunctorSpectralFiniteFiltration T Z I n (Fin.last (n + 1)) = ⊤ :=
  ExposeI.SpectralObjectConvergence.finiteFiltration_last _ n

/-- Consecutive quotients of the canonical image filtration on actual total cohomology. -/
def sheafFunctorSpectralGradedPiece {G : C}
    (I : InjectiveResolution G) (n q : ℤ) : AddCommGrpCat.{u + 1} :=
  ExposeI.SpectralObjectConvergence.gradedPiece
    (sheafFunctorSpectralAbelianSpectralObject T Z I) n q

/-- Stable actual pages are genuine graded quotients
of the abutment filtration, uniformly from page `n + 2` in total degree `n`. -/
def sheafFunctorSpectralStablePageIsoGraded {G : C}
    (I : InjectiveResolution G) (n : ℕ) (q : Fin (n + 1)) (r : ℤ) (hr : (n : ℤ) + 2 ≤ r) :
    ((sheafFunctorSpectralSequence T Z I).page r).X ((n : ℤ) - q, q) ≅
      sheafFunctorSpectralGradedPiece T Z I n q :=
  ExposeI.SpectralObjectConvergence.stablePageIsoGradedTotal
    (sheafFunctorSpectralAbelianSpectralObject T Z I) n q r hr

end SGA.SGA2.ExposeVI
