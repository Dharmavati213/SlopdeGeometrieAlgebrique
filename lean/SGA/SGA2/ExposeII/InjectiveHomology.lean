/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.InjectiveDetection
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# SGA 2, Exposé II, Lemma 9: Hom into injectives and homology

For an injective coefficient module, cohomology of the dual complex agrees
with Hom of homology. The comparison is natural in the original complex,
so it also compares the direct systems obtained by dualizing inverse systems
of complexes. This supplies the homological-algebra input used in II.9.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R]

/-- Contravariant module-valued Hom preserves limits. -/
instance linearYonedaObj_preservesLimits (E : ModuleCat.{u} R) :
    PreservesLimits ((linearYoneda R (ModuleCat.{u} R)).obj E) := by
  have : PreservesLimits
      (((linearYoneda R (ModuleCat.{u} R)).obj E) ⋙ forget (ModuleCat.{u} R)) :=
    inferInstanceAs (PreservesLimits (yoneda.obj E))
  exact preservesLimits_of_reflects_of_preserves _ (forget (ModuleCat.{u} R))

/-- Injectivity makes contravariant module-valued Hom preserve epimorphisms. -/
instance linearYonedaObj_preservesEpimorphisms (E : ModuleCat.{u} R) [Injective E] :
    ((linearYoneda R (ModuleCat.{u} R)).obj E).PreservesEpimorphisms := by
  have : (((linearYoneda R (ModuleCat.{u} R)).obj E) ⋙
      forget (ModuleCat.{u} R)).PreservesEpimorphisms :=
    (Injective.injective_iff_preservesEpimorphisms_yoneda_obj E).mp inferInstance
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects _ (forget (ModuleCat.{u} R))

/-- Hom into an injective module is exact, hence preserves homology. -/
instance linearYonedaObj_preservesHomology (E : ModuleCat.{u} R) [Injective E] :
    ((linearYoneda R (ModuleCat.{u} R)).obj E).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

variable {ι : Type v} (c : ComplexShape ι)

/-- The contravariant functor taking a complex to its module-valued Hom
complex with coefficient module `E`. -/
def homComplexFunctor (E : ModuleCat.{u} R) :
    (HomologicalComplex (ModuleCat.{u} R) c)ᵒᵖ ⥤
      HomologicalComplex (ModuleCat.{u} R) c.symm :=
  HomologicalComplex.opFunctor _ c ⋙
    ((linearYoneda R (ModuleCat.{u} R)).obj E).mapHomologicalComplex c.symm

/-- Cohomology of the Hom complex for injective coefficients is Hom of
the original homology. -/
def homComplexHomologyIso (K : HomologicalComplex (ModuleCat.{u} R) c)
    (E : ModuleCat.{u} R) [Injective E] (i : ι) :
    ((homComplexFunctor c E).obj (op K)).homology i ≅
      ModuleCat.of R (K.homology i ⟶ E) :=
  (K.op.sc i).mapHomologyIso ((linearYoneda R (ModuleCat.{u} R)).obj E) ≪≫
    ((linearYoneda R (ModuleCat.{u} R)).obj E).mapIso (K.homologyOp i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The injective-coefficient comparison commutes with chain maps. -/
@[reassoc]
theorem homComplexHomologyIso_hom_naturality
    {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L)
    (E : ModuleCat.{u} R) [Injective E] (i : ι) :
    HomologicalComplex.homologyMap ((homComplexFunctor c E).map f.op) i ≫
        (homComplexHomologyIso c K E i).hom =
      (homComplexHomologyIso c L E i).hom ≫
        ((linearYoneda R (ModuleCat.{u} R)).obj E).map
          (HomologicalComplex.homologyMap f i).op := by
  let H := (linearYoneda R (ModuleCat.{u} R)).obj E
  let φ : L.op.sc i ⟶ K.op.sc i := (HomologicalComplex.shortComplexFunctor _ c.symm i).map
    ((HomologicalComplex.opFunctor _ c).map f.op)
  change ShortComplex.homologyMap (H.mapShortComplex.map φ) ≫
      ((K.op.sc i).mapHomologyIso H).hom ≫ H.map (K.homologyOp i).hom =
    (((L.op.sc i).mapHomologyIso H).hom ≫ H.map (L.homologyOp i).hom) ≫
      H.map (HomologicalComplex.homologyMap f i).op
  rw [← Category.assoc]
  rw [ShortComplex.mapHomologyIso_hom_naturality]
  rw [Category.assoc, ← Functor.map_comp]
  change ((L.op.sc i).mapHomologyIso H).hom ≫
    H.map (HomologicalComplex.homologyMap ((HomologicalComplex.opFunctor _ c).map f.op) i ≫
      (K.homologyOp i).hom) = _
  rw [HomologicalComplex.homologyOp_hom_naturality]
  simp only [Functor.map_comp, Category.assoc]

/-- The Hom-homology comparison as a natural isomorphism in the complex. -/
def homComplexHomologyNatIso (E : ModuleCat.{u} R) [Injective E] (i : ι) :
    homComplexFunctor c E ⋙ HomologicalComplex.homologyFunctor _ c.symm i ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c i).op ⋙
        (linearYoneda R (ModuleCat.{u} R)).obj E :=
  NatIso.ofComponents (fun K => homComplexHomologyIso c K.unop E i)
    (fun f => homComplexHomologyIso_hom_naturality c f.unop E i)

/-- II.9: for a chain complex this is the standard Hom cochain complex
already used in mathlib's Ext construction. -/
def linearYonedaObjHomologyIso (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (E : ModuleCat.{u} R) [Injective E] (i : ℕ) :
    (K.linearYonedaObj R E).homology i ≅ ModuleCat.of R (K.homology i ⟶ E) :=
  homComplexHomologyIso (ComplexShape.down ℕ) K E i

/-- The direct system of cohomology modules obtained by applying Hom to
an inverse sequence of complexes. -/
def homComplexCohomologyDiagram
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{u} R) c)
    (E : ModuleCat.{u} R) (i : ι) : ℕᵒᵖᵒᵖ ⥤ ModuleCat.{u} R :=
  K.op ⋙ homComplexFunctor c E ⋙ HomologicalComplex.homologyFunctor _ c.symm i

/-- Injective coefficients identify the direct limit of Hom-complex
cohomology with the direct limit of Hom of the homology system. -/
def homComplexCohomologyColimitIso
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{u} R) c)
    (E : ModuleCat.{u} R) [Injective E] (i : ι) :
    colimit (homComplexCohomologyDiagram c K E i) ≅
      colimit ((K ⋙ HomologicalComplex.homologyFunctor _ c i).op ⋙
        (linearYoneda R (ModuleCat.{u} R)).obj E) :=
  HasColimit.isoOfNatIso (Functor.isoWhiskerLeft K.op (homComplexHomologyNatIso c E i))

/-- II.9(b) ⇔ (c), for an arbitrary inverse sequence of complexes:
vanishing of the direct limit of Hom-complex cohomology on all injective
coefficients is equivalent to essential vanishing of the homology system. -/
theorem isEssentiallyZero_homology_iff_isZero_cohomology_colimit
    (K : ℕᵒᵖ ⥤ HomologicalComplex (ModuleCat.{u} R) c) (i : ι) :
    IsEssentiallyZero (K ⋙ HomologicalComplex.homologyFunctor _ c i) ↔
      ∀ (E : ModuleCat.{u} R) [Injective E],
        IsZero (colimit (homComplexCohomologyDiagram c K E i)) := by
  constructor
  · intro h E _
    exact (h.isZero_hom_colimit E).of_iso (homComplexCohomologyColimitIso c K E i)
  · intro h
    apply isEssentiallyZero_of_isZero_hom_colimit_injective
    intro E _
    exact (h E).of_iso (homComplexCohomologyColimitIso c K E i).symm

end SGA.SGA2.ExposeII
