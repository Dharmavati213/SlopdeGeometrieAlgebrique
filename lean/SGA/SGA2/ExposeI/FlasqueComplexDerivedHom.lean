/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.HomComplexDerivedMap
import SGA.SGA2.ExposeI.FlasqueQuasiIso
import SGA.SGA2.ExposeI.SupportedCohomologyComparison
import Mathlib.Algebra.Homology.Factorizations.CM5a

/-!
# Supported derived Hom computed on bounded-below flasque complexes

The canonical localization map, already natural for arbitrary cochain maps,
is bijective for a bounded-below complex of flasque sheaves. An actual
injective replacement and preservation of its quasi-isomorphism by supported
sections prove bijectivity. The comparison itself is independent of this
replacement, so all original additive cochain maps, including scalar actions,
remain visible.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat CochainComplex
open CochainComplex.HomComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (Z : Closeds X)

local instance : HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard _

/-- The actual single-source Hom complex is the complex of original supported sections. -/
def closedSupportHomComplexIso (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    HomComplex ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj
      (zZX_closed Z)) K ≅ ((gammaZSectionsFunctor Z ⊤).mapHomologicalComplex _).obj K :=
  homComplexFromSingleIso (zZX_closed Z) K ≪≫
    (NatIso.mapHomologicalComplex (closedSupportHomFunctorIso Z) (ComplexShape.up ℤ)).app K

@[reassoc]
theorem closedSupportHomComplexIso_naturality
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ} (f : K ⟶ L) :
    homComplexPostcomp
        ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (zZX_closed Z)) f ≫
        (closedSupportHomComplexIso Z L).hom =
      (closedSupportHomComplexIso Z K).hom ≫
        ((gammaZSectionsFunctor Z ⊤).mapHomologicalComplex _).map f := by
  dsimp only [closedSupportHomComplexIso, Iso.trans_hom]
  rw [homComplexFromSingleIso_naturality_assoc]
  simpa only [Iso.app_hom, Category.assoc] using congrArg
    (fun a ↦ (homComplexFromSingleIso (zZX_closed Z) K).hom ≫ a)
    ((NatIso.mapHomologicalComplex (closedSupportHomFunctorIso Z)
      (ComplexShape.up ℤ)).hom.naturality f)

/-- The unchanged supported-section/Hom-complex comparison on homology. -/
def closedSupportHomComplexHomologyIso
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) (n : ℤ) :
    (HomComplex ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj
      (zZX_closed Z)) K).homology n ≅
      (((gammaZSectionsFunctor Z ⊤).mapHomologicalComplex _).obj K).homology n :=
  (homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) n).mapIso (closedSupportHomComplexIso Z K)

@[reassoc]
theorem closedSupportHomComplexHomologyIso_naturality
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ} (f : K ⟶ L) (n : ℤ) :
    homologyMap (homComplexPostcomp
        ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (zZX_closed Z)) f) n ≫
        (closedSupportHomComplexHomologyIso Z L n).hom =
      (closedSupportHomComplexHomologyIso Z K n).hom ≫
        homologyMap (((gammaZSectionsFunctor Z ⊤).mapHomologicalComplex _).map f) n := by
  have h := congrArg (fun a ↦ homologyMap a n) (closedSupportHomComplexIso_naturality Z f)
  simp only [homologyMap_comp] at h
  exact h

/-- Supported Hom-complex homology preserves the actual flasque replacement map. -/
theorem closedSupportHomComplexPostcomp_isIso_homologyMap
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ} (f : K ⟶ L) [QuasiIso f]
    (d : ℤ) [K.IsStrictlyGE d] [L.IsStrictlyGE d]
    [∀ n, IsFlasque (K.X n)] [∀ n, IsFlasque (L.X n)] (n : ℤ) :
    IsIso (homologyMap (homComplexPostcomp
      ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (zZX_closed Z)) f) n) := by
  have := gammaZSections_quasiIso_of_boundedBelow_flasque Z ⊤ f d
    (fun n hn ↦ isZero_of_isStrictlyGE K d n hn) (fun n hn ↦ isZero_of_isStrictlyGE L d n hn)
  rw [← isIso_comp_right_iff _ (closedSupportHomComplexHomologyIso Z L n).hom,
    closedSupportHomComplexHomologyIso_naturality]
  infer_instance

/-- The canonical localization map is bijective on bounded-below flasque complexes. -/
theorem closedSupportHomComplexDerivedHomMap_bijective
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) (d : ℤ) [K.IsStrictlyGE d]
    [∀ n, IsFlasque (K.X n)] (n : ℤ) :
    Function.Bijective (homComplexHomologyDerivedHomMap
      ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (zZX_closed Z)) K n) := by
  obtain ⟨L, i, hi, hL, hb⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K d
  have : L.IsKInjective := CochainComplex.isKInjective_of_injective L d
  have (j : ℤ) : IsFlasque (L.X j) := isFlasque_of_injective (L.X j)
  let A := (CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (zZX_closed Z)
  have := closedSupportHomComplexPostcomp_isIso_homologyMap Z i d n
  have hleft : Function.Bijective (fun x : (HomComplex A K).homology n ↦
      homComplexHomologyDerivedHomMap A L n (homologyMap (homComplexPostcomp A i) n x)) :=
    (homComplexHomologyDerivedHomEquiv A L n).bijective.comp
      (ConcreteCategory.bijective_of_isIso (homologyMap (homComplexPostcomp A i) n))
  have hright : Function.Bijective (fun x : (HomComplex A K).homology n ↦
      homComplexHomologyDerivedHomMap A K n x ≫ (DerivedCategory.Q.map i)⟦n⟧') := by
    convert hleft using 1
    funext x
    exact (homComplexHomologyDerivedHomMap_naturality A i n x).symm
  exact hright.of_comp_left (fun a b h ↦ (cancel_mono ((DerivedCategory.Q.map i)⟦n⟧')).mp h)

/-- The actual supported-section complex computes derived supported Hom on every
bounded-below flasque complex, in every integer degree. -/
def flasqueGammaComplexDerivedHomEquiv
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) (d : ℤ) [K.IsStrictlyGE d]
    [∀ n, IsFlasque (K.X n)] (n : ℤ) :
    (((gammaZSectionsFunctor Z ⊤).mapHomologicalComplex _).obj K).homology n ≃+
      ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (zZX_closed Z) ⟶
        (DerivedCategory.Q.obj K)⟦n⟧) :=
  (closedSupportHomComplexHomologyIso Z K n).symm.addCommGroupIsoToAddEquiv.trans
    (AddEquiv.ofBijective (homComplexHomologyDerivedHomMap
      ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (zZX_closed Z)) K n)
      (closedSupportHomComplexDerivedHomMap_bijective Z K d n))

/-- The canonical comparison is natural for all actual cochain maps, not just
maps between injective resolutions or maps linear over a structure ring. -/
theorem flasqueGammaComplexDerivedHomEquiv_naturality
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ} (f : K ⟶ L)
    (d : ℤ) [K.IsStrictlyGE d] [L.IsStrictlyGE d]
    [∀ n, IsFlasque (K.X n)] [∀ n, IsFlasque (L.X n)] (n : ℤ)
    (x : (((gammaZSectionsFunctor Z ⊤).mapHomologicalComplex _).obj K).homology n) :
    flasqueGammaComplexDerivedHomEquiv Z L d n
        (homologyMap (((gammaZSectionsFunctor Z ⊤).mapHomologicalComplex _).map f) n x) =
      flasqueGammaComplexDerivedHomEquiv Z K d n x ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  let A := (CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (zZX_closed Z)
  have h : homologyMap (((gammaZSectionsFunctor Z ⊤).mapHomologicalComplex _).map f) n ≫
        (closedSupportHomComplexHomologyIso Z L n).inv =
      (closedSupportHomComplexHomologyIso Z K n).inv ≫
        homologyMap (homComplexPostcomp A f) n := by
    rw [← cancel_epi (closedSupportHomComplexHomologyIso Z K n).hom,
      ← Category.assoc, ← closedSupportHomComplexHomologyIso_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  change homComplexHomologyDerivedHomMap A L n
      ((closedSupportHomComplexHomologyIso Z L n).inv
        (homologyMap (((gammaZSectionsFunctor Z ⊤).mapHomologicalComplex _).map f) n x)) =
    homComplexHomologyDerivedHomMap A K n ((closedSupportHomComplexHomologyIso Z K n).inv x) ≫
      (DerivedCategory.Q.map f)⟦n⟧'
  have hx := ConcreteCategory.congr_hom h x
  simp only [ConcreteCategory.comp_apply] at hx
  rw [hx]
  exact homComplexHomologyDerivedHomMap_naturality A f n _

end SGA.SGA2.ExposeI
