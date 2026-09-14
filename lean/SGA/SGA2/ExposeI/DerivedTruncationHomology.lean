/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-! # Single-degree canonical truncation and actual derived-category homology -/

noncomputable section

universe w v u

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Truncation below `q + 1` does not change degree-`q` homology. -/
instance derivedTruncLT_homologyMap_isIso (K : DerivedCategory C) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor C q).map
      ((DerivedCategory.TStructure.t.truncLTι (q + 1)).app K)) := by
  let H := DerivedCategory.homologyFunctor C 0
  let T := (DerivedCategory.TStructure.t.triangleLTGE (q + 1)).obj K
  have hT : T ∈ distTriang _ := DerivedCategory.TStructure.t.triangleLTGE_distinguished _ K
  have hzero : IsZero ((DerivedCategory.homologyFunctor C q).obj T.obj₃) :=
    DerivedCategory.isZero_of_isGE _ (q + 1) q (by lia)
  have hprev : IsZero ((DerivedCategory.homologyFunctor C (q - 1)).obj T.obj₃) :=
    DerivedCategory.isZero_of_isGE _ (q + 1) (q - 1) (by lia)
  have : Mono ((H.shift q).map T.mor₁) :=
    (H.homologySequence_exact₁ T hT (q - 1) q (by lia)).mono_g (hprev.eq_of_src _ _)
  have : Epi ((H.shift q).map T.mor₁) :=
    (H.homologySequence_exact₂ T hT q).epi_f (hzero.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((H.shift q).map T.mor₁)

/-- Truncation from `q` upwards does not change degree-`q` homology. -/
instance derivedTruncGE_homologyMap_isIso (K : DerivedCategory C) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor C q).map
      ((DerivedCategory.TStructure.t.truncGEπ q).app K)) := by
  let H := DerivedCategory.homologyFunctor C 0
  let T := (DerivedCategory.TStructure.t.triangleLTGE q).obj K
  have hT : T ∈ distTriang _ := DerivedCategory.TStructure.t.triangleLTGE_distinguished _ K
  have hzero : IsZero ((DerivedCategory.homologyFunctor C q).obj T.obj₁) :=
    DerivedCategory.isZero_of_isLE _ (q - 1) q (by lia)
  have hnext : IsZero ((DerivedCategory.homologyFunctor C (q + 1)).obj T.obj₁) :=
    DerivedCategory.isZero_of_isLE _ (q - 1) (q + 1) (by lia)
  have : Mono ((H.shift q).map T.mor₂) :=
    (H.homologySequence_exact₂ T hT q).mono_g (hzero.eq_of_src _ _)
  have : Epi ((H.shift q).map T.mor₂) :=
    (H.homologySequence_exact₃ T hT q (q + 1) rfl).epi_f (hnext.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((H.shift q).map T.mor₂)

/-- Canonical truncation to the single degree `q`. -/
def derivedSingleDegreeTruncation (K : DerivedCategory C) (q : ℤ) : DerivedCategory C :=
  (DerivedCategory.TStructure.t.truncGE q).obj
    ((DerivedCategory.TStructure.t.truncLT (q + 1)).obj K)

/-- Homology of the single-degree truncation is the original degree-`q`
homology object. -/
def derivedSingleDegreeTruncationHomologyIso (K : DerivedCategory C) (q : ℤ) :
    (DerivedCategory.homologyFunctor C q).obj (derivedSingleDegreeTruncation K q) ≅
      (DerivedCategory.homologyFunctor C q).obj K :=
  (asIso ((DerivedCategory.homologyFunctor C q).map
    ((DerivedCategory.TStructure.t.truncGEπ q).app
      ((DerivedCategory.TStructure.t.truncLT (q + 1)).obj K)))).symm ≪≫
    asIso ((DerivedCategory.homologyFunctor C q).map
      ((DerivedCategory.TStructure.t.truncLTι (q + 1)).app K))

/-- The actual canonical single-degree truncation is isomorphic to the
single complex of its actual homology object. -/
def derivedSingleDegreeTruncationIsoSingle (K : DerivedCategory C) (q : ℤ) :
    derivedSingleDegreeTruncation K q ≅
      (DerivedCategory.singleFunctor C q).obj ((DerivedCategory.homologyFunctor C q).obj K) := by
  have : (derivedSingleDegreeTruncation K q).IsGE q := by
    dsimp [derivedSingleDegreeTruncation]
    infer_instance
  have : (derivedSingleDegreeTruncation K q).IsLE q := by
    dsimp [derivedSingleDegreeTruncation]
    infer_instance
  let hA := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (derivedSingleDegreeTruncation K q) q
  let A := Classical.choose hA
  let e := Classical.choice (Classical.choose_spec hA)
  let h : (DerivedCategory.homologyFunctor C q).obj (derivedSingleDegreeTruncation K q) ≅ A :=
    (DerivedCategory.homologyFunctor C q).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).app A
  exact e ≪≫ (DerivedCategory.singleFunctor C q).mapIso
    (h.symm ≪≫ derivedSingleDegreeTruncationHomologyIso K q)

end SGA.SGA2.ExposeI
