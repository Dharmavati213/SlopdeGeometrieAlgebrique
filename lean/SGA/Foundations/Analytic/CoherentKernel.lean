/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.CoherentGenerators
import SGA.Foundations.Analytic.OkaRelations
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Stalks of relation sheaves

Let `φ : 𝒪_X^ι ⟶ 𝒪_X` be a morphism from a finite free module on a locally ringed space. The
stalk at `x` of `ker φ` is the module of relations `∑ᵢ aᵢ φᵢ = 0` between the coefficients
`φᵢ ∈ 𝒪_{X,x}` of `φ`
(`AlgebraicGeometry.LocallyRingedSpace.Modules.relationKernelStalkLinearEquiv`), and these
coefficients are the germs of the global sections `φ(eᵢ)` (`relationStalkCoefficients_eq_germ`).
This identifies the relation sheaf of `SheafOfModules` with the explicit relation modules
`AnalyticGeometry.relationModule` of Oka's theorem.

Adopted from the unmerged branch `codex/foundations-missing-inputs` (commit `c65c9a0`, file
`CoherenceKernel.lean`). References: Grauert–Remmert, *Coherent analytic sheaves*, 2.5;
Stacks Project, Tag 01BU.
-/

noncomputable section

-- stalks of `SheafOfModules` carry module structures that are only defeq after unfolding
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}} {ι : Type u} [Fintype ι]

/-- Finite-coordinate form of the free stalk comparison. -/
def stalkFiniteFreeLinearEquiv (x : X) :
    (stalkFunctor x).obj (SheafOfModules.free (R := X.ringCatSheaf) ι) ≃ₗ[X.presheaf.stalk x]
      (ι → X.presheaf.stalk x) :=
  (stalkFreeLinearEquiv x ι).trans (Finsupp.linearEquivFunOnFinite _ _ _)

variable (φ : SheafOfModules.free (R := X.ringCatSheaf) ι ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- The linear row map induced by a finite-free sheaf morphism at a point. -/
def relationStalkRow (x : X) : (ι → X.presheaf.stalk x) →ₗ[X.presheaf.stalk x]
    X.presheaf.stalk x :=
  (stalkUnitLinearEquiv x).toLinearMap ∘ₗ stalkMap φ x ∘ₗ
    (stalkFiniteFreeLinearEquiv (ι := ι) x).symm.toLinearMap

open Classical in
/-- The coefficients of a finite-free sheaf morphism in the local ring. -/
def relationStalkCoefficients (x : X) (i : ι) : X.presheaf.stalk x :=
  relationStalkRow φ x (Pi.single i 1)

open Classical in
/-- The finite free stalk coordinates of the `i`-th unit germ are the `i`-th standard
basis vector. -/
lemma stalkFiniteFreeLinearEquiv_ι_one (x : X) (i : ι) :
    stalkFiniteFreeLinearEquiv x
      (stalkMap (SheafOfModules.ιFree (R := X.ringCatSheaf) i) x
        ((presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).germ ⊤ x (by trivial)
          (1 : X.presheaf.obj (op ⊤)))) = Pi.single i 1 := by
  change (Finsupp.linearEquivFunOnFinite (X.presheaf.stalk x) (X.presheaf.stalk x) ι)
    (stalkFreeLinearEquiv x ι ((stalkFunctor x).map (SheafOfModules.ιFree i) _)) = _
  rw [stalkFreeLinearEquiv_map_ιFree, stalkUnitLinearEquiv_germ]
  have h1 : X.presheaf.germ ⊤ x (by trivial) (1 : X.presheaf.obj (op ⊤)) = 1 :=
    map_one (X.presheaf.germ ⊤ x (by trivial)).hom
  rw [h1]
  ext k
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The local coefficients are exactly the germs of the global coefficients of the
free sheaf morphism. -/
lemma relationStalkCoefficients_eq_germ (x : X) (i : ι) :
    relationStalkCoefficients φ x i = X.presheaf.germ ⊤ x (by trivial)
      (((SheafOfModules.unit X.ringCatSheaf).freeHomEquiv φ i).val (op ⊤)) := by
  classical
  let s := (SheafOfModules.unit X.ringCatSheaf).freeHomEquiv φ i
  let t := (presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).germ ⊤ x (by trivial)
    (1 : X.presheaf.obj (op ⊤))
  have he : (stalkFiniteFreeLinearEquiv (ι := ι) x).symm (Pi.single i 1) =
      stalkMap (SheafOfModules.ιFree i) x t := by
    apply (stalkFiniteFreeLinearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, stalkFiniteFreeLinearEquiv_ι_one]
  have hcomp : SheafOfModules.ιFree i ≫ φ =
      (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm s :=
    (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply φ i).symm
  change stalkUnitLinearEquiv x (stalkMap φ x
    ((stalkFiniteFreeLinearEquiv x).symm (Pi.single i 1))) = _
  rw [he]
  have hm : stalkMap φ x (stalkMap (SheafOfModules.ιFree i) x t) =
      globalSectionGerm s x := by
    change (((stalkFunctor x).map (SheafOfModules.ιFree i)) ≫
      (stalkFunctor x).map φ) t = _
    rw [← Functor.map_comp, hcomp]
    exact stalkMap_unitHomEquiv_symm_one s x
  rw [hm]
  exact stalkUnitLinearEquiv_germ x ⊤ (by trivial) (s.val (op ⊤))

/-- The row map is the linear combination map of its coefficients. -/
lemma relationStalkRow_eq_linearCombination (x : X) :
    relationStalkRow φ x = Fintype.linearCombination (X.presheaf.stalk x)
      (relationStalkCoefficients φ x) := by
  classical
  apply LinearMap.ext
  intro a
  have ha : ∑ i, a i • Pi.single i (1 : X.presheaf.stalk x) = a := by
    ext i
    simp [Pi.single_apply, mul_ite]
  calc
    relationStalkRow φ x a = relationStalkRow φ x (∑ i, a i • Pi.single i 1) := congrArg _ ha.symm
    _ = ∑ i, a i • relationStalkCoefficients φ x i := by simp [relationStalkCoefficients]
    _ = _ := rfl

/-- Changing from free-stalk coordinates to ordinary vectors identifies the concrete
kernel with the relation module. -/
def relationStalkKerEquiv (x : X) :
    (stalkMap φ x).ker ≃ₗ[X.presheaf.stalk x]
      AnalyticGeometry.relationModule (relationStalkCoefficients φ x) where
  toFun a := ⟨stalkFiniteFreeLinearEquiv x a.val, by
    change Fintype.linearCombination _ _ (stalkFiniteFreeLinearEquiv x a.val) = 0
    rw [← relationStalkRow_eq_linearCombination]
    change stalkUnitLinearEquiv x
      (stalkMap φ x ((stalkFiniteFreeLinearEquiv x).symm
        (stalkFiniteFreeLinearEquiv x a.val))) = 0
    rw [LinearEquiv.symm_apply_apply, a.2, map_zero]⟩
  invFun a := ⟨(stalkFiniteFreeLinearEquiv x).symm a.val, by
    apply (stalkUnitLinearEquiv x).injective
    change relationStalkRow φ x a.val = (stalkUnitLinearEquiv x) 0
    rw [relationStalkRow_eq_linearCombination, map_zero]
    exact a.2⟩
  left_inv a := Subtype.ext (LinearEquiv.symm_apply_apply _ _)
  right_inv a := Subtype.ext (LinearEquiv.apply_symm_apply _ _)
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext (map_smul _ _ _)

/-- The actual stalk of a relation-kernel sheaf is the explicit local relation module. -/
def relationKernelStalkLinearEquiv (x : X) :
    (stalkFunctor x).obj (kernel φ) ≃ₗ[X.presheaf.stalk x]
      AnalyticGeometry.relationModule (relationStalkCoefficients φ x) :=
  ((PreservesKernel.iso (stalkFunctor x) φ).toLinearEquiv).trans
    (((ModuleCat.kernelIsoKer ((stalkFunctor x).map φ)).toLinearEquiv).trans
      (relationStalkKerEquiv φ x))

end AlgebraicGeometry.LocallyRingedSpace.Modules
