/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ModulesHomExact
import SGA.Foundations.Analytic.ModulesStalkFree
import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Hom sheaves from free module sheaves

The Hom sheaf from the structure sheaf identifies with its target. This comparison
is compatible with the canonical map on stalks.

Adopted from the unmerged branch `codex/foundations-missing-inputs` (commit `c65c9a0`, file
`ModuleHomFree.lean`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}} (N : X.Modules)

/-- A section of `N` on `U` defines a local homomorphism from the structure sheaf. -/
def HomOn.fromUnitSection (U : Opens X) (s : N.presheaf.obj (op U)) :
    HomOn (SheafOfModules.unit X.ringCatSheaf) N U where
  app V hV := (LinearMap.ringLmapEquivSelf (X.presheaf.obj (op V))
    (X.presheaf.obj (op V)) (N.presheaf.obj (op V))).symm
      (N.presheaf.map (homOfLE hV).op s)
  naturality {V W} hWV hV r := by
    change @HSMul.hSMul (X.presheaf.obj (op W)) (N.presheaf.obj (op W))
      (N.presheaf.obj (op W)) inferInstance (X.presheaf.map (homOfLE hWV).op r)
      (N.presheaf.map (homOfLE (hWV.trans hV)).op s) =
      N.presheaf.map (homOfLE hWV).op
        (@HSMul.hSMul (X.presheaf.obj (op V)) (N.presheaf.obj (op V))
          (N.presheaf.obj (op V)) inferInstance r (N.presheaf.map (homOfLE hV).op s))
    rw [Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

/-- Maps from the structure sheaf on an open set are determined by the image of one. -/
def HomOn.unitSectionEquiv (U : Opens X) :
    HomOn (SheafOfModules.unit X.ringCatSheaf) N U ≃ₗ[X.presheaf.obj (op U)]
      N.presheaf.obj (op U) where
  toFun φ := φ.app U le_rfl (1 : X.presheaf.obj (op U))
  invFun := HomOn.fromUnitSection N U
  left_inv φ := by
    apply HomOn.ext
    funext V hV
    apply LinearMap.ext
    intro r
    have h := φ.naturality hV le_rfl (1 : X.presheaf.obj (op U))
    have h1 : (presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).map
        (homOfLE hV).op (1 : X.presheaf.obj (op U)) = (1 : X.presheaf.obj (op V)) :=
      map_one (X.presheaf.map (homOfLE hV).op).hom
    rw [h1] at h
    change @HSMul.hSMul (X.presheaf.obj (op V)) (N.presheaf.obj (op V))
      (N.presheaf.obj (op V)) inferInstance r
      (N.presheaf.map (homOfLE hV).op (φ.app U le_rfl (1 : X.presheaf.obj (op U)))) = φ.app V hV r
    rw [← h, ← LinearMap.map_smul]
    congr 1
    exact mul_one (show X.presheaf.obj (op V) from r)
  right_inv s := by
    change (1 : X.presheaf.obj (op U)) • N.presheaf.map (homOfLE le_rfl).op s = s
    simp
  map_add' φ ψ := rfl
  map_smul' r φ := by
    rw [HomOn.smul_app, LinearMap.smul_apply]
    simp

/-- The Hom sheaf from the structure sheaf is canonically its target. -/
def sheafHomUnitIso : sheafHom (SheafOfModules.unit X.ringCatSheaf) N ≅ N :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ (HomOn.unitSectionEquiv N U.unop).toModuleIso)
      (fun {U V} i ↦ by
        ext φ
        have h := φ.naturality i.unop.le le_rfl (1 : X.presheaf.obj U)
        have h1 : (presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).map i
            (1 : X.presheaf.obj U) = (1 : X.presheaf.obj V) :=
          map_one (X.presheaf.map i).hom
        change φ.app V.unop i.unop.le (1 : X.presheaf.obj V) =
          N.presheaf.map i (φ.app U.unop le_rfl (1 : X.presheaf.obj U))
        have hi : (homOfLE i.unop.le).op = i := Subsingleton.elim _ _
        rw [hi] at h
        erw [h1] at h
        exact h))

@[simp] lemma sheafHomUnitIso_hom_app (U : Opens X)
    (φ : HomOn (SheafOfModules.unit X.ringCatSheaf) N U) :
    (sheafHomUnitIso N).hom.val.app (op U) φ = φ.app U le_rfl (1 : X.presheaf.obj (op U)) := rfl

/-- Evaluation at one identifies homomorphisms from the stalk of the structure sheaf
with the target stalk. -/
def homStalkUnitTargetEquiv (x : X) :
    ((presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).stalk x →ₗ[X.presheaf.stalk x]
      N.presheaf.stalk x) ≃ₗ[X.presheaf.stalk x] N.presheaf.stalk x :=
  (LinearEquiv.arrowCongr (stalkUnitLinearEquiv x)
    (LinearEquiv.refl (X.presheaf.stalk x) (N.presheaf.stalk x))).trans
      (LinearMap.ringLmapEquivSelf (X.presheaf.stalk x) (X.presheaf.stalk x) (N.presheaf.stalk x))

lemma homStalkUnitTargetEquiv_homStalkMap (x : X)
    (s : (sheafHom (SheafOfModules.unit X.ringCatSheaf) N).presheaf.stalk x) :
    homStalkUnitTargetEquiv N x (homStalkMap (SheafOfModules.unit X.ringCatSheaf) N x s) =
      stalkMap (sheafHomUnitIso N).hom x s := by
  obtain ⟨U, hx, φ, rfl⟩ :=
    (sheafHom (SheafOfModules.unit X.ringCatSheaf) N).presheaf.exists_germ_eq s
  rw [homStalkMap_germ, stalkMap_germ, sheafHomUnitIso_hom_app]
  change φ.stalkMap x hx ((stalkUnitLinearEquiv x).symm 1) = _
  have h1 : (stalkUnitLinearEquiv x).symm 1 =
      (presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).germ U x hx
        (1 : X.presheaf.obj (op U)) := by
    apply (stalkUnitLinearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, stalkUnitLinearEquiv_germ, map_one]
  rw [h1, HomOn.stalkMap_germ φ x hx le_rfl]

/-- The canonical Hom-stalk comparison is bijective when the source is the structure
sheaf. -/
theorem bijective_homStalkMap_unit (x : X) :
    Function.Bijective (homStalkMap (SheafOfModules.unit X.ringCatSheaf) N x) := by
  let e := homStalkUnitTargetEquiv N x
  have hcomp : Function.Bijective
      (e ∘ homStalkMap (SheafOfModules.unit X.ringCatSheaf) N x) := by
    have he : e ∘ homStalkMap (SheafOfModules.unit X.ringCatSheaf) N x =
        stalkMap (sheafHomUnitIso N).hom x := funext (homStalkUnitTargetEquiv_homStalkMap N x)
    rw [he]
    exact ((stalkFunctor x).mapIso (sheafHomUnitIso N)).toLinearEquiv.bijective
  refine ⟨fun a b hab ↦ hcomp.injective (congrArg e hab), fun t ↦ ?_⟩
  obtain ⟨s, hs⟩ := hcomp.surjective (e t)
  exact ⟨s, e.injective hs⟩

/-- A local map from a free module sheaf is a family of local maps from its summands. -/
def homOnFreeEquiv (I : Type u) (U : Opens X) :
    HomOn (SheafOfModules.free (R := X.ringCatSheaf) I) N U ≃ₗ[X.presheaf.obj (op U)]
      (I → HomOn (SheafOfModules.unit X.ringCatSheaf) N U) := by
  let L : HomOn (SheafOfModules.free (R := X.ringCatSheaf) I) N U →ₗ[X.presheaf.obj (op U)]
      (I → HomOn (SheafOfModules.unit X.ringCatSheaf) N U) := {
    toFun := fun φ i ↦ φ.precomp (SheafOfModules.ιFree i)
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun r φ ↦ funext fun i ↦ HomOn.precomp_smul _ r φ }
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  let hc := isColimitOfHasCoproductOfPreservesColimit F
    (fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf)
  apply LinearEquiv.ofBijective L
  constructor
  · intro φ ψ h
    apply (homOnOverEquiv U).injective
    apply hc.hom_ext
    intro j
    change (SheafOfModules.ιFree j.as).over U ≫ homOnOverEquiv U φ =
      (SheafOfModules.ιFree j.as).over U ≫ homOnOverEquiv U ψ
    rw [← homOnOverEquiv_precomp, ← homOnOverEquiv_precomp]
    exact congrArg (homOnOverEquiv U) (congrFun h j.as)
  · intro ψ
    let s := Cofan.mk (N.over U) (fun i : I ↦ homOnOverEquiv U (ψ i))
    refine ⟨(homOnOverEquiv U).symm (hc.desc s), ?_⟩
    funext i
    apply (homOnOverEquiv U).injective
    change homOnOverEquiv U (((homOnOverEquiv U).symm (hc.desc s)).precomp
      (SheafOfModules.ιFree i)) = _
    rw [homOnOverEquiv_precomp]
    erw [Equiv.apply_symm_apply]
    exact hc.fac s ⟨i⟩

@[simp] lemma homOnFreeEquiv_apply (I : Type u) (U : Opens X)
    (φ : HomOn (SheafOfModules.free (R := X.ringCatSheaf) I) N U) (i : I) :
    homOnFreeEquiv N I U φ i = φ.precomp (SheafOfModules.ιFree i) := rfl

/-- Internal Hom carries a free source to the product of the Hom sheaves of its summands. -/
def sheafHomFreeFan (I : Type u) :
    Fan (fun _ : I ↦ sheafHom (SheafOfModules.unit X.ringCatSheaf) N) :=
  Fan.mk (sheafHom (SheafOfModules.free (R := X.ringCatSheaf) I) N)
    (fun i ↦ sheafHomPrecomp (SheafOfModules.ιFree i) N)

/-- The preceding Hom fan is a product, including for an infinite free source. -/
def sheafHomFreeFanIsLimit (I : Type u) : IsLimit (sheafHomFreeFan N I) := by
  apply isLimitOfReflects (SheafOfModules.forget X.ringCatSheaf)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  let e := (homOnFreeEquiv N I U.unop).toModuleIso
  refine IsLimit.ofIsoLimit
    (ModuleCat.productConeIsLimit (fun _ : I ↦ ModuleCat.of (X.presheaf.obj (op U.unop))
      (HomOn (SheafOfModules.unit X.ringCatSheaf) N U.unop)))
    (Cone.ext e.symm ?_)
  intro i
  ext φ
  change φ i.as = (e.inv φ).precomp (SheafOfModules.ιFree i.as)
  exact (congrFun ((homOnFreeEquiv N I U.unop).apply_symm_apply φ) i.as).symm

/-- Internal Hom of a free source is the product of copies of the target's Hom from the unit. -/
def sheafHomFreePiIso (I : Type u) :
    sheafHom (SheafOfModules.free (R := X.ringCatSheaf) I) N ≅
      ∏ᶜ (fun _ : I ↦ sheafHom (SheafOfModules.unit X.ringCatSheaf) N) :=
  (sheafHomFreeFanIsLimit N I).conePointUniqueUpToIso (limit.isLimit _)

/-- At a stalk, Hom from a finite free source is the finite product of the stalks of
the Hom sheaves from its summands. -/
def stalkHomFreePiIso (x : X) (I : Type u) [Finite I] :
    (stalkFunctor x).obj (sheafHom (SheafOfModules.free (R := X.ringCatSheaf) I) N) ≅
      ModuleCat.of (X.presheaf.stalk x)
        (I → (stalkFunctor x).obj (sheafHom (SheafOfModules.unit X.ringCatSheaf) N)) :=
  (isLimitFanMkObjOfIsLimit (stalkFunctor x)
    (fun _ : I ↦ sheafHom (SheafOfModules.unit X.ringCatSheaf) N)
    (fun i ↦ sheafHomPrecomp (SheafOfModules.ιFree i) N)
    (sheafHomFreeFanIsLimit N I)).conePointUniqueUpToIso
      (ModuleCat.productConeIsLimit (fun _ : I ↦
        (stalkFunctor x).obj (sheafHom (SheafOfModules.unit X.ringCatSheaf) N)))

lemma stalkHomFreePiIso_hom_apply (x : X) (I : Type u) [Finite I]
    (s : (sheafHom (SheafOfModules.free (R := X.ringCatSheaf) I) N).presheaf.stalk x) (i : I) :
    (stalkHomFreePiIso N x I).hom s i =
      stalkMap (sheafHomPrecomp (SheafOfModules.ιFree i) N) x s := by
  let h := isLimitFanMkObjOfIsLimit (stalkFunctor x)
    (fun _ : I ↦ sheafHom (SheafOfModules.unit X.ringCatSheaf) N)
    (fun i ↦ sheafHomPrecomp (SheafOfModules.ιFree i) N) (sheafHomFreeFanIsLimit N I)
  have he := h.conePointUniqueUpToIso_hom_comp
    (ModuleCat.productConeIsLimit (fun _ : I ↦
      (stalkFunctor x).obj (sheafHom (SheafOfModules.unit X.ringCatSheaf) N))) ⟨i⟩
  exact congrArg (fun q ↦ q s) he

/-- The canonical Hom-stalk comparison is bijective for a finite free source. -/
theorem bijective_homStalkMap_free (x : X) (I : Type u) [Finite I] :
    Function.Bijective (homStalkMap (SheafOfModules.free (R := X.ringCatSheaf) I) N x) := by
  let e := stalkHomFreePiIso N x I
  constructor
  · intro s t hst
    apply e.toLinearEquiv.injective
    funext i
    apply (bijective_homStalkMap_unit N x).injective
    change homStalkMap _ N x ((stalkHomFreePiIso N x I).hom s i) =
      homStalkMap _ N x ((stalkHomFreePiIso N x I).hom t i)
    erw [stalkHomFreePiIso_hom_apply, stalkHomFreePiIso_hom_apply,
      homStalkMap_precomp, homStalkMap_precomp, hst]
  · intro t
    choose s hs using fun i : I ↦ (bijective_homStalkMap_unit N x).surjective
      (t.comp (stalkMap (SheafOfModules.ιFree i) x))
    let s' := e.inv s
    have hs' (i : I) : stalkMap (sheafHomPrecomp (SheafOfModules.ιFree i) N) x s' = s i := by
      rw [← stalkHomFreePiIso_hom_apply]
      exact congrFun (e.inv_hom_id_apply s) i
    refine ⟨s', ?_⟩
    have h : ModuleCat.ofHom (homStalkMap (SheafOfModules.free (R := X.ringCatSheaf) I) N x s') =
        ModuleCat.ofHom t := by
      apply (isColimitOfPreserves (stalkFunctor x) (SheafOfModules.isColimitFreeCofan I)).hom_ext
      intro i
      apply ModuleCat.hom_ext
      change (homStalkMap (SheafOfModules.free (R := X.ringCatSheaf) I) N x s').comp
        (stalkMap (SheafOfModules.ιFree i.as) x) = t.comp (stalkMap (SheafOfModules.ιFree i.as) x)
      rw [← homStalkMap_precomp, hs']
      exact hs i.as
    exact congrArg ModuleCat.Hom.hom h

end AlgebraicGeometry.LocallyRingedSpace.Modules
