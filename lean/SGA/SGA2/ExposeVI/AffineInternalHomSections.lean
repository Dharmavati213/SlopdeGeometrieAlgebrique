/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.SheafTensorHom
import SGA.SGA2.ExposeVI.SchemeInternalHom
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Detecting local morphisms between actual affine module sheaves

A local morphism out of `M~` is determined by its values on the original
sections `M → Γ(M~, U)`. The proof checks equality on the principal-open
basis, where those sections are the actual module localization maps.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The actual internal Hom module of two scheme modules. -/
def schemeModuleInternalHom {X : Scheme.{u}} (F G : X.Modules) : X.Modules :=
  moduleSheafHom (Opens.grothendieckTopology X) (S := X.sheaf) F G

/-- An actual source isomorphism induces the contravariant internal-Hom isomorphism. -/
def schemeModuleInternalHomSourceIso {X : Scheme.{u}} {F F' : X.Modules}
    (e : F ≅ F') (G : X.Modules) :
    schemeModuleInternalHom F G ≅ schemeModuleInternalHom F' G where
  hom := moduleSheafHomPrecomp _ e.inv G
  inv := moduleSheafHomPrecomp _ e.hom G
  hom_inv_id := by
    ext U φ
    apply moduleLocalHom_ext
    intro V x
    change φ.val.app (op V) (e.inv.val.app (op V.left) (e.hom.val.app (op V.left) x)) =
      φ.val.app (op V) x
    have h := ConcreteCategory.congr_hom
      (congrArg (fun a : F ⟶ F ↦ a.val.app (op V.left)) e.hom_inv_id) x
    exact congrArg (φ.val.app (op V)) h
  inv_hom_id := by
    ext U φ
    apply moduleLocalHom_ext
    intro V x
    change φ.val.app (op V) (e.hom.val.app (op V.left) (e.inv.val.app (op V.left) x)) =
      φ.val.app (op V) x
    have h := ConcreteCategory.congr_hom
      (congrArg (fun a : F' ⟶ F' ↦ a.val.app (op V.left)) e.inv_hom_id) x
    exact congrArg (φ.val.app (op V)) h

/-- Internal Hom respects the original isomorphisms of its source and target modules. -/
def schemeModuleInternalHomIso {X : Scheme.{u}} {F F' G G' : X.Modules}
    (e : F ≅ F') (d : G ≅ G') :
    schemeModuleInternalHom F G ≅ schemeModuleInternalHom F' G' :=
  schemeModuleInternalHomSourceIso e G ≪≫
    (moduleSheafHomFunctor (Opens.grothendieckTopology X) (S := X.sheaf) F').mapIso d

variable {R : CommRingCat.{u}} (M N : ModuleCat.{u} R)

local instance (U : (Spec R).Opens) (V : Over U) :
    Module R (((Over.forget U).op ⋙ (tilde N).val.presheaf).obj (op V)) :=
  inferInstanceAs (Module R Γ(tilde N, V.left))

local instance (U : (Spec R).Opens) (V : Over U) :
    Module ((Spec R).presheaf.obj (op V.left))
      (((Over.forget U).op ⋙ (tilde N).val.presheaf).obj (op V)) :=
  inferInstanceAs (Module ((Spec R).presheaf.obj (op V.left)) Γ(tilde N, V.left))

/-- The original local linear map evaluated on the chosen open, restricted to `R`-scalars. -/
def affineLocalHomApp (U : (Spec R).Opens)
    (φ : Γ(schemeModuleInternalHom (tilde M) (tilde N), U)) :
    Γ(tilde M, U) →ₗ[R] Γ(tilde N, U) where
  toFun x := φ.val.app (op (Over.mk (𝟙 U))) x
  map_add' x y := map_add _ x y
  map_smul' r x := φ.property (Over.mk (𝟙 U))
    ((Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv r)) x

/-- Evaluation on the actual generating sections of an affine tilde sheaf. -/
def affineInternalHomEvaluation (U : (Spec R).Opens) :
    Γ(schemeModuleInternalHom (tilde M) (tilde N), U) →ₗ[R] (M →ₗ[R] Γ(tilde N, U)) where
  toFun φ := (affineLocalHomApp M N U φ).comp (tilde.toOpen M U).hom
  map_add' φ ψ := by ext m; rfl
  map_smul' r φ := by
    ext m
    change (((Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv r)) • φ).val.app
        (op (Over.mk (𝟙 U))) ((tilde.toOpen M U) m) =
      r • (φ.val.app (op (Over.mk (𝟙 U))) ((tilde.toOpen M U) m) : Γ(tilde N, U))
    rw [moduleLocalHom_smul_app]
    rfl

/-- Evaluation commutes with the actual open restrictions of source and coefficient sections. -/
theorem affineLocalHom_eval_restrict (U V : (Spec R).Opens) (i : V ⟶ U)
    (φ : Γ(schemeModuleInternalHom (tilde M) (tilde N), U)) (m : M) :
    (φ.val.app (op (Over.mk i))) ((tilde.toOpen M V) m) =
      (tilde N).val.map i.op ((affineInternalHomEvaluation M N U φ) m) := by
  have h := NatTrans.naturality_apply φ.val
    (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 U)).op ((tilde.toOpen M U) m)
  change φ.val.app (op (Over.mk i)) ((tilde M).val.map i.op ((tilde.toOpen M U) m)) = _ at h
  have ht := ConcreteCategory.congr_hom (tilde.toOpen_res M U V i) m
  exact (congrArg (φ.val.app (op (Over.mk i))) ht.symm).trans h

/-- A local map between affine tilde sheaves is determined by its values on the original module. -/
theorem affineInternalHomEvaluation_injective (U : (Spec R).Opens) :
    Function.Injective (affineInternalHomEvaluation M N U) := by
  intro φ ψ h
  apply moduleLocalHom_ext
  intro V x
  apply TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj (tilde N)).property
  intro p hp
  obtain ⟨W, ⟨_, ⟨f, rfl⟩, rfl⟩, hpW, hWV⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp V.left.2
  let i : PrimeSpectrum.basicOpen f ⟶ V.left := homOfLE hWV
  let j : PrimeSpectrum.basicOpen f ⟶ U := i ≫ V.hom
  refine ⟨PrimeSpectrum.basicOpen f, hWV, hpW, ?_⟩
  have hnφ := NatTrans.naturality_apply φ.val
    (Over.homMk i : Over.mk j ⟶ V).op x
  have hnψ := NatTrans.naturality_apply ψ.val
    (Over.homMk i : Over.mk j ⟶ V).op x
  change φ.val.app (op (Over.mk j)) ((tilde M).val.map i.op x) =
    (tilde N).val.map i.op (φ.val.app (op V) x) at hnφ
  change ψ.val.app (op (Over.mk j)) ((tilde M).val.map i.op x) =
    (tilde N).val.map i.op (ψ.val.app (op V) x) at hnψ
  change (tilde N).val.map i.op (φ.val.app (op V) x) =
    (tilde N).val.map i.op (ψ.val.app (op V) x)
  rw [← hnφ, ← hnψ]
  let aφ : Γ(tilde M, PrimeSpectrum.basicOpen f) →ₗ[R]
      Γ(tilde N, PrimeSpectrum.basicOpen f) :=
    { toFun y := φ.val.app (op (Over.mk j)) y
      map_add' y z := map_add _ y z
      map_smul' r y := φ.property (Over.mk j)
        ((Spec R).presheaf.map (PrimeSpectrum.basicOpen f).leTop.op ((Scheme.ΓSpecIso R).inv r)) y }
  let aψ : Γ(tilde M, PrimeSpectrum.basicOpen f) →ₗ[R]
      Γ(tilde N, PrimeSpectrum.basicOpen f) :=
    { toFun y := ψ.val.app (op (Over.mk j)) y
      map_add' y z := map_add _ y z
      map_smul' r y := ψ.property (Over.mk j)
        ((Spec R).presheaf.map (PrimeSpectrum.basicOpen f).leTop.op ((Scheme.ΓSpecIso R).inv r)) y }
  have ha : aφ = aψ := by
    apply IsLocalizedModule.ext (.powers f) (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom
      (IsLocalizedModule.map_units (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom)
    ext m
    change φ.val.app (op (Over.mk j)) ((tilde.toOpen M (PrimeSpectrum.basicOpen f)) m) =
      ψ.val.app (op (Over.mk j)) ((tilde.toOpen M (PrimeSpectrum.basicOpen f)) m)
    rw [affineLocalHom_eval_restrict M N U _ j φ,
      affineLocalHom_eval_restrict M N U _ j ψ, h]
  exact LinearMap.congr_fun ha ((tilde M).val.map i.op x)

/-- An original module map gives its genuine local sheaf morphism. -/
def affineHomSection (U : (Spec R).Opens) (f : M →ₗ[R] N) :
    Γ(schemeModuleInternalHom (tilde M) (tilde N), U) :=
  ⟨Functor.whiskerLeft (Over.forget U).op
      ((PresheafOfModules.toPresheaf _).map (tilde.map (ModuleCat.ofHom f)).val),
    fun V r x ↦ ((tilde.map (ModuleCat.ofHom f)).val.app (op V.left)).hom.map_smul r x⟩

/-- Evaluation of the actual tilde morphism is the original localized module map. -/
theorem affineHomSection_eval (U : (Spec R).Opens) (f : M →ₗ[R] N) :
    affineInternalHomEvaluation M N U (affineHomSection M N U f) =
      (tilde.toOpen N U).hom.comp f := by
  ext m
  exact ConcreteCategory.congr_hom (tilde.toOpen_map_app (ModuleCat.ofHom f) U) m

/-- These sections respect the actual restriction maps of the Hom module sheaf. -/
theorem affineHomSection_restrict {U V : (Spec R).Opens} (i : V ⟶ U) (f : M →ₗ[R] N) :
    (schemeModuleInternalHom (tilde M) (tilde N)).val.map i.op (affineHomSection M N U f) =
      affineHomSection M N V f := by
  apply moduleLocalHom_ext
  intro W x
  rfl

/-- The local tilde maps retain actual postcomposition of the original coefficient maps. -/
theorem affineHomSection_postcomp {P : ModuleCat.{u} R} (a : N ⟶ P)
    (U : (Spec R).Opens) (h : M →ₗ[R] N) :
    moduleLocalHomPostcomp (tilde M).val (tilde.map a).val U (affineHomSection M N U h) =
      affineHomSection M P U (a.hom.comp h) := by
  apply moduleLocalHom_ext
  intro V x
  change (tilde.map a).val.app (op V.left)
      ((tilde.map (ModuleCat.ofHom h)).val.app (op V.left) x) =
    (tilde.map (ModuleCat.ofHom h ≫ a)).val.app (op V.left) x
  rw [tilde.map_comp]
  rfl

/-- The local tilde maps also retain actual precomposition in the source module. -/
theorem affineHomSection_precomp {P : ModuleCat.{u} R} (a : P ⟶ M)
    (U : (Spec R).Opens) (h : M →ₗ[R] N) :
    moduleLocalHomPrecomp (tilde.map a).val (tilde N).val U (affineHomSection M N U h) =
      affineHomSection P N U (h.comp a.hom) := by
  apply moduleLocalHom_ext
  intro V x
  change (tilde.map (ModuleCat.ofHom h)).val.app (op V.left)
      ((tilde.map a).val.app (op V.left) x) =
    (tilde.map (a ≫ ModuleCat.ofHom h)).val.app (op V.left) x
  rw [tilde.map_comp]
  rfl

/-- Evaluation of local Hom commutes with actual coefficient-section restriction. -/
theorem affineInternalHomEvaluation_restrict {U V : (Spec R).Opens} (i : V ⟶ U)
    (φ : Γ(schemeModuleInternalHom (tilde M) (tilde N), U)) :
    affineInternalHomEvaluation M N V
        ((schemeModuleInternalHom (tilde M) (tilde N)).val.map i.op φ) =
      ((modulesSpecToSheaf.obj (tilde N)).presheaf.map i.op).hom.comp
        (affineInternalHomEvaluation M N U φ) := by
  ext m
  change (moduleLocalHomRestrict (tilde M).val (tilde N).val i φ).val.app
      (op (Over.mk (𝟙 V))) ((tilde.toOpen M V) m) = _
  rw [moduleLocalHomRestrict_eval]
  exact affineLocalHom_eval_restrict M N U V i φ m

/-- Global local-linear maps, evaluated back in the original affine coefficient modules. -/
def affineGlobalHomEvaluation :
    Γ(schemeModuleInternalHom (tilde M) (tilde N), ⊤) →ₗ[R] (M →ₗ[R] N) where
  toFun φ := (tilde.isoTop N).inv.hom.comp (affineInternalHomEvaluation M N ⊤ φ)
  map_add' φ ψ := by
    ext m
    change (tilde.isoTop N).inv ((affineInternalHomEvaluation M N ⊤ (φ + ψ)) m) = _
    rw [map_add, LinearMap.add_apply, map_add]
    rfl
  map_smul' r φ := by
    ext m
    change (tilde.isoTop N).inv ((affineInternalHomEvaluation M N ⊤ (r • φ)) m) = _
    rw [map_smul, LinearMap.smul_apply, (tilde.isoTop N).inv.hom.map_smul]
    rfl

/-- Global evaluation of the genuine tilde map recovers its original coefficient map. -/
theorem affineGlobalHomEvaluation_section (f : M →ₗ[R] N) :
    affineGlobalHomEvaluation M N (affineHomSection M N ⊤ f) = f := by
  change (tilde.isoTop N).inv.hom.comp
    (affineInternalHomEvaluation M N ⊤ (affineHomSection M N ⊤ f)) = f
  rw [affineHomSection_eval]
  ext m
  exact (tilde.isoTop N).hom_inv_id_apply (f m)

/-- Global linear Hom is exactly Hom of the original affine coefficient modules. -/
def affineGlobalHomEquiv :
    (M →ₗ[R] N) ≃ₗ[R] Γ(schemeModuleInternalHom (tilde M) (tilde N), ⊤) :=
  (LinearEquiv.ofBijective (affineGlobalHomEvaluation M N)
    ⟨by
      intro φ ψ h
      apply affineInternalHomEvaluation_injective M N ⊤
      ext m
      apply (tilde.isoTop N).toLinearEquiv.symm.injective
      exact LinearMap.congr_fun h m,
    fun f ↦ ⟨affineHomSection M N ⊤ f, affineGlobalHomEvaluation_section M N f⟩⟩).symm

/-- The global equivalence is the original tilde map on every coefficient morphism. -/
@[simp]
theorem affineGlobalHomEquiv_apply (f : M →ₗ[R] N) :
    affineGlobalHomEquiv M N f = affineHomSection M N ⊤ f := by
  apply (affineGlobalHomEquiv M N).symm.injective
  change (affineGlobalHomEquiv M N).symm (affineGlobalHomEquiv M N f) =
    affineGlobalHomEvaluation M N (affineHomSection M N ⊤ f)
  rw [LinearEquiv.symm_apply_apply, affineGlobalHomEvaluation_section]

/-- Global module sheaf morphisms out of a tilde sheaf are determined by the original generators. -/
theorem affineTildeMorphism_ext (P : ModuleCat.{u} R) (G : (Spec R).Modules)
    {a b : tilde P ⟶ G}
    (h : ∀ p : P, a.val.app (op ⊤) ((tilde.toOpen P ⊤) p) =
      b.val.app (op ⊤) ((tilde.toOpen P ⊤) p)) : a = b := by
  apply (tilde.adjunction (R := R)).homEquiv P G |>.injective
  ext p
  exact h p

end SGA.SGA2.ExposeVI
