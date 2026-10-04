/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ModulesStalk
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.JacobsonSpace

/-!
# Exactness of module sheaves on stalks; flat inverse images are exact

Exactness of sheaves of modules on a locally ringed space can be tested on stalks
(`exact_iff_stalkFunctor_map_exact`; a module sheaf is zero iff all its stalks are,
`isZero_iff_stalkFunctor_obj_isZero`). Combined with the stalk formula for inverse images
(`pullbackStalkIso`, `SGA.Foundations.Analytic.ModulesStalk`), the inverse image `f^*` along a
morphism whose maps on stalks are flat is exact (`exact_pullback_of_flat_stalkMap`,
`preservesFiniteLimits_pullback_of_flat_stalkMap`; EGA 0_I 6.7.1, Stacks Project, Tag 02N4).
This gives the exactness of `F ↦ F^an` (SGA 1 XII.1.3.1, Serre, GAGA, §2), proved for `X^an` in
`SGA.SGA1.ExposeXII.GAGAModules`. On a space whose underlying space is Jacobson, a sheaf of modules
is zero as soon as its stalks at the closed points vanish (`isZero_of_forall_closedPoints`; the
support of a section is locally closed).

Adopted from the unmerged branch `codex/foundations-missing-inputs` (commit `c65c9a0`, file
`ModuleExactness.lean`), without its part on the affine analytification of a presentation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X Y : LocallyRingedSpace.{u}}

instance isLeftAdjoint_pullback (f : X ⟶ Y) : (pullback f).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction f).isLeftAdjoint

instance isRightAdjoint_pushforward (f : X ⟶ Y) : (pushforward f).IsRightAdjoint :=
  (pullbackPushforwardAdjunction f).isRightAdjoint

instance additive_pullback (f : X ⟶ Y) : (pullback f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (pullback f)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Forgetting the local-ring action on a module stalk gives the stalk of the underlying
sheaf of abelian groups. -/
def stalkFunctorForgetIso (x : X) :
    stalkFunctor x ⋙ forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toSheafedSpace ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
  Iso.refl _

instance preservesFiniteLimits_stalkFunctor (x : X) : PreservesFiniteLimits (stalkFunctor x) := by
  have : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf) := inferInstance
  have : PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toSheafedSpace ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := inferInstance
  have : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X.toSheafedSpace ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits
      (stalkFunctor x ⋙ forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}) :=
    preservesFiniteLimits_of_natIso (stalkFunctorForgetIso x).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u})

/-- A module sheaf vanishes if and only if every stalk vanishes. -/
theorem isZero_iff_stalkFunctor_obj_isZero (M : X.Modules) :
    IsZero M ↔ ∀ x : X, IsZero ((stalkFunctor x).obj M) := by
  refine ⟨fun h x ↦ (stalkFunctor x).map_isZero h, fun h ↦ ?_⟩
  have hz : IsZero ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj M) := by
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro x
    exact (forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}).map_isZero (h x)
  rw [IsZero.iff_id_eq_zero] at hz ⊢
  apply (SheafOfModules.toSheaf.{u} X.ringCatSheaf).zero_of_map_zero
  simpa using hz

/-- Exactness of module sheaves can be checked on their modules of germs. -/
theorem exact_iff_stalkFunctor_map_exact (C : ShortComplex X.Modules) :
    C.Exact ↔ ∀ x : X, (C.map (stalkFunctor x)).Exact := by
  refine ⟨fun h x ↦ h.map (stalkFunctor x), fun h ↦ ?_⟩
  simp_rw [ShortComplex.exact_iff_isZero_homology] at h
  rw [ShortComplex.exact_iff_isZero_homology, isZero_iff_stalkFunctor_obj_isZero]
  intro x
  exact (h x).of_iso (ShortComplex.mapHomologyIso C (stalkFunctor x)).symm

/-- Exactness on sections over every open set implies exactness of module sheaves. -/
theorem exact_of_sections (C : ShortComplex X.Modules)
    (hC : ∀ U : TopologicalSpace.Opens X,
      Function.Exact (C.f.val.app (.op U)) (C.g.val.app (.op U))) : C.Exact := by
  apply (exact_iff_stalkFunctor_map_exact C).mpr
  intro x
  rw [ShortComplex.moduleCat_exact_iff]
  intro m hm
  change stalkMap C.g x m = 0 at hm
  obtain ⟨U, hxU, m, rfl⟩ := C.X₂.presheaf.exists_germ_eq m
  rw [stalkMap_germ] at hm
  obtain ⟨V, hxV, i, j, hv⟩ := C.X₃.presheaf.germ_eq x hxU hxU
    (C.g.val.app (.op U) m) 0 (by simpa using hm)
  have hz : C.g.val.app (.op V) (C.X₂.presheaf.map i.op m) = 0 := by
    erw [PresheafOfModules.naturality_apply]
    change C.X₃.presheaf.map i.op (C.g.val.app (.op U) m) = 0
    simpa only [map_zero] using hv
  obtain ⟨n, hn⟩ := (hC V _).mp hz
  refine ⟨C.X₁.presheaf.germ V x hxV n, ?_⟩
  change stalkMap C.f x (C.X₁.presheaf.germ V x hxV n) = C.X₂.presheaf.germ U x hxU m
  rw [stalkMap_germ, hn, C.X₂.presheaf.germ_res_apply]

/-- Inverse image preserves exact complexes of module sheaves if all its stalk maps
are flat. -/
theorem exact_pullback_of_flat_stalkMap (f : X ⟶ Y)
    (hf : ∀ x : X, (f.stalkMap x).hom.Flat) (C : ShortComplex Y.Modules) (hC : C.Exact) :
    (C.map (pullback f)).Exact := by
  apply (exact_iff_stalkFunctor_map_exact _).mpr
  intro x
  have : PreservesFiniteLimits (ModuleCat.extendScalars (f.stalkMap x).hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (hf x)
  have h := ((exact_iff_stalkFunctor_map_exact C).mp hC (f.base x)).map
    (ModuleCat.extendScalars (f.stalkMap x).hom)
  exact ShortComplex.exact_of_iso (C.mapNatIso (pullbackStalkIso x f)).symm h

/-- Flat inverse image preserves kernels and cokernels of module sheaves. -/
theorem preservesHomology_pullback_of_flat_stalkMap (f : X ⟶ Y)
    (hf : ∀ x : X, (f.stalkMap x).hom.Flat) : (pullback f).PreservesHomology :=
  (pullback f).preservesHomology_of_map_exact (exact_pullback_of_flat_stalkMap f hf)

/-- Flat inverse image preserves finite limits of module sheaves. -/
theorem preservesFiniteLimits_pullback_of_flat_stalkMap (f : X ⟶ Y)
    (hf : ∀ x : X, (f.stalkMap x).hom.Flat) : PreservesFiniteLimits (pullback f) := by
  have := preservesHomology_pullback_of_flat_stalkMap f hf
  exact (pullback f).preservesFiniteLimits_of_preservesHomology

section Jacobson

/-- On a locally ringed space whose underlying space is Jacobson, a sheaf of modules whose stalks
at all closed points vanish is zero (the support of a section over an open `U` is closed in `U`,
hence locally closed in `X`, so it contains a closed point of `X` if it is nonempty). -/
theorem isZero_of_forall_closedPoints [JacobsonSpace X] (M : X.Modules)
    (h : ∀ x ∈ closedPoints X, IsZero ((stalkFunctor x).obj M)) : IsZero M := by
  rw [isZero_iff_stalkFunctor_obj_isZero]
  intro x
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun a b ↦ ?_⟩
  suffices H : ∀ m : M.presheaf.stalk x, m = 0 by rw [H a, H b]
  intro m
  obtain ⟨U, hxU, s, rfl⟩ := M.presheaf.exists_germ_eq m
  by_contra hne
  -- the support of `s` in `U` is closed in `U`, hence locally closed in `X`
  let Z : Set X := {y | ∃ hy : y ∈ U, M.presheaf.germ U y hy s ≠ 0}
  have hZ : IsLocallyClosed Z := by
    refine ⟨U.carrier, {y | ∃ hy : y ∈ U, M.presheaf.germ U y hy s ≠ 0} ∪ U.carrierᶜ, U.2,
      ?_, ?_⟩
    · rw [← isOpen_compl_iff, Set.compl_union, compl_compl]
      rw [isOpen_iff_forall_mem_open]
      rintro y ⟨hy0, hyU⟩
      have hy0' : M.presheaf.germ U y hyU s = M.presheaf.germ U y hyU 0 := by
        rw [map_zero]
        by_contra hc
        exact hy0 ⟨hyU, hc⟩
      obtain ⟨V, hyV, i, j, hij⟩ := M.presheaf.germ_eq y hyU hyU s 0 hy0'
      refine ⟨V.carrier, fun z hz ↦ ⟨?_, i.le hz⟩, V.2, hyV⟩
      rintro ⟨hzU, hz0⟩
      apply hz0
      rw [← M.presheaf.germ_res_apply i z hz s, hij, map_zero, map_zero]
    · ext y
      constructor
      · rintro ⟨hy, hne⟩
        exact ⟨hy, Or.inl ⟨hy, hne⟩⟩
      · rintro ⟨hyU, (hy | hy)⟩
        · exact hy
        · exact absurd hyU hy
  obtain ⟨y, ⟨hyU, hy⟩, hyc⟩ :=
    nonempty_inter_closedPoints (show Z.Nonempty from ⟨x, hxU, hne⟩) hZ
  have hsub : Subsingleton (M.presheaf.stalk y) := ModuleCat.isZero_iff_subsingleton.mp (h y hyc)
  exact hy (hsub.elim _ _)

end Jacobson

end AlgebraicGeometry.LocallyRingedSpace.Modules
