/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ModulesStalkFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Generating module sheaves from their germs

A family of global sections of an `𝒪_X`-module `M` on a locally ringed space generates it
(the induced morphism from the free module is an epimorphism) iff the germs generate every stalk
(`AlgebraicGeometry.LocallyRingedSpace.Modules.epi_freeHomEquiv_of_stalk_span`,
`stalk_span_of_epi_freeHomEquiv`). On stalks the morphism from the free module is the linear
combination map of the germs (`stalkMap_freeHomEquiv_eq_linearCombination`). This connects the
germ-level relation calculations of Oka's theorem (`SGA.Foundations.Analytic.OkaRelationSheaf`)
with sheaves of modules.

Adopted from the unmerged branch `codex/foundations-missing-inputs` (commit `c65c9a0`, file
`CoherenceGenerators.lean`). References: EGA 0_I 5.2.1; Stacks Project, Tag 01B5.
-/

noncomputable section

-- stalks of `SheafOfModules` carry module structures that are only defeq after unfolding
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}} {M : X.Modules}

/-- The germ of a global section of a module sheaf. -/
def globalSectionGerm (s : M.sections) (x : X) : (stalkFunctor x).obj M :=
  M.presheaf.germ ⊤ x (by trivial) (s.val (op ⊤))

/-- The germ of a section is the value of its corresponding map from the structure
sheaf on the germ of `1`. -/
lemma stalkMap_unitHomEquiv_symm_one (s : M.sections) (x : X) :
    stalkMap (M.unitHomEquiv.symm s) x
      ((presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).germ ⊤ x (by trivial)
        (1 : X.presheaf.obj (op ⊤))) =
        globalSectionGerm s x := by
  rw [stalkMap_germ]
  apply congrArg (M.presheaf.germ ⊤ x (by trivial))
  exact congrArg (fun t : M.sections ↦ t.val (op ⊤)) (M.unitHomEquiv.apply_symm_apply s)

variable {ι : Type u}

/-- Every generating section is in the image of the induced free map on stalks. -/
lemma globalSectionGerm_mem_range_freeHomEquiv (s : ι → M.sections) (x : X) (i : ι) :
    globalSectionGerm (s i) x ∈ (stalkMap (M.freeHomEquiv.symm s) x).range := by
  let t := (presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).germ ⊤ x (by trivial)
    (1 : X.presheaf.obj (op ⊤))
  refine ⟨stalkMap (SheafOfModules.ιFree i) x t, ?_⟩
  have hcomp : SheafOfModules.ιFree i ≫ M.freeHomEquiv.symm s =
      M.unitHomEquiv.symm (s i) := by
    simpa only [Equiv.apply_symm_apply] using
      (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply (M.freeHomEquiv.symm s) i).symm
  change (((stalkFunctor x).map (SheafOfModules.ιFree i)) ≫
    (stalkFunctor x).map (M.freeHomEquiv.symm s)) t = _
  rw [← Functor.map_comp, hcomp]
  exact stalkMap_unitHomEquiv_symm_one (s i) x

/-- The map from a free sheaf sends its `i`-th stalk basis vector to the germ of
the corresponding section. -/
lemma stalkMap_freeHomEquiv_basis (s : ι → M.sections) (x : X) (i : ι) :
    stalkMap (M.freeHomEquiv.symm s) x
      ((stalkFreeLinearEquiv x ι).symm (Finsupp.single i 1)) = globalSectionGerm (s i) x := by
  let t := (presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).germ ⊤ x (by trivial)
    (1 : X.presheaf.obj (op ⊤))
  have ht : stalkUnitLinearEquiv x t = 1 := by
    rw [stalkUnitLinearEquiv_germ]
    exact map_one (X.presheaf.germ ⊤ x (by trivial)).hom
  have hb : (stalkFreeLinearEquiv x ι).symm (Finsupp.single i 1) =
      stalkMap (SheafOfModules.ιFree i) x t := by
    apply (stalkFreeLinearEquiv x ι).injective
    rw [LinearEquiv.apply_symm_apply]
    change Finsupp.single i 1 = stalkFreeLinearEquiv x ι
      ((stalkFunctor x).map (SheafOfModules.ιFree i) t)
    rw [stalkFreeLinearEquiv_map_ιFree, ht]
  rw [hb]
  have hcomp : SheafOfModules.ιFree i ≫ M.freeHomEquiv.symm s =
      M.unitHomEquiv.symm (s i) := by
    simpa only [Equiv.apply_symm_apply] using
      (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply (M.freeHomEquiv.symm s) i).symm
  change (((stalkFunctor x).map (SheafOfModules.ιFree i)) ≫
    (stalkFunctor x).map (M.freeHomEquiv.symm s)) t = _
  rw [← Functor.map_comp, hcomp]
  exact stalkMap_unitHomEquiv_symm_one (s i) x

/-- On stalks, the map from a free sheaf is the ordinary linear-combination map
of the germs of its generating sections. -/
lemma stalkMap_freeHomEquiv_eq_linearCombination (s : ι → M.sections) (x : X) :
    (stalkMap (M.freeHomEquiv.symm s) x).comp (stalkFreeLinearEquiv x ι).symm.toLinearMap =
      Finsupp.linearCombination (X.presheaf.stalk x) (fun i ↦ globalSectionGerm (s i) x) := by
  classical
  apply Finsupp.lhom_ext
  intro i r
  have hsingle : Finsupp.single i r = r • Finsupp.single i (1 : X.presheaf.stalk x) := by
    simp
  simp only [hsingle, map_smul, LinearMap.comp_apply]
  apply congrArg (fun z ↦ r • z)
  exact (stalkMap_freeHomEquiv_basis s x i).trans
    ((Finsupp.linearCombination_single (X.presheaf.stalk x)
      (v := fun i ↦ globalSectionGerm (s i) x) 1 i).trans (one_smul _ _)).symm

/-- An epimorphic family of sections spans every stalk. -/
theorem stalk_span_of_epi_freeHomEquiv (s : ι → M.sections) (h : Epi (M.freeHomEquiv.symm s))
    (x : X) : Submodule.span (X.presheaf.stalk x)
      (Set.range (fun i ↦ globalSectionGerm (s i) x)) = ⊤ := by
  have hepi := (epi_iff_stalkFunctor_map_epi (M.freeHomEquiv.symm s)).mp h x
  have hsurj : Function.Surjective (stalkMap (M.freeHomEquiv.symm s) x) :=
    (ModuleCat.epi_iff_surjective ((stalkFunctor x).map (M.freeHomEquiv.symm s))).mp hepi
  rw [← Finsupp.range_linearCombination, LinearMap.range_eq_top,
    ← stalkMap_freeHomEquiv_eq_linearCombination s x]
  exact hsurj.comp (stalkFreeLinearEquiv x ι).symm.surjective

/-- A family of sections which spans every stalk gives an epimorphism from the
corresponding free module sheaf. -/
theorem epi_freeHomEquiv_of_stalk_span (s : ι → M.sections)
    (hs : ∀ x : X, Submodule.span (X.presheaf.stalk x)
      (Set.range (fun i ↦ globalSectionGerm (s i) x)) = ⊤) :
    Epi (M.freeHomEquiv.symm s) := by
  apply (epi_iff_stalkFunctor_map_epi _).mpr
  intro x
  rw [ModuleCat.epi_iff_surjective]
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hs x]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact globalSectionGerm_mem_range_freeHomEquiv s x i

/-- Generating sections span every local module. -/
theorem generatingSections_stalk_span (G : M.GeneratingSections) (x : X) :
    Submodule.span (X.presheaf.stalk x)
      (Set.range (fun i ↦ globalSectionGerm (G.s i) x)) = ⊤ :=
  stalk_span_of_epi_freeHomEquiv G.s G.epi x

/-- Actual generating-section data obtained from generation of every stalk. -/
def generatingSectionsOfStalkSpan (s : ι → M.sections)
    (hs : ∀ x : X, Submodule.span (X.presheaf.stalk x)
      (Set.range (fun i ↦ globalSectionGerm (s i) x)) = ⊤) : M.GeneratingSections where
  I := ι
  s := s
  epi := epi_freeHomEquiv_of_stalk_span s hs

instance generatingSectionsOfStalkSpan_isFiniteType [Finite ι] (s : ι → M.sections)
    (hs : ∀ x : X, Submodule.span (X.presheaf.stalk x)
      (Set.range (fun i ↦ globalSectionGerm (s i) x)) = ⊤) :
    (generatingSectionsOfStalkSpan s hs).IsFiniteType := ⟨inferInstanceAs (Finite ι)⟩

/-- A finite family which spans every stalk makes the sheaf finite type in the
standard category of sheaves of modules. -/
theorem isFiniteType_of_stalk_span [Finite ι] (s : ι → M.sections)
    (hs : ∀ x : X, Submodule.span (X.presheaf.stalk x)
      (Set.range (fun i ↦ globalSectionGerm (s i) x)) = ⊤) : M.IsFiniteType := by
  let G := generatingSectionsOfStalkSpan s hs
  let D : M.LocalGeneratorsData := G.localGeneratorsData
  have hD : D.IsFiniteType := by
    refine { isFiniteType := fun U ↦ ?_ }
    exact ⟨inferInstanceAs (Finite ι)⟩
  refine SheafOfModules.IsFiniteType.mk (M := M) ?_
  exact ⟨D, hD⟩

end AlgebraicGeometry.LocallyRingedSpace.Modules
