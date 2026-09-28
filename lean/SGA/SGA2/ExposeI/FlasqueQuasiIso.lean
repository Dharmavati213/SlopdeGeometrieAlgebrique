/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.FlasqueAcyclicComplex
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Supported sections preserve quasi-isomorphisms of flasque complexes

The mapping cone of a quasi-isomorphism between bounded-below complexes of
flasque sheaves is bounded below, acyclic, and termwise flasque. Supported
sections preserve its acyclicity and commute with mapping cones. Thus they
preserve the original quasi-isomorphism on every open and closed support.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat CochainComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

section Cone

variable {C : Type*} [Category C] [Abelian C]

/-- A cochain map is a quasi-isomorphism exactly when its actual mapping cone
is acyclic. This uses the proved distinguished mapping-cone triangle. -/
theorem quasiIso_iff_mappingCone_acyclic {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    QuasiIso φ ↔ (mappingCone φ).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
    (mappingCone.triangleh φ) (HomotopyCategory.mappingCone_triangleh_distinguished φ)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic (mappingCone φ))

end Cone

variable {X : TopCat.{u}}

/-- The binary direct sum of flasque sheaves is flasque. -/
theorem isFlasque_biprod (F G : Sheaf AddCommGrpCat.{u} X)
    [IsFlasque F] [IsFlasque G] : IsFlasque (F ⊞ G) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨a, ha⟩ := (AddCommGrpCat.epi_iff_surjective (F.obj.map i)).mp inferInstance
      ((biprod.fst : F ⊞ G ⟶ F).hom.app V s)
    obtain ⟨b, hb⟩ := (AddCommGrpCat.epi_iff_surjective (G.obj.map i)).mp inferInstance
      ((biprod.snd : F ⊞ G ⟶ G).hom.app V s)
    refine ⟨(biprod.inl : F ⟶ F ⊞ G).hom.app U a +
      (biprod.inr : G ⟶ F ⊞ G).hom.app U b, ?_⟩
    rw [map_add, ← NatTrans.naturality_apply (biprod.inl : F ⟶ F ⊞ G).hom i a, ha,
      ← NatTrans.naturality_apply (biprod.inr : G ⟶ F ⊞ G).hom i b, hb]
    have h := congrArg (fun a : F ⊞ G ⟶ F ⊞ G ↦ a.hom.app V)
      (biprod.total (X := F) (Y := G))
    exact ConcreteCategory.congr_hom h s

/-- Mapping cones of maps between termwise flasque complexes are termwise flasque. -/
theorem mappingCone_isFlasque {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ}
    (φ : K ⟶ L) [∀ n, IsFlasque (K.X n)] [∀ n, IsFlasque (L.X n)] (n : ℤ) :
    IsFlasque ((mappingCone φ).X n) := by
  have := isFlasque_biprod (K.X (n + 1)) (L.X n)
  exact isFlasque_of_iso (homotopyCofiber.XIsoBiprod φ n (n + 1) rfl)

/-- The actual supported-section map of a quasi-isomorphism of bounded-below
flasque complexes is a quasi-isomorphism. -/
theorem gammaZSections_quasiIso_of_boundedBelow_flasque
    (Z : Closeds X) (U : Opens X)
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (d : ℤ) (hK : ∀ n < d, IsZero (K.X n)) (hL : ∀ n < d, IsZero (L.X n))
    [∀ n, IsFlasque (K.X n)] [∀ n, IsFlasque (L.X n)] :
    QuasiIso (((gammaZSectionsFunctor Z U).mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  have : ∀ n, IsFlasque ((mappingCone φ).X n) := mappingCone_isFlasque φ
  have hcone := (quasiIso_iff_mappingCone_acyclic φ).mp inferInstance
  have hbound : ∀ n < d - 1, IsZero ((mappingCone φ).X n) := by
    intro n hn
    exact (mappingCone.isZero_X_iff φ n).mpr ⟨hK _ (by omega), hL _ (by omega)⟩
  have h := gammaZSections_acyclic_of_boundedBelow_flasque Z U (mappingCone φ)
    hcone (d - 1) hbound
  apply (quasiIso_iff_mappingCone_acyclic _).mpr
  intro n
  exact (exactAt_iff_of_quasiIsoAt
    (mappingCone.mapHomologicalComplexIso φ (gammaZSectionsFunctor Z U)).hom n).mp (h n)

end SGA.SGA2.ExposeI
