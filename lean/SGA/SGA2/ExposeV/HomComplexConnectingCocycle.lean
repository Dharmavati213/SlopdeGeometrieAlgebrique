/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.HomComplexComposition
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # V.1: the original cocycle lift and the derived connecting morphism -/

noncomputable section
universe w v u
open CategoryTheory Limits Preadditive HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]
  {P : CochainComplex C ℤ} (S : ShortComplex (CochainComplex C ℤ))
  {n m : ℤ} (h : n + 1 = m)
  (a : Cocycle P S.X₁ m) (b : Cochain P S.X₂ n) (c : Cocycle P S.X₃ n)
  (hb : δ n m b = a.1.comp (Cochain.ofHom S.f) (add_zero m))
  (hc : b.comp (Cochain.ofHom S.g) (add_zero n) = c.1)

/-- The actual lifted cocycle into the mapping cone. The negative first
component compensates the cone's differential convention. -/
def connectingConeCocycle : Cocycle P (mappingCone S.f) n :=
  mappingCone.liftCocycle S.f (-a) b h (by simp [hb])

include hc in
/-- The cone cocycle projects to the original cocycle, without altering
its representative in the quotient complex. -/
theorem connectingConeCocycle_postcomp :
    (connectingConeCocycle S h a b hb).postcomp (mappingCone.descShortComplex S) = c := by
  apply Subtype.ext
  change (mappingCone.liftCochain S.f (-a.1) b h).comp
    (Cochain.ofHom (mappingCone.descShortComplex S)) (add_zero n) = c.1
  simpa [mappingCone.liftCochain, mappingCone.descShortComplex] using hc

/-- Composing with the actual cone connecting cocycle recovers the original
boundary representative, including the cone's negative-projection sign. -/
theorem connectingConeCocycle_comp_fst :
    homCocycleComp (connectingConeCocycle S h a b hb) (-mappingCone.fst S.f) h = a := by
  apply Subtype.ext
  simp [homCocycleComp, connectingConeCocycle, mappingCone.liftCocycle]

/-- The lifted shifted chain map has the original boundary as its composite
with the third arrow of the mapping-cone triangle. -/
theorem connectingConeCocycle_comp_triangle :
    ShiftedHom.comp (Cocycle.equivHomShift.symm (connectingConeCocycle S h a b hb))
        (mappingCone.triangle S.f).mor₃ (by omega) = Cocycle.equivHomShift.symm a := by
  change ShiftedHom.comp (Cocycle.equivHomShift.symm (connectingConeCocycle S h a b hb))
    (Cocycle.equivHomShift.symm (-mappingCone.fst S.f)) (by omega) = _
  rw [← homCocycleComp_equivHomShift _ _ h, connectingConeCocycle_comp_fst]

variable [HasDerivedCategory.{w} C]

include hb hc in
/-- The actual lift-and-differentiate boundary is the derived connecting
morphism of the original short exact sequence of complexes. -/
theorem homCocycle_connecting_eq_derived (hS : S.ShortExact) :
    ShiftedHom.comp (ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q)
        (DerivedCategory.triangleOfSESδ hS) (by omega) =
      ShiftedHom.map (Cocycle.equivHomShift.symm a) DerivedCategory.Q := by
  have hp := congrArg (fun z : Cocycle P S.X₃ n => Cocycle.equivHomShift.symm z)
    (connectingConeCocycle_postcomp S h a b c hb hc)
  rw [Cocycle.equivHomShift_symm_postcomp] at hp
  rw [← hp, ← ShiftedHom.comp_mk₀ _ 0 rfl (mappingCone.descShortComplex S),
    ShiftedHom.map_comp, ShiftedHom.map_mk₀,
    ShiftedHom.comp_assoc _ _ _ (zero_add n) (add_zero 1) (by omega),
    ShiftedHom.mk₀_comp, DerivedCategory.descShortComplex_triangleOfSESδ]
  change ShiftedHom.comp _
    (ShiftedHom.map (mappingCone.triangle S.f).mor₃ DerivedCategory.Q) (by omega) = _
  rw [← ShiftedHom.map_comp, connectingConeCocycle_comp_triangle]

/-- The same original lifted cocycle in the literal source convention has
the target-degree sign in its derived connecting formula. -/
theorem sourceHomCocycle_connecting_eq_derived (hS : S.ShortExact)
    (hb' : sourceHomδ n m b = a.1.comp (Cochain.ofHom S.f) (add_zero m))
    (hc' : b.comp (Cochain.ofHom S.g) (add_zero n) = c.1) :
    ShiftedHom.comp (ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q)
        (DerivedCategory.triangleOfSESδ hS) (by omega) =
      m.negOnePow • ShiftedHom.map (Cocycle.equivHomShift.symm a) DerivedCategory.Q := by
  have hb'' : δ n m b = (m.negOnePow • a).1.comp (Cochain.ofHom S.f) (add_zero m) := by
    have ht := congrArg (m.negOnePow • ·) hb'
    simpa only [sourceHomδ, smul_smul, Int.units_mul_self, one_smul,
      Cocycle.coe_units_smul, Cochain.units_smul_comp] using ht
  have ht := homCocycle_connecting_eq_derived S h (m.negOnePow • a) b c hb'' hc' hS
  simpa [Units.smul_def, ShiftedHom.map] using ht

end SGA.SGA2.ExposeV
