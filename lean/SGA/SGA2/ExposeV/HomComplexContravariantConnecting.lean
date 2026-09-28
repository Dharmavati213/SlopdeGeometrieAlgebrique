/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.HomComplexConnectingCocycle

/-! # V.1: the original contravariant connecting cocycle -/

noncomputable section
universe w v u
open CategoryTheory Limits Preadditive HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]
  {P : CochainComplex C ℤ} (S : ShortComplex (CochainComplex C ℤ))
  {n m : ℤ} (h : n + 1 = m)
  (a : Cocycle S.X₃ P m) (b : Cochain S.X₂ P n) (c : Cocycle S.X₁ P n)
  (hb : δ n m b = (Cochain.ofHom S.g).comp a.1 (zero_add m))
  (hc : (Cochain.ofHom S.f).comp b (zero_add n) = c.1)

/-- The original lifted cochain, extended along the cone's second projection. -/
def contravariantConnectingPrimitive : Cochain (mappingCone S.f) P n :=
  (mappingCone.snd S.f).comp b (zero_add n)

include hb hc in
/-- The cone differential explicitly measures the difference between the
lift-and-differentiate representative and the signed triangle composite. -/
theorem contravariantConnectingPrimitive_δ :
    δ n m (contravariantConnectingPrimitive S b) =
      (a.precomp (mappingCone.descShortComplex S)).1 -
        m.negOnePow • (homCocycleComp (-mappingCone.fst S.f) c (by omega)).1 := by
  rw [contravariantConnectingPrimitive, δ_zero_cochain_comp _ _ m h,
    hb, mappingCone.δ_snd]
  simp only [Cochain.neg_comp, Cochain.comp_assoc_of_second_is_zero_cochain, hc,
    homCocycleComp, Cocycle.mk_coe, Cocycle.coe_neg, Cochain.neg_comp,
    smul_neg, sub_neg_eq_add]
  have hp : (mappingCone.snd S.f).comp
      ((Cochain.ofHom S.g).comp a.1 (zero_add m)) (zero_add m) =
        (a.precomp (mappingCone.descShortComplex S)).1 := by
    simp [mappingCone.descShortComplex, mappingCone.descCochain]
  have hs : m.negOnePow = -n.negOnePow := by rw [← h, Int.negOnePow_succ]
  rw [hp, hs, Units.neg_smul]

include hb hc in
/-- The actual contravariant cone representatives have the same cohomology
class, with the target-degree sign explicitly retained. -/
theorem contravariantConnecting_cohomologyClass :
    CohomologyClass.mk (a.precomp (mappingCone.descShortComplex S)) =
      m.negOnePow • CohomologyClass.mk
        (homCocycleComp (-mappingCone.fst S.f) c (by omega)) := by
  change (CohomologyClass.mkAddMonoidHom _ _ _)
      (a.precomp (mappingCone.descShortComplex S)) =
    ((m.negOnePow : ℤ) • (CohomologyClass.mkAddMonoidHom _ _ _) _)
  rw [← map_zsmul (CohomologyClass.mkAddMonoidHom _ _ _), ← sub_eq_zero, ← map_sub]
  change CohomologyClass.mk _ = 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n h]
  exact ⟨contravariantConnectingPrimitive S b,
    contravariantConnectingPrimitive_δ S h a b c hb hc⟩

variable [HasDerivedCategory.{w} C]

/-- Equal original cocycle classes induce equal shifted maps in the derived
category, via their actual chain homotopy. -/
theorem homCocycle_derivedMap_eq_of_mk_eq {F G : CochainComplex C ℤ} {i : ℤ}
    {z z' : Cocycle F G i} (hz : CohomologyClass.mk z = CohomologyClass.mk z') :
    ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q =
      ShiftedHom.map (Cocycle.equivHomShift.symm z') DerivedCategory.Q := by
  have ht := congrArg CohomologyClass.toHom hz
  have hh := HomotopyCategory.homotopyOfEq _ _ ht
  simp only [ShiftedHom.map]
  erw [DerivedCategory.Q_map_eq_of_homotopy C hh]
  rfl

include hb hc in
/-- Before inverting the actual cone projection, the original contravariant
lift-and-differentiate class is the signed triangle composite. -/
theorem contravariantConnecting_cone_derived :
    ShiftedHom.map (Cocycle.equivHomShift.symm
        (a.precomp (mappingCone.descShortComplex S))) DerivedCategory.Q =
      m.negOnePow • ShiftedHom.map (Cocycle.equivHomShift.symm
        (homCocycleComp (-mappingCone.fst S.f) c (by omega))) DerivedCategory.Q := by
  have ht := contravariantConnecting_cohomologyClass S h a b c hb hc
  have hs : CohomologyClass.mk (a.precomp (mappingCone.descShortComplex S)) =
      CohomologyClass.mk (m.negOnePow • homCocycleComp (-mappingCone.fst S.f) c (by omega)) := by
    change _ = (CohomologyClass.mkAddMonoidHom _ _ _)
      ((m.negOnePow : ℤ) • homCocycleComp (-mappingCone.fst S.f) c (by omega))
    rw [map_zsmul]
    exact ht
  rw [homCocycle_derivedMap_eq_of_mk_eq hs]
  simp [Units.smul_def, ShiftedHom.map]

include hb hc in
/-- The actual contravariant lift-and-differentiate cocycle computes
precomposition with the original derived connecting arrow, including its sign. -/
theorem homCocycle_contravariantConnecting_eq_derived (hS : S.ShortExact) :
    ShiftedHom.comp (DerivedCategory.triangleOfSESδ hS)
        (ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q) (by omega) =
      m.negOnePow • ShiftedHom.map (Cocycle.equivHomShift.symm a) DerivedCategory.Q := by
  have := mappingCone.quasiIso_descShortComplex hS
  have hd := contravariantConnecting_cone_derived S h a b c hb hc
  rw [Cocycle.equivHomShift_symm_precomp] at hd
  have hp : ShiftedHom.map
      (mappingCone.descShortComplex S ≫ Cocycle.equivHomShift.symm a) DerivedCategory.Q =
        DerivedCategory.Q.map (mappingCone.descShortComplex S) ≫
          ShiftedHom.map (Cocycle.equivHomShift.symm a) DerivedCategory.Q := by
    simp only [ShiftedHom.map, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hp, homCocycleComp_equivHomShift, ShiftedHom.map_comp] at hd
  have hs := congrArg (m.negOnePow • ·) hd
  simp only [smul_smul, Int.units_mul_self, one_smul] at hs
  apply (cancel_epi (DerivedCategory.Q.map (mappingCone.descShortComplex S))).mp
  calc
    _ = ShiftedHom.comp
        (ShiftedHom.map (mappingCone.triangle S.f).mor₃ DerivedCategory.Q)
        (ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q) (by omega) := by
      simp only [ShiftedHom.comp, ← Category.assoc]
      rw [DerivedCategory.descShortComplex_triangleOfSESδ]
      rfl
    _ = m.negOnePow • (DerivedCategory.Q.map (mappingCone.descShortComplex S) ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm a) DerivedCategory.Q) := hs.symm
    _ = _ := by simp [Units.smul_def]

/-- For the literal source differential, the contravariant formula has no
additional sign: its differential has already supplied the required factor. -/
theorem sourceHomCocycle_contravariantConnecting_eq_derived (hS : S.ShortExact)
    (hb' : sourceHomδ n m b = (Cochain.ofHom S.g).comp a.1 (zero_add m))
    (hc' : (Cochain.ofHom S.f).comp b (zero_add n) = c.1) :
    ShiftedHom.comp (DerivedCategory.triangleOfSESδ hS)
        (ShiftedHom.map (Cocycle.equivHomShift.symm c) DerivedCategory.Q) (by omega) =
      ShiftedHom.map (Cocycle.equivHomShift.symm a) DerivedCategory.Q := by
  have hb'' : δ n m b = (Cochain.ofHom S.g).comp (m.negOnePow • a).1 (zero_add m) := by
    have ht := congrArg (m.negOnePow • ·) hb'
    simpa only [sourceHomδ, smul_smul, Int.units_mul_self, one_smul,
      Cocycle.coe_units_smul, Cochain.comp_units_smul] using ht
  have ht := homCocycle_contravariantConnecting_eq_derived S h (m.negOnePow • a) b c
    hb'' hc' hS
  simpa [Units.smul_def, ShiftedHom.map, smul_smul] using ht

end SGA.SGA2.ExposeV
