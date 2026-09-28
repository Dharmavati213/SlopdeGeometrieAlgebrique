/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.FlasqueResolution

/-!
# Cycle sequences for integer-indexed cochain complexes

These exact sequences provide the degreewise input for comparing bounded-below
flasque resolutions, including their mapping cones.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Abelian C]

/-- The sequence from cycles to a cochain term to the next cycles. -/
def integerCochainCyclesSequence (K : CochainComplex C ℤ) (n : ℤ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (by
    rw [← cancel_mono (K.iCycles (n + 1))]
    simp)

/-- Exactness in the next degree makes the cycle sequence short exact. -/
theorem integerCochainCyclesSequence_shortExact (K : CochainComplex C ℤ) (n : ℤ)
    (hK : K.ExactAt (n + 1)) : (integerCochainCyclesSequence K n).ShortExact := by
  let A := integerCochainCyclesSequence K n
  let B := ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (K.iCycles_d n (n + 1))
  let φ : A ⟶ B :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles (n + 1)
      comm₂₃ := by simp [A, B, integerCochainCyclesSequence] }
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    exact B.exact_of_f_is_kernel (K.cyclesIsKernel n (n + 1) (by simp))
  · exact inferInstanceAs (Mono (K.iCycles n))
  · let Q := ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
      (K.toCycles_comp_homologyπ n (n + 1))
    have hQ : Q.Exact := Q.exact_of_g_is_cokernel
      (K.homologyIsCokernel n (n + 1) (by simp))
    exact (ShortComplex.exact_iff_epi Q (hK.isZero_homology.eq_of_tgt _ _)).mp hQ

/-- If a complex term is zero, its subobject of cycles is zero. -/
theorem cycles_isZero_of_term_isZero (K : CochainComplex C ℤ) (n : ℤ)
    (h : IsZero (K.X n)) : IsZero (K.cycles n) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (K.iCycles n), Category.id_comp, zero_comp]
  exact h.eq_of_tgt _ _

/-- Left exactness together with surjectivity onto cycles implies exactness
of the mapped complex in the following degree. -/
theorem map_integerCochain_exactAt_of_cycle_surjective
    {D : Type*} [Category D] [Abelian D] (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] (K : CochainComplex C ℤ) (n : ℤ)
    [Epi (G.map (K.toCycles n (n + 1)))] :
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt (n + 1) := by
  let A := ShortComplex.mk (G.map (K.d n (n + 1))) (G.map (K.d (n + 1) (n + 2)))
    (by rw [← G.map_comp, K.d_comp_d, G.map_zero])
  let B := ShortComplex.mk (K.iCycles (n + 1)) (K.d (n + 1) (n + 2))
    (K.iCycles_d (n + 1) (n + 2))
  have hB : B.Exact := B.exact_of_f_is_kernel
    (K.cyclesIsKernel (n + 1) (n + 2) (by simp; omega))
  have : Mono B.f := inferInstanceAs (Mono (K.iCycles (n + 1)))
  have hGB := hB.map_of_mono_of_preservesKernel G inferInstance inferInstance
  let φ : A ⟶ B.map G :=
    { τ₁ := G.map (K.toCycles n (n + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        change G.map (K.toCycles n (n + 1)) ≫ G.map (K.iCycles (n + 1)) =
          G.map (K.d n (n + 1)) ≫ 𝟙 _
        rw [Category.comp_id, ← G.map_comp, K.toCycles_i]
      comm₂₃ := by simp [A, B] }
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp; omega)]
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hGB

end SGA.SGA2.ExposeI
