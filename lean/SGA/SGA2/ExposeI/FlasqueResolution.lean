/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.FlasqueCohomology
import SGA.SGA2.ExposeI.DerivedSupportedSections

/-!
# Supported sections of a flasque injective resolution

The cycles in an injective resolution of a flasque sheaf are flasque.
Consequently actual supported sections preserve its positive-degree
exactness. This proves supported acyclicity for the original right-derived
section functor, independently of its comparison with Ext.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

section Cycles

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The sequence from cycles to a cochain term to the next cycles. -/
def cochainCyclesSequence (K : CochainComplex C ℕ) (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (by
    rw [← cancel_mono (K.iCycles (n + 1))]
    simp)

/-- Exactness of a complex at the next term makes the cycle sequence short exact. -/
theorem cochainCyclesSequence_shortExact (K : CochainComplex C ℕ) (n : ℕ)
    (hK : K.ExactAt (n + 1)) : (cochainCyclesSequence K n).ShortExact := by
  let S := cochainCyclesSequence K n
  let T := ShortComplex.mk (K.iCycles n) (K.d n (n + 1)) (K.iCycles_d n (n + 1))
  let φ : S ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles (n + 1)
      comm₂₃ := by simp [S, T, cochainCyclesSequence] }
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    exact T.exact_of_f_is_kernel (K.cyclesIsKernel n (n + 1) (by simp))
  · exact inferInstanceAs (Mono (K.iCycles n))
  · let Q := ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
      (K.toCycles_comp_homologyπ n (n + 1))
    have hQ : Q.Exact := Q.exact_of_g_is_cokernel
      (K.homologyIsCokernel n (n + 1) (by simp))
    exact (ShortComplex.exact_iff_epi Q (hK.isZero_homology.eq_of_tgt _ _)).mp hQ

end Cycles

variable {X : TopCat.{u}}

/-- Degree-zero cycles of an injective resolution recover the resolved sheaf. -/
def injectiveResolutionCyclesZeroIso (F : Sheaf AddCommGrpCat.{u} X)
    (I : InjectiveResolution F) : I.cocomplex.cycles 0 ≅ F :=
  (I.cocomplex.cyclesIsKernel 0 1 (by simp)).conePointUniqueUpToIso I.isLimitKernelFork

/-- Every cycle sheaf in an injective resolution of a flasque sheaf is flasque. -/
theorem injectiveResolution_cycles_isFlasque (F : Sheaf AddCommGrpCat.{u} X)
    [IsFlasque F] (I : InjectiveResolution F) (n : ℕ) :
    IsFlasque (I.cocomplex.cycles n) := by
  induction n with
  | zero => exact isFlasque_of_iso (injectiveResolutionCyclesZeroIso F I)
  | succ n ih =>
    have : IsFlasque (cochainCyclesSequence I.cocomplex n).X₁ := ih
    have : IsFlasque (cochainCyclesSequence I.cocomplex n).X₂ :=
      isFlasque_of_injective (I.cocomplex.X n)
    exact Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
      (cochainCyclesSequence_shortExact I.cocomplex n (I.cocomplex_exactAt_succ n))

/-- Supported sections of an injective resolution of a flasque sheaf are
exact in every positive degree. -/
theorem gammaZSections_injectiveResolution_exactAt (Z : Closeds X) (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (I : InjectiveResolution F) (n : ℕ) :
    (((gammaZSectionsFunctor Z U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).ExactAt (n + 1) := by
  let K := I.cocomplex
  let G := gammaZSectionsFunctor Z U
  have : IsFlasque (cochainCyclesSequence K n).X₁ :=
    injectiveResolution_cycles_isFlasque F I n
  have hseq := gammaZSectionsFunctor_map_shortExact
    (cochainCyclesSequence_shortExact K n (I.cocomplex_exactAt_succ n)) Z U
  have : Epi (G.map (K.toCycles n (n + 1))) := hseq.epi_g
  let S := ShortComplex.mk (G.map (K.d n (n + 1))) (G.map (K.d (n + 1) (n + 2)))
    (by rw [← G.map_comp, K.d_comp_d, G.map_zero])
  let T := ShortComplex.mk (K.iCycles (n + 1)) (K.d (n + 1) (n + 2))
    (K.iCycles_d (n + 1) (n + 2))
  have hT : T.Exact := T.exact_of_f_is_kernel
    (K.cyclesIsKernel (n + 1) (n + 2) (by simp))
  have : Mono T.f := inferInstanceAs (Mono (K.iCycles (n + 1)))
  have hGT := hT.map_of_mono_of_preservesKernel G inferInstance inferInstance
  let φ : S ⟶ T.map G :=
    { τ₁ := G.map (K.toCycles n (n + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        change G.map (K.toCycles n (n + 1)) ≫ G.map (K.iCycles (n + 1)) =
          G.map (K.d n (n + 1)) ≫ 𝟙 _
        rw [Category.comp_id, ← G.map_comp, K.toCycles_i]
      comm₂₃ := by simp [S, T] }
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  change S.Exact
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hGT

/-- Flasque sheaves are acyclic for the original right-derived supported
section functor on every open and every closed support. -/
theorem derivedGammaZSections_isZero_of_isFlasque (Z : Closeds X) (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (n : ℕ) :
    IsZero ((derivedGammaZSections Z U (n + 1)).obj F) := by
  let I := InjectiveResolution.of F
  exact IsZero.of_iso
    (gammaZSections_injectiveResolution_exactAt Z U F I n).isZero_homology
    (I.isoRightDerivedObj (gammaZSectionsFunctor Z U) (n + 1))

end SGA.SGA2.ExposeI
