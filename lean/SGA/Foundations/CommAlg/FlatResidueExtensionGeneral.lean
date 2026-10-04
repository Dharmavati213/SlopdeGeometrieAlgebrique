/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.FlatResidueExtensionTranscendental
import SGA.Foundations.CommAlg.FlatResidueExtensionSeparable
import SGA.Foundations.CommAlg.FlatResidueExtensionInseparable
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# EGA 0_III 10.3.1: flat local extensions with a prescribed residue field

Let `A` be a local ring with residue field `k` and `k → K` a field extension. Then `K` is realized
over `A` (`IsLocalRing.realizes_top`): there is a local `A`-algebra `C`, flat over `A`, with
`𝔪_A C = 𝔪_C` and residue field `K` over `k`. For `A` noetherian, its completion is a complete
noetherian local ring with the same properties: `IsLocalRing.flatResidueExtensionStatement`
proves `IsLocalRing.FlatResidueExtensionStatement` (EGA 0_III 10.3.1; Bourbaki, *Algèbre
commutative* IX, Appendice, "gonflements"). With `K` an algebraic closure of `k`:
`IsLocalRing.exists_flat_isAlgClosed_residueField`, the input of SGA 1 IX.4.6.

## Proof

Let `x` be a transcendence basis of `K` over `k`. Three steps, composed with
`IsLocalRing.Realizes.trans`:

1. `k(x)` is realized by `A[X]_{𝔪 A[X]}` (`realizes_adjoin_of_algebraicIndependent`);
2. the separable closure `K_s` of `k(x)` in `K` is realized by the strict henselization with
   respect to `K` (`realizes_separableClosure`);
3. `K` is purely inseparable over `K_s` (it is algebraic over `k(x)`), and is realized by a tower
   of free extensions built from relative `p`-bases (`realizes_top_of_forall_pow_mem`); in
   characteristic `0`, `K_s = K`.

SGA (and EGA, Bourbaki) proceed instead by a transfinite induction on monogenic extensions.
-/

universe u

open IsLocalRing

namespace IsLocalRing

/-- If `y ∈ K` is algebraic over a subring of `K` contained in the image of `ι : F →+* K`, it is
algebraic over `F` (with `K` an `F`-algebra via `ι`). -/
lemma isAlgebraic_of_isAlgebraic_subalgebra {F K : Type*} [Field F] [Field K] (ι : F →+* K)
    {R₀ : Type*} [CommRing R₀] [Algebra R₀ K] (h : ∀ r : R₀, algebraMap R₀ K r ∈ ι.fieldRange)
    (hinj : Function.Injective (algebraMap R₀ K)) {y : K} (hy : IsAlgebraic R₀ y) :
    letI := ι.toAlgebra
    IsAlgebraic F y := by
  let _ : Algebra F K := ι.toAlgebra
  obtain ⟨P, hP0, hPy⟩ := hy
  have hlift : P.map (algebraMap R₀ K) ∈ Polynomial.lifts ι := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro m
    rw [Polynomial.coeff_map]
    obtain ⟨d, hd⟩ := h (P.coeff m)
    exact ⟨d, hd⟩
  obtain ⟨Q, hQ⟩ := hlift
  rw [Polynomial.coe_mapRingHom] at hQ
  refine ⟨Q, ?_, ?_⟩
  · rintro rfl
    apply hP0
    rw [Polynomial.map_zero] at hQ
    exact Polynomial.map_injective _ hinj (by rw [← hQ, Polynomial.map_zero])
  · rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    change Polynomial.eval y (Q.map ι) = 0
    rw [hQ, Polynomial.eval_map, ← Polynomial.aeval_def, hPy]

/-- EGA 0_III 10.3.1 (without completion): let `A` be a local ring and `φ : k → K` a field
extension of its residue field. Then `K` is realized over `(A, φ)`: there is a local `A`-algebra
`C`, flat over `A`, with `𝔪_A C = 𝔪_C`, and an isomorphism of its residue field onto `K`
extending `φ`. -/
theorem realizes_top (A : Type u) [CommRing A] [IsLocalRing A] {K : Type u} [Field K]
    (φ : ResidueField A →+* K) : Realizes A φ ⊤ := by
  let _ : Algebra (ResidueField A) K := φ.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (ResidueField A) K
  have halg := hs.isAlgebraic
  refine (realizes_adjoin_of_algebraicIndependent A φ (Subtype.val : s → K) hs.1).trans
    fun C _ _ ι hι ↦ ?_
  let _ : Algebra (ResidueField C) K := ι.toAlgebra
  -- `K` is algebraic over the residue field of `C`.
  have hCalg : Algebra.IsAlgebraic (ResidueField C) K := by
    constructor
    intro y
    refine isAlgebraic_of_isAlgebraic_subalgebra ι (fun r ↦ ?_) Subtype.val_injective
      (halg.isAlgebraic y)
    rw [hι]
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ r.2
  refine (realizes_separableClosure C ι).trans fun D _ _ ι' hι' ↦ ?_
  have hιinj := ι.injective
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
  · have := Fact.mk hp
    have : CharP (ResidueField C) (ringChar K) := (ι.charP_iff_charP _).mpr (ringChar.charP K)
    refine realizes_top_of_forall_pow_mem D (ringChar K) ι' fun y ↦ ?_
    obtain ⟨n, z, hz⟩ :=
      IsPurelyInseparable.pow_mem (separableClosure (ResidueField C) K) (ringChar K) y
    refine ⟨n, ?_⟩
    rw [hι', ← hz]
    exact z.2
  · have : CharP K 0 := h0 ▸ ringChar.charP K
    have : CharZero K := CharP.charP_to_charZero K
    have : CharP (ResidueField C) 0 := (ι.charP_iff_charP 0).mpr ‹_›
    have : CharZero (ResidueField C) := CharP.charP_to_charZero (ResidueField C)
    have htop : ι'.fieldRange = ⊤ := by
      rw [hι', (separableClosure.eq_top_iff (ResidueField C) K).mpr inferInstance]
      rfl
    rw [← htop]
    exact realizes_self D ι'

/-- EGA 0_III 10.3.1 (Bourbaki, *Algèbre commutative* IX, Appendice): a noetherian local ring
`A` with residue field `k` has, for every field extension `K` of `k`, a flat local extension
`A → B` with `B` a complete noetherian local ring, `𝔪_A B = 𝔪_B`, and residue field `K` over `k`.
-/
theorem flatResidueExtensionStatement : FlatResidueExtensionStatement.{u} := by
  intro A _ _ _ K _ _
  exact exists_of_realizes_top A (realizes_top A (algebraMap (ResidueField A) K))

/-- A noetherian local ring `R` has a flat local extension `R → R'` (hence faithfully flat) with
`R'` a complete noetherian local ring with algebraically closed residue field: EGA 0_III 10.3.1
with `K` an algebraic closure of the residue field. This is the input of SGA 1 IX.4.6. -/
theorem exists_flat_isAlgClosed_residueField (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R') (_ : IsNoetherianRing R')
      (_ : IsAdicComplete (maximalIdeal R') R') (_ : Algebra R R'),
      IsLocalHom (algebraMap R R') ∧ Module.Flat R R' ∧ IsAlgClosed (ResidueField R') := by
  obtain ⟨B, _, _, _, _, _, hloc, hflat, -, ⟨e⟩⟩ :=
    flatResidueExtensionStatement R (AlgebraicClosure (ResidueField R))
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hloc, hflat,
    IsAlgClosed.of_ringEquiv _ _ e.symm.toRingEquiv⟩

end IsLocalRing
