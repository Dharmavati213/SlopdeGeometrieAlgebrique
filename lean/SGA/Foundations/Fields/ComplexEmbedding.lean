/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.RingTheory.Algebraic.Cardinality

/-!
# Embedding fields of characteristic zero into `ℂ`

The "Lefschetz principle" step used to transport statements proved over `ℂ` to other fields of
characteristic `0`:

* `Complex.nonempty_ringHom_of_mk_le_continuum`: a field of characteristic `0` of cardinality
  at most `𝔠` embeds into `ℂ` (an algebraic closure of `k(Tᵢ, i ∈ ℝ)` has characteristic `0` and
  cardinality `𝔠`, hence is isomorphic to `ℂ` by Steinitz' classification); in particular every
  countable field of characteristic `0` does (`Complex.nonempty_ringHom_of_countable`);
* `Complex.nonempty_ringEquiv_of_mk_eq_continuum`: an algebraically closed field of
  characteristic `0` and cardinality `𝔠` is isomorphic to `ℂ`.

Here `𝔠` is `Cardinal.continuum` in the universe of `k`.

## References

* [E. Steinitz, *Algebraische Theorie der Körper*][Steinitz1910]
* [S. Lang, *Algebra*, VI §1, Theorem 1.12 (isomorphism of algebraically closed fields)][Lang2002]
-/

universe u

open Cardinal

namespace Complex

variable (k : Type u) [Field k] [CharZero k]

/-- An algebraically closed field of characteristic `0` and cardinality `𝔠` is isomorphic to
`ℂ`. -/
theorem nonempty_ringEquiv_of_mk_eq_continuum [IsAlgClosed k] (hk : #k = 𝔠) :
    Nonempty (k ≃+* ℂ) := by
  have hk' : Cardinal.lift.{0} #k = Cardinal.lift.{u} #ℂ := by
    rw [mk_complex, hk, lift_continuum, lift_continuum]
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero ?_ (lift_mk_eq'.mp hk')
  rw [hk]
  exact aleph0_lt_continuum

/-- A field of characteristic `0` and cardinality at most `𝔠` embeds into `ℂ`: an algebraic
closure `L` of `k(Tᵢ, i ∈ ℝ)` has characteristic `0` and cardinality `𝔠`, hence `L ≃+* ℂ`. -/
theorem nonempty_ringHom_of_mk_le_continuum (hk : #k ≤ 𝔠) : Nonempty (k →+* ℂ) := by
  let P := MvPolynomial ℝ k
  let F := FractionRing P
  let L := AlgebraicClosure F
  have hP : #P = 𝔠 := by
    rw [MvPolynomial.cardinalMk_eq_max_lift, mk_real, lift_continuum, Cardinal.lift_uzero,
      max_eq_right hk, max_eq_left aleph0_le_continuum]
  have hF : #F = 𝔠 := (IsFractionRing.cardinalMk (R := P) F).trans hP
  have hL : #L = 𝔠 := le_antisymm
    ((Algebra.IsAlgebraic.cardinalMk_le_max F L).trans (by
      rw [hF, max_eq_left aleph0_le_continuum]))
    (hF ▸ mk_le_of_injective (algebraMap F L).injective)
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  obtain ⟨e⟩ := nonempty_ringEquiv_of_mk_eq_continuum L hL
  exact ⟨e.toRingHom.comp (algebraMap k L)⟩

/-- A countable field of characteristic `0` embeds into `ℂ`. -/
theorem nonempty_ringHom_of_countable [Countable k] : Nonempty (k →+* ℂ) :=
  nonempty_ringHom_of_mk_le_continuum k (mk_le_aleph0.trans aleph0_le_continuum)

end Complex
