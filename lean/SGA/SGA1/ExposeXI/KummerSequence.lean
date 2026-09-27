/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import SGA.SGA1.ExposeXI.Kummer

/-!
# SGA 1, Exposé XI.6.1: the Kummer exact sequence

The Kummer sequence `0 → μ_n → 𝔾_m → 𝔾_m → 0`, with `u_n : 𝔾_m → 𝔾_m` the `n`-th power map,
is exact in the sense of XI.4: `u_n` is faithfully flat and `𝔾_m` is a principal homogeneous
bundle over `𝔾_m` (via `u_n`) under `μ_n`. For `S = Spec A`, `𝔾_m = Spec A[t, t⁻¹]`; the proof in
SGA observes that `A[t, t⁻¹]` is free with basis `1, t, …, tⁿ⁻¹` over `A[s, s⁻¹]`, `s = tⁿ`.

We show that `u_n` *is* the universal Kummer covering: `A[t, t⁻¹] ≅ A'[T]/(Tⁿ - s)` with
`A' = A[s, s⁻¹]`, compatibly with `u_n` (`laurentKummerEquiv`). Exactness then follows from the
results on Kummer coverings: `u_n` is faithfully flat (`powLaurent_faithfullyFlat`), and
`𝔾_m ×_{𝔾_m} 𝔾_m ≅ 𝔾_m ×_{𝔾_m} μ_{n, 𝔾_m}` (`Kummer.torsorEquiv` applied to `a = s`).
-/

namespace SGA.SGA1.ExposeXI

open Polynomial TensorProduct LaurentPolynomial

variable {A : Type*} [CommRing A] (n : ℕ)

/-- XI.6.1: the `n`-th power homomorphism `u_n : 𝔾_m → 𝔾_m` on rings,
`A[s, s⁻¹] → A[t, t⁻¹]`, `s ↦ tⁿ`. -/
noncomputable def powLaurent : A[T;T⁻¹] →+* A[T;T⁻¹] :=
  LaurentPolynomial.eval₂ LaurentPolynomial.C (isUnit_T (n : ℤ)).unit

@[simp]
theorem powLaurent_C (a : A) : powLaurent n (LaurentPolynomial.C a) = LaurentPolynomial.C a :=
  eval₂_C _ _ a

@[simp]
theorem powLaurent_T_one : powLaurent n (T 1 : A[T;T⁻¹]) = T n := by
  rw [powLaurent, eval₂_T, zpow_one, IsUnit.unit_spec]

/-- Two ring homomorphisms out of `A[t, t⁻¹]` agreeing on constants and on `t` are equal. -/
theorem laurent_ringHom_ext {R : Type*} [Semiring R] {f g : A[T;T⁻¹] →+* R}
    (hC : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a)) (hT : f (T 1) = g (T 1)) :
    f = g := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (X : A[X])) (Polynomial.ringHom_ext ?_ ?_)
  · intro a
    simpa [algebraMap_eq_toLaurent, toLaurent_C] using hC a
  · simpa [algebraMap_eq_toLaurent, toLaurent_X] using hT

variable [NeZero n]

/-- The root of `Tⁿ - s` over `A[s, s⁻¹]` is a unit. -/
theorem isUnit_root_laurent :
    IsUnit (AdjoinRoot.root (X ^ n - Polynomial.C (T 1 : A[T;T⁻¹]))) :=
  Kummer.isUnit_root n (isUnit_T 1)

theorem eval₂_root_T_nat :
    LaurentPolynomial.eval₂ (algebraMap A (KummerAlgebra A[T;T⁻¹] n (T 1)))
      (isUnit_root_laurent n).unit (T n) = AdjoinRoot.root _ ^ n := by
  rw [LaurentPolynomial.eval₂_T, zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec]

omit [NeZero n] in
theorem algebraMap_laurent_kummer (a : A) :
    algebraMap A (KummerAlgebra A[T;T⁻¹] n (T 1)) a =
      algebraMap A[T;T⁻¹] (KummerAlgebra A[T;T⁻¹] n (T 1)) (LaurentPolynomial.C a) := by
  rw [LaurentPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- The map `A'[T]/(Tⁿ - s) → A[t, t⁻¹]`, `T ↦ t`, `s ↦ tⁿ`. -/
noncomputable def laurentKummerHom : KummerAlgebra A[T;T⁻¹] n (T 1) →+* A[T;T⁻¹] :=
  AdjoinRoot.lift (powLaurent n) (T 1) (by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, powLaurent_T_one,
      T_pow, mul_one, sub_self])

omit [NeZero n] in
theorem laurentKummerHom_of (x : A[T;T⁻¹]) :
    laurentKummerHom n (AdjoinRoot.of _ x) = powLaurent n x :=
  AdjoinRoot.lift_of _

omit [NeZero n] in
theorem laurentKummerHom_root :
    laurentKummerHom n (AdjoinRoot.root (X ^ n - Polynomial.C (T 1 : A[T;T⁻¹]))) = T 1 :=
  AdjoinRoot.lift_root _

/-- XI.6.1: `A[t, t⁻¹]` is the universal Kummer covering: `A'[T]/(Tⁿ - s) ≅ A[t, t⁻¹]` for
`A' = A[s, s⁻¹]`, `T ↦ t`, compatibly with `u_n : A' → A[t, t⁻¹]`
(`laurentKummerEquiv_algebraMap`). -/
noncomputable def laurentKummerEquiv :
    KummerAlgebra A[T;T⁻¹] n (T 1) ≃+* A[T;T⁻¹] :=
  RingEquiv.ofRingHom (laurentKummerHom n)
    (LaurentPolynomial.eval₂ (algebraMap A _) (isUnit_root_laurent n).unit)
    (laurent_ringHom_ext (fun a ↦ by
        rw [RingHom.comp_apply, LaurentPolynomial.eval₂_C, algebraMap_laurent_kummer,
          AdjoinRoot.algebraMap_eq, laurentKummerHom_of, powLaurent_C, RingHom.id_apply])
      (by
        rw [RingHom.comp_apply, LaurentPolynomial.eval₂_T, zpow_one, IsUnit.unit_spec,
          laurentKummerHom_root, RingHom.id_apply]))
    (AdjoinRoot.ringHom_ext
      (laurent_ringHom_ext
        (fun a ↦ by
          rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, laurentKummerHom_of,
            powLaurent_C, LaurentPolynomial.eval₂_C, algebraMap_laurent_kummer,
            AdjoinRoot.algebraMap_eq, RingHom.id_apply])
        (by
          rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, laurentKummerHom_of,
            powLaurent_T_one, eval₂_root_T_nat, Kummer.root_pow, AdjoinRoot.algebraMap_eq,
            RingHom.id_apply]))
      (by
        rw [RingHom.comp_apply, laurentKummerHom_root, LaurentPolynomial.eval₂_T, zpow_one,
          IsUnit.unit_spec, RingHom.id_apply]))

theorem laurentKummerEquiv_algebraMap (x : A[T;T⁻¹]) :
    laurentKummerEquiv n (algebraMap _ (KummerAlgebra A[T;T⁻¹] n (T 1)) x) = powLaurent n x := by
  rw [AdjoinRoot.algebraMap_eq]
  exact laurentKummerHom_of n x

theorem laurentKummerEquiv_root :
    laurentKummerEquiv n (AdjoinRoot.root (X ^ n - Polynomial.C (T 1 : A[T;T⁻¹]))) = T 1 :=
  laurentKummerHom_root n

/-- XI.6.1: the `n`-th power map `u_n : 𝔾_m → 𝔾_m` is faithfully flat. -/
theorem powLaurent_faithfullyFlat : (powLaurent n : A[T;T⁻¹] →+* A[T;T⁻¹]).FaithfullyFlat := by
  have h : powLaurent n = (laurentKummerEquiv (A := A) n).toRingHom.comp
      (algebraMap A[T;T⁻¹] (KummerAlgebra A[T;T⁻¹] n (T 1))) :=
    RingHom.ext fun x ↦ (laurentKummerEquiv_algebraMap n x).symm
  rw [h]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
    (RingHom.FaithfullyFlat.of_bijective (laurentKummerEquiv n).bijective)

/-- XI.6.1: exactness of the Kummer sequence in the sense of XI.4: over the base `𝔾_m`, the
`n`-th power map makes `𝔾_m` formally principal homogeneous under `μ_n`, i.e.
`𝔾_m ×_{𝔾_m} 𝔾_m ≅ 𝔾_m ×_{𝔾_m} μ_{n, 𝔾_m}` (with `𝔾_m → 𝔾_m` identified with the universal
Kummer covering by `laurentKummerEquiv`). -/
noncomputable def kummerSequenceTorsorEquiv :
    KummerAlgebra A[T;T⁻¹] n (T 1) ⊗[A[T;T⁻¹]] KummerAlgebra A[T;T⁻¹] n (T 1)
      ≃ₐ[KummerAlgebra A[T;T⁻¹] n (T 1)]
      KummerAlgebra A[T;T⁻¹] n (T 1) ⊗[A[T;T⁻¹]] MuAlgebra A[T;T⁻¹] n :=
  Kummer.torsorEquiv n (isUnit_T 1)

end SGA.SGA1.ExposeXI
