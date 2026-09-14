/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
import all Mathlib.AlgebraicGeometry.StructureSheaf

/-!
# Finite normalized fraction covers

Expose the finite-fraction normalization theorem proved internally in mathlib's
construction of the associated sheaf. Its compatibility equation holds in the
original module, which is needed to extend sections of injective modules.
-/

public section

universe u

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite

namespace SGA.SGA2.ExposeII

/-- A section on a quasi-compact open has finitely many fractional
representatives with globally compatible numerators and denominators. -/
theorem exists_normalized_finite_fraction_cover
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (U : Opens (PrimeSpectrum.Top R)) (hU : IsCompact (U : Set (PrimeSpectrum.Top R)))
    (s : (structureSheafInType R M).presheaf.obj (op U)) :
    ∃ (ι : Type u) (_ : Fintype ι) (a : ι → M) (b : ι → R)
      (hle : ∀ i, PrimeSpectrum.basicOpen (b i) ≤ U),
      (U ≤ ⨆ i, PrimeSpectrum.basicOpen (b i)) ∧
      (∀ i j, b j • a i = b i • a j) ∧
      ∀ i, (structureSheafInType R M).presheaf.map (hle i).hom.op s =
        StructureSheaf.const (a i) (b i) _ le_rfl :=
  StructureSheaf.exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const U hU s

end SGA.SGA2.ExposeII
