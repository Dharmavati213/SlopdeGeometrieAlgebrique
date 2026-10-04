/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Flat local extensions with a prescribed residue field (statement)

EGA 0_III 10.3.1 (Bourbaki, *Algèbre commutative* IX, Appendice, "gonflements"): let `A` be a
noetherian local ring with residue field `k`, and let `K` be a field extension of `k`. There is a
noetherian local ring `B` and a flat local homomorphism `A → B` with `𝔪_A B = 𝔪_B` and residue
field `K` over `k`. Replacing `B` by its completion (EGA 0_I 7.3.5), `B` can be taken complete.

This file records the statement in its complete form, `IsLocalRing.FlatResidueExtensionStatement`,
as the interface of the `local-alg` work stream (registry row A42). It is proved in
`SGA.Foundations.CommAlg.FlatResidueExtensionGeneral` (`IsLocalRing.flatResidueExtensionStatement`):
transcendental, separable algebraic and purely inseparable steps
(`FlatResidueExtension{Transcendental,Separable,Inseparable}`), composed with
`IsLocalRing.Realizes.trans` (`FlatResidueExtensionRealize`), then completed
(`FlatResidueExtensionCompletion`). The case SGA 1 IX.4.6 uses, `K` an algebraic closure of `k`,
is `IsLocalRing.exists_flat_isAlgClosed_residueField`.
-/

universe u

open IsLocalRing

namespace IsLocalRing

/-- EGA 0_III 10.3.1, with `B` complete (EGA 0_I 7.3.5), statement: let `A` be a noetherian local
ring and `K` a field extension of its residue field `k`. There is a complete noetherian local
ring `B` with a flat local homomorphism `A → B` such that `𝔪_A B = 𝔪_B`, and a `k`-isomorphism
from the residue field of `B` to `K`. The rings `A`, `B` and the field `K` are in the same
universe `u`. -/
def FlatResidueExtensionStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : Type u) [Field K]
    [Algebra (ResidueField A) K],
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B)
      (_ : IsAdicComplete (maximalIdeal B) B) (_ : Algebra A B) (_ : IsLocalHom (algebraMap A B)),
      Module.Flat A B ∧ (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ∧
        Nonempty (ResidueField B ≃ₐ[ResidueField A] K)

end IsLocalRing
