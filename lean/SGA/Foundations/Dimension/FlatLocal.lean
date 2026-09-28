/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Dimension of the closed fibre of a local homomorphism

Let `A → B` be a local homomorphism of noetherian local rings. Then
`dim B ≤ dim A + dim B/𝔪_A B`, with equality if `B` is flat over `A`
(Stacks Project, Tag 00ON; EGA IV §6.1; Matsumura, Theorem 15.1). This is the local form of
mathlib's `Ideal.height_le_height_add_of_liesOver` and
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`.
-/

open IsLocalRing

namespace IsLocalRing

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

/-- The Krull dimension of the closed fibre `B/𝔪_A B` of a local homomorphism is the height of
the image of `𝔪_B` in it. -/
theorem height_map_maximalIdeal_eq_ringKrullDim_quotient :
    ((maximalIdeal B).map (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A B)))).height =
      ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  set I := (maximalIdeal A).map (algebraMap A B)
  have hI : I ≤ maximalIdeal B :=
    ((local_hom_TFAE (algebraMap A B)).out 1 3).mp ‹IsLocalHom (algebraMap A B)›
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
    (maximalIdeal.isMaximal B).ne_top hI)
  have : IsLocalRing (B ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : ((maximalIdeal B).map (Ideal.Quotient.mk I)).IsMaximal :=
    .map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  rw [IsLocalRing.eq_maximalIdeal this, maximalIdeal_height_eq_ringKrullDim]

variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- `dim B ≤ dim A + dim B/𝔪_A B` for a local homomorphism of noetherian local rings
(Stacks Project, Tag 00OM). -/
theorem ringKrullDim_le_ringKrullDim_add_ringKrullDim_quotient :
    ringKrullDim B ≤ ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim,
    ← height_map_maximalIdeal_eq_ringKrullDim_quotient, ← WithBot.coe_add, WithBot.coe_le_coe]
  exact Ideal.height_le_height_add_of_liesOver (maximalIdeal A) (maximalIdeal B)

/-- **Dimension formula for flat local homomorphisms** (Stacks Project, Tag 00ON; EGA IV §6.1):
if `A → B` is a flat local homomorphism of noetherian local rings, then
`dim B = dim A + dim B/𝔪_A B`. -/
theorem ringKrullDim_eq_ringKrullDim_add_ringKrullDim_quotient_of_flat [Module.Flat A B] :
    ringKrullDim B = ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim,
    ← height_map_maximalIdeal_eq_ringKrullDim_quotient, ← WithBot.coe_add, WithBot.coe_inj]
  exact Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)

end IsLocalRing
