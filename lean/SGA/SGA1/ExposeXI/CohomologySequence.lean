/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# SGA 1, Exposé XI.6.4–XI.6.10: formal consequences of the exact cohomology sequence

XI.6.4 (Kummer) and XI.6.8 (Artin–Schreier) deduce from a six-term exact sequence
`H⁰(G) →u H⁰(G) →∂ H¹(G') →i H¹(G) →v H¹(G)` (with `u` the `n`-th power, resp. `℘`, and `v` the
map it induces on `H¹`) the short exact sequence `1 → coker u → H¹(G') → ker v → 1`; XI.6.5,
XI.6.6, XI.6.9 and XI.6.10 are its two degenerate cases. This file proves this formal step for
commutative groups, written multiplicatively (as the cohomology groups `H¹` of
`SGA.Foundations.Etale`) and additively (`addCokerLift`, …). It is applied to the fpqc
cohomology of `S` in `KummerCohomology` and `ArtinSchreierCohomology`.
-/

namespace SGA.SGA1.ExposeXI

variable {G H P : Type*} [CommGroup G] [CommGroup H] [CommGroup P]
  {u : G →* G} {δ : G →* H} {i : H →* P} {v : P →* P}

/-- The map `coker u → H` induced by `δ`, when `δ ∘ u = 1`. -/
@[to_additive addCokerLift /-- The map `coker u → H` induced by `δ`, when `δ ∘ u = 0`. -/]
def cokerLift (h₁ : δ.ker = u.range) : G ⧸ u.range →* H :=
  QuotientGroup.lift u.range δ fun x hx ↦ by rwa [← h₁] at hx

/-- The map `H → ker v` induced by `i`, when `v ∘ i = 1`. -/
@[to_additive addKerRestrict /-- The map `H → ker v` induced by `i`, when `v ∘ i = 0`. -/]
def kerRestrict (h₃ : v.ker = i.range) : H →* v.ker :=
  i.codRestrict v.ker fun x ↦ by rw [h₃]; exact ⟨x, rfl⟩

@[to_additive (attr := simp) addCokerLift_mk]
theorem cokerLift_mk (h₁ : δ.ker = u.range) (x : G) :
    cokerLift h₁ (QuotientGroup.mk x) = δ x := rfl

@[to_additive (attr := simp) addKerRestrict_apply]
theorem kerRestrict_apply (h₃ : v.ker = i.range) (x : H) : (kerRestrict h₃ x : P) = i x := rfl

variable (h₁ : δ.ker = u.range) (h₂ : i.ker = δ.range) (h₃ : v.ker = i.range)

/-- XI.6.4, XI.6.8 (formal part): `coker u → H` is injective. -/
@[to_additive addCokerLift_injective]
theorem cokerLift_injective : Function.Injective (cokerLift h₁) := by
  refine (injective_iff_map_eq_one _).mpr fun x hx ↦ ?_
  induction x using QuotientGroup.induction_on with | H x => ?_
  rw [cokerLift_mk] at hx
  have : x ∈ δ.ker := hx
  rw [h₁] at this
  exact (QuotientGroup.eq_one_iff _).mpr this

include h₂ in
/-- XI.6.4, XI.6.8 (formal part): exactness at `H`, the image of `coker u` is the kernel of
`H → ker v`. -/
@[to_additive addKerRestrict_ker]
theorem kerRestrict_ker : (kerRestrict h₃).ker = (cokerLift h₁).range := by
  ext y
  constructor
  · intro hy
    have : y ∈ i.ker := congr_arg Subtype.val hy
    rw [h₂] at this
    obtain ⟨x, rfl⟩ := this
    exact ⟨QuotientGroup.mk x, rfl⟩
  · rintro ⟨x, rfl⟩
    induction x using QuotientGroup.induction_on with | H x => ?_
    refine Subtype.ext ?_
    change i (δ x) = 1
    have : δ x ∈ i.ker := by rw [h₂]; exact ⟨x, rfl⟩
    exact this

/-- XI.6.4, XI.6.8 (formal part): `H → ker v` is surjective. -/
@[to_additive addKerRestrict_surjective]
theorem kerRestrict_surjective : Function.Surjective (kerRestrict h₃) := by
  rintro ⟨y, hy⟩
  rw [h₃] at hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, rfl⟩

include h₂ h₃ in
/-- XI.6.5, XI.6.9 (formal part): if `ker v = 1` (e.g. `ₙPic(S) = 0`, resp. `H¹(S, 𝒪_S)^F = 0`),
then `coker u ≅ H`. -/
@[to_additive addCokerLift_bijective_of_ker_eq_bot]
theorem cokerLift_bijective_of_ker_eq_bot (hv : v.ker = ⊥) :
    Function.Bijective (cokerLift h₁) := by
  refine ⟨cokerLift_injective h₁, fun y ↦ ?_⟩
  have : y ∈ (kerRestrict h₃).ker := Subtype.ext (by
    have : kerRestrict h₃ y ∈ (⊤ : Subgroup v.ker) := trivial
    have hbot : (⊤ : Subgroup v.ker) = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨z, hz⟩ -
      rw [hv] at hz
      exact Subtype.ext hz
    rw [hbot] at this
    exact congr_arg Subtype.val this)
  rw [kerRestrict_ker h₁ h₂ h₃] at this
  exact this

include h₁ h₂ in
/-- XI.6.6, XI.6.10 (formal part): if `u` is surjective (every section of `𝒪_S^*` is an `n`-th
power, resp. `℘` is surjective on `H⁰(S, 𝒪_S)`), then `H ≅ ker v`. -/
@[to_additive addKerRestrict_bijective_of_surjective]
theorem kerRestrict_bijective_of_surjective (hu : Function.Surjective u) :
    Function.Bijective (kerRestrict h₃) := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun y hy ↦ ?_, kerRestrict_surjective h₃⟩
  have : y ∈ (kerRestrict h₃).ker := hy
  rw [kerRestrict_ker h₁ h₂ h₃] at this
  obtain ⟨x, rfl⟩ := this
  induction x using QuotientGroup.induction_on with | H x => ?_
  obtain ⟨x', rfl⟩ := hu x
  change δ (u x') = 1
  have : u x' ∈ δ.ker := by rw [h₁]; exact ⟨x', rfl⟩
  exact this

end SGA.SGA1.ExposeXI
