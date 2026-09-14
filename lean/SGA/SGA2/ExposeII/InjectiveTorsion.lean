/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.Torsion
import SGA.SGA2.ExposeII.InjectiveLocalization
import Mathlib.RingTheory.Filtration

/-!
# SGA 2, Exposé II: injectivity of supported elements

Over a noetherian ring, ideal-power torsion in an injective module is injective.
The proof uses Artin–Rees and Baer's criterion: a map from an ideal into the
torsion submodule kills the intersection with a sufficiently high support-ideal
power, so it extends through the corresponding quotient of the ring.
-/

noncomputable section

universe u v

open CategoryTheory

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R]

/-- A finitely generated submodule of ideal-power torsion has a uniform
annihilating ideal power. -/
theorem exists_le_torsionBySet_pow_of_fg {M : Type v} [AddCommGroup M] [Module R M]
    (I : Ideal R) (N : Submodule R M) (hN : N.FG) (h : N ≤ powerTorsion I M) :
    ∃ n : ℕ, N ≤ Submodule.torsionBySet R M (I ^ n : Ideal R) := by
  classical
  obtain ⟨s, hs⟩ := hN
  have hx (x : s) : ∃ n : ℕ, (x : M) ∈ Submodule.torsionBySet R M (I ^ n : Ideal R) := by
    have := h (show (x : M) ∈ N by rw [← hs]; exact Submodule.subset_span x.property)
    simpa only [powerTorsion, Submodule.mem_iSup_of_directed _
      (torsionBySet_pow_monotone I M).directed_le] using this
  choose n hn using hx
  refine ⟨s.attach.sup n, ?_⟩
  rw [← hs, Submodule.span_le]
  intro x hx
  exact torsionBySet_pow_monotone I M
    (Finset.le_sup (s.mem_attach ⟨x, hx⟩)) (hn ⟨x, hx⟩)

/-- Artin–Rees turns a torsion-valued map on an ideal into a map that kills
the intersection with some power of the support ideal. -/
theorem exists_pow_inf_le_map_ker_of_range_le_powerTorsion [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] (I J : Ideal R)
    (f : J →ₗ[R] M) (hf : f.range ≤ powerTorsion I M) :
    ∃ n : ℕ, I ^ n ⊓ J ≤ f.ker.map J.subtype := by
  obtain ⟨n, hn⟩ := exists_le_torsionBySet_pow_of_fg I f.range (Submodule.fg_range f) hf
  have hkill : I ^ n • J ≤ f.ker.map J.subtype := by
    apply Submodule.smul_le.mpr
    intro r hr x hx
    refine ⟨r • (⟨x, hx⟩ : J), ?_, rfl⟩
    change f (r • (⟨x, hx⟩ : J)) = 0
    rw [f.map_smul]
    have ht := hn (f.mem_range_self ⟨x, hx⟩)
    rw [Submodule.mem_torsionBySet_iff] at ht
    exact ht ⟨r, hr⟩
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul J
  refine ⟨k + n, ?_⟩
  have hkn := hk (k + n) (Nat.le_add_right k n)
  simp only [Ideal.smul_eq_mul, Ideal.mul_top, Nat.add_sub_cancel_left] at hkn
  rw [hkn]
  exact (smul_le_smul_left (I ^ n) inf_le_right).trans hkill

/-- Ideal-power torsion in an injective module over a noetherian ring
satisfies Baer's criterion. -/
theorem powerTorsion_baer_of_injective [IsNoetherianRing R]
    (I : Ideal R) (E : ModuleCat.{u} R) [Injective E] :
    Module.Baer R (powerTorsion I E) := by
  intro J f
  let q : J →ₗ[R] E := (powerTorsion I E).subtype.comp f
  obtain ⟨n, hn⟩ := exists_pow_inf_le_map_ker_of_range_le_powerTorsion I J q
    (by rintro _ ⟨x, rfl⟩; exact (f x).property)
  let p : J →ₗ[R] R ⧸ I ^ n := (I ^ n).mkQ.comp J.subtype
  have hpq : p.ker ≤ q.ker := by
    intro x hx
    have hxn : (x : R) ∈ I ^ n := (Submodule.Quotient.mk_eq_zero (I ^ n)).mp hx
    obtain ⟨y, hy, he⟩ := hn ⟨hxn, x.property⟩
    have hyx : y = x := Subtype.ext he
    exact hyx ▸ hy
  obtain ⟨g, hg⟩ := exists_linearMap_extension_of_ker_le
    (A := ModuleCat.of R J) (B := ModuleCat.of R (R ⧸ I ^ n)) p q hpq
  let e : R →ₗ[R] E := g.comp (I ^ n).mkQ
  have he : ∀ x : R, e x ∈ powerTorsion I E := by
    intro x
    refine (mem_powerTorsion_iff I E (e x)).mpr ⟨n, fun r hr ↦ ?_⟩
    rw [← e.map_smul]
    change g ((I ^ n).mkQ (r * x)) = 0
    rw [show (I ^ n).mkQ (r * x) = 0 from
      (Submodule.Quotient.mk_eq_zero (I ^ n)).mpr (Ideal.mul_mem_right x _ hr), g.map_zero]
  refine ⟨e.codRestrict _ he, ?_⟩
  intro x hx
  apply Subtype.ext
  exact congrArg (fun l : J →ₗ[R] E ↦ l ⟨x, hx⟩) hg

/-- The algebraic supported-section functor preserves injective modules
over a noetherian ring. -/
theorem powerTorsion_injective_of_injective [IsNoetherianRing R]
    (I : Ideal R) (E : ModuleCat.{u} R) [Injective E] :
    Injective (ModuleCat.of R (powerTorsion I E)) := by
  let : Module.Injective R (powerTorsion I E) :=
    (powerTorsion_baer_of_injective I E).injective
  exact Module.injective_object_of_injective_module R _

/-- Supported elements form a direct summand in an injective module over
a noetherian ring. -/
theorem exists_powerTorsion_retraction [IsNoetherianRing R]
    (I : Ideal R) (E : ModuleCat.{u} R) [Injective E] :
    ∃ p : E →ₗ[R] powerTorsion I E, p.comp (powerTorsion I E).subtype = LinearMap.id := by
  let : Injective (ModuleCat.of R (powerTorsion I E)) :=
    powerTorsion_injective_of_injective I E
  exact exists_linearMap_extension_of_ker_le
    (A := ModuleCat.of R (powerTorsion I E)) (B := E)
    (powerTorsion I E).subtype LinearMap.id (by
      intro x hx
      exact Subtype.ext hx)

end SGA.SGA2.ExposeII
