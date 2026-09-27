/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.QuasiFinite.Basic
import SGA.Foundations.Dimension.FiniteType

/-!
# Dimension and quasi-finite algebras

For a quasi-finite `R`-algebra `S`, two comparable primes of `S` with the same contraction are
equal, so contraction `Spec S → Spec R` is strictly monotone. Hence heights and coheights
(`dim S/Q`) do not increase under contraction; with going down (e.g. `S` flat over `R`) the
heights are preserved (`PrimeSpectrum.height_comap_of_quasiFinite`).

For algebras of finite type over a field, contraction along any morphism does not increase
`dim S/Q` (`Algebra.FiniteType.coheight_comap_le`), so for quasi-finite morphisms it preserves
it (`Algebra.FiniteType.coheight_comap_of_quasiFinite`). As a consequence, a quasi-finite
morphism to an integral scheme of finite type over a field maps every irreducible component of
maximal dimension dominantly ("dominant for reasons of dimension", SGA 1 II.5.1;
`Algebra.FiniteType.comap_eq_bot_of_quasiFinite`).
-/

open Order PrimeSpectrum

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace PrimeSpectrum

/-- Incomparability for quasi-finite algebras: contraction of primes is strictly monotone. -/
theorem comap_strictMono_of_quasiFinite [Algebra.QuasiFinite R S] :
    StrictMono (comap (algebraMap R S)) := fun a b h ↦
  lt_of_le_of_ne (show (comap _ a).asIdeal ≤ (comap _ b).asIdeal from Ideal.comap_mono h.le)
    fun e ↦ h.ne (PrimeSpectrum.ext
      (Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) _ _ h.le (congrArg asIdeal e)))

theorem height_le_height_comap_of_quasiFinite [Algebra.QuasiFinite R S] (Q : PrimeSpectrum S) :
    height Q ≤ height (comap (algebraMap R S) Q) :=
  height_le_height_apply_of_strictMono _ comap_strictMono_of_quasiFinite Q

theorem coheight_le_coheight_comap_of_quasiFinite [Algebra.QuasiFinite R S]
    (Q : PrimeSpectrum S) : coheight Q ≤ coheight (comap (algebraMap R S) Q) :=
  coheight_le_coheight_apply_of_strictMono _ comap_strictMono_of_quasiFinite Q

/-- For a quasi-finite algebra with going down (e.g. a flat quasi-finite algebra, such as an
étale algebra), contraction preserves heights: `dim S_Q = dim R_{Q ∩ R}`. -/
theorem height_comap_of_quasiFinite [Algebra.QuasiFinite R S] [Algebra.HasGoingDown R S]
    (Q : PrimeSpectrum S) : height (comap (algebraMap R S) Q) = height Q :=
  le_antisymm (height_comap_le_height_of_hasGoingDown Q)
    (height_le_height_comap_of_quasiFinite Q)

end PrimeSpectrum

namespace Algebra.FiniteType

variable (k : Type*) [Field k] [Algebra k R] [Algebra k S] [IsScalarTower k R S]

/-- For a quasi-finite morphism of algebras of finite type over a field, contraction of primes
preserves `dim S/Q`. -/
theorem coheight_comap_of_quasiFinite [Algebra.FiniteType k R] [Algebra.FiniteType k S]
    [Algebra.QuasiFinite R S] (Q : PrimeSpectrum S) :
    coheight (comap (algebraMap R S) Q) = coheight Q :=
  le_antisymm (coheight_comap_le k (IsScalarTower.toAlgHom k R S) Q)
    (coheight_le_coheight_comap_of_quasiFinite Q)

/-- "Dominant for reasons of dimension" (SGA 1 II.5.1): let `S` be quasi-finite over a domain
`R`, both of finite type over a field. If a prime `Q` of `S` has `dim S/Q ≥ dim R` (e.g. `Q` is
a minimal prime with `dim S/Q = dim R`), then `Q` lies over the generic point `(0)` of `R`. -/
theorem comap_eq_bot_of_quasiFinite [IsDomain R] [Algebra.FiniteType k R]
    [Algebra.FiniteType k S] [Algebra.QuasiFinite R S] (Q : PrimeSpectrum S)
    (hQ : ringKrullDim R ≤ coheight Q) : (comap (algebraMap R S) Q).asIdeal = ⊥ := by
  set P := comap (algebraMap R S) Q
  have h := height_add_coheight_eq k P
  rw [coheight_comap_of_quasiFinite k] at h
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq k (A := R)
  rw [hn] at h hQ
  have hc : coheight Q ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n)
    (le_add_self.trans (WithBot.coe_le_coe.mp h.le))
  have h' : height P + coheight Q = n := WithBot.coe_inj.mp h
  have hP : height P = 0 := by
    have h₀ : height P + coheight Q ≤ 0 + coheight Q := by
      rw [zero_add, h']
      exact WithBot.coe_le_coe.mp hQ
    exact nonpos_iff_eq_zero.mp ((ENat.add_le_add_iff_right hc).mp h₀)
  rw [← height_eq_orderHeight, Ideal.height_eq_zero_iff_eq_bot] at hP
  exact hP

end Algebra.FiniteType
