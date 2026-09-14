/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.Exactness

/-!
# SGA 2, IX: exactness of adic completion

Exposé IX compares algebraic and formal geometry along an ideal. The first
algebraic input is that `I`-adic completion preserves surjectivity and, over
noetherian rings on finite modules, injectivity and exactness.
-/

universe u

namespace SGA.SGA2.ExposeIX

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Adic completion preserves surjectivity (mathlib). -/
theorem adicCompletion_map_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (AdicCompletion.map I f) :=
  AdicCompletion.map_surjective I hf

/-- Over a noetherian ring, adic completion preserves injectivity of maps
into a finite module (mathlib). -/
theorem adicCompletion_map_injective [IsNoetherianRing R] [Module.Finite R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (AdicCompletion.map I f) :=
  AdicCompletion.map_injective I hf

/-- Over a noetherian ring, adic completion is exact on finite modules when
the sequence is short exact (mathlib). -/
theorem adicCompletion_map_exact [IsNoetherianRing R]
    {P : Type u} [AddCommGroup P] [Module R P] [Module.Finite R N]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) :=
  AdicCompletion.map_exact (I := I) hf hfg hg

end SGA.SGA2.ExposeIX
