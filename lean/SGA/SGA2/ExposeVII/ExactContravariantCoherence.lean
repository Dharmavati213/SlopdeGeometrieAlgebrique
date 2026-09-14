/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic

/-!
# SGA 2, VII.1.5: coherence via an exact contravariant δ-functor

If `T*` is an exact contravariant δ-functor on coherent modules and the values
on the supported kernel `F' = Γ_Y(F)` are coherent in degrees `i` and `i-1`,
then coherence of `Tⁱ F` is equivalent to coherence of `Tⁱ F''` on the
quotient `F'' = F / Γ_Y(F)`. The module-level transfer used in that argument
is `Module.Finite.of_exact`.
-/

universe u

namespace SGA.SGA2.ExposeVII

variable {R : Type u} [CommRing R]

/-- Finite generation transfers across a short exact sequence of modules. -/
theorem finite_of_exact {M N P : Type u}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (h_exact : Function.Exact f g) (h_surj : Function.Surjective g)
    [Module.Finite R M] [Module.Finite R P] :
    Module.Finite R N :=
  Module.Finite.of_exact h_exact h_surj

/-- Finite generation of a module follows from finiteness of a submodule and
of the corresponding quotient — the exact-sequence input to VII.1.5. -/
theorem finite_of_submodule_quotient {M : Type u}
    [AddCommGroup M] [Module R M] (N : Submodule R M)
    [Module.Finite R N] [Module.Finite R (M ⧸ N)] :
    Module.Finite R M :=
  Module.Finite.of_submodule_quotient N

/-- On a noetherian ring, submodules of finite modules are finite. -/
theorem finite_submodule [IsNoetherianRing R] {M : Type u}
    [AddCommGroup M] [Module R M] [Module.Finite R M] (N : Submodule R M) :
    Module.Finite R N :=
  inferInstance

/-- Quotients of finite modules are finite. -/
theorem finite_quotient {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (N : Submodule R M) :
    Module.Finite R (M ⧸ N) :=
  inferInstance

end SGA.SGA2.ExposeVII
