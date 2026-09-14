/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.LocalInjectiveEnvelopes
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Actual socles in essential extensions

Every essential submodule contains the actual socle. The original embedding
therefore induces a bijection on socles, so finite socle is preserved by the
genuinely constructed injective envelope. No finiteness of the whole
essential extension is assumed.
-/

noncomputable section
universe u
open CategoryTheory

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Restrict an original module map to the actual maximal-ideal annihilators. -/
def localSocleMap {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    localSocle (R := R) M →ₗ[R] localSocle (R := R) N :=
  f.hom.restrict fun x hx => (mem_localSocle N (f x)).mpr (fun r hr => by
    rw [← map_smul, (mem_localSocle M x).mp hx r hr, map_zero])

/-- Socle restriction preserves injectivity of the actual map. -/
theorem localSocleMap_injective {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : Function.Injective f.hom) : Function.Injective (localSocleMap f) := by
  intro x y h
  exact Subtype.ext (hf (congrArg Subtype.val h))

/-- Every essential submodule contains all simple submodules, and hence
the actual socle. -/
theorem EssentialIn.localSocle_le {M : ModuleCat.{u} R} {S : Submodule R M}
    (hS : EssentialIn S ⊤) : localSocle (R := R) M ≤ S := by
  rw [localSocle_eq_sSup_simple]
  apply sSup_le
  intro P hP
  have : IsSimpleModule R P := hP
  by_contra hn
  have hd : Disjoint P S :=
    (IsSimpleModule.isAtom (R := R) (m := P)).not_le_iff_disjoint.mp hn
  have hz := (essentialIn_iff_disjoint _ _).mp hS |>.2 P le_top hd.symm
  exact (IsSimpleModule.isAtom (R := R) (m := P)).ne_bot hz

/-- An essential embedding induces a surjection on the unchanged socles. -/
theorem EssentialModuleMap.localSocleMap_surjective {M N : ModuleCat.{u} R}
    {f : M ⟶ N} (hf : EssentialModuleMap f) : Function.Surjective (localSocleMap f) := by
  intro y
  obtain ⟨x, hx⟩ := hf.2.localSocle_le y.property
  have hxs : x ∈ localSocle (R := R) M := by
    rw [mem_localSocle]
    intro r hr
    apply hf.1
    rw [map_smul, hx, (mem_localSocle N y.val).mp y.property r hr, map_zero]
  exact ⟨⟨x, hxs⟩, Subtype.ext hx⟩

/-- Finite socle is preserved by an arbitrary essential embedding. -/
theorem EssentialModuleMap.localSocle_finite {M N : ModuleCat.{u} R}
    {f : M ⟶ N} (hf : EssentialModuleMap f) [Module.Finite R (localSocle (R := R) M)] :
    Module.Finite R (localSocle (R := R) N) :=
  Module.Finite.of_surjective (localSocleMap f) hf.localSocleMap_surjective

/-- Finite socle passes to a submodule through its original injection. -/
theorem localSocle_finite_of_injective [IsNoetherianRing R]
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (hf : Function.Injective f.hom)
    [Module.Finite R (localSocle (R := R) N)] :
    Module.Finite R (localSocle (R := R) M) :=
  Module.Finite.of_injective (localSocleMap f) (localSocleMap_injective f hf)

end SGA.SGA2.ExposeIV
