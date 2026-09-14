/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.EssentiallyZero
import SGA.SGA2.ExposeII.Principal

/-!
# SGA 2, Exposé II, Lemmas 9 and 11: the principal system as a functor

We connect the principal annihilator calculation to the essentially zero
system API, and deduce that its Hom colimits vanish on a noetherian module.
The Koszul interpretation of this system is proved in `PrincipalKoszul.lean`.
-/

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/-- The inverse system of annihilators of powers of `f` in II.11. -/
def principalAnnihilatorSystem (f : R) : ℕᵒᵖ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (Submodule.torsionBy R M (f ^ n.unop))
  map h := ModuleCat.ofHom (torsionTransition f (leOfHom h.unop))
  map_id n := by
    change ModuleCat.ofHom (torsionTransition (M := M) f (le_refl n.unop)) = _
    rw [torsionTransition_self]
    rfl
  map_comp h k := by
    apply ModuleCat.hom_ext
    exact (torsionTransition_comp f (leOfHom k.unop) (leOfHom h.unop)).symm

/-- II.11, principal algebraic case, in the general system terminology. -/
theorem principalAnnihilatorSystem_isEssentiallyZero [IsNoetherian R M] (f : R) :
    IsEssentiallyZero (principalAnnihilatorSystem M f) := by
  apply (isEssentiallyZero_iff_strict _).mpr
  intro n
  obtain ⟨m, hnm, hzero⟩ := principal_annihilator_system_essentially_zero (M := M) f n
  exact ⟨m, hnm, by
    change ModuleCat.ofHom (torsionTransition (M := M) f hnm.le) = 0
    rw [hzero]
    rfl⟩

/-- The Hom colimits used in II.9 vanish for the principal annihilator system
of a noetherian module, for every coefficient module. -/
theorem principalAnnihilatorSystem_isZero_hom_colimit [IsNoetherian R M]
    (f : R) (N : ModuleCat.{u} R) :
    IsZero (colimit ((principalAnnihilatorSystem M f).op ⋙
      (linearYoneda R (ModuleCat.{u} R)).obj N)) :=
  (principalAnnihilatorSystem_isEssentiallyZero M f).isZero_hom_colimit N

end SGA.SGA2.ExposeII
