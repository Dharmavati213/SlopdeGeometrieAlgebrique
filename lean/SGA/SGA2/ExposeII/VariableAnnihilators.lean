/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.PrincipalSystem

/-!
# SGA 2, Exposé II, Lemma 11: annihilators with varying coefficients

In the induction in II.11 the right-hand terms are annihilators of `f ^ n`
in modules which themselves vary with `n`. We construct this inverse system
for any inverse sequence `F`. Its transition first changes coefficients and
then multiplies by `f ^ (m - n)`. If every `F_n` is noetherian, the system is
essentially zero: the principal bound may depend on the target index `n`.

This proves the variable-coefficient argument in the last paragraph of II.11.
`KoszulCofiber.lean` supplies the Koszul exact sequence, and
`KoszulProZero.lean` uses this result to complete the induction.
-/

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R] (F : ℕᵒᵖ ⥤ ModuleCat.{u} R) (f : R)

/-- The varying-coefficient annihilator system in the induction in II.11. -/
def variableAnnihilatorSystem : ℕᵒᵖ ⥤ ModuleCat.{u} R where
  obj n := ModuleCat.of R (Submodule.torsionBy R (F.obj n) (f ^ n.unop))
  map {m n} h := ModuleCat.ofHom
    ((torsionTransition f (leOfHom h.unop)).comp
      (torsionByMap (f ^ m.unop) (F.map h).hom))
  map_id n := by
    ext x
    change f ^ (n.unop - n.unop) • F.map (𝟙 n) (x : F.obj n) = x
    simp
  map_comp {k m n} h g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change f ^ (k.unop - n.unop) • F.map (h ≫ g) (x : F.obj k) =
      f ^ (m.unop - n.unop) •
        F.map g (f ^ (k.unop - m.unop) • F.map h (x : F.obj k))
    rw [Functor.map_comp, ModuleCat.comp_apply, map_smul, ← mul_smul, ← pow_add]
    congr 2
    have hnm := leOfHom g.unop
    have hmk := leOfHom h.unop
    omega

/-- The transition factors through the annihilator with fixed target
coefficients, exactly as in the proof of II.11. -/
theorem variableAnnihilatorSystem_map_factorization {m n : ℕᵒᵖ} (h : m ⟶ n) :
    (variableAnnihilatorSystem F f).map h =
      ModuleCat.ofHom (torsionByMap (f ^ m.unop) (F.map h).hom) ≫
        ModuleCat.ofHom (torsionTransition f (leOfHom h.unop)) := rfl

@[simp]
theorem variableAnnihilatorSystem_map_apply {m n : ℕᵒᵖ} (h : m ⟶ n)
    (x : Submodule.torsionBy R (F.obj m) (f ^ m.unop)) :
    Subtype.val (p := fun y : F.obj n => y ∈ Submodule.torsionBy R (F.obj n) (f ^ n.unop))
      ((variableAnnihilatorSystem F f).map h x) =
      f ^ (m.unop - n.unop) • F.map h (x : F.obj m) := rfl

/-- II.11, the right-hand system in the induction: noetherianness at each
target index is enough to make the varying-coefficient system essentially zero. -/
theorem variableAnnihilatorSystem_isEssentiallyZero
    [∀ n, IsNoetherian R (F.obj n)] :
    IsEssentiallyZero (variableAnnihilatorSystem F f) := by
  intro n
  obtain ⟨c, hc⟩ := exists_uniform_torsionTransition_eq_zero (M := F.obj n) f
  let m := n.unop + c
  have hnm : n.unop ≤ m := Nat.le_add_right _ _
  refine ⟨op m, (homOfLE hnm).op, ?_⟩
  rw [variableAnnihilatorSystem_map_factorization]
  have hz := hc n.unop m hnm le_rfl
  rw [hz]
  exact comp_zero

/-- Hom colimits of the varying-coefficient annihilator system vanish for
every coefficient module when the terms of `F` are noetherian. -/
theorem variableAnnihilatorSystem_isZero_hom_colimit
    [∀ n, IsNoetherian R (F.obj n)] (M : ModuleCat.{u} R) :
    IsZero (colimit ((variableAnnihilatorSystem F f).op ⋙
      (linearYoneda R (ModuleCat.{u} R)).obj M)) :=
  (variableAnnihilatorSystem_isEssentiallyZero F f).isZero_hom_colimit M

end SGA.SGA2.ExposeII
