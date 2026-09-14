/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.KoszulTopTransition
import SGA.SGA2.ExposeII.EssentiallyZero

/-!
# Actual Koszul transitions above the number of nonannihilating parameters

For a list consisting of annihilators followed by `d` arbitrary parameters,
the original consecutive-power transition on Hom cochains is zero in every
degree greater than `d`. This gives vanishing of actual stable Koszul
cohomology, not a replacement complex or a postulated comparison.
-/

noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The original cofiber map sends its shifted summand by the left side
of the actual commuting square. -/
@[reassoc]
theorem cofiber_inlX_mapArrowHom
    {F G F' G' : ChainComplex (ModuleCat.{u} R) ℕ}
    (φ : F ⟶ G) (φ' : F' ⟶ G') (α : Arrow.mk φ ⟶ Arrow.mk φ') (i : ℕ) :
    homotopyCofiber.inlX φ i (i + 1) rfl ≫
        (homotopyCofiber.mapArrowHom φ φ' chainShape_hasPredecessor α).f (i + 1) =
      α.left.f i ≫ homotopyCofiber.inlX φ' i (i + 1) rfl := by
  simp [homotopyCofiber.mapArrowHom,
    homotopyCofiber.inrCompHomotopy_hom φ' chainShape_hasPredecessor i (i + 1) rfl]

/-- A zero cochain component induces zero on the homology in that degree. -/
theorem homologyMap_eq_zero_of_component_eq_zero
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ D) (i : ℕ)
    (h : φ.f i = 0) : homologyMap φ i = 0 := by
  have hc : cyclesMap φ i = 0 := by
    apply (cancel_mono (D.iCycles i)).mp
    rw [cyclesMap_i, h]
    simp
  apply (cancel_epi (C.homologyπ i)).mp
  rw [homologyπ_naturality, hc]
  simp

/-- On an actual degree above the tail length, precomposition with the
consecutive-power transition vanishes when every prefix element annihilates
the coefficient module. -/
theorem koszulTransition_comp_eq_zero_of_annihilating_prefix
    (M : ModuleCat.{u} R) (gs fs : List R)
    (hgs : ∀ f ∈ gs, f ∈ Module.annihilator R M)
    (n i : ℕ) (hi : fs.length < i)
    (g : (koszulPowerComplex (ModuleCat.of R R) (gs ++ fs) n).X i ⟶ M) :
    (koszulTransition (ModuleCat.of R R) (gs ++ fs) (Nat.le_succ n)).f i ≫ g = 0 := by
  induction gs with
  | nil =>
    exact (koszulComplex_isZero_X (ModuleCat.of R R) (fs.map (fun f => f ^ (n + 1)))
      i (by simpa using hi)).eq_of_src _ _
  | cons f gs ih =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    let K := koszulPowerComplex (ModuleCat.of R R) (gs ++ fs) (n + 1)
    change (homotopyCofiber
      (f ^ n • 𝟙 (koszulPowerComplex (ModuleCat.of R R) (gs ++ fs) n))).X (j + 1) ⟶ M at g
    apply homotopyCofiber.ext_from_X (f ^ (n + 1) • 𝟙 K) j (j + 1) rfl
    · change homotopyCofiber.inlX (f ^ (n + 1) • 𝟙 K) j (j + 1) rfl ≫
        (homotopyCofiber.mapArrowHom _ _ chainShape_hasPredecessor
          (scalarPowerArrow f (Nat.le_succ n)
            (koszulTransition (ModuleCat.of R R) (gs ++ fs) (Nat.le_succ n)))).f (j + 1) ≫ g = _
      erw [cofiber_inlX_mapArrowHom_assoc]
      simp only [scalarPowerArrow, Arrow.homMk_left, HomologicalComplex.smul_f_apply,
        show n.succ - n = 1 by omega, pow_one, Linear.smul_comp, comp_zero]
      ext x
      exact Module.mem_annihilator.mp (hgs f (by simp)) _
    · change homotopyCofiber.inrX (f ^ (n + 1) • 𝟙 K) (j + 1) ≫
        (homotopyCofiber.mapArrowHom _ _ chainShape_hasPredecessor
          (scalarPowerArrow f (Nat.le_succ n)
            (koszulTransition (ModuleCat.of R R) (gs ++ fs) (Nat.le_succ n)))).f (j + 1) ≫ g = _
      dsimp only [homotopyCofiber.mapArrowHom]
      erw [homotopyCofiber.inrX_desc_f_assoc]
      simp only [HomologicalComplex.comp_f, scalarPowerArrow, Arrow.homMk_right,
        homotopyCofiber.inr_f, comp_zero]
      exact ih (fun a ha => hgs a (by simp [ha]))
        (homotopyCofiber.inrX (f ^ n • 𝟙 (koszulPowerComplex (ModuleCat.of R R) (gs ++ fs) n))
          (j + 1) ≫ g)

/-- The actual Hom cochain transition is zero in every degree above the
number of nonannihilating parameters. -/
theorem koszulHomTransition_eq_zero_of_annihilating_prefix
    (M : ModuleCat.{u} R) (gs fs : List R)
    (hgs : ∀ f ∈ gs, f ∈ Module.annihilator R M)
    (n i : ℕ) (hi : fs.length < i) :
    (koszulHomTransition (gs ++ fs) M (Nat.le_succ n)).f i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  exact koszulTransition_comp_eq_zero_of_annihilating_prefix M gs fs hgs n i hi g

/-- **V.3.1(i), the parameter-power calculation:** the actual stable
Koszul cohomology vanishes above the length of the nonannihilating tail. -/
theorem stableKoszulCohomology_isZero_of_annihilating_prefix
    (M : ModuleCat.{u} R) (gs fs : List R)
    (hgs : ∀ f ∈ gs, f ∈ Module.annihilator R M)
    (i : ℕ) (hi : fs.length < i) :
    IsZero (stableKoszulCohomology (gs ++ fs) M i) := by
  apply isZero_colimit_of_zero_transitions
  intro n
  refine ⟨op (op (n.unop.unop + 1)), (homOfLE (Nat.le_succ n.unop.unop)).op.op, ?_⟩
  exact homologyMap_eq_zero_of_component_eq_zero _ i
    (koszulHomTransition_eq_zero_of_annihilating_prefix M gs fs hgs n.unop.unop i hi)

end SGA.SGA2.ExposeV
