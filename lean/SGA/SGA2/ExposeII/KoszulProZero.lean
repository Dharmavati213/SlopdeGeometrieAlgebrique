/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.KoszulComplex
import SGA.SGA2.ExposeII.KoszulCofiber
import SGA.SGA2.ExposeII.VariableAnnihilators
import SGA.SGA2.ExposeII.KoszulCohomology

/-!
# SGA 2, Exposé II, Lemma 11: essential vanishing for finite Koszul systems

The scalar cofiber sequence gives an exact sequence from the positive
homology of the tail list, through homology of the full list, to a
varying-coefficient annihilator system. This exact sequence is natural in
the power index. Induction on the list, together with noetherianness of
Koszul homology and stabilization of principal annihilators, proves II.11.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite HomologicalComplex

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/-- The natural inclusion from tail homology into full Koszul homology. -/
def koszulConsHomologyInr (f : R) (fs : List R) (i : ℕ) :
    koszulHomologySystem M fs (i + 1) ⟶ koszulHomologySystem M (f :: fs) (i + 1) where
  app n := homologyMap (homotopyCofiber.inr (f ^ n.unop • 𝟙 (koszulPowerComplex M fs n.unop)))
    (i + 1)
  naturality {m n} h := by
    change homologyMap (koszulTransition M fs (leOfHom h.unop)) (i + 1) ≫
      homologyMap (homotopyCofiber.inr _) (i + 1) =
      homologyMap (homotopyCofiber.inr _) (i + 1) ≫
        homologyMap (koszulTransition M (f :: fs) (leOfHom h.unop)) (i + 1)
    rw [← homologyMap_comp, ← homologyMap_comp]
    congr 1
    exact (homotopyCofiber_inr_mapArrowHom _ _
      (scalarPowerArrow f (leOfHom h.unop) (koszulTransition M fs (leOfHom h.unop)))).symm

/-- The natural projection to the annihilator of the new generator on
the preceding tail homology. -/
def koszulConsHomologyProjection (f : R) (fs : List R) (i : ℕ) :
    koszulHomologySystem M (f :: fs) (i + 1) ⟶
      variableAnnihilatorSystem (koszulHomologySystem M fs i) f where
  app n := scalarCofiberHomologyProjection (koszulPowerComplex M fs n.unop) (f ^ n.unop) i
  naturality {m n} h := by
    let ι := ModuleCat.ofHom (Submodule.torsionBy R
      ((koszulPowerComplex M fs n.unop).homology i) (f ^ n.unop)).subtype
    have : Mono ι := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
    apply (cancel_mono ι).mp
    change (homologyMap (koszulTransition M (f :: fs) (leOfHom h.unop)) (i + 1) ≫
        scalarCofiberHomologyProjection _ _ i) ≫ ι = _
    rw [Category.assoc, scalarCofiberHomologyProjection_subtype]
    rw [koszulTransition_cons, cofiberHomologyProjection_naturality]
    change cofiberHomologyProjection
        (f ^ m.unop • 𝟙 (koszulPowerComplex M fs m.unop)) i ≫
          homologyMap (f ^ (m.unop - n.unop) • koszulTransition M fs (leOfHom h.unop)) i =
      (scalarCofiberHomologyProjection (koszulPowerComplex M fs m.unop) (f ^ m.unop) i ≫
        (variableAnnihilatorSystem (koszulHomologySystem M fs i) f).map h) ≫ ι
    rw [homologyMap_smul]
    have ht : (variableAnnihilatorSystem (koszulHomologySystem M fs i) f).map h ≫ ι =
        ModuleCat.ofHom (Submodule.torsionBy R
          ((koszulPowerComplex M fs m.unop).homology i) (f ^ m.unop)).subtype ≫
          (f ^ (m.unop - n.unop) • homologyMap (koszulTransition M fs (leOfHom h.unop)) i) := by
      ext x
      rfl
    rw [Category.assoc, ht, ← Category.assoc, scalarCofiberHomologyProjection_subtype]

/-- The sequence used in II.11 is exact at each power index. -/
theorem koszulConsHomology_exact (f : R) (fs : List R) (i : ℕ) (n : ℕᵒᵖ) :
    Function.Exact ((koszulConsHomologyInr M f fs i).app n)
      ((koszulConsHomologyProjection M f fs i).app n) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (scalarCofiberHomology_exact (koszulPowerComplex M fs n.unop) (f ^ n.unop) i)

/-- **SGA 2, II.11.** For a finite list of elements and a noetherian
coefficient module, every positive Koszul homology inverse system is
essentially zero. The ring itself need not be noetherian. -/
theorem II_11 [IsNoetherian R M] (fs : List R) (i : ℕ) (hi : 0 < i) :
    IsEssentiallyZero (koszulHomologySystem M fs i) := by
  induction fs generalizing i with
  | nil =>
    intro n
    refine ⟨n, 𝟙 n, ?_⟩
    exact (koszulComplex_isZero_homology M [] i hi).eq_of_src _ _
  | cons f fs ih =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    apply IsEssentiallyZero.of_exact (koszulConsHomologyInr M f fs j)
      (koszulConsHomologyProjection M f fs j) (koszulConsHomology_exact M f fs j)
    · exact ih (j + 1) (by omega)
    · have (n : ℕᵒᵖ) : IsNoetherian R ((koszulHomologySystem M fs j).obj n) := by
        change IsNoetherian R ((koszulPowerComplex M fs n.unop).homology j)
        infer_instance
      exact variableAnnihilatorSystem_isEssentiallyZero _ f

/-- II.11 followed by II.9: over a noetherian ring, stable Koszul cohomology
vanishes in positive degree for injective coefficients. -/
theorem stableKoszulCohomology_isZero_of_injective [IsNoetherianRing R]
    (fs : List R) (E : ModuleCat.{u} R) [Injective E] (i : ℕ) (hi : 0 < i) :
    IsZero (stableKoszulCohomology fs E i) := by
  have : IsNoetherian R (ModuleCat.of R R) := inferInstanceAs (IsNoetherian R R)
  exact (II_9_b_iff_c fs i).mpr (II_11 (ModuleCat.of R R) fs i hi) E

end SGA.SGA2.ExposeII
