/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.ExtColimitSequence
import SGA.SGA2.ExposeII.KoszulExtComparisonZero
import SGA.SGA2.ExposeII.KoszulProZero

/-!
# SGA 2, Exposé II, Theorem 8: the actual Ext-to-Koszul comparison

The comparison induced by the augmentation of a projective Koszul complex
commutes with the coefficient connecting maps. Passing to the power colimits
therefore gives a morphism of cohomological sequences. Over a noetherian ring,
dimension shifting and the vanishing theorem II.11 show that this actual
comparison is an isomorphism in every degree.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The augmented-projective-complex comparison respects the actual Ext boundary. -/
@[reassoc]
theorem extToHomComplexCohomology_extCoefficientδ
    (K : ChainComplex (ModuleCat.{u} R) ℕ) [∀ i, Projective (K.X i)]
    {X : ModuleCat.{u} R} (a : K ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj X)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    extCoefficientδ X S hS i ≫ extToHomComplexCohomology K a S.X₁ (i + 1) =
      extToHomComplexCohomology K a S.X₃ i ≫ homCohomologyδ K S hS i := by
  simpa only [extCoefficientδ, Category.assoc] using
    extToHomComplexCohomology_δ K a S hS i

/-- The finite-stage comparison is a morphism of coefficient connecting sequences. -/
def koszulExtComparisonConnectingHom (fs : List R) :
    ConnectingSequence.Hom
      (extConnectingSequence (ModuleCat.of R (R ⧸ koszulIdeal fs)))
      (homCohomologyConnectingSequence (koszulComplex (ModuleCat.of R R) fs)) where
  app i := koszulExtComparisonNatTrans fs i
  comm S hS i := extToHomComplexCohomology_extCoefficientδ _ (koszulAugmentation fs) S hS i

/-- Positive-degree generator-power Ext colimits vanish on injective coefficients. -/
theorem stableKoszulExtFunctor_isZero_of_injective (fs : List R)
    (E : ModuleCat.{u} R) [Injective E] (i : ℕ) :
    IsZero ((stableKoszulExtFunctor fs (i + 1)).obj E) :=
  isZero_extColimitFunctor_succ_of_injective (koszulQuotientSystem fs) E i

/-- II.(7.6) is a morphism of the actual coefficient connecting sequences. -/
def stableKoszulExtComparisonConnectingHom (fs : List R) :
    ConnectingSequence.Hom (stableKoszulExtConnectingSequence fs)
      (stableKoszulConnectingSequence fs) where
  app i := stableKoszulExtComparisonNatTrans fs i
  comm S hS i := by
    change colim.map _ ≫ colim.map _ = colim.map _ ≫ colim.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply NatTrans.ext
    funext n
    exact (koszulExtComparisonConnectingHom (fs.map fun f => f ^ n.unop.unop)).comm S hS i

/-- II.9(b) implies II.9(a) for the actual map (7.6), by dimension shifting. -/
theorem stableKoszulExtComparison_isIso_of_vanishesOnInjectives (fs : List R)
    (hfs : (stableKoszulConnectingSequence fs).VanishesOnInjectives)
    (E : ModuleCat.{u} R) (i : ℕ) : IsIso (stableKoszulExtComparison fs E i) :=
  ConnectingSequence.Hom.isIso_of_degree_zero
    (stableKoszulExtComparisonConnectingHom fs)
    (stableKoszulExtConnectingSequence_vanishesOnInjectives fs) hfs
    (fun E => stableKoszulExtComparison_zero_isIso fs E) i E

/-- II.9(a) ⇔ (b), for the constructed comparison (7.6) over any commutative ring. -/
theorem II_9_a_iff_b (fs : List R) :
    (∀ (i : ℕ) (E : ModuleCat.{u} R), IsIso (stableKoszulExtComparison fs E i)) ↔
      (stableKoszulConnectingSequence fs).VanishesOnInjectives := by
  constructor
  · intro h E hE i
    have := h (i + 1) E
    exact (stableKoszulExtFunctor_isZero_of_injective fs E i).of_iso
      (asIso (stableKoszulExtComparison fs E (i + 1))).symm
  · intro h i E
    exact stableKoszulExtComparison_isIso_of_vanishesOnInjectives fs h E i

/-- II.9(a) ⇔ (c): the actual Ext comparison is invertible in all degrees
exactly when the positive Koszul homology systems are essentially zero. -/
theorem II_9_a_iff_c (fs : List R) :
    (∀ (i : ℕ) (E : ModuleCat.{u} R), IsIso (stableKoszulExtComparison fs E i)) ↔
      ∀ i : ℕ, 0 < i →
        IsEssentiallyZero (koszulHomologySystem (ModuleCat.of R R) fs i) := by
  rw [II_9_a_iff_b]
  constructor
  · intro h i hi
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    exact (II_9_b_iff_c fs (i + 1)).mp (fun E _ => h E i)
  · intro h E hE i
    exact (II_9_b_iff_c fs (i + 1)).mpr (h (i + 1) (by omega)) E

/-- II.8: over a noetherian ring the canonical comparison (7.6) is an
isomorphism in every degree, for every coefficient module. -/
instance stableKoszulExtComparison_isIso [IsNoetherianRing R]
    (fs : List R) (E : ModuleCat.{u} R) (i : ℕ) :
    IsIso (stableKoszulExtComparison fs E i) :=
  stableKoszulExtComparison_isIso_of_vanishesOnInjectives fs
    (fun E _ i => stableKoszulCohomology_isZero_of_injective fs E (i + 1) (by omega)) E i

/-- II.8, stated directly for the constructed generator-power Ext comparison. -/
theorem II_8 [IsNoetherianRing R] (fs : List R) (E : ModuleCat.{u} R) (i : ℕ) :
    IsIso (stableKoszulExtComparison fs E i) := inferInstance

instance stableKoszulExtComparisonNatTrans_isIso [IsNoetherianRing R]
    (fs : List R) (i : ℕ) : IsIso (stableKoszulExtComparisonNatTrans fs i) := by
  have : ∀ E, IsIso ((stableKoszulExtComparisonNatTrans fs i).app E) :=
    fun E => stableKoszulExtComparison_isIso fs E i
  exact NatIso.isIso_of_isIso_app _

/-- The canonical comparison isomorphism of II.8, naturally in coefficients. -/
def stableKoszulExtComparisonIso [IsNoetherianRing R] (fs : List R) (i : ℕ) :
    stableKoszulExtFunctor fs i ≅ stableKoszulCohomologyFunctor fs i :=
  asIso (stableKoszulExtComparisonNatTrans fs i)

@[simp]
theorem stableKoszulExtComparisonIso_hom_app [IsNoetherianRing R]
    (fs : List R) (i : ℕ) (E : ModuleCat.{u} R) :
    (stableKoszulExtComparisonIso fs i).hom.app E = stableKoszulExtComparison fs E i := rfl

end SGA.SGA2.ExposeII
