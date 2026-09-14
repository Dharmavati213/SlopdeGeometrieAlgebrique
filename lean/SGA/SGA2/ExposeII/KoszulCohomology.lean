/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.KoszulComplex
import SGA.SGA2.ExposeII.InjectiveHomology
import SGA.SGA2.ExposeII.InjectiveLocalCohomology

/-!
# SGA 2, Exposé II, Lemma 9: Koszul cohomology and essential vanishing

The cohomology at a finite stage is the homology of the genuine Hom cochain
complex of the Koszul chain complex over the ring. Its direct limit over
powers of the generators is the stable Koszul cohomology in II.5–II.9.
For injective coefficients, comparison with Hom of Koszul homology proves
both directions of II.9(b) ⇔ (c).
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R]

/-- Koszul cohomology at a finite stage, defined from the Hom cochain complex. -/
def koszulCohomology (fs : List R) (E : ModuleCat.{u} R) (i : ℕ) : ModuleCat.{u} R :=
  ((koszulComplex (ModuleCat.of R R) fs).linearYonedaObj R E).homology i

/-- The direct system in the definition of stable Koszul cohomology. -/
def koszulCohomologyDiagram (fs : List R) (E : ModuleCat.{u} R) (i : ℕ) :
    ℕᵒᵖᵒᵖ ⥤ ModuleCat.{u} R :=
  homComplexCohomologyDiagram (ComplexShape.down ℕ)
    (koszulSystem (ModuleCat.of R R) fs) E i

/-- The direct-limit Koszul cohomology denoted `H^i((f), E)` in II.5–II.9. -/
def stableKoszulCohomology (fs : List R) (E : ModuleCat.{u} R) (i : ℕ) : ModuleCat.{u} R :=
  colimit (koszulCohomologyDiagram fs E i)

/-- For injective coefficients, Koszul cohomology is Hom of Koszul homology. -/
def koszulCohomologyIsoHom (fs : List R) (E : ModuleCat.{u} R) [Injective E] (i : ℕ) :
    koszulCohomology fs E i ≅
      ModuleCat.of R ((koszulComplex (ModuleCat.of R R) fs).homology i ⟶ E) :=
  linearYonedaObjHomologyIso _ E i

/-- The finite-stage comparisons commute with the actual Koszul transition
maps, hence induce a comparison of their colimits. -/
def stableKoszulCohomologyIsoHomColimit
    (fs : List R) (E : ModuleCat.{u} R) [Injective E] (i : ℕ) :
    stableKoszulCohomology fs E i ≅
      colimit ((koszulHomologySystem (ModuleCat.of R R) fs i).op ⋙
        (linearYoneda R (ModuleCat.{u} R)).obj E) :=
  homComplexCohomologyColimitIso (ComplexShape.down ℕ) _ E i

/-- II.9(b) ⇔ (c), for the actual Koszul complexes of a finite list. -/
theorem II_9_b_iff_c (fs : List R) (i : ℕ) :
    (∀ (E : ModuleCat.{u} R) [Injective E], IsZero (stableKoszulCohomology fs E i)) ↔
      IsEssentiallyZero (koszulHomologySystem (ModuleCat.of R R) fs i) :=
  (isEssentiallyZero_homology_iff_isZero_cohomology_colimit
    (ComplexShape.down ℕ) (koszulSystem (ModuleCat.of R R) fs) i).symm

/-- II.9(a) ⇒ (b), at a positive degree: a comparison isomorphism with
the Ext-colimit definition implies vanishing on injective coefficients. -/
theorem II_9_a_implies_b (fs : List R) (I : Ideal R) (i : ℕ) (hi : 0 < i)
    (comparison : ∀ E : ModuleCat.{u} R,
      (_root_.localCohomology I i).obj E ≅ stableKoszulCohomology fs E i)
    (E : ModuleCat.{u} R) [Injective E] : IsZero (stableKoszulCohomology fs E i) :=
  (isZero_localCohomology_of_injective I E i hi).of_iso (comparison E).symm

end SGA.SGA2.ExposeII
