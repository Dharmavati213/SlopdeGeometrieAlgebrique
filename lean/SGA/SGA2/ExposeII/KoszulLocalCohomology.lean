/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulComparisonIsomorphism
import SGA.SGA2.ExposeII.FiniteGeneratorColimits

/-!
# SGA 2, Exposé II, (7.3)–(7.6) and Lemma 8: algebraic local cohomology

Cofinality of generator powers identifies the source of the actual
Ext-to-Koszul comparison with mathlib's ideal-power definition of algebraic
local cohomology. Over a noetherian ring this yields isomorphisms in all
degrees, natural in the coefficient module. The target here is stable
Koszul cohomology; a comparison with higher supported sheaf cohomology is
a separate geometric theorem.
-/

noncomputable section

universe u v

open CategoryTheory Limits

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R]

/-- Pointwise colimits recover mathlib's colimit of coefficient functors. -/
def stableKoszulExtIsoOfDiagram (fs : List R) (i : ℕ) :
    stableKoszulExtFunctor fs i ≅
      localCohomology.ofDiagram (koszulGeneratorIdeals fs) i :=
  (colimitIsoFlipCompColim (localCohomology.diagram (koszulGeneratorIdeals fs) i)).symm

/-- The generator-power comparison transported to equal ideal diagrams
and equal support ideals. -/
def generatorPowersLocalCohomologyIsoOfEq {ι : Type v} [Finite ι]
    (f : ι → R) (D : Opposite ℕ ⥤ Ideal R) (I : Ideal R)
    (hD : D = generatorPowersDiagram f) (hI : I = Ideal.span (Set.range f)) (i : ℕ) :
    localCohomology.ofDiagram D i ≅ _root_.localCohomology I i := by
  subst D I
  exact generatorPowersLocalCohomologyIso f i

/-- The source of (7.6) is naturally the ideal-power Ext colimit in (7.3). -/
def stableKoszulExtIsoLocalCohomology (fs : List R) (i : ℕ) :
    stableKoszulExtFunctor fs i ≅ _root_.localCohomology (koszulIdeal fs) i :=
  stableKoszulExtIsoOfDiagram fs i ≪≫
    generatorPowersLocalCohomologyIsoOfEq (fun j : Fin fs.length ↦ fs.get j)
      (koszulGeneratorIdeals fs) (koszulIdeal fs)
      (koszulIdealPowersDiagram_eq_generatorPowersDiagram fs) (koszulIdeal_eq_span_get fs) i

/-- The canonical algebraic comparison, now expressed using ordinary ideal powers. -/
def localCohomologyToStableKoszul (fs : List R) (i : ℕ) :
    _root_.localCohomology (koszulIdeal fs) i ⟶ stableKoszulCohomologyFunctor fs i :=
  (stableKoszulExtIsoLocalCohomology fs i).inv ≫ stableKoszulExtComparisonNatTrans fs i

/-- II.8 together with the cofinal reindexing (7.3)–(7.4). -/
instance localCohomologyToStableKoszul_isIso [IsNoetherianRing R]
    (fs : List R) (i : ℕ) : IsIso (localCohomologyToStableKoszul fs i) :=
  inferInstanceAs (IsIso
    ((stableKoszulExtIsoLocalCohomology fs i).inv ≫ stableKoszulExtComparisonNatTrans fs i))

/-- Over a noetherian ring, algebraic local cohomology is stable Koszul
cohomology, naturally in every coefficient module and in every degree. -/
def localCohomologyIsoStableKoszul [IsNoetherianRing R] (fs : List R) (i : ℕ) :
    _root_.localCohomology (koszulIdeal fs) i ≅ stableKoszulCohomologyFunctor fs i :=
  asIso (localCohomologyToStableKoszul fs i)

end SGA.SGA2.ExposeII
