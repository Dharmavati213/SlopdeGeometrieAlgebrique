/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulCohomology
import SGA.SGA2.ExposeII.KoszulDegreeZero
import SGA.SGA2.ExposeII.GeneratorHomColimit

/-!
# SGA 2, Exposé II, (7.5): degree-zero Koszul cohomology

For arbitrary coefficients, degree-zero cohomology of the Hom complex of a
nonnegative chain complex is Hom of its degree-zero homology. The comparison
is natural in chain maps and therefore passes to direct limits of inverse
chain systems. The quotient calculation of zeroth Koszul homology then
identifies finite-stage degree-zero Koszul cohomology with the annihilator
of the generated ideal, and stable degree-zero cohomology with ideal-power
torsion. These comparisons hold for arbitrary coefficient modules.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeII

attribute [local instance 2000] CategoryWithHomology.hasHomology

variable {R : Type u} [CommRing R]

/-- In degree zero, the opposite chain complex has no incoming
differential, so preserving kernels suffices to preserve its homology. -/
instance linearYonedaObj_preservesLeftHomology_zero
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (E : ModuleCat.{u} R) :
    ((linearYoneda R (ModuleCat.{u} R)).obj E).PreservesLeftHomologyOf (K.op.sc 0) := by
  apply Functor.preservesLeftHomology_of_zero_f
  change (K.d 0 _).op = 0
  rw [K.shape _ _ (by simp)]
  rfl

/-- Degree-zero cohomology of Hom agrees with Hom of degree-zero homology,
without any injectivity assumption on the coefficient module. -/
def homComplexHomologyZeroIso (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (E : ModuleCat.{u} R) :
    ((homComplexFunctor (ComplexShape.down ℕ) E).obj (op K)).homology 0 ≅
      ModuleCat.of R (K.homology 0 ⟶ E) :=
  (K.op.sc 0).mapHomologyIso ((linearYoneda R (ModuleCat.{u} R)).obj E) ≪≫
    ((linearYoneda R (ModuleCat.{u} R)).obj E).mapIso (K.homologyOp 0)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero Hom comparison commutes with chain maps. -/
@[reassoc]
theorem homComplexHomologyZeroIso_hom_naturality
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (E : ModuleCat.{u} R) :
    HomologicalComplex.homologyMap
        ((homComplexFunctor (ComplexShape.down ℕ) E).map f.op) 0 ≫
        (homComplexHomologyZeroIso K E).hom =
      (homComplexHomologyZeroIso L E).hom ≫
        ((linearYoneda R (ModuleCat.{u} R)).obj E).map
          (HomologicalComplex.homologyMap f 0).op := by
  let H := (linearYoneda R (ModuleCat.{u} R)).obj E
  let φ : L.op.sc 0 ⟶ K.op.sc 0 :=
    (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) 0).map
      ((HomologicalComplex.opFunctor _ (ComplexShape.down ℕ)).map f.op)
  change ShortComplex.homologyMap (H.mapShortComplex.map φ) ≫
      ((K.op.sc 0).mapHomologyIso H).hom ≫ H.map (K.homologyOp 0).hom =
    (((L.op.sc 0).mapHomologyIso H).hom ≫ H.map (L.homologyOp 0).hom) ≫
      H.map (HomologicalComplex.homologyMap f 0).op
  rw [← Category.assoc, ShortComplex.mapHomologyIso_hom_naturality,
    Category.assoc, ← Functor.map_comp]
  change ((L.op.sc 0).mapHomologyIso H).hom ≫
    H.map (HomologicalComplex.homologyMap
      ((HomologicalComplex.opFunctor _ (ComplexShape.down ℕ)).map f.op) 0 ≫
      (K.homologyOp 0).hom) = _
  rw [HomologicalComplex.homologyOp_hom_naturality]
  simp only [Functor.map_comp, Category.assoc]

/-- The degree-zero Hom comparison as a natural isomorphism. -/
def homComplexHomologyZeroNatIso (E : ModuleCat.{u} R) :
    homComplexFunctor (ComplexShape.down ℕ) E ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) 0 ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).op ⋙
        (linearYoneda R (ModuleCat.{u} R)).obj E :=
  NatIso.ofComponents (fun K => homComplexHomologyZeroIso K.unop E)
    (fun f => homComplexHomologyZeroIso_hom_naturality f.unop E)

/-- The degree-zero comparison for mathlib's standard Hom cochain complex. -/
def linearYonedaObjHomologyZeroIso (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (E : ModuleCat.{u} R) :
    (K.linearYonedaObj R E).homology 0 ≅ ModuleCat.of R (K.homology 0 ⟶ E) :=
  homComplexHomologyZeroIso K E

/-- For arbitrary coefficients, the direct limit of degree-zero Hom
cohomology is the direct limit of Hom of the zeroth homology system. -/
def homComplexCohomologyZeroColimitIso
    (K : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ) (E : ModuleCat.{u} R) :
    colimit (homComplexCohomologyDiagram (ComplexShape.down ℕ) K E 0) ≅
      colimit ((K ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) 0).op ⋙
        (linearYoneda R (ModuleCat.{u} R)).obj E) :=
  HasColimit.isoOfNatIso (Functor.isoWhiskerLeft K.op (homComplexHomologyZeroNatIso E))

/-- The degree-zero stable Koszul comparison with Hom of zeroth Koszul
homology, valid for arbitrary coefficient modules. -/
def stableKoszulCohomologyZeroIsoHomColimit (fs : List R) (E : ModuleCat.{u} R) :
    stableKoszulCohomology fs E 0 ≅
      colimit ((koszulHomologySystem (ModuleCat.of R R) fs 0).op ⋙
        (linearYoneda R (ModuleCat.{u} R)).obj E) :=
  homComplexCohomologyZeroColimitIso _ E

/-- The ideal generated by a list equals the ideal of its finite indexed family. -/
theorem koszulIdeal_eq_span_get (fs : List R) :
    koszulIdeal fs = Ideal.span (Set.range (fun j : Fin fs.length => fs.get j)) := by
  unfold koszulIdeal
  congr 1
  ext x
  exact List.mem_iff_get

/-- Taking powers of a list gives the same ideal as taking powers of its
finite indexed family. -/
theorem koszulIdeal_map_pow_eq_generatorPowerIdeal (fs : List R) (n : ℕ) :
    koszulIdeal (fs.map fun f => f ^ n) =
      generatorPowerIdeal (fun j : Fin fs.length => fs.get j) n := by
  unfold koszulIdeal generatorPowerIdeal
  congr 1
  ext x
  change x ∈ fs.map (fun f => f ^ n) ↔ ∃ j : Fin fs.length, fs.get j ^ n = x
  rw [List.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hf
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨fs.get j, List.get_mem _ _, rfl⟩

/-- The inverse diagram of ideals generated by the powered Koszul lists. -/
def koszulIdealPowersDiagram (fs : List R) : ℕᵒᵖ ⥤ Ideal R where
  obj n := koszulIdeal (fs.map fun f => f ^ n.unop)
  map h := homOfLE (koszulIdeal_pow_antitone fs (leOfHom h.unop))

/-- The list-based and finite-family ideal diagrams coincide. -/
theorem koszulIdealPowersDiagram_eq_generatorPowersDiagram (fs : List R) :
    koszulIdealPowersDiagram fs =
      generatorPowersDiagram (fun j : Fin fs.length => fs.get j) := by
  refine CategoryTheory.Functor.ext
    (fun n => koszulIdeal_map_pow_eq_generatorPowerIdeal fs n.unop) ?_
  intros
  apply Subsingleton.elim

/-- Zeroth Koszul homology, including its inverse transitions, is the
system of quotient rings by the ideals generated by powers. -/
def koszulHomologyZeroSystemIsoQuotients (fs : List R) :
    koszulHomologySystem (ModuleCat.of R R) fs 0 ≅
      localCohomology.ringModIdeals (koszulIdealPowersDiagram fs) :=
  NatIso.ofComponents
    (fun n => koszulHomologyZeroIsoQuotient (fs.map fun f => f ^ n.unop))
    (fun h => koszulHomologyZeroIsoQuotient_naturality fs (leOfHom h.unop))

/-- Zeroth Koszul homology agrees with the quotient-ring diagram used in
the finite-generator local cohomology comparison. -/
def koszulHomologyZeroSystemIsoGeneratorQuotients (fs : List R) :
    koszulHomologySystem (ModuleCat.of R R) fs 0 ≅
      localCohomology.ringModIdeals
        (generatorPowersDiagram (fun j : Fin fs.length => fs.get j)) := by
  rw [← koszulIdealPowersDiagram_eq_generatorPowersDiagram]
  exact koszulHomologyZeroSystemIsoQuotients fs

/-- Degree-zero finite-stage Koszul cohomology consists of the elements
annihilated by the ideal generated by the list. -/
def koszulCohomologyZeroIsoAnnihilator (fs : List R) (E : ModuleCat.{u} R) :
    koszulCohomology fs E 0 ≅
      ModuleCat.of R (Submodule.torsionBySet R E (koszulIdeal fs)) :=
  linearYonedaObjHomologyZeroIso _ E ≪≫
    ((linearYoneda R (ModuleCat.{u} R)).obj E).mapIso
      (koszulHomologyZeroIsoQuotient fs).op.symm ≪≫
    (ModuleCat.homLinearEquiv.trans (quotientHomEquivTorsionBySet (koszulIdeal fs) E)).toModuleIso

/-- II.(7.5), algebraic Koszul comparison in degree zero: stable Koszul
cohomology is ideal-power torsion for arbitrary coefficient modules. -/
def stableKoszulCohomologyZeroIsoPowerTorsion (fs : List R) (E : ModuleCat.{u} R) :
    stableKoszulCohomology fs E 0 ≅ ModuleCat.of R (powerTorsion (koszulIdeal fs) E) := by
  rw [koszulIdeal_eq_span_get]
  exact stableKoszulCohomologyZeroIsoHomColimit fs E ≪≫
    HasColimit.isoOfNatIso
      (Functor.isoWhiskerRight (NatIso.op (koszulHomologyZeroSystemIsoGeneratorQuotients fs)).symm
        ((linearYoneda R (ModuleCat.{u} R)).obj E)) ≪≫
    (colimitObjIsoColimitCompEvaluation
      (generatorHomDiagram (fun j : Fin fs.length => fs.get j)) E).symm ≪≫
    (generatorHomColimitIso (fun j : Fin fs.length => fs.get j)).app E

end SGA.SGA2.ExposeII
