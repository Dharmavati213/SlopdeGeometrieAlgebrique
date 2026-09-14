/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.FiniteGenerators
import Mathlib.Algebra.Homology.LocalCohomology

/-!
# SGA 2, Exposé II, (7.3)–(7.4): reindexing the Ext colimit

For a finite family generating `I`, the colimits of `Ext(R/I^n, -)` and
`Ext(R/(fₐ^n), -)` agree in every degree. Both diagrams are initial in the
category of ideals whose radical contains `I`. Finite generation of `I`
suffices for this reduction; no noetherian hypothesis on the ring is needed.

These are isomorphisms of module-valued functors. The comparison with sheaf
or Koszul cohomology is not assumed or established here.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R]

/-- The ideal-power diagram is initial among ideals whose radical contains
`I` whenever `I` is finitely generated. -/
theorem idealPowersToSelfLERadical_initial_of_fg (I : Ideal R) (hI : I.FG) :
    Functor.Initial (localCohomology.idealPowersToSelfLERadical I) where
  out J := by
    apply +allowSynthFailures zigzag_isConnected
    · obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg J.2 hI
      exact ⟨CostructuredArrow.mk
        (⟨⟨⟨hk⟩⟩⟩ : (localCohomology.idealPowersToSelfLERadical I).obj (op k) ⟶ J)⟩
    · intro j₁ j₂
      apply Relation.ReflTransGen.single
      rcases le_total j₁.left.unop j₂.left.unop with h | h
      · right; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
      · left; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

variable {ι : Type v} (f : ι → R)

/-- The decreasing ideal diagram `(fₐ^n)` from II.(7.4). -/
def generatorPowersDiagram : ℕᵒᵖ ⥤ Ideal R where
  obj n := generatorPowerIdeal f n.unop
  map h := homOfLE (generatorPowerIdeal_antitone f (leOfHom h.unop))

/-- The generator-power diagram lies in the same radical indexing category
as the ordinary ideal-power diagram. -/
def generatorPowersToSelfLERadical :
    ℕᵒᵖ ⥤ localCohomology.SelfLERadical (Ideal.span (Set.range f)) :=
  ObjectProperty.lift _ (generatorPowersDiagram f)
    (fun n => span_le_radical_generatorPowerIdeal f n.unop)

/-- II.(7.4): the generator-power diagram is initial in the radical diagram. -/
instance generatorPowersToSelfLERadical_initial [Finite ι] :
    Functor.Initial (generatorPowersToSelfLERadical f) where
  out J := by
    apply +allowSynthFailures zigzag_isConnected
    · obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg J.2
        (Submodule.fg_span (Set.finite_range f))
      exact ⟨CostructuredArrow.mk
        (⟨⟨⟨(generatorPowerIdeal_le_pow f k).trans hk⟩⟩⟩ :
          (generatorPowersToSelfLERadical f).obj (op k) ⟶ J)⟩
    · intro j₁ j₂
      apply Relation.ReflTransGen.single
      rcases le_total j₁.left.unop j₂.left.unop with h | h
      · right; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
      · left; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

/-- II.(7.3)–(7.4): replacing ideal powers by powers of the individual
generators leaves the Ext colimit unchanged, naturally in the module. -/
def generatorPowersLocalCohomologyIso [Finite ι] (i : ℕ) :
    localCohomology.ofDiagram (generatorPowersDiagram f) i ≅
      _root_.localCohomology (Ideal.span (Set.range f)) i := by
  let I := Ideal.span (Set.range f)
  letI := idealPowersToSelfLERadical_initial_of_fg I
    (Submodule.fg_span (Set.finite_range f))
  exact localCohomology.isoOfFinal (generatorPowersToSelfLERadical f)
      (localCohomology.selfLERadicalDiagram I) i ≪≫
    (localCohomology.isoOfFinal (localCohomology.idealPowersToSelfLERadical I)
      (localCohomology.selfLERadicalDiagram I) i).symm

end SGA.SGA2.ExposeII
