/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.EssentiallyZero
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-!
# SGA 2, Exposé II, Lemma 9: detection by injective coefficients

An inverse sequence of modules is essentially zero if and only if the direct
limit of its module-valued Hom diagram vanishes for every injective coefficient
module. This proves the diagram argument in II.9(b) ⇒ (c): embed a term in an
injective module, use eventual vanishing of its class in a filtered colimit,
and cancel the embedding. Together with the converse from `EssentiallyZero`,
this also gives the equivalence with vanishing for every coefficient module.

The comparison between Koszul cohomology and Hom of Koszul homology is not
part of these statements.
-/

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R] (F : ℕᵒᵖ ⥤ ModuleCat.{u} R)

/-- II.9(b) ⇒ (c), the injective detection argument for inverse sequences
of modules. -/
theorem isEssentiallyZero_of_isZero_hom_colimit_injective
    (h : ∀ (E : ModuleCat.{u} R) [Injective E],
      IsZero (colimit (F.op ⋙ (linearYoneda R (ModuleCat.{u} R)).obj E))) :
    IsEssentiallyZero F := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  intro n
  let E := Injective.under (F.obj n)
  let j : F.obj n ⟶ E := Injective.ι (F.obj n)
  let D := F.op ⋙ (linearYoneda R (ModuleCat.{u} R)).obj E
  have : Subsingleton ↥(colimit D) := ModuleCat.subsingleton_of_isZero (h E)
  have hj : colimit.ι D (op n) j = colimit.ι D (op n) 0 := Subsingleton.elim _ _
  obtain ⟨k, f, hf⟩ := ((colimit.isColimit D).eq_iff' j 0).mp hj
  refine ⟨k.unop, f.unop, (cancel_mono j).mp ?_⟩
  change F.map f.unop ≫ j = F.map f.unop ≫ 0 at hf
  simpa using hf

/-- II.9(b) ⇔ (c), after expressing (b) as a Hom colimit: injective
coefficient modules detect whether an inverse sequence is essentially zero. -/
theorem isEssentiallyZero_iff_isZero_hom_colimit_injective :
    IsEssentiallyZero F ↔
      ∀ (E : ModuleCat.{u} R) [Injective E],
        IsZero (colimit (F.op ⋙ (linearYoneda R (ModuleCat.{u} R)).obj E)) := by
  constructor
  · intro hF E _
    exact hF.isZero_hom_colimit E
  · exact isEssentiallyZero_of_isZero_hom_colimit_injective F

/-- Vanishing of all Hom colimits is equivalent to essential vanishing
of the inverse sequence. -/
theorem isEssentiallyZero_iff_isZero_hom_colimit :
    IsEssentiallyZero F ↔
      ∀ M : ModuleCat.{u} R,
        IsZero (colimit (F.op ⋙ (linearYoneda R (ModuleCat.{u} R)).obj M)) := by
  constructor
  · exact fun hF M ↦ hF.isZero_hom_colimit M
  · intro h
    exact isEssentiallyZero_of_isZero_hom_colimit_injective F (fun E _ ↦ h E)

end SGA.SGA2.ExposeII
