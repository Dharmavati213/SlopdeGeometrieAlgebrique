/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.BasedEquivalences
import SGA.SGA1.ExposeVI.Groupoids
import Mathlib.CategoryTheory.CodiscreteCategory

/-!
# SGA 1, Exposé VI: checks on the hypotheses of §§1–4

These finite examples demonstrate why both quasi-inverse identities in
VI.1, and the condition on fibers in VI.4.2, are essential. In particular,
ordinary categorical equivalence is weaker than equivalence over a base.
-/

namespace SGA.SGA1.ExposeVI.Examples

open CategoryTheory

/-- Include one object into a discrete category with two objects. -/
def selectFalse : Discrete Unit ⥤ Discrete Bool := Discrete.functor (fun _ ↦ ⟨false⟩)

/-- Collapse the two-object discrete category to one object. -/
def collapse : Discrete Bool ⥤ Discrete Unit := Discrete.functor (fun _ ↦ ⟨()⟩)

/-- The composite in one direction is naturally isomorphic to the identity. -/
def oneSidedUnit : 𝟭 (Discrete Unit) ≅ selectFalse ⋙ collapse :=
  Discrete.natIso (fun _ ↦ eqToIso (Subsingleton.elim _ _))

/-- VI.1: a one-sided quasi-inverse alone does not imply equivalence. -/
theorem selectFalse_not_isEquivalence : ¬ selectFalse.IsEquivalence := by
  intro h
  let e := selectFalse.objObjPreimageIso (Discrete.mk true)
  have hfalse : false = true := e.hom.eq
  cases hfalse

/-- The codiscrete two-object groupoid has isomorphic but unequal objects. -/
def oneToTwo : Codiscrete Unit ⥤ Codiscrete Bool := Codiscrete.functor (fun _ ↦ false)

instance : oneToTwo.Full where
  map_surjective _ := ⟨default, Subsingleton.elim _ _⟩

instance : oneToTwo.Faithful where
  map_injective _ := Subsingleton.elim _ _

instance : oneToTwo.EssSurj where
  mem_essImage y := ⟨⟨()⟩, ⟨Codiscrete.iso _ y⟩⟩

/-- This functor is an ordinary equivalence. -/
instance : oneToTwo.IsEquivalence where

/-- Regard the same functor as a functor over its two-object codomain. -/
def oneToTwoOver : BasedFunctor (BasedCategory.ofFunctor oneToTwo)
    (BasedCategory.ofFunctor (𝟭 (Codiscrete Bool))) where
  toFunctor := oneToTwo

/-- VI.4.1–2: an ordinary equivalence need not be an equivalence over the base.
The fiber over `true` is missing from the source. -/
theorem oneToTwo_not_basedEquivalence : ¬ IsBasedEquivalence oneToTwoOver := by
  intro h
  obtain ⟨x, e, he⟩ := (isBasedEquivalence_iff oneToTwoOver).mp h |>.2.2 (Codiscrete.mk true)
  have hfalse : Codiscrete.mk false = Codiscrete.mk true :=
    @IsHomLift.domain_eq _ _ _ _ (𝟭 (Codiscrete Bool)) _ _ _ _
      (𝟙 (Codiscrete.mk true)) e.hom he
  cases hfalse

/-- Every arrow in the one-object codiscrete category is invertible, hence cartesian. -/
theorem oneToTwo_all_cartesian : AllMorphismsCartesian oneToTwo := by
  intro R S f a b φ hφ
  have : IsIso φ := by
    rw [Codiscrete.eq_iso_hom φ]
    infer_instance
  infer_instance

/-- VI.6.1, remark: all morphisms being cartesian does not supply missing lifts. -/
theorem oneToTwo_not_prefibered : ¬ oneToTwo.IsPreFibered := by
  intro h
  let a : Codiscrete Unit := ⟨()⟩
  let f : Codiscrete.mk true ⟶ oneToTwo.obj a := (Codiscrete.iso _ _).hom
  obtain ⟨b, φ, hφ⟩ := CategoryTheory.Functor.IsPreFibered.exists_isCartesian'
    (p := oneToTwo) f
  have hfalse : Codiscrete.mk false = Codiscrete.mk true :=
    IsHomLift.domain_eq oneToTwo f φ
  cases hfalse

end SGA.SGA1.ExposeVI.Examples
