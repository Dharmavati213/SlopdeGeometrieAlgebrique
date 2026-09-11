/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.CartesianFunctors
import SGA.SGA1.ExposeVI.Fibered

/-!
# SGA 1, Exposé VI, VI.6.2: (pre)fiberedness under based equivalence

A based equivalence preserves cartesian morphisms and their existence, so
it preserves and reflects being prefibered and being fibered.
-/

universe v v₁ v₂ u u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E]
  {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₂, u₂} E}

/-- VI.6.2: a based equivalence sends a prefibered source to a prefibered target. -/
theorem isPreFibered_of_isBasedEquivalence (F : BasedFunctor X Y)
    (hF : IsBasedEquivalence F) [IsPreFibered X.p] : IsPreFibered Y.p := by
  refine (isPreFibered_iff Y.p).mpr ?_
  intro y R f
  obtain ⟨_, _, hess⟩ := (isBasedEquivalence_iff F).mp hF
  obtain ⟨x, e, he⟩ := hess y
  have hx : X.p.obj x = Y.p.obj y :=
    (F.w_obj x).symm.trans (IsHomLift.domain_eq Y.p (𝟙 (Y.p.obj y)) e.hom)
  obtain ⟨a, φ, hφ⟩ := IsPreFibered.exists_isCartesian X.p hx f
  have : IsCartesian Y.p f (F.map φ) :=
    isCartesian_map_of_isBasedEquivalence F hF f φ
  have : IsHomLift Y.p (𝟙 (Y.p.obj y)) e.hom := he
  exact ⟨F.obj a, F.map φ ≫ e.hom, inferInstance⟩

/-- VI.6.2: a based equivalence reflects prefiberedness. -/
theorem isPreFibered_of_isBasedEquivalence_inverse (F : BasedFunctor X Y)
    (hF : IsBasedEquivalence F) [IsPreFibered Y.p] : IsPreFibered X.p := by
  obtain ⟨Q⟩ := hF
  exact isPreFibered_of_isBasedEquivalence Q.inverse Q.isBasedEquivalence_inverse

/-- VI.6.2: a based equivalence sends a fibered source to a fibered target. -/
theorem isFibered_of_isBasedEquivalence (F : BasedFunctor X Y)
    (hF : IsBasedEquivalence F) [IsFibered X.p] : IsFibered Y.p := by
  have : IsPreFibered Y.p := isPreFibered_of_isBasedEquivalence F hF
  refine (isFibered_iff_comp Y.p).mpr ?_
  intro R S T f g a b c φ ψ hφ hψ
  obtain ⟨Q⟩ := hF
  have : IsCartesian X.p f (Q.inverse.map φ) :=
    isCartesian_map_of_isBasedEquivalence Q.inverse Q.isBasedEquivalence_inverse f φ
  have : IsCartesian X.p g (Q.inverse.map ψ) :=
    isCartesian_map_of_isBasedEquivalence Q.inverse Q.isBasedEquivalence_inverse g ψ
  have : IsCartesian X.p (f ≫ g) (Q.inverse.map φ ≫ Q.inverse.map ψ) := inferInstance
  have : IsHomLift Y.p (f ≫ g) (φ ≫ ψ) := inferInstance
  have : Q.inverse.toFunctor.Full := Q.toEquivalence.full_inverse
  have : Q.inverse.toFunctor.Faithful := Q.toEquivalence.faithful_inverse
  have : IsCartesian X.p (f ≫ g) (Q.inverse.map (φ ≫ ψ)) := by
    simpa [Functor.map_comp] using
      ‹IsCartesian X.p (f ≫ g) (Q.inverse.map φ ≫ Q.inverse.map ψ)›
  exact isCartesian_of_map_of_fullyFaithful Q.inverse (f ≫ g) (φ ≫ ψ) ‹_›

/-- VI.6.2: a based equivalence reflects fiberedness. -/
theorem isFibered_of_isBasedEquivalence_inverse (F : BasedFunctor X Y)
    (hF : IsBasedEquivalence F) [IsFibered Y.p] : IsFibered X.p := by
  obtain ⟨Q⟩ := hF
  exact isFibered_of_isBasedEquivalence Q.inverse Q.isBasedEquivalence_inverse

end SGA.SGA1.ExposeVI
