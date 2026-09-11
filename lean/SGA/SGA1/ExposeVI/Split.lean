/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Opposites

/-!
# SGA 1, Exposé VI, VI.8–VI.9: Grothendieck construction and split categories

VI.8 reconstructs a normalized cloven fibered category from a pseudofunctor
`Eᵒᵖ → Cat`. Mathlib's `∫ᶜ F` (`Pseudofunctor.CoGrothendieck`) is that
construction, in the fibered case where the comparison 2-cells `mapComp`
are isomorphisms. Cartesian lifts are `cartesianLift`, i.e. pairs `(f, 𝟙)`.

VI.9 specialises to a 1-functor `φ : Eᵒᵖ ⥤ Cat`, equivalently a
pseudofunctor with `c_{f,g} = id` (implemented as `eqToIso` of `map_comp`).
The associated split fibered category is `SplitFibered φ`.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Opposite
open CategoryTheory.Pseudofunctor

variable {E : Type u₁} [Category.{v₁} E]

/-! ### VI.8: cloven fibered category from a pseudofunctor -/

variable (Fψ : Pseudofunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂})

/-- VI.8: the CoGrothendieck construction of a pseudofunctor
`LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat` is fibered over `E`. -/
theorem cogrothendieck_isFibered : IsFibered (CoGrothendieck.forget Fψ) :=
  inferInstance

/-- VI.8: it is in particular prefibered. -/
theorem cogrothendieck_isPreFibered : IsPreFibered (CoGrothendieck.forget Fψ) :=
  inferInstance

/-- VI.8(5): the chosen lift of `f` at `ξ` is the transport morphism `(f, 𝟙)`,
and it is strongly cartesian. -/
theorem cogrothendieck_isStronglyCartesian_cartesianLift {S : E}
    (a : Fψ.obj ⟨op S⟩) {R : E} (f : R ⟶ S) :
    IsStronglyCartesian (CoGrothendieck.forget Fψ) f
      (CoGrothendieck.cartesianLift a f) :=
  CoGrothendieck.isStronglyCartesian_homCartesianLift a f

/-- VI.8(4): the fiber over `S` is equivalent to `F(S)`. -/
noncomputable def cogrothendieck_fiberEquiv (S : E) :
    Fψ.obj ⟨op S⟩ ≌ Fiber (CoGrothendieck.forget Fψ) S :=
  (HasFibers.inducedFunctor (CoGrothendieck.forget Fψ) S).asEquivalence

variable {Fψ}

/-! ### VI.9: split fibered category from a functor `Eᵒᵖ ⥤ Cat` -/

/-- VI.9: the split fibered category associated to a functor `φ : Eᵒᵖ ⥤ Cat`. -/
abbrev SplitFibered (F : Eᵒᵖ ⥤ Cat.{v₂, u₂}) :=
  CoGrothendieck F.toPseudofunctor'

namespace SplitFibered

variable (F : Eᵒᵖ ⥤ Cat.{v₂, u₂})

/-- VI.9: the projection of the split category to the base. -/
abbrev forget : SplitFibered F ⥤ E :=
  CoGrothendieck.forget F.toPseudofunctor'

/-- VI.9: a split category is fibered. -/
theorem forget_isFibered : IsFibered (forget F) :=
  cogrothendieck_isFibered F.toPseudofunctor'

/-- VI.9: a split category is prefibered. -/
theorem forget_isPreFibered : IsPreFibered (forget F) :=
  cogrothendieck_isPreFibered F.toPseudofunctor'

instance : IsFibered (forget F) :=
  forget_isFibered F

/-- The fiber category `φ(S)` as it appears in the Grothendieck construction. -/
abbrev fiberCat (S : E) := F.toPseudofunctor'.obj ⟨op S⟩

/-- VI.8(4): the Grothendieck fiber is the value of the original functor. -/
theorem fiberCat_eq (S : E) : fiberCat F S = F.obj (op S) :=
  Functor.toPseudofunctor'_obj F ⟨op S⟩

/-- Inverse image functor `f^* : φ(S) ⥤ φ(T)`. -/
abbrev pullback {S T : E} (f : T ⟶ S) : fiberCat F S ⥤ fiberCat F T :=
  (F.toPseudofunctor'.map f.op.toLoc).toFunctor

/-- VI.9 / VI.8(4): the fiber over `S` is equivalent to `φ(S)`. -/
noncomputable def fiberEquiv (S : E) :
    fiberCat F S ≌ Fiber (forget F) S :=
  cogrothendieck_fiberEquiv F.toPseudofunctor' S

end SplitFibered

end SGA.SGA1.ExposeVI
