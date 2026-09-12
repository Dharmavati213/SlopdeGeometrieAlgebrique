/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.Locus

/-!
# SGA 1, Exposé I, §3: unramified (net) morphisms

SGA says a finite-type morphism is *net* / *unramified* at `x` when the
residue extension is finite separable, equivalently when `Ω¹` vanishes at `x`,
equivalently when the diagonal is an open immersion near `x`. Mathlib splits
this into `FormallyUnramified` (`Ω¹ = 0`) and a finiteness hypothesis
(`FiniteType` / `LocallyOfFiniteType`); together they are SGA's net morphisms.
The historical synonym *net* is not used as a Lean name.
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry Algebra CategoryTheory CategoryTheory.Limits IsLocalRing

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- I.3.1(i)↔formally unramified, for a local essentially finite-type homomorphism:
the residue extension is separable and `m_A S = m_S`. -/
theorem formallyUnramified_iff_separable_residue [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [EssFiniteType R S] :
    FormallyUnramified R S ↔
      Algebra.IsSeparable (ResidueField R) (ResidueField S) ∧
        (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
  FormallyUnramified.iff_map_maximalIdeal_eq

/-- I.3.1(ii): unramified at a prime means that `Ω¹` vanishes after localizing. -/
theorem isUnramifiedAt_iff_subsingleton_differentials (q : Ideal S) [q.IsPrime] :
    IsUnramifiedAt R q ↔ Subsingleton Ω[Localization.AtPrime q⁄R] :=
  Algebra.formallyUnramified_iff _ _

/-- I.3.2: SGA's unramified algebras are mathlib's `Algebra.Unramified`
(formally unramified and of finite type). -/
theorem unramified_iff :
    Unramified R S ↔ FormallyUnramified R S ∧ FiniteType R S :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ⟨inferInstance, inferInstance⟩⟩

/-- I.3.3: the unramified locus of an essentially finite-type algebra is open. -/
theorem isOpen_unramifiedLocus [EssFiniteType R S] : IsOpen (unramifiedLocus R S) :=
  Algebra.isOpen_unramifiedLocus

/-- I.3.1, I.3.3: unramifiedness can be checked after localizing away from an element. -/
theorem exists_unramified_away [FiniteType R S] (q : Ideal S) [q.IsPrime]
    [IsUnramifiedAt R q] :
    ∃ f ∉ q, Unramified R (Localization.Away f) :=
  exists_unramified_of_isUnramifiedAt (R := R) q

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- I.3.1(iii): for a finite-type morphism, formally unramified means the diagonal
is an open immersion. -/
theorem formallyUnramified_of_isOpenImmersion_diagonal
    [IsOpenImmersion (pullback.diagonal f)] : FormallyUnramified f :=
  inferInstance

theorem isOpenImmersion_diagonal_of_formallyUnramified
    [FormallyUnramified f] [LocallyOfFiniteType f] :
    IsOpenImmersion (pullback.diagonal f) :=
  inferInstance

/-- I.3.5(i): an immersion is unramified. -/
instance (priority := 900) formallyUnramified_of_isImmersion [IsImmersion f] :
    FormallyUnramified f :=
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- I.3.5(ii): the composite of unramified morphisms is unramified. -/
instance formallyUnramified_comp {Z : Scheme.{u}} (g : Y ⟶ Z)
    [FormallyUnramified f] [FormallyUnramified g] : FormallyUnramified (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹_› ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/-- I.3.5(iii): unramified is stable under base change. -/
instance formallyUnramified_fst {X' : Scheme.{u}} (g : X' ⟶ Y) [FormallyUnramified g] :
    FormallyUnramified (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g ‹_›

/-- I.3.6(v): if `f ≫ g` is unramified then `f` is unramified. -/
theorem formallyUnramified_of_comp {Z : Scheme.{u}} (g : Y ⟶ Z)
    [FormallyUnramified (f ≫ g)] : FormallyUnramified f :=
  FormallyUnramified.of_comp f g

set_option backward.isDefEq.respectTransparency.types false in
/-- I.3.6(iv): a fibre product of unramified morphisms is unramified. -/
instance formallyUnramified_snd {X' : Scheme.{u}} (g : X' ⟶ Y) [FormallyUnramified f] :
    FormallyUnramified (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/-- I.3.4: if `X` is unramified over `Y`, the graph of a `Y`-morphism `X' ⟶ X`
is an open immersion. (The graph is `X' ⟶ X' ×_Y X`, as in the standard
formulation; the source's target `X ×_Y X` is recorded in the translation
README.) -/
instance isOpenImmersion_graph {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] :
    IsOpenImmersion (pullback.lift (𝟙 X') g (Category.id_comp (g ≫ f))) :=
  MorphismProperty.of_isPullback (pullback_lift_diagonal_isPullback g f) inferInstance

end SGA.SGA1.ExposeI
