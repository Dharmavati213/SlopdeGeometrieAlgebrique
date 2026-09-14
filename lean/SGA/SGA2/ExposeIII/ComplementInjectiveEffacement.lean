/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.RestrictionCoefficientShift

/-!
# Genuine injective effacement adapted to an open complement

If the original complement unit of `F` is invertible, embed its actual
restriction into an injective sheaf on the complement and push forward.
The resulting ambient sheaf is injective, its original complement unit
is invertible, and the original map from `F` into it is a monomorphism.
This supplies coefficient dimension shifting without assuming local
effacement or a replacement cohomology presheaf.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian
open SGA.SGA2.ExposeI

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- The actual ambient-intersection restriction is bijective exactly when
the proved relative-sequence restriction on the open subspace is. -/
theorem intersectionRestriction_bijective_iff_relative (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (V : Opens X) (n : ℕ) :
    Function.Bijective (ordinaryCohomologyRestrictionToIntersection V Z.compl F n) ↔
      Function.Bijective
        (relativeRestriction (closedSupportOnOpen Z V) (restrictToOpen F V) n) := by
  have h := congrArg (fun W : Opens ((Opens.toTopCat X).obj V) =>
    Function.Bijective (ordinaryCohomologyRestriction W (restrictToOpen F V) n))
    (closedSupportOnOpen_compl_eq Z V)
  refine (ordinaryCohomologyRestrictionToIntersection_bijective_iff V Z.compl F n).trans
    (h.to_iff.symm.trans ?_)
  rw [relativeRestriction_eq_ordinary]

/-- An invertible original complement unit gives actual degree-zero
restriction isomorphisms on every ambient open. -/
theorem relativeRestriction_zero_bijective_of_unit_isIso (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsIso (toComplementPushforward F Z)]
    (V : Opens X) :
    Function.Bijective
      (relativeRestriction (closedSupportOnOpen Z V) (restrictToOpen F V) 0) := by
  rw [relativeRestriction_eq_ordinary]
  apply (restrictToComplement_bijective_iff_ordinary_zero Z F V).mp
  have : IsIso (restrictToComplement F Z V) := by
    rw [← toComplementPushforward_comp_sectionsIso]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- Ordinary restriction is an isomorphism in all degrees for an injective
ambient sheaf whose actual complement unit is invertible. -/
theorem relativeRestriction_bijective_of_injective_of_unit_isIso (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] [IsIso (toComplementPushforward F Z)]
    (V : Opens X) (n : ℕ) :
    Function.Bijective
      (relativeRestriction (closedSupportOnOpen Z V) (restrictToOpen F V) n) := by
  cases n with
  | zero => exact relativeRestriction_zero_bijective_of_unit_isIso Z F V
  | succ n =>
    have : Injective (restrictToOpen F V) :=
      (iShriek_open_preservesInjectiveObjects V).injective_obj inferInstance
    have : Injective (restrictToOpen (restrictToOpen F V) (closedSupportOnOpen Z V).compl) :=
      (iShriek_open_preservesInjectiveObjects (closedSupportOnOpen Z V).compl).injective_obj
        inferInstance
    exact Function.bijective_of_subsingleton' _

/-- The direct image of an actual injective over the complement. -/
def complementInjective (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    Sheaf AddCommGrpCat.{u} X :=
  (Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)).obj
    (Injective.under (restrictToOpen F Z.compl))

instance complementInjective_injective (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    Injective (complementInjective Z F) := by
  unfold complementInjective
  infer_instance

/-- The original unit is invertible on this direct image, by the proved
full faithfulness of actual open direct image. -/
instance complementInjective_unit_isIso (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    IsIso (toComplementPushforward (complementInjective Z F) Z) := by
  let P := Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)
  have : P.Full := (fullyFaithfulOpenPushforward Z.compl).full
  have : P.Faithful := (fullyFaithfulOpenPushforward Z.compl).faithful
  change IsIso ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (complementInclusion Z)).unit.app (P.obj (Injective.under (restrictToOpen F Z.compl))))
  infer_instance

/-- The actual unit followed by the direct image of the injective embedding. -/
def toComplementInjective (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    F ⟶ complementInjective Z F :=
  toComplementPushforward F Z ≫
    (Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)).map
      (Injective.ι (restrictToOpen F Z.compl))

instance toComplementInjective_mono (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X)
    [IsIso (toComplementPushforward F Z)] : Mono (toComplementInjective Z F) := by
  have : Mono (toComplementPushforward F Z) := inferInstance
  have : Mono ((Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)).map
      (Injective.ι (restrictToOpen F Z.compl))) := inferInstance
  unfold toComplementInjective
  infer_instance

/-- The actual short exact sequence used in higher redundancy. -/
def complementInjectiveSequence (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.cokernelSequence (toComplementInjective Z F)

theorem complementInjectiveSequence_shortExact (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsIso (toComplementPushforward F Z)] :
    (complementInjectiveSequence Z F).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := inferInstanceAs (Mono (toComplementInjective Z F))
  epi_g := inferInstanceAs (Epi (cokernel.π (toComplementInjective Z F)))

end SGA.SGA2.ExposeIII
