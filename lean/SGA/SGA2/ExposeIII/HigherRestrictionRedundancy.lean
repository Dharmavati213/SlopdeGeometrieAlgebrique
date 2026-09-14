/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.ComplementInjectiveEffacement

/-!
# Higher redundancy in the original ordinary restriction criterion

I.2.13 for every `N > 0`, equivalently III.3.2 at every threshold at
least two. The highest injectivity hypothesis is omitted for the actual
ordinary restriction maps with literal ambient-intersection targets.

The proof uses genuine complement-adapted injective effacement and
coefficient dimension shifting. It does not assume local effacement,
sheafification of a replacement presheaf, or the desired vanishing.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian AlgebraicGeometry
open SGA.SGA2.ExposeI

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- Bijectivity below a positive cutoff already annihilates all supported
cohomology through that cutoff, on every open. The coefficient sequence
used in the induction is constructed from actual sheaves. -/
theorem local_H_Z_vanishes_of_intersectionRestriction_bijective
    (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (h : ∀ (V : Opens X) (i : ℕ), i < n + 1 → Function.Bijective
      (ordinaryCohomologyRestrictionToIntersection V Z.compl F i)) :
    ∀ (V : Opens X) (i : ℕ), i < n + 2 →
      Subsingleton (H_Z (closedSupportOnOpen Z V) (restrictToOpen F V) i) := by
  induction n generalizing F with
  | zero =>
    exact (derivedSupported_vanishes_iff_local_H_Z Z F 2).mp
      ((derivedSupported_vanishes_two_iff_intersectionRestriction_zero Z F).mpr
        (fun V => h V 0 (by omega)))
  | succ n ih =>
    have hunit : IsIso (toComplementPushforward F Z) :=
      toComplementPushforward_isIso_of_intersectionRestriction_zero Z F
        (fun V => h V 0 (by omega))
    let S := complementInjectiveSequence Z F
    have hS : S.ShortExact := complementInjectiveSequence_shortExact Z F
    have hQ : ∀ (V : Opens X) (i : ℕ), i < n + 1 → Function.Bijective
        (ordinaryCohomologyRestrictionToIntersection V Z.compl S.X₃ i) := by
      intro V i hi
      apply (intersectionRestriction_bijective_iff_relative Z S.X₃ V i).mpr
      apply relativeRestriction_bijective_cokernel (closedSupportOnOpen Z V)
        (restrictToOpen_shortExact V hS) i
      · exact (intersectionRestriction_bijective_iff_relative Z F V i).mp
          (h V i (by omega))
      · exact relativeRestriction_bijective_of_injective_of_unit_isIso Z
          (complementInjective Z F) V i
      · exact (intersectionRestriction_bijective_iff_relative Z F V (i + 1)).mp
          (h V (i + 1) (by omega))
      · exact relativeRestriction_bijective_of_injective_of_unit_isIso Z
          (complementInjective Z F) V (i + 1)
    have hQzero := ih S.X₃ hQ
    intro V i hi
    cases i with
    | zero =>
      exact supported_zero_subsingleton_of_relativeRestriction_injective
        (closedSupportOnOpen Z V) (restrictToOpen F V)
        ((intersectionRestriction_bijective_iff_relative Z F V 0).mp
          (h V 0 (by omega))).injective
    | succ i =>
      have : Injective (restrictToOpen S.X₂ V) :=
        (iShriek_open_preservesInjectiveObjects V).injective_obj
          (inferInstanceAs (Injective (complementInjective Z F)))
      have : Subsingleton (H_Z (closedSupportOnOpen Z V) (restrictToOpen S.X₃ V) i) :=
        hQzero V i (by omega)
      have : Injective (S.map (iShriek_open V)).X₂ :=
        inferInstanceAs (Injective (restrictToOpen S.X₂ V))
      have : Subsingleton (Ext (zZX_closed (closedSupportOnOpen Z V))
          (S.map (iShriek_open V)).X₃ i) :=
        inferInstanceAs
          (Subsingleton (H_Z (closedSupportOnOpen Z V) (restrictToOpen S.X₃ V) i))
      apply subsingleton_of_forall_eq 0
      intro x
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
        (zZX_closed (closedSupportOnOpen Z V)) (restrictToOpen_shortExact V hS) x
        (Ext.eq_zero_of_injective _) (n₀ := i) rfl
      rw [← hy, Subsingleton.elim y 0, Ext.zero_comp]

/-- **I.2.13 for all `N > 0`; III.3.2 for every threshold at least two:**
bijectivity in lower degrees on every open suffices; the highest-degree
injectivity is not a hypothesis. All functors and restriction maps are the
original actual ones. -/
theorem derivedSupported_vanishes_iff_intersectionRestriction_bijective
    (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (∀ i < n + 2, IsZero ((derivedUnderlineGammaZ Z i).obj F)) ↔
      ∀ (V : Opens X) (i : ℕ), i < n + 1 → Function.Bijective
        (ordinaryCohomologyRestrictionToIntersection V Z.compl F i) := by
  constructor
  · intro h V i hi
    exact ((derivedSupported_vanishes_iff_intersectionRestriction Z F (n + 1)).mp h V).1 i hi
  · intro h
    exact (derivedSupported_vanishes_iff_local_H_Z Z F (n + 2)).mpr
      (local_H_Z_vanishes_of_intersectionRestriction_bijective Z F n h)

/-- The discarded highest-degree injectivity follows for the actual
ordinary restriction map on every ambient open. -/
theorem intersectionRestriction_highest_injective_of_lower_bijective
    (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (h : ∀ (V : Opens X) (i : ℕ), i < n + 1 → Function.Bijective
      (ordinaryCohomologyRestrictionToIntersection V Z.compl F i)) (V : Opens X) :
    Function.Injective (ordinaryCohomologyRestrictionToIntersection V Z.compl F (n + 1)) :=
  ((derivedSupported_vanishes_iff_intersectionRestriction Z F (n + 1)).mp
    ((derivedSupported_vanishes_iff_intersectionRestriction_bijective Z F n).mpr h) V).2

/-- **III.3.2–3.3:** coherent stalk depth at every threshold at least two
is detected by lower ordinary restriction bijectivity alone. -/
theorem coherent_depth_iff_intersectionRestriction_bijective
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsFinitePresentation] (Z : Closeds X) (n : ℕ) :
    (∀ x : X, x ∈ Z → (n + 2 : ℕ∞) ≤ moduleStalkDepth M x) ↔
      ∀ (V : X.Opens) (i : ℕ), i < n + 1 → Function.Bijective
        (ordinaryCohomologyRestrictionToIntersection V Z.compl (schemeModuleAbSheaf M) i) :=
  (coherent_depth_iff_derivedSupported_vanishes M Z (n + 2)).trans
    (derivedSupported_vanishes_iff_intersectionRestriction_bijective Z (schemeModuleAbSheaf M) n)

end SGA.SGA2.ExposeIII
