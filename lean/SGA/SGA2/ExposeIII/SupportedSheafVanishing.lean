/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalConvergence
import SGA.SGA2.ExposeI.LocalToGlobalE2
import SGA.SGA2.ExposeI.SupportedSheafRestriction
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Lower vanishing for original supported sheaves and local cohomology

The local-to-global implication uses the actual supported spectral sequence
and its proved finite convergence filtration. The reverse implication uses
the actual sheafification comparison, not an assumed local-global criterion.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian
open SGA.SGA2.ExposeI
open SGA.SGA2.ExposeI.SpectralObjectConvergence

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

/-- A zero term of an actual spectral sequence remains zero on later pages. -/
theorem spectralSequence_isZero_page_of_isZero
    {C : Type*} [Category C] [Abelian C] {κ : Type*}
    {c : ℤ → ComplexShape κ} {r₀ : ℤ} (E : SpectralSequence C c r₀)
    {s : ℤ} (hs : r₀ ≤ s) (pq : κ) (h : IsZero ((E.page s hs).X pq))
    (r : ℤ) (hsr : s ≤ r) : IsZero ((E.page r (hs.trans hsr)).X pq) := by
  induction r, hsr using Int.leInduction with
  | base => exact h
  | succ r hsr ih =>
    exact (ShortComplex.isZero_homology_of_isZero_X₂ _ ih).of_iso
      (E.iso r (r + 1) pq rfl (hs.trans hsr)).symm

/-- Vanishing of a diagonal of the actual first page forces vanishing of
the actual total object, by the canonical finite convergence filtration. -/
theorem spectralObject_total_isZero_of_firstPage
    {C : Type*} [Category C] [Abelian C]
    (S : SpectralObject C EInt) [S.IsFirstQuadrant] (n : ℕ)
    (h : ∀ q : ℕ, q ≤ n →
      IsZero ((S.E₂SpectralSequence.page 2).X ((n : ℤ) - q, q))) :
    IsZero (SpectralObjectConvergence.total S n) := by
  have hinfty (q : ℕ) (hq : q ≤ n) : IsZero (inftyTerm S n q) := by
    have hz := spectralSequence_isZero_page_of_isZero S.E₂SpectralSequence
      (le_refl 2) ((n : ℤ) - q, q) (h q hq) ((n : ℤ) + 2) (by omega)
    have e := stablePageIsoInfty S ((n : ℤ) - q) q ((n : ℤ) + 2)
      (by omega) (by exact_mod_cast Nat.add_le_add_right hq 2) (by omega)
    simpa only [sub_add_cancel] using hz.of_iso e.symm
  have hf : ∀ q : ℕ, q ≤ n + 1 → IsZero (filtrationObj S n (q : ℤ)) := by
    intro q
    induction q with
    | zero =>
      intro _
      exact S.isZero_opcycles _ _ _ (S.isZero₁_of_isFirstQuadrant ⊥ (0 : ℤ)
        bot_le le_rfl n)
    | succ q ih =>
      intro hq
      have hz := (filtrationSequence_exact S n q).isZero_of_both_isZero
        (ih (by omega)) (hinfty q (by omega))
      simpa only [filtrationSequence, Nat.cast_add, Nat.cast_one] using hz
  have hi : IsIso (filtrationι S n ((n : ℤ) + 1 : ℤ)) :=
    S.isIso_fromOpcycles _ _ _ _ n
      (S.isZero₂_of_isFirstQuadrant ((n : ℤ) + 1 : ℤ) ⊤ le_top n (by simp))
  have hz := hf (n + 1) le_rfl
  simp only [Nat.cast_add, Nat.cast_one] at hz
  exact hz.of_iso (asIso (SpectralObjectConvergence.filtrationι S n ((n : ℤ) + 1 : ℤ))).symm

variable {X : TopCat.{u}}

/-- Original supported-sheaf vanishing below a bound implies vanishing of
the original supported cohomology below the same bound. -/
theorem H_Z_subsingleton_of_derivedSupported_vanishing
    (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (h : ∀ q < n, IsZero ((derivedUnderlineGammaZ Z q).obj F))
    (i : ℕ) (hi : i < n) : Subsingleton (H_Z Z F i) := by
  let I := injectiveResolution F
  have hz : IsZero (SpectralObjectConvergence.total
      (supportedLocalToGlobalAbelianSpectralObject Z I) i) := by
    apply spectralObject_total_isZero_of_firstPage
    intro q hq
    have hH : IsZero ((extFunctorObj (constantZ X) (i - q)).obj
        ((derivedUnderlineGammaZ Z q).obj F)) :=
      (extFunctorObj (constantZ X) (i - q)).map_isZero (h q (by omega))
    have hs : Subsingleton (H ((derivedUnderlineGammaZ Z q).obj F) (i - q)) :=
      AddCommGrpCat.isZero_iff_subsingleton.mp hH
    have hz :=
      (supportedTruncationSpectralSequenceE2Equiv Z I (i - q) q).symm.subsingleton_congr.mp hs
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    simpa only [supportedTruncationSpectralSequence, Nat.cast_sub hq] using hz
  exact (supportedCohomologyAbutmentEquiv Z I i).subsingleton_congr.mp
    (AddCommGrpCat.isZero_iff_subsingleton.mp hz)

/-- Vanishing on a genuine open basis kills every actual presheaf stalk. -/
theorem presheafStalk_isZero_of_basis (P : X.Presheaf AddCommGrpCat.{u})
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hP : ∀ U ∈ B, IsZero (P.obj (op U))) (x : X) : IsZero (P.stalk x) := by
  have hz (t : P.stalk x) : t = 0 := by
    obtain ⟨V, hxV, s, rfl⟩ := P.exists_germ_eq t
    obtain ⟨U, hUB, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp hB hxV
    have := AddCommGrpCat.isZero_iff_subsingleton.mp (hP U hUB)
    rw [← P.germ_res_apply (homOfLE hUV) x hxU s]
    rw [show P.map (homOfLE hUV).op s = 0 from Subsingleton.elim _ _, map_zero]
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- Vanishing of a presheaf on a basis implies vanishing of its actual
sheafification, through the genuine sheafification unit on stalks. -/
theorem sheafification_isZero_of_basis (P : X.Presheaf AddCommGrpCat.{u})
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hP : ∀ U ∈ B, IsZero (P.obj (op U))) :
    IsZero ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj P) := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  have : IsIso ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) P)) :=
    Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  exact (presheafStalk_isZero_of_basis P B hB hP x).of_iso
    (asIso ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X) P))).symm

/-- Local supported cohomology need only vanish on an actual basis to
annihilate the original derived supported sheaf in a fixed degree. -/
theorem derivedSupported_isZero_of_local_H_Z_basis (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (i : ℕ) (h : ∀ U ∈ B,
      Subsingleton (H_Z (closedSupportOnOpen Z U) (restrictToOpen F U) i)) :
    IsZero ((derivedUnderlineGammaZ Z i).obj F) := by
  have hz := sheafification_isZero_of_basis
    ((supportedCohomologyPresheafFunctor Z i).obj F) B hB (fun U hU =>
      AddCommGrpCat.isZero_iff_subsingleton.mpr
        ((supportedCohomologyPresheafSectionsEquiv Z U F i).subsingleton_congr.mpr (h U hU)))
  exact hz.of_iso ((supportedCohomologySheafificationIso Z i).app F).symm

/-- **III.3.1, (i) iff (iii):** lower vanishing of the original derived
supported sheaves is exactly lower vanishing of actual supported cohomology
on every open subspace. -/
theorem derivedSupported_vanishes_iff_local_H_Z (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (∀ i < n, IsZero ((derivedUnderlineGammaZ Z i).obj F)) ↔
      ∀ (U : Opens X) (i : ℕ), i < n →
        Subsingleton (H_Z (closedSupportOnOpen Z U) (restrictToOpen F U) i) := by
  constructor
  · intro h U i hi
    apply H_Z_subsingleton_of_derivedSupported_vanishing (closedSupportOnOpen Z U)
      (restrictToOpen F U) n _ i hi
    intro q hq
    exact ((iShriek_open U).map_isZero (h q hq)).of_iso
      ((derivedSupportedSheafRestrictionIso Z U q).app F).symm
  · intro h i hi
    have hz : IsZero ((supportedCohomologyPresheafFunctor Z i).obj F) := by
      apply Functor.isZero
      intro U
      exact AddCommGrpCat.isZero_iff_subsingleton.mpr
        ((supportedCohomologyPresheafSectionsEquiv Z U.unop F i).subsingleton_congr.mpr
          (h U.unop i hi))
    exact ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map_isZero hz).of_iso
      ((supportedCohomologySheafificationIso Z i).app F).symm

end SGA.SGA2.ExposeIII
