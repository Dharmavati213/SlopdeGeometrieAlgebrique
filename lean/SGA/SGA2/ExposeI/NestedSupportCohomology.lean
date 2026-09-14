/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.NestedSupportObjects

/-!
# The genuine nested-support long exact sequence

The proved short exact sequence of the original integer-support objects
gives I.2.8 in all degrees, naturally in coefficients. Its degree-zero maps
are the actual inclusion and restriction of supported sections.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} {A B : Closeds X}

/-- The support-increasing map on the original Ext-valued cohomology. -/
def nestedSupportCohomologyMap (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H_locallyClosed (LocallyClosedIn.ofOpenClosed V A) F n →+
      H_locallyClosed (LocallyClosedIn.ofOpenClosed V B) F n :=
  (Ext.mk₀ (nestedSupportObjectRestriction h V)).precomp F (zero_add n)

/-- Restriction to the actual locally closed difference on Ext. -/
def nestedSupportCohomologyRestriction (A B : Closeds X) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H_locallyClosed (LocallyClosedIn.ofOpenClosed V B) F n →+
      H_locallyClosed (LocallyClosedIn.ofOpenClosed (V ⊓ A.compl) B) F n :=
  (Ext.mk₀ (nestedSupportObjectInclusion A B V)).precomp F (zero_add n)

/-- The genuine connecting map, using the Ext class of the proved actual
support-object short exact sequence. -/
def nestedSupportCohomologyBoundary (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H_locallyClosed (LocallyClosedIn.ofOpenClosed (V ⊓ A.compl) B) F n →+
      H_locallyClosed (LocallyClosedIn.ofOpenClosed V A) F (n + 1) :=
  (nestedSupportObjectSequence_shortExact h V).extClass.precomp F (Nat.add_comm 1 n)

/-- **I.2.8:** exactness at the middle supported cohomology. -/
theorem nestedSupportCohomology_exact_middle (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Function.Exact (nestedSupportCohomologyMap h V F n)
      (nestedSupportCohomologyRestriction A B V F n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.contravariant_sequence_exact₂' (nestedSupportObjectSequence_shortExact h V) F n)

/-- **I.2.8:** exactness at cohomology of the difference. -/
theorem nestedSupportCohomology_exact_difference (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Function.Exact (nestedSupportCohomologyRestriction A B V F n)
      (nestedSupportCohomologyBoundary h V F n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.contravariant_sequence_exact₁' (nestedSupportObjectSequence_shortExact h V)
      F n (n + 1) (Nat.add_comm 1 n))

/-- **I.2.8:** exactness at the next closed-in-middle supported group. -/
theorem nestedSupportCohomology_exact_left (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Function.Exact (nestedSupportCohomologyBoundary h V F n)
      (nestedSupportCohomologyMap h V F (n + 1)) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.contravariant_sequence_exact₃' (nestedSupportObjectSequence_shortExact h V)
      F n (n + 1) (Nat.add_comm 1 n))

/-- The actual sequence starts injectively in degree zero. -/
theorem nestedSupportCohomologyMap_zero_injective (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Function.Injective (nestedSupportCohomologyMap h V F 0) :=
  Ext.precomp_mk₀_injective_of_epi F (nestedSupportObjectRestriction h V)

/-- Six consecutive terms of the actual nested-support sequence. -/
def nestedSupportCohomologySequence (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) : ComposableArrows AddCommGrpCat.{u} 5 :=
  Ext.contravariantSequence (nestedSupportObjectSequence_shortExact h V)
    F n (n + 1) (Nat.add_comm 1 n)

/-- **I.2.8:** the genuine six-term segments are exact in all degrees. -/
theorem nestedSupportCohomologySequence_exact (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (nestedSupportCohomologySequence h V F n).Exact :=
  Ext.contravariantSequence_exact (nestedSupportObjectSequence_shortExact h V)
    F n (n + 1) (Nat.add_comm 1 n)

/-- The support-increasing map is natural in the coefficient sheaf. -/
theorem nestedSupportCohomologyMap_naturality (h : A ≤ B) (V : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ)
    (x : H_locallyClosed (LocallyClosedIn.ofOpenClosed V A) F n) :
    nestedSupportCohomologyMap h V G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (nestedSupportCohomologyMap h V F n x).comp (Ext.mk₀ f) (add_zero n) := by
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)).symm

/-- Restriction to the difference is natural in the coefficient sheaf. -/
theorem nestedSupportCohomologyRestriction_naturality (A B : Closeds X) (V : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ)
    (x : H_locallyClosed (LocallyClosedIn.ofOpenClosed V B) F n) :
    nestedSupportCohomologyRestriction A B V G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (nestedSupportCohomologyRestriction A B V F n x).comp (Ext.mk₀ f) (add_zero n) := by
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)).symm

/-- The genuine connecting maps are natural in the coefficient sheaf. -/
theorem nestedSupportCohomologyBoundary_naturality (h : A ≤ B) (V : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ)
    (x : H_locallyClosed (LocallyClosedIn.ofOpenClosed (V ⊓ A.compl) B) F n) :
    nestedSupportCohomologyBoundary h V G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (nestedSupportCohomologyBoundary h V F n x).comp (Ext.mk₀ f) (add_zero (n + 1)) := by
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (Nat.add_comm 1 n)).symm

/-- Original degree-zero support Ext is the concrete supported-section group. -/
def openClosedSupportCohomologyZeroEquiv (Z : Closeds X) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    H_locallyClosed (LocallyClosedIn.ofOpenClosed V Z) F 0 ≃+ gammaZSections F Z V :=
  Ext.addEquiv₀.trans (openClosedSupportHomEquiv Z V F)

/-- The degree-zero support-increasing map is actual inclusion of sections. -/
theorem nestedSupportCohomologyMap_zero_sections (h : A ≤ B) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X)
    (x : H_locallyClosed (LocallyClosedIn.ofOpenClosed V A) F 0) :
    openClosedSupportCohomologyZeroEquiv B V F (nestedSupportCohomologyMap h V F 0 x) =
      nestedSupportSectionsInclusion h V F (openClosedSupportCohomologyZeroEquiv A V F x) := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ F).surjective x
  change openClosedSupportHomEquiv B V F
      (Ext.addEquiv₀ ((Ext.mk₀ (nestedSupportObjectRestriction h V)).comp
        (Ext.mk₀ f) (zero_add 0))) = _
  rw [Ext.mk₀_comp_mk₀]
  simp only [openClosedSupportCohomologyZeroEquiv, AddEquiv.trans_apply,
    ← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  exact nestedSupportObjectRestriction_sections h V f

/-- The degree-zero map to the difference is actual restriction of sections. -/
theorem nestedSupportCohomologyRestriction_zero_sections (A B : Closeds X) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X)
    (x : H_locallyClosed (LocallyClosedIn.ofOpenClosed V B) F 0) :
    openClosedSupportCohomologyZeroEquiv B (V ⊓ A.compl) F
        (nestedSupportCohomologyRestriction A B V F 0 x) =
      nestedSupportSectionsRestriction A B V F (openClosedSupportCohomologyZeroEquiv B V F x) := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ F).surjective x
  change openClosedSupportHomEquiv B (V ⊓ A.compl) F
      (Ext.addEquiv₀ ((Ext.mk₀ (nestedSupportObjectInclusion A B V)).comp
        (Ext.mk₀ f) (zero_add 0))) = _
  rw [Ext.mk₀_comp_mk₀]
  simp only [openClosedSupportCohomologyZeroEquiv, AddEquiv.trans_apply,
    ← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  exact nestedSupportObjectInclusion_sections A B V f

end SGA.SGA2.ExposeI
