/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.ConstantSupportSequence
import SGA.SGA2.ExposeI.OpenSupportCohomology
import SGA.SGA2.ExposeI.SupportedCohomologyComparison

/-!
# The relative cohomology sequence

The actual short exact sequence of open/closed constant support sheaves gives
the relative long exact sequence. The open terms are transported through the
proved Ext adjunction to ordinary cohomology of the restricted sheaf. Thus no
support sequence or comparison is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

set_option backward.isDefEq.respectTransparency false

private theorem addHom_comp_symm_equiv {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ C) (e : A ≃+ B) :
    (f.comp e.symm.toAddMonoidHom).comp e.toAddMonoidHom = f := by
  ext x
  exact congrArg f (e.symm_apply_apply x)

/-- The canonical map from supported to ordinary cohomology. -/
def relativeSupportMap (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H_Z Z F n →+ H F n :=
  (Ext.mk₀ (constantToClosedSupport Z)).precomp F (zero_add n)

/-- The map to cohomology on the open complement, induced by the genuine
open constant inclusion and the proved open-support Ext comparison. -/
def relativeRestriction (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H F n →+ H (restrictToOpen F Z.compl) n :=
  (openSupportExtEquiv Z.compl F n).toAddMonoidHom.comp
    ((Ext.mk₀ (zZX_openToConstant Z.compl)).precomp F (zero_add n))

/-- The actual relative connecting map, from the Ext class of the constant
support short exact sequence. -/
def relativeBoundary (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H (restrictToOpen F Z.compl) n →+ H_Z Z F (n + 1) :=
  ((constantSupportSequence_shortExact Z).extClass.precomp F (Nat.add_comm 1 n)).comp
    (openSupportExtEquiv Z.compl F n).symm.toAddMonoidHom

/-- **I.2.9:** exactness at ordinary cohomology in every degree. -/
theorem relative_exact_at_ordinary (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Function.Exact (relativeSupportMap Z F n) (relativeRestriction Z F n) := by
  apply Function.Exact.of_ladder_addEquiv_of_exact
    (e₁ := AddEquiv.refl _) (e₂ := AddEquiv.refl _)
    (e₃ := openSupportExtEquiv Z.compl F n)
    (H := (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.contravariant_sequence_exact₂' (constantSupportSequence_shortExact Z) F n))
  · rfl
  · rfl

/-- **I.2.9:** exactness at cohomology of the open complement in every degree. -/
theorem relative_exact_at_open (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Function.Exact (relativeRestriction Z F n) (relativeBoundary Z F n) := by
  apply Function.Exact.of_ladder_addEquiv_of_exact
    (e₁ := AddEquiv.refl _) (e₂ := openSupportExtEquiv Z.compl F n)
    (e₃ := AddEquiv.refl _)
    (H := (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.contravariant_sequence_exact₁' (constantSupportSequence_shortExact Z)
        F n (n + 1) (Nat.add_comm 1 n)))
  · rfl
  · exact addHom_comp_symm_equiv
      ((constantSupportSequence_shortExact Z).extClass.precomp F (Nat.add_comm 1 n))
      (openSupportExtEquiv Z.compl F n)

/-- **I.2.9:** exactness at positive supported cohomology in every degree. -/
theorem relative_exact_at_supported (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Function.Exact (relativeBoundary Z F n) (relativeSupportMap Z F (n + 1)) := by
  apply Function.Exact.of_ladder_addEquiv_of_exact
    (e₁ := openSupportExtEquiv Z.compl F n) (e₂ := AddEquiv.refl _)
    (e₃ := AddEquiv.refl _)
    (H := (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.contravariant_sequence_exact₃' (constantSupportSequence_shortExact Z)
        F n (n + 1) (Nat.add_comm 1 n)))
  · exact addHom_comp_symm_equiv
      ((constantSupportSequence_shortExact Z).extClass.precomp F (Nat.add_comm 1 n))
      (openSupportExtEquiv Z.compl F n)
  · rfl

/-- The relative sequence begins with an injection in degree zero. -/
theorem relativeSupportMap_zero_injective (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Function.Injective (relativeSupportMap Z F 0) :=
  Ext.precomp_mk₀_injective_of_epi F (constantToClosedSupport Z)

/-- **I.2.9:** six consecutive terms of the genuine relative sequence. -/
def relativeCohomologySequence (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) : ComposableArrows AddCommGrpCat.{u} 5 :=
  ComposableArrows.mk₅ (AddCommGrpCat.ofHom (relativeSupportMap Z F n))
    (AddCommGrpCat.ofHom (relativeRestriction Z F n))
    (AddCommGrpCat.ofHom (relativeBoundary Z F n))
    (AddCommGrpCat.ofHom (relativeSupportMap Z F (n + 1)))
    (AddCommGrpCat.ofHom (relativeRestriction Z F (n + 1)))

/-- The actual relative cohomology sequence is exact. -/
private theorem ab_exact_mk₂ {A B C : AddCommGrpCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (h : Function.Exact f g) :
    (ComposableArrows.mk₂ f g).Exact := by
  let S := ShortComplex.mk f g (by ext x; exact h.apply_apply_eq_zero x)
  exact ((ShortComplex.ab_exact_iff_function_exact S).mpr h).exact_toComposableArrows

/-- The actual relative cohomology sequence is exact. -/
theorem relativeCohomologySequence_exact (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (relativeCohomologySequence Z F n).Exact := by
  have h₁ := relative_exact_at_ordinary Z F n
  have h₂ := relative_exact_at_open Z F n
  have h₃ := relative_exact_at_supported Z F n
  have h₄ := relative_exact_at_ordinary Z F (n + 1)
  exact ComposableArrows.exact_of_δ₀
    (ab_exact_mk₂ _ _ h₁)
      (ComposableArrows.exact_of_δ₀
        (ab_exact_mk₂ _ _ h₂)
        (ComposableArrows.exact_of_δ₀
          (ab_exact_mk₂ _ _ h₃)
          (ab_exact_mk₂ _ _ h₄)))

/-- Vanishing of the next supported group makes the relative restriction
map surjective. -/
theorem relativeRestriction_surjective_of_supported_vanishing (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) [Subsingleton (H_Z Z F (n + 1))] :
    Function.Surjective (relativeRestriction Z F n) := by
  intro y
  exact (relative_exact_at_open Z F n y).mp (Subsingleton.elim _ _)

/-- Vanishing of the supported group makes relative restriction injective. -/
theorem relativeRestriction_injective_of_supported_vanishing (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) [Subsingleton (H_Z Z F n)] :
    Function.Injective (relativeRestriction Z F n) := by
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  rw [AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨y, rfl⟩ := (relative_exact_at_ordinary Z F n x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

/-- If two adjacent ordinary cohomology groups vanish, the relative
boundary is an isomorphism. -/
theorem relativeBoundary_bijective_of_ordinary_vanishing (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    [Subsingleton (H F n)] [Subsingleton (H F (n + 1))] :
    Function.Bijective (relativeBoundary Z F n) := by
  constructor
  · apply (AddMonoidHom.ker_eq_bot_iff _).mp
    rw [AddSubgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨y, rfl⟩ := (relative_exact_at_open Z F n x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  · intro y
    exact (relative_exact_at_supported Z F n y).mp (Subsingleton.elim _ _)

/-- The boundary isomorphism under adjacent ordinary vanishing. -/
def relativeBoundaryEquiv (Z : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    [Subsingleton (H F n)] [Subsingleton (H F (n + 1))] :
    H (restrictToOpen F Z.compl) n ≃+ H_Z Z F (n + 1) :=
  AddEquiv.ofBijective _ (relativeBoundary_bijective_of_ordinary_vanishing Z F n)

/-- Injectivity of degree-zero relative restriction forces the degree-zero
supported group to vanish. -/
theorem supported_zero_subsingleton_of_relativeRestriction_injective (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X)
    (h : Function.Injective (relativeRestriction Z F 0)) :
    Subsingleton (H_Z Z F 0) := by
  apply subsingleton_of_forall_eq 0
  intro x
  apply relativeSupportMap_zero_injective Z F
  apply h
  rw [map_zero, map_zero]
  exact (relative_exact_at_ordinary Z F 0).apply_apply_eq_zero x

/-- Surjectivity one degree below and injectivity in the given degree
force the supported group to vanish. -/
theorem supported_succ_subsingleton_of_relativeRestriction (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (hs : Function.Surjective (relativeRestriction Z F n))
    (hi : Function.Injective (relativeRestriction Z F (n + 1))) :
    Subsingleton (H_Z Z F (n + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  have hx : relativeSupportMap Z F (n + 1) x = 0 := by
    apply hi
    rw [map_zero]
    exact (relative_exact_at_ordinary Z F (n + 1)).apply_apply_eq_zero x
  obtain ⟨y, hy⟩ := (relative_exact_at_supported Z F n x).mp hx
  obtain ⟨z, rfl⟩ := hs y
  rw [← hy]
  exact (relative_exact_at_open Z F n).apply_apply_eq_zero z

/-- The group-valued vanishing/restriction criterion behind I.2.14 and
III.3.1(ii)–(iii), for one space and one closed support. -/
theorem supported_vanishing_iff_relativeRestriction (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (∀ i : ℕ, i ≤ n → Subsingleton (H_Z Z F i)) ↔
      ((∀ i : ℕ, i < n → Function.Bijective (relativeRestriction Z F i)) ∧
        Function.Injective (relativeRestriction Z F n)) := by
  constructor
  · intro h
    constructor
    · intro i hi
      have := h i (by omega)
      have := h (i + 1) (by omega)
      exact ⟨relativeRestriction_injective_of_supported_vanishing Z F i,
        relativeRestriction_surjective_of_supported_vanishing Z F i⟩
    · have := h n le_rfl
      exact relativeRestriction_injective_of_supported_vanishing Z F n
  · rintro ⟨hs, hi⟩ i hin
    have hinj (j : ℕ) (hj : j ≤ n) : Function.Injective (relativeRestriction Z F j) := by
      by_cases hlt : j < n
      · exact (hs j hlt).injective
      · have : j = n := by omega
        subst j
        exact hi
    cases i with
    | zero =>
      exact supported_zero_subsingleton_of_relativeRestriction_injective Z F (hinj 0 hin)
    | succ i =>
      exact supported_succ_subsingleton_of_relativeRestriction Z F i
        (hs i (by omega)).surjective (hinj (i + 1) hin)

end SGA.SGA2.ExposeI
