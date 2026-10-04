/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.Purity
import SGA.SGA1.ExposeXIII.NormalCrossings

/-!
# SGA 1, Exposé XIII, §3: the desingularization hypotheses

Several results of Exposé XIII §3 and §4 (3.1 2), 3.2 2), 3.3, 3.4, 3.5, 4.6) assume that the
schemes of finite type of dimension `≤ d` over an algebraically closed field `k` are
*desingularizable* (EGA IV 7.9.1) or *strongly desingularizable* (SGA 5 I 3.1.5). These are
hypotheses of SGA's own statements, which hold in characteristic `0` (Hironaka) and are open in
characteristic `p > 0` beyond small dimension. This file defines them:

* `IsDesingularizable Z`: the integral scheme `Z` admits a proper birational morphism from a
  regular scheme (a proper morphism `q : Z' ⟶ Z` with `Z'` regular and integral which is an
  isomorphism over a nonempty open subset of `Z`);
* `DesingularizableUpTo k d`: the integral schemes of finite type over `k` of dimension `≤ d` are
  desingularizable;
* `IsStronglyDesingularizable p`, `StronglyDesingularizableUpTo k d`: for every nonempty regular
  open `U` of `Z`, there is a proper `q : Z' ⟶ Z` with `Z'` regular, which is an isomorphism over
  `U`, such that `Z' - q⁻¹(U)` is the support of a divisor with normal crossings relative to `k`
  (`SGA.SGA1.ExposeXIII.IsNormalCrossingsSupport`).

In dimension `0` both hypotheses hold over every field (`desingularizableUpTo_zero`,
`stronglyDesingularizableUpTo_zero`): an integral scheme of dimension `≤ 0` is the spectrum of a
field. In dimension `≤ 1` both hold over every perfect field, by normalization
(`SGA.SGA1.ExposeXIII.desingularizableUpTo_one` in `SGA.SGA1.ExposeXIII.DesingularizationCurves`,
`SGA.SGA1.ExposeXIII.stronglyDesingularizableUpTo_one` in
`SGA.SGA1.ExposeXIII.DesingularizationCurvesStrong`).

The text of SGA 5 I 3.1.5 is not in this repository. The strong form above is the property used
in the proof of XIII.3.1 2) (step 3) 1: a smooth `X` is the complement of a divisor with normal
crossings in a smooth proper `Z` over a compactification of `X`) and in XIII.4.6. Its comparison
with the text of SGA 5 is not checked.

For every `d`, both hypotheses as defined here quantify only over *integral* schemes of finite
type of dimension `≤ d`. SGA states them for all "schemes of finite type of dimension `≤ d`"; its
proofs only apply them to integral schemes (the irreducible components with their reduced
structure), so nothing is lost for the uses in Exposé XIII.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace SGA.SGA1.ExposeXIII

open ExposeX (IsRegularScheme)

/-- EGA IV 7.9.1: an integral scheme `Z` is *desingularizable* if there is a proper birational
morphism `q : Z' ⟶ Z` from a regular integral scheme `Z'`; birationality is expressed by `q` being
an isomorphism over a nonempty open subset of `Z`. -/
def IsDesingularizable (Z : Scheme.{u}) : Prop :=
  ∃ (Z' : Scheme.{u}) (q : Z' ⟶ Z), IsProper q ∧ IsIntegral Z' ∧ IsRegularScheme Z' ∧
    ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ IsIso (q ∣_ U)

/-- EGA IV 7.9.1, the hypothesis of XIII.3.3 and 3.4: the integral schemes of finite type over the
field `k` of dimension `≤ d` are desingularizable. -/
def DesingularizableUpTo (k : Type u) [Field k] (d : WithBot ℕ∞) : Prop :=
  ∀ ⦃Z : Scheme.{u}⦄ (p : Z ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    [IsIntegral Z], topologicalKrullDim Z ≤ d → IsDesingularizable Z

/-- SGA 5 I 3.1.5 (reconstructed, see the module docstring): a scheme `Z` over the field `k`
(`p : Z ⟶ Spec k`) is *strongly desingularizable* if for every nonempty regular open subset `U`
of `Z` there is a proper morphism `q : Z' ⟶ Z` from a regular scheme which is an isomorphism over
`U` and such that `Z' - q⁻¹(U)` is the support of a divisor with normal crossings relative to
`k`. -/
def IsStronglyDesingularizable {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) : Prop :=
  ∀ U : Z.Opens, (U : Set Z).Nonempty → IsRegularScheme U →
    ∃ (Z' : Scheme.{u}) (q : Z' ⟶ Z), IsProper q ∧ IsRegularScheme Z' ∧ IsIso (q ∣_ U) ∧
      IsNormalCrossingsSupport (q ≫ p) (q ⁻¹ᵁ U : Set Z')ᶜ

/-- SGA 5 I 3.1.5, the hypothesis of XIII.3.1 2), 3.2 2), 3.5 and 4.6: the integral schemes of
finite type over the field `k` of dimension `≤ d` are strongly desingularizable. -/
def StronglyDesingularizableUpTo (k : Type u) [Field k] (d : WithBot ℕ∞) : Prop :=
  ∀ ⦃Z : Scheme.{u}⦄ (p : Z ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    [IsIntegral Z], topologicalKrullDim Z ≤ d → IsStronglyDesingularizable p

variable {k : Type u} [Field k] {d e : WithBot ℕ∞}

lemma DesingularizableUpTo.mono (h : DesingularizableUpTo k d) (hed : e ≤ d) :
    DesingularizableUpTo k e :=
  fun _ p _ _ _ hZ ↦ h p (hZ.trans hed)

lemma StronglyDesingularizableUpTo.mono (h : StronglyDesingularizableUpTo k d) (hed : e ≤ d) :
    StronglyDesingularizableUpTo k e :=
  fun _ p _ _ _ hZ ↦ h p (hZ.trans hed)

/-- A regular integral scheme is desingularizable (by the identity). -/
lemma IsDesingularizable.of_isRegularScheme {Z : Scheme.{u}} [IsIntegral Z]
    (h : IsRegularScheme Z) : IsDesingularizable Z :=
  ⟨Z, 𝟙 Z, inferInstance, inferInstance, h, ⊤, ⟨genericPoint Z, trivial⟩, inferInstance⟩

/-- The empty set is the support of a divisor with normal crossings. -/
lemma isNormalCrossingsSupport_empty {X S : Scheme.{u}} (p : X ⟶ S) :
    IsNormalCrossingsSupport p (∅ : Set X) :=
  ⟨PUnit, fun _ ↦ X, fun _ ↦ 𝟙 X, fun _ ↦ inferInstance,
    Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨⟨⟩, x, rfl⟩,
    fun _ ↦ ⟨Empty, inferInstance, Empty.elim, fun x hx ↦ by simp at hx, by simp⟩⟩

section DimensionZero

variable {Z : Scheme.{u}} [IsIntegral Z]

omit [IsIntegral Z] in
/-- In a scheme of dimension `≤ 0`, every point is maximal for generization. -/
lemma coheight_eq_zero_of_topologicalKrullDim_le_zero (h : topologicalKrullDim Z ≤ 0) (z : Z) :
    Order.coheight z = 0 := by
  have hle : Order.coheight z ≤ 0 := by
    let _ : PartialOrder Z := specializationOrder Z
    have h₁ := Order.coheight_le_krullDim ((irreducibleSetEquivPoints (α := Z)).symm z)
    rw [Order.coheight_orderIso] at h₁
    have h₂ : ((Order.coheight z : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := h₁.trans h
    exact_mod_cast h₂
  exact nonpos_iff_eq_zero.mp hle

/-- An integral scheme of dimension `≤ 0` is regular: its local rings are fields. -/
lemma isRegularScheme_of_topologicalKrullDim_le_zero (h : topologicalKrullDim Z ≤ 0) :
    IsRegularScheme Z := by
  intro z
  have : Ring.KrullDimLE 0 (Z.presheaf.stalk z) := krullDimLE_of_coheight_le
    (by rw [coheight_eq_zero_of_topologicalKrullDim_le_zero h z]; rfl)
  have hF := Ring.KrullDimLE.isField_of_isDomain (R := Z.presheaf.stalk z)
  let _ := hF.toField
  infer_instance

/-- An integral scheme of dimension `≤ 0` is a point: every point is the generic point. -/
lemma eq_genericPoint_of_topologicalKrullDim_le_zero (h : topologicalKrullDim Z ≤ 0) (z : Z) :
    z = genericPoint Z := by
  have hmax : IsMax z := Order.coheight_eq_zero.mp
    (coheight_eq_zero_of_topologicalKrullDim_le_zero h z)
  have h₁ : genericPoint Z ⤳ z := (genericPoint_spec Z).specializes trivial
  have h₂ : z ⤳ genericPoint Z := hmax (show z ≤ genericPoint Z from h₁)
  exact (h₂.antisymm h₁).eq

/-- EGA IV 7.9.1 in dimension `0`: the integral schemes of dimension `≤ 0` are desingularizable,
over any field. -/
theorem desingularizableUpTo_zero : DesingularizableUpTo k 0 :=
  fun _ _ _ _ _ hZ ↦ .of_isRegularScheme (isRegularScheme_of_topologicalKrullDim_le_zero hZ)

/-- SGA 5 I 3.1.5 in dimension `0` (in the form of `IsStronglyDesingularizable`): the integral
schemes of dimension `≤ 0` are strongly desingularizable, over any field. -/
theorem stronglyDesingularizableUpTo_zero : StronglyDesingularizableUpTo k 0 := by
  intro Z p _ _ _ hZ U hU _
  have hUZ : (U : Set Z) = Set.univ := by
    obtain ⟨u, hu⟩ := hU
    refine Set.eq_univ_of_forall fun z ↦ ?_
    rwa [eq_genericPoint_of_topologicalKrullDim_le_zero hZ z,
      ← eq_genericPoint_of_topologicalKrullDim_le_zero hZ u]
  refine ⟨Z, 𝟙 Z, inferInstance, isRegularScheme_of_topologicalKrullDim_le_zero hZ,
    inferInstance, ?_⟩
  have : ((𝟙 Z) ⁻¹ᵁ U : Set Z)ᶜ = ∅ := by
    simp only [Scheme.Hom.id_preimage, hUZ, Set.compl_univ]
  rw [this]
  exact isNormalCrossingsSupport_empty _

end DimensionZero

end SGA.SGA1.ExposeXIII
