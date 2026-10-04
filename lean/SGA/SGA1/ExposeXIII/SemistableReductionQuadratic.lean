/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Blowup.Quadratic
import SGA.Foundations.Blowup.Proj
import SGA.SGA1.ExposeII.RegularSequence
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeX.Purity

/-!
# Quadratic transformations of regular local rings of dimension two

An input of the semistable reduction theorem for curves (`SemistableReductionStatement`, used in
Raynaud's case B of XIII.2.13), through resolution of surfaces and minimal models (Stacks,
chapters 54 and 55): blowing up the closed point of a regular local ring `A` of dimension `2`
gives a regular scheme whose exceptional fibre is the projective line over the residue field
(Stacks, Tags 0AGQ, 0AGR). Proved here: the regularity half of 0AGR (irreducibility is not
proved) and the chart part of 0AGQ (1) (the exceptional fibre meets each chart in `𝔸¹_κ`;
`E ≅ ℙ¹_κ` and 0AGQ (2), (3) are not proved). On the chart `A[𝔪/x]`, for a regular system of
parameters `(x, y)`:

* `SGA.SGA1.ExposeXIII.quasiRegular_of_isRegularLocalRing`: `(x, y)` is a quasi-regular sequence,
  from II.4.14 (`ExposeII.isRegularSystemOfGenerators_of_isWeaklyRegular`) and the fact that a
  regular system of parameters is a regular sequence;
* `SGA.SGA1.ExposeXIII.isRegularRing_affineBlowup`: `A[𝔪/x]` is a regular ring;
* `SGA.SGA1.ExposeXIII.affineBlowupQuotientEquiv`: `A[𝔪/x] / 𝔪 A[𝔪/x] ≅ κ[T]`, `T ↦ y/x`;
* `SGA.SGA1.ExposeXIII.isRegularScheme_blowup_maximalIdeal`: the blow-up
  `Bl_𝔪 (Spec A) = Proj (⊕ 𝔪ⁿ)` is a regular scheme (the regularity half of Stacks, Tag 0AGR).

The algebra is in `SGA.Foundations.Blowup.Quadratic`, where quasi-regularity is a hypothesis
(Foundations cannot import Exposé II).
-/

universe u

open IsLocalRing AlgebraicGeometry

namespace SGA.SGA1.ExposeXIII

variable {A : Type u} [CommRing A] [IsRegularLocalRing A] {x y : A}

private lemma ne_of_dim_two (hdim : ringKrullDim A = 2)
    (hxy : maximalIdeal A = Ideal.span {x, y}) : x ≠ y := by
  rintro rfl
  have h1 : (maximalIdeal A).spanFinrank ≤ 1 := by
    rw [hxy, Set.pair_eq_singleton]
    simpa using Submodule.spanFinrank_span_le_ncard_of_finite (R := A) (Set.finite_singleton x)
  have h2 : ((maximalIdeal A).spanFinrank : WithBot ℕ∞) = 2 := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal, hdim]
  have : (maximalIdeal A).spanFinrank = 2 := by exact_mod_cast h2
  omega

/-- A regular system of parameters `(x, y)` of a regular local ring of dimension `2` is a
quasi-regular sequence: a homogeneous polynomial `F` of degree `d` with `F(x, y) ∈ 𝔪^{d+1}` has all
its coefficients in `𝔪` (II.4.14 for the regular sequence `x, y`). -/
theorem quasiRegular_of_isRegularLocalRing (hdim : ringKrullDim A = 2)
    (hxy : maximalIdeal A = Ideal.span {x, y}) :
    ∀ (d : ℕ) (F : MvPolynomial (Fin 2) A), F.IsHomogeneous d →
      MvPolynomial.eval ![x, y] F ∈ maximalIdeal A ^ (d + 1) →
        ∀ m, F.coeff m ∈ maximalIdeal A := by
  have hne := ne_of_dim_two hdim hxy
  have hofList : Ideal.ofList [x, y] = maximalIdeal A := by
    rw [hxy]
    change Ideal.span {r | r ∈ [x, y]} = _
    congr 1
    ext r
    simp
  have hreg : RingTheory.Sequence.IsRegular A [x, y] :=
    IsRegularLocalRing.isRegular_of_span_eq_maximalIdeal (by simpa using hne) hofList
      (by rw [hdim]; rfl)
  have hgen := ExposeII.isRegularSystemOfGenerators_of_isWeaklyRegular [x, y]
    hreg.toIsWeaklyRegular
  have hfun : (fun i : Fin [x, y].length ↦ [x, y][i]) = ![x, y] := by
    funext i
    fin_cases i <;> rfl
  rw [hfun] at hgen
  have hspan : Ideal.span (Set.range ![x, y]) = maximalIdeal A := by
    rw [hxy, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  intro d F hF hmem m
  rw [← hspan] at hmem ⊢
  exact hgen d F hF hmem m

private lemma ne_zero_of_dim_two (hdim : ringKrullDim A = 2)
    (hxy : maximalIdeal A = Ideal.span {x, y}) : x ≠ 0 := by
  rintro rfl
  have h1 : (maximalIdeal A).spanFinrank ≤ 1 := by
    rw [hxy, Ideal.span_insert_zero]
    simpa using Submodule.spanFinrank_span_le_ncard_of_finite (R := A) (Set.finite_singleton y)
  have h2 : ((maximalIdeal A).spanFinrank : WithBot ℕ∞) = 2 := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal, hdim]
  have : (maximalIdeal A).spanFinrank = 2 := by exact_mod_cast h2
  omega

/-- The regularity half of Stacks, Tag 0AGR, on the chart `A[𝔪/x]`: for a regular local ring `A`
of dimension `2` and a regular system of parameters `(x, y)`, the affine blowup algebra `A[𝔪/x]`
is a regular ring. -/
theorem isRegularRing_affineBlowup (hdim : ringKrullDim A = 2)
    (hxy : maximalIdeal A = Ideal.span {x, y}) :
    IsRegularRing ((maximalIdeal A).affineBlowup x) :=
  Ideal.QuadraticTransform.isRegularRing hxy inferInstance (ne_zero_of_dim_two hdim hxy)
    (quasiRegular_of_isRegularLocalRing hdim hxy)

/-- The chart part of Stacks, Tag 0AGQ (1), on `A[𝔪/x]`: for a regular local ring `A` of
dimension `2` with residue field `κ` and a regular system of parameters `(x, y)`, the fibre of the
chart over the closed point is the affine line, `A[𝔪/x] / 𝔪 A[𝔪/x] ≅ κ[T]` with `T ↦ y/x`. -/
noncomputable def affineBlowupQuotientEquiv (hdim : ringKrullDim A = 2)
    (hxy : maximalIdeal A = Ideal.span {x, y}) :
    Polynomial (A ⧸ maximalIdeal A) ≃+*
      (maximalIdeal A).affineBlowup x ⧸ Ideal.QuadraticTransform.extendedIdeal A x :=
  Ideal.QuadraticTransform.quotientEquiv hxy (ne_zero_of_dim_two hdim hxy)
    (quasiRegular_of_isRegularLocalRing hdim hxy)

omit [IsRegularLocalRing A] in
/-- A point of the blow-up lying on the chart `D₊(a t)` has a regular local ring when the chart
ring `A[I/a]` is regular. -/
lemma isRegularLocalRing_stalk_blowup_of_mem {I : Ideal A} {a : A} (ha : a ∈ I)
    (hreg : IsRegularRing (I.affineBlowup a)) (z : I.blowup)
    (hz : z ∈ Proj.basicOpen I.reesGrading (Ideal.reesT ha)) :
    IsRegularLocalRing (I.blowup.presheaf.stalk z) := by
  have hU := Proj.isAffineOpen_basicOpen I.reesGrading (Ideal.reesT ha) (Ideal.reesT_mem ha)
    one_pos
  have : IsRegularRing Γ(I.blowup, Proj.basicOpen I.reesGrading (Ideal.reesT ha)) :=
    IsRegularRing.of_ringEquiv ((Ideal.reesAwayEquiv ha).symm.trans
      (Proj.basicOpenIsoAway I.reesGrading (Ideal.reesT ha) (Ideal.reesT_mem ha)
        one_pos).commRingCatIsoToRingEquiv)
  exact IsRegularLocalRing.of_ringEquiv (ExposeI.stalkEquivLocalization hU z hz).symm

/-- The regularity half of Stacks, Tag 0AGR: the blow-up of a regular local ring of dimension `2`
at its closed point is a regular scheme. Irreducibility of the blow-up (the other half of 0AGR) is
not proved here. -/
theorem isRegularScheme_blowup_maximalIdeal (hdim : ringKrullDim A = 2) :
    ExposeX.IsRegularScheme (maximalIdeal A).blowup := by
  -- a regular system of parameters `(x, y)`
  obtain ⟨s, hs_card, hs_span⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal A))
  have h2 : (maximalIdeal A).spanFinrank = 2 := by
    have h : ((maximalIdeal A).spanFinrank : WithBot ℕ∞) = 2 := by
      rw [IsRegularLocalRing.spanFinrank_maximalIdeal, hdim]
    exact_mod_cast h
  rw [h2] at hs_card
  obtain ⟨x, y, -, rfl⟩ := Set.encard_eq_two.mp hs_card
  have hxy : maximalIdeal A = Ideal.span {x, y} := hs_span.symm
  have hyx : maximalIdeal A = Ideal.span {y, x} := by rw [hxy, Set.pair_comm]
  intro z
  have hz : z ∈ (⊤ : (maximalIdeal A).blowup.Opens) := trivial
  rw [← Ideal.iSup_opensRange_blowupChart hxy.symm] at hz
  obtain ⟨⟨a, ha⟩, hza⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  rw [Ideal.opensRange_blowupChart] at hza
  rcases ha with rfl | rfl
  · exact isRegularLocalRing_stalk_blowup_of_mem _ (isRegularRing_affineBlowup hdim hxy) z hza
  · exact isRegularLocalRing_stalk_blowup_of_mem _ (isRegularRing_affineBlowup hdim hyx) z hza

end SGA.SGA1.ExposeXIII
