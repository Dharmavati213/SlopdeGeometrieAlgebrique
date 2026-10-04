/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannReduction
import SGA.SGA1.ExposeXI.MultiplicativeGroupCoveringKummer
import SGA.Foundations.Topology.PuncturedDisc

/-!
# SGA 1, Exposé XII, 5.1 for `𝔾_m`: Kummer coverings

The Riemann existence theorem XII.5.1 holds for `𝔾_{m,ℂ} = Spec ℂ[T, T⁻¹]`
(`riemannExistence_laurentPolynomial`). This is the local model SGA uses near a divisor with
normal crossings (the proof of XII.5.1, 2) c)), in dimension one:

* `GmPoints.homeomorph`: `𝔾_m(ℂ) = ℂ ∖ {0}`;
* `Kummer.finiteEtale d`: the Kummer covering `ℂ[T, T⁻¹][z]/(zᵈ - T)` (finite étale by
  `ExposeXI.etale_kummer`), whose points are `{w | wᵈ ≠ 0}` with projection `w ↦ wᵈ`
  (`Kummer.homeomorph`, `Kummer.homeomorph_proj`);
* every connected finite covering of `ℂ ∖ {0}` is a Kummer covering
  (`Complex.exists_homeomorph_powRestrict`, `Foundations/Topology/PuncturedDisc.lean`), so every
  connected finite covering of `𝔾_m(ℂ)` comes from a finite étale algebra
  (`essImage_pointsFunctor_laurentPolynomial`), and `Ψ` is an equivalence
  (`isEquivalence_pointsFunctor_of_forall_isConnected`).

No algebraic computation of `π₁(𝔾_m)` is needed. (Through `autContinuousMulEquiv` this identifies
`π₁(𝔾_{m,ℂ})` with the profinite completion of `π₁(ℂ ∖ {0}) = ℤ`; that corollary is not stated
here.)
-/

noncomputable section

open CategoryTheory Topology Set Polynomial
open scoped LaurentPolynomial

namespace SGA.SGA1.ExposeXII

namespace GmPoints

/-- The punctured plane `ℂ ∖ {0} = 𝔾_m(ℂ)`. -/
abbrev Base : Set ℂ := {0}ᶜ

/-- Evaluation of Laurent polynomials at a nonzero complex number. -/
def evalAt (z : Base) : Points ℂ ℂ[T;T⁻¹] :=
  { LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 z.1 z.2) with
    commutes' := fun c ↦ by
      change LaurentPolynomial.eval₂ (RingHom.id ℂ) _ (LaurentPolynomial.C c) = c
      rw [LaurentPolynomial.eval₂_C]
      rfl }

lemma evalAt_T (z : Base) : evalAt z (LaurentPolynomial.T 1) = z := by
  change LaurentPolynomial.eval₂ (RingHom.id ℂ) _ (LaurentPolynomial.T 1) = z
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  rfl

lemma apply_T_ne_zero (φ : Points ℂ ℂ[T;T⁻¹]) : φ (LaurentPolynomial.T 1) ≠ 0 :=
  ((LaurentPolynomial.isUnit_T 1).map φ).ne_zero

lemma continuous_evalAt_apply (a : ℂ[T;T⁻¹]) : Continuous fun z : Base ↦ evalAt z a := by
  obtain ⟨n, f, hf⟩ := LaurentPolynomial.exists_T_pow a
  have ha : a = Polynomial.toLaurent f * LaurentPolynomial.T (-n) := by
    rw [hf, mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      mul_one]
  have key (z : Base) : evalAt z a = f.eval z.1 * (z.1 ^ n)⁻¹ := by
    change LaurentPolynomial.eval₂ (RingHom.id ℂ) _ a = _
    rw [ha, map_mul, LaurentPolynomial.eval₂_toLaurent, LaurentPolynomial.eval₂_T,
      Polynomial.eval₂_id]
    simp [zpow_neg]
    rfl
  simp_rw [key]
  exact ((f.continuous.comp continuous_subtype_val).mul
    (((continuous_subtype_val.pow n).inv₀ fun z ↦ pow_ne_zero n z.2)))

/-- `𝔾_m(ℂ) = ℂ ∖ {0}`. -/
def homeomorph : Points ℂ ℂ[T;T⁻¹] ≃ₜ Base where
  toFun φ := ⟨φ (LaurentPolynomial.T 1), apply_T_ne_zero φ⟩
  invFun := evalAt
  left_inv φ := by
    refine AlgHom.coe_ringHom_injective (ExposeXI.laurent_ringHom_ext (A := ℂ) (fun c ↦ ?_) ?_)
    · exact ((evalAt _).commutes c).trans (φ.commutes c).symm
    · exact evalAt_T _
  right_inv z := Subtype.ext (evalAt_T z)
  continuous_toFun := ((Points.continuous_apply _).subtype_mk _)
  continuous_invFun := Points.continuous_iff.mpr continuous_evalAt_apply

end GmPoints

namespace Kummer

open CommAlgCat GmPoints

variable (d : ℕ) [NeZero d]

/-- The polynomial `Xᵈ - T` over `ℂ[T, T⁻¹]`. -/
abbrev poly : ℂ[T;T⁻¹][X] := X ^ d - C (LaurentPolynomial.T 1)

/-- The Kummer covering `z ↦ zᵈ` of `𝔾_m`, `ℂ[T, T⁻¹][z]/(zᵈ - T)`, as a finite étale
`ℂ[T, T⁻¹]`-algebra (`ExposeXI.etale_kummer`). -/
def finiteEtale : FiniteEtale ℂ[T;T⁻¹] :=
  haveI := ExposeXI.etale_kummer (k := ℂ) (d := d) (Nat.cast_ne_zero.mpr (NeZero.ne d))
  FiniteEtale.of ℂ[T;T⁻¹] (ExposeXI.KummerAlgebra ℂ[T;T⁻¹] d (LaurentPolynomial.T 1))

/-- The class of `z`. -/
abbrev root : (finiteEtale d).obj := AdjoinRoot.root (poly d)

lemma root_pow : root d ^ d = algebraMap ℂ[T;T⁻¹] (finiteEtale d).obj (LaurentPolynomial.T 1) := by
  have h := AdjoinRoot.eval₂_root (poly d)
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
  exact h

variable {d}

lemma apply_root_pow_mem (χ : letI := algebraOfFiniteEtale ℂ ℂ[T;T⁻¹] (finiteEtale d)
    Points ℂ (finiteEtale d).obj) : χ (root d) ^ d ∈ Base := by
  let := algebraOfFiniteEtale ℂ ℂ[T;T⁻¹] (finiteEtale d)
  rw [← map_pow, root_pow]
  exact (((LaurentPolynomial.isUnit_T 1).map _).map χ).ne_zero

omit [NeZero d] in
lemma eval₂_poly (w : {w : ℂ // w ^ d ∈ Base}) :
    eval₂ (evalAt ⟨w.1 ^ d, w.2⟩).toRingHom w.1 (poly d) = 0 := by
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero]
  exact (evalAt_T ⟨w.1 ^ d, w.2⟩).symm

/-- The point of the Kummer covering with coordinate `w`. -/
def pointOf (w : {w : ℂ // w ^ d ∈ Base}) :
    letI := algebraOfFiniteEtale ℂ ℂ[T;T⁻¹] (finiteEtale d)
    Points ℂ (finiteEtale d).obj :=
  letI := algebraOfFiniteEtale ℂ ℂ[T;T⁻¹] (finiteEtale d)
  { AdjoinRoot.lift (evalAt ⟨w.1 ^ d, w.2⟩).toRingHom w.1 (eval₂_poly w) with
    commutes' := fun c ↦ by
      change AdjoinRoot.lift _ _ _ (AdjoinRoot.of (poly d) (algebraMap ℂ ℂ[T;T⁻¹] c)) = c
      rw [AdjoinRoot.lift_of]
      exact (evalAt _).commutes c }

lemma pointOf_root (w : {w : ℂ // w ^ d ∈ Base}) : pointOf w (root d) = w.1 :=
  AdjoinRoot.lift_root (eval₂_poly w)

lemma pointOf_mk (w : {w : ℂ // w ^ d ∈ Base}) (q : ℂ[T;T⁻¹][X]) :
    pointOf w (AdjoinRoot.mk (poly d) q) = q.eval₂ (evalAt ⟨w.1 ^ d, w.2⟩).toRingHom w.1 :=
  AdjoinRoot.lift_mk (eval₂_poly w) q

lemma pointOf_of (w : {w : ℂ // w ^ d ∈ Base}) (a : ℂ[T;T⁻¹]) :
    pointOf w (AdjoinRoot.of (poly d) a) = evalAt ⟨w.1 ^ d, w.2⟩ a :=
  AdjoinRoot.lift_of (eval₂_poly w)

lemma continuous_pointOf_apply (a : (finiteEtale d).obj) :
    Continuous fun w : {w : ℂ // w ^ d ∈ Base} ↦ pointOf w a := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  simp_rw [pointOf_mk, eval₂_eq_sum_range]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  have h₁ : Continuous fun w : {w : ℂ // w ^ d ∈ Base} ↦ (⟨w.1 ^ d, w.2⟩ : Base) :=
    (continuous_subtype_val.pow d).subtype_mk _
  exact ((continuous_evalAt_apply (q.coeff i)).comp h₁).mul (continuous_subtype_val.pow i)

/-- The points of the Kummer covering: `χ ↦ χ(z)` identifies them with `{w | wᵈ ∈ ℂ ∖ {0}}`. -/
def homeomorph :
    letI := algebraOfFiniteEtale ℂ ℂ[T;T⁻¹] (finiteEtale d)
    Points ℂ (finiteEtale d).obj ≃ₜ {w : ℂ // w ^ d ∈ Base} :=
  letI := algebraOfFiniteEtale ℂ ℂ[T;T⁻¹] (finiteEtale d)
  haveI := isScalarTower_of_finiteEtale ℂ ℂ[T;T⁻¹] (finiteEtale d)
  { toFun χ := ⟨χ (root d), apply_root_pow_mem χ⟩
    invFun := pointOf
    left_inv χ := by
      refine AlgHom.coe_ringHom_injective (AdjoinRoot.ringHom_ext (RingHom.ext fun a ↦ ?_)
        (pointOf_root _))
      have hχ := congrArg (fun φ : Points ℂ ℂ[T;T⁻¹] ↦ φ a) (GmPoints.homeomorph.left_inv
        (Points.map (IsScalarTower.toAlgHom ℂ ℂ[T;T⁻¹] (finiteEtale d).obj) χ))
      have hT : (⟨χ (root d) ^ d, apply_root_pow_mem χ⟩ : Base) =
          GmPoints.homeomorph (Points.map (IsScalarTower.toAlgHom ℂ ℂ[T;T⁻¹] _) χ) :=
        Subtype.ext (by
          change χ (root d) ^ d = χ (algebraMap _ _ (LaurentPolynomial.T 1))
          rw [← root_pow, map_pow])
      refine (pointOf_of _ a).trans ?_
      rw [hT]
      exact hχ
    right_inv w := Subtype.ext (pointOf_root w)
    continuous_toFun := (Points.continuous_apply _).subtype_mk _
    continuous_invFun := Points.continuous_iff.mpr continuous_pointOf_apply }

lemma homeomorph_proj (χ : letI := algebraOfFiniteEtale ℂ ℂ[T;T⁻¹] (finiteEtale d)
    Points ℂ (finiteEtale d).obj) :
    letI := algebraOfFiniteEtale ℂ ℂ[T;T⁻¹] (finiteEtale d)
    haveI := isScalarTower_of_finiteEtale ℂ ℂ[T;T⁻¹] (finiteEtale d)
    GmPoints.homeomorph (Points.proj ℂ[T;T⁻¹] (finiteEtale d).obj χ) =
      Complex.powRestrict Base d (homeomorph χ) := by
  let := algebraOfFiniteEtale ℂ ℂ[T;T⁻¹] (finiteEtale d)
  have := isScalarTower_of_finiteEtale ℂ ℂ[T;T⁻¹] (finiteEtale d)
  refine Subtype.ext ?_
  change χ (algebraMap _ _ (LaurentPolynomial.T 1)) = χ (root d) ^ d
  rw [← root_pow, map_pow]

end Kummer

section Gm

open TopCat.FiniteCovering Opposite

/-- `𝔾_m(ℂ) = ℂ ∖ {0}` is strongly locally contractible. This is a special case of xii52's
`Points.stronglyLocallyContractibleSpace_of_ringKrullDim_le_one` (curves) and of
`Points.stronglyLocallyContractibleSpace_of_smooth`; proved directly here, since `ℂ[T, T⁻¹]` has
neither a Krull dimension nor an `Algebra.Smooth` instance in this repository, and `ℂ ∖ {0}` is
open in `ℂ`. -/
instance stronglyLocallyContractibleSpace_points_laurentPolynomial :
    StronglyLocallyContractibleSpace (Points ℂ ℂ[T;T⁻¹]) :=
  have : StronglyLocallyContractibleSpace GmPoints.Base :=
    isOpen_compl_singleton.stronglyLocallyContractibleSpace
  IsLocalHomeomorph.stronglyLocallyContractibleSpace (Y := Points ℂ ℂ[T;T⁻¹])
    GmPoints.homeomorph.isLocalHomeomorph

/-- XII.5.1 for `𝔾_m`, connected coverings: every connected finite covering of
`𝔾_m(ℂ) = ℂ ∖ {0}` is isomorphic to the Kummer covering `z ↦ zᵈ` of some degree `d`, i.e. to
`S(ℂ)` for `S = ℂ[T, T⁻¹][z]/(zᵈ - T)` (`Complex.exists_homeomorph_powRestrict`). -/
theorem essImage_pointsFunctor_laurentPolynomial
    (E : TopCat.FiniteCovering (TopCat.of (Points ℂ ℂ[T;T⁻¹]))) [ConnectedSpace E.obj.left] :
    (pointsFunctor ℂ ℂ[T;T⁻¹]).essImage E := by
  let h := GmPoints.homeomorph
  let E' := (mapHomeomorph (X := TopCat.of (Points ℂ ℂ[T;T⁻¹])) (Y := TopCat.of GmPoints.Base)
    h).obj E
  have : LocallyPathConnectedSpace E.obj.left :=
    E.isCoveringMap.isLocalHomeomorph.locallyPathConnectedSpace
  have : PathConnectedSpace E.obj.left := .of_locallyPathConnectedSpace
  have : Nonempty E'.obj.left := inferInstanceAs (Nonempty E.obj.left)
  have : PathConnectedSpace E'.obj.left := inferInstanceAs (PathConnectedSpace E.obj.left)
  obtain ⟨n, hn, φ, hφ⟩ := Complex.exists_homeomorph_powRestrict (B := GmPoints.Base)
    isOpen_compl_singleton (by simp) Complex.isSimplyConnected_exp_preimage_compl_zero
    (E := E'.obj.left) (p := E'.obj.hom) E'.isCoveringMap E'.property.2
    fun b e₁ e₂ ↦ exists_monodromy_eq b E' e₁ e₂
  have : NeZero n := ⟨hn⟩
  let := algebraOfFiniteEtale ℂ ℂ[T;T⁻¹] (Kummer.finiteEtale n)
  have := isScalarTower_of_finiteEtale ℂ ℂ[T;T⁻¹] (Kummer.finiteEtale n)
  refine ⟨op (Kummer.finiteEtale n), ⟨ObjectProperty.isoMk _ (Over.isoMk
    (TopCat.isoOfHomeo ((Kummer.homeomorph (d := n)).trans φ.symm)) ?_)⟩⟩
  refine TopCat.hom_ext (ContinuousMap.ext fun χ ↦ h.injective ?_)
  change E'.obj.hom (φ.symm (Kummer.homeomorph χ)) =
    h (Points.proj ℂ[T;T⁻¹] (Kummer.finiteEtale n).obj χ)
  rw [← hφ, Homeomorph.apply_symm_apply]
  exact (Kummer.homeomorph_proj χ).symm

/-- **XII.5.1 for `𝔾_m`**: the Riemann existence theorem holds for `𝔾_{m,ℂ} = Spec ℂ[T, T⁻¹]`:
the functor `Ψ` from finite étale `ℂ[T, T⁻¹]`-algebras to finite coverings of `ℂ ∖ {0}` is an
equivalence of categories. (Every connected finite covering of `ℂ ∖ {0}` is a Kummer covering,
`Complex.exists_homeomorph_powRestrict`; the Kummer coverings are finite étale,
`ExposeXI.etale_kummer`.) -/
theorem riemannExistence_laurentPolynomial :
    (pointsFunctor ℂ ℂ[T;T⁻¹]).IsEquivalence := by
  have : ConnectedSpace (Points ℂ ℂ[T;T⁻¹]) := Points.connectedComparison _ inferInstance
  have : PathConnectedSpace (Points ℂ ℂ[T;T⁻¹]) := .of_locallyPathConnectedSpace
  refine isEquivalence_pointsFunctor_of_forall_isConnected ℂ[T;T⁻¹] fun E _ ↦ ?_
  have := TopCat.FiniteCovering.connectedSpace_of_isConnected E
  exact essImage_pointsFunctor_laurentPolynomial E

end Gm

end SGA.SGA1.ExposeXII
