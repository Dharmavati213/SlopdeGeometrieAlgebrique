/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.RationalVarieties
import SGA.SGA1.ExposeII.Field
import SGA.SGA1.ExposeX.PurityDenseOpen
import Mathlib.FieldTheory.RatFunc.Luroth

/-!
# Unirational curves are simply connected (XI.1.4 for curves)

XI.1.4 (Serre) says that a smooth projective unirational variety over an algebraically closed
field of characteristic `0` is simply connected. For curves no Hodge theory is needed, and the
characteristic is irrelevant: by Lüroth's theorem (mathlib's `RatFunc.Luroth.algEquiv`) a
unirational field of transcendence degree one is purely transcendental, so the curve is rational
and XI.1.2 (`isSimplyConnected_of_isPurelyTranscendental`) applies.

* `IsPurelyTranscendental.of_algEquiv`: pure transcendence is invariant under `k`-isomorphism.
* `isPurelyTranscendental_ratFunc`: `k(X)` is purely transcendental over `k`.
* `isPurelyTranscendental_of_isUnirational_of_trdeg_eq_one`: Lüroth's theorem in the form
  "unirational of transcendence degree one implies purely transcendental", for any field `k`.
* `isSimplyConnected_of_isUnirational_of_trdeg_eq_one`: XI.1.4 for normal proper curves, in every
  characteristic (curves expressed by `trdeg_k K(X) = 1`);
  `isSimplyConnected_of_isUnirational_of_trdeg_eq_one_of_smooth` is the smooth version.
-/

universe u

open AlgebraicGeometry CategoryTheory IntermediateField

namespace SGA.SGA1.ExposeXI

section Field

variable {k A B : Type*} [Field k] [Field A] [Field B] [Algebra k A] [Algebra k B]

/-- Pure transcendence is invariant under isomorphisms of `k`-algebras. -/
theorem IsPurelyTranscendental.of_algEquiv (e : A ≃ₐ[k] B) (h : IsPurelyTranscendental k A) :
    IsPurelyTranscendental k B := by
  obtain ⟨s, hs, hadj⟩ := h
  refine ⟨e '' s, ?_, ?_⟩
  · have h' : AlgebraicIndependent k (e.toAlgHom ∘ ((↑) : s → A)) := hs.map' e.injective
    exact (algebraicIndependent_image (f := e.toAlgHom) e.injective.injOn).mp h'
  · change adjoin k (e.toAlgHom '' s) = ⊤
    rw [← IntermediateField.adjoin_map, hadj]
    rw [← AlgHom.fieldRange_eq_map]
    exact AlgHom.fieldRange_eq_top.mpr e.surjective

variable (k) in
/-- The rational function field `k(X)` is purely transcendental over `k`. -/
theorem isPurelyTranscendental_ratFunc : IsPurelyTranscendental k (RatFunc k) :=
  ⟨{RatFunc.X}, (algebraicIndependent_singleton_iff ⟨_, rfl⟩).mpr RatFunc.transcendental_X,
    RatFunc.adjoin_X⟩

/-- **Lüroth's theorem**, unirational form (used for XI.1.4 for curves): a field `K ⊇ k` of
transcendence degree one over `k` which has a finite extension `L` purely transcendental over `k`
is itself purely transcendental over `k`. No assumption on `k` is needed. -/
theorem isPurelyTranscendental_of_isUnirational_of_trdeg_eq_one {k K : Type u} [Field k]
    [Field K] [Algebra k K] (h : IsUnirational k K) (h1 : Algebra.trdeg k K = 1) :
    IsPurelyTranscendental k K := by
  obtain ⟨L, _, _, _, hL⟩ := h
  let _ : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨s, hs, hadj⟩ := hL
  -- `trdeg_k L = 1`
  have hL1 : Algebra.trdeg k L = 1 := by
    rw [← trdeg_add_eq k K (A := L), h1, trdeg_eq_zero, add_zero]
  -- so `s = {t}`
  have hs1 : Cardinal.mk s ≤ 1 := hL1 ▸ hs.cardinalMk_le_trdeg
  have hsne : s.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    rw [IntermediateField.adjoin_empty] at hadj
    have : Algebra.IsAlgebraic k L := by
      refine ⟨fun x ↦ ?_⟩
      have hx : x ∈ (⊥ : IntermediateField k L) := hadj ▸ IntermediateField.mem_top
      obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hx
      exact isAlgebraic_algebraMap c
    rw [trdeg_eq_zero] at hL1
    exact zero_ne_one hL1
  obtain ⟨t, ht⟩ := hsne
  have hst : s = {t} :=
    (Cardinal.mk_le_one_iff_set_subsingleton.mp hs1).eq_singleton_of_mem ht
  subst hst
  have htr : Transcendental k t := (algebraicIndependent_singleton_iff ⟨t, rfl⟩).mp hs
  -- `L ≅ k(X)`
  let eL : RatFunc k ≃ₐ[k] L := (RatFunc.algEquivOfTranscendental t htr).trans
    ((IntermediateField.equivOfEq hadj).trans
      IntermediateField.topEquiv)
  -- the image `E ⊆ k(X)` of `K`
  let ψ : K →ₐ[k] RatFunc k := eL.symm.toAlgHom.comp (IsScalarTower.toAlgHom k K L)
  let eK : K ≃ₐ[k] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  have hE : ψ.fieldRange ≠ ⊥ := by
    intro hbot
    have h0 : Algebra.trdeg k ψ.fieldRange = 0 := by
      rw [hbot, trdeg_eq_zero_iff]
      exact (IntermediateField.botEquiv k (RatFunc k)).symm.isAlgebraic
    rw [← eK.trdeg_eq, h1] at h0
    exact one_ne_zero h0
  exact (isPurelyTranscendental_ratFunc k).of_algEquiv
    ((RatFunc.Luroth.algEquiv hE).trans eK.symm)

end Field

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- XI.1.4 for curves, in every characteristic: a proper normal integral scheme over an
algebraically closed field `k` whose function field is unirational of transcendence degree one
over `k` is simply connected. This differs from SGA's XI.1.4 in that `X` is a curve (expressed by
`trdeg_k K(X) = 1`) and only normal, and that `k` may have any characteristic. The proof is
Lüroth's theorem plus XI.1.2; no Hodge theory is needed. -/
theorem isSimplyConnected_of_isUnirational_of_trdeg_eq_one [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [IsProper f] (hX : IsNormalScheme X)
    (h : letI := (functionFieldMap f).toAlgebra; IsUnirational k X.functionField)
    (h1 : letI := (functionFieldMap f).toAlgebra; Algebra.trdeg k X.functionField = 1) :
    IsSimplyConnected X :=
  let _ := (functionFieldMap f).toAlgebra
  isSimplyConnected_of_isPurelyTranscendental f hX
    (isPurelyTranscendental_of_isUnirational_of_trdeg_eq_one h h1)

omit [IsIntegral X] in
/-- A scheme smooth over a field is normal (via II.5.3: it is regular). -/
theorem isNormalScheme_of_smooth (f : X ⟶ Spec (.of k)) [Smooth f] : IsNormalScheme X :=
  fun x ↦ (ExposeX.isNormalScheme_of_isRegularScheme
    (fun y ↦ ExposeII.isRegularLocalRing_stalk_of_smooth_field k f y) x).2

/-- XI.1.4 for smooth proper curves, in every characteristic: a smooth proper integral scheme over
an algebraically closed field `k` whose function field is unirational of transcendence degree one
over `k` is simply connected. This is SGA's XI.1.4 restricted to curves (expressed by
`trdeg_k K(X) = 1`), with the characteristic-zero hypothesis dropped. -/
theorem isSimplyConnected_of_isUnirational_of_trdeg_eq_one_of_smooth [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    (h : letI := (functionFieldMap f).toAlgebra; IsUnirational k X.functionField)
    (h1 : letI := (functionFieldMap f).toAlgebra; Algebra.trdeg k X.functionField = 1) :
    IsSimplyConnected X :=
  isSimplyConnected_of_isUnirational_of_trdeg_eq_one f (isNormalScheme_of_smooth f) h h1

end Curve

end SGA.SGA1.ExposeXI
