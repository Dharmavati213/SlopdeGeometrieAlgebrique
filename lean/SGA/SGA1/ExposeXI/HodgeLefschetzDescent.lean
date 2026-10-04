/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.HodgeLefschetz
import SGA.SGA1.ExposeX.BaseChangeAlgClosed
import SGA.SGA1.ExposeXI.ProjectiveSpaceSimplyConnected

/-!
# The Lefschetz principle for XI.1.4: fields of any cardinality

`HodgeLefschetz.lean` proves XI.1.4 (projective form) over algebraically closed fields `k` of
characteristic `0` with `#k ≤ 𝔠` (embed `k ↪ ℂ`). For larger `k` one first descends `X` to a
countable algebraically closed subfield `k₁ ⊆ k`, then uses that `π₁` does not change under
extension of algebraically closed fields (X.1.8).

* `isSimplyConnected_pullback_of_isSimplyConnected`: **X.1.8 for simple connectivity**: for
  `k ⊆ K` algebraically closed and `X` proper over `k`, if `X` is simply connected then so is
  `X ×_k K` (`ExposeX.bijective_map_pullback_fst`).
* `SerreLefschetzDescentStatement` (statement only): a smooth projective integral unirational
  scheme over an algebraically closed field `K` of characteristic `0` is the base change of a
  smooth projective integral unirational scheme over a countable algebraically closed subfield of
  `K`. This is the spreading-out half of the Lefschetz principle (EGA IV 8; registry rows A4,
  A47). Proved as `serreLefschetzDescentStatement` in `HodgeLefschetzSpread.lean`.
* `serreUnirationalProjectiveStatement_of_hodgeSymmetryZeroComplex_of_descent`: **XI.1.4 in SGA's
  form, in universe `0`**, from `HodgeSymmetryZeroComplexStatement` (stream `hodge`) and
  `SerreLefschetzDescentStatement` (proved in `HodgeLefschetzSpread.lean`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace SGA.SGA1.ExposeXI

/-- **X.1.8 for simple connectivity**: let `k ⊆ K` be algebraically closed fields and `X` a proper
`k`-scheme. If `X` is simply connected, so is `X ×_k K`: it is connected (`k = k̄`), and
`π₁(X ×_k K) → π₁(X)` is bijective (`ExposeX.bijective_map_pullback_fst`). -/
theorem isSimplyConnected_pullback_of_isSimplyConnected {k K : Type u} [Field k] [IsAlgClosed k]
    [Field K] [IsAlgClosed K] [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (h : IsSimplyConnected X) :
    IsSimplyConnected (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have : ConnectedSpace X := h.1
  set ρ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : ConnectedSpace ↥(pullback f ρ) :=
    connectedSpace_pullback_of_isAlgClosed_of_connectedSpace f ρ
  obtain ⟨z⟩ : Nonempty ↥(pullback f ρ) := inferInstance
  let φ : (pullback f ρ).residueField z ⟶
      CommRingCat.of (AlgebraicClosure ((pullback f ρ).residueField z)) :=
    CommRingCat.ofHom (algebraMap ((pullback f ρ).residueField z)
      (AlgebraicClosure ((pullback f ρ).residueField z)))
  let t := Spec.map φ ≫ (pullback f ρ).fromSpecResidueField z
  refine (isSimplyConnected_iff_subsingleton _ t).mpr ?_
  have := (isSimplyConnected_iff_subsingleton _ (t ≫ pullback.fst f ρ)).mp h
  exact (ExposeX.bijective_map_pullback_fst k K f _ t).injective.subsingleton

/-- XI.1.4, Lefschetz principle, spreading-out half (statement only): a smooth projective
(proper and quasi-projective) integral scheme `X` over an algebraically closed field `K` of
characteristic `0` with unirational function field is the base change `X₁ ×_{k₁} K` of a smooth
projective integral scheme `X₁` with unirational function field over a countable algebraically
closed subfield `k₁ ⊆ K` (EGA IV 8.8.2, 8.10.5, 17.7.8). -/
def SerreLefschetzDescentStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [IsQuasiProjective f] [Smooth f],
    (letI := (functionFieldMap f).toAlgebra; IsUnirational K X.functionField) →
    ∃ (k₁ : Subfield K) (X₁ : Scheme.{u}) (_ : IsIntegral X₁) (f₁ : X₁ ⟶ Spec (.of k₁))
      (e : X ⟶ X₁), IsAlgClosed k₁ ∧ Countable k₁ ∧ IsProper f₁ ∧ IsQuasiProjective f₁ ∧
        Smooth f₁ ∧ (letI := (functionFieldMap f₁).toAlgebra; IsUnirational k₁ X₁.functionField) ∧
        IsPullback e f f₁ (Spec.map (CommRingCat.ofHom k₁.subtype))

/-- **XI.1.4 (Serre) in SGA's form, in universe `0`**, conditional on Hodge symmetry over `ℂ`
(`HodgeSymmetryZeroComplexStatement`, stream `hodge`) and on the spreading-out half of the
Lefschetz principle (`SerreLefschetzDescentStatement`, proved as `serreLefschetzDescentStatement`
in `HodgeLefschetzSpread.lean`, where the combination is
`serreUnirationalProjectiveStatement_of_hodgeSymmetryZeroComplex`). Descend `X` to
`X₁` over a countable algebraically closed `k₁ ⊆ K`; `X₁` is simply connected because `k₁` embeds
in `ℂ` (`isSimplyConnected_of_hodgeSymmetryZeroComplex_of_mk_le_continuum`), and so is
`X = X₁ ×_{k₁} K` by X.1.8 (`isSimplyConnected_pullback_of_isSimplyConnected`). -/
theorem serreUnirationalProjectiveStatement_of_hodgeSymmetryZeroComplex_of_descent
    (hC : HodgeSymmetryZeroComplexStatement) (hD : SerreLefschetzDescentStatement.{0}) :
    SerreUnirationalProjectiveStatement.{0} := by
  intro K _ _ _ X _ f _ _ _ h
  obtain ⟨k₁, X₁, _, f₁, e, _, _, _, _, _, h₁, H⟩ := hD K X f h
  have : CharZero k₁ := ⟨fun a b hab ↦ by simpa using congrArg k₁.subtype hab⟩
  have hk : Cardinal.mk k₁ ≤ Cardinal.continuum :=
    Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum
  have hX₁ := isSimplyConnected_of_hodgeSymmetryZeroComplex_of_mk_le_continuum hC hk f₁ h₁
  exact ProjectiveSpace.isSimplyConnected_of_iso H.isoPullback.symm
    (isSimplyConnected_pullback_of_isSimplyConnected (K := K) f₁ hX₁)

end SGA.SGA1.ExposeXI
