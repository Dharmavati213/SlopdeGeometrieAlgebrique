/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.PinchingCurve
import SGA.Foundations.Desingularization
import SGA.SGA1.ExposeXIII.DesingularizationCurvesStrong

/-!
# SGA 1, Exposé IX, 5.4, consequence, for the normalization of a curve

Let `D` be an integral scheme of finite type and of dimension `≤ 1` over an algebraically closed
field `k`, and `ν : D' ⟶ D` its normalization (mathlib's relative normalization of
`Spec K(D) ⟶ D`). Then `π₁(D')` is topologically finitely generated as soon as `π₁(D)` is
(`isTopologicallyFG_etaleFundamentalGroup_normalization_of_isTopologicallyFG`); the proof maps
`π₁(D)` continuously onto `π₁(D')` (`SGA.SGA1.ExposeIX.Pinching`). This is the
consequence of IX.5.4 (pinching) for the normalization of a curve; IX.5.5 is the example of a
rational curve with one singular point.

The hypotheses of `isTopologicallyFG_etaleFundamentalGroup_of_isFinite_of_isIso_morphismRestrict`
hold: `ν` is finite (E. Noether,
`AlgebraicGeometry.isFinite_fromNormalization_fromSpecStalk_genericPoint`) and surjective, `D'`
is integral, `ν` is an isomorphism over a nonempty open `V`
(`AlgebraicGeometry.exists_isAffineOpen_isIntegrallyClosed`,
`AlgebraicGeometry.isIso_fromNormalization_restrict`), and `D ∖ V` consists of finitely many
closed points (`SGA.SGA1.ExposeXIII.isClosed_singleton_of_ne_genericPoint`,
`TopologicalSpace.NoetherianSpace.finite_of_isClosed_of_forall_isClosed_singleton`).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeIX

/-- **IX.5.4, consequence, for the normalization of a curve**: let `k` be algebraically closed
and `D` an integral scheme of finite type over `k` of dimension `≤ 1`, with normalization
`ν : D' ⟶ D`. If `π₁(D)` is topologically finitely generated (at some geometric point), so is
`π₁(D')`, at every geometric point (the proof maps `π₁(D)` continuously onto `π₁(D')`).

SGA's IX.5.4 is for a general finite `g : S' ⟶ S` with one geometric point in the fibre over
each point outside a discrete set; here `g` is the normalization of a curve over an algebraically
closed field. -/
theorem isTopologicallyFG_etaleFundamentalGroup_normalization_of_isTopologicallyFG
    {k : Type u} [Field k] [IsAlgClosed k] {D : Scheme.{u}} [IsIntegral D]
    (τ : D ⟶ Spec (.of k)) [LocallyOfFiniteType τ] [CompactSpace D]
    (hD : topologicalKrullDim D ≤ 1) {Ω₀ : Type u} [Field Ω₀] [IsSepClosed Ω₀]
    (s₀ : Spec (.of Ω₀) ⟶ D)
    (h : ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω₀ s₀))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ (D.fromSpecStalk (genericPoint D)).normalization) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω s) := by
  set ν := (D.fromSpecStalk (genericPoint D)).fromNormalization
  have : IsFinite ν := isFinite_fromNormalization_fromSpecStalk_genericPoint τ
  have : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian τ
  have : IsNoetherian D := { }
  obtain ⟨V, hV, hVne, hVi⟩ := exists_isAffineOpen_isIntegrallyClosed τ
  have : Nonempty V := hVne.to_subtype
  have : IsIso (ν ∣_ V) := isIso_fromNormalization_restrict hV
  have hgen (d : D) (hd : d ∉ V) : d ≠ genericPoint D := by
    rintro rfl
    exact hd (((genericPoint_spec D).mem_open_set_iff V.isOpen).mpr (by simpa using hVne))
  have hUc : ∀ d ∉ V, IsClosed ({d} : Set D) := fun d hd ↦
    ExposeXIII.isClosed_singleton_of_ne_genericPoint hD (hgen d hd)
  have hU : (↑V : Set D)ᶜ.Finite :=
    TopologicalSpace.NoetherianSpace.finite_of_isClosed_of_forall_isClosed_singleton
      V.isOpen.isClosed_compl hUc
  exact isTopologicallyFG_etaleFundamentalGroup_of_isFinite_of_isIso_morphismRestrict τ ν V hU hUc
    s₀ h Ω s

end SGA.SGA1.ExposeIX
