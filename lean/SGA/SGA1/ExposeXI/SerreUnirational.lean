/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.UnirationalCovers
import SGA.SGA1.ExposeXI.UnirationalCurves
import SGA.SGA1.ExposeXI.UnirationalForms
import SGA.SGA1.ExposeX.ProperOverField
import SGA.Foundations.Cohomology.EulerCharacteristicFiniteEtaleProof
import SGA.Foundations.Cohomology.ProperFiniteness
import SGA.Foundations.Limits.GeometricFiberCardIso

/-!
# Serre's theorem: unirational varieties are simply connected (XI.1.4)

XI.1.4 (Serre, 1959) says that a smooth projective unirational variety `X` over an algebraically
closed field of characteristic `0` is simply connected (`SerreUnirationalSimplyConnectedStatement`,
stated for proper `X`). SGA gives no proof; Serre's argument has four steps:

1. `H⁰(X, Ω^q) = 0` for `q > 0`: a regular form pulls back to a regular form on `ℙʳ`, hence is `0`
   (`regularForms`, in `UnirationalForms`);
2. Hodge symmetry `h^{0,q} = h^{q,0}` (transcendental), hence `H^q(X, 𝒪_X) = 0` for `q > 0` and
   `χ(X, 𝒪_X) = 1`;
3. a connected finite étale covering `Y ⟶ X` is again unirational
   (`isUnirational_of_isFinite_of_etale`, in `UnirationalCovers`), so `χ(Y, 𝒪_Y) = 1` too;
4. `χ(Y, 𝒪_Y) = d χ(X, 𝒪_X)` for `Y ⟶ X` of degree `d` (`EulerCharFiniteEtaleStatement`, proved
   by dévissage in `eulerCharFiniteEtaleStatement`, in every characteristic), so `d = 1`.

This file states the transcendental input of step 2, `HodgeSymmetryZeroStatement`, and Serre's
vanishing `UnirationalStructureSheafVanishingStatement`, and proves:

* `unirationalStructureSheafVanishing_of_hodgeSymmetryZero`: step 2, from Hodge symmetry and
  step 1 (`regularForms_eq_bot_of_isUnirational`);
* `serreUnirationalSimplyConnectedStatement_of_vanishing`: steps 3–4, XI.1.4 follows from
  `UnirationalStructureSheafVanishingStatement`;
* `serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero`: XI.1.4 follows from
  `HodgeSymmetryZeroStatement`, the only remaining (transcendental) input.

Helpers: `finrankH_unit_zero_eq_one` and `eulerChar_unit_eq_one`; a finite étale morphism of
degree one onto a connected scheme is an isomorphism by
`Scheme.Hom.isIso_of_geometricFiberCard_eq_one_of_connectedSpace`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits PreGaloisCategory

namespace SGA.SGA1.ExposeXI

section Statements

/-- XI.1.4, transcendental input (statement only): the `(0, q)` case of **Hodge symmetry**,
`h^{0,q} = h^{q,0}`, i.e. `dim_k H^q(X, 𝒪_X) = dim_k H⁰(X, Ω^q_{X/k})`, for a smooth proper integral
scheme `X` over an algebraically closed field `k` of characteristic `0`. Here `H⁰(X, Ω^q_{X/k})` is
`regularForms f q` (the forms of `Ω^q_{K(X)/k}` regular at every point). For projective `X` over
`ℂ` this is Hodge theory (`H^q(X, 𝒪) ≅ conj H⁰(X, Ω^q)`); for proper `X` it follows from Deligne's
purity of the Hodge structure on `H^n(X)` (Hodge II), and for arbitrary `k` by the Lefschetz
principle. It is the only transcendental ingredient of Serre's proof of XI.1.4. -/
def HodgeSymmetryZeroStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f] (q : ℕ),
    letI := (functionFieldMap f).toAlgebra
    Scheme.Modules.finrankH f (CohomologyAux.unitModule X) q =
      Module.finrank k (regularForms f q)

/-- XI.1.4, step 2 of Serre's proof (statement only): a smooth proper integral unirational scheme
`X` over an algebraically closed field of characteristic `0` has `H^q(X, 𝒪_X) = 0` for `q > 0`.
It follows from `HodgeSymmetryZeroStatement` and the vanishing of regular forms. -/
def UnirationalStructureSheafVanishingStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f],
    (letI := (functionFieldMap f).toAlgebra; IsUnirational k X.functionField) →
    ∀ q : ℕ, Subsingleton ((CohomologyAux.unitModule X).H (q + 1))

end Statements

section EulerCharacteristic

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsProper f] [IsReduced X] [ConnectedSpace X]

/-- `h⁰(X, 𝒪_X) = 1` for a proper connected reduced scheme `X` over an algebraically closed field
(`Γ(X, 𝒪_X) = k`, `ExposeX.isIso_app_of_isProper`). -/
theorem finrankH_unit_zero_eq_one :
    Scheme.Modules.finrankH f (CohomologyAux.unitModule X) 0 = 1 := by
  have := ExposeX.isIso_app_of_isProper f ⊤
  have hφ : Function.Bijective f.specStructureRingHom := by
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
      inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.app ⊤))
    exact ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)
  let _ := (CohomologyAux.unitModule X).moduleOver f 0 ⊤
  have h := rank_eq_of_equiv_equiv f.specStructureRingHom
    (Scheme.Modules.H.equiv₀ (CohomologyAux.unitModule X)).toAddEquiv hφ
    fun r m ↦ (Scheme.Modules.H.equiv₀ _).map_smul (f.specStructureRingHom r) m
  rw [Scheme.Modules.finrankH, Module.finrank, h]
  exact CommSemiring.finrank_self Γ(X, ⊤)

/-- `χ(X, 𝒪_X) = 1` for a proper connected reduced scheme `X` over an algebraically closed field
with `H^q(X, 𝒪_X) = 0` for `q > 0`. -/
theorem eulerChar_unit_eq_one
    (hV : ∀ q : ℕ, Subsingleton ((CohomologyAux.unitModule X).H (q + 1))) :
    Scheme.Modules.eulerChar f (CohomologyAux.unitModule X) = 1 := by
  rw [Scheme.Modules.eulerChar_eq_sum f _ {0} (fun p hp ↦ ?_), Finset.sum_singleton, pow_zero,
    one_mul, finrankH_unit_zero_eq_one f, Nat.cast_one]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simpa using hp)
  have := hV q
  let _ := (CohomologyAux.unitModule X).moduleOver f (q + 1) ⊤
  exact Module.finrank_zero_of_subsingleton

end EulerCharacteristic

section Serre

/-- XI.1.4, Serre's deduction (steps 3 and 4): if smooth proper unirational varieties in
characteristic `0` have `H^q(𝒪) = 0` for `q > 0` (`UnirationalStructureSheafVanishingStatement`),
then they are simply connected. A connected finite étale covering `Y ⟶ X` of degree `d` is again
smooth, proper and unirational, so `1 = χ(Y, 𝒪_Y) = d χ(X, 𝒪_X) = d`
(`eulerCharFiniteEtaleStatement`). -/
theorem serreUnirationalSimplyConnectedStatement_of_vanishing
    (hV : UnirationalStructureSheafVanishingStatement.{u}) :
    SerreUnirationalSimplyConnectedStatement.{u} := by
  intro k _ _ _ X _ f _ _ h
  refine ⟨inferInstance, fun Y π _ _ hY ↦ ?_⟩
  have hXn : IsNormalScheme X := isNormalScheme_of_smooth f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsIntegral Y := isIntegral_of_etale_of_isNormalScheme (fun x ↦ ⟨inferInstance, hXn x⟩) π
  have hY' := isUnirational_of_isFinite_of_etale f π h
  have hχX := eulerChar_unit_eq_one f (hV k X f h)
  have hχY := eulerChar_unit_eq_one (π ≫ f) (hV k Y (π ≫ f) hY')
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  have hd : ∀ x : X, π.geometricFiberCard x = π.geometricFiberCard x₀ := fun x ↦
    congrFun (π.isLocallyConstant_geometricFiberCard.eq_const x₀) x
  have e := eulerCharFiniteEtaleStatement k X Y f π _ hd
  rw [hχX, hχY, mul_one] at e
  exact π.isIso_of_geometricFiberCard_eq_one_of_connectedSpace x₀ (by exact_mod_cast e.symm)

/-- XI.1.4, step 2 of Serre's proof: Hodge symmetry `h^{0,q} = h^{q,0}`
(`HodgeSymmetryZeroStatement`) and the vanishing of regular forms on unirational varieties
(`regularForms_eq_bot_of_isUnirational`) give `H^q(X, 𝒪_X) = 0` for `q > 0`. -/
theorem unirationalStructureSheafVanishing_of_hodgeSymmetryZero
    (hH : HodgeSymmetryZeroStatement.{u}) : UnirationalStructureSheafVanishingStatement.{u} := by
  intro k _ _ _ X _ f _ _ h q
  have e := hH k X f (q + 1)
  rw [regularForms_eq_bot_of_isUnirational f h (Nat.succ_pos q), finrank_bot] at e
  let _ := (CohomologyAux.unitModule X).moduleOver f (q + 1) ⊤
  have : Module.Finite k ((CohomologyAux.unitModule X).H (q + 1)) :=
    properFinitenessStatement (.of k) X f (CohomologyAux.unitModule X) (q + 1)
  exact Module.finrank_zero_iff.mp e

/-- **XI.1.4 (Serre), conditional form**: a smooth proper unirational variety over an
algebraically closed field of characteristic `0` is simply connected, given Hodge symmetry
`h^{0,q} = h^{q,0}` (`HodgeSymmetryZeroStatement`, transcendental; not proved). Everything else in
Serre's proof is proved, in particular the multiplicativity of `χ(𝒪)` in finite étale coverings
(`eulerCharFiniteEtaleStatement`). -/
theorem serreUnirationalSimplyConnectedStatement_of_hodgeSymmetryZero
    (hH : HodgeSymmetryZeroStatement.{u}) : SerreUnirationalSimplyConnectedStatement.{u} :=
  serreUnirationalSimplyConnectedStatement_of_vanishing
    (unirationalStructureSheafVanishing_of_hodgeSymmetryZero hH)

end Serre

end SGA.SGA1.ExposeXI
