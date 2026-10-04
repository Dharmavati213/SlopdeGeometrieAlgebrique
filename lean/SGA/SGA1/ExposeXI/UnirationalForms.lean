/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.UnirationalVarieties
import SGA.SGA1.ExposeXI.UnirationalCoversParametrization
import SGA.SGA1.ExposeXI.UnirationalFormsAlgebra
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin

/-!
# Regular differential forms (XI.1.4, step 1)

Step (1) of Serre's proof of XI.1.4 is that a unirational variety in characteristic `0` has no
nonzero regular `p`-forms for `p > 0`. To state it without building the sheaf `Ω^p_{X/k}`, we
define the regular `p`-forms of an integral `k`-scheme `X` inside `Ω^p_{K/k} = ⋀^p_K Ω_{K/k}`,
`K = K(X)`:

* `regularForms f p`: the `p`-forms which lie, for every point `x`, in the image of
  `⋀^p Ω_{𝒪_{X,x}/k}`, i.e. are `k`-linear combinations of `a₀ da₁ ∧ ⋯ ∧ daₚ` with `aᵢ ∈ 𝒪_{X,x}`.

When `X` is smooth over `k`, `Ω^p_{X/k}` is locally free, so its global sections are the elements of
its generic stalk `Ω^p_{K/k}` lying in every stalk `Ω^p_{𝒪_{X,x}/k}`: `regularForms f p` is
`Γ(X, Ω^p_{X/k}) = H^0(X, Ω^p_{X/k})` (EGA IV 17.2.3 for local freeness; Hartshorne II.8.13).

* `exists_germ_mem_of_valuationSubring`: a valuation ring of `K(X)` containing `k` has a centre on
  `X` when `X` is proper over `k` (valuative criterion);
* `regularForms_eq_bot_of_isUnirational`: **Serre's step (1)**, in characteristic `0`: a proper
  integral `k`-scheme whose function field is unirational has no nonzero regular `p`-forms,
  `p > 0`. No smoothness is needed. Serre pulls a form back to `ℙʳ` and uses
  `H⁰(ℙʳ, Ω^p) = 0`; we pull it back to `k(x₁, …, x_r)` and show that its coefficients are
  polynomials (regularity at the primes of `k[x]`) with positive valuation at infinity, hence `0`
  (`RegularForms.eq_zero_of_forall_mem_spanOver`).
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace SGA.SGA1.ExposeXI

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- The **regular `p`-forms** of an integral scheme `X` over `Spec k`, as a `k`-subspace of
`Ω^p_{K/k} = ⋀^p_K Ω_{K/k}`, `K = K(X)`: the forms which, for every `x ∈ X`, are `k`-linear
combinations of `a₀ da₁ ∧ ⋯ ∧ daₚ` with `aᵢ ∈ 𝒪_{X,x}` (i.e. lie in the image of
`⋀^p Ω_{𝒪_{X,x}/k}`). For `X` smooth over `k` this is `H⁰(X, Ω^p_{X/k})`. -/
noncomputable def regularForms (f : X ⟶ Spec (.of k)) (p : ℕ) :
    letI := (functionFieldMap f).toAlgebra
    Submodule k (⋀[X.functionField]^p Ω[X.functionField⁄k]) :=
  letI := (functionFieldMap f).toAlgebra
  ⨅ x : X, Submodule.span k
    {ω | ∃ a : Fin (p + 1) → X.presheaf.stalk x,
      ω = (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom (a 0) •
        exteriorPower.ιMulti X.functionField p (fun i ↦ KaehlerDifferential.D k X.functionField
          ((X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom (a i.succ)))}

/-- A valuation ring of the function field of an integral scheme `X` proper over `k`, containing
`k`, has a centre on `X`: a point `x` whose local ring maps into it (valuative criterion of
properness, EGA II 7.3.8; Stacks Tag 0BX5). -/
theorem exists_germ_mem_of_valuationSubring (f : X ⟶ Spec (.of k)) [IsProper f]
    (U : ValuationSubring X.functionField) (hU : ∀ c : k, functionFieldMap f c ∈ U) :
    ∃ x : X, ∀ a : X.presheaf.stalk x,
      (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom a ∈ U := by
  let φU : k →+* U := (functionFieldMap f).codRestrict U.toSubring hU
  have hsq : CommSq (X.fromSpecStalk (genericPoint X) : Spec (.of X.functionField) ⟶ X)
      (Spec.map (CommRingCat.ofHom (algebraMap U X.functionField))) f
      (Spec.map (CommRingCat.ofHom φU)) := ⟨by
    rw [fromSpecStalk_comp_eq_SpecMap]
    exact (congrArg Spec.map (show CommRingCat.ofHom (functionFieldMap f) =
      CommRingCat.ofHom φU ≫ CommRingCat.ofHom (algebraMap U X.functionField) from rfl)).trans
      (Spec.map_comp _ _)⟩
  let V : ValuativeCommSq f :=
    { R := U, K := X.functionField, i₁ := X.fromSpecStalk (genericPoint X),
      i₂ := Spec.map (CommRingCat.ofHom φU), commSq := hsq }
  have hE : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨⟨l, hl₁, -⟩⟩ := (hE V).exists_lift
  change Spec.map (CommRingCat.ofHom (algebraMap U X.functionField)) ≫ l =
    X.fromSpecStalk (genericPoint X) at hl₁
  obtain ⟨a, -, ha⟩ := exists_SpecMap_fromSpecStalk l (l (IsLocalRing.closedPoint U)) rfl
  refine ⟨l (IsLocalRing.closedPoint U), fun s ↦ ?_⟩
  have e : a ≫ CommRingCat.ofHom (algebraMap U X.functionField) =
      X.presheaf.stalkSpecializes (genericPoint_specializes _) := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk _), Spec.map_comp, Category.assoc, ha, hl₁,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  rw [← e]
  exact (a.hom s).2

/-- **XI.1.4, step (1) of Serre's proof**: let `X` be a proper integral scheme over a field `k` of
characteristic `0` whose function field is unirational over `k`. Then `X` has no nonzero regular
`p`-forms for `p > 0`: `regularForms f p = ⊥`, i.e. `H⁰(X, Ω^p_{X/k}) = 0` when `X` is smooth.
This is more general than Serre's statement (no smoothness, no projectivity, any `k` of
characteristic `0`). -/
theorem regularForms_eq_bot_of_isUnirational [CharZero k] (f : X ⟶ Spec (.of k)) [IsProper f]
    (h : letI := (functionFieldMap f).toAlgebra; IsUnirational k X.functionField) {p : ℕ}
    (hp : 0 < p) : regularForms f p = ⊥ := by
  let _ := (functionFieldMap f).toAlgebra
  have : Algebra.EssFiniteType k X.functionField := essFiniteType_functionFieldMap f
  -- `K(X)` embeds into `k(x_i : i ∈ σ)`, finite over it.
  obtain ⟨σ, _, ι, _⟩ := exists_algHom_fractionRing_of_isUnirational h
  let _ : Algebra X.functionField (FractionRing (MvPolynomial σ k)) := ι.toRingHom.toAlgebra
  have : IsScalarTower k X.functionField (FractionRing (MvPolynomial σ k)) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (ι.commutes c).symm
  let _ : LinearOrder σ := IsWellOrder.linearOrder WellOrderingRel
  -- Every regular form satisfies the hypothesis of `RegularForms.eq_zero_of_forall_mem_spanOver`.
  rw [eq_bot_iff]
  intro ω hω
  rw [Submodule.mem_bot]
  refine RegularForms.eq_zero_of_forall_mem_spanOver (σ := σ) p hp ω fun V hV ↦ ?_
  let U := V.comap (algebraMap X.functionField (FractionRing (MvPolynomial σ k)))
  have hU : ∀ c : k, functionFieldMap f c ∈ U := fun c ↦ by
    change algebraMap X.functionField _ (algebraMap k X.functionField c) ∈ V
    rw [← IsScalarTower.algebraMap_apply]
    exact hV c
  obtain ⟨x, hx⟩ := exists_germ_mem_of_valuationSubring f U hU
  have hωx := (iInf_le _ x : regularForms f p ≤ _) hω
  refine Submodule.span_mono ?_ hωx
  rintro _ ⟨a, rfl⟩
  exact ⟨fun i ↦ (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom (a i),
    fun i ↦ hx (a i), rfl⟩

end SGA.SGA1.ExposeXI
