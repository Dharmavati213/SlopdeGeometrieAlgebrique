/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.MultiplicativeGroupInertiaChart

/-!
# SGA 1, XIII.2.12 for `g = 0`, `n = 2`: the inertia condition at `0` on `𝔾_m ⊆ 𝔸¹`

Let `k` be algebraically closed of characteristic `p`, `X = 𝔸¹_k = Spec k[T]` and
`U = 𝔾_m = D(T)` (`multiplicativeGroupOpen`). XIII.2.12 for `ℙ¹ - {0, ∞}` asks that the generator
`σ` of `π₁^{p'}(U)` (`multiplicativeGroupPrimeToPStatement`) generate an inertia group at `0`
(`IsInertiaSubgroupAt`). `multiplicativeGroupInertiaStatement` proves it on the chart `𝔸¹` of
`ℙ¹`: every inertia subgroup `H` at a geometric point over the origin maps onto `π₁^{p'}(U)`. It is
the case `V = 𝔸¹` of `AffineLineChart.topologicalClosure_sup_proLKernel_eq_top` (the Kummer
coverings `z^m = T` stay connected over `U ×_X Spec 𝒪^{sh}`). The statement on `ℙ¹`, with inertia
at `0` and at `∞`, is `tameCurvePrimeToPConclusion_projectiveLine_two`.

References: SGA 1 XIII.2.12; for strict localizations EGA IV 18.8, Stacks 04HX.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Polynomial LaurentPolynomial

namespace SGA.SGA1.ExposeXIII

/-- The multiplicative group `𝔾_{m,k} = D(T)`, as an open subscheme of the affine line
`𝔸¹_k = Spec k[T]`. -/
noncomputable abbrev multiplicativeGroupOpen (k : Type u) [Field k] : (Spec (.of k[X])).Opens :=
  PrimeSpectrum.basicOpen (Polynomial.X : k[X])

namespace AffineLineOrigin

variable (k : Type u) [Field k]

/-- `𝔾_m = D(T) ≅ Spec k[T, T⁻¹]`. -/
noncomputable def multiplicativeGroupOpenIso :
    (multiplicativeGroupOpen k : Scheme.{u}) ≅ Spec (.of k[T;T⁻¹]) :=
  basicOpenIsoSpecAway (R := .of k[X]) Polynomial.X ≪≫ (Scheme.Spec.mapIso
    (IsLocalization.algEquiv (Submonoid.powers (Polynomial.X : k[X]))
      (Localization.Away (Polynomial.X : k[X])) k[T;T⁻¹]).toRingEquiv.toCommRingCatIso.op).symm

/-- `Γ(𝔸¹) ≅ k[T]`. -/
noncomputable abbrev sectionsEquiv : Γ(Spec (.of k[X]), ⊤) ≃+* k[X] :=
  (Scheme.ΓSpecIso (.of k[X])).commRingCatIsoToRingEquiv

lemma basicOpen_sectionsEquiv_symm :
    (Spec (.of k[X])).basicOpen ((sectionsEquiv k).symm Polynomial.X) =
      multiplicativeGroupOpen k :=
  basicOpen_eq_of_affine (R := .of k[X]) Polynomial.X

end AffineLineOrigin

open AffineLineOrigin ExposeV PreGaloisCategory

/-- XIII.2.12 for `g = 0`, `n = 2`, with the inertia condition at `0` (statement): for `k`
algebraically closed of characteristic `p`, `U = 𝔾_m = D(T) ⊆ X = 𝔸¹ = Spec k[T]` and a geometric
point `ξ` of `U`, some `σ ∈ π₁(U, ξ)` presents `π₁^{p'}(U, ξ)` as the pro-`p'` completion of `ℤ`
(`φ ↦ φ σ` is bijective on continuous homomorphisms to finite groups of order prime to `p`) and
generates the inertia groups at `0`: for every geometric point `x̄` of `𝔸¹` over the origin (the
point of `X - U`), inertia subgroups `H` of `π₁(U, ξ)` at `x̄` exist (`IsInertiaSubgroupAt`), and
each of them has the same image as `σ^ℤ` in `π₁^{p'}(U, ξ)`, written
`closure (H · proLKernel) = closure (σ^ℤ · proLKernel)` as in `TameCurvePrimeToPStatement`.
SGA states XIII.2.12 on `X = ℙ¹`, `U = ℙ¹ - {0, ∞}`; this is the condition at the point `0`, on
the chart `𝔸¹` (the strict localization at `0` only depends on a neighbourhood of `0`). The form on
`ℙ¹` with both points is `tameCurvePrimeToPConclusion_projectiveLine_two`. `k` is algebraically
closed (SGA: separably closed). -/
def MultiplicativeGroupInertiaStatement (p : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharP k p] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ (multiplicativeGroupOpen k : Scheme.{u})),
    ∃ σ : etaleFundamentalGroup Ω ξ,
      (∀ (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G],
        IsLGroup (primesDifferentFrom p) G →
        Function.Bijective fun φ : ContinuousMonoidHom (etaleFundamentalGroup Ω ξ) G ↦ φ σ) ∧
      ∀ (Ω₀ : Type u) [Field Ω₀] [IsSepClosed Ω₀] (xb : Spec (.of Ω₀) ⟶ Spec (.of (Polynomial k))),
        xb.imagePoint ∉ multiplicativeGroupOpen k →
        (∃ H, IsInertiaSubgroupAt (multiplicativeGroupOpen k) xb ξ H) ∧
        ∀ H, IsInertiaSubgroupAt (multiplicativeGroupOpen k) xb ξ H →
          (H ⊔ proLKernel (primesDifferentFrom p) (etaleFundamentalGroup Ω ξ)).topologicalClosure =
            (Subgroup.zpowers σ ⊔
              proLKernel (primesDifferentFrom p) (etaleFundamentalGroup Ω ξ)).topologicalClosure

/-- XIII.2.12 for `g = 0`, `n = 2`, with the inertia condition at `0`
(`MultiplicativeGroupInertiaStatement`). Both sides are all of `π₁(U, ξ)`: `σ` generates
`π₁^{p'}(U)` (`multiplicativeGroupPrimeToPStatement`), and an inertia subgroup at `0` maps onto
every finite quotient of `π₁^{p'}(U)` (`AffineLineChart.topologicalClosure_sup_proLKernel_eq_top`
for the chart `V = 𝔸¹`). -/
theorem multiplicativeGroupInertiaStatement (p : ℕ) :
    MultiplicativeGroupInertiaStatement.{u} p := by
  intro k _ _ _ Ω _ _ ξ
  have : ConnectedSpace (multiplicativeGroupOpen k : Scheme.{u}) :=
    Scheme.connectedSpace_of_iso (multiplicativeGroupOpenIso k)
  obtain ⟨σ, hσ⟩ := exists_bijective_eval_of_iso p k (multiplicativeGroupOpenIso k) Ω ξ
  have hne : ((multiplicativeGroupOpen k : (Spec (.of k[X])).Opens) :
      Set (Spec (.of k[X]))).Nonempty := by
    obtain ⟨x⟩ : Nonempty (multiplicativeGroupOpen k : Scheme.{u}) := inferInstance
    exact ⟨x.1, x.2⟩
  refine ⟨σ, hσ, fun Ω₀ _ _ xb hxb ↦
    ⟨exists_isInertiaSubgroupAt _ hne xb ξ, fun H hH ↦ ?_⟩⟩
  have hxo : xb.imagePoint = AffineLineChart.origin (isAffineOpen_top _) (sectionsEquiv k) :=
    AffineLineChart.eq_origin _ _ trivial (by rwa [basicOpen_sectionsEquiv_symm])
  rw [AffineLineChart.topologicalClosure_sup_proLKernel_eq_top p (isAffineOpen_top _)
    (sectionsEquiv k) (basicOpen_sectionsEquiv_symm k) hxo hH,
    topologicalClosure_zpowers_sup_proLKernel_eq_top hσ]

end SGA.SGA1.ExposeXIII
