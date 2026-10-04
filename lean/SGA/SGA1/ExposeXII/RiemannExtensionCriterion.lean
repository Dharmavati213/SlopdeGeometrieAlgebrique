/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannExtensionTopology
import SGA.SGA1.ExposeXII.RiemannExtensionAlgebra
import SGA.SGA1.ExposeXII.RiemannCurvesSeparable

/-!
# SGA 1, Exposé XII, 5.1 for curves: the extension criterion

Let `X = Spec B` be an integral affine curve over `ℂ` (`B` a domain of finite type whose nonzero
primes are maximal), `h ∈ B` nonzero with finitely many zeros in `X(ℂ)`, at each of which `X(ℂ)`
has connected punctured neighbourhoods, and `E` a finite covering of `X(ℂ)`. Let `C` be a finite
flat `B`-algebra, unramified over `{h ≠ 0}`, such that `Y(ℂ)`, `Y = Spec C`, has connected punctured
neighbourhoods at the points over `{h = 0}`. If `E` and `Y(ℂ)` agree over `Ω = {h ≠ 0}` (two open
embeddings `Γ : W → E` and `r : W → Y(ℂ)` onto the parts over `Ω`, compatible with the
projections), then `C` is étale over `B` and `E ≅ Y(ℂ)` over `X(ℂ)`
(`RiemannExtension.etale_and_mem_essImage`).

Proof: the identification over `Ω` extends to a continuous injective map `Φ : E → Y(ℂ)` over
`X(ℂ)` (`exists_continuous_extension`, `injective_of_extension`); the fibres of `E` all have
`n = rank_B C` points (locally constant cardinality, `n` over `Ω` by
`Points.card_fiber_eq_finrank`), so `Y(ℂ)` has at least `n` points over each zero of `h` and `C`
is étale (`Points.etale_of_forall_card_fiber`); then both fibres have `n` points everywhere and
`Φ` is bijective, hence an isomorphism of coverings (`TopCat.FiniteCovering.isoOfBijective`).

Also `mem_essImage_pointsFunctor_of_bijective` (a finite covering with a continuous bijection over
`X(ℂ)` onto `C(ℂ)`, `C` finite étale, is `Ψ(C)`) and `IsCoveringMap.eventually_card_fiber_eq`
(the cardinality of the fibres of a covering map is locally constant). This route is this
project's; see `SGA.SGA1.ExposeXII.RiemannExtension` for its use.
-/

noncomputable section

open CategoryTheory Topology Set Filter Module

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- The cardinality of the fibres of a covering map is locally constant. -/
theorem eventually_card_fiber_eq (hp : IsCoveringMap p) (x : X) :
    ∀ᶠ x' in 𝓝 x, Nat.card (p ⁻¹' {x'}) = Nat.card (p ⁻¹' {x}) := by
  obtain ⟨-, U, hxU, hU, -, H, hH⟩ := hp x
  have key (z : X) (hz : z ∈ U) : Nat.card (p ⁻¹' {z}) = Nat.card (p ⁻¹' {x}) := by
    have hmem (f : p ⁻¹' {z}) : f.1 ∈ p ⁻¹' U := by
      change p f.1 ∈ U
      rw [show p f.1 = z from f.2]
      exact hz
    refine Nat.card_congr
      { toFun f := (H ⟨f.1, hmem f⟩).2
        invFun i := ⟨H.symm (⟨z, hz⟩, i), by
          change p _ = z
          rw [← hH, Homeomorph.apply_symm_apply]⟩
        left_inv f := Subtype.ext ?_
        right_inv i := ?_ }
    · have h1 : (H ⟨f.1, hmem f⟩).1 = ⟨z, hz⟩ := Subtype.ext (by rw [hH]; exact f.2)
      change ((H.symm (⟨z, hz⟩, (H ⟨f.1, hmem f⟩).2) : p ⁻¹' U) : E) = f.1
      rw [← h1, Prod.mk.eta, Homeomorph.symm_apply_apply]
    · change (H ⟨(H.symm (⟨z, hz⟩, i) : E), _⟩).2 = i
      rw [Subtype.coe_eta, Homeomorph.apply_symm_apply]
  filter_upwards [hU.mem_nhds hxU] with x' hx' using key x' hx'

end IsCoveringMap

namespace SGA.SGA1.ExposeXII

namespace RiemannExtension

section Topology

variable {E X Y W : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace W] {p : E → X} {q : Y → X} {Ω : Set X}

omit [TopologicalSpace X] in
/-- Two open embeddings `Γ : W → E`, `r : W → Y` over `X` onto the parts over `Ω` give a map
`Φ₀ : E → Y` which is, on `p⁻¹(Ω)`, a continuous open embedding over `X` onto `q⁻¹(Ω)`. -/
theorem exists_of_isOpenEmbedding [Nonempty W] {Γ : W → E} {r : W → Y} (hΓ : IsOpenEmbedding Γ)
    (hr : IsOpenEmbedding r) (hpq : ∀ w, p (Γ w) = q (r w)) (hΓrange : range Γ = p ⁻¹' Ω)
    (hrrange : range r = q ⁻¹' Ω) :
    ∃ Φ₀ : E → Y, ContinuousOn Φ₀ (p ⁻¹' Ω) ∧ (∀ e, p e ∈ Ω → q (Φ₀ e) = p e) ∧
      IsOpenEmbedding ((p ⁻¹' Ω).domRestrict Φ₀) ∧ q ⁻¹' Ω ⊆ Φ₀ '' (p ⁻¹' Ω) := by
  classical
  set Φ₀ : E → Y := Function.extend Γ r fun _ ↦ r (Classical.arbitrary W)
  have hΦΓ (w : W) : Φ₀ (Γ w) = r w := hΓ.injective.extend_apply _ _ w
  let H : W ≃ₜ p ⁻¹' Ω := hΓ.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hΓrange)
  have hH (w : W) : (H w : E) = Γ w := rfl
  have hres : (p ⁻¹' Ω).domRestrict Φ₀ = r ∘ H.symm := by
    funext e
    obtain ⟨w, rfl⟩ := H.surjective e
    rw [Set.domRestrict_apply, hH, hΦΓ, Function.comp_apply, Homeomorph.symm_apply_apply]
  have hemb : IsOpenEmbedding ((p ⁻¹' Ω).domRestrict Φ₀) := by
    rw [hres]
    exact hr.comp H.symm.isOpenEmbedding
  refine ⟨Φ₀, ?_, fun e he ↦ ?_, hemb, fun y hy ↦ ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    exact hemb.continuous
  · obtain ⟨w, hw⟩ : e ∈ range Γ := hΓrange ▸ he
    rw [← hw, hΦΓ, hpq]
  · obtain ⟨w, rfl⟩ : y ∈ range r := hrrange ▸ hy
    refine ⟨Γ w, ?_, hΦΓ w⟩
    rw [← hΓrange]
    exact mem_range_self w

end Topology

section Points

open CommAlgCat Opposite

/-- A finite covering `E` of `X(ℂ)`, `X = Spec B`, with a continuous bijection `Φ : E → C(ℂ)` over
`X(ℂ)`, where `C` is a finite étale `B`-algebra, is isomorphic to `Ψ(C) = C(ℂ)`. -/
theorem mem_essImage_pointsFunctor_of_bijective {B C : Type} [CommRing B] [Algebra ℂ B]
    [CommRing C] [Algebra ℂ C] [Algebra B C] [IsScalarTower ℂ B C] [Algebra.Etale B C]
    [Module.Finite B C] (E : TopCat.FiniteCovering (TopCat.of (Points ℂ B)))
    {Φ : E.obj.left → Points ℂ C} (hΦ : Continuous Φ)
    (hΦq : ∀ e, Points.proj B C (Φ e) = E.obj.hom e) (hb : Function.Bijective Φ) :
    (pointsFunctor ℂ B).essImage E := by
  obtain rfl : ‹Algebra ℂ C› = algebraOfFiniteEtale ℂ B (FiniteEtale.of B C) :=
    Algebra.algebra_ext _ _ fun c ↦ IsScalarTower.algebraMap_apply ℂ B C c
  exact ⟨op (FiniteEtale.of B C), ⟨(TopCat.FiniteCovering.isoOfBijective
    (E₂ := (pointsFunctor ℂ B).obj (op (FiniteEtale.of B C))) ⟨Φ, hΦ⟩ hΦq hb).symm⟩⟩

end Points

section Criterion

variable {B : Type} [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
  {C : Type} [CommRing C] [Algebra ℂ C] [Algebra B C] [IsScalarTower ℂ B C] [Module.Finite B C]
  [Module.Flat B C]

/-- **The extension criterion** (XII.5.1 for curves, extension across finitely many points; this
project's route). Let `B` be a domain of finite type over `ℂ` whose nonzero primes are maximal,
`h ≠ 0` in `B` with finitely many zeros in `X(ℂ)`, at each of which `X(ℂ)` has connected
punctured neighbourhoods, and `E` a nonempty finite covering of `X(ℂ)`. Let `C` be a finite flat
`B`-algebra with `C[1/h]` unramified over `B`, such that `Y(ℂ)`, `Y = Spec C`, has connected
punctured neighbourhoods at the points where `h` vanishes. Suppose given open embeddings
`Γ : W → E` and `r : W → Y(ℂ)` compatible with the projections to `X(ℂ)`, with images the parts
of `E` and of `Y(ℂ)` over `{h ≠ 0}`. Then `C` is étale over `B`, and `E ≅ Y(ℂ) = Ψ(C)`. -/
theorem etale_and_mem_essImage (hmax : ∀ P : Ideal B, P.IsPrime → P ≠ ⊥ → P.IsMaximal)
    {h : B} (hh : h ≠ 0) (hZ : {φ : Points ℂ B | φ h = 0}.Finite)
    (hpunctB : ∀ φ : Points ℂ B, φ h = 0 → HasConnectedPuncturedNhds φ)
    (hunr : Algebra.FormallyUnramified B (Localization.Away (algebraMap B C h)))
    (hpunctC : ∀ ψ : Points ℂ C, ψ (algebraMap B C h) = 0 → HasConnectedPuncturedNhds ψ)
    (E : TopCat.FiniteCovering (TopCat.of (Points ℂ B))) [Nonempty E.obj.left]
    {W : Type*} [TopologicalSpace W] {Γ : W → E.obj.left} {r : W → Points ℂ C}
    (hΓ : IsOpenEmbedding Γ) (hr : IsOpenEmbedding r)
    (hΓr : ∀ w, E.obj.hom (Γ w) = Points.proj B C (r w))
    (hΓrange : range Γ = E.obj.hom ⁻¹' {φ | φ h ≠ 0})
    (hrrange : range r = {ψ | ψ (algebraMap B C h) ≠ 0}) :
    Algebra.Etale B C ∧ (pointsFunctor ℂ B).essImage E := by
  classical
  set p : E.obj.left → Points ℂ B := ⇑E.obj.hom
  set q : Points ℂ C → Points ℂ B := Points.proj B C
  set Ω : Set (Points ℂ B) := {φ | φ h ≠ 0}
  have hqΩ : q ⁻¹' Ω = {ψ | ψ (algebraMap B C h) ≠ 0} := rfl
  have hp : IsCoveringMap p := E.isCoveringMap
  have hpfin : ∀ x, (p ⁻¹' {x}).Finite := E.property.2
  have hΩ : IsOpen Ω := isOpen_compl_singleton.preimage (Points.continuous_apply h)
  have hpunct : ∀ x ∉ Ω, HasConnectedPuncturedNhds x := fun x hx ↦ hpunctB x (not_not.mp hx)
  have hiso : ∀ x ∉ Ω, ∃ N ∈ 𝓝 x, N \ {x} ⊆ Ω := by
    intro x _
    refine ⟨({φ : Points ℂ B | φ h = 0} \ {x})ᶜ,
      (hZ.sdiff).isClosed.isOpen_compl.mem_nhds fun hx ↦ hx.2 rfl, ?_⟩
    rintro y ⟨hy, hyx⟩ hyΩ
    exact hy ⟨hyΩ, hyx⟩
  have hqfin : ∀ x, (q ⁻¹' {x}).Finite := fun x ↦ Points.finite_proj_preimage_of_finite x
  have hq : IsClosedMap q := (Points.isProperMap_proj_of_isIntegral).isClosedMap
  have hqc : Continuous q := Points.continuous_map _
  have hYpunct : ∀ y, q y ∉ Ω → HasConnectedPuncturedNhds y := fun y hy ↦
    hpunctC y (not_not.mp hy)
  -- `W` is nonempty: points over `Ω` accumulate at every point of `E`
  have hW : Nonempty W := by
    obtain ⟨e⟩ := ‹Nonempty E.obj.left›
    have : ∃ e', p e' ∈ Ω := by
      by_cases he : p e ∈ Ω
      · exact ⟨e, he⟩
      · obtain ⟨N, hN, hNΩ⟩ := hiso (p e) he
        obtain ⟨N', hN', hN'Ω⟩ := exists_mem_nhds_diff_subset hp hN hNΩ
        have := (hasConnectedPuncturedNhds_of_isCoveringMap hp (hpunct (p e) he)).neBot
        obtain ⟨e', he'⟩ := Filter.nonempty_of_mem (sdiff_mem_nhdsWithin_compl hN' {e})
        exact ⟨e', hN'Ω he'⟩
    obtain ⟨e', he'⟩ := this
    obtain ⟨w, -⟩ : e' ∈ range Γ := hΓrange ▸ he'
    exact ⟨w⟩
  obtain ⟨Φ₀, hΦ₀c, hΦ₀q, hΦ₀emb, hΦ₀range⟩ :=
    exists_of_isOpenEmbedding (p := p) (q := q) (Ω := Ω) hΓ hr hΓr hΓrange hrrange
  obtain ⟨Φ, hΦc, hΦq, hΦeq⟩ := exists_continuous_extension hp hq hΩ hpunct hiso
    (fun x _ ↦ hqfin x) hΦ₀c hΦ₀q
  have hres : (p ⁻¹' Ω).domRestrict Φ = (p ⁻¹' Ω).domRestrict Φ₀ := by
    funext e
    exact hΦeq e.1 e.2
  have hrange' : q ⁻¹' Ω ⊆ Φ '' (p ⁻¹' Ω) := by
    have : Φ '' (p ⁻¹' Ω) = Φ₀ '' (p ⁻¹' Ω) := image_congr fun e he ↦ hΦeq e he
    rw [this]
    exact hΦ₀range
  have hinj : Function.Injective Φ := injective_of_extension hp hpfin hqc hpunct hiso
    (fun x _ ↦ hqfin x) hΦc hΦq (hres ▸ hΦ₀emb) hrange' hYpunct
  -- the map induced by `Φ` on fibres
  let fib (x : Points ℂ B) : p ⁻¹' {x} → {ψ : Points ℂ C // q ψ = x} := fun e ↦
    ⟨Φ e.1, by rw [hΦq]; exact e.2⟩
  have hfibinj (x : Points ℂ B) : Function.Injective (fib x) := fun e₁ e₂ he ↦
    Subtype.ext (hinj (congrArg Subtype.val he))
  have hfinC (x : Points ℂ B) : Finite {ψ : Points ℂ C // q ψ = x} := (hqfin x).to_subtype
  -- over `Ω`, the fibres of `E` have `n = rank_B C` points
  have hcardΩ (x : Points ℂ B) (hx : x ∈ Ω) : Nat.card (p ⁻¹' {x}) = finrank B C := by
    have hsurj : Function.Surjective (fib x) := by
      rintro ⟨ψ, hψ⟩
      obtain ⟨e, -, rfl⟩ := hrange' (show q ψ ∈ Ω by rw [hψ]; exact hx)
      exact ⟨⟨e, by rw [mem_preimage, mem_singleton_iff, ← hΦq]; exact hψ⟩, rfl⟩
    rw [Nat.card_congr (Equiv.ofBijective _ ⟨hfibinj x, hsurj⟩)]
    refine Points.card_fiber_eq_finrank x fun Q _ _ ↦ ?_
    have hQ : algebraMap B C h ∉ Q := fun hQ ↦ hx (by
      have : h ∈ Q.comap (algebraMap B C) := hQ
      rw [← Ideal.under_def, ← Ideal.over_def Q (Points.ker x)] at this
      exact Points.mem_ker.mp this)
    exact (Algebra.basicOpen_subset_unramifiedLocus_iff.mpr hunr)
      (show (⟨Q, ‹_›⟩ : PrimeSpectrum C) ∈ PrimeSpectrum.basicOpen (algebraMap B C h) from hQ)
  -- by local constancy, all fibres of `E` have `n` points
  have hcard (x : Points ℂ B) : Nat.card (p ⁻¹' {x}) = finrank B C := by
    by_cases hx : x ∈ Ω
    · exact hcardΩ x hx
    obtain ⟨N, hN, hNΩ⟩ := hiso x hx
    have := (hpunct x hx).neBot
    obtain ⟨x', ⟨hx'1, hx'N⟩, hx'x⟩ := Filter.nonempty_of_mem
      (sdiff_mem_nhdsWithin_compl (inter_mem (hp.eventually_card_fiber_eq x) hN) {x})
    rw [← hx'1, hcardΩ x' (hNΩ ⟨hx'N, hx'x⟩)]
  -- hence `Y(ℂ)` has at least `n` points over each zero of `h`, and `C` is étale
  have hEt : Algebra.Etale B C := by
    refine Points.etale_of_forall_card_fiber hmax hh hunr fun x _ ↦ ?_
    rw [← hcard x]
    exact Nat.card_le_card_of_injective _ (hfibinj x)
  refine ⟨hEt, ?_⟩
  -- `Φ` is bijective, fibre by fibre
  have hsurj : Function.Surjective Φ := by
    intro ψ
    have hb := (hfibinj (q ψ)).bijective_of_nat_card_le (by
      rw [hcard, Points.card_fiber_eq_finrank]
      intro Q _ _
      have hU : Algebra.unramifiedLocus B C = univ :=
        Algebra.unramifiedLocus_eq_univ_iff.mpr inferInstance
      exact (hU.symm ▸ mem_univ (⟨Q, ‹_›⟩ : PrimeSpectrum C) :
        (⟨Q, ‹_›⟩ : PrimeSpectrum C) ∈ Algebra.unramifiedLocus B C))
    obtain ⟨e, he⟩ := hb.2 ⟨ψ, rfl⟩
    exact ⟨e.1, congrArg Subtype.val he⟩
  exact mem_essImage_pointsFunctor_of_bijective E hΦc hΦq ⟨hinj, hsurj⟩

end Criterion

end RiemannExtension

end SGA.SGA1.ExposeXII
