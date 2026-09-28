/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Topology.LocalAtTarget
import SGA.SGA1.ExposeXII.RootLocus
import SGA.SGA1.ExposeXII.PrimitiveElement
import SGA.SGA1.ExposeXII.ClosureComparison
import SGA.SGA1.ExposeXII.ProjectiveSpace
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Separation.Connected

/-!
# SGA 1, Exposé XII, 2.4 and 2.6: connectedness of `X(ℂ)`

**XII.2.4**: for `X` locally of finite type over `ℂ`, `X` is connected if and only if `X(ℂ)` is
(`SchemePoints.connectedComparison`, `SchemePoints.connectedSpace_iff'`; affine case
`Points.connectedComparison`). **XII.2.6**: `π₀(X(ℂ)) → π₀(X)` is bijective
(`SchemePoints.connectedComponentsComparison`).

SGA reduces XII.2.4 to normal projective varieties and uses Serre's GAGA connectedness theorem. We
avoid GAGA with the classical argument through Noether normalization:

* for `B` a domain of finite type over `ℂ` (`Points.preconnectedSpace_of_isDomain`), choose a
  Noether normalization `R = ℂ[z₁, …, zₙ] ⊆ B`, a primitive element `f ∈ B` with minimal polynomial
  `P ∈ R[T]` and `g ≠ 0` with `g • B ⊆ R[f]` (`exists_smul_mem_adjoin`), and `h ≠ 0` with
  `a P + b P' = h` (`exists_bezout_minpoly`). Over `{gh ≠ 0}`, `φ ↦ (π(φ), φ(f))` is a
  homeomorphism (proper, injective since `g • B ⊆ R[f]`, surjective by lying over) onto the root
  locus of `P`, which is connected (`RootLocus.isPreconnected_rootLocus`); and `{gh ≠ 0}` is dense
  in `X(ℂ)` (XII.2.2, `Points.dense_apply_ne_zero`);
* in general, the Zariski closures of a clopen subset of `X(ℂ)` and of its complement are disjoint
  (`Points.disjoint_closure_image_of_isClopen`,
  `SchemePoints.disjoint_closure_image_pt_of_isClopen`), each irreducible component having
  connected space of points.

XII.2.6 follows, a locally noetherian scheme being locally connected
(`locallyConnectedSpace_of_isLocallyNoetherian`): the connected component of `p` in `X(ℂ)` is
`C(ℂ)` for the connected component `C` of `p` in `X`
(`SchemePoints.connectedComponent_eq_preimage`); in particular the connected components of
`X(ℂ)` are open (`SchemePoints.isOpen_connectedComponent_points`).
-/

universe u

open Polynomial Topology Set

namespace SGA.SGA1.ExposeXII

namespace Points

open RootLocus

/-- XII.2.4, affine integral case: for `B` a domain of finite type over `ℂ`, the space `X(ℂ)` of
`X = Spec B` is preconnected. -/
theorem preconnectedSpace_of_isDomain (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] : PreconnectedSpace (Points ℂ B) := by
  classical
  obtain ⟨s, g₀, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ B
  let R := MvPolynomial (Fin s) ℂ
  let : Algebra R B := g₀.toRingHom.toAlgebra
  have : IsScalarTower ℂ R B := .of_algebraMap_eq fun c ↦ (g₀.commutes c).symm
  have : Module.Finite R B := hfin
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr hinj
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (FractionRing R)).injective
  obtain ⟨f, g, hg, hgf⟩ := exists_smul_mem_adjoin R B
  obtain ⟨a, b, h, hh, hab⟩ := exists_bezout_minpoly R B f
  have hint : IsIntegral R f := Algebra.IsIntegral.isIntegral f
  set P := minpoly R f with hPdef
  have hPm : P.Monic := minpoly.monic hint
  have hirr : Irreducible P := minpoly.irreducible hint
  set H := g * h with hHdef
  have hH : H ≠ 0 := mul_ne_zero hg hh
  have hsimple : ∀ z, MvPolynomial.eval z H ≠ 0 → ∀ t, (specAt P z).IsRoot t →
      (specAt P z).derivative.eval t ≠ 0 := by
    intro z hz t ht h0
    have := congrArg (fun p ↦ (p.map (MvPolynomial.eval z)).eval t) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, Polynomial.map_C,
      eval_C] at this
    rw [← derivative_map, h0, ht.eq_zero, mul_zero, mul_zero, add_zero] at this
    apply hz
    rw [hHdef, map_mul, ← this, mul_zero]
  have hSigma := isPreconnected_rootLocus hPm hsimple hirr hH
  -- the coordinates `X(ℂ) → ℂˢ`
  let π : Points ℂ B → (Fin s → ℂ) := fun φ i ↦ φ (algebraMap R B (MvPolynomial.X i))
  have hπc : Continuous π := continuous_pi fun i ↦ Points.continuous_apply _
  have hπeval (φ : Points ℂ B) (p : R) :
      MvPolynomial.eval (π φ) p = φ (algebraMap R B p) := by
    have : MvPolynomial.eval (π φ) = φ.toRingHom.comp (algebraMap R B) := by
      refine MvPolynomial.ringHom_ext (fun c ↦ ?_) fun i ↦ ?_
      swap
      · rw [MvPolynomial.eval_X]; rfl
      simp only [MvPolynomial.eval_C, RingHom.coe_comp, Function.comp_apply]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      exact (φ.apply_algebraMap c).symm
    exact congr($this p)
  have hPeval (φ : Points ℂ B) (q : R[X]) :
      (q.map (MvPolynomial.eval (π φ))).eval (φ f) = φ (aeval f q) := by
    rw [eval_map, aeval_def]
    change _ = φ.toRingHom (eval₂ (algebraMap R B) f q)
    rw [hom_eval₂]
    congr 1
    ext p
    · exact hπeval φ _
    · exact hπeval φ _
  -- the map `X_H(ℂ) → Σ`, `φ ↦ (π φ, φ f)`
  let W : Set (Fin s → ℂ) := {z | MvPolynomial.eval z H ≠ 0}
  let Xw : Set (Points ℂ B) := π ⁻¹' W
  have hroot (φ : Points ℂ B) : (specAt P (π φ)).IsRoot (φ f) := by
    rw [IsRoot, hPeval, hPdef, minpoly.aeval, map_zero]
  let e : Xw → rootLocus P H := fun φ ↦ ⟨(π φ.1, φ.1 f), φ.2, hroot φ.1⟩
  have hec : Continuous e :=
    ((hπc.comp continuous_subtype_val).prodMk
      ((Points.continuous_apply f).comp continuous_subtype_val)).subtype_mk _
  -- injectivity: `g • B ⊆ R[f]`
  have heinj : Function.Injective e := by
    rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ hφψ
    have h1 : π φ = π ψ := congrArg (fun x : rootLocus P H ↦ x.1.1) hφψ
    have h2 : φ f = ψ f := congrArg (fun x : rootLocus P H ↦ x.1.2) hφψ
    have hR (p : R) : φ (algebraMap R B p) = ψ (algebraMap R B p) := by
      rw [← hπeval, ← hπeval, h1]
    have hadj (y : B) (hy : y ∈ Algebra.adjoin R {f}) : φ y = ψ y := by
      induction hy using Algebra.adjoin_induction with
      | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact h2
      | algebraMap r => exact hR r
      | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
      | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]
    have hg0 : φ (algebraMap R B g) ≠ 0 := by
      rw [← hπeval]
      intro h0
      apply hφ
      change MvPolynomial.eval (π φ) (g * h) = 0
      rw [map_mul, h0, zero_mul]
    refine Subtype.ext (Points.ext fun y ↦ ?_)
    have := hadj _ (hgf y)
    rw [Algebra.smul_def, map_mul, map_mul, ← hR g] at this
    exact mul_left_cancel₀ hg0 this
  -- surjectivity: lying over for `R[T]/(P) → B`
  have hesurj : Function.Surjective e := by
    rintro ⟨⟨z, t⟩, hz, ht⟩
    let A' := AdjoinRoot P
    let ι : A' →ₐ[R] B := AdjoinRoot.liftAlgHom P (Algebra.ofId R B) f (minpoly.aeval R f)
    have hιof (r : R) : ι (AdjoinRoot.of P r) = algebraMap R B r :=
      AdjoinRoot.liftAlgHom_of _ _ _ _ r
    have hιmk (q : R[X]) : ι (AdjoinRoot.mk P q) = aeval f q :=
      AdjoinRoot.liftAlgHom_mk _ _ _ _ q
    have hιroot : ι (AdjoinRoot.root P) = f := AdjoinRoot.liftAlgHom_root _ _ _ _
    let : Algebra A' B := ι.toRingHom.toAlgebra
    have : IsScalarTower ℂ A' B := .of_algebraMap_eq fun c ↦ by
      change algebraMap ℂ B c = ι (AdjoinRoot.of P (algebraMap ℂ R c))
      rw [hιof, ← IsScalarTower.algebraMap_apply]
    have : IsScalarTower R A' B := .of_algebraMap_eq fun r ↦ by
      change algebraMap R B r = ι (AdjoinRoot.of P r)
      rw [hιof]
    have : Algebra.IsIntegral A' B := Algebra.IsIntegral.tower_top R
    have hιinj : Function.Injective (algebraMap A' B) := by
      refine (injective_iff_map_eq_zero _).mpr fun y hy ↦ ?_
      induction y using AdjoinRoot.induction_on with
      | ih q =>
        change ι (AdjoinRoot.mk P q) = 0 at hy
        rw [hιmk] at hy
        exact AdjoinRoot.mk_eq_zero.mpr (minpoly.isIntegrallyClosed_dvd hint hy)
    have hχ : P.eval₂ (MvPolynomial.eval z) t = 0 := by
      rw [← eval_map]; exact ht
    let χ₀ := AdjoinRoot.lift (MvPolynomial.eval z) t hχ
    let χ : Points ℂ A' := Points.ofAlgHom { χ₀ with
      commutes' := fun c ↦ by
        change χ₀ (AdjoinRoot.of P (algebraMap ℂ R c)) = c
        rw [AdjoinRoot.lift_of, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C] }
    have hmem : toPrimeSpectrum χ ∈ range (PrimeSpectrum.comap (algebraMap A' B)) := by
      obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (ker χ) ⊥
        (fun y hy ↦ by
          have : y = 0 := hιinj (by rw [map_zero]; exact hy)
          rw [this]; exact zero_mem _)
      exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQc⟩
    obtain ⟨ψ, hψ⟩ := exists_proj_eq_of_mem_range hmem
    have hψR (p : R) : ψ (algebraMap R B p) = MvPolynomial.eval z p := by
      rw [IsScalarTower.algebraMap_apply R A' B, ← proj_apply, hψ]
      change χ₀ (AdjoinRoot.of P p) = _
      rw [AdjoinRoot.lift_of]
    have hπψ : π ψ = z := funext fun i ↦ by
      change ψ (algebraMap R B (MvPolynomial.X i)) = z i
      rw [hψR, MvPolynomial.eval_X]
    have hψf : ψ f = t := by
      have : f = algebraMap A' B (AdjoinRoot.root P) := by
        change f = ι (AdjoinRoot.root P)
        rw [hιroot]
      rw [this, ← proj_apply, hψ]
      exact AdjoinRoot.lift_root (i := MvPolynomial.eval z) (h := hχ)
    refine ⟨⟨ψ, show π ψ ∈ W from hπψ ▸ hz⟩, ?_⟩
    exact Subtype.ext (Prod.ext hπψ hψf)
  -- properness of `π`, hence of `e`
  have hπproper : IsProperMap π := by
    have h1 : IsProperMap (proj R B : Points ℂ B → Points ℂ R) := isProperMap_proj_of_isIntegral
    have h2 : π = homeomorphMvPolynomial (Fin s) ∘ proj R B := rfl
    rw [h2]
    exact (homeomorphMvPolynomial (Fin s)).isProperMap.comp h1
  let pr : rootLocus P H → W := fun x ↦ ⟨x.1.1, x.2.1⟩
  have hprc : Continuous pr := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hcomp : pr ∘ e = W.restrictPreimage π := rfl
  have heproper : IsProperMap e :=
    isProperMap_of_comp_of_t2 hec hprc (hcomp ▸ hπproper.restrictPreimage W)
  let E : Xw ≃ₜ rootLocus P H :=
    (Equiv.ofBijective e ⟨heinj, hesurj⟩).toHomeomorphOfContinuousClosed hec heproper.isClosedMap
  have : PreconnectedSpace (rootLocus P H) := Subtype.preconnectedSpace hSigma
  have hXw : IsPreconnected Xw := by
    rw [isPreconnected_iff_preconnectedSpace, preconnectedSpace_iff_univ]
    have := isPreconnected_range E.symm.continuous
    rwa [E.symm.surjective.range_eq] at this
  -- density of `X_H(ℂ)` (XII.2.2)
  have hXwdense : Dense Xw := by
    have hne : algebraMap R B H ∈ nonZeroDivisors B :=
      mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ (show Function.Injective
        (algebraMap R B) from hinj)).mpr hH)
    have := dense_apply_ne_zero AffineAnalytification.rueckertNullstellensatz hne
    convert this using 1
    ext φ
    simp only [Xw, W, mem_preimage, mem_ofPred_eq, hπeval]
  rw [preconnectedSpace_iff_univ, ← hXwdense.closure_eq]
  exact hXw.closure

/-- XII.2.4, affine integral case, any universe. -/
theorem preconnectedSpace_of_isDomain' {A : Type*} [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] : PreconnectedSpace (Points ℂ A) := by
  obtain ⟨n, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let e := Ideal.quotientKerAlgEquivOfSurjective hq
  have : IsDomain (MvPolynomial (Fin n) ℂ ⧸ RingHom.ker q) :=
    Function.Injective.isDomain e.toRingEquiv.toRingHom e.injective
  have := preconnectedSpace_of_isDomain (MvPolynomial (Fin n) ℂ ⧸ RingHom.ker q)
  rw [preconnectedSpace_iff_univ, ← (Points.homeomorph e).symm.surjective.range_eq]
  exact isPreconnected_range (Points.homeomorph e).symm.continuous

variable {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

/-- XII.2.4, affine case, key step: for a clopen subset `U` of `X(ℂ)`, `X = Spec A`, the Zariski
closures of `U` and of its complement are disjoint. Every irreducible component `V(p)` of `X` has
connected space of points `V(p)(ℂ)`, which lies in `U` or in its complement. -/
theorem disjoint_closure_image_of_isClopen {U : Set (Points ℂ A)} (hU : IsClopen U) :
    Disjoint (closure (toPrimeSpectrum '' U)) (closure (toPrimeSpectrum '' Uᶜ)) := by
  classical
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  let C : Ideal A → Set (Points ℂ A) := fun p ↦ range (Points.map (Ideal.Quotient.mkₐ ℂ p))
  have hC (p : Ideal A) (hp : p.IsPrime) : IsPreconnected (C p) := by
    have : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
    have := preconnectedSpace_of_isDomain' (A := A ⧸ p)
    exact isPreconnected_range (Points.continuous_map _)
  have hmemC (p : Ideal A) (φ : Points ℂ A) : φ ∈ C p ↔ p ≤ ker φ := by
    change φ ∈ range (Points.map (Ideal.Quotient.mkₐ ℂ p)) ↔ _
    rw [range_map_of_surjective (Ideal.Quotient.mkₐ_surjective ℂ p)]
    simp only [mem_ofPred_eq, RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact ⟨fun h a ha ↦ mem_ker.mpr (h a ha), fun h a ha ↦ mem_ker.mp (h ha)⟩
  have hcover (φ : Points ℂ A) : ∃ p ∈ minimalPrimes A, φ ∈ C p := by
    obtain ⟨p, hp, hpφ⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ ker φ)
    exact ⟨p, hp, (hmemC p φ).mpr hpφ⟩
  -- the closed sets `S V = ⋃ {V(p) | V(p)(ℂ) ⊆ V}`
  let S : Set (Points ℂ A) → Set (PrimeSpectrum A) := fun V ↦
    ⋃ p ∈ {p ∈ minimalPrimes A | C p ⊆ V}, PrimeSpectrum.zeroLocus (p : Set A)
  have hSclosed (V : Set (Points ℂ A)) : IsClosed (S V) :=
    (hfin.subset fun p hp ↦ hp.1).isClosed_biUnion fun p _ ↦ PrimeSpectrum.isClosed_zeroLocus _
  have hsub (V : Set (Points ℂ A)) (hV : IsClopen V) : toPrimeSpectrum '' V ⊆ S V := by
    rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨p, hp, hφp⟩ := hcover φ
    refine mem_iUnion₂.mpr ⟨p, ⟨hp, (hC p hp.1.1).subset_isClopen hV ⟨φ, hφp, hφ⟩⟩, ?_⟩
    rw [PrimeSpectrum.mem_zeroLocus, toPrimeSpectrum_asIdeal]
    exact (hmemC p φ).mp hφp
  have hdisj : Disjoint (S U) (S Uᶜ) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨p, ⟨-, hpU⟩, hxp⟩ := mem_iUnion₂.mp hx
    obtain ⟨p', ⟨-, hpU'⟩, hxp'⟩ := mem_iUnion₂.mp hx'
    obtain ⟨m, hm, hxm⟩ := Ideal.exists_le_maximal x.asIdeal x.isPrime.ne_top
    obtain ⟨φ, hφ⟩ := exists_ker_eq (K := ℂ) m
    have h1 : φ ∈ C p := (hmemC p φ).mpr (hφ ▸ ((PrimeSpectrum.mem_zeroLocus _ _).mp hxp).trans hxm)
    have h2 : φ ∈ C p' :=
      (hmemC p' φ).mpr (hφ ▸ ((PrimeSpectrum.mem_zeroLocus _ _).mp hxp').trans hxm)
    exact hpU' h2 (hpU h1)
  exact hdisj.mono (closure_minimal (hsub U hU) (hSclosed U))
    (closure_minimal (hsub Uᶜ hU.compl) (hSclosed Uᶜ))

/-- XII.2.4, affine case: if `X = Spec A` is connected, so is `X(ℂ)`. -/
theorem connectedSpace_of_connectedSpace_primeSpectrum [ConnectedSpace (PrimeSpectrum A)] :
    ConnectedSpace (Points ℂ A) := by
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  have : Nonempty (Points ℂ A) := (nonempty_iff_nontrivial ℂ A).mpr inferInstance
  refine @ConnectedSpace.mk _ _ (preconnectedSpace_iff_clopen.mpr fun U hU ↦ ?_) this
  set F₁ := closure (toPrimeSpectrum '' U)
  set F₂ := closure (toPrimeSpectrum '' Uᶜ)
  have hdisj := disjoint_closure_image_of_isClopen hU
  have hunion : F₁ ∪ F₂ = univ := by
    rw [← closure_union, ← image_union, union_compl_self, image_univ]
    exact (denseRange_toPrimeSpectrum (K := ℂ)).closure_range
  have hcompl : F₁ᶜ = F₂ := IsCompl.compl_eq ⟨hdisj, codisjoint_iff.mpr hunion⟩
  have hF₁ : IsClopen F₁ := ⟨isClosed_closure, by
    rw [← isClosed_compl_iff, hcompl]; exact isClosed_closure⟩
  rcases isClopen_iff.mp hF₁ with h0 | h1
  · left
    have := subset_closure.trans h0.subset
    rwa [subset_empty_iff, image_eq_empty] at this
  · right
    have h2 : F₂ = ∅ := by rw [← hcompl, h1, compl_univ]
    have := (subset_closure (s := toPrimeSpectrum '' Uᶜ)).trans h2.subset
    rwa [subset_empty_iff, image_eq_empty, compl_empty_iff] at this

/-- XII.2.4, affine case (`Comparison.lean`): if `X = Spec A` is connected, so is `X(ℂ)`. -/
theorem connectedComparison : ConnectedComparisonStatement.{u} :=
  fun _ _ _ _ _ ↦ connectedSpace_of_connectedSpace_primeSpectrum

/-- XII.2.4, affine case: `X = Spec A` is connected if and only if `X(ℂ)` is. -/
theorem connectedSpace_iff' : ConnectedSpace (Points ℂ A) ↔ ConnectedSpace (PrimeSpectrum A) :=
  connectedSpace_iff connectedComparison

end Points

/-! ### Schemes -/

/-- A noetherian space has finitely many connected components. -/
theorem finite_connectedComponents_of_noetherianSpace (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] : Finite (ConnectedComponents X) := by
  obtain ⟨S, hS, _, hI, hcov⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_univ : IsClosed (univ : Set X))
  have hf : (⋃ t ∈ S, ConnectedComponents.mk '' t).Finite := hS.biUnion fun t ht ↦
    ((hI t ht).isConnected.isPreconnected.image _
      ConnectedComponents.continuous_coe.continuousOn).subsingleton.finite
  refine Finite.of_finite_univ (hf.subset fun c _ ↦ ?_)
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨t, ht, hxt⟩ : x ∈ ⋃₀ S := hcov ▸ mem_univ x
  exact mem_iUnion₂.mpr ⟨t, ht, x, hxt, rfl⟩

open AlgebraicGeometry in
/-- A locally noetherian scheme is locally connected. -/
theorem locallyConnectedSpace_of_isLocallyNoetherian (X : Scheme.{u}) [IsLocallyNoetherian X] :
    LocallyConnectedSpace X := by
  refine locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr fun x S hS ↦ ?_
  obtain ⟨O, hOS, hO, hxO⟩ := mem_nhds_iff.mp hS
  obtain ⟨V, hV, hxV, hVO⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨O, hO⟩) hxO
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : TopologicalSpace.NoetherianSpace (V : Set X) := noetherianSpace_of_isAffineOpen V hV
  have := finite_connectedComponents_of_noetherianSpace (V : Set X)
  let y : (V : Set X) := ⟨x, hxV⟩
  have hclopen : IsClopen (connectedComponent y) := by
    refine ⟨isClosed_connectedComponent, ?_⟩
    have hc : (connectedComponent y)ᶜ = ⋃ c ∈ ({ConnectedComponents.mk y}ᶜ :
        Set (ConnectedComponents (V : Set X))), ConnectedComponents.mk ⁻¹' {c} := by
      rw [Set.biUnion_preimage_singleton, preimage_compl, connectedComponents_preimage_singleton]
    rw [← isClosed_compl_iff, hc]
    refine (Set.toFinite _).isClosed_biUnion fun c _ ↦ ?_
    obtain ⟨w, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent
  refine ⟨Subtype.val '' connectedComponent y, ?_, ?_, ⟨y, mem_connectedComponent, rfl⟩,
    isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn⟩
  · rintro _ ⟨z, _, rfl⟩
    exact hOS (hVO z.2)
  · exact V.2.isOpenMap_subtype_val _ hclopen.isOpen

namespace SchemePoints

open AlgebraicGeometry CategoryTheory

attribute [local instance] sectionsAlgebra

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]

/-- XII.2.4, key step: for a clopen subset `U` of `X(ℂ)`, the Zariski closures of `U` and of its
complement in `X` are disjoint (local on `X`, by the affine case
`Points.disjoint_closure_image_of_isClopen`). -/
theorem disjoint_closure_image_pt_of_isClopen {U : Set (SchemePoints ℂ X)} (hU : IsClopen U) :
    Disjoint (closure (pt '' U)) (closure (pt '' Uᶜ)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (mem_univ x) isOpen_univ
  have hV : IsAffineOpen V := hV
  have : Algebra.FiniteType ℂ Γ(X, V) := finiteType_sections hV
  have hc := isOpenEmbedding_chart (K := ℂ) hV
  have hfs := hV.fromSpec.isOpenEmbedding
  have hpre (W : Set (SchemePoints ℂ X)) :
      hV.fromSpec ⁻¹' (pt '' W) = Points.toPrimeSpectrum '' (chart hV ⁻¹' W) := by
    ext y
    constructor
    · rintro ⟨p, hp, hpy⟩
      have hpV : p.pt ∈ V := by
        change p.pt ∈ (V : Set X)
        rw [hpy, ← hV.range_fromSpec]
        exact mem_range_self y
      obtain ⟨φ, rfl⟩ := exists_chart_eq hV p hpV
      refine ⟨φ, hp, hfs.injective ?_⟩
      rw [← pt_chart_eq, hpy]
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨chart hV φ, hφ, pt_chart_eq hV φ⟩
  obtain ⟨y, rfl⟩ : x ∈ range hV.fromSpec := by rw [hV.range_fromSpec]; exact hxV
  have hd := Points.disjoint_closure_image_of_isClopen (hU.preimage hc.continuous)
  have h1 : y ∈ closure (hV.fromSpec ⁻¹' (pt '' U)) := by
    rw [← hfs.isOpenMap.preimage_closure_eq_closure_preimage hfs.continuous]
    exact hx
  have h2 : y ∈ closure (hV.fromSpec ⁻¹' (pt '' Uᶜ)) := by
    rw [← hfs.isOpenMap.preimage_closure_eq_closure_preimage hfs.continuous]
    exact hx'
  rw [hpre] at h1 h2
  exact Set.disjoint_left.mp hd h1 h2

/-- **XII.2.4**: if `X`, locally of finite type over `ℂ`, is connected, then so is `X(ℂ)`. -/
theorem connectedComparison : ConnectedComparisonStatement := by
  intro X _ _ hX
  have : Nonempty (SchemePoints ℂ X) := nonempty_iff.mpr inferInstance
  refine @ConnectedSpace.mk _ _ (preconnectedSpace_iff_clopen.mpr fun U hU ↦ ?_) this
  set F₁ := closure (pt '' U)
  set F₂ := closure (pt '' Uᶜ)
  have hdisj := disjoint_closure_image_pt_of_isClopen hU
  have hunion : F₁ ∪ F₂ = univ := by
    rw [← closure_union, ← image_union, union_compl_self, image_univ]
    exact (denseRange_pt (K := ℂ)).closure_range
  have hcompl : F₁ᶜ = F₂ := IsCompl.compl_eq ⟨hdisj, codisjoint_iff.mpr hunion⟩
  have hF₁ : IsClopen F₁ := ⟨isClosed_closure, by
    rw [← isClosed_compl_iff, hcompl]; exact isClosed_closure⟩
  rcases isClopen_iff.mp hF₁ with h0 | h1
  · left
    have := subset_closure.trans h0.subset
    rwa [subset_empty_iff, image_eq_empty] at this
  · right
    have h2 : F₂ = ∅ := by rw [← hcompl, h1, compl_univ]
    have := (subset_closure (s := pt '' Uᶜ)).trans h2.subset
    rwa [subset_empty_iff, image_eq_empty, compl_empty_iff] at this

/-- XII.2.4: `X` is connected if and only if `X(ℂ)` is. -/
theorem connectedSpace_iff' (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] :
    ConnectedSpace (SchemePoints ℂ X) ↔ ConnectedSpace X :=
  connectedSpace_iff connectedComparison X

/-- For a connected component `C` of `X` (open: `X` is locally noetherian), `C(ℂ) ⊆ X(ℂ)` is
connected (XII.2.4 for the open subscheme `C`). -/
theorem isPreconnected_preimage_connectedComponent (x : X) :
    IsPreconnected (pt ⁻¹' connectedComponent x : Set (SchemePoints ℂ X)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  have := locallyConnectedSpace_of_isLocallyNoetherian X
  let V : X.Opens := ⟨connectedComponent x, isOpen_connectedComponent⟩
  let : V.toScheme.Over (Spec (.of ℂ)) := .ofHom (V.ι ≫ X ↘ Spec (.of ℂ))
  have : V.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (V.ι ≫ X ↘ Spec (.of ℂ))
    infer_instance
  have : ConnectedSpace V.toScheme := Subtype.connectedSpace isConnected_connectedComponent
  have := connectedComparison V.toScheme this
  have hrange : range (map (K := ℂ) V.ι) = pt ⁻¹' connectedComponent x := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      rw [mem_preimage, pt_map]
      have := mem_range_self (f := V.ι) q.pt
      rwa [Scheme.Opens.range_ι] at this
    · intro hp
      exact exists_map_eq_of_isOpenImmersion V.ι p (by rw [Scheme.Opens.range_ι]; exact hp)
  rw [← hrange]
  exact isPreconnected_range (continuous_map _)

/-- XII.2.6: the connected component of `p` in `X(ℂ)` is the set of `ℂ`-points of the connected
component of `p` in `X`. -/
theorem connectedComponent_eq_preimage (p : SchemePoints ℂ X) :
    connectedComponent p = pt ⁻¹' connectedComponent p.pt := by
  refine subset_antisymm (fun q hq ↦ ?_) ((isPreconnected_preimage_connectedComponent p.pt)
    |>.subset_connectedComponent mem_connectedComponent)
  exact (isPreconnected_connectedComponent.image _ continuous_pt.continuousOn)
    |>.subset_connectedComponent (mem_image_of_mem _ mem_connectedComponent)
      (mem_image_of_mem _ hq)

/-- XII.2.6: the connected components of `X(ℂ)` are open. -/
theorem isOpen_connectedComponent_points (p : SchemePoints ℂ X) :
    IsOpen (connectedComponent p) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  have := locallyConnectedSpace_of_isLocallyNoetherian X
  rw [connectedComponent_eq_preimage]
  exact isOpen_connectedComponent.preimage continuous_pt

/-- **XII.2.6**: the map `π₀(X(ℂ)) → π₀(X)` is bijective. -/
theorem connectedComponentsComparison : ConnectedComponentsComparisonStatement := by
  intro X _ _
  refine ⟨fun a b hab ↦ ?_, connectedComponentsMap_surjective⟩
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe a
  obtain ⟨q, rfl⟩ := ConnectedComponents.surjective_coe b
  rw [Continuous.connectedComponentsMap_mk, Continuous.connectedComponentsMap_mk,
    ConnectedComponents.coe_eq_coe'] at hab
  rw [ConnectedComponents.coe_eq_coe', connectedComponent_eq_preimage]
  exact hab

end SchemePoints

end SGA.SGA1.ExposeXII
