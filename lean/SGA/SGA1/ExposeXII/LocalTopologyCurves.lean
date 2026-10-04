/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Dimension.FiniteType
import SGA.Foundations.Topology.ContractibleNhds
import SGA.SGA1.ExposeXII.LocalTopologyLPC

/-!
# SGA 1, Exposé XII, 5.2 for curves: `X(ℂ)` is locally contractible in dimension `≤ 1`

For `X` locally of finite type over `ℂ` of dimension `≤ 1` (a curve, possibly singular, possibly
with isolated points), `X(ℂ)` is strongly locally contractible
(`SchemePoints.stronglyLocallyContractibleSpace_of_topologicalKrullDim_le_one`): this is the
special case of `LocallyContractibleStatement` for curves. Consequently XII.5.2 holds for all
curves, conditionally only on the Riemann existence theorem XII.5.1
(`schemeFundamentalGroupComparison_of_topologicalKrullDim_le_one`). This is now a special case of
XII.5.2 for all `X`, conditional only on XII.5.1
(`schemeFundamentalGroupComparison_of_riemannExistence`, `LocalTopologySLSC.lean`, which uses the
weaker semilocal simple connectedness); the strong local contractibility proved here is more than
XII.5.2 needs.

The proof uses no triangulation. For `B` a domain of dimension `≤ 1`, a Noether normalization
`ℂ[z] ⊆ B` makes `X(ℂ) → ℂ` a branched covering (`Points.exists_branchedCover`) with finitely
many branch points. Near `x`, a neighbourhood `V` of `x` with `x` the only point over `π(x)` is a
finite covering of a punctured disc, and the radial contraction of the disc lifts to a contraction
of `V` onto `x` fixing `x` (`HasContractibleNhdsRel.of_isCoveringMapOn_ball`,
`BranchedCover.hasContractibleNhdsRel`). In general the irreducible components through `x` meet
only in finitely many points, so these contractions glue
(`HasContractibleNhdsRel.of_finite_isClosed_cover`).
-/

universe u

open Topology Set Filter Metric AlgebraicGeometry Polynomial

namespace SGA.SGA1.ExposeXII

/-! ### Branched coverings of the line -/

section Line

variable {E : Type*} [TopologicalSpace E]

/-- A nonzero polynomial in at most one variable has finitely many zeros. -/
lemma finite_setOf_eval_eq_zero_of_subsingleton {σ : Type*} [Subsingleton σ]
    {q : MvPolynomial σ ℂ} (hq : q ≠ 0) : {z : σ → ℂ | MvPolynomial.eval z q = 0}.Finite := by
  obtain ⟨a, ha⟩ : ∃ a : σ → ℂ, MvPolynomial.eval a q ≠ 0 := by
    by_contra! h
    exact hq (MvPolynomial.funext fun z ↦ by simpa using h z)
  refine ((finite_setOf_eval_line_eq_zero ha (fun _ ↦ 1)).image
    fun s : ℂ ↦ a + s • fun _ ↦ (1 : ℂ)).subset fun z hz ↦ ?_
  have hz' : z = a + (z - a) := by abel
  rcases isEmpty_or_nonempty σ with hσ | ⟨⟨i⟩⟩
  · exact ⟨0, by simpa [Subsingleton.elim z a] using hz, Subsingleton.elim _ _⟩
  · have hza : z - a = (z i - a i) • fun _ ↦ (1 : ℂ) := by
      funext j
      rw [Subsingleton.elim j i]
      simp
    refine ⟨z i - a i, ?_, ?_⟩
    · change MvPolynomial.eval (a + (z i - a i) • fun _ ↦ (1 : ℂ)) q = 0
      rw [← hza, ← hz']
      exact hz
    · change a + (z i - a i) • (fun _ ↦ (1 : ℂ)) = z
      rw [← hza, ← hz']

/-- A branched covering of `ℂˢ`, `s ≤ 1`, has at every point arbitrarily small open
neighbourhoods contracting onto that point: near `x`, a neighbourhood whose only point over
`π(x)` is `x` covers a punctured disc free of branch points, and contracts radially. -/
theorem BranchedCover.hasContractibleNhdsRel [T2Space E] (D : BranchedCover E)
    (hdim : D.dim ≤ 1) (x : E) : HasContractibleNhdsRel x := by
  have : Subsingleton (Fin D.dim) := Fin.subsingleton_iff_le_one.mpr hdim
  -- a punctured ball around `π x` avoids the branch locus
  obtain ⟨r, hr, hrZ⟩ := Metric.isOpen_iff.mp
    ((finite_setOf_eval_eq_zero_of_subsingleton D.disc_ne_zero).sdiff
      (t := {D.proj x})).isClosed.isOpen_compl (D.proj x) (fun h ↦ h.2 rfl)
  exact .of_isCoveringMapOn_ball D.isProperMap_proj hr
    (fun z hz ↦ D.isCoveringMapOn_proj z fun h0 ↦ hrZ hz.1 ⟨h0, hz.2⟩)
    (D.finite_proj_preimage _)

end Line


/-! ### Complex points of curves -/

namespace Points

/-- For `B` a domain of finite type over `ℂ` of dimension `≤ 1`, every point of `X(ℂ)`,
`X = Spec B`, has arbitrarily small open neighbourhoods contracting onto it. A Noether
normalization `ℂ[z₁, …, zₛ] ⊆ B` has `s = dim B ≤ 1`
(`Algebra.FiniteType.ringKrullDim_eq_of_isIntegral_mvPolynomial`). -/
theorem hasContractibleNhdsRel_of_isDomain (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] (hB : ringKrullDim B ≤ 1) (x : Points ℂ B) :
    HasContractibleNhdsRel x := by
  obtain ⟨D, g₀, hinj, hfin, -⟩ := exists_branchedCover B
  rw [Algebra.FiniteType.ringKrullDim_eq_of_isIntegral_mvPolynomial ℂ hinj
    (RingHom.IsIntegral.of_finite hfin)] at hB
  exact D.hasContractibleNhdsRel (by exact_mod_cast hB) x

/-- Two distinct irreducible components of `X = Spec A`, `A` of dimension `≤ 1`, have finitely
many common `ℂ`-points. -/
lemma finite_range_inter_range {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (hA : ringKrullDim A ≤ 1) {p q : Ideal A} (hp : p ∈ minimalPrimes A) (hq : q ∈ minimalPrimes A)
    (hpq : p ≠ q) :
    (range (Points.map (K := ℂ) (Ideal.Quotient.mkₐ ℂ p)) ∩
      range (Points.map (K := ℂ) (Ideal.Quotient.mkₐ ℂ q))).Finite := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hA' : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hA
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing A (p ⊔ q)).preimage
    ker_injective.injOn).subset fun φ ⟨hφp, hφq⟩ ↦ ?_
  rw [mem_range_map_quotient_iff] at hφp hφq
  have hker : (ker φ).IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨hker, sup_le hφp hφq⟩, fun P' hP' hle ↦ ?_⟩
  have := hP'.1
  -- `P'` strictly contains the minimal prime `p`, so it is maximal
  have hpP' : p < P' := by
    refine lt_of_le_of_ne (le_sup_left.trans hP'.2) fun h ↦ hpq ?_
    have hqp : q ≤ p := h ▸ le_sup_right.trans hP'.2
    exact le_antisymm (hp.2 ⟨hq.1.1, bot_le⟩ hqp) hqp
  have hmax : P'.IsMaximal := (Ring.krullDimLE_one_iff.mp hA' P' hP'.1).resolve_left
    fun hmin ↦ absurd (hmin.2 ⟨hp.1.1, bot_le⟩ hpP'.le) (not_le_of_gt hpP')
  exact (hmax.eq_of_le hker.ne_top hle).ge

/-- XII.5.2, topological input, curves: for `A` of finite type over `ℂ` of Krull dimension `≤ 1`,
the space `X(ℂ)`, `X = Spec A`, is strongly locally contractible. -/
theorem stronglyLocallyContractibleSpace_of_ringKrullDim_le_one (A : Type u) [CommRing A]
    [Algebra ℂ A] [Algebra.FiniteType ℂ A] (hA : ringKrullDim A ≤ 1) :
    StronglyLocallyContractibleSpace (Points ℂ A) := by
  -- reduce to `A` in `Type`
  obtain ⟨n, I, ⟨e⟩⟩ := exists_algEquiv_quotient A
  let A' := MvPolynomial (Fin n) ℂ ⧸ I
  have hA' : ringKrullDim A' ≤ 1 := (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).le.trans hA
  suffices StronglyLocallyContractibleSpace (Points ℂ A') from
    (Points.homeomorph e).isLocalHomeomorph.stronglyLocallyContractibleSpace
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing ℂ A'
  have : Finite (minimalPrimes A') := (minimalPrimes.finite_of_isNoetherianRing A').to_subtype
  -- the irreducible components through a point meet only in finitely many points
  let C : minimalPrimes A' → Set (Points ℂ A') := fun p ↦
    range (Points.map (Ideal.Quotient.mkₐ ℂ (p : Ideal A')))
  have hemb (p : minimalPrimes A') :
      IsClosedEmbedding (Points.map (K := ℂ) (Ideal.Quotient.mkₐ ℂ (p : Ideal A'))) :=
    isClosedEmbedding_map_of_surjective (Ideal.Quotient.mkₐ_surjective ℂ _)
  refine .of_forall_hasContractibleNhdsRel fun x ↦ ?_
  refine HasContractibleNhdsRel.of_finite_isClosed_cover (C := C)
    (fun p ↦ (hemb p).isClosed_range) (fun φ ↦ ?_) (fun p p' hpp' hxp hxp' ↦ ?_) fun p hp ↦ ?_
  · obtain ⟨p, hp, hφ⟩ := exists_mem_minimalPrimes_mem_range φ
    exact ⟨⟨p, hp⟩, hφ⟩
  · have hfin := finite_range_inter_range hA' p.2 p'.2 fun h ↦ hpp' (Subtype.ext h)
    filter_upwards [(hfin.sdiff (t := {x})).isClosed.isOpen_compl.mem_nhds
      fun h ↦ h.2 rfl] with y hy hyp hyp'
    by_contra hne
    exact hy ⟨⟨hyp, hyp'⟩, hne⟩
  · have : (p : Ideal A').IsPrime := p.2.1.1
    have hdim : ringKrullDim (A' ⧸ (p : Ideal A')) ≤ 1 :=
      (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective).trans hA'
    let h := (hemb p).isEmbedding.toHomeomorph
    have := (hasContractibleNhdsRel_of_isDomain (A' ⧸ (p : Ideal A')) hdim
      (h.symm ⟨x, hp⟩)).homeomorph h
    rwa [h.apply_symm_apply] at this

end Points

namespace SchemePoints

/-- XII.5.2, topological input, curves: for `X` locally of finite type over `ℂ` of dimension
`≤ 1`, the space `X(ℂ)` is strongly locally contractible (the case of curves of
`LocallyContractibleStatement`). -/
theorem stronglyLocallyContractibleSpace_of_topologicalKrullDim_le_one (X : Scheme.{0})
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    (hX : topologicalKrullDim X ≤ 1) : StronglyLocallyContractibleSpace (SchemePoints ℂ X) := by
  refine .of_isOpen_cover fun p ↦ ?_
  obtain ⟨A, _, _, _, f, hf, hp, hdim⟩ := exists_isOpenEmbedding_points X p
  have := Points.stronglyLocallyContractibleSpace_of_ringKrullDim_le_one A (hdim.trans hX)
  exact ⟨range f, hf.isOpen_range, hp,
    hf.isEmbedding.toHomeomorph.symm.isLocalHomeomorph.stronglyLocallyContractibleSpace⟩

end SchemePoints

/-- XII.5.2 for curves, singular or not: for `X` connected and locally of finite type over `ℂ`, of
dimension `≤ 1`, and `x ∈ X(ℂ)`, the Riemann existence theorem XII.5.1 implies that the étale
fundamental group `π₁(X, x)` is the profinite completion of `π₁(X(ℂ), x)`. -/
theorem schemeFundamentalGroupComparison_of_topologicalKrullDim_le_one
    (H : SchemeRiemannExistenceStatement) (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (hX : topologicalKrullDim X ≤ 1)
    (hc : ConnectedSpace X) (x : SchemePoints ℂ X) :
    Nonempty (ExposeV.etaleFundamentalGroup ℂ x.1 ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (FundamentalGroup (SchemePoints ℂ X) x))) :=
  have := SchemePoints.stronglyLocallyContractibleSpace_of_topologicalKrullDim_le_one X hX
  schemeFundamentalGroupComparison_of_semilocallySimplyConnectedSpace H X hc x

end SGA.SGA1.ExposeXII
