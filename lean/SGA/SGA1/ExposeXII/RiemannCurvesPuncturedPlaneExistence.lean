/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannCurvesPuncturedPlane
import SGA.SGA1.ExposeXII.RiemannCurvesSeparable
import SGA.SGA1.ExposeXII.RiemannLocalChart
import SGA.SGA1.ExposeXII.RiemannReduction
import SGA.SGA1.ExposeXII.RiemannReductionFiniteEtale
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# SGA 1, Exposé XII, 5.1 for `ℂ ∖ S`, from separating functions

Let `S ⊂ ℂ` be finite and `A = ℂ[t][1/f_S]` (`PuncturedPlane.coordRing S`), so that
`X = Spec A` has `X(ℂ) = ℂ ∖ S`. Assuming the analytic input `FiberSeparatingFunctionStatement`
(on a connected finite covering of `ℂ ∖ S`, every fibre is separated by a holomorphic function
of moderate growth), the Riemann existence theorem holds for `X`
(`PuncturedPlane.isEquivalence_pointsFunctor_coordRing`).

Proof (this project's route, not SGA's; see `SGA.SGA1.ExposeXII.RiemannCurves`). Let `E` be a
connected finite covering of `X(ℂ)`. For every `z ∈ ℂ ∖ S` let `F_z` separate the fibre over `z`,
and `P_z ∈ A[T]` be its fibrewise characteristic polynomial, monic
(`exists_monic_map_evalAt_eq_fiberCharpoly`).

* The resultant `δ_z = Res(P_z, P_z') ∈ A` does not vanish at `z`, because `P_z(z)` has the
  distinct roots `F_z(e)`, `e` over `z` (`PuncturedPlane.map_resultant_ne_zero`).
* Every point of `X` lies in some `D(δ_z)`: every prime lies in a maximal ideal, the kernel of a
  `ℂ`-point (Nullstellensatz). So the affine opens contained in some `D(δ_z)` form a basis of `X`
  (`PuncturedPlane.basis`).
* On such an open `U`, `P_z` is separable, since `δ_z` is invertible on `U`
  (`PuncturedPlane.separable_map_of_isUnit`), so `E|_U` is the covering cut out by `P_z`, i.e.
  `Γ(U)[T]/(P_z)(ℂ)` (`SeparableCovering.mem_essImage_pointsFunctor`).
* These local models glue (`RiemannLocal.mem_essImage_schemePointsFunctor`), and `Ψ` is an
  equivalence since every finite covering is a sum of connected ones
  (`isEquivalence_schemePointsFunctor_of_forall_isConnected`).

Consequently (`PuncturedPlane.isEquivalence_pointsFunctor_finiteEtale`) XII.5.1 holds, under the
same hypothesis, for every finite étale covering of `ℂ ∖ S`.

The hypothesis is proved (`fiberSeparatingFunction`, `SGA.SGA1.ExposeXII.GAGAFiberSeparating`);
the unconditional forms are `PuncturedPlane.riemannExistence_coordRing` and
`PuncturedPlane.riemannExistence_finiteEtale` there.
-/

noncomputable section

open CategoryTheory Topology Set Polynomial AlgebraicGeometry Opposite

namespace SGA.SGA1.ExposeXII

namespace PuncturedPlane

section Resultant

variable {A R : Type*} [CommRing A] [CommRing R]

/-- If the resultant of `f` and `g`, computed with degree bounds `m ≥ deg f` and `n ≥ deg g`
(not both `0`), is a unit, then `f` and `g` generate the unit ideal. -/
lemma isCoprime_of_isUnit_resultant {f g : R[X]} {m n : ℕ} (hf : f.natDegree ≤ m)
    (hg : g.natDegree ≤ n) (H : m ≠ 0 ∨ n ≠ 0) (hu : IsUnit (resultant f g m n)) :
    IsCoprime f g := by
  obtain ⟨p, q, -, -, e⟩ := exists_mul_add_mul_eq_C_resultant f g hf hg H
  exact ⟨C (hu.unit⁻¹).1 * p, C (hu.unit⁻¹).1 * q, by simp only [mul_assoc, ← mul_add, mul_comm p,
    mul_comm q, e, ← map_mul, IsUnit.val_inv_mul, map_one]⟩

/-- A monic `P` becomes separable along any ring map `φ` making `Res(P, P')` invertible. -/
lemma separable_map_of_isUnit {P : A[X]} (hP : P.Monic) (φ : A →+* R)
    (hu : IsUnit (φ (resultant P (derivative P)))) : (P.map φ).Separable := by
  by_cases hd : P.natDegree = 0
  · rw [eq_one_of_monic_natDegree_zero hP hd, Polynomial.map_one]
    exact separable_one
  rw [← resultant_map_map] at hu
  rw [Polynomial.Separable, derivative_map]
  exact isCoprime_of_isUnit_resultant natDegree_map_le natDegree_map_le (Or.inl hd) hu

/-- `Res(P, P')` does not vanish at a point `φ` where the monic `P` specialises to a separable
polynomial. -/
lemma map_resultant_ne_zero {P : A[X]} (hP : P.Monic) (φ : A →+* ℂ) (hs : (P.map φ).Separable) :
    φ (resultant P (derivative P)) ≠ 0 := by
  rw [← resultant_map_map, ← derivative_map]
  have h1 : (P.map φ).natDegree = P.natDegree := hP.natDegree_map φ
  have h2 : (derivative (P.map φ)).natDegree = (derivative P).natDegree := by
    apply le_antisymm
    · rw [derivative_map]
      exact natDegree_map_le
    · rw [natDegree_derivative (P.map φ), h1]
      exact natDegree_derivative_le P
  rw [← h2, ← h1]
  exact ((isUnit_resultant_iff_isCoprime (hP.map φ)).mpr hs).ne_zero

end Resultant

attribute [local instance] SchemePoints.specOver SchemePoints.sectionsAlgebra

section Spec

variable (S : Finset ℂ)

/-- `(Spec ℂ[t][1/f_S])(ℂ) = ℂ ∖ S`. -/
def schemeHomeomorph : SchemePoints ℂ (Spec (.of (coordRing S))) ≃ₜ {z : ℂ // z ∉ S} :=
  (specHomeomorph (coordRing S)).symm.trans (homeomorph S)

variable {S}

/-- The restriction `ℂ[t][1/f_S] = Γ(Spec, ⊤) → Γ(Spec, U)`. -/
def restrict (U : (Spec (.of (coordRing S))).Opens) :
    coordRing S →ₐ[ℂ] Γ(Spec (.of (coordRing S)), U) :=
  (SchemePoints.resAlgHom (le_top : U ≤ ⊤)).comp
    (SchemePoints.ΓSpecAlgEquiv (K := ℂ) (coordRing S)).symm.toAlgHom

lemma ΓSpecAlgEquiv_symm_apply (a : coordRing S) :
    (SchemePoints.ΓSpecAlgEquiv (K := ℂ) (coordRing S)).symm a =
      (Scheme.ΓSpecIso (.of (coordRing S))).inv a := by
  apply (SchemePoints.ΓSpecAlgEquiv (K := ℂ) (coordRing S)).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of (coordRing S))) a).symm

lemma restrict_apply (U : (Spec (.of (coordRing S))).Opens) (a : coordRing S) :
    restrict U a = (Spec (.of (coordRing S))).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso (.of (coordRing S))).inv a) := by
  rw [← ΓSpecAlgEquiv_symm_apply]
  rfl

lemma restrict_comp_ΓSpecAlgHom (U : (Spec (.of (coordRing S))).Opens) :
    (restrict U).comp (SchemePoints.ΓSpecAlgHom (K := ℂ) (coordRing S)) =
      SchemePoints.resAlgHom (le_top : U ≤ ⊤) := by
  ext g
  change SchemePoints.resAlgHom (K := ℂ) _ ((SchemePoints.ΓSpecAlgEquiv (K := ℂ) (coordRing S)).symm
    (SchemePoints.ΓSpecAlgEquiv (K := ℂ) (coordRing S) g)) = _
  rw [AlgEquiv.symm_apply_apply]

/-- A `ℂ`-point of an affine open `U` of `Spec ℂ[t][1/f_S]`, as a point of `ℂ[t][1/f_S]`, is its
composition with the restriction. -/
lemma specHomeomorph_map_restrict {U : (Spec (.of (coordRing S))).Opens} (hU : IsAffineOpen U)
    (ψ : Points ℂ Γ(Spec (.of (coordRing S)), U)) :
    specHomeomorph (coordRing S) (Points.map (restrict U) ψ) = SchemePoints.chart hU ψ := by
  rw [SchemePoints.specPointHomeomorph_apply (K := ℂ), SchemePoints.specPoint_eq_chart,
    ← Function.comp_apply (f := Points.map _), ← Points.map_comp, restrict_comp_ΓSpecAlgHom]
  exact SchemePoints.chart_map (isAffineOpen_top _) hU le_top ψ

/-- A function invertible on `D(g)` is invertible on every open `U ⊆ D(g)`. -/
lemma isUnit_restrict {U : (Spec (.of (coordRing S))).Opens} {a : coordRing S}
    (hU : U ≤ (Spec (.of (coordRing S))).basicOpen ((Scheme.ΓSpecIso (.of (coordRing S))).inv a)) :
    IsUnit (restrict U a) := by
  rw [restrict_apply]
  have h := ((Spec (.of (coordRing S))).toRingedSpace.isUnit_res_basicOpen
    ((Scheme.ΓSpecIso (.of (coordRing S))).inv a)).map
    ((Spec (.of (coordRing S))).presheaf.map (homOfLE hU).op).hom
  have e : (homOfLE (le_top : U ≤ ⊤)).op = (homOfLE ((Spec (.of (coordRing S))).basicOpen_le
      ((Scheme.ΓSpecIso (.of (coordRing S))).inv a))).op ≫ (homOfLE hU).op :=
    Subsingleton.elim _ _
  rw [e, Functor.map_comp, CommRingCat.comp_apply]
  exact h

/-- Every point of `Spec ℂ[t][1/f_S]` lies in `D(δ z)` for some `z`, if `δ z` does not vanish at
`z`: every prime lies in a maximal ideal, which is the kernel of a `ℂ`-point. -/
lemma exists_mem_basicOpen {δ : {z : ℂ // z ∉ S} → coordRing S}
    (hδ : ∀ z, evalAt z (δ z) ≠ 0) (x : Spec (.of (coordRing S))) :
    ∃ z, x ∈ (Spec (.of (coordRing S))).basicOpen ((Scheme.ΓSpecIso (.of (coordRing S))).inv
      (δ z)) := by
  let x' : PrimeSpectrum (coordRing S) := x
  obtain ⟨m, hm, hxm⟩ := Ideal.exists_le_maximal x'.asIdeal x'.isPrime.ne_top
  have hc : (⟨m, hm.isPrime⟩ : PrimeSpectrum (coordRing S)) ∈
      closedPoints (PrimeSpectrum (coordRing S)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hm
  rw [← Points.range_toPrimeSpectrum (K := ℂ)] at hc
  obtain ⟨χ, hχ⟩ := hc
  refine ⟨homeomorph S χ, ?_⟩
  rw [basicOpen_eq_of_affine]
  change δ (homeomorph S χ) ∉ x'.asIdeal
  intro h
  have h' : δ (homeomorph S χ) ∈ (Points.toPrimeSpectrum χ).asIdeal := by
    rw [hχ]
    exact hxm h
  rw [Points.toPrimeSpectrum_asIdeal, Points.mem_ker] at h'
  have := hδ (homeomorph S χ)
  rw [← homeomorph_symm_apply, Homeomorph.symm_apply_apply] at this
  exact this h'

/-- The affine opens of `Spec ℂ[t][1/f_S]` contained in some `D(δ z)`, a basis of the topology
when `δ z` does not vanish at `z`. -/
def basis {δ : {z : ℂ // z ∉ S} → coordRing S} (hδ : ∀ z, evalAt z (δ z) ≠ 0) :
    RiemannLocal.AffineOpenBasis (Spec (.of (coordRing S))) where
  P U := IsAffineOpen U ∧ ∃ z, U ≤ (Spec (.of (coordRing S))).basicOpen
    ((Scheme.ΓSpecIso (.of (coordRing S))).inv (δ z))
  isAffineOpen h := h.1
  exists_le {x W} hxW := by
    obtain ⟨z, hz⟩ := exists_mem_basicOpen hδ x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
      (Spec (.of (coordRing S))).isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ (W ⊓ (Spec (.of (coordRing S))).basicOpen
          ((Scheme.ΓSpecIso (.of (coordRing S))).inv (δ z)) : (Spec (.of (coordRing S))).Opens)
          from ⟨hxW, hz⟩) (W ⊓ _).isOpen
    exact ⟨U, ⟨hU, z, fun y hy ↦ (hUW hy).2⟩, hxU, fun y hy ↦ (hUW hy).1⟩

end Spec

section Covering

variable {S : Finset ℂ}
  (E : TopCat.FiniteCovering (TopCat.of (SchemePoints ℂ (Spec (.of (coordRing S))))))

/-- The projection of a finite covering of `(Spec ℂ[t][1/f_S])(ℂ)` to `ℂ ∖ S`. -/
abbrev proj (e : E.obj.left) : {z : ℂ // z ∉ S} := schemeHomeomorph S (E.obj.hom e)

lemma isCoveringMap_proj : IsCoveringMap (proj E) :=
  E.isCoveringMap.homeomorph_comp (schemeHomeomorph S)

lemma finite_proj (z : {z : ℂ // z ∉ S}) : (proj E ⁻¹' {z}).Finite := by
  have : proj E ⁻¹' {z} = E.obj.hom ⁻¹' {(schemeHomeomorph S).symm z} := by
    ext e
    exact (schemeHomeomorph S).toEquiv.eq_symm_apply.symm
  rw [this]
  exact E.property.2 _

/-- Separating data on a finite covering `E` of `ℂ ∖ S`: for every `z`, a continuous function
`F z` injective on the fibre over `z`, and a monic `P z` over `ℂ[t][1/f_S]` whose specialisation
at every point is the fibrewise characteristic polynomial of `F z`. -/
structure SeparatingData where
  /-- The separating functions. -/
  F : {z : ℂ // z ∉ S} → E.obj.left → ℂ
  continuous_F : ∀ z, Continuous (F z)
  injOn_F : ∀ z, InjOn (F z) (proj E ⁻¹' {z})
  /-- Their fibrewise characteristic polynomials. -/
  P : {z : ℂ // z ∉ S} → (coordRing S)[X]
  monic_P : ∀ z, (P z).Monic
  map_P : ∀ z y, (P z).map (evalAt y).toRingHom = fiberCharpoly (finite_proj E) (F z) y

/-- Separating data, from the analytic input `FiberSeparatingFunctionStatement` and the
symmetric-function step `exists_monic_map_evalAt_eq_fiberCharpoly`. -/
lemma nonempty_separatingData (H : FiberSeparatingFunctionStatement) [ConnectedSpace E.obj.left] :
    Nonempty (SeparatingData E) := by
  choose F hF hhol hmod hinj using
    H S E.obj.left (proj E) (isCoveringMap_proj E) (finite_proj E)
  choose P hP hmap using fun z ↦
    exists_monic_map_evalAt_eq_fiberCharpoly (finite_proj E) (isCoveringMap_proj E) (hhol z)
      (hmod z)
  exact ⟨⟨F, hF, hinj, P, hP, hmap⟩⟩

variable {E} (D : SeparatingData E)

/-- The resultant `Res(P_z, P_z')`, a function on `ℂ ∖ S` vanishing where `F_z` fails to separate
the fibres. -/
abbrev SeparatingData.δ (z : {z : ℂ // z ∉ S}) : coordRing S :=
  resultant (D.P z) (derivative (D.P z))

lemma SeparatingData.evalAt_δ_ne_zero (z : {z : ℂ // z ∉ S}) : evalAt z (D.δ z) ≠ 0 := by
  have hs : ((D.P z).map (evalAt z).toRingHom).Separable := by
    rw [D.map_P, fiberCharpoly]
    refine separable_prod_X_sub_C_iff'.mpr fun e he e' he' h ↦ D.injOn_F z ?_ ?_ h
    · exact (finite_proj E z).mem_toFinset.mp he
    · exact (finite_proj E z).mem_toFinset.mp he'
  exact map_resultant_ne_zero (D.monic_P z) (evalAt z).toRingHom hs

/-- XII.5.1 for `ℂ ∖ S`, local step: over an affine open `U ⊆ D(δ_z)`, the covering `E` is cut
out by the separable polynomial `P_z`, so `E|_U` comes from a finite étale `Γ(U)`-algebra. -/
theorem SeparatingData.mem_essImage_chartCovering (U : (Spec (.of (coordRing S))).affineOpens)
    (z : {z : ℂ // z ∉ S}) (hUz : U.1 ≤ (Spec (.of (coordRing S))).basicOpen
      ((Scheme.ΓSpecIso (.of (coordRing S))).inv (D.δ z))) :
    (pointsFunctor ℂ Γ(Spec (.of (coordRing S)), U.1)).essImage
      (RiemannLocal.chartCovering E U) := by
  classical
  have hU : IsAffineOpen U.1 := U.2
  refine SeparableCovering.mem_essImage_pointsFunctor ((D.monic_P z).map _)
    (separable_map_of_isUnit (D.monic_P z) (restrict U.1).toRingHom (isUnit_restrict hUz))
    (F := fun e ↦ D.F z e.1) ?_ ((D.continuous_F z).comp continuous_subtype_val)
  intro ψ
  let y := schemeHomeomorph S (SchemePoints.chart hU ψ)
  have hmem (e : E.obj.left) : e ∈ (finite_proj E y).toFinset ↔
      E.obj.hom e = SchemePoints.chart hU ψ := by
    rw [Set.Finite.mem_toFinset, mem_preimage, mem_singleton_iff]
    exact (schemeHomeomorph S).injective.eq_iff
  have hchart (e : (RiemannLocal.chartCovering E U).obj.left) :
      (RiemannLocal.chartCovering E U).obj.hom e = ψ ↔ E.obj.hom e.1 = SchemePoints.chart hU ψ := by
    rw [← RiemannLocal.chart_chartCovering_hom E U e]
    exact (SchemePoints.chart_injective hU).eq_iff.symm
  refine ⟨((RiemannLocal.chartCovering E U).property.2 ψ).toFinset, fun e ↦ ?_, ?_⟩
  · rw [Set.Finite.mem_toFinset, mem_preimage, mem_singleton_iff]
  · have hψ : (Points.map (restrict U.1) ψ) = evalAt y := by
      rw [← homeomorph_symm_apply]
      change _ = (homeomorph S).symm (homeomorph S ((specHomeomorph (coordRing S)).symm _))
      rw [Homeomorph.symm_apply_apply, ← specHomeomorph_map_restrict hU ψ,
        Homeomorph.symm_apply_apply]
    rw [Polynomial.map_map]
    change (D.P z).map (Points.map (restrict U.1) ψ).toRingHom = _
    rw [hψ, D.map_P, fiberCharpoly]
    symm
    refine Finset.prod_bij (fun e _ ↦ e.1) (fun e he ↦ ?_) (fun e _ e' _ h ↦ Subtype.ext h)
      (fun e he ↦ ?_) fun _ _ ↦ rfl
    · rw [Set.Finite.mem_toFinset, mem_preimage, mem_singleton_iff] at he
      exact (hmem e.1).mpr ((hchart e).mp he)
    · have he' := (hmem e).mp he
      have hpt : (E.obj.hom e).pt ∈ U.1 := by
        rw [he']
        exact SchemePoints.pt_chart hU ψ
      let q : (RiemannLocal.chartCovering E U).obj.left := ⟨e, hpt⟩
      refine ⟨q, ?_, rfl⟩
      rw [Set.Finite.mem_toFinset, mem_preimage, mem_singleton_iff, hchart]
      exact he'

end Covering

attribute [local instance] locallyOfFiniteType_specOver

/-- XII.5.1 for `ℂ ∖ S`, connected coverings, from the analytic input: every connected finite
covering of `(Spec ℂ[t][1/f_S])(ℂ)` comes from a finite étale covering. -/
theorem mem_essImage_schemePointsFunctor (H : FiberSeparatingFunctionStatement) {S : Finset ℂ}
    (E : TopCat.FiniteCovering (TopCat.of (SchemePoints ℂ (Spec (.of (coordRing S))))))
    [ConnectedSpace E.obj.left] :
    (schemePointsFunctor ℂ (Spec (.of (coordRing S)))).essImage E := by
  obtain ⟨D⟩ := nonempty_separatingData E H
  refine RiemannLocal.mem_essImage_schemePointsFunctor E (basis D.evalAt_δ_ne_zero) fun U ↦ ?_
  obtain ⟨z, hz⟩ := U.2.2
  exact D.mem_essImage_chartCovering ⟨U.1, U.2.1⟩ z hz

/-- **XII.5.1 for `ℂ ∖ S`, conditionally on the analytic input**: if every fibre of a connected
finite covering of `ℂ ∖ S` is separated by a holomorphic function of moderate growth
(`FiberSeparatingFunctionStatement`), then the Riemann existence theorem holds for
`Spec ℂ[t][1/∏_{a ∈ S} (t - a)]`: the functor `Ψ` from finite étale algebras to finite coverings
of `ℂ ∖ S` is an equivalence of categories. (This project's route, not SGA's: see
`SGA.SGA1.ExposeXII.RiemannCurves`.) The hypothesis is proved, and the unconditional form is
`PuncturedPlane.riemannExistence_coordRing` (`SGA.SGA1.ExposeXII.GAGAFiberSeparating`). -/
theorem isEquivalence_pointsFunctor_coordRing (H : FiberSeparatingFunctionStatement)
    (S : Finset ℂ) : (pointsFunctor ℂ (coordRing S)).IsEquivalence := by
  rw [isEquivalence_pointsFunctor_iff]
  have hne : Nonempty {z : ℂ // z ∉ S} := let ⟨z, hz⟩ := S.exists_notMem; ⟨⟨z, hz⟩⟩
  have hpre : PreconnectedSpace {z : ℂ // z ∉ S} := preconnectedSpace_compl
  have : ConnectedSpace {z : ℂ // z ∉ S} := { toPreconnectedSpace := hpre, toNonempty := hne }
  have : ConnectedSpace (SchemePoints ℂ (Spec (.of (coordRing S)))) :=
    (schemeHomeomorph S).symm.surjective.connectedSpace (schemeHomeomorph S).symm.continuous
  have : ConnectedSpace (Spec (.of (coordRing S))) :=
    (SchemePoints.connectedSpace_iff' _).mp inferInstance
  have : PathConnectedSpace (SchemePoints ℂ (Spec (.of (coordRing S)))) :=
    .of_locallyPathConnectedSpace
  have : StronglyLocallyContractibleSpace {z : ℂ // z ∉ S} :=
    S.finite_toSet.isClosed.isOpen_compl.stronglyLocallyContractibleSpace
  have : StronglyLocallyContractibleSpace (SchemePoints ℂ (Spec (.of (coordRing S)))) :=
    (schemeHomeomorph S).isLocalHomeomorph.stronglyLocallyContractibleSpace
  refine isEquivalence_schemePointsFunctor_of_forall_isConnected _ fun E _ ↦ ?_
  have := TopCat.FiniteCovering.connectedSpace_of_isConnected E
  exact mem_essImage_schemePointsFunctor H E

/-- XII.5.1 for finite étale coverings of `ℂ ∖ S`, conditionally on the analytic input: the
Riemann existence theorem holds for every finite étale `ℂ[t][1/∏_{a ∈ S} (t - a)]`-algebra `B`
(`isEquivalence_pointsFunctor_of_finiteEtale`). Every smooth affine curve becomes such a covering
after removing finitely many points (a finite map to `𝔸¹` is étale over the complement of a
finite set). Unconditional form: `PuncturedPlane.riemannExistence_finiteEtale`
(`SGA.SGA1.ExposeXII.GAGAFiberSeparating`). -/
theorem isEquivalence_pointsFunctor_finiteEtale (H : FiberSeparatingFunctionStatement)
    (S : Finset ℂ) (B : CommAlgCat.FiniteEtale.{0} (coordRing S)) :
    letI := algebraOfFiniteEtale ℂ (coordRing S) B
    (pointsFunctor ℂ B).IsEquivalence :=
  have := isEquivalence_pointsFunctor_coordRing H S
  isEquivalence_pointsFunctor_of_finiteEtale B

end PuncturedPlane

end SGA.SGA1.ExposeXII
