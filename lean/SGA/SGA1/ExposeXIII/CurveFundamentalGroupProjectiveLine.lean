/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.ProjectiveLinePower
import SGA.SGA1.ExposeXI.ProjectiveSpaceSimplyConnected
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupPresentation
import SGA.SGA1.ExposeXIII.MultiplicativeGroupInertiaChart

/-!
# SGA 1, XIII.2.12 for the projective line

The projective line `ℙ¹_k = Proj k[x₀, x₁]` (`SGA.SGA1.ExposeXI.ProjectiveLine.toSpec`) is a
proper smooth connected curve of genus `0`, so it satisfies the hypotheses of XIII.2.12
(`projectiveLine_isProper_smooth_connected_genus`):

* `ProjectiveLineCurve.smoothOfRelativeDimension_toSpec`: `ℙ¹_k → Spec k` is smooth of relative
  dimension `1`, since on the charts `D₊(x₀)`, `D₊(x₁)` it is `Spec k[t] → Spec k`
  (`ProjectiveLineCurve.isStandardSmoothOfRelativeDimension_polynomial`: `R[X]` is standard
  smooth of relative dimension `1` over `R`);
* `ProjectiveLineCurve.genus_toSpec`: `h¹(ℙ¹, 𝒪) = 0` (from `Hᵖ(ℙʳ, 𝒪) = 0`, `p > 0`,
  `AlgebraicGeometry.projectiveSpace.H_structureModule_subsingleton`).

The points `0 = V₊(x₁)` and `∞ = V₊(x₀)` (`ProjectiveLineCurve.pointZero`, `pointInfinity`) are
the origins of the charts `D₊(x₀) = ℙ¹ - {∞}` and `D₊(x₁) = ℙ¹ - {0}`
(`ProjectiveLineCurve.coe_chart₀`, `coe_chart₁`, `coe_torus`). The conclusion of
`TameCurvePrimeToPStatement` for given data (`TameCurvePrimeToPConclusion`) holds for `X = ℙ¹` and:

* `n = 0` (`tameCurvePrimeToPConclusion_projectiveLine_zero`): `π₁^{p'}(ℙ¹) = 1`, from XI.1.1;
* `n = 1`, the point `∞` removed (`tameCurvePrimeToPConclusion_projectiveLine_one`):
  `π₁^{p'}(𝔸¹) = 1` (`affineLinePrimeToPTrivialStatement`), and inertia subgroups at `∞` exist
  (`exists_isInertiaSubgroupAt`);
* `n = 2`, the points `0, ∞` removed (`tameCurvePrimeToPConclusion_projectiveLine_two`): `σ, σ⁻¹`
  present `π₁^{p'}(ℙ¹ - {0, ∞})` (`multiplicativeGroupPrimeToPStatement`), and the inertia groups
  at `0` and at `∞` map onto `π₁^{p'}` (`AffineLineChart.topologicalClosure_sup_proLKernel_eq_top`
  on the two charts).

With `projectiveLine_isProper_smooth_connected_genus` these are the instances `(g, n) = (0, 0)`,
`(0, 1)`, `(0, 2)` of XIII.2.12 (`k` algebraically closed; for `n = 1, 2` at the points `∞`,
resp. `0, ∞`): the hypotheses of the general statement can be met.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXIII.ProjectiveLineCurve


section Polynomial

variable (R : Type u) [CommRing R]

/-- The submersive presentation of `R[X]` with one generator and no relation. -/
noncomputable def polynomialPresentation :
    Algebra.SubmersivePresentation R
      (MvPolynomial Unit R ⧸
        Ideal.span (Set.range (PEmpty.elim : PEmpty.{1} → MvPolynomial Unit R)))
      Unit PEmpty.{1} where
  __ := Algebra.PreSubmersivePresentation.naive (σ := Unit) (v := PEmpty.elim)
    (PEmpty.elim : PEmpty.{1} → Unit) (fun x ↦ x.elim)
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp [Matrix.det_isEmpty]

/-- `R[X]` is standard smooth of relative dimension `1` over `R`. -/
instance isStandardSmoothOfRelativeDimension_polynomial :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R (Polynomial R) := by
  have h : (Ideal.span (Set.range (PEmpty.elim : PEmpty.{1} → MvPolynomial Unit R))) = ⊥ := by
    simp
  have := (polynomialPresentation R).isStandardSmoothOfRelativeDimension (n := 1) (by
    simp [Algebra.Presentation.dimension])
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
    ((Ideal.quotientEquivAlgOfEq R h).trans ((AlgEquiv.quotientBot R _).trans
      (MvPolynomial.uniqueAlgEquiv R Unit)))

end Polynomial

section Charts

open ExposeXI.ProjectiveLine HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

local notation "ℙ¹" => Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

lemma sectionToLaurent_toSpec_appTop (c : k) :
    projectiveSpace.sectionToLaurent (Fin 2) k ⊤ le_top
      ((toSpec k).appTop ((Scheme.ΓSpecIso (.of k)).inv c)) =
      projectiveSpace.toLaurent (Fin 2) k (MvPolynomial.C c) := by
  rw [toSpec, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have h : (Scheme.ΓSpecIso _).hom ((Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin 2) k 0)))).appTop
        ((Scheme.ΓSpecIso (.of k)).inv c)) =
      algebraMap k (MvPolynomial.homogeneousSubmodule (Fin 2) k 0) c := by
    rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply,
      Iso.inv_hom_id_apply]
    rfl
  rw [projectiveSpace.sectionToLaurent_appTop, h]
  rfl

lemma chartEquiv₀_toSpec_appLE (c : k) :
    chartEquiv₀ k ((toSpec k).appLE ⊤ (chart₀ k) le_top ((Scheme.ΓSpecIso (.of k)).inv c)) =
      Polynomial.C c := by
  apply (lineLaurent_injective (k := k)).comp Polynomial.toLaurent_injective
  simp only [Function.comp_apply]
  have e : (toSpec k).appLE ⊤ (chart₀ k) le_top ((Scheme.ΓSpecIso (.of k)).inv c) =
      (ℙ¹).presheaf.map (homOfLE (le_top : chart₀ k ≤ ⊤)).op
        ((toSpec k).appTop ((Scheme.ΓSpecIso (.of k)).inv c)) := rfl
  rw [lineLaurent_chartEquiv₀, e, projectiveSpace.sectionToLaurent_map le_top,
    sectionToLaurent_toSpec_appTop]
  simp only [lineLaurent, projectiveSpace.toLaurent, Polynomial.toLaurent_C,
    AddMonoidAlgebra.mapDomainRingHom_apply]
  have h₁ : (MvPolynomial.C c : MvPolynomial (Fin 2) k) = AddMonoidAlgebra.single 0 c := rfl
  have h₂ : (LaurentPolynomial.C c : LaurentPolynomial k) = AddMonoidAlgebra.single 0 c := rfl
  rw [h₁, h₂, AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.mapDomain_single, map_zero,
    map_zero]

lemma toLaurent_C_eq_lineLaurent_C (c : k) :
    projectiveSpace.toLaurent (Fin 2) k (MvPolynomial.C c) =
      lineLaurent k (LaurentPolynomial.C c) := by
  simp only [lineLaurent, projectiveSpace.toLaurent, AddMonoidAlgebra.mapDomainRingHom_apply]
  have h₁ : (MvPolynomial.C c : MvPolynomial (Fin 2) k) = AddMonoidAlgebra.single 0 c := rfl
  have h₂ : (LaurentPolynomial.C c : LaurentPolynomial k) = AddMonoidAlgebra.single 0 c := rfl
  rw [h₁, h₂, AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.mapDomain_single, map_zero,
    map_zero]

lemma chartEquiv₁_toSpec_appLE (c : k) :
    chartEquiv₁ k ((toSpec k).appLE ⊤ (chart₁ k) le_top ((Scheme.ΓSpecIso (.of k)).inv c)) =
      Polynomial.C c := by
  apply (lineLaurent_injective (k := k)).comp (ExposeXI.toLaurentInv_injective (k := k))
  simp only [Function.comp_apply]
  have e : (toSpec k).appLE ⊤ (chart₁ k) le_top ((Scheme.ΓSpecIso (.of k)).inv c) =
      (ℙ¹).presheaf.map (homOfLE (le_top : chart₁ k ≤ ⊤)).op
        ((toSpec k).appTop ((Scheme.ΓSpecIso (.of k)).inv c)) := rfl
  rw [lineLaurent_chartEquiv₁, e, projectiveSpace.sectionToLaurent_map le_top,
    sectionToLaurent_toSpec_appTop, toLaurent_C_eq_lineLaurent_C,
    show Polynomial.C c = algebraMap k (Polynomial k) c from rfl, AlgHom.commutes]
  rfl

/-- On a chart `U` of `ℙ¹` with `Γ(U) ≅ k[X]` compatibly with constants, `ℙ¹ ⟶ Spec k` is given by
a standard smooth ring map of relative dimension `1`. -/
lemma isStandardSmoothOfRelativeDimension_toSpec_appLE (U : (ℙ¹).Opens)
    (ψ : Γ(ℙ¹, U) ≃+* Polynomial k)
    (h : ∀ c, ψ ((toSpec k).appLE ⊤ U le_top ((Scheme.ΓSpecIso (.of k)).inv c)) = Polynomial.C c) :
    ((toSpec k).appLE ⊤ U le_top).hom.IsStandardSmoothOfRelativeDimension 1 := by
  have hC : (algebraMap k (Polynomial k)).IsStandardSmoothOfRelativeDimension 1 :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr inferInstance
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.left _ ψ.symm hC
  have h₂ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right _
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv h₁
  convert h₂ using 1
  ext x
  obtain ⟨c, rfl⟩ : ∃ c, (Scheme.ΓSpecIso (.of k)).inv c = x :=
    ⟨(Scheme.ΓSpecIso (.of k)).hom x, Iso.hom_inv_id_apply _ x⟩
  have hc : (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
      ((Scheme.ΓSpecIso (.of k)).inv c) = c := (Scheme.ΓSpecIso (.of k)).inv_hom_id_apply c
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, hc]
  rw [show algebraMap k (Polynomial k) c = Polynomial.C c from rfl, ← h c,
    RingEquiv.symm_apply_apply]

lemma isAffineOpen_chart₀ : IsAffineOpen (chart₀ k) :=
  Proj.isAffineOpen_basicOpen _ _ (projectiveSpace.prodX_mem _) (by simp)

lemma isAffineOpen_chart₁ : IsAffineOpen (chart₁ k) :=
  Proj.isAffineOpen_basicOpen _ _ (projectiveSpace.prodX_mem _) (by simp)

/-- The projective line `ℙ¹_k → Spec k` is smooth of relative dimension `1`: it is covered by the
two charts `D₊(x₀) ≅ D₊(x₁) ≅ 𝔸¹_k`. -/
instance smoothOfRelativeDimension_toSpec : SmoothOfRelativeDimension 1 (toSpec k) := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (![⟨chart₀ k, isAffineOpen_chart₀ k⟩, ⟨chart₁ k, isAffineOpen_chart₁ k⟩] :
      Fin 2 → (ℙ¹).affineOpens) ?_ fun i ↦ ?_
  · rw [eq_top_iff, ← chart₀_sup_chart₁ k]
    exact sup_le (le_iSup_of_le (0 : Fin 2) le_rfl) (le_iSup_of_le (1 : Fin 2) le_rfl)
  · fin_cases i
    · exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        (isStandardSmoothOfRelativeDimension_toSpec_appLE k _ (chartEquiv₀ k)
          (chartEquiv₀_toSpec_appLE k))
    · exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
        (isStandardSmoothOfRelativeDimension_toSpec_appLE k _ (chartEquiv₁ k)
          (chartEquiv₁_toSpec_appLE k))

/-- The projective line has genus `0`: `H¹(ℙ¹, 𝒪) = 0`. -/
theorem genus_toSpec : (toSpec k).genus = 0 := by
  have := projectiveSpace.H_structureModule_subsingleton (A := k) 1 0
  let := Scheme.Modules.moduleOver (toSpec k) (SheafOfModules.unit (ℙ¹).ringCatSheaf) 1 ⊤
  exact Module.finrank_zero_of_subsingleton

end Charts

end SGA.SGA1.ExposeXIII.ProjectiveLineCurve

namespace SGA.SGA1.ExposeXIII

open ProjectiveLineCurve

section GenusZero

open ExposeXI ExposeXI.ProjectiveLine ExposeV PreGaloisCategory

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

local notation "ℙ¹" => Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

/-- The projective line satisfies the hypotheses of XIII.2.12 with `g = 0`: it is a proper smooth
connected curve of genus `0`. -/
theorem projectiveLine_isProper_smooth_connected_genus :
    IsProper (toSpec k) ∧ SmoothOfRelativeDimension 1 (toSpec k) ∧ ConnectedSpace ℙ¹ ∧
      (toSpec k).genus = 0 :=
  ⟨inferInstance, inferInstance, inferInstance, genus_toSpec k⟩

/-- The fundamental group of `ℙ¹_k` (`k` algebraically closed) is trivial at every geometric point
of the open `⊤`. -/
lemma subsingleton_etaleFundamentalGroup_top [IsAlgClosed k] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ ((⊤ : (ℙ¹).Opens) : Scheme.{u})) :
    Subsingleton (etaleFundamentalGroup Ω ξ) := by
  have : IsIso (⊤ : (ℙ¹).Opens).ι := inferInstanceAs (IsIso (Scheme.topIso ℙ¹).hom)
  have h := (isSimplyConnected_iff_subsingleton Ω (ξ ≫ (⊤ : (ℙ¹).Opens).ι)).mp
    (isSimplyConnected_projectiveLine k)
  exact (autMap_bijective (FEt.pullback (⊤ : (ℙ¹).Opens).ι)
    (FEt.pullbackFiberIso Ω (⊤ : (ℙ¹).Opens).ι ξ)).injective.subsingleton

/-- XIII.2.12 for `X = ℙ¹_k`, `g = 0`, `n = 0` ("in other words" form, `k` algebraically
closed): `π₁^{p'}(ℙ¹)` is trivial, the pro-`p'` group with no generators. Together with
`projectiveLine_isProper_smooth_connected_genus`, this is the instance `(g, n) = (0, 0)` of
`TameCurvePrimeToPStatement` (a non-vacuity check). -/
theorem tameCurvePrimeToPConclusion_projectiveLine_zero [IsAlgClosed k] (a : Fin 0 → ℙ¹)
    (U : (ℙ¹).Opens) (hU : (U : Set ℙ¹) = (Set.range a)ᶜ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ (U : Scheme.{u})) :
    TameCurvePrimeToPConclusion k ℙ¹ 0 0 a U Ω ξ := by
  obtain rfl : U = ⊤ := by
    ext x
    simp [hU]
  have := subsingleton_etaleFundamentalGroup_top k Ω ξ
  refine ⟨Fin.elim0, Fin.elim0, Fin.elim0, ⟨?_, fun G _ _ _ _ ↦ ⟨fun φ ψ _ _ _ ↦ ?_,
    fun x' y' σ' _ ↦ ⟨1, funext fun i ↦ i.elim0, funext fun i ↦ i.elim0, funext fun i ↦ i.elim0⟩⟩⟩,
    fun j ↦ j.elim0⟩
  · rw [Subsingleton.elim (surfaceWord _ _ _) 1]
    exact one_mem _
  · ext γ
    rw [Subsingleton.elim γ 1, map_one, map_one]

end GenusZero

end SGA.SGA1.ExposeXIII

namespace SGA.SGA1.ExposeXIII.ProjectiveLineCurve

open ExposeXI ExposeXI.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

local notation "ℙ¹" => Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

lemma chartEquiv₀_symm_X : (chartEquiv₀ k).symm Polynomial.X = chartCoord₀ k := by
  rw [RingEquiv.symm_apply_eq, chartEquiv₀_chartCoord₀]

lemma chartEquiv₁_symm_X : (chartEquiv₁ k).symm Polynomial.X = chartCoord₁ k := by
  rw [RingEquiv.symm_apply_eq, chartEquiv₁_chartCoord₁]

/-- The point `0 = V₊(x₁)` of `ℙ¹_k`: the origin `t = 0` of the chart `D₊(x₀) = Spec k[t]`
(`t = x₁/x₀`). -/
noncomputable def pointZero : ℙ¹ :=
  AffineLineChart.origin (isAffineOpen_chart₀ k) (chartEquiv₀ k)

/-- The point `∞ = V₊(x₀)` of `ℙ¹_k`: the origin `s = 0` of the chart `D₊(x₁) = Spec k[s]`
(`s = x₀/x₁`). -/
noncomputable def pointInfinity : ℙ¹ :=
  AffineLineChart.origin (isAffineOpen_chart₁ k) (chartEquiv₁ k)

/-- `D₊(x₀) = ℙ¹ - {∞}`. -/
lemma coe_chart₀ : (chart₀ k : Set ℙ¹) = {pointInfinity k}ᶜ :=
  AffineLineChart.coe_eq_compl_origin _ _ (by rw [sup_comm, chart₀_sup_chart₁])
    (by rw [chartEquiv₁_symm_X, basicOpen_chartCoord₁, inf_comm, chart₀_inf_chart₁])

/-- `D₊(x₁) = ℙ¹ - {0}`. -/
lemma coe_chart₁ : (chart₁ k : Set ℙ¹) = {pointZero k}ᶜ :=
  AffineLineChart.coe_eq_compl_origin _ _ (chart₀_sup_chart₁ k)
    (by rw [chartEquiv₀_symm_X, basicOpen_chartCoord₀, chart₀_inf_chart₁])

/-- `D₊(x₀x₁) = ℙ¹ - {0, ∞}`. -/
lemma coe_torus :
    (projectiveSpace.torus (Fin 2) k : Set ℙ¹) = {pointZero k, pointInfinity k}ᶜ := by
  rw [← chart₀_inf_chart₁, TopologicalSpace.Opens.coe_inf, coe_chart₀, coe_chart₁,
    Set.insert_eq, Set.compl_union, Set.inter_comm]

lemma isClosed_singleton_pointInfinity : IsClosed {pointInfinity k} := by
  rw [← compl_compl ({pointInfinity k} : Set ℙ¹), ← coe_chart₀]
  exact (chart₀ k).isOpen.isClosed_compl

lemma isClosed_singleton_pointZero : IsClosed {pointZero k} := by
  rw [← compl_compl ({pointZero k} : Set ℙ¹), ← coe_chart₁]
  exact (chart₁ k).isOpen.isClosed_compl

lemma pointZero_ne_pointInfinity : pointZero k ≠ pointInfinity k := by
  intro h
  have : pointZero k ∈ (chart₀ k : Set ℙ¹) :=
    AffineLineChart.origin_mem (isAffineOpen_chart₀ k) (chartEquiv₀ k)
  rw [coe_chart₀, h] at this
  exact this rfl

/-- `D₊(x₀) ≅ Spec k[t]`. -/
noncomputable def chart₀Iso : (chart₀ k : Scheme.{u}) ≅ Spec (.of (Polynomial k)) :=
  (isAffineOpen_chart₀ k).isoSpec ≪≫
    (Scheme.Spec.mapIso (chartEquiv₀ k).toCommRingCatIso.op).symm

open ExposeV in
/-- `π₁^{p'}(ℙ¹ - {∞}) = 1` (`k` algebraically closed of characteristic `p`): `ℙ¹ - {∞} = D₊(x₀)`
is the affine line (`affineLinePrimeToPTrivialStatement`). -/
lemma proLKernel_chart₀_eq_top [IsAlgClosed k] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ (chart₀ k : Scheme.{u})) :
    proLKernel (primesDifferentFrom (ringChar k)) (etaleFundamentalGroup Ω ξ) = ⊤ := by
  have : ConnectedSpace (chart₀ k : Scheme.{u}) := Scheme.connectedSpace_of_iso (chart₀Iso k)
  let ψ := autContinuousMulEquiv (FEt.pullback (chart₀Iso k).hom)
    (FEt.pullbackFiberIso Ω (chart₀Iso k).hom ξ)
  have h := affineLinePrimeToPTrivialStatement (ringChar k) k Ω (ξ ≫ (chart₀Iso k).hom)
  rw [eq_top_iff]
  refine le_trans ?_ (comap_proLKernel_le_of_isOpenMap _ ψ.toMulEquiv.toMonoidHom ψ.bijective
    ψ.toHomeomorph.isOpenMap)
  change ⊤ ≤ (proLKernel _ (FundamentalGroup (ξ ≫ (chart₀Iso k).hom))).comap _
  rw [h, Subgroup.comap_top]

end SGA.SGA1.ExposeXIII.ProjectiveLineCurve

namespace SGA.SGA1.ExposeXIII

open ProjectiveLineCurve ExposeXI ExposeXI.ProjectiveLine ExposeV

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

local notation "ℙ¹" => Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

/-- XIII.2.12 for `X = ℙ¹_k`, `g = 0`, `n = 1` ("in other words" form, `k` algebraically
closed): for `U = ℙ¹ - {∞}`, `π₁^{p'}(U)` is the pro-`p'` group generated by `σ₁` with `σ₁ = 1`
(it is trivial, XIII.2.12 for the affine line), and inertia subgroups at `∞` exist. Together with
`projectiveLine_isProper_smooth_connected_genus`, this is the instance `(g, n) = (0, 1)` of
`TameCurvePrimeToPStatement` with the point `∞` removed. -/
theorem tameCurvePrimeToPConclusion_projectiveLine_one [IsAlgClosed k] (a : Fin 1 → ℙ¹)
    (ha : a 0 = pointInfinity k) (U : (ℙ¹).Opens) (hU : (U : Set ℙ¹) = (Set.range a)ᶜ)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ (U : Scheme.{u})) :
    TameCurvePrimeToPConclusion k ℙ¹ 0 1 a U Ω ξ := by
  obtain rfl : U = chart₀ k := by
    ext x
    rw [hU, coe_chart₀, Set.range_unique, Fin.default_eq_zero, ha]
  have hK := proLKernel_chart₀_eq_top k Ω ξ
  have : IsIntegral ℙ¹ := inferInstanceAs (IsIntegral (projectiveSpace k 1))
  have hne : ((chart₀ k : (ℙ¹).Opens) : Set ℙ¹).Nonempty := by
    have : Nontrivial Γ(ℙ¹, chart₀ k) := (chartEquiv₀ k).symm.injective.nontrivial
    obtain ⟨p⟩ : Nonempty (PrimeSpectrum Γ(ℙ¹, chart₀ k)) := inferInstance
    rw [← (isAffineOpen_chart₀ k).range_fromSpec]
    exact ⟨_, p, rfl⟩
  refine ⟨Fin.elim0, Fin.elim0, fun _ ↦ 1, ⟨by rw [hK]; trivial, fun G _ _ _ hG ↦
    ⟨fun φ ψ _ _ _ ↦ ?_, fun x' y' σ' hσ' ↦ ⟨1, funext fun i ↦ i.elim0,
      funext fun i ↦ i.elim0, funext fun j ↦ ?_⟩⟩⟩, fun j ↦ ?_⟩
  · have hφ := proLKernel_le_ker hG (φ : etaleFundamentalGroup Ω ξ →* G) φ.continuous
    have hψ := proLKernel_le_ker hG (ψ : etaleFundamentalGroup Ω ξ →* G) ψ.continuous
    rw [hK] at hφ hψ
    ext γ
    exact ((MonoidHom.mem_ker).mp (hφ trivial)).trans ((MonoidHom.mem_ker).mp (hψ trivial)).symm
  · rw [surfaceWord_genus_zero] at hσ'
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at hσ'
    rw [Fin.fin_one_eq_zero j, hσ']
    rfl
  · obtain ⟨H, hH⟩ := exists_isInertiaSubgroupAt (chart₀ k) hne (geometricPointAt ℙ¹ (a j)) ξ
    refine ⟨_, _, inferInstance, geometricPointAt ℙ¹ (a j), H,
      imagePoint_geometricPointAt _, hH, ?_⟩
    rw [hK, sup_top_eq, sup_top_eq]


section Torus

open scoped LaurentPolynomial

/-- The torus `D₊(x₀x₁) = ℙ¹ - {0, ∞}` is affine. -/
lemma isAffineOpen_torus : IsAffineOpen (projectiveSpace.torus (Fin 2) k) := by
  rw [← basicOpen_chartCoord₀]
  exact (isAffineOpen_chart₀ k).basicOpen _

/-- `ℙ¹ - {0, ∞} = D₊(x₀x₁) ≅ 𝔾_m = Spec k[T, T⁻¹]`, `T = x₁/x₀`. -/
noncomputable def torusIso :
    ((projectiveSpace.torus (Fin 2) k : (ℙ¹).Opens) : Scheme.{u}) ≅ Spec (.of k[T;T⁻¹]) :=
  (isAffineOpen_torus k).isoSpec ≪≫
    (Scheme.Spec.mapIso (torusEquiv k).toCommRingCatIso.op).symm

variable [IsAlgClosed k] {Ω₀ : Type u} [Field Ω₀] [IsSepClosed Ω₀]
  {xb : Spec (.of Ω₀) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)}
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  {ξ : Spec (.of Ω) ⟶ ((projectiveSpace.torus (Fin 2) k :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Opens) : Scheme.{u})}
  {H : Subgroup (etaleFundamentalGroup Ω ξ)}

/-- XIII.2.12 for `ℙ¹ - {0, ∞}`, inertia at `0` (`k` algebraically closed): every inertia
subgroup of `π₁(ℙ¹ - {0, ∞})` at a geometric point over `0` maps onto `π₁^{p'}(ℙ¹ - {0, ∞})`. -/
theorem topologicalClosure_sup_proLKernel_eq_top_of_pointZero (hxb : xb.imagePoint = pointZero k)
    (hH : IsInertiaSubgroupAt (projectiveSpace.torus (Fin 2) k) xb ξ H) :
    (H ⊔ proLKernel (primesDifferentFrom (ringChar k))
      (etaleFundamentalGroup Ω ξ)).topologicalClosure = ⊤ :=
  AffineLineChart.topologicalClosure_sup_proLKernel_eq_top (ringChar k) (isAffineOpen_chart₀ k)
    (chartEquiv₀ k) (by rw [chartEquiv₀_symm_X, basicOpen_chartCoord₀]) hxb hH

/-- XIII.2.12 for `ℙ¹ - {0, ∞}`, inertia at `∞` (`k` algebraically closed): every inertia
subgroup of `π₁(ℙ¹ - {0, ∞})` at a geometric point over `∞` maps onto `π₁^{p'}(ℙ¹ - {0, ∞})`. -/
theorem topologicalClosure_sup_proLKernel_eq_top_of_pointInfinity
    (hxb : xb.imagePoint = pointInfinity k)
    (hH : IsInertiaSubgroupAt (projectiveSpace.torus (Fin 2) k) xb ξ H) :
    (H ⊔ proLKernel (primesDifferentFrom (ringChar k))
      (etaleFundamentalGroup Ω ξ)).topologicalClosure = ⊤ :=
  AffineLineChart.topologicalClosure_sup_proLKernel_eq_top (ringChar k) (isAffineOpen_chart₁ k)
    (chartEquiv₁ k) (by rw [chartEquiv₁_symm_X, basicOpen_chartCoord₁]) hxb hH

omit [IsAlgClosed k] in
lemma range_eq_pair (a : Fin 2 → ℙ¹) (ha₀ : a 0 = pointZero k) (ha₁ : a 1 = pointInfinity k) :
    Set.range a = {pointZero k, pointInfinity k} := by
  rw [← ha₀, ← ha₁]
  ext x
  simp [Fin.exists_fin_two, eq_comm]

/-- XIII.2.12 for `X = ℙ¹_k`, `g = 0`, `n = 2`, `U = ℙ¹ - {0, ∞}` ("in other words" form, with
the inertia condition): for `k` algebraically closed of characteristic `p`, `σ₁ = σ` and
`σ₂ = σ⁻¹` present `π₁^{p'}(ℙ¹ - {0, ∞})` as the pro-`p'` group generated by `σ₁, σ₂` with
`σ₁ σ₂ = 1` (the pro-`p'` completion of `ℤ`, `multiplicativeGroupPrimeToPStatement`), and every
inertia group at `0` (resp. `∞`) has the same image as `σ₁^ℤ` (resp. `σ₂^ℤ`) in `π₁^{p'}`. Together
with `projectiveLine_isProper_smooth_connected_genus` and `pointZero_ne_pointInfinity`, this is the
instance `(g, n) = (0, 2)` of `TameCurvePrimeToPStatement` for the points `0, ∞` (SGA: any two
points, which `PGL₂(k)` moves to `0, ∞`; and `k` separably closed). -/
theorem tameCurvePrimeToPConclusion_projectiveLine_two (a : Fin 2 → ℙ¹)
    (ha₀ : a 0 = pointZero k) (ha₁ : a 1 = pointInfinity k) (U : (ℙ¹).Opens)
    (hU : (U : Set ℙ¹) = (Set.range a)ᶜ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ (U : Scheme.{u})) :
    TameCurvePrimeToPConclusion k ℙ¹ 0 2 a U Ω ξ := by
  obtain rfl : U = projectiveSpace.torus (Fin 2) k :=
    SetLike.coe_injective (by rw [hU, range_eq_pair k a ha₀ ha₁, coe_torus])
  have : ConnectedSpace ((projectiveSpace.torus (Fin 2) k : (ℙ¹).Opens) : Scheme.{u}) :=
    Scheme.connectedSpace_of_iso (torusIso k)
  have : IsIntegral ℙ¹ := inferInstanceAs (IsIntegral (projectiveSpace k 1))
  have hne : ((projectiveSpace.torus (Fin 2) k : (ℙ¹).Opens) : Set ℙ¹).Nonempty := by
    obtain ⟨x⟩ : Nonempty ((projectiveSpace.torus (Fin 2) k : (ℙ¹).Opens) : Scheme.{u}) :=
      inferInstance
    exact ⟨x.1, x.2⟩
  obtain ⟨σ, hσ⟩ := exists_bijective_eval_of_iso (ringChar k) k (torusIso k) Ω ξ
  have hσtop := topologicalClosure_zpowers_sup_proLKernel_eq_top hσ
  refine ⟨Fin.elim0, Fin.elim0, ![σ, σ⁻¹], isProLSurfaceGroup_of_bijective_eval hσ, fun j ↦ ?_⟩
  obtain ⟨H, hH⟩ := exists_isInertiaSubgroupAt _ hne (geometricPointAt ℙ¹ (a j)) ξ
  refine ⟨_, _, inferInstance, geometricPointAt ℙ¹ (a j), H, imagePoint_geometricPointAt _, hH,
    ?_⟩
  obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · rw [topologicalClosure_sup_proLKernel_eq_top_of_pointZero k
      (by rw [imagePoint_geometricPointAt, ha₀]) hH]
    simpa using hσtop.symm
  · rw [topologicalClosure_sup_proLKernel_eq_top_of_pointInfinity k
      (by rw [imagePoint_geometricPointAt, ha₁]) hH]
    simpa [Subgroup.zpowers_inv] using hσtop.symm

end Torus

end SGA.SGA1.ExposeXIII
