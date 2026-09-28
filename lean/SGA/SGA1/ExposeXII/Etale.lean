/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic
import SGA.SGA1.ExposeXII.Points
import SGA.SGA1.ExposeXII.SimpleRoot

/-!
# SGA 1, Exposé XII: étale and finite morphisms on points

For an `A`-algebra `B` and a complete nontrivially normed field `𝕜` (for instance `ℂ`), we study
the map `Y(𝕜) → X(𝕜)` induced by `Y = Spec B → X = Spec A`.

* XII.3.1 (iii), XII.3.3 a): if `B` is étale over `A`, the map is a local homeomorphism
  (`isLocalHomeomorph_proj_of_etale`). SGA argues that `f^an` is étale, hence a local
  isomorphism; here `B` is locally standard étale (mathlib's local structure theorem), and for
  `B = A[t, g(t)⁻¹]/(f(t))` the points of `Y` are the pairs `(x, t)` with `f_x(t) = 0`,
  `g_x(t) ≠ 0`, whose simple root `t` depends continuously on `x` by the implicit function
  theorem (`exists_continuousOn_simpleRoot`).
* XII.3.2 (v), (vi), one direction: if `B` is integral (e.g. finite) over `A` and `𝕜` is proper
  (`ℝ`, `ℂ`, …), the map is proper (`isProperMap_proj_of_isIntegral`), by Cauchy's bound on the
  roots of monic polynomials.
* Hence a finite étale `A`-algebra gives a finite covering map `Y(𝕜) → X(𝕜)`
  (`isCoveringMap_proj`, `finite_proj_preimage`): this is the functor of XII.5.1 on points.
-/

noncomputable section

namespace SGA.SGA1.ExposeXII

open Topology Set Filter Polynomial

namespace Points

section Eval

variable {K : Type*} [CommRing K] {A : Type*} [CommRing A] [Algebra K A]

variable {B : Type*} [CommRing B] [Algebra K B] [Algebra A B] [IsScalarTower K A B]

lemma apply_aeval (ψ : Points K B) (p : A[X]) (b : B) :
    ψ (aeval b p) = (p.map (proj A B ψ).toRingHom).eval (ψ b) := by
  rw [aeval_def, eval_map]
  exact hom_eval₂ p (algebraMap A B) ψ.toRingHom b

variable [TopologicalSpace K] [IsTopologicalRing K]

lemma continuous_eval_map (p : A[X]) :
    Continuous fun z : Points K A × K ↦ (p.map z.1.toRingHom).eval z.2 := by
  simp_rw [eval_map, eval₂_eq_sum_range, toRingHom_apply]
  exact continuous_finsetSum _ fun i _ ↦
    ((continuous_apply _).comp continuous_fst).mul (continuous_snd.pow i)

end Eval

/-! ### Standard étale algebras -/

section StandardEtale

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {A : Type*} [CommRing A] [Algebra 𝕜 A] {B : Type*} [CommRing B] [Algebra 𝕜 B] [Algebra A B]
  [IsScalarTower 𝕜 A B] (P : StandardEtalePresentation A B)

/-- The locus `{(x, t) | f_x(t) = 0, g_x(t) ≠ 0}` in `X(𝕜) × 𝕜` attached to a standard étale
presentation `B = A[t, g(t)⁻¹]/(f(t))`. -/
def standardEtaleLocus : Set (Points 𝕜 A × 𝕜) :=
  {z | (P.f.map z.1.toRingHom).IsRoot z.2 ∧ (P.g.map z.1.toRingHom).eval z.2 ≠ 0}

/-- The coordinates `(π y, y(t))` of a point `y` of a standard étale algebra. -/
def standardEtaleCoords (ψ : Points 𝕜 B) : Points 𝕜 A × 𝕜 := (proj A B ψ, ψ P.x)

omit [Algebra 𝕜 A] [IsScalarTower 𝕜 A B] in
lemma apply_aeval_g_ne_zero (ψ : Points 𝕜 B) : ψ (aeval P.x P.g) ≠ 0 :=
  (P.hasMap.2.map ψ).ne_zero

lemma standardEtaleCoords_mem (ψ : Points 𝕜 B) :
    standardEtaleCoords P ψ ∈ standardEtaleLocus P := by
  refine ⟨?_, ?_⟩
  · rw [IsRoot.def, standardEtaleCoords, ← apply_aeval, P.hasMap.1, map_zero]
  · rw [standardEtaleCoords, ← apply_aeval]
    exact apply_aeval_g_ne_zero P ψ

/-- Every element of a standard étale algebra is a rational function of `t` over `A`, whose
denominator is a power of `g(t)`; hence the value of a point is a continuous function of its
coordinates. -/
lemma exists_apply_eq (s : B) : ∃ (p : A[X]) (n : ℕ), ∀ ψ : Points 𝕜 B,
    ψ s = (p.map (proj A B ψ).toRingHom).eval (ψ P.x) /
      ((P.g.map (proj A B ψ).toRingHom).eval (ψ P.x)) ^ n := by
  obtain ⟨p, n, hp⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
  refine ⟨p, n, fun ψ ↦ ?_⟩
  have := congr(ψ $hp)
  rw [map_mul, map_pow, apply_aeval, apply_aeval] at this
  rw [← this, mul_div_cancel_right₀]
  rw [← apply_aeval]
  exact pow_ne_zero n (apply_aeval_g_ne_zero P ψ)

lemma standardEtaleCoords_injective : Function.Injective (standardEtaleCoords (𝕜 := 𝕜) P) := by
  intro ψ₁ ψ₂ h
  simp only [standardEtaleCoords, Prod.ext_iff] at h
  ext s
  obtain ⟨p, n, hp⟩ := exists_apply_eq (𝕜 := 𝕜) P s
  rw [hp, hp, h.1, h.2]

lemma range_standardEtaleCoords :
    range (standardEtaleCoords (𝕜 := 𝕜) P) = standardEtaleLocus P := by
  refine (range_subset_iff.mpr (standardEtaleCoords_mem P)).antisymm ?_
  rintro ⟨φ, t⟩ ⟨hf, hg⟩
  let : Algebra A 𝕜 := φ.toRingHom.toAlgebra
  have hmap : P.HasMap t := by
    refine ⟨?_, Ne.isUnit ?_⟩
    · rw [aeval_def, ← eval_map]
      exact hf
    · rwa [aeval_def, ← eval_map]
  let χ : B →+* 𝕜 := ((P.lift t hmap).comp P.equivRing.toAlgHom).toRingHom
  have hχ : χ.comp (algebraMap A B) = φ.toAlgHom.toRingHom := by
    ext a
    exact ((P.lift t hmap).comp P.equivRing.toAlgHom).commutes a
  refine ⟨ofRingHomOver φ χ hχ, ?_⟩
  simp only [standardEtaleCoords, proj_ofRingHomOver, ofRingHomOver_apply, Prod.mk.injEq,
    true_and]
  simp [χ]

lemma continuous_standardEtaleCoords : Continuous (standardEtaleCoords (𝕜 := 𝕜) P) :=
  (continuous_map _).prodMk (continuous_apply _)

/-- The points of a standard étale algebra `A[t, g(t)⁻¹]/(f(t))` form the locus
`{(x, t) | f_x(t) = 0, g_x(t) ≠ 0}` in `X(𝕜) × 𝕜`, with the subspace topology. -/
lemma isEmbedding_standardEtaleCoords : IsEmbedding (standardEtaleCoords (𝕜 := 𝕜) P) := by
  refine ⟨isInducing_of_forall (continuous_standardEtaleCoords P) fun s ↦ ?_,
    standardEtaleCoords_injective P⟩
  obtain ⟨p, n, hp⟩ := exists_apply_eq (𝕜 := 𝕜) P s
  refine ⟨fun z ↦ (p.map z.1.toRingHom).eval z.2 / ((P.g.map z.1.toRingHom).eval z.2) ^ n,
    ?_, fun ψ ↦ hp ψ⟩
  rw [range_standardEtaleCoords]
  exact (continuous_eval_map p).continuousOn.div ((continuous_eval_map P.g).pow n).continuousOn
    fun z hz ↦ pow_ne_zero n hz.2

variable [CompleteSpace 𝕜]

omit [Algebra 𝕜 B] [IsScalarTower 𝕜 A B] in
/-- The projection `{(x, t) | f_x(t) = 0, g_x(t) ≠ 0} → X(𝕜)` is a local homeomorphism: near a
point, the simple root `t` of `f_x` is a continuous function of `x` (implicit function
theorem). -/
theorem isLocalHomeomorph_standardEtaleLocus_fst :
    IsLocalHomeomorph fun z : standardEtaleLocus (𝕜 := 𝕜) P ↦ z.1.1 := by
  classical
  rintro ⟨⟨φ₀, t₀⟩, hf₀, hg₀⟩
  -- the derivative of `f` does not vanish at `t₀`
  have hsimple : (P.f.map φ₀.toRingHom).derivative.eval t₀ ≠ 0 := by
    obtain ⟨p₁, p₂, n, e⟩ := P.cond
    have := congr_arg (fun q ↦ eval t₀ (q.map φ₀.toRingHom)) e
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, eval_add, eval_mul,
      eval_pow, hf₀.eq_zero, zero_mul, add_zero] at this
    rw [derivative_map]
    intro h
    rw [h, zero_mul] at this
    exact pow_ne_zero n hg₀ this.symm
  obtain ⟨U, V, hU, hV, hφU, htV, r, hr, hrUV, hroot⟩ :=
    exists_continuousOn_simpleRoot (fun φ : Points 𝕜 A ↦ P.f.map φ.toRingHom)
      (fun φ ↦ P.monic_f.map _) (fun φ ↦ P.monic_f.natDegree_map _)
      (fun i ↦ by simpa only [coeff_map, toRingHom_apply] using continuous_apply _) hf₀ hsimple
  have hr_root : ∀ φ ∈ U, (P.f.map φ.toRingHom).IsRoot (r φ) :=
    fun φ hφ ↦ (hroot φ hφ (r φ) (hrUV hφ)).mpr rfl
  have hgr : ContinuousOn (fun φ ↦ (P.g.map φ.toRingHom).eval (r φ)) U :=
    (continuous_eval_map P.g).comp_continuousOn (continuousOn_id.prodMk hr)
  let D : Set (Points 𝕜 A) := U ∩ (fun φ ↦ (P.g.map φ.toRingHom).eval (r φ)) ⁻¹' {0}ᶜ
  have hD : IsOpen D := hgr.isOpen_inter_preimage hU isOpen_compl_singleton
  let Z := standardEtaleLocus (𝕜 := 𝕜) P
  let z₀ : Z := ⟨(φ₀, t₀), hf₀, hg₀⟩
  let s : Points 𝕜 A → Z := fun φ ↦
    if h : φ ∈ D then ⟨(φ, r φ), hr_root φ h.1, h.2⟩ else z₀
  have hs : ∀ φ (h : φ ∈ D), s φ = ⟨(φ, r φ), hr_root φ h.1, h.2⟩ := fun φ h ↦ by
    simp [s, h]
  let O : Set Z := {z | z.1.1 ∈ U ∧ z.1.2 ∈ V}
  have hO : IsOpen O :=
    (hU.prod hV).preimage continuous_subtype_val
  -- on `O`, a point is determined by its image
  have key : ∀ z ∈ O, z.1.2 = r z.1.1 := fun z hz ↦ ((hroot _ hz.1 _ hz.2).mp z.2.1).symm
  have hr₀ : r φ₀ = t₀ := key z₀ ⟨hφU, htV⟩ |>.symm
  let e : OpenPartialHomeomorph Z (Points 𝕜 A) :=
    { toFun := fun z ↦ z.1.1
      invFun := s
      source := O
      target := D
      map_source' := fun z hz ↦ ⟨hz.1, by
        simpa [key z hz] using z.2.2⟩
      map_target' := fun φ hφ ↦ by
        rw [hs φ hφ]
        exact ⟨hφ.1, hrUV hφ.1⟩
      left_inv' := fun z hz ↦ by
        have hD' : z.1.1 ∈ D := ⟨hz.1, by simpa [key z hz] using z.2.2⟩
        rw [hs _ hD']
        exact Subtype.ext (Prod.ext rfl (key z hz).symm)
      right_inv' := fun φ hφ ↦ by rw [hs φ hφ]
      open_source := hO
      open_target := hD
      continuousOn_toFun := (continuous_fst.comp continuous_subtype_val).continuousOn
      continuousOn_invFun := by
        rw [IsInducing.subtypeVal.continuousOn_iff]
        refine (continuousOn_id.prodMk (hr.mono inter_subset_left)).congr fun φ hφ ↦ ?_
        simp [hs φ hφ] }
  refine ⟨e, ⟨hφU, htV⟩, rfl⟩

/-- XII.3.1 (iii), XII.3.3 a), standard étale case: for a standard étale algebra `B` over `A`,
the map `Y(𝕜) → X(𝕜)` is a local homeomorphism. -/
theorem isLocalHomeomorph_proj_of_isStandardEtale [Algebra.IsStandardEtale A B] :
    IsLocalHomeomorph (proj A B : Points 𝕜 B → Points 𝕜 A) := by
  let P : StandardEtalePresentation A B :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let h := (isEmbedding_standardEtaleCoords (𝕜 := 𝕜) P).toHomeomorph
  let h' := h.trans (Homeomorph.setCongr (range_standardEtaleCoords (𝕜 := 𝕜) P))
  have : (proj A B : Points 𝕜 B → Points 𝕜 A) =
      (fun z : standardEtaleLocus (𝕜 := 𝕜) P ↦ z.1.1) ∘ h' := rfl
  rw [this]
  exact (isLocalHomeomorph_standardEtaleLocus_fst P).comp h'.isLocalHomeomorph

end StandardEtale

/-! ### Étale algebras -/

section Etale

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {A : Type*} [CommRing A] [Algebra 𝕜 A] {B : Type*} [CommRing B] [Algebra 𝕜 B] [Algebra A B]
  [IsScalarTower 𝕜 A B]

/-- XII.3.1 (iii), XII.3.3 a), affine case: if `B` is étale over `A`, then the map
`Y(𝕜) → X(𝕜)` is a local homeomorphism. SGA deduces this from `f^an` étale and the implicit
function theorem; here the local structure theorem (`B` is locally standard étale) reduces it to
`isLocalHomeomorph_proj_of_isStandardEtale`. -/
theorem isLocalHomeomorph_proj_of_etale [Algebra.Etale A B] :
    IsLocalHomeomorph (proj A B : Points 𝕜 B → Points 𝕜 A) := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  intro ψ₀ _
  let Q := RingHom.ker ψ₀.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime _
  have : Algebra.IsEtaleAt A Q := by
    have h := (Algebra.etaleLocus_eq_univ_iff (R := A) (A := B)).mpr inferInstance
    have : (⟨Q, ‹_›⟩ : PrimeSpectrum B) ∈ Algebra.etaleLocus A B := h ▸ mem_univ _
    exact this
  obtain ⟨h, hhQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let C := Localization.Away h
  let ι : Points 𝕜 C → Points 𝕜 B := proj B C
  have hι : IsOpenEmbedding ι := isOpenEmbedding_map_of_isLocalizationAway (K := 𝕜) (B := C) h
  have hcomp : proj A B ∘ ι = proj A C := by
    funext ψ
    ext a
    simp [ι, IsScalarTower.algebraMap_apply A B C]
  have h₁ : IsLocalHomeomorphOn (proj A B ∘ ι) univ :=
    hcomp ▸ (isLocalHomeomorph_proj_of_isStandardEtale (𝕜 := 𝕜)).isLocalHomeomorphOn
  have h₂ := h₁.of_comp_right hι.isLocalHomeomorph.isLocalHomeomorphOn
  have hψ₀ : ψ₀ ∈ ι '' univ := by
    rw [image_univ]
    change ψ₀ ∈ range (map (IsScalarTower.toAlgHom 𝕜 B C))
    rw [range_map_of_isLocalizationAway h]
    exact fun h0 ↦ hhQ (RingHom.mem_ker.mpr h0)
  exact h₂ ψ₀ hψ₀

end Etale

/-! ### Finite algebras -/

section Proper

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Cauchy's bound for the roots of a monic polynomial. -/
lemma norm_le_of_isRoot_of_monic {p : 𝕜[X]} (hp : p.Monic) {t : 𝕜} (ht : p.IsRoot t) :
    ‖t‖ ≤ 1 + ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ := by
  have h₁ := ht.norm_lt_cauchyBound hp.ne_zero
  have h₂ : cauchyBound p ≤ 1 + ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊ := by
    rw [cauchyBound, hp.leadingCoeff, nnnorm_one, div_one, add_comm]
    gcongr
    exact Finset.sup_le fun i hi ↦
      Finset.single_le_sum (f := fun i ↦ ‖p.coeff i‖₊) (fun j _ ↦ zero_le) hi
  have := (h₁.le.trans h₂)
  rw [← NNReal.coe_le_coe] at this
  simpa using this

variable [ProperSpace 𝕜]
  {A : Type*} [CommRing A] [Algebra 𝕜 A] {B : Type*} [CommRing B] [Algebra 𝕜 B] [Algebra A B]
  [IsScalarTower 𝕜 A B]

/-- XII.3.2 (v), XII.3.2 (vi), affine case, one direction: if `B` is integral over `A` (for
instance finite), then `Y(𝕜) → X(𝕜)` is a proper map. The values of a point of `Y` are roots of
monic polynomials whose coefficients are values of its image in `X`, hence bounded over compact
subsets of `X(𝕜)`. -/
theorem isProperMap_proj_of_isIntegral [Algebra.IsIntegral A B] :
    IsProperMap (proj A B : Points 𝕜 B → Points 𝕜 A) := by
  rw [isProperMap_iff_ultrafilter]
  refine ⟨continuous_map _, fun 𝒰 φ₀ h𝒰 ↦ ?_⟩
  -- every evaluation converges along `𝒰`
  have hconv : ∀ b : B, ∃ l, Tendsto (fun ψ : Points 𝕜 B ↦ ψ b) 𝒰 (𝓝 l) := by
    intro b
    obtain ⟨p, hpm, hpb⟩ := Algebra.IsIntegral.isIntegral (R := A) b
    let C : Points 𝕜 A → ℝ := fun φ ↦ 1 + ∑ i ∈ Finset.range p.natDegree, ‖φ (p.coeff i)‖
    have hC : Continuous C :=
      continuous_const.add (continuous_finsetSum _ fun i _ ↦ (continuous_apply _).norm)
    have hbound (ψ : Points 𝕜 B) : ‖ψ b‖ ≤ C (proj A B ψ) := by
      have hroot : (p.map (proj A B ψ).toRingHom).IsRoot (ψ b) := by
        rw [IsRoot.def, ← apply_aeval, aeval_def, hpb, map_zero]
      have := norm_le_of_isRoot_of_monic (hpm.map _) hroot
      simpa [C, hpm.natDegree_map, coeff_map] using this
    have hev : ∀ᶠ ψ in (𝒰 : Filter (Points 𝕜 B)), ψ b ∈ Metric.closedBall (0 : 𝕜) (C φ₀ + 1) := by
      have : ∀ᶠ ψ in (𝒰 : Filter (Points 𝕜 B)), C (proj A B ψ) < C φ₀ + 1 :=
        ((hC.tendsto φ₀).comp h𝒰).eventually (gt_mem_nhds (lt_add_one _))
      filter_upwards [this] with ψ hψ
      simpa using (hbound ψ).trans hψ.le
    obtain ⟨l, -, hl⟩ := (isCompact_closedBall (0 : 𝕜) (C φ₀ + 1)).ultrafilter_le_nhds
      (𝒰.map fun ψ ↦ ψ b) (by rw [Ultrafilter.coe_map, le_principal_iff]; exact hev)
    exact ⟨l, by rwa [Ultrafilter.coe_map] at hl⟩
  choose L hL using hconv
  have hLim : Tendsto (fun ψ : Points 𝕜 B ↦ (ψ : B → 𝕜)) 𝒰 (𝓝 L) := tendsto_pi_nhds.mpr hL
  obtain ⟨ψ₀, hψ₀⟩ : L ∈ range fun ψ : Points 𝕜 B ↦ (ψ : B → 𝕜) :=
    isClosed_range_coe.mem_of_tendsto hLim (Eventually.of_forall fun ψ ↦ mem_range_self ψ)
  have h𝒰ψ : (𝒰 : Filter (Points 𝕜 B)) ≤ 𝓝 ψ₀ := by
    rw [← hψ₀] at hLim
    exact tendsto_id'.mp ((isEmbedding_coe.tendsto_nhds_iff (f := id)).mpr hLim)
  exact ⟨ψ₀, tendsto_nhds_unique (((continuous_map _).tendsto ψ₀).comp h𝒰ψ) h𝒰, h𝒰ψ⟩

/-- XII.5.1, the functor `Ψ` on points, affine case: if `B` is finite étale over `A` (it suffices
that `B` be integral and étale), then `Y(𝕜) → X(𝕜)` is a covering map (with finite fibres): it is
a local homeomorphism (`isLocalHomeomorph_proj_of_etale`) and a proper map
(`isProperMap_proj_of_isIntegral`). -/
theorem isCoveringMap_proj [CompleteSpace 𝕜] [Algebra.IsIntegral A B] [Algebra.Etale A B] :
    IsCoveringMap (proj A B : Points 𝕜 B → Points 𝕜 A) := by
  have hloc := isLocalHomeomorph_proj_of_etale (𝕜 := 𝕜) (A := A) (B := B)
  have hprop := isProperMap_proj_of_isIntegral (𝕜 := 𝕜) (A := A) (B := B)
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  refine hprop.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun φ _ ↦ ?_)
    hloc.isLocalHomeomorphOn
  exact (hprop.isCompact_preimage isCompact_singleton).finite
    (hloc.isLocalHomeomorphOn.isDiscrete_of_image
      (subsingleton_singleton.anti (image_preimage_subset _ _)).isDiscrete)

/-- The fibres of `Y(𝕜) → X(𝕜)` are finite when `B` is finite (or integral) and étale over `A`. -/
theorem finite_proj_preimage [CompleteSpace 𝕜] [Algebra.IsIntegral A B] [Algebra.Etale A B]
    (φ : Points 𝕜 A) : (proj A B ⁻¹' {φ} : Set (Points 𝕜 B)).Finite :=
  (isProperMap_proj_of_isIntegral.isCompact_preimage isCompact_singleton).finite
    ((isLocalHomeomorph_proj_of_etale (𝕜 := 𝕜)).isLocalHomeomorphOn.isDiscrete_of_image
      (subsingleton_singleton.anti (image_preimage_subset _ _)).isDiscrete)

end Proper

end Points

end SGA.SGA1.ExposeXII
