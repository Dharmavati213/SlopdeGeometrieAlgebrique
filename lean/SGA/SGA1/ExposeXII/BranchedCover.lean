/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.CoveringMapOn
import SGA.SGA1.ExposeXII.Connected
import SGA.SGA1.ExposeXII.Etale
import SGA.SGA1.ExposeXII.Comparison
import SGA.SGA1.ExposeXII.FiniteLimits

/-!
# SGA 1, Exposé XII: `X(ℂ)` as a branched covering of `ℂˢ`

For `B` a domain of finite type over `ℂ`, a Noether normalization `ℂ[z₁, …, zₛ] ⊆ B` makes
`X(ℂ) → ℂˢ`, `X = Spec B`, a *branched covering*: a proper map with finite fibres, which is a
covering map over the complement `{H ≠ 0}` of a hypersurface, whose preimage is dense
(`Points.exists_branchedCover`). The algebraic input is generic étaleness of a finite extension
of domains in characteristic `0`: `B[1/H]` is standard étale over `R` for some `H ≠ 0` in `R`
(`exists_isStandardEtale_localizationAway`, from the primitive element `f` with
`g • B ⊆ R[f]` and the Bézout relation for its minimal polynomial `P`: `B[1/H] ≅ (R[T]/P)[1/H]`).

The topological consequence used in XII.5.2 is that a branched covering of `ℂˢ` is locally
path-connected (`BranchedCover.locallyPathConnectedSpace`): a point `y` near `x` lying over
`{H ≠ 0}` is joined to `x` by lifting a path from `π(y)` to `π(x)` which avoids `{H = 0}` before
its endpoint (`exists_path_avoiding`); the lift on `[0, 1)` (`IsCoveringMapOn.exists_path_lift`)
converges to `x`, the only point of the fibre near `x`, by properness
(`IsCoveringMapOn.locallyPathConnectedSpace`). Points over `{H = 0}` are
reached by density. Hence `X(ℂ)` is locally path-connected for `X = Spec B`, `B` a domain
(`Points.locallyPathConnectedSpace_of_isDomain`); the general case is in `LocalTopologyLPC.lean`.

This avoids triangulation; the argument is the classical one for local connectedness of analytic
sets through branched coverings (e.g. Gunning–Rossi, *Analytic functions of several complex
variables*, III.B).
-/

noncomputable section

open Topology Set Filter Metric Polynomial

namespace SGA.SGA1.ExposeXII

/-! ### Paths avoiding a hypersurface -/

section Avoid

/-- An arc from `0` to `1` in `ℂ`: `t ↦ t + i c t (1 - t)`. -/
private def arc (c t : ℝ) : ℂ := (t : ℂ) + ((c * t * (1 - t) : ℝ) : ℂ) * Complex.I

private lemma arc_re (c t : ℝ) : (arc c t).re = t := by simp [arc]

private lemma arc_im (c t : ℝ) : (arc c t).im = c * t * (1 - t) := by simp [arc]

private lemma norm_arc_sub_one_le {c t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖arc c t - 1‖ ≤ 1 + |c| := by
  have h1 : arc c t - 1 = ((t - 1 : ℝ) : ℂ) + ((c * t * (1 - t) : ℝ) : ℂ) * Complex.I := by
    simp [arc]; ring
  rw [h1]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  obtain ⟨h0, h1⟩ := ht
  have e1 : |t - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have e2 : |c * t * (1 - t)| ≤ |c| := by
    rw [abs_mul, abs_mul]
    have : |t| * |1 - t| ≤ 1 := by
      rw [abs_of_nonneg h0, abs_of_nonneg (by linarith)]
      nlinarith
    calc |c| * |t| * |1 - t| = |c| * (|t| * |1 - t|) := by ring
      _ ≤ |c| * 1 := by gcongr
      _ = |c| := mul_one _
  linarith

variable {σ : Type*} [Fintype σ]

/-- In `ℂ^σ`, a point `a` of a ball around `z₀` with `q(a) ≠ 0` is joined to the centre by a path
in the ball along which the polynomial `q` does not vanish, except possibly at the endpoint `z₀`.
The path runs along an arc in the complex line through `a` and `z₀`, chosen to miss the finitely
many zeros of `q` on that line. -/
theorem exists_path_avoiding {q : MvPolynomial σ ℂ} {a z₀ : σ → ℂ} {r : ℝ}
    (ha : a ∈ ball z₀ r) (hqa : MvPolynomial.eval a q ≠ 0) :
    ∃ γ : Path a z₀, (∀ t, γ t ∈ ball z₀ r) ∧
      ∀ t : unitInterval, t ≠ 1 → MvPolynomial.eval (γ t) q ≠ 0 := by
  set v := z₀ - a with hv
  have hF := finite_setOf_eval_line_eq_zero hqa v
  set F := {s : ℂ | MvPolynomial.eval (a + s • v) q = 0}
  have hbad := hF.image fun w : ℂ ↦ w.im / (w.re * (1 - w.re))
  have hvr : ‖v‖ < r := by rwa [hv, ← dist_eq_norm', ← mem_ball]
  -- choose `c` small, off the finite bad set
  set δ := (r - ‖v‖) / (‖v‖ + 1) with hδ
  have hδ0 : 0 < δ := div_pos (by linarith) (by positivity)
  obtain ⟨c, ⟨hc0, hcδ⟩, hcbad⟩ := ((Ioo_infinite hδ0).sdiff hbad).nonempty
  have hcv : (1 + |c|) * ‖v‖ < r := by
    have : |c| * ‖v‖ ≤ |c| * (‖v‖ + 1) := by gcongr; linarith
    have h2 : |c| * (‖v‖ + 1) < δ * (‖v‖ + 1) := by
      gcongr
      rwa [abs_of_pos hc0]
    have h3 : δ * (‖v‖ + 1) = r - ‖v‖ := by
      rw [hδ]; field_simp
    nlinarith
  refine ⟨⟨⟨fun t ↦ a + arc c t • v, by unfold arc; fun_prop⟩, by simp [arc], by
    simp [arc, hv]⟩, fun t ↦ ?_, fun t ht ↦ ?_⟩
  · change a + arc c t • v ∈ ball z₀ r
    rw [mem_ball, dist_eq_norm, hv]
    have : a + arc c t • (z₀ - a) - z₀ = (arc c t - 1) • (z₀ - a) := by
      rw [sub_smul, one_smul]; abel
    rw [this, norm_smul, ← hv]
    refine lt_of_le_of_lt ?_ hcv
    gcongr
    exact norm_arc_sub_one_le t.2
  · change MvPolynomial.eval (a + arc c t • v) q ≠ 0
    rcases eq_or_ne (t : ℝ) 0 with h0 | h0
    · simpa [arc, h0] using hqa
    have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm h0)
    have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h ↦ ht (Subtype.ext h)
    intro hz
    apply hcbad
    refine ⟨arc c t, hz, ?_⟩
    change (arc c t).im / ((arc c t).re * (1 - (arc c t).re)) = c
    rw [arc_re, arc_im]
    field_simp [show (1 - (t : ℝ)) ≠ 0 by linarith]

end Avoid

/-- A *branched covering* of `ℂˢ` (`s = dim`): a proper map `proj : E → ℂˢ` with finite fibres,
which is a covering map over the complement of the hypersurface `{disc = 0}`, whose preimage is
dense in `E`. -/
structure BranchedCover (E : Type*) [TopologicalSpace E] where
  /-- The dimension of the base `ℂˢ`. -/
  dim : ℕ
  /-- The projection to `ℂˢ`. -/
  proj : E → (Fin dim → ℂ)
  /-- An equation of a hypersurface containing the branch locus. -/
  disc : MvPolynomial (Fin dim) ℂ
  disc_ne_zero : disc ≠ 0
  isProperMap_proj : IsProperMap proj
  finite_proj_preimage : ∀ z, (proj ⁻¹' {z}).Finite
  isCoveringMapOn_proj : IsCoveringMapOn proj {z | MvPolynomial.eval z disc ≠ 0}
  dense_proj_preimage : Dense (proj ⁻¹' {z | MvPolynomial.eval z disc ≠ 0})

/-- A (Hausdorff) branched covering of `ℂˢ` is locally path-connected. -/
theorem BranchedCover.locallyPathConnectedSpace {E : Type*} [TopologicalSpace E] [T2Space E]
    (D : BranchedCover E) : LocallyPathConnectedSpace E :=
  D.isCoveringMapOn_proj.locallyPathConnectedSpace D.isProperMap_proj D.finite_proj_preimage
    D.dense_proj_preimage fun _ _ _ ha hW ↦ exists_path_avoiding ha hW

/-! ### Generic étaleness of finite extensions of domains in characteristic `0` -/

section GenericEtale

variable (R B : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing B] [IsDomain B]
  [Algebra R B] [FaithfulSMul R B] [Module.Finite R B] [CharZero (FractionRing R)]

/-- Generic étaleness of a finite extension of domains `R ⊆ B` in characteristic `0`, `R`
integrally closed: there is `H ≠ 0` in `R` such that `B[1/H]` is standard étale over `R`. With a
primitive element `f` (`g • B ⊆ R[f]`, `g ≠ 0`) whose minimal polynomial `P` satisfies
`a P + b P' = h ≠ 0`, take `H = g h`; then `B[1/H] ≅ (R[T]/P)[1/H]`, and `P'` is invertible there.
-/
theorem exists_isStandardEtale_localizationAway :
    ∃ H : R, H ≠ 0 ∧ Algebra.IsStandardEtale R (Localization.Away (algebraMap R B H)) := by
  classical
  obtain ⟨f, g, hg, hgf⟩ := exists_smul_mem_adjoin R B
  obtain ⟨a, b, h, hh, hab⟩ := exists_bezout_minpoly R B f
  have hint : IsIntegral R f := Algebra.IsIntegral.isIntegral f
  set P := minpoly R f with hPdef
  have hPm : P.Monic := minpoly.monic hint
  set H := g * h with hH
  refine ⟨H, mul_ne_zero hg hh, ?_⟩
  let SP : StandardEtalePair R :=
    { f := P
      monic_f := hPm
      g := C H
      cond := ⟨b * C g, a * C g, 1, by
        rw [pow_one, hH, C_mul]
        linear_combination (C g) * hab⟩ }
  let A' := AdjoinRoot P
  let ι : A' →ₐ[R] B := AdjoinRoot.liftAlgHom P (Algebra.ofId R B) f (minpoly.aeval R f)
  have hιof (r : R) : ι (AdjoinRoot.of P r) = algebraMap R B r :=
    AdjoinRoot.liftAlgHom_of _ _ _ _ r
  have hιmk (q : R[X]) : ι (AdjoinRoot.mk P q) = aeval f q :=
    AdjoinRoot.liftAlgHom_mk _ _ _ _ q
  have hιinj : Function.Injective ι := by
    refine (injective_iff_map_eq_zero _).mpr fun y hy ↦ ?_
    induction y using AdjoinRoot.induction_on with
    | ih q =>
      rw [hιmk] at hy
      exact AdjoinRoot.mk_eq_zero.mpr (minpoly.isIntegrallyClosed_dvd hint hy)
  have hιrange (y : B) (hy : y ∈ Algebra.adjoin R {f}) : y ∈ ι.range := by
    refine Algebra.adjoin_le ?_ hy
    rintro _ rfl
    exact ⟨AdjoinRoot.root P, AdjoinRoot.liftAlgHom_root _ _ _ _⟩
  let BH := Localization.Away (algebraMap R B H)
  let : Algebra A' BH := ((algebraMap B BH).comp ι.toRingHom).toAlgebra
  have hA'BH (y : A') : algebraMap A' BH y = algebraMap B BH (ι y) := rfl
  have : IsScalarTower R A' BH := .of_algebraMap_eq fun r ↦ by
    rw [hA'BH, AdjoinRoot.algebraMap_eq, hιof, IsScalarTower.algebraMap_apply R B BH]
  have hHB : algebraMap R B H ≠ 0 := by
    rw [ne_eq, ← map_zero (algebraMap R B)]
    exact (FaithfulSMul.algebraMap_injective R B).ne (mul_ne_zero hg hh)
  have hBH : Function.Injective (algebraMap B BH) :=
    IsLocalization.injective BH (powers_le_nonZeroDivisors_of_noZeroDivisors hHB)
  have hιH : ι (AdjoinRoot.mk P (C H)) = algebraMap R B H := by
    rw [AdjoinRoot.mk_C, hιof]
  -- `B[1/H]` is the localization of `R[T]/P` away from `H`
  have : IsLocalization.Away (AdjoinRoot.mk P (C H)) BH :=
    { map_units := by
        rintro ⟨_, n, rfl⟩
        rw [map_pow, hA'BH, hιH]
        exact (IsLocalization.Away.algebraMap_isUnit _).pow n
      surj := fun z ↦ by
        obtain ⟨⟨y, _, n, rfl⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R B H)) z
        obtain ⟨q, hq⟩ := hιrange _ (hgf y)
        refine ⟨⟨q * AdjoinRoot.mk P (C h), ⟨_, n + 1, rfl⟩⟩, ?_⟩
        have hq' : ι q = g • y := hq
        have hz' : z * algebraMap B BH (algebraMap R B H) ^ n = algebraMap B BH y := by
          rw [← map_pow]; exact hz
        change z * algebraMap A' BH (AdjoinRoot.mk P (C H) ^ (n + 1)) =
          algebraMap A' BH (q * AdjoinRoot.mk P (C h))
        rw [map_pow, hA'BH, hA'BH, hιH, map_mul ι, hq', AdjoinRoot.mk_C, hιof, pow_succ,
          ← mul_assoc, hz', ← map_mul]
        congr 1
        rw [Algebra.smul_def, hH, map_mul]
        ring
      exists_of_eq := fun {x y} hxy ↦ ⟨1, by
        rw [hA'BH, hA'BH] at hxy
        rw [hιinj (hBH hxy)]⟩ }
  let e : Localization.Away (AdjoinRoot.mk P (C H)) ≃ₐ[A'] BH :=
    IsLocalization.algEquiv (Submonoid.powers (AdjoinRoot.mk P (C H))) _ _
  exact .of_equiv (SP.equivAwayAdjoinRoot.trans (e.restrictScalars R))

end GenericEtale

/-! ### Complex points of a domain of finite type -/

namespace Points

/-- For `B` a domain of finite type over `ℂ`, a Noether normalization
`g₀ : ℂ[z₁, …, zₛ] → B` (injective and finite) makes `X(ℂ) → ℂˢ`, `φ ↦ (φ(g₀ zᵢ))ᵢ`, a branched
covering: it is proper with finite fibres, and a covering map over `{H ≠ 0}` for some `H ≠ 0`
with `B[1/H]` étale over `ℂ[z]` (`exists_isStandardEtale_localizationAway`); the preimage of
`{H ≠ 0}` is dense by XII.2.2 (`Points.dense_apply_ne_zero`). -/
theorem exists_branchedCover (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] : ∃ (D : BranchedCover (Points ℂ B))
      (g₀ : MvPolynomial (Fin D.dim) ℂ →ₐ[ℂ] B), Function.Injective g₀ ∧ g₀.Finite ∧
      ∀ φ i, D.proj φ i = φ (g₀ (MvPolynomial.X i)) := by
  classical
  obtain ⟨s, g₀, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ B
  let R := MvPolynomial (Fin s) ℂ
  let : Algebra R B := g₀.toRingHom.toAlgebra
  have : IsScalarTower ℂ R B := .of_algebraMap_eq fun c ↦ (g₀.commutes c).symm
  have : Module.Finite R B := hfin
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr hinj
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (FractionRing R)).injective
  obtain ⟨H, hH, hstd⟩ := exists_isStandardEtale_localizationAway R B
  let BH := Localization.Away (algebraMap R B H)
  have : IsScalarTower ℂ R BH := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply ℂ B BH, IsScalarTower.algebraMap_apply ℂ R B,
      ← IsScalarTower.algebraMap_apply R B BH]
  let π : Points ℂ B → (Fin s → ℂ) := homeomorphMvPolynomial (Fin s) ∘ proj R B
  have hπ (φ : Points ℂ B) (i : Fin s) : π φ i = φ (g₀ (MvPolynomial.X i)) := rfl
  have hπeval (φ : Points ℂ B) (p : R) :
      MvPolynomial.eval (π φ) p = φ (algebraMap R B p) := by
    have : MvPolynomial.eval (π φ) = φ.toRingHom.comp (algebraMap R B) := by
      refine MvPolynomial.ringHom_ext (fun c ↦ ?_) fun i ↦ ?_
      · simp only [MvPolynomial.eval_C, RingHom.coe_comp, Function.comp_apply]
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact (φ.apply_algebraMap c).symm
      · rw [MvPolynomial.eval_X]; rfl
    exact congr($this p)
  have hπproper : IsProperMap π :=
    (homeomorphMvPolynomial (Fin s)).isProperMap.comp isProperMap_proj_of_isIntegral
  have hπfin (z : Fin s → ℂ) : (π ⁻¹' {z}).Finite := by
    have := finite_proj_preimage_of_finite (K := ℂ) (A := R) (B := B)
      ((homeomorphMvPolynomial (Fin s)).symm z)
    convert this using 1
    ext φ
    simp [π, Homeomorph.eq_symm_apply]
  let W : Set (Fin s → ℂ) := {z | MvPolynomial.eval z H ≠ 0}
  -- `X(ℂ)` over `W` is `Spec B[1/H] (ℂ)`, which is étale over `ℂˢ`
  let ι : Points ℂ BH → Points ℂ B := Points.map (IsScalarTower.toAlgHom ℂ B BH)
  have hι : IsOpenEmbedding ι := isOpenEmbedding_map_of_isLocalizationAway (algebraMap R B H)
  have hιrange : range ι = π ⁻¹' W := by
    rw [range_map_of_isLocalizationAway (algebraMap R B H)]
    ext φ
    simp [W, hπeval]
  have hπι : π ∘ ι = homeomorphMvPolynomial (Fin s) ∘ proj R BH := by
    funext ψ
    simp only [Function.comp_apply, π]
    congr 1
  have hloc : IsLocalHomeomorphOn π (π ⁻¹' W) := by
    have h₁ : IsLocalHomeomorphOn (π ∘ ι) univ := by
      rw [hπι]
      exact ((homeomorphMvPolynomial (Fin s)).isLocalHomeomorph.comp
        (isLocalHomeomorph_proj_of_isStandardEtale (𝕜 := ℂ))).isLocalHomeomorphOn
    have := h₁.of_comp_right hι.isLocalHomeomorph.isLocalHomeomorphOn
    rwa [image_univ, hιrange] at this
  refine ⟨⟨s, π, H, hH, hπproper, hπfin, hπproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun z _ ↦ hπfin z) hloc, ?_⟩, g₀, hinj, hfin, hπ⟩
  have hne : algebraMap R B H ∈ nonZeroDivisors B :=
    mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ (show Function.Injective
      (algebraMap R B) from hinj)).mpr hH)
  have := dense_apply_ne_zero AffineAnalytification.rueckertNullstellensatz hne
  convert this using 1
  ext φ
  simp [hπeval]

/-- XII.5.2, topological input, affine integral case: for `B` a domain of finite type over `ℂ`,
the space `X(ℂ)` of `X = Spec B` is locally path-connected. -/
theorem locallyPathConnectedSpace_of_isDomain (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] : LocallyPathConnectedSpace (Points ℂ B) :=
  have ⟨D, _⟩ := exists_branchedCover B
  D.locallyPathConnectedSpace

end Points

end SGA.SGA1.ExposeXII
