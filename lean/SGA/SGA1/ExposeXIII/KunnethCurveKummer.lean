/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.KunnethCurveExtension

/-!
# SGA 1, XIII.4.6 in characteristic `0`: the Kummer covering of `𝔸¹ ∖ V(g)`

For the resolution-free route to XIII.4.6 in characteristic `0`
(`AffineLineOpenInvarianceStatement`), an étale covering of `U' = (𝔸¹ ∖ V(g)) ⊗ₖ k'` is extended
over the base change `C̄'` of the smooth compactification `C̄` of a connected component `V` of the
Kummer covering `U[z_a]/(z_a^N - (t - a))` of `U = D(g) ⊆ 𝔸¹ ⊆ ℙ¹` (`a` running over the roots of
`g`). The extension rests on Abhyankar's lemma
(`SGA.SGA1.ExposeXIII.isEtaleAt_integralClosure_of_pow_eq_mul`), whose hypothesis is that the
function field of `V` contains an `N`-th root of `x - b` up to a unit at every point `b` of
`ℙ¹ ∖ U`, in either chart. This file provides these roots, for `g(0) = 0`:

* `lineChart₀`, `lineChart₁`: the charts `D₊(x₀)` (coordinate `t`, `U = D(g)`) and `D₊(x₁)`
  (coordinate `s = t⁻¹`, `U = D(s · rev(g / t))`) as `LineChart`s;
* `kummerCovering k g N`: `Spec` of the Kummer algebra, an étale covering of `Spec Γ(U)`;
* `exists_pow_mul_eq_chartPullback₀`, `exists_pow_mul_eq_chartPullback₁`: on any covering `V`
  with a morphism to `kummerCovering k g N`, the roots are `z_a` at `t = a` (chart `0`), `z_0⁻¹` at
  `s = 0` and `z_a z_0⁻¹` (with the unit `-a⁻¹`) at `s = a⁻¹` (chart `1`), as
  `y^N u = x - b` with `u(b) ≠ 0`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Polynomial
open SGA.SGA1.ExposeXI.ProjectiveLine SGA.SGA1.ExposeXI

namespace SGA.SGA1.ExposeXIII.KummerCompactification

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {g : k[X]}

local notation "ℙ¹" => Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

/-- The chart `D₊(x₀) ≅ 𝔸¹` (coordinate `t`), in which `U = D(g)`. -/
noncomputable def lineChart₀ (hg : g ≠ 0) : LineChart g where
  O := chart₀ k
  isAffineOpen := ExposeXIII.ProjectiveLineCurve.isAffineOpen_chart₀ k
  le := lineOpen_le_chart₀ g
  φ := chartEquiv₀ k
  φ_C := ExposeXIII.ProjectiveLineCurve.chartEquiv₀_toSpec_appLE k
  g₀ := g
  g₀_ne_zero := hg
  basicOpen_eq := rfl

/-- The chart `D₊(x₁) ≅ 𝔸¹` (coordinate `s = t⁻¹`), in which `U = D(s · rev(g / t))` when
`g(0) = 0`. -/
noncomputable def lineChart₁ (hg : g ≠ 0) (hg0 : g.IsRoot 0) : LineChart g where
  O := chart₁ k
  isAffineOpen := ExposeXIII.ProjectiveLineCurve.isAffineOpen_chart₁ k
  le := lineOpen_le_chart₁ hg0
  φ := chartEquiv₁ k
  φ_C := ExposeXIII.ProjectiveLineCurve.chartEquiv₁_toSpec_appLE k
  g₀ := chartPoly₁ k g
  g₀_ne_zero := chartPoly₁_ne_zero hg hg0
  basicOpen_eq := basicOpen_chartPoly₁ hg0

/-- The restriction to `U` of the functions of a chart, `p ↦ p|_U`. -/
noncomputable def LineChart.res (d : LineChart g) : k[X] →+* Γ(ℙ¹, lineOpen k g) :=
  ((ℙ¹).presheaf.map (homOfLE d.le).op).hom.comp d.φ.symm.toRingHom

set_option backward.isDefEq.respectTransparency false in
lemma LineChart.res_C (d : LineChart g) (c : k) :
    d.res (C c) = (toSpec k).appLE ⊤ (lineOpen k g) le_top ((Scheme.ΓSpecIso (.of k)).inv c) := by
  have hc : d.φ.symm (C c) = (toSpec k).appLE ⊤ d.O le_top ((Scheme.ΓSpecIso (.of k)).inv c) :=
    (d.φ.symm_apply_eq).mpr (d.φ_C c).symm
  change (ℙ¹).presheaf.map (homOfLE d.le).op (d.φ.symm (C c)) = _
  rw [hc, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- The map `Γ(U) → Γ(V)` of an étale covering `V` of `Spec Γ(U)`. -/
noncomputable def sectionsHom (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) :
    Γ(ℙ¹, lineOpen k g) ⟶ Γ(V.left, ⊤) :=
  (Scheme.ΓSpecIso Γ(ℙ¹, lineOpen k g)).inv ≫ V.hom.appTop

set_option backward.isDefEq.respectTransparency false in
lemma chartPullback_eq (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) (d : LineChart g)
    (p : k[X]) : chartPullback V d p = sectionsHom V (d.res p) := by
  change (toLine V).appLE d.O ⊤ _ (d.φ.symm p) =
    ((ℙ¹).presheaf.map (homOfLE d.le).op ≫ sectionsHom V) (d.φ.symm p)
  congr 1
  rw [Scheme.Hom.appLE, toLine_app_eq V d.le, sectionsHom, Category.assoc, Category.assoc]
  congr 3
  let p' : V.left ⟶ Spec Γ(ℙ¹, lineOpen k g) := V.hom
  change p'.appLE ⊤ (toLine V ⁻¹ᵁ d.O) le_top ≫ V.left.presheaf.map _ = p'.appTop
  rw [Scheme.Hom.appLE_map, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

section Kummer

variable [CharZero k] [DecidableEq k]

variable (k g) in
/-- The Kummer covering `Spec Γ(U)[z_a]/(z_a^N - (t - a))` of `Spec Γ(U)`, `U = D(g) ⊆ 𝔸¹`, `a`
running over the roots of `g` (finite étale for `N ≠ 0`, as `N` and the `t - a` are units). -/
noncomputable def kummerCovering (N : ℕ) [NeZero N] :
    ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g)) :=
  MorphismProperty.Over.mk ⊤
    (Spec.map (CommRingCat.ofHom (R := Γ(ℙ¹, lineOpen k g))
      (algebraMap Γ(ℙ¹, lineOpen k g) (kummerRing k g N))))
    ⟨by
      rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr (finite_kummerRing (NeZero.ne N)), by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      exact RingHom.etale_algebraMap.mpr (etale_kummerRing (NeZero.ne N))⟩

/-- The ring map `Γ(U)[z_a]/(z_a^N - (t - a)) → Γ(V)` of a morphism of coverings
`V ⟶ kummerCovering k g N`. -/
noncomputable def kummerHom {N : ℕ} [NeZero N] {V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))}
    (φ : V ⟶ kummerCovering k g N) : kummerRing k g N →+* Γ(V.left, ⊤) :=
  ((Scheme.ΓSpecIso (.of (kummerRing k g N))).inv ≫ φ.left.appTop).hom

set_option backward.isDefEq.respectTransparency false in
lemma kummerHom_algebraMap {N : ℕ} [NeZero N] {V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))}
    (φ : V ⟶ kummerCovering k g N) (x : Γ(ℙ¹, lineOpen k g)) :
    kummerHom φ (algebraMap _ _ x) = sectionsHom V x := by
  have hw : φ.left ≫ (kummerCovering k g N).hom = V.hom := MorphismProperty.Over.w φ
  have h : CommRingCat.ofHom (R := Γ(ℙ¹, lineOpen k g))
      (algebraMap Γ(ℙ¹, lineOpen k g) (kummerRing k g N)) ≫
      (Scheme.ΓSpecIso (.of (kummerRing k g N))).inv ≫ φ.left.appTop = sectionsHom V := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← Scheme.Hom.comp_appTop, sectionsHom]
    congr 2
  exact congr($h x)

/-- The `N`-th roots `z_a` of `t - a` on a covering of `kummerCovering k g N`. -/
lemma exists_pow_eq_res₀ (hg : g ≠ 0) {N : ℕ} [NeZero N]
    {V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))} (φ : V ⟶ kummerCovering k g N) {a : k}
    (ha : g.IsRoot a) :
    ∃ z : Γ(V.left, ⊤), z ^ N = sectionsHom V ((lineChart₀ hg).res (X - C a)) := by
  have hmem : a ∈ g.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots hg).mpr ha)
  refine ⟨kummerHom φ (KummerAlgebra.T _ _ ⟨a, hmem⟩), ?_⟩
  rw [← map_pow, KummerAlgebra.T_pow, kummerHom_algebraMap]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- XIII.5.2 input in the chart `D₊(x₀)`: at a root `c` of `g`, `z_c^N = t - c` on a covering of
`kummerCovering k g N`. -/
lemma exists_pow_mul_eq_chartPullback₀ (hg : g ≠ 0) {N : ℕ} [NeZero N]
    {V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))} (φ : V ⟶ kummerCovering k g N) (c : k)
    (hc : (lineChart₀ hg).g₀.IsRoot c) :
    ∃ (y₀ : Γ(V.left, ⊤)) (u₀ : k[X]), ¬ u₀.IsRoot c ∧
      y₀ ^ N * chartPullback V (lineChart₀ hg) u₀ =
        chartPullback V (lineChart₀ hg) (X - C c) := by
  obtain ⟨z, hz⟩ := exists_pow_eq_res₀ hg φ (a := c) hc
  refine ⟨z, 1, by simp, ?_⟩
  rw [map_one, mul_one, chartPullback_eq, hz]

omit [CharZero k] [DecidableEq k] in
/-- The algebra behind `exists_pow_mul_eq_chartPullback₁`: let `Ψ₀, Ψ₁ : k[X] → A` (the two charts
`t`, `s` of `ℙ¹` mapped to a ring) agree on constants with `Ψ₀(X) Ψ₁(X) = 1`, and let every
`Ψ₀(X - a)`, `a` a root of `g`, be an `N`-th power (`N ≠ 0`). If `g(0) = 0`, then for every root
`b` of `chartPoly₁ k g = s · rev(g / t)` there are `y`, `u` with `u(b) ≠ 0` and
`y^N Ψ₁(u) = Ψ₁(X - b)`: `y = z_0⁻¹`, `u = 1` for `b = 0`, and `y = z_{b⁻¹} z_0⁻¹`, `u = -b`
otherwise. -/
lemma exists_pow_mul_eq_of_isRoot_chartPoly₁ {A : Type*} [CommRing A] (hg0 : g.IsRoot 0)
    {N : ℕ} [NeZero N] (Ψ₀ Ψ₁ : k[X] →+* A) (hC : ∀ c, Ψ₀ (C c) = Ψ₁ (C c))
    (hX : Ψ₀ X * Ψ₁ X = 1) (hz : ∀ a, g.IsRoot a → ∃ z : A, z ^ N = Ψ₀ (X - C a)) {b : k}
    (hb : (chartPoly₁ k g).IsRoot b) :
    ∃ (y : A) (u : k[X]), ¬ u.IsRoot b ∧ y ^ N * Ψ₁ u = Ψ₁ (X - C b) := by
  obtain ⟨z₀, hz₀⟩ := hz 0 hg0
  rw [C_0, sub_zero] at hz₀
  have hz₀' : z₀ ^ N * Ψ₁ X = 1 := by rw [hz₀, hX]
  obtain ⟨w, hw⟩ : ∃ w, z₀ * w = 1 := ⟨z₀ ^ (N - 1) * Ψ₁ X, by
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel NeZero.one_le, hz₀']⟩
  have hwN : w ^ N = Ψ₁ X := by
    calc w ^ N = w ^ N * (z₀ ^ N * Ψ₁ X) := by rw [hz₀', mul_one]
      _ = (z₀ * w) ^ N * Ψ₁ X := by ring
      _ = Ψ₁ X := by rw [hw, one_pow, one_mul]
  rcases (isRoot_chartPoly₁_iff hg0).mp hb with rfl | ⟨hb0, hgb⟩
  · refine ⟨w, 1, by simp, ?_⟩
    rw [map_one, mul_one, hwN, C_0, sub_zero]
  · obtain ⟨z, hz⟩ := hz _ hgb
    refine ⟨z * w, C (-b), by simp [hb0], ?_⟩
    have hpoly : (X - C b : k[X]) = (1 - C b⁻¹ * X) * C (-b) := by
      have h1 : C b⁻¹ * C b = (1 : k[X]) := by rw [← C_mul, inv_mul_cancel₀ hb0, C_1]
      rw [C_neg]
      linear_combination (-X) * h1
    rw [mul_pow, hz, hwN, hpoly]
    simp only [map_sub, map_mul, map_one]
    rw [hC b⁻¹]
    linear_combination Ψ₁ (C (-b)) * hX

omit [CharZero k] [DecidableEq k] in
set_option backward.isDefEq.respectTransparency false in
/-- `t · s = 1` on `U`, pulled back to a covering `V` of `Spec Γ(U)` (`g(0) = 0`). -/
lemma sectionsHom_res_X_mul_res_X (hg : g ≠ 0) (hg0 : g.IsRoot 0)
    (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) :
    sectionsHom V ((lineChart₀ hg).res X) * sectionsHom V ((lineChart₁ hg hg0).res X) = 1 := by
  have e₀ : (lineChart₀ hg).res X =
      (ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₀ g)).op (chartCoord₀ k) := by
    change (ℙ¹).presheaf.map _ ((chartEquiv₀ k).symm X) = _
    rw [← chartEquiv₀_chartCoord₀, RingEquiv.symm_apply_apply]
  have e₁ : (lineChart₁ hg hg0).res X =
      (ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₁ hg0)).op (chartCoord₁ k) := by
    change (ℙ¹).presheaf.map _ ((chartEquiv₁ k).symm X) = _
    rw [← chartEquiv₁_chartCoord₁, RingEquiv.symm_apply_apply]
  rw [e₀, e₁, ← map_mul, res_chartCoord₀_mul_res_chartCoord₁ hg0, map_one]

/-- XIII.5.2 input in the chart `D₊(x₁)` (coordinate `s = t⁻¹`), for `g(0) = 0`: at `s = 0`,
`(z_0⁻¹)^N = s`; at `s = b ≠ 0` (`b⁻¹` a root of `g`), `(z_{b⁻¹} z_0⁻¹)^N · (-b) = s - b`. -/
lemma exists_pow_mul_eq_chartPullback₁ (hg : g ≠ 0) (hg0 : g.IsRoot 0) {N : ℕ} [NeZero N]
    {V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))} (φ : V ⟶ kummerCovering k g N) (b : k)
    (hb : (lineChart₁ hg hg0).g₀.IsRoot b) :
    ∃ (y₀ : Γ(V.left, ⊤)) (u₀ : k[X]), ¬ u₀.IsRoot b ∧
      y₀ ^ N * chartPullback V (lineChart₁ hg hg0) u₀ =
        chartPullback V (lineChart₁ hg hg0) (X - C b) := by
  have hcp : chartPullback V (lineChart₁ hg hg0) =
      (sectionsHom V).hom.comp (lineChart₁ hg hg0).res :=
    RingHom.ext (chartPullback_eq V _)
  rw [hcp]
  have hC (c : k) : ((sectionsHom V).hom.comp (lineChart₀ hg).res) (C c) =
      ((sectionsHom V).hom.comp (lineChart₁ hg hg0).res) (C c) :=
    congrArg (sectionsHom V).hom ((LineChart.res_C _ c).trans (LineChart.res_C _ c).symm)
  have hX : ((sectionsHom V).hom.comp (lineChart₀ hg).res) X *
      ((sectionsHom V).hom.comp (lineChart₁ hg hg0).res) X = 1 :=
    sectionsHom_res_X_mul_res_X hg hg0 V
  have hz (a : k) (ha : g.IsRoot a) : ∃ z : Γ(V.left, ⊤),
      z ^ N = ((sectionsHom V).hom.comp (lineChart₀ hg).res) (X - C a) :=
    exists_pow_eq_res₀ hg φ ha
  exact exists_pow_mul_eq_of_isRoot_chartPoly₁ hg0 _ _ hC hX hz hb

end Kummer

end SGA.SGA1.ExposeXIII.KummerCompactification
