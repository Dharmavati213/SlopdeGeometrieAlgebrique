/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeII.Field
import SGA.SGA1.ExposeX.TameLiftingPurity
import SGA.SGA1.ExposeXIII.KunnethAbhyankar
import SGA.SGA1.ExposeXIII.KunnethCompactification
import SGA.SGA1.ExposeXIII.KunnethCurveOpen
import SGA.SGA1.ExposeXIII.KunnethCurvePurity
import SGA.SGA1.ExposeXIII.KunnethField

/-!
# SGA 1, XIII.4.6 in characteristic `0`: the compactification after base change

Continuation of `SGA.SGA1.ExposeXIII.KunnethCompactification`: for an algebraically closed
extension `k'` of `k`, the base change `C̄' = C̄ ×_{ℙ¹} ℙ¹_{k'}` of the compactification `C̄` of a
connected étale covering `V` of `U = 𝔸¹ ∖ V(g)` (`g(0) = 0`):

* is a base change of `C̄ ⟶ Spec k` along `Spec k' ⟶ Spec k` (`isPullback_compactification`), so
  X.1.8 applies: étale coverings of `C̄'` come from `C̄`
  (`isEquivalence_pullback_compactification`);
* is smooth over `k'`, regular and integral
  (`smooth_isIntegral_isRegularScheme_pullback_compactification`), so the purity theorem
  `SGA.SGA1.ExposeX.finite_etale_fromNormalization_of_isRegularScheme` applies to it;
* has charts `pr⁻¹ O` of `ℙ¹_{k'}` with rings `k'[X]` (`chartEquiv'`).

We also record that the invariance property is invariant under isomorphisms of `k`-schemes
(`HasAlgClosedBaseChangeInvariance.of_iso`), and reduce `AffineLineOpenInvarianceStatement` to
polynomials with `g(0) = 0` by translating a root to `0`
(`affineLineOpenInvarianceStatement_of_isRoot_zero`).

For the purity step we also transfer Kummer roots on `V` to the base change
(`exists_pow_mul_eq_chart`, over a chart given as a `LineChart`). The purity step itself and the
domination argument, which prove `AffineLineOpenInvarianceStatement`, are in
`SGA.SGA1.ExposeXIII.KunnethCurveInvariance`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Polynomial PreGaloisCategory
open SGA.SGA1.ExposeXI.ProjectiveLine SGA.SGA1.ExposeXI

namespace SGA.SGA1.ExposeXIII.KummerCompactification

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] {g : k[X]}

local notation "ℙ¹" => Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

/-- `Spec k' ⟶ Spec k`. -/
local notation "ρ" => Spec.map (CommRingCat.ofHom (algebraMap k k'))

/-- The base change `C̄' = C̄ ×_{ℙ¹} ℙ¹_{k'}` of the compactification is a base change of `C̄` along
`Spec k' ⟶ Spec k`. -/
lemma isPullback_compactification (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) :
    IsPullback (pullback.fst (toLine V).fromNormalization (pullback.fst (toSpec k) ρ))
      (pullback.snd (toLine V).fromNormalization (pullback.fst (toSpec k) ρ) ≫
        pullback.snd (toSpec k) ρ) ((toLine V).fromNormalization ≫ toSpec k) ρ :=
  (IsPullback.of_hasPullback _ _).paste_vert (IsPullback.of_hasPullback _ _)

section Abstract

variable [IsAlgClosed k] [CharZero k]

/-! The base change `C̄' = C̄ ×_{ℙ¹} ℙ¹_{k'}` is given by abstract pullback squares
`hP : P' = ℙ¹ ×_k k'` and `hC : C' = C̄ ×_{ℙ¹} P'` (this keeps elaboration fast). -/

/-- X.1.8 for the compactification: for `V` connected, `g ≠ 0` with `g(0) = 0`, and `C'` a base
change of `C̄` along `ℙ¹_{k'} ⟶ ℙ¹`, base change of étale coverings along `C' ⟶ C̄` is an
equivalence. -/
lemma isEquivalence_pullback_compactification [IsAlgClosed k'] {P' C' : Scheme.{u}}
    {pr : P' ⟶ ℙ¹} {sP' : P' ⟶ Spec (.of k')} {π' : C' ⟶ P'} (hP : IsPullback pr sP' (toSpec k) ρ)
    (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) [IsConnected V] (hg : g ≠ 0) (hg0 : g.IsRoot 0)
    {prC : C' ⟶ (toLine V).normalization}
    (hC : IsPullback prC π' (toLine V).fromNormalization pr) :
    (ExposeV.FEt.pullback prC).IsEquivalence := by
  obtain ⟨_, _, _⟩ := isProper_smooth_isIntegral_normalization V hg hg0
  exact (hasAlgClosedBaseChangeInvariance_of_isProper _).isEquivalence_of_isPullback ρ
    (hC.paste_vert hP)

/-- For `V` connected, `g ≠ 0` with `g(0) = 0`, the base change `C'` of `C̄` along
`ℙ¹_{k'} ⟶ ℙ¹` is smooth over `k'`, integral, regular and locally noetherian, and finite over
`ℙ¹_{k'}`. -/
lemma smooth_isIntegral_isRegularScheme_pullback_compactification [IsAlgClosed k']
    {P' C' : Scheme.{u}} {pr : P' ⟶ ℙ¹} {sP' : P' ⟶ Spec (.of k')} {π' : C' ⟶ P'}
    (hP : IsPullback pr sP' (toSpec k) ρ) (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g)))
    [IsConnected V] (hg : g ≠ 0) (hg0 : g.IsRoot 0) {prC : C' ⟶ (toLine V).normalization}
    (hC : IsPullback prC π' (toLine V).fromNormalization pr) :
    Smooth (π' ≫ sP') ∧ IsIntegral C' ∧ ExposeX.IsRegularScheme C' ∧ IsLocallyNoetherian C' ∧
      IsFinite π' := by
  obtain ⟨_, _, _⟩ := isProper_smooth_isIntegral_normalization V hg hg0
  have := isFinite_fromNormalization V hg hg0
  have H := hC.paste_vert hP
  have hsm : Smooth (π' ≫ sP') := MorphismProperty.of_isPullback H inferInstance
  have hreg : ExposeX.IsRegularScheme C' :=
    fun x ↦ ExposeII.isRegularLocalRing_stalk_of_smooth_field k' (π' ≫ sP') x
  have : ConnectedSpace (Spec (.of k')) := inferInstance
  have : ConnectedSpace ↥(pullback ((toLine V).fromNormalization ≫ toSpec k) ρ) :=
    connectedSpace_pullback_of_isAlgClosed_of_connectedSpace _ _
  have : ConnectedSpace C' :=
    (Scheme.homeoOfIso H.isoPullback).symm.surjective.connectedSpace
      (Scheme.homeoOfIso H.isoPullback).symm.continuous
  have : IsLocallyNoetherian C' := LocallyOfFiniteType.isLocallyNoetherian (π' ≫ sP')
  exact ⟨hsm, ExposeX.isIntegral_of_isRegularScheme hreg, hreg, inferInstance,
    MorphismProperty.of_isPullback hC inferInstance⟩

end Abstract

section Charts

/-- `Γ(P', pr⁻¹ O) ≅ k'[X]` for a chart `O` of `ℙ¹_k` with `Γ(O) ≅ k[X]` (compatibly with the
constants) and `P' = ℙ¹ ×_k k'`, the variable going to the pulled-back coordinate
(`bijective_aeval_of_isPullback`). -/
noncomputable def chartEquiv' {P' : Scheme.{u}} {pr : P' ⟶ ℙ¹}
    {sP' : P' ⟶ Spec (.of k')} (hP : IsPullback pr sP' (toSpec k) ρ) {O : (ℙ¹).Opens}
    (hO : IsAffineOpen O) (φ : Γ(ℙ¹, O) ≃+* k[X])
    (hφ : ∀ c : k, φ ((toSpec k).appLE ⊤ O le_top ((Scheme.ΓSpecIso (.of k)).inv c)) = C c) :
    k'[X] ≃+* Γ(P', pr ⁻¹ᵁ O) :=
  letI : Algebra k' Γ(P', pr ⁻¹ᵁ O) :=
    ((sP'.appLE ⊤ (pr ⁻¹ᵁ O) le_top).hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom).toAlgebra
  RingEquiv.ofBijective (Polynomial.aeval (R := k')
      (pr.appLE O (pr ⁻¹ᵁ O) le_rfl (φ.symm X))).toRingHom
    (bijective_aeval_of_isPullback hP hO φ hφ)

set_option backward.isDefEq.respectTransparency false in
/-- `chartEquiv'` on polynomials with coefficients in `k`: `p ↦ pr^* φ⁻¹(p)`. -/
lemma chartEquiv'_map {P' : Scheme.{u}} {pr : P' ⟶ ℙ¹}
    {sP' : P' ⟶ Spec (.of k')} (hP : IsPullback pr sP' (toSpec k) ρ) {O : (ℙ¹).Opens}
    (hO : IsAffineOpen O) (φ : Γ(ℙ¹, O) ≃+* k[X])
    (hφ : ∀ c : k, φ ((toSpec k).appLE ⊤ O le_top ((Scheme.ΓSpecIso (.of k)).inv c)) = C c)
    (p : k[X]) :
    chartEquiv' k' hP hO φ hφ (p.map (algebraMap k k')) = pr.app O (φ.symm p) := by
  let : Algebra k' Γ(P', pr ⁻¹ᵁ O) :=
    ((sP'.appLE ⊤ (pr ⁻¹ᵁ O) le_top).hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom).toAlgebra
  have hc (c : k) :
      φ.symm (C c) = (toSpec k).appLE ⊤ O le_top ((Scheme.ΓSpecIso (.of k)).inv c) :=
    (φ.symm_apply_eq).mpr (hφ c).symm
  have hsq : (Scheme.ΓSpecIso (.of k)).inv ≫ (toSpec k).appLE ⊤ O le_top ≫ pr.app O =
      CommRingCat.ofHom (algebraMap k k') ≫ (Scheme.ΓSpecIso (.of k')).inv ≫
        sP'.appLE ⊤ (pr ⁻¹ᵁ O) le_top := by
    rw [Scheme.Hom.app_eq_appLE pr, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq hP.w,
      Scheme.Hom.comp_appLE, Scheme.ΓSpecIso_inv_naturality_assoc]
    rfl
  have : (chartEquiv' k' hP hO φ hφ).toRingHom.comp (mapRingHom (algebraMap k k')) =
      (pr.app O).hom.comp φ.symm.toRingHom := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · change Polynomial.aeval _ ((C c).map (algebraMap k k')) = pr.app O (φ.symm (C c))
      rw [Polynomial.map_C, aeval_C, hc]
      exact congr($(hsq).hom c).symm
    · change Polynomial.aeval _ ((X : k[X]).map (algebraMap k k')) = pr.app O (φ.symm X)
      rw [Polynomial.map_X, aeval_X, Scheme.Hom.appLE_eq_app]
  exact congr($this p)

/-- The preimage in `ℙ¹_{k'}` of a basic open `D(φ⁻¹ g₀)` of a chart is the basic open of
`chartEquiv' (g₀ ⊗ k')`. -/
lemma basicOpen_chartEquiv'_map {P' : Scheme.{u}} {pr : P' ⟶ ℙ¹}
    {sP' : P' ⟶ Spec (.of k')} (hP : IsPullback pr sP' (toSpec k) ρ) {O : (ℙ¹).Opens}
    (hO : IsAffineOpen O) (φ : Γ(ℙ¹, O) ≃+* k[X])
    (hφ : ∀ c : k, φ ((toSpec k).appLE ⊤ O le_top ((Scheme.ΓSpecIso (.of k)).inv c)) = C c)
    (g₀ : k[X]) :
    P'.basicOpen (chartEquiv' k' hP hO φ hφ (g₀.map (algebraMap k k'))) =
      pr ⁻¹ᵁ (ℙ¹).basicOpen (φ.symm g₀) := by
  rw [chartEquiv'_map, Scheme.preimage_basicOpen]

end Charts

section Extension

/-- An affine chart `O ≅ 𝔸¹_k` of `ℙ¹_k` (`Γ(O) ≅ k[X]` compatibly with the constants) containing
`U = lineOpen k g`, in which `U = D(g₀)` for a nonzero polynomial `g₀`. -/
structure LineChart (g : k[X]) where
  /-- The chart. -/
  O : (ℙ¹).Opens
  isAffineOpen : IsAffineOpen O
  le : lineOpen k g ≤ O
  /-- The coordinate ring of the chart. -/
  φ : Γ(ℙ¹, O) ≃+* k[X]
  φ_C : ∀ c : k, φ ((toSpec k).appLE ⊤ O le_top ((Scheme.ΓSpecIso (.of k)).inv c)) = C c
  /-- The equation of `U` in the chart. -/
  g₀ : k[X]
  g₀_ne_zero : g₀ ≠ 0
  basicOpen_eq : (ℙ¹).basicOpen (φ.symm g₀) = lineOpen k g

/-- A morphism of commutative rings preserves relations `y ^ N * x = z`. -/
lemma pow_mul_eq_of_eq {A B : CommRingCat.{u}} (ψ : A ⟶ B) {y x z : A} {N : ℕ}
    (h : y ^ N * x = z) : ψ y ^ N * ψ x = ψ z := by
  rw [← map_pow, ← map_mul, h]

/-- The pullback of the functions of a chart `d` to an étale covering `V` of `U`. -/
noncomputable def chartPullback (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) (d : LineChart g) :
    k[X] →+* Γ(V.left, ⊤) :=
  ((toLine V).appLE d.O ⊤ (toLine_preimage_eq_top V d.le).ge).hom.comp d.φ.symm.toRingHom

/-- Transfer of the Kummer roots to the base change: let `a : π'⁻¹ pr⁻¹ U ⟶ V` lie over
`U ⊆ ℙ¹` (`a ≫ (V ⟶ ℙ¹) = π' ≫ pr`). If for every root `c` of the equation `g₀` of `U` in the
chart `d` there are `y₀ ∈ Γ(V)` and `u₀ ∈ k[X]` with `u₀(c) ≠ 0` and `y₀^N u₀ = X - c` on `V`
(through the chart), then the same holds on `π'⁻¹ pr⁻¹ U` over `k'` for the roots of `g₀ ⊗ k'`
(`k` algebraically closed, so these are the roots of `g₀`). This is the hypothesis of
`isEtaleAt_integralClosure_chart` for the chart `pr⁻¹ O` of `ℙ¹_{k'}`. -/
lemma exists_pow_mul_eq_chart [IsAlgClosed k] {P' C' : Scheme.{u}} {pr : P' ⟶ ℙ¹}
    {sP' : P' ⟶ Spec (.of k')}
    (hP : IsPullback pr sP' (toSpec k) ρ) (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g)))
    {π' : C' ⟶ P'} (a : (π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).toScheme ⟶ V.left)
    (ha : a ≫ toLine V = (π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).ι ≫ π' ≫ pr) (d : LineChart g) (N : ℕ)
    (hK : ∀ c : k, d.g₀.IsRoot c → ∃ (y₀ : Γ(V.left, ⊤)) (u₀ : k[X]), ¬ u₀.IsRoot c ∧
      y₀ ^ N * chartPullback V d u₀ = chartPullback V d (X - C c)) (b : k')
    (hb : (d.g₀.map (algebraMap k k')).IsRoot b) :
    ∃ (y : Γ((π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).toScheme, ⊤)) (v : k'[X]), ¬ v.IsRoot b ∧
      y ^ N * ((π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).ι ≫ π').appLE (pr ⁻¹ᵁ d.O) ⊤
        (fun x _ ↦ (pr.preimage_mono d.le : pr ⁻¹ᵁ lineOpen k g ≤ pr ⁻¹ᵁ d.O) x.2)
        (chartEquiv' k' hP d.isAffineOpen d.φ d.φ_C v) =
      ((π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).ι ≫ π').appLE (pr ⁻¹ᵁ d.O) ⊤
        (fun x _ ↦ (pr.preimage_mono d.le : pr ⁻¹ᵁ lineOpen k g ≤ pr ⁻¹ᵁ d.O) x.2)
        (chartEquiv' k' hP d.isAffineOpen d.φ d.φ_C (X - C b)) := by
  have hg₀' : d.g₀.map (algebraMap k k') ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap k k').injective).mpr d.g₀_ne_zero
  have hroots := roots_map_of_injective_of_card_eq_natDegree (algebraMap k k').injective
    (IsAlgClosed.card_roots_eq_natDegree (k := k) (p := d.g₀))
  have hb' : b ∈ (d.g₀.map (algebraMap k k')).roots := (mem_roots hg₀').mpr hb
  rw [← hroots] at hb'
  obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hb'
  obtain ⟨y₀, u₀, hu₀, hy₀⟩ := hK c ((mem_roots d.g₀_ne_zero).mp hc)
  have key (p : k[X]) : ((π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).ι ≫ π').appLE (pr ⁻¹ᵁ d.O) ⊤
      (fun x _ ↦ (pr.preimage_mono d.le : pr ⁻¹ᵁ lineOpen k g ≤ pr ⁻¹ᵁ d.O) x.2)
        (chartEquiv' k' hP d.isAffineOpen d.φ d.φ_C (p.map (algebraMap k k'))) =
      a.appLE ⊤ ⊤ le_top (chartPullback V d p) := by
    set_option backward.isDefEq.respectTransparency false in
    rw [chartEquiv'_map]
    change (pr.app d.O ≫ ((π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).ι ≫ π').appLE (pr ⁻¹ᵁ d.O) ⊤ _)
      (d.φ.symm p) = ((toLine V).appLE d.O ⊤ _ ≫ a.appLE ⊤ ⊤ le_top) (d.φ.symm p)
    congr 1
    set_option backward.isDefEq.respectTransparency false in
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
      appLE_eq_of_eq (by rw [ha, Category.assoc] :
        ((π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).ι ≫ π') ≫ pr = a ≫ toLine V)]
  refine ⟨a.appLE ⊤ ⊤ le_top y₀, u₀.map (algebraMap k k'), ?_, ?_⟩
  · rwa [isRoot_map_iff (algebraMap k k').injective]
  · have k1 := key u₀
    have k2 := key (X - C c)
    have hX : (X - C (algebraMap k k' c) : k'[X]) = (X - C c).map (algebraMap k k') := by
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [hX]
    exact (congrArg (_ * ·) k1).trans
      ((pow_mul_eq_of_eq (a.appLE ⊤ ⊤ le_top) hy₀).trans k2.symm)

end Extension

end SGA.SGA1.ExposeXIII.KummerCompactification

namespace SGA.SGA1.ExposeXIII

set_option backward.isDefEq.respectTransparency false in
/-- The invariance property (`HasAlgClosedBaseChangeInvariance`) is invariant under isomorphisms
of `k`-schemes. -/
theorem HasAlgClosedBaseChangeInvariance.of_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} (e : X ≅ Y) (he : e.hom ≫ sY = sX)
    (h : HasAlgClosedBaseChangeInvariance sY) : HasAlgClosedBaseChangeInvariance sX := by
  intro k' _ _ _
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have H : IsPullback (pullback.fst sX ρ ≫ e.hom) (pullback.snd sX ρ) sY ρ :=
    (IsPullback.of_hasPullback sX ρ).of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp [he]) (by simp)
  have := h.isEquivalence_of_isPullback ρ H
  exact ExposeV.FEt.isEquivalence_pullback_of_comp (pullback.fst sX ρ) e.hom

set_option backward.isDefEq.respectTransparency false in
/-- Reduction of `AffineLineOpenInvarianceStatement` to polynomials vanishing at `0`: for a
nonconstant `g`, the translation `X ↦ X + a` by a root `a` identifies `k[X]_g` with
`k[X]_{g(X + a)}` over `k`; constant `g` give the affine line
(`hasAlgClosedBaseChangeInvariance_localization_away_of_isUnit`). -/
theorem affineLineOpenInvarianceStatement_of_isRoot_zero
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (g : k[X]), g ≠ 0 →
      g.IsRoot 0 → HasAlgClosedBaseChangeInvariance
        (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away g))))) :
    AffineLineOpenInvarianceStatement.{u} := by
  intro k _ _ _ g hg
  by_cases hu : IsUnit g
  · exact hasAlgClosedBaseChangeInvariance_localization_away_of_isUnit k hu
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root g fun h0 ↦
    hu (isUnit_iff_degree_eq_zero.mpr h0)
  let τ : k[X] ≃ₐ[k] k[X] := taylorEquiv a
  have hg' : τ g ≠ 0 := (map_ne_zero_iff _ τ.injective).mpr hg
  have h0 : (τ g).IsRoot 0 := by
    change (taylor a g).eval 0 = 0
    rw [taylor_eval, zero_add]
    exact ha
  let e : Localization.Away g ≃ₐ[k] Localization.Away (τ g) :=
    IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers g) (T := Submonoid.powers (τ g))
      (Localization.Away g) (Localization.Away (τ g)) τ (by rw [Submonoid.map_powers])
  refine (h k (τ g) hg' h0).of_iso
    (Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op) ?_
  change Spec.map (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) ≫ _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun c ↦ e.symm.commutes c

end SGA.SGA1.ExposeXIII
