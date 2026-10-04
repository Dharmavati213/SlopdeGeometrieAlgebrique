/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.CurveLiftAssembly
import SGA.Foundations.Projective.CurveProjectiveChart
import SGA.Foundations.Projective.CurveProjective
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.MvPolynomial.Expand

/-!
# SGA 1, Exposé III, 7.4: the level `0` data of a curve with a finite flat morphism to `ℙ¹`

Let `A` be a local ring with residue field `κ`, `X₀` a smooth `κ`-scheme and `g : X₀ ⟶ ℙ¹_κ` a
finite flat `κ`-morphism. The inverse images `U₀ = g⁻¹ D₊(x₀)`, `U₁ = g⁻¹ D₊(x₁)` of the standard
charts are affine with affine intersection, and the pulled back coordinates `τ = g^*(x₁ / x₀)`,
`σ = g^*(x₀ / x₁)` satisfy `τ σ = 1` on `U₀ ∩ U₁ = D(τ) = D(σ)`. For `d ≫ 0` the Čech condition
`Γ(U₀ ∩ U₁) = τᵈ Γ(U₁) + σᵈ Γ(U₀)` holds (`H¹(X₀, g^* 𝒪(2d)) = 0`, by
`AmpleLift.exists_forall_eq_add_pow_mul`), so `(X₀, U₀, U₁, τᵈ, σᵈ)` is level `0` data
(`CurveLift.baseOfHom`, a `CurveLift.Base` over `A / 𝔪`) whose chart homomorphisms
`κ[t] → Γ(U₀)`, `t ↦ τᵈ` and `κ[s] → Γ(U₁)`, `s ↦ σᵈ` are finite and flat
(`CurveLift.chartHom_baseOfHom_zero`, `CurveLift.chartHom_baseOfHom_one`). Replacing `τ` by `τᵈ`
replaces `g` by its composite with the finite flat `d`-th power map of `ℙ¹`; the algebra behind it
is `CurveLift.finite_expand` and `CurveLift.flat_expand` (`κ[t]` is finite and flat over
`κ[tᵈ]`).

With `CurveLift.exists_lift_of_base` this gives SGA 1 III.7.4 for every smooth proper curve with a
finite flat morphism to `ℙ¹` (`CurveLift.exists_lift_of_finite_flat`), hence
`SGA.SGA1.ExposeIII.SmoothProperCurveLiftStatement` from
`AlgebraicGeometry.SmoothProperCurveFiniteFlatStatement`
(`smoothProperCurveLiftStatement_of_smoothProperCurveFiniteFlatStatement`).

## References

* [SGA 1, III.7.4][SGA1]; [Hartshorne, III.5.2] (Serre vanishing on `ℙ¹`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
  AlgebraicGeometry.AmpleLift MvPolynomial IsLocalRing

namespace SGA.SGA1.ExposeIII.CurveLift

section Algebra

/-- An injective ring homomorphism from a Dedekind domain to a domain is flat (torsion-free
modules over a Dedekind domain are flat). -/
theorem flat_of_injective_of_isDedekindDomain {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain R] [IsDomain S] (φ : R →+* S) (hφ : Function.Injective φ) :
    φ.Flat := by
  algebraize [φ]
  have : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  exact (inferInstance : Module.Flat R S)

variable (k : Type*) [Field k] {d : ℕ} {σ : Type*} [Unique σ]

/-- The homomorphism `k[t] → k[t]`, `t ↦ tᵈ`, from polynomials to polynomials in the single
variable indexed by `σ`. -/
noncomputable def powHom (d : ℕ) : Polynomial k →+* MvPolynomial σ k :=
  Polynomial.eval₂RingHom MvPolynomial.C (X default ^ d)

lemma expand_eq_powHom_comp :
    (MvPolynomial.expand d : MvPolynomial σ k →ₐ[k] MvPolynomial σ k).toRingHom =
      (powHom k d).comp (MvPolynomial.uniqueAlgEquiv k σ).toRingEquiv.toRingHom := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
  · simp [powHom]
  · simp [powHom, Subsingleton.elim i default]

lemma powHom_injective (hd : 0 < d) : Function.Injective (powHom k (σ := σ) d) := by
  intro p q h
  apply (MvPolynomial.uniqueAlgEquiv k σ).symm.injective
  apply MvPolynomial.expand_injective hd
  have h' := congrArg (fun φ : MvPolynomial σ k →+* MvPolynomial σ k ↦ φ)
    (expand_eq_powHom_comp k (d := d) (σ := σ))
  have hp := RingHom.congr_fun h' ((MvPolynomial.uniqueAlgEquiv k σ).symm p)
  have hq := RingHom.congr_fun h' ((MvPolynomial.uniqueAlgEquiv k σ).symm q)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp,
    Function.comp_apply, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_ringEquiv,
    AlgEquiv.apply_symm_apply] at hp hq
  rw [hp, hq, h]

/-- `t ↦ tᵈ` makes `k[t]` finite over `k[t]` (`d > 0`). -/
theorem finite_powHom (hd : 0 < d) : (powHom k (σ := σ) d).Finite := by
  algebraize [powHom k (σ := σ) d]
  have hX : IsIntegral (Polynomial k) (X default : MvPolynomial σ k) := by
    refine ⟨Polynomial.X ^ d - Polynomial.C Polynomial.X,
      Polynomial.monic_X_pow_sub_C _ hd.ne', ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    change X default ^ d - powHom k d Polynomial.X = 0
    rw [powHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, sub_self]
  have htop : Algebra.adjoin (Polynomial k) {(X default : MvPolynomial σ k)} = ⊤ := by
    refine Algebra.eq_top_iff.mpr fun p ↦ ?_
    induction p using MvPolynomial.induction_on with
    | C a =>
      have : (C a : MvPolynomial σ k) =
          algebraMap (Polynomial k) (MvPolynomial σ k) (Polynomial.C a) := by
        change _ = powHom k d (Polynomial.C a)
        rw [powHom, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
      rw [Subsingleton.elim i default]
      exact mul_mem hp (Algebra.subset_adjoin rfl)
  have hfg := hX.fg_adjoin_singleton
  rw [htop, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩

/-- `t ↦ tᵈ` makes `k[t]` flat over `k[t]` (`d > 0`). -/
theorem flat_powHom (hd : 0 < d) : (powHom k (σ := σ) d).Flat :=
  flat_of_injective_of_isDedekindDomain _ (powHom_injective k hd)

/-- The `d`-th power map `k[t] → k[t]`, `t ↦ tᵈ`, in one variable, is finite. -/
theorem finite_expand (hd : 0 < d) :
    (MvPolynomial.expand d : MvPolynomial σ k →ₐ[k] MvPolynomial σ k).toRingHom.Finite := by
  rw [expand_eq_powHom_comp]
  exact (finite_powHom k hd).comp
    (RingHom.Finite.of_surjective _ (MvPolynomial.uniqueAlgEquiv k σ).toRingEquiv.surjective)

/-- The `d`-th power map `k[t] → k[t]`, `t ↦ tᵈ`, in one variable, is flat. -/
theorem flat_expand (hd : 0 < d) :
    (MvPolynomial.expand d : MvPolynomial σ k →ₐ[k] MvPolynomial σ k).toRingHom.Flat := by
  rw [expand_eq_powHom_comp]
  exact RingHom.Flat.comp
    (RingHom.Flat.of_bijective (f := (MvPolynomial.uniqueAlgEquiv k σ).toRingEquiv.toRingHom)
      (MvPolynomial.uniqueAlgEquiv k σ).toRingEquiv.bijective) (flat_powHom k hd)

end Algebra

section Span

/-- If `R` is finite over `k[t]` through `t ↦ τ`, then `R` is spanned over `k` by the `τʲ e` for
`e` in a finite set. -/
theorem exists_finset_span_pow_mul_eq_top {k R ι : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (τ : R) (h : (eval₂Hom (algebraMap k R) (fun _ : ι ↦ τ)).Finite) :
    ∃ s : Finset R, Submodule.span k {x | ∃ (j : ℕ) (e : R), e ∈ s ∧ x = τ ^ j * e} = ⊤ := by
  algebraize [(eval₂Hom (algebraMap k R) (fun _ : ι ↦ τ) : MvPolynomial ι k →+* R)]
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := MvPolynomial ι k) (M := R)
  refine ⟨s, eq_top_iff.mpr fun y hy0 ↦ ?_⟩
  clear hy0
  set S := Submodule.span k {x | ∃ (j : ℕ) (e : R), e ∈ s ∧ x = τ ^ j * e}
  have hτ : ∀ x ∈ S, τ * x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, e, he, rfl⟩ := hx
      exact Submodule.subset_span ⟨j + 1, e, he, by ring⟩
    | zero => simp
    | add x y _ _ hx hy => simpa [mul_add] using S.add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def, mul_left_comm, ← Algebra.smul_def]
      exact S.smul_mem c hx
  have hφ : ∀ (p : MvPolynomial ι k), ∀ x ∈ S, algebraMap (MvPolynomial ι k) R p * x ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      intro x hx
      have : algebraMap (MvPolynomial ι k) R (C a) * x = a • x := by
        rw [Algebra.smul_def]
        simp [RingHom.algebraMap_toAlgebra]
      rw [this]
      exact S.smul_mem a hx
    | add p q hp hq =>
      intro x hx
      rw [map_add, add_mul]
      exact S.add_mem (hp x hx) (hq x hx)
    | mul_X p i hp =>
      intro x hx
      have : algebraMap (MvPolynomial ι k) R (p * X i) * x =
          algebraMap (MvPolynomial ι k) R p * (τ * x) := by
        simp only [RingHom.algebraMap_toAlgebra, map_mul, coe_eval₂Hom, eval₂_X]
        ring
      rw [this]
      exact hp _ (hτ x hx)
  have hy : y ∈ Submodule.span (MvPolynomial ι k) (s : Set R) := hs ▸ trivial
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨0, x, hx, by ring⟩
  | zero => exact S.zero_mem
  | add x y _ _ hx hy => exact S.add_mem hx hy
  | smul p x _ hx =>
    rw [Algebra.smul_def]
    exact hφ p x hx

/-- Sections over a basic open `D(f)` of an affine open `U` are fractions `r / fⁿ`. -/
lemma exists_mul_pow_eq_of_basicOpen {X : Scheme.{u}} {U W : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(X, U)) (hWU : W ≤ U) (hW : X.basicOpen f = W) (w : Γ(X, W)) :
    ∃ (r : Γ(X, U)) (n : ℕ),
      w * X.presheaf.map (homOfLE hWU).op f ^ n = X.presheaf.map (homOfLE hWU).op r := by
  subst hW
  have := hU.isLocalization_basicOpen f
  obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) w
  refine ⟨r, n, ?_⟩
  simpa [RingHom.algebraMap_toAlgebra] using h

end Span

section BaseOfHom

variable {κ : Type u} [Field κ] {X₀ : Scheme.{u}} (g : X₀ ⟶ Proj (grading Two.{u} κ))

/-- The chart `g⁻¹ D₊(x₀)`. -/
noncomputable abbrev homChart₀ : X₀.Opens := g ⁻¹ᵁ lineChart₀ κ

/-- The chart `g⁻¹ D₊(x₁)`. -/
noncomputable abbrev homChart₁ : X₀.Opens := g ⁻¹ᵁ lineChart₁ κ

/-- The coordinate `g^*(x₁ / x₀)` on `g⁻¹ D₊(x₀)`. -/
noncomputable abbrev homCoord₀ : Γ(X₀, homChart₀ g) := g.app _ (lineCoord₀ κ)

/-- The coordinate `g^*(x₀ / x₁)` on `g⁻¹ D₊(x₁)`. -/
noncomputable abbrev homCoord₁ : Γ(X₀, homChart₁ g) := g.app _ (lineCoord₁ κ)

/-- Pulling back sections commutes with restriction. -/
lemma app_res {Y : Scheme.{u}} {U U' : (Proj (grading Two.{u} κ)).Opens} (h : U ≤ U')
    (x : Γ(Proj (grading Two.{u} κ), U')) (k : Y ⟶ Proj (grading Two.{u} κ)) :
    Y.presheaf.map (homOfLE (k.preimage_mono h)).op (k.app U' x) =
      k.app U ((Proj (grading Two.{u} κ)).presheaf.map (homOfLE h).op x) := by
  have := congrArg (fun φ ↦ φ.hom x) (k.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
  exact this.symm

lemma homCoord_pow_mul (d : ℕ) :
    X₀.presheaf.map (homOfLE inf_le_left : homChart₀ g ⊓ homChart₁ g ⟶ homChart₀ g).op
        (homCoord₀ g ^ d) *
      X₀.presheaf.map (homOfLE inf_le_right : homChart₀ g ⊓ homChart₁ g ⟶ homChart₁ g).op
        (homCoord₁ g ^ d) = 1 := by
  rw [map_pow, map_pow, ← mul_pow]
  have h0 := app_res (κ := κ) (inf_le_left : lineChart₀ κ ⊓ lineChart₁ κ ≤ lineChart₀ κ)
    (lineCoord₀ κ) g
  have h1 := app_res (κ := κ) (inf_le_right : lineChart₀ κ ⊓ lineChart₁ κ ≤ lineChart₁ κ)
    (lineCoord₁ κ) g
  have h2 := congrArg (g.app (lineChart₀ κ ⊓ lineChart₁ κ)).hom (lineCoord_mul κ)
  rw [map_mul, h0.symm, h1.symm, map_one] at h2
  exact (congrArg (· ^ d) h2).trans (one_pow d)

lemma homChart_sup : homChart₀ g ⊔ homChart₁ g = ⊤ := by
  rw [← Scheme.Hom.preimage_sup, lineChart₀_sup_lineChart₁, Scheme.Hom.preimage_top]

lemma basicOpen_homCoord₀ : X₀.basicOpen (homCoord₀ g) = homChart₀ g ⊓ homChart₁ g := by
  rw [← Scheme.preimage_basicOpen, basicOpen_lineCoord₀, Scheme.Hom.preimage_inf]

lemma basicOpen_homCoord₁ : X₀.basicOpen (homCoord₁ g) = homChart₀ g ⊓ homChart₁ g := by
  rw [← Scheme.preimage_basicOpen, basicOpen_lineCoord₁, Scheme.Hom.preimage_inf, inf_comm]

lemma isAffineOpen_homChart₀ [IsAffineHom g] : IsAffineOpen (homChart₀ g) :=
  isAffineOpen_lineChart₀.preimage g

lemma isAffineOpen_homChart₁ [IsAffineHom g] : IsAffineOpen (homChart₁ g) :=
  isAffineOpen_lineChart₁.preimage g

lemma isAffineOpen_homChart_inf [IsAffineHom g] :
    IsAffineOpen (homChart₀ g ⊓ homChart₁ g) := by
  rw [← basicOpen_homCoord₀]
  exact (isAffineOpen_homChart₀ g).basicOpen _

/-- **The Čech `H¹` of `g^* 𝒪(2d)` vanishes for `d ≫ 0`** (Serre vanishing on `ℙ¹` for the finite
morphism `g`): `Γ(U₀ ∩ U₁) = τᵈ Γ(U₁) + σᵈ Γ(U₀)`. -/
theorem exists_pow_H1 [IsFinite g] :
    ∃ d : ℕ, 0 < d ∧ ∀ w : Γ(X₀, homChart₀ g ⊓ homChart₁ g),
      ∃ (r : Γ(X₀, homChart₀ g)) (v : Γ(X₀, homChart₁ g)),
        w = X₀.presheaf.map (homOfLE inf_le_left : homChart₀ g ⊓ homChart₁ g ⟶ _).op
              (homCoord₀ g ^ d) *
            X₀.presheaf.map (homOfLE inf_le_right : homChart₀ g ⊓ homChart₁ g ⟶ _).op v +
          X₀.presheaf.map (homOfLE inf_le_right : homChart₀ g ⊓ homChart₁ g ⟶ _).op
              (homCoord₁ g ^ d) *
            X₀.presheaf.map (homOfLE inf_le_left : homChart₀ g ⊓ homChart₁ g ⟶ _).op r := by
  set U₀ := homChart₀ g
  set U₁ := homChart₁ g
  let : Algebra κ Γ(X₀, U₀) := (lineCOver g U₀).toAlgebra
  let : Algebra κ Γ(X₀, U₁) := (lineCOver g U₁).toAlgebra
  let : Algebra κ Γ(X₀, U₀ ⊓ U₁) := (lineCOver g (U₀ ⊓ U₁)).toAlgebra
  have hres (V W : X₀.Opens) (h : W ≤ V) (a : κ) :
      X₀.presheaf.map (homOfLE h).op (lineCOver g V a) = lineCOver g W a := by
    have := congrArg (fun φ ↦ φ.hom ((Scheme.ΓSpecIso (.of κ)).inv a))
      (Scheme.Hom.appLE_map (g ≫ projToSpec Two.{u} κ)
        (le_top.trans_eq (g ≫ projToSpec Two.{u} κ).preimage_top.symm) (homOfLE h).op)
    exact this
  let ρ : Γ(X₀, U₀) →ₐ[κ] Γ(X₀, U₀ ⊓ U₁) :=
    { (X₀.presheaf.map (homOfLE inf_le_left : U₀ ⊓ U₁ ⟶ U₀).op).hom with
      commutes' := hres _ _ inf_le_left }
  let ρ' : Γ(X₀, U₁) →ₐ[κ] Γ(X₀, U₀ ⊓ U₁) :=
    { (X₀.presheaf.map (homOfLE inf_le_right : U₀ ⊓ U₁ ⟶ U₁).op).hom with
      commutes' := hres _ _ inf_le_right }
  have hρ (x : Γ(X₀, U₀)) : ρ x = X₀.presheaf.map (homOfLE inf_le_left : U₀ ⊓ U₁ ⟶ U₀).op x :=
    rfl
  have hρ' (x : Γ(X₀, U₁)) : ρ' x = X₀.presheaf.map (homOfLE inf_le_right : U₀ ⊓ U₁ ⟶ U₁).op x :=
    rfl
  have hτσ : ρ (homCoord₀ g) * ρ' (homCoord₁ g) = 1 := by
    have := homCoord_pow_mul g 1
    rw [pow_one, pow_one] at this
    exact this
  have hR (w : Γ(X₀, U₀ ⊓ U₁)) : ∃ (r : Γ(X₀, U₀)) (n : ℕ), w * ρ (homCoord₀ g) ^ n = ρ r :=
    exists_mul_pow_eq_of_basicOpen (isAffineOpen_homChart₀ g) (homCoord₀ g) inf_le_left
      (basicOpen_homCoord₀ g) w
  have hS (w : Γ(X₀, U₀ ⊓ U₁)) : ∃ (b : Γ(X₀, U₁)) (n : ℕ), w * ρ' (homCoord₁ g) ^ n = ρ' b :=
    exists_mul_pow_eq_of_basicOpen (isAffineOpen_homChart₁ g) (homCoord₁ g) inf_le_right
      (basicOpen_homCoord₁ g) w
  obtain ⟨s, hs⟩ := exists_finset_span_pow_mul_eq_top (k := κ) (homCoord₀ g)
    (finite_eval₂Hom_app_lineCoord₀ g)
  obtain ⟨N, hN⟩ := exists_forall_eq_add_pow_mul ρ ρ' (homCoord₀ g) (homCoord₁ g) hτσ hR hS s hs
  refine ⟨N + 1, Nat.succ_pos N, fun w ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := hN (2 * (N + 1)) (by omega) (w * ρ (homCoord₀ g) ^ (N + 1))
  refine ⟨a, b, ?_⟩
  rw [map_pow, map_pow, ← hρ, ← hρ, ← hρ', ← hρ']
  have hστ : ρ (homCoord₀ g) ^ (N + 1) * ρ' (homCoord₁ g) ^ (N + 1) = 1 := by
    rw [← mul_pow, hτσ, one_pow]
  calc w = w * (ρ (homCoord₀ g) ^ (N + 1) * ρ' (homCoord₁ g) ^ (N + 1)) := by rw [hστ, mul_one]
    _ = (w * ρ (homCoord₀ g) ^ (N + 1)) * ρ' (homCoord₁ g) ^ (N + 1) := by ring
    _ = (ρ a + ρ (homCoord₀ g) ^ (2 * (N + 1)) * ρ' b) * ρ' (homCoord₁ g) ^ (N + 1) := by
        rw [hab]
    _ = ρ (homCoord₀ g) ^ (N + 1) * ρ' b * (ρ (homCoord₀ g) ^ (N + 1) *
          ρ' (homCoord₁ g) ^ (N + 1)) + ρ' (homCoord₁ g) ^ (N + 1) * ρ a := by ring
    _ = _ := by rw [hστ, mul_one]

end BaseOfHom

section Lift

/-- The one-element type `{j // j ≠ x₀}` of the coordinates of the chart `D₊(x₀)`. -/
@[instance_reducible]
def uniqueNeZero : Unique {j : Two.{u} // j ≠ Two.zero} where
  default := ⟨Two.one, by decide⟩
  uniq := fun ⟨⟨j⟩, hj⟩ ↦ by
    fin_cases j
    · exact absurd rfl hj
    · rfl

/-- The one-element type `{j // j ≠ x₁}` of the coordinates of the chart `D₊(x₁)`. -/
@[instance_reducible]
def uniqueNeOne : Unique {j : Two.{u} // j ≠ Two.one} where
  default := ⟨Two.zero, by decide⟩
  uniq := fun ⟨⟨j⟩, hj⟩ ↦ by
    fin_cases j
    · rfl
    · exact absurd rfl hj

variable {A : Type u} [CommRing A] [IsLocalRing A] {X₀ : Scheme.{u}}
  (f₀ : X₀ ⟶ Spec (.of (ResidueField A))) [Smooth f₀]
  (g : X₀ ⟶ Proj (grading Two.{u} (ResidueField A))) [IsFinite g]

/-- The exponent `d` with `H¹(X₀, g^* 𝒪(2d)) = 0` (`exists_pow_H1`). -/
noncomputable def homExponent : ℕ := (exists_pow_H1 g).choose

lemma homExponent_pos : 0 < homExponent g := (exists_pow_H1 g).choose_spec.1

instance : IsIso (Spec.map (CommRingCat.ofHom (residueEquiv (A := A)).toRingHom)) :=
  isIso_SpecMap_iff.2 residueEquiv.bijective

/-- **The level `0` data of a finite morphism `g : X₀ ⟶ ℙ¹_κ`**: `X₀` over `A / 𝔪 ≅ κ`, the
charts `g⁻¹ D₊(x₀)`, `g⁻¹ D₊(x₁)`, the coordinates `τᵈ`, `σᵈ` (`τ = g^*(x₁ / x₀)`,
`σ = g^*(x₀ / x₁)`), with `d = homExponent g` making the Čech condition hold. -/
noncomputable def baseOfHom : Base (maximalIdeal A) where
  X := X₀
  f := f₀ ≫ Spec.map (CommRingCat.ofHom residueEquiv.toRingHom)
  smooth := inferInstance
  U₀ := homChart₀ g
  U₁ := homChart₁ g
  isAffineOpen_U₀ := isAffineOpen_homChart₀ g
  isAffineOpen_U₁ := isAffineOpen_homChart₁ g
  isAffineOpen_inf := isAffineOpen_homChart_inf g
  sup_eq_top := homChart_sup g
  t := homCoord₀ g ^ homExponent g
  s := homCoord₁ g ^ homExponent g
  mul_eq_one := homCoord_pow_mul g _
  basicOpen_t_le := by
    rw [Scheme.basicOpen_pow _ _ (homExponent_pos g), basicOpen_homCoord₀]
    exact inf_le_right
  basicOpen_s_le := by
    rw [Scheme.basicOpen_pow _ _ (homExponent_pos g), basicOpen_homCoord₁]
    exact inf_le_left
  H1 := (exists_pow_H1 g).choose_spec.2

variable {f₀ g}

omit [IsFinite g] in
lemma cQ_comp_residueEquiv (hg : g ≫ projToSpec Two.{u} (ResidueField A) = f₀) (V : X₀.Opens)
    (a : A ⧸ maximalIdeal A ^ (0 + 1)) :
    cQ (I := maximalIdeal A) (n := 0)
        (f₀ ≫ Spec.map (CommRingCat.ofHom residueEquiv.toRingHom)) V a =
      lineCOver g V (residueEquiv a) := by
  subst hg
  simp only [cQ, lineCOver, RingHom.coe_comp, Function.comp_apply]
  rw [Scheme.Hom.comp_appLE]
  have h := congrArg (fun φ ↦ φ.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (residueEquiv (A := A)).toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  exact congrArg ((g ≫ projToSpec Two.{u} (ResidueField A)).appLE ⊤ V
    (le_top.trans_eq (g ≫ projToSpec Two.{u} (ResidueField A)).preimage_top.symm)).hom h.symm

lemma chartHom_baseOfHom_zero_eq (hg : g ≫ projToSpec Two.{u} (ResidueField A) = f₀) :
    chartHom (I := maximalIdeal A) (n := 0) {j : Two.{u} // j ≠ Two.zero}
        (f₀ ≫ Spec.map (CommRingCat.ofHom residueEquiv.toRingHom)) (homChart₀ g)
        (homCoord₀ g ^ homExponent g) =
      (eval₂Hom (lineCOver g (homChart₀ g)) (fun _ ↦ homCoord₀ g)).comp
        ((MvPolynomial.expand (homExponent g)).toRingHom.comp
          (MvPolynomial.map residueEquiv.toRingHom)) := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
  · refine (eval₂Hom_C _ _ a).trans ((cQ_comp_residueEquiv hg _ a).trans ?_)
    simp
  · refine (eval₂Hom_X' _ _ i).trans ?_
    simp

lemma chartHom_baseOfHom_one_eq (hg : g ≫ projToSpec Two.{u} (ResidueField A) = f₀) :
    chartHom (I := maximalIdeal A) (n := 0) {j : Two.{u} // j ≠ Two.one}
        (f₀ ≫ Spec.map (CommRingCat.ofHom residueEquiv.toRingHom)) (homChart₁ g)
        (homCoord₁ g ^ homExponent g) =
      (eval₂Hom (lineCOver g (homChart₁ g)) (fun _ ↦ homCoord₁ g)).comp
        ((MvPolynomial.expand (homExponent g)).toRingHom.comp
          (MvPolynomial.map residueEquiv.toRingHom)) := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
  · refine (eval₂Hom_C _ _ a).trans ((cQ_comp_residueEquiv hg _ a).trans ?_)
    simp
  · refine (eval₂Hom_X' _ _ i).trans ?_
    simp

/-- The chart homomorphism `(A/𝔪)[t] → Γ(U₀)`, `t ↦ τᵈ`, of `baseOfHom` is finite and flat. -/
theorem chartHom_baseOfHom_zero (hg : g ≫ projToSpec Two.{u} (ResidueField A) = f₀) [Flat g] :
    (chartHom {j : Two.{u} // j ≠ Two.zero} (baseOfHom f₀ g).f (baseOfHom f₀ g).U₀
        (baseOfHom f₀ g).t).Finite ∧
      (chartHom {j : Two.{u} // j ≠ Two.zero} (baseOfHom f₀ g).f (baseOfHom f₀ g).U₀
        (baseOfHom f₀ g).t).Flat := by
  let := uniqueNeZero.{u}
  change (chartHom (I := maximalIdeal A) (n := 0) {j : Two.{u} // j ≠ Two.zero}
      (f₀ ≫ Spec.map (CommRingCat.ofHom residueEquiv.toRingHom)) (homChart₀ g)
      (homCoord₀ g ^ homExponent g)).Finite ∧ (chartHom (I := maximalIdeal A) (n := 0)
        {j : Two.{u} // j ≠ Two.zero} (f₀ ≫ Spec.map (CommRingCat.ofHom residueEquiv.toRingHom))
        (homChart₀ g) (homCoord₀ g ^ homExponent g)).Flat
  rw [chartHom_baseOfHom_zero_eq hg]
  have hM : Function.Bijective (MvPolynomial.map (σ := {j : Two.{u} // j ≠ Two.zero})
      (residueEquiv (A := A)).toRingHom) :=
    ⟨MvPolynomial.map_injective _ residueEquiv.injective,
      MvPolynomial.map_surjective _ residueEquiv.surjective⟩
  exact ⟨(finite_eval₂Hom_app_lineCoord₀ g).comp ((finite_expand _ (homExponent_pos g)).comp
      (RingHom.Finite.of_surjective _ hM.2)),
    RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective hM)
      (flat_expand _ (homExponent_pos g))) (flat_eval₂Hom_app_lineCoord₀ g)⟩

/-- The chart homomorphism `(A/𝔪)[s] → Γ(U₁)`, `s ↦ σᵈ`, of `baseOfHom` is finite and flat. -/
theorem chartHom_baseOfHom_one (hg : g ≫ projToSpec Two.{u} (ResidueField A) = f₀) [Flat g] :
    (chartHom {j : Two.{u} // j ≠ Two.one} (baseOfHom f₀ g).f (baseOfHom f₀ g).U₁
        (baseOfHom f₀ g).s).Finite ∧
      (chartHom {j : Two.{u} // j ≠ Two.one} (baseOfHom f₀ g).f (baseOfHom f₀ g).U₁
        (baseOfHom f₀ g).s).Flat := by
  let := uniqueNeOne.{u}
  change (chartHom (I := maximalIdeal A) (n := 0) {j : Two.{u} // j ≠ Two.one}
      (f₀ ≫ Spec.map (CommRingCat.ofHom residueEquiv.toRingHom)) (homChart₁ g)
      (homCoord₁ g ^ homExponent g)).Finite ∧ (chartHom (I := maximalIdeal A) (n := 0)
        {j : Two.{u} // j ≠ Two.one} (f₀ ≫ Spec.map (CommRingCat.ofHom residueEquiv.toRingHom))
        (homChart₁ g) (homCoord₁ g ^ homExponent g)).Flat
  rw [chartHom_baseOfHom_one_eq hg]
  have hM : Function.Bijective (MvPolynomial.map (σ := {j : Two.{u} // j ≠ Two.one})
      (residueEquiv (A := A)).toRingHom) :=
    ⟨MvPolynomial.map_injective _ residueEquiv.injective,
      MvPolynomial.map_surjective _ residueEquiv.surjective⟩
  exact ⟨(finite_eval₂Hom_app_lineCoord₁ g).comp ((finite_expand _ (homExponent_pos g)).comp
      (RingHom.Finite.of_surjective _ hM.2)),
    RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective hM)
      (flat_expand _ (homExponent_pos g))) (flat_eval₂Hom_app_lineCoord₁ g)⟩

/-- **SGA 1 III.7.4 for a curve with a finite flat morphism to `ℙ¹`**: let `A` be a complete
noetherian local ring with residue field `κ`, `f₀ : X₀ ⟶ Spec κ` smooth of relative dimension `n`,
and `g : X₀ ⟶ ℙ¹_κ` a finite flat `κ`-morphism. Then `X₀` is the closed fibre of a proper
`f : X ⟶ Spec A`, smooth of relative dimension `n`. (SGA's III.7.4 assumes `X₀` proper of
relative dimension `1` instead of the existence of `g`; see
`smoothProperCurveLiftStatement_of_smoothProperCurveFiniteFlatStatement`.) -/
theorem exists_lift_of_finite_flat [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]
    (n : ℕ) [SmoothOfRelativeDimension n f₀] [Flat g]
    (hg : g ≫ projToSpec Two.{u} (ResidueField A) = f₀) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), SmoothOfRelativeDimension n f ∧ IsProper f ∧
      ∃ e : pullback f (Spec.map (CommRingCat.ofHom (residue A))) ≅ X₀,
        e.hom ≫ f₀ = pullback.snd _ _ := by
  exact @exists_lift_of_base A _ _ _ _ (baseOfHom f₀ g) f₀ rfl n ‹_›
    (chartHom_baseOfHom_zero hg).1 (chartHom_baseOfHom_one hg).1 (chartHom_baseOfHom_zero hg).2
    (chartHom_baseOfHom_one hg).2

end Lift

end SGA.SGA1.ExposeIII.CurveLift

namespace SGA.SGA1.ExposeIII

/-- **SGA 1 III.7.4 from the finiteness and flatness of smooth proper curves over `ℙ¹`**: if every
smooth proper curve over a field has a finite flat morphism to `ℙ¹`
(`AlgebraicGeometry.SmoothProperCurveFiniteFlatStatement`), then every smooth proper curve over
the residue field of a complete noetherian local ring lifts to a smooth proper curve over the ring
(`SmoothProperCurveLiftStatement`). -/
theorem smoothProperCurveLiftStatement_of_smoothProperCurveFiniteFlatStatement
    (H : AlgebraicGeometry.SmoothProperCurveFiniteFlatStatement.{u}) :
    SmoothProperCurveLiftStatement.{u} := by
  intro A _ _ _ _ X₀ f₀ _ _
  obtain ⟨g, hfin, hfl, hg⟩ := H (ResidueField A) X₀ f₀
  have : Smooth f₀ := SmoothOfRelativeDimension.smooth 1 f₀
  exact CurveLift.exists_lift_of_finite_flat (g := g) 1 hg

end SGA.SGA1.ExposeIII
