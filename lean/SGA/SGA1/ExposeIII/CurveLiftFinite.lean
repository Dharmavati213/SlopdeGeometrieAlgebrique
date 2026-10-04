/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.CurveLiftSystem
import SGA.SGA1.ExposeIV.LocalCriterion

/-!
# SGA 1, Exposé III, 7.4: the lifted morphisms to `ℙ¹` are finite and flat

Finiteness and flatness of the morphisms `qₙ : Xₙ ⟶ ℙ¹_A ×_A Aₙ` of the lifts
(`SGA.SGA1.ExposeIII.CurveLiftSystem`) reduce to finiteness and flatness at level `0`, by
Nakayama's lemma for the nilpotent ideal `I Aₙ` and by the local flatness criterion for a
nilpotent ideal (SGA 1 IV.5.9, `ExposeIV.flat_iff_flat_and_flat_fibre_of_isNilpotent`): `Γ(Uₙ)`
is flat over `Aₙ` (`Xₙ` is smooth over `Aₙ`) and its reduction `Γ(U₀)` is flat over `A₀[t]`.

This file contains the commutative algebra:
* `finite_of_finite_reduction_of_isNilpotent`: a ring map which is finite modulo a nilpotent ideal
  of the base is finite;
* `flat_of_flat_reduction_of_isNilpotent`: the local flatness criterion in the form used here.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace SGA.SGA1.ExposeIII.CurveLift

section Algebra

variable {Λ P M P₀ M₀ : Type u} [CommRing Λ] [CommRing P] [CommRing M] [CommRing P₀]
  [CommRing M₀] [Algebra Λ P] [Algebra Λ M]

/-- **Nakayama's lemma for a nilpotent ideal, for ring maps**: let `φ : P → M` be a `Λ`-algebra
map, `N ⊆ Λ` a nilpotent ideal, and `πP : P → P₀`, `πM : M → M₀` surjections with kernels
`N P` and `N M`, and `φ₀ : P₀ → M₀` with `φ₀ πP = πM φ`. If `φ₀` is finite, so is `φ`. -/
theorem finite_of_finite_reduction_of_isNilpotent (φ : P →ₐ[Λ] M) (N : Ideal Λ)
    (hN : IsNilpotent N) (πP : P →+* P₀) (πM : M →+* M₀) (hπM : Function.Surjective πM)
    (hkM : RingHom.ker πM = N.map (algebraMap Λ M)) (φ₀ : P₀ →+* M₀)
    (hφ₀ : φ₀.comp πP = πM.comp φ.toRingHom) (hπP : Function.Surjective πP)
    (hfin : φ₀.Finite) : φ.toRingHom.Finite := by
  let := φ.toRingHom.toAlgebra
  let := φ₀.toAlgebra
  obtain ⟨s, hs⟩ := hfin.1
  -- lift the generators
  choose lift hlift using hπM
  let N' : Submodule P M := Submodule.span P (lift '' s)
  have hsup : N' ⊔ (N.map (algebraMap Λ P)) • (⊤ : Submodule P M) = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    have hx : πM x ∈ Submodule.span P₀ (s : Set M₀) := hs ▸ trivial
    -- write `πM x = Σ pᵢ sᵢ`
    obtain ⟨c, hc⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).mp hx
    choose cl hcl using fun z ↦ hπP z
    let y : M := ∑ i ∈ c.support, φ (cl (c i)) * lift i
    have hy : y ∈ N' := Submodule.sum_mem _ fun i hi ↦
      Submodule.smul_mem _ (cl (c i)) (Submodule.subset_span ⟨i, i.2, rfl⟩)
    have hxy : x - y ∈ RingHom.ker πM := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero, ← hc]
      simp only [y, map_sum, map_mul, hlift, Finsupp.linearCombination_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have := congrArg (fun g ↦ g (cl (c i))) hφ₀
      simp only [RingHom.coe_comp, Function.comp_apply, hcl] at this
      rw [Algebra.smul_def]
      change φ₀ (c i) * (i : M₀) = πM (φ (cl (c i))) * (i : M₀)
      rw [show πM (φ (cl (c i))) = φ₀ (c i) from this.symm]
    rw [hkM] at hxy
    have hxy' : x - y ∈ (N.map (algebraMap Λ P)) • (⊤ : Submodule P M) := by
      rw [Ideal.smul_top_eq_map, Ideal.map_map,
        show (algebraMap P M).comp (algebraMap Λ P) = algebraMap Λ M from φ.comp_algebraMap]
      exact (Submodule.restrictScalars_mem _ _ _).mpr hxy
    have := Submodule.add_mem_sup hy hxy'
    rwa [add_sub_cancel] at this
  obtain ⟨n, hn⟩ := hN
  have hpow : (N.map (algebraMap Λ P)) ^ n • (⊤ : Submodule P M) = ⊥ := by
    rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, Submodule.bot_smul]
  have := CohomologyAux.Submodule.eq_top_of_sup_smul_eq_top_of_pow _ N' hsup n hpow
  exact ⟨⟨(lift '' s).toFinite.toFinset, by simpa using this⟩⟩

/-- **The local flatness criterion for a nilpotent ideal, for ring maps** (SGA 1 IV.5.9, nilpotent
case): let `φ : P → M` be a map of flat `Λ`-algebras, `N ⊆ Λ` a nilpotent ideal, `πP : P → P₀`,
`πM : M → M₀` surjections with kernels `N P` and `N M`, and `φ₀ : P₀ → M₀` with
`φ₀ πP = πM φ`. If `φ₀` is flat, so is `φ`. -/
theorem flat_of_flat_reduction_of_isNilpotent (φ : P →ₐ[Λ] M) (N : Ideal Λ)
    (hN : IsNilpotent N) [Module.Flat Λ P] [Module.Flat Λ M] (πP : P →+* P₀)
    (hπP : Function.Surjective πP) (hkP : RingHom.ker πP = N.map (algebraMap Λ P))
    (πM : M →+* M₀) (hπM : Function.Surjective πM)
    (hkM : RingHom.ker πM = N.map (algebraMap Λ M)) (φ₀ : P₀ →+* M₀)
    (hφ₀ : φ₀.comp πP = πM.comp φ.toRingHom) (hfl : φ₀.Flat) : φ.toRingHom.Flat := by
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower Λ P M := IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  change Module.Flat P M
  refine (ExposeIV.flat_iff_flat_and_flat_fibre_of_isNilpotent N hN).mpr ⟨inferInstance, ?_⟩
  set J := N.map (algebraMap Λ P) with hJ
  -- `P / J ≅ P₀`
  let e₁ : P ⧸ J ≃+* P₀ :=
    (Ideal.quotEquivOfEq (hkP.symm)).trans (RingHom.quotientKerEquivOfSurjective hπP)
  have he₁ (p : P) : e₁ (Ideal.Quotient.mk J p) = πP p := rfl
  -- `M / J M ≅ M₀`
  have hJM : J.map (algebraMap P M) = RingHom.ker πM := by
    rw [hkM, hJ, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let e₃ : M ⧸ J.map (algebraMap P M) ≃+* M₀ :=
    (Ideal.quotEquivOfEq hJM).trans (RingHom.quotientKerEquivOfSurjective hπM)
  have he₃ (m : M) : e₃ (Ideal.Quotient.mk _ m) = πM m := rfl
  -- `(P / J) ⊗[P] M ≅ M / J M`
  let e₂ : (P ⧸ J) ⊗[P] M ≃ₐ[P] M ⧸ J.map (algebraMap P M) :=
    (Algebra.TensorProduct.comm P (P ⧸ J) M).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot M J).symm.restrictScalars P)
  have he₂ (q : P ⧸ J) (m : M) : e₂ (q ⊗ₜ m) = q • Ideal.Quotient.mk _ m := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    rfl
  let e : (P ⧸ J) ⊗[P] M ≃+* M₀ := e₂.toRingEquiv.trans e₃
  rw [← RingHom.flat_algebraMap_iff]
  have key : algebraMap (P ⧸ J) ((P ⧸ J) ⊗[P] M) =
      e.symm.toRingHom.comp (φ₀.comp e₁.toRingHom) := by
    ext p
    apply e.injective
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    have hp : φ₀ (πP p) = πM (φ p) := RingHom.congr_fun hφ₀ p
    rw [he₁, hp]
    have h1 : algebraMap (P ⧸ J) ((P ⧸ J) ⊗[P] M) (Ideal.Quotient.mk J p) =
        p • (1 : (P ⧸ J) ⊗[P] M) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
      rfl
    rw [h1]
    change e₃ (e₂ (p • 1)) = _
    rw [map_smul, map_one, Algebra.smul_def, mul_one]
    exact he₃ (algebraMap P M p)
  rw [key]
  exact RingHom.Flat.respectsIso.1 _ _ (RingHom.Flat.respectsIso.2 _ _ hfl)

end Algebra

section Local

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
/-- `f` restricted over an affine open `U` with affine inverse image is finite if `Γ(U) → Γ(f⁻¹ U)`
is finite. -/
lemma isFinite_morphismRestrict_of_appLE {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens}
    (hV : f ⁻¹ᵁ U = V) (hVa : IsAffineOpen V) (h : (f.appLE U V hV.ge).hom.Finite) :
    IsFinite (f ∣_ U) := by
  subst hV
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U) := hVa
  rw [← Scheme.Hom.resLE_eq_morphismRestrict,
    MorphismProperty.arrow_mk_iso_iff @IsFinite.{u} (arrowIsoSpecΓOfIsAffine _),
    IsFinite.SpecMap_iff]
  exact (RingHom.finite_respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U (f ⁻¹ᵁ U) le_rfl)).mpr h

set_option backward.isDefEq.respectTransparency.types false in
/-- `f` restricted over an affine open `U` with affine inverse image is flat if `Γ(U) → Γ(f⁻¹ U)`
is flat. -/
lemma flat_morphismRestrict_of_appLE {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens}
    (hV : f ⁻¹ᵁ U = V) (hVa : IsAffineOpen V) (h : (f.appLE U V hV.ge).hom.Flat) :
    Flat (f ∣_ U) := by
  subst hV
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U) := hVa
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, HasRingHomProperty.iff_of_isAffine (P := @Flat.{u})]
  exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U (f ⁻¹ᵁ U) le_rfl)).mpr h

end Local

section Charts

open MvPolynomial

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- The `Aₙ`-algebra structure on `Γ(X, V)` for a scheme `X` over `Spec Aₙ`. -/
noncomputable abbrev cQ {n : ℕ} {X : Scheme.{u}} (f : X ⟶ Spec (Q I n)) (V : X.Opens) :
    A ⧸ I ^ (n + 1) →+* Γ(X, V) :=
  (f.appLE ⊤ V (le_top.trans_eq f.preimage_top.symm)).hom.comp
    (Scheme.ΓSpecIso (Q I n)).inv.hom

/-- `cQ` is compatible with a morphism `i : X₀ ⟶ X` over `Spec A₀ ⟶ Spec Aₙ`. -/
lemma cQ_comp {n : ℕ} {X X₀ : Scheme.{u}} (f : X ⟶ Spec (Q I n)) (f₀ : X₀ ⟶ Spec (Q I 0))
    (i : X₀ ⟶ X) (hw : i ≫ f = f₀ ≫ ρ I n) {U : X.Opens} {U₀ : X₀.Opens} (hle : U₀ ≤ i ⁻¹ᵁ U)
    (a : A ⧸ I ^ (n + 1)) :
    cQ f₀ U₀ (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ n + 1)) a) =
      i.appLE U U₀ hle (cQ f U a) := by
  have h1 := congrArg (fun g ↦ g.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ n + 1)) :
      A ⧸ I ^ (n + 1) →+* A ⧸ I ^ (0 + 1))))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at h1
  simp only [cQ, RingHom.coe_comp, Function.comp_apply]
  rw [h1]
  have h2 := congrArg (fun g ↦ g.hom ((Scheme.ΓSpecIso (Q I n)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE i f ⊤ U U₀ (le_top.trans_eq f.preimage_top.symm) hle)
  have h3 := congrArg (fun g ↦ g.hom ((Scheme.ΓSpecIso (Q I n)).inv.hom a))
    (Scheme.Hom.comp_appLE f₀ (ρ I n) ⊤ U₀ (le_top.trans_eq (f₀ ≫ ρ I n).preimage_top.symm))
  have h4 := congrArg (fun g ↦ g.hom ((Scheme.ΓSpecIso (Q I n)).inv.hom a))
    (CohomologyAux.appLE_eq_of_eq hw ⊤ U₀ (hle.trans (i.preimage_mono
      (le_top.trans_eq f.preimage_top.symm))) (le_top.trans_eq (f₀ ≫ ρ I n).preimage_top.symm))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2 h3 h4
  rw [h2, h4, h3]
  rfl

/-- The chart homomorphism `Aₙ[t] → Γ(X, V)`, `t ↦ τ` (polynomials in the variables `σ`, all
sent to `τ`; for `ℙ¹`, `σ` has one element). -/
noncomputable def chartHom (σ : Type u) {n : ℕ} {X : Scheme.{u}} (f : X ⟶ Spec (Q I n))
    (V : X.Opens) (τ : Γ(X, V)) : MvPolynomial σ (A ⧸ I ^ (n + 1)) →+* Γ(X, V) :=
  eval₂Hom (cQ f V) (fun _ ↦ τ)

/-- **Finiteness and flatness of the chart homomorphisms lift from level `0`**: let `X` be flat
over `Aₙ` with reduction `X₀ = X ×_{Aₙ} A₀`, `U` an affine open of `X` with inverse image `U₀`,
`τ ∈ Γ(U)` with image `τ₀`. If `A₀[t] → Γ(U₀)`, `t ↦ τ₀`, is finite (resp. flat), so is
`Aₙ[t] → Γ(U)`, `t ↦ τ`. -/
theorem chartHom_finite_flat_of_isPullback (σ : Type u) {n : ℕ} {X X₀ : Scheme.{u}}
    (f : X ⟶ Spec (Q I n)) (f₀ : X₀ ⟶ Spec (Q I 0)) [Flat f] (i : X₀ ⟶ X)
    (hi : IsPullback i f₀ f (ρ I n)) {U : X.Opens} (hU : IsAffineOpen U) {U₀ : X₀.Opens}
    (hpre : i ⁻¹ᵁ U = U₀) (τ : Γ(X, U)) (τ₀ : Γ(X₀, U₀))
    (hτ : i.appLE U U₀ hpre.ge τ = τ₀) :
    ((chartHom σ f₀ U₀ τ₀).Finite → (chartHom σ f U τ).Finite) ∧
      ((chartHom σ f₀ U₀ τ₀).Flat → (chartHom σ f U τ).Flat) := by
  let Λ := A ⧸ I ^ (n + 1)
  let : Algebra Λ Γ(X, U) := (cQ f U).toAlgebra
  let φ : MvPolynomial σ Λ →ₐ[Λ] Γ(X, U) := aeval fun _ ↦ τ
  have hφ : φ.toRingHom = chartHom σ f U τ := rfl
  let fac : Λ →+* A ⧸ I ^ (0 + 1) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : 0 + 1 ≤ n + 1))
  have hfac : Function.Surjective fac := Ideal.Quotient.factor_surjective _
  set N := RingHom.ker fac with hNdef
  have hN : IsNilpotent N := by
    refine ⟨n + 1, ?_⟩
    rw [hNdef, ker_factor_pow, ← Ideal.map_pow, ← pow_mul, Ideal.zero_eq_bot, eq_bot_iff,
      Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_le_pow_right (by omega) hx
  let πP : MvPolynomial σ Λ →+* MvPolynomial σ (A ⧸ I ^ (0 + 1)) := MvPolynomial.map fac
  have hπP : Function.Surjective πP := MvPolynomial.map_surjective _ hfac
  have hkP : RingHom.ker πP = N.map (algebraMap Λ (MvPolynomial σ Λ)) := MvPolynomial.ker_map _
  obtain ⟨hπM, hkM⟩ := appLE_surjective_ker_of_isPullback_specMap (CommRingCat.ofHom fac) hfac
    hi hU hpre
  have hkM' : RingHom.ker (i.appLE U U₀ hpre.ge).hom = N.map (algebraMap Λ Γ(X, U)) := by
    rw [hkM]
    rfl
  -- compatibility with the reductions
  have hcompat : (chartHom σ f₀ U₀ τ₀).comp πP = (i.appLE U U₀ hpre.ge).hom.comp φ.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, πP, map_C, chartHom, coe_eval₂Hom,
        eval₂_C, φ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      change (cQ f₀ U₀) (fac a) = (i.appLE U U₀ hpre.ge) (cQ f U a)
      exact cQ_comp f f₀ i hi.w hpre.ge a
    · simp only [RingHom.coe_comp, Function.comp_apply, πP, map_X, chartHom, coe_eval₂Hom,
        eval₂_X, φ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      exact hτ.symm
  have : Module.Flat Λ Γ(X, U) := by
    have h := HasRingHomProperty.appLE (P := @Flat) f ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
      (le_top.trans_eq f.preimage_top.symm)
    have h' := RingHom.Flat.respectsIso.2
      (f.appLE ⊤ U (le_top.trans_eq f.preimage_top.symm)).hom
      (Scheme.ΓSpecIso (Q I n)).commRingCatIsoToRingEquiv.symm h
    exact h'
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← hφ]
    exact finite_of_finite_reduction_of_isNilpotent φ N hN πP _ hπM hkM' _ hcompat hπP h
  · rw [← hφ]
    exact flat_of_flat_reduction_of_isNilpotent φ N hN πP hπP hkP _ hπM hkM' _ hcompat h

variable {B : Base I}

/-- The chart homomorphisms `Aₙ[t] → Γ(Uₙ,₀)`, `t ↦ tₙ`, of a stage are finite and flat if those of
the level `0` data are. -/
theorem Stage.chartHom₀_finite_flat (σ : Type u) {n : ℕ} (S : Stage B n) :
    ((chartHom σ B.f B.U₀ B.t).Finite → (chartHom σ S.f S.U₀ S.t).Finite) ∧
      ((chartHom σ B.f B.U₀ B.t).Flat → (chartHom σ S.f S.U₀ S.t).Flat) := by
  have := S.smooth
  exact chartHom_finite_flat_of_isPullback σ S.f B.f S.i S.isPullback S.isAffineOpen_U₀
    S.preimage_U₀ S.t B.t S.t_eq

/-- The chart homomorphisms `Aₙ[s] → Γ(Uₙ,₁)`, `s ↦ sₙ`, of a stage are finite and flat if those of
the level `0` data are. -/
theorem Stage.chartHom₁_finite_flat (σ : Type u) {n : ℕ} (S : Stage B n) :
    ((chartHom σ B.f B.U₁ B.s).Finite → (chartHom σ S.f S.U₁ S.s).Finite) ∧
      ((chartHom σ B.f B.U₁ B.s).Flat → (chartHom σ S.f S.U₁ S.s).Flat) := by
  have := S.smooth
  exact chartHom_finite_flat_of_isPullback σ S.f B.f S.i S.isPullback S.isAffineOpen_U₁
    S.preimage_U₁ S.s B.s S.s_eq

end Charts

section FiniteToProj

open MvPolynomial AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.AmpleLift

variable {A : Type u} [CommRing A] {I : Ideal A} {B : Base I}

lemma Stage.chartData_c₀_eq {n : ℕ} (S : Stage B n) :
    S.chartData.c₀ = (cQ S.f S.U₀).comp (Ideal.Quotient.mk (I ^ (n + 1))) := rfl

lemma Stage.chartData_c₁_eq {n : ℕ} (S : Stage B n) :
    S.chartData.c₁ = (cQ S.f S.U₁).comp (Ideal.Quotient.mk (I ^ (n + 1))) := rfl

lemma eval₂Hom_comp_map_mk (σ : Type u) {n : ℕ} {X : Scheme.{u}} (f : X ⟶ Spec (Q I n))
    (V : X.Opens) (τ : Γ(X, V)) :
    eval₂Hom ((cQ f V).comp (Ideal.Quotient.mk (I ^ (n + 1)))) (fun _ : σ ↦ τ) =
      (chartHom σ f V τ).comp (MvPolynomial.map (Ideal.Quotient.mk (I ^ (n + 1)))) := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun j ↦ ?_) <;> simp [chartHom]

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism `Xₙ ⟶ ℙ¹_A` of a stage is finite if the level `0` chart homomorphisms are. -/
theorem Stage.isFinite_toProj {n : ℕ} (S : Stage B n)
    (h₀ : (chartHom {j : Two.{u} // j ≠ Two.zero} B.f B.U₀ B.t).Finite)
    (h₁ : (chartHom {j : Two.{u} // j ≠ Two.one} B.f B.U₁ B.s).Finite) :
    IsFinite S.toProj := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun i : Two.{u} ↦ Proj.basicOpen (grading Two.{u} A) (MvPolynomial.X i))
    (iSup_basicOpen_X Two.{u} A)
    fun i ↦ ?_
  obtain ⟨i⟩ := i
  fin_cases i
  · refine isFinite_morphismRestrict_of_appLE S.toProj
      (Proj.isAffineOpen_basicOpen _ _ (X_mem_grading Two.zero) one_pos)
      S.chartData.toProj_preimage_basicOpen_zero S.isAffineOpen_U₀ ?_
    have hiso := (Proj.basicOpenIsoAway (grading Two.{u} A) (MvPolynomial.X Two.zero)
      (X_mem_grading Two.zero) one_pos).isIso_hom
    rw [Proj.basicOpenIsoAway_hom] at hiso
    rw [← RingHom.finite_respectsIso.cancel_left_isIso
      (Proj.awayToSection _ (MvPolynomial.X Two.zero)), ← CommRingCat.hom_comp]
    change (Proj.awayToSection (grading Two.{u} A) (MvPolynomial.X Two.zero) ≫
      S.chartData.toProj.appLE _ S.chartData.U₀ _).hom.Finite
    rw [TwoChartData.awayToSection_comp_appLE_zero, CommRingCat.hom_ofHom]
    refine RingHom.finite_respectsIso.2 _ _ ?_
    have hfin : ((chartHom {j : Two.{u} // j ≠ Two.zero} S.f S.U₀ S.t).comp
        (MvPolynomial.map (Ideal.Quotient.mk (I ^ (n + 1))))).Finite :=
      RingHom.Finite.comp ((S.chartHom₀_finite_flat _).1 h₀)
        (RingHom.Finite.of_surjective _ (MvPolynomial.map_surjective _
          Ideal.Quotient.mk_surjective))
    rw [← eval₂Hom_comp_map_mk] at hfin
    exact hfin
  · refine isFinite_morphismRestrict_of_appLE S.toProj
      (Proj.isAffineOpen_basicOpen _ _ (X_mem_grading Two.one) one_pos)
      S.chartData.toProj_preimage_basicOpen_one S.isAffineOpen_U₁ ?_
    have hiso := (Proj.basicOpenIsoAway (grading Two.{u} A) (MvPolynomial.X Two.one)
      (X_mem_grading Two.one) one_pos).isIso_hom
    rw [Proj.basicOpenIsoAway_hom] at hiso
    rw [← RingHom.finite_respectsIso.cancel_left_isIso
      (Proj.awayToSection _ (MvPolynomial.X Two.one)), ← CommRingCat.hom_comp]
    change (Proj.awayToSection (grading Two.{u} A) (MvPolynomial.X Two.one) ≫
      S.chartData.toProj.appLE _ S.chartData.U₁ _).hom.Finite
    rw [TwoChartData.awayToSection_comp_appLE_one, CommRingCat.hom_ofHom]
    refine RingHom.finite_respectsIso.2 _ _ ?_
    have hfin : ((chartHom {j : Two.{u} // j ≠ Two.one} S.f S.U₁ S.s).comp
        (MvPolynomial.map (Ideal.Quotient.mk (I ^ (n + 1))))).Finite :=
      RingHom.Finite.comp ((S.chartHom₁_finite_flat _).1 h₁)
        (RingHom.Finite.of_surjective _ (MvPolynomial.map_surjective _
          Ideal.Quotient.mk_surjective))
    rw [← eval₂Hom_comp_map_mk] at hfin
    exact hfin

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism `qₙ : Xₙ ⟶ ℙ¹_A ×_A Aₙ` of a stage is finite if the level `0` chart homomorphisms
are. -/
theorem Stage.isFinite_thickeningHom {n : ℕ} (S : Stage B n)
    (h₀ : (chartHom {j : Two.{u} // j ≠ Two.zero} B.f B.U₀ B.t).Finite)
    (h₁ : (chartHom {j : Two.{u} // j ≠ Two.one} B.f B.U₁ B.s).Finite) :
    IsFinite S.thickeningHom := by
  have h := S.isFinite_toProj h₀ h₁
  rw [← S.thickeningHom_ι] at h
  exact IsFinite.of_comp S.thickeningHom (thickening.ι (projToSpec Two.{u} A) I n)

end FiniteToProj

end SGA.SGA1.ExposeIII.CurveLift
