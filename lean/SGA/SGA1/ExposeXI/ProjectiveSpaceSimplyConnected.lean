/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import SGA.SGA1.ExposeXI.BirationalInvariance
import SGA.SGA1.ExposeXI.ProjectiveLinePower
import SGA.SGA1.ExposeXI.ProjectiveSpace

/-!
# Projective space is simply connected (XI.1.1)

Let `k` be algebraically closed. A connected étale covering of `Proj k[σ]` (`σ` finite with two
distinct elements) is an isomorphism (`isIso_of_isFinite_of_etale`), by restricting it to the
generic line through a point (outline in `SGA.SGA1.ExposeXI.ProjectiveSpace`; the algebraic core is
`ringHom_eq_of_line`). This proves XI.1.1 without the genus formula or X.3.4:

* `isSimplyConnected_projectiveSpace`, `projectiveSpaceSimplyConnectedStatement`: `ℙʳ_k` is simply
  connected for every `r`;
* `isSimplyConnected_pullback_toSpec`, `isSimplyConnected_prod`: with the Künneth formula X.1.7,
  `ℙʳ ×ₖ T` for `T` simply connected, and products of projective spaces, are simply connected;
* `isSimplyConnected_of_partialIso_projectiveSpace`: XI.1.2 for a proper regular variety with a
  given birational map to `ℙʳ`, by X.3.4 (`ExposeX.birationalInvariance`); `ℙʳ` is regular
  (`isRegularScheme_projectiveSpace`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
  AlgebraicGeometry.ProjectiveSpace TensorProduct LaurentPolynomial

namespace SGA.SGA1.ExposeXI.ProjectiveSpace

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Algebra

open Polynomial GenericLine

variable {F : Type*} [Field F] {AN AS ANS CN CS CNS : Type*} [CommRing AN] [CommRing AS]
  [CommRing ANS] [CommRing CN] [CommRing CS] [CommRing CNS]
  [Algebra AN CN] [Algebra AS CS] [Algebra ANS CNS] [Algebra AN ANS] [Algebra AS ANS]
  [Algebra CN CNS] [Algebra CS CNS] [Algebra AN CNS] [Algebra AS CNS]
  [IsScalarTower AN ANS CNS] [IsScalarTower AS ANS CNS] [IsScalarTower AN CN CNS]
  [IsScalarTower AS CS CNS]

/-- XI.1.1, the generic line argument in algebraic form. Let `Y` be finite étale over a scheme
covered by `Spec A_N`, `Spec A_S` with intersection `Spec A_{NS}`,
`A_{NS} = A_N[1/z_N] = A_S[1/z_S]`, with rings of `Y` given by `C_N`, `C_S`, `C_{NS}`. Let
`A_N → F[t]`, `A_S → F[u]`, `A_{NS} → F[t, t⁻¹]` be a line (compatible with `u = t⁻¹`,
`z_N ↦ t`, `z_S ↦ u`) such that `F[u]` is a localization of `A_S`, and let `C_S` be a domain.
Then two rational points of `C_N` over `t = 0` agree. -/
theorem ringHom_eq_of_line [Algebra.Etale AN CN] [Algebra.Etale AS CS] [Module.Finite AN CN]
    [Module.Finite AS CS] [IsDomain CS] (lN : AN →+* F[X]) (lS : AS →+* F[X])
    (lNS : ANS →+* F[T;T⁻¹]) (hlN : lNS.comp (algebraMap AN ANS) = toLaurent.comp lN)
    (hlS : lNS.comp (algebraMap AS ANS) = (toLaurentInv F).toRingHom.comp lS)
    (zN : AN) (zS : AS) [IsLocalization.Away zN ANS] [IsLocalization.Away zS ANS]
    [IsLocalization.Away (algebraMap AN CN zN) CNS] [IsLocalization.Away (algebraMap AS CS zS) CNS]
    (hzN : lN zN = Polynomial.X) (hzS : lS zS = Polynomial.X)
    (hS : letI := lS.toAlgebra; ∃ M : Submonoid AS, IsLocalization M F[X])
    (c₁ c₂ : CN →+* F) (hc₁ : ∀ a, c₁ (algebraMap AN CN a) = (lN a).eval 0)
    (hc₂ : ∀ a, c₂ (algebraMap AN CN a) = (lN a).eval 0) : c₁ = c₂ := by
  classical
  let _ : Algebra AN F[X] := lN.toAlgebra
  let _ : Algebra AS F[X] := lS.toAlgebra
  let _ : Algebra ANS F[T;T⁻¹] := lNS.toAlgebra
  let _ : Algebra AN F[T;T⁻¹] := (lNS.comp (algebraMap AN ANS)).toAlgebra
  let _ : Algebra AS F[T;T⁻¹] := (lNS.comp (algebraMap AS ANS)).toAlgebra
  have : IsScalarTower AN ANS F[T;T⁻¹] := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower AS ANS F[T;T⁻¹] := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower AN F[X] F[T;T⁻¹] := IsScalarTower.of_algebraMap_eq fun x ↦
    RingHom.congr_fun hlN x
  -- `B₀ = F[t] ⊗ C_N` and `W = F[t, t⁻¹] ⊗ C_{NS}` is `B₀[1/t]`.
  have : IsLocalization (Algebra.algebraMapSubmonoid CN (Submonoid.powers zN)) CNS := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  have : IsLocalization (Algebra.algebraMapSubmonoid F[X] (Submonoid.powers zN)) F[T;T⁻¹] := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    change IsLocalization.Away (lN zN) _
    rw [hzN]
    infer_instance
  let φN := baseChangeMap AN CN F[X] (A' := ANS) (C' := CNS) (P' := F[T;T⁻¹]) zN
  let _ : Algebra (F[X] ⊗[AN] CN) (F[T;T⁻¹] ⊗[ANS] CNS) := φN.toAlgebra
  have hW₀ : IsLocalization (Algebra.algebraMapSubmonoid (F[X] ⊗[AN] CN)
      (Submonoid.powers (Polynomial.X : F[X]))) (F[T;T⁻¹] ⊗[ANS] CNS) := by
    have h := isLocalization_baseChangeMap (A := AN) (C := CN) (P := F[X])
      (A' := ANS) (C' := CNS) (P' := F[T;T⁻¹]) zN
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at h ⊢
    rwa [IsScalarTower.algebraMap_apply AN F[X] (F[X] ⊗[AN] CN), RingHom.algebraMap_toAlgebra,
      hzN] at h
  have h₀ : ∀ x : F[X], algebraMap (F[X] ⊗[AN] CN) (F[T;T⁻¹] ⊗[ANS] CNS)
      (algebraMap F[X] _ x) = algebraMap F[T;T⁻¹] _ (toLaurent x) :=
    fun x ↦ baseChangeMap_algebraMap_left (A := AN) (C := CN) (P := F[X])
      (A' := ANS) (C' := CNS) (P' := F[T;T⁻¹]) zN x
  -- `B₁ = F[u] ⊗ C_S`, with `W = B₁[1/u]` over `u ↦ t⁻¹`.
  obtain ⟨φS, h₁, hW₁⟩ : ∃ φS : F[X] ⊗[AS] CS →+* F[T;T⁻¹] ⊗[ANS] CNS,
      (∀ x, φS (algebraMap F[X] _ x) = algebraMap F[T;T⁻¹] _ (toLaurentInv F x)) ∧
      letI := φS.toAlgebra
      IsLocalization (Algebra.algebraMapSubmonoid (F[X] ⊗[AS] CS)
        (Submonoid.powers (Polynomial.X : F[X]))) (F[T;T⁻¹] ⊗[ANS] CNS) := by
    let _ : Algebra F[X] F[T;T⁻¹] := (toLaurentInv F).toRingHom.toAlgebra
    have : IsScalarTower AS F[X] F[T;T⁻¹] := IsScalarTower.of_algebraMap_eq fun x ↦
      RingHom.congr_fun hlS x
    have : IsLocalization (Algebra.algebraMapSubmonoid CS (Submonoid.powers zS)) CNS := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      infer_instance
    have : IsLocalization (Algebra.algebraMapSubmonoid F[X] (Submonoid.powers zS))
        F[T;T⁻¹] := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      change IsLocalization.Away (lS zS) _
      rw [hzS]
      exact isLocalization_toLaurentInv F
    let φS := baseChangeMap AS CS F[X] (A' := ANS) (C' := CNS) (P' := F[T;T⁻¹]) zS
    refine ⟨φS, fun x ↦ baseChangeMap_algebraMap_left zS x, ?_⟩
    let _ := φS.toAlgebra
    have h := isLocalization_baseChangeMap (A := AS) (C := CS) (P := F[X])
      (A' := ANS) (C' := CNS) (P' := F[T;T⁻¹]) zS
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at h ⊢
    rwa [IsScalarTower.algebraMap_apply AS F[X] (F[X] ⊗[AS] CS), RingHom.algebraMap_toAlgebra,
      hzS] at h
  let _ := φS.toAlgebra
  -- `W` is a localization of the domain `C_S`.
  obtain ⟨M, hM⟩ := hS
  have hW : Nontrivial (F[T;T⁻¹] ⊗[ANS] CNS) → IsDomain (F[T;T⁻¹] ⊗[ANS] CNS) := fun _ ↦ by
    have : Nontrivial (F[X] ⊗[AS] CS) :=
      (algebraMap (F[X] ⊗[AS] CS) (F[T;T⁻¹] ⊗[ANS] CNS)).domain_nontrivial
    have : IsLocalization (Algebra.algebraMapSubmonoid CS M) (F[X] ⊗[AS] CS) :=
      isLocalization_tensorProduct_right AS CS F[X] M
    have : IsDomain (F[X] ⊗[AS] CS) := isDomain_of_isLocalization (Algebra.algebraMapSubmonoid CS M)
    exact isDomain_of_isLocalization (Algebra.algebraMapSubmonoid (F[X] ⊗[AS] CS)
      (Submonoid.powers (Polynomial.X : F[X])))
  -- The rational points `B₀ → F` over `t = 0`.
  have hχ : ∀ c : CN →+* F, (∀ a, c (algebraMap AN CN a) = (lN a).eval 0) →
      ∃ χ : F[X] ⊗[AN] CN →+* F, (∀ x, χ (algebraMap F[X] (F[X] ⊗[AN] CN) x) = x.eval 0) ∧
        ∀ y, χ (1 ⊗ₜ y) = c y := by
    intro c hc
    let _ : Algebra AN F := ((evalRingHom 0).comp lN).toAlgebra
    have : IsScalarTower AN AN F[X] := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have : IsScalarTower AN AN F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let ev : F[X] →ₐ[AN] F := { evalRingHom 0 with commutes' := fun _ ↦ rfl }
    let g : CN →ₐ[AN] F := { c with commutes' := hc }
    let χ := Algebra.TensorProduct.lift ev g fun _ _ ↦ Commute.all _ _
    refine ⟨χ.toRingHom, fun x ↦ ?_, fun y ↦ ?_⟩
    · exact (Algebra.TensorProduct.lift_tmul ev g _ x 1).trans (by rw [map_one, mul_one]; rfl)
    · exact (Algebra.TensorProduct.lift_tmul ev g _ 1 y).trans (by rw [map_one, one_mul]; rfl)
  obtain ⟨χ₁, hχ₁, hχ₁c⟩ := hχ c₁ hc₁
  obtain ⟨χ₂, hχ₂, hχ₂c⟩ := hχ c₂ hc₂
  have := ringHom_eq_of_isDomain_of_isLocalization h₀ h₁ hW₀ hW₁ hW χ₁ χ₂ hχ₁ hχ₂
  ext y
  rw [← hχ₁c y, ← hχ₂c y, this]

end Algebra

section Geometry

variable {k : Type u} [Field k] [IsAlgClosed k] {σ : Type u} [Finite σ]
  {n s : σ} {Y : Scheme.{u}} (p : Y ⟶ Proj (grading σ k))

set_option hygiene false in
/-- `Γ(D₊(xₙ)) = k[σ]_(xₙ)`. -/
local notation "𝔸ₙ" => Away (grading σ k) (X n)
set_option hygiene false in
/-- `Γ(D₊(x_s)) = k[σ]_(x_s)`. -/
local notation "𝔸ₛ" => Away (grading σ k) (X s)
set_option hygiene false in
/-- `Γ(D₊(xₙ x_s)) = k[σ]_(xₙ x_s)`. -/
local notation "𝔸ₙₛ" => Away (grading σ k) (X n * X s)
set_option hygiene false in
/-- `Γ(Y, p⁻¹ D₊(xₙ))`. -/
local notation "ℂₙ" => Γ(Y, p ⁻¹ᵁ Proj.basicOpen (grading σ k) (X n))
set_option hygiene false in
/-- `Γ(Y, p⁻¹ D₊(x_s))`. -/
local notation "ℂₛ" => Γ(Y, p ⁻¹ᵁ Proj.basicOpen (grading σ k) (X s))
set_option hygiene false in
/-- `Γ(Y, p⁻¹ D₊(xₙ x_s))`. -/
local notation "ℂₙₛ" => Γ(Y, p ⁻¹ᵁ Proj.basicOpen (grading σ k) (X n * X s))

open GenericLine in
/-- XI.1.1, the key step: a connected étale covering `p : Y ⟶ Proj k[σ]` (`σ` with two distinct
elements `n ≠ s`) is an isomorphism. The points of `Y` over `e = (xₙ = 1, xⱼ = 0)` are unique by
`ringHom_eq_of_line` applied to the generic line through `e`. -/
theorem isIso_of_isFinite_of_etale (hns : n ≠ s) [IsFinite p] [Etale p] [ConnectedSpace Y] :
    IsIso p := by
  classical
  have : Nonempty σ := ⟨n⟩
  have : IsIntegral Y := isIntegral_of_isFinite_of_etale p
  have hsurj := surjective_of_isFinite_of_etale p
  -- The charts `D₊(xₙ)`, `D₊(x_s)`, `D₊(xₙ x_s)` and the corresponding rings of `Y`.
  have hN := X_mem_grading (R := k) n
  have hS := X_mem_grading (R := k) s
  have hxN : (X n * X s : MvPolynomial σ k) = X n * X s := rfl
  have hxS : (X n * X s : MvPolynomial σ k) = X s * X n := mul_comm _ _
  let _ : Algebra 𝔸ₙ ℂₙ := (chartMap p (X n)).toAlgebra
  let _ : Algebra 𝔸ₛ ℂₛ := (chartMap p (X s)).toAlgebra
  let _ : Algebra 𝔸ₙₛ ℂₙₛ := (chartMap p (X n * X s)).toAlgebra
  let _ : Algebra 𝔸ₙ 𝔸ₙₛ := (awayMap (grading σ k) hS hxN).toAlgebra
  let _ : Algebra 𝔸ₛ 𝔸ₙₛ := (awayMap (grading σ k) hN hxS).toAlgebra
  let _ : Algebra ℂₙ ℂₙₛ :=
    (chartRes p (X n) (X n * X s) (Proj.basicOpen_mono _ _ _ ⟨_, hxN⟩)).toAlgebra
  let _ : Algebra ℂₛ ℂₙₛ :=
    (chartRes p (X s) (X n * X s) (Proj.basicOpen_mono _ _ _ ⟨_, hxS⟩)).toAlgebra
  let _ : Algebra 𝔸ₙ ℂₙₛ :=
    ((chartMap p (X n * X s)).comp (awayMap (grading σ k) hS hxN)).toAlgebra
  let _ : Algebra 𝔸ₛ ℂₙₛ :=
    ((chartMap p (X n * X s)).comp (awayMap (grading σ k) hN hxS)).toAlgebra
  have : IsScalarTower 𝔸ₙ 𝔸ₙₛ ℂₙₛ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower 𝔸ₛ 𝔸ₙₛ ℂₙₛ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower 𝔸ₙ ℂₙ ℂₙₛ := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.congr_fun (chartRes_comp_chartMap p hS hxN) x).symm
  have : IsScalarTower 𝔸ₛ ℂₛ ℂₙₛ := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.congr_fun (chartRes_comp_chartMap p hN hxS) x).symm
  have : Algebra.Etale 𝔸ₙ ℂₙ := chartMap_etale p n
  have : Algebra.Etale 𝔸ₛ ℂₛ := chartMap_etale p s
  have : Module.Finite 𝔸ₙ ℂₙ := chartMap_finite p n
  have : Module.Finite 𝔸ₛ ℂₛ := chartMap_finite p s
  have : IsLocalization.Away (Away.isLocalizationElem hN hS) 𝔸ₙₛ :=
    Away.isLocalization_mul hN hS hxN one_ne_zero
  have : IsLocalization.Away (Away.isLocalizationElem hS hN) 𝔸ₙₛ :=
    Away.isLocalization_mul hS hN hxS one_ne_zero
  have : IsLocalization.Away (algebraMap 𝔸ₙ ℂₙ (Away.isLocalizationElem hN hS)) ℂₙₛ :=
    isLocalization_chartRes p n s hxN
  have : IsLocalization.Away (algebraMap 𝔸ₛ ℂₛ (Away.isLocalizationElem hS hN)) ℂₙₛ :=
    isLocalization_chartRes p s n hxS
  -- `Γ(Y, p⁻¹ D₊(x_s))` is a domain.
  have : Nonempty (p ⁻¹ᵁ Proj.basicOpen (grading σ k) (X s)) := by
    have : Nontrivial 𝔸ₛ :=
      (awayEquiv s (rfl : (X s : MvPolynomial σ k) = X s)).toEquiv.nontrivial
    obtain ⟨y, hy⟩ := hsurj (Proj.awayι (grading σ k) (X s) hS one_pos
      (Classical.arbitrary (Spec (.of 𝔸ₛ))))
    refine ⟨⟨y, ?_⟩⟩
    change p y ∈ Proj.basicOpen (grading σ k) (X s)
    rw [hy, ← Proj.opensRange_awayι _ _ hS one_pos]
    exact ⟨_, rfl⟩
  -- The point `e = (xₙ = 1, xⱼ = 0)` and the points of `Y` over it.
  have hU := isAffineOpen_basicOpen_X (k := k) n
  have hV : IsAffineOpen (p ⁻¹ᵁ Proj.basicOpen (grading σ k) (X n)) := hU.preimage p
  let εΓ : Γ(Proj (grading σ k), Proj.basicOpen (grading σ k) (X n)) →+* k :=
    (pointN k n).comp (Proj.basicOpenIsoAway (grading σ k) (X n) hN one_pos).inv.hom
  let e : Spec (.of k) ⟶ Proj (grading σ k) := Spec.map (CommRingCat.ofHom εΓ) ≫ hU.fromSpec
  have hεΓ : εΓ.comp (Proj.awayToSection (grading σ k) (X n)).hom = pointN k n := by
    refine RingHom.ext fun x ↦ ?_
    have h := (Proj.basicOpenIsoAway (grading σ k) (X n) hN one_pos).hom_inv_id
    rw [Proj.basicOpenIsoAway_hom] at h
    exact congrArg (pointN k n) (congrArg (fun φ : CommRingCat.of 𝔸ₙ ⟶ _ ↦ φ.hom x) h)
  have hpt : ∀ y : Spec (.of k) ⟶ Y, y ≫ p = e → ∃ c : ℂₙ →+* k,
      c.comp (chartMap p (X n)) = pointN k n ∧
        y = Spec.map (CommRingCat.ofHom c) ≫ hV.fromSpec := by
    intro y hy
    have h : ⊤ ≤ y ⁻¹ᵁ (p ⁻¹ᵁ Proj.basicOpen (grading σ k) (X n)) := by
      change ⊤ ≤ (y ≫ p) ⁻¹ᵁ Proj.basicOpen (grading σ k) (X n)
      rw [hy]
      change ⊤ ≤ Spec.map (CommRingCat.ofHom εΓ) ⁻¹ᵁ
        (hU.fromSpec ⁻¹ᵁ Proj.basicOpen (grading σ k) (X n))
      rw [hU.fromSpec_preimage_self]
      exact le_rfl
    refine ⟨(y.appLE _ ⊤ h ≫ (Scheme.ΓSpecIso _).hom).hom, ?_, ?_⟩
    · have H : ∀ (z : Spec (.of k) ⟶ Proj (grading σ k)) (_ : z = e)
          (h' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen (grading σ k) (X n)),
          z.appLE _ ⊤ h' ≫ (Scheme.ΓSpecIso _).hom = CommRingCat.ofHom εΓ := by
        rintro z rfl h'
        exact appLE_SpecMap_fromSpec hU _ h'
      have H' := (congrArg (· ≫ (Scheme.ΓSpecIso _).hom) (Scheme.Hom.comp_appLE y p
        (Proj.basicOpen (grading σ k) (X n)) ⊤ h)).symm.trans (H (y ≫ p) hy h)
      rw [Category.assoc] at H'
      rw [← hεΓ]
      exact RingHom.ext fun x ↦
        congrArg (fun φ ↦ φ.hom ((Proj.awayToSection (grading σ k) (X n)).hom x)) H'
    · have := eq_SpecMap_fromSpec hV y h
      rwa [CommRingCat.ofHom_hom]
  -- The points of `Y` over `e` agree: the generic line through `e`.
  refine isIso_of_forall_eq p k e fun y₁ y₂ h₁ h₂ ↦ ?_
  obtain ⟨c₁, hc₁, rfl⟩ := hpt y₁ h₁
  obtain ⟨c₂, hc₂, rfl⟩ := hpt y₂ h₂
  suffices c₁ = c₂ by rw [this]
  have hc : ∀ c : ℂₙ →+* k, c.comp (chartMap p (X n)) = pointN k n →
      ∀ a, ((algebraMap k (LineField k n s)).comp c) (algebraMap 𝔸ₙ ℂₙ a) =
        (lineN k n s a).eval 0 := by
    intro c hc a
    have h1 := RingHom.congr_fun hc a
    have h2 := RingHom.congr_fun (evalZero_comp_lineN (k := k) (n := n) (s := s)) a
    simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom] at h1 h2 ⊢
    rw [h2, ← h1]
    rfl
  have := ringHom_eq_of_line (F := LineField k n s) (AN := 𝔸ₙ) (AS := 𝔸ₛ) (ANS := 𝔸ₙₛ)
    (CN := ℂₙ) (CS := ℂₛ) (CNS := ℂₙₛ) (lineN k n s) (lineS k n s hns)
    (lineNS k n s hns) (lineNS_comp_awayMapN hns) (lineNS_comp_awayMapS hns)
    (Away.isLocalizationElem hN hS) (Away.isLocalizationElem hS hN)
    (lineN_isLocalizationElem hns) (lineS_isLocalizationElem hns) (isLocalization_lineS hns)
    _ _ (hc c₁ hc₁) (hc c₂ hc₂)
  ext a
  exact (algebraMap k (LineField k n s)).injective (RingHom.congr_fun this a)

end Geometry

section Main

/-- Simple connectedness is invariant under isomorphism. -/
lemma isSimplyConnected_of_iso {X X' : Scheme.{u}} (e : X ≅ X') (h : IsSimplyConnected X) :
    IsSimplyConnected X' := by
  have := h.1
  refine ⟨(Scheme.homeoOfIso e).surjective.connectedSpace (Scheme.homeoOfIso e).continuous,
    fun Y f _ _ hY ↦ ?_⟩
  have : IsIso (f ≫ e.inv) := h.2 (f ≫ e.inv) hY
  have : IsIso ((f ≫ e.inv) ≫ e.hom) := inferInstance
  simpa using this

variable (k : Type u) [Field k]

/-- XI.1.1 for `r = 0`: `Proj k[x] = Spec k` is simply connected (`k` separably closed). -/
theorem isSimplyConnected_proj_of_unique [IsSepClosed k] (σ : Type u) [Unique σ] :
    IsSimplyConnected (Proj (grading σ k)) := by
  let i : σ := default
  have hi := X_mem_grading (R := k) i
  have : IsIso (Proj.awayι (grading σ k) (X i) hi one_pos) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    rw [Proj.opensRange_awayι, ← iSup_basicOpen_X σ k]
    exact le_antisymm (le_iSup (fun j ↦ Proj.basicOpen (grading σ k) (X j)) i)
      (iSup_le fun j ↦ by rw [Subsingleton.elim j i])
  have : IsEmpty {j : σ // j ≠ i} := ⟨fun j ↦ j.2 (Subsingleton.elim _ _)⟩
  let e : CommRingCat.of (Away (grading σ k) (X i)) ≅ CommRingCat.of k :=
    ((awayEquiv i rfl).trans (MvPolynomial.isEmptyRingEquiv k _)).toCommRingCatIso
  exact isSimplyConnected_of_iso (Scheme.Spec.mapIso e.op ≪≫
    asIso (Proj.awayι (grading σ k) (X i) hi one_pos)) (isSimplyConnected_spec_of_isSepClosed k)

/-- XI.1.1: `Proj k[σ]` is simply connected (`σ` finite with at least two elements, `k`
algebraically closed). -/
theorem isSimplyConnected_proj [IsAlgClosed k] (σ : Type u) [Finite σ] [Nontrivial σ] :
    IsSimplyConnected (Proj (grading σ k)) := by
  obtain ⟨n, s, hns⟩ := exists_pair_ne σ
  exact ⟨inferInstance, fun _ f _ _ _ ↦ isIso_of_isFinite_of_etale f hns⟩

/-- XI.1.1: projective space `ℙʳ_k` over an algebraically closed field is simply connected. -/
theorem isSimplyConnected_projectiveSpace [IsAlgClosed k] (r : ℕ) :
    IsSimplyConnected (projectiveSpace k r) := by
  let e := projRenameIso (R := k) (Equiv.ulift.{u}.symm : Fin (r + 1) ≃ ULift (Fin (r + 1)))
  rcases r with _ | r
  · have : Unique (ULift.{u} (Fin (0 + 1))) := Equiv.ulift.unique (β := Fin 1)
    exact isSimplyConnected_of_iso e.symm (isSimplyConnected_proj_of_unique k _)
  · exact isSimplyConnected_of_iso e.symm (isSimplyConnected_proj k _)

/-- XI.1.1: `ProjectiveSpaceSimplyConnectedStatement` holds. -/
theorem projectiveSpaceSimplyConnectedStatement : ProjectiveSpaceSimplyConnectedStatement.{u} :=
  fun k _ _ r ↦ isSimplyConnected_projectiveSpace k r

end Main

section Products

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The structure morphism `ℙʳ_k ⟶ Spec k`. -/
noncomputable def toSpec (r : ℕ) : projectiveSpace k r ⟶ Spec (.of k) :=
  Proj.toSpecZero _ ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (homogeneousSubmodule (Fin (r + 1)) k 0)))

instance (r : ℕ) : IsProper (toSpec k r) := by
  have : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap k (homogeneousSubmodule (Fin (r + 1)) k 0)))) :=
    isIso_SpecMap_iff.2 ⟨fun a b h ↦ C_injective (Fin (r + 1)) k (congrArg Subtype.val h),
      projectiveSpace.surjective_algebraMap_gradeZero⟩
  rw [toSpec]
  infer_instance

instance (r : ℕ) : AlgebraicGeometry.IsReduced (projectiveSpace k r) := by
  have (i : (Proj.affineOpenCover (homogeneousSubmodule (Fin (r + 1)) k)).openCover.I₀) :
      AlgebraicGeometry.IsReduced ((Proj.affineOpenCover _).openCover.X i) := by
    have : _root_.IsReduced
        (HomogeneousLocalization.Away (homogeneousSubmodule (Fin (r + 1)) k) i.2.1) :=
      isReduced_of_injective
        (algebraMap _ (Localization.Away (i.2.1 : MvPolynomial (Fin (r + 1)) k)))
        (HomogeneousLocalization.val_injective _)
    exact inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of _)))
  exact AlgebraicGeometry.IsReduced.of_openCover _ (Proj.affineOpenCover _).openCover

instance (r : ℕ) : IsLocallyNoetherian (projectiveSpace k r) :=
  LocallyOfFiniteType.isLocallyNoetherian (toSpec k r)

instance (r : ℕ) : CompactSpace (projectiveSpace k r) :=
  QuasiCompact.compactSpace_of_compactSpace (toSpec k r)

/-- XI.1.1 with the Künneth formula X.1.7: if `T` is a simply connected `k`-scheme, quasi-compact
and locally of finite type (`k` algebraically closed), then so is `ℙʳ_T = ℙʳ_k ×ₖ T`. -/
theorem isSimplyConnected_pullback_toSpec [IsAlgClosed k] (r : ℕ) {T : Scheme.{u}}
    (sT : T ⟶ Spec (.of k)) [CompactSpace T] [LocallyOfFiniteType sT]
    (hT : IsSimplyConnected T) : IsSimplyConnected (pullback (toSpec k r) sT) := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  exact isSimplyConnected_pullback (toSpec k r) sT (isSimplyConnected_projectiveSpace k r) hT

/-- The product `ℙ^{r₁} ×ₖ ⋯ ×ₖ ℙ^{rₘ}` over `Spec k`. -/
noncomputable def prod : List ℕ → Over (Spec (.of k))
  | [] => Over.mk (𝟙 _)
  | r :: rs => Over.mk (pullback.snd (toSpec k r) (prod rs).hom ≫ (prod rs).hom)

lemma prod_properties [IsAlgClosed k] (rs : List ℕ) :
    IsSimplyConnected (prod k rs).left ∧ LocallyOfFiniteType (prod k rs).hom ∧
      CompactSpace (prod k rs).left := by
  induction rs with
  | nil =>
    exact ⟨isSimplyConnected_spec_of_isSepClosed k, inferInstanceAs (LocallyOfFiniteType (𝟙 _)),
      inferInstanceAs (CompactSpace (Spec (.of k)))⟩
  | cons r rs ih =>
    obtain ⟨h₁, h₂, h₃⟩ := ih
    have : QuasiCompact (toSpec k r) := inferInstance
    exact ⟨isSimplyConnected_pullback_toSpec k r (prod k rs).hom h₁,
      inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _ ≫ _)),
      inferInstanceAs (CompactSpace ↑(pullback (toSpec k r) (prod k rs).hom))⟩

/-- XI.1.1 with X.1.7: a product of projective spaces over an algebraically closed field is
simply connected. -/
theorem isSimplyConnected_prod [IsAlgClosed k] (rs : List ℕ) :
    IsSimplyConnected (prod k rs).left :=
  (prod_properties k rs).1

end Products

section Birational

variable (k : Type u) [Field k]

/-- Projective space over a field is regular. -/
theorem isRegularScheme_proj (σ : Type u) [Finite σ] :
    ExposeX.IsRegularScheme (Proj (grading σ k)) := by
  intro x
  obtain ⟨i, hi⟩ : ∃ i, x ∈ Proj.basicOpen (grading σ k) (X i) := by
    have hx : x ∈ (⊤ : (Proj (grading σ k)).Opens) := trivial
    rw [← iSup_basicOpen_X σ k] at hx
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  have hU := isAffineOpen_basicOpen_X (k := k) i
  have : IsRegularRing Γ(Proj (grading σ k), Proj.basicOpen (grading σ k) (X i)) :=
    IsRegularRing.of_ringEquiv (chartRingEquiv i).symm
  exact IsRegularLocalRing.of_ringEquiv (ExposeI.stalkEquivLocalization hU x hi).symm

/-- Regularity is invariant under isomorphism. -/
lemma isRegularScheme_of_iso {X X' : Scheme.{u}} (e : X ≅ X') (h : ExposeX.IsRegularScheme X) :
    ExposeX.IsRegularScheme X' := fun x ↦
  have := h (e.inv x)
  IsRegularLocalRing.of_ringEquiv (asIso (e.inv.stalkMap x)).commRingCatIsoToRingEquiv

/-- The isomorphism `ℙʳ_k ≅ Proj k[ULift (Fin (r + 1))]`. -/
noncomputable def projectiveSpaceIso (r : ℕ) :
    projectiveSpace k r ≅ Proj (grading (ULift.{u} (Fin (r + 1))) k) :=
  projRenameIso (R := k) Equiv.ulift.symm

/-- Projective space over a field is regular. -/
theorem isRegularScheme_projectiveSpace (r : ℕ) : ExposeX.IsRegularScheme (projectiveSpace k r) :=
  isRegularScheme_of_iso (projectiveSpaceIso k r).symm (isRegularScheme_proj k _)

instance (r : ℕ) : IsIntegral (projectiveSpace k r) := by
  have : IsIntegral (Proj (grading (ULift.{u} (Fin (r + 1))) k)) :=
    isIntegral_of_isFinite_of_etale (𝟙 _)
  have : Nonempty (projectiveSpace k r) := ⟨(projectiveSpaceIso k r).inv
    (Classical.arbitrary (Proj (grading (ULift.{u} (Fin (r + 1))) k)))⟩
  exact isIntegral_of_isOpenImmersion (projectiveSpaceIso k r).hom

/-- XI.1.2 for varieties with a given birational map to `ℙʳ`, from X.3.4
(`ExposeX.birationalInvariance`): a proper, integral, regular `k`-scheme birational to `ℙʳ_k`
(`k` algebraically closed) is simply connected. -/
theorem isSimplyConnected_of_partialIso_projectiveSpace [IsAlgClosed k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsProper sX] [IsIntegral X] (hX : ExposeX.IsRegularScheme X) {r : ℕ}
    (φ : X.PartialIso (projectiveSpace k r)) (hφ : φ.IsOver sX (toSpec k r)) :
    IsSimplyConnected X :=
  isSimplyConnected_of_partialIso_of_isRegularScheme sX (toSpec k r) hX
    (isRegularScheme_projectiveSpace k r) φ hφ (isSimplyConnected_projectiveSpace k r)

end Birational

end SGA.SGA1.ExposeXI.ProjectiveSpace
