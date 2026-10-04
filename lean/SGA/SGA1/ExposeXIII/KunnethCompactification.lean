/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Normalization
import SGA.Foundations.NormalizationFinite
import SGA.SGA1.ExposeV.FiniteEtaleSpec
import SGA.SGA1.ExposeX.CurveFiniteSmooth
import SGA.SGA1.ExposeX.NormalCompleteLocalBase
import SGA.SGA1.ExposeX.PurityDenseOpen
import SGA.SGA1.ExposeXIII.KummerCoverings
import SGA.SGA1.ExposeXIII.KunnethNormalProduct
import SGA.SGA1.ExposeXIII.KunnethProjectiveLine
import SGA.SGA1.ExposeXIII.RootAdjunction

/-!
# SGA 1, XIII.4.6 in characteristic `0`: the Kummer covering of `U = 𝔸¹ ∖ V(g)` and its
compactification

For the curve case of the resolution-free route to XIII.4.6 in characteristic `0`
(`AffineLineOpenInvarianceStatement`), an étale covering of `U_{k'} = (𝔸¹ ∖ V(g))_{k'}` is pulled
back to a Kummer covering of `U` and extended over the smooth compactification of the latter
(Abhyankar's lemma at the missing points, then purity). This file constructs the objects over `k`:

* `kummerRing k g N = Γ(U)[z_a]/(z_a^N - (t - a))` (`a` running over the roots of `g`), finite
  étale over `Γ(U)` (`etale_kummerRing`, `finite_kummerRing`);
* `exists_isConnected_hom`: a nonempty étale covering of a connected affine scheme receives a
  morphism from a connected one (the decomposition into connected components in the Galois
  category);
* for a connected étale covering `V` of `U = Spec Γ(U)`, its compactification is mathlib's relative
  normalization of `ℙ¹_k` in `V` (of `toLine V : V ⟶ U ⊆ ℙ¹`). When `g(0) = 0`, so that `U` lies in
  both charts of `ℙ¹`, the compactification is finite over `ℙ¹` (`isFinite_fromNormalization`):
  over each chart `Γ = k[X]` it is the integral closure of `k[X]` in `Γ(V)`, finite by
  `finite_integralClosure_of_isLocalization` (`Γ(V)` is finite over the localization `Γ(U)` of
  `k[X]`; characteristic `0`).

References: SGA 1 XIII.5 (Kummer coverings), EGA II 6.3 (normalization), Stacks 0BAK.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Polynomial PreGaloisCategory
open SGA.SGA1.ExposeXI.ProjectiveLine SGA.SGA1.ExposeXI
open scoped nonZeroDivisors

namespace SGA.SGA1.ExposeXIII.KummerCompactification

section Algebra

/-- Finiteness of a normalization chart: let `R` be a noetherian integrally closed domain of
characteristic `0`, `A` its localization at a nonzero `g₀` and `B` a domain, finite and faithful
over `A`. Then the integral closure of `R` in `B` is a finite `R`-module. -/
theorem finite_integralClosure_of_isLocalization {R : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [IsNoetherianRing R] [CharZero R] {g₀ : R}
    (hg₀ : g₀ ≠ 0) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.Away g₀ A]
    (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [FaithfulSMul A B]
    [Algebra R B] [IsScalarTower R A B] :
    Module.Finite R (integralClosure R B) := by
  classical
  have : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers g₀)
    A (powers_le_nonZeroDivisors_of_noZeroDivisors hg₀)
  let K := FractionRing R
  let L := FractionRing B
  have hinjA : Function.Injective (algebraMap R A) :=
    IsLocalization.injective A (powers_le_nonZeroDivisors_of_noZeroDivisors hg₀)
  have : FaithfulSMul R L := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq R B L,
      IsScalarTower.algebraMap_eq R A B]
    exact (IsFractionRing.injective B L).comp
      ((FaithfulSMul.algebraMap_injective A B).comp hinjA)
  let : Algebra K L := FractionRing.liftAlgebra R L
  have : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  -- `K` is the fraction field of `A`
  have hg₀K : IsUnit (algebraMap R K g₀) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hg₀).isUnit
  let : Algebra A K := (IsLocalization.Away.lift g₀ hg₀K).toAlgebra
  have : IsScalarTower R A K :=
    .of_algebraMap_eq fun a ↦ (IsLocalization.Away.lift_eq g₀ hg₀K a).symm
  have : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers g₀) A K
  have : IsScalarTower A K L := .of_algebraMap_eq fun a ↦ by
    have : (algebraMap A L).comp (algebraMap R A) =
        ((algebraMap K L).comp (algebraMap A K)).comp (algebraMap R A) := by
      refine RingHom.ext fun x ↦ ?_
      change algebraMap A L (algebraMap R A x) =
        algebraMap K L (algebraMap A K (algebraMap R A x))
      rw [← IsScalarTower.algebraMap_apply R A K, ← IsScalarTower.algebraMap_apply R K L,
        IsScalarTower.algebraMap_apply A B L, ← IsScalarTower.algebraMap_apply R A B,
        ← IsScalarTower.algebraMap_apply R B L]
    exact congrArg (· a) (IsLocalization.ringHom_ext (Submonoid.powers g₀) this)
  have : Algebra.IsIntegral A B := inferInstance
  have : Module.Finite K L := Module.Finite.of_isLocalization A B A⁰
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  have : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hfin := IsIntegralClosure.finite R K L (integralClosure R L)
  let ι := (IsScalarTower.toAlgHom R B L).mapIntegralClosure
  exact Module.Finite.of_injective ι.toLinearMap fun x y h ↦
    Subtype.ext ((IsFractionRing.injective B L) (congrArg Subtype.val h))

end Algebra

section Galois

/-- In the Galois category of étale coverings of a connected affine scheme, a covering with
nonempty source receives a morphism from a connected covering. -/
lemma exists_isConnected_hom {R : CommRingCat.{u}} [ConnectedSpace (PrimeSpectrum R)]
    (Y : ExposeV.FEt (Spec R)) [Nonempty Y.left] :
    ∃ (V : ExposeV.FEt (Spec R)) (_ : V ⟶ Y), IsConnected V := by
  obtain ⟨ι, f, i, hl, hc, -⟩ := has_decomp_connected_components Y
  by_cases hι : Nonempty ι
  · obtain ⟨a⟩ := hι
    exact ⟨f a, i a, hc a⟩
  · rw [not_nonempty_iff] at hι
    have hY : IsInitial Y := IsInitial.ofUniqueHom
      (fun Z ↦ hl.desc (Cofan.mk Z fun a ↦ isEmptyElim a))
      (fun Z m ↦ hl.hom_ext fun a ↦ isEmptyElim a.as)
    exact ((ExposeV.FEt.nonempty_left_iff_not_isInitial Y).mp inferInstance hY).elim

end Galois

section Kummer

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] [CharZero k] [DecidableEq k] (g : k[X])

local notation "ℙ¹" => Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

/-- The function `t - a` on `U = D(g) ⊆ 𝔸¹ = D₊(x₀)`. -/
noncomputable def radicand (a : k) : Γ(ℙ¹, lineOpen k g) :=
  (ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₀ g)).op ((chartEquiv₀ k).symm (X - C a))

omit [CharZero k] [DecidableEq k] in
variable {k g} in
lemma isUnit_radicand {a : k} (ha : g.IsRoot a) : IsUnit (radicand k g a) := by
  have h := (ℙ¹).toRingedSpace.isUnit_res_basicOpen ((chartEquiv₀ k).symm g)
  refine isUnit_of_dvd_unit ?_ h
  exact map_dvd _ (map_dvd _ (dvd_iff_isRoot.mpr ha))

/-- The Kummer algebra `Γ(U)[z_a]/(z_a^N - (t - a))`, `a` running over the roots of `g`. -/
abbrev kummerRing (N : ℕ) : Type u :=
  KummerAlgebra (fun _ : g.roots.toFinset ↦ N) (fun a ↦ radicand k g a.1)

omit [CharZero k] [DecidableEq k] in
lemma isDomain_sections_lineOpen (hg : g ≠ 0) : IsDomain Γ(ℙ¹, lineOpen k g) := by
  let : Algebra k[X] Γ(ℙ¹, lineOpen k g) :=
    (((ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₀ g)).op).hom.comp
      (chartEquiv₀ k).symm.toRingHom).toAlgebra
  have := isLocalization_lineOpen₀ g
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers g) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors hg)

variable {k g} in
lemma etale_kummerRing {N : ℕ} (hN : N ≠ 0) :
    Algebra.Etale Γ(ℙ¹, lineOpen k g) (kummerRing k g N) := by
  refine KummerAlgebra.etale (fun _ ↦ ?_) fun a ↦ isUnit_radicand ?_
  · have : ((N : ℕ) : Γ(ℙ¹, lineOpen k g)) = (ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₀ g)).op
        ((chartEquiv₀ k).symm (C (N : k))) := by
      simp
    rw [this]
    exact ((isUnit_C.mpr (Ne.isUnit (Nat.cast_ne_zero.mpr hN))).map _).map _
  · have := Multiset.mem_toFinset.mp a.2
    exact (mem_roots'.mp this).2

omit [CharZero k] in
variable {k g} in
lemma finite_kummerRing {N : ℕ} (hN : N ≠ 0) :
    Module.Finite Γ(ℙ¹, lineOpen k g) (kummerRing k g N) := by
  have := KummerAlgebra.isIntegral (A := Γ(ℙ¹, lineOpen k g))
    (n := fun _ : g.roots.toFinset ↦ N) (fun a ↦ radicand k g a.1) fun _ ↦ Nat.pos_of_ne_zero hN
  exact Algebra.IsIntegral.finite

end Kummer

section Compactification

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {g : k[X]}

local notation "ℙ¹" => Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

/-- `V ⟶ U ⊆ ℙ¹` for an étale covering `V` of `U = Spec Γ(U)`. -/
noncomputable def toLine (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) : V.left ⟶ ℙ¹ :=
  V.hom ≫ (isAffineOpen_lineOpen g).fromSpec

instance (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) : QuasiCompact (toLine V) := by
  have : IsFinite V.hom := V.prop.1
  unfold toLine
  infer_instance

instance (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) : QuasiSeparated (toLine V) := by
  have : IsFinite V.hom := V.prop.1
  unfold toLine
  infer_instance

lemma toLine_preimage_eq_top (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) {O : (ℙ¹).Opens}
    (hO : lineOpen k g ≤ O) : toLine V ⁻¹ᵁ O = ⊤ := by
  rw [toLine, Scheme.Hom.comp_preimage, eq_top_iff]
  intro x _
  have h := (isAffineOpen_lineOpen g).fromSpec_preimage_self
  have : V.hom x ∈ (isAffineOpen_lineOpen g).fromSpec ⁻¹ᵁ lineOpen k g := by rw [h]; trivial
  exact hO this

/-- The sections of `V` over the preimage of an open `O ⊇ U`, as an algebra over `Γ(U)`. -/
noncomputable abbrev sectionsAlgebra (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g)))
    (O : (ℙ¹).Opens) : Algebra Γ(ℙ¹, lineOpen k g) Γ(V.left, toLine V ⁻¹ᵁ O) :=
  ((V.hom.appLE ⊤ (toLine V ⁻¹ᵁ O) le_top).hom.comp
    (Scheme.ΓSpecIso Γ(ℙ¹, lineOpen k g)).inv.hom).toAlgebra

lemma toLine_app_eq (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) {O : (ℙ¹).Opens}
    (hO : lineOpen k g ≤ O) : (toLine V).app O = (ℙ¹).presheaf.map (homOfLE hO).op ≫
      (Scheme.ΓSpecIso Γ(ℙ¹, lineOpen k g)).inv ≫ V.hom.appLE ⊤ (toLine V ⁻¹ᵁ O) le_top := by
  rw [toLine, Scheme.Hom.comp_app, IsAffineOpen.fromSpec_app_of_le _ _ hO, Category.assoc,
    Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
  rfl

lemma isNormalScheme_spec_sections_lineOpen (hg : g ≠ 0) :
    ExposeI.IsNormalScheme (Spec Γ(ℙ¹, lineOpen k g)) := by
  let : Algebra k[X] Γ(ℙ¹, lineOpen k g) :=
    (((ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₀ g)).op).hom.comp
      (chartEquiv₀ k).symm.toRingHom).toAlgebra
  have := isLocalization_lineOpen₀ g
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hg
  have : IsDomain Γ(ℙ¹, lineOpen k g) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers g) _ hle
  have : IsIntegrallyClosed Γ(ℙ¹, lineOpen k g) :=
    isIntegrallyClosed_of_isLocalization _ (Submonoid.powers g) hle
  exact isNormalScheme_spec (R := Γ(ℙ¹, lineOpen k g))

lemma isNormalScheme_left (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) (hg : g ≠ 0) :
    ExposeI.IsNormalScheme V.left := by
  have : Etale V.hom := V.prop.2
  exact ExposeI.isNormalScheme_of_etale V.hom (isNormalScheme_spec_sections_lineOpen hg)

lemma isIntegral_left (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) [IsConnected V]
    (hg : g ≠ 0) : IsIntegral V.left := by
  let p : V.left ⟶ Spec Γ(ℙ¹, lineOpen k g) := V.hom
  have : IsFinite p := V.prop.1
  have : IsDomain Γ(ℙ¹, lineOpen k g) := isDomain_sections_lineOpen k g hg
  have : IsLocallyNoetherian V.left := by
    have : IsNoetherianRing Γ(ℙ¹, lineOpen k g) := by
      let : Algebra k[X] Γ(ℙ¹, lineOpen k g) :=
        (((ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₀ g)).op).hom.comp
          (chartEquiv₀ k).symm.toRingHom).toAlgebra
      have := isLocalization_lineOpen₀ g
      exact IsLocalization.isNoetherianRing (Submonoid.powers g) _ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian p
  have : ConnectedSpace V.left := ExposeV.FEt.connectedSpace_of_isConnected V
  exact ExposeX.isIntegral_of_isNormalScheme (isNormalScheme_left V hg)

variable [CharZero k] in
/-- Over a chart `O ⊇ U` with `Γ(O) ≅ k[X]` and `U = D(σ)`, the normalization of `ℙ¹` in `V` is
finite. -/
lemma finite_integralClosure_chart (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) [IsConnected V]
    (hg : g ≠ 0) {O : (ℙ¹).Opens} (hO : IsAffineOpen O) (hUO : lineOpen k g ≤ O)
    (φ : Γ(ℙ¹, O) ≃+* k[X]) (σ : Γ(ℙ¹, O)) (hσ0 : σ ≠ 0)
    (hσ : (ℙ¹).basicOpen σ = lineOpen k g) :
    letI := ((toLine V).app O).hom.toAlgebra
    Module.Finite Γ(ℙ¹, O) (integralClosure Γ(ℙ¹, O) Γ(V.left, toLine V ⁻¹ᵁ O)) := by
  let : Algebra Γ(ℙ¹, O) Γ(V.left, toLine V ⁻¹ᵁ O) := ((toLine V).app O).hom.toAlgebra
  let p : V.left ⟶ Spec Γ(ℙ¹, lineOpen k g) := V.hom
  have : IsFinite p := V.prop.1
  have : Etale p := V.prop.2
  have : IsDomain Γ(ℙ¹, O) := φ.toMulEquiv.isDomain_iff.mpr inferInstance
  have : IsIntegrallyClosed Γ(ℙ¹, O) := IsIntegrallyClosed.of_equiv φ.symm
  have : IsNoetherianRing Γ(ℙ¹, O) := isNoetherianRing_of_ringEquiv k[X] φ.symm
  have : CharZero Γ(ℙ¹, O) := charZero_of_injective_ringHom
    (f := φ.symm.toRingHom.comp (algebraMap k k[X]))
    (φ.symm.injective.comp (algebraMap k k[X]).injective)
  let : Algebra Γ(ℙ¹, O) Γ(ℙ¹, lineOpen k g) :=
    ((ℙ¹).presheaf.map (homOfLE hUO).op).hom.toAlgebra
  have : IsLocalization.Away σ Γ(ℙ¹, lineOpen k g) :=
    hO.isLocalization_of_eq_basicOpen σ (homOfLE hUO) hσ.symm
  let := sectionsAlgebra V O
  have : IsScalarTower Γ(ℙ¹, O) Γ(ℙ¹, lineOpen k g) Γ(V.left, toLine V ⁻¹ᵁ O) :=
    .of_algebraMap_eq fun x ↦ by
      change (toLine V).app O x = _
      rw [toLine_app_eq V hUO]
      rfl
  have hW := toLine_preimage_eq_top V hUO
  have : IsIntegral V.left := isIntegral_left V hg
  have : Nonempty V.left := (ExposeV.FEt.nonempty_left_iff_not_isInitial V).mpr
    IsConnected.notInitial
  have : Nonempty (toLine V ⁻¹ᵁ O) := by
    obtain ⟨x⟩ := this
    exact ⟨⟨x, by rw [hW]; trivial⟩⟩
  have : IsDomain Γ(V.left, toLine V ⁻¹ᵁ O) := inferInstance
  -- the restriction from `⊤` to `toLine⁻¹ O = ⊤` is an isomorphism
  have hiso : IsIso (V.left.presheaf.map (homOfLE (le_top : toLine V ⁻¹ᵁ O ≤ ⊤)).op) := by
    have : IsIso (homOfLE (le_top : toLine V ⁻¹ᵁ O ≤ ⊤)) :=
      ⟨⟨homOfLE (by rw [hW]), Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    infer_instance
  have happ : V.hom.appLE ⊤ (toLine V ⁻¹ᵁ O) le_top =
      p.appTop ≫ V.left.presheaf.map (homOfLE (le_top : toLine V ⁻¹ᵁ O ≤ ⊤)).op := rfl
  have : Module.Finite Γ(ℙ¹, lineOpen k g) Γ(V.left, toLine V ⁻¹ᵁ O) := by
    rw [← RingHom.finite_algebraMap]
    change ((V.hom.appLE ⊤ (toLine V ⁻¹ᵁ O) le_top).hom.comp
      (Scheme.ΓSpecIso Γ(ℙ¹, lineOpen k g)).inv.hom).Finite
    rw [happ, CommRingCat.hom_comp]
    exact RingHom.Finite.comp (RingHom.Finite.comp
      (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
      (p.finite_appTop)) (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso _).2)
  have : Module.Flat Γ(ℙ¹, lineOpen k g) Γ(V.left, toLine V ⁻¹ᵁ O) := by
    rw [← RingHom.flat_algebraMap_iff]
    have : IsAffine V.left := isAffine_of_isAffineHom p
    have hWa : IsAffineOpen (toLine V ⁻¹ᵁ O) := by rw [hW]; exact isAffineOpen_top _
    have := HasRingHomProperty.appLE (P := @Flat) p inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨_, hWa⟩ le_top
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso Γ(ℙ¹, lineOpen k g)).inv)) this
  have : IsDomain Γ(ℙ¹, lineOpen k g) := isDomain_sections_lineOpen k g hg
  have : FaithfulSMul Γ(ℙ¹, lineOpen k g) Γ(V.left, toLine V ⁻¹ᵁ O) := inferInstance
  exact finite_integralClosure_of_isLocalization hσ0 Γ(ℙ¹, lineOpen k g)
    Γ(V.left, toLine V ⁻¹ᵁ O)

lemma chartPoly₁_ne_zero (hg : g ≠ 0) (hg0 : g.IsRoot 0) : chartPoly₁ k g ≠ 0 := by
  rw [chartPoly₁]
  refine mul_ne_zero X_ne_zero ?_
  rw [Ne, reverse_eq_zero]
  intro h
  apply hg
  rw [eq_X_mul_divByMonic hg0, h, mul_zero]

variable [CharZero k] in
set_option backward.isDefEq.respectTransparency false in
/-- The compactification `C̄ → ℙ¹` (the normalization of `ℙ¹` in `V`) is finite, for `k` of
characteristic `0`, `g ≠ 0` with `g(0) = 0` (so that `U` lies in both charts) and `V` connected. -/
theorem isFinite_fromNormalization (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) [IsConnected V]
    (hg : g ≠ 0) (hg0 : g.IsRoot 0) : IsFinite (toLine V).fromNormalization := by
  let c : Fin 2 → (ℙ¹).affineOpens :=
    ![⟨chart₀ k, ExposeXIII.ProjectiveLineCurve.isAffineOpen_chart₀ k⟩,
      ⟨chart₁ k, ExposeXIII.ProjectiveLineCurve.isAffineOpen_chart₁ k⟩]
  have hc : ⨆ j, (c j : (ℙ¹).Opens) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← chart₀_sup_chart₁ k]
    exact sup_le (le_iSup (fun j ↦ (c j : (ℙ¹).Opens)) 0) (le_iSup (fun j ↦ (c j : (ℙ¹).Opens)) 1)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) (fun j ↦ (c j).1) hc]
  intro j
  set U := c j
  let e := IsOpenImmersion.isoOfRangeEq ((toLine V).fromNormalization ⁻¹ᵁ U).ι
    ((toLine V).normalizationOpenCover.f U)
      (by simpa using congr($((toLine V).fromNormalization_preimage U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _ U.2.isoSpec.hom]
  have : ((toLine V).normalizationDiagramMap.app (.op U)).hom.Finite := by
    let := ((toLine V).app U).hom.toAlgebra
    change (algebraMap Γ(ℙ¹, U) (integralClosure Γ(ℙ¹, U) Γ(V.left, toLine V ⁻¹ᵁ U))).Finite
    rw [RingHom.finite_algebraMap]
    fin_cases j
    · exact finite_integralClosure_chart V hg
        (ExposeXIII.ProjectiveLineCurve.isAffineOpen_chart₀ k) (lineOpen_le_chart₀ g)
        (chartEquiv₀ k) ((chartEquiv₀ k).symm g)
        ((map_ne_zero_iff _ (chartEquiv₀ k).symm.injective).mpr hg) rfl
    · exact finite_integralClosure_chart V hg
        (ExposeXIII.ProjectiveLineCurve.isAffineOpen_chart₁ k) (lineOpen_le_chart₁ hg0)
        (chartEquiv₁ k) ((chartEquiv₁ k).symm (chartPoly₁ k g))
        ((map_ne_zero_iff _ (chartEquiv₁ k).symm.injective).mpr (chartPoly₁_ne_zero hg hg0))
        (basicOpen_chartPoly₁ hg0)
  convert! (IsFinite.SpecMap_iff _).mpr this
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, Scheme.Hom.ι_fromNormalization]

set_option backward.isDefEq.respectTransparency false in
/-- `V ⟶ C̄` is an open immersion onto the preimage of `U`: normalization commutes with the open
immersion `U ⟶ ℙ¹` (mathlib's `Scheme.Hom.normalizationPullback`, smooth base change), and `V` is
finite over `U`, hence its own normalization there. -/
theorem isOpenImmersion_toNormalization (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) :
    IsOpenImmersion (toLine V).toNormalization ∧
      Set.range (toLine V).toNormalization =
        (toLine V).fromNormalization ⁻¹' (lineOpen k g : Set ℙ¹) := by
  let p : V.left ⟶ Spec Γ(ℙ¹, lineOpen k g) := V.hom
  have : IsFinite p := V.prop.1
  let a : V.left ⟶ (lineOpen k g).toScheme := p ≫ (isAffineOpen_lineOpen g).isoSpec.inv
  let ι := (lineOpen k g).ι
  have hf : toLine V = a ≫ ι := by
    simp only [toLine, a, Category.assoc]
    rfl
  have hsq : IsPullback (𝟙 V.left) a (toLine V) ι :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, hf]⟩
  have hfst : pullback.fst (toLine V) ι = hsq.isoPullback.inv := by
    rw [← cancel_epi hsq.isoPullback.hom, Iso.hom_inv_id, hsq.isoPullback_hom_fst]
  have hsnd : pullback.snd (toLine V) ι = hsq.isoPullback.inv ≫ a := by
    rw [← cancel_epi hsq.isoPullback.hom, Iso.hom_inv_id_assoc, hsq.isoPullback_hom_snd]
  have : IsIntegralHom (pullback.snd (toLine V) ι) := by
    rw [hsnd]
    infer_instance
  have key := (toLine V).toNormalization_normalizationPullback_fst ι
  have hj : (toLine V).toNormalization = hsq.isoPullback.hom ≫
      (pullback.snd (toLine V) ι).toNormalization ≫ (toLine V).normalizationPullback ι ≫
        pullback.fst (toLine V).fromNormalization ι := by
    rw [key, hfst, Iso.hom_inv_id_assoc]
  refine ⟨by rw [hj]; infer_instance, ?_⟩
  set e := hsq.isoPullback.hom ≫ (pullback.snd (toLine V) ι).toNormalization ≫
    (toLine V).normalizationPullback ι
  have he : (toLine V).toNormalization = e ≫ pullback.fst (toLine V).fromNormalization ι := by
    rw [hj]
    simp only [e, Category.assoc]
  have : IsIso e := by simp only [e]; infer_instance
  rw [he, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr e.surjective, Set.image_univ, Scheme.Pullback.range_fst,
    Scheme.Opens.range_ι]

lemma exists_chart (hg : g ≠ 0) (hg0 : g.IsRoot 0) (y : ℙ¹) :
    ∃ O : (ℙ¹).Opens, IsAffineOpen O ∧ y ∈ O ∧ lineOpen k g ≤ O ∧
      Nonempty (Γ(ℙ¹, O) ≃+* k[X]) ∧
        ∃ σ : Γ(ℙ¹, O), σ ≠ 0 ∧ (ℙ¹).basicOpen σ = lineOpen k g := by
  have hy : y ∈ chart₀ k ⊔ chart₁ k := by rw [chart₀_sup_chart₁]; trivial
  rcases TopologicalSpace.Opens.mem_sup.mp hy with h | h
  · exact ⟨_, ExposeXIII.ProjectiveLineCurve.isAffineOpen_chart₀ k, h, lineOpen_le_chart₀ g,
      ⟨chartEquiv₀ k⟩, (chartEquiv₀ k).symm g,
      (map_ne_zero_iff _ (chartEquiv₀ k).symm.injective).mpr hg, rfl⟩
  · exact ⟨_, ExposeXIII.ProjectiveLineCurve.isAffineOpen_chart₁ k, h, lineOpen_le_chart₁ hg0,
      ⟨chartEquiv₁ k⟩, (chartEquiv₁ k).symm (chartPoly₁ k g),
      (map_ne_zero_iff _ (chartEquiv₁ k).symm.injective).mpr (chartPoly₁_ne_zero hg hg0),
      basicOpen_chartPoly₁ hg0⟩

variable [CharZero k] in
set_option backward.isDefEq.respectTransparency false in
/-- The local rings of the compactification `C̄` are regular (discrete valuation rings or fields):
over a chart `O ≅ 𝔸¹` it is the integral closure of `k[X]` in the normal domain `Γ(V)`, an
integrally closed noetherian domain of dimension `≤ 1`. -/
theorem isRegularLocalRing_stalk_normalization (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g)))
    [IsConnected V] (hg : g ≠ 0) (hg0 : g.IsRoot 0) (x : (toLine V).normalization) :
    IsRegularLocalRing ((toLine V).normalization.presheaf.stalk x) := by
  have : IsIntegral V.left := isIntegral_left V hg
  obtain ⟨O, hO, hxO, hUO, ⟨φ⟩, σ, hσ0, hσ⟩ :=
    exists_chart hg hg0 ((toLine V).fromNormalization x)
  let := ((toLine V).app O).hom.toAlgebra
  have hW := toLine_preimage_eq_top V hUO
  have : Nonempty V.left := (ExposeV.FEt.nonempty_left_iff_not_isInitial V).mpr
    IsConnected.notInitial
  have : Nonempty (toLine V ⁻¹ᵁ O) := by
    obtain ⟨y⟩ := this
    exact ⟨⟨y, by rw [hW]; trivial⟩⟩
  have : IsAffine V.left := by
    let p : V.left ⟶ Spec Γ(ℙ¹, lineOpen k g) := V.hom
    have : IsFinite p := V.prop.1
    exact isAffine_of_isAffineHom p
  have hWa : IsAffineOpen (toLine V ⁻¹ᵁ O) := by rw [hW]; exact isAffineOpen_top _
  have : IsIntegrallyClosed Γ(V.left, toLine V ⁻¹ᵁ O) :=
    ExposeX.isIntegrallyClosed_of_isAffineOpen (isNormalScheme_left V hg) hWa
  have : IsDomain Γ(ℙ¹, O) := φ.toMulEquiv.isDomain_iff.mpr inferInstance
  have : IsNoetherianRing Γ(ℙ¹, O) := isNoetherianRing_of_ringEquiv k[X] φ.symm
  let R := integralClosure Γ(ℙ¹, O) Γ(V.left, toLine V ⁻¹ᵁ O)
  have : Module.Finite Γ(ℙ¹, O) R := finite_integralClosure_chart V hg hO hUO φ σ hσ0 hσ
  have : IsIntegrallyClosed R :=
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn (R := R)
      (S := Γ(V.left, toLine V ⁻¹ᵁ O))
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing Γ(ℙ¹, O) R
  have hdimR : ringKrullDim R ≤ 1 := by
    have : Algebra.IsIntegral Γ(ℙ¹, O) R := inferInstance
    calc ringKrullDim R ≤ ringKrullDim Γ(ℙ¹, O) := ringKrullDim_le_of_isIntegral
      _ = ringKrullDim k[X] := ringKrullDim_eq_of_ringEquiv φ
      _ = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one _ (Polynomial.not_isField k)
  let C := (toLine V).normalization
  let e := ((toLine V).normalizationObjIso hO).commRingCatIsoToRingEquiv
  have hV : IsAffineOpen ((toLine V).fromNormalization ⁻¹ᵁ O) := hO.preimage _
  have : IsDomain Γ(C, (toLine V).fromNormalization ⁻¹ᵁ O) :=
    e.toMulEquiv.isDomain_iff.mpr inferInstance
  have : IsIntegrallyClosed Γ(C, (toLine V).fromNormalization ⁻¹ᵁ O) :=
    IsIntegrallyClosed.of_equiv e.symm
  have : IsNoetherianRing Γ(C, (toLine V).fromNormalization ⁻¹ᵁ O) :=
    isNoetherianRing_of_ringEquiv R e.symm
  have hdim : ringKrullDim Γ(C, (toLine V).fromNormalization ⁻¹ᵁ O) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e]
    exact hdimR
  let : Algebra Γ(C, (toLine V).fromNormalization ⁻¹ᵁ O) (C.presheaf.stalk x) :=
    C.presheaf.algebra_section_stalk ⟨x, hxO⟩
  have : IsLocalization.AtPrime (C.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxO⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxO⟩
  have : IsIntegrallyClosed (C.presheaf.stalk x) :=
    isIntegrallyClosed_of_isLocalization _ _
      (Ideal.primeCompl_le_nonZeroDivisors (hV.primeIdealOf ⟨x, hxO⟩).asIdeal)
  have : IsNoetherianRing (C.presheaf.stalk x) :=
    IsLocalization.isNoetherianRing (hV.primeIdealOf ⟨x, hxO⟩).asIdeal.primeCompl _ inferInstance
  have hd : ringKrullDim (C.presheaf.stalk x) ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨x, hxO⟩).asIdeal
      (C.presheaf.stalk x)]
    exact Ideal.height_le_ringKrullDim_of_isPrime.trans hdim
  have := IsPrincipalIdealRing.of_isIntegrallyClosed_of_ringKrullDim_le_one hd
  infer_instance

variable [CharZero k] in
/-- The compactification `C̄` of a connected étale covering `V` of `U = 𝔸¹ ∖ V(g)` (`g(0) = 0`):
the normalization of `ℙ¹_k` in `V` is an integral scheme, proper and smooth over `k` (a smooth
projective curve), and `V` is the open subscheme over `U`
(`isOpenImmersion_toNormalization`). -/
theorem isProper_smooth_isIntegral_normalization (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g)))
    [IsConnected V] (hg : g ≠ 0) (hg0 : g.IsRoot 0) :
    IsProper ((toLine V).fromNormalization ≫ toSpec k) ∧
      Smooth ((toLine V).fromNormalization ≫ toSpec k) ∧
        IsIntegral (toLine V).normalization := by
  have := isFinite_fromNormalization V hg hg0
  have := isIntegral_left V hg
  exact ⟨inferInstance, ExposeX.smooth_of_forall_isRegularLocalRing_stalk _
    (isRegularLocalRing_stalk_normalization V hg hg0), inferInstance⟩

end Compactification

end SGA.SGA1.ExposeXIII.KummerCompactification
