/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.FormallySmooth
import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Flat

/-!
# SGA 1, Exposé III, 1.7 and 1.9: formal smoothness and smoothness

Proposition III.1.9 says that for a local homomorphism `A → B` with `B` a localization of an
`A`-algebra of finite type, `B` is smooth over `A` (in the sense of Exposé II, i.e.
`Algebra.FormallySmooth A B` for such local rings) if and only if it is formally smooth in the
sense of III.1.1, equivalently (III.2.1) formally smooth for the `𝔯(B)`-adic topology.

We prove this equivalence for the adic lifting property `AdicFormallySmooth`, over any
noetherian base ring. SGA reduces to a base field and uses the structure theory of complete
regular local rings; we argue instead with the Jacobian criterion of mathlib
(`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange`): for a presentation
`S = P ⧸ I` with `P` smooth, a lift of `S → S ⧸ 𝔫ᴺ` to `P ⧸ (𝔪 I + 𝔪ᴺ)` gives a derivation
splitting `I ⧸ 𝔪 I → κ ⊗ Ω_P`, once `N` is large enough for the Artin–Rees lemma to give
`𝔪ᴺ ∩ I ⊆ 𝔪 I`.

Combined with mathlib's fibrewise criterion, this also gives Corollary III.1.7 (flatness plus
formal smoothness of the closed fibre) for such local rings; III.1.7 for complete local rings with
finite residue extension is in `FlatFibre.lean`, and III.1.9 in the form of Definition III.1.1
(through the completions) is in `Completion.lean`.
-/

universe u

namespace SGA.SGA1.ExposeIII

open IsLocalRing TensorProduct

variable {R S P : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]
  [CommRing P] [Algebra R P] [Algebra P S] [IsScalarTower R P S]

/-- III.1.9, sufficiency, for a local algebra `S = P ⧸ I` presented by a noetherian formally
smooth `R`-algebra `P` with `Ω[P⁄R]` finite free and `I` finitely generated. -/
theorem formallySmooth_of_adicFormallySmooth_aux [IsNoetherianRing P]
    [Algebra.FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG)
    (h : AdicFormallySmooth R (maximalIdeal S)) : Algebra.FormallySmooth R S := by
  set I := RingHom.ker (algebraMap P S)
  set 𝔪 := (maximalIdeal S).comap (algebraMap P S)
  have : 𝔪.IsMaximal := Ideal.comap_isMaximal_of_surjective _ h₁
  have hI𝔪 : I ≤ 𝔪 := fun x hx ↦ by
    simp [𝔪, RingHom.mem_ker.mp hx]
  have hmap𝔪 : 𝔪.map (algebraMap P S) = maximalIdeal S := Ideal.map_comap_of_surjective _ h₁ _
  -- Artin–Rees
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔪 (I.restrictScalars P)
  set N := k + 1
  have hAR : 𝔪 ^ N ⊓ I ≤ 𝔪 * I := by
    intro x ⟨hxN, hxI⟩
    have hx : x ∈ 𝔪 ^ N • (⊤ : Submodule P P) ⊓ I.restrictScalars P :=
      ⟨by simpa [smul_eq_mul] using hxN, hxI⟩
    rw [hk N (by omega), show N - k = 1 by omega, pow_one] at hx
    exact (smul_mono_right _ inf_le_right : _ ≤ 𝔪 • I.restrictScalars P) hx
  -- the test ring `C = P ⧸ (𝔪 I + 𝔪ᴺ)` and the map `g : C → S ⧸ 𝔫ᴺ`
  set Q : Ideal P := 𝔪 * I ⊔ 𝔪 ^ N
  have hQ : Q ≤ RingHom.ker ((Ideal.Quotient.mkₐ R (maximalIdeal S ^ N)).comp
      (IsScalarTower.toAlgHom R P S)) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [RingHom.mem_ker, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
        RingHom.mem_ker.mp (Ideal.mul_le_right hx), map_zero]
    · intro x hx
      simp only [RingHom.mem_ker, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      rw [← hmap𝔪, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hx
  let g : P ⧸ Q →ₐ[R] S ⧸ maximalIdeal S ^ N := Ideal.Quotient.liftₐ Q _ hQ
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, rfl⟩ := h₁ y
    exact ⟨Ideal.Quotient.mk Q p, rfl⟩
  have hker : RingHom.ker g ≤ (I ⊔ 𝔪 ^ N).map (Ideal.Quotient.mk Q) := by
    intro y hy
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine Ideal.mem_map_of_mem _ ?_
    have : algebraMap P S c ∈ (𝔪 ^ N).map (algebraMap P S) := by
      rw [Ideal.map_pow, hmap𝔪, ← Ideal.Quotient.eq_zero_iff_mem]
      exact hy
    obtain ⟨m, hm, hmc⟩ := (Ideal.mem_map_iff_of_surjective _ h₁).mp this
    have : c - m ∈ I := by rw [RingHom.mem_ker, map_sub, hmc, sub_self]
    simpa using Submodule.add_mem_sup this hm
  have hsq : RingHom.ker g ^ 2 = ⊥ := by
    refine eq_bot_iff.mpr ((Ideal.pow_right_mono hker 2).trans ?_)
    rw [← Ideal.map_pow, ← Ideal.map_quotient_self Q]
    refine Ideal.map_mono ?_
    rw [pow_two, Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul]
    exact sup_le (sup_le (le_sup_of_le_left (Ideal.mul_mono_left hI𝔪))
      (le_sup_of_le_right Ideal.mul_le_left)) (sup_le (le_sup_of_le_right Ideal.mul_le_right)
      (le_sup_of_le_right Ideal.mul_le_left))
  obtain ⟨s, hs⟩ := h.exists_lift_of_surjective g hg ⟨2, hsq⟩
    (Ideal.Quotient.mkₐ R (maximalIdeal S ^ N)) ⟨N, fun x hx ↦ by
      rw [RingHom.mem_ker, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hx⟩
  -- the derivation `P → ker g` given by the difference of `P → C` and `P → S → C`
  set Kb := RingHom.ker g
  let f' : P →ₐ[R] P ⧸ Q := s.comp (IsScalarTower.toAlgHom R P S)
  have e : (Ideal.Quotient.mkₐ R Kb).comp f' = IsScalarTower.toAlgHom R P ((P ⧸ Q) ⧸ Kb) := by
    refine AlgHom.ext fun p ↦ ?_
    change Ideal.Quotient.mk Kb (s (algebraMap P S p)) =
      Ideal.Quotient.mk Kb (Ideal.Quotient.mk Q p)
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    exact congr($hs (algebraMap P S p))
  let D := derivationToSquareZeroOfLift Kb hsq f' e
  have hD (i : P) (hi : i ∈ I) : (D i : P ⧸ Q) = - Ideal.Quotient.mk Q i := by
    rw [derivationToSquareZeroOfLift_apply]
    change s (algebraMap P S i) - Ideal.Quotient.mk Q i = _
    rw [RingHom.mem_ker.mp hi, map_zero, zero_sub]
  have hkill (m : P) (hm : m ∈ 𝔪) (y : Kb) : m • y = 0 := by
    obtain ⟨c, hc, hcy⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
      (hker y.2)
    ext1
    change Ideal.Quotient.mk Q m * y = 0
    rw [← hcy, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hc
    rw [mul_add]
    exact add_mem ((le_sup_left : 𝔪 * I ≤ Q) (Ideal.mul_mem_mul hm ha))
      ((le_sup_right : 𝔪 ^ N ≤ Q) (Ideal.mul_mem_left _ m hb))
  -- the Jacobian criterion, with the residue field `P ⧸ 𝔪` of `S`
  let : Field (P ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let φ : S →+* P ⧸ 𝔪 := (Ideal.Quotient.factor hI𝔪).comp
    (RingHom.quotientKerEquivOfSurjective h₁).symm.toRingHom
  have hφ (p : P) : φ (algebraMap P S p) = Ideal.Quotient.mk 𝔪 p := by
    have : (RingHom.quotientKerEquivOfSurjective h₁).symm (algebraMap P S p) =
        Ideal.Quotient.mk I p := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, this]
    rfl
  let : Algebra S (P ⧸ 𝔪) := φ.toAlgebra
  have : IsScalarTower P S (P ⧸ 𝔪) := IsScalarTower.of_algebraMap_eq fun p ↦ (hφ p).symm
  have h₃ : maximalIdeal S ≤ RingHom.ker (algebraMap S (P ⧸ 𝔪)) := by
    intro x hx
    obtain ⟨p, rfl⟩ := h₁ x
    rw [RingHom.mem_ker, RingHom.algebraMap_toAlgebra, hφ, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange P (P ⧸ 𝔪) h₁ h₂ h₃,
    injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨i, rfl⟩ : ∃ i : I, (1 : P ⧸ 𝔪) ⊗ₜ[P] i = x := by
    obtain ⟨i, hi⟩ := Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul I 𝔪 x)
    refine ⟨i, ?_⟩
    rw [← quotTensorEquivQuotSMul_symm_mk, hi, LinearEquiv.symm_apply_apply]
  rw [KaehlerDifferential.cotangentComplexBaseChange_tmul, one_smul,
    KaehlerDifferential.kerToTensor_apply] at hx
  -- apply the derivation: `D i = 0` modulo `𝔪`, hence `D i = 0`
  have h2 := congrArg (D.liftKaehlerDifferential.lTensor (P ⧸ 𝔪)) hx
  rw [LinearMap.lTensor_tmul, LinearMap.map_zero,
    Derivation.liftKaehlerDifferential_comp_D] at h2
  have h3 := congrArg (quotTensorEquivQuotSMul Kb 𝔪) h2
  rw [quotTensorEquivQuotSMul_mk_one_tmul, LinearEquiv.map_zero,
    Submodule.Quotient.mk_eq_zero] at h3
  have hbot : 𝔪 • (⊤ : Submodule P Kb) = ⊥ :=
    eq_bot_iff.mpr (Submodule.smul_le.mpr fun m hm y _ ↦ by simp [hkill m hm y])
  rw [hbot, Submodule.mem_bot] at h3
  -- so `i ∈ Q`, and by Artin–Rees `i ∈ 𝔪 I`
  have h5 : (i : P) ∈ Q := by
    have := congrArg Subtype.val h3
    rw [hD i i.2, ZeroMemClass.coe_zero, neg_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  have h6 : (i : P) ∈ 𝔪 * I := by
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h5
    have hbI : b ∈ I := by
      rw [show b = i - a by rw [← hab]; ring]
      exact I.sub_mem i.2 (Ideal.mul_le_right ha)
    rw [← hab]
    exact add_mem ha (hAR ⟨hb, hbI⟩)
  have h7 : i ∈ 𝔪 • (⊤ : Submodule P I) := by
    rw [Submodule.mem_smul_top_iff]
    exact h6
  rw [← quotTensorEquivQuotSMul_symm_mk, (Submodule.Quotient.mk_eq_zero _).mpr h7,
    LinearEquiv.map_zero]

omit [IsLocalRing S] in
/-- A localization `S` of a finitely presented `R`-algebra is a quotient, by a finitely generated
ideal, of a localization of a polynomial ring in finitely many variables. -/
lemma exists_surjective_localization_mvPolynomial {P₀ : Type u} [CommRing P₀]
    [Algebra R P₀] [Algebra P₀ S] [IsScalarTower R P₀ S] [Algebra.FinitePresentation R P₀]
    (M : Submonoid P₀) [IsLocalization M S] :
    ∃ (n : ℕ) (M' : Submonoid (MvPolynomial (Fin n) R)) (fP : Localization M' →ₐ[R] S),
      Function.Surjective fP ∧ (RingHom.ker fP).FG := by
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R P₀)
  let M' := M.comap f₀
  let P' := Localization M'
  let fP : P' →ₐ[R] S := IsLocalization.liftAlgHom (M := M')
      (f := (IsScalarTower.toAlgHom R P₀ S).comp f₀) fun x ↦ by
    simpa using IsLocalization.map_units (M := M) _ ⟨f₀ x.1, x.2⟩
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := M') _ x ⟨s, hs⟩, ?_⟩
    simp [fP, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight]
  refine ⟨n, M', fP, hf₁, ?_⟩
  have := Algebra.FinitePresentation.ker_fG_of_surjective _ hf₀
  convert! this.map (algebraMap _ P')
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ by simp_all [fP])
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M' x
  obtain ⟨a, ha, e⟩ : ∃ a ∈ M, a * f₀ x = 0 := by
    simpa [fP, IsLocalization.lift_mk', IsLocalization.map_eq_zero_iff M] using hx
  obtain ⟨a, rfl⟩ := hf₀ a
  rw [IsLocalization.mk'_mem_map_algebraMap_iff]
  exact ⟨a, ha, by simpa⟩

/-- III.1.9: a local ring `S` which is a localization of an algebra of finite type over a
noetherian ring `R` is formally smooth over `R` (i.e. smooth in the sense of Exposé II) if and
only if it is formally smooth for its `𝔯(S)`-adic topology. -/
theorem formallySmooth_iff_adicFormallySmooth [IsNoetherianRing R] {P₀ : Type u} [CommRing P₀]
    [Algebra R P₀] [Algebra P₀ S] [IsScalarTower R P₀ S] [Algebra.FiniteType R P₀]
    (M : Submonoid P₀) [IsLocalization M S] :
    Algebra.FormallySmooth R S ↔ AdicFormallySmooth R (maximalIdeal S) := by
  refine ⟨fun _ ↦ .of_formallySmooth _, fun h ↦ ?_⟩
  have : Algebra.FinitePresentation R P₀ :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨n, M', fP, hf₁, hfP⟩ := exists_surjective_localization_mvPolynomial (R := R) (S := S) M
  let P' := Localization M'
  algebraize [fP.toRingHom]
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) R) P' := .of_isLocalization M'
  have : Algebra.FormallySmooth R P' := .comp _ (MvPolynomial (Fin n) R) _
  have : Module.Free P' Ω[P'⁄R] :=
    .of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin n) R) P')
  have : Module.Finite P' Ω[P'⁄R] := .equiv
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin n) R) P')
  have : IsNoetherianRing P' := IsLocalization.isNoetherianRing M' P' inferInstance
  exact formallySmooth_of_adicFormallySmooth_aux (P := P') hf₁ hfP h

/-- III.1.9, for the local ring of a finite type algebra at a prime: `A` is smooth over `R`
at `q` if and only if `A_q` is formally smooth over `R` for its adic topology. -/
theorem isSmoothAt_iff_adicFormallySmooth [IsNoetherianRing R] {A : Type u} [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A] (q : Ideal A) [q.IsPrime] :
    Algebra.IsSmoothAt R q ↔
      AdicFormallySmooth R (maximalIdeal (Localization.AtPrime q)) :=
  formallySmooth_iff_adicFormallySmooth q.primeCompl

/-- III.1.7 (for localizations of algebras of finite type over a noetherian local ring): `S` is
formally smooth over `R` if and only if it is flat over `R` and its closed fibre `k ⊗[R] S` is
formally smooth over the residue field `k`. -/
theorem adicFormallySmooth_iff_flat_and_formallySmooth_fiber [IsLocalRing R] [IsNoetherianRing R]
    [IsLocalHom (algebraMap R S)] {P₀ : Type u} [CommRing P₀] [Algebra R P₀] [Algebra P₀ S]
    [IsScalarTower R P₀ S] [Algebra.FiniteType R P₀] (M : Submonoid P₀) [IsLocalization M S] :
    AdicFormallySmooth R (maximalIdeal S) ↔ Module.Flat R S ∧
      Algebra.FormallySmooth (ResidueField R) (ResidueField R ⊗[R] S) := by
  have : Algebra.FinitePresentation R P₀ :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rw [← formallySmooth_iff_adicFormallySmooth M]
  refine ⟨fun _ ↦ ⟨?_, inferInstance⟩, fun ⟨_, _⟩ ↦
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (P := P₀) M⟩
  obtain ⟨n, M', fP, hf₁, -⟩ := exists_surjective_localization_mvPolynomial (R := R) (S := S) M
  have : IsNoetherianRing (Localization M') := IsLocalization.isNoetherianRing M' _ inferInstance
  have : Module.Flat R (Localization M') := .trans R (MvPolynomial (Fin n) R) _
  exact Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing fP hf₁

end SGA.SGA1.ExposeIII
