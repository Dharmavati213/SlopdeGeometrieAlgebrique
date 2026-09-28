/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Localization.BaseChange
import SGA.Foundations.CommAlg.RegularLocalRing
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Regular local rings are factorial

The theorem of Auslander–Buchsbaum: a regular local ring is a unique factorization domain
(`IsRegularLocalRing.uniqueFactorizationMonoid`, Stacks 0AG0; Matsumura, *Commutative Ring
Theory*, Th. 20.3). The proof is by induction on the dimension:

* choose `x ∈ 𝔪 \ 𝔪²`; `R/(x)` is regular, hence a domain, so `x` is prime, and by Nagata's
  criterion (`UniqueFactorizationMonoid.of_isLocalization_away`, Stacks 0AFU) it suffices that
  `S = R[1/x]` is factorial;
* by Kaplansky's criterion it suffices that every height-one prime `Q` of `S` is principal. The
  localizations of `S` at maximal ideals are regular of smaller dimension, hence factorial by
  induction, so `Q` is locally principal, hence projective
  (`Ideal.projective_of_isPrincipal_localization`);
* `Q ∩ R` has finite projective dimension over `R` (Serre), so `Q = S ⊗ (Q ∩ R)` is stably free
  (`exists_prod_linearEquiv_of_hasProjectiveDimensionLE`): `Q ⊕ Sᵃ ≅ Sᵃ⁺¹`
  (`Ideal.eq_add_one_of_prod_linearEquiv`), and a stably free ideal of rank one is principal
  (`Ideal.isPrincipal_of_prod_linearEquiv`, a determinant argument).
-/

universe u

open Ideal Matrix CategoryTheory TensorProduct

section Nagata

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]

/-- If `x` is prime and does not divide `q`, then `q ∣ xⁿ b` implies `q ∣ b`. -/
theorem Prime.dvd_of_dvd_pow_mul {x q b : R} (hx : Prime x) (hxq : ¬ x ∣ q) :
    ∀ n : ℕ, q ∣ x ^ n * b → q ∣ b := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rintro ⟨e, he⟩
    have hxe : x ∣ q * e := ⟨x ^ n * b, by rw [← he, pow_succ']; ring⟩
    obtain ⟨e', rfl⟩ := (hx.dvd_or_dvd hxe).resolve_left hxq
    apply ih
    refine ⟨e', mul_left_cancel₀ hx.ne_zero ?_⟩
    rw [← mul_assoc, ← pow_succ', he]
    ring

/-- Nagata's criterion (Stacks 0AFU): if `x` is a prime element of a noetherian domain `R` and
the localization `R[1/x]` is factorial, then `R` is factorial. -/
theorem UniqueFactorizationMonoid.of_isLocalization_away [IsNoetherianRing R] {x : R}
    (hx : Prime x) [IsLocalization.Away x S] [IsDomain S] [UniqueFactorizationMonoid S] :
    UniqueFactorizationMonoid R := by
  refine UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr fun P hP0 hP ↦ ?_
  by_cases hxP : x ∈ P
  · exact ⟨x, hxP, hx⟩
  have hdisj : Disjoint (Submonoid.powers x : Set R) P :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime x).mpr hxP
  have hPS : (P.map (algebraMap R S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x) S P hP hdisj
  have hcomap : (P.map (algebraMap R S)).comap (algebraMap R S) = P :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers x) S hP hdisj
  have hPS0 : P.map (algebraMap R S) ≠ ⊥ := by
    intro h
    apply hP0
    rw [← hcomap, h, ← RingHom.ker_eq_comap_bot, ← RingHom.injective_iff_ker_eq_bot]
    exact IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
  obtain ⟨p', hp'P, hp'⟩ := hPS.exists_mem_prime_of_ne_bot hPS0
  have hunit : ∀ k : ℕ, IsUnit (algebraMap R S (x ^ k)) := fun k ↦
    IsLocalization.map_units S (⟨x ^ k, k, rfl⟩ : Submonoid.powers x)
  obtain ⟨⟨a, _, k, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers x) p'
  change p' * algebraMap R S (x ^ k) = algebraMap R S a at ha
  have haS : Prime (algebraMap R S a) := by
    rw [← ha]
    exact (associated_mul_unit_right _ _ (hunit k)).prime hp'
  have haP : a ∈ P := by
    rw [← hcomap, Ideal.mem_comap, ← ha]
    exact Ideal.mul_mem_right _ _ hp'P
  have ha0 : a ≠ 0 := fun h ↦ haS.ne_zero (by rw [h, map_zero])
  obtain ⟨n, q, hxq, rfl⟩ := WfDvdMonoid.max_power_factor ha0 hx.irreducible
  have hqP : q ∈ P := (hP.mem_or_mem haP).resolve_left fun h ↦ hxP (hP.mem_of_pow_mem n h)
  refine ⟨q, hqP, ?_⟩
  have hqS : Prime (algebraMap R S q) := by
    rw [map_mul] at haS
    exact ((associated_unit_mul_left _ _ (hunit n)).prime_iff).mp haS
  refine ⟨fun h ↦ hqS.ne_zero (by rw [h, map_zero]), fun h ↦ hqS.not_isUnit (h.map _), ?_⟩
  intro b c hbc
  have key : ∀ b : R, algebraMap R S q ∣ algebraMap R S b → q ∣ b := by
    intro b ⟨s, hs⟩
    obtain ⟨⟨d, _, m, rfl⟩, hd⟩ := IsLocalization.surj (Submonoid.powers x) s
    change s * algebraMap R S (x ^ m) = algebraMap R S d at hd
    have : algebraMap R S (x ^ m * b) = algebraMap R S (q * d) := by
      rw [map_mul, map_mul, hs, ← hd]
      ring
    obtain ⟨⟨_, l, rfl⟩, hl⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers x) this
    simp only at hl
    exact hx.dvd_of_dvd_pow_mul hxq (l + m) ⟨x ^ l * d, by rw [pow_add, mul_assoc, hl]; ring⟩
  have hdiv : algebraMap R S q ∣ algebraMap R S b * algebraMap R S c := by
    rw [← map_mul]
    exact map_dvd (algebraMap R S) hbc
  rcases hqS.dvd_or_dvd hdiv with h | h
  · exact Or.inl (key b h)
  · exact Or.inr (key c h)

end Nagata

section StablyFree

variable {D : Type*} [CommRing D] [IsDomain D]

/-- An ideal `I` of a domain with `I ⊕ Dⁿ ≅ Dⁿ⁺¹` (a stably free ideal of rank one) is
principal. -/
theorem Ideal.isPrincipal_of_prod_linearEquiv (I : Ideal D) {n : ℕ}
    (e : (I × (Fin n → D)) ≃ₗ[D] (Fin (n + 1) → D)) : I.IsPrincipal := by
  classical
  by_cases hI : I = ⊥
  · exact hI ▸ bot_isPrincipal
  obtain ⟨b₀, hb₀I, hb₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  let w : Fin n → (Fin (n + 1) → D) := fun k ↦ e (0, Pi.single k 1)
  let v : I → (Fin (n + 1) → D) := fun b ↦ e (b, 0)
  -- the matrix with columns `u, w₀, …, wₙ₋₁`
  let M : (Fin (n + 1) → D) → Matrix (Fin (n + 1)) (Fin (n + 1)) D := fun u ↦
    Matrix.of fun i j ↦ (Fin.cons u w : Fin (n + 1) → Fin (n + 1) → D) j i
  have hM : ∀ u, M u = (M 0).updateCol 0 u := fun u ↦ by
    ext i j
    refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp [M]
  let φ : (Fin (n + 1) → D) →ₗ[D] D :=
    { toFun u := (M u).det
      map_add' u u' := by rw [hM, hM u, hM u', det_updateCol_add]
      map_smul' c u := by rw [hM, hM u, det_updateCol_smul]; rfl }
  have hφw : ∀ k, φ (w k) = 0 := fun k ↦
    det_zero_of_column_eq (i := 0) (j := k.succ) (Fin.succ_ne_zero k).symm fun i ↦ by simp [M]
  have hmulVec : ∀ u t, M u *ᵥ t = t 0 • u + ∑ k, t k.succ • w k := fun u t ↦ by
    ext i
    simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]
  -- decomposition of `e`
  have he : ∀ (b : I) (s : Fin n → D), e (b, s) = v b + ∑ k, s k • w k := by
    intro b s
    have : ((b, s) : I × (Fin n → D)) = (b, 0) + ∑ k, s k • ((0 : I), Pi.single k (1 : D)) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_add, Prod.fst_sum]
        simp
      · rw [Prod.snd_add, Prod.snd_sum]
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
    rw [this, map_add, map_sum]
    simp only [map_smul]
    rfl
  have hφe : ∀ (b : I) s, φ (e (b, s)) = φ (v b) := fun b s ↦ by
    rw [he, map_add, map_sum]
    simp [map_smul, hφw]
  -- the map `T u = (φ u, h u)`, where `e⁻¹ u = (g u, h u)`
  let h : (Fin (n + 1) → D) →ₗ[D] (Fin n → D) :=
    LinearMap.snd D I (Fin n → D) ∘ₗ e.symm.toLinearMap
  let T : (Fin (n + 1) → D) →ₗ[D] (Fin (n + 1) → D) :=
    LinearMap.pi (Fin.cons φ fun k ↦ LinearMap.proj k ∘ₗ h)
  have hTw : ∀ k, T (w k) = Pi.single k.succ 1 := by
    intro k
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [T, hφw]
    · simp [T, h, w, Pi.single_apply]
  -- `det T · φ u = φ u`
  let N : (Fin (n + 1) → D) → Matrix (Fin (n + 1)) (Fin (n + 1)) D := fun u ↦
    Matrix.of fun i j ↦ (Fin.cons (T u) (fun k ↦ Pi.single k.succ 1) :
      Fin (n + 1) → Fin (n + 1) → D) j i
  have hN : ∀ u, T ∘ₗ Matrix.toLin' (M u) = Matrix.toLin' (N u) := by
    intro u
    ext t i
    simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.toLin'_apply, hmulVec]
    rw [map_add, map_sum]
    simp only [map_smul, hTw]
    simp [N, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]
  have hNdet : ∀ u, (N u).det = φ u := by
    intro u
    rw [det_succ_row_zero, Fin.sum_univ_succ]
    have h1 : (N u).submatrix Fin.succ Fin.succ = 1 := by
      ext i k
      simp [N, Matrix.one_apply, Pi.single_apply]
    have h2 : (N u) 0 0 = φ u := by simp [N, T]
    have h3 : ∀ j : Fin n, N u 0 j.succ = 0 := fun j ↦ by
      simp [N, (Fin.succ_ne_zero j).symm]
    simp only [Fin.succAbove_zero, h1, h2, h3, det_one, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul, mul_one]
  have hdetT : ∀ u, LinearMap.det T * φ u = φ u := fun u ↦ by
    have := congrArg LinearMap.det (hN u)
    rw [LinearMap.det_comp, LinearMap.det_toLin', LinearMap.det_toLin', hNdet] at this
    exact this
  -- `φ (v b₀) ≠ 0`, since the matrix `(v b₀, w)` is injective
  let b₀' : I := ⟨b₀, hb₀I⟩
  have hv : ∀ (a : D) (b : I), a • v b = v (a • b) := fun a b ↦ by
    simp only [v, ← map_smul, Prod.smul_mk, smul_zero]
  have hne : φ (v b₀') ≠ 0 := by
    intro h0
    obtain ⟨t, ht, htv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hmulVec, hv, ← he] at htv
    have := e.injective (htv.trans (map_zero e).symm)
    rw [Prod.mk_eq_zero] at this
    have ht0 : t 0 = 0 := by
      have h1 := congrArg Subtype.val this.1
      simp only [Submodule.coe_smul, smul_eq_mul, ZeroMemClass.coe_zero, b₀'] at h1
      exact (mul_eq_zero.mp h1).resolve_right hb₀
    apply ht
    ext i
    refine Fin.cases ht0 (fun k ↦ ?_) i
    exact congrFun this.2 k
  have hdet : LinearMap.det T = 1 := by
    have := hdetT (v b₀')
    exact mul_right_cancel₀ hne (this.trans (one_mul _).symm)
  have hTsurj : Function.Surjective T := by
    have : IsUnit T := (LinearMap.isUnit_iff_isUnit_det T).mpr (hdet ▸ isUnit_one)
    exact (Module.End.isUnit_iff T).mp this |>.2
  obtain ⟨u₀, hu₀⟩ := hTsurj (Pi.single 0 1)
  have hφu₀ : φ u₀ = 1 := by
    have := congrFun hu₀ 0
    simpa [T] using this
  have hhu₀ : h u₀ = 0 := by
    ext k
    have := congrFun hu₀ k.succ
    simpa [T, Pi.single_apply, Fin.succ_ne_zero] using this
  let c : I := (e.symm u₀).1
  have hc : v c = u₀ := by
    have : e.symm u₀ = (c, 0) := Prod.ext rfl hhu₀
    rw [← e.apply_symm_apply u₀, this]
  have hcb : ∀ b : I, (b : D) = c * φ (v b) := by
    intro b
    have key : (c : D) • v b = (b : D) • v c := by
      rw [hv, hv]
      congr 1
      exact Subtype.ext (mul_comm _ _)
    have := congrArg φ key
    rw [map_smul, map_smul, hc, hφu₀, smul_eq_mul, smul_eq_mul, mul_one] at this
    exact this.symm
  refine ⟨⟨c, le_antisymm (fun b hb ↦ ?_) ?_⟩⟩
  · rw [Submodule.mem_span_singleton]
    exact ⟨φ (v ⟨b, hb⟩), by rw [smul_eq_mul, mul_comm]; exact (hcb ⟨b, hb⟩).symm⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact c.2

end StablyFree

/-- A finite free module is isomorphic to `Sᵇ` for some `b`. -/
theorem Module.exists_linearEquiv_fin_of_free (S : Type*) [CommRing S] (M : Type*)
    [AddCommGroup M] [Module S M] [Module.Free S M] [Module.Finite S M] :
    ∃ b : ℕ, Nonempty (M ≃ₗ[S] (Fin b → S)) := by
  let bM := Module.Free.chooseBasis S M
  exact ⟨_, ⟨bM.equivFun ≪≫ₗ LinearEquiv.funCongrLeft S S (Fintype.equivFin _).symm⟩⟩

/-- `Sᵃ × Sᵇ ≅ Sᵃ⁺ᵇ`. -/
noncomputable def finProdFinLinearEquiv (S : Type*) [CommRing S] (a b : ℕ) :
    ((Fin a → S) × (Fin b → S)) ≃ₗ[S] (Fin (a + b) → S) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) S S).symm ≪≫ₗ
    LinearEquiv.funCongrLeft S S finSumFinEquiv.symm

section FiniteProjectiveDimension

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Let `R` be a noetherian local ring and `S` a flat `R`-algebra. If a finite `R`-module `M` has
finite projective dimension and `S ⊗ M` is projective over `S`, then `S ⊗ M` is stably free:
`(S ⊗ M) × Sᵃ ≅ Sᵇ` for some `a, b`. -/
theorem exists_prod_linearEquiv_of_hasProjectiveDimensionLE (S : Type u) [CommRing S]
    [Algebra R S] [Module.Flat R S] (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      HasProjectiveDimensionLE (ModuleCat.of R M) n → Module.Projective S (S ⊗[R] M) →
        ∃ a b : ℕ, Nonempty (((S ⊗[R] M) × (Fin a → S)) ≃ₗ[S] (Fin b → S)) := by
  induction n with
  | zero =>
    intro M _ _ _ h _
    rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective] at h
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    obtain ⟨b, ⟨e⟩⟩ := Module.exists_linearEquiv_fin_of_free S (S ⊗[R] M)
    exact ⟨0, b, ⟨LinearEquiv.prodUnique ≪≫ₗ e⟩⟩
  | succ n ih =>
    intro M _ _ _ h hproj
    obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have : Projective (ModuleCat.of R (Fin m → R)) := by
      rw [← IsProjective.iff_projective]
      infer_instance
    have hK : HasProjectiveDimensionLE (ModuleCat.of R K) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n this).mp h
    -- base change of `0 → K → Rᵐ → M → 0`
    let f := K.subtype.baseChange S
    let g := π.baseChange S
    have hf : Function.Injective f := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ K.injective_subtype
    have hg : Function.Surjective g := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact LinearMap.lTensor_surjective S hπ
    have hfg : Function.Exact f g := by
      rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
      refine lTensor_exact S ?_ hπ
      intro y
      simp [K]
    obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id hg
    obtain ⟨e, -, -⟩ := hfg.splitSurjectiveEquiv hf ⟨l, hl⟩
    have : Module.Projective S (S ⊗[R] K) :=
      Module.Projective.of_split (e.symm.toLinearMap ∘ₗ LinearMap.inl S _ _)
        (LinearMap.fst S _ _ ∘ₗ e.toLinearMap) (by ext; simp)
    obtain ⟨a', b', ⟨eK⟩⟩ := ih K hK this
    obtain ⟨c, ⟨eF⟩⟩ := Module.exists_linearEquiv_fin_of_free S (S ⊗[R] (Fin m → R))
    refine ⟨b', c + a', ⟨?_⟩⟩
    exact (LinearEquiv.prodCongr (LinearEquiv.refl S _) eK.symm) ≪≫ₗ
      (LinearEquiv.prodAssoc S _ _ _).symm ≪≫ₗ
      LinearEquiv.prodCongr (LinearEquiv.prodComm S _ _ ≪≫ₗ e.symm ≪≫ₗ eF)
        (LinearEquiv.refl S _) ≪≫ₗ finProdFinLinearEquiv S c a'


end FiniteProjectiveDimension

/-- If `I × Dᵃ ≅ Dᵇ` for a nonzero ideal `I` of a domain `D`, then `b = a + 1`. -/
theorem Ideal.eq_add_one_of_prod_linearEquiv {D : Type*} [CommRing D] [IsDomain D] (I : Ideal D)
    (hI : I ≠ ⊥) {a b : ℕ} (e : (I × (Fin a → D)) ≃ₗ[D] (Fin b → D)) : b = a + 1 := by
  let ι : (I × (Fin a → D)) →ₗ[D] (Fin (1 + a) → D) :=
    (finProdFinLinearEquiv D 1 a).toLinearMap ∘ₗ
      LinearMap.prodMap ((LinearEquiv.funUnique (Fin 1) D D).symm.toLinearMap ∘ₗ I.subtype)
        LinearMap.id
  have hι : Function.Injective ι := by
    intro u v h
    have := (finProdFinLinearEquiv D 1 a).injective h
    simp only [LinearMap.prodMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, Prod.mk.injEq] at this
    exact Prod.ext (Subtype.ext ((LinearEquiv.funUnique (Fin 1) D D).symm.injective this.1))
      this.2
  obtain ⟨q, hqI, hq⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  let κ : (Fin (1 + a) → D) →ₗ[D] (I × (Fin a → D)) :=
    LinearMap.prodMap (LinearMap.toSpanSingleton D I ⟨q, hqI⟩ ∘ₗ
      (LinearEquiv.funUnique (Fin 1) D D).toLinearMap) LinearMap.id ∘ₗ
      (finProdFinLinearEquiv D 1 a).symm.toLinearMap
  have hκ : Function.Injective κ := by
    intro u v h
    apply (finProdFinLinearEquiv D 1 a).symm.injective
    simp only [κ, LinearMap.coe_comp, Function.comp_apply, LinearMap.prodMap_apply,
      LinearEquiv.coe_coe, Prod.mk.injEq, LinearMap.toSpanSingleton_apply] at h
    refine Prod.ext ((LinearEquiv.funUnique (Fin 1) D D).injective ?_) h.2
    have := congrArg Subtype.val h.1
    simp only [SetLike.val_smul, smul_eq_mul] at this
    exact mul_right_cancel₀ hq this
  have h1 := le_of_fin_injective D (ι ∘ₗ e.symm.toLinearMap) (hι.comp e.symm.injective)
  have h2 := le_of_fin_injective D (e.toLinearMap ∘ₗ κ) (e.injective.comp hκ)
  omega

/-- A principal ideal of a domain is a projective module. -/
theorem Ideal.projective_of_isPrincipal {T : Type*} [CommRing T] [IsDomain T] (J : Ideal T)
    [hJ : J.IsPrincipal] : Module.Projective T J := by
  obtain ⟨a, rfl⟩ := hJ.principal
  by_cases ha : a = 0
  · subst ha
    have : Subsingleton (Submodule.span T {(0 : T)}) := by
      rw [Submodule.span_zero_singleton]; infer_instance
    have : Module.Free T (Submodule.span T {(0 : T)}) := Module.Free.of_subsingleton _ _
    infer_instance
  · exact Module.Projective.of_equiv (LinearEquiv.toSpanNonzeroSingleton T T a ha)

/-- An ideal of a noetherian domain which is principal locally at every maximal ideal is a
projective module. -/
theorem Ideal.projective_of_isPrincipal_localization {S : Type*} [CommRing S] [IsDomain S]
    [IsNoetherianRing S] (Q : Ideal S)
    (h : ∀ (N : Ideal S) [N.IsMaximal],
      (Q.map (algebraMap S (Localization.AtPrime N))).IsPrincipal) :
    Module.Projective S Q := by
  have : Module.FinitePresentation S Q := Module.finitePresentation_of_finite _ _
  refine Module.projective_of_localization_maximal' (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Submodule.localized' (Localization.AtPrime P) P.primeCompl
      (Algebra.linearMap S (Localization.AtPrime P)) Q)
    (fun P _ ↦ Q.toLocalized' (Localization.AtPrime P) P.primeCompl
      (Algebra.linearMap S (Localization.AtPrime P))) fun N hN ↦ ?_
  rw [Ideal.localized'_eq_map]
  have := h N
  exact Ideal.projective_of_isPrincipal _


open IsLocalRing in
/-- **Auslander–Buchsbaum**: a regular local ring is factorial (Stacks 0AG0), by induction on the
dimension. -/
theorem IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_eq (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R], ringKrullDim R = d →
      UniqueFactorizationMonoid R := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro R _ _ hd
  by_cases hfield : IsField R
  · let := hfield.toField
    infer_instance
  have hd0 : d ≠ 0 := by
    rintro rfl
    apply hfield
    have hm : (maximalIdeal R).height = 0 := by
      have := maximalIdeal_height_eq_ringKrullDim (R := R)
      rw [hd] at this
      exact_mod_cast this
    rw [Ideal.height_eq_zero_iff_eq_bot] at hm
    exact isField_iff_maximalIdeal_eq.mpr hm
  have hpos : 0 < ringKrullDim R := by rw [hd]; exact_mod_cast Nat.pos_of_ne_zero hd0
  obtain ⟨x, hxm, hx2, -⟩ := exists_mem_maximalIdeal_notMem_sq_notMem_minimalPrimes hpos
  obtain ⟨-, hreg, -⟩ := IsRegularLocalRing.quotient_span_singleton hxm hx2
  have hx0 : x ≠ 0 := fun h ↦ hx2 (h ▸ zero_mem _)
  have hxprime : Prime x :=
    (Ideal.span_singleton_prime hx0).mp ((Ideal.Quotient.isDomain_iff_prime _).mp inferInstance)
  let S := Localization.Away x
  have : IsDomain S :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  suffices UniqueFactorizationMonoid S from
    UniqueFactorizationMonoid.of_isLocalization_away hxprime (S := S)
  rw [UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime]
  intro P hP0 hP
  obtain ⟨s, hsP, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le
    (show Ideal.span {s} ≤ P from (Ideal.span_singleton_le_iff_mem _).mpr hsP)
  have hQprime : Q.IsPrime := hQ.1.1
  have hsQ : s ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self s)
  have hQ0 : Q ≠ ⊥ := fun h ↦ hs0 (by rw [h] at hsQ; exact hsQ)
  have hQ1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
  -- every nonzero prime contained in `Q` is `Q`
  have hQmin : ∀ J : Ideal S, J.IsPrime → J ≠ ⊥ → J ≤ Q → J = Q := by
    intro J hJ hJ0 hJQ
    by_contra hne
    have := Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne hJQ hne)
    have h0 : J.height = 0 := by
      have := this.trans_le hQ1
      exact Order.lt_one_iff.mp this
    exact hJ0 (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  suffices hprinc : Q.IsPrincipal by
    obtain ⟨q, hq⟩ := hprinc.principal
    have hq0 : q ≠ 0 := fun h ↦ hQ0 (by rw [hq, h]; exact Submodule.span_zero_singleton _)
    refine ⟨q, hQP (hq ▸ Submodule.mem_span_singleton_self q), ?_⟩
    have : Q = Ideal.span {q} := hq
    rw [← Ideal.span_singleton_prime hq0, ← this]
    exact hQprime
  -- `Q` is locally principal
  have hloc : ∀ (N : Ideal S) [N.IsMaximal],
      (Q.map (algebraMap S (Localization.AtPrime N))).IsPrincipal := by
    intro N _
    let SN := Localization.AtPrime N
    by_cases hQN : Q ≤ N
    · have : IsLocalization.AtPrime SN (N.comap (algebraMap R S)) :=
        IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
          (Submonoid.powers x) SN N
      have : IsRegularLocalRing SN :=
        IsRegularLocalRing.of_isLocalization_atPrime (N.comap (algebraMap R S)) SN
      -- `dim S_N < dim R`
      have hlt : N.comap (algebraMap R S) < maximalIdeal R := by
        refine lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.comap _).ne_top) fun h ↦ ?_
        have hx : algebraMap R S x ∈ N := Ideal.mem_comap.mp (h ▸ hxm)
        exact (Ideal.IsMaximal.ne_top ‹N.IsMaximal›) (Ideal.eq_top_of_isUnit_mem N hx
          (IsLocalization.Away.algebraMap_isUnit (S := S) x))
      have hdimN := IsLocalization.AtPrime.ringKrullDim_eq_height (N.comap (algebraMap R S)) SN
      have hht := Ideal.height_strict_mono_of_isPrime hlt
      have hlt' : ringKrullDim SN < d := by
        rw [hdimN, ← hd, ← maximalIdeal_height_eq_ringKrullDim]
        exact_mod_cast hht
      have hdimN' := IsRegularLocalRing.ringKrullDim_eq_spanFinrank (R := SN)
      have : UniqueFactorizationMonoid SN := ih _ (by
        rw [hdimN'] at hlt'
        exact_mod_cast hlt') SN hdimN'
      -- `Q_N` is a nonzero prime of the factorial ring `S_N`
      have hdisj : Disjoint (N.primeCompl : Set S) Q :=
        Set.disjoint_left.mpr fun a ha haQ ↦ ha (hQN haQ)
      have hQNprime : (Q.map (algebraMap S SN)).IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint N.primeCompl SN Q hQprime hdisj
      have hQNcomap : (Q.map (algebraMap S SN)).comap (algebraMap S SN) = Q :=
        IsLocalization.under_map_of_isPrime_disjoint N.primeCompl SN hQprime hdisj
      have hinj : Function.Injective (algebraMap S SN) :=
        IsLocalization.injective SN N.primeCompl_le_nonZeroDivisors
      have hQN0 : Q.map (algebraMap S SN) ≠ ⊥ := by
        intro h0
        apply hs0
        apply hinj
        rw [map_zero, ← Submodule.mem_bot (R := SN), ← h0]
        exact Ideal.mem_map_of_mem _ hsQ
      obtain ⟨p, hpQ, hp⟩ := hQNprime.exists_mem_prime_of_ne_bot hQN0
      let J := (Ideal.span {p}).comap (algebraMap S SN)
      have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
      have hJprime : J.IsPrime := Ideal.IsPrime.comap _
      have hJQ : J ≤ Q := by
        rw [← hQNcomap]
        exact Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).mpr hpQ)
      have hJ0 : J ≠ ⊥ := by
        obtain ⟨⟨a, t⟩, ha⟩ := IsLocalization.surj N.primeCompl p
        intro hJ0
        have haJ : a ∈ J := by
          rw [Ideal.mem_comap, ← ha]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self p)
        rw [hJ0, Submodule.mem_bot] at haJ
        rw [haJ, map_zero, mul_eq_zero] at ha
        exact hp.ne_zero (ha.resolve_right
          (IsLocalization.map_units SN t).ne_zero)
      have hJQ' := hQmin J hJprime hJ0 hJQ
      rw [← hJQ', IsLocalization.map_under N.primeCompl SN]
      exact ⟨⟨p, rfl⟩⟩
    · obtain ⟨q, hqQ, hqN⟩ := Set.not_subset.mp hQN
      have : Q.map (algebraMap S SN) = ⊤ := Ideal.eq_top_of_isUnit_mem _
        (Ideal.mem_map_of_mem _ hqQ) ((IsLocalization.AtPrime.isUnit_to_map_iff SN N q).mpr hqN)
      rw [this]
      infer_instance
  have hQproj : Module.Projective S Q := Ideal.projective_of_isPrincipal_localization Q hloc
  -- `Q` is stably free, since `Q ∩ R` has finite projective dimension over `R`
  let Q' := Q.comap (algebraMap R S)
  let f := Q'.toLocalized' S (Submonoid.powers x) (Algebra.linearMap R S)
  have hbase := IsLocalizedModule.isBaseChange (Submonoid.powers x) S f
  have hQ'Q : Submodule.localized' S (Submonoid.powers x) (Algebra.linearMap R S) Q' = Q := by
    rw [Ideal.localized'_eq_map]
    exact IsLocalization.map_under (Submonoid.powers x) S Q
  let e : (S ⊗[R] Q') ≃ₗ[S] Q := hbase.equiv ≪≫ₗ LinearEquiv.ofEq _ _ hQ'Q
  have hpd : HasProjectiveDimensionLE (ModuleCat.of R Q') d :=
    IsRegularLocalRing.hasProjectiveDimensionLE hd _
  have : Module.Projective S (S ⊗[R] Q') := Module.Projective.of_equiv e.symm
  obtain ⟨a, b, ⟨eQ⟩⟩ := exists_prod_linearEquiv_of_hasProjectiveDimensionLE S d Q' hpd this
  let eQ' : (Q × (Fin a → S)) ≃ₗ[S] (Fin b → S) :=
    (e.symm.prodCongr (LinearEquiv.refl _ _)) ≪≫ₗ eQ
  obtain rfl := Ideal.eq_add_one_of_prod_linearEquiv Q hQ0 eQ'
  exact Ideal.isPrincipal_of_prod_linearEquiv Q eQ'

/-- **Auslander–Buchsbaum**: a regular local ring is factorial (Stacks 0AG0). -/
instance IsRegularLocalRing.uniqueFactorizationMonoid (R : Type u) [CommRing R]
    [IsRegularLocalRing R] : UniqueFactorizationMonoid R :=
  uniqueFactorizationMonoid_of_ringKrullDim_eq _ R ringKrullDim_eq_spanFinrank
