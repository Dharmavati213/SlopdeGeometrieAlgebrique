/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.AbhyankarPurity

/-!
# SGA 1, Exposé XIII, 5.2–5.3: the extension for all exponents and the descent argument

* XIII.5.2, extension part, without any assumption on the characteristic
  (`exists_etale_kummerAlgebra_of_isTamelyRamifiedAlong_of_pos`, `absoluteAbhyankar_extension`):
  at a maximal point of `V(T_j)` in `X' = X[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`, the covering becomes étale after
  the tame root adjunction `R[T']/(T'^m - f_j)`, `R = A_(f_j)`, and stays so after any further base
  change to a normal domain (`formallyEtale_integralClosure_tensorProduct`, by I.9.5).
* SGA's descent argument showing that the `nᵢ` may be taken prime to `p`
  (`mem_range_of_formallyUnramified_integralClosure`): `X' → X₂ = X[Tᵢ]/(Tᵢ^{n'ᵢ} - fᵢ)` is radicial
  modulo `p`, and two sections of a formally unramified algebra that agree modulo a nilpotent
  ideal are equal (`tmul_eq_of_formallyUnramified`).
* XIII.5.3 over every strictly henselian regular local ring
  (`exists_injective_kummerAlgebra_of_isStrictlyHenselian`).
-/

universe u

open IsLocalRing Polynomial
open scoped TensorProduct

namespace SGA.SGA1.ExposeXIII

/-- The normalization of an integrally closed domain `S` in a localization `C = D[1/t]` of a finite
smooth `S`-algebra `D` is `D` (I.9.5: `D` is integrally closed in `D ⊗_S Frac S`). -/
theorem exists_algEquiv_integralClosure_of_isLocalization_away {S D C : Type u} [CommRing S]
    [IsDomain S] [IsIntegrallyClosed S] [CommRing D] [Algebra S D] [Algebra.Smooth S D]
    [Algebra.IsIntegral S D] [CommRing C] [Algebra S C] [Algebra D C] [IsScalarTower S D C]
    {t : S} (ht : t ≠ 0) [IsLocalization.Away (algebraMap S D t) C] :
    ∃ e : D ≃ₐ[S] integralClosure S C, ∀ d, (e d : C) = algebraMap D C d := by
  have ht' : t ∈ nonZeroDivisors S := mem_nonZeroDivisors_of_ne_zero ht
  -- `D → C` is injective
  have hinj : Function.Injective (algebraMap D C) := by
    refine IsLocalization.injective (M := Submonoid.powers (algebraMap S D t)) C ?_
    rintro _ ⟨k, rfl⟩
    change (algebraMap S D) t ^ k ∈ nonZeroDivisors D
    rw [← map_pow, mem_nonZeroDivisors_iff_right]
    intro y hy
    have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := D) (pow_mem ht' k)
    exact this.right_eq_zero_of_smul (by rwa [Algebra.smul_def, mul_comm])
  -- `ι : C → D ⊗_S Frac S`
  let F := FractionRing S
  have hIC : IsIntegrallyClosedIn D (D ⊗[S] F) :=
    SGA.SGA1.ExposeI.isIntegrallyClosedIn_tensor_fractionRing F
  have hinjF : Function.Injective (algebraMap D (D ⊗[S] F)) :=
    SGA.SGA1.ExposeI.injective_algebraMap_tensor_fractionRing F
  have hu : IsUnit (algebraMap D (D ⊗[S] F) (algebraMap S D t)) := by
    rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply',
      ← Algebra.TensorProduct.includeRight_apply]
    exact (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective S F)).mpr
      ht)).map _
  let ι : C →+* D ⊗[S] F := IsLocalization.Away.lift _ hu
  have hι (d : D) : ι (algebraMap D C d) = algebraMap D (D ⊗[S] F) d :=
    IsLocalization.Away.lift_eq _ hu d
  have hιinj : Function.Injective ι := by
    refine (injective_iff_map_eq_zero ι).mpr fun x hx ↦ ?_
    obtain ⟨d, ⟨y, hy⟩, rfl⟩ := IsLocalization.exists_mk'_eq
      (Submonoid.powers (algebraMap S D t)) x
    have h1 : ι (IsLocalization.mk' C d ⟨y, hy⟩) * ι (algebraMap D C y) =
        ι (algebraMap D C d) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    rw [hx, zero_mul, hι] at h1
    have h2 : d = 0 := hinjF (by rw [← h1, map_zero])
    rw [h2, IsLocalization.mk'_zero]
  let ιS : C →ₐ[S] D ⊗[S] F :=
    { ι with
      commutes' := fun s ↦ by
        change ι (algebraMap S C s) = _
        rw [IsScalarTower.algebraMap_apply S D C, hι, ← IsScalarTower.algebraMap_apply] }
  -- `D → integralClosure S C`
  let φ : D →ₐ[S] integralClosure S C :=
    (IsScalarTower.toAlgHom S D C).codRestrict (integralClosure S C) fun d ↦
      (Algebra.IsIntegral.isIntegral (R := S) d).map (IsScalarTower.toAlgHom S D C)
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y h ↦ hinj (congrArg Subtype.val h), fun x ↦ ?_⟩
    have h1 : IsIntegral D (ι x.1) := (x.2.map ιS).tower_top
    obtain ⟨d, hd⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp h1
    refine ⟨d, Subtype.ext (hιinj ?_)⟩
    change ι (algebraMap D C d) = ι x.1
    rw [hι, hd]
  exact ⟨AlgEquiv.ofBijective φ hφ, fun _ ↦ rfl⟩


/-- For a discrete valuation ring `R` with uniformizer `π` and fraction field `K`, an `R`-algebra
`S₀` and an integral `K`-algebra `C` over `S₀`, `C` is the localization at `π` of the
normalization of `S₀` in `C`. -/
theorem isLocalization_powers_integralClosure_of_isScalarTower {R : Type*} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {π : R} (hπ : Irreducible π) (S₀ C : Type*) [CommRing S₀] [Algebra R S₀]
    [CommRing C] [Algebra K C] [Algebra R C] [IsScalarTower R K C] [Algebra S₀ C]
    [IsScalarTower R S₀ C] [Algebra.IsIntegral K C] :
    IsLocalization (Submonoid.powers (algebraMap S₀ (integralClosure S₀ C) (algebraMap R S₀ π)))
      C where
  map_units := by
    rintro ⟨_, k, rfl⟩
    have h : IsUnit (algebraMap R K π) := isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hπ.ne_zero)
    change IsUnit (((algebraMap S₀ (integralClosure S₀ C) (algebraMap R S₀ π) ^ k :
      integralClosure S₀ C)) : C)
    rw [SubmonoidClass.coe_pow]
    change IsUnit (algebraMap S₀ C (algebraMap R S₀ π) ^ k)
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R K C]
    exact (h.map _).pow k
  surj z := by
    obtain ⟨⟨m, hm⟩, hmz⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := K)
      (nonZeroDivisors R) z (Algebra.IsIntegral.isIntegral z)
    obtain ⟨k, u, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hm) hπ
    have hint : IsIntegral R (π ^ k • z) := by
      have := hmz.smul (((u⁻¹ : Rˣ) : R))
      rwa [Submonoid.smul_def, smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
    refine ⟨⟨⟨π ^ k • z, hint.tower_top⟩, ⟨_, k, rfl⟩⟩, ?_⟩
    change z * ((algebraMap S₀ (integralClosure S₀ C) (algebraMap R S₀ π) ^ k :
      integralClosure S₀ C) : C) = π ^ k • z
    rw [SubmonoidClass.coe_pow, Algebra.smul_def, map_pow, mul_comm]
    rw [IsScalarTower.algebraMap_apply R S₀ C]
    rfl
  exists_of_eq h := ⟨1, by simpa using Subtype.ext h⟩

/-- XIII.5.2 for a discrete valuation ring `R` (uniformizer `π`, fraction field `K`), after an
arbitrary base change: let `B` be a finite étale `K`-algebra whose normalization over `R` is
tamely ramified with ramification indices dividing `n` (`n` prime to the residue
characteristic), and `S'` an integrally closed domain over `S₀ = R[T]/(Tⁿ - π)` in which `π ≠ 0`.
Then the normalization of `S'` in `S' ⊗_R B` is formally étale over `S'`: it is `S' ⊗_{S₀} W₀`,
`W₀` the (finite étale, `etale_integralClosure_of_forall_isTamelyRamifiedOver`) normalization
of `S₀` in `S₀ ⊗_R B`, by I.9.5 (`exists_algEquiv_integralClosure_of_isLocalization_away`). Unlike
`formallyEtale_integralClosure_of_forall_isTamelyRamifiedAt`, `S'` need not be étale over `S₀`
up to the factor `R[T]/(Tⁿ - π)`. -/
theorem formallyEtale_integralClosure_tensorProduct (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] (π : R)
    [Fact (Irreducible π)] (n : ℕ) [NeZero n] (hnR : (n : R) ∉ maximalIdeal R)
    (B : Type u) [CommRing B] [Algebra K B] [Algebra R B] [IsScalarTower R K B]
    [Module.Finite K B] [Algebra.Etale K B]
    (hB : ∀ (Q : Ideal (integralClosure R B)) [Q.IsPrime], Q.LiesOver (maximalIdeal R) →
      IsTamelyRamifiedAt R Q ∧ Q.ramificationIdx R ∣ n)
    (S' : Type u) [CommRing S'] [IsDomain S'] [IsIntegrallyClosed S'] [Algebra R S']
    [Algebra (AdjoinRoot (X ^ n - C π)) S'] [IsScalarTower R (AdjoinRoot (X ^ n - C π)) S']
    (hπ : algebraMap R S' π ≠ 0) :
    Algebra.FormallyEtale S' (integralClosure S' (S' ⊗[R] B)) := by
  classical
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  have : IsReduced B := Algebra.FormallyUnramified.isReduced_of_field K B
  have hfac := forall_factors_of_forall_isTamelyRamifiedAt (R := R) B n hB
  -- `C₀ = S₀ ⊗_R B` as a `K`-algebra, generated over `S₀` by `B`
  let : Algebra K (AdjoinRoot (X ^ n - C π) ⊗[R] B) :=
    ((Algebra.TensorProduct.includeRight (R := R) (A := AdjoinRoot (X ^ n - C π))
      (B := B)).toRingHom.comp (algebraMap K B)).toAlgebra
  have : IsScalarTower R K (AdjoinRoot (X ^ n - C π) ⊗[R] B) := .of_algebraMap_eq fun r ↦ by
    change _ = Algebra.TensorProduct.includeRight (algebraMap K B (algebraMap R K r))
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  let β : B →ₐ[K] AdjoinRoot (X ^ n - C π) ⊗[R] B :=
    { Algebra.TensorProduct.includeRight with commutes' := fun _ ↦ rfl }
  have hgen (c : AdjoinRoot (X ^ n - C π) ⊗[R] B) :
      c ∈ Algebra.adjoin (AdjoinRoot (X ^ n - C π)) (Set.range β) := by
    induction c using TensorProduct.induction_on with
    | zero => exact Subalgebra.zero_mem _
    | tmul s b =>
      have : s ⊗ₜ[R] b = s • β b := by
        change _ = s • ((1 : AdjoinRoot (X ^ n - C π)) ⊗ₜ[R] b)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self b)) s
    | add x y hx hy => exact Subalgebra.add_mem _ hx hy
  have hW := etale_integralClosure_of_forall_isTamelyRamifiedOver R K π n hnR
    (AdjoinRoot (X ^ n - C π)) AlgEquiv.refl B (fun M ↦ (hfac M).1) (fun M ↦ (hfac M).2)
    (AdjoinRoot (X ^ n - C π) ⊗[R] B) β hgen
  -- `W₀ = integralClosure S₀ C₀` and `C₀ = W₀[1/π]`
  obtain ⟨_, _⟩ := hW
  have : Algebra.IsIntegral K (AdjoinRoot (X ^ n - C π) ⊗[R] B) := ⟨fun c ↦ by
    induction c using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul s b =>
      have hs : IsIntegral K (s ⊗ₜ[R] (1 : B)) :=
        ((Algebra.IsIntegral.isIntegral (R := R) s).map
          (Algebra.TensorProduct.includeLeft (S := R) (B := B))).tower_top
      have hb : IsIntegral K (β b) := (Algebra.IsIntegral.isIntegral (R := K) b).map β
      have : s ⊗ₜ[R] b = s ⊗ₜ[R] (1 : B) * β b := by
        change _ = s ⊗ₜ[R] (1 : B) * (1 : AdjoinRoot (X ^ n - C π)) ⊗ₜ[R] b
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact hs.mul hb
    | add x y hx hy => exact hx.add hy⟩
  have hloc := isLocalization_powers_integralClosure_of_isScalarTower (K := K)
    (Fact.out : Irreducible π) (AdjoinRoot (X ^ n - C π)) (AdjoinRoot (X ^ n - C π) ⊗[R] B)
  -- `D = S' ⊗_{S₀} W₀`, finite étale over `S'`, and `S' ⊗_{S₀} C₀ = D[1/π]`
  let W₀ := integralClosure (AdjoinRoot (X ^ n - C π)) (AdjoinRoot (X ^ n - C π) ⊗[R] B)
  let D := S' ⊗[AdjoinRoot (X ^ n - C π)] W₀
  let C₁ := S' ⊗[AdjoinRoot (X ^ n - C π)] (AdjoinRoot (X ^ n - C π) ⊗[R] B)
  let μ : D →ₐ[S'] C₁ := Algebra.TensorProduct.map (AlgHom.id S' S')
    (IsScalarTower.toAlgHom (AdjoinRoot (X ^ n - C π)) W₀ (AdjoinRoot (X ^ n - C π) ⊗[R] B))
  let : Algebra D C₁ := μ.toRingHom.toAlgebra
  have : IsScalarTower S' D C₁ := IsScalarTower.of_algHom μ
  have hloc₁ := IsLocalization.tensorProduct_tensorProduct_right (AdjoinRoot (X ^ n - C π)) S'
    (Submonoid.powers (algebraMap (AdjoinRoot (X ^ n - C π)) W₀ (algebraMap R _ π)))
    (AdjoinRoot (X ^ n - C π) ⊗[R] B) (by
      ext x
      change μ (1 ⊗ₜ x) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl)
  have hpow : (Submonoid.powers (algebraMap (AdjoinRoot (X ^ n - C π)) W₀
      (algebraMap R _ π))).map (Algebra.TensorProduct.includeRight (R := AdjoinRoot (X ^ n - C π))
        (A := S')) = Submonoid.powers (algebraMap S' D (algebraMap R S' π)) := by
    rw [Submonoid.map_powers]
    congr 1
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R (AdjoinRoot (X ^ n - C π)) S',
      ← IsScalarTower.algebraMap_apply (AdjoinRoot (X ^ n - C π)) S' D]
  have : IsLocalization.Away (algebraMap S' D (algebraMap R S' π)) C₁ := by
    change IsLocalization (Submonoid.powers _) C₁
    rw [← hpow]
    exact hloc₁
  -- `S' ⊗_R B ≅ S' ⊗_{S₀} C₀`
  let eC : C₁ ≃ₐ[S'] S' ⊗[R] B :=
    Algebra.TensorProduct.cancelBaseChange R (AdjoinRoot (X ^ n - C π)) S' S' B
  let : Algebra D (S' ⊗[R] B) := ((eC : C₁ →ₐ[S'] S' ⊗[R] B).comp μ).toRingHom.toAlgebra
  have : IsScalarTower S' D (S' ⊗[R] B) :=
    IsScalarTower.of_algHom ((eC : C₁ →ₐ[S'] S' ⊗[R] B).comp μ)
  have : IsLocalization.Away (algebraMap S' D (algebraMap R S' π)) (S' ⊗[R] B) :=
    IsLocalization.isLocalization_of_algEquiv _
      (AlgEquiv.ofRingEquiv (f := eC.toRingEquiv) fun _ ↦ rfl : C₁ ≃ₐ[D] S' ⊗[R] B)
  obtain ⟨e, -⟩ := exists_algEquiv_integralClosure_of_isLocalization_away (S := S') (D := D)
    (C := S' ⊗[R] B) hπ
  exact Algebra.FormallyEtale.of_equiv e


/-- Base change and localization: let `N` be a submonoid of `A`, `R = N⁻¹A`, `S'` and `C'` the
localizations at `N` of an `A`-algebra `S` and of `S ⊗_A B`, and `B_K` an `R`-algebra generated
over a localization `K` of `A` by the image of `B`, mapping to `C'` compatibly with `B`. Then
`S' ⊗_R B_K → C'` is bijective (in the application `K = Frac A`, `B_K = K ⊗_A B`, and the elements
of `A - {0}` are units in `C'`). -/
theorem bijective_lift_tensorProduct_of_isLocalization {A S B R K BK S' C' : Type*} [CommRing A]
    [CommRing S] [CommRing B] [CommRing R] [CommRing K] [CommRing BK] [CommRing S'] [CommRing C']
    [Algebra A S] [Algebra A B] [Algebra A R] [Algebra A K] [Algebra R K] [IsScalarTower A R K]
    [Algebra K BK] [Algebra R BK] [Algebra A BK] [IsScalarTower R K BK] [IsScalarTower A R BK]
    [IsScalarTower A K BK]
    [Algebra S S'] [Algebra A S'] [Algebra R S'] [IsScalarTower A S S'] [IsScalarTower A R S']
    [Algebra (S ⊗[A] B) C'] [Algebra S' C'] [Algebra S C'] [Algebra A C'] [Algebra R C']
    [Algebra K C'] [IsScalarTower S S' C'] [IsScalarTower S (S ⊗[A] B) C'] [IsScalarTower A S C']
    [IsScalarTower R S' C'] [IsScalarTower R K C'] [IsScalarTower A K C']
    (N : Submonoid A) [IsLocalization (Algebra.algebraMapSubmonoid S N) S']
    (M : Submonoid A) [IsLocalization M K]
    [IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[A] B) (Algebra.algebraMapSubmonoid S N)) C']
    (ιB : B →ₐ[A] BK) (hgen : ∀ y, y ∈ Algebra.adjoin K (Set.range ιB)) (β : BK →ₐ[K] C')
    (hβ : ∀ b, β (ιB b) = algebraMap (S ⊗[A] B) C' (1 ⊗ₜ b)) :
    Function.Bijective (Algebra.TensorProduct.lift (Algebra.ofId S' C') (β.restrictScalars R)
      (fun _ _ ↦ Commute.all _ _) : S' ⊗[R] BK →ₐ[S'] C') := by
  have : IsScalarTower A (S ⊗[A] B) C' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A S (S ⊗[A] B),
      ← IsScalarTower.algebraMap_apply S (S ⊗[A] B) C', ← IsScalarTower.algebraMap_apply]
  set F : S' ⊗[R] BK →ₐ[S'] C' := Algebra.TensorProduct.lift (S := S') (Algebra.ofId S' C')
    (β.restrictScalars R) (fun _ _ ↦ Commute.all _ _)
  -- `G₀ : S ⊗_A B → S' ⊗_R B_K`
  let g₁ : S →ₐ[A] S' ⊗[R] BK :=
    ((Algebra.TensorProduct.includeLeft (R := R) (S := S') (B := BK)).restrictScalars A).comp
      (IsScalarTower.toAlgHom A S S')
  let g₂ : B →ₐ[A] S' ⊗[R] BK :=
    ((Algebra.TensorProduct.includeRight (R := R) (A := S') (B := BK)).restrictScalars A).comp ιB
  let G₀ : S ⊗[A] B →ₐ[A] S' ⊗[R] BK := Algebra.TensorProduct.lift g₁ g₂ fun _ _ ↦ Commute.all _ _
  have hG₀ (s : S) : G₀ (algebraMap S (S ⊗[A] B) s) = algebraMap S S' s ⊗ₜ 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  have hunitsG : ∀ y : Algebra.algebraMapSubmonoid (S ⊗[A] B) (Algebra.algebraMapSubmonoid S N),
      IsUnit (G₀ y) := by
    rintro ⟨_, s, hs, rfl⟩
    rw [hG₀]
    exact (IsLocalization.map_units S' (⟨s, hs⟩ : Algebra.algebraMapSubmonoid S N)).map
      (Algebra.TensorProduct.includeLeft (R := R) (S := S') (B := BK))
  let G : C' →+* S' ⊗[R] BK := IsLocalization.lift (g := G₀.toRingHom) hunitsG
  have hG (t : S ⊗[A] B) : G (algebraMap _ _ t) = G₀ t := IsLocalization.lift_eq hunitsG t
  -- `G ∘ F = id`
  have hGS (s : S') : G (algebraMap S' C' s) = s ⊗ₜ 1 := by
    have : G.comp (algebraMap S' C') =
        (Algebra.TensorProduct.includeLeft (R := R) (S := S') (B := BK)).toRingHom := by
      refine IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid S N) (RingHom.ext fun s ↦ ?_)
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S (S ⊗[A] B), hG, hG₀]
      rfl
    exact DFunLike.congr_fun this s
  have hGK (k : K) : G (algebraMap K C' k) = 1 ⊗ₜ algebraMap K BK k := by
    let hK : K →ₐ[A] S' ⊗[R] BK :=
      ((Algebra.TensorProduct.includeRight (R := R) (A := S') (B := BK)).restrictScalars A).comp
        ((IsScalarTower.toAlgHom K K BK).restrictScalars A)
    have : G.comp (algebraMap K C') = hK.toRingHom := by
      refine IsLocalization.ringHom_ext M (RingHom.ext fun a ↦ ?_)
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A (S ⊗[A] B), hG,
        AlgHom.commutes]
      exact (hK.commutes a).symm
    rw [show G (algebraMap K C' k) = (G.comp (algebraMap K C')) k from rfl, this]
    rfl
  have hGβ (y : BK) : G (β y) = 1 ⊗ₜ y := by
    have hy := hgen y
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [hβ, hG, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    | algebraMap k => rw [AlgHom.commutes, hGK]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, TensorProduct.tmul_add]
    | mul x y _ _ hx hy =>
      rw [map_mul, map_mul, hx, hy, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hGF (x : S' ⊗[R] BK) : G (F x) = x := by
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul s y =>
      rw [Algebra.TensorProduct.lift_tmul, map_mul, Algebra.ofId_apply, hGS]
      change _ * G (β y) = _
      rw [hGβ, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  -- `F ∘ G = id`
  have hFG (c : C') : F (G c) = c := by
    have : (F.toRingHom.comp G).comp (algebraMap (S ⊗[A] B) C') = algebraMap (S ⊗[A] B) C' := by
      refine RingHom.ext fun t ↦ ?_
      simp only [RingHom.comp_apply]
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, map_zero]
      | tmul s b =>
        rw [hG, Algebra.TensorProduct.lift_tmul, map_mul]
        change F (algebraMap S S' s ⊗ₜ 1) * F (1 ⊗ₜ ιB b) = _
        rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one, mul_one,
          map_one, one_mul]
        change algebraMap S' C' (algebraMap S S' s) * β (ιB b) = _
        rw [hβ, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S (S ⊗[A] B),
          ← map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    have h2 := IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (S ⊗[A] B)
      (Algebra.algebraMapSubmonoid S N)) (j := F.toRingHom.comp G) (k := RingHom.id C')
      (by rw [this, RingHom.id_comp])
    exact DFunLike.congr_fun h2 c
  exact ⟨Function.LeftInverse.injective hGF, Function.RightInverse.surjective hFG⟩

set_option maxHeartbeats 1600000 in
-- the instance problems on the localizations of `S ⊗_A B` are large
/-- XIII.5.2, the input in codimension one, without any assumption on the other `nᵢ`: let `A` be
a regular local ring, `f₁, …, f_r` part of a regular system of parameters, `B` a finite étale
`A[1/∏ fᵢ]`-algebra tamely ramified along `Σ div fᵢ`, and `S` an integrally closed domain
containing `A` and an `n_j`-th root `T` of `f_j`, where `n_j` is a multiple of the ramification
indices above `(f_j)`. Then, `N` denoting the complement of `(f_j)` in `A`, the normalization of
`N⁻¹S` in `N⁻¹(S ⊗_A B)` is formally étale over `N⁻¹S`. We apply
`formallyEtale_integralClosure_tensorProduct` over the discrete valuation ring `R = A_(f_j)` with
`S₀ = R[T']/(T'^m - f_j)`, `m = gcd(n_j, n)` for a multiple `n` of the ramification indices which
is nonzero in `κ((f_j))` (`exists_ramificationIdx_dvd_of_isTamelyRamifiedAlong`), mapping `T'` to
`T^{n_j/m}`, and identify `N⁻¹(S ⊗_A B)` with `N⁻¹S ⊗_R (K ⊗_A B)`. -/
theorem formallyEtale_integralClosure_localization_of_pow_eq (A : Type u) [CommRing A]
    [IsRegularLocalRing A] {r : ℕ} (f : Fin r → A) (hf : IsPartOfRegularSystemOfParameters f)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B)
    (j : Fin r) [(Ideal.span {f j}).IsPrime] (nj : ℕ) (hnj : 0 < nj)
    (hdvd : ∀ (Q : Ideal (integralClosure A (FractionRing A ⊗[A] B))) [Q.IsPrime],
      Q.LiesOver (Ideal.span {f j}) → Q.ramificationIdx A ∣ nj)
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra A S]
    (hS : Function.Injective (algebraMap A S)) (T : S) (hT : T ^ nj = algebraMap A S (f j))
    (S' : Type u) [CommRing S'] [Algebra S S'] [Algebra A S'] [IsScalarTower A S S']
    [IsLocalization (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl) S']
    [Algebra (Localization.AtPrime (Ideal.span {f j})) S']
    [IsScalarTower A (Localization.AtPrime (Ideal.span {f j})) S']
    (C' : Type u) [CommRing C'] [Algebra (S ⊗[A] B) C'] [Algebra S' C'] [Algebra S C']
    [Algebra A C'] [IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
      (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl)) C']
    [IsScalarTower S S' C'] [IsScalarTower S (S ⊗[A] B) C'] [IsScalarTower A S C'] :
    Algebra.FormallyEtale S' (integralClosure S' C') := by
  classical
  have : IsScalarTower A S' C' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A S C', IsScalarTower.algebraMap_apply A S S',
      ← IsScalarTower.algebraMap_apply S S' C']
  have : IsScalarTower A (S ⊗[A] B) C' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A S (S ⊗[A] B),
      ← IsScalarTower.algebraMap_apply S (S ⊗[A] B) C', ← IsScalarTower.algebraMap_apply]
  have hf0 : f j ≠ 0 := hf.ne_zero j
  -- the discrete valuation ring `R = A_(f_j)`, with fraction field `K = Frac A`
  have hf0R : algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j) ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective _
      (Ideal.span {f j}).primeCompl_le_nonZeroDivisors)).mpr hf0
  have hRm : maximalIdeal (Localization.AtPrime (Ideal.span {f j})) =
      Ideal.span {algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j)} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {f j}), Ideal.map_span,
      Set.image_singleton]
  have hnf : ¬ IsField (Localization.AtPrime (Ideal.span {f j})) := fun h ↦ by
    have := (IsLocalRing.isField_iff_maximalIdeal_eq.mp h)
    rw [hRm, Ideal.span_singleton_eq_bot] at this
    exact hf0R this
  have hRp : (maximalIdeal (Localization.AtPrime (Ideal.span {f j}))).IsPrincipal := ⟨⟨_, hRm⟩⟩
  have : IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {f j})) :=
    ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).mpr hRp
  have hπR : Irreducible (algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hRm
  have : Fact (Irreducible (algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j))) :=
    ⟨hπR⟩
  have : IsFractionRing (Localization.AtPrime (Ideal.span {f j})) (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Ideal.span {f j}).primeCompl _ _
  -- `m = gcd(n_j, n)`
  obtain ⟨N, hNf, hNdvd⟩ := exists_ramificationIdx_dvd_of_isTamelyRamifiedAlong f
    (fun i ↦ hf.ne_zero i) B hB j
  set m := Nat.gcd nj N with hm
  have hmpos : 0 < m := Nat.gcd_pos_of_pos_left _ hnj
  have : NeZero m := ⟨hmpos.ne'⟩
  have hmf : (m : A) ∉ Ideal.span {f j} := fun h ↦ hNf (by
    obtain ⟨c, hc⟩ := Nat.gcd_dvd_right nj N
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h)
  have hnR : ((m : ℕ) : Localization.AtPrime (Ideal.span {f j})) ∉
      maximalIdeal (Localization.AtPrime (Ideal.span {f j})) := by
    rw [← map_natCast (algebraMap A (Localization.AtPrime (Ideal.span {f j}))),
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Ideal.span {f j})]
    exact hmf
  -- `E = Frac A ⊗_A B` is finite étale over `Frac A`
  have hπK : IsUnit (algebraMap A (FractionRing A) (∏ i, f i)) := isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective A _)).mpr
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hf.ne_zero i))
  let : Algebra (Localization.Away (∏ i, f i)) (FractionRing A) :=
    (IsLocalization.Away.lift _ hπK).toAlgebra
  have : IsScalarTower A (Localization.Away (∏ i, f i)) (FractionRing A) :=
    .of_algebraMap_eq fun a ↦ (IsLocalization.Away.lift_eq _ hπK a).symm
  let eE : FractionRing A ⊗[Localization.Away (∏ i, f i)] B ≃ₐ[FractionRing A]
      FractionRing A ⊗[A] B :=
    AlgEquiv.ofRingEquiv (f := (IsLocalization.algebraTensorEquiv (Submonoid.powers (∏ i, f i))
      (Localization.Away (∏ i, f i)) (FractionRing A) B).toRingEquiv) fun _ ↦ rfl
  have : Algebra.Etale (FractionRing A) (FractionRing A ⊗[A] B) := Algebra.Etale.of_equiv eE
  have : Module.Finite (FractionRing A) (FractionRing A ⊗[A] B) :=
    Module.Finite.equiv eE.toLinearEquiv
  -- the normalization of `R` in `E` is the localization of that of `A`
  let ι : integralClosure A (FractionRing A ⊗[A] B) →+*
      integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B) :=
    { toFun x := ⟨x.1, x.2.tower_top⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  let : Algebra (integralClosure A (FractionRing A ⊗[A] B))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B)) :=
    ι.toAlgebra
  have : IsScalarTower (integralClosure A (FractionRing A ⊗[A] B))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B))
      (FractionRing A ⊗[A] B) := ⟨fun x y z ↦ mul_assoc (x : FractionRing A ⊗[A] B)
        (y : FractionRing A ⊗[A] B) z⟩
  have : IsScalarTower A (integralClosure A (FractionRing A ⊗[A] B))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid (FractionRing A ⊗[A] B)
      (Ideal.span {f j}).primeCompl) (FractionRing A ⊗[A] B) := by
    refine IsLocalization.of_le_isUnit ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [IsScalarTower.algebraMap_apply A (FractionRing A)]
    refine (isUnit_iff_ne_zero.mpr ?_).map _
    exact (map_ne_zero_iff _ (IsFractionRing.injective A _)).mpr fun h ↦ ha (h ▸ zero_mem _)
  have hloc := IsLocalization.integralClosure (R := A) (S := FractionRing A ⊗[A] B)
    (Rf := Localization.AtPrime (Ideal.span {f j})) (Sf := FractionRing A ⊗[A] B)
    (Ideal.span {f j}).primeCompl
  -- the primes of the normalization of `R` in `E` over `𝔪_R` are tame, with `e ∣ m`
  have hRtame : ∀ (Q' : Ideal (integralClosure (Localization.AtPrime (Ideal.span {f j}))
      (FractionRing A ⊗[A] B))) [Q'.IsPrime],
      Q'.LiesOver (maximalIdeal (Localization.AtPrime (Ideal.span {f j}))) →
      IsTamelyRamifiedAt (Localization.AtPrime (Ideal.span {f j})) Q' ∧
        Q'.ramificationIdx (Localization.AtPrime (Ideal.span {f j})) ∣ m := by
    intro Q' _ hQ'
    have hQ'eq := IsLocalization.map_under (Algebra.algebraMapSubmonoid
      (integralClosure A (FractionRing A ⊗[A] B)) (Ideal.span {f j}).primeCompl) _ Q'
    have : (Q'.under (integralClosure A (FractionRing A ⊗[A] B))).IsPrime :=
      Ideal.comap_isPrime _ _
    have : (Q'.under (integralClosure A (FractionRing A ⊗[A] B))).LiesOver
        (Ideal.span {f j}) := ⟨by
      have e1 : (Q'.under (integralClosure A (FractionRing A ⊗[A] B))).under A = Q'.under A :=
        Ideal.under_under Q'
      have e2 : (Q'.under (Localization.AtPrime (Ideal.span {f j}))).under A = Q'.under A :=
        Ideal.under_under Q'
      rw [e1, ← e2, ← Ideal.over_def Q' (maximalIdeal (Localization.AtPrime (Ideal.span {f j}))),
        Localization.AtPrime.under_maximalIdeal]⟩
    have h1 := (isTamelyRamifiedAt_map_iff_of_isLocalization A (Ideal.span {f j})
      (Localization.AtPrime (Ideal.span {f j}))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B))
      (Q'.under (integralClosure A (FractionRing A ⊗[A] B)))).mpr (hB j _ inferInstance)
    have h2 := IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx
      (S := integralClosure A (FractionRing A ⊗[A] B)) (Ideal.span {f j})
      (Localization.AtPrime (Ideal.span {f j}))
      (integralClosure (Localization.AtPrime (Ideal.span {f j})) (FractionRing A ⊗[A] B))
      (Q'.under (integralClosure A (FractionRing A ⊗[A] B)))
    have h3 := Nat.dvd_gcd (hdvd (Q'.under (integralClosure A (FractionRing A ⊗[A] B)))
      inferInstance) (hNdvd (Q'.under (integralClosure A (FractionRing A ⊗[A] B))) inferInstance)
    rw [← hm, ← h2] at h3
    convert And.intro h1 h3 using 3 <;> exact hQ'eq.symm
  -- `S_R = N⁻¹S`, an integrally closed domain over `S₀ = R[T']/(T'^m - f_j)`
  have hM : Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl ≤ nonZeroDivisors S := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ha ?_
    rw [(map_eq_zero_iff _ hS).mp h0]
    exact zero_mem _
  have : IsDomain S' := IsLocalization.isDomain_of_le_nonZeroDivisors S' hM
  have : IsIntegrallyClosed S' := isIntegrallyClosed_of_isLocalization S' _ hM
  have hTm : (T ^ (nj / m)) ^ m = algebraMap A S (f j) := by
    rw [← pow_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left nj N), hT]
  let ψ₀ : AdjoinRoot (X ^ m - C (algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j)))
      →ₐ[Localization.AtPrime (Ideal.span {f j})]
      S' :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) (algebraMap S _ (T ^ (nj / m))) (by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, ← map_pow, hTm, sub_eq_zero,
        ← IsScalarTower.algebraMap_apply]
      exact IsScalarTower.algebraMap_apply _ _ _ _)
  let : Algebra (AdjoinRoot (X ^ m - C (algebraMap A (Localization.AtPrime (Ideal.span {f j}))
      (f j)))) (S') :=
    ψ₀.toRingHom.toAlgebra
  have : IsScalarTower (Localization.AtPrime (Ideal.span {f j}))
      (AdjoinRoot (X ^ m - C (algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j))))
      (S') :=
    IsScalarTower.of_algHom ψ₀
  have hπS : algebraMap (Localization.AtPrime (Ideal.span {f j}))
      (S')
      (algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j)) ≠ 0 := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A S]
    exact (map_ne_zero_iff _ (IsLocalization.injective _ hM)).mpr
      ((map_ne_zero_iff _ hS).mpr hf0)
  have hG2 := formallyEtale_integralClosure_tensorProduct (Localization.AtPrime (Ideal.span {f j}))
    (FractionRing A) (algebraMap A (Localization.AtPrime (Ideal.span {f j})) (f j)) m hnR
    (FractionRing A ⊗[A] B) hRtame
    (S') hπS
  -- `C' = N⁻¹(S ⊗_A B)` as an `R`- and `K`-algebra: the nonzero elements of `A` are units in `C'`
  let : Algebra (Localization.AtPrime (Ideal.span {f j})) (C') :=
    ((algebraMap (S')
      (C')).comp
      (algebraMap (Localization.AtPrime (Ideal.span {f j}))
        (S'))).toAlgebra
  have : IsScalarTower (Localization.AtPrime (Ideal.span {f j}))
      (S')
      (C') :=
    .of_algebraMap_eq fun _ ↦ rfl
  have hAC (a : A) : algebraMap A (C') a =
      algebraMap (Localization.AtPrime (Ideal.span {f j})) _
        (algebraMap A (Localization.AtPrime (Ideal.span {f j})) a) := by
    rw [IsScalarTower.algebraMap_apply (Localization.AtPrime (Ideal.span {f j}))
      (S'),
      ← IsScalarTower.algebraMap_apply A (Localization.AtPrime (Ideal.span {f j})),
      IsScalarTower.algebraMap_apply A S (S'), ← IsScalarTower.algebraMap_apply S,
      ← IsScalarTower.algebraMap_apply]
  have : IsScalarTower A (Localization.AtPrime (Ideal.span {f j}))
      (C') :=
    .of_algebraMap_eq hAC
  have hπC : IsUnit (algebraMap A (C') (f j)) := by
    have hπB : IsUnit (algebraMap A B (f j)) := by
      refine isUnit_of_dvd_unit (map_dvd (algebraMap A B)
        (Finset.dvd_prod_of_mem f (Finset.mem_univ j))) ?_
      rw [IsScalarTower.algebraMap_apply A (Localization.Away (∏ i, f i)) B]
      exact (IsLocalization.Away.algebraMap_isUnit _).map _
    rw [IsScalarTower.algebraMap_apply A (S ⊗[A] B), Algebra.TensorProduct.algebraMap_apply']
    exact (hπB.map (Algebra.TensorProduct.includeRight (R := A) (A := S))).map _
  have hunitsK : ∀ y : nonZeroDivisors A, IsUnit (algebraMap A
      (C') y) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      ((map_ne_zero_iff _ (IsLocalization.injective _
        (Ideal.span {f j}).primeCompl_le_nonZeroDivisors)).mpr (nonZeroDivisors.ne_zero hy)) hπR
    rw [hAC, hu, map_mul, map_pow, ← hAC]
    exact (u.isUnit.map _).mul (hπC.pow k)
  let : Algebra (FractionRing A) (C') :=
    (IsLocalization.lift hunitsK).toAlgebra
  have : IsScalarTower A (FractionRing A) (C') :=
    .of_algebraMap_eq fun a ↦ (IsLocalization.lift_eq hunitsK a).symm
  have : IsScalarTower (Localization.AtPrime (Ideal.span {f j})) (FractionRing A)
      (C') := by
    refine .of_algebraMap_eq' (IsLocalization.ringHom_ext (Ideal.span {f j}).primeCompl ?_)
    ext a
    simp only [RingHom.comp_apply]
    rw [← hAC, ← IsScalarTower.algebraMap_apply A (Localization.AtPrime (Ideal.span {f j}))
      (FractionRing A), ← IsScalarTower.algebraMap_apply A (FractionRing A)]
  let β : FractionRing A ⊗[A] B →ₐ[FractionRing A] C' :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ((IsScalarTower.toAlgHom A (S ⊗[A] B) _).comp
      Algebra.TensorProduct.includeRight) fun _ _ ↦ Commute.all _ _
  -- `S' ⊗_R (K ⊗_A B) ≅ C'`
  have hbij := bijective_lift_tensorProduct_of_isLocalization (A := A) (S := S) (B := B)
    (R := Localization.AtPrime (Ideal.span {f j})) (K := FractionRing A)
    (BK := FractionRing A ⊗[A] B) (S' := S') (C' := C') (Ideal.span {f j}).primeCompl
    (nonZeroDivisors A) Algebra.TensorProduct.includeRight (fun y ↦ by
      induction y using TensorProduct.induction_on with
      | zero => exact Subalgebra.zero_mem _
      | tmul k b =>
        have : k ⊗ₜ[A] b = k • Algebra.TensorProduct.includeRight b := by
          rw [Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', smul_eq_mul,
            mul_one]
        rw [this]
        exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self b)) k
      | add x y hx hy => exact Subalgebra.add_mem _ hx hy) β (fun b ↦ by
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one,
        one_mul]
      rfl)
  exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective _ hbij).mapIntegralClosure

set_option maxHeartbeats 1600000 in
-- the instance problems on the localizations of `A' ⊗_A B` are large
/-- XIII.5.2, the input in codimension one, for any exponents: let `A` be a regular local ring,
`f₁, …, f_r` part of a regular system of parameters, `B` a finite étale `A[1/∏ fᵢ]`-algebra
tamely ramified along `Σ div fᵢ` with ramification indices above `(fᵢ)` dividing `nᵢ > 0`, and
`A' = A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`. Then the normalization of `A'` in `A' ⊗_A B` is étale over `A'`
above the height-one primes of `V(∏ Tᵢ)`. Such a prime lies over `(f_j)` for some `j`, and we
apply `formallyEtale_integralClosure_localization_of_pow_eq`. Unlike
`isEtaleAt_integralClosure_of_isTamelyRamifiedAlong`, the `nᵢ` need not be nonzero in the residue
fields `κ((f_j))`. -/
theorem isEtaleAt_integralClosure_kummerAlgebra_of_isTamelyRamifiedAlong (A : Type u)
    [CommRing A] [IsRegularLocalRing A] {r : ℕ} (f : Fin r → A)
    (hf : IsPartOfRegularSystemOfParameters f) (B : Type u) [CommRing B] [Algebra A B]
    [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B)
    (n : Fin r → ℕ) (hnpos : ∀ i, 0 < n i)
    (hdvd : ∀ (i : Fin r) (Q : Ideal (integralClosure A (FractionRing A ⊗[A] B))) [Q.IsPrime],
      Q.LiesOver (Ideal.span {f i}) → Q.ramificationIdx A ∣ n i)
    (S : Type u) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra A S]
    (σ₀ : S ≃ₐ[A] KummerAlgebra n f)
    (q : Ideal (integralClosure S (S ⊗[A] B))) [q.IsPrime]
    (hqt : algebraMap A S (∏ i, f i) ∈ q.comap (algebraMap S (integralClosure S (S ⊗[A] B))))
    (hqh : (q.comap (algebraMap S (integralClosure S (S ⊗[A] B)))).height = 1) :
    Algebra.IsEtaleAt S q := by
  classical
  have : Algebra.IsIntegral A (KummerAlgebra n f) := KummerAlgebra.isIntegral f hnpos
  have : Algebra.IsIntegral A S := ⟨fun x ↦ by
    simpa using (Algebra.IsIntegral.isIntegral (R := A) (σ₀ x)).map σ₀.symm.toAlgHom⟩
  have hinj : Function.Injective (algebraMap A S) := fun a b hab ↦
    KummerAlgebra.injective_algebraMap f hnpos (by rw [← σ₀.commutes, ← σ₀.commutes, hab])
  -- the prime `q ∩ A` contains one of the `f j`
  have : (q.comap (algebraMap A (integralClosure S
      (S ⊗[A] B)))).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨j, -, hj⟩ : ∃ j ∈ Finset.univ, f j ∈ q.comap (algebraMap A
      (integralClosure S (S ⊗[A] B))) := by
    refine Ideal.IsPrime.prod_mem_iff.mp ?_
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A S]
    exact hqt
  have hf0 : f j ≠ 0 := hf.ne_zero j
  have hp : (Ideal.span {f j}).IsPrime := hf.isPrime_span_singleton j
  -- `q` lies over `(f_j)`
  have hqA : q.comap (algebraMap A (integralClosure S
      (S ⊗[A] B))) = Ideal.span {f j} := by
    have hle : Ideal.span {f j} ≤ q.comap (algebraMap A (integralClosure S
        (S ⊗[A] B))) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hj
    have : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A _).mpr hinj
    have hPQ : (q.comap (algebraMap S (integralClosure S
        (S ⊗[A] B)))).under A = q.comap (algebraMap A
          (integralClosure S (S ⊗[A] B))) := by
      rw [Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    have hht := Ideal.height_under_le_height_of_hasGoingDown (R := A)
      (q.comap (algebraMap S (integralClosure S
        (S ⊗[A] B))))
    rw [hqh, hPQ] at hht
    by_contra hne
    have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle (Ne.symm hne))
    have h0 : (⊥ : Ideal A) < Ideal.span {f j} :=
      bot_lt_iff_ne_bot.mpr (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hf0)
    have : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
    have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime h0
    rw [Ideal.height_bot] at h2
    exact absurd ((Order.one_le_iff_pos.mpr h2).trans_lt h1) (not_lt.mpr hht)
  -- X.3.6 over `A_(f_j)`, after localization
  have := formallyEtale_integralClosure_localization_of_pow_eq A f hf B hB j (n j) (hnpos j)
    (hdvd j) S hinj (σ₀.symm (KummerAlgebra.T n f j)) (by
      rw [← map_pow, KummerAlgebra.T_pow, AlgEquiv.commutes])
    (Localization (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))
    (Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
      (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl)))
  refine isEtaleAt_integralClosure_of_isLocalization
    (S' := Localization (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl))
    (C' := Localization (Algebra.algebraMapSubmonoid (S ⊗[A] B)
      (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl)))
    (Algebra.algebraMapSubmonoid S (Ideal.span {f j}).primeCompl) q ?_
  rintro _ ⟨a, ha, rfl⟩ haq
  apply ha
  rw [← hqA]
  change a ∈ q.comap (algebraMap A (integralClosure S (S ⊗[A] B)))
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A S]
  exact haq

/-- XIII.5.2, existence part, for any exponents: if `B` is a finite étale `A[1/∏ fᵢ]`-algebra
tamely ramified along `Σ div fᵢ` and the ramification indices above `(fᵢ)` divide `nᵢ > 0`, then
the restriction of `B` to `U' = Spec A'[1/∏ fᵢ]`, `A' = A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`, extends to a finite
étale `A'`-algebra `W`. This removes from `exists_etale_kummerAlgebra_of_isTamelyRamifiedAlong`
the assumption that the `nᵢ` are nonzero in the residue fields `κ((f_j))`. -/
theorem exists_etale_kummerAlgebra_of_isTamelyRamifiedAlong_of_pos (A : Type u) [CommRing A]
    [IsRegularLocalRing A] {r : ℕ} (f : Fin r → A) (hf : IsPartOfRegularSystemOfParameters f)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B)
    (n : Fin r → ℕ) (hnpos : ∀ i, 0 < n i)
    (hdvd : ∀ (i : Fin r) (Q : Ideal (integralClosure A (FractionRing A ⊗[A] B))) [Q.IsPrime],
      Q.LiesOver (Ideal.span {f i}) → Q.ramificationIdx A ∣ n i) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra (KummerAlgebra n f) W),
      Module.Finite (KummerAlgebra n f) W ∧ Algebra.Etale (KummerAlgebra n f) W ∧
      Nonempty (KummerAlgebra n f ⊗[A] B ≃ₐ[KummerAlgebra n f]
        Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)) ⊗[KummerAlgebra n f]
          W) := by
  have : IsRegularLocalRing (KummerAlgebra n f) := KummerAlgebra.isRegularLocalRing hnpos hf
  have hπ : algebraMap A (KummerAlgebra n f) (∏ i, f i) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (KummerAlgebra.injective_algebraMap f hnpos)]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hf.ne_zero i
  exact exists_etale_of_forall_isEtaleAt (∏ i, f i) B (KummerAlgebra n f) hπ
    fun q _ hqt hqh ↦ isEtaleAt_integralClosure_kummerAlgebra_of_isTamelyRamifiedAlong A f hf B hB
      n hnpos hdvd (KummerAlgebra n f) AlgEquiv.refl q hqt hqh

/-! ### XIII.5.2: the descent argument for `nᵢ` prime to `p` -/

/-- Frobenius: if `x^{p^a} = y^{p^a}` in a commutative ring `C` then `(x - y)^{p^a} ∈ pC`. -/
theorem sub_pow_mem_span_of_pow_eq {C : Type*} [CommRing C] {p : ℕ} [Fact p.Prime] {x y : C}
    {a : ℕ} (h : x ^ p ^ a = y ^ p ^ a) : (x - y) ^ p ^ a ∈ Ideal.span {(p : C)} := by
  by_cases hu : IsUnit (p : C)
  · rw [Ideal.span_singleton_eq_top.mpr hu]
    trivial
  · have := CharP.quotient C p hu
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, map_sub, sub_pow_char_pow, ← map_pow,
      ← map_pow, h, sub_self]

/-- The local descent argument (XIII.5.2, "`Z'' → Z` is radicial"): let `D` be a formally
unramified `S`-algebra and `σ : D → A'` an `S`-algebra map, where `A'` is generated over `S` by
elements `tᵢ` such that `tᵢ ⊗ 1 - 1 ⊗ tᵢ` is nilpotent modulo `p` in `A' ⊗_S A'` (e.g.
`tᵢ^{p^{aᵢ}} ∈ S`), and `⋂ₙ pⁿ (A' ⊗_S A') = 0` (Krull). Then `σ(d) ⊗ 1 = 1 ⊗ σ(d)` for all `d`:
modulo `pⁿ`, the two maps `D → A' ⊗_S A'` agree modulo a nilpotent ideal. -/
theorem tmul_eq_of_formallyUnramified {S D A' : Type*} [CommRing S] [CommRing D] [CommRing A']
    [Algebra S D] [Algebra S A'] [Algebra.FormallyUnramified S D] (σ : D →ₐ[S] A') (p : S)
    {ι : Type*} [Finite ι] (t : ι → A') (hgen : Algebra.adjoin S (Set.range t) = ⊤)
    (ht : ∀ i, ∃ k : ℕ, (t i ⊗ₜ[S] (1 : A') - (1 : A') ⊗ₜ[S] t i) ^ k ∈
      Ideal.span {algebraMap S (A' ⊗[S] A') p})
    (hKrull : ∀ x : A' ⊗[S] A',
      (∀ n : ℕ, x ∈ Ideal.span {algebraMap S (A' ⊗[S] A') p} ^ n) → x = 0)
    (d : D) : σ d ⊗ₜ[S] (1 : A') = (1 : A') ⊗ₜ[S] σ d := by
  classical
  set P : Ideal (A' ⊗[S] A') := Ideal.span {algebraMap S (A' ⊗[S] A') p}
  set J : Ideal (A' ⊗[S] A') :=
    P ⊔ Ideal.span (Set.range fun i ↦ t i ⊗ₜ[S] (1 : A') - (1 : A') ⊗ₜ[S] t i)
  -- `y ⊗ 1 - 1 ⊗ y ∈ J` for all `y ∈ A'`
  have hJ (y : A') : y ⊗ₜ[S] (1 : A') - (1 : A') ⊗ₜ[S] y ∈ J := by
    have : (Ideal.Quotient.mkₐ S J).comp (Algebra.TensorProduct.includeLeft (S := S)) =
        (Ideal.Quotient.mkₐ S J).comp Algebra.TensorProduct.includeRight := by
      refine AlgHom.ext_of_adjoin_eq_top hgen ?_
      rintro _ ⟨i, rfl⟩
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
      exact Ideal.Quotient.eq.mpr (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    have h := DFunLike.congr_fun this y
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply] at h
    exact Ideal.Quotient.eq.mp h
  -- `J ⊆ √P`, hence `J^k ⊆ P` for some `k`
  have hJP : J ≤ P.radical := by
    refine sup_le Ideal.le_radical ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ht i
  have hJfg : J.FG := by
    refine Submodule.FG.sup ⟨{algebraMap S (A' ⊗[S] A') p}, by simp [P]⟩ ?_
    exact Submodule.fg_span (Set.finite_range _)
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJP hJfg
  refine sub_eq_zero.mp (hKrull _ fun n ↦ ?_)
  -- in `(A' ⊗_S A')/Pⁿ`, `J` becomes nilpotent
  have hnil : IsNilpotent (J.map (Ideal.Quotient.mk (P ^ n))) := by
    refine ⟨k * n, ?_⟩
    rw [← Ideal.map_pow, pow_mul, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact Ideal.pow_right_mono hk n
  have heq := Algebra.FormallyUnramified.ext (R := S) (A := D)
    (J.map (Ideal.Quotient.mk (P ^ n))) hnil
    (g₁ := (Ideal.Quotient.mkₐ S (P ^ n)).comp
      ((Algebra.TensorProduct.includeLeft (S := S)).comp σ))
    (g₂ := (Ideal.Quotient.mkₐ S (P ^ n)).comp (Algebra.TensorProduct.includeRight.comp σ))
    fun x ↦ by
      refine Ideal.Quotient.eq.mpr ?_
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
      rw [← map_sub]
      exact Ideal.mem_map_of_mem _ (hJ (σ x))
  have h := DFunLike.congr_fun heq d
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply] at h
  exact Ideal.Quotient.eq.mp h

/-- If `y ⊗ 1 = 1 ⊗ y` in `A' ⊗_S A'`, then the image of `y` in a field `L'` over a field `L₂`
(compatibly with `S → L₂`) lies in `L₂`. -/
theorem mem_range_of_tmul_eq {S A' L₂ L' : Type*} [CommRing S] [CommRing A'] [Field L₂]
    [Field L'] [Algebra S A'] [Algebra S L₂] [Algebra L₂ L'] [Algebra S L'] [IsScalarTower S L₂ L']
    [Algebra A' L'] [IsScalarTower S A' L'] {y : A'}
    (h : y ⊗ₜ[S] (1 : A') = (1 : A') ⊗ₜ[S] y) :
    algebraMap A' L' y ∈ Set.range (algebraMap L₂ L') := by
  let ι₁ : L' →ₐ[S] L' ⊗[L₂] L' :=
    (Algebra.TensorProduct.includeLeft (R := L₂) (S := L₂) (A := L') (B := L')).restrictScalars S
  let ι₂ : L' →ₐ[S] L' ⊗[L₂] L' :=
    (Algebra.TensorProduct.includeRight (R := L₂) (A := L') (B := L')).restrictScalars S
  let Θ : A' ⊗[S] A' →ₐ[S] L' ⊗[L₂] L' :=
    Algebra.TensorProduct.lift (ι₁.comp (IsScalarTower.toAlgHom S A' L'))
      (ι₂.comp (IsScalarTower.toAlgHom S A' L')) fun _ _ ↦ Commute.all _ _
  have h2 := congrArg Θ h
  simp only [Θ, Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul] at h2
  change algebraMap A' L' y ⊗ₜ[L₂] (1 : L') = (1 : L') ⊗ₜ[L₂] algebraMap A' L' y at h2
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap L₂ L')
    (LinearMap.ker_eq_bot.mpr (algebraMap L₂ L').injective)
  let Φ' : L' ⊗[L₂] L' →ₗ[L₂] L' :=
    (TensorProduct.lid L₂ L').toLinearMap ∘ₗ TensorProduct.map φ LinearMap.id
  have h3 := congrArg Φ' h2
  simp only [Φ', LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.lid_tmul] at h3
  have h1 : φ 1 = 1 := by
    have := DFunLike.congr_fun hφ 1
    simpa using this
  rw [h1, one_smul] at h3
  refine ⟨φ (algebraMap A' L' y), ?_⟩
  rw [Algebra.algebraMap_eq_smul_one]
  exact h3

/-- An element of an integral extension `R'` of an integrally closed domain `R₂` whose image in a
field `L'` lies in the fraction field `L₂` of `R₂` lies in `R₂`. -/
theorem mem_range_of_mem_range_fractionRing {R₂ R' L₂ L' : Type*} [CommRing R₂] [IsDomain R₂]
    [IsIntegrallyClosed R₂] [CommRing R'] [Field L₂] [Field L'] [Algebra R₂ R']
    [Algebra.IsIntegral R₂ R'] [Algebra R₂ L₂] [IsFractionRing R₂ L₂] [Algebra L₂ L']
    [Algebra R₂ L'] [IsScalarTower R₂ L₂ L'] [Algebra R' L'] [IsScalarTower R₂ R' L']
    (hinj : Function.Injective (algebraMap R' L')) {y : R'}
    (hy : algebraMap R' L' y ∈ Set.range (algebraMap L₂ L')) :
    y ∈ Set.range (algebraMap R₂ R') := by
  obtain ⟨z, hz⟩ := hy
  have h1 : IsIntegral R₂ (algebraMap L₂ L' z) := by
    rw [hz]
    exact (Algebra.IsIntegral.isIntegral (R := R₂) y).map (IsScalarTower.toAlgHom R₂ R' L')
  have h2 : IsIntegral R₂ z :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R₂ L₂ L') (algebraMap L₂ L').injective).mp h1
  obtain ⟨w, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  exact ⟨w, hinj (by rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R₂ L₂ L',
    hz])⟩

set_option maxHeartbeats 1600000 in
-- many localizations
/-- The descent step of XIII.5.2 ("`n₁` is prime to `p`"), at a prime `P` of `A` containing `p`:
let `A₂ → A'` be an integral extension of integrally closed noetherian domains over `A`, `A'`
generated over `A₂` by elements `tᵢ` with `tᵢ^{p^{aᵢ}} ∈ A₂` (so that `Spec A' → Spec A₂` is
radicial modulo `p`), `B` an integral `A[1/g]`-algebra and `Φ : B → A'[1/g]` an `A`-algebra map.
Suppose that, `N = A - P`, the normalization of `N⁻¹A₂` in `N⁻¹(A₂ ⊗_A B)` is formally unramified
over `N⁻¹A₂` (in XIII.5.2: `B ⊗_A A₂` is unramified at `P`). Then `Φ` takes values in `A₂[1/g]`.
Indeed `Φ` induces `σ : D → N⁻¹A'`, `D` that normalization, and the two maps
`D → N⁻¹A' ⊗_{N⁻¹A₂} N⁻¹A'` agree (`tmul_eq_of_formallyUnramified`, Krull's intersection theorem
over `N⁻¹A₂`, whose maximal ideals contain `p`), so that `σ` lands in `Frac A₂`
(`mem_range_of_tmul_eq`), hence `Φ` lands in `A₂[1/g]` (`mem_range_of_mem_range_fractionRing`). -/
theorem mem_range_of_formallyUnramified_integralClosure {A A₂ A' : Type u} [CommRing A]
    [IsDomain A] [CommRing A₂] [IsDomain A₂] [IsIntegrallyClosed A₂] [IsNoetherianRing A₂]
    [CommRing A'] [IsDomain A'] [IsIntegrallyClosed A'] [Algebra A A₂] [Algebra A A']
    [Algebra A₂ A'] [IsScalarTower A A₂ A'] [Algebra.IsIntegral A A₂] [Module.Finite A₂ A']
    (hinjA : Function.Injective (algebraMap A A₂)) (hinj₂ : Function.Injective (algebraMap A₂ A'))
    (p : ℕ) [Fact p.Prime] {ι : Type*} [Finite ι] (t : ι → A')
    (hgen : Algebra.adjoin A₂ (Set.range t) = ⊤) (a : ι → ℕ)
    (ht : ∀ i, t i ^ p ^ a i ∈ Set.range (algebraMap A₂ A'))
    (P : Ideal A) [P.IsPrime] (hpP : (p : A) ∈ P) {g : A} (hg : g ≠ 0)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra (Localization.Away g) B]
    [IsScalarTower A (Localization.Away g) B] [Algebra.IsIntegral (Localization.Away g) B]
    (A'g : Type u) [CommRing A'g] [Algebra A' A'g] [IsLocalization.Away (algebraMap A A' g) A'g]
    [Algebra A A'g] [IsScalarTower A A' A'g]
    (A₂g : Type u) [CommRing A₂g] [Algebra A₂ A₂g] [IsLocalization.Away (algebraMap A A₂ g) A₂g]
    [Algebra A₂g A'g] [Algebra A₂ A'g] [IsScalarTower A₂ A₂g A'g] [IsScalarTower A₂ A' A'g]
    (Φ : B →ₐ[A] A'g)
    (hD : Algebra.FormallyUnramified (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (integralClosure (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
        (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
          (Algebra.algebraMapSubmonoid A₂ P.primeCompl)))))
    (b : B) : Φ b ∈ Set.range (algebraMap A₂g A'g) := by
  classical
  have hg₂ : algebraMap A A₂ g ≠ 0 := (map_ne_zero_iff _ hinjA).mpr hg
  have hN₂ : Algebra.algebraMapSubmonoid A₂ P.primeCompl ≤ nonZeroDivisors A₂ := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ha ?_
    rw [(map_eq_zero_iff _ hinjA).mp h0]
    exact zero_mem _
  have hinjA' : Function.Injective (algebraMap A A') := by
    rw [IsScalarTower.algebraMap_eq A A₂ A']
    exact hinj₂.comp hinjA
  have hN' : Algebra.algebraMapSubmonoid A' (Algebra.algebraMapSubmonoid A₂ P.primeCompl) ≤
      nonZeroDivisors A' := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ha ?_
    rw [← IsScalarTower.algebraMap_apply] at h0
    rw [(map_eq_zero_iff _ hinjA').mp h0]
    exact zero_mem _
  -- the fraction fields `L₂ ⊆ L'`
  have : FaithfulSMul A₂ (FractionRing A') := (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    rw [IsScalarTower.algebraMap_eq A₂ A' (FractionRing A')]
    exact (IsFractionRing.injective A' (FractionRing A')).comp hinj₂)
  let : Algebra (FractionRing A₂) (FractionRing A') := FractionRing.liftAlgebra A₂ _
  -- `S_R = N⁻¹A₂ → L₂` and `A'_R = N⁻¹A' → L'`
  have hunits₂ : ∀ y : Algebra.algebraMapSubmonoid A₂ P.primeCompl,
      IsUnit (algebraMap A₂ (FractionRing A₂) y) := fun y ↦ isUnit_iff_ne_zero.mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective A₂ _)).mpr (nonZeroDivisors.ne_zero (hN₂ y.2)))
  let : Algebra (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) (FractionRing A₂) :=
    (IsLocalization.lift hunits₂).toAlgebra
  have : IsScalarTower A₂ (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (FractionRing A₂) := .of_algebraMap_eq fun a ↦ (IsLocalization.lift_eq hunits₂ a).symm
  have hunits' : ∀ y : Algebra.algebraMapSubmonoid A'
      (Algebra.algebraMapSubmonoid A₂ P.primeCompl), IsUnit (algebraMap A' (FractionRing A') y) :=
    fun y ↦ isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective A' _)).mpr
      (nonZeroDivisors.ne_zero (hN' y.2)))
  let : Algebra (Localization (Algebra.algebraMapSubmonoid A'
      (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) (FractionRing A') :=
    (IsLocalization.lift hunits').toAlgebra
  have : IsScalarTower A' (Localization (Algebra.algebraMapSubmonoid A'
      (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) (FractionRing A') :=
    .of_algebraMap_eq fun a ↦ (IsLocalization.lift_eq hunits' a).symm
  have : IsDomain (Localization (Algebra.algebraMapSubmonoid A'
      (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hN'
  have : IsIntegrallyClosed (Localization (Algebra.algebraMapSubmonoid A'
      (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) :=
    isIntegrallyClosed_of_isLocalization _ _ hN'
  have : IsFractionRing (Localization (Algebra.algebraMapSubmonoid A'
      (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) (FractionRing A') :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Algebra.algebraMapSubmonoid A' (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) _ _
  -- `S_R → L'` and the compatibility with `A'_R`
  let : Algebra (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) (FractionRing A') :=
    ((algebraMap (FractionRing A₂) (FractionRing A')).comp
      (algebraMap (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
        (FractionRing A₂))).toAlgebra
  have : IsScalarTower (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (FractionRing A₂) (FractionRing A') := .of_algebraMap_eq fun _ ↦ rfl
  have hA₂L' (a : A₂) : algebraMap A₂ (FractionRing A') a =
      algebraMap A' (FractionRing A') (algebraMap A₂ A' a) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  have : IsScalarTower (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (Localization (Algebra.algebraMapSubmonoid A'
        (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) (FractionRing A') := by
    refine .of_algebraMap_eq' (IsLocalization.ringHom_ext
      (Algebra.algebraMapSubmonoid A₂ P.primeCompl) (RingHom.ext fun a ↦ ?_))
    simp only [RingHom.comp_apply]
    have e1 : algebraMap (Localization (Algebra.algebraMapSubmonoid A'
        (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) (FractionRing A')
        (algebraMap (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
          (Localization (Algebra.algebraMapSubmonoid A'
            (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) (algebraMap A₂ _ a)) =
        algebraMap A₂ (FractionRing A') a := by
      rw [← IsScalarTower.algebraMap_apply A₂ (Localization (Algebra.algebraMapSubmonoid A₂
        P.primeCompl)) (Localization (Algebra.algebraMapSubmonoid A'
          (Algebra.algebraMapSubmonoid A₂ P.primeCompl))),
        IsScalarTower.algebraMap_apply A₂ A' (Localization (Algebra.algebraMapSubmonoid A'
          (Algebra.algebraMapSubmonoid A₂ P.primeCompl))), ← IsScalarTower.algebraMap_apply A',
        ← hA₂L']
    have e2 : algebraMap (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
        (FractionRing A') (algebraMap A₂ _ a) = algebraMap A₂ (FractionRing A') a := by
      change algebraMap (FractionRing A₂) (FractionRing A') (algebraMap
        (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) (FractionRing A₂)
          (algebraMap A₂ _ a)) = _
      rw [← IsScalarTower.algebraMap_apply A₂ (Localization (Algebra.algebraMapSubmonoid A₂
        P.primeCompl)) (FractionRing A₂), ← IsScalarTower.algebraMap_apply]
    rw [e1, e2]
  -- `A'[1/g] → L'`
  have hg' : algebraMap A A' g ≠ 0 := (map_ne_zero_iff _ hinjA').mpr hg
  have hunitsg : ∀ y : Submonoid.powers (algebraMap A A' g),
      IsUnit (algebraMap A' (FractionRing A') y) := by
    rintro ⟨_, k, rfl⟩
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective A' _)).mpr
      (pow_ne_zero k hg'))
  let : Algebra A'g (FractionRing A') := (IsLocalization.lift hunitsg).toAlgebra
  have : IsScalarTower A' A'g (FractionRing A') :=
    .of_algebraMap_eq fun a ↦ (IsLocalization.lift_eq hunitsg a).symm
  have hpowg' : Submonoid.powers (algebraMap A A' g) ≤ nonZeroDivisors A' :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hg'
  have : IsFractionRing A'g (FractionRing A') :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers (algebraMap A A' g)) _ _
  have hA'gL' : Function.Injective (algebraMap A'g (FractionRing A')) :=
    IsFractionRing.injective _ _
  have : IsScalarTower A A₂ (FractionRing A') := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A A' (FractionRing A'),
      IsScalarTower.algebraMap_apply A A₂ A', hA₂L']
  have : IsScalarTower A A'g (FractionRing A') := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A A' (FractionRing A'),
      IsScalarTower.algebraMap_apply A A' A'g, ← IsScalarTower.algebraMap_apply A' A'g]
  -- `Ψ₀ : A₂ ⊗_A B → L'` and `Ψ₁ : C' → L'`
  let Ψ₀ : A₂ ⊗[A] B →ₐ[A] FractionRing A' :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A A₂ (FractionRing A'))
      ((IsScalarTower.toAlgHom A A'g (FractionRing A')).comp Φ) fun _ _ ↦ Commute.all _ _
  have hunitsΨ : ∀ y : Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
      (Algebra.algebraMapSubmonoid A₂ P.primeCompl), IsUnit (Ψ₀ y) := by
    rintro ⟨_, z, hz, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hz
    change IsUnit (Ψ₀ (algebraMap A₂ (A₂ ⊗[A] B) (algebraMap A A₂ a)))
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
    refine isUnit_iff_ne_zero.mpr ?_
    rw [IsScalarTower.algebraMap_apply A A' (FractionRing A')]
    exact (map_ne_zero_iff _ (IsFractionRing.injective A' _)).mpr
      ((map_ne_zero_iff _ hinjA').mpr fun h0 ↦ ha (h0 ▸ zero_mem _))
  let Ψ₁ : Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
      (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) →+* FractionRing A' :=
    IsLocalization.lift (g := Ψ₀.toRingHom) hunitsΨ
  have hΨ₁ (x : A₂ ⊗[A] B) : Ψ₁ (algebraMap _ _ x) = Ψ₀ x := IsLocalization.lift_eq hunitsΨ x
  have hΨS (x : Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) :
      Ψ₁ (algebraMap _ _ x) = algebraMap _ (FractionRing A') x := by
    have : Ψ₁.comp (algebraMap (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) _) =
        algebraMap (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
          (FractionRing A') := by
      refine IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid A₂ P.primeCompl)
        (RingHom.ext fun a ↦ ?_)
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply A₂ (Localization (Algebra.algebraMapSubmonoid A₂
        P.primeCompl)), IsScalarTower.algebraMap_apply A₂ (A₂ ⊗[A] B), hΨ₁,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      change Ψ₀ (a ⊗ₜ 1) = algebraMap (FractionRing A₂) (FractionRing A') (algebraMap
        (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) (FractionRing A₂)
          (algebraMap A₂ _ a))
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one,
        ← IsScalarTower.algebraMap_apply A₂ (Localization (Algebra.algebraMapSubmonoid A₂
          P.primeCompl)) (FractionRing A₂), ← IsScalarTower.algebraMap_apply]
      rfl
    exact DFunLike.congr_fun this x
  -- `σ : D → A'_R`, `D` the normalization of `S_R` in `C'`
  let Ψ₁S : Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
      (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) →ₐ[Localization
        (Algebra.algebraMapSubmonoid A₂ P.primeCompl)] FractionRing A' :=
    { Ψ₁ with commutes' := hΨS }
  let jR := algebraMap (Localization (Algebra.algebraMapSubmonoid A'
    (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) (FractionRing A')
  have hjR : Function.Injective jR := IsFractionRing.injective _ _
  have hmem (d : integralClosure (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
        (Algebra.algebraMapSubmonoid A₂ P.primeCompl)))) : Ψ₁ d ∈ jR.range := by
    have h1 : IsIntegral (Localization (Algebra.algebraMapSubmonoid A'
        (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) (Ψ₁S d) := (d.2.map Ψ₁S).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
    exact ⟨y, hy⟩
  let σR₀ : integralClosure (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
        (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) →+* Localization
          (Algebra.algebraMapSubmonoid A' (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) :=
    (RingEquiv.ofBijective jR.rangeRestrict ⟨fun x y h ↦ hjR (congrArg Subtype.val h),
      jR.rangeRestrict_surjective⟩).symm.toRingHom.comp
      ((Ψ₁.comp (integralClosure _ _).val.toRingHom).codRestrict jR.range hmem)
  have hσR (d) : jR (σR₀ d) = Ψ₁ d := by
    have := (RingEquiv.ofBijective jR.rangeRestrict ⟨fun x y h ↦ hjR (congrArg Subtype.val h),
      jR.rangeRestrict_surjective⟩).apply_symm_apply
      ((Ψ₁.comp (integralClosure _ _).val.toRingHom).codRestrict jR.range hmem d)
    exact congrArg Subtype.val this
  let σR : integralClosure (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
        (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) →ₐ[Localization
          (Algebra.algebraMapSubmonoid A₂ P.primeCompl)] Localization
          (Algebra.algebraMapSubmonoid A' (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) :=
    { σR₀ with
      commutes' := fun x ↦ hjR (by
        change jR (σR₀ (algebraMap _ _ x)) = _
        rw [hσR, ← IsScalarTower.algebraMap_apply]
        exact (hΨS x).trans (IsScalarTower.algebraMap_apply _ _ _ x)) }
  -- the generators `tᵢ` of `A'_R` over `S_R`
  let t' : ι → Localization (Algebra.algebraMapSubmonoid A'
      (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) := fun i ↦ algebraMap A' _ (t i)
  have hgen' : Algebra.adjoin (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (Set.range t') = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨⟨y, ⟨_, s₂, hs₂, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid A' (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) x
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    refine Subalgebra.mul_mem _ ?_ ?_
    · have hy : y ∈ Algebra.adjoin A₂ (Set.range t) := by rw [hgen]; trivial
      have hle : (Algebra.adjoin A₂ (Set.range t)).map (IsScalarTower.toAlgHom A₂ A'
          (Localization (Algebra.algebraMapSubmonoid A'
            (Algebra.algebraMapSubmonoid A₂ P.primeCompl)))) ≤
          (Algebra.adjoin (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
            (Set.range t')).restrictScalars A₂ := by
        rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        exact Algebra.subset_adjoin ⟨i, rfl⟩
      exact hle ⟨y, hy, rfl⟩
    · have : IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid A'
          (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) (1 : A')
          ⟨algebraMap A₂ A' s₂, Algebra.mem_algebraMapSubmonoid_of_mem ⟨s₂, hs₂⟩⟩ =
          algebraMap (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) _
            (IsLocalization.mk' _ (1 : A₂) ⟨s₂, hs₂⟩) := by
        rw [IsLocalization.mk'_eq_iff_eq_mul, map_one, ← IsScalarTower.algebraMap_apply A₂ A',
          IsScalarTower.algebraMap_apply A₂ (Localization (Algebra.algebraMapSubmonoid A₂
            P.primeCompl)), ← map_mul, IsLocalization.mk'_spec, map_one, map_one]
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
  -- `(tᵢ ⊗ 1 - 1 ⊗ tᵢ)^{p^{aᵢ}} ∈ p (A'_R ⊗ A'_R)`
  have ht' : ∀ i, ∃ k : ℕ, (t' i ⊗ₜ[Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)]
      (1 : Localization (Algebra.algebraMapSubmonoid A'
        (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) - 1 ⊗ₜ t' i) ^ k ∈
      Ideal.span {algebraMap (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) _
        (p : Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))} := by
    intro i
    refine ⟨p ^ a i, ?_⟩
    rw [map_natCast]
    refine sub_pow_mem_span_of_pow_eq ?_
    obtain ⟨c, hc⟩ := ht i
    rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow]
    have : t' i ^ p ^ a i = algebraMap (Localization (Algebra.algebraMapSubmonoid A₂
        P.primeCompl)) _ (algebraMap A₂ _ c) := by
      simp only [t']
      rw [← map_pow, ← hc, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
    rw [this, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    simp only [one_pow]
  -- Krull: `⋂ pⁿ (A'_R ⊗ A'_R) = 0`, since `p` lies in the Jacobson radical of `S_R`
  have : IsNoetherianRing (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) :=
    IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid A₂ P.primeCompl) _ inferInstance
  have : Module.Finite (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (Localization (Algebra.algebraMapSubmonoid A'
        (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) :=
    .of_isLocalization A₂ A' (Algebra.algebraMapSubmonoid A₂ P.primeCompl)
  have : Algebra.IsIntegral (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) := ⟨isIntegral_localization⟩
  have hpJ : (p : Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) ∈
      Ideal.jacobson ⊥ := by
    refine Ideal.mem_sInf.mpr fun M ⟨_, hM⟩ ↦ ?_
    have hM' := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := Localization.AtPrime P) M
    have h1 : M.comap (algebraMap (Localization.AtPrime P) _) = maximalIdeal _ :=
      IsLocalRing.eq_maximalIdeal hM'
    have h2 : (p : Localization.AtPrime P) ∈ maximalIdeal (Localization.AtPrime P) := by
      rw [← map_natCast (algebraMap A (Localization.AtPrime P)),
        IsLocalization.AtPrime.to_map_mem_maximal_iff _ P]
      exact hpP
    rw [← h1, Ideal.mem_comap, map_natCast] at h2
    exact h2
  have hKrull : ∀ x : Localization (Algebra.algebraMapSubmonoid A'
      (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) ⊗[Localization (Algebra.algebraMapSubmonoid
        A₂ P.primeCompl)] Localization (Algebra.algebraMapSubmonoid A'
          (Algebra.algebraMapSubmonoid A₂ P.primeCompl)),
      (∀ n : ℕ, x ∈ Ideal.span {algebraMap (Localization (Algebra.algebraMapSubmonoid A₂
        P.primeCompl)) _ (p : Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))} ^ n) →
        x = 0 := by
    intro x hx
    have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson
      (R := Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (M := Localization (Algebra.algebraMapSubmonoid A'
        (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) ⊗[Localization
          (Algebra.algebraMapSubmonoid A₂ P.primeCompl)] Localization
            (Algebra.algebraMapSubmonoid A' (Algebra.algebraMapSubmonoid A₂ P.primeCompl)))
      (Ideal.span {(p : Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))})
      (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hpJ)
    have : x ∈ (⊥ : Submodule (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
        (Localization (Algebra.algebraMapSubmonoid A' (Algebra.algebraMapSubmonoid A₂
          P.primeCompl)) ⊗[Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)]
            Localization (Algebra.algebraMapSubmonoid A'
              (Algebra.algebraMapSubmonoid A₂ P.primeCompl)))) := by
      rw [← hK]
      refine Submodule.mem_iInf _ |>.mpr fun n ↦ ?_
      have hxn := hx n
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hxn
      obtain ⟨c, rfl⟩ := hxn
      rw [mul_comm, ← map_pow, ← Algebra.smul_def]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)
        Submodule.mem_top
    exact (Submodule.mem_bot _).mp this
  -- the descent: `σ(d) ∈ Frac A₂`
  have hdesc (d) : jR (σR d) ∈ Set.range (algebraMap (FractionRing A₂) (FractionRing A')) :=
    mem_range_of_tmul_eq (S := Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (tmul_eq_of_formallyUnramified σR _ t' hgen' ht' hKrull d)
  -- the element `g^k b` of `D`
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (Rₘ := Localization.Away g) (Submonoid.powers g) b (Algebra.IsIntegral.isIntegral b)
  rw [Submonoid.smul_def] at hk
  have hc : IsIntegral (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (algebraMap (A₂ ⊗[A] B) (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
        (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) ((1 : A₂) ⊗ₜ[A] ((g ^ k) • b))) := by
    have h1 : IsIntegral A ((1 : A₂) ⊗ₜ[A] ((g ^ k) • b)) :=
      hk.map (Algebra.TensorProduct.includeRight (R := A) (A := A₂) (B := B))
    have h2 : IsIntegral A₂ ((1 : A₂) ⊗ₜ[A] ((g ^ k) • b)) := h1.tower_top
    exact (h2.map (IsScalarTower.toAlgHom A₂ (A₂ ⊗[A] B) _)).tower_top
  have hΨd : Ψ₁ (algebraMap _ _ ((1 : A₂) ⊗ₜ[A] ((g ^ k) • b))) =
      algebraMap A (FractionRing A') (g ^ k) * algebraMap A'g (FractionRing A') (Φ b) := by
    rw [hΨ₁, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    change algebraMap A'g (FractionRing A') (Φ ((g ^ k) • b)) = _
    rw [map_smul, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  have hrange : algebraMap A'g (FractionRing A') (Φ b) ∈
      Set.range (algebraMap (FractionRing A₂) (FractionRing A')) := by
    obtain ⟨z, hz⟩ := hdesc ⟨_, (mem_integralClosure_iff _ _).mpr hc⟩
    have hz' := hz.trans (hσR ⟨_, (mem_integralClosure_iff _ _).mpr hc⟩)
    change _ = Ψ₁ (algebraMap _ _ ((1 : A₂) ⊗ₜ[A] ((g ^ k) • b))) at hz'
    rw [hΨd] at hz'
    have hgk : algebraMap A (FractionRing A') (g ^ k) = algebraMap (FractionRing A₂)
        (FractionRing A') (algebraMap A (FractionRing A₂) (g ^ k)) :=
      IsScalarTower.algebraMap_apply _ _ _ _
    have hgk0 : algebraMap A (FractionRing A') (g ^ k) ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply A A' (FractionRing A')]
      exact (map_ne_zero_iff _ (IsFractionRing.injective A' _)).mpr
        ((map_ne_zero_iff _ hinjA').mpr (pow_ne_zero k hg))
    refine ⟨(algebraMap A (FractionRing A₂) (g ^ k))⁻¹ * z, ?_⟩
    rw [map_mul, map_inv₀, hz', ← hgk, inv_mul_cancel_left₀ hgk0]
  -- `A₂[1/g] → A'[1/g]` is integral, and `A₂[1/g]` is integrally closed
  have hpowg₂ : Submonoid.powers (algebraMap A A₂ g) ≤ nonZeroDivisors A₂ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hg₂
  have : IsDomain A₂g := IsLocalization.isDomain_of_le_nonZeroDivisors _ hpowg₂
  have : IsIntegrallyClosed A₂g := isIntegrallyClosed_of_isLocalization _ _ hpowg₂
  have hunitsg₂ : ∀ y : Submonoid.powers (algebraMap A A₂ g),
      IsUnit (algebraMap A₂ (FractionRing A₂) y) := by
    rintro ⟨_, m, rfl⟩
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective A₂ _)).mpr
      (pow_ne_zero m hg₂))
  let : Algebra A₂g (FractionRing A₂) := (IsLocalization.lift hunitsg₂).toAlgebra
  have : IsScalarTower A₂ A₂g (FractionRing A₂) :=
    .of_algebraMap_eq fun a ↦ (IsLocalization.lift_eq hunitsg₂ a).symm
  have : IsFractionRing A₂g (FractionRing A₂) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers (algebraMap A A₂ g)) _ _
  let : Algebra A₂g (FractionRing A') :=
    ((algebraMap (FractionRing A₂) (FractionRing A')).comp
      (algebraMap A₂g (FractionRing A₂))).toAlgebra
  have : IsScalarTower A₂g (FractionRing A₂) (FractionRing A') := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A₂g A'g (FractionRing A') := by
    refine .of_algebraMap_eq' (IsLocalization.ringHom_ext
      (Submonoid.powers (algebraMap A A₂ g)) (RingHom.ext fun a ↦ ?_))
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply A₂ A₂g A'g, IsScalarTower.algebraMap_apply A₂ A' A'g,
      ← IsScalarTower.algebraMap_apply A' A'g (FractionRing A'), ← hA₂L',
      IsScalarTower.algebraMap_apply A₂ (FractionRing A₂) (FractionRing A'),
      IsScalarTower.algebraMap_apply A₂ A₂g (FractionRing A₂)]
    rfl
  have : Algebra.IsIntegral A₂ A' := Algebra.IsIntegral.of_finite A₂ A'
  have : Algebra.IsIntegral A₂g A'g := ⟨fun x ↦ by
    obtain ⟨⟨y, ⟨_, m, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Submonoid.powers (algebraMap A A' g)) x
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    refine IsIntegral.mul ?_ ?_
    · exact ((Algebra.IsIntegral.isIntegral (R := A₂) y).map
        (IsScalarTower.toAlgHom A₂ A' A'g)).tower_top
    · set s₂ : Submonoid.powers (algebraMap A A₂ g) := ⟨algebraMap A A₂ g ^ m, m, rfl⟩ with hs₂
      have h0 : algebraMap A' A'g (algebraMap A A' g ^ m) =
          algebraMap A₂g A'g (algebraMap A₂ A₂g (algebraMap A A₂ g ^ m)) := by
        rw [← IsScalarTower.algebraMap_apply A₂ A₂g A'g, IsScalarTower.algebraMap_apply A₂ A' A'g,
          map_pow, map_pow, ← IsScalarTower.algebraMap_apply A A₂ A', map_pow]
      have h1 : algebraMap A₂g A'g (IsLocalization.mk' A₂g (1 : A₂) s₂) *
          algebraMap A' A'g (algebraMap A A' g ^ m) = 1 := by
        rw [h0, ← map_mul]
        change algebraMap A₂g A'g (IsLocalization.mk' A₂g (1 : A₂) s₂ *
          algebraMap A₂ A₂g (s₂ : A₂)) = 1
        rw [IsLocalization.mk'_spec, map_one, map_one]
      have : IsLocalization.mk' A'g (1 : A') (⟨algebraMap A A' g ^ m, m, rfl⟩ :
          Submonoid.powers (algebraMap A A' g)) =
          algebraMap A₂g A'g (IsLocalization.mk' A₂g (1 : A₂) s₂) := by
        rw [IsLocalization.mk'_eq_iff_eq_mul, map_one]
        exact h1.symm
      rw [this]
      exact isIntegral_algebraMap⟩
  exact mem_range_of_mem_range_fractionRing (L₂ := FractionRing A₂) (L' := FractionRing A')
    hA'gL' hrange

/-- XIII.5.3, the section: over a strictly henselian regular local ring `A`, if `B` is an integral
finite étale `A[1/∏ fᵢ]`-algebra tamely ramified along `Σ div fᵢ` and the ramification indices
above `(fᵢ)` divide `nᵢ > 0`, there is an `A`-algebra map `B → A'[1/∏ fᵢ]`,
`A' = A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`: the extension `W` of `A' ⊗_A B`
(`exists_etale_kummerAlgebra_of_isTamelyRamifiedAlong_of_pos`) is a product of copies of the
strictly henselian `A'`. -/
theorem nonempty_algHom_away_kummerAlgebra (A : Type u) [CommRing A]
    [IsRegularLocalRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    {r : ℕ} (f : Fin r → A) (hf : IsPartOfRegularSystemOfParameters f)
    (B : Type u) [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B)
    (n : Fin r → ℕ) (hnpos : ∀ i, 0 < n i)
    (hdvd : ∀ (i : Fin r) (Q : Ideal (integralClosure A (FractionRing A ⊗[A] B))) [Q.IsPrime],
      Q.LiesOver (Ideal.span {f i}) → Q.ramificationIdx A ∣ n i) :
    Nonempty (B →ₐ[A] Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i))) := by
  classical
  obtain ⟨W, _, _, _, _, ⟨eW⟩⟩ :=
    exists_etale_kummerAlgebra_of_isTamelyRamifiedAlong_of_pos A f hf B hB n hnpos hdvd
  have : IsRegularLocalRing (KummerAlgebra n f) := KummerAlgebra.isRegularLocalRing hnpos hf
  have : Algebra.IsIntegral A (KummerAlgebra n f) := KummerAlgebra.isIntegral f hnpos
  have : Module.Finite A (KummerAlgebra n f) := Algebra.IsIntegral.finite
  have : IsStrictlyHenselian A := (isStrictlyHenselian_iff A).mpr ⟨inferInstance, inferInstance⟩
  have : IsStrictlyHenselian (KummerAlgebra n f) :=
    IsStrictlyHenselian.of_finite (A := A) (KummerAlgebra n f)
  -- `W` is nonzero, hence has a section `σ : W → A'`
  have : Nontrivial (KummerAlgebra n f ⊗[A] B) := by
    have hx (i : Fin r) : ∃ z : AlgebraicClosure (FractionRing B),
        z ^ n i = algebraMap B (AlgebraicClosure (FractionRing B)) (algebraMap A B (f i)) :=
      IsAlgClosed.exists_pow_nat_eq _ (hnpos i)
    choose z hz using hx
    let χ : KummerAlgebra n (fun i ↦ algebraMap A B (f i)) →ₐ[B]
        AlgebraicClosure (FractionRing B) := KummerAlgebra.lift z hz
    exact ((χ.toRingHom.comp (KummerAlgebra.baseChangeEquiv n f B).toRingHom).comp
      (Algebra.TensorProduct.comm A (KummerAlgebra n f) B).toRingHom).domain_nontrivial
  have : Nontrivial W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    have : Subsingleton (KummerAlgebra n f ⊗[A] B) := eW.toEquiv.subsingleton
    exact not_nontrivial _ ‹_›
  obtain ⟨m, ⟨eπ⟩⟩ := IsStrictlyHenselian.exists_algEquiv_pi (KummerAlgebra n f) W
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : Subsingleton W := eπ.toEquiv.subsingleton
      exact absurd ‹Nontrivial W› (not_nontrivial W)
    · exact hm
  let σ : W →ₐ[KummerAlgebra n f] KummerAlgebra n f :=
    (Pi.evalAlgHom (KummerAlgebra n f) (fun _ : Fin m ↦ KummerAlgebra n f) ⟨0, hm⟩).comp
      eπ.toAlgHom
  -- `Φ : B → A' ⊗_A B ≅ A'[1/∏ fᵢ] ⊗_{A'} W → A'[1/∏ fᵢ]`
  let Φ : B →+* Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)) :=
    ((Algebra.TensorProduct.rid (KummerAlgebra n f) (KummerAlgebra n f)
      (Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)))).toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id (KummerAlgebra n f)
        (Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)))) σ).toRingHom).comp
      (eW.toRingHom.comp (Algebra.TensorProduct.includeRight (R := A)
        (A := KummerAlgebra n f) (B := B)).toRingHom)
  have hΦ (a : A) : Φ (algebraMap A B a) = algebraMap A
      (Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i))) a := by
    have e1 : Algebra.TensorProduct.includeRight (R := A) (A := KummerAlgebra n f) (B := B)
        (algebraMap A B a) = Algebra.TensorProduct.includeLeft (S := KummerAlgebra n f)
          (algebraMap (KummerAlgebra n f) (KummerAlgebra n f)
            (algebraMap A (KummerAlgebra n f) a)) := by
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.algebraMap_self, RingHom.id_apply]
    change (Algebra.TensorProduct.rid (KummerAlgebra n f) (KummerAlgebra n f)
      (Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i))))
        ((Algebra.TensorProduct.map (AlgHom.id (KummerAlgebra n f)
          (Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)))) σ)
          (eW (Algebra.TensorProduct.includeRight (R := A) (A := KummerAlgebra n f) (B := B)
            (algebraMap A B a)))) = _
    rw [e1, AlgHom.commutes, AlgEquiv.commutes, AlgHom.commutes, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  exact ⟨{ Φ with commutes' := hΦ }⟩

/-- XIII.5.3, the embedding: an `A`-algebra map `Φ : B → A'[1/∏ fᵢ]`, `A' = A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`,
from an integral domain `B` finite over `A[1/∏ fᵢ]` induces an injective `A[1/∏ fᵢ]`-algebra
map `B → A[1/∏ fᵢ][Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`. -/
theorem exists_injective_kummerAlgebra_of_algHom (A : Type u) [CommRing A] [IsDomain A]
    {r : ℕ} (f : Fin r → A) (hf0 : ∀ i, f i ≠ 0)
    (B : Type u) [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    (n : Fin r → ℕ) (hnpos : ∀ i, 0 < n i)
    (Φ : B →ₐ[A] Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i))) :
    ∃ φ : B →ₐ[Localization.Away (∏ i, f i)]
        KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i)),
      Function.Injective φ := by
  classical
  -- `ψ : A'[1/∏ fᵢ] → A[1/∏ fᵢ][Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`
  let κ : KummerAlgebra n f →ₐ[A]
      KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i)) :=
    KummerAlgebra.lift (KummerAlgebra.T n _) fun i ↦ by
      rw [KummerAlgebra.T_pow, ← IsScalarTower.algebraMap_apply]
  have hκu : IsUnit (κ (algebraMap A (KummerAlgebra n f) (∏ i, f i))) := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A (Localization.Away (∏ i, f i))]
    exact (IsLocalization.Away.algebraMap_isUnit _).map _
  let ψ := IsLocalization.Away.lift (S := Localization.Away (algebraMap A (KummerAlgebra n f)
    (∏ i, f i))) _ hκu
  have hφA (a : A) : ψ (Φ (algebraMap A B a)) = algebraMap A
      (KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i))) a := by
    have e : algebraMap A (Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i))) a =
        algebraMap (KummerAlgebra n f) _ (algebraMap A (KummerAlgebra n f) a) :=
      IsScalarTower.algebraMap_apply _ _ _ _
    rw [Φ.commutes, e, IsLocalization.Away.lift_eq]
    exact κ.commutes a
  have hext : (ψ.comp Φ.toRingHom).comp (algebraMap (Localization.Away (∏ i, f i)) B) =
      algebraMap (Localization.Away (∏ i, f i))
        (KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i))) :=
    IsLocalization.ringHom_ext (Submonoid.powers (∏ i, f i)) (RingHom.ext fun a ↦ by
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply]
      change ψ (Φ (algebraMap A B a)) = _
      rw [hφA, ← IsScalarTower.algebraMap_apply])
  let φ : B →ₐ[Localization.Away (∏ i, f i)]
      KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i)) :=
    { ψ.comp Φ.toRingHom with commutes' := fun s ↦ DFunLike.congr_fun hext s }
  -- `φ` is injective: `B` is a domain, integral over `A[1/∏ fᵢ]`
  have hprod0 : ∏ i, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hf0 i
  have : IsDomain (Localization.Away (∏ i, f i)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hprod0)
  refine ⟨φ, (injective_iff_map_eq_zero φ).mpr fun x hx ↦ ?_⟩
  have hker : RingHom.ker φ = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := Localization.Away (∏ i, f i)) ?_
    refine eq_bot_iff.mpr fun s hs ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, φ.commutes] at hs
    exact (map_eq_zero_iff _ (KummerAlgebra.injective_algebraMap _ hnpos)).mp hs
  have : x ∈ RingHom.ker φ := hx
  rwa [hker] at this

set_option maxHeartbeats 800000 in
-- many localizations
/-- Away from the divisor the covering is unramified: if `g ∉ P`, `B` is an integral formally
unramified `A[1/g]`-algebra and `N = A - P`, then `N⁻¹(A₂ ⊗_A B)` is integral and formally
unramified over `N⁻¹A₂`, hence so is the normalization of `N⁻¹A₂` in it (which is everything). -/
theorem formallyUnramified_integralClosure_of_notMem {A A₂ : Type u} [CommRing A] [CommRing A₂]
    [Algebra A A₂] (P : Ideal A) [P.IsPrime] {g : A} (hg : g ∉ P)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra (Localization.Away g) B]
    [IsScalarTower A (Localization.Away g) B] [Algebra.IsIntegral (Localization.Away g) B]
    [Algebra.FormallyUnramified (Localization.Away g) B] :
    Algebra.FormallyUnramified (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (integralClosure (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
        (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
          (Algebra.algebraMapSubmonoid A₂ P.primeCompl)))) := by
  classical
  -- formal unramifiedness
  have : Algebra.FormallyUnramified A (Localization.Away g) :=
    Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers g)
  have : Algebra.FormallyUnramified A B := Algebra.FormallyUnramified.comp A (Localization.Away g) B
  have : Algebra.FormallyUnramified (A₂ ⊗[A] B) (Localization (Algebra.algebraMapSubmonoid
      (A₂ ⊗[A] B) (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) :=
    Algebra.FormallyUnramified.of_isLocalization
      (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B) (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
  have : Algebra.FormallyUnramified A₂ (Localization (Algebra.algebraMapSubmonoid
      (A₂ ⊗[A] B) (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) :=
    Algebra.FormallyUnramified.comp A₂ (A₂ ⊗[A] B) _
  have hFU : Algebra.FormallyUnramified (Localization (Algebra.algebraMapSubmonoid A₂
      P.primeCompl)) (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
        (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) :=
    Algebra.FormallyUnramified.of_restrictScalars A₂ _ _
  -- integrality
  have hint : ∀ c : Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
      (Algebra.algebraMapSubmonoid A₂ P.primeCompl)),
      IsIntegral (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) c := by
    intro c
    obtain ⟨⟨x, ⟨_, s₂, hs₂, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B) (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) c
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    refine IsIntegral.mul ?_ ?_
    · induction x using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact isIntegral_zero
      | add x y hx hy => rw [map_add]; exact hx.add hy
      | tmul a b =>
        rw [← mul_one a, ← one_mul b, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul]
        refine IsIntegral.mul ?_ ?_
        · have : algebraMap (A₂ ⊗[A] B) (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
              (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) (a ⊗ₜ 1) =
              algebraMap (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) _
                (algebraMap A₂ _ a) := by
            rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A₂ (A₂ ⊗[A] B),
              Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
          rw [this]
          exact isIntegral_algebraMap
        · obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
            (Rₘ := Localization.Away g) (Submonoid.powers g) b (Algebra.IsIntegral.isIntegral b)
          rw [Submonoid.smul_def] at hk
          have h1 : IsIntegral (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
              (algebraMap (A₂ ⊗[A] B) (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
                (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) ((1 : A₂) ⊗ₜ[A] ((g ^ k) • b))) :=
            (((hk.map (Algebra.TensorProduct.includeRight (R := A) (A := A₂) (B := B))).tower_top
              (A := A₂)).map (IsScalarTower.toAlgHom A₂ (A₂ ⊗[A] B) _)).tower_top
          have hu : IsUnit (algebraMap A₂ (Localization (Algebra.algebraMapSubmonoid A₂
              P.primeCompl)) (algebraMap A A₂ (g ^ k))) := by
            exact IsLocalization.map_units _ (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem
              (⟨g ^ k, pow_mem hg k⟩ : P.primeCompl)⟩ :
                Algebra.algebraMapSubmonoid A₂ P.primeCompl)
          obtain ⟨u, hu⟩ := hu
          have h2 : algebraMap (A₂ ⊗[A] B) (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
              (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) ((1 : A₂) ⊗ₜ[A] b) =
              algebraMap (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) _
                (↑u⁻¹) * algebraMap (A₂ ⊗[A] B) _ ((1 : A₂) ⊗ₜ[A] ((g ^ k) • b)) := by
            rw [TensorProduct.tmul_smul, Algebra.smul_def, map_mul,
              IsScalarTower.algebraMap_apply A A₂ (A₂ ⊗[A] B),
              ← IsScalarTower.algebraMap_apply A₂ (A₂ ⊗[A] B),
              IsScalarTower.algebraMap_apply A₂ (Localization (Algebra.algebraMapSubmonoid A₂
                P.primeCompl)), ← hu, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
          rw [h2]
          exact isIntegral_algebraMap.mul h1
    · have : IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
          (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) (1 : A₂ ⊗[A] B)
          ⟨algebraMap A₂ (A₂ ⊗[A] B) s₂, Algebra.mem_algebraMapSubmonoid_of_mem ⟨s₂, hs₂⟩⟩ =
          algebraMap (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl)) _
            (IsLocalization.mk' _ (1 : A₂) ⟨s₂, hs₂⟩) := by
        rw [IsLocalization.mk'_eq_iff_eq_mul, map_one, ← IsScalarTower.algebraMap_apply A₂
          (A₂ ⊗[A] B), IsScalarTower.algebraMap_apply A₂ (Localization
            (Algebra.algebraMapSubmonoid A₂ P.primeCompl)), ← map_mul, IsLocalization.mk'_spec,
          map_one, map_one]
      rw [this]
      exact isIntegral_algebraMap
  have htop : integralClosure (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
      (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
        (Algebra.algebraMapSubmonoid A₂ P.primeCompl))) = ⊤ :=
    eq_top_iff.mpr fun c _ ↦ hint c
  exact Algebra.FormallyUnramified.of_equiv
    ((Subalgebra.equivOfEq _ _ htop).trans Subalgebra.topEquiv).symm

set_option maxHeartbeats 1600000 in
-- many localizations
/-- XIII.5.3 for every strictly henselian regular local ring `A` (any characteristic): every
integral finite étale `A[1/∏ fᵢ]`-algebra `B` tamely ramified along `Σ div fᵢ` embeds into
`A[1/∏ fᵢ][Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` for integers `nᵢ > 0` prime to the residue characteristic `p`.
Take common multiples `Nᵢ` of the ramification indices (nonzero in `κ((fᵢ))`); `B` maps to
`A'[1/∏ fᵢ]`, `A' = A[Tᵢ]/(Tᵢ^{Nᵢ} - fᵢ)` (`nonempty_algHom_away_kummerAlgebra`). If `p` divides
some `Nᵢ`, write `Nᵢ = p^{aᵢ} N'ᵢ` with `p ∤ N'ᵢ` and `A₂ = A[Tᵢ]/(Tᵢ^{N'ᵢ} - fᵢ) → A'`,
`Tᵢ ↦ Tᵢ^{p^{aᵢ}}`, which is radicial modulo `p`. SGA's descent argument
(`mem_range_of_formallyUnramified_integralClosure`) at a prime `P ∋ p` where `A₂ ⊗_A B` is
unramified shows that the map lands in `A₂[1/∏ fᵢ]`: `P = (f_j)` if `p ∈ (f_j)` (where
`N'_j = N_j`, `formallyEtale_integralClosure_localization_of_pow_eq`), and otherwise `P = (q)` for a
prime factor `q` of `p`, which does not meet the divisor
(`formallyUnramified_integralClosure_of_notMem`). -/
theorem exists_injective_kummerAlgebra_of_isStrictlyHenselian (A : Type u) [CommRing A]
    [IsRegularLocalRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    {r : ℕ} (f : Fin r → A) (hf : IsPartOfRegularSystemOfParameters f)
    (B : Type u) [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B) :
    ∃ n : Fin r → ℕ, (∀ i, 0 < n i ∧ (n i : A) ∉ maximalIdeal A) ∧
      ∃ φ : B →ₐ[Localization.Away (∏ i, f i)]
          KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i)),
        Function.Injective φ := by
  classical
  -- common multiples `Nᵢ` of the ramification indices, nonzero in `κ((fᵢ))`
  have hN : ∀ i, ∃ n : ℕ, (n : A) ∉ Ideal.span {f i} ∧
      ∀ (Q : Ideal (integralClosure A (FractionRing A ⊗[A] B))) [Q.IsPrime],
        Q.LiesOver (Ideal.span {f i}) → Q.ramificationIdx A ∣ n := fun i ↦ by
    obtain ⟨_, _⟩ := hf.isDiscreteValuationRing_localization i
    exact exists_ramificationIdx_dvd_of_isTamelyRamifiedAlong f hf.ne_zero B hB i
  choose N hNf hNdvd using hN
  have hNpos (i : Fin r) : 0 < N i := Nat.pos_of_ne_zero fun h ↦ hNf i (by
    rw [h, Nat.cast_zero]; exact zero_mem _)
  have hmem (n : ℕ) : (n : A) ∈ maximalIdeal A ↔ ringChar (ResidueField A) ∣ n := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, ringChar.spec]
  obtain ⟨Φ⟩ := nonempty_algHom_away_kummerAlgebra A f hf B hB N hNpos
    fun i Q _ hQ ↦ hNdvd i Q hQ
  by_cases hall : ∀ i, (N i : A) ∉ maximalIdeal A
  · exact ⟨N, fun i ↦ ⟨hNpos i, hall i⟩,
      exists_injective_kummerAlgebra_of_algHom A f hf.ne_zero B N hNpos Φ⟩
  push Not at hall
  obtain ⟨i₀, hi₀⟩ := hall
  -- `p = char κ` is prime, and `p ∉ (f_{i₀})`
  set p := ringChar (ResidueField A) with hp
  have hpN : p ∣ N i₀ := (hmem _).mp hi₀
  have hp0 : p ≠ 0 := fun h ↦ (hNpos i₀).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hpN))
  have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero (ResidueField A) p).resolve_right hp0⟩
  have hpf₀ : (p : A) ∉ Ideal.span {f i₀} := fun h ↦ hNf i₀ (by
    obtain ⟨c, hc⟩ := hpN
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h)
  -- `Nᵢ = p^{aᵢ} N'ᵢ`
  let a : Fin r → ℕ := fun i ↦ (N i).factorization p
  let N' : Fin r → ℕ := fun i ↦ N i / p ^ a i
  have hNN' (i : Fin r) : p ^ a i * N' i = N i := Nat.ordProj_mul_ordCompl_eq_self (N i) p
  have hN'pos (i : Fin r) : 0 < N' i := Nat.ordCompl_pos p (hNpos i).ne'
  have hN'm (i : Fin r) : (N' i : A) ∉ maximalIdeal A := by
    rw [hmem]
    exact Nat.not_dvd_ordCompl Fact.out (hNpos i).ne'
  -- an abstract copy `A₂` of `A[Tᵢ]/(Tᵢ^{N'ᵢ} - fᵢ)`
  obtain ⟨A₂, _, _, _, ⟨σ₂⟩⟩ : ∃ (A₂ : Type u) (_ : CommRing A₂) (_ : Algebra A A₂)
      (_ : IsRegularLocalRing A₂), Nonempty (A₂ ≃ₐ[A] KummerAlgebra N' f) :=
    ⟨_, _, _, KummerAlgebra.isRegularLocalRing hN'pos hf, ⟨AlgEquiv.refl⟩⟩
  -- `ι : A₂ → A' = A[Tᵢ]/(Tᵢ^{Nᵢ} - fᵢ)`, `Tᵢ ↦ Tᵢ^{p^{aᵢ}}`
  let ι : A₂ →ₐ[A] KummerAlgebra N f :=
    (KummerAlgebra.lift (fun i ↦ KummerAlgebra.T N f i ^ p ^ a i) fun i ↦ by
      rw [← pow_mul, hNN', KummerAlgebra.T_pow]).comp σ₂.toAlgHom
  have : IsRegularLocalRing (KummerAlgebra N f) := KummerAlgebra.isRegularLocalRing hNpos hf
  have : Algebra.IsIntegral A (KummerAlgebra N f) := KummerAlgebra.isIntegral f hNpos
  have : Algebra.IsIntegral A (KummerAlgebra N' f) := KummerAlgebra.isIntegral f hN'pos
  have : Algebra.IsIntegral A A₂ := ⟨fun x ↦ by
    simpa using (Algebra.IsIntegral.isIntegral (R := A) (σ₂ x)).map σ₂.symm.toAlgHom⟩
  have : Module.Finite A (KummerAlgebra N f) := Algebra.IsIntegral.finite
  let : Algebra A₂ (KummerAlgebra N f) := ι.toRingHom.toAlgebra
  have : IsScalarTower A A₂ (KummerAlgebra N f) := IsScalarTower.of_algHom ι
  have : Module.Finite A₂ (KummerAlgebra N f) := Module.Finite.of_restrictScalars_finite A _ _
  have hinjA : Function.Injective (algebraMap A A₂) := fun x y h ↦
    KummerAlgebra.injective_algebraMap f hN'pos (by rw [← σ₂.commutes, ← σ₂.commutes, h])
  have hinj₂ : Function.Injective (algebraMap A₂ (KummerAlgebra N f)) := by
    refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    have hker : RingHom.ker (algebraMap A₂ (KummerAlgebra N f)) = ⊥ := by
      refine Ideal.eq_bot_of_comap_eq_bot (R := A) (eq_bot_iff.mpr fun a ha ↦ ?_)
      rw [Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply,
        map_eq_zero_iff _ (KummerAlgebra.injective_algebraMap f hNpos)] at ha
      exact ha
    have : x ∈ RingHom.ker (algebraMap A₂ (KummerAlgebra N f)) := hx
    rwa [hker] at this
  have hgen : Algebra.adjoin A₂ (Set.range (KummerAlgebra.T N f)) = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    have hx : x ∈ Algebra.adjoin A (Set.range (KummerAlgebra.T N f)) := by
      rw [KummerAlgebra.adjoin_range_T]; trivial
    have hle : Algebra.adjoin A (Set.range (KummerAlgebra.T N f)) ≤
        (Algebra.adjoin A₂ (Set.range (KummerAlgebra.T N f))).restrictScalars A :=
      Algebra.adjoin_le fun _ hy ↦ Algebra.subset_adjoin hy
    exact hle hx
  have ht : ∀ i, KummerAlgebra.T N f i ^ p ^ a i ∈
      Set.range (algebraMap A₂ (KummerAlgebra N f)) := fun i ↦
    ⟨σ₂.symm (KummerAlgebra.T N' f i), by
      change ι (σ₂.symm (KummerAlgebra.T N' f i)) = _
      simp [ι, KummerAlgebra.lift_T]⟩
  -- a prime `P ∋ p` of `A` at which `A₂ ⊗_A B` is unramified
  suffices H : ∀ (P : Ideal A) [P.IsPrime], (p : A) ∈ P →
      Algebra.FormallyUnramified
        (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
        (integralClosure
          (Localization (Algebra.algebraMapSubmonoid A₂ P.primeCompl))
          (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
            (Algebra.algebraMapSubmonoid A₂ P.primeCompl)))) →
      ∃ n : Fin r → ℕ, (∀ i, 0 < n i ∧ (n i : A) ∉ maximalIdeal A) ∧
        ∃ φ : B →ₐ[Localization.Away (∏ i, f i)]
            KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i)),
          Function.Injective φ by
    by_cases hJ : ∃ j, (p : A) ∈ Ideal.span {f j}
    · obtain ⟨j, hj⟩ := hJ
      have : (Ideal.span {f j}).IsPrime := hf.isPrime_span_singleton j
      have hpj : ¬ p ∣ N j := fun h ↦ hNf j (by
        obtain ⟨c, hc⟩ := h
        rw [hc, Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ hj)
      have haj : N' j = N j := by
        simp [N', a, Nat.factorization_eq_zero_of_not_dvd hpj]
      have := formallyEtale_integralClosure_localization_of_pow_eq A f hf B hB j (N' j)
        (hN'pos j) (fun Q _ hQ ↦ haj ▸ hNdvd j Q hQ) A₂ hinjA
        (σ₂.symm (KummerAlgebra.T N' f j)) (by
          rw [← map_pow, KummerAlgebra.T_pow, AlgEquiv.commutes])
        (Localization (Algebra.algebraMapSubmonoid A₂ (Ideal.span {f j}).primeCompl))
        (Localization (Algebra.algebraMapSubmonoid (A₂ ⊗[A] B)
          (Algebra.algebraMapSubmonoid A₂ (Ideal.span {f j}).primeCompl)))
      exact H _ hj (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mp this).1
    · push Not at hJ
      have hp0A : (p : A) ≠ 0 := fun h ↦ hpf₀ (h ▸ zero_mem _)
      have hpu : ¬ IsUnit (p : A) := fun h ↦
        (IsLocalRing.mem_maximalIdeal _).mp ((hmem p).mpr dvd_rfl) h
      obtain ⟨q, hq, hqp⟩ := WfDvdMonoid.exists_irreducible_factor hpu hp0A
      have hqprime : Prime q := UniqueFactorizationMonoid.irreducible_iff_prime.mp hq
      have : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hqprime.ne_zero).mpr hqprime
      have hgP : (∏ i, f i) ∉ Ideal.span {q} := by
        rw [Ideal.mem_span_singleton]
        intro hdvd
        obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hqprime _).mp hdvd
        have hfj : Prime (f j) :=
          (Ideal.span_singleton_prime (hf.ne_zero j)).mp (hf.isPrime_span_singleton j)
        obtain ⟨c, hc⟩ := hj
        have hcu : IsUnit c :=
          (hfj.irreducible.isUnit_or_isUnit hc).resolve_left hqprime.not_isUnit
        refine hJ j (Ideal.mem_span_singleton.mpr (dvd_trans ⟨↑hcu.unit⁻¹, ?_⟩ hqp))
        rw [hc, mul_assoc, IsUnit.mul_val_inv, mul_one]
      exact H _ (Ideal.mem_span_singleton.mpr hqp)
        (formallyUnramified_integralClosure_of_notMem (A₂ := A₂) _ hgP B)
  intro P _ hpP hD
  -- `A₂[1/g] → A'[1/g]`
  have hg0 : ∏ i, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ hf.ne_zero i
  have hunitsg : ∀ y : Submonoid.powers (algebraMap A A₂ (∏ i, f i)),
      IsUnit (algebraMap A₂ (Localization.Away (algebraMap A (KummerAlgebra N f) (∏ i, f i)))
        y) := by
    rintro ⟨_, k, rfl⟩
    rw [map_pow, IsScalarTower.algebraMap_apply A₂ (KummerAlgebra N f),
      ← IsScalarTower.algebraMap_apply A A₂ (KummerAlgebra N f)]
    exact (IsLocalization.Away.algebraMap_isUnit _).pow k
  let : Algebra (Localization.Away (algebraMap A A₂ (∏ i, f i)))
      (Localization.Away (algebraMap A (KummerAlgebra N f) (∏ i, f i))) :=
    (IsLocalization.lift hunitsg).toAlgebra
  have : IsScalarTower A₂ (Localization.Away (algebraMap A A₂ (∏ i, f i)))
      (Localization.Away (algebraMap A (KummerAlgebra N f) (∏ i, f i))) :=
    .of_algebraMap_eq fun a ↦ (IsLocalization.lift_eq hunitsg a).symm
  have : Algebra.IsIntegral (Localization.Away (∏ i, f i)) B := Algebra.IsIntegral.of_finite _ _
  have hdesc := mem_range_of_formallyUnramified_integralClosure hinjA hinj₂ p
    (KummerAlgebra.T N f) hgen a ht P hpP hg0 B
    (Localization.Away (algebraMap A (KummerAlgebra N f) (∏ i, f i)))
    (Localization.Away (algebraMap A A₂ (∏ i, f i))) Φ hD
  -- `A₂[1/g] → A'[1/g]` is injective
  have hinjg : Function.Injective (algebraMap (Localization.Away (algebraMap A A₂ (∏ i, f i)))
      (Localization.Away (algebraMap A (KummerAlgebra N f) (∏ i, f i)))) := by
    refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    obtain ⟨y, s, rfl⟩ := IsLocalization.exists_mk'_eq
      (Submonoid.powers (algebraMap A A₂ (∏ i, f i))) x
    have h1 : algebraMap A₂ (Localization.Away (algebraMap A (KummerAlgebra N f) (∏ i, f i))) y
        = 0 := by
      rw [IsScalarTower.algebraMap_apply A₂ (Localization.Away (algebraMap A A₂ (∏ i, f i))),
        ← IsLocalization.mk'_spec (Localization.Away (algebraMap A A₂ (∏ i, f i))) y s, map_mul,
        hx, zero_mul]
    rw [IsScalarTower.algebraMap_apply A₂ (KummerAlgebra N f)] at h1
    have hpow : Submonoid.powers (algebraMap A (KummerAlgebra N f) (∏ i, f i)) ≤
        nonZeroDivisors (KummerAlgebra N f) := powers_le_nonZeroDivisors_of_noZeroDivisors
      ((map_ne_zero_iff _ (KummerAlgebra.injective_algebraMap f hNpos)).mpr hg0)
    have h2 := IsLocalization.injective (Localization.Away (algebraMap A (KummerAlgebra N f)
      (∏ i, f i))) hpow (h1.trans (map_zero _).symm)
    rw [(map_eq_zero_iff _ hinj₂).mp h2, IsLocalization.mk'_zero]
  -- `Φ' : B → A₂[1/g]`
  let j₂ := algebraMap (Localization.Away (algebraMap A A₂ (∏ i, f i)))
    (Localization.Away (algebraMap A (KummerAlgebra N f) (∏ i, f i)))
  let Φ'₀ : B →+* Localization.Away (algebraMap A A₂ (∏ i, f i)) :=
    (RingEquiv.ofBijective j₂.rangeRestrict ⟨fun x y h ↦ hinjg (congrArg Subtype.val h),
      j₂.rangeRestrict_surjective⟩).symm.toRingHom.comp
      (Φ.toRingHom.codRestrict j₂.range hdesc)
  have hΦ' (b : B) : j₂ (Φ'₀ b) = Φ b := by
    have := (RingEquiv.ofBijective j₂.rangeRestrict ⟨fun x y h ↦ hinjg (congrArg Subtype.val h),
      j₂.rangeRestrict_surjective⟩).apply_symm_apply (Φ.toRingHom.codRestrict j₂.range hdesc b)
    exact congrArg Subtype.val this
  have hj₂A (a : A) : j₂ (algebraMap A (Localization.Away (algebraMap A A₂ (∏ i, f i))) a) =
      algebraMap A (Localization.Away (algebraMap A (KummerAlgebra N f) (∏ i, f i))) a := by
    rw [IsScalarTower.algebraMap_apply A A₂ (Localization.Away (algebraMap A A₂ (∏ i, f i))),
      ← IsScalarTower.algebraMap_apply A₂ (Localization.Away (algebraMap A A₂ (∏ i, f i))),
      IsScalarTower.algebraMap_apply A₂ (KummerAlgebra N f), ← IsScalarTower.algebraMap_apply A,
      ← IsScalarTower.algebraMap_apply]
  let Φ' : B →ₐ[A] Localization.Away (algebraMap A A₂ (∏ i, f i)) :=
    { Φ'₀ with
      commutes' := fun a ↦ hinjg (by
        change j₂ (Φ'₀ (algebraMap A B a)) = _
        rw [hΦ', Φ.commutes, hj₂A]) }
  -- `Ψ : A₂[1/g] → (A[Tᵢ]/(Tᵢ^{N'ᵢ} - fᵢ))[1/g]`
  have hΨu : IsUnit (((algebraMap (KummerAlgebra N' f) (Localization.Away (algebraMap A
      (KummerAlgebra N' f) (∏ i, f i)))).comp σ₂.toRingHom) (algebraMap A A₂ (∏ i, f i))) := by
    rw [RingHom.comp_apply]
    change IsUnit (algebraMap _ _ (σ₂ (algebraMap A A₂ (∏ i, f i))))
    rw [AlgEquiv.commutes]
    exact IsLocalization.Away.algebraMap_isUnit _
  let Ψ₀ := IsLocalization.Away.lift (S := Localization.Away (algebraMap A A₂ (∏ i, f i))) _ hΨu
  let Ψ : Localization.Away (algebraMap A A₂ (∏ i, f i)) →ₐ[A]
      Localization.Away (algebraMap A (KummerAlgebra N' f) (∏ i, f i)) :=
    { Ψ₀ with
      commutes' := fun a ↦ by
        change Ψ₀ _ = _
        rw [IsScalarTower.algebraMap_apply A A₂ (Localization.Away (algebraMap A A₂ (∏ i, f i))),
          IsLocalization.Away.lift_eq, RingHom.comp_apply]
        change algebraMap _ _ (σ₂ (algebraMap A A₂ a)) = _
        rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply] }
  exact ⟨N', fun i ↦ ⟨hN'pos i, hN'm i⟩,
    exists_injective_kummerAlgebra_of_algHom A f hf.ne_zero B N' hN'pos (Ψ.comp Φ')⟩

/-- XIII.5.2, extension part, with `nᵢ` the l.c.m. of the ramification indices and no assumption on
the characteristic: the restriction of `B` to `U' = Spec A'[1/∏ fᵢ]`,
`A' = A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`, extends to a finite étale `A'`-algebra. -/
theorem absoluteAbhyankar_extension (A : Type u) [CommRing A] [IsRegularLocalRing A] {r : ℕ}
    (f : Fin r → A) (hf : IsPartOfRegularSystemOfParameters f)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B)
    (n : Fin r → ℕ) (hn : ∀ i, IsLcmRamificationIndices (Ideal.span {f i}) B (n i)) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra (KummerAlgebra n f) W),
      Module.Finite (KummerAlgebra n f) W ∧ Algebra.Etale (KummerAlgebra n f) W ∧
      Nonempty (KummerAlgebra n f ⊗[A] B ≃ₐ[KummerAlgebra n f]
        Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)) ⊗[KummerAlgebra n f]
          W) := by
  refine exists_etale_kummerAlgebra_of_isTamelyRamifiedAlong_of_pos A f hf B hB n
    (fun i ↦ ?_) fun i Q _ hQ ↦ (hn i).1 Q hQ
  obtain ⟨_, _⟩ := hf.isDiscreteValuationRing_localization i
  obtain ⟨N, hNf, hNdvd⟩ := exists_ramificationIdx_dvd_of_isTamelyRamifiedAlong f hf.ne_zero B hB i
  have hN0 : N ≠ 0 := fun h ↦ hNf (by rw [h, Nat.cast_zero]; exact zero_mem _)
  exact Nat.pos_of_ne_zero fun h ↦ hN0 (Nat.eq_zero_of_zero_dvd
    (h ▸ (hn i).2 N fun Q _ hQ ↦ hNdvd Q hQ))

end SGA.SGA1.ExposeXIII
