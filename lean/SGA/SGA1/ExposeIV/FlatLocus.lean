/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIV.Constructible
import SGA.SGA1.ExposeIV.GenericFreeness
import SGA.SGA1.ExposeIV.LocalCriterion

/-!
# SGA 1, Exposé IV, §6: openness of the flat locus

Let `A` be noetherian, `B` a finitely generated `A`-algebra and `M` a finite `B`-module.

* IV.6.8: if `M_𝔭` is flat over `A` (`𝔭` prime in `B`, `𝔮 = 𝔭 ∩ A`), there is `g ∉ 𝔭` such
  that `(M/𝔮M)_g` is flat over `A/𝔮` and `Tor₁^A(M, A/𝔮)_g = 0`;
* IV.6.9: then `M_𝔭'` is flat over `A` for every prime `𝔭' ⊇ 𝔭` not containing `g`;
* IV.6.10: the set of primes `𝔭` of `B` at which `M` is `A`-flat is open (the affine case of the
  theorem);
* IV.6.11: if `A` is a domain, `M` is flat over `A` at every point over some nonempty open subset
  of `Spec A`.

The scheme forms of IV.6.10 and IV.6.11 are in `Schemes` (for `F = 𝒪_X`) and in
`CoherentModules` (for a coherent sheaf `F`).

The proofs follow SGA: generic freeness (IV.6.7, in `GenericFreeness`) over `A/𝔮`, the local
flatness criterion IV.5.6 and the openness criterion IV.6.4. Flatness of localizations is handled
through the following observation: `f ⊗ M_T` is injective iff every element of the kernel of
`f ⊗ M` is killed by an element of `T`.
-/

universe u v

namespace SGA.SGA1.ExposeIV

open TensorProduct LinearMap Function

section Localization

variable {R : Type*} [CommRing R] (S : Submonoid R)
  {X X' Y Y' : Type*} [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R X']
  [AddCommGroup Y] [Module R Y] [AddCommGroup Y'] [Module R Y']
  (i₁ : X →ₗ[R] X') (i₂ : Y →ₗ[R] Y') [IsLocalizedModule S i₁] [IsLocalizedModule S i₂]

/-- The localization of a map whose kernel is `S`-torsion is injective. -/
lemma IsLocalizedModule.map_injective_of_torsion (h : X →ₗ[R] Y)
    (hk : ∀ x, h x = 0 → ∃ s : S, s • x = 0) : Injective (IsLocalizedModule.map S i₁ i₂ h) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S i₁ y
  simp only [uncurry_apply_pair, IsLocalizedModule.map_mk'] at hy
  obtain ⟨c, hc⟩ := (IsLocalizedModule.mk'_eq_zero' i₂ s).1 hy
  rw [Submonoid.smul_def, ← map_smul] at hc
  obtain ⟨c', hc'⟩ := hk _ hc
  change IsLocalizedModule.mk' i₁ x s = 0
  rw [IsLocalizedModule.mk'_eq_zero']
  exact ⟨c' * c, by rw [mul_smul, Submonoid.smul_def c, hc']⟩

/-- Conversely, if the localization of `h` is injective, the kernel of `h` is `S`-torsion. -/
lemma IsLocalizedModule.torsion_of_map_injective (h : X →ₗ[R] Y)
    (hinj : Injective (IsLocalizedModule.map S i₁ i₂ h)) (x : X) (hx : h x = 0) :
    ∃ s : S, s • x = 0 := by
  have : i₁ x = 0 := hinj (by rw [IsLocalizedModule.map_apply, hx, map_zero, map_zero])
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := i₁)
    (this.trans (map_zero _).symm)
  exact ⟨c, by rw [hc, smul_zero]⟩

end Localization

section LocalizedTensor

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  (T : Submonoid B) {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]

/-- `M_T ⊗ X → M_T ⊗ Y` is the localization at `T` of `M ⊗ X → M ⊗ Y`. -/
private lemma coe_lTensor_localizedModule (f : X →ₗ[A] Y) :
    ⇑(f.lTensor (LocalizedModule T M)) = IsLocalizedModule.map T
      (AlgebraTensorModule.rTensor A X (LocalizedModule.mkLinearMap T M))
      (AlgebraTensorModule.rTensor A Y (LocalizedModule.mkLinearMap T M))
      (AlgebraTensorModule.lTensor B M f) := by
  rw [IsLocalizedModule.map_lTensor, AlgebraTensorModule.coe_lTensor]

/-- `f ⊗ M_T` is injective if and only if every element of the kernel of `f ⊗ M` is killed by
an element of `T`. -/
theorem lTensor_localizedModule_injective_iff (f : X →ₗ[A] Y) :
    Injective (f.lTensor (LocalizedModule T M)) ↔
      ∀ x : M ⊗[A] X, f.lTensor M x = 0 → ∃ t ∈ T, t • x = 0 := by
  rw [coe_lTensor_localizedModule]
  constructor
  · intro h x hx
    obtain ⟨t, ht⟩ := IsLocalizedModule.torsion_of_map_injective T _ _ _ h x
      (by rwa [AlgebraTensorModule.coe_lTensor])
    exact ⟨t, t.2, ht⟩
  · intro h
    refine IsLocalizedModule.map_injective_of_torsion T _ _ _ fun x hx ↦ ?_
    obtain ⟨t, ht, htx⟩ := h x (by rwa [AlgebraTensorModule.coe_lTensor] at hx)
    exact ⟨⟨t, ht⟩, htx⟩

/-- Flatness of a localization `M_T` over `A`, in terms of `M`. -/
theorem flat_localizedModule_iff :
    Module.Flat A (LocalizedModule T M) ↔ ∀ I : Ideal A, ∀ x : M ⊗[A] I,
      I.subtype.lTensor M x = 0 → ∃ t ∈ T, t • x = 0 := by
  rw [Module.Flat.iff_lTensor_injective']
  exact forall_congr' fun I ↦ lTensor_localizedModule_injective_iff T I.subtype

end LocalizedTensor


section FreeAway

variable {A' : Type*} [CommRing A'] {N : Type v} [AddCommGroup N] [Module A' N] {f : A'}

/-- If `N` is free after inverting `f` (`IsFreeAway`), then for every ideal `J`, the kernel of
`J ⊗ N → N` is killed by powers of `f`: `N_f` is flat. -/
theorem IsFreeAway.exists_pow_smul_eq_zero (h : IsFreeAway f N) (J : Ideal A')
    (x : J ⊗[A'] N) (hx : J.subtype.rTensor N x = 0) : ∃ n : ℕ, f ^ n • x = 0 := by
  obtain ⟨F, _, _, _, φ, hker, hcoker⟩ := h
  -- some `f ^ K • x` comes from `J ⊗ F`
  have hlift : ∀ y : J ⊗[A'] N, ∃ (K : ℕ) (z : J ⊗[A'] F), f ^ K • y = φ.lTensor J z := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul j n =>
      obtain ⟨k, y, hy⟩ := hcoker n
      exact ⟨k, j ⊗ₜ y, by rw [lTensor_tmul, hy, tmul_smul]⟩
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨K₁, z₁, hz₁⟩ := h₁
      obtain ⟨K₂, z₂, hz₂⟩ := h₂
      refine ⟨K₁ + K₂, f ^ K₂ • z₁ + f ^ K₁ • z₂, ?_⟩
      rw [map_add, map_smul, map_smul, ← hz₁, ← hz₂, smul_smul, smul_smul, ← pow_add, ← pow_add,
        smul_add, add_comm K₂ K₁]
  obtain ⟨K, z, hz⟩ := hlift x
  -- its image `w` in `A' ⊗ F` maps to zero in `N`, hence is killed by a power of `f`
  set w := J.subtype.rTensor F z
  have hw : φ.lTensor A' w = 0 := by
    rw [← rTensor_lTensor_apply, ← hz, map_smul, hx, smul_zero]
  have hlid : TensorProduct.lid A' N (φ.lTensor A' w) = φ (TensorProduct.lid A' F w) := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a y => simp
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  obtain ⟨m, hm⟩ := hker _ (by rw [← hlid, hw, map_zero])
  have hmw : f ^ m • w = 0 := (TensorProduct.lid A' F).injective (by rw [map_smul, hm, map_zero])
  -- `F` is flat, so `f ^ m • z = 0`
  have hmz : f ^ m • z = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := F) J.subtype Subtype.val_injective
    rw [map_smul, map_zero]
    exact hmw
  exact ⟨m + K, by rw [pow_add, mul_smul, hz, ← map_smul, hmz, map_zero]⟩

end FreeAway

section Fibre

variable {A : Type u} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
  {M : Type v} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  (q : Ideal A)

/-- Generic flatness of `M/𝔮M` over `A/𝔮` (the core of IV.6.8 (a)): there is `f ∉ 𝔮` such that
for every ideal `J` of `A/𝔮`, the kernel of `M ⊗_A J → M ⊗_A A/𝔮` is killed by powers of `f`. -/
theorem exists_forall_lTensor_torsion [IsNoetherianRing A] [Algebra.FiniteType A B]
    [Module.Finite B M] [q.IsPrime] :
    ∃ f : A, f ∉ q ∧ ∀ J : Ideal (A ⧸ q), ∀ x : M ⊗[A] J,
      (J.subtype.restrictScalars A).lTensor M x = 0 → ∃ n : ℕ, f ^ n • x = 0 := by
  let A' := A ⧸ q
  let Q := q.map (algebraMap A B)
  let B' := B ⧸ Q
  let N := M ⧸ (Q • (⊤ : Submodule B M))
  let : Module A' N := Module.compHom N (algebraMap A' B')
  have : IsScalarTower A' B' N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower A A' N := IsScalarTower.of_algebraMap_smul fun a n ↦ by
    change algebraMap A' B' (algebraMap A A' a) • n = a • n
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B B',
      algebraMap_smul, algebraMap_smul]
  have : Module.Finite B' N := by
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := N)
    refine ⟨⟨s, ?_⟩⟩
    rw [← Submodule.restrictScalars_eq_top_iff B,
      Submodule.restrictScalars_span B B' Ideal.Quotient.mk_surjective, hs]
  have : Algebra.FiniteType A B' :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A Q) Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType A' B' := Algebra.FiniteType.of_restrictScalars_finiteType A A' B'
  -- generic freeness of `N = M/𝔮M` over `A/𝔮`
  obtain ⟨f', hf', hfree⟩ := exists_isFreeAway_of_finiteType (A := A') (B := B') N
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f'
  refine ⟨f, fun hf ↦ hf' (Ideal.Quotient.eq_zero_iff_mem.2 hf), fun J x hx ↦ ?_⟩
  -- `A/𝔮 ⊗_A M ≃ M/𝔮M`
  let ψ : M →ₗ[A] A' ⊗[A] M := TensorProduct.mk A A' M 1
  have hQ : ∀ b ∈ Q, ∀ m : M, ψ (b • m) = 0 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨a, ha, rfl⟩ := hb
      intro m
      rw [algebraMap_smul, map_smul, TensorProduct.mk_apply, smul_tmul', Algebra.smul_def,
        mul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_tmul]
    | zero => intro m; rw [zero_smul, map_zero]
    | add b c _ _ hb hc => intro m; rw [add_smul, map_add, hb, hc, add_zero]
    | smul b c _ hc => intro m; rw [smul_eq_mul, mul_comm, mul_smul, hc]
  have hle : (Q • (⊤ : Submodule B M)).restrictScalars A ≤ LinearMap.ker ψ := by
    intro m hm
    have hm' : m ∈ Q • (⊤ : Submodule B M) := hm
    rw [LinearMap.mem_ker]
    refine Submodule.smul_induction_on hm' (fun b hb m _ ↦ hQ b hb m) fun m m' h h' ↦ ?_
    rw [map_add, h, h', add_zero]
  let bwd₀ : (M ⧸ (Q • (⊤ : Submodule B M)).restrictScalars A) →ₗ[A] A' ⊗[A] M :=
    ((Q • ⊤ : Submodule B M).restrictScalars A).liftQ ψ hle
  let e₀ : (M ⧸ (Q • (⊤ : Submodule B M)).restrictScalars A) ≃ₗ[A] N :=
    Submodule.Quotient.restrictScalarsEquiv A (Q • ⊤ : Submodule B M)
  let bwd : N →ₗ[A] A' ⊗[A] M := bwd₀ ∘ₗ e₀.symm.toLinearMap
  let fwd : A' ⊗[A] M →ₗ[A'] N :=
    LinearMap.liftBaseChange A' ((Q • ⊤ : Submodule B M).mkQ.restrictScalars A)
  have hinv (y : A' ⊗[A] M) : bwd (fwd y) = y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      have h1 : fwd (Ideal.Quotient.mk q a ⊗ₜ m) = Submodule.Quotient.mk (a • m) := by
        rw [LinearMap.liftBaseChange_tmul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
        rfl
      rw [h1]
      change ψ (a • m) = _
      rw [map_smul, TensorProduct.mk_apply, smul_tmul', Algebra.smul_def, mul_one,
        Ideal.Quotient.algebraMap_eq]
    | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  have hfwd : Bijective fwd := by
    refine ⟨fun y₁ y₂ h ↦ by rw [← hinv y₁, ← hinv y₂, h], fun n ↦ ?_⟩
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ n
    exact ⟨(1 : A') ⊗ₜ m, by rw [LinearMap.liftBaseChange_tmul, one_smul]; rfl⟩
  let E : A' ⊗[A] M ≃ₗ[A'] N := LinearEquiv.ofBijective fwd hfwd
  -- transport the kernel element to `J ⊗_{A/𝔮} N`
  let y := TensorProduct.comm A M J x
  have key (x' : M ⊗[A] J) : (J.subtype.restrictScalars A).rTensor M (TensorProduct.comm A M J x') =
      TensorProduct.comm A M A' ((J.subtype.restrictScalars A).lTensor M x') := by
    induction x' using TensorProduct.induction_on with
    | zero => simp
    | tmul m j => simp
    | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  have hy : (J.subtype.restrictScalars A).rTensor M y = 0 := by
    rw [key, hx, map_zero]
  let c := AlgebraTensorModule.cancelBaseChange A A' A' J M
  let z := c.symm y
  have hz : J.subtype.rTensor (A' ⊗[A] M) z = 0 := by
    apply (AlgebraTensorModule.cancelBaseChange A A' A' A' M).injective
    rw [cancelBaseChange_rTensor, LinearEquiv.apply_symm_apply, hy, map_zero]
  let w := E.toLinearMap.lTensor J z
  have hw : J.subtype.rTensor N w = 0 := by
    rw [rTensor_lTensor_apply, hz, map_zero]
  obtain ⟨n, hn⟩ := hfree.exists_pow_smul_eq_zero J w hw
  have hnz : (Ideal.Quotient.mk q f) ^ n • z = 0 := by
    apply (E.lTensor J).injective
    rw [map_smul, map_zero]
    exact hn
  refine ⟨n, (TensorProduct.comm A M J).injective ?_⟩
  rw [map_smul, map_zero]
  change f ^ n • y = 0
  have : y = c z := (c.apply_symm_apply y).symm
  rw [this, ← algebraMap_smul A', map_pow, Ideal.Quotient.algebraMap_eq, ← map_smul, hnz,
    map_zero]

end Fibre

section FlatLocus

variable {A : Type u} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
  {M : Type v} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- If `M_𝔭` is `A`-flat, `Tor₁^A(M, A/I)` is killed by some `g ∉ 𝔭`, for any ideal `I`. -/
lemma exists_smul_eq_zero_of_flat [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite B M]
    (p : Ideal B) [p.IsPrime] (hp : Module.Flat A (LocalizedModule p.primeCompl M))
    (I : Ideal A) :
    ∃ g ∉ p, ∀ x : M ⊗[A] I, I.subtype.lTensor M x = 0 → g • x = 0 := by
  classical
  have := finite_tensorProduct (A := A) (B := B) M I
  let K := LinearMap.ker (AlgebraTensorModule.lTensor B M I.subtype)
  obtain ⟨s, hs⟩ : K.FG := IsNoetherian.noetherian K
  have htors := (flat_localizedModule_iff p.primeCompl).1 hp I
  have hgen : ∀ k ∈ s, ∃ t ∉ p, t • k = 0 := fun k hk ↦ by
    have hkK : k ∈ K := hs ▸ Submodule.subset_span hk
    obtain ⟨t, ht, htk⟩ := htors k (by simpa [K, AlgebraTensorModule.coe_lTensor] using hkK)
    exact ⟨t, ht, htk⟩
  choose t ht htk using hgen
  let g := ∏ k ∈ s.attach, t k.1 k.2
  have hg : g ∉ p := by
    refine Submonoid.prod_mem p.primeCompl fun k _ ↦ ?_
    exact ht k.1 k.2
  refine ⟨g, hg, fun x hx ↦ ?_⟩
  have hxK : x ∈ K := by simpa [K, AlgebraTensorModule.coe_lTensor] using hx
  have : K ≤ LinearMap.ker (LinearMap.lsmul B (M ⊗[A] I) g) := by
    rw [← hs, Submodule.span_le]
    intro k hk
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.lsmul_apply]
    rw [show g = (∏ k' ∈ s.attach.erase ⟨k, hk⟩, t k'.1 k'.2) * t k hk from
      (Finset.prod_erase_mul _ _ (Finset.mem_attach _ _)).symm, mul_smul, htk, smul_zero]
  exact this hxK

/-- The data of IV.6.8, in the form used for IV.6.9: if `M_𝔭` is `A`-flat and `𝔮 = 𝔭 ∩ A`, there
is `g ∉ 𝔭` killing (a power of it) the kernels of `M ⊗_A J → M ⊗_A A/𝔮` for all ideals `J` of
`A/𝔮`, and the kernel of `M ⊗_A 𝔮 → M` (i.e. `Tor₁^A(M, A/𝔮)`). -/
theorem exists_torsion_data [IsNoetherianRing A] [Algebra.FiniteType A B] [Module.Finite B M]
    (p : Ideal B) [p.IsPrime] (hp : Module.Flat A (LocalizedModule p.primeCompl M)) :
    ∃ g ∉ p, (∀ J : Ideal (A ⧸ p.comap (algebraMap A B)), ∀ x : M ⊗[A] J,
        (J.subtype.restrictScalars A).lTensor M x = 0 → ∃ n : ℕ, g ^ n • x = 0) ∧
      ∀ x : M ⊗[A] p.comap (algebraMap A B),
        (p.comap (algebraMap A B)).subtype.lTensor M x = 0 → ∃ n : ℕ, g ^ n • x = 0 := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  set q := p.comap (algebraMap A B)
  obtain ⟨f, hfq, hf⟩ := exists_forall_lTensor_torsion (B := B) (M := M) q
  obtain ⟨g', hg', hg'x⟩ := exists_smul_eq_zero_of_flat p hp q
  refine ⟨algebraMap A B f * g', fun h ↦ (Ideal.IsPrime.mem_or_mem ‹_› h).elim hfq hg',
    fun J x hx ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨n, hn⟩ := hf J x hx
    exact ⟨n, by rw [mul_pow, mul_comm, mul_smul, ← map_pow, algebraMap_smul, hn, smul_zero]⟩
  · exact ⟨1, by rw [pow_one, mul_smul, hg'x x hx, smul_zero]⟩

end FlatLocus

section Main

variable {A : Type u} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
  {M : Type v} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- Flatness of `(A/𝔮) ⊗ M_T` over `A/𝔮` and vanishing of `Tor₁^A(M_T, A/𝔮)` from the torsion
data of `exists_torsion_data`, for any localization `M_T` at a multiplicative set containing
`g`. -/
private lemma flat_and_torOneVanishes_of_torsion (q : Ideal A) (T : Submonoid B) (g : B)
    (hgT : g ∈ T)
    (ha : ∀ J : Ideal (A ⧸ q), ∀ x : M ⊗[A] J,
      (J.subtype.restrictScalars A).lTensor M x = 0 → ∃ n : ℕ, g ^ n • x = 0)
    (hb : ∀ x : M ⊗[A] q, q.subtype.lTensor M x = 0 → ∃ n : ℕ, g ^ n • x = 0) :
    Module.Flat (A ⧸ q) ((A ⧸ q) ⊗[A] LocalizedModule T M) ∧
      TorOneVanishes A (LocalizedModule T M) (A ⧸ q) := by
  refine ⟨flat_baseChange_of_rTensor_injective fun J ↦ ?_, ?_⟩
  · rw [← LinearMap.lTensor_inj_iff_rTensor_inj, lTensor_localizedModule_injective_iff]
    intro x hx
    obtain ⟨n, hn⟩ := ha J x hx
    exact ⟨g ^ n, pow_mem hgT n, hn⟩
  · rw [torOneVanishes_quotient_iff, lTensor_localizedModule_injective_iff]
    intro x hx
    obtain ⟨n, hn⟩ := hb x hx
    exact ⟨g ^ n, pow_mem hgT n, hn⟩

/-- IV.6.8: let `A` be noetherian, `B` a finitely generated `A`-algebra, `M` a finite `B`-module,
`𝔭` a prime of `B` inducing `𝔮` on `A`, with `M_𝔭` flat over `A`. There is `g ∉ 𝔭` such that
(a) `(M/𝔮M)_g = A/𝔮 ⊗_A M_g` is flat over `A/𝔮` and (b) `Tor₁^A(M, A/𝔮)_g = Tor₁^A(M_g, A/𝔮)`
vanishes. -/
theorem exists_flat_quotient_and_torOneVanishes [IsNoetherianRing A] [Algebra.FiniteType A B]
    [Module.Finite B M] (p : Ideal B) [p.IsPrime]
    (hp : Module.Flat A (LocalizedModule p.primeCompl M)) :
    ∃ g ∉ p, Module.Flat (A ⧸ p.comap (algebraMap A B))
        ((A ⧸ p.comap (algebraMap A B)) ⊗[A] LocalizedModule (Submonoid.powers g) M) ∧
      TorOneVanishes A (LocalizedModule (Submonoid.powers g) M) (A ⧸ p.comap (algebraMap A B)) := by
  obtain ⟨g, hg, ha, hb⟩ := exists_torsion_data p hp
  exact ⟨g, hg, flat_and_torOneVanishes_of_torsion _ _ g (Submonoid.mem_powers g) ha hb⟩

/-- IV.6.9, in terms of the torsion data of `exists_torsion_data`. -/
theorem flat_localizedModule_of_torsion_data [IsNoetherianRing A] [Algebra.FiniteType A B]
    [Module.Finite B M] (p : Ideal B) [p.IsPrime] (g : B)
    (ha : ∀ J : Ideal (A ⧸ p.comap (algebraMap A B)), ∀ x : M ⊗[A] J,
      (J.subtype.restrictScalars A).lTensor M x = 0 → ∃ n : ℕ, g ^ n • x = 0)
    (hb : ∀ x : M ⊗[A] p.comap (algebraMap A B),
      (p.comap (algebraMap A B)).subtype.lTensor M x = 0 → ∃ n : ℕ, g ^ n • x = 0)
    (p' : Ideal B) [p'.IsPrime] (hpp' : p ≤ p') (hg : g ∉ p') :
    Module.Flat A (LocalizedModule p'.primeCompl M) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  set q := p.comap (algebraMap A B)
  obtain ⟨hF, hT⟩ := flat_and_torOneVanishes_of_torsion q p'.primeCompl g hg ha hb
  -- apply the local criterion IV.5.6 to `A → B_𝔭'` and the ideal `𝔮`
  have hI : q.map (algebraMap A (Localization.AtPrime p')) ≤ Ideal.jacobson ⊥ := by
    refine le_trans ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply A B,
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ p']
    exact hpp' ha
  have htf := flat_tfae (B := Localization.AtPrime p') (LocalizedModule p'.primeCompl M) q hI
  have := htf.out 1 2
  exact this.2 ⟨hF, hT⟩

/-- IV.6.9: let `g ∉ 𝔭` be as in IV.6.8, i.e. `(M/𝔮M)_g` is flat over `A/𝔮` and
`Tor₁^A(M, A/𝔮)_g = 0`. Then `M_𝔭'` is flat over `A` for every prime `𝔭' ⊇ 𝔭` not containing
`g`. -/
theorem flat_localizedModule_of_flat_quotient [IsNoetherianRing A] [Algebra.FiniteType A B]
    [Module.Finite B M] (p : Ideal B) [p.IsPrime] (g : B)
    (ha : Module.Flat (A ⧸ p.comap (algebraMap A B))
      ((A ⧸ p.comap (algebraMap A B)) ⊗[A] LocalizedModule (Submonoid.powers g) M))
    (hb : TorOneVanishes A (LocalizedModule (Submonoid.powers g) M)
      (A ⧸ p.comap (algebraMap A B)))
    (p' : Ideal B) [p'.IsPrime] (hpp' : p ≤ p') (hg : g ∉ p') :
    Module.Flat A (LocalizedModule p'.primeCompl M) := by
  refine flat_localizedModule_of_torsion_data p g (fun J x hx ↦ ?_) (fun x hx ↦ ?_) p' hpp' hg
  · have hJ := rTensor_injective_of_flat_baseChange (A := A)
      (S := A ⧸ p.comap (algebraMap A B)) (M := LocalizedModule (Submonoid.powers g) M)
      J.subtype Subtype.val_injective
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj, lTensor_localizedModule_injective_iff] at hJ
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hJ x hx
    exact ⟨n, hn⟩
  · rw [torOneVanishes_quotient_iff, lTensor_localizedModule_injective_iff] at hb
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hb x hx
    exact ⟨n, hn⟩

/-- IV.6.10 (affine case): let `A` be noetherian, `B` a finitely generated `A`-algebra and `M` a
finite `B`-module. The set of primes `𝔭` of `B` such that `M_𝔭` is flat over `A` is open in
`Spec B`. -/
theorem isOpen_flatLocus [IsNoetherianRing A] [Algebra.FiniteType A B] [Module.Finite B M] :
    IsOpen {P : PrimeSpectrum B | Module.Flat A (LocalizedModule P.asIdeal.primeCompl M)} := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  rw [isOpen_iff_of_noetherianSpace]
  refine ⟨fun P P' hP'P hP ↦ ?_, fun P hP ↦ ?_⟩
  · -- stable under generization
    rw [Set.mem_ofPred_eq, flat_localizedModule_iff] at hP ⊢
    intro I x hx
    obtain ⟨t, ht, htx⟩ := hP I x hx
    exact ⟨t, fun h ↦ ht ((PrimeSpectrum.le_iff_specializes P' P).2 hP'P h), htx⟩
  · -- a basic open neighbourhood from IV.6.8 and IV.6.9
    obtain ⟨g, hg, ha, hb⟩ := exists_torsion_data P.asIdeal hP
    refine ⟨PrimeSpectrum.basicOpen g, (PrimeSpectrum.basicOpen g).isOpen,
      ⟨P, hg, subset_closure rfl⟩, fun P' ⟨hP'g, hP'⟩ ↦ ?_⟩
    exact flat_localizedModule_of_torsion_data P.asIdeal g ha hb P'.asIdeal
      ((PrimeSpectrum.le_iff_mem_closure P P').2 hP') hP'g

/-- IV.6.11 (affine case): if moreover `A` is an integral domain, there is `f ≠ 0` in `A` such
that `M_𝔭` is flat over `A` for every prime `𝔭` of `B` not containing `f`; i.e. `M` is flat over
`Spec A` at every point above the nonempty open set `D(f)`. -/
theorem exists_forall_flat_localizedModule [IsDomain A] [IsNoetherianRing A]
    [Algebra.FiniteType A B] [Module.Finite B M] :
    ∃ f : A, f ≠ 0 ∧ ∀ P : PrimeSpectrum B, algebraMap A B f ∉ P.asIdeal →
      Module.Flat A (LocalizedModule P.asIdeal.primeCompl M) := by
  obtain ⟨f, hf, hfree⟩ := exists_isFreeAway_of_finiteType (A := A) (B := B) M
  refine ⟨f, hf, fun P hP ↦ ?_⟩
  rw [flat_localizedModule_iff]
  intro I x hx
  -- the kernel of `I ⊗ M → M` is killed by a power of `f`
  have key (x' : M ⊗[A] I) : (I.subtype.rTensor M) (TensorProduct.comm A M I x') =
      TensorProduct.comm A M A (I.subtype.lTensor M x') := by
    induction x' using TensorProduct.induction_on with
    | zero => simp
    | tmul m i => simp
    | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  obtain ⟨n, hn⟩ := hfree.exists_pow_smul_eq_zero I (TensorProduct.comm A M I x)
    (by rw [key, hx, map_zero])
  refine ⟨algebraMap A B f ^ n, fun h ↦ hP (P.2.mem_of_pow_mem n h), ?_⟩
  rw [← map_pow, algebraMap_smul]
  apply (TensorProduct.comm A M I).injective
  rw [map_smul, hn, map_zero]

/-- IV.6.11, with the open set: there is a nonempty open `V ⊆ Spec A` such that `M` is flat over
`A` at every point of `Spec B` above `V`. -/
theorem exists_isOpen_forall_flat_localizedModule [IsDomain A] [IsNoetherianRing A]
    [Algebra.FiniteType A B] [Module.Finite B M] :
    ∃ V : Set (PrimeSpectrum A), IsOpen V ∧ V.Nonempty ∧ ∀ P : PrimeSpectrum B,
      PrimeSpectrum.comap (algebraMap A B) P ∈ V →
        Module.Flat A (LocalizedModule P.asIdeal.primeCompl M) := by
  obtain ⟨f, hf, h⟩ := exists_forall_flat_localizedModule (A := A) (B := B) (M := M)
  refine ⟨PrimeSpectrum.basicOpen f, (PrimeSpectrum.basicOpen f).isOpen,
    ⟨⟨⊥, Ideal.isPrime_bot⟩, by simpa using hf⟩, fun P hP ↦ h P hP⟩

end Main

end SGA.SGA1.ExposeIV
