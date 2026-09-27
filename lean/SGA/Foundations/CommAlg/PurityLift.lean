/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Localization.Finiteness
import SGA.Foundations.CommAlg.PairSections
import SGA.Foundations.Formal.AdicRing

/-!
# Lifting maps into thickenings of depth-two algebras

Tools for the inductive proof of the purity theorem of Zariski–Nagata
(`SGA.Foundations.CommAlg.PurityInduction`):

* `IsAdicComplete.of_le`: a noetherian ring complete for `J` is complete for every `I ≤ J`
  (Matsumura, *Commutative ring theory*, Thm. 8.7 and Ex. 8.2).
* `Algebra.exists_algHom_comp_eq_of_isWeaklyRegular`: let `x, y` be a regular sequence on an
  `A`-algebra `T` and `T → T'` a surjection with nilpotent kernel. If `B` is an `A`-algebra such
  that `B_x` and `B_y` are formally étale over `A`, every `A`-algebra map `B → T'` lifts to `T`
  (lift on `D(x)` and `D(y)` by formal smoothness, glue by formal unramifiedness and Hartogs).
  The lift is unique (`Algebra.algHom_ext_of_isSMulRegular`).
* `exists_pow_smul_mem_range_of_isWeaklyRegular_away`: an elementary Hartogs lemma for cokernels.
* `exists_notMem_forall_smul_eq_zero_of_pow_smul_eq`: Nakayama's lemma at a prime, in elements.
-/

open RingTheory.Sequence IsLocalRing

universe u v

section AdicComplete

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

/-- A noetherian ring which is `J`-adically complete is `I`-adically complete for every ideal
`I ≤ J` (Matsumura, *Commutative ring theory*, Thm. 8.7). -/
theorem IsAdicComplete.of_le {I J : Ideal A} (hIJ : I ≤ J) [hJ : IsAdicComplete J A] :
    IsAdicComplete I A := by
  have hH : IsHausdorff I A := IsHausdorff.of_pow_le (k := 1) (J := J) (by simpa using hIJ)
  refine { toIsHausdorff := hH, toIsPrecomplete := ⟨fun {f} hf ↦ ?_⟩ }
  have hfJ : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (J ^ m • ⊤ : Submodule A A)] :=
    fun hmn ↦ (hf hmn).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hIJ _))
  obtain ⟨L, hL⟩ := hJ.toIsPrecomplete.prec hfJ
  refine ⟨L, fun n ↦ ?_⟩
  let N : Submodule A A := I ^ n • ⊤
  have hc : IsAdicComplete J (A ⧸ N) := IsAdicComplete.of_finite J _
  -- the image of `J ^ m` in `A ⧸ N` lies in `J ^ m • ⊤`
  have himg : ∀ m : ℕ, ∀ z ∈ (J ^ m • ⊤ : Submodule A A),
      N.mkQ z ∈ (J ^ m • ⊤ : Submodule A (A ⧸ N)) := by
    intro m z hz
    refine Submodule.smul_induction_on hz (fun r hr w _ ↦ ?_) (fun a b ha hb ↦ ?_)
    · rw [map_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · rw [map_add]
      exact add_mem ha hb
  have hzero : N.mkQ (f n - L) = 0 := by
    refine hc.toIsHausdorff.haus _ fun m ↦ ?_
    rw [SModEq.zero]
    have h1 : f n - f (max n m) ∈ N := by
      have := hf (le_max_left n m)
      rwa [SModEq, Submodule.Quotient.eq] at this
    have h2 : f (max n m) - L ∈ (J ^ m • ⊤ : Submodule A A) := by
      have := (hL (max n m)).mono
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right n m)))
      rwa [SModEq, Submodule.Quotient.eq] at this
    have : f n - L = (f n - f (max n m)) + (f (max n m) - L) := by ring
    have e1 : N.mkQ (f n - f (max n m)) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr h1
    rw [this, map_add, e1, zero_add]
    exact himg m _ h2
  rw [SModEq, Submodule.Quotient.eq]
  exact (Submodule.Quotient.mk_eq_zero N).mp hzero

end AdicComplete

section Regular

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

/-- If `S_h` is flat over `A` and `rs` is regular on `A_h`, then `rs` is regular on `S_h`. -/
theorem isWeaklyRegular_away_of_flat (h : A) [Module.Flat A (Localization.Away (algebraMap A S h))]
    {rs : List A}
    (hreg : IsWeaklyRegular (Localization.Away h) (rs.map (algebraMap A (Localization.Away h)))) :
    IsWeaklyRegular (Localization.Away (algebraMap A S h))
      (rs.map (algebraMap A (Localization.Away (algebraMap A S h)))) := by
  let Ah := Localization.Away h
  let Sh := Localization.Away (algebraMap A S h)
  let _ : Algebra Ah Sh := (Localization.awayMap (algebraMap A S) h).toAlgebra
  have : IsScalarTower A Ah Sh := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_comp, IsScalarTower.algebraMap_eq A S Sh])
  have : Module.Flat Ah Sh :=
    (Module.flat_iff_of_isLocalization Ah (Submonoid.powers h) Sh).mpr inferInstance
  have e : rs.map (algebraMap A Sh) = (rs.map (algebraMap A Ah)).map (algebraMap Ah Sh) := by
    rw [List.map_map]
    congr 1
    funext r
    exact IsScalarTower.algebraMap_apply A Ah Sh r
  rw [e]
  exact hreg.of_flat

end Regular

section Localization

variable {T : Type*} [CommRing T]

/-- If `z` lies in `J T_a`, then `a ^ n z ∈ J` for some `n`. -/
theorem exists_pow_mul_mem_of_algebraMap_mem_map (a : T) (J : Ideal T) {z : T}
    (hz : algebraMap T (Localization.Away a) z ∈ J.map (algebraMap T (Localization.Away a))) :
    ∃ n : ℕ, a ^ n * z ∈ J := by
  obtain ⟨⟨⟨j, hj⟩, ⟨_, m, rfl⟩⟩, h⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers a) _).mp hz
  rw [← map_mul] at h
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers a) h
  refine ⟨k + m, ?_⟩
  have : a ^ (k + m) * z = a ^ k * (z * a ^ m) := by ring
  rw [this, hk]
  exact J.mul_mem_left _ hj

/-- A nilpotent ideal stays nilpotent after extension. -/
theorem Ideal.IsNilpotent.map {T S : Type*} [CommRing T] [CommRing S] (g : T →+* S) {J : Ideal T}
    (hJ : IsNilpotent J) : IsNilpotent (J.map g) := by
  obtain ⟨n, hn⟩ := hJ
  exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]; rfl⟩

end Localization

namespace Algebra

variable {A B T T' : Type*} [CommRing A] [CommRing B] [CommRing T] [CommRing T']
  [Algebra A B] [Algebra A T] [Algebra A T']

/-- Two `A`-algebra maps `B → P` agreeing modulo a nilpotent ideal are equal, if `B_x` is formally
unramified over `A` and `x` is a unit in `P`. -/
theorem algHom_ext_of_away_of_isUnit {x : A}
    [FormallyUnramified A (Localization.Away (algebraMap A B x))]
    {P : Type*} [CommRing P] [Algebra A P] (hP : IsUnit (algebraMap A P x))
    (K : Ideal P) (hK : IsNilpotent K) {u v : B →ₐ[A] P} (h : ∀ b, u b - v b ∈ K) : u = v := by
  let M := Submonoid.powers (algebraMap A B x)
  let Bx := Localization.Away (algebraMap A B x)
  have hunit : ∀ w : B →ₐ[A] P, ∀ s : M, IsUnit (w s) := by
    rintro w ⟨_, n, rfl⟩
    rw [map_pow, AlgHom.commutes]
    exact hP.pow n
  let u' : Bx →ₐ[A] P := IsLocalization.liftAlgHom (hunit u)
  let v' : Bx →ₐ[A] P := IsLocalization.liftAlgHom (hunit v)
  have hu' : ∀ b, u' (algebraMap B Bx b) = u b := fun b ↦ IsLocalization.lift_eq _ b
  have hv' : ∀ b, v' (algebraMap B Bx b) = v b := fun b ↦ IsLocalization.lift_eq _ b
  have huv : u' = v' := by
    have hext : (Ideal.Quotient.mk K).comp u'.toRingHom =
        (Ideal.Quotient.mk K).comp v'.toRingHom := by
      apply IsLocalization.ringHom_ext M
      ext b
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hu', hv']
      exact Ideal.Quotient.eq.mpr (h b)
    exact FormallyUnramified.ext K hK fun z ↦ congr($hext z)
  ext b
  rw [← hu', ← hv', huv]

/-- Uniqueness of lifts: two `A`-algebra maps `B → T` which agree modulo a nilpotent ideal are
equal, if `B_x` is formally unramified over `A` and `x` is a nonzerodivisor on `T`. -/
theorem algHom_ext_of_isSMulRegular {x : A}
    [FormallyUnramified A (Localization.Away (algebraMap A B x))]
    (hT : IsSMulRegular T (algebraMap A T x)) (J : Ideal T) (hJ : IsNilpotent J)
    {φ φ' : B →ₐ[A] T} (h : ∀ b, φ b - φ' b ∈ J) : φ = φ' := by
  let a := algebraMap A T x
  let Tx := Localization.Away a
  let ι : T →ₐ[A] Tx := IsScalarTower.toAlgHom A T Tx
  have hP : IsUnit (algebraMap A Tx x) := by
    rw [IsScalarTower.algebraMap_apply A T Tx]
    exact IsLocalization.Away.algebraMap_isUnit a
  have := algHom_ext_of_away_of_isUnit (B := B) hP (J.map (algebraMap T Tx))
    (Ideal.IsNilpotent.map _ hJ) (u := ι.comp φ) (v := ι.comp φ') fun b ↦ by
      simp only [AlgHom.comp_apply, ι, IsScalarTower.coe_toAlgHom', ← map_sub]
      exact Ideal.mem_map_of_mem _ (h b)
  ext b
  have hb := congr($this b)
  simp only [AlgHom.comp_apply, ι, IsScalarTower.coe_toAlgHom'] at hb
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers a) hb
  exact (hT.pow n) hn

/-- Lifting on one chart: if `B_x` is formally smooth over `A`, and `π : T → T'` is surjective with
nilpotent kernel `J`, every `ρ : B → T'` lifts to `χ : B → T_x` modulo `J T_x`. -/
theorem exists_algHom_away_sub_mem {x : A}
    [FormallySmooth A (Localization.Away (algebraMap A B x))]
    (π : T →ₐ[A] T') (hπ : Function.Surjective π) (hnil : IsNilpotent (RingHom.ker π))
    (ρ : B →ₐ[A] T') :
    ∃ χ : B →ₐ[A] Localization.Away (algebraMap A T x), ∀ b t, π t = ρ b →
      χ b - algebraMap T _ t ∈ (RingHom.ker π).map (algebraMap T (Localization.Away
        (algebraMap A T x))) := by
  let a := algebraMap A T x
  let Tx := Localization.Away a
  let J := RingHom.ker π
  let Jx := J.map (algebraMap T Tx)
  let Bx := Localization.Away (algebraMap A B x)
  let ρ' : B →ₐ[A] T ⧸ J := (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom.comp ρ
  let σ : T ⧸ J →ₐ[A] Tx ⧸ Jx :=
    Ideal.quotientMapₐ Jx (IsScalarTower.toAlgHom A T Tx) Ideal.le_comap_map
  have hunit : ∀ s : Submonoid.powers (algebraMap A B x), IsUnit ((σ.comp ρ') s) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow, AlgHom.commutes, IsScalarTower.algebraMap_apply A Tx (Tx ⧸ Jx),
      IsScalarTower.algebraMap_apply A T Tx]
    exact ((IsLocalization.Away.algebraMap_isUnit a).map _).pow n
  let g : Bx →ₐ[A] Tx ⧸ Jx := IsLocalization.liftAlgHom hunit
  let χ' : Bx →ₐ[A] Tx := FormallySmooth.lift Jx (Ideal.IsNilpotent.map _ hnil) g
  refine ⟨χ'.comp (IsScalarTower.toAlgHom A B Bx), fun b t ht ↦ ?_⟩
  have hρ' : ρ' b = Ideal.Quotient.mk J t := by
    change (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (ρ b) = _
    rw [← ht, Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
  rw [← Ideal.Quotient.eq]
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  rw [FormallySmooth.mk_lift]
  change IsLocalization.lift hunit (algebraMap B Bx b) = _
  rw [IsLocalization.lift_eq]
  change σ (ρ' b) = _
  rw [hρ']
  rfl

/-- Lifting along a nilpotent thickening of a depth-two algebra. Let `x, y` be a regular sequence on
the `A`-algebra `T`, and `π : T → T'` a surjection with nilpotent kernel, `x` a nonzerodivisor on
`T'`. If `B_x` and `B_y` are formally étale over `A`, every `A`-algebra map `ρ : B → T'` lifts to
`T`. -/
theorem exists_algHom_comp_eq_of_isWeaklyRegular {x y : A}
    [FormallyEtale A (Localization.Away (algebraMap A B x))]
    [FormallyEtale A (Localization.Away (algebraMap A B y))]
    (hT : IsWeaklyRegular T ([algebraMap A T x, algebraMap A T y] : List T))
    (π : T →ₐ[A] T') (hπ : Function.Surjective π) (hnil : IsNilpotent (RingHom.ker π))
    (hT' : IsSMulRegular T' (algebraMap A T' x)) (ρ : B →ₐ[A] T') :
    ∃ φ : B →ₐ[A] T, π.comp φ = ρ := by
  classical
  let a := algebraMap A T x
  let b := algebraMap A T y
  let J := RingHom.ker π
  let Tx := Localization.Away a
  let Ty := Localization.Away b
  let Txy := Localization.Away (a * b)
  obtain ⟨χx, hχx⟩ := exists_algHom_away_sub_mem (x := x) π hπ hnil ρ
  obtain ⟨χy, hχy⟩ := exists_algHom_away_sub_mem (x := y) π hπ hnil ρ
  -- the two local lifts agree on `D(xy)`
  let rx : Tx →ₐ[A] Txy := (Localization.awayToMulRight a b).restrictScalars A
  let ry : Ty →ₐ[A] Txy := (Localization.awayToMulLeft a b).restrictScalars A
  have hrx : ∀ t : T, rx (algebraMap T Tx t) = algebraMap T Txy t :=
    Localization.awayToMulRight_algebraMap a b
  have hry : ∀ t : T, ry (algebraMap T Ty t) = algebraMap T Txy t :=
    Localization.awayToMulLeft_algebraMap a b
  have hmap : ∀ {S : Type _} [CommRing S] [Algebra T S] (r : S →+* Txy),
      (∀ t, r (algebraMap T S t) = algebraMap T Txy t) → ∀ z ∈ J.map (algebraMap T S),
      r z ∈ J.map (algebraMap T Txy) := by
    intro S _ _ r hr z hz
    have : (J.map (algebraMap T S)).map r = J.map (algebraMap T Txy) := by
      rw [Ideal.map_map]
      congr 1
      exact RingHom.ext hr
    exact this ▸ Ideal.mem_map_of_mem r hz
  have hxy : ∀ β : B, rx (χx β) = ry (χy β) := by
    have hunit : IsUnit (algebraMap A Txy x) := by
      rw [IsScalarTower.algebraMap_apply A T Txy]
      have hab : IsUnit (algebraMap T Txy (a * b)) := IsLocalization.Away.algebraMap_isUnit (a * b)
      rw [map_mul] at hab
      exact isUnit_of_mul_isUnit_left hab
    have := algHom_ext_of_away_of_isUnit (B := B) (x := x) hunit (J.map (algebraMap T Txy))
      (Ideal.IsNilpotent.map _ hnil) (u := rx.comp χx) (v := ry.comp χy) fun β ↦ by
        obtain ⟨t, ht⟩ := hπ (ρ β)
        have h1 := hmap rx.toRingHom hrx _ (hχx β t ht)
        have h2 := hmap ry.toRingHom hry _ (hχy β t ht)
        rw [map_sub] at h1 h2
        change rx (χx β) - rx (algebraMap T Tx t) ∈ _ at h1
        change ry (χy β) - ry (algebraMap T Ty t) ∈ _ at h2
        rw [hrx] at h1
        rw [hry] at h2
        simp only [AlgHom.comp_apply]
        have := sub_mem h1 h2
        rwa [sub_sub_sub_cancel_right] at this
    exact fun β ↦ congr($this β)
  -- glue using Hartogs on `T`
  have hbij := Localization.bijective_algebraMap_pairSections a b hT
  let E : T ≃ₐ[T] Localization.pairSections a b :=
    AlgEquiv.ofBijective (Algebra.ofId T _) hbij
  have hmem : ∀ β : B, (χx β, χy β) ∈ Localization.pairSections a b := fun β ↦
    (Localization.mem_pairSections a b).mpr (hxy β)
  let ψ : B →+* Localization.pairSections a b :=
    { toFun β := ⟨(χx β, χy β), hmem β⟩
      map_one' := by ext <;> simp
      map_mul' _ _ := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' _ _ := by ext <;> simp }
  let φ₀ : B →+* T := E.symm.toRingHom.comp ψ
  have hEφ : ∀ β, E (φ₀ β) = ψ β := fun β ↦ E.apply_symm_apply _
  have hE : ∀ t : T, E t = algebraMap T (Localization.pairSections a b) t := fun t ↦ rfl
  have hφx : ∀ β, algebraMap T Tx (φ₀ β) = χx β := by
    intro β
    have h := congr_arg (fun p : Localization.pairSections a b ↦ (p : Tx × Ty).1) (hEφ β)
    simp only [hE, Localization.algebraMap_pairSections_fst] at h
    exact h
  have hcomm : ∀ r : A, φ₀ (algebraMap A B r) = algebraMap A T r := by
    intro r
    apply E.injective
    rw [hEφ, hE]
    apply Subtype.ext
    ext
    · rw [Localization.algebraMap_pairSections_fst, ← IsScalarTower.algebraMap_apply]
      exact χx.commutes r
    · rw [Localization.algebraMap_pairSections_snd, ← IsScalarTower.algebraMap_apply]
      exact χy.commutes r
  let φ : B →ₐ[A] T := { φ₀ with commutes' := hcomm }
  refine ⟨φ, AlgHom.ext fun β ↦ ?_⟩
  obtain ⟨t, ht⟩ := hπ (ρ β)
  have h1 : algebraMap T Tx (φ₀ β - t) ∈ J.map (algebraMap T Tx) := by
    rw [map_sub, hφx]
    exact hχx β t ht
  obtain ⟨n, hn⟩ := exists_pow_mul_mem_of_algebraMap_mem_map a J h1
  have h2 : algebraMap A T' x ^ n * (π (φ₀ β) - π t) = algebraMap A T' x ^ n * 0 := by
    have := (RingHom.mem_ker (f := π)).mp hn
    rw [map_mul, map_pow, AlgHom.commutes, map_sub] at this
    rw [mul_zero, this]
  have := (hT'.pow n) h2
  rw [sub_eq_zero] at this
  simp only [AlgHom.comp_apply]
  exact this.trans ht

end Algebra

section Hartogs

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-- An elementary Hartogs lemma for the cokernel of an injective map. Let `φ : B → C` be injective,
`x, y` a regular sequence on `B_h` and `x` a nonzerodivisor on `C_h`. If `x c` and `y c` lie in the
image of `φ`, then so does `h ^ k c` for some `k`. -/
theorem exists_pow_smul_mem_range_of_isWeaklyRegular_away (φ : B →ₐ[A] C)
    (hφ : Function.Injective φ) {h x y : A}
    (hB : IsWeaklyRegular (Localization.Away (algebraMap A B h))
      [algebraMap A (Localization.Away (algebraMap A B h)) x,
        algebraMap A (Localization.Away (algebraMap A B h)) y])
    (hC : IsSMulRegular (Localization.Away (algebraMap A C h))
      (algebraMap A (Localization.Away (algebraMap A C h)) x))
    {c : C} (hx : x • c ∈ φ.range) (hy : y • c ∈ φ.range) : ∃ k : ℕ, h ^ k • c ∈ φ.range := by
  obtain ⟨b₁, hb₁⟩ := hx
  obtain ⟨b₂, hb₂⟩ := hy
  replace hb₁ : φ b₁ = x • c := hb₁
  replace hb₂ : φ b₂ = y • c := hb₂
  let Bh := Localization.Away (algebraMap A B h)
  let Ch := Localization.Away (algebraMap A C h)
  have hyx : y • b₁ = x • b₂ := hφ (by rw [map_smul, map_smul, hb₁, hb₂, smul_comm])
  -- `b₁ ∈ x B_h`
  obtain ⟨-, hdiv⟩ := (isWeaklyRegular_pair_iff _ _).mp hB
  obtain ⟨β, hβ⟩ := hdiv (algebraMap B Bh b₁) ⟨algebraMap B Bh b₂, by
    rw [IsScalarTower.algebraMap_apply A B Bh y, IsScalarTower.algebraMap_apply A B Bh x,
      ← map_mul, ← map_mul, ← Algebra.smul_def, ← Algebra.smul_def, hyx]⟩
  obtain ⟨⟨b, s⟩, hk⟩ := IsLocalization.surj (Submonoid.powers (algebraMap A B h)) β
  obtain ⟨k, hs⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  have h1 : algebraMap B Bh (h ^ k • b₁) = algebraMap B Bh (x • b) := by
    have hs' : algebraMap B Bh (s : B) = algebraMap A Bh h ^ k := by
      rw [← hs, map_pow, ← IsScalarTower.algebraMap_apply]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, hβ]
    change _ = _ * algebraMap B Bh (b, s).1
    rw [← hk]
    change _ = _ * (β * algebraMap B Bh (s : B))
    rw [hs']
    simp only [map_pow, ← IsScalarTower.algebraMap_apply]
    ring
  obtain ⟨c₁, hc₁⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap A B h)) h1
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp c₁.2
  rw [← hj, ← map_pow, ← Algebra.smul_def, ← Algebra.smul_def] at hc₁
  -- `x (h ^ (j + k) c - φ (h ^ j b)) = 0`
  have e1 : x • (h ^ (j + k) • c) = h ^ j • h ^ k • φ b₁ := by
    rw [hb₁, pow_add, mul_smul, smul_comm x, smul_comm x]
  have e2 : h ^ j • h ^ k • φ b₁ = x • φ (h ^ j • b) := by
    rw [← map_smul, ← map_smul, hc₁]
    simp only [map_smul]
    exact smul_comm _ _ _
  have h2 : x • (h ^ (j + k) • c - φ (h ^ j • b)) = 0 := by
    rw [smul_sub, e1, e2, sub_self]
  have h3 : algebraMap C Ch (h ^ (j + k) • c - φ (h ^ j • b)) = 0 := by
    apply hC
    change algebraMap A Ch x * _ = algebraMap A Ch x * 0
    rw [mul_zero, IsScalarTower.algebraMap_apply A C Ch, ← map_mul, ← Algebra.smul_def, h2,
      map_zero]
  rw [← map_zero (algebraMap C Ch)] at h3
  obtain ⟨c₂, hc₂⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap A C h)) h3
  obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp c₂.2
  rw [← hi, mul_zero, ← map_pow, ← Algebra.smul_def, smul_sub, sub_eq_zero, ← map_smul,
    ← mul_smul, ← pow_add] at hc₂
  exact ⟨i + (j + k), ⟨_, hc₂.symm⟩⟩

/-- Hartogs for the cokernel of an injective map: if `x, y` is a regular sequence on `B`, `x` a
nonzerodivisor on `C` and `x c, y c ∈ φ(B)`, then `c ∈ φ(B)`. -/
theorem mem_range_of_isWeaklyRegular (φ : B →ₐ[A] C) (hφ : Function.Injective φ) {x y : A}
    (hB : IsWeaklyRegular B [x, y]) (hC : IsSMulRegular C x) {c : C} (hx : x • c ∈ φ.range)
    (hy : y • c ∈ φ.range) : c ∈ φ.range := by
  obtain ⟨b₁, hb₁⟩ := hx
  obtain ⟨b₂, hb₂⟩ := hy
  replace hb₁ : φ b₁ = x • c := hb₁
  replace hb₂ : φ b₂ = y • c := hb₂
  have hyx : y • b₁ = x • b₂ := hφ (by rw [map_smul, map_smul, hb₁, hb₂, smul_comm])
  have hB' : IsWeaklyRegular B [algebraMap A B x, algebraMap A B y] :=
    (isWeaklyRegular_map_algebraMap_iff B B [x, y]).mpr hB
  obtain ⟨-, hdiv⟩ := (isWeaklyRegular_pair_iff _ _).mp hB'
  obtain ⟨b, hb⟩ := hdiv b₁ ⟨b₂, by rw [← Algebra.smul_def, ← Algebra.smul_def, hyx]⟩
  refine ⟨b, hC ?_⟩
  change x • φ b = x • c
  rw [← hb₁, ← map_smul, Algebra.smul_def, hb]

end Hartogs

section Nakayama

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- Nakayama's lemma at a prime `q`, in elements: if `f ∈ q`, `g ∉ q` and every element of the
finite module `M` becomes divisible by `f` after multiplication by a power of `g`, then a single
element outside `q` kills `M`. -/
theorem exists_notMem_forall_smul_eq_zero_of_pow_smul_eq (q : Ideal A) [q.IsPrime] {f g : A}
    (hf : f ∈ q) (hg : g ∉ q) (h : ∀ m : M, ∃ (j : ℕ) (m' : M), g ^ j • m = f • m') :
    ∃ s ∉ q, ∀ m : M, s • m = 0 := by
  let S := q.primeCompl
  let Aq := Localization S
  let Mq := LocalizedModule S M
  have hle : (⊤ : Submodule Aq Mq) ≤ Ideal.span {algebraMap A Aq f} • ⊤ := by
    intro z _
    induction z using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨j, m', hm'⟩ := h m
      have hgs : g ^ j * s ∈ S := S.mul_mem (S.pow_mem hg j) s.2
      have : LocalizedModule.mk m s = algebraMap A Aq f • LocalizedModule.mk m' ⟨_, hgs⟩ := by
        rw [algebraMap_smul, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        rw [one_smul, one_smul, Submonoid.mk_smul, Submonoid.smul_def, ← hm', mul_comm, mul_smul]
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  have hjac : Ideal.span {algebraMap A Aq f} ≤ (⊥ : Ideal Aq).jacobson := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have : IsLocalRing Aq := IsLocalization.AtPrime.isLocalRing Aq q
    exact IsLocalRing.maximalIdeal_le_jacobson _
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff Aq q f).mpr hf)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ ⊤
    (Module.Finite.fg_top) hle hjac
  have hsub : Subsingleton Mq := subsingleton_of_forall_eq 0 fun z ↦ by
    simpa [hbot] using (Submodule.mem_top : z ∈ (⊤ : Submodule Aq Mq))
  exact exists_notMem_forall_smul_eq_zero q fun m ↦ by
    obtain ⟨r, hr, hrm⟩ := LocalizedModule.subsingleton_iff.mp hsub m
    exact ⟨r, hr, hrm⟩

end Nakayama
