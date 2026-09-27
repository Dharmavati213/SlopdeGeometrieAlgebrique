/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Support
import SGA.SGA1.ExposeIV.FlatModules

/-!
# SGA 1, Exposé IV, §2: faithfully flat modules

Faithful flatness is mathlib's `Module.FaithfullyFlat`, defined by condition (i ter) of IV.2.1;
the other characterizations of IV.2.1 and the transitivity properties are in mathlib. We prove
IV.2.2 (over a local homomorphism, a finite module is faithfully flat iff it is flat and
nonzero), IV.2.3 (a module faithfully flat over `A` forces `Spec B → Spec A` to be surjective),
the resulting going-down property for a finite flat module of full support, IV.2.4, IV.2.5,
and the characterizations IV.2.6 of faithfully flat algebras.
-/

universe u v

namespace SGA.SGA1.ExposeIV

open TensorProduct LinearMap Function

variable {A : Type u} [CommRing A]

section Criteria

variable (M : Type v) [AddCommGroup M] [Module A M]

/-- IV.2.1: equivalent characterizations of faithfully flat modules: (i) `M ⊗ -` is faithful and
exact, (i bis) `M` is flat and `M ⊗ N = 0` implies `N = 0`, (i ter) `M` is flat and
`M ⊗ A/𝔪 ≠ 0` for every maximal ideal `𝔪`, (ii) a sequence is exact iff it is after tensoring
with `M`. The test modules live in the universe `max u v`. -/
theorem faithfullyFlat_tfae : List.TFAE
    [Module.FaithfullyFlat A M,
      Module.Flat A M ∧ ∀ {N : Type max u v} [AddCommGroup N] [Module A N]
        {N' : Type max u v} [AddCommGroup N'] [Module A N'] (f : N →ₗ[A] N'),
        f.lTensor M = 0 ↔ f = 0,
      Module.Flat A M ∧ ∀ (N : Type max u v) [AddCommGroup N] [Module A N],
        Subsingleton (M ⊗[A] N) → Subsingleton N,
      Module.Flat A M ∧ ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → Nontrivial (M ⊗[A] (A ⧸ 𝔪)),
      ∀ {N₁ : Type max u v} [AddCommGroup N₁] [Module A N₁] {N₂ : Type max u v}
        [AddCommGroup N₂] [Module A N₂] {N₃ : Type max u v} [AddCommGroup N₃] [Module A N₃]
        (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃),
        Exact f g ↔ Exact (f.lTensor M) (g.lTensor M)] := by
  tfae_have 1 ↔ 2 := Module.FaithfullyFlat.iff_zero_iff_lTensor_zero A M
  tfae_have 1 ↔ 3 := Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality A M
  tfae_have 1 ↔ 5 := Module.FaithfullyFlat.iff_exact_iff_lTensor_exact A M
  tfae_have 1 ↔ 4 := by
    rw [Module.faithfullyFlat_iff]
    refine and_congr_right fun _ ↦ forall_congr' fun 𝔪 ↦ imp_congr_right fun _ ↦ ?_
    have e := (quotTensorEquivQuotSMul M 𝔪).symm.trans (TensorProduct.comm A _ _)
    rw [← not_subsingleton_iff_nontrivial, Ne, ← Submodule.Quotient.subsingleton_iff,
      e.toEquiv.subsingleton_congr]
  tfae_finish

/-- IV.2: a faithfully flat module is faithful. -/
theorem faithfulSMul_of_faithfullyFlat [Module.FaithfullyFlat A M] : FaithfulSMul A M := by
  refine ⟨fun {a b} h ↦ ?_⟩
  rw [← sub_eq_zero]
  have hf := (Module.FaithfullyFlat.zero_iff_lTensor_zero A M (LinearMap.lsmul A A (a - b))).2 (by
    refine TensorProduct.ext' fun m x ↦ ?_
    rw [lTensor_tmul, lsmul_apply, LinearMap.zero_apply, ← smul_tmul, sub_smul, h, sub_self,
      zero_tmul])
  simpa using congr($hf 1)

/-- IV.2: if `M` is faithfully flat, a map `f` is injective, surjective or bijective as soon as
`M ⊗ f` is. -/
theorem injective_surjective_bijective_iff_lTensor [Module.FaithfullyFlat A M] {N N' : Type*}
    [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N'] (f : N →ₗ[A] N') :
    (Injective (f.lTensor M) ↔ Injective f) ∧ (Surjective (f.lTensor M) ↔ Surjective f) ∧
      (Bijective (f.lTensor M) ↔ Bijective f) :=
  ⟨Module.FaithfullyFlat.lTensor_injective_iff_injective A M f,
    Module.FaithfullyFlat.lTensor_surjective_iff_surjective A M f,
    Module.FaithfullyFlat.lTensor_bijective_iff_bijective A M f⟩

/-- IV.2: the tensor product of two faithfully flat modules is faithfully flat. -/
theorem faithfullyFlat_tensorProduct (N : Type v) [AddCommGroup N] [Module A N]
    [Module.FaithfullyFlat A M] [Module.FaithfullyFlat A N] :
    Module.FaithfullyFlat A (M ⊗[A] N) := by
  rw [Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality]
  refine ⟨inferInstance, fun P _ _ h ↦ ?_⟩
  have : Subsingleton (M ⊗[A] (N ⊗[A] P)) := (TensorProduct.assoc A M N P).symm.toEquiv.subsingleton
  have : Subsingleton (N ⊗[A] P) := Module.FaithfullyFlat.lTensor_reflects_triviality A M _
  exact Module.FaithfullyFlat.lTensor_reflects_triviality A N P

/-- IV.2: faithful flatness is preserved by change of base. -/
theorem faithfullyFlat_baseChange (B : Type*) [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A M] : Module.FaithfullyFlat B (B ⊗[A] M) := inferInstance

/-- IV.2: transitivity of faithful flatness. -/
theorem faithfullyFlat_trans (B : Type*) [CommRing B] [Algebra A B] [Module B M]
    [IsScalarTower A B M] [Module.FaithfullyFlat A B] [Module.FaithfullyFlat B M] :
    Module.FaithfullyFlat A M :=
  Module.FaithfullyFlat.trans A B M

end Criteria

section Local

variable {B : Type*} [CommRing B] [Algebra A B]
  {M : Type v} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- IV.2.2: for a local homomorphism of local rings `A → B` and a finite `B`-module `M`, `M` is
faithfully flat over `A` if and only if it is flat over `A` and nonzero. -/
theorem faithfullyFlat_iff_flat_and_nontrivial [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Module.Finite B M] :
    Module.FaithfullyFlat A M ↔ Module.Flat A M ∧ Nontrivial M := by
  refine ⟨fun h ↦ ⟨inferInstance, ?_⟩, fun ⟨hflat, hM⟩ ↦ ⟨fun 𝔪 h𝔪 htop ↦ ?_⟩⟩
  · have := Module.FaithfullyFlat.lTensor_nontrivial A M A
    exact (TensorProduct.rid A M).toEquiv.symm.nontrivial
  · -- `𝔪 M = M` would give `𝔪_B M = M`, hence `M = 0` by Nakayama.
    rw [IsLocalRing.eq_maximalIdeal h𝔪] at htop
    have hle : (⊤ : Submodule B M) ≤ IsLocalRing.maximalIdeal B • (⊤ : Submodule B M) := by
      intro x _
      have hx : x ∈ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A M)) := by
        rw [htop]; trivial
      refine Submodule.smul_induction_on hx (fun a ha y _ ↦ ?_) (fun _ _ ↦ Submodule.add_mem _)
      rw [← algebraMap_smul B a y]
      refine Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).2 fun hu ↦ ?_) trivial
      exact (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit (algebraMap A B) a hu)
    have := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ Module.Finite.fg_top hle
      (IsLocalRing.maximalIdeal_le_jacobson _)
    exact not_subsingleton M (subsingleton_iff_forall_eq 0 |>.2 fun x ↦ by
      simpa using (show x ∈ (⊥ : Submodule B M) from this ▸ trivial))

/-- IV.2.2, the case `M = B`: a local homomorphism of local rings is flat if and only if it
is faithfully flat. -/
theorem faithfullyFlat_iff_flat_of_isLocalHom [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] : Module.FaithfullyFlat A B ↔ Module.Flat A B :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ Module.FaithfullyFlat.of_flat_of_isLocalHom⟩

variable (A B M) in
/-- IV.2.3: if some `B`-module is faithfully flat over `A`, every prime ideal of `A` is induced
by a prime ideal of `B`, i.e. `Spec B → Spec A` is surjective. -/
theorem comap_surjective_of_faithfullyFlat [Module.FaithfullyFlat A M] :
    Surjective (PrimeSpectrum.comap (algebraMap A B)) := by
  intro p
  change p ∈ Set.range _
  rw [← PrimeSpectrum.nontrivial_iff_mem_rangeComap]
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : Subsingleton (B ⊗[A] p.asIdeal.ResidueField) :=
    (TensorProduct.comm A _ _).toEquiv.subsingleton
  have : Subsingleton (M ⊗[A] p.asIdeal.ResidueField) :=
    (AlgebraTensorModule.cancelBaseChange A B B M p.asIdeal.ResidueField).symm.toEquiv.subsingleton
  have := Module.FaithfullyFlat.lTensor_nontrivial A M p.asIdeal.ResidueField
  exact not_subsingleton (M ⊗[A] p.asIdeal.ResidueField) inferInstance

end Local



section GoingDown

variable {B : Type*} [CommRing B] [Algebra A B]
  {M : Type v} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

variable (A B M) in
/-- IV.2.3 applied at the local rings (the argument of IV.2.5 and IV.6.6): if `M` is a finite
`B`-module which is flat over `A` with support all of `Spec B`, then `A → B` has the going-down
property: for `𝔮` prime in `B` inducing `𝔭`, every prime `𝔭' ⊆ 𝔭` is induced by a prime
`𝔮' ⊆ 𝔮`. -/
theorem hasGoingDown_of_flat_of_support_eq_univ [Module.Finite B M] [Module.Flat A M]
    (hM : Module.support B M = Set.univ) : Algebra.HasGoingDown A B := by
  apply Algebra.HasGoingDown.of_comap_localRingHom_surjective
  intro P _
  let p := P.under A
  let Aₚ := Localization.AtPrime p
  let Bₚ := Localization.AtPrime P
  let : Algebra Aₚ Bₚ := Localization.AtPrime.algebraOfLiesOver p P
  let Mₚ := LocalizedModule P.primeCompl M
  let : Module Aₚ Mₚ := Module.compHom Mₚ (algebraMap Aₚ Bₚ)
  have : IsScalarTower Aₚ Bₚ Mₚ := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower A Aₚ Mₚ := IsScalarTower.of_algebraMap_smul fun a x ↦ by
    change (algebraMap Aₚ Bₚ (algebraMap A Aₚ a)) • x = a • x
    rw [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map, algebraMap_smul,
      algebraMap_smul]
  have : Module.Flat A Mₚ := flat_localizedModule P.primeCompl
  have : Module.Flat Aₚ Mₚ := (flat_iff_flat_of_isLocalization p.primeCompl Aₚ).2 inferInstance
  have : IsLocalHom (algebraMap Aₚ Bₚ) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom p P (algebraMap A B) Ideal.LiesOver.over
  have : Nontrivial Mₚ := Module.mem_support_iff.1
    (hM ▸ Set.mem_univ (⟨P, inferInstance⟩ : PrimeSpectrum B))
  have : Module.FaithfullyFlat Aₚ Mₚ :=
    (faithfullyFlat_iff_flat_and_nontrivial (B := Bₚ)).2 ⟨inferInstance, inferInstance⟩
  exact comap_surjective_of_faithfullyFlat Aₚ Bₚ Mₚ

/-- IV.2.4: if `M` is a finite `B`-module, flat over `A`, with support all of `Spec B`, then
every prime `𝔮` of `B` minimal among those containing `𝔭B` induces `𝔭`. -/
theorem comap_eq_of_isMinimalPrime_map [Module.Finite B M] [Module.Flat A M]
    (hM : Module.support B M = Set.univ) (p : Ideal A) [p.IsPrime] {q : Ideal B}
    (hq : (p.map (algebraMap A B)).IsMinimalPrime q) : q.comap (algebraMap A B) = p := by
  have := hasGoingDown_of_flat_of_support_eq_univ A B M hM
  have : q.IsPrime := hq.isPrime
  have hpq : p ≤ q.under A := Ideal.map_le_iff_le_comap.1 hq.le
  have : q.LiesOver (q.under A) := ⟨rfl⟩
  obtain ⟨P, hPq, hP, hPp⟩ := Ideal.exists_ideal_le_liesOver_of_le q hpq
  have hmap : p.map (algebraMap A B) ≤ P := Ideal.map_le_iff_le_comap.2 hPp.over.le
  have : q = P := le_antisymm (hq.2 ⟨hP, hmap⟩ hPq) hPq
  subst this
  exact hPp.over.symm

/-- IV.2.5: under the hypotheses of IV.2.4, every minimal prime of `B` induces a minimal prime
of `A`: every irreducible component of `Spec B` dominates an irreducible component of
`Spec A`. -/
theorem isMinimalPrime_comap [Module.Finite B M] [Module.Flat A M]
    (hM : Module.support B M = Set.univ) {q : Ideal B} (hq : IsMinimalPrime q) :
    IsMinimalPrime (q.comap (algebraMap A B)) := by
  have := hasGoingDown_of_flat_of_support_eq_univ A B M hM
  have : q.IsPrime := hq.isPrime
  refine ⟨⟨Ideal.IsPrime.comap _, bot_le⟩, fun p' ⟨hp', _⟩ hle ↦ ?_⟩
  have : q.LiesOver (q.under A) := ⟨rfl⟩
  obtain ⟨P, hPq, hP, hPp⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := p') q hle
  have : q = P := le_antisymm (hq.2 ⟨hP, bot_le⟩ hPq) hPq
  subst this
  exact hPp.over.ge

end GoingDown
section Algebra

variable {B : Type v} [CommRing B] [Algebra A B]

/-- The image of `I ⊗ B → B` lies in `IB`. -/
private lemma lid_rTensor_mem_map (I : Ideal A) (x : I ⊗[A] B) :
    TensorProduct.lid A B (I.subtype.rTensor B x) ∈ I.map (algebraMap A B) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul i b =>
    rw [rTensor_tmul, TensorProduct.lid_tmul, Submodule.subtype_apply, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ i.2)
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

/-- The converse of IV.1.1 used in IV.2.6, (iv bis) ⇒ (iii): if `B` is flat over `A` and
`IB ∩ A = I` for every ideal `I`, then `B/A` is flat over `A`. -/
private lemma flat_quotient_of_comap_map (hB : Module.Flat A B)
    (h : ∀ I : Ideal A, (I.map (algebraMap A B)).comap (algebraMap A B) = I) :
    Module.Flat A (B ⧸ LinearMap.range (Algebra.linearMap A B)) := by
  let ι := Algebra.linearMap A B
  let C := B ⧸ LinearMap.range ι
  let π : B →ₗ[A] C := (LinearMap.range ι).mkQ
  have hπ : Surjective π := Submodule.mkQ_surjective _
  have hιπ : Exact ι π := LinearMap.exact_map_mkQ_range ι
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective I hπ z
  have hβ : Injective (I.subtype.rTensor B) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  obtain ⟨w, hw⟩ := (_root_.lTensor_exact A hιπ hπ (I.subtype.rTensor B y)).1 (by
    rw [← rTensor_lTensor_apply, hz])
  -- `w ∈ A ⊗ A` is `a ⊗ 1` with `a ∈ I`, since `ι(a)` lies in `IB`
  have hlid (w : A ⊗[A] A) :
      TensorProduct.lid A B (ι.lTensor A w) = algebraMap A B (TensorProduct.lid A A w) := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [ι, Algebra.smul_def]
    | add x y hx hy => simp only [map_add, hx, hy]
  set a := TensorProduct.lid A A w
  have ha : a ∈ I := by
    rw [← h I, Ideal.mem_comap]
    have := lid_rTensor_mem_map I y
    rwa [← hw, hlid] at this
  have hw' : w = I.subtype.rTensor A ((⟨a, ha⟩ : I) ⊗ₜ[A] (1 : A)) := by
    apply (TensorProduct.lid A A).injective
    simp [a]
  have hy : y = ι.lTensor I ((⟨a, ha⟩ : I) ⊗ₜ[A] (1 : A)) := by
    apply hβ
    rw [rTensor_lTensor_apply, ← hw', hw]
  rw [hy, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hιπ.linearMap_comp_eq_zero,
    LinearMap.lTensor_zero, LinearMap.zero_apply]

variable (A B) in
/-- IV.2.6: characterizations of faithfully flat algebras: (i) `B` is faithfully flat;
(ii) `B` is flat and `Spec B → Spec A` is surjective; (ii bis) `B` is flat and every maximal
ideal of `A` is induced by an ideal of `B`; (iii) `A → B` is injective with flat cokernel;
(iv) `B ⊗ -` is exact and `N → B ⊗ N` is injective for every `N`; (iv bis) `B ⊗ I → B` is
injective (i.e. `I ⊗ B ≅ IB`) and `IB ∩ A = I` for every ideal `I`. -/
theorem faithfullyFlat_algebra_tfae : List.TFAE
    [Module.FaithfullyFlat A B,
      Module.Flat A B ∧ Surjective (PrimeSpectrum.comap (algebraMap A B)),
      Module.Flat A B ∧ ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ J : Ideal B,
        J.comap (algebraMap A B) = 𝔪,
      Injective (algebraMap A B) ∧ Module.Flat A (B ⧸ LinearMap.range (Algebra.linearMap A B)),
      Module.Flat A B ∧ ∀ (N : Type u) [AddCommGroup N] [Module A N],
        Injective (TensorProduct.mk A B N 1),
      (∀ I : Ideal A, Injective (I.subtype.lTensor B)) ∧
        ∀ I : Ideal A, (I.map (algebraMap A B)).comap (algebraMap A B) = I] := by
  tfae_have 1 → 2 := fun _ ↦ ⟨inferInstance, comap_surjective_of_faithfullyFlat A B B⟩
  tfae_have 2 → 3 := fun ⟨hB, hs⟩ ↦ ⟨hB, fun 𝔪 h𝔪 ↦ by
    obtain ⟨P, hP⟩ := hs ⟨𝔪, h𝔪.isPrime⟩
    exact ⟨P.asIdeal, congrArg PrimeSpectrum.asIdeal hP⟩⟩
  tfae_have 3 → 1 := fun ⟨hB, hJ⟩ ↦ ⟨fun 𝔪 h𝔪 htop ↦ by
    obtain ⟨J, hJ⟩ := hJ 𝔪 h𝔪
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at htop
    have : J = ⊤ := top_le_iff.1 (htop ▸ Ideal.map_le_iff_le_comap.2 hJ.ge)
    exact h𝔪.ne_top (by rw [← hJ, this, Ideal.comap_top])⟩
  tfae_have 1 → 5 := fun _ ↦ ⟨inferInstance, fun N _ _ ↦
    Module.FaithfullyFlat.tensorProduct_mk_injective N⟩
  tfae_have 5 → 6 := fun ⟨hB, hN⟩ ↦ by
    refine ⟨Module.Flat.iff_lTensor_injective'.1 hB, fun I ↦ ?_⟩
    refine le_antisymm (fun x hx ↦ ?_) Ideal.le_comap_map
    let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toLinearEquiv
    have inj : Injective (e.toLinearMap.restrictScalars A ∘ₗ TensorProduct.mk A B (A ⧸ I) 1) :=
      e.injective.comp (hN (A ⧸ I))
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply inj
    have : (e.toLinearMap.restrictScalars A ∘ₗ TensorProduct.mk A B (A ⧸ I) 1) x = 0 := by
      simp [e, ← Algebra.algebraMap_eq_smul_one, hx]
    simp [this]
  tfae_have 6 → 1 := fun ⟨hI, hcomap⟩ ↦ by
    have : Module.Flat A B := Module.Flat.iff_lTensor_injective'.2 hI
    refine ⟨fun 𝔪 h𝔪 htop ↦ ?_⟩
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at htop
    exact h𝔪.ne_top (by rw [← hcomap 𝔪, htop, Ideal.comap_top])
  tfae_have 6 → 4 := fun ⟨hI, hcomap⟩ ↦ by
    have hB : Module.Flat A B := Module.Flat.iff_lTensor_injective'.2 hI
    refine ⟨fun a b hab ↦ ?_, flat_quotient_of_comap_map hB hcomap⟩
    rw [← sub_eq_zero, ← Ideal.mem_bot, ← hcomap ⊥, Ideal.mem_comap, map_sub, hab, sub_self]
    exact zero_mem _
  tfae_have 4 → 5 := fun ⟨hinj, hC⟩ ↦ by
    let ι := Algebra.linearMap A B
    have hιπ : Exact ι (LinearMap.range ι).mkQ := LinearMap.exact_map_mkQ_range ι
    have hπ := Submodule.mkQ_surjective (LinearMap.range ι)
    refine ⟨(flat_iff_flat_of_flat_quotient ι _ hinj hιπ hπ).2 inferInstance, fun N _ _ ↦ ?_⟩
    have h := (rTensor_shortExact_of_flat ι _ hinj hιπ hπ N).1
    have : TensorProduct.mk A B N 1 = ι.rTensor N ∘ₗ (TensorProduct.lid A N).symm := by
      ext; simp [ι]
    rw [this, LinearMap.coe_comp]
    exact h.comp (TensorProduct.lid A N).symm.injective
  tfae_finish

end Algebra

end SGA.SGA1.ExposeIV
