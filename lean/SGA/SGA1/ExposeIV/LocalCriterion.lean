/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.TensorProduct.Finite
import SGA.SGA1.ExposeIV.FlatModules
import SGA.SGA1.ExposeIV.FreeModules
import SGA.SGA1.ExposeIV.Graded

/-!
# SGA 1, Exposé IV, §5: local criteria of flatness

* IV.5.2 (Serre): `Tor₁^A(M, N) = 0` for all `B`-modules `N` iff `Tor₁^A(M, B) = 0` and
  `B ⊗_A M` is `B`-flat;
* IV.5.3: for `B = A/I` this extends to all modules killed by a power of `I`;
* IV.5.4, IV.5.5: the local flatness criterion for a nilpotent ideal;
* IV.5.6: the local flatness criterion for `A → B` noetherian, `IB` in the radical of `B` and `M`
  a finite `B`-module;
* IV.5.7, IV.5.9: its corollaries.

Flatness of `M ⊗_A A/I` over `A/I` is written `Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M)`.
-/

universe u v w

namespace SGA.SGA1.ExposeIV

open TensorProduct LinearMap Function

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]

section BaseChange

variable {S : Type*} [CommRing S] [Algebra A S]

/-- Naturality of `P ⊗_S (S ⊗_A M) ≃ P ⊗_A M` in the `S`-module `P`. -/
lemma cancelBaseChange_rTensor {P P' : Type*} [AddCommGroup P] [Module A P] [Module S P]
    [IsScalarTower A S P] [AddCommGroup P'] [Module A P'] [Module S P'] [IsScalarTower A S P']
    (f : P' →ₗ[S] P) (x : P' ⊗[S] (S ⊗[A] M)) :
    AlgebraTensorModule.cancelBaseChange A S S P M (f.rTensor (S ⊗[A] M) x) =
      (f.restrictScalars A).rTensor M (AlgebraTensorModule.cancelBaseChange A S S P' M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
    | tmul s m => simp

/-- If `S ⊗_A M` is `S`-flat, tensoring with `M` over `A` preserves injectivity of `S`-linear
maps between `S`-modules. -/
lemma rTensor_injective_of_flat_baseChange [Module.Flat S (S ⊗[A] M)] {P P' : Type*}
    [AddCommGroup P] [Module A P] [Module S P] [IsScalarTower A S P] [AddCommGroup P']
    [Module A P'] [Module S P'] [IsScalarTower A S P'] (f : P' →ₗ[S] P) (hf : Injective f) :
    Injective ((f.restrictScalars A).rTensor M) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := S ⊗[A] M) f hf
  have : ⇑((f.restrictScalars A).rTensor M) =
      AlgebraTensorModule.cancelBaseChange A S S P M ∘ (f.rTensor (S ⊗[A] M)) ∘
        (AlgebraTensorModule.cancelBaseChange A S S P' M).symm := by
    ext x
    simp [cancelBaseChange_rTensor]
  rw [this]
  exact (LinearEquiv.injective _).comp (h.comp (LinearEquiv.injective _))

/-- Conversely, `S ⊗_A M` is `S`-flat as soon as `J ⊗_A M → S ⊗_A M` is injective for every
ideal `J` of `S`. -/
lemma flat_baseChange_of_rTensor_injective
    (h : ∀ J : Ideal S, Injective ((J.subtype.restrictScalars A).rTensor M)) :
    Module.Flat S (S ⊗[A] M) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro J
  have : ⇑(J.subtype.rTensor (S ⊗[A] M)) =
      (AlgebraTensorModule.cancelBaseChange A S S S M).symm ∘
        ((J.subtype.restrictScalars A).rTensor M) ∘
          AlgebraTensorModule.cancelBaseChange A S S J M := by
    ext x
    simp [← cancelBaseChange_rTensor]
  rw [this]
  exact (LinearEquiv.injective _).comp ((h J).comp (LinearEquiv.injective _))

end BaseChange

section Serre

variable (B : Type w) [CommRing B] [Algebra A B]

/-- IV.5.2 (Serre): for a ring homomorphism `A → B` and an `A`-module `M`, `Tor₁^A(M, N) = 0` for
every `B`-module `N` if and only if `Tor₁^A(M, B) = 0` and `B ⊗_A M` is `B`-flat. -/
theorem forall_torOneVanishes_iff :
    (∀ (N : Type w) [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N],
      TorOneVanishes A M N) ↔ TorOneVanishes A M B ∧ Module.Flat B (B ⊗[A] M) := by
  constructor
  · intro h
    refine ⟨h B, flat_baseChange_of_rTensor_injective fun J ↦ ?_⟩
    have := (h (B ⧸ J)).lTensor_injective (K := J) (P := B) (J.subtype.restrictScalars A)
      (J.mkQ.restrictScalars A) Subtype.val_injective (LinearMap.exact_subtype_mkQ J)
      (Submodule.mkQ_surjective J)
    exact (LinearMap.lTensor_inj_iff_rTensor_inj _ _).1 this
  · rintro ⟨hB, hflat⟩ N _ _ _ _
    -- a free presentation `0 → R → L → M → 0` of `M`
    have hK := exact_presentationKer A M
    have hF := presentationMap_surjective A M
    have hBR := (torOneVanishes_iff_rTensor_injective (L := M →₀ A)
      (presentationKer A M).subtype (presentationMap A M) Subtype.val_injective hK hF).1 hB
    have := torOneVanishes_iff_rTensor_injective (N := N) (L := M →₀ A)
      (presentationKer A M).subtype (presentationMap A M) Subtype.val_injective hK hF
    rw [this, ← LinearMap.lTensor_inj_iff_rTensor_inj]
    -- `0 → B ⊗ R → B ⊗ L → B ⊗ M → 0` is an exact sequence of `B`-modules with flat cokernel
    let i := AlgebraTensorModule.lTensor B B (presentationKer A M).subtype
    let p := AlgebraTensorModule.lTensor B B (presentationMap A M)
    have hi : Injective i := by
      simpa [i, AlgebraTensorModule.coe_lTensor, LinearMap.lTensor_inj_iff_rTensor_inj] using hBR
    have hip : Exact i p := by
      simpa [i, p, AlgebraTensorModule.coe_lTensor] using _root_.lTensor_exact B hK hF
    have hp : Surjective p := by
      simpa [p, AlgebraTensorModule.coe_lTensor] using LinearMap.lTensor_surjective B hF
    have h := LinearMap.lTensor_injective_of_exact_of_flat p hp i hi hip N
    have key := AlgebraTensorModule.lTensor_comp_cancelBaseChange A B B (M := N)
      (presentationKer A M).subtype
    have : ⇑((presentationKer A M).subtype.lTensor N) =
        AlgebraTensorModule.cancelBaseChange A B B N (M →₀ A) ∘ (i.lTensor N) ∘
          (AlgebraTensorModule.cancelBaseChange A B B N (presentationKer A M)).symm := by
      ext x
      have := congr($key ((AlgebraTensorModule.cancelBaseChange A B B N _).symm x))
      simpa [AlgebraTensorModule.coe_lTensor, i] using this
    rw [this]
    exact (LinearEquiv.injective _).comp (h.comp (LinearEquiv.injective _))

end Serre

section Nilpotent

variable (I : Ideal A)

/-- A module over `A/I` is killed by `I`. -/
lemma smul_top_eq_bot_of_quotient (N : Type*) [AddCommGroup N] [Module A N] [Module (A ⧸ I) N]
    [IsScalarTower A (A ⧸ I) N] : I • (⊤ : Submodule A N) = ⊥ :=
  eq_bot_iff.2 <| Submodule.smul_le.2 fun a ha x _ ↦ by
    rw [Submodule.mem_bot, ← algebraMap_smul (A ⧸ I) a x, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_smul]

/-- IV.5.3, the induction: if `Tor₁^A(M, N) = 0` for every `A/I`-module `N`, the same holds for
every module killed by `I^n`. -/
theorem torOneVanishes_of_pow_smul_eq_bot
    (h : ∀ (N : Type w) [AddCommGroup N] [Module A N] [Module (A ⧸ I) N]
      [IsScalarTower A (A ⧸ I) N], TorOneVanishes A M N) (n : ℕ) :
    ∀ (N : Type w) [AddCommGroup N] [Module A N], I ^ n • (⊤ : Submodule A N) = ⊥ →
      TorOneVanishes A M N := by
  induction n with
  | zero =>
    intro N _ _ hN
    have hsub : ∀ x : N, x = 0 := fun x ↦ by
      have : x ∈ (1 : Ideal A) • (⊤ : Submodule A N) := by rw [one_smul]; trivial
      rwa [← pow_zero I, hN] at this
    have hI : Module.IsTorsionBySet A N I := fun x _ ↦ hsub _
    let := hI.module
    have := hI.isScalarTower (S := A)
    exact h N
  | succ n ih =>
    intro N _ _ hN
    let P := I • (⊤ : Submodule A N)
    have hP : I ^ n • (⊤ : Submodule A P) = ⊥ := by
      apply Submodule.map_injective_of_injective P.injective_subtype
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, Submodule.map_bot,
        ← mul_smul, ← pow_succ, hN]
    exact TorOneVanishes.of_exact P.subtype P.mkQ P.injective_subtype
      (LinearMap.exact_subtype_mkQ P) P.mkQ_surjective (ih P hP) (h (N ⧸ P))

/-- IV.5.3: for `B = A/I`, the conditions of IV.5.2 are equivalent to `Tor₁^A(M, N) = 0` for
every module `N` killed by a power of `I`. -/
theorem forall_torOneVanishes_quotient_iff :
    (∀ (N : Type w) [AddCommGroup N] [Module A N] [Module (A ⧸ I) N]
      [IsScalarTower A (A ⧸ I) N], TorOneVanishes A M N) ↔
    ∀ (N : Type w) [AddCommGroup N] [Module A N], (∃ n, I ^ n • (⊤ : Submodule A N) = ⊥) →
      TorOneVanishes A M N :=
  ⟨fun h N _ _ ⟨n, hn⟩ ↦ torOneVanishes_of_pow_smul_eq_bot I h n N hn,
    fun h N _ _ _ _ ↦ h N ⟨1, by rw [pow_one]; exact smul_top_eq_bot_of_quotient I N⟩⟩

/-- `A/I^n` is killed by `I^n`. -/
lemma pow_smul_top_quotient_eq_bot (n : ℕ) : I ^ n • (⊤ : Submodule A (A ⧸ I ^ n)) = ⊥ :=
  smul_top_eq_bot_of_quotient (I ^ n) (A ⧸ I ^ n)

/-- IV.5.4: under the conditions of IV.5.3 (for `B = A/I`), the canonical map
`gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)` is an isomorphism and `M ⊗_A A/I` is flat over `A/I`. -/
theorem grMapInjective_and_flat_of_forall_torOneVanishes
    (h : ∀ (N : Type u) [AddCommGroup N] [Module A N] [Module (A ⧸ I) N]
      [IsScalarTower A (A ⧸ I) N], TorOneVanishes A M N) :
    GrMapInjective I M ∧ Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M) :=
  ⟨grMapInjective_of_torOneVanishes fun n _ ↦
      (forall_torOneVanishes_quotient_iff I).1 h _ ⟨n, pow_smul_top_quotient_eq_bot I n⟩,
    ((forall_torOneVanishes_iff (A ⧸ I)).1 h).2⟩

/-- The conditions of IV.5.2 for `B = A/I`, from `Tor₁^A(M, A/I) = 0` and the flatness of
`M ⊗_A A/I` over `A/I`. -/
lemma forall_torOneVanishes_of_flat_quotient (hT : TorOneVanishes A M (A ⧸ I))
    (hF : Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M)) :
    ∀ (N : Type u) [AddCommGroup N] [Module A N] [Module (A ⧸ I) N]
      [IsScalarTower A (A ⧸ I) N], TorOneVanishes A M N :=
  (forall_torOneVanishes_iff (A ⧸ I)).2 ⟨hT, hF⟩

variable (M) in
/-- IV.5.5 (local flatness criterion, nilpotent case): for a nilpotent ideal `I`, the following
are equivalent: (i) `M` is flat; (ii) `M ⊗_A A/I` is `A/I`-flat and `Tor₁^A(M, A/I) = 0`;
(iii) `M ⊗_A A/I` is `A/I`-flat and `gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)` is an isomorphism. -/
theorem flat_tfae_of_isNilpotent (hI : IsNilpotent I) : List.TFAE
    [Module.Flat A M,
      Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧ TorOneVanishes A M (A ⧸ I),
      Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧ GrMapInjective I M] := by
  tfae_have 1 → 2 := fun _ ↦ ⟨inferInstance, torOneVanishes_of_flat _⟩
  tfae_have 2 → 3 := fun ⟨hF, hT⟩ ↦
    ⟨hF, (grMapInjective_and_flat_of_forall_torOneVanishes I
      (forall_torOneVanishes_of_flat_quotient I hT hF)).1⟩
  tfae_have 3 → 1 := fun ⟨hF, hG⟩ ↦ by
    have hT := torOneVanishes_of_grMapInjective_of_isNilpotent hI hG 1
    rw [pow_one] at hT
    obtain ⟨n, hn⟩ := hI
    refine (flat_iff_forall_torOneVanishes A M).2 fun N _ _ ↦ ?_
    refine (forall_torOneVanishes_quotient_iff I).1 (forall_torOneVanishes_of_flat_quotient I hT hF)
      N ⟨n, ?_⟩
    rw [hn, Submodule.zero_eq_bot, Submodule.bot_smul]
  tfae_finish

end Nilpotent

section Noetherian

variable {B : Type w} [CommRing B] [Algebra A B] [Module B M] [IsScalarTower A B M]
  (I : Ideal A)

variable (M) in
/-- `M ⊗_A N` is a finite `B`-module if `M` is a finite `B`-module and `N` a finite `A`-module. -/
lemma finite_tensorProduct [Module.Finite B M] (N : Type*) [AddCommGroup N] [Module A N]
    [Module.Finite A N] : Module.Finite B (M ⊗[A] N) :=
  Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange A B B M N)

/-- Krull's intersection theorem, in the form used in IV.5.6: a finite `B`-module is
`I`-adically separated when `IB` lies in the radical of the noetherian ring `B`. -/
lemma eq_zero_of_forall_mem_pow_smul [IsNoetherianRing B]
    (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥) {X : Type*} [AddCommGroup X] [Module A X]
    [Module B X] [IsScalarTower A B X] [Module.Finite B X] {x : X}
    (hx : ∀ k, x ∈ I ^ k • (⊤ : Submodule A X)) : x = 0 := by
  have hle (k : ℕ) : I ^ k • (⊤ : Submodule A X) ≤
      ((I.map (algebraMap A B)) ^ k • (⊤ : Submodule B X)).restrictScalars A := by
    refine Submodule.smul_le.2 fun a ha y _ ↦ ?_
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul B a y]
    exact Submodule.smul_mem_smul (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha)
      trivial
  have hmem : x ∈ ⨅ k, (I.map (algebraMap A B)) ^ k • (⊤ : Submodule B X) :=
    Submodule.mem_iInf _ |>.2 fun k ↦ hle k (hx k)
  rwa [Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _ hI, Submodule.mem_bot] at hmem

variable (M) in
/-- For `J` an ideal of the noetherian ring `A`, `J ⊗_A M` is `I`-adically separated. -/
lemma eq_zero_of_forall_mem_pow_smul_tensor [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Finite B M] (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥) (J : Ideal A)
    {y : J ⊗[A] M} (hy : ∀ k, y ∈ I ^ k • (⊤ : Submodule A (J ⊗[A] M))) : y = 0 := by
  have := finite_tensorProduct (A := A) (B := B) M J
  let e := TensorProduct.comm A J M
  suffices e y = 0 by simpa using this
  refine eq_zero_of_forall_mem_pow_smul (B := B) I hI fun k ↦ ?_
  have := Submodule.mem_map_of_mem (f := e.toLinearMap) (hy k)
  rwa [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 e.surjective] at this

/-- The image of `P ⊗ M → X ⊗ M` lies in `K (X ⊗ M)` when `P ⊆ K X`. -/
lemma rTensor_subtype_mem_smul_top {X : Type*} [AddCommGroup X] [Module A X] (K : Ideal A)
    (P : Submodule A X) (hP : P ≤ K • ⊤) (z : P ⊗[A] M) :
    P.subtype.rTensor M z ∈ K • (⊤ : Submodule A (X ⊗[A] M)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => rw [map_add]; exact add_mem hy hz
  | tmul p m =>
    rw [rTensor_tmul, Submodule.subtype_apply]
    refine Submodule.smul_induction_on (hP p.2) (fun a ha x _ ↦ ?_) (fun x x' hx hx' ↦ ?_)
    · rw [← smul_tmul']
      exact Submodule.smul_mem_smul ha trivial
    · rw [add_tmul]
      exact add_mem hx hx'

/-- IV.5.6, (iv) ⇒ (i): the Artin–Rees argument. -/
theorem flat_of_forall_flat_quotient_pow [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Finite B M] (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥)
    (h : ∀ n, Module.Flat (A ⧸ I ^ n) ((A ⧸ I ^ n) ⊗[A] M)) : Module.Flat A M := by
  rw [Module.Flat.iff_rTensor_injective']
  intro J
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_forall_mem_pow_smul_tensor (B := B) M I hI J fun k ↦ ?_
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (J : Submodule A A)
  set n := k + c
  -- `V = J ∩ I^n`, the kernel of `J → A/I^n`
  let g : J →ₗ[A] A ⧸ I ^ n := (I ^ n).mkQ ∘ₗ J.subtype
  let V := LinearMap.ker g
  let gbar : (J ⧸ V) →ₗ[A] A ⧸ I ^ n := V.liftQ g le_rfl
  have hgbar : Injective gbar := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  -- `J/V` and `A/I^n` are `A/I^n`-modules, and `M ⊗ A/I^n` is flat over `A/I^n`
  have htors : Module.IsTorsionBySet A (J ⧸ V) (I ^ n : Ideal A) := by
    rintro y ⟨a, ha⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective V y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    change (I ^ n).mkQ (a • (y : A)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Ideal.mul_mem_right _ _ ha
  let := htors.module
  have := htors.isScalarTower (S := A)
  let gbar' : (J ⧸ V) →ₗ[A ⧸ I ^ n] A ⧸ I ^ n :=
    gbar.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have hinj : Injective ((gbar'.restrictScalars A).rTensor M) :=
    rTensor_injective_of_flat_baseChange (S := A ⧸ I ^ n) gbar' hgbar
  have hx' : V.mkQ.rTensor M x = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    change (g.rTensor M) x = 0
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, hx, map_zero]
  obtain ⟨z, rfl⟩ := (_root_.rTensor_exact M (LinearMap.exact_subtype_mkQ V)
    (Submodule.mkQ_surjective V) x).1 hx'
  refine rTensor_subtype_mem_smul_top (I ^ k) V ?_ z
  -- Artin–Rees: `J ∩ I^n ⊆ I^k J`
  intro v hv
  have hv' : (v : A) ∈ I ^ n • (⊤ : Submodule A A) ⊓ J := by
    refine ⟨?_, v.2⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    simpa [V, g, Ideal.Quotient.eq_zero_iff_mem] using hv
  rw [hc n (by omega), show n - c = k by omega] at hv'
  have hle : I ^ k • (I ^ c • (⊤ : Submodule A A) ⊓ J) ≤ I ^ k • J :=
    Submodule.smul_mono le_rfl inf_le_right
  have hmap : (I ^ k • (⊤ : Submodule A J)).map J.subtype = I ^ k • J := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← Submodule.comap_map_eq_of_injective J.injective_subtype (I ^ k • ⊤), hmap]
  exact hle hv'

variable (M) in
/-- IV.5.6 (local flatness criterion): let `A → B` be a homomorphism of noetherian rings, `I` an
ideal of `A` with `IB` contained in the radical of `B`, and `M` a finite `B`-module. The
following are equivalent: (i) `M` is `A`-flat; (ii) `M ⊗_A A/I` is `A/I`-flat and
`Tor₁^A(M, A/I) = 0`; (iii) `M ⊗_A A/I` is `A/I`-flat and
`gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)` is an isomorphism; (iv) `M ⊗_A A/I^n` is `A/I^n`-flat for
every `n`. -/
theorem flat_tfae [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite B M]
    (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥) : List.TFAE
    [Module.Flat A M,
      Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧ TorOneVanishes A M (A ⧸ I),
      Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧ GrMapInjective I M,
      ∀ n, Module.Flat (A ⧸ I ^ n) ((A ⧸ I ^ n) ⊗[A] M)] := by
  tfae_have 1 → 2 := fun _ ↦ ⟨inferInstance, torOneVanishes_of_flat _⟩
  tfae_have 2 → 3 := fun ⟨hF, hT⟩ ↦
    ⟨hF, (grMapInjective_and_flat_of_forall_torOneVanishes I
      (forall_torOneVanishes_of_flat_quotient I hT hF)).1⟩
  tfae_have 3 → 2 := fun ⟨hF, hG⟩ ↦ by
    refine ⟨hF, ?_⟩
    have := torOneVanishes_of_grMapInjective hG 1 fun y hy ↦
      eq_zero_of_forall_mem_pow_smul_tensor (B := B) M I hI (I ^ 1) hy
    rwa [pow_one] at this
  tfae_have 2 → 4 := fun ⟨hF, hT⟩ n ↦ by
    have h := forall_torOneVanishes_of_flat_quotient I hT hF
    refine ((forall_torOneVanishes_iff (A ⧸ I ^ n)).1 fun N _ _ _ _ ↦ ?_).2
    exact (forall_torOneVanishes_quotient_iff I).1 h N ⟨n, smul_top_eq_bot_of_quotient _ N⟩
  tfae_have 4 → 1 := flat_of_forall_flat_quotient_pow (B := B) I hI
  tfae_finish

end Noetherian

section Local

open IsLocalRing

variable {B : Type w} [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

/-- A local homomorphism maps `𝔪_A` into `𝔪_B`. -/
lemma algebraMap_mem_maximalIdeal {a : A} (ha : a ∈ maximalIdeal A) :
    algebraMap A B a ∈ maximalIdeal B :=
  (mem_maximalIdeal _).2 fun hu ↦ (mem_maximalIdeal _).1 ha
    (isUnit_of_map_unit (algebraMap A B) a hu)

/-- For a local homomorphism, `𝔪_A B` lies in the maximal ideal (the radical) of `B`. -/
lemma map_maximalIdeal_le_jacobson (I : Ideal A) (hI : I ≤ maximalIdeal A) :
    I.map (algebraMap A B) ≤ Ideal.jacobson ⊥ := by
  refine le_trans ?_ (maximalIdeal_le_jacobson _)
  rw [Ideal.map_le_iff_le_comap]
  exact fun a ha ↦ algebraMap_mem_maximalIdeal (hI ha)

/-- A module over the field `A/𝔪` is flat. -/
lemma flat_residueField (N : Type*) [AddCommGroup N] [Module (A ⧸ maximalIdeal A) N] :
    Module.Flat (A ⧸ maximalIdeal A) N := by
  let := Ideal.Quotient.field (maximalIdeal A)
  infer_instance

/-- Remark after IV.5.6: when `A → B` is a local homomorphism of noetherian local rings and
`I = 𝔪` (so `A/I` is a field), condition (iv) of IV.5.6 says that the `M ⊗_A A/𝔪^n` are free over
the artinian rings `A/𝔪^n`. -/
theorem flat_iff_forall_free_quotient_pow [IsNoetherianRing A] [IsNoetherianRing B]
    [Module B M] [IsScalarTower A B M] [Module.Finite B M] :
    Module.Flat A M ↔ ∀ n, Module.Free (A ⧸ maximalIdeal A ^ n)
      ((A ⧸ maximalIdeal A ^ n) ⊗[A] M) := by
  have htf := flat_tfae (B := B) M (maximalIdeal A) (map_maximalIdeal_le_jacobson _ le_rfl)
  have h14 := htf.out 1 4
  rw [h14]
  refine forall_congr' fun n ↦ ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · have : Subsingleton (A ⧸ maximalIdeal A ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
    exact Module.Free.of_subsingleton' _ _
  -- over `A/𝔪^n`, whose maximal ideal is nilpotent, flat modules are free (IV.4.3 (a))
  set S := A ⧸ maximalIdeal A ^ n
  set J := (maximalIdeal A).map (Ideal.Quotient.mk (maximalIdeal A ^ n))
  have : J.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact Ideal.pow_le_self hn.ne')
  have hJ : IsNilpotent J :=
    ⟨n, by rw [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.zero_eq_bot]⟩
  have h13 := (free_tfae_of_isNilpotent J (S ⊗[A] M) hJ).out 1 3
  exact h13.2 h

variable {M' : Type*} [AddCommGroup M'] [Module A M'] [Module B M'] [IsScalarTower A B M']
  [Module B M] [IsScalarTower A B M]

/-- IV.5.7: let `A → B` be a local homomorphism of noetherian local rings, `u : M' → M` a
homomorphism of finite `B`-modules with `M` flat over `A`, and `k = A/𝔪`. Then `u` is injective
with `A`-flat cokernel if and only if `u ⊗_A k` is injective. -/
theorem injective_and_flat_coker_iff [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Finite B M] [Module.Finite B M'] [Module.Flat A M] (u : M' →ₗ[B] M) :
    Injective u ∧ Module.Flat A (M ⧸ LinearMap.range u) ↔
      Injective ((u.restrictScalars A).rTensor (A ⧸ maximalIdeal A)) := by
  set k := A ⧸ maximalIdeal A
  let N := LinearMap.range u
  let C := M ⧸ N
  have hNC : Exact (N.subtype.restrictScalars A) (N.mkQ.restrictScalars A) :=
    LinearMap.exact_subtype_mkQ N
  have hC := Submodule.mkQ_surjective N
  constructor
  · rintro ⟨hu, hflat⟩
    exact (rTensor_shortExact_of_flat (u.restrictScalars A) (N.mkQ.restrictScalars A) hu
      (by simpa using LinearMap.exact_map_mkQ_range u) hC k).1
  · intro h
    -- `u ⊗ k` factors as `M' ⊗ k → N ⊗ k → M ⊗ k`
    let r := u.rangeRestrict
    have hr : Surjective r := LinearMap.surjective_rangeRestrict u
    have hfac : u.restrictScalars A = N.subtype.restrictScalars A ∘ₗ r.restrictScalars A := rfl
    rw [hfac, LinearMap.rTensor_comp, LinearMap.coe_comp] at h
    have hrk : Surjective ((r.restrictScalars A).rTensor k) :=
      LinearMap.rTensor_surjective k (g := r.restrictScalars A) hr
    have hN : Injective ((N.subtype.restrictScalars A).rTensor k) := h.of_comp_right hrk
    have hrk' : Injective ((r.restrictScalars A).rTensor k) := h.of_comp
    -- `Tor₁^A(C, k) = 0`, computed from the flat presentation `0 → N → M → C → 0`
    have hT : TorOneVanishes A C k :=
      (torOneVanishes_iff_rTensor_injective (N.subtype.restrictScalars A)
        (N.mkQ.restrictScalars A) N.injective_subtype hNC hC).2 hN
    -- hence `C` is flat by IV.5.6 (ii) ⇒ (i)
    have htf := flat_tfae (B := B) C (maximalIdeal A) (map_maximalIdeal_le_jacobson _ le_rfl)
    have hCflat : Module.Flat A C := by
      have := htf.out 1 2
      exact this.2 ⟨flat_residueField _, hT⟩
    -- so `N` is flat, and `0 → ker u → M' → N → 0` stays exact after `⊗ k`
    have hNflat : Module.Flat A N :=
      (flat_iff_flat_of_flat_quotient (N.subtype.restrictScalars A) (N.mkQ.restrictScalars A)
        N.injective_subtype hNC hC).1 inferInstance
    let K := LinearMap.ker u
    have hK : Exact (K.subtype.restrictScalars A) (r.restrictScalars A) := by
      intro x
      simp [K, r, LinearMap.mem_ker, Subtype.ext_iff]
    have hKk := (rTensor_shortExact_of_flat (K.subtype.restrictScalars A)
      (r.restrictScalars A) K.injective_subtype hK hr k).1
    -- `K ⊗ k = 0`, so `K = 𝔪 K = 0` by Nakayama
    have hsub (x : K ⊗[A] k) : x = 0 := hKk (hrk' (by
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hK.linearMap_comp_eq_zero,
        LinearMap.rTensor_zero, LinearMap.zero_apply, map_zero, map_zero]))
    have hKtop : maximalIdeal A • (⊤ : Submodule A K) = ⊤ := by
      rw [← Submodule.Quotient.subsingleton_iff]
      have e := (quotTensorEquivQuotSMul K (maximalIdeal A)).symm.trans
        (TensorProduct.comm A (A ⧸ maximalIdeal A) K)
      exact e.toEquiv.subsingleton_congr.2 ⟨fun x y ↦ by rw [hsub x, hsub y]⟩
    have hKbot : (⊤ : Submodule B K) = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal B) _
        Module.Finite.fg_top (fun x _ ↦ ?_) (maximalIdeal_le_jacobson _)
      have hx : x ∈ maximalIdeal A • (⊤ : Submodule A K) := by rw [hKtop]; trivial
      refine Submodule.smul_induction_on hx (fun a ha y _ ↦ ?_) fun _ _ ↦ Submodule.add_mem _
      rw [← algebraMap_smul B a y]
      exact Submodule.smul_mem_smul (algebraMap_mem_maximalIdeal ha) trivial
    refine ⟨fun x y hxy ↦ ?_, hCflat⟩
    have hmem : (⟨x - y, by simp [K, hxy]⟩ : K) ∈ (⊤ : Submodule B K) := trivial
    rw [hKbot, Submodule.mem_bot] at hmem
    exact sub_eq_zero.1 (congrArg Subtype.val hmem)

end Local

section Tower

open IsLocalRing

variable {B : Type w} [CommRing B] [Algebra A B]

omit [Module A M] in
/-- Flatness of a base change `R ⊗_B M` over `R` only depends on the `B`-algebra `R` up to
isomorphism. -/
lemma flat_baseChange_congr {R R' : Type*} [CommRing R] [CommRing R'] [Algebra B R] [Algebra B R']
    [Module B M] (e : R ≃ₐ[B] R') [Module.Flat R (R ⊗[B] M)] :
    Module.Flat R' (R' ⊗[B] M) := by
  let : Algebra R R' := e.toRingHom.toAlgebra
  have : IsScalarTower B R R' := IsScalarTower.of_algebraMap_eq fun b ↦ (e.commutes b).symm
  exact Module.Flat.of_linearEquiv
    (AlgebraTensorModule.cancelBaseChange B R R' R' M).symm


/-- For `B` flat over `A`, `Tor₁^B(M, B ⊗_A N) = Tor₁^A(M, N)` in the case `N = A/I`, `M` an
`A`-flat `B`-module: here `Tor₁^B(M, B/IB) = 0`. -/
lemma torOneVanishes_quotient_map_of_flat [Module.Flat A B] [Module B M] [IsScalarTower A B M]
    [Module.Flat A M] (I : Ideal A) :
    TorOneVanishes B M (B ⧸ I.map (algebraMap A B)) := by
  let f := AlgebraTensorModule.lTensor B B I.subtype
  let g := AlgebraTensorModule.lTensor B B I.mkQ
  have hf : Injective f := by
    simpa [f, AlgebraTensorModule.coe_lTensor] using
      Module.Flat.lTensor_preserves_injective_linearMap (M := B) I.subtype Subtype.val_injective
  have hfg : Exact f g := by
    simpa [f, g, AlgebraTensorModule.coe_lTensor] using
      _root_.lTensor_exact B (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
  have hg : Surjective g := by
    simpa [g, AlgebraTensorModule.coe_lTensor] using
      LinearMap.lTensor_surjective B I.mkQ_surjective
  have hT : TorOneVanishes B M (B ⊗[A] (A ⧸ I)) := by
    rw [torOneVanishes_iff_lTensor_injective f g hf hfg hg]
    have key := AlgebraTensorModule.lTensor_comp_cancelBaseChange A B B (M := M) I.subtype
    have : ⇑(f.lTensor M) =
        (AlgebraTensorModule.cancelBaseChange A B B M A).symm ∘ (I.subtype.lTensor M) ∘
          AlgebraTensorModule.cancelBaseChange A B B M I := by
      ext x
      have := congr($key x)
      simp only [LinearMap.coe_comp, comp_apply, LinearEquiv.coe_coe,
        AlgebraTensorModule.coe_lTensor] at this
      simp [f, this]
    rw [this]
    exact (LinearEquiv.injective _).comp
      ((Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective).comp
        (LinearEquiv.injective _))
  exact hT.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toLinearEquiv

/-- IV.5.9, nilpotent variant (remark after IV.5.9): if `B` is flat over `A` and `I` is a
nilpotent ideal of `A`, a `B`-module `M` is flat over `B` if and only if it is flat over `A` and
`M ⊗_A A/I = (B/IB) ⊗_B M` is flat over `B ⊗_A A/I = B/IB`. No finiteness is needed. -/
theorem flat_iff_flat_and_flat_fibre_of_isNilpotent [Module.Flat A B] [Module B M]
    [IsScalarTower A B M] (I : Ideal A) (hI : IsNilpotent I) :
    Module.Flat B M ↔ Module.Flat A M ∧
      Module.Flat (B ⧸ I.map (algebraMap A B)) ((B ⧸ I.map (algebraMap A B)) ⊗[B] M) := by
  constructor
  · intro _
    exact ⟨Module.Flat.trans A B M, inferInstance⟩
  · rintro ⟨hA, hF⟩
    have hIB : IsNilpotent (I.map (algebraMap A B)) := by
      obtain ⟨n, hn⟩ := hI
      exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]; rfl⟩
    have := (flat_tfae_of_isNilpotent M _ hIB).out 1 2
    exact this.2 ⟨hF, torOneVanishes_quotient_map_of_flat I⟩

variable {C : Type*} [CommRing C] [Algebra B C] [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
  [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)] [Module B M] [Module C M]
  [IsScalarTower A B M] [IsScalarTower B C M]

/-- IV.5.9: let `A → B → C` be local homomorphisms of noetherian local rings with `B` flat over
`A`, `M` a finite `C`-module and `k = A/𝔪`. Then `M` is flat over `B` if and only if `M` is flat
over `A` and `M ⊗_A k` is flat over `B ⊗_A k`. Here `B ⊗_A k` is written `B/𝔪B` and
`M ⊗_A k = (B/𝔪B) ⊗_B M`. -/
theorem flat_iff_flat_and_flat_fibre [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing C] [Module.Flat A B] [Module.Finite C M] :
    Module.Flat B M ↔ Module.Flat A M ∧
      Module.Flat (B ⧸ (maximalIdeal A).map (algebraMap A B))
        ((B ⧸ (maximalIdeal A).map (algebraMap A B)) ⊗[B] M) := by
  set J := (maximalIdeal A).map (algebraMap A B)
  constructor
  · intro _
    exact ⟨Module.Flat.trans A B M, inferInstance⟩
  · rintro ⟨hA, hF⟩
    have hJ : J ≤ maximalIdeal B := by
      rw [Ideal.map_le_iff_le_comap]
      exact fun a ha ↦ algebraMap_mem_maximalIdeal ha
    have htf := flat_tfae (B := C) M J (map_maximalIdeal_le_jacobson J hJ)
    have := htf.out 1 2
    exact this.2 ⟨hF, torOneVanishes_quotient_map_of_flat _⟩

/-- IV.5.9, with the fibre written literally: `M ⊗_A k` is flat over `B ⊗_A k`, where
`M ⊗_A k = (B ⊗_A k) ⊗_B M`. -/
theorem flat_iff_flat_and_flat_tensor_residueField [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing C] [Module.Flat A B] [Module.Finite C M] :
    Module.Flat B M ↔ Module.Flat A M ∧
      Module.Flat (B ⊗[A] (A ⧸ maximalIdeal A)) ((B ⊗[A] (A ⧸ maximalIdeal A)) ⊗[B] M) := by
  rw [flat_iff_flat_and_flat_fibre (A := A) (C := C)]
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (maximalIdeal A)
  exact and_congr_right fun _ ↦ ⟨fun _ ↦ flat_baseChange_congr e,
    fun _ ↦ flat_baseChange_congr e.symm⟩

end Tower


end SGA.SGA1.ExposeIV
