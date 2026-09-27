/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.StrictHenselization
import SGA.Foundations.Formal.NoetherianOfComplete
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Unramified.Finite

/-!
# The henselization of a noetherian local ring is noetherian

Let `R` be a noetherian local ring. The henselization and the strict henselization of `R` are
noetherian (Stacks 06LJ; EGA IV 18.6.6, 18.8.8). More generally, for any field `K` with a local
homomorphism `R → K`, `IsLocalRing.StrictHenselization R K` is noetherian
(`IsLocalRing.StrictHenselization.isNoetherianRing`).

The proof follows Stacks: let `C` be the colimit and `Ĉ` its completion for the maximal ideal
`𝔪_R C`, which is finitely generated. Then `Ĉ` is a complete local ring with finitely generated
maximal ideal, hence noetherian. Its reductions `Ĉ/𝔪ⁿĈ = C/𝔪ⁿC` are flat over `R/𝔪ⁿ`, so by the
local flatness criterion `Ĉ` is flat over `R`; since the neighbourhoods are unramified over `R`,
`Ĉ` is flat over each of them, hence over their colimit `C`. As `C → Ĉ` is local, it is faithfully
flat, and noetherianity descends along faithfully flat maps.

## Main results

* `IsNoetherianRing.of_faithfullyFlat`: faithfully flat descent of noetherianity.
* `Module.Flat.of_forall_flat_quotient_pow`: the local flatness criterion (EGA 0_III 10.2.2).
* `IsLocalRing.StrictHenselization.isNoetherianRing`.
* `IsLocalRing.Henselization.isNoetherianStatement`,
  `IsLocalRing.StrictHenselization.isNoetherianStatement`.
-/

universe u v w

open IsLocalRing TensorProduct LinearMap

/-- Noetherianity descends along faithfully flat ring maps. -/
theorem IsNoetherianRing.of_faithfullyFlat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [IsNoetherianRing B] : IsNoetherianRing A := by
  refine ⟨fun I ↦ ?_⟩
  classical
  obtain ⟨G, hGsub, hGspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    (algebraMap A B '' (I : Set A))).mp (IsNoetherian.noetherian (Ideal.span _))
  have hpre (g : B) (hg : g ∈ G) : ∃ a ∈ I, algebraMap A B a = g := hGsub hg
  choose f hfI hf using hpre
  let t : Finset A := G.attach.image fun g ↦ f g.1 g.2
  have htI : (t : Set A) ⊆ I := by
    intro a ha
    simp only [t, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
      true_and] at ha
    obtain ⟨g, rfl⟩ := ha
    exact hfI _ _
  have himage : algebraMap A B '' (t : Set A) = G := by
    ext b
    simp only [t, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      rw [hf]
      exact g.2
    · intro hb
      exact ⟨_, ⟨⟨b, hb⟩, rfl⟩, hf b hb⟩
  have hmap : Ideal.map (algebraMap A B) (Ideal.span (t : Set A)) =
      Ideal.map (algebraMap A B) I := by
    rw [Ideal.map_span, himage]
    exact hGspan.symm
  refine ⟨t, le_antisymm (Ideal.span_le.mpr htI) ?_⟩
  calc I ≤ Ideal.comap (algebraMap A B) (Ideal.map (algebraMap A B) I) := Ideal.le_comap_map
    _ = Ideal.comap (algebraMap A B) (Ideal.map (algebraMap A B) (Ideal.span (t : Set A))) := by
      rw [hmap]
    _ = Ideal.span (t : Set A) := Ideal.comap_map_eq_self_of_faithfullyFlat _

/-! ### The local flatness criterion -/

namespace Module.Flat

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
    [Module A P'] [Module S P'] [IsScalarTower A S P'] (f : P' →ₗ[S] P)
    (hf : Function.Injective f) : Function.Injective ((f.restrictScalars A).rTensor M) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := S ⊗[A] M) f hf
  have : ⇑((f.restrictScalars A).rTensor M) =
      AlgebraTensorModule.cancelBaseChange A S S P M ∘ (f.rTensor (S ⊗[A] M)) ∘
        (AlgebraTensorModule.cancelBaseChange A S S P' M).symm := by
    ext x
    simp [cancelBaseChange_rTensor]
  rw [this]
  exact (LinearEquiv.injective _).comp (h.comp (LinearEquiv.injective _))

end BaseChange

variable {B : Type w} [CommRing B] [Algebra A B] [Module B M] [IsScalarTower A B M]
  (I : Ideal A)

/-- Krull's intersection theorem: a finite `B`-module is `I`-adically separated when `IB` lies
in the Jacobson radical of the noetherian ring `B`. -/
lemma eq_zero_of_forall_mem_pow_smul [IsNoetherianRing B]
    (hI : Ideal.map (algebraMap A B) I ≤ Ideal.jacobson ⊥) {X : Type*} [AddCommGroup X] [Module A X]
    [Module B X] [IsScalarTower A B X] [Module.Finite B X] {x : X}
    (hx : ∀ k, x ∈ I ^ k • (⊤ : Submodule A X)) : x = 0 := by
  have hle (k : ℕ) : I ^ k • (⊤ : Submodule A X) ≤
      ((Ideal.map (algebraMap A B) I) ^ k • (⊤ : Submodule B X)).restrictScalars A := by
    refine Submodule.smul_le.2 fun a ha y _ ↦ ?_
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul B a y]
    exact Submodule.smul_mem_smul (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha)
      trivial
  have hmem : x ∈ ⨅ k, (Ideal.map (algebraMap A B) I) ^ k • (⊤ : Submodule B X) :=
    Submodule.mem_iInf _ |>.2 fun k ↦ hle k (hx k)
  rwa [Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _ hI, Submodule.mem_bot] at hmem

variable (M) in
/-- For `J` an ideal of the noetherian ring `A` and `M` finite over the noetherian `B`,
`J ⊗_A M` is `I`-adically separated. -/
lemma eq_zero_of_forall_mem_pow_smul_tensor [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Finite B M] (hI : Ideal.map (algebraMap A B) I ≤ Ideal.jacobson ⊥) (J : Ideal A)
    {y : J ⊗[A] M} (hy : ∀ k, y ∈ I ^ k • (⊤ : Submodule A (J ⊗[A] M))) : y = 0 := by
  have : Module.Finite B (M ⊗[A] J) :=
    Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange A B B M J)
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

/-- The local flatness criterion (EGA 0_III 10.2.2, Stacks 0912; adapted from
`SGA.SGA1.ExposeIV.flat_of_forall_flat_quotient_pow`): let `A → B` be a homomorphism of noetherian
rings, `I` an ideal of `A` with `IB` in the Jacobson radical of `B`, and `M` a finite `B`-module.
If `M/IⁿM` is flat over `A/Iⁿ` for every `n`, then `M` is flat over `A`. -/
theorem of_forall_flat_quotient_pow [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Finite B M] (hI : Ideal.map (algebraMap A B) I ≤ Ideal.jacobson ⊥)
    (h : ∀ n, Module.Flat (A ⧸ I ^ n) ((A ⧸ I ^ n) ⊗[A] M)) : Module.Flat A M := by
  rw [Module.Flat.iff_rTensor_injective']
  intro J
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_forall_mem_pow_smul_tensor (B := B) M I hI J fun k ↦ ?_
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (J : Submodule A A)
  set n := k + c
  let g : J →ₗ[A] A ⧸ I ^ n := (I ^ n).mkQ ∘ₗ J.subtype
  let V := LinearMap.ker g
  let gbar : (J ⧸ V) →ₗ[A] A ⧸ I ^ n := V.liftQ g le_rfl
  have hgbar : Function.Injective gbar := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have htors : Module.IsTorsionBySet A (J ⧸ V) (I ^ n : Ideal A) := by
    rintro y ⟨a, ha⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective V y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    change (I ^ n).mkQ (a • (y : A)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Ideal.mul_mem_right _ _ ha
  let := htors.module
  have := htors.isScalarTower (S := A)
  have := h n
  let gbar' : (J ⧸ V) →ₗ[A ⧸ I ^ n] A ⧸ I ^ n :=
    gbar.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have hinj : Function.Injective ((gbar'.restrictScalars A).rTensor M) :=
    rTensor_injective_of_flat_baseChange (S := A ⧸ I ^ n) gbar' hgbar
  have hx' : V.mkQ.rTensor M x = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    change (g.rTensor M) x = 0
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, hx, map_zero]
  obtain ⟨z, rfl⟩ := (_root_.rTensor_exact M (LinearMap.exact_subtype_mkQ V)
    (Submodule.mkQ_surjective V) x).1 hx'
  refine rTensor_subtype_mem_smul_top (I ^ k) V ?_ z
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

end Module.Flat

namespace IsLocalRing.StrictHenselization

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]

/-- An algebra over the strict henselization is flat if it is flat over the local ring of every
étale neighbourhood. -/
theorem flat_of_forall_flat (B : Type*) [CommRing B] [Algebra (StrictHenselization R K) B]
    (h : ∀ N : EtaleNbhd R K, letI : Algebra N.Stalk B :=
      ((algebraMap (StrictHenselization R K) B).comp (of N : N.Stalk →+* _)).toAlgebra
      Module.Flat N.Stalk B) : Module.Flat (StrictHenselization R K) B := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} hfx ↦ ?_
  obtain ⟨N, g, hg⟩ := exists_of_finite f
  let : Algebra N.Stalk B :=
    ((algebraMap (StrictHenselization R K) B).comp (of N : N.Stalk →+* _)).toAlgebra
  have := h N
  have hsmul (a : N.Stalk) (b : B) : a • b = of N a • b := by
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl
  have hrel : ∑ i, g i • x i = 0 := by
    simpa [hsmul, hg] using hfx
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨k, fun i j ↦ of N (a i j), y, fun i ↦ by simpa [hsmul] using hy i, fun j ↦ ?_⟩
  simp only [← hg, ← map_mul, ← map_sum, ha j, map_zero]

variable [IsLocalRing R] [IsNoetherianRing R] [IsLocalHom (algebraMap R K)]

/-- The strict henselization of a noetherian local ring with respect to any field `K` (with local
structure map) is noetherian (Stacks 06LJ; EGA IV 18.6.6, 18.8.8). -/
instance isNoetherianRing : IsNoetherianRing (StrictHenselization R K) := by
  set C := StrictHenselization R K
  have hfg : (maximalIdeal C).FG := by
    rw [← map_maximalIdeal]
    exact Ideal.FG.map (IsNoetherian.noetherian (maximalIdeal R)) _
  let Ĉ := AdicCompletion (maximalIdeal C) C
  have := AdicCompletion.isLocalRing_of_fg hfg
  have := AdicCompletion.isAdicComplete_of_fg hfg
  have := AdicCompletion.algebraMap_isLocalHom_of_fg hfg
  -- `Ĉ` is noetherian
  have hfg' : (maximalIdeal Ĉ).FG := by
    rw [AdicCompletion.maximalIdeal_eq_map_of_fg hfg]
    exact Ideal.FG.map hfg _
  have : IsNoetherianRing (Ĉ ⧸ maximalIdeal Ĉ) :=
    inferInstanceAs (IsNoetherianRing (ResidueField Ĉ))
  have hnoeth : IsNoetherianRing Ĉ := Ideal.isNoetherianRing_of_isAdicComplete _ hfg'
  -- `Ĉ` is flat over `R`, by the local flatness criterion
  have hflatR : Module.Flat R Ĉ := by
    refine Module.Flat.of_forall_flat_quotient_pow (B := Ĉ) (maximalIdeal R) ?_ fun n ↦ ?_
    · have : IsLocalHom (algebraMap R Ĉ) :=
        inferInstanceAs (IsLocalHom ((algebraMap C Ĉ).comp (algebraMap R C)))
      have h : (maximalIdeal R).map (algebraMap R Ĉ) ≤ maximalIdeal Ĉ :=
        ((local_hom_TFAE (algebraMap R Ĉ)).out 1 3).mp this
      exact h.trans (maximalIdeal_le_jacobson _)
    · set q : Ideal R := maximalIdeal R ^ n
      have hq : q.map (algebraMap R C) = maximalIdeal C ^ n := by
        rw [Ideal.map_pow, map_maximalIdeal]
      let ι : C →ₗ[R] Ĉ := (IsScalarTower.toAlgHom R C Ĉ).toLinearMap
      have hresĈ : (maximalIdeal C ^ n • (⊤ : Submodule C Ĉ)).restrictScalars R =
          q • (⊤ : Submodule R Ĉ) := by
        rw [← hq, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
      have hresC : (maximalIdeal C ^ n • (⊤ : Submodule C C)).restrictScalars R =
          q • (⊤ : Submodule R C) := by
        rw [← hq, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
      have hker (y : Ĉ) : y ∈ q • (⊤ : Submodule R Ĉ) ↔
          AdicCompletion.eval (maximalIdeal C) C n y = 0 := by
        rw [← hresĈ, Submodule.restrictScalars_mem, AdicCompletion.pow_smul_top_eq_ker_eval hfg,
          LinearMap.mem_ker]
      have hmemC (c : C) : c ∈ q • (⊤ : Submodule R C) ↔
          c ∈ maximalIdeal C ^ n • (⊤ : Submodule C C) := by
        rw [← hresC, Submodule.restrictScalars_mem]
      have hle : q • (⊤ : Submodule R C) ≤ (q • (⊤ : Submodule R Ĉ)).comap ι :=
        Submodule.smul_top_le_comap_smul_top q ι
      let μ := Submodule.mapQ _ _ ι hle
      have hμ : Function.Bijective μ := by
        constructor
        · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
          intro z hz
          obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
          rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, hker] at hz
          rw [Submodule.Quotient.mk_eq_zero, hmemC]
          change AdicCompletion.eval _ C n (AdicCompletion.of _ C c) = 0 at hz
          rw [AdicCompletion.eval_of, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero] at hz
          exact hz
        · intro z
          obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
          obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
            (AdicCompletion.eval (maximalIdeal C) C n y)
          refine ⟨Submodule.Quotient.mk c, ?_⟩
          rw [Submodule.mapQ_apply, Submodule.Quotient.eq, hker, map_sub]
          change AdicCompletion.eval _ C n (AdicCompletion.of _ C c) - _ = 0
          rw [AdicCompletion.eval_of, Submodule.mkQ_apply, hc, sub_self]
      let φ : (R ⧸ q) ⊗[R] C →ₗ[R ⧸ q] (R ⧸ q) ⊗[R] Ĉ :=
        AlgebraTensorModule.lTensor (R ⧸ q) (R ⧸ q) ι
      have hφ : Function.Bijective φ := by
        have hcomm : ⇑(quotTensorEquivQuotSMul Ĉ q) ∘ φ = μ ∘ (quotTensorEquivQuotSMul C q) := by
          funext z
          induction z using TensorProduct.induction_on with
          | zero => simp
          | tmul r c =>
            obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
            simp [φ, μ, ι]
          | add x y hx hy =>
            simp only [Function.comp_apply, map_add] at hx hy ⊢
            rw [hx, hy]
        have : Function.Bijective (⇑(quotTensorEquivQuotSMul Ĉ q) ∘ φ) := by
          rw [hcomm]
          exact hμ.comp (quotTensorEquivQuotSMul C q).bijective
        exact (Function.Bijective.of_comp_iff' (quotTensorEquivQuotSMul Ĉ q).bijective _).mp this
      exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective φ hφ).symm
  -- `Ĉ` is flat over `C`
  have hflatC : Module.Flat C Ĉ := flat_of_forall_flat Ĉ fun N ↦ by
    let : Algebra N.Stalk Ĉ := ((algebraMap C Ĉ).comp (of N : N.Stalk →+* C)).toAlgebra
    have : IsScalarTower R N.Stalk Ĉ := .of_algebraMap_eq fun r ↦ by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply]
    exact Algebra.FormallyUnramified.flat_of_restrictScalars R N.Stalk Ĉ
  have : Module.FaithfullyFlat C Ĉ := .of_flat_of_isLocalHom
  exact IsNoetherianRing.of_faithfullyFlat (B := Ĉ)

end IsLocalRing.StrictHenselization

namespace IsLocalRing

/-- Stacks 06LJ: the henselization of a noetherian local ring is noetherian. -/
theorem Henselization.isNoetherianStatement : Henselization.IsNoetherianStatement.{u} :=
  fun _ _ _ _ ↦ inferInstance

/-- The strict henselization of a noetherian local ring is noetherian (Stacks 06LJ). -/
theorem StrictHenselization.isNoetherianStatement :
    StrictHenselization.IsNoetherianStatement.{u} := fun R K _ _ _ _ _ _ _ _ ↦
  have := isLocalHom_algebraMap_of_isScalarTower (R := R) (K := K)
  inferInstance

end IsLocalRing
