/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Etale.Basic

/-!
# SGA 1, Exposé III, §§1–2: formally smooth local homomorphisms

SGA defines (III.1.1) a local homomorphism `A → B` of noetherian local rings with finite
residue extension to be *formally smooth* when, after a finite free local extension `A'`
of the completion of `A`, the local components of `B̂ ⊗ A'` become power series rings
over `A'`. Theorem III.2.1 characterises this by lifting properties; the Remark after
III.2.1 (and EGA 0_IV 19.3.1) takes the lifting property (iii) as the good definition.

Mathlib's `Algebra.FormallySmooth` is the discrete version of that lifting property.
Here we introduce the adic version `AdicFormallySmooth R I`: maps `B → C ⧸ J` killing a
power of `I` lift through every nilpotent ideal `J`. We prove

* the reduction to square-zero ideals (III.2.1 (iv) ⇔ (iv bis), in this setting);
* stability under base change and localization (the content of III.1.4 (i) for this notion);
* III.2.1 (iii) ⇒ (ii): lifting into complete rings, for an `I`-adically complete ring
  `C` and a closed ideal `J`, and in SGA's form for complete noetherian local rings;
* power series rings `R⟦X₁, …, Xₙ⟧` are `(X)`-adically formally smooth (the model
  case of III.1.1 and the key step of III.2.1 (i) ⇒ (iii)), and flat over a noetherian
  `R` (III.1.3 for them);
* Definition III.1.1 itself (stated for complete `A`, `B`), Lemma III.1.3, and the easy half of
  III.1.5 (power series rings are formally smooth in the sense of III.1.1).

III.1.4 (ii) (descent along a finite free extension) is in `Descent.lean`; III.1.5 and the
equivalences of III.2.1 and III.2.2 through Definition III.1.1, for a trivial residue extension,
are in `PowerSeriesStructure.lean`, and for a finite residue extension (with III.1.4 in the form of
Definition III.1.1 and III.1.6) in `LocalComponents.lean` and `LiftingCriteria.lean`;
Proposition III.1.9 (the comparison with smoothness) is in `SmoothLocal.lean`.
-/

universe u v w

namespace SGA.SGA1.ExposeIII

open Ideal

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

variable (R) in
/-- III.2.1 (iii), taken as the definition of formal smoothness in the Remark after III.2.1
(EGA 0_IV 19.3.1): `B` is *formally smooth over `R` for the `I`-adic topology* if every
`R`-algebra map `B → C ⧸ J` which kills a power of `I` (i.e. is continuous for the
discrete topology on `C ⧸ J`), with `J` a nilpotent ideal, lifts to an `R`-algebra map
`B → C`. (Such a lift is automatically continuous.) -/
def AdicFormallySmooth (I : Ideal B) : Prop :=
  ∀ ⦃C : Type v⦄ [CommRing C] [Algebra R C] (J : Ideal C), IsNilpotent J →
    ∀ f : B →ₐ[R] C ⧸ J, (∃ n, I ^ n ≤ RingHom.ker f) →
      ∃ g : B →ₐ[R] C, (Ideal.Quotient.mkₐ R J).comp g = f

namespace AdicFormallySmooth

variable {I I' : Ideal B}

/-- A formally smooth algebra (in the discrete sense of mathlib) is formally smooth for
every adic topology. -/
theorem of_formallySmooth [Algebra.FormallySmooth R B] (I : Ideal B) :
    AdicFormallySmooth R I :=
  fun _ _ _ J hJ f _ ↦ Algebra.FormallySmooth.exists_lift J hJ f

/-- Formal smoothness for the `I`-adic topology only depends on that topology: it passes to
every ideal `I'` containing a power of `I` (the `I'`-adic topology is coarser). -/
theorem of_pow_le (h : AdicFormallySmooth R I) (k : ℕ) (hk : I ^ k ≤ I') :
    AdicFormallySmooth R I' := by
  intro C _ _ J hJ f ⟨n, hn⟩
  exact h J hJ f ⟨k * n, by rw [pow_mul]; exact (Ideal.pow_right_mono hk n).trans hn⟩

/-- Formal smoothness for the `I`-adic topology implies it for a coarser adic topology; e.g.
`(X)`-adic formal smoothness of `R⟦X⟧` gives it for the maximal ideal. -/
theorem mono (h : AdicFormallySmooth R I) (hle : I ≤ I') : AdicFormallySmooth R I' :=
  h.of_pow_le 1 (by simpa using hle)

/-- The lifting property in terms of a surjection `C → D` with nilpotent kernel. -/
theorem exists_lift_of_surjective (h : AdicFormallySmooth R I) {C D : Type v} [CommRing C]
    [CommRing D] [Algebra R C] [Algebra R D] (g : C →ₐ[R] D) (hg : Function.Surjective g)
    (hker : IsNilpotent (RingHom.ker g)) (f : B →ₐ[R] D) (hf : ∃ n, I ^ n ≤ RingHom.ker f) :
    ∃ v : B →ₐ[R] C, g.comp v = f := by
  let e := Ideal.quotientKerAlgEquivOfSurjective hg
  obtain ⟨v, hv⟩ := h (RingHom.ker g) hker (e.symm.toAlgHom.comp f) (by
    obtain ⟨n, hn⟩ := hf
    refine ⟨n, fun x hx ↦ ?_⟩
    simp [RingHom.mem_ker.mp (hn hx)])
  refine ⟨v, AlgHom.ext fun x ↦ ?_⟩
  have := congr(e ($hv x))
  simpa [e, Ideal.quotientKerAlgEquivOfSurjective_mk] using this


/-- III.2.1, (iv bis) ⇒ (iv), for the adic lifting property: it suffices to lift through
square-zero ideals. The proof is the induction on the nilpotency index indicated in SGA. -/
theorem of_sq_zero (h : ∀ ⦃C : Type v⦄ [CommRing C] [Algebra R C] (J : Ideal C), J ^ 2 = ⊥ →
      ∀ f : B →ₐ[R] C ⧸ J, (∃ n, I ^ n ≤ RingHom.ker f) →
        ∃ g : B →ₐ[R] C, (Ideal.Quotient.mkₐ R J).comp g = f) :
    AdicFormallySmooth R I := by
  intro C _ _ J hJ
  revert ‹Algebra R C›
  refine Ideal.IsNilpotent.induction_on (S := C) J hJ
    (P := fun C _ J ↦ ∀ [Algebra R C], IsNilpotent J → ∀ f : B →ₐ[R] C ⧸ J,
      (∃ n, I ^ n ≤ RingHom.ker f) → ∃ g : B →ₐ[R] C, (Ideal.Quotient.mkₐ R J).comp g = f)
    ?_ ?_ hJ
  · intro C _ J hJ _ _ f hf; exact h J hJ f hf
  · intro C _ J K hJK h₁ h₂ _ hK f hf
    let e : ((C ⧸ J) ⧸ K.map (Ideal.Quotient.mk J)) ≃ₐ[R] C ⧸ K :=
      { (DoubleQuot.quotQuotEquivQuotSup J K).trans
          (Ideal.quotEquivOfEq (sup_eq_right.mpr hJK)) with
        commutes' := fun x => rfl }
    have he (y : C) : e (Ideal.Quotient.mk _ (Ideal.Quotient.mk J y)) = Ideal.Quotient.mk K y :=
      rfl
    obtain ⟨m, hm⟩ := hK
    have hJ : IsNilpotent J := ⟨m, eq_bot_iff.mpr ((Ideal.pow_right_mono hJK m).trans hm.le)⟩
    have hK' : (K.map (Ideal.Quotient.mk J)) ^ m = ⊥ := by
      rw [← Ideal.map_pow, hm, Ideal.zero_eq_bot, Ideal.map_bot]
    obtain ⟨n, hn⟩ := hf
    obtain ⟨g', hg'⟩ := h₂ ⟨m, hK'⟩ (e.symm.toAlgHom.comp f) ⟨n, fun x hx ↦ by
      simp [RingHom.mem_ker.mp (hn hx)]⟩
    have h1 : (I ^ n).map g' ≤ K.map (Ideal.Quotient.mk J) := by
      refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ Ideal.mem_comap.mpr ?_
      have := congr($hg' x)
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, RingHom.mem_ker.mp (hn hx),
        map_zero] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    obtain ⟨g, rfl⟩ := h₁ hJ g' ⟨n * m, by
      rw [← Ideal.map_eq_bot_iff_le_ker, pow_mul, Ideal.map_pow]
      exact eq_bot_iff.mpr ((Ideal.pow_right_mono h1 m).trans hK'.le)⟩
    refine ⟨g, AlgHom.ext fun x ↦ ?_⟩
    have := congrArg e (DFunLike.congr_fun hg' x)
    simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_coe,
      AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply, he] using this

/-- III.2.1, (iv) ⇔ (iv bis), for the adic lifting property. -/
theorem iff_sq_zero : AdicFormallySmooth R I ↔
    ∀ ⦃C : Type v⦄ [CommRing C] [Algebra R C] (J : Ideal C), J ^ 2 = ⊥ →
      ∀ f : B →ₐ[R] C ⧸ J, (∃ n, I ^ n ≤ RingHom.ker f) →
        ∃ g : B →ₐ[R] C, (Ideal.Quotient.mkₐ R J).comp g = f :=
  ⟨fun h C _ _ J hJ ↦ h (C := C) J ⟨2, hJ⟩, of_sq_zero⟩

end AdicFormallySmooth

/-- Formal smoothness for the adic topology is invariant under isomorphism. -/
theorem AdicFormallySmooth.of_algEquiv {R : Type*} {B B' : Type u} [CommRing R] [CommRing B]
    [CommRing B'] [Algebra R B] [Algebra R B'] (e : B ≃ₐ[R] B') {I : Ideal B'}
    (h : AdicFormallySmooth R I) : AdicFormallySmooth R (I.comap e) := by
  intro C _ _ J hJ f ⟨n, hn⟩
  obtain ⟨g, hg⟩ := h J hJ (f.comp e.symm.toAlgHom) ⟨n, fun y hy ↦ by
    have hy' : y ∈ ((I.comap e) ^ n).map e := by
      rwa [Ideal.map_pow, Ideal.map_comap_of_surjective _ e.surjective]
    obtain ⟨z, hz, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ e.surjective).1 hy'
    have := hn hz
    simpa using this⟩
  refine ⟨g.comp e.toAlgHom, AlgHom.ext fun b ↦ ?_⟩
  have := congr($hg (e b))
  simpa using this

section Pullback

variable {C : Type v} [CommRing C] [Algebra R C]

/-- The square with vertices `C ⧸ (𝔞 ⊓ 𝔟)`, `C ⧸ 𝔞`, `C ⧸ 𝔟`, `C ⧸ 𝔠` (for `𝔠 = 𝔞 ⊔ 𝔟`) is
cartesian: two maps into `C ⧸ 𝔞` and `C ⧸ 𝔟` which agree in `C ⧸ 𝔠` come from a map into
`C ⧸ (𝔞 ⊓ 𝔟)`. -/
lemma exists_algHom_quotient_inf {𝔞 𝔟 𝔠 : Ideal C} (ha : 𝔞 ≤ 𝔠) (hb : 𝔟 ≤ 𝔠) (hc : 𝔠 ≤ 𝔞 ⊔ 𝔟)
    (f : B →ₐ[R] C ⧸ 𝔞) (g : B →ₐ[R] C ⧸ 𝔟)
    (h : (Ideal.Quotient.factorₐ R ha).comp f = (Ideal.Quotient.factorₐ R hb).comp g) :
    ∃ w : B →ₐ[R] C ⧸ (𝔞 ⊓ 𝔟), (Ideal.Quotient.factorₐ R inf_le_left).comp w = f ∧
      (Ideal.Quotient.factorₐ R inf_le_right).comp w = g := by
  let ψ : C ⧸ (𝔞 ⊓ 𝔟) →ₐ[R] (C ⧸ 𝔞) × (C ⧸ 𝔟) :=
    (Ideal.Quotient.factorₐ R inf_le_left).prod (Ideal.Quotient.factorₐ R inf_le_right)
  have hψ : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).mpr fun x hx ↦ ?_
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [ψ, AlgHom.prod_apply, Prod.mk_eq_zero, Ideal.Quotient.factorₐ_apply,
      Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ⟨hx.1, hx.2⟩
  have hrange (x : B) : (f x, g x) ∈ ψ.range := by
    obtain ⟨c₁, hc₁⟩ := Ideal.Quotient.mk_surjective (f x)
    obtain ⟨c₂, hc₂⟩ := Ideal.Quotient.mk_surjective (g x)
    have : c₁ - c₂ ∈ 𝔞 ⊔ 𝔟 := by
      refine hc (Ideal.Quotient.eq.mp ?_)
      have := congr($h x)
      simp only [AlgHom.comp_apply, ← hc₁, ← hc₂, Ideal.Quotient.factorₐ_apply,
        Ideal.Quotient.factor_mk] at this
      exact this
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp this
    refine ⟨Ideal.Quotient.mk _ (c₁ - a), Prod.ext ?_ ?_⟩
    · change Ideal.Quotient.mk 𝔞 (c₁ - a) = f x
      rw [← hc₁, Ideal.Quotient.eq]; simpa using ha
    · change Ideal.Quotient.mk 𝔟 (c₁ - a) = g x
      rw [← hc₂, Ideal.Quotient.eq, show c₁ - a - c₂ = b by linear_combination -hab]; exact hb
  let w : B →ₐ[R] C ⧸ (𝔞 ⊓ 𝔟) :=
    (AlgEquiv.ofInjective ψ hψ).symm.toAlgHom.comp ((f.prod g).codRestrict ψ.range hrange)
  have hw (x : B) : ψ (w x) = (f x, g x) := by
    have := AlgEquiv.ofInjective_apply ψ hψ (w x)
    simp only [w, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] at this
    exact this.symm
  exact ⟨w, AlgHom.ext fun x ↦ congr_arg Prod.fst (hw x),
    AlgHom.ext fun x ↦ congr_arg Prod.snd (hw x)⟩

end Pullback

namespace AdicFormallySmooth

variable {I : Ideal B} {C : Type v} [CommRing C] [Algebra R C]

/-- The lifting property used in the proof of III.2.1, (iii) ⇒ (ii), for the test rings
`C ⧸ Kᵠ⁺¹`: maps `B → C ⧸ J'`, with `Kᵠ⁺¹ ⊆ J' ⊆ K` and `J' ⧸ Kᵠ⁺¹` of square zero, which kill
a power of `I`, lift to `C ⧸ Kᵠ⁺¹`. -/
def LiftsModPow (R : Type u) {B : Type v} [CommRing R] [CommRing B] [Algebra R B] (I : Ideal B)
    {C : Type v} [CommRing C] [Algebra R C] (K : Ideal C) : Prop :=
  ∀ (q : ℕ) (J' : Ideal C) (hle : K ^ (q + 1) ≤ J'), J' ≤ K →
    RingHom.ker (Ideal.Quotient.factorₐ R hle) ^ 2 = ⊥ →
      ∀ w : B →ₐ[R] C ⧸ J', (∃ n, I ^ n ≤ RingHom.ker w) →
        ∃ v : B →ₐ[R] C ⧸ K ^ (q + 1), (Ideal.Quotient.factorₐ R hle).comp v = w

/-- Formal smoothness for the `I`-adic topology gives the lifting property for the test rings
`C ⧸ Kᵠ⁺¹`. -/
lemma liftsModPow (h : AdicFormallySmooth R I) (K : Ideal C) : LiftsModPow R I K :=
  fun _ _ hle _ hsq w hw ↦ h.exists_lift_of_surjective (Ideal.Quotient.factorₐ R hle)
    (Ideal.Quotient.factor_surjective hle) ⟨2, hsq⟩ w hw

/-- The inductive step of III.2.1, (iii) ⇒ (ii): a lift `v` of `u` modulo `J + Kᵠ` to
`C ⧸ Kᵠ` extends to a lift modulo `J + Kᵠ⁺¹` to `C ⧸ Kᵠ⁺¹`. As in SGA, one glues `u` and
`v` to a map into `C ⧸ ((J + Kᵠ⁺¹) ∩ Kᵠ)` and lifts it through a square-zero ideal. -/
private lemma exists_lift_step {J K : Ideal C} (h : LiftsModPow R I K) (hJK : J ≤ K)
    (u : B →ₐ[R] C ⧸ J) (hu : I.map u ≤ K.map (Ideal.Quotient.mk J)) (q : ℕ)
    (v : B →ₐ[R] C ⧸ K ^ q)
    (hv : (Ideal.Quotient.factorₐ R (le_sup_right : K ^ q ≤ J ⊔ K ^ q)).comp v =
      (Ideal.Quotient.factorₐ R (le_sup_left : J ≤ J ⊔ K ^ q)).comp u) :
    ∃ v' : B →ₐ[R] C ⧸ K ^ (q + 1),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right q.le_succ)).comp v' = v ∧
      (Ideal.Quotient.factorₐ R (le_sup_right : K ^ (q + 1) ≤ J ⊔ K ^ (q + 1))).comp v' =
        (Ideal.Quotient.factorₐ R (le_sup_left : J ≤ J ⊔ K ^ (q + 1))).comp u := by
  have hKq : K ^ (q + 1) ≤ K := Ideal.pow_le_self q.succ_ne_zero
  have ha : J ⊔ K ^ (q + 1) ≤ J ⊔ K ^ q := sup_le_sup_left (Ideal.pow_le_pow_right q.le_succ) J
  have hc : J ⊔ K ^ q ≤ (J ⊔ K ^ (q + 1)) ⊔ K ^ q :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  obtain ⟨w, hw₁, hw₂⟩ := exists_algHom_quotient_inf ha le_sup_right hc
    ((Ideal.Quotient.factorₐ R le_sup_left).comp u) v (by
      rw [hv, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp])
  -- `u` and `v` map `I ^ (q + 1)` to zero
  have hu' : (I ^ (q + 1)).map u ≤ (K ^ (q + 1)).map (Ideal.Quotient.mk J) := by
    rw [Ideal.map_pow, Ideal.map_pow]; exact Ideal.pow_right_mono hu _
  have hvI : I.map v ≤ K.map (Ideal.Quotient.mk (K ^ q)) := by
    rcases q with - | q
    · intro x _
      have : Subsingleton (C ⧸ K ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
      rw [Subsingleton.elim x 0]; exact zero_mem _
    refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ Ideal.mem_comap.mpr ?_
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (v x)
    obtain ⟨k, hk, hk'⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
      (hu (Ideal.mem_map_of_mem u hx))
    have := congr($hv x)
    simp only [AlgHom.comp_apply, ← hc, ← hk', Ideal.Quotient.factorₐ_apply,
      Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at this
    have hcK : c ∈ K := by
      have := sup_le hJK (Ideal.pow_le_self q.succ_ne_zero) this
      simpa using K.add_mem this hk
    rw [← hc]; exact Ideal.mem_map_of_mem _ hcK
  have hv' : (I ^ (q + 1)).map v = ⊥ := by
    refine eq_bot_iff.mpr ?_
    rw [Ideal.map_pow]
    refine (Ideal.pow_right_mono hvI _).trans ?_
    rw [← Ideal.map_pow]
    refine (Ideal.map_mono (Ideal.pow_le_pow_right q.le_succ)).trans ?_
    rw [Ideal.map_quotient_self]
  have hwI : I ^ (q + 1) ≤ RingHom.ker w := by
    intro x hx
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (w x)
    have h₁ := congr($hw₁ x)
    have h₂ := congr($hw₂ x)
    simp only [AlgHom.comp_apply, ← hc, Ideal.Quotient.factorₐ_apply,
      Ideal.Quotient.factor_mk] at h₁ h₂
    have hc₁ : c ∈ J ⊔ K ^ (q + 1) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, h₁]
      obtain ⟨k, hk, hk'⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
        (hu' (Ideal.mem_map_of_mem u hx))
      rw [← hk', Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact (le_sup_right : K ^ (q + 1) ≤ J ⊔ K ^ (q + 1)) hk
    have hc₂ : c ∈ K ^ q := by
      have := Ideal.mem_map_of_mem v hx
      rw [hv', Ideal.mem_bot] at this
      rw [← Ideal.Quotient.eq_zero_iff_mem, h₂, this]
    rw [RingHom.mem_ker, ← hc, Ideal.Quotient.eq_zero_iff_mem]
    exact ⟨hc₁, hc₂⟩
  -- the kernel of `C ⧸ K ^ (q + 1) → C ⧸ (𝔞 ⊓ 𝔟)` is square zero
  have hle : K ^ (q + 1) ≤ (J ⊔ K ^ (q + 1)) ⊓ K ^ q :=
    le_inf le_sup_right (Ideal.pow_le_pow_right q.le_succ)
  have hnil : RingHom.ker (Ideal.Quotient.factorₐ R hle) ^ 2 = ⊥ := by
    refine eq_bot_iff.mpr ?_
    have hker : RingHom.ker (Ideal.Quotient.factorₐ R hle) ≤
        ((J ⊔ K ^ (q + 1)) ⊓ K ^ q).map (Ideal.Quotient.mk (K ^ (q + 1))) := by
      intro y hy
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [RingHom.mem_ker, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk,
        Ideal.Quotient.eq_zero_iff_mem] at hy
      exact Ideal.mem_map_of_mem _ hy
    refine (Ideal.pow_right_mono hker 2).trans ?_
    rw [← Ideal.map_pow, ← Ideal.map_quotient_self (K ^ (q + 1))]
    refine Ideal.map_mono ?_
    rw [pow_two]
    exact (Ideal.mul_mono (inf_le_left.trans (sup_le hJK hKq)) inf_le_right).trans_eq
      (pow_succ' K q).symm
  obtain ⟨v', hv'⟩ := h q _ hle (inf_le_left.trans (sup_le hJK hKq)) hnil w ⟨q + 1, hwI⟩
  refine ⟨v', ?_, ?_⟩
  · rw [← hw₂, ← hv', ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
  · rw [← hw₁, ← hv', ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]

/-- III.2.1, (iii) ⇒ (ii), with the lifting property only for the test rings `C ⧸ Kᵠ⁺¹`
(`LiftsModPow`): if `C` is `K`-adically complete and `J ≤ K` is closed for the `K`-adic topology,
then every map `u : B → C ⧸ J` sending `I` into `K` lifts to `B → C`. -/
theorem exists_lift_of_liftsModPow (K : Ideal C) (h : LiftsModPow R I K)
    [IsAdicComplete K C] {J : Ideal C} (hJK : J ≤ K) (hJ : ∀ c, (∀ q, c ∈ J ⊔ K ^ q) → c ∈ J)
    (u : B →ₐ[R] C ⧸ J) (hu : I.map u ≤ K.map (Ideal.Quotient.mk J)) :
    ∃ v : B →ₐ[R] C, (Ideal.Quotient.mkₐ R J).comp v = u := by
  let P (q : ℕ) (v : B →ₐ[R] C ⧸ K ^ q) : Prop :=
    (Ideal.Quotient.factorₐ R (le_sup_right : K ^ q ≤ J ⊔ K ^ q)).comp v =
      (Ideal.Quotient.factorₐ R (le_sup_left : J ≤ J ⊔ K ^ q)).comp u
  have step (q : ℕ) (v : {v // P q v}) := exists_lift_step h hJK u hu q v.1 v.2
  have : Subsingleton (C ⧸ K ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
  have : Subsingleton (C ⧸ (J ⊔ K ^ 0)) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
  let v₀ : {v // P 0 v} := ⟨default, AlgHom.ext fun _ ↦ Subsingleton.elim _ _⟩
  let seq : (q : ℕ) → {v // P q v} := fun q ↦
    Nat.rec v₀ (fun q v ↦ ⟨(step q v).choose, (step q v).choose_spec.2⟩) q
  have hseq (q : ℕ) : (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right q.le_succ)).comp
      (seq (q + 1)).1 = (seq q).1 := (step q (seq q)).choose_spec.1
  have compat {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (seq n).1 = (seq m).1 := by
    induction n, hmn using Nat.le_induction with
    | base => rw [Ideal.Quotient.factorₐ_refl]; rfl
    | succ n hmn ih =>
      rw [← ih, ← hseq n, ← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp]
  let v : B →ₐ[R] C := ((AdicCompletion.ofAlgEquiv K).symm.toAlgHom.restrictScalars R).comp
    (AdicCompletion.liftAlgHom K (fun n ↦ (seq n).1) compat)
  have hv (q : ℕ) (x : B) : Ideal.Quotient.mk (K ^ q) (v x) = (seq q).1 x := by
    simp [v]
  refine ⟨v, AlgHom.ext fun x ↦ ?_⟩
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (u x)
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← hc, Ideal.Quotient.eq]
  refine hJ _ fun q ↦ ?_
  have := congr($((seq q).2) x)
  simp only [AlgHom.comp_apply, ← hv, ← hc, Ideal.Quotient.factorₐ_apply,
    Ideal.Quotient.factor_mk] at this
  exact Ideal.Quotient.eq.mp this

/-- III.2.1, (iii) ⇒ (ii), in general form: if `B` is formally smooth for the `I`-adic
topology, `C` is `K`-adically complete, and `J ≤ K` is closed for the `K`-adic topology,
then every map `u : B → C ⧸ J` sending `I` into `K` lifts to `B → C`. -/
theorem exists_lift_of_isAdicComplete (h : AdicFormallySmooth R I) (K : Ideal C)
    [IsAdicComplete K C] {J : Ideal C} (hJK : J ≤ K) (hJ : ∀ c, (∀ q, c ∈ J ⊔ K ^ q) → c ∈ J)
    (u : B →ₐ[R] C ⧸ J) (hu : I.map u ≤ K.map (Ideal.Quotient.mk J)) :
    ∃ v : B →ₐ[R] C, (Ideal.Quotient.mkₐ R J).comp v = u :=
  exists_lift_of_liftsModPow K (h.liftsModPow K) hJK hJ u hu

/-- III.2.1, (iii) ⇒ (ii): if `B` is local and formally smooth for its `𝔯(B)`-adic topology,
then every local homomorphism `B → C ⧸ J`, with `C` a complete noetherian local ring and
`J` a proper ideal, lifts to `B → C`. -/
theorem exists_lift_of_isLocalRing [IsLocalRing B]
    (h : AdicFormallySmooth R (IsLocalRing.maximalIdeal B))
    [IsLocalRing C] [IsNoetherianRing C] [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    {J : Ideal C} (hJ : J ≠ ⊤) (u : B →ₐ[R] C ⧸ J) [IsLocalHom u] :
    ∃ v : B →ₐ[R] C, (Ideal.Quotient.mkₐ R J).comp v = u := by
  refine h.exists_lift_of_isAdicComplete _ (IsLocalRing.le_maximalIdeal hJ) (fun c hc ↦ ?_) u ?_
  · have hK := (IsLocalRing.maximalIdeal C).iInf_pow_smul_eq_bot_of_isLocalRing (M := C ⧸ J)
      (IsLocalRing.maximalIdeal.isMaximal C).ne_top
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk J c ∈ (⨅ i : ℕ, IsLocalRing.maximalIdeal C ^ i • ⊤ :
        Submodule C (C ⧸ J)) := by
      refine Submodule.mem_iInf _ |>.mpr fun q ↦ ?_
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hc q)
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
      have := Submodule.smul_mem_smul hb (Submodule.mem_top (x := (1 : C ⧸ J)))
      simpa [Algebra.smul_def] using this
    rwa [hK] at this
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ Ideal.mem_comap.mpr ?_
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (u x)
    rw [← hc]
    refine Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr fun hunit ↦ ?_)
    have : IsUnit (u x) := hc ▸ hunit.map _
    exact (IsLocalRing.mem_maximalIdeal _).mp hx (isUnit_of_map_unit u x this)

end AdicFormallySmooth


section PowerSeries

open MvPowerSeries

variable {R : Type u} [CommRing R] {σ : Type w} [Finite σ]

/-- The ideal of the variables of `R⟦X⟧` corresponds to that of `R[X]` in its completion. -/
lemma map_toAdicCompletionAlgEquiv_span_X :
    Ideal.map (toAdicCompletionAlgEquiv σ R).toRingEquiv (Ideal.span (Set.range X)) =
      (MvPolynomial.idealOfVars σ R).map (algebraMap _ _) := by
  simp_rw [Ideal.map_span, ← Set.range_comp]
  congr 2; ext1
  simp [AdicCompletion.algebraMap_apply, ← MvPolynomial.coe_X, toAdicCompletion_coe]

lemma truncTotalAlgHom_X (n : ℕ) (i : σ) :
    truncTotalAlgHom σ R n (X i) = Ideal.Quotient.mk _ (MvPolynomial.X i) := by
  have := (truncTotalAlgHom σ R n).commutes (MvPolynomial.X i)
  rwa [MvPowerSeries.algebraMap_apply', MvPolynomial.coe_X] at this

/-- Truncation in total degree `< n` identifies `R⟦X⟧ ⧸ (X)ⁿ` with `R[X] ⧸ (X)ⁿ`: its
kernel is the `n`-th power of the ideal of the variables. -/
lemma ker_truncTotalAlgHom (n : ℕ) :
    RingHom.ker (truncTotalAlgHom σ R n) = Ideal.span (Set.range X) ^ n := by
  refine le_antisymm (fun F hF ↦ ?_) ?_
  · set e := (toAdicCompletionAlgEquiv σ R).toRingEquiv
    rw [← Ideal.apply_mem_of_equiv_iff (f := e), Ideal.map_pow,
      map_toAdicCompletionAlgEquiv_span_X, ← Ideal.map_pow]
    have h1 : e F ∈ (MvPolynomial.idealOfVars σ R ^ n • ⊤ :
        Submodule (MvPolynomial σ R) (AdicCompletion _ (MvPolynomial σ R))) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.idealOfVars_fg σ R),
        LinearMap.mem_ker, AdicCompletion.eval_apply]
      change (toAdicCompletion σ R F).val n = 0
      rw [toAdicCompletion_apply_eq_mk_truncTotal, Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul,
        Ideal.mul_top]
      rw [RingHom.mem_ker, truncTotalAlgHom_apply, Ideal.Quotient.eq_zero_iff_mem] at hF
      exact hF
    rw [Ideal.smul_top_eq_map] at h1
    exact h1
  · rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, Ideal.map_span, ← Set.range_comp]
    have hle : Ideal.span (Set.range (truncTotalAlgHom σ R n ∘ X)) ≤
        (MvPolynomial.idealOfVars σ R).map (Ideal.Quotient.mk _) := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      simp only [Function.comp_apply, truncTotalAlgHom_X]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
    refine eq_bot_iff.mpr ((Ideal.pow_right_mono hle n).trans ?_)
    rw [← Ideal.map_pow, Ideal.map_quotient_self]

/-- III.2.1, (i) ⇒ (iii), for the model algebras of Definition III.1.1: a power series ring
`R⟦X₁, …, Xₙ⟧` is formally smooth over `R` for its `(X)`-adic topology. As in SGA, one lifts
the images of the variables arbitrarily; they are nilpotent, so evaluation at them is
defined on a truncation. -/
theorem adicFormallySmooth_mvPowerSeries :
    AdicFormallySmooth R (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) := by
  intro C _ _ J hJ f ⟨N, hN⟩
  choose z hz using fun i ↦ Ideal.Quotient.mk_surjective (f (X i))
  obtain ⟨m, hm⟩ := hJ
  have hz_nil (i : σ) : IsNilpotent (z i) := by
    have : z i ^ N ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, hz, ← map_pow]
      exact hN (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) N)
    refine ⟨N * m, ?_⟩
    rw [pow_mul, ← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hm]
    exact Ideal.pow_mem_pow this m
  obtain ⟨K, hK⟩ : IsNilpotent (Ideal.span (Set.range z)) :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range z))).mpr
      (Ideal.span_le.mpr (Set.range_subset_iff.mpr fun i ↦ mem_nilradical.mpr (hz_nil i)))
  set M := max K N
  have hφ : ∀ a ∈ MvPolynomial.idealOfVars σ R ^ M, MvPolynomial.aeval z a = 0 := by
    intro a ha
    have : (MvPolynomial.idealOfVars σ R ^ M).map (MvPolynomial.aeval z) = ⊥ := by
      rw [Ideal.map_pow, Ideal.map_span, ← Set.range_comp]
      simp only [Function.comp_def, MvPolynomial.aeval_X]
      refine eq_bot_iff.mpr ((Ideal.pow_le_pow_right (le_max_left K N)).trans ?_)
      rw [hK]; rfl
    rw [← Ideal.mem_bot, ← this]
    exact Ideal.mem_map_of_mem _ ha
  let φ : MvPolynomial σ R ⧸ MvPolynomial.idealOfVars σ R ^ M →ₐ[R] C :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval z) hφ
  refine ⟨φ.comp ((truncTotalAlgHom σ R M).restrictScalars R), AlgHom.ext fun F ↦ ?_⟩
  have key (p : MvPolynomial σ R) :
      Ideal.Quotient.mk J (MvPolynomial.aeval z p) = f p := by
    induction p using MvPolynomial.induction_on with
    | C r =>
      rw [MvPolynomial.aeval_C, MvPolynomial.coe_C, MvPowerSeries.c_eq_algebraMap, AlgHom.commutes,
        Ideal.Quotient.mk_algebraMap]
    | add p q hp hq => rw [map_add, map_add, hp, hq, MvPolynomial.coe_add, map_add]
    | mul_X p i hp =>
      rw [map_mul, map_mul, hp, MvPolynomial.aeval_X, hz, MvPolynomial.coe_mul, map_mul,
        MvPolynomial.coe_X]
  have hdiff : F - (truncTotal M F : MvPowerSeries σ R) ∈ RingHom.ker f := by
    refine hN ((Ideal.pow_le_pow_right (le_max_right K N)) ?_)
    rw [← ker_truncTotalAlgHom, RingHom.mem_ker, map_sub, sub_eq_zero]
    have := (truncTotalAlgHom σ R M).commutes (truncTotal M F)
    rw [MvPowerSeries.algebraMap_apply', Algebra.algebraMap_self, MvPowerSeries.map_id,
      RingHom.id_apply] at this
    rw [this, truncTotalAlgHom_apply]
    rfl
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hdiff
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', truncTotalAlgHom_apply,
    Ideal.Quotient.mkₐ_eq_mk, φ, Ideal.Quotient.liftₐ_apply]
  rw [hdiff, ← key]
  rfl

/-- III.1.3 for the model algebras: `R⟦X₁, …, Xₙ⟧` is flat over a noetherian ring `R` (it is
the completion of `R[X₁, …, Xₙ]`). -/
instance flat_mvPowerSeries [IsNoetherianRing R] : Module.Flat R (MvPowerSeries σ R) := by
  have : Module.Flat (MvPolynomial σ R) (MvPowerSeries σ R) :=
    Module.Flat.of_linearEquiv (toAdicCompletionAlgEquiv σ R).toLinearEquiv
  exact Module.Flat.trans R (MvPolynomial σ R) (MvPowerSeries σ R)

end PowerSeries


open scoped TensorProduct

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- III.1.1: `B` is formally smooth over `A` if, for some finite free local `A`-algebra `A'`,
the local components of `A' ⊗[A] B` are `A'`-isomorphic to power series rings over `A'`.

SGA applies this to the completions `Â → B̂` of a local homomorphism of noetherian local
rings with finite residue extension (by Remark III.1.2 the notion only depends on them); we
state it for `A`, `B` themselves, so it is SGA's definition when `A` and `B` are complete.
The local components of the complete semilocal ring `A' ⊗[A] B` are its localizations at
maximal ideals. -/
def FormallySmoothLocal : Prop :=
  ∃ (A' : Type u) (_ : CommRing A') (_ : IsLocalRing A') (_ : Algebra A A')
    (_ : Module.Finite A A') (_ : Module.Free A A'),
    ∀ (P : Ideal (A' ⊗[A] B)) [P.IsMaximal],
      ∃ n : ℕ, Nonempty (Localization.AtPrime P ≃ₐ[A'] MvPowerSeries (Fin n) A')

variable {A B}

/-- III.1.3: a formally smooth local algebra is flat. As in SGA, `A' ⊗[A] B` is flat over
`A'` since its localizations are power series rings, and flatness descends along the
faithfully flat extension `A → A'`. -/
theorem FormallySmoothLocal.flat [IsNoetherianRing A] (h : FormallySmoothLocal A B) :
    Module.Flat A B := by
  obtain ⟨A', _, _, _, _, _, hA'⟩ := h
  have : IsNoetherianRing A' := IsNoetherianRing.of_finite A A'
  have : Module.Flat A' (A' ⊗[A] B) := by
    refine Module.flat_of_isLocalized_maximal (A' ⊗[A] B) (A' ⊗[A] B)
      (fun P _ ↦ Localization.AtPrime P) (fun P _ ↦ Algebra.linearMap _ _) fun P _ ↦ ?_
    obtain ⟨n, ⟨e⟩⟩ := hA' P
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  exact Module.Flat.of_flat_tensorProduct A B A'

/-- III.1.5, sufficiency (with `Â = A`, `B̂ = B`): a power series ring over a local ring `A` is
formally smooth over `A` in the sense of Definition III.1.1 (take `A' = A`). -/
theorem formallySmoothLocal_mvPowerSeries (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    FormallySmoothLocal A (MvPowerSeries (Fin n) A) := by
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun P _ ↦ ⟨n, ⟨?_⟩⟩⟩
  have : Nontrivial (A ⊗[A] MvPowerSeries (Fin n) A) :=
    (Algebra.TensorProduct.lid A (MvPowerSeries (Fin n) A)).toRingEquiv.nontrivial
  have : IsLocalRing (A ⊗[A] MvPowerSeries (Fin n) A) :=
    .of_surjective' (Algebra.TensorProduct.lid A (MvPowerSeries (Fin n) A)).symm.toRingHom
      (Algebra.TensorProduct.lid A (MvPowerSeries (Fin n) A)).symm.surjective
  have hP : P = IsLocalRing.maximalIdeal _ := IsLocalRing.eq_maximalIdeal ‹_›
  have hunit : P.primeCompl ≤ IsUnit.submonoid (A ⊗[A] MvPowerSeries (Fin n) A) := by
    intro y hy
    have hy' : y ∉ IsLocalRing.maximalIdeal _ := hP ▸ hy
    exact (IsLocalRing.notMem_maximalIdeal.mp hy' : IsUnit y)
  exact ((IsLocalization.atUnits (A ⊗[A] MvPowerSeries (Fin n) A) P.primeCompl
    hunit).symm.restrictScalars A).trans (Algebra.TensorProduct.lid A (MvPowerSeries (Fin n) A))

/-- Remark III.1.2: formally étale means formally smooth and formally unramified (for the
discrete topology; SGA says "formally smooth and quasi-finite" in the local setting). -/
theorem formallyEtale_iff_formallyUnramified_and_formallySmooth {R : Type u} {B : Type v}
    [CommRing R] [CommRing B] [Algebra R B] :
    Algebra.FormallyEtale R B ↔ Algebra.FormallyUnramified R B ∧ Algebra.FormallySmooth R B :=
  Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth

namespace AdicFormallySmooth

section BaseChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {I : Ideal B}

/-- An element which is a unit modulo a nilpotent ideal is a unit. -/
lemma isUnit_of_isUnit_mk {C : Type*} [CommRing C] {J : Ideal C} (hJ : IsNilpotent J) {c : C}
    (h : IsUnit (Ideal.Quotient.mk J c)) : IsUnit c := by
  obtain ⟨d, hd⟩ := h.exists_right_inv
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
  have hmem : c * d - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hd, map_one, sub_self]
  obtain ⟨n, hn⟩ := hJ
  have : IsNilpotent (c * d - 1) := ⟨n, by
    have := Ideal.pow_mem_pow hmem n
    rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at this⟩
  exact isUnit_of_mul_isUnit_left (by simpa using this.isUnit_add_one)

/-- III.1.4 (i), for the adic lifting property: formal smoothness is preserved by base change
`A → A'` (SGA takes `A'` finite local, and then passes to the local components). -/
theorem baseChange (h : AdicFormallySmooth A I) (A' : Type u) [CommRing A'] [Algebra A A'] :
    AdicFormallySmooth A' (I.map (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B)) := by
  intro C _ _ J hJ f ⟨n, hn⟩
  let : Algebra A C := Algebra.compHom C (algebraMap A A')
  have : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq' rfl
  let f' : B →ₐ[A] C ⧸ J := (f.restrictScalars A).comp Algebra.TensorProduct.includeRight
  obtain ⟨g, hg⟩ := h J hJ f' ⟨n, fun x hx ↦ by
    rw [RingHom.mem_ker]
    exact hn (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hx)⟩
  refine ⟨Algebra.TensorProduct.lift (Algebra.ofId A' C) g fun _ _ ↦ Commute.all _ _, ?_⟩
  refine Algebra.TensorProduct.ext (AlgHom.ext fun a ↦ ?_) (AlgHom.ext fun b ↦ ?_)
  · have : a ⊗ₜ[A] (1 : B) = algebraMap A' (A' ⊗[A] B) a := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.lift_tmul, map_one, mul_one, Algebra.ofId_apply,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_algebraMap]
    rw [this, f.commutes]
  · have := congr($hg b)
    simpa [f'] using this

/-- III.1.4 (i), local components: formal smoothness for the adic lifting property passes to
localizations, with the induced ideal. -/
theorem localization (h : AdicFormallySmooth A I) (M : Submonoid B) (Bₘ : Type u) [CommRing Bₘ]
    [Algebra B Bₘ] [Algebra A Bₘ] [IsScalarTower A B Bₘ] [IsLocalization M Bₘ] :
    AdicFormallySmooth A (I.map (algebraMap B Bₘ)) := by
  intro C _ _ J hJ f ⟨n, hn⟩
  let f' : B →ₐ[A] C ⧸ J := f.comp (IsScalarTower.toAlgHom A B Bₘ)
  obtain ⟨g, hg⟩ := h J hJ f' ⟨n, fun x hx ↦ by
    rw [RingHom.mem_ker]
    exact hn (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hx)⟩
  have hunit (m : M) : IsUnit (g m) := by
    refine isUnit_of_isUnit_mk hJ ?_
    have := congr($hg m)
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    rw [this]
    exact (IsLocalization.map_units Bₘ m).map f
  refine ⟨IsLocalization.liftAlgHom (M := M) (S := Bₘ) hunit, ?_⟩
  have : ((Ideal.Quotient.mkₐ A J).comp (IsLocalization.liftAlgHom (M := M) (S := Bₘ) hunit) :
      Bₘ →+* C ⧸ J) = (f : Bₘ →+* C ⧸ J) := by
    refine IsLocalization.ringHom_ext M (RingHom.ext fun b ↦ ?_)
    have := congr($hg b)
    simpa [f'] using this
  exact AlgHom.coe_ringHom_injective this

end BaseChange

end AdicFormallySmooth


end SGA.SGA1.ExposeIII
