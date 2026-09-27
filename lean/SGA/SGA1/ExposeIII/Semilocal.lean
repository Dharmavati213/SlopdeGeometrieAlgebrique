/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.FormallySmooth
import SGA.Foundations.Formal.AdicRing
import SGA.Foundations.HenselianLifting
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Local components of complete semi-local rings

SGA uses throughout §§1–2 of Exposé III that for a finite local algebra `A'` over a complete
noetherian local ring `A`, and `B` complete local over `A`, the semi-local ring `B' = A' ⊗ B` is
"a direct sum of complete local rings", its *local components*, which are its localizations at
its maximal ideals. Here:

* `HenselianRing.exists_isIdempotentElem_mk_eq`: idempotents lift along an ideal `I` for which
  `R` is henselian (e.g. `R` is `I`-adically complete);
* `exists_completeOrthogonalIdempotents`: if moreover `R ⧸ I` is artinian, the maximal ideals
  `P` of `R` correspond to a complete family of orthogonal idempotents `e_P` with `e_P ∉ P` and
  `e_P ∈ Q` for `Q ≠ P`;
* `isLocalization_atPrime_quotient`: `R ⧸ (1 - e_P)` is the localization of `R` at `P`;
* `AdicFormallySmooth.of_completeOrthogonalIdempotents`, `AdicFormallySmooth.of_localization`:
  formal smoothness (for the lifting property of III.2.1 (iii)) can be checked on the local
  components, and `AdicFormallySmooth.quotient_span_one_sub` passes to them;
* `isAdicComplete_map_of_finite`, `isArtinianRing_quotient_map_maximalIdeal`: a finite algebra
  over a complete noetherian local ring is complete and semi-local in this sense.
-/

universe u v

open Polynomial IsLocalRing

namespace SGA.SGA1.ExposeIII

section Idempotents

variable {R : Type*} [CommRing R]

/-- Idempotents lift along an ideal `I` for which `R` is henselian: `X² - X` has a simple root
modulo `I` at any lift of an idempotent (Stacks 09XI). -/
theorem HenselianRing.exists_isIdempotentElem_mk_eq (I : Ideal R) [HenselianRing R I]
    {ē : R ⧸ I} (hē : IsIdempotentElem ē) :
    ∃ e : R, IsIdempotentElem e ∧ Ideal.Quotient.mk I e = ē := by
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective ē
  have hmon : (X ^ 2 - X : R[X]).Monic :=
    monic_X_pow_sub (degree_X_le.trans_lt (by exact_mod_cast one_lt_two))
  have hē' : Ideal.Quotient.mk I a₀ * Ideal.Quotient.mk I a₀ = Ideal.Quotient.mk I a₀ := hē
  obtain ⟨a, ha, haI⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 - X) hmon a₀ (by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [eval_sub, eval_pow, eval_X, map_sub, map_pow]
    rw [sq, hē', sub_self]) (by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (2 * a₀ - 1)) ?_
    have h2 : Ideal.Quotient.mk I (2 : R) = 2 := map_ofNat _ 2
    simp only [map_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C,
      eval_X, eval_one, map_mul, map_one, Nat.cast_ofNat, h2, Nat.reduceSub, pow_one]
    linear_combination 4 * hē')
  refine ⟨a, ?_, (Ideal.Quotient.eq.mpr haI)⟩
  have : a ^ 2 - a = 0 := by simpa using ha
  rw [IsIdempotentElem]
  linear_combination this

/-- An element lying in every maximal ideal lies in the Jacobson radical. -/
lemma mem_jacobson_bot_of_forall {x : R} (h : ∀ M : Ideal R, M.IsMaximal → x ∈ M) :
    x ∈ Ideal.jacobson ⊥ := by
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro J ⟨-, hJ⟩
  exact h J hJ

lemma le_of_le_jacobson {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥) (M : Ideal R) [hM : M.IsMaximal] :
    I ≤ M :=
  hI.trans (sInf_le ⟨bot_le, hM⟩)

variable (I : Ideal R) [HenselianRing R I] [IsArtinianRing (R ⧸ I)]
include I

/-- If `R` is henselian along `I` and `R ⧸ I` is artinian, then for every maximal ideal `P` of
`R` there is an idempotent `e ∉ P` lying in every other maximal ideal. -/
theorem exists_isIdempotentElem_notMem_forall_mem (P : Ideal R) [P.IsMaximal] :
    ∃ e : R, IsIdempotentElem e ∧ e ∉ P ∧ ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → e ∈ Q := by
  have hle (Q : Ideal R) [Q.IsMaximal] : I ≤ Q := le_of_le_jacobson HenselianRing.jac Q
  have hker (Q : Ideal R) [Q.IsMaximal] : RingHom.ker (Ideal.Quotient.mk I) ≤ Q := by
    rw [Ideal.mk_ker]; exact hle Q
  have hprime (Q : Ideal R) [Q.IsMaximal] : (Q.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker Q)
  obtain ⟨r, hrP, hr, hrQ⟩ := IsArtinianRing.exists_not_mem_forall_mem_of_ne
    (R := R ⧸ I) (P.map (Ideal.Quotient.mk I))
  obtain ⟨e, he, rfl⟩ := HenselianRing.exists_isIdempotentElem_mk_eq I hr
  refine ⟨e, he, fun heP ↦ hrP (Ideal.mem_map_of_mem _ heP), fun Q hQ hQP ↦ ?_⟩
  refine (Ideal.mem_quotient_iff_mem (hle Q)).mp (hrQ _ (hprime Q) fun h ↦ hQP ?_)
  ext x
  rw [← Ideal.mem_quotient_iff_mem (hle Q), h, Ideal.mem_quotient_iff_mem (hle P)]

/-- If `R` is henselian along `I` and `R ⧸ I` is artinian, `R` has finitely many maximal
ideals. -/
theorem finite_maximalSpectrum : Finite (MaximalSpectrum R) := by
  have hle (Q : Ideal R) [Q.IsMaximal] : I ≤ Q := le_of_le_jacobson HenselianRing.jac Q
  let φ : MaximalSpectrum R → PrimeSpectrum (R ⧸ I) := fun P ↦
    ⟨P.asIdeal.map (Ideal.Quotient.mk I), Ideal.map_isPrime_of_surjective
      Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle P.asIdeal)⟩
  refine Finite.of_injective φ fun P Q h ↦ MaximalSpectrum.ext (Ideal.ext fun x ↦ ?_)
  have h' := congrArg PrimeSpectrum.asIdeal h
  rw [← Ideal.mem_quotient_iff_mem (hle P.asIdeal), ← Ideal.mem_quotient_iff_mem (hle Q.asIdeal)]
  exact SetLike.ext_iff.mp h' _

/-- If `R` is henselian along `I` and `R ⧸ I` is artinian, there is a complete family of
orthogonal idempotents `e_P`, indexed by the maximal ideals of `R`, with `e_P ∈ Q` if and only if
`P ≠ Q`: `R` is the product of the rings `R ⧸ (1 - e_P)`, its local components. -/
theorem exists_completeOrthogonalIdempotents [Fintype (MaximalSpectrum R)] :
    ∃ e : MaximalSpectrum R → R, CompleteOrthogonalIdempotents e ∧
      ∀ P Q : MaximalSpectrum R, e P ∈ Q.asIdeal ↔ P ≠ Q := by
  classical
  choose e he heP heQ using fun P : MaximalSpectrum R ↦
    exists_isIdempotentElem_notMem_forall_mem I P.asIdeal
  have hmem (P Q : MaximalSpectrum R) : e P ∈ Q.asIdeal ↔ P ≠ Q := by
    refine ⟨fun h hPQ ↦ heP P (hPQ ▸ h), fun hPQ ↦ heQ P Q.asIdeal Q.isMaximal fun h ↦ hPQ ?_⟩
    exact (MaximalSpectrum.ext h).symm
  have hortho : OrthogonalIdempotents e := by
    refine ⟨he, fun P Q hPQ ↦ ?_⟩
    refine ((he P).mul (he Q)).eq_zero_of_mem_jacobson (mem_jacobson_bot_of_forall fun M hM ↦ ?_)
    by_cases h : P = ⟨M, hM⟩
    · subst h
      exact M.mul_mem_left _ ((hmem Q _).mpr (Ne.symm hPQ))
    · exact M.mul_mem_right _ ((hmem P _).mpr h)
  refine ⟨e, ⟨hortho, ?_⟩, hmem⟩
  have hs : IsIdempotentElem (∑ P, e P) := hortho.isIdempotentElem_sum
  have h0 := hs.one_sub.eq_zero_of_mem_jacobson (mem_jacobson_bot_of_forall fun M hM ↦ ?_)
  · exact (sub_eq_zero.mp h0).symm
  set Q : MaximalSpectrum R := ⟨M, hM⟩
  have h1 : 1 - e Q ∈ M := by
    have : e Q * (1 - e Q) ∈ M := by rw [mul_sub, mul_one, (he Q).eq, sub_self]; exact M.zero_mem
    exact (hM.isPrime.mem_or_mem this).resolve_left (heP Q)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ Q), sub_add_eq_sub_sub]
  refine M.sub_mem h1 (M.sum_mem fun P hP ↦ (hmem P Q).mpr (Finset.ne_of_mem_erase hP))

end Idempotents

section Components

variable {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e) {P : Ideal R} [P.IsMaximal]
  (heP : e ∉ P) (hQ : ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → e ∈ Q)
include he heP hQ

omit he heP [P.IsMaximal] in
/-- An element outside `P` becomes a unit in the local component `R ⧸ (1 - e)`. -/
lemma isUnit_mk_of_notMem {s : R} (hs : s ∉ P) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {1 - e}) s) := by
  by_contra h
  obtain ⟨M, hM, hsM⟩ := exists_max_ideal_of_mem_nonunits h
  have hMc := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := M)
  have h1 : 1 - e ∈ M.comap (Ideal.Quotient.mk (Ideal.span {1 - e})) := by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
    exact M.zero_mem
  by_cases hMP : M.comap (Ideal.Quotient.mk (Ideal.span {1 - e})) = P
  · exact hs (hMP ▸ hsM)
  · have h2 := hQ _ hMc hMP
    exact hMc.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using add_mem h1 h2))

/-- The local component `R ⧸ (1 - e)` is the localization of `R` at `P`, when `e` is an
idempotent outside `P` lying in all other maximal ideals. -/
theorem isLocalization_atPrime_quotient :
    IsLocalization.AtPrime (R ⧸ Ideal.span {1 - e}) P where
  map_units y := isUnit_mk_of_notMem hQ y.2
  surj z := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨⟨x, 1⟩, by simp⟩
  exists_of_eq {x y} hxy := by
    refine ⟨⟨e, heP⟩, ?_⟩
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hxy
    obtain ⟨c, hc⟩ := hxy
    change e * x = e * y
    rw [← sub_eq_zero, ← mul_sub, ← hc, mul_left_comm, mul_sub, mul_one, he.eq, sub_self,
      mul_zero]

/-- The local component `R ⧸ (1 - e)` is a local ring. -/
theorem isLocalRing_quotient : IsLocalRing (R ⧸ Ideal.span {1 - e}) :=
  have := isLocalization_atPrime_quotient he heP hQ
  IsLocalization.AtPrime.isLocalRing _ P

end Components

/-- In a local ring `S`, an ideal `J` with `S ⧸ J` artinian contains a power of the maximal
ideal. -/
lemma exists_pow_maximalIdeal_le_of_isArtinianRing {S : Type*} [CommRing S] [IsLocalRing S]
    (J : Ideal S)
    [IsArtinianRing (S ⧸ J)] : ∃ N, maximalIdeal S ^ N ≤ J := by
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := S ⧸ J)
  refine ⟨N, ?_⟩
  have hle : (maximalIdeal S).map (Ideal.Quotient.mk J) ≤ Ideal.jacobson ⊥ :=
    Ideal.map_le_iff_le_comap.mpr fun x hx ↦ mem_jacobson_bot_of_forall fun M hM ↦ by
      have := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := M)
      exact (IsLocalRing.eq_maximalIdeal this).ge hx
  rw [← Ideal.mk_ker (I := J), ← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, eq_bot_iff,
    ← Ideal.zero_eq_bot, ← hN]
  exact Ideal.pow_right_mono hle N

section Finite

variable {B : Type*} [CommRing B] {B' : Type*} [CommRing B'] [Algebra B B'] [Module.Finite B B']

/-- A finite algebra over an `𝔟`-adically complete noetherian ring is complete for `𝔟 B'`. -/
theorem isAdicComplete_map_of_finite [IsNoetherianRing B] (𝔟 : Ideal B) [IsAdicComplete 𝔟 B] :
    IsAdicComplete (𝔟.map (algebraMap B B')) B' := by
  have := IsAdicComplete.of_finite 𝔟 B'
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr this

/-- For `B'` finite over a local ring `B`, the ring `B' ⧸ 𝔫 B'` is artinian. -/
theorem isArtinianRing_quotient_map_maximalIdeal [IsLocalRing B] :
    IsArtinianRing (B' ⧸ (maximalIdeal B).map (algebraMap B B')) := by
  let := Ideal.Quotient.field (maximalIdeal B)
  have : Module.Finite B (B' ⧸ (maximalIdeal B).map (algebraMap B B')) := inferInstance
  have : Module.Finite (B ⧸ maximalIdeal B) (B' ⧸ (maximalIdeal B).map (algebraMap B B')) :=
    Module.Finite.of_restrictScalars_finite B _ _
  exact IsArtinianRing.of_finite (B ⧸ maximalIdeal B) _

end Finite

namespace AdicFormallySmooth

section Quotient

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B] {I : Ideal B}

/-- Formal smoothness (for the adic lifting property) passes to the local components
`B ⧸ (1 - e)`, which are localizations of `B`. -/
theorem quotient_span_one_sub (h : AdicFormallySmooth A I) {e : B} (he : IsIdempotentElem e) :
    AdicFormallySmooth A (I.map (Ideal.Quotient.mk (Ideal.span {1 - e}))) := by
  have := IsLocalization.Away.quotient_of_isIdempotentElem he
  have := h.localization (Submonoid.powers e) (B ⧸ Ideal.span {1 - e})
  rwa [Ideal.Quotient.algebraMap_eq] at this

end Quotient

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal B}

/-- Formal smoothness for the adic lifting property can be checked on the factors of a finite
product decomposition `B ≅ ∏ B ⧸ (1 - eᵢ)` given by complete orthogonal idempotents. As in SGA
("the local components"), one decomposes the test ring `C` with the lifted images of the `eᵢ`
and lifts factor by factor. -/
theorem of_completeOrthogonalIdempotents {ι : Type*} [Fintype ι] {e : ι → B}
    (he : CompleteOrthogonalIdempotents e)
    (h : ∀ i, AdicFormallySmooth R (I.map (Ideal.Quotient.mk (Ideal.span {1 - e i})))) :
    AdicFormallySmooth R I := by
  intro C _ _ J hJ f ⟨n, hn⟩
  have hnil : ∀ x ∈ RingHom.ker (Ideal.Quotient.mk J), IsNilpotent x := by
    intro x hx
    rw [Ideal.mk_ker] at hx
    obtain ⟨m, hm⟩ := hJ
    exact ⟨m, by have := Ideal.pow_mem_pow hx m; rwa [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at this⟩
  obtain ⟨c, hc, hce⟩ := CompleteOrthogonalIdempotents.lift_of_isNilpotent_ker
    (Ideal.Quotient.mk J) hnil (he.map (f : B →+* C ⧸ J)) fun i ↦ Ideal.Quotient.mk_surjective _
  have hce' (i : ι) : Ideal.Quotient.mk J (c i) = f (e i) := congr_fun hce i
  -- the factors of `C`
  let K (i : ι) : Ideal C := Ideal.span {1 - c i}
  let q (i : ι) : C ⧸ J →ₐ[R] (C ⧸ K i) ⧸ J.map (Ideal.Quotient.mk (K i)) :=
    Ideal.quotientMapₐ _ (Ideal.Quotient.mkₐ R (K i)) Ideal.le_comap_map
  have hq (i : ι) (x : C) : q i (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk (K i) x) := rfl
  have hqe (i : ι) : (q i).comp f (1 - e i) = 0 := by
    rw [AlgHom.comp_apply, map_sub, map_one, ← hce' i, ← map_one (Ideal.Quotient.mk J),
      ← map_sub, hq, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
      map_zero]
  let f' (i : ι) : B ⧸ Ideal.span {1 - e i} →ₐ[R] (C ⧸ K i) ⧸ J.map (Ideal.Quotient.mk (K i)) :=
    Ideal.Quotient.liftₐ _ ((q i).comp f) fun a ha ↦ by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, hqe, mul_zero]
  have hf' (i : ι) (b : B) : f' i (Ideal.Quotient.mk _ b) = q i (f b) := rfl
  have hJi (i : ι) : IsNilpotent (J.map (Ideal.Quotient.mk (K i))) := by
    obtain ⟨m, hm⟩ := hJ
    exact ⟨m, by rw [← Ideal.map_pow, hm, Ideal.zero_eq_bot, Ideal.map_bot]; rfl⟩
  choose g hg using fun i ↦ h i (J.map (Ideal.Quotient.mk (K i))) (hJi i) (f' i) ⟨n, by
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.mem_ker, hf', RingHom.mem_ker.mp (hn hb), map_zero]⟩
  have hg' (i : ι) (b : B) : Ideal.Quotient.mk _ (g i (Ideal.Quotient.mk _ b)) = q i (f b) :=
    congr($(hg i) (Ideal.Quotient.mk _ b))
  -- recombine
  let Φ : C →ₐ[R] ∀ i, C ⧸ K i := AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ R (K i)
  have hΦ : Function.Bijective Φ := hc.bijective_pi
  let Φe := AlgEquiv.ofBijective Φ hΦ
  let G : B →ₐ[R] ∀ i, C ⧸ K i := AlgHom.pi fun i ↦
    (g i).comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))
  refine ⟨Φe.symm.toAlgHom.comp G, AlgHom.ext fun b ↦ ?_⟩
  set y := Φe.symm (G b)
  have hy (i : ι) : Ideal.Quotient.mk (K i) y = g i (Ideal.Quotient.mk _ b) := by
    have : Φ y = G b := Φe.apply_symm_apply (G b)
    exact congr_fun this i
  -- the difference `z` is killed by every `cᵢ`, hence is zero
  set z := Ideal.Quotient.mk J y - f b
  have hz (i : ι) : Ideal.Quotient.mk J (c i) * z = 0 := by
    have hqz : q i z = 0 := by
      rw [map_sub, hq, hy, hg', sub_self]
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective z
    rw [← hw, hq, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hqz
    obtain ⟨w', hw', hww'⟩ := hqz
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hww'
    obtain ⟨t, ht⟩ := hww'
    have hcw : c i * w = c i * w' := by
      have : c i * (w' - w) = 0 := by
        rw [← ht, mul_left_comm, mul_sub, mul_one, (hc.idem i).eq, sub_self, mul_zero]
      linear_combination -this
    rw [← hw, ← map_mul, hcw, Ideal.Quotient.eq_zero_iff_mem]
    exact J.mul_mem_left _ hw'
  have : z = 0 := by
    have hsum : (∑ i, Ideal.Quotient.mk J (c i)) * z = 0 := by
      rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun i _ ↦ hz i
    rwa [← map_sum, hc.complete, map_one, one_mul] at hsum
  simpa [z, sub_eq_zero] using this

end AdicFormallySmooth

namespace AdicFormallySmooth

variable {A : Type u} {B' : Type u} [CommRing A] [CommRing B'] [Algebra A B'] {I : Ideal B'}
  [HenselianRing B' I] [IsArtinianRing (B' ⧸ I)]

/-- Formal smoothness is local on the maximal ideals, for a ring henselian along an ideal `I`
with `R ⧸ I` artinian (e.g. a finite algebra over a complete noetherian local ring): if the
localizations `B'_P` at the maximal ideals are formally smooth over `A` for their maximal-adic
topologies, then `B'` is formally smooth over `A` for the `I`-adic topology. -/
theorem of_localization
    (h : ∀ (P : Ideal B') [P.IsMaximal],
      AdicFormallySmooth A (maximalIdeal (Localization.AtPrime P))) :
    AdicFormallySmooth A I := by
  classical
  have := finite_maximalSpectrum I
  let _ := Fintype.ofFinite (MaximalSpectrum B')
  obtain ⟨e, he, hmem⟩ := exists_completeOrthogonalIdempotents I
  refine of_completeOrthogonalIdempotents he fun P ↦ ?_
  have heP : e P ∉ P.asIdeal := fun h ↦ (hmem P P).mp h rfl
  have hQ : ∀ Q : Ideal B', Q.IsMaximal → Q ≠ P.asIdeal → e P ∈ Q := fun Q hQ hQP ↦
    (hmem P ⟨Q, hQ⟩).mpr fun h ↦ hQP (congrArg MaximalSpectrum.asIdeal h).symm
  set S := B' ⧸ Ideal.span {1 - e P}
  have := isLocalization_atPrime_quotient (he.idem P) heP hQ
  have := isLocalRing_quotient (he.idem P) heP hQ
  let φ : S ≃ₐ[A] Localization.AtPrime P.asIdeal :=
    (IsLocalization.algEquiv P.asIdeal.primeCompl S _).restrictScalars A
  have h₁ : AdicFormallySmooth A (maximalIdeal S) := by
    have h' := (h P.asIdeal).of_algEquiv φ
    have hmax : ((maximalIdeal (Localization.AtPrime P.asIdeal)).comap φ).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ φ.surjective
    rwa [IsLocalRing.eq_maximalIdeal hmax] at h'
  -- `𝔪_S ^ N ≤ I S`, since `S ⧸ I S` is artinian
  set J := I.map (Ideal.Quotient.mk (Ideal.span {1 - e P}))
  have : IsArtinianRing (S ⧸ J) :=
    (Ideal.quotientMap_surjective (H := Ideal.le_comap_map)
      Ideal.Quotient.mk_surjective).isArtinianRing
  obtain ⟨N, hN⟩ := exists_pow_maximalIdeal_le_of_isArtinianRing J
  exact h₁.of_pow_le N hN

end AdicFormallySmooth

end SGA.SGA1.ExposeIII
