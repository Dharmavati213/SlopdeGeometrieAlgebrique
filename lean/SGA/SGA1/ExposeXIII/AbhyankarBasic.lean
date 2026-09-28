/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.IntegralClosure.GoingDown
import SGA.Foundations.CommAlg.PurityInduction
import SGA.Foundations.Dimension.Integral
import SGA.Foundations.HenselianFiniteEtale
import SGA.Foundations.HenselianFiniteLocal
import SGA.Foundations.Ramification.Pi
import SGA.SGA1.ExposeII.Coordinates
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeXIII.RootAdjunction

/-!
# SGA 1, Exposé XIII, Appendix I: Abhyankar's lemma — statements and dimension one

The notions and statements of XIII.5.2–5.4 (`IsTamelyRamifiedAlong`, `IsLcmRamificationIndices`,
`AbsoluteAbhyankarAt`, `AbsoluteAbhyankarStatement`, `TameCoveringsOfStrictlyLocalAt`,
`TameCoveringsOfStrictlyLocalStatement`, `RootAdjunctionSmoothStatement`), the étale part of
XIII.5.4 (`etale_localization_away_kummerAlgebra`), and XIII.5.2–5.3 over a discrete valuation
ring (X.3.6: `etale_integralClosure_of_adjoinRoot`,
`nonempty_algEquiv_adjoinRoot_of_isTameExtension`) and for regular local rings of dimension one
(`absoluteAbhyankarAt_of_ringKrullDim_eq_one`,
`tameCoveringsOfStrictlyLocalAt_of_ringKrullDim_eq_one`). See `SGA.SGA1.ExposeXIII.Abhyankar` for
an overview.
-/

universe u

open IsLocalRing
open scoped TensorProduct

namespace SGA.SGA1.ExposeXIII

variable {A : Type u} [CommRing A] {ι : Type*}

/-- XIII.2.3 c), for `X = Spec A` and `D = Σ div fᵢ`: the `A`-algebra `B` (the ring of an étale
covering of `U = Spec A[1/∏ fᵢ]`) is tamely ramified along `D` when every prime of the
normalisation of `A` in `Frac A ⊗_A B` lying over one of the primes `(fᵢ)` is tamely ramified. -/
def IsTamelyRamifiedAlong (f : ι → A) (B : Type u) [CommRing B] [Algebra A B] : Prop :=
  ∀ (i : ι) (Q : Ideal (integralClosure A (FractionRing A ⊗[A] B))) [Q.IsPrime],
    Q.LiesOver (Ideal.span {f i}) → IsTamelyRamifiedAt A Q

/-- XIII.5.2: `n` is the least common multiple of the ramification indices of the primes of the
normalisation of `A` in `Frac A ⊗_A B` over `p`. -/
def IsLcmRamificationIndices (p : Ideal A) (B : Type u) [CommRing B] [Algebra A B] (n : ℕ) :
    Prop :=
  (∀ (Q : Ideal (integralClosure A (FractionRing A ⊗[A] B))) [Q.IsPrime], Q.LiesOver p →
      Q.ramificationIdx A ∣ n) ∧
    ∀ m : ℕ, (∀ (Q : Ideal (integralClosure A (FractionRing A ⊗[A] B))) [Q.IsPrime],
      Q.LiesOver p → Q.ramificationIdx A ∣ m) → n ∣ m

/-- XIII.5.2 (absolute Abhyankar lemma, existence part) for a given regular local ring `A` and a
given number `r` of divisors. Let `f₁, …, f_r` be part of a regular system of parameters of `A`,
and `B` a finite étale `A[1/∏ fᵢ]`-algebra tamely ramified along `D = Σ div fᵢ`. Let `nᵢ` be the
l.c.m. of the ramification indices above `(fᵢ)` and `A' = A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`. Then the `nᵢ` are
prime to the residue characteristic of `A`, and there is a finite étale `A'`-algebra `W` whose
restriction to `U' = Spec A'[1/∏ fᵢ]` is `V' = V ×_X X'`. (SGA also states that `W` is unique up
to unique isomorphism, which follows from the normality of `X'` by I.10.2; this is not included
here.) Proved for `dim A = 1`, `r = 1` in `absoluteAbhyankarAt_of_ringKrullDim_eq_one` and for
`A` of equal characteristic in `absoluteAbhyankarAt_of_ringChar_eq`; the extension part holds for
every `A` (`absoluteAbhyankar_extension`). -/
def AbsoluteAbhyankarAt (A : Type u) [CommRing A] [IsRegularLocalRing A] (r : ℕ) : Prop :=
  ∀ (f : Fin r → A), IsPartOfRegularSystemOfParameters f →
    ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra (Localization.Away (∏ i, f i)) B]
      [IsScalarTower A (Localization.Away (∏ i, f i)) B]
      [Module.Finite (Localization.Away (∏ i, f i)) B]
      [Algebra.Etale (Localization.Away (∏ i, f i)) B],
    IsTamelyRamifiedAlong f B →
    ∀ n : Fin r → ℕ, (∀ i, IsLcmRamificationIndices (Ideal.span {f i}) B (n i)) →
      (∀ i, (n i : A) ∉ maximalIdeal A) ∧
      ∃ (W : Type u) (_ : CommRing W) (_ : Algebra (KummerAlgebra n f) W),
        Module.Finite (KummerAlgebra n f) W ∧ Algebra.Etale (KummerAlgebra n f) W ∧
        Nonempty (KummerAlgebra n f ⊗[A] B ≃ₐ[KummerAlgebra n f]
          Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)) ⊗[KummerAlgebra n f] W)

/-- XIII.5.2 (absolute Abhyankar lemma; statement only, existence part): `AbsoluteAbhyankarAt A r`
for every regular local ring `A` and every `r`. The extension part is proved in
`absoluteAbhyankar_extension`; that the `nᵢ` are prime to the residue characteristic is proved
when the `κ((fᵢ))` have that characteristic, and in mixed characteristic in the form of 5.3 over
strictly henselian rings (`tameCoveringsOfStrictlyLocalStatement`). -/
def AbsoluteAbhyankarStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] (r : ℕ), AbsoluteAbhyankarAt A r

/-- The extension part of `AbsoluteAbhyankarAt`, assuming that the `nᵢ` are prime to the residue
characteristic of `A` (in SGA this is part of the conclusion; it is automatic when the residue
fields of the `(fᵢ)` have the residue characteristic of `A`). Proved for every `A` and `r` in
`absoluteAbhyankarExtensionAt`; the assumption is not needed (`absoluteAbhyankar_extension`). -/
def AbsoluteAbhyankarExtensionAt (A : Type u) [CommRing A] [IsRegularLocalRing A] (r : ℕ) :
    Prop :=
  ∀ (f : Fin r → A), IsPartOfRegularSystemOfParameters f →
    ∀ (B : Type u) [CommRing B] [Algebra A B] [Algebra (Localization.Away (∏ i, f i)) B]
      [IsScalarTower A (Localization.Away (∏ i, f i)) B]
      [Module.Finite (Localization.Away (∏ i, f i)) B]
      [Algebra.Etale (Localization.Away (∏ i, f i)) B],
    IsTamelyRamifiedAlong f B →
    ∀ n : Fin r → ℕ, (∀ i, IsLcmRamificationIndices (Ideal.span {f i}) B (n i)) →
      (∀ i, (n i : A) ∉ maximalIdeal A) →
      ∃ (W : Type u) (_ : CommRing W) (_ : Algebra (KummerAlgebra n f) W),
        Module.Finite (KummerAlgebra n f) W ∧ Algebra.Etale (KummerAlgebra n f) W ∧
        Nonempty (KummerAlgebra n f ⊗[A] B ≃ₐ[KummerAlgebra n f]
          Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)) ⊗[KummerAlgebra n f] W)

theorem AbsoluteAbhyankarAt.extensionAt {A : Type u} [CommRing A] [IsRegularLocalRing A]
    {r : ℕ} (h : AbsoluteAbhyankarAt A r) : AbsoluteAbhyankarExtensionAt A r :=
  fun f hf B _ _ _ _ _ _ hB n hn _ ↦ (h f hf B hB n hn).2

/-- XIII.5.3, in terms of coverings, for a given regular strictly local ring `A` (henselian with
separably closed residue field) and a given number `r` of divisors: let `f₁, …, f_r` be part of a
regular system of parameters. Every connected (here: integral) finite étale `A[1/∏ fᵢ]`-algebra
`B` tamely ramified along `Σ div fᵢ` is a quotient of a Kummer covering: there are integers
`nᵢ > 0` prime to the residue characteristic and an injective `A[1/∏ fᵢ]`-algebra map from `B` to
the ring of `U[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`. Together with XIII.5.3.0
(`KummerAlgebra.rootsOfUnityToAlgEquiv_bijective`) this says that the tame fundamental group of
`U` is `lim ∏ᵢ μ_{nᵢ} = ∏_{ℓ ≠ p} ℤ_ℓ(1)^r`. Proved in `tameCoveringsOfStrictlyLocalAt` (by SGA's
descent argument; see also `tameCoveringsOfStrictlyLocalAt_of_ringKrullDim_eq_one` and, for `A` of
equal characteristic, `tameCoveringsOfStrictlyLocalAt_of_ringChar_eq`). -/
def TameCoveringsOfStrictlyLocalAt (A : Type u) [CommRing A] [IsRegularLocalRing A]
    [HenselianLocalRing A] [IsSepClosed (ResidueField A)] (r : ℕ) : Prop :=
  ∀ (f : Fin r → A), IsPartOfRegularSystemOfParameters f →
    ∀ (B : Type u) [CommRing B] [IsDomain B] [Algebra A B]
      [Algebra (Localization.Away (∏ i, f i)) B]
      [IsScalarTower A (Localization.Away (∏ i, f i)) B]
      [Module.Finite (Localization.Away (∏ i, f i)) B]
      [Algebra.Etale (Localization.Away (∏ i, f i)) B],
    IsTamelyRamifiedAlong f B →
    ∃ n : Fin r → ℕ, (∀ i, 0 < n i ∧ (n i : A) ∉ maximalIdeal A) ∧
      ∃ φ : B →ₐ[Localization.Away (∏ i, f i)]
          KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i)),
        Function.Injective φ

/-- XIII.5.3: `TameCoveringsOfStrictlyLocalAt A r` for every regular strictly local ring `A` and
every `r`. Proved in `tameCoveringsOfStrictlyLocalStatement`. -/
def TameCoveringsOfStrictlyLocalStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)] (r : ℕ), TameCoveringsOfStrictlyLocalAt A r

/-- XIII.5.4 (smoothness part), locally at a point `x = q` of `X = Spec A` smooth over
`S = Spec R` (`S` locally noetherian, as everywhere in SGA 1): if the `fᵢ` vanish at `x` and
`V((fᵢ))` is smooth over `S` at `x` of codimension `r` in `X`, then `X' = X[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` is
smooth over `S` at the points `x'` over `x`. Proved in `rootAdjunctionSmoothStatement`. The étale
part of XIII.5.4 is `etale_localization_away_kummerAlgebra`. -/
def RootAdjunctionSmoothStatement : Prop :=
  ∀ (R A : Type u) [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A]
    (r : ℕ) (f : Fin r → A) (n : Fin r → ℕ) (q : Ideal A) [q.IsPrime],
    (∀ i, 0 < n i) → (∀ i, f i ∈ q) → Algebra.IsSmoothAt R q →
    Algebra.FormallySmooth R (Localization.AtPrime q ⧸
      (Ideal.span (Set.range f)).map (algebraMap A (Localization.AtPrime q))) →
    ((Ideal.span (Set.range f)).map (algebraMap A (Localization.AtPrime q))).height = r →
    ∀ (Q : Ideal (KummerAlgebra n f)) [Q.IsPrime], Q.LiesOver q → Algebra.IsSmoothAt R Q

/-- XIII.5.4, étale part: let `x = q` be a point of `X = Spec A` and `X₁ = Spec O_{X,x}`,
`U₁ = X₁[1/∏ fᵢ]`. If the `nᵢ` are prime to the characteristic of `κ(x)` (`nᵢ ∉ q`), then
`U'₁ = U₁[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` is étale over `U₁`. -/
theorem etale_localization_away_kummerAlgebra [Fintype ι] (q : Ideal A) [q.IsPrime] (f : ι → A)
    {n : ι → ℕ} (hn : ∀ i, (n i : A) ∉ q) :
    let f₁ := fun i ↦ algebraMap A (Localization.AtPrime q) (f i)
    Algebra.Etale (Localization.Away (∏ i, f₁ i))
      (Localization.Away (∏ i, f₁ i) ⊗[Localization.AtPrime q] KummerAlgebra n f₁) :=
  KummerAlgebra.etale_away _ fun i ↦ by
    simpa using (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q _).mpr (hn i)

section DiscreteValuationRing

/-! ### Abhyankar's lemma for discrete valuation rings

The proof of XIII.5.2 in dimension one, following X.3.6: all extensions are placed in the Galois
closure `N` of a composite `F` of `L` and `K'`; there the inertia group `I` of a prime is cyclic
(`F`, hence `N`, is tame), and `I ∩ Gal(N/K') ⊆ Gal(N/L)` because `e(L) ∣ e(K')`. -/

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]

open integralClosure in
/-- For a tamely ramified extension `E ⊆ N`, `N/K` finite Galois, and a prime `Q` of the
normalization of `R` in `N`, the index of `I_Q ∩ Gal(N/E)` in the inertia group `I_Q` is the
ramification index of `Q ∩ E` (the residue extension is separable). -/
lemma relIndex_inertia_eq_ramificationIdx (E N : Type*) [Field E] [Algebra K E] [Algebra R E]
    [IsScalarTower R K E] [FiniteDimensional K E] [Algebra.IsSeparable K E] [Field N]
    [Algebra K N] [Algebra R N] [IsScalarTower R K N] [FiniteDimensional K N] [IsGalois K N]
    [Algebra E N] [IsScalarTower K E N] [IsScalarTower R E N] (hE : IsTameExtension R (K := K) E)
    (Q : Ideal (integralClosure R N)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    letI := algebraOfTower R E N
    (fixingSubgroup Gal(N/K) (Set.range (algebraMap E N))).relIndex (Q.inertia Gal(N/K)) =
      (Q.under (integralClosure R E)).ramificationIdx R := by
  let := algebraOfTower R E N
  have := isDedekindDomain' R K N
  have := integralClosure.finite R K N
  have := integralClosure.flat R K N
  have := integralClosure.isGaloisGroup R K N
  have := integralClosure.finite R K E
  have := finite_of_tower R E N K
  have := flat_of_tower R E N K
  have := isGaloisGroup_of_tower R E N K
  let := Localization.AtPrime.algebraOfLiesOver (IsLocalRing.maximalIdeal R)
    (Q.under (integralClosure R E))
  rw [Ideal.relIndex_inertia_eq (C := integralClosure R E) _ (IsLocalRing.maximalIdeal R) Q]
  have ht := (isTameExtension_iff_isTamelyRamifiedOver R E).mp hE
    (Q.under (integralClosure R E)) inferInstance
  rw [isTamelyRamifiedAt_iff_of_liesOver R (IsLocalRing.maximalIdeal R)] at ht
  have := ht.2
  rw [Algebra.IsSeparable.finInsepDegree_eq, mul_one]

open integralClosure in
/-- XIII.5.2 in dimension one (Abhyankar's lemma for a discrete valuation ring `R` with fraction
field `K`). Let `L` and `K'` be finite separable extensions of `K`, tamely ramified over `R`, such
that the ramification index of every prime of the normalization of `R` in `L` divides that of
every prime of the normalization of `R` in `K'` (e.g. `K' = K(π^{1/n})` with `n` the l.c.m. of
the ramification indices of `L`). Then every composite `F` of `L` and `K'` (a field generated by
the images of `L` and `K'`) is unramified over `K'`: every prime of the normalization of `R` in
`F` over the maximal ideal has ramification index `1` over the normalization of `R` in `K'` and a
separable residue field extension. -/
theorem ramificationIdx_eq_one_and_isSeparable_of_dvd {L K' F : Type*} [Field L] [Field K']
    [Field F] [Algebra K L] [Algebra K K'] [Algebra K F] [Algebra R L] [Algebra R K']
    [Algebra R F] [IsScalarTower R K L] [IsScalarTower R K K'] [IsScalarTower R K F]
    [Algebra K' F] [IsScalarTower K K' F] [IsScalarTower R K' F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (f : L →ₐ[K] F) (hgen : Algebra.adjoin K (Set.range f ∪ Set.range (algebraMap K' F)) = ⊤)
    (hL : IsTameExtension R (K := K) L) (hK' : IsTameExtension R (K := K) K')
    (hdvd : ∀ (Q : Ideal (integralClosure R L)) (Q' : Ideal (integralClosure R K')), Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → Q'.IsPrime →
      Q'.LiesOver (IsLocalRing.maximalIdeal R) → Q.ramificationIdx R ∣ Q'.ramificationIdx R)
    (P : Ideal (integralClosure R F)) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal R)] :
    letI := algebraOfTower R K' F
    letI := Localization.AtPrime.algebraOfLiesOver (P.under (integralClosure R K')) P
    P.ramificationIdx (integralClosure R K') = 1 ∧
      Algebra.IsSeparable (P.under (integralClosure R K')).ResidueField P.ResidueField := by
  set p := IsLocalRing.maximalIdeal R
  set N := galoisClosure K F
  set G := Gal(N/K)
  -- the algebra structures on the Galois closure `N` of `F`
  let : Algebra L N := ((algebraMap F N).comp f.toRingHom).toAlgebra
  let : Algebra K' N := ((algebraMap F N).comp (algebraMap K' F)).toAlgebra
  have : IsScalarTower K L N := .of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, f.commutes, ← IsScalarTower.algebraMap_apply]
  have : IsScalarTower R L N := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply R K L, IsScalarTower.algebraMap_apply R K N,
      ← IsScalarTower.algebraMap_apply K L N]
  have : IsScalarTower K' F N := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K K' N := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply K' F N (algebraMap K K' x),
      ← IsScalarTower.algebraMap_apply K K' F, ← IsScalarTower.algebraMap_apply K F N]
  have : IsScalarTower R K' N := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply R K K', IsScalarTower.algebraMap_apply R K N,
      ← IsScalarTower.algebraMap_apply K K' N]
  have : FiniteDimensional K L := FiniteDimensional.of_injective f.toLinearMap f.injective
  have : Algebra.IsSeparable K L := Algebra.IsSeparable.of_algHom (F := K) (E := L) (E' := F) f
  have : FiniteDimensional K K' := FiniteDimensional.of_injective
    (IsScalarTower.toAlgHom K K' F).toLinearMap (algebraMap K' F).injective
  have : Algebra.IsSeparable K K' :=
    Algebra.IsSeparable.of_algHom (F := K) (E := K') (E' := F) (IsScalarTower.toAlgHom K K' F)
  -- `F` is tamely ramified, being a composite of tamely ramified extensions
  have hF : IsTameExtension R (K := K) F :=
    IsTameExtension.of_adjoin_eq_top R f (IsScalarTower.toAlgHom K K' F) hgen hL hK'
  have := isDedekindDomain' R K N
  have := integralClosure.finite R K N
  have := integralClosure.flat R K N
  have := integralClosure.isGaloisGroup R K N
  have : FaithfulSMul G (integralClosure R N) := IsGaloisGroup.faithful R
  -- a prime `Q` of the normalization of `R` in `N` over `P`
  have : Module.Finite R (integralClosure R F) := integralClosure.finite R K F
  let := algebraOfTower R F N
  have := finite_of_tower R F N K
  have := flat_of_tower R F N K
  have := isGaloisGroup_of_tower R F N K
  have : FaithfulSMul (integralClosure R F) (integralClosure R N) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap_algebraOfTower_injective R F N)
  obtain ⟨Q, hQ, hQP⟩ := (inferInstance : Nonempty (P.primesOver (integralClosure R N)))
  have : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have hQ0 := ne_bot_of_liesOver_maximalIdeal R (K := K) N Q
  -- the inertia group of `Q` is cyclic
  have hcard : ((Nat.card (Q.inertia G) : ℕ) : integralClosure R N ⧸ Q) ≠ 0 := by
    rw [← Ideal.natCast_residueField_ne_zero_iff p Q,
      Ideal.natCast_card_inertia_ne_zero_iff_wildInertia_eq_bot p Q hQ0]
    exact (isTameExtension_iff_forall_wildInertia_eq_bot R F).mp hF Q hQ inferInstance
  obtain ⟨_, hπ⟩ := Ideal.exists_isLocalUniformizer_of_ne_bot Q hQ0
  have := Ideal.isCyclic_inertia G Q hπ hcard
  set I := Q.inertia G
  set HL := fixingSubgroup G (Set.range (algebraMap L N))
  set HK := fixingSubgroup G (Set.range (algebraMap K' N))
  set HF := fixingSubgroup G (Set.range (algebraMap F N))
  -- the ramification indices of `L` and `K'` are the indices of `I ∩ HL` and `I ∩ HK` in `I`
  have hdvd' : HL.relIndex I ∣ HK.relIndex I := by
    rw [relIndex_inertia_eq_ramificationIdx R L N hL Q,
      relIndex_inertia_eq_ramificationIdx R K' N hK' Q]
    exact hdvd _ _ inferInstance inferInstance inferInstance inferInstance
  -- in the cyclic group `I`, `I ∩ HK ⊆ I ∩ HL`
  have hA : HK.subgroupOf I ≤ HL.subgroupOf I := by
    apply Subgroup.le_of_card_dvd_of_isCyclic
    have h₁ := (HL.subgroupOf I).card_mul_index
    have h₂ := (HK.subgroupOf I).card_mul_index
    rw [← Subgroup.relIndex] at h₁ h₂
    obtain ⟨k, hk⟩ := hdvd'
    rw [hk] at h₂
    refine ⟨k, Nat.eq_of_mul_eq_mul_right (m := HL.relIndex I)
      (Nat.pos_of_ne_zero fun h ↦ ?_) ?_⟩
    · rw [h, mul_zero] at h₁
      exact (Nat.card_pos (α := I)).ne' h₁.symm
    · rw [h₁, ← h₂]
      ring
  -- `HL ∩ HK ⊆ HF`, since `F` is generated by the images of `L` and `K'`
  have hLKF : HL ⊓ HK ≤ HF := by
    rintro σ ⟨hσL, hσK⟩
    let ι := IsScalarTower.toAlgHom K F N
    have hS : Algebra.adjoin K (Set.range f ∪ Set.range (algebraMap K' F)) ≤
        AlgHom.equalizer ((σ : Gal(N/K)).toAlgHom.comp ι) ι := by
      rw [Algebra.adjoin_le_iff]
      rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · exact (mem_fixingSubgroup_iff _).mp hσL _ ⟨x, rfl⟩
      · exact (mem_fixingSubgroup_iff _).mp hσK _ ⟨x, rfl⟩
    rw [hgen, top_le_iff] at hS
    rintro ⟨_, ⟨y, rfl⟩⟩
    have hy : y ∈ AlgHom.equalizer ((σ : Gal(N/K)).toAlgHom.comp ι) ι := hS ▸ Algebra.mem_top
    exact hy
  -- the Galois extension of `integralClosure R K'` by `integralClosure R N`
  let := algebraOfTower R K' F
  let := algebraOfTower R K' N
  have := integralClosure.finite R K K'
  have := finite_of_tower R K' N K
  have := flat_of_tower R K' N K
  have := finite_of_tower R K' F K
  have := isGaloisGroup_of_tower R K' N K
  have : IsScalarTower (integralClosure R K') (integralClosure R F) (integralClosure R N) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have hFK : HF ≤ HK := fixingSubgroup_antitone _ _ (by
    rintro _ ⟨x, rfl⟩
    exact ⟨algebraMap K' F x, rfl⟩)
  have : IsGaloisGroup (HF.subgroupOf HK) (integralClosure R F) (integralClosure R N) :=
    IsGaloisGroup.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFK) fun _ _ ↦ rfl
  have : Q.LiesOver (P.under (integralClosure R K')) :=
    Ideal.LiesOver.trans Q P (P.under (integralClosure R K'))
  obtain rfl : P = Q.under (integralClosure R F) := Ideal.over_def Q P
  have key := Ideal.relIndex_inertia_eq (A := integralClosure R K') (C := integralClosure R F)
    (G := HK) (HF.subgroupOf HK) ((Q.under (integralClosure R F)).under (integralClosure R K')) Q
  have h1 : (HF.subgroupOf HK).relIndex (Q.inertia HK) = 1 := by
    refine Subgroup.relIndex_eq_one.mpr fun σ hσ ↦ ?_
    have hσI : (σ : G) ∈ I := AddSubgroup.coe_mem_inertia.mpr hσ
    have hσL : (σ : G) ∈ HL := Subgroup.mem_subgroupOf.mp
      (hA (Subgroup.mem_subgroupOf.mpr σ.2 : (⟨σ, hσI⟩ : I) ∈ HK.subgroupOf I))
    exact Subgroup.mem_subgroupOf.mpr (hLKF ⟨hσL, σ.2⟩)
  rw [h1, eq_comm, mul_eq_one] at key
  let := Localization.AtPrime.algebraOfLiesOver
    ((Q.under (integralClosure R F)).under (integralClosure R K')) (Q.under (integralClosure R F))
  exact ⟨key.1, (isSeparable_iff_finInsepDegree_eq_one _ _).mpr key.2⟩

open integralClosure in
/-- XIII.5.2 in dimension one, étale form: in the situation of
`ramificationIdx_eq_one_and_isSeparable_of_dvd`, the normalization of `R` in `F` is a finite étale
algebra over the normalization `R'` of `R` in `K'`. That is, the connected étale covering
`Spec F` of `Spec K'` extends to a finite étale covering of `Spec R'`. -/
theorem etale_integralClosure_of_dvd {L K' F : Type*} [Field L] [Field K']
    [Field F] [Algebra K L] [Algebra K K'] [Algebra K F] [Algebra R L] [Algebra R K']
    [Algebra R F] [IsScalarTower R K L] [IsScalarTower R K K'] [IsScalarTower R K F]
    [Algebra K' F] [IsScalarTower K K' F] [IsScalarTower R K' F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (f : L →ₐ[K] F) (hgen : Algebra.adjoin K (Set.range f ∪ Set.range (algebraMap K' F)) = ⊤)
    (hL : IsTameExtension R (K := K) L) (hK' : IsTameExtension R (K := K) K')
    (hdvd : ∀ (Q : Ideal (integralClosure R L)) (Q' : Ideal (integralClosure R K')), Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → Q'.IsPrime →
      Q'.LiesOver (IsLocalRing.maximalIdeal R) → Q.ramificationIdx R ∣ Q'.ramificationIdx R) :
    letI := algebraOfTower R K' F
    Module.Finite (integralClosure R K') (integralClosure R F) ∧
      Algebra.Etale (integralClosure R K') (integralClosure R F) := by
  let := algebraOfTower R K' F
  have : FiniteDimensional K K' := FiniteDimensional.of_injective
    (IsScalarTower.toAlgHom K K' F).toLinearMap (algebraMap K' F).injective
  have : Algebra.IsSeparable K K' :=
    Algebra.IsSeparable.of_algHom (F := K) (E := K') (E' := F) (IsScalarTower.toAlgHom K K' F)
  have := isDedekindDomain' R K K'
  have := isDedekindDomain' R K F
  have := integralClosure.finite R K F
  have := finite_of_tower R K' F K
  have := flat_of_tower R K' F K
  have : Algebra.IsIntegral R (integralClosure R F) := inferInstance
  -- the nonzero primes of the normalization of `R` in `F` are unramified over `K'`
  have hmax (Q : Ideal (integralClosure R F)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
      Algebra.IsUnramifiedAt (integralClosure R K') Q := by
    have : Q.IsMaximal := Ideal.IsPrime.isMaximal ‹_› hQ
    have : Q.LiesOver (IsLocalRing.maximalIdeal R) :=
      ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)).symm⟩
    obtain ⟨he, hsep⟩ := ramificationIdx_eq_one_and_isSeparable_of_dvd R f hgen hL hK' hdvd Q
    exact Algebra.isUnramifiedAt_of_ramificationIdx_eq_one Q he hsep
  have : Algebra.FormallyUnramified (integralClosure R K') (integralClosure R F) := by
    rw [Algebra.formallyUnramified_iff_forall]
    intro q
    by_cases hq : q.asIdeal = ⊥
    · -- the generic point specializes to a closed point, and the unramified locus is open
      have : FaithfulSMul R (integralClosure R F) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
        (integralClosure.algebraMap_injective_of_isFractionRing R K F)
      obtain ⟨Q, hQ, hQm⟩ := (inferInstance : Nonempty ((IsLocalRing.maximalIdeal R).primesOver
        (integralClosure R F)))
      have hQu : (⟨Q, hQ⟩ : PrimeSpectrum (integralClosure R F)) ∈
          Algebra.unramifiedLocus (integralClosure R K') (integralClosure R F) :=
        hmax Q (ne_bot_of_liesOver_maximalIdeal R (K := K) F Q)
      have hspec : q ⤳ ⟨Q, hQ⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp (by
        change q.asIdeal ≤ Q
        rw [hq]
        exact bot_le)
      exact hspec.mem_open Algebra.isOpen_unramifiedLocus hQu
    · exact hmax q.asIdeal hq
  have : Algebra.FinitePresentation (integralClosure R K') (integralClosure R F) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, Algebra.Etale.of_formallyUnramified_of_flat⟩

/-- For a discrete valuation ring `R` with uniformizer `π` and fraction field `K`, an integral
`K`-algebra `C` is the localization at `π` of the normalization of `R` in `C`. -/
theorem isLocalization_powers_integralClosure {π : R} (hπ : Irreducible π) (C : Type*)
    [CommRing C] [Algebra K C] [Algebra R C] [IsScalarTower R K C] [Algebra.IsIntegral K C] :
    IsLocalization (Submonoid.powers (algebraMap R (integralClosure R C) π)) C where
  map_units := by
    rintro ⟨_, k, rfl⟩
    have h : IsUnit (algebraMap R K π) := isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hπ.ne_zero)
    change IsUnit (((algebraMap R (integralClosure R C) π ^ k : integralClosure R C)) : C)
    rw [SubmonoidClass.coe_pow]
    change IsUnit (algebraMap R C π ^ k)
    rw [IsScalarTower.algebraMap_apply R K C]
    exact (h.map _).pow k
  surj z := by
    obtain ⟨⟨m, hm⟩, hmz⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := K)
      (nonZeroDivisors R) z (Algebra.IsIntegral.isIntegral z)
    obtain ⟨k, u, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hm) hπ
    have hint : IsIntegral R (π ^ k • z) := by
      have := hmz.smul (((u⁻¹ : Rˣ) : R))
      rwa [Submonoid.smul_def, smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
    refine ⟨⟨⟨π ^ k • z, hint⟩, ⟨_, k, rfl⟩⟩, ?_⟩
    change z * ((algebraMap R (integralClosure R C) π ^ k : integralClosure R C) : C) = π ^ k • z
    rw [SubmonoidClass.coe_pow, Algebra.smul_def, map_pow, mul_comm]
    rfl
  exists_of_eq h := ⟨1, by simpa using Subtype.ext h⟩

section RootAdjunction

open Polynomial

variable (π : R) [Fact (Irreducible π)] (n : ℕ) [NeZero n]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] [Fact (Irreducible π)] in
/-- The root `T` of `Tⁿ - π` in `K' = K[T]/(Tⁿ - π)` is integral over `R`. -/
lemma isIntegral_root_X_pow_sub_C :
    IsIntegral R (AdjoinRoot.root (X ^ n - C (algebraMap R K π))) := by
  refine ⟨X ^ n - C π, monic_X_pow_sub_C π (NeZero.ne n), ?_⟩
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, root_X_pow_sub_C_pow, sub_eq_zero,
    ← IsScalarTower.algebraMap_apply]

/-- XIII.5.1 for a discrete valuation ring, in terms of the normalization: if `n` is prime to the
residue characteristic, every prime of the normalization of `R` in `K' = K[T]/(Tⁿ - π)` over the
maximal ideal has ramification index `n` and inertia degree `1`. -/
lemma ramificationIdx_integralClosure_adjoinRoot
    (hnR : (n : R) ∉ IsLocalRing.maximalIdeal R)
    (Q : Ideal (integralClosure R (AdjoinRoot (X ^ n - C (algebraMap R K π))))) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    Q.ramificationIdx R = n ∧ Q.inertiaDeg R = 1 := by
  set K' := AdjoinRoot (X ^ n - C (algebraMap R K π))
  set p := IsLocalRing.maximalIdeal R
  have : Fact (Irreducible (X ^ n - C (algebraMap R K π))) :=
    ⟨irreducible_X_pow_sub_C_algebraMap π n K⟩
  have : Algebra.Etale K K' := etale_adjoinRoot_X_pow_sub_C_algebraMap π n K hnR
  have : Algebra.IsSeparable K K' := Algebra.FormallyUnramified.isSeparable K _
  have hK'n : Module.finrank K K' = n := finrank_adjoinRoot_X_pow_sub_C _ n
  have := integralClosure.isDedekindDomain' R K K'
  have := integralClosure.finite R K K'
  have := integralClosure.flat R K K'
  have : Module.IsTorsionFree R K' := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq R K K']
    exact (algebraMap K K').injective.comp (IsFractionRing.injective R K))
  have : Module.IsTorsionFree R (integralClosure R K') :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (integralClosure.algebraMap_injective_of_isFractionRing R K K')
  -- `T ∈ Q` and `p S' = (T)ⁿ ⊆ Qⁿ`, so `e(Q) ≥ n`
  let t : integralClosure R K' := ⟨_, isIntegral_root_X_pow_sub_C R π n⟩
  have ht : t ^ n = algebraMap R _ π := Subtype.ext (by
    change AdjoinRoot.root _ ^ n = algebraMap R K' π
    rw [root_X_pow_sub_C_pow, ← IsScalarTower.algebraMap_apply])
  have hπ : π ∈ p := (IsLocalRing.mem_maximalIdeal _).mpr (Fact.out : Irreducible π).not_isUnit
  have htQ : t ∈ Q := by
    have : algebraMap R _ π ∈ Q := by
      rw [← Ideal.mem_comap, ← Ideal.under_def, ← Ideal.over_def Q p]
      exact hπ
    rw [← ht] at this
    exact ‹Q.IsPrime›.mem_of_pow_mem n this
  have hmap : p.map (algebraMap R (integralClosure R K')) ≤ Q ^ n := by
    change (IsLocalRing.maximalIdeal R).map _ ≤ _
    rw [(Fact.out : Irreducible π).maximalIdeal_eq, Ideal.map_span, Set.image_singleton, ← ht,
      ← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).mpr htQ) n
  have he : n ≤ Q.ramificationIdx R := by
    have hne : Q.ramificationIdx R ≠ 0 := (Q.ramificationIdx_pos R).ne'
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx p Q (IsDiscreteValuationRing.not_a_field R)]
      at hne ⊢
    by_cases hb : BddAbove {k | p.map (algebraMap R (integralClosure R K')) ≤ Q ^ k}
    · exact le_csSup hb hmap
    · rw [Ideal.ramificationIdx', Nat.sSup_of_not_bddAbove hb] at hne
      exact absurd rfl hne
  -- the fundamental identity `Σ e f = n` forces `e = n` and `f = 1`
  have : Fintype (p.primesOver (integralClosure R K')) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (integralClosure R K')
  rw [IsIntegralClosure.rank R K K' (integralClosure R K'), hK'n] at hsum
  have hle := Finset.single_le_sum
    (f := fun q : p.primesOver (integralClosure R K') ↦ q.1.ramificationIdx R * q.1.inertiaDeg R)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ ⟨Q, inferInstance, inferInstance⟩)
  rw [hsum] at hle
  replace hle : Q.ramificationIdx R * Q.inertiaDeg R ≤ n := hle
  have hf := Q.inertiaDeg_pos R
  have h1 : Q.ramificationIdx R ≤ Q.ramificationIdx R * Q.inertiaDeg R :=
    Nat.le_mul_of_pos_right _ hf
  have hen : Q.ramificationIdx R = n := le_antisymm (h1.trans hle) he
  refine ⟨hen, ?_⟩
  have : Q.ramificationIdx R * Q.inertiaDeg R ≤ Q.ramificationIdx R * 1 := by
    rw [mul_one]
    exact hle.trans hen.ge
  have := Nat.le_of_mul_le_mul_left this (Q.ramificationIdx_pos R)
  omega

instance fact_irreducible_X_pow_sub_C_algebraMap :
    Fact (Irreducible (X ^ n - C (algebraMap R K π))) :=
  ⟨irreducible_X_pow_sub_C_algebraMap π n K⟩

/-- `K' = K[T]/(Tⁿ - π)` is tamely ramified over `R` when `n` is prime to the residue
characteristic (XIII.5.1). -/
lemma isTameExtension_adjoinRoot (hnR : (n : R) ∉ IsLocalRing.maximalIdeal R) :
    IsTameExtension R (K := K) (AdjoinRoot (X ^ n - C (algebraMap R K π))) := by
  have : Algebra.Etale K (AdjoinRoot (X ^ n - C (algebraMap R K π))) :=
    etale_adjoinRoot_X_pow_sub_C_algebraMap π n K hnR
  have : Algebra.IsSeparable K (AdjoinRoot (X ^ n - C (algebraMap R K π))) :=
    Algebra.FormallyUnramified.isSeparable K _
  rw [isTameExtension_iff_isTamelyRamifiedOver]
  intro Q _ _
  obtain ⟨he, hf⟩ := ramificationIdx_integralClosure_adjoinRoot R π n hnR Q
  rw [isTamelyRamifiedAt_iff_of_liesOver R (IsLocalRing.maximalIdeal R), he]
  refine ⟨fun h ↦ hnR ((natCast_mem_iff_residueField R _ n).mpr h), ?_⟩
  let := Localization.AtPrime.algebraOfLiesOver (IsLocalRing.maximalIdeal R) Q
  rw [Ideal.inertiaDeg_eq (IsLocalRing.maximalIdeal R) Q, ← Field.finSepDegree_mul_finInsepDegree]
    at hf
  exact (isSeparable_iff_finInsepDegree_eq_one _ _).mpr (Nat.eq_one_of_mul_eq_one_left hf)

/-- The map `R[T]/(Tⁿ - π) → K[T]/(Tⁿ - π)`. -/
noncomputable def adjoinRootAlgHom :
    AdjoinRoot (X ^ n - C π) →ₐ[R] AdjoinRoot (X ^ n - C (algebraMap R K π)) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _) (AdjoinRoot.root _) (by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, root_X_pow_sub_C_pow, sub_eq_zero]
    exact (IsScalarTower.algebraMap_apply R K
      (AdjoinRoot (X ^ n - C (algebraMap R K π))) π).symm)

@[simp]
lemma adjoinRootAlgHom_root :
    adjoinRootAlgHom R (K := K) π n (AdjoinRoot.root _) = AdjoinRoot.root _ := by
  simp [adjoinRootAlgHom]

lemma injective_adjoinRootAlgHom : Function.Injective (adjoinRootAlgHom R (K := K) π n) := by
  let ι := adjoinRootAlgHom R (K := K) π n
  rw [injective_iff_map_eq_zero]
  intro x hx
  let pb := AdjoinRoot.powerBasis' (monic_X_pow_sub_C π (NeZero.ne n))
  have hf : X ^ n - C (algebraMap R K π) ≠ 0 := (monic_X_pow_sub_C _ (NeZero.ne n)).ne_zero
  let pb' := AdjoinRoot.powerBasis hf
  have hdim : pb.dim = pb'.dim := by
    simp only [pb, pb', AdjoinRoot.powerBasis'_dim, AdjoinRoot.powerBasis_dim,
      natDegree_X_pow_sub_C]
  rw [← pb.basis.sum_repr x, map_sum] at hx
  have hx' : ∑ i : Fin pb'.dim, algebraMap R K (pb.basis.repr x (Fin.cast hdim.symm i)) •
      pb'.basis i = 0 := by
    rw [← hx]
    refine (Fintype.sum_equiv (finCongr hdim) _ _ fun i ↦ ?_).symm
    rw [map_smul, algebraMap_smul, PowerBasis.coe_basis, PowerBasis.coe_basis, map_pow]
    simp [pb, pb']
  have h := (Fintype.linearIndependent_iff.mp pb'.basis.linearIndependent) _ hx'
  rw [← pb.basis.sum_repr x]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have := h (Fin.cast hdim i)
  rw [Fin.cast_cast, Fin.cast_eq_self,
    map_eq_zero_iff _ (IsFractionRing.injective R K)] at this
  rw [this, zero_smul]

/-- XIII.5.1 for a discrete valuation ring: `K[T]/(Tⁿ - π)` is the fraction field of
`R[T]/(Tⁿ - π)`. -/
theorem isFractionRing_adjoinRoot :
    letI := (adjoinRootAlgHom R (K := K) π n).toRingHom.toAlgebra
    IsFractionRing (AdjoinRoot (X ^ n - C π)) (AdjoinRoot (X ^ n - C (algebraMap R K π))) := by
  let ι := adjoinRootAlgHom R (K := K) π n
  let := ι.toRingHom.toAlgebra
  have : FaithfulSMul (AdjoinRoot (X ^ n - C π)) (AdjoinRoot (X ^ n - C (algebraMap R K π))) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (injective_adjoinRootAlgHom R π n)
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  have hf : X ^ n - C (algebraMap R K π) ≠ 0 := (monic_X_pow_sub_C _ (NeZero.ne n)).ne_zero
  let pb := AdjoinRoot.powerBasis hf
  obtain ⟨⟨b, hb⟩, hbi⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    Finset.univ (fun i ↦ pb.basis.repr z i)
  choose a ha using fun i ↦ hbi i (Finset.mem_univ i)
  refine ⟨∑ i, a i • AdjoinRoot.root (X ^ n - C π) ^ (i : ℕ),
    algebraMap R (AdjoinRoot (X ^ n - C π)) b, ?_⟩
  have hb0 : algebraMap R (AdjoinRoot (X ^ n - C (algebraMap R K π))) b ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R K (AdjoinRoot (X ^ n - C (algebraMap R K π))) b]
    exact (_root_.map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)
  change z = ι _ / ι _
  rw [AlgHom.commutes, eq_div_iff hb0, map_sum, ← pb.basis.sum_repr z, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, map_pow, adjoinRootAlgHom_root, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen,
    Algebra.smul_def, Algebra.smul_def, mul_comm, ← mul_assoc,
    IsScalarTower.algebraMap_apply R K (AdjoinRoot (X ^ n - C (algebraMap R K π))) b,
    IsScalarTower.algebraMap_apply R K (AdjoinRoot (X ^ n - C (algebraMap R K π))) (a i),
    ← map_mul, ha i, Algebra.smul_def, mul_comm (algebraMap R K b)]

/-- XIII.5.1 for a discrete valuation ring: `R[T]/(Tⁿ - π)` is the normalization of `R` in
`K[T]/(Tⁿ - π)`. -/
theorem isIntegralClosure_adjoinRoot :
    letI := (adjoinRootAlgHom R (K := K) π n).toRingHom.toAlgebra
    IsIntegralClosure (AdjoinRoot (X ^ n - C π)) R (AdjoinRoot (X ^ n - C (algebraMap R K π))) := by
  let ι := adjoinRootAlgHom R (K := K) π n
  let := ι.toRingHom.toAlgebra
  have : IsScalarTower R (AdjoinRoot (X ^ n - C π)) (AdjoinRoot (X ^ n - C (algebraMap R K π))) :=
    IsScalarTower.of_algHom ι
  have := isFractionRing_adjoinRoot R (K := K) π n
  exact IsIntegralClosure.of_isIntegrallyClosed _ _ _

variable {π n} in
/-- XIII.5.2 in dimension one: let `R` be a discrete valuation ring with uniformizer `π` and
fraction field `K`, `L` a finite separable extension of `K` tamely ramified over `R`, and `n` a
common multiple of the ramification indices of the primes of the normalization of `R` in `L`
which is prime to the residue characteristic (e.g. their l.c.m., `natCast_lcm_notMem`). Then
every composite `F` of `L` and `K' = K[T]/(Tⁿ - π)` is unramified over `K'`: each prime of the
normalization of `R` in `F` has ramification index `1` over the normalization of `R` in `K'`
(which is `R[T]/(Tⁿ - π)`) and a separable residue field extension. -/
theorem ramificationIdx_eq_one_and_isSeparable_of_adjoinRoot
    (hnR : (n : R) ∉ IsLocalRing.maximalIdeal R) {L F : Type*} [Field L] [Field F]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Algebra (AdjoinRoot (X ^ n - C (algebraMap R K π))) F]
    [IsScalarTower K (AdjoinRoot (X ^ n - C (algebraMap R K π))) F]
    [IsScalarTower R (AdjoinRoot (X ^ n - C (algebraMap R K π))) F]
    (f : L →ₐ[K] F) (hgen : Algebra.adjoin K (Set.range f ∪
      Set.range (algebraMap (AdjoinRoot (X ^ n - C (algebraMap R K π))) F)) = ⊤)
    (hL : IsTameExtension R (K := K) L)
    (hn : ∀ Q : Ideal (integralClosure R L), Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → Q.ramificationIdx R ∣ n)
    (P : Ideal (integralClosure R F)) [P.IsPrime] [P.LiesOver (IsLocalRing.maximalIdeal R)] :
    letI := integralClosure.algebraOfTower R (AdjoinRoot (X ^ n - C (algebraMap R K π))) F
    letI := Localization.AtPrime.algebraOfLiesOver
      (P.under (integralClosure R (AdjoinRoot (X ^ n - C (algebraMap R K π))))) P
    P.ramificationIdx (integralClosure R (AdjoinRoot (X ^ n - C (algebraMap R K π)))) = 1 ∧
      Algebra.IsSeparable
        (P.under (integralClosure R (AdjoinRoot (X ^ n - C (algebraMap R K π))))).ResidueField
        P.ResidueField :=
  ramificationIdx_eq_one_and_isSeparable_of_dvd R f hgen hL
    (isTameExtension_adjoinRoot R π n hnR) (fun Q Q' hQ hQm _ _ ↦ by
      rw [(ramificationIdx_integralClosure_adjoinRoot R π n hnR Q').1]
      exact hn Q hQ hQm) P

variable {π n} in
/-- XIII.5.2 in dimension one, étale form: with the notation of
`ramificationIdx_eq_one_and_isSeparable_of_adjoinRoot`, the normalization of `R` in the composite
`F` is finite étale over the normalization `R'` of `R` in `K' = K[T]/(Tⁿ - π)` (which is
`R[T]/(Tⁿ - π)`, `RootAdjunction`): the restriction of the covering `Spec L` to `Spec K'`
extends (on each connected component `Spec F`) to a finite étale covering of `Spec R'`. -/
theorem etale_integralClosure_of_adjoinRoot
    (hnR : (n : R) ∉ IsLocalRing.maximalIdeal R) {L F : Type*} [Field L] [Field F]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [Algebra (AdjoinRoot (X ^ n - C (algebraMap R K π))) F]
    [IsScalarTower K (AdjoinRoot (X ^ n - C (algebraMap R K π))) F]
    [IsScalarTower R (AdjoinRoot (X ^ n - C (algebraMap R K π))) F]
    (f : L →ₐ[K] F) (hgen : Algebra.adjoin K (Set.range f ∪
      Set.range (algebraMap (AdjoinRoot (X ^ n - C (algebraMap R K π))) F)) = ⊤)
    (hL : IsTameExtension R (K := K) L)
    (hn : ∀ Q : Ideal (integralClosure R L), Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → Q.ramificationIdx R ∣ n) :
    letI := integralClosure.algebraOfTower R (AdjoinRoot (X ^ n - C (algebraMap R K π))) F
    Module.Finite (integralClosure R (AdjoinRoot (X ^ n - C (algebraMap R K π))))
        (integralClosure R F) ∧
      Algebra.Etale (integralClosure R (AdjoinRoot (X ^ n - C (algebraMap R K π))))
        (integralClosure R F) :=
  etale_integralClosure_of_dvd R f hgen hL (isTameExtension_adjoinRoot R π n hnR)
    fun Q Q' hQ hQm _ _ ↦ by
      rw [(ramificationIdx_integralClosure_adjoinRoot R π n hnR Q').1]
      exact hn Q hQ hQm

/-- XIII.5.2: the l.c.m. `n` of the ramification indices of a tamely ramified extension `L` is
nonzero and prime to the residue characteristic. -/
lemma natCast_lcm_notMem (L : Type*) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hL : IsTameExtension R (K := K) L) (n : ℕ)
    (hmin : ∀ k : ℕ, (∀ Q : Ideal (integralClosure R L), Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → Q.ramificationIdx R ∣ k) → n ∣ k) :
    n ≠ 0 ∧ (n : R) ∉ IsLocalRing.maximalIdeal R := by
  set p := IsLocalRing.maximalIdeal R
  have := integralClosure.finite R K L
  have : Fintype (p.primesOver (integralClosure R L)) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  set k := ∏ q : p.primesOver (integralClosure R L), q.1.ramificationIdx R
  have hk : n ∣ k := hmin k fun Q hQ hQm ↦ Finset.dvd_prod_of_mem
    (fun q : p.primesOver (integralClosure R L) ↦ q.1.ramificationIdx R)
    (Finset.mem_univ ⟨Q, hQ, hQm⟩)
  have htame := (isTameExtension_iff_isTamelyRamifiedOver R L).mp hL
  have hk0 : (k : R) ∉ p := by
    rw [natCast_mem_iff_residueField, Nat.cast_prod, Finset.prod_eq_zero_iff]
    rintro ⟨q, -, hq⟩
    have := q.2.1
    have := q.2.2
    have h := htame q.1 this
    rw [isTamelyRamifiedAt_iff_of_liesOver R p] at h
    exact h.1 hq
  refine ⟨fun h0 ↦ ?_, fun hn' ↦ hk0 ?_⟩
  · rw [h0, zero_dvd_iff] at hk
    exact hk0 (by rw [hk, Nat.cast_zero]; exact zero_mem _)
  · obtain ⟨c, hc⟩ := hk
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hn'

end RootAdjunction

section StrictlyHenselian

variable [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]

/-- Over a strictly henselian discrete valuation ring, a tamely ramified finite separable
extension `E/K` is totally ramified: the prime over the maximal ideal has ramification index
`[E : K]`. -/
lemma ramificationIdx_eq_finrank_of_isTameExtension (E : Type*) [Field E] [Algebra K E]
    [Algebra R E] [IsScalarTower R K E] [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (hE : IsTameExtension R (K := K) E) (Q : Ideal (integralClosure R E)) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    Q.ramificationIdx R = Module.finrank K E := by
  set p := IsLocalRing.maximalIdeal R
  have := integralClosure.finite R K E
  have := integralClosure.flat R K E
  have : Module.IsTorsionFree R E := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq R K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective R K))
  have hrank : Module.finrank R (integralClosure R E) = Module.finrank K E :=
    IsIntegralClosure.rank R K E (integralClosure R E)
  have : Fintype (p.primesOver (integralClosure R E)) :=
    (Algebra.QuasiFinite.finite_primesOver p).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (integralClosure R E)
  have huniq (q : p.primesOver (integralClosure R E)) : q = ⟨Q, inferInstance, inferInstance⟩ := by
    have := q.2.1
    have := q.2.2
    exact Subtype.ext (HenselianLocalRing.eq_of_liesOver (A := R) q.1 Q)
  have : Subsingleton (p.primesOver (integralClosure R E)) :=
    ⟨fun a b ↦ (huniq a).trans (huniq b).symm⟩
  rw [Fintype.sum_subsingleton _ ⟨Q, inferInstance, inferInstance⟩, hrank] at hsum
  -- the residue extension is trivial: separable and purely inseparable
  have ht := (isTameExtension_iff_isTamelyRamifiedOver R E).mp hE Q inferInstance
  rw [isTamelyRamifiedAt_iff_of_liesOver R p] at ht
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsSepClosed p.ResidueField :=
    IsSepClosed.of_ringEquiv (IsLocalRing.residueFieldEquivResidueFieldMaximalIdeal R)
  have := ht.2
  have hf : Q.inertiaDeg R = 1 := by
    rw [Ideal.inertiaDeg_eq p Q, ← Field.finSepDegree_mul_finInsepDegree,
      IsPurelyInseparable.finSepDegree_eq_one, Algebra.IsSeparable.finInsepDegree_eq, mul_one]
  rw [hf, mul_one] at hsum
  exact hsum

/-- The key step of XIII.5.3 in dimension one: over a strictly henselian discrete valuation ring,
if `L` and `K'` are tamely ramified of the same degree, every composite `F` of `L` and `K'` equals
`K'` (it is unramified over `K'`, and the residue field of `K'` is separably closed). -/
lemma bijective_algebraMap_of_composite {L K' F : Type*} [Field L] [Field K'] [Field F]
    [Algebra K L] [Algebra K K'] [Algebra K F] [Algebra R L] [Algebra R K'] [Algebra R F]
    [IsScalarTower R K L] [IsScalarTower R K K'] [IsScalarTower R K F] [Algebra K' F]
    [IsScalarTower K K' F] [IsScalarTower R K' F] [FiniteDimensional K F]
    [Algebra.IsSeparable K F] (f : L →ₐ[K] F)
    (hgen : Algebra.adjoin K (Set.range f ∪ Set.range (algebraMap K' F)) = ⊤)
    (hL : IsTameExtension R (K := K) L) (hK' : IsTameExtension R (K := K) K')
    (hLK' : Module.finrank K L = Module.finrank K K') :
    Function.Bijective (algebraMap K' F) := by
  have : FiniteDimensional K L := FiniteDimensional.of_injective f.toLinearMap f.injective
  have : Algebra.IsSeparable K L := Algebra.IsSeparable.of_algHom (F := K) (E := L) (E' := F) f
  have : FiniteDimensional K K' := FiniteDimensional.of_injective
    (IsScalarTower.toAlgHom K K' F).toLinearMap (algebraMap K' F).injective
  have : Algebra.IsSeparable K K' :=
    Algebra.IsSeparable.of_algHom (F := K) (E := K') (E' := F) (IsScalarTower.toAlgHom K K' F)
  have hF : IsTameExtension R (K := K) F :=
    IsTameExtension.of_adjoin_eq_top R f (IsScalarTower.toAlgHom K K' F) hgen hL hK'
  have := integralClosure.finite R K F
  have : FaithfulSMul R (integralClosure R F) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (integralClosure.algebraMap_injective_of_isFractionRing R K F)
  obtain ⟨P, hP, hPm⟩ := (inferInstance : Nonempty ((IsLocalRing.maximalIdeal R).primesOver
    (integralClosure R F)))
  have key := ramificationIdx_eq_one_and_isSeparable_of_dvd R f hgen hL hK'
    (fun Q Q' _ _ _ _ ↦ by
      rw [ramificationIdx_eq_finrank_of_isTameExtension R L hL Q,
        ramificationIdx_eq_finrank_of_isTameExtension R K' hK' Q', hLK']) P
  -- `[F : K] = e(P) = e(P ∩ K') e(P / P ∩ K') = [K' : K]`
  let := integralClosure.algebraOfTower R K' F
  have := integralClosure.flat_of_tower R K' F K
  have htower := Ideal.ramificationIdx_tower (R := R) (P.under (integralClosure R K')) P
  rw [key.1, mul_one, ramificationIdx_eq_finrank_of_isTameExtension R F hF P,
    ramificationIdx_eq_finrank_of_isTameExtension R K' hK'] at htower
  refine ⟨(algebraMap K' F).injective, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank htower.symm
    (f := (IsScalarTower.toAlgHom K K' F).toLinearMap)).mp (algebraMap K' F).injective

open Polynomial in
/-- XIII.5.3 in dimension one: let `R` be a strictly henselian discrete valuation ring with
uniformizer `π` and fraction field `K`. Every tamely ramified finite separable extension `L` of
`K` is a quotient of a Kummer covering: `n = [L : K]` is prime to the residue characteristic and
`L` is isomorphic to `K[T]/(Tⁿ - π)`. (SGA states this for a regular strictly local scheme of any
dimension and a divisor with normal crossings; this is the case of dimension one, where `L` is the
function field of a connected tamely ramified covering of `U = Spec K`.) -/
theorem nonempty_algEquiv_adjoinRoot_of_isTameExtension (π : R) [Fact (Irreducible π)]
    (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (hL : IsTameExtension R (K := K) L) :
    ¬ ringChar (IsLocalRing.ResidueField R) ∣ Module.finrank K L ∧
      Nonempty (L ≃ₐ[K] AdjoinRoot (X ^ Module.finrank K L - C (algebraMap R K π))) := by
  have hn : ¬ ringChar (IsLocalRing.ResidueField R) ∣ Module.finrank K L :=
    (isTameExtension_iff_not_dvd_finrank R L).mp hL
  refine ⟨hn, ?_⟩
  have : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  have hnR : (Module.finrank K L : R) ∉ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast,
      CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R) (ringChar _)]
    exact hn
  have : Fact (Irreducible (X ^ Module.finrank K L - C (algebraMap R K π))) :=
    ⟨irreducible_X_pow_sub_C_algebraMap π _ K⟩
  have : Algebra.Etale K (AdjoinRoot (X ^ Module.finrank K L - C (algebraMap R K π))) :=
    etale_adjoinRoot_X_pow_sub_C_algebraMap π _ K hnR
  have : Algebra.IsSeparable K (AdjoinRoot (X ^ Module.finrank K L - C (algebraMap R K π))) :=
    Algebra.FormallyUnramified.isSeparable K _
  have hK'n : Module.finrank K (AdjoinRoot (X ^ Module.finrank K L - C (algebraMap R K π))) =
      Module.finrank K L := finrank_adjoinRoot_X_pow_sub_C _ _
  have hK' : IsTameExtension R (K := K)
      (AdjoinRoot (X ^ Module.finrank K L - C (algebraMap R K π))) := by
    rw [isTameExtension_iff_not_dvd_finrank, hK'n]
    exact hn
  have : Algebra.FormallyEtale K L := .of_isSeparable K L
  have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale K L := {}
  -- a composite `F` of `L` and `K'`: a residue field of `K' ⊗_K L`
  have : Algebra.Etale K (TensorProduct K
      (AdjoinRoot (X ^ Module.finrank K L - C (algebraMap R K π))) L) := Algebra.Etale.comp K
    (AdjoinRoot (X ^ Module.finrank K L - C (algebraMap R K π))) _
  have : Module.Finite K (TensorProduct K
      (AdjoinRoot (X ^ Module.finrank K L - C (algebraMap R K π))) L) :=
    Algebra.FormallyUnramified.finite_of_free K _
  have : Nontrivial (TensorProduct K
      (AdjoinRoot (X ^ Module.finrank K L - C (algebraMap R K π))) L) :=
    Module.nontrivial_of_finrank_pos (R := K) (by
      rw [Module.finrank_tensorProduct]
      exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct K
    (AdjoinRoot (X ^ Module.finrank K L - C (algebraMap R K π))) L)
  let := Ideal.Quotient.field m
  let f := (Ideal.Quotient.mkₐ K m).comp (Algebra.TensorProduct.includeRight (R := K)
    (A := AdjoinRoot (X ^ Module.finrank K L - C (algebraMap R K π))) (B := L))
  have hgen : Algebra.adjoin K (Set.range f ∪ Set.range (algebraMap
      (AdjoinRoot (X ^ Module.finrank K L - C (algebraMap R K π))) (TensorProduct K
        (AdjoinRoot (X ^ Module.finrank K L - C (algebraMap R K π))) L ⧸ m))) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have : Ideal.Quotient.mk m (a ⊗ₜ[K] b) = algebraMap _ _ a * f b := by
        rw [← Ideal.Quotient.mk_algebraMap, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply]
        simp only [f, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
          Algebra.TensorProduct.includeRight_apply, ← map_mul,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact mul_mem (Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩))
        (Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩))
    | add x y hx hy => simpa using add_mem hx hy
  have hbij := bijective_algebraMap_of_composite R f hgen hL hK' hK'n.symm
  let g := (AlgEquiv.ofBijective (IsScalarTower.toAlgHom K _ _) hbij).symm.toAlgHom.comp f
  have hg : Function.Bijective g := ⟨g.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hK'n.symm
      (f := g.toLinearMap)).mp g.injective⟩
  exact ⟨AlgEquiv.ofBijective g hg⟩

end StrictlyHenselian

end DiscreteValuationRing

section DimensionOne

/-! ### XIII.5.2 and XIII.5.3 for regular local rings of dimension one

A regular local ring `A` of dimension one with `f₁` part of a regular system of parameters is a
discrete valuation ring with uniformizer `f₁`, and `A[1/f₁]` is its fraction field. -/

open Polynomial

/-- A regular local ring of dimension one in which the single element `f 0` is part of a regular
system of parameters is a discrete valuation ring with uniformizer `f 0`. -/
lemma isDiscreteValuationRing_of_ringKrullDim_eq_one {A : Type*} [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 1) (f : Fin 1 → A)
    (hf : IsPartOfRegularSystemOfParameters f) :
    IsDiscreteValuationRing A ∧ maximalIdeal A = Ideal.span {f 0} := by
  obtain ⟨k, g, hmax, hk⟩ := hf
  rw [hdim, Nat.card_eq_fintype_card, Fintype.card_fin] at hk
  have hk0 : k = 0 := by
    have : 1 + k = 1 := by exact_mod_cast hk
    omega
  subst hk0
  have hm : maximalIdeal A = Ideal.span {f 0} := by
    rw [hmax]
    congr 1
    ext x
    simp [Set.range_eq_empty, eq_comm, Fin.exists_fin_one]
  have hnf : ¬ IsField A := fun h ↦ by
    have := ringKrullDim_eq_zero_of_isField h
    rw [hdim] at this
    exact absurd this (by decide)
  have hp : (maximalIdeal A).IsPrincipal := ⟨⟨f 0, hm⟩⟩
  exact ⟨((IsDiscreteValuationRing.TFAE A hnf).out 1 5).mpr hp, hm⟩

/-- For a discrete valuation ring with uniformizer `π`, `A[1/π]` is the fraction field. -/
lemma isFractionRing_away_of_irreducible {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {π : A} (hπ : Irreducible π) :
    IsFractionRing A (Localization.Away π) := by
  refine IsLocalization.of_le (Submonoid.powers π) (nonZeroDivisors A)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) fun r hr ↦ ?_
  obtain ⟨n, u, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hr) hπ
  rw [map_mul, map_pow]
  exact (u.isUnit.map _).mul ((IsLocalization.Away.algebraMap_isUnit π).pow n)

/-- For an `A[1/π]`-algebra `B` with `A[1/π]` the fraction field of `A`, `Frac A ⊗_A B = B`. -/
noncomputable def fractionRingTensorAlgEquiv {A : Type*} [CommRing A] [IsDomain A] (π : A)
    [IsFractionRing A (Localization.Away π)] (B : Type*) [CommRing B] [Algebra A B]
    [Algebra (Localization.Away π) B] [IsScalarTower A (Localization.Away π) B] :
    FractionRing A ⊗[A] B ≃ₐ[A] B :=
  (Algebra.TensorProduct.congr
    (IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing A) (Localization.Away π))
    AlgEquiv.refl).trans
    ((IsLocalization.algebraLid (Submonoid.powers π) (Localization.Away π) B).restrictScalars A)

/-- XIII.5.3 for a regular strictly local ring `A` of dimension one and `r = 1` (so that `A` is a
strictly henselian discrete valuation ring with uniformizer `f₁`): every connected (integral)
finite étale `A[1/f₁]`-algebra `B` tamely ramified along `div f₁` is a quotient of a Kummer
covering, i.e. embeds in `A[1/f₁][T]/(Tⁿ - f₁)` with `n` prime to the residue characteristic
(here `n = [B : A[1/f₁]]` and the embedding is an isomorphism). This is
`TameCoveringsOfStrictlyLocalAt A 1` for `dim A = 1`
(`tameCoveringsOfStrictlyLocalAt_of_ringKrullDim_eq_one`). -/
theorem exists_injective_kummerAlgebra_of_ringKrullDim_eq_one (A : Type u) [CommRing A]
    [IsRegularLocalRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    (hdim : ringKrullDim A = 1) (f : Fin 1 → A) (hf : IsPartOfRegularSystemOfParameters f)
    (B : Type u) [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B) :
    ∃ n : Fin 1 → ℕ, (∀ i, 0 < n i ∧ (n i : A) ∉ maximalIdeal A) ∧
      ∃ φ : B →ₐ[Localization.Away (∏ i, f i)]
          KummerAlgebra n (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i)),
        Function.Injective φ := by
  obtain ⟨hdvr, hm⟩ := isDiscreteValuationRing_of_ringKrullDim_eq_one hdim f hf
  have hprod : ∏ i, f i = f 0 := Fin.prod_univ_one f
  have hπ : Irreducible (∏ i, f i) := by
    rw [hprod]
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hm
  have : Fact (Irreducible (∏ i, f i)) := ⟨hπ⟩
  have : IsFractionRing A (Localization.Away (∏ i, f i)) := isFractionRing_away_of_irreducible hπ
  -- `B` is tamely ramified over `A` (before choosing field structures)
  have hB' : IsTamelyRamifiedOver A (integralClosure A B) := by
    refine IsTamelyRamifiedOver.of_algEquiv (S := integralClosure A (FractionRing A ⊗[A] B)) A
      ?_ fun Q _ hQ ↦ ?_
    · exact (fractionRingTensorAlgEquiv (∏ i, f i) B).mapIntegralClosure
    · have : Q.LiesOver (Ideal.span {f 0}) := hm ▸ hQ
      exact hB 0 Q this
  let : Field (Localization.Away (∏ i, f i)) := IsFractionRing.toField A
  let : Field B :=
    (isField_of_isIntegral_of_isField' (R := Localization.Away (∏ i, f i))
      (Field.toIsField _)).toField
  have : Algebra.IsSeparable (Localization.Away (∏ i, f i)) B :=
    Algebra.FormallyUnramified.isSeparable _ _
  have htame : IsTameExtension A (K := Localization.Away (∏ i, f i)) B :=
    (isTameExtension_iff_isTamelyRamifiedOver A B).mpr hB'
  obtain ⟨hn, ⟨eB⟩⟩ := nonempty_algEquiv_adjoinRoot_of_isTameExtension A (∏ i, f i) B htame
  set n := Module.finrank (Localization.Away (∏ i, f i)) B
  have hnR : (n : A) ∉ maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast,
      CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) (ringChar _)]
    exact hn
  refine ⟨fun _ ↦ n, fun _ ↦ ⟨Module.finrank_pos, hnR⟩, ?_⟩
  have : NeZero n := ⟨Module.finrank_pos.ne'⟩
  have hT : (KummerAlgebra.T (fun _ ↦ n)
      (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i)) 0) ^ n =
      algebraMap _ _ (algebraMap A (Localization.Away (∏ i, f i)) (∏ i, f i)) := by
    rw [KummerAlgebra.T_pow, hprod]
  let ψ := AdjoinRoot.liftAlgHom
    (X ^ n - C (algebraMap A (Localization.Away (∏ i, f i)) (∏ i, f i)))
    (Algebra.ofId _ _)
    (KummerAlgebra.T (fun _ ↦ n) (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i)) 0)
    (by rw [eval₂_sub, eval₂_X_pow, eval₂_C, hT, sub_eq_zero]; rfl)
  -- the Kummer algebra is nonzero: it maps to `K[T]/(Tⁿ - π)`
  have : Nontrivial (KummerAlgebra (fun _ : Fin 1 ↦ n)
      (fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i))) := by
    let χ := KummerAlgebra.lift (n := fun _ : Fin 1 ↦ n)
      (f := fun i ↦ algebraMap A (Localization.Away (∏ i, f i)) (f i))
      (A := AdjoinRoot (X ^ n - C (algebraMap A (Localization.Away (∏ i, f i)) (∏ i, f i))))
      (fun _ ↦ AdjoinRoot.root _) fun i ↦ by
        rw [root_X_pow_sub_C_pow, Fin.eq_zero i, hprod]
    exact χ.toRingHom.domain_nontrivial
  exact ⟨ψ.comp eB.toAlgHom, (ψ.comp eB.toAlgHom).injective⟩

/-- For a discrete valuation ring `A` and a nonzero `t` in the maximal ideal, `A[1/t]` is the
fraction field of `A`. -/
lemma isFractionRing_away_of_mem_maximalIdeal {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {t : A} (ht0 : t ≠ 0) (htm : t ∈ maximalIdeal A) :
    IsFractionRing A (Localization.Away t) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨j, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hϖ
  have hj : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hv
    exact (IsLocalRing.mem_maximalIdeal _).mp htm (hv ▸ v.isUnit)
  have hϖu : IsUnit (algebraMap A (Localization.Away t) ϖ) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away t) t
    have h2 : algebraMap A (Localization.Away t) t =
        algebraMap A _ (v : A) * (algebraMap A _ ϖ) ^ j := by
      rw [← map_pow, ← map_mul, ← hv]
    rw [h2] at h
    exact (isUnit_pow_iff hj).mp (isUnit_of_mul_isUnit_right h)
  refine IsLocalization.of_le (Submonoid.powers t) (nonZeroDivisors A)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ht0) fun r hr ↦ ?_
  obtain ⟨n, u, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hr) hϖ
  rw [map_mul, map_pow]
  exact (u.isUnit.map _).mul (hϖu.pow n)

/-- XIII.5.2 in dimension one, reduction to fields. Let `A` be a discrete valuation ring with
uniformizer `f₁`, `K = A[1/f₁]` and `B` a finite étale `K`-algebra tamely ramified along `div f₁`,
and `n` the l.c.m. of the ramification indices. Then `n` is prime to the residue characteristic,
and every factor `B/M` of `B` is tamely ramified with ramification indices dividing `n`. -/
lemma tame_factors_of_isTamelyRamifiedAlong {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (f : Fin 1 → A) (hm : maximalIdeal A = Ideal.span {f 0})
    [IsFractionRing A (Localization.Away (∏ i, f i))] (B : Type u) [CommRing B] [Algebra A B]
    [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B)
    (n : Fin 1 → ℕ) (hn : ∀ i, IsLcmRamificationIndices (Ideal.span {f i}) B (n i)) :
    (n 0 : A) ∉ maximalIdeal A ∧ ∀ M : MaximalSpectrum B,
      IsTamelyRamifiedOver A (integralClosure A (B ⧸ M.asIdeal)) ∧
      ∀ Q : Ideal (integralClosure A (B ⧸ M.asIdeal)), Q.IsPrime →
        Q.LiesOver (maximalIdeal A) → Q.ramificationIdx A ∣ n 0 := by
  let : Field (Localization.Away (∏ i, f i)) := IsFractionRing.toField A
  have : IsArtinianRing B := IsArtinianRing.of_finite (Localization.Away (∏ i, f i)) B
  have : IsReduced B := Algebra.FormallyUnramified.isReduced_of_field
    (Localization.Away (∏ i, f i)) B
  -- the hypotheses, for the normalization of `A` in `B ≅ Frac A ⊗_A B`
  have hB' : ∀ (Q : Ideal (integralClosure A B)) [Q.IsPrime], Q.LiesOver (Ideal.span {f 0}) →
      IsTamelyRamifiedAt A Q := by
    refine forall_isTamelyRamifiedAt_of_algEquiv (S := integralClosure A (FractionRing A ⊗[A] B))
      A ?_ _ (hB 0)
    exact (fractionRingTensorAlgEquiv (∏ i, f i) B).mapIntegralClosure
  have hn' : ∀ (Q : Ideal (integralClosure A B)), Q.IsPrime → Q.LiesOver (Ideal.span {f 0}) →
      Q.ramificationIdx A ∣ n 0 := by
    refine forall_ramificationIdx_dvd_of_algEquiv
      (S := integralClosure A (FractionRing A ⊗[A] B)) A ?_ _ _ (hn 0).1
    exact (fractionRingTensorAlgEquiv (∏ i, f i) B).mapIntegralClosure
  have hmin' : ∀ k : ℕ, (∀ (Q : Ideal (integralClosure A B)), Q.IsPrime →
      Q.LiesOver (Ideal.span {f 0}) → Q.ramificationIdx A ∣ k) → n 0 ∣ k := by
    intro k hk
    refine (hn 0).2 k (forall_ramificationIdx_dvd_of_algEquiv
      (S' := integralClosure A (FractionRing A ⊗[A] B)) A ?_ _ _ hk)
    exact ((fractionRingTensorAlgEquiv (∏ i, f i) B).mapIntegralClosure).symm
  let Φ := ((IsArtinianRing.equivPi B).restrictScalars A).mapIntegralClosure.trans
      (integralClosure.piAlgEquiv A (fun M : MaximalSpectrum B ↦ B ⧸ M.asIdeal))
  let φ := Φ.toAlgHom
  -- the primes of the normalization of `B` are those of the factors
  have key (M : MaximalSpectrum B) (Q : Ideal (integralClosure A (B ⧸ M.asIdeal))) [Q.IsPrime] :
      (IsTamelyRamifiedAt A ((Q.comap (Pi.evalAlgHom A
        (fun M : MaximalSpectrum B ↦ integralClosure A (B ⧸ M.asIdeal)) M)).comap φ) ↔
        IsTamelyRamifiedAt A Q) ∧
      ((Q.comap (Pi.evalAlgHom A
        (fun M : MaximalSpectrum B ↦ integralClosure A (B ⧸ M.asIdeal)) M)).comap φ).ramificationIdx
          A = Q.ramificationIdx A ∧
      ((Q.comap (Pi.evalAlgHom A
        (fun M : MaximalSpectrum B ↦ integralClosure A (B ⧸ M.asIdeal)) M)).comap φ).under A =
          Q.under A := by
    have h1 := Ideal.bijective_localAlgHom_evalAlgHom (A := A)
      (L := fun M : MaximalSpectrum B ↦ integralClosure A (B ⧸ M.asIdeal)) M Q
    have h3 := bijective_localAlgHom_algEquiv A Φ (Q.comap (Pi.evalAlgHom A
      (fun M : MaximalSpectrum B ↦ integralClosure A (B ⧸ M.asIdeal)) M))
    refine ⟨(isTamelyRamifiedAt_comap_iff_of_bijective A _ _ h3).trans
      (isTamelyRamifiedAt_comap_iff_of_bijective A _ _ h1), ?_, ?_⟩
    · rw [Ideal.ramificationIdx_comap_of_bijective _ _ h3,
        Ideal.ramificationIdx_comap_of_bijective _ _ h1]
    · rw [Ideal.under_comap_algHom, Ideal.under_comap_algHom]
  have hsurj (P : Ideal (integralClosure A B)) [P.IsPrime] :
      ∃ (M : MaximalSpectrum B) (Q : Ideal (integralClosure A (B ⧸ M.asIdeal))) (_ : Q.IsPrime),
        P = (Q.comap (Pi.evalAlgHom A
          (fun M : MaximalSpectrum B ↦ integralClosure A (B ⧸ M.asIdeal)) M)).comap φ := by
    obtain ⟨M, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
      ⟨P.comap Φ.symm.toAlgHom, Ideal.comap_isPrime _ _⟩
    refine ⟨M, q.asIdeal, q.isPrime, ?_⟩
    have hq' : q.asIdeal.comap (Pi.evalAlgHom A
        (fun M : MaximalSpectrum B ↦ integralClosure A (B ⧸ M.asIdeal)) M) =
        P.comap Φ.symm.toAlgHom :=
      congrArg PrimeSpectrum.asIdeal hq
    rw [hq']
    ext x
    simp [φ]
  have hmax (M : MaximalSpectrum B) (Q : Ideal (integralClosure A (B ⧸ M.asIdeal)))
      [Q.IsPrime] (hQ : Q.LiesOver (maximalIdeal A)) :
      ((Q.comap (Pi.evalAlgHom A
        (fun M : MaximalSpectrum B ↦ integralClosure A (B ⧸ M.asIdeal)) M)).comap φ).LiesOver
          (Ideal.span {f 0}) := ⟨by
    rw [(key M Q).2.2, ← hm, ← Ideal.over_def Q (maximalIdeal A)]⟩
  -- the factors are tamely ramified, with ramification indices dividing `n`
  have htame (M : MaximalSpectrum B) :
      IsTamelyRamifiedOver A (integralClosure A (B ⧸ M.asIdeal)) := fun Q _ hQ ↦
    (key M Q).1.mp (hB' _ (hmax M Q hQ))
  have hdvd (M : MaximalSpectrum B) (Q : Ideal (integralClosure A (B ⧸ M.asIdeal)))
      (_ : Q.IsPrime) (hQ : Q.LiesOver (maximalIdeal A)) : Q.ramificationIdx A ∣ n 0 := by
    rw [← (key M Q).2.1]
    exact hn' _ inferInstance (hmax M Q hQ)
  refine ⟨?_, fun M ↦ ⟨htame M, hdvd M⟩⟩
  -- `n` is prime to the residue characteristic
  have hfin (M : MaximalSpectrum B) : Module.Finite A (integralClosure A (B ⧸ M.asIdeal)) := by
    let := Ideal.Quotient.field M.asIdeal
    exact integralClosure.finite A (Localization.Away (∏ i, f i)) (B ⧸ M.asIdeal)
  have (M : MaximalSpectrum B) : Fintype ((maximalIdeal A).primesOver
      (integralClosure A (B ⧸ M.asIdeal))) :=
    (Algebra.QuasiFinite.finite_primesOver (maximalIdeal A)).fintype
  have : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  set k := ∏ M : MaximalSpectrum B, ∏ q : (maximalIdeal A).primesOver
    (integralClosure A (B ⧸ M.asIdeal)), q.1.ramificationIdx A
  have hk : n 0 ∣ k := by
    refine hmin' k fun P _ hP ↦ ?_
    obtain ⟨M, Q, _, rfl⟩ := hsurj P
    have hQm : Q.LiesOver (maximalIdeal A) := ⟨by
      rw [← (key M Q).2.2, hm, ← Ideal.over_def _ (Ideal.span {f 0})]⟩
    rw [(key M Q).2.1]
    exact (Finset.dvd_prod_of_mem (fun q : (maximalIdeal A).primesOver
      (integralClosure A (B ⧸ M.asIdeal)) ↦ q.1.ramificationIdx A)
        (Finset.mem_univ ⟨Q, inferInstance, hQm⟩)).trans
      (Finset.dvd_prod_of_mem (fun M : MaximalSpectrum B ↦ ∏ q : (maximalIdeal A).primesOver
        (integralClosure A (B ⧸ M.asIdeal)), q.1.ramificationIdx A) (Finset.mem_univ M))
  have hk0 : (k : A) ∉ maximalIdeal A := by
    simp only [k, Nat.cast_prod]
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨M, -, hM⟩
    rw [Ideal.IsPrime.prod_mem_iff] at hM
    obtain ⟨q, -, hq⟩ := hM
    have := q.2.1
    have := q.2.2
    have h := htame M q.1 q.2.2
    rw [isTamelyRamifiedAt_iff_of_liesOver A (maximalIdeal A)] at h
    exact h.1 ((natCast_mem_iff_residueField A _ _).mp hq)
  obtain ⟨c, hc⟩ := hk
  intro hn0
  apply hk0
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hn0

namespace KummerAlgebra

variable {A : Type*} [CommRing A] (n : Fin 1 → ℕ) (f : Fin 1 → A)

/-- With one variable, `A[T]/(Tⁿ - f)` is `AdjoinRoot (Tⁿ - f)`. -/
noncomputable def equivAdjoinRoot :
    KummerAlgebra n f ≃ₐ[A] AdjoinRoot (X ^ n 0 - C (f 0)) :=
  AlgEquiv.ofAlgHom
    (lift (fun _ ↦ AdjoinRoot.root _) fun i ↦ by
      rw [Fin.eq_zero i, root_X_pow_sub_C_pow])
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (T n f 0) (by
      simp [eval₂_sub, T_pow]))
    (AdjoinRoot.algHom_ext (by simp))
    (algHom_ext fun i ↦ by rw [Fin.eq_zero i]; simp)

/-- With one variable, `A[T]/(Tⁿ - f)` is `AdjoinRoot (Tⁿ - ∏ f)`. -/
noncomputable def equivAdjoinRootProd :
    KummerAlgebra n f ≃ₐ[A] AdjoinRoot (X ^ n 0 - C (∏ i, f i)) := by
  rw [Fin.prod_univ_one]
  exact equivAdjoinRoot n f

end KummerAlgebra

/-- Finiteness and formal étaleness are transported along an isomorphism of the base. -/
lemma finite_and_formallyEtale_of_ringEquiv {S I W : Type*} [CommRing S] [CommRing I]
    [CommRing W] {_ : Algebra I W} [Algebra S W] (σ : S ≃+* I)
    (h : ∀ s, algebraMap S W s = algebraMap I W (σ s)) (h1 : Module.Finite I W)
    (h2 : Algebra.FormallyEtale I W) :
    Module.Finite S W ∧ Algebra.FormallyEtale S W := by
  let : Algebra S I := σ.toRingHom.toAlgebra
  have : IsScalarTower S I W := .of_algebraMap_eq h
  let e : S ≃ₐ[S] I := AlgEquiv.ofRingEquiv (f := σ) fun _ ↦ rfl
  have : Module.Finite S I := Module.Finite.equiv e.toLinearEquiv
  have : Algebra.FormallyEtale S I := Algebra.FormallyEtale.of_equiv e
  exact ⟨Module.Finite.trans I W, Algebra.FormallyEtale.comp S I W⟩

set_option maxHeartbeats 1600000 in
-- the instance problems on the quotients of `B ⊗_R S` and their normalizations are large
/-- XIII.5.2 for a discrete valuation ring `R` with uniformizer `π`, algebra form. Let
`S ≅ R[T]/(Tⁿ - π)` with `n` prime to the residue characteristic (such that `K ⊗_R S` is étale
over `K`), and `B` a finite étale `K`-algebra whose factors are tamely ramified over `R` with
ramification indices dividing `n`. Then the normalization `W` of `R` in `B ⊗_R S` is finite étale
over `S` and `S ⊗_R B = S[1/π] ⊗_S W`. -/
theorem exists_etale_of_forall_isTamelyRamifiedOver (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (π : R)
    [Fact (Irreducible π)] (n : ℕ) [NeZero n] (hnR : (n : R) ∉ maximalIdeal R) (S : Type u)
    [CommRing S] [Algebra R S] (ρ : S ≃ₐ[R] AdjoinRoot (X ^ n - C π))
    [Algebra.Etale K (K ⊗[R] S)] (B : Type u) [CommRing B] [Algebra K B] [Algebra R B]
    [IsScalarTower R K B] [Module.Finite K B] [Algebra.Etale K B]
    (htame : ∀ M : MaximalSpectrum B, IsTamelyRamifiedOver R (integralClosure R (B ⧸ M.asIdeal)))
    (hdvd : ∀ (M : MaximalSpectrum B) (Q : Ideal (integralClosure R (B ⧸ M.asIdeal))),
      Q.IsPrime → Q.LiesOver (maximalIdeal R) → Q.ramificationIdx R ∣ n) :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra S W), Module.Finite S W ∧ Algebra.Etale S W ∧
      Nonempty (S ⊗[R] B ≃ₐ[S] Localization.Away (algebraMap R S π) ⊗[S] W) := by
  classical
  have : Module.Finite R S := Module.Finite.equiv ρ.symm.toLinearEquiv
  -- `B ⊗_R S` is finite étale over `K`
  have : Algebra.Etale B (B ⊗[R] S) := Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange (R := R) (S := K) (T := B) (A := B) (B := S))
  have : Module.Finite B (B ⊗[R] S) := Module.Finite.equiv
    (Algebra.TensorProduct.cancelBaseChange (R := R) (S := K) (T := B) (A := B)
      (B := S)).toLinearEquiv
  have : Algebra.Etale K (B ⊗[R] S) := Algebra.Etale.comp K B (B ⊗[R] S)
  have : Module.Finite K (B ⊗[R] S) := Module.Finite.trans B (B ⊗[R] S)
  have : IsArtinianRing (B ⊗[R] S) := IsArtinianRing.of_finite K (B ⊗[R] S)
  have : IsReduced (B ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field K (B ⊗[R] S)
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  -- `σ : S ≅ R[T]/(Tⁿ - π) ≅` the normalization of `R` in `K' = K[T]/(Tⁿ - π)`
  let : Algebra (AdjoinRoot (X ^ n - C π)) (AdjoinRoot (X ^ n - C (algebraMap R K π))) :=
    (adjoinRootAlgHom R (K := K) π n).toRingHom.toAlgebra
  have : IsScalarTower R (AdjoinRoot (X ^ n - C π))
      (AdjoinRoot (X ^ n - C (algebraMap R K π))) :=
    IsScalarTower.of_algHom _
  have := isIntegralClosure_adjoinRoot R (K := K) π n
  let σ : S ≃ₐ[R] integralClosure R (AdjoinRoot (X ^ n - C (algebraMap R K π))) :=
    ρ.trans (IsIntegralClosure.equiv R (AdjoinRoot (X ^ n - C π))
      (AdjoinRoot (X ^ n - C (algebraMap R K π))) _)
  have hσ (s : S) : (σ s : AdjoinRoot (X ^ n - C (algebraMap R K π))) =
      adjoinRootAlgHom R (K := K) π n (ρ s) :=
    IsIntegralClosure.algebraMap_equiv R (AdjoinRoot (X ^ n - C π))
      (AdjoinRoot (X ^ n - C (algebraMap R K π)))
      (integralClosure R (AdjoinRoot (X ^ n - C (algebraMap R K π)))) (ρ s)
  -- `κ : K' → B ⊗_R S`, `T ↦ 1 ⊗ T`
  let κ : AdjoinRoot (X ^ n - C (algebraMap R K π)) →ₐ[K] B ⊗[R] S :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId K _) ((1 : B) ⊗ₜ ρ.symm (AdjoinRoot.root _)) (by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, Algebra.TensorProduct.tmul_pow, one_pow, ← map_pow,
        root_X_pow_sub_C_pow, AlgEquiv.commutes, sub_eq_zero]
      change _ = algebraMap K (B ⊗[R] S) (algebraMap R K π)
      rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply'])
  have hκσ (s : S) : κ (σ s) = (1 : B) ⊗ₜ[R] s := by
    obtain ⟨y, rfl⟩ := ρ.symm.surjective s
    rw [hσ, AlgEquiv.apply_symm_apply]
    have := AdjoinRoot.algHom_ext
      (g₁ := (κ.restrictScalars R).comp (adjoinRootAlgHom R (K := K) π n))
      (g₂ := Algebra.TensorProduct.includeRight.comp ρ.symm.toAlgHom) (by simp [κ])
    exact DFunLike.congr_fun this y
  let : Algebra (AdjoinRoot (X ^ n - C (algebraMap R K π))) (B ⊗[R] S) := κ.toRingHom.toAlgebra
  have : IsScalarTower K (AdjoinRoot (X ^ n - C (algebraMap R K π))) (B ⊗[R] S) :=
    IsScalarTower.of_algHom κ
  have : IsScalarTower R (AdjoinRoot (X ^ n - C (algebraMap R K π))) (B ⊗[R] S) :=
    .of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R K (AdjoinRoot (X ^ n - C (algebraMap R K π))) r,
        IsScalarTower.algebraMap_apply R K (B ⊗[R] S) r]
      exact (κ.commutes _).symm
  -- each factor `F` of `B ⊗_R S` is a composite of `K'` and a factor `L` of `B`
  let : ∀ M : MaximalSpectrum (B ⊗[R] S), Algebra S (integralClosure R (B ⊗[R] S ⧸ M.asIdeal)) :=
    fun M ↦ (((IsScalarTower.toAlgHom R (AdjoinRoot (X ^ n - C (algebraMap R K π)))
      (B ⊗[R] S ⧸ M.asIdeal)).mapIntegralClosure).comp σ.toAlgHom).toRingHom.toAlgebra
  have key (M : MaximalSpectrum (B ⊗[R] S)) :
      Module.Finite S (integralClosure R (B ⊗[R] S ⧸ M.asIdeal)) ∧
        Algebra.FormallyEtale S (integralClosure R (B ⊗[R] S ⧸ M.asIdeal)) := by
    let := Ideal.Quotient.field M.asIdeal
    let M' : Ideal B := M.asIdeal.comap (algebraMap B (B ⊗[R] S))
    have : M'.IsPrime := Ideal.comap_isPrime _ _
    have : M'.IsMaximal := IsArtinianRing.isMaximal_of_isPrime M'
    let := Ideal.Quotient.field M'
    have : Module.Finite K (B ⊗[R] S ⧸ M.asIdeal) := Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ K M.asIdeal).toLinearMap Ideal.Quotient.mk_surjective
    have : Algebra.FormallyUnramified K (B ⊗[R] S ⧸ M.asIdeal) :=
      Algebra.FormallyUnramified.comp K (B ⊗[R] S) _
    have : Algebra.IsSeparable K (B ⊗[R] S ⧸ M.asIdeal) :=
      Algebra.FormallyUnramified.isSeparable K _
    have : Module.Finite K (B ⧸ M') := Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ K M').toLinearMap Ideal.Quotient.mk_surjective
    have : Algebra.FormallyUnramified K (B ⧸ M') := Algebra.FormallyUnramified.comp K B _
    have : Algebra.IsSeparable K (B ⧸ M') := Algebra.FormallyUnramified.isSeparable K _
    let g : (B ⧸ M') →ₐ[K] (B ⊗[R] S ⧸ M.asIdeal) :=
      Ideal.quotientMapₐ M.asIdeal (IsScalarTower.toAlgHom K B (B ⊗[R] S)) fun _ h ↦ h
    have hgen : Algebra.adjoin K (Set.range g ∪
        Set.range (algebraMap (AdjoinRoot (X ^ n - C (algebraMap R K π)))
          (B ⊗[R] S ⧸ M.asIdeal))) = ⊤ := by
      refine eq_top_iff.mpr ?_
      rintro x -
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
      induction c using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Subalgebra.zero_mem _
      | tmul b s =>
        have : (b ⊗ₜ[R] s : B ⊗[R] S) = (b ⊗ₜ[R] (1 : S)) * κ (σ s) := by
          rw [hκσ, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [this, map_mul]
        exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inl ⟨Ideal.Quotient.mk M' b, rfl⟩))
          (Algebra.subset_adjoin (Or.inr ⟨σ s, rfl⟩))
      | add x y hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
    have hL : IsTameExtension R (K := K) (B ⧸ M') :=
      (isTameExtension_iff_isTamelyRamifiedOver R (B ⧸ M')).mpr (htame ⟨M', inferInstance⟩)
    obtain ⟨h1, h2⟩ := etale_integralClosure_of_adjoinRoot R hnR g hgen hL
      (hdvd ⟨M', inferInstance⟩)
    exact finite_and_formallyEtale_of_ringEquiv σ.toRingEquiv (fun _ ↦ rfl) h1 inferInstance
  have : ∀ M : MaximalSpectrum (B ⊗[R] S),
      Module.Finite S (integralClosure R (B ⊗[R] S ⧸ M.asIdeal)) := fun M ↦ (key M).1
  -- the normalization `W` of `R` in `B ⊗_R S`, as an `S`-algebra
  let : Algebra S (B ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  have hSint (s : S) : IsIntegral R ((1 : B) ⊗ₜ[R] s) :=
    (Algebra.IsIntegral.isIntegral s).map Algebra.TensorProduct.includeRight
  let j : S →ₐ[R] integralClosure R (B ⊗[R] S) :=
    Algebra.TensorProduct.includeRight.codRestrict _ hSint
  let : Algebra S (integralClosure R (B ⊗[R] S)) := j.toRingHom.toAlgebra
  have : IsScalarTower S (integralClosure R (B ⊗[R] S)) (B ⊗[R] S) :=
    .of_algebraMap_eq fun _ ↦ rfl
  -- `W` is the product of the normalizations in the factors
  let Φ := ((IsArtinianRing.equivPi (B ⊗[R] S)).restrictScalars R).mapIntegralClosure.trans
    (integralClosure.piAlgEquiv R (fun M : MaximalSpectrum (B ⊗[R] S) ↦ B ⊗[R] S ⧸ M.asIdeal))
  let Φ' : integralClosure R (B ⊗[R] S) ≃ₐ[S]
      Π M : MaximalSpectrum (B ⊗[R] S), integralClosure R (B ⊗[R] S ⧸ M.asIdeal) :=
    AlgEquiv.ofRingEquiv (f := Φ.toRingEquiv) fun s ↦ by
      funext M
      apply Subtype.ext
      change Ideal.Quotient.mk M.asIdeal ((1 : B) ⊗ₜ[R] s) =
        Ideal.Quotient.mk M.asIdeal (κ (σ s))
      rw [hκσ]
  have : Algebra.FormallyEtale S
      (Π M : MaximalSpectrum (B ⊗[R] S), integralClosure R (B ⊗[R] S ⧸ M.asIdeal)) :=
    (Algebra.FormallyEtale.pi_iff _).mpr fun M ↦ (key M).2
  have : Module.Finite S (integralClosure R (B ⊗[R] S)) :=
    Module.Finite.equiv Φ'.symm.toLinearEquiv
  have : Algebra.FormallyEtale S (integralClosure R (B ⊗[R] S)) :=
    Algebra.FormallyEtale.of_equiv Φ'.symm
  have : IsNoetherianRing S := isNoetherianRing_of_ringEquiv _ ρ.symm.toRingEquiv
  have : Algebra.FinitePresentation S (integralClosure R (B ⊗[R] S)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale S (integralClosure R (B ⊗[R] S)) := ⟨inferInstance, inferInstance⟩
  -- `B ⊗_R S` is the localization of `W` at `π`
  have hloc := isLocalization_powers_integralClosure R (K := K) (Fact.out : Irreducible π)
    (B ⊗[R] S)
  have : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R (B ⊗[R] S))
      (Submonoid.powers (algebraMap R S π))) (B ⊗[R] S) := by
    rw [Algebra.algebraMapSubmonoid_powers, show algebraMap S (integralClosure R (B ⊗[R] S))
      (algebraMap R S π) = algebraMap R _ π from j.commutes π]
    exact hloc
  have hu : IsUnit (algebraMap S (B ⊗[R] S) (algebraMap R S π)) := by
    change IsUnit ((1 : B) ⊗ₜ[R] algebraMap R S π)
    rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply R K (B ⊗[R] S)]
    exact (isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
      (Fact.out : Irreducible π).ne_zero)).map _
  let : Algebra (Localization.Away (algebraMap R S π)) (B ⊗[R] S) :=
    (IsLocalization.Away.lift _ hu).toAlgebra
  have : IsScalarTower S (Localization.Away (algebraMap R S π)) (B ⊗[R] S) :=
    .of_algebraMap_eq fun s ↦ (IsLocalization.Away.lift_eq _ hu s).symm
  have hpush := Algebra.isPushout_of_isLocalization (Submonoid.powers (algebraMap R S π))
    (Localization.Away (algebraMap R S π)) (integralClosure R (B ⊗[R] S)) (B ⊗[R] S)
  have := hpush.symm
  let e₁ : S ⊗[R] B ≃ₐ[S] B ⊗[R] S :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R S B).toRingEquiv) fun s ↦ by
      simp [Algebra.TensorProduct.algebraMap_apply]
      rfl
  exact ⟨integralClosure R (B ⊗[R] S), inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨e₁.trans ((Algebra.IsPushout.equiv S (Localization.Away (algebraMap R S π))
      (integralClosure R (B ⊗[R] S)) (B ⊗[R] S)).symm.restrictScalars S)⟩⟩

/-- The tame ramification data of the normalization of a local ring `R` in a finite product of
rings `E` (an artinian reduced ring) are those of its factors. -/
theorem forall_factors_of_forall_isTamelyRamifiedAt {R : Type*} [CommRing R] [IsLocalRing R]
    (E : Type*) [CommRing E] [Algebra R E] [IsArtinianRing E] [IsReduced E] (k : ℕ)
    (h : ∀ (Q : Ideal (integralClosure R E)) [Q.IsPrime], Q.LiesOver (maximalIdeal R) →
      IsTamelyRamifiedAt R Q ∧ Q.ramificationIdx R ∣ k) (M : MaximalSpectrum E) :
    IsTamelyRamifiedOver R (integralClosure R (E ⧸ M.asIdeal)) ∧
      ∀ Q : Ideal (integralClosure R (E ⧸ M.asIdeal)), Q.IsPrime →
        Q.LiesOver (maximalIdeal R) → Q.ramificationIdx R ∣ k := by
  let Φ := ((IsArtinianRing.equivPi E).restrictScalars R).mapIntegralClosure.trans
      (integralClosure.piAlgEquiv R (fun M : MaximalSpectrum E ↦ E ⧸ M.asIdeal))
  let φ := Φ.toAlgHom
  have key (Q : Ideal (integralClosure R (E ⧸ M.asIdeal))) [Q.IsPrime] :
      (IsTamelyRamifiedAt R ((Q.comap (Pi.evalAlgHom R
        (fun M : MaximalSpectrum E ↦ integralClosure R (E ⧸ M.asIdeal)) M)).comap φ) ↔
        IsTamelyRamifiedAt R Q) ∧
      ((Q.comap (Pi.evalAlgHom R
        (fun M : MaximalSpectrum E ↦ integralClosure R (E ⧸ M.asIdeal)) M)).comap φ).ramificationIdx
          R = Q.ramificationIdx R ∧
      ((Q.comap (Pi.evalAlgHom R
        (fun M : MaximalSpectrum E ↦ integralClosure R (E ⧸ M.asIdeal)) M)).comap φ).under R =
          Q.under R := by
    have h1 := Ideal.bijective_localAlgHom_evalAlgHom (A := R)
      (L := fun M : MaximalSpectrum E ↦ integralClosure R (E ⧸ M.asIdeal)) M Q
    have h3 := bijective_localAlgHom_algEquiv R Φ (Q.comap (Pi.evalAlgHom R
      (fun M : MaximalSpectrum E ↦ integralClosure R (E ⧸ M.asIdeal)) M))
    refine ⟨(isTamelyRamifiedAt_comap_iff_of_bijective R _ _ h3).trans
      (isTamelyRamifiedAt_comap_iff_of_bijective R _ _ h1), ?_, ?_⟩
    · rw [Ideal.ramificationIdx_comap_of_bijective _ _ h3,
        Ideal.ramificationIdx_comap_of_bijective _ _ h1]
    · rw [Ideal.under_comap_algHom, Ideal.under_comap_algHom]
  have hmax (Q : Ideal (integralClosure R (E ⧸ M.asIdeal))) [Q.IsPrime]
      (hQ : Q.LiesOver (maximalIdeal R)) :
      ((Q.comap (Pi.evalAlgHom R
        (fun M : MaximalSpectrum E ↦ integralClosure R (E ⧸ M.asIdeal)) M)).comap φ).LiesOver
          (maximalIdeal R) := ⟨by
    rw [(key Q).2.2, ← Ideal.over_def Q (maximalIdeal R)]⟩
  refine ⟨fun Q _ hQ ↦ (key Q).1.mp (h _ (hmax Q hQ)).1, fun Q _ hQ ↦ ?_⟩
  rw [← (key Q).2.1]
  exact (h _ (hmax Q hQ)).2

set_option maxHeartbeats 1600000 in
-- the instance problems on the quotients of `C'` and their normalizations are large
/-- XIII.5.2 for a discrete valuation ring `R` with uniformizer `π`, in terms of an algebra `C'`
generated by `S ≅ R[T]/(Tⁿ - π)` and a finite étale `K`-algebra `B` whose factors are tamely
ramified over `R` with ramification indices dividing `n` (`n` prime to the residue
characteristic): the normalization of `S` in `C'` is finite étale over `S`. (For
`C' = S ⊗_R B` this is `exists_etale_of_forall_isTamelyRamifiedOver`; in general `C'` is a
quotient of `K' ⊗_K B`, `K' = K[T]/(Tⁿ - π)`.) -/
theorem etale_integralClosure_of_forall_isTamelyRamifiedOver (R : Type*) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (π : R) [Fact (Irreducible π)] (n : ℕ) [NeZero n]
    (hnR : (n : R) ∉ maximalIdeal R) (S : Type*) [CommRing S] [Algebra R S]
    (ρ : S ≃ₐ[R] AdjoinRoot (X ^ n - C π)) (B : Type*) [CommRing B] [Algebra K B] [Algebra R B]
    [IsScalarTower R K B] [Module.Finite K B] [Algebra.Etale K B]
    (htame : ∀ M : MaximalSpectrum B, IsTamelyRamifiedOver R (integralClosure R (B ⧸ M.asIdeal)))
    (hdvd : ∀ (M : MaximalSpectrum B) (Q : Ideal (integralClosure R (B ⧸ M.asIdeal))),
      Q.IsPrime → Q.LiesOver (maximalIdeal R) → Q.ramificationIdx R ∣ n)
    (C' : Type*) [CommRing C'] [Algebra K C'] [Algebra R C'] [IsScalarTower R K C']
    [Algebra S C'] [IsScalarTower R S C'] (β : B →ₐ[K] C')
    (hgen : ∀ c : C', c ∈ Algebra.adjoin S (Set.range β)) :
    Module.Finite S (integralClosure S C') ∧ Algebra.Etale S (integralClosure S C') := by
  classical
  have : Module.Finite R S := Module.Finite.equiv ρ.symm.toLinearEquiv
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  -- `σ : S ≅ R[T]/(Tⁿ - π) ≅` the normalization of `R` in `K' = K[T]/(Tⁿ - π)`
  let : Algebra (AdjoinRoot (X ^ n - C π)) (AdjoinRoot (X ^ n - C (algebraMap R K π))) :=
    (adjoinRootAlgHom R (K := K) π n).toRingHom.toAlgebra
  have : IsScalarTower R (AdjoinRoot (X ^ n - C π))
      (AdjoinRoot (X ^ n - C (algebraMap R K π))) :=
    IsScalarTower.of_algHom _
  have := isIntegralClosure_adjoinRoot R (K := K) π n
  let σ : S ≃ₐ[R] integralClosure R (AdjoinRoot (X ^ n - C (algebraMap R K π))) :=
    ρ.trans (IsIntegralClosure.equiv R (AdjoinRoot (X ^ n - C π))
      (AdjoinRoot (X ^ n - C (algebraMap R K π))) _)
  have hσ (s : S) : (σ s : AdjoinRoot (X ^ n - C (algebraMap R K π))) =
      adjoinRootAlgHom R (K := K) π n (ρ s) :=
    IsIntegralClosure.algebraMap_equiv R (AdjoinRoot (X ^ n - C π))
      (AdjoinRoot (X ^ n - C (algebraMap R K π)))
      (integralClosure R (AdjoinRoot (X ^ n - C (algebraMap R K π)))) (ρ s)
  -- `κ : K' → C'`, `T ↦ T`
  let κ : AdjoinRoot (X ^ n - C (algebraMap R K π)) →ₐ[K] C' :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId K _) (algebraMap S C' (ρ.symm (AdjoinRoot.root _))) (by
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, ← map_pow, ← map_pow, root_X_pow_sub_C_pow,
        AlgEquiv.commutes, sub_eq_zero, ← IsScalarTower.algebraMap_apply]
      change _ = algebraMap K C' (algebraMap R K π)
      rw [← IsScalarTower.algebraMap_apply])
  have hκσ (s : S) : κ (σ s) = algebraMap S C' s := by
    obtain ⟨y, rfl⟩ := ρ.symm.surjective s
    rw [hσ, AlgEquiv.apply_symm_apply]
    have := AdjoinRoot.algHom_ext
      (g₁ := (κ.restrictScalars R).comp (adjoinRootAlgHom R (K := K) π n))
      (g₂ := (IsScalarTower.toAlgHom R S C').comp ρ.symm.toAlgHom) (by simp [κ])
    exact DFunLike.congr_fun this y
  let : Algebra (AdjoinRoot (X ^ n - C (algebraMap R K π))) C' := κ.toRingHom.toAlgebra
  have : IsScalarTower K (AdjoinRoot (X ^ n - C (algebraMap R K π))) C' :=
    IsScalarTower.of_algHom κ
  have : IsScalarTower R (AdjoinRoot (X ^ n - C (algebraMap R K π))) C' :=
    .of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R K (AdjoinRoot (X ^ n - C (algebraMap R K π))) r,
        IsScalarTower.algebraMap_apply R K C' r]
      exact (κ.commutes _).symm
  -- `C'` is a quotient of `K' ⊗_K B`, hence finite étale over `K`
  have : Algebra.Etale K (AdjoinRoot (X ^ n - C (algebraMap R K π))) :=
    etale_adjoinRoot_X_pow_sub_C_algebraMap π n K hnR
  have hf : X ^ n - C (algebraMap R K π) ≠ 0 := (monic_X_pow_sub_C _ (NeZero.ne n)).ne_zero
  have : Module.Finite K (AdjoinRoot (X ^ n - C (algebraMap R K π))) :=
    (AdjoinRoot.powerBasis hf).finite
  have : Algebra.Etale K (AdjoinRoot (X ^ n - C (algebraMap R K π)) ⊗[K] B) :=
    Algebra.Etale.comp K (AdjoinRoot (X ^ n - C (algebraMap R K π))) _
  have : Module.Finite K (AdjoinRoot (X ^ n - C (algebraMap R K π)) ⊗[K] B) :=
    Module.Finite.trans (AdjoinRoot (X ^ n - C (algebraMap R K π))) _
  let Λ : AdjoinRoot (X ^ n - C (algebraMap R K π)) ⊗[K] B →ₐ[K] C' :=
    Algebra.TensorProduct.lift κ β fun _ _ ↦ Commute.all _ _
  have hΛ : Function.Surjective Λ := by
    intro c
    induction hgen c using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact ⟨1 ⊗ₜ b, by simp [Λ]⟩
    | algebraMap s => exact ⟨σ s ⊗ₜ 1, by simp [Λ, hκσ]⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' * y', map_mul _ _ _⟩
  have : Algebra.FormallyUnramified K C' := Algebra.FormallyUnramified.of_surjective Λ hΛ
  have : Module.Finite K C' := Module.Finite.of_surjective Λ.toLinearMap hΛ
  have : IsArtinianRing C' := IsArtinianRing.of_finite K C'
  have : IsReduced C' := Algebra.FormallyUnramified.isReduced_of_field K C'
  -- each factor `F` of `C'` is a composite of `K'` and a factor `L` of `B`
  have key (M : MaximalSpectrum C') :
      Module.Finite S (integralClosure S (C' ⧸ M.asIdeal)) ∧
        Algebra.FormallyEtale S (integralClosure S (C' ⧸ M.asIdeal)) := by
    let := Ideal.Quotient.field M.asIdeal
    let M' : Ideal B := M.asIdeal.comap β
    have : M'.IsPrime := Ideal.comap_isPrime _ _
    have : M'.IsMaximal := IsArtinianRing.isMaximal_of_isPrime M'
    let := Ideal.Quotient.field M'
    have : Module.Finite K (C' ⧸ M.asIdeal) := Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ K M.asIdeal).toLinearMap Ideal.Quotient.mk_surjective
    have : Algebra.FormallyUnramified K (C' ⧸ M.asIdeal) :=
      Algebra.FormallyUnramified.comp K C' _
    have : Algebra.IsSeparable K (C' ⧸ M.asIdeal) := Algebra.FormallyUnramified.isSeparable K _
    have : Module.Finite K (B ⧸ M') := Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ K M').toLinearMap Ideal.Quotient.mk_surjective
    have : Algebra.FormallyUnramified K (B ⧸ M') := Algebra.FormallyUnramified.comp K B _
    have : Algebra.IsSeparable K (B ⧸ M') := Algebra.FormallyUnramified.isSeparable K _
    let g : (B ⧸ M') →ₐ[K] (C' ⧸ M.asIdeal) := Ideal.quotientMapₐ M.asIdeal β fun _ h ↦ h
    have hgenF : Algebra.adjoin K (Set.range g ∪
        Set.range (algebraMap (AdjoinRoot (X ^ n - C (algebraMap R K π)))
          (C' ⧸ M.asIdeal))) = ⊤ := by
      refine eq_top_iff.mpr ?_
      rintro x -
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := hΛ c
      induction y using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact Subalgebra.zero_mem _
      | tmul k b =>
        have : Λ (k ⊗ₜ b) = κ k * β b := Algebra.TensorProduct.lift_tmul _ _ _ _ _
        rw [this, map_mul]
        exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Or.inr ⟨k, rfl⟩))
          (Algebra.subset_adjoin (Or.inl ⟨Ideal.Quotient.mk M' b, rfl⟩))
      | add x y hx hy => rw [map_add, map_add]; exact Subalgebra.add_mem _ hx hy
    have hL : IsTameExtension R (K := K) (B ⧸ M') :=
      (isTameExtension_iff_isTamelyRamifiedOver R (B ⧸ M')).mpr (htame ⟨M', inferInstance⟩)
    obtain ⟨h1, h2⟩ := etale_integralClosure_of_adjoinRoot R hnR g hgenF hL
      (hdvd ⟨M', inferInstance⟩)
    -- the normalizations of `R` and of `S` in `F` agree
    let : Algebra S (integralClosure R (C' ⧸ M.asIdeal)) :=
      (((IsScalarTower.toAlgHom R (AdjoinRoot (X ^ n - C (algebraMap R K π)))
        (C' ⧸ M.asIdeal)).mapIntegralClosure).comp σ.toAlgHom).toRingHom.toAlgebra
    obtain ⟨h1', h2'⟩ := finite_and_formallyEtale_of_ringEquiv σ.toRingEquiv (fun _ ↦ rfl) h1
      inferInstance
    have : Algebra.IsIntegral R S := inferInstance
    let Z : integralClosure S (C' ⧸ M.asIdeal) ≃ₐ[S] integralClosure R (C' ⧸ M.asIdeal) :=
      { toFun x := ⟨x.1, isIntegral_trans (A := S) _ x.2⟩
        invFun y := ⟨y.1, y.2.tower_top⟩
        left_inv _ := rfl
        right_inv _ := rfl
        map_mul' _ _ := rfl
        map_add' _ _ := rfl
        commutes' s := Subtype.ext (by
          change algebraMap S (C' ⧸ M.asIdeal) s =
            Ideal.Quotient.mk M.asIdeal (κ (σ s : AdjoinRoot (X ^ n - C (algebraMap R K π))))
          rw [hκσ]
          rfl) }
    exact ⟨Module.Finite.equiv Z.symm.toLinearEquiv, Algebra.FormallyEtale.of_equiv Z.symm⟩
  have : ∀ M : MaximalSpectrum C', Module.Finite S (integralClosure S (C' ⧸ M.asIdeal)) :=
    fun M ↦ (key M).1
  -- the normalization of `S` in `C'` is the product of the normalizations in the factors
  let Φ := ((IsArtinianRing.equivPi C').restrictScalars S).mapIntegralClosure.trans
    (integralClosure.piAlgEquiv S (fun M : MaximalSpectrum C' ↦ C' ⧸ M.asIdeal))
  have : Algebra.FormallyEtale S
      (Π M : MaximalSpectrum C', integralClosure S (C' ⧸ M.asIdeal)) :=
    (Algebra.FormallyEtale.pi_iff _).mpr fun M ↦ (key M).2
  have : Module.Finite S (integralClosure S C') := Module.Finite.equiv Φ.symm.toLinearEquiv
  have : Algebra.FormallyEtale S (integralClosure S C') := Algebra.FormallyEtale.of_equiv Φ.symm
  have : IsNoetherianRing S := isNoetherianRing_of_ringEquiv _ ρ.symm.toRingEquiv
  have : Algebra.FinitePresentation S (integralClosure S C') :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩

/-- Tame ramification and ramification indices are unchanged along an unramified flat
extension: if `S → T` is flat and unramified at the prime `P` of `T` and `P ∩ S` is tamely
ramified over `R`, then so is `P`, with the same ramification index. -/
theorem isTamelyRamifiedAt_and_ramificationIdx_eq_of_isUnramifiedAt {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.Flat S T] [Algebra.EssFiniteType S T] (P : Ideal T) [P.IsPrime]
    [Algebra.IsUnramifiedAt S P] (h : IsTamelyRamifiedAt R (P.under S)) :
    IsTamelyRamifiedAt R P ∧ P.ramificationIdx R = (P.under S).ramificationIdx R := by
  have he : P.ramificationIdx R = (P.under S).ramificationIdx R := by
    rw [Ideal.ramificationIdx_tower (R := R) (P.under S) P,
      P.ramificationIdx_eq_one S, mul_one]
  refine ⟨?_, he⟩
  set p := P.under R
  have : (P.under S).LiesOver p := ⟨(Ideal.under_under P).symm⟩
  rw [isTamelyRamifiedAt_iff_of_liesOver R p (P.under S)] at h
  rw [isTamelyRamifiedAt_iff_of_liesOver R p P, he]
  refine ⟨h.1, ?_⟩
  let := Localization.AtPrime.algebraOfLiesOver p (P.under S)
  let := Localization.AtPrime.algebraOfLiesOver p P
  let := Localization.AtPrime.algebraOfLiesOver (P.under S) P
  have := h.2
  exact Algebra.IsSeparable.trans p.ResidueField (P.under S).ResidueField P.ResidueField

/-- Tame ramification, with ramification indices dividing `n`, is preserved by a finite étale base
change `B ↦ B ⊗_R E` over a local ring `R`: the normalization of `R` in `B ⊗_R E` is
`W ⊗_R E`, `W` the normalization of `R` in `B` (smooth base change of integral closures), which is
étale over `W`. -/
theorem isTamelyRamifiedAt_tensorProduct_of_etale {R : Type*} [CommRing R] [IsLocalRing R]
    (B E : Type*) [CommRing B] [Algebra R B] [CommRing E] [Algebra R E] [Algebra.Etale R E]
    [Module.Finite R E] (n : ℕ)
    (hB : ∀ (Q : Ideal (integralClosure R B)) [Q.IsPrime], Q.LiesOver (maximalIdeal R) →
      IsTamelyRamifiedAt R Q ∧ Q.ramificationIdx R ∣ n)
    (Q : Ideal (integralClosure R (B ⊗[R] E))) [Q.IsPrime] (hQ : Q.LiesOver (maximalIdeal R)) :
    IsTamelyRamifiedAt R Q ∧ Q.ramificationIdx R ∣ n := by
  -- `Φ : W ⊗_R E → W'`, `W`, `W'` the normalizations of `R` in `B`, `B ⊗_R E`
  let Φ : integralClosure R B ⊗[R] E →ₐ[R] integralClosure R (B ⊗[R] E) :=
    (Algebra.TensorProduct.map (integralClosure R B).val (AlgHom.id R E)).codRestrict
      (integralClosure R (B ⊗[R] E)) fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact zero_mem _
      | tmul w e =>
        have : Algebra.TensorProduct.map (integralClosure R B).val (AlgHom.id R E) (w ⊗ₜ e) =
            Algebra.TensorProduct.includeLeft (S := R) (w : B) *
              Algebra.TensorProduct.includeRight e := by
          rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
          rfl
        rw [this]
        exact IsIntegral.mul (w.2.map Algebra.TensorProduct.includeLeft)
          ((Algebra.IsIntegral.isIntegral (R := R) e).map Algebra.TensorProduct.includeRight)
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
  have hΦ (x : integralClosure R B ⊗[R] E) : (Φ x : B ⊗[R] E) =
      Algebra.TensorProduct.map (integralClosure R B).val (AlgHom.id R E) x := rfl
  have hinj : Function.Injective Φ := fun x y h ↦
    Module.Flat.rTensor_preserves_injective_linearMap (M := E)
      (integralClosure R B).val.toLinearMap Subtype.val_injective (congrArg Subtype.val h)
  have hsurj : Function.Surjective Φ := by
    intro x
    obtain ⟨z, hz⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := E)
      (B := B)).2 ⟨Algebra.TensorProduct.comm R B E x.1,
        (x.2.map (Algebra.TensorProduct.comm R B E).toAlgHom).tower_top⟩
    refine ⟨Algebra.TensorProduct.comm R E (integralClosure R B) z, Subtype.ext ?_⟩
    have hz' := congrArg (fun y ↦ Algebra.TensorProduct.comm R E B y.1) hz
    simp only at hz'
    rw [← Algebra.TensorProduct.comm_symm, AlgEquiv.symm_apply_apply] at hz'
    rw [← hz', hΦ]
    clear hz hz'
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul e w => simp [TensorProduct.toIntegralClosure]
    | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  -- `W'` is finite étale over `W`
  let : Algebra (integralClosure R B) (integralClosure R (B ⊗[R] E)) :=
    (Φ.comp Algebra.TensorProduct.includeLeft).toRingHom.toAlgebra
  have : IsScalarTower R (integralClosure R B) (integralClosure R (B ⊗[R] E)) :=
    .of_algebraMap_eq fun r ↦ ((Φ.comp Algebra.TensorProduct.includeLeft).commutes r).symm
  let e : integralClosure R B ⊗[R] E ≃ₐ[integralClosure R B] integralClosure R (B ⊗[R] E) :=
    AlgEquiv.ofBijective { Φ with commutes' := fun _ ↦ rfl } ⟨hinj, hsurj⟩
  have : Algebra.Etale (integralClosure R B) (integralClosure R (B ⊗[R] E)) :=
    Algebra.Etale.of_equiv e
  have : Module.Finite (integralClosure R B) (integralClosure R (B ⊗[R] E)) :=
    Module.Finite.equiv e.toLinearEquiv
  have : Algebra.IsUnramifiedAt (integralClosure R B) Q :=
    Algebra.FormallyUnramified.comp (integralClosure R B) (integralClosure R (B ⊗[R] E)) _
  have : (Q.under (integralClosure R B)).LiesOver (maximalIdeal R) :=
    ⟨by rw [Ideal.under_under]; exact hQ.over⟩
  obtain ⟨h1, h2⟩ := hB (Q.under (integralClosure R B)) this
  obtain ⟨h3, h4⟩ :=
    isTamelyRamifiedAt_and_ramificationIdx_eq_of_isUnramifiedAt (S := integralClosure R B) Q h1
  exact ⟨h3, h4 ▸ h2⟩

set_option maxHeartbeats 1600000 in
-- the instance problems on the quotients of `B ⊗_R E` and their normalizations are large
/-- XIII.5.2 for a discrete valuation ring `R` with uniformizer `π`, with an extra finite étale
factor: let `S₀ ≅ R[T]/(Tⁿ - π)` (`n` prime to the residue characteristic), `E` a finite étale
`R`-algebra and `S'` an `S₀`-algebra generated by the image of `E` (e.g.
`S' = R[T, Tᵢ]/(Tⁿ - π, Tᵢ^{nᵢ} - uᵢ)` with the `uᵢ`, `nᵢ` units). Let `B` be a finite étale
`K`-algebra whose normalization over `R` is tamely ramified with ramification indices dividing
`n`, and `C'` an `S'`-algebra generated by the image of `B`. Then the normalization of `S'` in
`C'` is formally étale over `S'`. -/
theorem formallyEtale_integralClosure_of_forall_isTamelyRamifiedAt (R : Type*) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (π : R) [Fact (Irreducible π)] (n : ℕ) [NeZero n]
    (hnR : (n : R) ∉ maximalIdeal R) (S₀ : Type*) [CommRing S₀] [Algebra R S₀]
    (ρ : S₀ ≃ₐ[R] AdjoinRoot (X ^ n - C π)) (E : Type*) [CommRing E] [Algebra R E]
    [Algebra.Etale R E] [Module.Finite R E] (B : Type*) [CommRing B] [Algebra K B] [Algebra R B]
    [IsScalarTower R K B] [Module.Finite K B] [Algebra.Etale K B]
    (hB : ∀ (Q : Ideal (integralClosure R B)) [Q.IsPrime], Q.LiesOver (maximalIdeal R) →
      IsTamelyRamifiedAt R Q ∧ Q.ramificationIdx R ∣ n)
    (S' : Type*) [CommRing S'] [Algebra R S'] [Algebra S₀ S'] [IsScalarTower R S₀ S']
    (γ : E →ₐ[R] S') (hS' : ∀ s, s ∈ Algebra.adjoin S₀ (Set.range γ))
    (C' : Type*) [CommRing C'] [Algebra K C'] [Algebra R C'] [IsScalarTower R K C']
    [Algebra S' C'] [IsScalarTower R S' C'] (β : B →ₐ[K] C')
    (hgen : ∀ c : C', c ∈ Algebra.adjoin S' (Set.range β)) :
    Algebra.FormallyEtale S' (integralClosure S' C') := by
  -- `B' = B ⊗_R E` is finite étale over `K`, tamely ramified with indices dividing `n`
  have : Algebra.Etale K (B ⊗[R] E) := Algebra.Etale.comp K B (B ⊗[R] E)
  have : Module.Finite K (B ⊗[R] E) := Module.Finite.trans B (B ⊗[R] E)
  have : IsArtinianRing (B ⊗[R] E) := IsArtinianRing.of_finite K (B ⊗[R] E)
  have : IsReduced (B ⊗[R] E) := Algebra.FormallyUnramified.isReduced_of_field K (B ⊗[R] E)
  have hfac := forall_factors_of_forall_isTamelyRamifiedAt (R := R) (B ⊗[R] E) n
    fun Q _ hQ ↦ isTamelyRamifiedAt_tensorProduct_of_etale B E n hB Q hQ
  -- `C'` as an `S₀`-algebra, generated by the image of `B'`
  let : Algebra S₀ C' := ((algebraMap S' C').comp (algebraMap S₀ S')).toAlgebra
  have : IsScalarTower S₀ S' C' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R S₀ C' := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R S' C', IsScalarTower.algebraMap_apply R S₀ S']
    rfl
  let β' : B ⊗[R] E →ₐ[K] C' := Algebra.TensorProduct.lift β
    ((IsScalarTower.toAlgHom R S' C').comp γ) fun _ _ ↦ Commute.all _ _
  have hS'C (s : S') : algebraMap S' C' s ∈ Algebra.adjoin S₀ (Set.range β') := by
    have h1 : (Algebra.adjoin S₀ (Set.range γ)).map (IsScalarTower.toAlgHom S₀ S' C') ≤
        Algebra.adjoin S₀ (Set.range β') := by
      rw [AlgHom.map_adjoin]
      refine Algebra.adjoin_mono ?_
      rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
      exact ⟨1 ⊗ₜ e, by simp [β']⟩
    exact h1 ⟨s, hS' s, rfl⟩
  let D : Subalgebra S' C' :=
    { (Algebra.adjoin S₀ (Set.range β')).toSubsemiring with
      algebraMap_mem' := hS'C }
  have hgen' (c : C') : c ∈ Algebra.adjoin S₀ (Set.range β') := by
    have : Algebra.adjoin S' (Set.range β) ≤ D := Algebra.adjoin_le fun _ ⟨b, hb⟩ ↦
      Algebra.subset_adjoin ⟨b ⊗ₜ 1, by simp [β', ← hb]⟩
    exact this (hgen c)
  obtain ⟨-, hW⟩ := etale_integralClosure_of_forall_isTamelyRamifiedOver R K π n hnR S₀ ρ
    (B ⊗[R] E) (fun M ↦ (hfac M).1) (fun M ↦ (hfac M).2) C' β' hgen'
  -- `S'` is integral and formally unramified over `S₀`
  let μ : S₀ ⊗[R] E →ₐ[S₀] S' := Algebra.TensorProduct.lift (Algebra.ofId S₀ S') γ
    fun _ _ ↦ Commute.all _ _
  have hμ : Function.Surjective μ := by
    intro s
    have : Algebra.adjoin S₀ (Set.range γ) ≤ μ.range := Algebra.adjoin_le fun _ ⟨e, he⟩ ↦
      ⟨1 ⊗ₜ e, by simp [μ, he]⟩
    exact this (hS' s)
  have : Algebra.IsIntegral S₀ S' := Algebra.IsIntegral.of_surjective μ hμ
  have : Algebra.FormallyUnramified S₀ S' := Algebra.FormallyUnramified.of_surjective μ hμ
  -- the normalizations of `S₀` and `S'` in `C'` agree
  have heq : (integralClosure S' C').restrictScalars S₀ = integralClosure S₀ C' := by
    ext x
    simp only [mem_integralClosure_iff, Subalgebra.mem_restrictScalars]
    exact ⟨fun hx ↦ isIntegral_trans x hx, fun hx ↦ hx.tower_top⟩
  have : Algebra.FormallyEtale S₀ ((integralClosure S' C').restrictScalars S₀) :=
    Algebra.FormallyEtale.of_equiv (Subalgebra.equivOfEq _ _ heq).symm
  have : Algebra.FormallyEtale S₀ (integralClosure S' C') := this
  exact Algebra.FormallyEtale.of_restrictScalars (R := S₀)

/-- XIII.5.2 for a regular local ring `A` of dimension one and `r = 1` (`A` is then a discrete
valuation ring with uniformizer `f₁`): if `B` is a finite étale `A[1/f₁]`-algebra tamely ramified
along `div f₁` and `n` is the l.c.m. of the ramification indices over `(f₁)`, then `n` is prime to
the residue characteristic and the restriction `A' ⊗_A B` of `B` to `U' = Spec A'[1/f₁]`,
`A' = A[T]/(Tⁿ - f₁)`, extends to a finite étale `A'`-algebra `W` (the normalization of `A` in
`B ⊗_A A'`). This is `AbsoluteAbhyankarAt A 1` for `dim A = 1`
(`absoluteAbhyankarAt_of_ringKrullDim_eq_one`). -/
theorem absoluteAbhyankar_of_ringKrullDim_eq_one (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 1) (f : Fin 1 → A)
    (hf : IsPartOfRegularSystemOfParameters f) (B : Type u) [CommRing B] [Algebra A B]
    [Algebra (Localization.Away (∏ i, f i)) B]
    [IsScalarTower A (Localization.Away (∏ i, f i)) B]
    [Module.Finite (Localization.Away (∏ i, f i)) B]
    [Algebra.Etale (Localization.Away (∏ i, f i)) B] (hB : IsTamelyRamifiedAlong f B)
    (n : Fin 1 → ℕ) (hn : ∀ i, IsLcmRamificationIndices (Ideal.span {f i}) B (n i)) :
    (∀ i, (n i : A) ∉ maximalIdeal A) ∧
      ∃ (W : Type u) (_ : CommRing W) (_ : Algebra (KummerAlgebra n f) W),
        Module.Finite (KummerAlgebra n f) W ∧ Algebra.Etale (KummerAlgebra n f) W ∧
        Nonempty (KummerAlgebra n f ⊗[A] B ≃ₐ[KummerAlgebra n f]
          Localization.Away (algebraMap A (KummerAlgebra n f) (∏ i, f i)) ⊗[KummerAlgebra n f]
            W) := by
  obtain ⟨hdvr, hm⟩ := isDiscreteValuationRing_of_ringKrullDim_eq_one hdim f hf
  have hprod : ∏ i, f i = f 0 := Fin.prod_univ_one f
  have hπ : Irreducible (∏ i, f i) := by
    rw [hprod]
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hm
  have : Fact (Irreducible (∏ i, f i)) := ⟨hπ⟩
  have : IsFractionRing A (Localization.Away (∏ i, f i)) := isFractionRing_away_of_irreducible hπ
  obtain ⟨hn0, hfactors⟩ := tame_factors_of_isTamelyRamifiedAlong f hm B hB n hn
  refine ⟨fun i ↦ by rw [Fin.eq_zero i]; exact hn0, ?_⟩
  have hn00 : n 0 ≠ 0 := fun h ↦ hn0 (by rw [h, Nat.cast_zero]; exact zero_mem _)
  have : NeZero (n 0) := ⟨hn00⟩
  -- `B` as an algebra over `Frac A ≅ A[1/f₁]`
  let eK : FractionRing A ≃ₐ[A] Localization.Away (∏ i, f i) :=
    IsLocalization.algEquiv (nonZeroDivisors A) _ _
  let : Algebra (FractionRing A) (Localization.Away (∏ i, f i)) := eK.toRingHom.toAlgebra
  let : Algebra (FractionRing A) B :=
    ((algebraMap (Localization.Away (∏ i, f i)) B).comp eK.toRingHom).toAlgebra
  have : IsScalarTower (FractionRing A) (Localization.Away (∏ i, f i)) B :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A (FractionRing A) B := .of_algebraMap_eq fun a ↦ by
    change _ = algebraMap (Localization.Away (∏ i, f i)) B (eK (algebraMap A _ a))
    rw [eK.commutes, ← IsScalarTower.algebraMap_apply]
  let e₀ : FractionRing A ≃ₐ[FractionRing A] Localization.Away (∏ i, f i) :=
    AlgEquiv.ofRingEquiv (f := eK.toRingEquiv) fun _ ↦ rfl
  have : Algebra.Etale (FractionRing A) (Localization.Away (∏ i, f i)) :=
    Algebra.Etale.of_equiv e₀
  have : Module.Finite (FractionRing A) (Localization.Away (∏ i, f i)) :=
    Module.Finite.equiv e₀.toLinearEquiv
  have : Algebra.Etale (FractionRing A) B :=
    Algebra.Etale.comp _ (Localization.Away (∏ i, f i)) B
  have : Module.Finite (FractionRing A) B := Module.Finite.trans (Localization.Away (∏ i, f i)) B
  -- `Frac A ⊗_A A'` is étale over `Frac A`
  have hnu : ∀ i, IsUnit ((n i : ℕ) : FractionRing A) := fun i ↦ by
    rw [Fin.eq_zero i, isUnit_iff_ne_zero, ← map_natCast (algebraMap A (FractionRing A))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective A _)).mpr
      fun h ↦ hn0 (h ▸ zero_mem _)
  have hfu : ∀ i, IsUnit (algebraMap A (FractionRing A) (f i)) := fun i ↦ by
    rw [Fin.eq_zero i, isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective A _)).mpr (hprod ▸ hπ.ne_zero)
  have := KummerAlgebra.etale (B := FractionRing A) hnu hfu
  have : Algebra.Etale (FractionRing A) (FractionRing A ⊗[A] KummerAlgebra n f) :=
    Algebra.Etale.of_equiv (KummerAlgebra.baseChangeEquiv n f (FractionRing A)).symm
  exact exists_etale_of_forall_isTamelyRamifiedOver A (FractionRing A) (∏ i, f i) (n 0) hn0
    (KummerAlgebra n f) (KummerAlgebra.equivAdjoinRootProd n f) B (fun M ↦ (hfactors M).1)
    (fun M ↦ (hfactors M).2)

end DimensionOne

end SGA.SGA1.ExposeXIII
