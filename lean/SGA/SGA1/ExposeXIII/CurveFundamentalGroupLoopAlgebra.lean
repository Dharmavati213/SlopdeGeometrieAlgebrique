/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import SGA.Foundations.Etale.LocalAcyclicityHenselian
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupTame

/-!
# Inertia groups and points of the normalization (algebra for XIII.2.12 over `ℂ`)

The algebraic half of the comparison of inertia groups with loops (registry row C32). Let `R` be
the local ring of a curve at a point `a`, `O` its strict henselization (a henselian discrete
valuation ring with the same uniformizer) and `K'` the fraction field of `O`. For a Galois étale
covering `E` with group `G`, the inertia group at `a` acts on the geometric points of
`E ×_U Spec K'`; its orbits are the points `Q` of that `K'`-scheme, and the stabilizer of the
orbit through a point is the stabilizer in `G` of `Q`, of order `[κ(Q) : K']`. The normalization
`Ē` of the curve in `E` has a point `P(Q)` over `a`: the centre of the valuation of `κ(Q)` (the
unique maximal ideal of the integral closure of `O` in `κ(Q)`) on the normalization. The
stabilizer of `Q` is contained in that of `P(Q)`, whose order is the ramification index `e(P)`;
this file proves the inequality `e(P) ≤ [κ(Q) : K']` that makes the two stabilizers equal.

* `le_ramificationIdx_of_map_le_pow`: in a Dedekind extension, `p S ≤ 𝔓ⁿ` implies `n ≤ e(𝔓 | p)`;
* `le_finrank_of_map_le_pow`: for the integral closure `O_F` of a discrete valuation ring `O` in a
  finite separable extension `F` of its fraction field, `𝔪_O O_F ≤ 𝔓ⁿ` implies `n ≤ [F : K']`
  (from `∑ e f = [F : K']`);
* `isLocalRing_integralClosure`, `mem_maximalIdeal_integralClosure_iff`: over a henselian `O`, the
  integral closure of `O` in a field is local, and its maximal ideal is described without
  reference to the integral closure (`y = 0` or `y⁻¹` not integral), hence is transported by
  `O`-algebra isomorphisms (`mem_maximalIdeal_integralClosure_iff_of_algEquiv`);
* `centre χ hχ Q`: for `χ : S → D` with integral image and a maximal ideal `Q` of `D`, the
  preimage in `S` of the maximal ideal of the integral closure of `O` in `D ⧸ Q`;
  `mem_centre_iff_of_map_eq`: its equivariance;
* `comap_eq_iff_mem_stabilizer_centre`: **the stabilizer in `G` of a point `Q` of `D` (a finite
  étale `K'`-algebra on which `G` acts simply transitively on geometric points) is the stabilizer
  of its centre on the Galois extension `S` of the domain `B`**, `S` a Dedekind domain finite and
  flat over `B`, for a maximal ideal `m ≠ 0` of `B` with perfect residue field, trivial residue
  extensions in `S` and `𝔪_O = m O` (equivariance gives `⊆`;
  `|Stab Q| = [D ⧸ Q : K'] ≥ e = |Stab P|` gives equality).

## References

* [J.-P. Serre, *Corps locaux*, I §4][serre1962]
-/

open IsLocalRing Module

namespace SGA.SGA1.ExposeXIII.LoopAlgebra

section Ramification

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsDedekindDomain S] [Module.IsTorsionFree R S]

/-- In a Dedekind extension `S` of a domain `R`, if `p S ≤ 𝔓ⁿ` (`p ≠ 0`) then `n` is at most the
ramification index of `𝔓` over `p`. -/
theorem le_ramificationIdx_of_map_le_pow (p : Ideal R) (𝔓 : Ideal S) [𝔓.IsPrime]
    [𝔓.LiesOver p] (hp : p ≠ ⊥) {n : ℕ} (h : p.map (algebraMap R S) ≤ 𝔓 ^ n) :
    n ≤ 𝔓.ramificationIdx R := by
  have hpS : p.map (algebraMap R S) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (p := p) (q := 𝔓) hp,
    Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hpS inferInstance]
  have hunit : ¬ IsUnit 𝔓 := by
    rw [Ideal.isUnit_iff]
    exact Ideal.IsPrime.ne_top inferInstance
  exact (FiniteMultiplicity.of_not_isUnit hunit hpS).le_multiplicity_of_pow_dvd
    (Ideal.dvd_iff_le.mpr h)

end Ramification

section Bound

variable (O K' F : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K']
  [Algebra O K'] [IsFractionRing O K'] [Field F] [Algebra K' F] [FiniteDimensional K' F]
  [Algebra.IsSeparable K' F] [Algebra O F] [IsScalarTower O K' F]

/-- **The ramification bound.** Let `O` be a discrete valuation ring with fraction field `K'`, `F`
a finite separable extension of `K'` and `O_F` the integral closure of `O` in `F`. If the maximal
ideal of `O` maps into `𝔓ⁿ` for a prime `𝔓` of `O_F` over it, then `n ≤ [F : K']`. -/
theorem le_finrank_of_map_le_pow (𝔓 : Ideal (integralClosure O F)) [𝔓.IsPrime]
    [𝔓.LiesOver (maximalIdeal O)] {n : ℕ}
    (h : (maximalIdeal O).map (algebraMap O (integralClosure O F)) ≤ 𝔓 ^ n) :
    n ≤ finrank K' F := by
  classical
  have : IsDedekindDomain (integralClosure O F) := integralClosure.isDedekindDomain O K' F
  have : Module.Finite O (integralClosure O F) :=
    IsIntegralClosure.finite O K' F (integralClosure O F)
  have : Module.IsTorsionFree O F := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq O K' F]
    exact (algebraMap K' F).injective.comp (IsFractionRing.injective O K')
  have : Module.IsTorsionFree O (integralClosure O F) := IsIntegralClosure.isTorsionFree O F
  have : Module.Free O (integralClosure O F) :=
    IsIntegralClosure.module_free O K' F (integralClosure O F)
  have hp : maximalIdeal O ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have hn := le_ramificationIdx_of_map_le_pow (maximalIdeal O) 𝔓 hp h
  have : Fintype ((maximalIdeal O).primesOver (integralClosure O F)) :=
    (Algebra.QuasiFinite.finite_primesOver (maximalIdeal O)).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal O) (integralClosure O F)
  rw [IsIntegralClosure.rank O K' F (integralClosure O F)] at hsum
  let q₀ : (maximalIdeal O).primesOver (integralClosure O F) := ⟨𝔓, inferInstance, inferInstance⟩
  have hle : 𝔓.ramificationIdx O * 𝔓.inertiaDeg O ≤ finrank K' F := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun q : (maximalIdeal O).primesOver (integralClosure O F) ↦
      q.1.ramificationIdx O * q.1.inertiaDeg O) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ q₀)
  have hf : 1 ≤ 𝔓.inertiaDeg O := Ideal.inertiaDeg_pos 𝔓 O
  calc n ≤ 𝔓.ramificationIdx O := hn
    _ ≤ 𝔓.ramificationIdx O * 𝔓.inertiaDeg O := Nat.le_mul_of_pos_right _ hf
    _ ≤ finrank K' F := hle

end Bound

section Centre

variable (O : Type*) [CommRing O] [HenselianLocalRing O] (F : Type*) [Field F]
  [Algebra O F]

/-- Over a henselian local domain `O`, the integral closure of `O` in a field is a local ring. -/
theorem isLocalRing_integralClosure : IsLocalRing (integralClosure O F) :=
  HenselianLocalRing.isLocalRing_of_isIntegral O fun _ he ↦
    IsIdempotentElem.iff_eq_zero_or_one.mp he

attribute [local instance] isLocalRing_integralClosure

variable {O F}

/-- An element `y` of the integral closure of `O` in `F` lies in its maximal ideal iff `y = 0` or
`y⁻¹` is not integral over `O`. -/
theorem mem_maximalIdeal_integralClosure_iff (y : integralClosure O F) :
    y ∈ maximalIdeal (integralClosure O F) ↔ (y : F) = 0 ∨ ¬ IsIntegral O (y : F)⁻¹ := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hy
    by_contra! h
    obtain ⟨hy0, hint⟩ := h
    exact hy ⟨⟨y, ⟨_, hint⟩, Subtype.ext (mul_inv_cancel₀ hy0), Subtype.ext (inv_mul_cancel₀ hy0)⟩,
      rfl⟩
  · rintro h ⟨u, rfl⟩
    rcases h with h | h
    · have : ((u : integralClosure O F) : F) * ((u⁻¹ : (integralClosure O F)ˣ) : F) = 1 := by
        rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
      rw [h, zero_mul] at this
      exact zero_ne_one this
    · apply h
      have e : ((u : integralClosure O F) : F)⁻¹ = ((u⁻¹ : (integralClosure O F)ˣ) : F) := by
        rw [inv_eq_of_mul_eq_one_right]
        rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
      rw [e]
      exact ((u⁻¹ : (integralClosure O F)ˣ) : integralClosure O F).2

/-- An `O`-algebra isomorphism of fields maps the maximal ideals of the integral closures of `O`
onto each other. -/
theorem mem_maximalIdeal_integralClosure_iff_of_algEquiv {F' : Type*} [Field F'] [Algebra O F']
    (τ : F ≃ₐ[O] F') {y : F} (hy : IsIntegral O y) :
    (⟨y, hy⟩ : integralClosure O F) ∈ maximalIdeal (integralClosure O F) ↔
      (⟨τ y, hy.map τ⟩ : integralClosure O F') ∈ maximalIdeal (integralClosure O F') := by
  rw [mem_maximalIdeal_integralClosure_iff, mem_maximalIdeal_integralClosure_iff]
  simp only
  rw [map_eq_zero_iff τ τ.injective, ← map_inv₀, isIntegral_algEquiv]

end Centre

section CentreMap

attribute [local instance] isLocalRing_integralClosure

variable {O : Type*} [CommRing O] [HenselianLocalRing O] {D : Type*} [CommRing D] [Algebra O D]
  {S : Type*} [CommRing S] (χ : S →+* D) (hχ : ∀ s, IsIntegral O (χ s)) (Q : Ideal D)
  [Q.IsMaximal]

/-- The map `S → D ⧸ Q`, landing in the integral closure of `O` in the field `D ⧸ Q`. -/
noncomputable def centreHom :
    letI := Ideal.Quotient.field Q
    S →+* integralClosure O (D ⧸ Q) :=
  letI := Ideal.Quotient.field Q
  ((Ideal.Quotient.mk Q).comp χ).codRestrict (integralClosure O (D ⧸ Q))
    fun s ↦ (hχ s).map (Ideal.Quotient.mkₐ O Q)

/-- **The centre** on `S` of the valuation of the field `D ⧸ Q`: the preimage of the maximal
ideal of the integral closure of `O` in `D ⧸ Q` (a local ring, `O` being henselian). When `S` is
the normalization of a curve in a covering and `D` the algebra of the covering over the fraction
field of the strict henselization `O` at `a`, this is the point of the normalization over `a`
attached to the point `Q` of the covering over that field. -/
noncomputable def centre : Ideal S :=
  letI := Ideal.Quotient.field Q
  (maximalIdeal (integralClosure O (D ⧸ Q))).comap (centreHom χ hχ Q)

theorem mem_centre_iff (s : S) :
    letI := Ideal.Quotient.field Q
    s ∈ centre χ hχ Q ↔ Ideal.Quotient.mk Q (χ s) = 0 ∨
      ¬ IsIntegral O (Ideal.Quotient.mk Q (χ s))⁻¹ := by
  let := Ideal.Quotient.field Q
  exact mem_maximalIdeal_integralClosure_iff (centreHom χ hχ Q s)

/-- **Equivariance of the centre**: if `σ` is an `O`-algebra automorphism of `D` mapping the
maximal ideal `Q'` onto `Q` and `f` is an endomorphism of `S` with `χ ∘ f = σ ∘ χ`, then `s` lies
in the centre attached to `Q'` iff `f s` lies in the centre attached to `Q`. -/
theorem mem_centre_iff_of_map_eq (σ : D ≃ₐ[O] D) (f : S →+* S) (hf : ∀ s, χ (f s) = σ (χ s))
    (Q' : Ideal D) [Q'.IsMaximal] (hQ : Q = Q'.map σ) (s : S) :
    s ∈ centre χ hχ Q' ↔ f s ∈ centre χ hχ Q := by
  let := Ideal.Quotient.field Q
  let := Ideal.Quotient.field Q'
  let τ : (D ⧸ Q') ≃ₐ[O] (D ⧸ Q) := Ideal.quotientEquivAlg Q' Q σ hQ
  have hτ : τ (Ideal.Quotient.mk Q' (χ s)) = Ideal.Quotient.mk Q (χ (f s)) := by
    rw [hf]
    rfl
  change centreHom χ hχ Q' s ∈ maximalIdeal _ ↔ centreHom χ hχ Q (f s) ∈ maximalIdeal _
  have h := mem_maximalIdeal_integralClosure_iff_of_algEquiv τ
    ((hχ s).map (Ideal.Quotient.mkₐ O Q'))
  convert h using 2
  · exact Subtype.ext rfl
  · exact Subtype.ext hτ.symm

end CentreMap

section Stabilizer

open scoped Pointwise

attribute [local instance] isLocalRing_integralClosure

variable {B : Type*} [CommRing B] {S : Type*} [CommRing S] [Algebra B S] [Algebra.IsIntegral B S]
  {O : Type*} [CommRing O] [HenselianLocalRing O] [Algebra B O]
  {K' : Type*} [Field K'] [Algebra O K'] {D : Type*} [CommRing D] [Algebra K' D] [Algebra O D]
  [IsScalarTower O K' D]
  (χ : S →+* D) (hχB : ∀ b, χ (algebraMap B S b) = algebraMap O D (algebraMap B O b))

omit [HenselianLocalRing O] in
include hχB in
/-- The images of `S` in `D` are integral over `O`. -/
theorem isIntegral_apply (s : S) : IsIntegral O (χ s) := by
  let : Algebra B D := ((algebraMap O D).comp (algebraMap B O)).toAlgebra
  have : IsScalarTower B O D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let χ' : S →ₐ[B] D := { χ with commutes' := hχB }
  exact ((Algebra.IsIntegral.isIntegral (R := B) s).map χ').tower_top

variable {G : Type*} [Group G] [MulSemiringAction G S] (ρ : G →* (D ≃ₐ[K'] D))
  (hχρ : ∀ (g : G) (s : S), χ (g • s) = ρ g (χ s))

include hχρ in
/-- The centre is equivariant: an element `g` of `G` fixing the point `Q` (`ρ g (Q) = Q`) fixes
its centre. -/
theorem mem_stabilizer_centre_of_comap_eq (Q : Ideal D) [Q.IsMaximal] {g : G}
    (hg : Q.comap (ρ g) = Q) :
    g ∈ MulAction.stabilizer G (centre χ (isIntegral_apply χ hχB) Q) := by
  set σ : D ≃ₐ[O] D := (ρ g).restrictScalars O
  have hQ : Q = Q.map σ := by
    conv_rhs => rw [← hg]
    exact (Ideal.map_comap_of_surjective _ σ.surjective Q).symm
  have key (s : S) : s ∈ centre χ (isIntegral_apply χ hχB) Q ↔
      g • s ∈ centre χ (isIntegral_apply χ hχB) Q :=
    mem_centre_iff_of_map_eq χ (isIntegral_apply χ hχB) Q σ
      (MulSemiringAction.toRingHom G S g) (fun s ↦ hχρ g s) Q hQ s
  rw [MulAction.mem_stabilizer_iff, Ideal.pointwise_smul_eq_comap]
  ext s
  rw [Ideal.mem_comap, key]
  simp

include hχρ in
/-- **Stabilizer of a point over `K'` = stabilizer of its centre.** In the setting of
`mem_stabilizer_centre_of_comap_eq` (`S` integral over `B`, `O` henselian, `χ : S → D` compatible
with `B → O → K' → D`, and `G` acting on `S` and, through `ρ`, on the `K'`-algebra `D`,
compatibly with `χ`), assume moreover:
* `B` is a domain, `S` is a Dedekind domain, finite, flat and torsion-free over `B`, `G` is
  finite and `S` is Galois over `B` with group `G` (`IsGaloisGroup`);
* `O` is a discrete valuation ring with fraction field `K'`, and `D` is finite and unramified
  over `K'`;
* `m ≠ 0` is a maximal ideal of `B` with perfect residue field, the residue extensions of the
  primes of `S` over `m` are trivial (`m.inertiaDegIn S = 1`), and `O` is unramified over `B` at
  `m` (`𝔪_O = m O`);
* `G` acts simply transitively (through `ρ`) on the geometric points `D →ₐ[K'] Ω`, `Ω`
  algebraically closed.

Then for every maximal ideal `Q` of `D`, the stabilizer of `Q` in `G` is the stabilizer of its
centre on `S`. (Inclusion by equivariance; equality by counting:
`|Stab Q| = [D ⧸ Q : K'] ≥ e = |Stab (centre Q)|`.) -/
theorem comap_eq_iff_mem_stabilizer_centre [IsDomain B] [IsDedekindDomain S] [Module.Finite B S]
    [Module.Flat B S] [Module.IsTorsionFree B S] [Finite G] [IsGaloisGroup G B S] [IsDomain O]
    [IsDiscreteValuationRing O] [IsFractionRing O K'] [Module.Finite K' D]
    [Algebra.FormallyUnramified K' D] (m : Ideal B) [m.IsMaximal] [PerfectField m.ResidueField]
    (hmO : maximalIdeal O = m.map (algebraMap B O))
    (hm : m ≠ ⊥) (hf1 : m.inertiaDegIn S = 1) {Ω : Type*} [Field Ω] [Algebra K' Ω]
    [IsAlgClosed Ω] (hS : ∀ φ : D →ₐ[K'] Ω, Function.Bijective fun g : G ↦ φ.comp (ρ g).toAlgHom)
    (Q : Ideal D) [Q.IsMaximal] (g : G) :
    Q.comap (ρ g) = Q ↔ g ∈ MulAction.stabilizer G (centre χ (isIntegral_apply χ hχB) Q) := by
  classical
  refine ⟨mem_stabilizer_centre_of_comap_eq χ hχB ρ hχρ Q, fun hg ↦ ?_⟩
  let := Ideal.Quotient.field Q
  set P := centre χ (isIntegral_apply χ hχB) Q
  set OQ := integralClosure O (D ⧸ Q)
  have : Module.Finite K' (D ⧸ Q) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K' Q).toLinearMap
    (Ideal.Quotient.mkₐ_surjective K' Q)
  have : Algebra.FormallyUnramified K' (D ⧸ Q) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ K' Q)
      (Ideal.Quotient.mkₐ_surjective K' Q)
  have : Algebra.IsSeparable K' (D ⧸ Q) := Algebra.FormallyUnramified.isSeparable K' (D ⧸ Q)
  have : Algebra.IsAlgebraic K' (D ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  -- `ρ` is injective, and its image acts simply transitively
  let φ₀ : D →ₐ[K'] Ω := (IsAlgClosed.lift : (D ⧸ Q) →ₐ[K'] Ω).comp (Ideal.Quotient.mkₐ K' Q)
  have hρinj : Function.Injective ρ := fun g₁ g₂ h ↦ (hS φ₀).1 (by simp only [h])
  let e : G ≃* ρ.range := MonoidHom.ofInjective hρinj
  have hS' : ∀ φ : D →ₐ[K'] Ω,
      Function.Bijective fun s : ρ.range ↦ φ.comp (s.1 : D ≃ₐ[K'] D).toAlgHom := by
    intro φ
    have : (fun s : ρ.range ↦ φ.comp (s.1 : D ≃ₐ[K'] D).toAlgHom) =
        (fun g : G ↦ φ.comp (ρ g).toAlgHom) ∘ e.symm := by
      funext s
      simp only [Function.comp_apply]
      congr 3
      exact (congrArg Subtype.val (e.apply_symm_apply s)).symm
    rw [this]
    exact (hS φ).comp e.symm.bijective
  -- the stabilizer of `Q`, as a subgroup of `G`
  let H₁ : Subgroup G := (TameGaloisAlgebra.stabilizer ρ.range Q).comap e.toMonoidHom
  have hH₁ (g : G) : g ∈ H₁ ↔ Q.comap (ρ g) = Q := Iff.rfl
  have hcard₁ : Nat.card H₁ = Module.finrank K' (D ⧸ Q) := by
    rw [← TameGaloisAlgebra.card_stabilizer_eq_finrank hS' Q]
    change Nat.card ((TameGaloisAlgebra.stabilizer ρ.range Q).comap e.toMonoidHom) = _
    rw [Subgroup.comap_equiv_eq_map_symm', Subgroup.card_map_of_injective e.symm.injective]
  -- the centre `P` is a prime of `S` over `m`
  have hcomapO : (maximalIdeal O).comap (algebraMap B O) = m := by
    have hle : m ≤ (maximalIdeal O).comap (algebraMap B O) := by
      rw [hmO]
      exact Ideal.le_comap_map
    exact ((inferInstance : m.IsMaximal).eq_of_le
      (Ideal.comap_ne_top _ (maximalIdeal.isMaximal O).ne_top) hle).symm
  have hcomp : (centreHom χ (isIntegral_apply χ hχB) Q).comp (algebraMap B S) =
      (algebraMap O OQ).comp (algebraMap B O) := by
    ext b
    change Ideal.Quotient.mk Q (χ (algebraMap B S b)) = _
    rw [hχB]
    rfl
  have hOQ : (maximalIdeal OQ).comap (algebraMap O OQ) = maximalIdeal O :=
    HenselianLocalRing.comap_eq_maximalIdeal_of_isMaximal (maximalIdeal.isMaximal OQ)
  have hPprime : P.IsPrime := Ideal.comap_isPrime _ _
  have hPover : P.LiesOver m := by
    refine ⟨?_⟩
    change m = (P.comap (algebraMap B S))
    change m = ((maximalIdeal OQ).comap (centreHom χ (isIntegral_apply χ hχB) Q)).comap
      (algebraMap B S)
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hOQ, hcomapO]
  -- the order of the stabilizer of `P` is the ramification index `e`
  have hcardP : Nat.card (MulAction.stabilizer G P) = P.ramificationIdx B := by
    rw [Ideal.card_stabilizer_eq m P, hf1, mul_one,
      Ideal.ramificationIdxIn_eq_ramificationIdx m P G]
  -- `e ≤ [D ⧸ Q : K']`
  have hold : m.ramificationIdx' P = P.ramificationIdx B :=
    Ideal.ramificationIdx'_eq_ramificationIdx (p := m) (q := P) hm
  have hOQover : (maximalIdeal OQ).LiesOver (maximalIdeal O) := ⟨hOQ.symm⟩
  have hle : P.ramificationIdx B ≤ Module.finrank K' (D ⧸ Q) := by
    rw [← hold]
    apply le_finrank_of_map_le_pow O K' (D ⧸ Q) (maximalIdeal OQ)
    rw [hmO, Ideal.map_map, ← hcomp, ← Ideal.map_map]
    calc _ ≤ (P ^ m.ramificationIdx' P).map (centreHom χ (isIntegral_apply χ hχB) Q) :=
          Ideal.map_mono (Ideal.le_pow_ramificationIdx' (p := m) (P := P))
      _ = (P.map (centreHom χ (isIntegral_apply χ hχB) Q)) ^ m.ramificationIdx' P :=
          Ideal.map_pow _ _ _
      _ ≤ _ := Ideal.pow_right_mono Ideal.map_comap_le _
  -- hence the stabilizer of `Q` is that of `P`
  have hH₁P : H₁ ≤ MulAction.stabilizer G P :=
    fun g' hg' ↦ mem_stabilizer_centre_of_comap_eq χ hχB ρ hχρ Q hg'
  have heq : H₁ = MulAction.stabilizer G P :=
    Subgroup.eq_of_le_of_card_ge hH₁P (by rw [hcardP, hcard₁]; exact hle)
  rw [← hH₁ g, heq]
  exact hg
end Stabilizer

end SGA.SGA1.ExposeXIII.LoopAlgebra
