/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.TameLiftingProof
import SGA.SGA1.ExposeXIII.ProLShortExact

/-!
# SGA 1, Exposé XIII, 4.4 (second part) over a complete discrete valuation ring

With the core of X.3.8 (`SGA.SGA1.ExposeX.tameLiftingDVRStatement`) the conclusion of XIII.4.3,
the exactness of `1 → π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1`, holds at the geometric generic point of
the spectrum of a complete discrete valuation ring with separably closed residue field. Together
with X.2.1 at the closed point (`isProLShortExact_of_isRegularLocalRing`) this gives the second
part of XIII.4.4 for such bases, without the section
(`properSmoothHomotopyExactSequence_of_isDiscreteValuationRing`).

* `comap_primeKernel_le_proLKernel_of_factorsPrimeTo`: group theory. If every continuous
  homomorphism of `π₁(X_s̄)` into a finite group of order prime to `q` factors through
  `u : π₁(X_s̄) → π₁(X)`, and no prime of `L` divides `q`, then `π₁^L(X_s̄) → π'₁(X)` is injective.
* `isProLShortExact_generic_of_isSepClosed_residueField`: the generic geometric point.
* `properSmoothHomotopyExactSequence_of_isDiscreteValuationRing`: every geometric point.
* `ProperSmoothHomotopyExactSequenceRegularStatement`: the second part of XIII.4.4 over a regular
  base (statement only), the target of "route B".
-/

universe u v

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace SGA.SGA1.ExposeXIII

section Group

variable {L : Set ℕ} {G'' G' G : Type v} [Group G''] [Group G'] [Group G]
  [TopologicalSpace G''] [TopologicalSpace G'] [IsTopologicalGroup G'']

/-- The injectivity of `u : π₁^L(X_s̄) → π'₁(X)` from a factorization property: if every
continuous homomorphism of `G''` into a finite group of order prime to `q` factors continuously
through `h' : G'' → G'`, and no prime of `L` divides `q`, then the preimage of the kernel `N` of
`ker h → (ker h)^L` lies in the pro-`L` kernel of `G''`. -/
theorem comap_primeKernel_le_proLKernel_of_factorsPrimeTo (h' : G'' →* G') (h : G' →* G) (q : ℕ)
    (hLq : ∀ ℓ ∈ L, ¬ ℓ ∣ q) (hf : ExposeX.FactorsPrimeTo h' q) :
    (primeKernel L h).comap h' ≤ proLKernel L G'' := by
  intro x hx
  rw [mem_proLKernel]
  intro N hN hNo hNL
  -- the finite quotient `Q = G'' ⧸ N`, with the discrete topology
  let Q := G'' ⧸ N
  have : N.FiniteIndex := ⟨hNL.1⟩
  have : Finite Q := inferInstance
  let : TopologicalSpace Q := ⊥
  have : DiscreteTopology Q := ⟨rfl⟩
  have hφ : Continuous (QuotientGroup.mk' N) := by
    refine continuous_discrete_rng.mpr fun c ↦ ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    have : (QuotientGroup.mk' N) ⁻¹' {(g : Q)} = (fun y ↦ g * y) '' (N : Set G'') := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, QuotientGroup.mk'_apply,
        Set.mem_image, SetLike.mem_coe]
      rw [eq_comm, QuotientGroup.eq]
      constructor
      · intro hy
        exact ⟨g⁻¹ * y, hy, by group⟩
      · rintro ⟨n, hn, rfl⟩
        rwa [← mul_assoc, inv_mul_cancel, one_mul]
    rw [this]
    exact (Homeomorph.mulLeft g).isOpenMap _ hNo
  have hcop : (Nat.card Q).Coprime q := by
    refine Nat.coprime_of_dvd fun ℓ hℓ hdvd hdvdq ↦ hLq ℓ (hNL.2 ℓ hℓ ?_) hdvdq
    exact hdvd
  obtain ⟨g, hg, hgu⟩ := hf Q hcop (QuotientGroup.mk' N) hφ
  -- `ker g ∩ ker h` is an open normal subgroup of `ker h` with `L`-group quotient
  obtain ⟨y, hy, hyx⟩ := hx
  let M : Subgroup h.ker := g.ker.subgroupOf h.ker
  have hMo : IsOpen (M : Set h.ker) := by
    have : IsOpen (g.ker : Set G') := by
      have : (g.ker : Set G') = g ⁻¹' {1} := rfl
      rw [this]
      exact (isOpen_discrete _).preimage hg
    exact this.preimage continuous_subtype_val
  have hML : IsLIndex L M := by
    have hdvd : M.index ∣ Nat.card Q := by
      have h₁ : M.index ∣ g.ker.index := Subgroup.relIndex_dvd_index_of_normal g.ker h.ker
      have h₂ : g.ker.index ∣ Nat.card Q := by
        rw [Subgroup.index_ker]
        exact Subgroup.card_subgroup_dvd_card _
      exact h₁.trans h₂
    refine ⟨fun h0 ↦ ?_, fun ℓ hℓ hdvdℓ ↦ hNL.2 ℓ hℓ (hdvdℓ.trans hdvd)⟩
    rw [h0, zero_dvd_iff] at hdvd
    exact (Nat.card_pos (α := Q)).ne' hdvd
  have hyM : y ∈ M := proLKernel_le (Subgroup.normal_subgroupOf) hMo hML hy
  have hgx : g (h' x) = 1 := by
    rw [← hyx]
    exact hyM
  have : QuotientGroup.mk' N x = 1 := by
    rw [← hgu, MonoidHom.comp_apply, hgx]
  exact (QuotientGroup.eq_one_iff x).mp this

end Group

section DVR

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [IsSepClosed (ResidueField R)] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Smooth f] [GeometricallyConnected f]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsAdicComplete (maximalIdeal R) R]
  [IsSepClosed (ResidueField R)] in
/-- A prime invertible on the spectrum of a local ring does not divide the characteristic
exponent of its residue field. -/
lemma not_dvd_ringExpChar_of_mem_primesInvertibleOn [IsLocalRing R] {ℓ : ℕ}
    (hℓ : ℓ ∈ primesInvertibleOn (Spec (.of R))) : ¬ ℓ ∣ ringExpChar (ResidueField R) := by
  obtain ⟨hprime, hne⟩ := hℓ
  intro hdvd
  have hchar : ringChar ((Spec (.of R)).residueField (closedPoint R)) =
      ringChar (ResidueField R) := by
    let e₁ : ResidueField R ≃+* (maximalIdeal R).ResidueField :=
      RingEquiv.ofBijective (algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField _)
    let e₂ : (maximalIdeal R).ResidueField ≃+* (Spec (.of R)).residueField (closedPoint R) :=
      (Scheme.Spec.residueFieldIso (.of R) (closedPoint R)).commRingCatIsoToRingEquiv.symm
    let : Algebra (ResidueField R) ((Spec (.of R)).residueField (closedPoint R)) :=
      (e₁.trans e₂).toRingHom.toAlgebra
    have : Nontrivial ((Spec (.of R)).residueField (closedPoint R)) :=
      (e₁.trans e₂).injective.nontrivial
    exact (Algebra.ringChar_eq (ResidueField R) _).symm
  apply hne (closedPoint R)
  rw [hchar]
  obtain ⟨p, hp⟩ : ∃ p, ExpChar (ResidueField R) p := ⟨_, ringExpChar.of_eq rfl⟩
  rw [ringExpChar.eq _ p] at hdvd
  cases hp with
  | zero => exact absurd (Nat.le_of_dvd one_pos hdvd) hprime.one_lt.not_ge
  | prime hp' =>
    rw [ringChar.eq (ResidueField R) p]
    exact ((Nat.prime_dvd_prime_iff_eq hprime hp').mp hdvd).symm

/-- The second part of XIII.4.4 (the conclusion XIII.4.3.1 of XIII.4.3) at the geometric generic
point of the spectrum of a complete discrete valuation ring `R` with separably closed residue
field, without a section: for `f : X ⟶ Spec R` proper and smooth with geometrically connected
fibres, `1 → π₁^L(X_η̄) → π'₁(X) → π₁(Spec R) → 1` is exact, `L` the primes invertible on `R`.
(The core of X.3.8, `SGA.SGA1.ExposeX.tameLiftingDVRStatement`.) -/
theorem isProLShortExact_generic_of_isSepClosed_residueField (Ω₁ : Type u) [Field Ω₁]
    [IsAlgClosed Ω₁] [Algebra R Ω₁] (hinj : Function.Injective (algebraMap R Ω₁)) (Ω : Type u)
    [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R Ω₁)))) :
    IsProLShortExact (primesInvertibleOn (Spec (.of R)))
      (FundamentalGroup.map (pullback.fst f _) a)
      (FundamentalGroup.map f (a ≫ pullback.fst f _)) :=
  ⟨properHomotopyExactSequence _ f Ω₁ _ Ω a,
    comap_primeKernel_le_proLKernel_of_factorsPrimeTo _ _ _
      (fun _ hℓ ↦ not_dvd_ringExpChar_of_mem_primesInvertibleOn R hℓ)
      (ExposeX.tameLiftingDVRStatement R f Ω₁ hinj Ω a)⟩

/-- **The second part of XIII.4.4 over a complete discrete valuation ring with separably closed
residue field** (`ProperSmoothHomotopyExactSequenceStatement` for `S = Spec R`, without the
section): for `f : X ⟶ Spec R` proper and smooth with geometrically connected fibres, the sequence
`1 → π₁^L(X_s̄) → π'₁(X) → π₁(Spec R) → 1` is exact at every geometric point `s̄`, `L` the primes
invertible on `R`. At the closed point this is X.2.1 (`isProLShortExact_of_isRegularLocalRing`), at
the generic point the core of X.3.8 (`isProLShortExact_generic_of_isSepClosed_residueField`). -/
theorem properSmoothHomotopyExactSequence_of_isDiscreteValuationRing (Ω₀ : Type u) [Field Ω₀]
    [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ Spec (.of R)) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f s) :
    IsProLShortExact (primesInvertibleOn (Spec (.of R)))
      (FundamentalGroup.map (pullback.fst f s) a)
      (FundamentalGroup.map f (a ≫ pullback.fst f s)) := by
  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of R ⟶ CommRingCat.of Ω₀, s = Spec.map φ :=
    ⟨Spec.preimage s, (Spec.map_preimage s).symm⟩
  let : Algebra R Ω₀ := φ.hom.toAlgebra
  by_cases hinj : Function.Injective φ.hom
  · exact isProLShortExact_generic_of_isSepClosed_residueField R f Ω₀ hinj Ω a
  · refine isProLShortExact_of_isRegularLocalRing R f _ Ω₀ (Spec.map φ) (fun x ↦ ?_) Ω a
    have hker : RingHom.ker φ.hom ≠ ⊥ := fun h ↦ hinj ((RingHom.injective_iff_ker_eq_bot _).mpr h)
    have hx : x.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ x.isPrime
    apply PrimeSpectrum.ext
    change Ideal.comap φ.hom x.asIdeal = maximalIdeal R
    rw [hx, ← RingHom.ker_eq_comap_bot]
    exact IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ.hom).isMaximal hker)

end DVR

/-- XIII.4.4, second part, over a regular base (statement only): the statement
`ProperSmoothHomotopyExactSequenceStatement` for `S` regular. Over a regular base SGA's route
through `R¹f_*` (XIII.1.16, cohomological properness) can be replaced by purity on the regular `X`
and the core of X.3.8 at the codimension-one points of `S` ("route B"). Proved so far, without the
section, when `S` is the spectrum of a field (`properSmoothHomotopyExactSequence_of_field`,
`SGA.SGA1.ExposeXIII.ProLShortExact`) and when `S` is the spectrum of a complete discrete valuation
ring with separably closed residue field
(`properSmoothHomotopyExactSequence_of_isDiscreteValuationRing`). -/
def ProperSmoothHomotopyExactSequenceRegularStatement : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    [IsLocallyNoetherian S] [ConnectedSpace S], ExposeX.IsRegularScheme S →
    ∀ (g : S ⟶ X), g ≫ f = 𝟙 S →
    ∀ (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ S) (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback f s),
    IsProLShortExact (primesInvertibleOn S) (FundamentalGroup.map (pullback.fst f s) a)
      (FundamentalGroup.map f (a ≫ pullback.fst f s))

end SGA.SGA1.ExposeXIII
