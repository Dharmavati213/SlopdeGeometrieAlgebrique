/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.PuncturedDiscConnected
import SGA.Foundations.Topology.CoveringProd
import SGA.Foundations.Topology.FundamentalGroupProd

/-!
# Products of punctured discs: the local model of a normal-crossings divisor

Let `Bᵢ ⊆ ℂ ∖ {0}` (`i` in a finite type `ι`) be open with `exp⁻¹(Bᵢ)` simply connected, e.g.
punctured discs, and let `Y` be simply connected, e.g. a polydisc. The product
`(Π i, Bᵢ) × Y` is the complement of a normal-crossings divisor in a polydisc, locally:
`(Δ*)ᵖ × Δ^q`. This file computes its fundamental group and its connected finite coverings:

* `Complex.fundamentalGroupMulEquivIntPi : Multiplicative (ι → ℤ) ≃* π₁((Π i, Bᵢ) × Y, b)`,
  sending the `i`-th basis vector to the loop around `0` in the `i`-th factor;
* `Complex.multiPowRestrict`: the multi-Kummer covering `((wᵢ)ᵢ, y) ↦ ((wᵢⁿ)ᵢ, y)`, a finite
  covering (`Complex.isCoveringMap_multiPowRestrict`) on whose fibres `a ∈ ℤ^ι` acts by
  `wᵢ ↦ exp (2πi / n) ^ aᵢ * wᵢ` (`Complex.monodromy_fundamentalGroupMulEquivIntPi_fst`);
* `Complex.exists_continuousMap_multiPowRestrict`: every connected finite covering `E` of
  `(Π i, Bᵢ) × Y` is dominated by a multi-Kummer covering: there are `n ≠ 0` and a continuous
  map `f` from the multi-Kummer covering of degree `n` to `E`, over `(Π i, Bᵢ) × Y`.
  Moreover (`Complex.exists_subgroup_continuousMap_multiPowRestrict`) `f` is an open quotient map
  and identifies `E` with the quotient of the multi-Kummer covering by a subgroup `H` of the group
  `(μₙ)^ι` of its deck transformations (`Complex.multiPowRestrictDeck`): `f x = f x'` iff
  `x' = ζ • x` for some `ζ ∈ H`.

This is the topological input of the proof of SGA 1 XII.5.1 (step (c): a finite étale covering of
`(Δ*)ᵖ × Δ^q` is a quotient of a Kummer covering `Tᵢ^{nᵢ} = zᵢ`) and of XII.5.4. Here all the
exponents `nᵢ` are equal, which is no loss: the Kummer covering with exponents `nᵢ` is itself a
quotient of the one with exponent `lcm nᵢ`. The case `ι = Unit`, `Y = Unit` is
`Complex.exists_homeomorph_powRestrict` (punctured disc).

General tool proved on the way: `MulAction.exists_smul_comm_of_stabilizer_le` (an equivariant map
out of a transitive `G`-set exists as soon as stabilizers are contained in each other).

## References

* [SGA 1, Exposé XII, proof of 5.1 and 5.4][grothendieck1971]
* [A. Hatcher, *Algebraic Topology*, §1.3][hatcher02]
-/

open Set Topology CategoryTheory Real

/-- If `A` is a pretransitive `G`-set and `a ∈ A`, `b ∈ B` satisfy `stab a ≤ stab b`, then there
is a `G`-equivariant map `A → B` sending `a` to `b`. -/
theorem MulAction.exists_smul_comm_of_stabilizer_le {G A B : Type*} [Group G] [MulAction G A]
    [MulAction G B] [IsPretransitive G A] {a : A} {b : B}
    (h : stabilizer G a ≤ stabilizer G b) :
    ∃ Φ : A → B, Φ a = b ∧ ∀ (g : G) (x : A), Φ (g • x) = g • Φ x := by
  have key (g g' : G) (hg : g • a = g' • a) : g • b = g' • b := by
    have hmem : g'⁻¹ * g ∈ stabilizer G a := by
      rw [mem_stabilizer_iff, mul_smul, hg, inv_smul_smul]
    have := h hmem
    rwa [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff] at this
  choose χ hχ using fun x : A ↦ exists_smul_eq G a x
  refine ⟨fun x ↦ χ x • b, (key _ 1 (by rw [hχ, one_smul])).trans (one_smul _ _),
    fun g x ↦ ?_⟩
  rw [smul_smul]
  exact key _ _ (by rw [hχ, mul_smul, hχ])

namespace Complex

/-! ### The fundamental group -/

section FundamentalGroup

variable {ι : Type*} {B : ι → Set ℂ} {Y : Type*} [TopologicalSpace Y]
  (hB0 : ∀ i, (0 : ℂ) ∉ B i) [∀ i, SimplyConnectedSpace (expPreimage (B i))]
  [SimplyConnectedSpace Y]

/-- `π₁((Π i, Bᵢ) × Y) ≅ ℤ^ι` for `Bᵢ ⊆ ℂ ∖ {0}` with `exp⁻¹(Bᵢ)` simply connected (e.g.
punctured discs) and `Y` simply connected (e.g. a polydisc). The vector `a` goes to the product
of the loops `ℓᵢ^{aᵢ}`, `ℓᵢ` being the loop around `0` in the `i`-th factor
(`fundamentalGroupMulEquivIntPi_apply`). -/
noncomputable def fundamentalGroupMulEquivIntPi (b : (∀ i, B i) × Y) :
    Multiplicative (ι → ℤ) ≃* FundamentalGroup ((∀ i, B i) × Y) b :=
  letI : Unique (FundamentalGroup Y b.2) := uniqueOfSubsingleton 1
  (MulEquiv.funMultiplicative ι ℤ).trans <|
    (MulEquiv.piCongrRight fun i ↦ fundamentalGroupMulEquivInt (hB0 i) (b.1 i)).trans <|
      (FundamentalGroup.piMulEquiv b.1).trans <|
        MulEquiv.prodUnique.symm.trans (FundamentalGroup.prodMulEquiv b.1 b.2)

lemma fundamentalGroupMulEquivIntPi_apply (b : (∀ i, B i) × Y) (a : Multiplicative (ι → ℤ)) :
    fundamentalGroupMulEquivIntPi hB0 b a =
      FundamentalGroup.prodMulEquiv b.1 b.2 (FundamentalGroup.piMulEquiv b.1
        (fun i ↦ generatorLoop (hB0 i) (b.1 i) ^ (Multiplicative.toAdd a i)), 1) :=
  rfl

end FundamentalGroup

/-! ### Kummer coverings -/

section Kummer

variable {B : Set ℂ} {n : ℕ}

/-- The monodromy of `ℓᵏ` (`ℓ` the loop around `0`) on the Kummer covering of degree `n` is
multiplication by `exp (2πi / n) ^ k`. -/
theorem monodromy_generatorLoop_zpow_powRestrict (hB0 : (0 : ℂ) ∉ B)
    [PathConnectedSpace (expPreimage B)] (hn : n ≠ 0) (b : B) (k : ℤ)
    (w : powRestrict B n ⁻¹' {b}) :
    ((isCoveringMap_powRestrict hB0 hn).monodromy (generatorLoop hB0 b ^ k) w : ℂ) =
      exp (2 * π * I / n) ^ k * w := by
  let _ := (isCoveringMap_powRestrict hB0 hn).fundamentalGroupMulAction b
  set ℓ := generatorLoop hB0 b
  set ζ := exp (2 * π * I / n)
  have h1 (w : powRestrict B n ⁻¹' {b}) : ((ℓ • w : powRestrict B n ⁻¹' {b}) : ℂ) = ζ * w :=
    monodromy_generatorLoop_powRestrict hB0 hn b w
  have hinv (w : powRestrict B n ⁻¹' {b}) : ((ℓ⁻¹ • w : powRestrict B n ⁻¹' {b}) : ℂ) =
      ζ⁻¹ * w := by
    have h := h1 (ℓ⁻¹ • w)
    rw [smul_inv_smul] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ (exp_ne_zero _), one_mul]
  change (((ℓ ^ k) • w : powRestrict B n ⁻¹' {b}) : ℂ) = _
  induction k using Int.induction_on generalizing w with
  | zero => rw [zpow_zero, one_smul, zpow_zero, one_mul]
  | succ k ih =>
    rw [zpow_add_one, mul_smul, ih, h1, zpow_add_one₀ (exp_ne_zero _)]
    ring
  | pred k ih =>
    rw [zpow_sub_one, mul_smul, ih, hinv, zpow_sub_one₀ (exp_ne_zero _)]
    ring

/-- The Kummer space `{w | wⁿ ∈ B}` is path-connected if `exp⁻¹(B)` is. -/
theorem pathConnectedSpace_powRestrict [PathConnectedSpace (expPreimage B)] (hB0 : (0 : ℂ) ∉ B)
    (hn : n ≠ 0) : PathConnectedSpace {w : ℂ // w ^ n ∈ B} := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  let g : expPreimage B → {w : ℂ // w ^ n ∈ B} := fun v ↦ ⟨exp (v / n), by
    rw [← exp_nat_mul, mul_div_cancel₀ _ hn']
    exact v.2⟩
  refine Function.Surjective.pathConnectedSpace (f := g) (fun w ↦ ?_) (by fun_prop)
  have hw : (w : ℂ) ≠ 0 := by
    intro h
    have := w.2
    rw [h, zero_pow hn] at this
    exact hB0 this
  refine ⟨⟨n * log w, ?_⟩, Subtype.ext ?_⟩
  · change exp (n * log w) ∈ B
    rw [exp_nat_mul, exp_log hw]
    exact w.2
  · change exp (n * log w / n) = w
    rw [mul_div_cancel_left₀ _ hn', exp_log hw]

end Kummer

/-! ### Multi-Kummer coverings -/

section MultiKummer

variable {ι : Type*} (B : ι → Set ℂ) (Y : Type*) [TopologicalSpace Y] (n : ℕ)

/-- The multi-Kummer covering `((wᵢ)ᵢ, y) ↦ ((wᵢⁿ)ᵢ, y)` of `(Π i, Bᵢ) × Y`. -/
def multiPowRestrict : (∀ i, {w : ℂ // w ^ n ∈ B i}) × Y → (∀ i, B i) × Y :=
  Prod.map (Pi.map fun i ↦ powRestrict (B i) n) id

@[fun_prop] lemma continuous_multiPowRestrict : Continuous (multiPowRestrict B Y n) :=
  (Continuous.piMap fun i ↦ continuous_powRestrict (B i) n).prodMap continuous_id

variable {B Y n}

/-- For `0 ∉ Bᵢ` and `n ≠ 0`, the multi-Kummer map is a covering map. -/
theorem isCoveringMap_multiPowRestrict [Finite ι] (hB0 : ∀ i, (0 : ℂ) ∉ B i) (hn : n ≠ 0) :
    IsCoveringMap (multiPowRestrict B Y n) :=
  (IsCoveringMap.piMap fun i ↦ isCoveringMap_powRestrict (hB0 i) hn).prodMap (IsCoveringMap.id Y)

omit [TopologicalSpace Y] in
/-- The fibres of the multi-Kummer covering are finite. -/
theorem finite_multiPowRestrict_preimage [Finite ι] (hn : n ≠ 0) (b : (∀ i, B i) × Y) :
    (multiPowRestrict B Y n ⁻¹' {b}).Finite := by
  refine ((Set.Finite.pi fun i ↦ finite_powRestrict_preimage hn (b.1 i)).prod
    (finite_singleton b.2)).subset ?_
  rintro ⟨w, y⟩ h
  have h : (Pi.map (fun i ↦ powRestrict (B i) n) w, y) = b := h
  exact ⟨fun i _ ↦ congrFun (congrArg Prod.fst h) i, congrArg Prod.snd h⟩

/-- The multi-Kummer covering space is path-connected. -/
theorem pathConnectedSpace_multiPowRestrict [∀ i, PathConnectedSpace (expPreimage (B i))]
    [PathConnectedSpace Y] (hB0 : ∀ i, (0 : ℂ) ∉ B i) (hn : n ≠ 0) :
    PathConnectedSpace ((∀ i, {w : ℂ // w ^ n ∈ B i}) × Y) :=
  have := fun i ↦ pathConnectedSpace_powRestrict (B := B i) (hB0 i) hn
  inferInstance

/-- The deck transformation `((wᵢ)ᵢ, y) ↦ ((ζᵢ wᵢ)ᵢ, y)` of the multi-Kummer covering of degree
`n`, for `ζ ∈ (μₙ)^ι`. -/
def multiPowRestrictDeck (ζ : ι → rootsOfUnity n ℂ) (x : (∀ i, {w : ℂ // w ^ n ∈ B i}) × Y) :
    (∀ i, {w : ℂ // w ^ n ∈ B i}) × Y :=
  (fun i ↦ ⟨((ζ i : ℂˣ) : ℂ) * x.1 i, by
    rw [mul_pow, (mem_rootsOfUnity' n _).mp (ζ i).2, one_mul]
    exact (x.1 i).2⟩, x.2)

omit [TopologicalSpace Y] in
@[simp] lemma coe_multiPowRestrictDeck_fst (ζ : ι → rootsOfUnity n ℂ)
    (x : (∀ i, {w : ℂ // w ^ n ∈ B i}) × Y) (i : ι) :
    ((multiPowRestrictDeck ζ x).1 i : ℂ) = ((ζ i : ℂˣ) : ℂ) * x.1 i :=
  rfl

omit [TopologicalSpace Y] in
@[simp] lemma multiPowRestrictDeck_snd (ζ : ι → rootsOfUnity n ℂ)
    (x : (∀ i, {w : ℂ // w ^ n ∈ B i}) × Y) : (multiPowRestrictDeck ζ x).2 = x.2 :=
  rfl

@[fun_prop] lemma continuous_multiPowRestrictDeck (ζ : ι → rootsOfUnity n ℂ) :
    Continuous (multiPowRestrictDeck (B := B) (Y := Y) ζ) := by
  unfold multiPowRestrictDeck
  fun_prop

omit [TopologicalSpace Y] in
lemma multiPowRestrict_multiPowRestrictDeck (ζ : ι → rootsOfUnity n ℂ)
    (x : (∀ i, {w : ℂ // w ^ n ∈ B i}) × Y) :
    multiPowRestrict B Y n (multiPowRestrictDeck ζ x) = multiPowRestrict B Y n x :=
  Prod.ext (funext fun i ↦ Subtype.ext (by
    change (((ζ i : ℂˣ) : ℂ) * x.1 i) ^ n = (x.1 i : ℂ) ^ n
    rw [mul_pow, (mem_rootsOfUnity' n _).mp (ζ i).2, one_mul])) rfl

omit [TopologicalSpace Y] in
lemma multiPowRestrictDeck_one (x : (∀ i, {w : ℂ // w ^ n ∈ B i}) × Y) :
    multiPowRestrictDeck 1 x = x :=
  Prod.ext (funext fun _ ↦ Subtype.ext (one_mul _)) rfl

omit [TopologicalSpace Y] in
lemma multiPowRestrictDeck_mul (ζ ζ' : ι → rootsOfUnity n ℂ)
    (x : (∀ i, {w : ℂ // w ^ n ∈ B i}) × Y) :
    multiPowRestrictDeck (ζ * ζ') x = multiPowRestrictDeck ζ (multiPowRestrictDeck ζ' x) :=
  Prod.ext (funext fun i ↦ Subtype.ext (by
    simp only [coe_multiPowRestrictDeck_fst, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul,
      mul_assoc])) rfl

omit [TopologicalSpace Y] in
/-- Two points of the multi-Kummer covering lie over the same point iff they differ by a deck
transformation. -/
lemma multiPowRestrict_eq_iff (hB0 : ∀ i, (0 : ℂ) ∉ B i) (hn : n ≠ 0)
    {x x' : (∀ i, {w : ℂ // w ^ n ∈ B i}) × Y} :
    multiPowRestrict B Y n x = multiPowRestrict B Y n x' ↔
      ∃ ζ : ι → rootsOfUnity n ℂ, x' = multiPowRestrictDeck ζ x := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hpow (i : ι) : (x.1 i : ℂ) ^ n = (x'.1 i : ℂ) ^ n :=
      congrArg Subtype.val (congrFun (congrArg Prod.fst h) i)
    have hx0 (i : ι) : (x.1 i : ℂ) ≠ 0 := by
      intro h0
      have := (x.1 i).2
      rw [h0, zero_pow hn] at this
      exact hB0 i this
    have hq (i : ι) : ((x'.1 i : ℂ) / x.1 i) ^ n = 1 := by
      rw [div_pow, ← hpow, div_self (pow_ne_zero _ (hx0 i))]
    have hq0 (i : ι) : (x'.1 i : ℂ) / x.1 i ≠ 0 := by
      intro h0
      have := hq i
      rw [h0, zero_pow hn] at this
      exact zero_ne_one this
    refine ⟨fun i ↦ ⟨Units.mk0 _ (hq0 i), (mem_rootsOfUnity' n _).mpr (hq i)⟩,
      Prod.ext (funext fun i ↦ Subtype.ext ?_) (congrArg Prod.snd h).symm⟩
    change (x'.1 i : ℂ) = (x'.1 i : ℂ) / x.1 i * x.1 i
    rw [div_mul_cancel₀ _ (hx0 i)]
  · rintro ⟨ζ, rfl⟩
    exact (multiPowRestrict_multiPowRestrictDeck ζ x).symm

variable [∀ i, SimplyConnectedSpace (expPreimage (B i))] [SimplyConnectedSpace Y]

/-- The monodromy of `a ∈ ℤ^ι` on the multi-Kummer covering of degree `n` multiplies the `i`-th
coordinate by `exp (2πi / n) ^ aᵢ`. -/
theorem monodromy_fundamentalGroupMulEquivIntPi_fst [Finite ι] (hB0 : ∀ i, (0 : ℂ) ∉ B i)
    (hn : n ≠ 0) (b : (∀ i, B i) × Y) (a : Multiplicative (ι → ℤ))
    (w : multiPowRestrict B Y n ⁻¹' {b}) (i : ι) :
    (((isCoveringMap_multiPowRestrict hB0 hn).monodromy (fundamentalGroupMulEquivIntPi hB0 b a)
      w).1.1 i : ℂ) = exp (2 * π * I / n) ^ (Multiplicative.toAdd a i) * w.1.1 i := by
  have hK := IsCoveringMap.piMap fun i ↦ isCoveringMap_powRestrict (hB0 i) hn
  have h₁ := congrArg Prod.fst <| hK.monodromy_prodMap (IsCoveringMap.id Y)
    (Path.Homotopic.pi fun i ↦ generatorLoop (hB0 i) (b.1 i) ^ (Multiplicative.toAdd a i))
    (Path.Homotopic.Quotient.refl b.2) w
  have h₂ := congrFun (IsCoveringMap.monodromy_piMap
    (fun i ↦ isCoveringMap_powRestrict (hB0 i) hn)
    (fun i ↦ generatorLoop (hB0 i) (b.1 i) ^ (Multiplicative.toAdd a i))
    ⟨w.1.1, congrArg Prod.fst w.2⟩) i
  have h₃ := monodromy_generatorLoop_zpow_powRestrict (hB0 i) hn (b.1 i)
    (Multiplicative.toAdd a i) ⟨w.1.1 i, congrFun (congrArg Prod.fst w.2) i⟩
  exact (congrArg (fun z : (∀ i, {w : ℂ // w ^ n ∈ B i}) ↦ ((z i : {w : ℂ // w ^ n ∈ B i}) : ℂ))
    h₁).trans ((congrArg Subtype.val h₂).trans h₃)

/-- The monodromy of `ℤ^ι` on the multi-Kummer covering does not move the `Y` coordinate. -/
theorem monodromy_fundamentalGroupMulEquivIntPi_snd [Finite ι] (hB0 : ∀ i, (0 : ℂ) ∉ B i)
    (hn : n ≠ 0) (b : (∀ i, B i) × Y) (a : Multiplicative (ι → ℤ))
    (w : multiPowRestrict B Y n ⁻¹' {b}) :
    ((isCoveringMap_multiPowRestrict hB0 hn).monodromy (fundamentalGroupMulEquivIntPi hB0 b a)
      w).1.2 = w.1.2 := by
  have hK := IsCoveringMap.piMap fun i ↦ isCoveringMap_powRestrict (hB0 i) hn
  have h₁ := congrArg Prod.snd <| hK.monodromy_prodMap (IsCoveringMap.id Y)
    (Path.Homotopic.pi fun i ↦ generatorLoop (hB0 i) (b.1 i) ^ (Multiplicative.toAdd a i))
    (Path.Homotopic.Quotient.refl b.2) w
  refine h₁.trans ?_
  change ((IsCoveringMap.id Y).monodromy (.refl b.2) ⟨w.1.2, _⟩ : Y) = w.1.2
  rw [IsCoveringMap.monodromy_refl]
  rfl

end MultiKummer

/-! ### Connected finite coverings are dominated by multi-Kummer coverings -/

section Domination

variable {ι : Type} [Finite ι] {B : ι → Set ℂ} {Y : Type} [TopologicalSpace Y]

/-- **Connected finite coverings of `(Δ*)ᵖ × Δ^q` are dominated by Kummer coverings.** Let
`Bᵢ ⊆ ℂ ∖ {0}` (`i` in a finite type) be open with `exp⁻¹(Bᵢ)` simply connected (e.g. punctured
discs) and `Y` simply connected and locally path-connected (e.g. a polydisc). Let `p : E → (Π i,
Bᵢ) × Y` be a covering map with finite fibres and connected total space. Then for some `n ≠ 0`
there is a continuous map `f` from the multi-Kummer covering `((wᵢ)ᵢ, y) ↦ ((wᵢⁿ)ᵢ, y)` to `E`
with `p ∘ f` the multi-Kummer map. One can take for `n` the degree of `p`. -/
theorem exists_continuousMap_multiPowRestrict (hBo : ∀ i, IsOpen (B i))
    (hB0 : ∀ i, (0 : ℂ) ∉ B i) (hS : ∀ i, IsSimplyConnected (exp ⁻¹' B i))
    [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y] {E : Type} [TopologicalSpace E]
    [ConnectedSpace E] {p : E → (∀ i, B i) × Y} (hp : IsCoveringMap p)
    (hfin : ∀ b, (p ⁻¹' {b}).Finite) :
    ∃ (n : ℕ) (_ : n ≠ 0) (f : C((∀ i, {w : ℂ // w ^ n ∈ B i}) × Y, E)),
      ∀ x, p (f x) = multiPowRestrict B Y n x := by
  classical
  have : ∀ i, SimplyConnectedSpace (expPreimage (B i)) := fun i ↦ (hS i).simplyConnectedSpace
  have : ∀ i, PathConnectedSpace (B i) := fun i ↦
    (isAddQuotientCoveringMap_expRestrict (hB0 i)).surjective.pathConnectedSpace
      continuous_expRestrict
  have : ∀ i, LocallyPathConnectedSpace (B i) := fun i ↦ (hBo i).locallyPathConnectedSpace
  have : ∀ i, SemilocallySimplyConnectedSpace (B i) := fun i ↦
    have := (hBo i).stronglyLocallyContractibleSpace
    inferInstance
  have : LocallyPathConnectedSpace E := hp.isLocalHomeomorph.locallyPathConnectedSpace
  have hE : PathConnectedSpace E := .of_locallyPathConnectedSpace
  obtain ⟨e₀⟩ := (inferInstance : Nonempty E)
  set b₀ := p e₀
  have hF : Finite (p ⁻¹' {b₀}) := (hfin b₀).to_subtype
  set n := Nat.card (p ⁻¹' {b₀}) with hn_def
  have hn : n ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨⟨e₀, rfl⟩⟩, hF⟩
  have hK := isCoveringMap_multiPowRestrict (Y := Y) hB0 hn
  let X := TopCat.of ((∀ i, B i) × Y)
  let EC : TopCat.FiniteCovering X := ⟨Over.mk (TopCat.ofHom ⟨p, hp.continuous⟩), hp, hfin⟩
  let KC : TopCat.FiniteCovering X :=
    ⟨Over.mk (TopCat.ofHom ⟨multiPowRestrict B Y n, continuous_multiPowRestrict B Y n⟩), hK,
      finite_multiPowRestrict_preimage hn⟩
  let G := FundamentalGroup ((∀ i, B i) × Y) b₀
  let _ : MulAction G (p ⁻¹' {b₀}) := hp.fundamentalGroupMulAction b₀
  let _ : MulAction G (multiPowRestrict B Y n ⁻¹' {b₀}) := hK.fundamentalGroupMulAction b₀
  let ψ := fundamentalGroupMulEquivIntPi (Y := Y) hB0 b₀
  have hcomm (γ δ : G) : γ * δ = δ * γ := by
    obtain ⟨a, rfl⟩ := ψ.surjective γ
    obtain ⟨c, rfl⟩ := ψ.surjective δ
    rw [← map_mul, ← map_mul, mul_comm]
  -- the fibre of `E`: transitive, so `δⁿ` fixes every point
  have : PathConnectedSpace EC.obj.left := hE
  have htE : MulAction.IsPretransitive G (p ⁻¹' {b₀}) :=
    ⟨TopCat.FiniteCovering.exists_monodromy_eq (X := X) b₀ EC⟩
  let e₀' : p ⁻¹' {b₀} := ⟨e₀, rfl⟩
  have hpow (δ : G) : δ ^ n ∈ MulAction.stabilizer G e₀' := by
    let S := MulAction.stabilizer G e₀'
    have : S.Normal := ⟨fun γ hγ δ ↦ by rwa [hcomm δ γ, mul_inv_cancel_right]⟩
    have hidx : S.index = n := MulAction.index_stabilizer_of_transitive G e₀'
    rw [← hidx]
    exact S.pow_index_mem δ
  -- the fibre of the multi-Kummer covering
  let ζ := exp (2 * π * I / n)
  have hζ : IsPrimitiveRoot ζ n := isPrimitiveRoot_exp n hn
  have hmon (a : Multiplicative (ι → ℤ)) (w : multiPowRestrict B Y n ⁻¹' {b₀}) (i : ι) :
      (((ψ a • w : multiPowRestrict B Y n ⁻¹' {b₀})).1.1 i : ℂ) =
        ζ ^ (Multiplicative.toAdd a i) * w.1.1 i :=
    monodromy_fundamentalGroupMulEquivIntPi_fst hB0 hn b₀ a w i
  have hmon2 (a : Multiplicative (ι → ℤ)) (w : multiPowRestrict B Y n ⁻¹' {b₀}) :
      ((ψ a • w : multiPowRestrict B Y n ⁻¹' {b₀})).1.2 = w.1.2 :=
    monodromy_fundamentalGroupMulEquivIntPi_snd hB0 hn b₀ a w
  have hwb (w : multiPowRestrict B Y n ⁻¹' {b₀}) (i : ι) : (w.1.1 i : ℂ) ^ n = b₀.1 i :=
    congrArg Subtype.val (congrFun (congrArg Prod.fst w.2) i)
  have hwY (w : multiPowRestrict B Y n ⁻¹' {b₀}) : w.1.2 = b₀.2 := congrArg Prod.snd w.2
  have hb0 (i : ι) : (b₀.1 i : ℂ) ≠ 0 := fun h ↦ hB0 i (h ▸ (b₀.1 i).2)
  have hw0 (w : multiPowRestrict B Y n ⁻¹' {b₀}) (i : ι) : (w.1.1 i : ℂ) ≠ 0 := by
    intro h
    have := hwb w i
    rw [h, zero_pow hn] at this
    exact hb0 i this.symm
  have hroot (i : ι) : exp (log (b₀.1 i) / n) ^ n = b₀.1 i := by
    rw [← exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn), exp_log (hb0 i)]
  let k₀ : multiPowRestrict B Y n ⁻¹' {b₀} :=
    ⟨(fun i ↦ ⟨exp (log (b₀.1 i) / n), by rw [hroot]; exact (b₀.1 i).2⟩, b₀.2),
      Prod.ext (funext fun i ↦ Subtype.ext (hroot i)) rfl⟩
  have htK : MulAction.IsPretransitive G (multiPowRestrict B Y n ⁻¹' {b₀}) := by
    refine ⟨fun w w' ↦ ?_⟩
    have : NeZero n := ⟨hn⟩
    choose c _ hc using fun i ↦ hζ.eq_pow_of_pow_eq_one (ξ := (w'.1.1 i : ℂ) / w.1.1 i)
      (by rw [div_pow, hwb, hwb, div_self (hb0 i)])
    refine ⟨ψ (Multiplicative.ofAdd fun i ↦ (c i : ℤ)),
      Subtype.ext (Prod.ext (funext fun i ↦ Subtype.ext ?_) ?_)⟩
    · rw [hmon, toAdd_ofAdd, zpow_natCast, hc, div_mul_cancel₀ _ (hw0 w i)]
    · rw [hmon2, hwY, hwY]
  have hstab : MulAction.stabilizer G k₀ ≤ MulAction.stabilizer G e₀' := by
    intro γ hγ
    obtain ⟨a, rfl⟩ := ψ.surjective γ
    have hdvd (i : ι) : (n : ℤ) ∣ Multiplicative.toAdd a i := by
      have h := congrArg (fun w : multiPowRestrict B Y n ⁻¹' {b₀} ↦ (w.1.1 i : ℂ))
        (MulAction.mem_stabilizer_iff.mp hγ)
      simp only [hmon] at h
      exact (hζ.zpow_eq_one_iff_dvd _).mp ((mul_eq_right₀ (hw0 k₀ i)).mp h)
    choose c hc using hdvd
    have ha : a = Multiplicative.ofAdd c ^ n := by
      apply Multiplicative.toAdd.injective
      ext i
      rw [toAdd_pow, toAdd_ofAdd, Pi.smul_apply, hc, nsmul_eq_mul]
    rw [ha, map_pow]
    exact hpow _
  obtain ⟨Φ, -, hΦ⟩ := MulAction.exists_smul_comm_of_stabilizer_le hstab
  -- the morphism of finite coverings
  have : PathConnectedSpace X := (inferInstance : PathConnectedSpace ((∀ i, B i) × Y))
  have : LocallyPathConnectedSpace X :=
    (inferInstance : LocallyPathConnectedSpace ((∀ i, B i) × Y))
  have : SemilocallySimplyConnectedSpace X :=
    (inferInstance : SemilocallySimplyConnectedSpace ((∀ i, B i) × Y))
  let Φ' : (TopCat.FiniteCovering.fiber b₀).obj KC ⟶ (TopCat.FiniteCovering.fiber b₀).obj EC :=
    FintypeCat.homMk Φ
  let φ : (TopCat.FiniteCovering.monodromyAction b₀).obj KC ⟶
      (TopCat.FiniteCovering.monodromyAction b₀).obj EC :=
    ⟨Φ', fun γ ↦ by
      ext x
      exact hΦ γ x⟩
  let j : KC ⟶ EC :=
    (TopCat.FiniteCovering.equivalenceAction (X := X) b₀).fullyFaithfulFunctor.preimage φ
  clear_value j
  refine ⟨n, hn, j.hom.left.hom, fun x ↦ ?_⟩
  exact ConcreteCategory.congr_hom (Over.w j.hom) x


/-- **Connected finite coverings of `(Δ*)ᵖ × Δ^q` are quotients of Kummer coverings** (the form
used in the proof of SGA 1 XII.5.1, step 2 c)). With the hypotheses of
`exists_continuousMap_multiPowRestrict`, for some `n ≠ 0` there are an open quotient map `f`
from the multi-Kummer covering of degree `n` to `E`, over `(Π i, Bᵢ) × Y`, and a subgroup `H` of
the group `(μₙ)^ι` of deck transformations of the multi-Kummer covering
(`multiPowRestrictDeck`) such that `f x = f x'` iff `x' = ζ • x` for some `ζ ∈ H`. So `E` is the
quotient of the multi-Kummer covering by `H`. -/
theorem exists_subgroup_continuousMap_multiPowRestrict (hBo : ∀ i, IsOpen (B i))
    (hB0 : ∀ i, (0 : ℂ) ∉ B i) (hS : ∀ i, IsSimplyConnected (exp ⁻¹' B i))
    [SimplyConnectedSpace Y] [LocallyPathConnectedSpace Y] {E : Type} [TopologicalSpace E]
    [ConnectedSpace E] {p : E → (∀ i, B i) × Y} (hp : IsCoveringMap p)
    (hfin : ∀ b, (p ⁻¹' {b}).Finite) :
    ∃ (n : ℕ) (_ : n ≠ 0) (f : C((∀ i, {w : ℂ // w ^ n ∈ B i}) × Y, E))
      (H : Subgroup (ι → rootsOfUnity n ℂ)),
      (∀ x, p (f x) = multiPowRestrict B Y n x) ∧ IsOpenQuotientMap f ∧
      ∀ x x', f x = f x' ↔ ∃ ζ ∈ H, x' = multiPowRestrictDeck ζ x := by
  obtain ⟨n, hn, f, hf⟩ := exists_continuousMap_multiPowRestrict hBo hB0 hS hp hfin
  have : ∀ i, SimplyConnectedSpace (expPreimage (B i)) := fun i ↦ (hS i).simplyConnectedSpace
  have := pathConnectedSpace_multiPowRestrict (Y := Y) hB0 hn
  let K := (∀ i, {w : ℂ // w ^ n ∈ B i}) × Y
  have hpf : p ∘ f = multiPowRestrict B Y n := funext hf
  let H : Subgroup (ι → rootsOfUnity n ℂ) :=
    { carrier := {ζ | ∀ x, f (multiPowRestrictDeck ζ x) = f x}
      one_mem' x := by rw [multiPowRestrictDeck_one]
      mul_mem' {ζ ζ'} hζ hζ' x := by
        change ∀ x, _ at hζ hζ'
        rw [multiPowRestrictDeck_mul, hζ, hζ']
      inv_mem' {ζ} hζ x := by
        change ∀ x, _ at hζ
        rw [← hζ, ← multiPowRestrictDeck_mul, mul_inv_cancel, multiPowRestrictDeck_one] }
  have hK := isCoveringMap_multiPowRestrict (Y := Y) hB0 hn
  have hopen : IsOpenMap f :=
    (IsLocalHomeomorph.of_comp (hpf ▸ hK.isLocalHomeomorph) hp.isLocalHomeomorph
      f.continuous).isOpenMap
  refine ⟨n, hn, f, H, hf, ⟨?_, f.continuous, hopen⟩, fun x x' ↦ ⟨fun h ↦ ?_, ?_⟩⟩
  · -- surjectivity: transport along the monodromy
    intro e
    have hb0 (i : ι) : ((p e).1 i : ℂ) ≠ 0 := fun h ↦ hB0 i (h ▸ ((p e).1 i).2)
    have hroot (i : ι) : exp (log ((p e).1 i) / n) ^ n = (p e).1 i := by
      rw [← exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn), exp_log (hb0 i)]
    let x₀ : K := (fun i ↦ ⟨exp (log ((p e).1 i) / n), by rw [hroot]; exact ((p e).1 i).2⟩,
      (p e).2)
    have hx₀ : multiPowRestrict B Y n x₀ = p e :=
      Prod.ext (funext fun i ↦ Subtype.ext (hroot i)) rfl
    have : LocallyPathConnectedSpace (∀ i, B i) := by
      have := fun i ↦ (hBo i).locallyPathConnectedSpace
      infer_instance
    have : LocallyPathConnectedSpace E := hp.isLocalHomeomorph.locallyPathConnectedSpace
    have hE : PathConnectedSpace E := .of_locallyPathConnectedSpace
    let EC : TopCat.FiniteCovering (TopCat.of ((∀ i, B i) × Y)) :=
      ⟨Over.mk (TopCat.ofHom ⟨p, hp.continuous⟩), hp, hfin⟩
    have : PathConnectedSpace EC.obj.left := hE
    obtain ⟨γ, hγ⟩ := TopCat.FiniteCovering.exists_monodromy_eq
      (X := TopCat.of ((∀ i, B i) × Y)) (p e) EC ⟨f x₀, (hf x₀).trans hx₀⟩ ⟨e, rfl⟩
    have := hK.apply_monodromy hp f hf γ ⟨x₀, hx₀⟩
    exact ⟨_, this.trans (congrArg Subtype.val hγ)⟩
  · -- `f x = f x'` gives a deck transformation in `H`
    have hbase : multiPowRestrict B Y n x = multiPowRestrict B Y n x' := by
      rw [← hf, ← hf, h]
    obtain ⟨ζ, rfl⟩ := (multiPowRestrict_eq_iff hB0 hn).mp hbase
    refine ⟨ζ, fun y ↦ ?_, rfl⟩
    have := hp.eq_of_comp_eq (f.continuous.comp (continuous_multiPowRestrictDeck ζ)) f.continuous
      (by rw [← Function.comp_assoc, hpf]; exact funext fun y ↦
        multiPowRestrict_multiPowRestrictDeck ζ y) x h.symm
    exact congrFun this y
  · rintro ⟨ζ, hζ, rfl⟩
    exact (hζ x).symm

end Domination

end Complex
