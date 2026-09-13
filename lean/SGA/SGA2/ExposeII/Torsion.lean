/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# SGA 2, Exposé II, (7.5): the algebra of sections killed by ideal powers

The degree-zero comparison in II.(7.5) starts from
`Hom_R(R/J, M) ≃ {m : M | J • m = 0}` and takes the increasing union over powers
of an ideal. This file constructs the quotient-Hom equivalence and the submodule
`powerTorsion I M` of elements killed by some power of `I`, together with its
functorial linear maps and its dependence only on the radical for finitely
generated ideals.

These are algebraic ingredients of II.(7.5). No comparison with sheaf cohomology,
Koszul cohomology, or a categorical colimit is asserted here.
-/

universe u v w z

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R]
variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/-- The elements annihilated by some power of `I`, written `Γ_I(M)` in the
algebraic degree-zero formulation of local cohomology. -/
def powerTorsion : Submodule R M :=
  ⨆ n : ℕ, Submodule.torsionBySet R M (I ^ n : Ideal R)

/-- The annihilators of the powers of an ideal form an increasing sequence. -/
theorem torsionBySet_pow_monotone :
    Monotone (fun n : ℕ => Submodule.torsionBySet R M (I ^ n : Ideal R)) :=
  fun i j h => Submodule.torsionBySet_le_torsionBySet_pow i j h I

/-- The supremum defining `Γ_I(M)` is an elementwise union. -/
@[simp]
theorem mem_powerTorsion_iff (x : M) :
    x ∈ powerTorsion I M ↔ ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0 := by
  simp only [powerTorsion,
    Submodule.mem_iSup_of_directed _ (torsionBySet_pow_monotone I M).directed_le,
    Submodule.mem_torsionBySet_iff, SetCoe.forall, SetLike.mem_coe]

variable {I M}

/-- An inclusion of ideals reverses the inclusion of their power-torsion submodules. -/
theorem powerTorsion_antitone {J : Ideal R} (hIJ : I ≤ J) :
    powerTorsion J M ≤ powerTorsion I M := by
  intro x hx
  obtain ⟨n, hn⟩ := (mem_powerTorsion_iff J M x).mp hx
  exact (mem_powerTorsion_iff I M x).mpr
    ⟨n, fun a ha => hn a ((pow_le_pow_left' hIJ n) ha)⟩

/-- Cofinality of two sequences of ideal powers gives an inclusion of torsion submodules. -/
theorem powerTorsion_le_of_pow_le {J : Ideal R} {k : ℕ} (h : I ^ k ≤ J) :
    powerTorsion J M ≤ powerTorsion I M := by
  intro x hx
  obtain ⟨n, hn⟩ := (mem_powerTorsion_iff J M x).mp hx
  refine (mem_powerTorsion_iff I M x).mpr ⟨k * n, fun a ha => hn a ?_⟩
  exact (pow_le_pow_left' h n) (by simpa only [pow_mul] using ha)

/-- Passing to a positive power of the support ideal leaves `Γ_I(M)` unchanged. -/
theorem powerTorsion_pow (n : ℕ) (hn : n ≠ 0) :
    powerTorsion (I ^ n) M = powerTorsion I M :=
  le_antisymm (powerTorsion_le_of_pow_le le_rfl) (powerTorsion_antitone (I.pow_le_self hn))

/-- Finite generation turns containment in a radical into the power containment
needed for degree-zero local cohomology. -/
theorem powerTorsion_le_of_le_radical {J : Ideal R} (hI : I.FG)
    (h : I ≤ J.radical) : powerTorsion J M ≤ powerTorsion I M := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h hI
  exact powerTorsion_le_of_pow_le hk

/-- For finitely generated ideals, `Γ_I(M)` depends only on the radical of `I`. -/
theorem powerTorsion_eq_of_radical_eq {J : Ideal R} (hI : I.FG) (hJ : J.FG)
    (h : I.radical = J.radical) : powerTorsion I M = powerTorsion J M := by
  apply le_antisymm
  · apply powerTorsion_le_of_le_radical hJ
    exact Ideal.le_radical.trans_eq h.symm
  · apply powerTorsion_le_of_le_radical hI
    exact Ideal.le_radical.trans_eq h

/-- In particular, radical invariance holds over a noetherian ring. -/
theorem powerTorsion_eq_of_radical_eq_of_isNoetherianRing [IsNoetherianRing R]
    {J : Ideal R} (h : I.radical = J.radical) :
    powerTorsion I M = powerTorsion J M :=
  powerTorsion_eq_of_radical_eq I.fg_of_isNoetherianRing J.fg_of_isNoetherianRing h

variable (I M)

@[simp]
theorem powerTorsion_top : powerTorsion (⊤ : Ideal R) M = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨n, hn⟩ := (mem_powerTorsion_iff (⊤ : Ideal R) M x).mp hx
  simpa only [one_smul, Submodule.mem_bot] using hn 1 (by simp [← Ideal.one_eq_top])

@[simp]
theorem powerTorsion_bot : powerTorsion (⊥ : Ideal R) M = ⊤ := by
  apply top_unique
  intro x _
  refine (mem_powerTorsion_iff _ M x).mpr ⟨1, ?_⟩
  simp

variable {M} {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type z} [AddCommGroup P] [Module R P]

/-- Linear maps preserve elements annihilated by ideal powers. -/
theorem map_mem_powerTorsion (f : M →ₗ[R] N) {x : M}
    (hx : x ∈ powerTorsion I M) : f x ∈ powerTorsion I N := by
  obtain ⟨n, hn⟩ := (mem_powerTorsion_iff I M x).mp hx
  exact (mem_powerTorsion_iff I N (f x)).mpr
    ⟨n, fun a ha => by rw [← f.map_smul, hn a ha, f.map_zero]⟩

/-- The linear map on `Γ_I` induced by a linear map of modules. -/
def powerTorsionMap (f : M →ₗ[R] N) : powerTorsion I M →ₗ[R] powerTorsion I N :=
  f.restrict fun _ hx => map_mem_powerTorsion I f hx

@[simp]
theorem powerTorsionMap_apply (f : M →ₗ[R] N) (x : powerTorsion I M) :
    (powerTorsionMap I f x : N) = f x := rfl

@[simp]
theorem powerTorsionMap_id :
    powerTorsionMap I (LinearMap.id : M →ₗ[R] M) = LinearMap.id := rfl

@[simp]
theorem powerTorsionMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    powerTorsionMap I (g.comp f) = (powerTorsionMap I g).comp (powerTorsionMap I f) := rfl

/-- Restricting an injective map to `Γ_I` remains injective. -/
theorem powerTorsionMap_injective (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (powerTorsionMap I f) := by
  intro x y h
  exact Subtype.ext (hf (congrArg Subtype.val h))

/-- Injective linear maps detect, as well as preserve, ideal-power torsion. -/
theorem map_mem_powerTorsion_iff (f : M →ₗ[R] N) (hf : Function.Injective f) (x : M) :
    f x ∈ powerTorsion I N ↔ x ∈ powerTorsion I M := by
  refine ⟨fun hx => ?_, map_mem_powerTorsion I f⟩
  obtain ⟨n, hn⟩ := (mem_powerTorsion_iff I N (f x)).mp hx
  refine (mem_powerTorsion_iff I M x).mpr ⟨n, fun a ha => hf ?_⟩
  rw [f.map_smul, hn a ha, f.map_zero]

/-- The algebraic functor `Γ_I` is left exact: it preserves exactness of a
sequence whose first map is injective. -/
theorem powerTorsionMap_range_eq_ker (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range (powerTorsionMap I f) = LinearMap.ker (powerTorsionMap I g) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    change g (f x.val) = 0
    exact hfg.le ⟨x.val, rfl⟩
  · intro hy
    have hgy : g y.val = 0 := congrArg Subtype.val hy
    obtain ⟨x, hx⟩ := hfg.ge hgy
    have hxt : x ∈ powerTorsion I M :=
      (map_mem_powerTorsion_iff I f hf x).mp (hx.symm ▸ y.property)
    exact ⟨⟨x, hxt⟩, Subtype.ext hx⟩

variable (M)

/-- An element killed by `I` induces a linear map from `R/I`. -/
def quotientHomOfTorsionBySet (x : Submodule.torsionBySet R M I) : (R ⧸ I) →ₗ[R] M := by
  have hx : I ≤ (LinearMap.toSpanSingleton R M x.val).ker := by
    intro a ha
    change a • x.val = 0
    have hh := x.property
    rw [Submodule.mem_torsionBySet_iff] at hh
    exact hh ⟨a, ha⟩
  exact Submodule.liftQ (τ₁₂ := RingHom.id R) I (LinearMap.toSpanSingleton R M x.val) hx

/-- II.(7.5), at one ideal: evaluation at `1` identifies maps out of `R/I`
with elements annihilated by `I`. -/
def quotientHomEquivTorsionBySet :
    ((R ⧸ I) →ₗ[R] M) ≃ₗ[R] Submodule.torsionBySet R M I where
  toFun f := ⟨f 1, by
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    rw [← f.map_smul]
    have ha : (a : R) • (1 : R ⧸ I) = 0 := by
      change Submodule.Quotient.mk ((a : R) * 1) = 0
      simpa using (Submodule.Quotient.mk_eq_zero I).mpr a.property
    rw [ha, f.map_zero]⟩
  invFun := quotientHomOfTorsionBySet I M
  left_inv f := by
    apply LinearMap.ext
    intro q
    refine Submodule.Quotient.induction_on I q ?_
    intro a
    change a • f 1 = f (Submodule.Quotient.mk a)
    rw [← f.map_smul]
    congr 1
    change Submodule.Quotient.mk (a * 1) = Submodule.Quotient.mk a
    rw [mul_one]
  right_inv x := by
    apply Subtype.ext
    change (LinearMap.toSpanSingleton R M x.val) 1 = x.val
    simp
  map_add' f g := rfl
  map_smul' a f := rfl

@[simp]
theorem quotientHomEquivTorsionBySet_apply (f : (R ⧸ I) →ₗ[R] M) :
    (quotientHomEquivTorsionBySet I M f : M) = f 1 := rfl

/-- The canonical inclusion of the `n`-th Hom module in `Γ_I(M)`, obtained
from the evaluation isomorphism in II.(7.5). -/
def quotientHomToPowerTorsion (n : ℕ) :
    ((R ⧸ I ^ n) →ₗ[R] M) →ₗ[R] powerTorsion I M :=
  (Submodule.inclusion (le_iSup (fun k : ℕ =>
    Submodule.torsionBySet R M (I ^ k : Ideal R)) n)).comp
      (quotientHomEquivTorsionBySet (I ^ n) M).toLinearMap

@[simp]
theorem quotientHomToPowerTorsion_apply (n : ℕ) (f : (R ⧸ I ^ n) →ₗ[R] M) :
    (quotientHomToPowerTorsion I M n f : M) = f 1 := rfl

/-- Each stage of the Hom system embeds in `Γ_I(M)`. -/
theorem quotientHomToPowerTorsion_injective (n : ℕ) :
    Function.Injective (quotientHomToPowerTorsion I M n) := by
  intro f g h
  apply (quotientHomEquivTorsionBySet (I ^ n) M).injective
  apply Subtype.ext
  exact congrArg (fun z : powerTorsion I M => (z : M)) h

/-- The inclusions into `Γ_I(M)` respect the transition maps in the direct
system of II.(7.5). -/
theorem quotientHomToPowerTorsion_transition (n m : ℕ) (hnm : n ≤ m)
    (f : (R ⧸ I ^ n) →ₗ[R] M) :
    quotientHomToPowerTorsion I M m
      (f.comp ((I ^ m).mapQ (I ^ n) LinearMap.id (Ideal.pow_le_pow_right hnm))) =
        quotientHomToPowerTorsion I M n f := by
  apply Subtype.ext
  rfl

variable {M}

/-- The maps from the Hom stages into `Γ_I` are natural in the module. -/
theorem quotientHomToPowerTorsion_natural (n : ℕ) (f : M →ₗ[R] N)
    (g : (R ⧸ I ^ n) →ₗ[R] M) :
    quotientHomToPowerTorsion I N n (f.comp g) =
      powerTorsionMap I f (quotientHomToPowerTorsion I M n g) := rfl

variable (M)

/-- II.(7.5), elementwise union: every element of `Γ_I(M)` comes from a
linear map `R/I^n → M` by evaluation at `1`. -/
theorem mem_powerTorsion_iff_exists_quotientHom (x : M) :
    x ∈ powerTorsion I M ↔ ∃ (n : ℕ) (f : (R ⧸ I ^ n) →ₗ[R] M), f 1 = x := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := (mem_powerTorsion_iff I M x).mp hx
    let y : Submodule.torsionBySet R M (I ^ n : Ideal R) := ⟨x, by
      rw [Submodule.mem_torsionBySet_iff]
      exact fun a => hn a a.property⟩
    refine ⟨n, (quotientHomEquivTorsionBySet (I ^ n) M).symm y, ?_⟩
    exact congrArg Subtype.val ((quotientHomEquivTorsionBySet (I ^ n) M).apply_symm_apply y)
  · rintro ⟨n, f, rfl⟩
    exact (quotientHomToPowerTorsion I M n f).property

end SGA.SGA2.ExposeII
