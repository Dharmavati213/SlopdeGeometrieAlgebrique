/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Derivation.ToSquareZero
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Algebra.Torsor.Defs

/-!
# SGA 1, Exposé III, §5 and 6.1: the torsor of infinitesimal extensions (affine case)

Proposition III.5.1: for a closed subscheme `Y₀ ⊆ Y` defined by a square-zero ideal `J`, and an
`S`-morphism `g₀ : Y₀ → X`, the extensions of `g₀` to `Y` form a formally principal homogeneous
sheaf under `Hom(g₀* Ω¹_{X/S}, J)`; by III.5.2 it is principal homogeneous when `X` is smooth.
Proposition III.6.1: the automorphisms of a lift `X_{n+1}` inducing the identity on `X_n` form
the commutative group `𝔤 ⊗ gr^{n+1}`.

Mathlib has no sheaf of differentials on schemes, so we treat the affine case, which is the
content of SGA's proof. For `X = Spec A`, `Y = Spec B`, `Y₀ = Spec (B ⧸ J)` with `J² = 0`:

* `SqZeroIdeal J g₀` is `J` viewed as an `A`-module through `g₀ : A → B ⧸ J`;
* `Lifts J g₀` is the set of lifts of `g₀` to `A → B`; it is an `AddTorsor` under
  `Derivation R A (SqZeroIdeal J g₀)` as soon as it is nonempty (III.5.1), and it is nonempty
  when `A` is formally smooth (III.5.2);
* `Der_R(A, J) ≅ Hom_A(Ω_{A/R}, J)` and, when `Ω_{A/R}` is finite free, `≅ 𝔤_{A/R} ⊗ J`;
* III.6.1: for `J = I B` with `I` an ideal of the base, the automorphisms of `B` inducing the
  identity on `B ⧸ J` form a group isomorphic to `Der_R(B, J)` (`autReductionEquivDerivation`).
  No smoothness is needed for this.

The sheaf-theoretic statements (the sheaf `𝒫(g₀)` and its class in `H¹`) are not formalized.
-/

universe u v w

open scoped TensorProduct

namespace SGA.SGA1.ExposeIII

variable {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- The square-zero ideal `J`, as an `A`-module through `g₀ : A → B ⧸ J` (III.5.1). It is a
type synonym for `J`; the `A`-module structure is only defined when `J ^ 2 = 0`. -/
@[nolint unusedArguments]
def SqZeroIdeal (J : Ideal B) (_g₀ : A →ₐ[R] B ⧸ J) : Type w := J

namespace SqZeroIdeal

variable {J : Ideal B} {g₀ : A →ₐ[R] B ⧸ J}

instance : AddCommGroup (SqZeroIdeal J g₀) := inferInstanceAs (AddCommGroup J)
instance : Module B (SqZeroIdeal J g₀) := inferInstanceAs (Module B J)
instance : Module R (SqZeroIdeal J g₀) := inferInstanceAs (Module R J)
instance : IsScalarTower R B (SqZeroIdeal J g₀) := inferInstanceAs (IsScalarTower R B J)

/-- `SqZeroIdeal J g₀` is `J`. -/
def equiv : SqZeroIdeal J g₀ ≃ J := Equiv.refl _

/-- The element of `B` underlying an element of `SqZeroIdeal J g₀`. -/
def val (x : SqZeroIdeal J g₀) : B := (equiv x).1

lemma val_mem (x : SqZeroIdeal J g₀) : x.val ∈ J := (equiv x).2

/-- An element of `J`, as an element of `SqZeroIdeal J g₀`. -/
def mk (x : B) (hx : x ∈ J) : SqZeroIdeal J g₀ := equiv.symm ⟨x, hx⟩

@[simp] lemma val_mk (x : B) (hx : x ∈ J) : (mk x hx : SqZeroIdeal J g₀).val = x := rfl

@[ext] lemma ext {x y : SqZeroIdeal J g₀} (h : x.val = y.val) : x = y :=
  equiv.injective (Subtype.ext h)

@[simp] lemma val_add (x y : SqZeroIdeal J g₀) : (x + y).val = x.val + y.val := rfl
@[simp] lemma val_zero : (0 : SqZeroIdeal J g₀).val = 0 := rfl
@[simp] lemma val_neg (x : SqZeroIdeal J g₀) : (-x).val = -x.val := rfl
@[simp] lemma val_sub (x y : SqZeroIdeal J g₀) : (x - y).val = x.val - y.val := rfl
@[simp] lemma val_smul_B (b : B) (x : SqZeroIdeal J g₀) : (b • x).val = b * x.val := rfl
@[simp] lemma val_smul_R (r : R) (x : SqZeroIdeal J g₀) : (r • x).val = r • x.val := rfl

variable [hJ : Fact (J ^ 2 = ⊥)]

lemma mul_eq_zero {x y : B} (hx : x ∈ J) (hy : y ∈ J) : x * y = 0 := by
  have := Ideal.mul_mem_mul hx hy
  rwa [← pow_two, hJ.out, Ideal.mem_bot] at this

lemma isTorsionBySet : Module.IsTorsionBySet B (SqZeroIdeal J g₀) J :=
  fun x a ↦ ext (mul_eq_zero a.2 x.val_mem)

/-- A square-zero ideal `J` is a module over `B ⧸ J`. -/
instance quotModule : Module (B ⧸ J) (SqZeroIdeal J g₀) := isTorsionBySet.module

instance : Module A (SqZeroIdeal J g₀) := Module.compHom _ g₀.toRingHom

lemma smul_eq (a : A) (b : B) (hb : Ideal.Quotient.mk J b = g₀ a) (x : SqZeroIdeal J g₀) :
    a • x = b • x := by
  change g₀ a • x = b • x
  rw [← hb]
  rfl

lemma val_smul (a : A) (b : B) (hb : Ideal.Quotient.mk J b = g₀ a) (x : SqZeroIdeal J g₀) :
    (a • x).val = b * x.val := by
  rw [smul_eq a b hb]; rfl

instance : IsScalarTower R A (SqZeroIdeal J g₀) where
  smul_assoc r a x := by
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (g₀ a)
    have hb' : Ideal.Quotient.mk J (r • b) = g₀ (r • a) := by
      rw [Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap, hb, map_smul, Algebra.smul_def]
    rw [smul_eq (r • a) (r • b) hb', smul_eq a b hb, smul_assoc]

end SqZeroIdeal

/-- III.5.1 (affine case): the lifts of `g₀ : A → B ⧸ J` to `A → B`, i.e. the sections of the
sheaf `𝒫(g₀)` of SGA over `Spec B`. -/
def Lifts (J : Ideal B) (g₀ : A →ₐ[R] B ⧸ J) : Type _ :=
  {g : A →ₐ[R] B // (Ideal.Quotient.mkₐ R J).comp g = g₀}

namespace Lifts

variable {J : Ideal B} {g₀ : A →ₐ[R] B ⧸ J}

instance : CoeFun (Lifts J g₀) (fun _ ↦ A → B) := ⟨fun g ↦ g.1⟩

@[ext] lemma ext {g g' : Lifts J g₀} (h : ∀ x, g x = g' x) : g = g' :=
  Subtype.ext (AlgHom.ext h)

lemma mk_apply (g : Lifts J g₀) (x : A) : Ideal.Quotient.mk J (g x) = g₀ x :=
  congr($(g.2) x)

lemma sub_mem (g g' : Lifts J g₀) (x : A) : g x - g' x ∈ J := by
  rw [← Ideal.Quotient.eq, mk_apply, mk_apply]

variable [Fact (J ^ 2 = ⊥)]

/-- Adding a derivation to a lift. -/
def vaddAlgHom (d : Derivation R A (SqZeroIdeal J g₀)) (g : Lifts J g₀) : A →ₐ[R] B where
  toFun x := g x + (d x).val
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, Derivation.leibniz, SqZeroIdeal.val_add,
      SqZeroIdeal.val_smul x (g x) (mk_apply g x), SqZeroIdeal.val_smul y (g y) (mk_apply g y)]
    have := SqZeroIdeal.mul_eq_zero (d x).val_mem (d y).val_mem
    linear_combination -this
  map_zero' := by simp
  map_add' x y := by simp only [map_add, SqZeroIdeal.val_add]; ring
  commutes' r := by simp

instance : VAdd (Derivation R A (SqZeroIdeal J g₀)) (Lifts J g₀) where
  vadd d g := ⟨vaddAlgHom d g, AlgHom.ext fun x ↦ by
    change Ideal.Quotient.mk J (g x + (d x).val) = g₀ x
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (d x).val_mem, add_zero, mk_apply]⟩

lemma vadd_apply (d : Derivation R A (SqZeroIdeal J g₀)) (g : Lifts J g₀) (x : A) :
    (d +ᵥ g) x = g x + (d x).val := rfl

/-- The difference of two lifts is a derivation. -/
def vsubDerivation (g g' : Lifts J g₀) : Derivation R A (SqZeroIdeal J g₀) where
  toFun x := SqZeroIdeal.mk (g x - g' x) (sub_mem g g' x)
  map_add' x y := by ext; simp only [map_add, SqZeroIdeal.val_mk, SqZeroIdeal.val_add]; ring
  map_smul' r x := by ext; simp [smul_sub]
  map_one_eq_zero' := by ext; simp
  leibniz' x y := by
    ext
    change g (x * y) - g' (x * y) =
      (x • SqZeroIdeal.mk (g₀ := g₀) (g y - g' y) (sub_mem g g' y)).val +
      (y • SqZeroIdeal.mk (g₀ := g₀) (g x - g' x) (sub_mem g g' x)).val
    rw [SqZeroIdeal.val_smul x (g x) (mk_apply g x), SqZeroIdeal.val_smul y (g' y) (mk_apply g' y),
      SqZeroIdeal.val_mk, SqZeroIdeal.val_mk, map_mul, map_mul]
    ring

instance : VSub (Derivation R A (SqZeroIdeal J g₀)) (Lifts J g₀) where
  vsub := vsubDerivation

lemma vsub_apply (g g' : Lifts J g₀) (x : A) : ((g -ᵥ g') x).val = g x - g' x := rfl

instance : AddAction (Derivation R A (SqZeroIdeal J g₀)) (Lifts J g₀) where
  zero_vadd g := ext fun x ↦ by simp [vadd_apply]
  add_vadd d d' g := by
    ext x
    simp only [vadd_apply, Derivation.add_apply, SqZeroIdeal.val_add]
    ring

/-- III.5.1 (affine case): the lifts of `g₀` through a square-zero ideal form a formally
principal homogeneous space under `Der_R(A, J)`: a principal homogeneous space as soon as it is
nonempty. -/
instance [Nonempty (Lifts J g₀)] : AddTorsor (Derivation R A (SqZeroIdeal J g₀)) (Lifts J g₀) where
  vsub_vadd' g g' := ext fun x ↦ by simp [vadd_apply, vsub_apply]
  vadd_vsub' d g := by ext x; simp [vadd_apply, vsub_apply]

/-- III.5.1 (affine case), the bijection `(*)` of SGA: once a lift `g` of `g₀` is fixed,
`d ↦ g + d` is a bijection from `Der_R(A, J)` onto the set of lifts of `g₀`. -/
def equivDerivation (g : Lifts J g₀) : Derivation R A (SqZeroIdeal J g₀) ≃ Lifts J g₀ :=
  have : Nonempty (Lifts J g₀) := ⟨g⟩
  Equiv.vaddConst g

@[simp] lemma equivDerivation_apply (g : Lifts J g₀) (d : Derivation R A (SqZeroIdeal J g₀)) :
    equivDerivation g d = d +ᵥ g := rfl

/-- III.5.2 (affine case): if `A` is formally smooth over `R`, lifts exist, so the lifts of `g₀`
form a principal homogeneous space (and not only a formally principal homogeneous one). -/
instance nonempty_of_formallySmooth [Algebra.FormallySmooth R A] : Nonempty (Lifts J g₀) := by
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift J ⟨2, Fact.out⟩ g₀
  exact ⟨⟨g, hg⟩⟩

end Lifts

variable (R A) in
/-- III.5.1: the structure group of the torsor of lifts is
`Hom_A(Ω_{A/R}, J) = Hom(g₀* Ω¹_{X/S}, J)`, identified with `Der_R(A, J)`. -/
noncomputable def homKaehlerEquivDerivation (M : Type*) [AddCommGroup M] [Module A M] [Module R M]
    [IsScalarTower R A M] : (Ω[A⁄R] →ₗ[A] M) ≃ₗ[A] Derivation R A M :=
  KaehlerDifferential.linearMapEquivDerivation R A

variable (R A) in
/-- III.5.2: when `Ω_{A/R}` is free of finite type (e.g. `A` smooth and `Ω_{A/R}` trivial), the
structure group is `𝔤_{A/R} ⊗ J`, where `𝔤_{A/R}` is the dual of `Ω_{A/R}` (the tangent
module). -/
noncomputable def tangentTensorEquivDerivation (M : Type*) [AddCommGroup M] [Module A M]
    [Module R M] [IsScalarTower R A M] [Module.Free A Ω[A⁄R]] [Module.Finite A Ω[A⁄R]] :
    (Module.Dual A Ω[A⁄R] ⊗[A] M) ≃ₗ[A] Derivation R A M :=
  dualTensorHomEquiv A Ω[A⁄R] M ≪≫ₗ homKaehlerEquivDerivation R A M

section Automorphisms

variable (I : Ideal R)

/-- The automorphisms of the `R`-algebra `B` inducing the identity on `B ⧸ I B`. -/
def autReduction : Subgroup (B ≃ₐ[R] B) where
  carrier := {σ | ∀ x, σ x - x ∈ I.map (algebraMap R B)}
  mul_mem' {σ τ} hσ hτ x := by
    rw [AlgEquiv.mul_apply, show σ (τ x) - x = (σ (τ x) - τ x) + (τ x - x) by ring]
    exact add_mem (hσ _) (hτ x)
  one_mem' x := by simp
  inv_mem' {σ} hσ x := by
    have := hσ (σ⁻¹ x)
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at this
    rw [← neg_sub]
    exact neg_mem this

variable {I}

lemma mem_autReduction {σ : B ≃ₐ[R] B} :
    σ ∈ autReduction I ↔ ∀ x, σ x - x ∈ I.map (algebraMap R B) := Iff.rfl

variable (hI : I.map (algebraMap R B) ^ 2 = ⊥)
include hI

/-- A derivation into `J = I B` vanishes on `J` when `J ^ 2 = 0`. -/
lemma derivation_apply_eq_zero (d : Derivation R B (I.map (algebraMap R B))) {x : B}
    (hx : x ∈ I.map (algebraMap R B)) : d x = 0 := by
  have hmul {a b : B} (ha : a ∈ I.map (algebraMap R B)) (hb : b ∈ I.map (algebraMap R B)) :
      a * b = 0 := by
    have := Ideal.mul_mem_mul ha hb
    rwa [← pow_two, hI, Ideal.mem_bot] at this
  rw [Ideal.map, Ideal.span, Submodule.mem_span_set'] at hx
  obtain ⟨n, c, y, rfl⟩ := hx
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  obtain ⟨r, hr, hry⟩ := (y i).2
  rw [smul_eq_mul, Derivation.leibniz, ← hry, Derivation.map_algebraMap, smul_zero, zero_add]
  ext1
  exact hmul (Ideal.mem_map_of_mem _ hr) (d (c i)).2

lemma derivation_apply_coe_eq_zero (d : Derivation R B (I.map (algebraMap R B)))
    (y : I.map (algebraMap R B)) : d y = 0 :=
  derivation_apply_eq_zero hI d y.2

/-- III.6.1 (affine case): the automorphisms of `B` over `R` inducing the identity modulo a
square-zero ideal `J = I B` coming from the base form a group isomorphic to the additive group
`Der_R(B, J)`; in particular it is commutative. -/
noncomputable def autReductionEquivDerivation :
    autReduction (B := B) I ≃* Multiplicative (Derivation R B (I.map (algebraMap R B))) where
  toFun σ := Multiplicative.ofAdd (derivationToSquareZeroOfLift _ hI σ.1.toAlgHom
    (AlgHom.ext fun x ↦ by
      change Ideal.Quotient.mk _ (σ.1 x) = Ideal.Quotient.mk _ x
      rw [Ideal.Quotient.eq]; exact σ.2 x))
  invFun d := ⟨AlgEquiv.ofAlgHom (liftOfDerivationToSquareZero _ hI d.toAdd)
      (liftOfDerivationToSquareZero _ hI (-d.toAdd))
      (AlgHom.ext fun x ↦ by
        simp [liftOfDerivationToSquareZero_apply, derivation_apply_coe_eq_zero hI])
      (AlgHom.ext fun x ↦ by
        simp [liftOfDerivationToSquareZero_apply, derivation_apply_coe_eq_zero hI]),
    fun x ↦ by simp [liftOfDerivationToSquareZero_apply]⟩
  left_inv σ := by
    ext x
    simp [liftOfDerivationToSquareZero_apply, derivationToSquareZeroOfLift_apply]
  right_inv d := by
    ext x
    simp [liftOfDerivationToSquareZero_apply, derivationToSquareZeroOfLift_apply]
  map_mul' σ τ := by
    rw [← ofAdd_add]
    congr 1
    ext x
    simp only [Subgroup.coe_mul, derivationToSquareZeroOfLift_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.mul_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Derivation.add_apply, Submodule.coe_add]
    have h := derivation_apply_eq_zero hI (derivationToSquareZeroOfLift _ hI σ.1.toAlgHom
      (AlgHom.ext fun x ↦ by
        change Ideal.Quotient.mk _ (σ.1 x) = Ideal.Quotient.mk _ x
        rw [Ideal.Quotient.eq]; exact σ.2 x)) (τ.2 x)
    rw [Subtype.ext_iff, derivationToSquareZeroOfLift_apply] at h
    simp only [AlgEquiv.coe_toAlgHom, map_sub, Algebra.algebraMap_self,
      RingHom.id_apply, ZeroMemClass.coe_zero] at h
    linear_combination h

end Automorphisms

end SGA.SGA1.ExposeIII
