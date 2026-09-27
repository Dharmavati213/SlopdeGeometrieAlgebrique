/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Tactic.Group

/-!
# SGA 1, Exposé XI, §4–§5: non-abelian `H¹` of a group

In XI.5 a finite étale group scheme over a connected pointed scheme `S` is a finite group `𝒢`
with a continuous action of `Γ = π₁(S)`, and a principal homogeneous bundle under it is a finite
`Γ`-set `𝒫` which is a principal homogeneous `𝒢`-set compatibly with `Γ`. This gives the
bijection `(*)` of XI.5 between `H¹(S, G)` and the set `H¹(Γ, 𝒢)` of cocycles modulo
cohomology. This file formalizes the group-theoretic side, for an arbitrary group `Γ`:

* `Z1`, `H1`, `H0`: cocycles, the pointed set `H¹(Γ, G)`, the invariants `H⁰(Γ, G)`;
* `IsPrincipalHomogeneous`, `classOf`: the class in `H¹(Γ, G)` of a principal homogeneous
  `G`-set with compatible `Γ`-action; two such sets are isomorphic if and only if their classes
  agree, every class comes from the twisted set `Twist φ`, and the class is trivial if and only
  if there is a `Γ`-invariant point (XI.5 `(*)`); pointed sets are classified by cocycles;
* for trivial action, cocycles are homomorphisms and `H¹` is `Hom(Γ, G)` modulo conjugation
  (XI.5, p. 300);
* `connecting`: the coboundary `H⁰(Γ, C) → H¹(Γ, A)` of a short exact sequence of `Γ`-groups,
  identified with the class of the fibre `p⁻¹(c)` (as in XI.4), and the exactness of the
  six-term sequence of pointed sets
  `1 → H⁰(A) → H⁰(B) → H⁰(C) → H¹(A) → H¹(B) → H¹(C)`,
  which is the non-commutative variant of XI.4.5 asked for in XI.4.9.

Continuity (the profinite topology on `π₁`) plays no role in these statements.
The comparison with principal coverings, through the Galois theory of Exposé V, is in
`SGA.SGA1.ExposeXI.TwistedPrincipal`.
-/

namespace SGA.SGA1.ExposeXI

open MulOpposite

section Cocycles

variable (Γ : Type*) [Group Γ] (G : Type*) [Group G] [MulDistribMulAction Γ G]

/-- XI.5: a `1`-cocycle of `Γ` with values in the `Γ`-group `G`, i.e. a map `φ : Γ → G`
with `φ (s * t) = φ s * s • φ t`. -/
@[ext]
structure Z1 where
  /-- The underlying map. -/
  toFun : Γ → G
  map_mul' : ∀ s t, toFun (s * t) = toFun s * s • toFun t

namespace Z1

variable {Γ G}

instance : CoeFun (Z1 Γ G) fun _ ↦ Γ → G := ⟨toFun⟩

theorem map_mul (φ : Z1 Γ G) (s t : Γ) : φ (s * t) = φ s * s • φ t := φ.map_mul' s t

@[simp]
theorem map_one (φ : Z1 Γ G) : φ 1 = 1 := by
  have h := φ.map_mul 1 1
  rw [mul_one, one_smul] at h
  exact mul_left_cancel (a := φ 1) (by rw [mul_one]; exact h.symm)

/-- The trivial cocycle. -/
instance : One (Z1 Γ G) := ⟨⟨fun _ ↦ 1, fun s t ↦ by simp⟩⟩

@[simp]
theorem one_apply (s : Γ) : (1 : Z1 Γ G) s = 1 := rfl

/-- Two cocycles are cohomologous if `ψ s = g⁻¹ * φ s * s • g` for some `g : G`. -/
def Cohomologous (φ ψ : Z1 Γ G) : Prop :=
  ∃ g : G, ∀ s, ψ s = g⁻¹ * φ s * s • g

theorem cohomologous_equivalence : Equivalence (@Cohomologous Γ _ G _ _) where
  refl φ := ⟨1, fun s ↦ by simp⟩
  symm := by
    rintro φ ψ ⟨g, hg⟩
    refine ⟨g⁻¹, fun s ↦ ?_⟩
    rw [hg s, smul_inv']
    group
  trans := by
    rintro φ ψ χ ⟨g, hg⟩ ⟨h, hh⟩
    refine ⟨g * h, fun s ↦ ?_⟩
    rw [hh s, hg s, smul_mul']
    group

/-- The cohomology relation on cocycles. -/
instance setoid : Setoid (Z1 Γ G) := ⟨Cohomologous, cohomologous_equivalence⟩

end Z1

/-- XI.5: the pointed set `H¹(Γ, G)` of cocycles modulo cohomology. -/
def H1 : Type _ := Quotient (Z1.setoid (Γ := Γ) (G := G))

/-- XI.4.4: the group `H⁰(Γ, G)` of invariant elements. -/
abbrev H0 : Subgroup G := FixedPoints.subgroup Γ G

namespace H1

variable {Γ G}

/-- The class of a cocycle. -/
def mk (φ : Z1 Γ G) : H1 Γ G := Quotient.mk _ φ

/-- The marked point of `H¹(Γ, G)`: the class of the trivial cocycle. -/
instance : One (H1 Γ G) := ⟨mk 1⟩

theorem mk_surjective : Function.Surjective (mk : Z1 Γ G → H1 Γ G) :=
  Quotient.mk_surjective

theorem mk_eq_mk {φ ψ : Z1 Γ G} : mk φ = mk ψ ↔ Z1.Cohomologous φ ψ :=
  Quotient.eq

/-- A cocycle has trivial class if and only if it is a coboundary. -/
theorem mk_eq_one {φ : Z1 Γ G} : mk φ = 1 ↔ ∃ g : G, ∀ s, φ s = g⁻¹ * s • g := by
  change mk φ = mk 1 ↔ _
  rw [eq_comm, mk_eq_mk]
  simp [Z1.Cohomologous]

end H1

variable {Γ G} {G' : Type*} [Group G'] [MulDistribMulAction Γ G']

/-- The cocycle `f ∘ φ` for an equivariant homomorphism `f`. -/
def Z1.map (f : G →*[Γ] G') (φ : Z1 Γ G) : Z1 Γ G' :=
  ⟨fun s ↦ f (φ s), fun s t ↦ by rw [φ.map_mul, _root_.map_mul, map_smul]⟩

@[simp]
theorem Z1.map_apply (f : G →*[Γ] G') (φ : Z1 Γ G) (s : Γ) : φ.map f s = f (φ s) := rfl

/-- XI.4.4: functoriality of `H¹` in the coefficient group. -/
def H1.map (f : G →*[Γ] G') : H1 Γ G → H1 Γ G' :=
  Quotient.map (Z1.map f) fun _ _ ⟨g, hg⟩ ↦
    ⟨f g, fun s ↦ by simp only [Z1.map_apply, hg s, map_mul, map_inv, map_smul]⟩

@[simp]
theorem H1.map_mk (f : G →*[Γ] G') (φ : Z1 Γ G) : H1.map f (H1.mk φ) = H1.mk (φ.map f) := rfl

@[simp]
theorem H1.map_one (f : G →*[Γ] G') : H1.map f 1 = 1 :=
  congrArg H1.mk (Z1.ext (funext fun _ ↦ _root_.map_one f))

/-- XI.4.4: functoriality of `H⁰` in the coefficient group. -/
def H0.map (f : G →*[Γ] G') : H0 Γ G →* H0 Γ G' :=
  ((f : G →* G').comp (H0 Γ G).subtype).codRestrict _ fun x ↦
    (FixedPoints.mem_subgroup Γ G' _).mpr fun s ↦ by
      change s • f x = f x
      rw [← map_smul, (FixedPoints.mem_subgroup Γ G x).mp x.2 s]

@[simp]
theorem H0.coe_map (f : G →*[Γ] G') (x : H0 Γ G) : (H0.map f x : G') = f x := rfl

section Trivial

variable (htriv : ∀ (s : Γ) (g : G), s • g = g)
include htriv

/-- XI.5, p. 300: for a trivial action, cocycles are homomorphisms `Γ →* G`. -/
def Z1.equivMonoidHom : Z1 Γ G ≃ (Γ →* G) where
  toFun φ := ⟨⟨φ, φ.map_one⟩, fun s t ↦ by
    change φ (s * t) = φ s * φ t
    rw [φ.map_mul, htriv]⟩
  invFun f := ⟨f, fun s t ↦ by rw [_root_.map_mul, htriv]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- XI.5, p. 300: for a trivial action, cohomologous cocycles are conjugate homomorphisms,
so `H¹(Γ, G) = Hom(Γ, G) / (inner automorphisms of G)`. -/
theorem Z1.cohomologous_iff_of_trivial {φ ψ : Z1 Γ G} :
    Z1.Cohomologous φ ψ ↔ ∃ g : G, ∀ s, ψ s = g⁻¹ * φ s * g := by
  simp [Z1.Cohomologous, htriv]

end Trivial

end Cocycles

section Torsors

variable {Γ : Type*} [Group Γ] {G : Type*} [Group G] [MulDistribMulAction Γ G]

variable (Γ G) in
/-- XI.5: a set `P` with an action of `Γ` and a right action of `G` (written `op g • x`) is a
principal homogeneous `G`-set compatible with `Γ` if `s (x g) = (s x) (s g)` and `P` is
nonempty with `G` acting simply transitively. -/
structure IsPrincipalHomogeneous (P : Type*) [MulAction Γ P] [MulAction Gᵐᵒᵖ P] : Prop where
  smul_op_smul : ∀ (s : Γ) (g : G) (x : P), s • (op g • x) = op (s • g) • s • x
  nonempty : Nonempty P
  existsUnique : ∀ x y : P, ∃! g : G, op g • x = y

theorem op_mul_smul_eq {P : Type*} [MulAction Gᵐᵒᵖ P] (g h : G) (x : P) :
    op (g * h) • x = op h • op g • x := by
  rw [op_mul, mul_smul]

namespace IsPrincipalHomogeneous

variable {P : Type*} [MulAction Γ P] [MulAction Gᵐᵒᵖ P] (hP : IsPrincipalHomogeneous Γ G P)
include hP

/-- The unique `g` with `x g = y`. -/
noncomputable def diff (x y : P) : G := (hP.existsUnique x y).choose

@[simp]
theorem op_diff_smul (x y : P) : op (hP.diff x y) • x = y := (hP.existsUnique x y).choose_spec.1

theorem diff_eq {x y : P} {g : G} (h : op g • x = y) : hP.diff x y = g :=
  ((hP.existsUnique x y).choose_spec.2 g h).symm

@[simp]
theorem diff_op_smul (x : P) (g : G) : hP.diff x (op g • x) = g := hP.diff_eq rfl

@[simp]
theorem diff_self (x : P) : hP.diff x x = 1 := hP.diff_eq (by rw [op_one, one_smul])

theorem diff_op_smul_right (x y : P) (g : G) : hP.diff x (op g • y) = hP.diff x y * g :=
  hP.diff_eq (by rw [op_mul_smul_eq, op_diff_smul])

/-- The cocycle of a point: `s • x = x · φ s`. -/
noncomputable def cocycleAt (x : P) : Z1 Γ G where
  toFun s := hP.diff x (s • x)
  map_mul' s t := hP.diff_eq (by
    rw [op_mul_smul_eq, op_diff_smul, ← hP.smul_op_smul, op_diff_smul, mul_smul])

theorem op_cocycleAt_smul (x : P) (s : Γ) : op (hP.cocycleAt x s) • x = s • x :=
  hP.op_diff_smul _ _

theorem cocycleAt_apply (x : P) (s : Γ) : hP.cocycleAt x s = hP.diff x (s • x) := rfl

theorem diff_smul (x y : P) (s : Γ) :
    hP.diff x (s • y) = hP.cocycleAt x s * s • hP.diff x y := by
  refine hP.diff_eq ?_
  rw [op_mul_smul_eq, op_cocycleAt_smul, ← hP.smul_op_smul, op_diff_smul]

/-- Changing the base point changes the cocycle by a coboundary. -/
theorem cocycleAt_op_smul (x : P) (g : G) (s : Γ) :
    hP.cocycleAt (op g • x) s = g⁻¹ * hP.cocycleAt x s * s • g := by
  refine hP.diff_eq ?_
  rw [hP.smul_op_smul, ← op_cocycleAt_smul hP x s, ← mul_smul, ← mul_smul, ← op_mul, ← op_mul]
  congr 2
  group

theorem cohomologous_cocycleAt (x y : P) :
    Z1.Cohomologous (hP.cocycleAt x) (hP.cocycleAt y) :=
  ⟨hP.diff x y, fun s ↦ by rw [← hP.cocycleAt_op_smul, op_diff_smul]⟩

/-- XI.5 `(*)`: the class in `H¹(Γ, G)` of a principal homogeneous set. -/
noncomputable def classOf : H1 Γ G := H1.mk (hP.cocycleAt hP.nonempty.some)

theorem classOf_eq (x : P) : hP.classOf = H1.mk (hP.cocycleAt x) :=
  H1.mk_eq_mk.mpr (hP.cohomologous_cocycleAt _ _)

/-- XI.4: a principal homogeneous set is trivial (has trivial class) if and only if it has a
`Γ`-invariant point, i.e. a section. -/
theorem classOf_eq_one_iff : hP.classOf = 1 ↔ ∃ x : P, ∀ s : Γ, s • x = x := by
  constructor
  · intro h
    obtain ⟨x⟩ := hP.nonempty
    obtain ⟨g, hg⟩ := H1.mk_eq_one.mp ((hP.classOf_eq x).symm.trans h)
    refine ⟨op g⁻¹ • x, fun s ↦ ?_⟩
    rw [hP.smul_op_smul, ← op_cocycleAt_smul hP x s, hg s, ← mul_smul, ← op_mul, smul_inv']
    congr 2
    group
  · rintro ⟨x, hx⟩
    rw [hP.classOf_eq x]
    exact congrArg H1.mk (Z1.ext (funext fun s ↦ hP.diff_eq (by rw [hx]; exact one_smul Gᵐᵒᵖ x)))

end IsPrincipalHomogeneous

/-- An isomorphism of sets with actions of `Γ` and right actions of `G`. -/
structure PHIso (Γ G P Q : Type*) [Group Γ] [Group G] [MulAction Γ P] [MulAction Gᵐᵒᵖ P]
    [MulAction Γ Q] [MulAction Gᵐᵒᵖ Q] extends P ≃ Q where
  map_smul' : ∀ (s : Γ) (x : P), toFun (s • x) = s • toFun x
  map_op_smul' : ∀ (g : G) (x : P), toFun (op g • x) = op g • toFun x

namespace IsPrincipalHomogeneous

variable {P Q : Type*} [MulAction Γ P] [MulAction Gᵐᵒᵖ P] [MulAction Γ Q] [MulAction Gᵐᵒᵖ Q]
  (hP : IsPrincipalHomogeneous Γ G P) (hQ : IsPrincipalHomogeneous Γ G Q)

/-- An isomorphism preserves cocycles of corresponding points. -/
theorem cocycleAt_map (e : PHIso Γ G P Q) (x : P) :
    hQ.cocycleAt (e.toFun x) = hP.cocycleAt x := by
  ext s
  refine hQ.diff_eq ?_
  rw [← e.map_op_smul', op_cocycleAt_smul, e.map_smul']

/-- XI.5 and V, end of no. 5: pointed principal homogeneous sets are classified by their
cocycles: `(P, x) ≅ (Q, y)` if and only if the cocycles of `x` and `y` agree. -/
theorem exists_phIso_iff (x : P) (y : Q) :
    (∃ e : PHIso Γ G P Q, e.toFun x = y) ↔ hP.cocycleAt x = hQ.cocycleAt y := by
  refine ⟨fun ⟨e, he⟩ ↦ he ▸ (cocycleAt_map hP hQ e x).symm, fun h ↦ ?_⟩
  refine ⟨{ toFun := fun z ↦ op (hP.diff x z) • y
            invFun := fun w ↦ op (hQ.diff y w) • x
            left_inv := fun z ↦ by simp
            right_inv := fun w ↦ by simp
            map_smul' := fun s z ↦ ?_
            map_op_smul' := fun g z ↦ ?_ }, by simp⟩
  · rw [hP.diff_smul, h, op_mul_smul_eq, op_cocycleAt_smul, hQ.smul_op_smul]
  · rw [hP.diff_op_smul_right, op_mul_smul_eq]

/-- XI.5 `(*)`, injectivity: two principal homogeneous sets are isomorphic if and only if they
have the same class in `H¹(Γ, G)`. -/
theorem classOf_eq_classOf_iff : hP.classOf = hQ.classOf ↔ Nonempty (PHIso Γ G P Q) := by
  obtain ⟨x⟩ := hP.nonempty
  obtain ⟨y⟩ := hQ.nonempty
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ ?_⟩
  · rw [hP.classOf_eq x, hQ.classOf_eq y, H1.mk_eq_mk] at h
    obtain ⟨g, hg⟩ := h
    have : hP.cocycleAt x = hQ.cocycleAt (op g⁻¹ • y) := by
      ext s
      rw [hQ.cocycleAt_op_smul, hg s, smul_inv']
      group
    exact ⟨((exists_phIso_iff hP hQ x _).mpr this).choose⟩
  · rw [hP.classOf_eq x, hQ.classOf_eq (e.toFun x), cocycleAt_map hP hQ e]

end IsPrincipalHomogeneous

/-- The twist of `G` by a cocycle `φ`: the set `G`, with `s` acting by `g ↦ φ s * s • g` and
`G` acting by right multiplication. -/
@[ext]
structure Twist (φ : Z1 Γ G) where
  /-- The underlying element of `G`. -/
  val : G

namespace Twist

variable (φ : Z1 Γ G)

instance : MulAction Γ (Twist φ) where
  smul s x := ⟨φ s * s • x.val⟩
  one_smul x := by ext; change φ 1 * (1 : Γ) • x.val = x.val; simp
  mul_smul s t x := by
    ext
    change φ (s * t) * (s * t) • x.val = φ s * s • (φ t * t • x.val)
    rw [φ.map_mul, mul_smul, smul_mul', mul_assoc]

instance : MulAction Gᵐᵒᵖ (Twist φ) where
  smul g x := ⟨x.val * g.unop⟩
  one_smul x := by ext; exact mul_one x.val
  mul_smul g h x := by
    ext
    change x.val * (h.unop * g.unop) = x.val * h.unop * g.unop
    rw [mul_assoc]

@[simp]
theorem smul_val (s : Γ) (x : Twist φ) : (s • x).val = φ s * s • x.val := rfl

@[simp]
theorem op_smul_val (g : G) (x : Twist φ) : (op g • x).val = x.val * g := rfl

/-- The twist is principal homogeneous. -/
theorem isPrincipalHomogeneous : IsPrincipalHomogeneous Γ G (Twist φ) where
  smul_op_smul s g x := by
    ext
    change φ s * s • (x.val * g) = φ s * s • x.val * s • g
    rw [smul_mul', mul_assoc]
  nonempty := ⟨⟨1⟩⟩
  existsUnique x y := ⟨x.val⁻¹ * y.val, by ext; exact mul_inv_cancel_left x.val y.val, fun g hg ↦ by
    rw [← hg, op_smul_val, inv_mul_cancel_left]⟩

/-- XI.5 `(*)`, surjectivity: the twist by `φ` has class `[φ]`. -/
theorem classOf_eq : (isPrincipalHomogeneous φ).classOf = H1.mk φ := by
  rw [(isPrincipalHomogeneous φ).classOf_eq ⟨1⟩]
  congr 1
  ext s
  refine (isPrincipalHomogeneous φ).diff_eq ?_
  ext
  simp

end Twist

end Torsors

section ExactSequence

variable {Γ : Type*} [Group Γ] {A B C : Type*} [Group A] [Group B] [Group C]
  [MulDistribMulAction Γ A] [MulDistribMulAction Γ B] [MulDistribMulAction Γ C]

/-- A short exact sequence `1 → A → B → C → 1` of groups with `Γ`-action. -/
structure IsShortExact (i : A →*[Γ] B) (p : B →*[Γ] C) : Prop where
  injective : Function.Injective i
  surjective : Function.Surjective p
  exact : ∀ b, p b = 1 ↔ ∃ a, i a = b

variable {i : A →*[Γ] B} {p : B →*[Γ] C} (h : IsShortExact i p)
include h

namespace IsShortExact

theorem mem_ker (b : B) (hb : ∀ s : Γ, s • p b = p b) (s : Γ) : ∃ a, i a = b⁻¹ * s • b :=
  (h.exact _).mp (by rw [map_mul, map_inv, map_smul, hb, inv_mul_cancel])

/-- The cocycle `s ↦ i⁻¹ (b⁻¹ * s • b)` attached to a lift `b` of an invariant element. -/
noncomputable def connectingCocycle (b : B) (hb : ∀ s : Γ, s • p b = p b) : Z1 Γ A where
  toFun s := (h.mem_ker b hb s).choose
  map_mul' s t := h.injective (by
    rw [map_mul, map_smul, (h.mem_ker b hb _).choose_spec, (h.mem_ker b hb _).choose_spec,
      (h.mem_ker b hb _).choose_spec, mul_smul, smul_mul', smul_inv']
    group)

theorem map_connectingCocycle (b : B) (hb : ∀ s : Γ, s • p b = p b) (s : Γ) :
    i (h.connectingCocycle b hb s) = b⁻¹ * s • b :=
  (h.mem_ker b hb s).choose_spec

theorem connectingCocycle_eq {b : B} (hb : ∀ s : Γ, s • p b = p b) {φ : Z1 Γ A}
    (hφ : ∀ s, i (φ s) = b⁻¹ * s • b) : h.connectingCocycle b hb = φ := by
  ext s
  exact h.injective (by rw [map_connectingCocycle, hφ])

theorem cohomologous_connectingCocycle {b b' : B} (hb : ∀ s : Γ, s • p b = p b)
    (hb' : ∀ s : Γ, s • p b' = p b') (hbb' : p b = p b') :
    Z1.Cohomologous (h.connectingCocycle b hb) (h.connectingCocycle b' hb') := by
  obtain ⟨a, ha⟩ := (h.exact (b⁻¹ * b')).mp (by rw [map_mul, map_inv, hbb', inv_mul_cancel])
  refine ⟨a, fun s ↦ h.injective ?_⟩
  rw [map_mul, map_mul, map_inv, map_smul, map_connectingCocycle, map_connectingCocycle, ha,
    smul_mul', smul_inv']
  group

/-- XI.4 (before XI.4.5): the coboundary `∂ : H⁰(Γ, C) → H¹(Γ, A)`. -/
noncomputable def connecting (c : H0 Γ C) : H1 Γ A :=
  H1.mk (h.connectingCocycle (Function.surjInv h.surjective c) (by
    rw [Function.surjInv_eq h.surjective]
    exact (FixedPoints.mem_subgroup Γ C _).mp c.2))

theorem connecting_eq (c : H0 Γ C) (b : B) (hb : p b = c) :
    h.connecting c = H1.mk (h.connectingCocycle b (by
      rw [hb]; exact (FixedPoints.mem_subgroup Γ C _).mp c.2)) :=
  H1.mk_eq_mk.mpr (h.cohomologous_connectingCocycle _ _
    (by rw [Function.surjInv_eq h.surjective, hb]))

/-- XI.4.5, exactness at `H⁰(A)`: `H⁰(A) → H⁰(B)` is injective. -/
theorem injective_H0_map : Function.Injective (H0.map i) := fun _ _ hxy ↦
  Subtype.ext (h.injective (congrArg Subtype.val hxy))

/-- XI.4.5, exactness at `H⁰(B)`. -/
theorem H0_exact_left (b : H0 Γ B) : H0.map p b = 1 ↔ ∃ a, H0.map i a = b := by
  constructor
  · intro hb
    obtain ⟨a, ha⟩ := (h.exact b).mp (congrArg Subtype.val hb)
    refine ⟨⟨a, (FixedPoints.mem_subgroup Γ A a).mpr fun s ↦ h.injective ?_⟩, Subtype.ext ha⟩
    rw [map_smul, ha]
    exact (FixedPoints.mem_subgroup Γ B _).mp b.2 s
  · rintro ⟨a, rfl⟩
    exact Subtype.ext ((h.exact (i a)).mpr ⟨a, rfl⟩)

/-- XI.4.5, exactness at `H⁰(C)`: the kernel of `∂` is the image of `H⁰(B)`. -/
theorem H0_exact_right (c : H0 Γ C) : h.connecting c = 1 ↔ ∃ b, H0.map p b = c := by
  obtain ⟨b, hb⟩ := h.surjective (c : C)
  rw [h.connecting_eq c b hb, H1.mk_eq_one]
  constructor
  · rintro ⟨a, ha⟩
    have hc : ∀ s : Γ, s • p b = p b := by
      rw [hb]; exact (FixedPoints.mem_subgroup Γ C _).mp c.2
    refine ⟨⟨b * (i a)⁻¹, (FixedPoints.mem_subgroup Γ B _).mpr fun s ↦ ?_⟩, Subtype.ext ?_⟩
    · have := h.map_connectingCocycle b hc s
      rw [ha s, map_mul, map_inv, map_smul] at this
      have key : s • b = b * ((i a)⁻¹ * s • i a) := by rw [this]; group
      rw [smul_mul', smul_inv', key]
      group
    · change p (b * (i a)⁻¹) = c
      rw [map_mul, map_inv, hb, (h.exact (i a)).mpr ⟨a, rfl⟩, inv_one, mul_one]
  · rintro ⟨b', hb'⟩
    have hbb : p b' = p b := by rw [hb]; exact congrArg Subtype.val hb'
    obtain ⟨a, ha⟩ := (h.exact ((b' : B)⁻¹ * b)).mp (by rw [map_mul, map_inv, hbb, inv_mul_cancel])
    refine ⟨a, fun s ↦ h.injective ?_⟩
    have hb's : s • (b' : B) = b' := (FixedPoints.mem_subgroup Γ B _).mp b'.2 s
    have hbeq : b = b' * i a := by rw [ha]; group
    rw [map_connectingCocycle, map_mul, map_inv, map_smul, hbeq, smul_mul', hb's]
    group


/-- XI.4.5, exactness at `H¹(A)`: the kernel of `H¹(A) → H¹(B)` is the image of `∂`. -/
theorem H1_exact_left (x : H1 Γ A) : H1.map i x = 1 ↔ ∃ c, h.connecting c = x := by
  constructor
  · intro hx
    obtain ⟨φ, rfl⟩ := H1.mk_surjective x
    rw [H1.map_mk, H1.mk_eq_one] at hx
    obtain ⟨b, hb⟩ := hx
    have hb' : ∀ s, i (φ s) = b⁻¹ * s • b := hb
    have hinv : ∀ s : Γ, s • p b = p b := fun s ↦ by
      rw [← map_smul, show s • b = b * i (φ s) by rw [hb' s]; group,
        map_mul, (h.exact _).mpr ⟨_, rfl⟩, mul_one]
    refine ⟨⟨p b, (FixedPoints.mem_subgroup Γ C _).mpr hinv⟩, ?_⟩
    rw [h.connecting_eq _ b rfl]
    exact congrArg H1.mk (h.connectingCocycle_eq _ hb')
  · rintro ⟨c, rfl⟩
    obtain ⟨b, hb⟩ := h.surjective (c : C)
    rw [h.connecting_eq c b hb, H1.map_mk, H1.mk_eq_one]
    exact ⟨b, fun s ↦ by rw [Z1.map_apply, map_connectingCocycle]⟩

/-- XI.4.5, exactness at `H¹(B)`: the kernel of `H¹(B) → H¹(C)` is the image of
`H¹(A) → H¹(B)`. -/
theorem H1_exact_right (y : H1 Γ B) : H1.map p y = 1 ↔ ∃ x, H1.map i x = y := by
  constructor
  · intro hy
    obtain ⟨ψ, rfl⟩ := H1.mk_surjective y
    rw [H1.map_mk, H1.mk_eq_one] at hy
    obtain ⟨c, hc⟩ := hy
    obtain ⟨b, rfl⟩ := h.surjective c
    have hker : ∀ s : Γ, p (b * ψ s * (s • b)⁻¹) = 1 := fun s ↦ by
      rw [map_mul, map_mul, map_inv, map_smul, ← Z1.map_apply, hc s]
      group
    choose a ha using fun s ↦ (h.exact _).mp (hker s)
    let α : Z1 Γ A := ⟨a, fun s t ↦ h.injective (by
      rw [map_mul, map_smul, ha, ha, ha, ψ.map_mul, mul_smul, smul_mul', smul_mul', smul_inv']
      group)⟩
    refine ⟨H1.mk α, ?_⟩
    rw [H1.map_mk, H1.mk_eq_mk]
    refine ⟨b, fun s ↦ ?_⟩
    rw [Z1.map_apply, show α s = a s from rfl, ha]
    group
  · rintro ⟨x, rfl⟩
    obtain ⟨φ, rfl⟩ := H1.mk_surjective x
    rw [H1.map_mk, H1.map_mk, H1.mk_eq_one]
    exact ⟨1, fun s ↦ by
      rw [Z1.map_apply, Z1.map_apply, (h.exact _).mpr ⟨_, rfl⟩, inv_one, smul_one, mul_one]⟩

/-- The fibre `p⁻¹(c)` of an element `c`, as in XI.4: for `c` invariant it is a principal
homogeneous `A`-set with compatible `Γ`-action, whose class is `∂ c`. -/
@[ext]
structure Fiber (_h : IsShortExact i p) (c : C) where
  /-- The underlying element of `B`. -/
  val : B
  prop : p val = c

variable (c : H0 Γ C)

instance : MulAction Γ (h.Fiber c) where
  smul s b := ⟨s • b.val, by
    rw [map_smul, b.prop]; exact (FixedPoints.mem_subgroup Γ C _).mp c.2 s⟩
  one_smul b := Fiber.ext (one_smul _ _)
  mul_smul s t b := Fiber.ext (mul_smul _ _ _)

instance : MulAction Aᵐᵒᵖ (h.Fiber c) where
  smul a b := ⟨b.val * i a.unop, by rw [map_mul, b.prop, (h.exact _).mpr ⟨_, rfl⟩, mul_one]⟩
  one_smul b := Fiber.ext (by change b.val * i 1 = b.val; rw [map_one, mul_one])
  mul_smul a a' b := Fiber.ext (by
    change b.val * i (a'.unop * a.unop) = b.val * i a'.unop * i a.unop
    rw [map_mul, mul_assoc])

theorem fiber_smul_val (s : Γ) (b : h.Fiber c) : (s • b).val = s • b.val := rfl

theorem fiber_op_smul_val (a : A) (b : h.Fiber c) : (op a • b).val = b.val * i a := rfl

/-- XI.4: the fibre over an invariant element is principal homogeneous under `A`. -/
theorem isPrincipalHomogeneous_fiber : IsPrincipalHomogeneous Γ A (h.Fiber c) where
  smul_op_smul s a b := Fiber.ext (by
    simp only [fiber_smul_val, fiber_op_smul_val, smul_mul', map_smul])
  nonempty := ⟨⟨_, (h.surjective c).choose_spec⟩⟩
  existsUnique x y := by
    obtain ⟨a, ha⟩ := (h.exact (x.val⁻¹ * y.val)).mp (by
      rw [map_mul, map_inv, x.prop, y.prop, inv_mul_cancel])
    refine ⟨a, Fiber.ext (by rw [fiber_op_smul_val, ha, mul_inv_cancel_left]), fun a' ha' ↦ ?_⟩
    apply h.injective
    rw [ha, ← ha', fiber_op_smul_val, inv_mul_cancel_left]

/-- XI.4: `∂ c` is the class of the fibre `p⁻¹(c)`, i.e. the inverse image of the section
`c` under `p`. -/
theorem classOf_fiber : (h.isPrincipalHomogeneous_fiber c).classOf = h.connecting c := by
  obtain ⟨b, hb⟩ := h.surjective (c : C)
  rw [(h.isPrincipalHomogeneous_fiber c).classOf_eq ⟨b, hb⟩, h.connecting_eq c b hb]
  congr 1
  refine (h.connectingCocycle_eq _ fun s ↦ ?_).symm
  have := congrArg Fiber.val
    ((h.isPrincipalHomogeneous_fiber c).op_cocycleAt_smul ⟨b, hb⟩ s)
  simp only [fiber_op_smul_val, fiber_smul_val] at this
  rw [← this, inv_mul_cancel_left]

end IsShortExact

end ExactSequence

end SGA.SGA1.ExposeXI
