/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Invariant.Basic
import SGA.SGA1.ExposeV.FiniteQuotientBaseChange

/-!
# SGA 1, Exposé V, §2: decomposition and inertia groups

We work in the affine situation of V.1.1: a finite group `G` acting on a ring `A`, with
`B = A^G`. A point `x` of `Spec A` is a prime `Q`; its decomposition group `G_d(x)` is the
stabilizer `MulAction.stabilizer G Q`, and its inertia group `G_i(x)` is mathlib's
`Q.inertia G = {g | ∀ a, g • a - a ∈ Q}`, the elements of `G_d(x)` acting trivially on the
residue ring (`map_ker_stabilizerHom`). By V.1.1 (iii) (mathlib), `G_d(x)/G_i(x)` is the Galois
group of `κ(x)/κ(y)`.

* Geometric points: `X(Ω) → Y(Ω)` is surjective for `Ω` algebraically closed, its fibres are
  the `G`-orbits, and the stabilizer of `a : A → Ω` is the inertia group of its locality.
* V.2.1: inertia groups do not change under base change (`inertia_tensorProduct`).
* V.2.2 is stated here (`DecompositionInertiaEtaleStatement`) and proved in `InertiaEtale.lean`
  (`decompositionInertiaEtaleStatement`).

Decomposition and inertia groups of points of arbitrary schemes, and the scheme versions of
V.1.3 (iii), V.2.3, V.2.4 and V.3.2, are in `InertiaGroups.lean`.
-/

open TensorProduct
open scoped Pointwise

namespace SGA.SGA1.ExposeV

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A] (G : Type*) [Group G]
  [MulSemiringAction G A]

section Definitions

/-- V.2: the inertia group of `Q` is the kernel of the action of the decomposition group
`G_d(Q) = stabilizer G Q` on the residue ring `A ⧸ Q` (mathlib). -/
theorem map_ker_stabilizerHom [SMulCommClass G B A] (P : Ideal B) (Q : Ideal A) [Q.LiesOver P] :
    (Ideal.Quotient.stabilizerHom Q P G).ker.map (MulAction.stabilizer G Q).subtype =
      Q.inertia G :=
  Ideal.Quotient.map_ker_stabilizer_subtype Q P G

/-- V.2: `G_i(Q) ⊆ G_d(Q)`. -/
theorem inertia_le_stabilizer (Q : Ideal A) : Q.inertia G ≤ MulAction.stabilizer G Q :=
  Ideal.inertia_le_stabilizer Q

/-- V.2 (mathlib, V.1.1 (iii)): `G_d(x)/G_i(x)` is the group of automorphisms of the residue
field extension `κ(x)/κ(y)`; here `K`, `L` are the fraction fields of `B/P` and `A/Q`. -/
noncomputable alias decompositionQuotientInertiaEquiv :=
  IsFractionRing.stabilizerQuotientInertiaEquiv

/-- V.2: the stabilizer of a geometric point `a : A → Ω` (for the action `a ↦ a ∘ g`) is the
inertia group of the point `ker a` of `Spec A` at which it is located. -/
theorem comp_toRingHom_eq_iff_mem_inertia {Ω : Type*} [CommRing Ω] (a : A →+* Ω) (g : G) :
    a.comp (MulSemiringAction.toRingHom G A g) = a ↔ g ∈ (RingHom.ker a).inertia G := by
  simp only [RingHom.ext_iff, RingHom.comp_apply, MulSemiringAction.toRingHom_apply,
    AddSubgroup.mem_inertia, Submodule.mem_toAddSubgroup, RingHom.mem_ker, map_sub, sub_eq_zero]

end Definitions

section GeometricPoints

variable {Ω : Type*} [Field Ω] [Finite G] [SMulCommClass G B A] [Algebra.IsInvariant B A G]

omit [SMulCommClass G B A] in
include G in
/-- V.2, geometric points: for `Ω` algebraically closed, every `Ω`-point of `Y = Spec A^G`
lifts to `X = Spec A`, i.e. `X(Ω) → Y(Ω)` is surjective. -/
theorem exists_comp_algebraMap_eq_of_isAlgClosed [IsAlgClosed Ω]
    (hinj : Function.Injective (algebraMap B A)) (φ : B →+* Ω) :
    ∃ a : A →+* Ω, a.comp (algebraMap B A) = φ := by
  have := Algebra.IsInvariant.isIntegral B A G
  let P := RingHom.ker φ
  have : P.IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal A)
    (by rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have : Q.LiesOver P := ⟨hQP.symm⟩
  let φ' : B ⧸ P →+* Ω := Ideal.Quotient.lift P φ fun _ h ↦ h
  let _ : Algebra (B ⧸ P) Ω := φ'.toAlgebra
  have hφ' : Function.Injective φ' := RingHom.lift_injective_of_ker_le_ideal P _ le_rfl
  have : Module.IsTorsionFree (B ⧸ P) Ω := Module.isTorsionFree_iff_algebraMap_injective.mpr hφ'
  have : Module.IsTorsionFree (B ⧸ P) (A ⧸ Q) := inferInstance
  have : Algebra.IsIntegral (B ⧸ P) (A ⧸ Q) := inferInstance
  have : Algebra.IsAlgebraic (B ⧸ P) (A ⧸ Q) := inferInstance
  let l := IsAlgClosed.lift (R := B ⧸ P) (S := A ⧸ Q) (M := Ω)
  refine ⟨l.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun b ↦ ?_⟩
  change l (Ideal.Quotient.mk Q (algebraMap B A b)) = φ b
  rw [← Ideal.Quotient.algebraMap_mk_of_liesOver (p := P) (P := Q), AlgHom.commutes]
  rfl

/-- V.2, geometric points: two `Ω`-points of `X` with the same image in `Y` are conjugate
under `G`, so that `Y(Ω) = X(Ω)/G` (for any field `Ω`; SGA takes `Ω` algebraically closed).
The stabilizer of a point is the inertia group of its locality
(`comp_toRingHom_eq_iff_mem_inertia`). -/
theorem exists_comp_toRingHom_eq_of_comp_algebraMap_eq (a₁ a₂ : A →+* Ω)
    (h : a₁.comp (algebraMap B A) = a₂.comp (algebraMap B A)) :
    ∃ g : G, a₁.comp (MulSemiringAction.toRingHom G A g) = a₂ := by
  let P := RingHom.ker (a₂.comp (algebraMap B A))
  have : P.IsPrime := RingHom.ker_isPrime _
  let Q := RingHom.ker a₂
  have : Q.IsPrime := RingHom.ker_isPrime _
  have : (RingHom.ker a₁).IsPrime := RingHom.ker_isPrime _
  have hQ₁ : (RingHom.ker a₁).under B = Q.under B := by
    ext c
    change a₁ (algebraMap B A c) = 0 ↔ a₂ (algebraMap B A c) = 0
    rw [show a₁ (algebraMap B A c) = a₂ (algebraMap B A c) from congr($h c)]
  obtain ⟨g₀, hg₀⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B A G Q (RingHom.ker a₁)
    (by rw [hQ₁])
  -- `b = a₁ ∘ g₀` has kernel `Q`
  let b := a₁.comp (MulSemiringAction.toRingHom G A g₀)
  have hb : RingHom.ker b = Q := by
    ext x
    simp only [b, RingHom.mem_ker, RingHom.comp_apply, MulSemiringAction.toRingHom_apply]
    rw [← RingHom.mem_ker, hg₀, Ideal.smul_mem_pointwise_smul_iff, RingHom.mem_ker]
  have hbB : b.comp (algebraMap B A) = a₂.comp (algebraMap B A) := by
    rw [← h]; ext; simp [b]
  have : Q.LiesOver P := ⟨by ext; simp [P, Q, Ideal.under, RingHom.mem_ker]⟩
  let K := FractionRing (B ⧸ P)
  let L := FractionRing (A ⧸ Q)
  let _ := FractionRing.liftAlgebra (B ⧸ P) L
  let φ₀ : B ⧸ P →+* Ω := Ideal.Quotient.lift P (a₂.comp (algebraMap B A)) fun _ h ↦ h
  have hφ₀ : Function.Injective φ₀ := RingHom.lift_injective_of_ker_le_ideal P _ le_rfl
  let b₀ : A ⧸ Q →+* Ω := Ideal.Quotient.lift Q b fun x hx ↦ by rwa [← hb] at hx
  have hb₀ : Function.Injective b₀ := RingHom.lift_injective_of_ker_le_ideal Q _ hb.le
  let a₀ : A ⧸ Q →+* Ω := Ideal.Quotient.lift Q a₂ fun _ h ↦ h
  have ha₀ : Function.Injective a₀ := RingHom.lift_injective_of_ker_le_ideal Q _ le_rfl
  let ιb : L →+* Ω := IsFractionRing.lift hb₀
  let ι₂ : L →+* Ω := IsFractionRing.lift ha₀
  let _ : Algebra K Ω := (IsFractionRing.lift hφ₀).toAlgebra
  have hcomm : ∀ ι : L →+* Ω, (ι.comp (algebraMap (A ⧸ Q) L)).comp
      (algebraMap (B ⧸ P) (A ⧸ Q)) = φ₀ → ∀ k : K, ι (algebraMap K L k) = algebraMap K Ω k := by
    intro ι hι k
    have := IsLocalization.ringHom_ext (nonZeroDivisors (B ⧸ P))
      (j := ι.comp (algebraMap K L)) (k := algebraMap K Ω) (by
        rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq,
          IsScalarTower.algebraMap_eq (B ⧸ P) (A ⧸ Q) L, ← RingHom.comp_assoc, hι]
        exact (RingHom.ext fun c ↦ IsFractionRing.lift_algebraMap hφ₀ c).symm)
    exact congr($this k)
  have hι₂ : (ι₂.comp (algebraMap (A ⧸ Q) L)).comp (algebraMap (B ⧸ P) (A ⧸ Q)) = φ₀ := by
    ext c
    change ι₂ (algebraMap (A ⧸ Q) L (algebraMap (B ⧸ P) (A ⧸ Q) (Ideal.Quotient.mk P c))) =
      φ₀ (Ideal.Quotient.mk P c)
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hιb : (ιb.comp (algebraMap (A ⧸ Q) L)).comp (algebraMap (B ⧸ P) (A ⧸ Q)) = φ₀ := by
    ext c
    change ιb (algebraMap (A ⧸ Q) L (algebraMap (B ⧸ P) (A ⧸ Q) (Ideal.Quotient.mk P c))) =
      φ₀ (Ideal.Quotient.mk P c)
    rw [IsFractionRing.lift_algebraMap]
    exact congr($hbB c)
  let ι₂' : L →ₐ[K] Ω := { ι₂ with commutes' := hcomm ι₂ hι₂ }
  let _ : Algebra L Ω := ιb.toAlgebra
  have : IsScalarTower K L Ω := .of_algebraMap_eq fun k ↦ (hcomm ιb hιb k).symm
  have : Normal K L := Ideal.IsFractionRing.normal G P Q K L
  let τ := ι₂'.restrictNormal' L
  obtain ⟨σ, hσ⟩ := IsFractionRing.stabilizerHom_surjective G P Q K L τ
  refine ⟨g₀ * σ, RingHom.ext fun x ↦ ?_⟩
  have h1 : ιb (τ (algebraMap (A ⧸ Q) L (Ideal.Quotient.mk Q x))) =
      ι₂ (algebraMap (A ⧸ Q) L (Ideal.Quotient.mk Q x)) :=
    AlgHom.restrictNormal_commutes ι₂' L _
  rw [← hσ, IsFractionRing.stabilizerHom_apply_apply_mk] at h1
  simp only [ιb, ι₂, IsFractionRing.lift_algebraMap] at h1
  have h2 : b (σ.1 • x) = a₂ x := h1
  simpa [b, mul_smul] using h2

end GeometricPoints

section BaseChange

variable (B') [CommRing B'] [Algebra B B'] [SMulCommClass G B A]

/-- V.2.1: inertia groups are invariant under change of base. If `Q'` is a prime (or any ideal)
of `A' = B' ⊗_B A`, and `Q` is its inverse image in `A`, then `G_i(Q') = G_i(Q)`. -/
theorem inertia_tensorProduct (Q' : Ideal (B' ⊗[B] A)) :
    letI := tensorAction (B := B) (A := A) B' G
    Q'.inertia G =
      (Q'.comap (Algebra.TensorProduct.includeRight : A →ₐ[B] B' ⊗[B] A)).inertia G := by
  let _ := tensorAction (B := B) (A := A) B' G
  have hsmul : ∀ (g : G) (b : B') (a : A), g • (b ⊗ₜ[B] a) = b ⊗ₜ (g • a) :=
    fun g b a ↦ tensorAction_tmul B' G g b a
  ext g
  simp only [AddSubgroup.mem_inertia, Submodule.mem_toAddSubgroup, Ideal.mem_comap,
    Algebra.TensorProduct.includeRight_apply]
  constructor
  · intro h a
    have := h (1 ⊗ₜ a)
    rwa [hsmul, ← tmul_sub] at this
  · intro h x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b a =>
      rw [hsmul, ← tmul_sub, show b ⊗ₜ[B] (g • a - a) = (b ⊗ₜ 1) * (1 ⊗ₜ (g • a - a)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
      exact Q'.mul_mem_left _ (h a)
    | add x y hx hy =>
      rw [smul_add, add_sub_add_comm]
      exact Q'.add_mem hx hy

end BaseChange

section Statement

/-- V.2.2 (proved as `decompositionInertiaEtaleStatement` in `InertiaEtale.lean`): let `B` be
noetherian, `A` finite over `B = A^G`, `H ≤ G`, `Q` a prime of `A`, `Q' = Q ∩ A^H` and
`P = Q ∩ B`.
(i) If `G_d(Q) ⊆ H`, then `B_P → (A^H)_{Q'}` induces an isomorphism on completions; we state the
equivalent condition (EGA IV 17.6.3) that `A^H` is étale over `B` at `Q'` with `κ(Q') = κ(P)`.
(ii) If `G_i(Q) ⊆ H`, then `A^H` is étale over `B` at `Q'`.
The case `H = 1` of (ii) with all inertia trivial is also `PrincipalCovering.lean`. -/
def DecompositionInertiaEtaleStatement : Prop :=
  ∀ (B A G : Type) [CommRing B] [CommRing A] [Algebra B A] [Group G] [Finite G]
    [MulSemiringAction G A] [SMulCommClass G B A] [IsNoetherianRing B] [Module.Finite B A]
    [Algebra.IsInvariant B A G], Function.Injective (algebraMap B A) →
    ∀ (H : Subgroup G) (Q : Ideal A) [Q.IsPrime],
      let Q' := Q.comap (FixedPoints.subalgebra B A H).val
      (MulAction.stabilizer G Q ≤ H →
        ∃ _ : Q'.IsPrime, Algebra.IsEtaleAt B Q' ∧
          Function.Bijective (Ideal.ResidueField.map (Q.comap (algebraMap B A)) Q'
            (algebraMap B (FixedPoints.subalgebra B A H)) rfl)) ∧
      (Q.inertia G ≤ H → ∃ _ : Q'.IsPrime, Algebra.IsEtaleAt B Q')

end Statement

end SGA.SGA1.ExposeV
