/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# The order of the inertia group

Let `S/R` be a finite flat extension of domains with Galois group `G` (`IsGaloisGroup G R S`),
`p` a prime of `R` and `P` a prime of `S` over `p`. Mathlib proves that the inertia group
`I_P = P.inertia G` has order the ramification index `e` when the residue field `κ(p)` is
perfect (`Ideal.card_inertia_eq_ramificationIdxIn`). In general the residue extension
`κ(P)/κ(p)` is normal but possibly inseparable, and (Serre, *Local fields*, I §7, Prop. 21, with
the remark of SGA 1 XIII 2.0 for inseparable residue extensions):

* `Ideal.card_stabilizer_eq_card_inertia_mul_finSepDegree`: `|D_P| = |I_P| [κ(P) : κ(p)]_s`;
* `Ideal.card_inertia_eq_ramificationIdx_mul_finInsepDegree`: `|I_P| = e [κ(P) : κ(p)]_i`;
* `Ideal.card_inertia_natCast_ne_zero_iff`: `|I_P|` is prime to the residue characteristic if and
  only if `e` is and `κ(P)/κ(p)` is separable (tame ramification);
* `Algebra.isUnramifiedAt_of_ramificationIdx_eq_one`: a prime with ramification index `1` and
  separable residue extension is unramified (Serre, *Local fields*, I §4 and III §5).
-/

open Algebra Module
open scoped Pointwise

/-- The inseparable degree of a finite extension `E/F` is nonzero in `F` (that is, prime to the
characteristic) if and only if `E/F` is separable. -/
theorem Field.natCast_finInsepDegree_ne_zero_iff (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    (Field.finInsepDegree F E : F) ≠ 0 ↔ Algebra.IsSeparable F E := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [Algebra.IsSeparable.finInsepDegree_eq]⟩
  obtain ⟨q, hq⟩ : ∃ q, ExpChar F q := ⟨ringExpChar F, inferInstance⟩
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow F E q
  cases hq with
  | zero => exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  | prime hprime =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [pow_zero] at hn
      exact (isSeparable_iff_finInsepDegree_eq_one F E).mpr hn
    · rw [hn, Nat.cast_pow, CharP.cast_eq_zero, zero_pow hpos.ne'] at h
      exact absurd rfl h

namespace Ideal

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

/-- The number of automorphisms of a finite normal extension is its separable degree. -/
theorem _root_.Normal.nat_card_algEquiv_eq_finSepDegree (F E : Type*) [Field F] [Field E]
    [Algebra F E] [Normal F E] : Nat.card Gal(E/F) = Field.finSepDegree F E :=
  (Nat.card_congr (Normal.algHomEquivAut F (AlgebraicClosure E) E)).symm

/-- The order of the decomposition group is the order of the inertia group times the separable
degree of the residue extension. -/
theorem card_stabilizer_eq_card_inertia_mul_finSepDegree (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    Nat.card (MulAction.stabilizer G P) =
      Nat.card (inertia G P) * Field.finSepDegree p.ResidueField P.ResidueField := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have heq : (algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P)) =
      (algebraMap p.ResidueField P.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  let := ((algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
  have : IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField := .of_algebraMap_eq' rfl
  have : IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField := .of_algebraMap_eq' heq
  have : Normal p.ResidueField P.ResidueField :=
    Ideal.IsFractionRing.normal G p P p.ResidueField P.ResidueField
  have : Subgroup.index _ = _ := Nat.card_congr
    (IsFractionRing.stabilizerQuotientInertiaEquiv G p P p.ResidueField P.ResidueField).toEquiv
  rw [← Normal.nat_card_algEquiv_eq_finSepDegree, ← this,
    ← ((inertia G P).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inertia_le_stabilizer (M := G) P)).toEquiv,
    AddSubgroup.subgroupOf_inertia]

/-- `|G| = r |D_P|`, where `r` is the number of primes over `p`. -/
theorem ncard_primesOver_mul_card_stabilizer (p : Ideal R) [p.IsPrime] (P : Ideal S)
    [P.LiesOver p] [P.IsPrime] :
    (p.primesOver S).ncard * Nat.card (MulAction.stabilizer G P) = Nat.card G := by
  rw [← IsInvariant.orbit_eq_primesOver R S G p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

/-- The order of the inertia group is the ramification index times the inseparable degree of the
residue extension (Serre, *Local fields*, I §7, Prop. 21 when `κ(P)/κ(p)` is separable). -/
theorem card_inertia_eq_ramificationIdx_mul_finInsepDegree [IsDomain R] [IsDomain S]
    [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.LiesOver p]
    [P.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    Nat.card (inertia G P) =
      P.ramificationIdx R * Field.finInsepDegree p.ResidueField P.ResidueField := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have h1 := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G
  have h2 := ncard_primesOver_mul_card_stabilizer (G := G) p P
  rw [card_stabilizer_eq_card_inertia_mul_finSepDegree p P] at h2
  rw [ramificationIdxIn_eq_ramificationIdx p P G, inertiaDegIn_eq_inertiaDeg p P G,
    inertiaDeg_eq p P, ← Field.finSepDegree_mul_finInsepDegree] at h1
  have hr : (p.primesOver S).ncard ≠ 0 := by
    have := IsGaloisGroup.finite G R S
    grind [Nat.card_pos]
  have hs : Field.finSepDegree p.ResidueField P.ResidueField ≠ 0 := by
    have := (Module.finrank_pos (R := p.ResidueField) (M := P.ResidueField)).ne'
    rw [← Field.finSepDegree_mul_finInsepDegree] at this
    exact left_ne_zero_of_mul this
  rw [← h2] at h1
  have : Nat.card (inertia G P) * Field.finSepDegree p.ResidueField P.ResidueField =
      (P.ramificationIdx R * Field.finInsepDegree p.ResidueField P.ResidueField) *
        Field.finSepDegree p.ResidueField P.ResidueField := by
    have := (Nat.mul_left_cancel (Nat.pos_of_ne_zero hr) h1).symm
    rw [this]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hs) this

/-- If the residue extension is separable, the order of the inertia group is the ramification
index. -/
theorem card_inertia_eq_ramificationIdx_of_isSeparable [IsDomain R] [IsDomain S]
    [Module.Finite R S] [Module.Flat R S] (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.LiesOver p]
    [P.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    Algebra.IsSeparable p.ResidueField P.ResidueField →
      Nat.card (inertia G P) = P.ramificationIdx R := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  intro _
  rw [card_inertia_eq_ramificationIdx_mul_finInsepDegree p P,
    Algebra.IsSeparable.finInsepDegree_eq, mul_one]

/-- The inertia group has order prime to the residue characteristic (`|I_P| ≠ 0` in `κ(p)`) if
and only if `P` is tamely ramified: its ramification index is prime to the residue characteristic
and its residue extension is separable. -/
theorem card_inertia_natCast_ne_zero_iff [IsDomain R] [IsDomain S] [Module.Finite R S]
    [Module.Flat R S] (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.LiesOver p] [P.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    (Nat.card (inertia G P) : p.ResidueField) ≠ 0 ↔
      (P.ramificationIdx R : p.ResidueField) ≠ 0 ∧
        Algebra.IsSeparable p.ResidueField P.ResidueField := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  rw [card_inertia_eq_ramificationIdx_mul_finInsepDegree p P, Nat.cast_mul, mul_ne_zero_iff,
    Field.natCast_finInsepDegree_ne_zero_iff]

section Tower

variable {A C B : Type*} [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra C B]
  [Algebra A B] [IsScalarTower A C B] [IsDomain A] [IsDomain C] [IsDomain B]
  [Module.Finite A B] [Module.Flat A B] [Module.Finite C B] [Module.Flat C B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
  (H : Subgroup G) [IsGaloisGroup H C B]

omit [IsDomain B] [Finite G] in
/-- `|I_P| = |I_P ∩ H| [I_P : I_P ∩ H]`, where `I_P ∩ H` is the inertia group of `P` for the
action of `H`. -/
theorem card_inertia_eq_card_inertia_mul_relIndex (P : Ideal B) :
    Nat.card (P.inertia G) = Nat.card (P.inertia H) * H.relIndex (P.inertia G) := by
  rw [← (H.subgroupOf (P.inertia G)).card_mul_index, Subgroup.relIndex]
  congr 1
  have e1 : Nat.card (H.subgroupOf (P.inertia G)) = Nat.card (H ⊓ P.inertia G : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have e2 : Nat.card (P.inertia H) = Nat.card (P.inertia G ⊓ H : Subgroup G) := by
    change Nat.card ((P.inertia G).subgroupOf H) = _
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [e1, e2, inf_comm]

include H in
/-- Let `C` be an intermediate ring with Galois group `H ≤ G` for `B/C`, `P` a prime of `B` over
`p` and `Q = P ∩ C`. Then `[I_P : I_P ∩ H] = e(Q/p) [κ(Q) : κ(p)]_i`: the ramification of `Q`
over `p` is measured by the image of the inertia group in `G/H`. -/
theorem relIndex_inertia_eq (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p (P.under C)
    H.relIndex (P.inertia G) = (P.under C).ramificationIdx A *
      Field.finInsepDegree p.ResidueField (P.under C).ResidueField := by
  set Q := P.under C
  have : Q.LiesOver p := ⟨by rw [Ideal.under_under, ← Ideal.over_def P p]⟩
  have := IsGaloisGroup.finite H C B
  let := Localization.AtPrime.algebraOfLiesOver p Q
  let := Localization.AtPrime.algebraOfLiesOver Q P
  let := Localization.AtPrime.algebraOfLiesOver p P
  have hG := card_inertia_eq_ramificationIdx_mul_finInsepDegree (G := G) p P
  have hH := card_inertia_eq_ramificationIdx_mul_finInsepDegree (G := H) Q P
  have he : P.ramificationIdx A = Q.ramificationIdx A * P.ramificationIdx C :=
    Ideal.ramificationIdx_tower Q P
  have : Algebra.IsAlgebraic p.ResidueField Q.ResidueField :=
    Algebra.IsAlgebraic.tower_bot p.ResidueField Q.ResidueField P.ResidueField
  have hf := Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic p.ResidueField
    Q.ResidueField P.ResidueField
  have hc := card_inertia_eq_card_inertia_mul_relIndex (G := G) H P
  have hpos : 0 < Nat.card (P.inertia H) := Nat.card_pos
  have h1 : Nat.card (P.inertia G) = Nat.card (P.inertia H) *
      (Q.ramificationIdx A * Field.finInsepDegree p.ResidueField Q.ResidueField) := by
    rw [hG, hH, he, ← hf]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos (hc.symm.trans h1)

end Tower

end Ideal

namespace Algebra

/-- A prime `q` with ramification index `1` over `R` and separable residue field extension is
unramified. -/
theorem isUnramifiedAt_of_ramificationIdx_eq_one {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [EssFiniteType R S] (q : Ideal S) [q.IsPrime] (he : q.ramificationIdx R = 1) :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    Algebra.IsSeparable (q.under R).ResidueField q.ResidueField → IsUnramifiedAt R q := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  intro hsep
  rw [isUnramifiedAt_iff_map_eq R (q.under R) q]
  refine ⟨hsep, ?_⟩
  rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff] at he
  exact he

end Algebra
