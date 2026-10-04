/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import SGA.Foundations.GroupScheme.Points
import SGA.SGA1.ExposeI.DominantUnramified
import SGA.SGA1.ExposeXI.TateModule

/-!
# SGA 1, Exposé XI.2.1 for abelian varieties whose `n_A` are isogenies

SGA recalls that for an abelian variety `A` over an algebraically closed field `k` and `n > 0`,
multiplication by `n` is an isogeny, i.e. finite and surjective (`MulNIsogenyStatement`). We
derive from this the hypotheses of the criterion `exists_tateModule_equiv_of_isPretransitive`
(`TateModule`), except faithfulness:

* `finite_torsionPoints`: if `n_A` is finite, `K_n` is finite (its points lie in the fibre of
  `n_A` over the origin, and a `k`-point is determined by its image,
  `ext_of_apply_closedPoint_eq`);
* `exists_pow_eq_of_surjective`: if `n_A` is surjective, every `k`-point of `A` is an `n`-th power
  (closed points of the fibre are `k`-points, `A` being Jacobson);
* `exists_torsionPoints_of_lift`: if `n_A` is surjective, every lift `g : A ⟶ Y` of `n_A` through a
  connected étale covering maps `K_n` onto the fibre of `Y` at the origin. Indeed `Y` is
  irreducible (normal and connected), `g` maps the generic point of `A` to a point of the fibre of
  `Y` over the generic point of `A`, which is discrete, hence to the generic point of `Y`; and `g`
  is proper, so it is surjective.

Hence `exists_tateModule_equiv_of_isogeny`: XI.2.1 for an abelian variety all of whose `n_A` are
isogenies, given for every `n` an étale covering through which `n_A` lifts injectively on `K_n`.
For `n` invertible in `k` the covering `n_A` itself does (`AbelianVarietyMulN`); in general it is
the quotient `A / K_n`, descended along the radicial `A / K_n ⟶ A` by IX.4.10
(`exists_lift_mulN_injective`, `AbelianVarietyQuotient`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  IsLocalRing PreGaloisCategory

namespace SGA.SGA1.ExposeXI

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]

section Points

variable [LocallyOfFiniteType A.hom]

omit [GrpObj A] in
variable {A} in
/-- Two `k`-points of a `k`-scheme of finite type with the same image are equal. -/
lemma pointLeft_injective {x y : 𝟙_ (Over (Spec (.of k))) ⟶ A}
    (h : pointLeft A x (closedPoint k) = pointLeft A y (closedPoint k)) : x = y :=
  Over.OverMorphism.ext (ext_of_apply_closedPoint_eq A.hom (Over.w x) (Over.w y) h)

/-- If `n_A` is surjective, every `k`-point of `A` is an `n`-th power. -/
theorem exists_pow_eq_of_surjective {n : ℕ} [Surjective (mulN A n).left]
    (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : ∃ b, b ^ n = a := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  let p := pointLeft A a (closedPoint k)
  have hp : IsClosed {p} := ((pointEquivClosedPoint A.hom) ⟨pointLeft A a, Over.w a⟩).2
  obtain ⟨q, hq, hqc⟩ := nonempty_inter_closedPoints ((mulN A n).left.surjective p)
    (hp.preimage (mulN A n).left.continuous).isLocallyClosed
  have hqc : IsClosed {q} := hqc
  refine ⟨Over.homMk (pointOfClosedPoint A.hom q hqc) (pointOfClosedPoint_comp A.hom q hqc), ?_⟩
  apply pointLeft_injective
  rw [← pointLeft_comp_mulN]
  change (mulN A n).left (pointOfClosedPoint A.hom q hqc (closedPoint k)) = p
  exact (congrArg (mulN A n).left (pointOfClosedPoint_apply A.hom q hqc _)).trans hq

variable [IsCommMonObj A]

/-- If `n_A` is finite, the group `K_n` of `n`-torsion points is finite. -/
theorem finite_torsionPoints {n : ℕ} [IsFinite (mulN A n).left] : Finite (torsionPoints A n) := by
  let e : A.left := unitSection A (closedPoint k)
  have : Finite ((mulN A n).left ⁻¹' {e}) :=
    ((mulN A n).left.finite_preimage_singleton e).to_subtype
  let f : torsionPoints A n → (mulN A n).left ⁻¹' {e} := fun x ↦
    ⟨pointLeft A x (closedPoint k), by
      change (pointLeft A x ≫ (mulN A n).left) (closedPoint k) = e
      rw [pointLeft_comp_mulN, (mem_torsionPoints A).mp x.2, pointLeft_one]⟩
  exact Finite.of_injective f fun x y h ↦ Subtype.ext (pointLeft_injective (congrArg Subtype.val h))

end Points

section Lift

variable [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left]

omit [IsAlgClosed k] [IsCommMonObj A] in
/-- If `n_A` is surjective, a lift `g : A ⟶ Y` of `n_A` through a connected étale covering
`q : Y ⟶ A` is surjective: `Y` is irreducible (normal and connected), `g` is proper, and `g` maps
the generic point of `A` to that of `Y` (`Scheme.Hom.surjective_of_isDominant_comp`). -/
theorem surjective_of_comp_eq_mulN {n : ℕ} [Surjective (mulN A n).left] {Y : Scheme.{u}}
    (q : Y ⟶ A.left) [IsFinite q] [Etale q] [ConnectedSpace Y] (g : A.left ⟶ Y)
    (hg : g ≫ q = (mulN A n).left) : Surjective g := by
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have hreg := ExposeII.isRegularLocalRing_stalk_of_smooth_field k A.hom
  have : IsIntegral A.left := ExposeX.isIntegral_of_isRegularScheme hreg
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (q ≫ A.hom)
  have hY := ExposeI.isNormalScheme_of_etale q (ExposeX.isNormalScheme_of_isRegularScheme hreg)
  have : IrreducibleSpace Y := ExposeI.irreducibleSpace_of_isDomain_stalk fun y ↦ (hY y).1
  have : IsDominant (g ≫ q) := by rw [hg]; infer_instance
  have : IsProper (g ≫ q ≫ A.hom) := by
    rw [← Category.assoc, hg, Over.w (mulN A n)]
    infer_instance
  have : IsProper g := IsProper.of_comp g (q ≫ A.hom)
  exact g.surjective_of_isDominant_comp q

omit [IsCommMonObj A] in
/-- If `n_A` is surjective, a lift `g : A ⟶ Y` of `n_A` through a connected étale covering
`q : Y ⟶ A` maps the `k`-points of `A` onto those of `Y`. -/
theorem exists_pointLeft_comp_eq {n : ℕ} [Surjective (mulN A n).left] {Y : Scheme.{u}}
    (q : Y ⟶ A.left) [IsFinite q] [Etale q] [ConnectedSpace Y] (g : A.left ⟶ Y)
    (hg : g ≫ q = (mulN A n).left) (y : Spec (.of k) ⟶ Y) (hy : y ≫ q ≫ A.hom = 𝟙 _) :
    ∃ b : 𝟙_ (Over (Spec (.of k))) ⟶ A, pointLeft A b ≫ g = y := by
  have := surjective_of_comp_eq_mulN A q g hg
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hp : IsClosed {y (closedPoint k)} := ((pointEquivClosedPoint (q ≫ A.hom)) ⟨y, hy⟩).2
  obtain ⟨a, ha, hac⟩ := nonempty_inter_closedPoints (g.surjective (y (closedPoint k)))
    (hp.preimage g.continuous).isLocallyClosed
  have hac : IsClosed {a} := hac
  refine ⟨Over.homMk (pointOfClosedPoint A.hom a hac) (pointOfClosedPoint_comp A.hom a hac), ?_⟩
  refine ext_of_apply_closedPoint_eq (q ≫ A.hom) ?_ hy ?_
  · change pointOfClosedPoint A.hom a hac ≫ g ≫ q ≫ A.hom = 𝟙 _
    rw [← Category.assoc g, hg, Over.w (mulN A n)]
    exact pointOfClosedPoint_comp A.hom a hac
  · change g (pointOfClosedPoint A.hom a hac (closedPoint k)) = _
    exact (congrArg g (pointOfClosedPoint_apply A.hom a hac _)).trans ha

/-- If `n_A` is surjective, a lift `g : A ⟶ Y` of `n_A` through a connected étale covering
maps `K_n` onto the fibre of `Y` at the origin. -/
theorem exists_torsionPoints_of_lift {n : ℕ} [Surjective (mulN A n).left]
    (Y : ExposeV.FEt A.left) [IsConnected Y] (g : A.left ⟶ Y.left)
    (hg : g ≫ Y.hom = (mulN A n).left) (y : Spec (.of k) ⟶ Y.left)
    (hy : y ≫ Y.hom = unitSection A) :
    ∃ a : torsionPoints A n, y = pointLeft A a ≫ g := by
  let q : Y.left ⟶ A.left := Y.hom
  have : IsFinite q := Y.prop.1
  have : Etale q := Y.prop.2
  have : ConnectedSpace Y.left := ExposeV.FEt.connectedSpace_of_isConnected Y
  obtain ⟨b, hb⟩ := exists_pointLeft_comp_eq A q g hg y (by
    rw [← Category.assoc, hy]
    exact Over.w η[A])
  refine ⟨⟨b, (mem_torsionPoints A).mpr ?_⟩, hb.symm⟩
  apply Over.OverMorphism.ext
  change pointLeft A (b ^ n) = pointLeft A 1
  rw [← pointLeft_comp_mulN, ← hg, ← Category.assoc, hb, hy, pointLeft_one]

variable (k) in
/-- XI.2.1 for an abelian variety `A` all of whose multiplications `n_A` (`n > 0`) are isogenies
(finite and surjective, `MulNIsogenyStatement`), given, for every `n > 0`, an étale covering
through which `n_A` lifts injectively on `K_n`: the canonical map `T(A) → π₁(A, 0)` is an
isomorphism of topological groups. (`IsCommMonObj A` is automatic, `isCommMonObj_of_smooth`.) -/
theorem exists_tateModule_equiv_of_isogeny
    (hiso : ∀ n : ℕ, 0 < n → IsFinite (mulN A n).left ∧ Surjective (mulN A n).left)
    (hsep : ∀ n : ℕ+, ∃ (Y : ExposeV.FEt A.left) (g : A.left ⟶ Y.left),
      g ≫ Y.hom = (mulN A n).left ∧ ∀ a b : torsionPoints A n,
        pointLeft A a ≫ g = pointLeft A b ≫ g → a = b) :
    AbelianVarietyFundamentalGroupConclusion k A := by
  have : IsReduced A.left := ExposeII.isReduced_of_smooth_of_isReduced A.hom
  have hfin (n : ℕ+) : Finite (torsionPoints A n) :=
    have := (hiso n n.pos).1
    finite_torsionPoints A
  have hdiv (n : ℕ) (hn : 0 < n) (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : ∃ b, b ^ n = a :=
    have := (hiso n hn).2
    exists_pow_eq_of_surjective A a
  have := compactSpace_tateModule A hfin
  refine exists_tateModule_equiv_of_isPretransitive A
    (fun Y _ ↦ isPretransitive_tateModule hfin hdiv Y fun n g hg y ↦ ?_)
    (eq_one_of_forall_smul_eq hsep)
  have := (hiso n n.pos).2
  exact exists_torsionPoints_of_lift A Y g hg _ (ExposeV.FEt.fiberPoint_comp k y)

end Lift

end SGA.SGA1.ExposeXI
