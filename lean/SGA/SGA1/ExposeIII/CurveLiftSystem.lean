/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.CurveLiftStage
import SGA.Foundations.Formal.AmpleLiftProj

/-!
# SGA 1, Exposé III, 7.4: the formal system of lifts over `ℙ¹`

From the level `0` data `B : CurveLift.Base I` (a smooth `A₀`-scheme with a morphism to `ℙ¹`
given on two charts, with the vanishing of the relevant `H¹`), the lifting step
`CurveLift.Stage.exists_succ` gives a sequence of stages `CurveLift.stage B n` over
`Aₙ = A / I^{n+1}`, with transition morphisms `Xₙ ⟶ Xₙ₊₁` making `Xₙ = Xₙ₊₁ ×_{Aₙ₊₁} Aₙ`. Their
morphisms to `ℙ¹_A = Proj A[x₀, x₁]` (`AmpleLift.TwoChartData.toProj`) define morphisms
`qₙ : Xₙ ⟶ ℙ¹_A ×_A Aₙ` to the thickenings of `ℙ¹_A` (`CurveLift.Stage.thickeningHom`), and the
squares `Xₙ ⟶ Xₙ₊₁` over the thickenings are cartesian
(`CurveLift.Stage.isPullback_thickeningHom`). If the `qₙ`
are finite and flat, this is a finite flat covering of the formal completion of `ℙ¹_A`
(`CurveLift.formalFiniteFlat`), to which `CohomologyAux.exists_finite_flat_of_formalFiniteFlat`
applies.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
  AlgebraicGeometry.AmpleLift

namespace SGA.SGA1.ExposeIII.CurveLift

variable {A : Type u} [CommRing A] {I : Ideal A} {B : Base I}

section Sequence

variable [IsNoetherianRing A]

/-- The next stage. -/
noncomputable def Stage.succ {n : ℕ} (S : Stage B n) : Stage B (n + 1) :=
  S.exists_succ.choose

/-- The transition morphism `Xₙ ⟶ Xₙ₊₁`. -/
noncomputable def Stage.toSucc {n : ℕ} (S : Stage B n) : S.X ⟶ S.succ.X :=
  S.exists_succ.choose_spec.choose

lemma Stage.preimage_succ_U₀ {n : ℕ} (S : Stage B n) : S.toSucc ⁻¹ᵁ S.succ.U₀ = S.U₀ :=
  S.exists_succ.choose_spec.choose_spec.choose

lemma Stage.preimage_succ_U₁ {n : ℕ} (S : Stage B n) : S.toSucc ⁻¹ᵁ S.succ.U₁ = S.U₁ :=
  S.exists_succ.choose_spec.choose_spec.choose_spec.choose

lemma Stage.isPullback_toSucc {n : ℕ} (S : Stage B n) :
    IsPullback S.toSucc S.f S.succ.f (π I n) :=
  S.exists_succ.choose_spec.choose_spec.choose_spec.choose_spec.1

lemma Stage.i_toSucc {n : ℕ} (S : Stage B n) : S.i ≫ S.toSucc = S.succ.i :=
  S.exists_succ.choose_spec.choose_spec.choose_spec.choose_spec.2.1

lemma Stage.appLE_toSucc_t {n : ℕ} (S : Stage B n) :
    S.toSucc.appLE S.succ.U₀ S.U₀ S.preimage_succ_U₀.ge S.succ.t = S.t :=
  S.exists_succ.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1

lemma Stage.appLE_toSucc_s {n : ℕ} (S : Stage B n) :
    S.toSucc.appLE S.succ.U₁ S.U₁ S.preimage_succ_U₁.ge S.succ.s = S.s :=
  S.exists_succ.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2

variable (B) in
/-- The sequence of stages. -/
noncomputable def stage : ∀ n, Stage B n
  | 0 => Stage.zero B
  | n + 1 => (stage n).succ

end Sequence

section Proj

/-- The chart data of a stage, over `A`. -/
noncomputable def Stage.chartData {n : ℕ} (S : Stage B n) : TwoChartData S.X A where
  c := cA I S.f
  U₀ := S.U₀
  U₁ := S.U₁
  sup_eq_top := S.sup_eq_top
  τ := S.t
  σ := S.s
  mul_eq_one := S.mul_eq_one
  basicOpen_τ_le := S.basicOpen_t_le
  basicOpen_σ_le := S.basicOpen_s_le

/-- The morphism `Xₙ ⟶ ℙ¹_A` of a stage. -/
noncomputable def Stage.toProj {n : ℕ} (S : Stage B n) : S.X ⟶ Proj (grading Two.{u} A) :=
  S.chartData.toProj

lemma toSpecΓ_SpecMap_cA {n : ℕ} {X : Scheme.{u}} (f : X ⟶ Spec (Q I n)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (cA I f)) =
      f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) := by
  rw [cA, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    CommRingCat.ofHom_hom, CommRingCat.ofHom_hom, ← Category.assoc, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]

lemma Stage.toProj_projToSpec {n : ℕ} (S : Stage B n) :
    S.toProj ≫ projToSpec Two.{u} A =
      S.f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) := by
  rw [Stage.toProj, TwoChartData.toProj_projToSpec, ← toSpecΓ_SpecMap_cA]
  rfl

lemma cA_comp {n : ℕ} {X X' : Scheme.{u}} (f : X ⟶ Spec (Q I n)) (f' : X' ⟶ Spec (Q I (n + 1)))
    (k : X ⟶ X') (hk : k ≫ f' = f ≫ π I n) (r : A) : cA I f r = k.appTop (cA I f' r) := by
  have h1 : (Scheme.ΓSpecIso (Q I n)).inv.hom (Ideal.Quotient.mk (I ^ (n + 1)) r) =
      (π I n).appTop.hom ((Scheme.ΓSpecIso (Q I (n + 1))).inv.hom
        (Ideal.Quotient.mk (I ^ (n + 1 + 1)) r)) := by
    have := congrArg (fun g ↦ g.hom (Ideal.Quotient.mk (I ^ (n + 1 + 1)) r))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) : A ⧸ I ^ (n + 1 + 1) →+* A ⧸ I ^ (n + 1))))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom, Ideal.Quotient.factor_mk] at this
    exact this
  have h2 := congrArg (fun g ↦ g.hom ((Scheme.ΓSpecIso (Q I (n + 1))).inv.hom
    (Ideal.Quotient.mk (I ^ (n + 1 + 1)) r))) (congrArg Scheme.Hom.appTop hk)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply] at h2
  change f.appTop.hom ((Scheme.ΓSpecIso (Q I n)).inv.hom (Ideal.Quotient.mk (I ^ (n + 1)) r)) = _
  rw [h1]
  exact h2.symm

lemma Stage.toSucc_toProj [IsNoetherianRing A] {n : ℕ} (S : Stage B n) :
    S.toSucc ≫ S.succ.toProj = S.toProj :=
  TwoChartData.comp_toProj S.succ.chartData S.toSucc S.chartData S.preimage_succ_U₀.ge
    S.preimage_succ_U₁.ge (cA_comp S.f S.succ.f S.toSucc S.isPullback_toSucc.w)
    S.appLE_toSucc_t.symm S.appLE_toSucc_s.symm

end Proj

section System

variable [IsNoetherianRing A]

/-- The projection `ℙ¹_A ×_A Aₙ ⟶ Spec Aₙ` of the `n`-th thickening of `ℙ¹_A`. -/
noncomputable abbrev thickeningSnd {P : Scheme.{u}} (f : P ⟶ Spec (.of A)) (n : ℕ) :
    thickening f I n ⟶ Spec (Q I n) :=
  pullback.snd _ _

omit [IsNoetherianRing A] in
lemma thickening_hom_ext {P T : Scheme.{u}} (f : P ⟶ Spec (.of A)) {n : ℕ}
    {g g' : T ⟶ thickening f I n} (h₁ : g ≫ thickening.ι f I n = g' ≫ thickening.ι f I n)
    (h₂ : g ≫ thickeningSnd f n = g' ≫ thickeningSnd f n) : g = g' :=
  pullback.hom_ext h₁ h₂

/-- The morphism `qₙ : Xₙ ⟶ ℙ¹_A ×_A Aₙ` of a stage to the `n`-th thickening of `ℙ¹_A`. -/
noncomputable def Stage.thickeningHom {n : ℕ} (S : Stage B n) :
    S.X ⟶ thickening (projToSpec Two.{u} A) I n :=
  pullback.lift S.toProj S.f S.toProj_projToSpec

omit [IsNoetherianRing A] in
@[reassoc (attr := simp)]
lemma Stage.thickeningHom_ι {n : ℕ} (S : Stage B n) :
    S.thickeningHom ≫ thickening.ι (projToSpec Two.{u} A) I n = S.toProj := by
  rw [Stage.thickeningHom, thickening.ι]
  exact pullback.lift_fst _ _ _

omit [IsNoetherianRing A] in
@[reassoc (attr := simp)]
lemma Stage.thickeningHom_snd {n : ℕ} (S : Stage B n) :
    S.thickeningHom ≫ thickeningSnd (projToSpec Two.{u} A) n = S.f := by
  rw [Stage.thickeningHom]
  exact pullback.lift_snd _ _ _

omit [IsNoetherianRing A] in
/-- The transition `X_n ⟶ X_{n+1}` between thickenings is the base change of
`Spec Aₙ ⟶ Spec Aₙ₊₁`. -/
lemma isPullback_thickening_transition {P : Scheme.{u}} (f : P ⟶ Spec (.of A)) (n : ℕ) :
    IsPullback (thickening.transition f I n) (thickeningSnd f n) (thickeningSnd f (n + 1))
      (π I n) := by
  have h1 : thickening.transition f I n ≫ thickening.ι f I (n + 1) = thickening.ι f I n :=
    thickening.transition_ι f I n
  have h2 : π I n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) := by
    rw [π, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
  refine IsPullback.of_right (h₁₂ := thickening.ι f I (n + 1)) (v₁₃ := f) ?_ ?_
    (CohomologyAux.isPullback_thickening (A := CommRingCat.of A) I f (n + 1))
  · refine (CohomologyAux.isPullback_thickening (A := CommRingCat.of A) I f n).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Iso.refl_hom]
      exact (Category.comp_id _).trans (h1.symm.trans (Category.id_comp _).symm)
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · rw [Iso.refl_hom, Iso.refl_hom]
      exact (Category.comp_id _).trans (h2.symm.trans (Category.id_comp _).symm)
  · rw [thickening.transition]
    exact pullback.lift_snd _ _ _

/-- The squares `Xₙ ⟶ Xₙ₊₁` over the thickenings of `ℙ¹_A` are cartesian. -/
lemma Stage.isPullback_thickeningHom {n : ℕ} (S : Stage B n) :
    IsPullback S.toSucc S.thickeningHom S.succ.thickeningHom
      (thickening.transition (projToSpec Two.{u} A) I n) := by
  refine IsPullback.of_bot ?_ ?_ (isPullback_thickening_transition _ n)
  · rw [Stage.thickeningHom_snd, Stage.thickeningHom_snd]
    exact S.isPullback_toSucc
  · refine thickening_hom_ext _ ?_ ?_
    · rw [Category.assoc, Stage.thickeningHom_ι, S.toSucc_toProj, Category.assoc,
        thickening.transition_ι, Stage.thickeningHom_ι]
    · rw [Category.assoc, Stage.thickeningHom_snd, Category.assoc,
        (isPullback_thickening_transition (projToSpec Two.{u} A) n).w,
        Stage.thickeningHom_snd_assoc, S.isPullback_toSucc.w]

variable (B) in
/-- The finite flat covering of the formal completion of `ℙ¹_A` along `V(I)` given by the stages,
provided the morphisms `qₙ : Xₙ ⟶ ℙ¹_A ×_A Aₙ` are finite and flat. -/
noncomputable def formalFiniteFlat (hfin : ∀ n, IsFinite (stage B n).thickeningHom)
    (hfl : ∀ n, Flat (stage B n).thickeningHom) :
    CohomologyAux.FormalFiniteFlat (A := CommRingCat.of A) I (projToSpec Two.{u} A) where
  obj n := (stage B n).X
  hom n := (stage B n).thickeningHom
  isFinite_hom := hfin
  flat_hom := hfl
  transition n := (stage B n).toSucc
  isPullback n := (stage B n).isPullback_thickeningHom

variable (B) in
/-- **Algebraization of the lifts** (a variant of SGA 1 III.7.2): if `A` is noetherian and
`I`-adically complete and the morphisms `qₙ : Xₙ ⟶ ℙ¹_A ×_A Aₙ` are finite and flat, there is a
finite flat `p : Y ⟶ ℙ¹_A` whose reduction modulo `I` is `X₀ ⟶ ℙ¹_A ×_A A₀`. It differs from
III.7.2 in two ways: the formal curve is given with a finite flat morphism to the formal completion
of `ℙ¹_A` (not with an ample line bundle, and `H²(X₀, 𝒪) = 0` is not used), and only the reduction
modulo `I` of `Y` is identified with `X₀` (III.7.2 identifies the formal completion of `Y` with the
whole formal system `(Xₙ)`). -/
theorem exists_algebraization [IsAdicComplete I A]
    (hfin : ∀ n, IsFinite (stage B n).thickeningHom) (hfl : ∀ n, Flat (stage B n).thickeningHom) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ Proj (grading Two.{u} A)) (_ : IsFinite p) (_ : Flat p)
      (e : pullback p (thickening.ι (projToSpec Two.{u} A) I 0) ≅ B.X),
      e.hom ≫ (stage B 0).thickeningHom = pullback.snd _ _ :=
  CohomologyAux.exists_finite_flat_of_formalFiniteFlat (A := CommRingCat.of A) I
    (isoProj Two.{u} A).hom (projToSpec Two.{u} A) (isoProj_hom_over Two.{u} A).symm
    (formalFiniteFlat B hfin hfl)

end System

end SGA.SGA1.ExposeIII.CurveLift
