/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.CurveLiftFinite

/-!
# SGA 1, Exposé III, 7.4: the lifted morphisms to `ℙ¹` are flat

The `n`-th thickening `ℙ¹_A ×_A Aₙ` of `ℙ¹_A = Proj A[x₀, x₁]` is `ℙ¹_{Aₙ} = Proj Aₙ[x₀, x₁]`
(`CurveLift.isPullback_projBaseChange`, from `ProjectiveSpace.isPullback_proj`), and the morphism
`qₙ : Xₙ ⟶ ℙ¹_A ×_A Aₙ` of a stage is the morphism `Xₙ ⟶ ℙ¹_{Aₙ}` of its chart data over `Aₙ`
followed by this identification (`CurveLift.Stage.thickeningHom_eq`). On the charts of `ℙ¹_{Aₙ}`
the latter is `Aₙ[t] → Γ(Uₙ)`, `t ↦ tₙ`, which is flat if it is at level `0`
(`CurveLift.chartHom_finite_flat_of_isPullback`). Hence `qₙ` is flat
(`CurveLift.Stage.flat_thickeningHom`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
  AlgebraicGeometry.AmpleLift MvPolynomial

namespace SGA.SGA1.ExposeIII.CurveLift

variable {A : Type u} [CommRing A] {I : Ideal A}

section BaseChange

variable (I) in
/-- The morphism `ℙ¹_{Aₙ} ⟶ ℙ¹_A` over `Spec Aₙ ⟶ Spec A`. -/
noncomputable def projMap (n : ℕ) :
    Proj (grading Two.{u} (A ⧸ I ^ (n + 1))) ⟶ Proj (grading Two.{u} A) :=
  (isPullback_proj (σ := Two.{u}) (R := A)).lift (projToProjInt Two.{u} (A ⧸ I ^ (n + 1)))
    (projToSpec Two.{u} (A ⧸ I ^ (n + 1)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
    (terminal.hom_ext _ _)

@[reassoc (attr := simp)]
lemma projMap_projToProjInt (n : ℕ) :
    projMap I n ≫ projToProjInt Two.{u} A = projToProjInt Two.{u} (A ⧸ I ^ (n + 1)) :=
  (isPullback_proj (σ := Two.{u}) (R := A)).lift_fst _ _ _

@[reassoc (attr := simp)]
lemma projMap_projToSpec (n : ℕ) :
    projMap I n ≫ projToSpec Two.{u} A = projToSpec Two.{u} (A ⧸ I ^ (n + 1)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) :=
  (isPullback_proj (σ := Two.{u}) (R := A)).lift_snd _ _ _

variable (I) in
/-- `ℙ¹_{Aₙ} = ℙ¹_A ×_A Aₙ`. -/
lemma isPullback_projBaseChange (n : ℕ) :
    IsPullback (projMap I n) (projToSpec Two.{u} (A ⧸ I ^ (n + 1))) (projToSpec Two.{u} A)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) := by
  refine IsPullback.of_right (h₁₂ := projToProjInt Two.{u} A) ?_ (projMap_projToSpec n)
    (isPullback_proj (σ := Two.{u}) (R := A))
  rw [projMap_projToProjInt, terminal.comp_from]
  exact isPullback_proj (σ := Two.{u}) (R := A ⧸ I ^ (n + 1))

variable (I) in
/-- `ℙ¹_{Aₙ} ≅ ℙ¹_A ×_A Aₙ`, the `n`-th thickening of `ℙ¹_A`. -/
noncomputable def projThickeningIso (n : ℕ) :
    Proj (grading Two.{u} (A ⧸ I ^ (n + 1))) ≅ thickening (projToSpec Two.{u} A) I n :=
  (isPullback_projBaseChange I n).isoPullback

@[reassoc (attr := simp)]
lemma projThickeningIso_hom_ι (n : ℕ) :
    (projThickeningIso I n).hom ≫ thickening.ι (projToSpec Two.{u} A) I n = projMap I n :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
lemma projThickeningIso_hom_snd (n : ℕ) :
    (projThickeningIso I n).hom ≫ thickeningSnd (projToSpec Two.{u} A) n =
      projToSpec Two.{u} (A ⧸ I ^ (n + 1)) :=
  IsPullback.isoPullback_hom_snd _

end BaseChange

section Stage

variable {B : Base I}

/-- The chart data of a stage, over `Aₙ`. -/
noncomputable def Stage.chartDataQ {n : ℕ} (S : Stage B n) :
    TwoChartData S.X (A ⧸ I ^ (n + 1)) where
  c := S.f.appTop.hom.comp (Scheme.ΓSpecIso (Q I n)).inv.hom
  U₀ := S.U₀
  U₁ := S.U₁
  sup_eq_top := S.sup_eq_top
  τ := S.t
  σ := S.s
  mul_eq_one := S.mul_eq_one
  basicOpen_τ_le := S.basicOpen_t_le
  basicOpen_σ_le := S.basicOpen_s_le

/-- The morphism `Xₙ ⟶ ℙ¹_{Aₙ}` of a stage. -/
noncomputable def Stage.toProjQ {n : ℕ} (S : Stage B n) :
    S.X ⟶ Proj (grading Two.{u} (A ⧸ I ^ (n + 1))) :=
  S.chartDataQ.toProj

@[reassoc]
lemma Stage.toProjQ_projToSpec {n : ℕ} (S : Stage B n) :
    S.toProjQ ≫ projToSpec Two.{u} (A ⧸ I ^ (n + 1)) = S.f := by
  rw [Stage.toProjQ, TwoChartData.toProj_projToSpec]
  change S.X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (Q I n)).inv ≫ S.f.appTop) = S.f
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

lemma Stage.toProjQ_projMap {n : ℕ} (S : Stage B n) : S.toProjQ ≫ projMap I n = S.toProj := by
  apply (isPullback_proj (σ := Two.{u}) (R := A)).hom_ext
  · rw [Category.assoc, projMap_projToProjInt, Stage.toProj, Stage.toProjQ, projToProjInt,
      projToProjInt, TwoChartData.toProj_comp_map, TwoChartData.toProj_comp_map]
    have hc : (S.chartDataQ.comap (intCast (A ⧸ I ^ (n + 1)))).c =
        (S.chartData.comap (intCast A)).c := ringHom_ext_uliftInt _ _
    have : S.chartDataQ.comap (intCast (A ⧸ I ^ (n + 1))) = S.chartData.comap (intCast A) := by
      cases h : S.chartDataQ.comap (intCast (A ⧸ I ^ (n + 1)))
      cases h' : S.chartData.comap (intCast A)
      rw [h, h'] at hc
      simp only [TwoChartData.comap, Stage.chartDataQ, Stage.chartData] at h h'
      obtain ⟨-, rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨-, rfl, rfl, rfl, rfl⟩ := h'
      simp only at hc
      rw [hc]
    rw [this]
  · rw [Category.assoc, projMap_projToSpec, Stage.toProjQ_projToSpec_assoc,
      Stage.toProj_projToSpec]

lemma Stage.thickeningHom_eq {n : ℕ} (S : Stage B n) :
    S.thickeningHom = S.toProjQ ≫ (projThickeningIso I n).hom := by
  apply thickening_hom_ext (projToSpec Two.{u} A)
  · rw [Stage.thickeningHom_ι, Category.assoc, projThickeningIso_hom_ι, S.toProjQ_projMap]
  · rw [Stage.thickeningHom_snd, Category.assoc, projThickeningIso_hom_snd,
      S.toProjQ_projToSpec]

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism `Xₙ ⟶ ℙ¹_{Aₙ}` of a stage is flat if the level `0` chart homomorphisms are. -/
theorem Stage.flat_toProjQ {n : ℕ} (S : Stage B n)
    (h₀ : (chartHom {j : Two.{u} // j ≠ Two.zero} B.f B.U₀ B.t).Flat)
    (h₁ : (chartHom {j : Two.{u} // j ≠ Two.one} B.f B.U₁ B.s).Flat) :
    Flat S.toProjQ := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun i : Two.{u} ↦ Proj.basicOpen (grading Two.{u} (A ⧸ I ^ (n + 1))) (MvPolynomial.X i))
    (iSup_basicOpen_X Two.{u} (A ⧸ I ^ (n + 1))) fun i ↦ ?_
  obtain ⟨i⟩ := i
  fin_cases i
  · refine flat_morphismRestrict_of_appLE S.toProjQ
      (Proj.isAffineOpen_basicOpen _ _ (X_mem_grading Two.zero) one_pos)
      S.chartDataQ.toProj_preimage_basicOpen_zero S.isAffineOpen_U₀ ?_
    have hiso := (Proj.basicOpenIsoAway (grading Two.{u} (A ⧸ I ^ (n + 1)))
      (MvPolynomial.X Two.zero) (X_mem_grading Two.zero) one_pos).isIso_hom
    rw [Proj.basicOpenIsoAway_hom] at hiso
    rw [← RingHom.Flat.respectsIso.cancel_left_isIso
      (Proj.awayToSection _ (MvPolynomial.X Two.zero)), ← CommRingCat.hom_comp]
    change (Proj.awayToSection (grading Two.{u} (A ⧸ I ^ (n + 1))) (MvPolynomial.X Two.zero) ≫
      S.chartDataQ.toProj.appLE _ S.chartDataQ.U₀ _).hom.Flat
    rw [TwoChartData.awayToSection_comp_appLE_zero, CommRingCat.hom_ofHom]
    exact RingHom.Flat.respectsIso.2 _ _ ((S.chartHom₀_finite_flat _).2 h₀)
  · refine flat_morphismRestrict_of_appLE S.toProjQ
      (Proj.isAffineOpen_basicOpen _ _ (X_mem_grading Two.one) one_pos)
      S.chartDataQ.toProj_preimage_basicOpen_one S.isAffineOpen_U₁ ?_
    have hiso := (Proj.basicOpenIsoAway (grading Two.{u} (A ⧸ I ^ (n + 1)))
      (MvPolynomial.X Two.one) (X_mem_grading Two.one) one_pos).isIso_hom
    rw [Proj.basicOpenIsoAway_hom] at hiso
    rw [← RingHom.Flat.respectsIso.cancel_left_isIso
      (Proj.awayToSection _ (MvPolynomial.X Two.one)), ← CommRingCat.hom_comp]
    change (Proj.awayToSection (grading Two.{u} (A ⧸ I ^ (n + 1))) (MvPolynomial.X Two.one) ≫
      S.chartDataQ.toProj.appLE _ S.chartDataQ.U₁ _).hom.Flat
    rw [TwoChartData.awayToSection_comp_appLE_one, CommRingCat.hom_ofHom]
    exact RingHom.Flat.respectsIso.2 _ _ ((S.chartHom₁_finite_flat _).2 h₁)

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism `qₙ : Xₙ ⟶ ℙ¹_A ×_A Aₙ` of a stage is flat if the level `0` chart homomorphisms
are. -/
theorem Stage.flat_thickeningHom {n : ℕ} (S : Stage B n)
    (h₀ : (chartHom {j : Two.{u} // j ≠ Two.zero} B.f B.U₀ B.t).Flat)
    (h₁ : (chartHom {j : Two.{u} // j ≠ Two.one} B.f B.U₁ B.s).Flat) :
    Flat S.thickeningHom := by
  have := S.flat_toProjQ h₀ h₁
  rw [S.thickeningHom_eq]
  infer_instance

end Stage

variable (B : Base I)

/-- **Algebraization of the lifts of a curve with a finite flat morphism to `ℙ¹`** (a variant of
SGA 1 III.7.2): let `A` be noetherian and `I`-adically complete and `B` level `0` data (a smooth
`A₀`-scheme `X₀` with charts `U₀`, `U₁`, coordinates `t`, `s`, and the `H¹` condition) whose chart
homomorphisms `A₀[t] → Γ(U₀)`, `A₀[s] → Γ(U₁)` are finite and flat. Then there is a finite flat
`p : Y ⟶ ℙ¹_A` whose reduction modulo `I` is `X₀ ⟶ ℙ¹_A ×_A A₀`. It differs from III.7.2 in two
ways: `X₀` comes with a finite flat morphism to `ℙ¹` instead of an ample line bundle (and
`H²(X₀, 𝒪) = 0` is not used), and only the reduction modulo `I` of `Y` is identified with `X₀`. -/
theorem exists_algebraization_of_base [IsNoetherianRing A] [IsAdicComplete I A]
    (hfin₀ : (chartHom {j : Two.{u} // j ≠ Two.zero} B.f B.U₀ B.t).Finite)
    (hfin₁ : (chartHom {j : Two.{u} // j ≠ Two.one} B.f B.U₁ B.s).Finite)
    (hfl₀ : (chartHom {j : Two.{u} // j ≠ Two.zero} B.f B.U₀ B.t).Flat)
    (hfl₁ : (chartHom {j : Two.{u} // j ≠ Two.one} B.f B.U₁ B.s).Flat) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ Proj (grading Two.{u} A)) (_ : IsFinite p) (_ : Flat p)
      (e : pullback p (thickening.ι (projToSpec Two.{u} A) I 0) ≅ B.X),
      e.hom ≫ (stage B 0).thickeningHom = pullback.snd _ _ :=
  exists_algebraization B (fun n ↦ (stage B n).isFinite_thickeningHom hfin₀ hfin₁)
    (fun n ↦ (stage B n).flat_thickeningHom hfl₀ hfl₁)

end SGA.SGA1.ExposeIII.CurveLift
