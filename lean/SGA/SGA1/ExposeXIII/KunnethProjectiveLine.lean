/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.PolynomialAlgebra
import SGA.Foundations.Projective.SectionsBaseChange
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupProjectiveLine

/-!
# SGA 1, XIII.4.6 in characteristic `0`: an open subset of the affine line inside `ℙ¹`

The curve case of the resolution-free route to XIII.4.6 in characteristic `0`
(`AffineLineOpenInvarianceStatement`) compactifies a Kummer covering of `U = 𝔸¹ ∖ V(g)` inside
the projective line `ℙ¹_k = Proj k[x₀, x₁]` (`SGA.SGA1.ExposeXI.ProjectiveLine`). This file
collects the facts about the charts `D₊(x₀) = Spec k[t]` and `D₊(x₁) = Spec k[s]`, `s = t⁻¹`,
used there:

* `bijective_aeval_of_isPullback`: base change of a chart `Γ(Y, O) ≅ k[X]` along a field extension
  `k → k'`: the sections of `Y ×ₖ k'` over the preimage of `O` are `k'[X]` (flat base change of
  sections, `Scheme.LineBundle.isPushout_appLE_of_flat`, and `polyEquivTensor`);
* `lineOpen k g = D(g) ⊆ D₊(x₀)`, and, when `g(0) = 0` (so that `U ⊆ D₊(x₀x₁)`), its equation
  `chartPoly₁ k g = s · rev(g / t)` in the chart `D₊(x₁)` (`basicOpen_chartPoly₁`);
* the coordinate rings `Γ(U) = k[t]_g = k[s]_{s · rev(g / t)}` as localizations of the two charts
  (`isLocalization_lineOpen₀`, `isLocalization_lineOpen₁`) and the relation `t s = 1` on `U`
  (`res_chartCoord₀_mul_res_chartCoord₁`);
* the roots of `chartPoly₁ k g`: `0` and the inverses of the nonzero roots of `g`
  (`isRoot_chartPoly₁_iff`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Polynomial LaurentPolynomial
open SGA.SGA1.ExposeXI.ProjectiveLine SGA.SGA1.ExposeXI
open scoped TensorProduct

namespace SGA.SGA1.ExposeXIII.KummerCompactification

section BaseChange

set_option backward.isDefEq.respectTransparency false in
/-- Base change of an affine chart `Γ(Y, O) ≅ k[X]` along a field extension `k → k'`: if
`P = Y ×ₖ k'` (with projections `fst`, `snd`), the `k'`-algebra map `k'[X] → Γ(P, fst⁻¹ O)` sending
`X` to the pullback of the coordinate is bijective. -/
theorem bijective_aeval_of_isPullback {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {Y P : Scheme.{u}} {f : Y ⟶ Spec (.of k)} {fst : P ⟶ Y} {snd : P ⟶ Spec (.of k')}
    (H : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    {O : Y.Opens} (hO : IsAffineOpen O) (φ : Γ(Y, O) ≃+* k[X])
    (hφ : ∀ c : k, φ (f.appLE ⊤ O le_top ((Scheme.ΓSpecIso (.of k)).inv c)) = Polynomial.C c) :
    letI : Algebra k' Γ(P, fst ⁻¹ᵁ O) :=
      ((snd.appLE ⊤ (fst ⁻¹ᵁ O) le_top).hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom).toAlgebra
    Function.Bijective
      (Polynomial.aeval (R := k') (fst.appLE O (fst ⁻¹ᵁ O) le_rfl (φ.symm X))) := by
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have : Flat ρ := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have h := AlgebraicGeometry.Scheme.LineBundle.isPushout_appLE_of_flat H hO.isCompact
    hO.isQuasiSeparated
  let Γ' := Γ(P, fst ⁻¹ᵁ O)
  let : Algebra k' Γ' :=
    ((snd.appLE ⊤ (fst ⁻¹ᵁ O) le_top).hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom).toAlgebra
  let : Algebra k[X] Γ' := ((fst.appLE O (fst ⁻¹ᵁ O) le_rfl).hom.comp φ.symm.toRingHom).toAlgebra
  let : Algebra k Γ' := ((algebraMap k' Γ').comp (algebraMap k k')).toAlgebra
  have : IsScalarTower k k' Γ' := .of_algebraMap_eq fun _ ↦ rfl
  -- the square of rings `k → k', k[X] → Γ'` is a pushout
  have hsq : f.appLE ⊤ O le_top ≫ φ.toCommRingCatIso.hom =
      (Scheme.ΓSpecIso (.of k)).hom ≫ CommRingCat.ofHom (algebraMap k k[X]) := by
    rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv, Iso.inv_hom_id_assoc]
    exact CommRingCat.hom_ext (RingHom.ext fun c ↦ hφ c)
  have hpush : IsPushout (CommRingCat.ofHom (algebraMap k k'))
      (CommRingCat.ofHom (algebraMap k k[X]))
      (CommRingCat.ofHom (algebraMap k' Γ')) (CommRingCat.ofHom (algebraMap k[X] Γ')) := by
    refine h.flip.of_iso (Scheme.ΓSpecIso (.of k)) (Scheme.ΓSpecIso (.of k'))
      φ.toCommRingCatIso (Iso.refl _) ?_ hsq ?_ ?_
    · have : ρ.appLE ⊤ ⊤ le_top = ρ.appTop := Scheme.Hom.appLE_eq_app ρ
      rw [this]
      exact Scheme.ΓSpecIso_naturality _
    · rw [Iso.refl_hom, Category.comp_id, show CommRingCat.ofHom (algebraMap k' Γ') =
        (Scheme.ΓSpecIso (.of k')).inv ≫ snd.appLE ⊤ (fst ⁻¹ᵁ O) le_top from rfl,
        Iso.hom_inv_id_assoc]
    · ext x
      change _ = fst.appLE O (fst ⁻¹ᵁ O) le_rfl (φ.symm (φ x))
      rw [RingEquiv.symm_apply_apply]
      rfl
  have : IsScalarTower k k[X] Γ' := .of_algebraMap_eq fun c ↦
    congrArg (fun g ↦ g.hom c) hpush.w
  have := (CommRingCat.isPushout_iff_isPushout).mp hpush
  let e : k'[X] ≃ₐ[k'] Γ' :=
    (polyEquivTensor' k k').trans (Algebra.IsPushout.equiv k k' k[X] Γ')
  have he : (Polynomial.aeval (R := k') (fst.appLE O (fst ⁻¹ᵁ O) le_rfl (φ.symm X)) :
      k'[X] →ₐ[k'] Γ') = e.toAlgHom := by
    refine Polynomial.algHom_ext ?_
    rw [aeval_X]
    change _ = Algebra.IsPushout.equiv k k' k[X] Γ' (polyEquivTensor' k k' X)
    rw [show polyEquivTensor' k k' X = (1 : k') ⊗ₜ[k] (X : k[X]) by simp [polyEquivTensor'],
      Algebra.IsPushout.equiv_tmul, map_one, one_mul]
    rfl
  rw [he]
  exact e.bijective

end BaseChange

section Line

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

local notation "ℙ¹" => Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

/-- The open subset `U = D(g) ⊆ D₊(x₀) = 𝔸¹` of the projective line. -/
noncomputable def lineOpen (g : k[X]) : (ℙ¹).Opens :=
  (ℙ¹).basicOpen ((chartEquiv₀ k).symm g)

/-- The polynomial in `s = t⁻¹` cutting out `U` in the chart `D₊(x₁)` when `g(0) = 0`:
`s · rev(g / t)`. -/
noncomputable def chartPoly₁ (g : k[X]) : k[X] := X * (g /ₘ X).reverse

variable {k}

lemma eq_X_mul_divByMonic {g : k[X]} (hg : g.IsRoot 0) : g = X * (g /ₘ X) := by
  have := (mul_divByMonic_eq_iff_isRoot (a := (0 : k)) (p := g)).mpr hg
  simpa using this.symm

lemma lineOpen_le_torus {g : k[X]} (hg : g.IsRoot 0) :
    lineOpen k g ≤ projectiveSpace.torus (Fin 2) k := by
  rw [lineOpen, eq_X_mul_divByMonic hg, map_mul, Scheme.basicOpen_mul,
    ← chartEquiv₀_chartCoord₀, RingEquiv.symm_apply_apply, basicOpen_chartCoord₀]
  exact inf_le_left

lemma basicOpen_chartPoly₁_le_torus (g : k[X]) :
    (ℙ¹).basicOpen ((chartEquiv₁ k).symm (chartPoly₁ k g)) ≤ projectiveSpace.torus (Fin 2) k := by
  rw [chartPoly₁, map_mul, Scheme.basicOpen_mul, ← chartEquiv₁_chartCoord₁,
    RingEquiv.symm_apply_apply, basicOpen_chartCoord₁]
  exact inf_le_left

lemma toLaurentInv_chartPoly₁ (g : k[X]) (hg : g.IsRoot 0) :
    toLaurentInv k (chartPoly₁ k g) = toLaurent g * T (-2 - ((g /ₘ X).natDegree : ℤ)) := by
  set h := g /ₘ X
  have hgx : toLaurent g = T 1 * toLaurent h := by
    conv_lhs => rw [eq_X_mul_divByMonic hg]
    rw [map_mul, toLaurent_X]
  rw [chartPoly₁, toLaurentInv_apply, map_mul, map_mul, toLaurent_reverse, map_mul,
    involutive_invert, toLaurent_X, invert_T, invert_T, hgx, mul_left_comm, ← T_add,
    mul_comm (T 1), mul_assoc, ← T_add]
  congr 2
  ring

lemma basicOpen_chartPoly₁ {g : k[X]} (hg : g.IsRoot 0) :
    (ℙ¹).basicOpen ((chartEquiv₁ k).symm (chartPoly₁ k g)) = lineOpen k g := by
  set V := projectiveSpace.torus (Fin 2) k
  have h₀ : lineOpen k g = (ℙ¹).basicOpen
      ((ℙ¹).presheaf.map (homOfLE (torus_le_chart₀ k)).op ((chartEquiv₀ k).symm g)) := by
    rw [Scheme.basicOpen_res]
    exact (inf_eq_right.mpr (lineOpen_le_torus hg)).symm
  have h₁ : (ℙ¹).basicOpen ((chartEquiv₁ k).symm (chartPoly₁ k g)) = (ℙ¹).basicOpen
      ((ℙ¹).presheaf.map (homOfLE (torus_le_chart₁ k)).op
        ((chartEquiv₁ k).symm (chartPoly₁ k g))) := by
    rw [Scheme.basicOpen_res, inf_eq_right.mpr (basicOpen_chartPoly₁_le_torus g)]
  rw [h₀, h₁]
  have : (ℙ¹).presheaf.map (homOfLE (torus_le_chart₁ k)).op
      ((chartEquiv₁ k).symm (chartPoly₁ k g)) =
      (ℙ¹).presheaf.map (homOfLE (torus_le_chart₀ k)).op ((chartEquiv₀ k).symm g) *
        (torusEquiv k).symm (T (-2 - ((g /ₘ X).natDegree : ℤ))) := by
    apply (torusEquiv k).injective
    rw [map_mul, torusEquiv_res₀, torusEquiv_res₁, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, toLaurentInv_chartPoly₁ g hg]
  rw [this, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ ((isUnit_T _).map _),
    inf_eq_left.mpr (Scheme.basicOpen_le _ _)]

lemma isAffineOpen_lineOpen (g : k[X]) : IsAffineOpen (lineOpen k g) :=
  (ExposeXIII.ProjectiveLineCurve.isAffineOpen_chart₀ k).basicOpen _

lemma lineOpen_le_chart₀ (g : k[X]) : lineOpen k g ≤ chart₀ k := Scheme.basicOpen_le _ _

lemma lineOpen_le_chart₁ {g : k[X]} (hg : g.IsRoot 0) : lineOpen k g ≤ chart₁ k := by
  rw [← basicOpen_chartPoly₁ hg]
  exact Scheme.basicOpen_le _ _

/-- `t s = 1` on `U ⊆ D₊(x₀x₁)`, for the coordinates `t` of `D₊(x₀)` and `s` of `D₊(x₁)`. -/
lemma res_chartCoord₀_mul_res_chartCoord₁ {g : k[X]} (hg : g.IsRoot 0) :
    (ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₀ g)).op (chartCoord₀ k) *
      (ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₁ hg)).op (chartCoord₁ k) = 1 := by
  have h₀ : (ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₀ g)).op (chartCoord₀ k) =
      (ℙ¹).presheaf.map (homOfLE (lineOpen_le_torus hg)).op
        ((ℙ¹).presheaf.map (homOfLE (torus_le_chart₀ k)).op (chartCoord₀ k)) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have h₁ : (ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₁ hg)).op (chartCoord₁ k) =
      (ℙ¹).presheaf.map (homOfLE (lineOpen_le_torus hg)).op
        ((ℙ¹).presheaf.map (homOfLE (torus_le_chart₁ k)).op (chartCoord₁ k)) := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have ht : (ℙ¹).presheaf.map (homOfLE (torus_le_chart₀ k)).op (chartCoord₀ k) *
      (ℙ¹).presheaf.map (homOfLE (torus_le_chart₁ k)).op (chartCoord₁ k) = 1 := by
    apply (torusEquiv k).injective
    rw [map_mul, torusEquiv_res₀, torusEquiv_res₁, chartEquiv₀_chartCoord₀,
      chartEquiv₁_chartCoord₁, map_one, toLaurent_X, toLaurentInv_apply, toLaurent_X, invert_T,
      ← T_add]
    simp
  rw [h₀, h₁, ← map_mul, ht, map_one]

/-- `Γ(U) = k[t]_g`, through the chart `D₊(x₀)`. -/
lemma isLocalization_lineOpen₀ (g : k[X]) :
    letI : Algebra k[X] Γ(ℙ¹, lineOpen k g) :=
      (((ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₀ g)).op).hom.comp
        (chartEquiv₀ k).symm.toRingHom).toAlgebra
    IsLocalization.Away g Γ(ℙ¹, lineOpen k g) := by
  let : Algebra Γ(ℙ¹, chart₀ k) Γ(ℙ¹, lineOpen k g) :=
    ((ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₀ g)).op).hom.toAlgebra
  have := (ExposeXIII.ProjectiveLineCurve.isAffineOpen_chart₀ k).isLocalization_of_eq_basicOpen
    ((chartEquiv₀ k).symm g) (homOfLE (lineOpen_le_chart₀ g)) rfl
  have h := IsLocalization.isLocalization_of_base_ringEquiv
    (Submonoid.powers ((chartEquiv₀ k).symm g)) Γ(ℙ¹, lineOpen k g) (chartEquiv₀ k)
  rw [Submonoid.map_powers, RingEquiv.apply_symm_apply] at h
  exact h

/-- `Γ(U) = k[s]_{s · rev(g/t)}`, through the chart `D₊(x₁)` (when `g(0) = 0`). -/
lemma isLocalization_lineOpen₁ {g : k[X]} (hg : g.IsRoot 0) :
    letI : Algebra k[X] Γ(ℙ¹, lineOpen k g) :=
      (((ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₁ hg)).op).hom.comp
        (chartEquiv₁ k).symm.toRingHom).toAlgebra
    IsLocalization.Away (chartPoly₁ k g) Γ(ℙ¹, lineOpen k g) := by
  let : Algebra Γ(ℙ¹, chart₁ k) Γ(ℙ¹, lineOpen k g) :=
    ((ℙ¹).presheaf.map (homOfLE (lineOpen_le_chart₁ hg)).op).hom.toAlgebra
  have := (ExposeXIII.ProjectiveLineCurve.isAffineOpen_chart₁ k).isLocalization_of_eq_basicOpen
    ((chartEquiv₁ k).symm (chartPoly₁ k g)) (homOfLE (lineOpen_le_chart₁ hg))
    (basicOpen_chartPoly₁ hg).symm
  have h := IsLocalization.isLocalization_of_base_ringEquiv
    (Submonoid.powers ((chartEquiv₁ k).symm (chartPoly₁ k g))) Γ(ℙ¹, lineOpen k g)
    (chartEquiv₁ k)
  rw [Submonoid.map_powers, RingEquiv.apply_symm_apply] at h
  exact h

/-- The roots of `chartPoly₁ k g = s · rev(g / t)` are `0` and the inverses of the nonzero roots
of `g`. -/
lemma isRoot_chartPoly₁_iff {g : k[X]} (hg : g.IsRoot 0) {b : k} :
    (chartPoly₁ k g).IsRoot b ↔ b = 0 ∨ (b ≠ 0 ∧ g.IsRoot b⁻¹) := by
  rw [chartPoly₁, IsRoot, eval_mul, eval_X, mul_eq_zero]
  by_cases hb : b = 0
  · simp [hb]
  have : Invertible b⁻¹ := invertibleOfNonzero (inv_ne_zero hb)
  have hrev := eval₂_reverse_eq_zero_iff (RingHom.id k) b⁻¹ (g /ₘ X)
  rw [invOf_eq_inv, inv_inv] at hrev
  simp only [hb, false_or, ne_eq, not_false_eq_true, true_and, IsRoot]
  rw [← eval₂_id, hrev, eval₂_id]
  conv_rhs => rw [eq_X_mul_divByMonic hg, eval_mul, eval_X]
  simp [hb]

end Line

end SGA.SGA1.ExposeXIII.KummerCompactification
