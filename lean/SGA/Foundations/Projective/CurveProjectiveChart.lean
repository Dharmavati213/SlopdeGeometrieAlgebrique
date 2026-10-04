/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Formal.AmpleLiftProj
import SGA.Foundations.Projective.TwistingSheaf
import SGA.Foundations.Projective.ProjectiveSpaceSpec

/-!
# The standard charts of `ℙ¹_R` and their pull-backs

On `ℙ¹_R = Proj R[x₀, x₁]` the standard affine charts are `D₊(x₀)` and `D₊(x₁)`, with coordinates
`x₁ / x₀` and `x₀ / x₁` (`ProjectiveSpace.lineCoord₀`, `ProjectiveSpace.lineCoord₁`). This file
records:

* `ProjectiveSpace.lineCoord_mul`: `(x₁ / x₀)(x₀ / x₁) = 1` on `D₊(x₀) ∩ D₊(x₁)`;
* `ProjectiveSpace.basicOpen_lineCoord₀`: the coordinate `x₁ / x₀` is invertible exactly on
  `D₊(x₀) ∩ D₊(x₁)`;
* `ProjectiveSpace.bijective_eval₂Hom_lineCoord₀`: `R[t] → Γ(D₊(x₀), 𝒪)`, `t ↦ x₁ / x₀`, is an
  isomorphism (EGA II 2.3.1, through `Proj.awayToSection` and the dehomogenization `awayEquiv`);
* `ProjectiveSpace.finite_eval₂Hom_app_lineCoord₀`, `ProjectiveSpace.flat_eval₂Hom_app_lineCoord₀`:
  for a finite (resp. flat) morphism `g : Y ⟶ ℙ¹_R`, the ring homomorphism
  `R[t] → Γ(g⁻¹ D₊(x₀), 𝒪_Y)`, `t ↦ g^*(x₁ / x₀)`, is finite (resp. flat); likewise for `D₊(x₁)`.

## References

* [EGA II, 2.3.1, 2.6.3][EGA2].
-/

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization AlgebraicGeometry.AmpleLift

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R]

/-- The standard chart `D₊(x₀)` of `ℙ¹_R`. -/
abbrev lineChart₀ : (Proj (grading Two.{u} R)).Opens :=
  Proj.basicOpen (grading Two.{u} R) (X Two.zero)

/-- The standard chart `D₊(x₁)` of `ℙ¹_R`. -/
abbrev lineChart₁ : (Proj (grading Two.{u} R)).Opens :=
  Proj.basicOpen (grading Two.{u} R) (X Two.one)

/-- The coordinate `x₁ / x₀` on `D₊(x₀)`. -/
def lineCoord₀ : Γ(Proj (grading Two.{u} R), lineChart₀ R) :=
  Proj.fracSection (grading Two.{u} R) (X_mem_grading Two.one) (X_mem_grading Two.zero) _ le_rfl

/-- The coordinate `x₀ / x₁` on `D₊(x₁)`. -/
def lineCoord₁ : Γ(Proj (grading Two.{u} R), lineChart₁ R) :=
  Proj.fracSection (grading Two.{u} R) (X_mem_grading Two.zero) (X_mem_grading Two.one) _ le_rfl

lemma lineChart₀_sup_lineChart₁ : lineChart₀ R ⊔ lineChart₁ R = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨⟨i⟩, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_basicOpen_X Two.{u} R).ge (Set.mem_univ x))
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi

/-- `(x₁ / x₀)(x₀ / x₁) = 1` on `D₊(x₀) ∩ D₊(x₁)`. -/
lemma lineCoord_mul :
    (Proj (grading Two.{u} R)).presheaf.map
        (homOfLE inf_le_left : lineChart₀ R ⊓ lineChart₁ R ⟶ lineChart₀ R).op (lineCoord₀ R) *
      (Proj (grading Two.{u} R)).presheaf.map
        (homOfLE inf_le_right : lineChart₀ R ⊓ lineChart₁ R ⟶ lineChart₁ R).op (lineCoord₁ R) =
      1 := by
  rw [lineCoord₀, lineCoord₁, Proj.map_fracSection, Proj.map_fracSection]
  exact Proj.fracSection_mul_fracSection_swap _ _ _ inf_le_right inf_le_left

/-- `x₁ / x₀` is invertible exactly on `D₊(x₀) ∩ D₊(x₁)`. -/
lemma basicOpen_lineCoord₀ :
    (Proj (grading Two.{u} R)).basicOpen (lineCoord₀ R) = lineChart₀ R ⊓ lineChart₁ R :=
  Proj.basicOpen_fracSection _ _ _ _

/-- `x₀ / x₁` is invertible exactly on `D₊(x₁) ∩ D₊(x₀)`. -/
lemma basicOpen_lineCoord₁ :
    (Proj (grading Two.{u} R)).basicOpen (lineCoord₁ R) = lineChart₁ R ⊓ lineChart₀ R :=
  Proj.basicOpen_fracSection _ _ _ _

/-- The ring homomorphism `R → Γ(V, 𝒪_{ℙ¹_R})` of the structure morphism. -/
def lineC (V : (Proj (grading Two.{u} R)).Opens) :
    R →+* Γ(Proj (grading Two.{u} R), V) :=
  ((projToSpec Two.{u} R).appLE ⊤ V
    (le_top.trans_eq (projToSpec Two.{u} R).preimage_top.symm)).hom.comp
      (Scheme.ΓSpecIso (.of R)).inv.hom

/-- On `D₊(t)` (`t = xᵢ`), the structure morphism is `R → R[x₀, x₁]_(t) → Γ(D₊(t))`. -/
lemma awayToSection_comp_awayC {t : MvPolynomial Two.{u} R} (ht : t ∈ grading Two.{u} R 1) :
    (Proj.awayToSection (grading Two.{u} R) t).hom.comp (awayC t) =
      lineC R (Proj.basicOpen (grading Two.{u} R) t) := by
  have e : Proj.basicOpen (grading Two.{u} R) t ≤ projToSpec Two.{u} R ⁻¹ᵁ ⊤ :=
    le_top.trans_eq (projToSpec Two.{u} R).preimage_top.symm
  have h1 : (Proj.basicOpen (grading Two.{u} R) t).ι ≫ projToSpec Two.{u} R =
      (Proj.basicOpen (grading Two.{u} R) t).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (awayC t) ≫ Proj.awayToSection (grading Two.{u} R) t) := by
    calc (Proj.basicOpen (grading Two.{u} R) t).ι ≫ projToSpec Two.{u} R
        = ((Proj.basicOpenIsoSpec _ t ht one_pos).hom ≫ Proj.awayι _ t ht one_pos) ≫
            projToSpec Two.{u} R := by
          rw [← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
      _ = (Proj.basicOpenIsoSpec _ t ht one_pos).hom ≫ Spec.map (CommRingCat.ofHom (awayC t)) := by
          rw [Category.assoc, awayι_projToSpec]
      _ = _ := by
          rw [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec, Category.assoc, ← Spec.map_comp]
  have h2 : (Proj.basicOpen (grading Two.{u} R) t).toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ (projToSpec Two.{u} R).appLE ⊤ _ e) =
      (Proj.basicOpen (grading Two.{u} R) t).ι ≫ projToSpec Two.{u} R := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE,
      Scheme.Opens.toSpecΓ_top, Category.assoc, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id, Scheme.Hom.resLE_comp_ι]
  have := eq_of_toSpecΓ_SpecMap_eq _ (h2.trans h1).symm
  exact congrArg CommRingCat.Hom.hom this

lemma awayEquiv_symm_apply {σ : Type u} (i : σ) (y : MvPolynomial {j // j ≠ i} R) :
    (awayEquiv i (rfl : (X i : MvPolynomial σ R) = X i)).symm y = awayHomogenize i rfl y :=
  rfl

/-- `Proj.awayToSection` sends `xⱼ / xᵢ` to the section `xⱼ / xᵢ`. -/
lemma awayToSection_awayX (i j : Two.{u}) :
    Proj.awayToSection (grading Two.{u} R) (X i)
        (awayX i (rfl : (X i : MvPolynomial Two.{u} R) = X i) j) =
      Proj.fracSection (grading Two.{u} R) (X_mem_grading j) (X_mem_grading i) _ le_rfl := by
  refine Proj.section_ext _ fun x ↦ ?_
  rw [Proj.val_fracSection_apply]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [awayX, Away.val_mk, Localization.mk_eq_mk', Localization.mk_eq_mk', IsLocalization.map_mk']
  simp only [RingHom.id_apply, pow_one]

/-- On `D₊(x₀)`, `R[t] → Γ(D₊(x₀))`, `t ↦ x₁ / x₀`, is `Proj.awayToSection` composed with the
dehomogenization isomorphism. -/
lemma eval₂Hom_lineCoord₀ :
    eval₂Hom (lineC R (lineChart₀ R)) (fun _ : {j : Two.{u} // j ≠ Two.zero} ↦ lineCoord₀ R) =
      (Proj.awayToSection (grading Two.{u} R) (X Two.zero)).hom.comp
        (awayEquiv Two.zero
          (rfl : (X Two.zero : MvPolynomial Two.{u} R) = X Two.zero)).symm.toRingHom := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun ⟨⟨j⟩, hj⟩ ↦ ?_)
  · rw [eval₂Hom_C, ← awayToSection_comp_awayC R (X_mem_grading Two.zero)]
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, awayEquiv_symm_apply, awayHomogenize, eval₂Hom_C]
  · fin_cases j
    · exact absurd rfl hj
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, awayEquiv_symm_apply, awayHomogenize, eval₂Hom_X']
      exact (awayToSection_awayX R Two.zero Two.one).symm

/-- On `D₊(x₁)`, `R[s] → Γ(D₊(x₁))`, `s ↦ x₀ / x₁`, is `Proj.awayToSection` composed with the
dehomogenization isomorphism. -/
lemma eval₂Hom_lineCoord₁ :
    eval₂Hom (lineC R (lineChart₁ R)) (fun _ : {j : Two.{u} // j ≠ Two.one} ↦ lineCoord₁ R) =
      (Proj.awayToSection (grading Two.{u} R) (X Two.one)).hom.comp
        (awayEquiv Two.one
          (rfl : (X Two.one : MvPolynomial Two.{u} R) = X Two.one)).symm.toRingHom := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun ⟨⟨j⟩, hj⟩ ↦ ?_)
  · rw [eval₂Hom_C, ← awayToSection_comp_awayC R (X_mem_grading Two.one)]
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, awayEquiv_symm_apply, awayHomogenize, eval₂Hom_C]
  · fin_cases j
    · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, awayEquiv_symm_apply, awayHomogenize, eval₂Hom_X']
      exact (awayToSection_awayX R Two.one Two.zero).symm
    · exact absurd rfl hj

lemma bijective_awayToSection {t : MvPolynomial Two.{u} R} (ht : t ∈ grading Two.{u} R 1) :
    Function.Bijective (Proj.awayToSection (grading Two.{u} R) t) :=
  ((Proj.basicOpenIsoAway (grading Two.{u} R) t ht one_pos).commRingCatIsoToRingEquiv).bijective

/-- **`D₊(x₀) ≅ Spec R[t]`**: `R[t] → Γ(D₊(x₀))`, `t ↦ x₁ / x₀`, is bijective. -/
lemma bijective_eval₂Hom_lineCoord₀ :
    Function.Bijective
      (eval₂Hom (lineC R (lineChart₀ R))
        (fun _ : {j : Two.{u} // j ≠ Two.zero} ↦ lineCoord₀ R)) := by
  rw [eval₂Hom_lineCoord₀]
  exact (bijective_awayToSection R (X_mem_grading Two.zero)).comp (RingEquiv.bijective _)

/-- **`D₊(x₁) ≅ Spec R[s]`**: `R[s] → Γ(D₊(x₁))`, `s ↦ x₀ / x₁`, is bijective. -/
lemma bijective_eval₂Hom_lineCoord₁ :
    Function.Bijective
      (eval₂Hom (lineC R (lineChart₁ R))
        (fun _ : {j : Two.{u} // j ≠ Two.one} ↦ lineCoord₁ R)) := by
  rw [eval₂Hom_lineCoord₁]
  exact (bijective_awayToSection R (X_mem_grading Two.one)).comp (RingEquiv.bijective _)

section Pullback

variable {R} {Y : Scheme.{u}} (g : Y ⟶ Proj (grading Two.{u} R))

/-- The ring homomorphism `R → Γ(W, 𝒪_Y)` of a scheme `g : Y ⟶ ℙ¹_R` over `ℙ¹_R`. -/
def lineCOver (W : Y.Opens) : R →+* Γ(Y, W) :=
  ((g ≫ projToSpec Two.{u} R).appLE ⊤ W
    (le_top.trans_eq (g ≫ projToSpec Two.{u} R).preimage_top.symm)).hom.comp
      (Scheme.ΓSpecIso (.of R)).inv.hom

lemma app_lineC (V : (Proj (grading Two.{u} R)).Opens) (r : R) :
    g.app V (lineC R V r) = lineCOver g (g ⁻¹ᵁ V) r := by
  have h := congrArg (fun φ ↦ φ.hom ((Scheme.ΓSpecIso (.of R)).inv r))
    (Scheme.Hom.appLE_comp_appLE g (projToSpec Two.{u} R) ⊤ V (g ⁻¹ᵁ V)
      (le_top.trans_eq (projToSpec Two.{u} R).preimage_top.symm) le_rfl)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
  rw [Scheme.Hom.app_eq_appLE]
  exact h

/-- The chart homomorphism `R[t] → Γ(g⁻¹ D₊(x₀))`, `t ↦ g^*(x₁ / x₀)`, factors through
`Γ(D₊(x₀)) ≅ R[t]`. -/
lemma eval₂Hom_app_lineCoord₀ :
    eval₂Hom (lineCOver g (g ⁻¹ᵁ lineChart₀ R))
        (fun _ : {j : Two.{u} // j ≠ Two.zero} ↦ g.app _ (lineCoord₀ R)) =
      (g.app (lineChart₀ R)).hom.comp
        (eval₂Hom (lineC R (lineChart₀ R)) (fun _ ↦ lineCoord₀ R)) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
  · simp only [eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]
    exact (app_lineC g _ r).symm
  · simp only [eval₂Hom_X', RingHom.coe_comp, Function.comp_apply]

/-- The chart homomorphism `R[s] → Γ(g⁻¹ D₊(x₁))`, `s ↦ g^*(x₀ / x₁)`, factors through
`Γ(D₊(x₁)) ≅ R[s]`. -/
lemma eval₂Hom_app_lineCoord₁ :
    eval₂Hom (lineCOver g (g ⁻¹ᵁ lineChart₁ R))
        (fun _ : {j : Two.{u} // j ≠ Two.one} ↦ g.app _ (lineCoord₁ R)) =
      (g.app (lineChart₁ R)).hom.comp
        (eval₂Hom (lineC R (lineChart₁ R)) (fun _ ↦ lineCoord₁ R)) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
  · simp only [eval₂Hom_C, RingHom.coe_comp, Function.comp_apply]
    exact (app_lineC g _ r).symm
  · simp only [eval₂Hom_X', RingHom.coe_comp, Function.comp_apply]

lemma isAffineOpen_lineChart₀ : IsAffineOpen (lineChart₀ R) :=
  Proj.isAffineOpen_basicOpen _ _ (X_mem_grading Two.zero) one_pos

lemma isAffineOpen_lineChart₁ : IsAffineOpen (lineChart₁ R) :=
  Proj.isAffineOpen_basicOpen _ _ (X_mem_grading Two.one) one_pos

/-- For finite `g : Y ⟶ ℙ¹_R`, `R[t] → Γ(g⁻¹ D₊(x₀))`, `t ↦ g^*(x₁ / x₀)`, is finite. -/
theorem finite_eval₂Hom_app_lineCoord₀ [IsFinite g] :
    (eval₂Hom (lineCOver g (g ⁻¹ᵁ lineChart₀ R))
      (fun _ : {j : Two.{u} // j ≠ Two.zero} ↦ g.app _ (lineCoord₀ R))).Finite := by
  rw [eval₂Hom_app_lineCoord₀]
  exact (g.finite_app _ isAffineOpen_lineChart₀).comp
    (RingHom.Finite.of_surjective _ (bijective_eval₂Hom_lineCoord₀ R).2)

/-- For finite `g : Y ⟶ ℙ¹_R`, `R[s] → Γ(g⁻¹ D₊(x₁))`, `s ↦ g^*(x₀ / x₁)`, is finite. -/
theorem finite_eval₂Hom_app_lineCoord₁ [IsFinite g] :
    (eval₂Hom (lineCOver g (g ⁻¹ᵁ lineChart₁ R))
      (fun _ : {j : Two.{u} // j ≠ Two.one} ↦ g.app _ (lineCoord₁ R))).Finite := by
  rw [eval₂Hom_app_lineCoord₁]
  exact (g.finite_app _ isAffineOpen_lineChart₁).comp
    (RingHom.Finite.of_surjective _ (bijective_eval₂Hom_lineCoord₁ R).2)

/-- For flat affine `g : Y ⟶ ℙ¹_R`, `R[t] → Γ(g⁻¹ D₊(x₀))`, `t ↦ g^*(x₁ / x₀)`, is flat. -/
theorem flat_eval₂Hom_app_lineCoord₀ [IsAffineHom g] [Flat g] :
    (eval₂Hom (lineCOver g (g ⁻¹ᵁ lineChart₀ R))
      (fun _ : {j : Two.{u} // j ≠ Two.zero} ↦ g.app _ (lineCoord₀ R))).Flat := by
  rw [eval₂Hom_app_lineCoord₀]
  have h := HasRingHomProperty.appLE (P := @Flat) g ‹_› ⟨_, isAffineOpen_lineChart₀⟩
    ⟨_, isAffineOpen_lineChart₀.preimage g⟩ le_rfl
  rw [Scheme.Hom.appLE_eq_app] at h
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective (bijective_eval₂Hom_lineCoord₀ R)) h

/-- For flat affine `g : Y ⟶ ℙ¹_R`, `R[s] → Γ(g⁻¹ D₊(x₁))`, `s ↦ g^*(x₀ / x₁)`, is flat. -/
theorem flat_eval₂Hom_app_lineCoord₁ [IsAffineHom g] [Flat g] :
    (eval₂Hom (lineCOver g (g ⁻¹ᵁ lineChart₁ R))
      (fun _ : {j : Two.{u} // j ≠ Two.one} ↦ g.app _ (lineCoord₁ R))).Flat := by
  rw [eval₂Hom_app_lineCoord₁]
  have h := HasRingHomProperty.appLE (P := @Flat) g ‹_› ⟨_, isAffineOpen_lineChart₁⟩
    ⟨_, isAffineOpen_lineChart₁.preimage g⟩ le_rfl
  rw [Scheme.Hom.appLE_eq_app] at h
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective (bijective_eval₂Hom_lineCoord₁ R)) h

end Pullback

end AlgebraicGeometry.ProjectiveSpace

end
