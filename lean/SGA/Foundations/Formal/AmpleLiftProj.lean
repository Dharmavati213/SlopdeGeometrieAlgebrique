/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Projective.Dehomogenization
import SGA.Foundations.Projective.Segre

/-!
# Morphisms to `ℙ¹` given on two charts

Let `T` be a scheme with a ring homomorphism `c : R → Γ(T, 𝒪_T)`, covered by two open subsets
`U₀`, `U₁`, and let `τ ∈ Γ(U₀)`, `σ ∈ Γ(U₁)` with `τ σ = 1` on `U₀ ∩ U₁`, `τ` invertible only on
`U₀ ∩ U₁` (`D(τ) ⊆ U₁`) and likewise `D(σ) ⊆ U₀` (`AmpleLift.TwoChartData`). This defines a
morphism `T ⟶ ℙ¹_R = Proj R[x₀, x₁]`, `x ↦ (1 : τ(x)) = (σ(x) : 1)`
(`TwoChartData.toProj`), with `U₀`, `U₁` the inverse images of `D₊(x₀)`, `D₊(x₁)`
(`TwoChartData.toProj_preimage_basicOpen_zero`). On `U₀` it is given by the ring homomorphism
`R[x₀, x₁]_(x₀) = R[t] → Γ(U₀)`, `t ↦ τ` (`TwoChartData.awayToSection_comp_appLE_zero`). The
morphism is that of EGA II 4.2.3 for the line bundle trivialized on `U₀`, `U₁` with transition
function `τ` and its sections `(1, σ)`, `(τ, 1)`; it is built with
`Scheme.LineBundle.GradedHom.toProj`. It is natural in `T` (`TwoChartData.comp_toProj`) and
compatible with change of the base ring (`TwoChartData.toProj_comp_map`).

## References

* [EGA II, 4.2.3][EGA2]; [Hartshorne, II.7.1].
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpace

noncomputable section

namespace AlgebraicGeometry.AmpleLift

/-- The index type `{0, 1}` of the homogeneous coordinates of `ℙ¹`, in universe `u`. -/
abbrev Two : Type u := ULift.{u} (Fin 2)

/-- The index of `x₀`. -/
abbrev Two.zero : Two.{u} := ⟨0⟩

/-- The index of `x₁`. -/
abbrev Two.one : Two.{u} := ⟨1⟩

variable (T : Scheme.{u}) (R : Type u) [CommRing R]

/-- Data of a morphism `T ⟶ ℙ¹_R` given on two charts: a ring homomorphism `c : R → Γ(T, ⊤)`,
an open cover `U₀ ∪ U₁ = T`, and `τ ∈ Γ(U₀)`, `σ ∈ Γ(U₁)` with `τ σ = 1` on `U₀ ∩ U₁`,
`D(τ) ⊆ U₁` and `D(σ) ⊆ U₀`. -/
structure TwoChartData where
  /-- The structure homomorphism. -/
  c : R →+* Γ(T, ⊤)
  /-- The inverse image of `D₊(x₀)`. -/
  U₀ : T.Opens
  /-- The inverse image of `D₊(x₁)`. -/
  U₁ : T.Opens
  sup_eq_top : U₀ ⊔ U₁ = ⊤
  /-- The coordinate `x₁ / x₀` on `U₀`. -/
  τ : Γ(T, U₀)
  /-- The coordinate `x₀ / x₁` on `U₁`. -/
  σ : Γ(T, U₁)
  mul_eq_one : T.presheaf.map (homOfLE inf_le_left : U₀ ⊓ U₁ ⟶ U₀).op τ *
    T.presheaf.map (homOfLE inf_le_right : U₀ ⊓ U₁ ⟶ U₁).op σ = 1
  basicOpen_τ_le : T.basicOpen τ ≤ U₁
  basicOpen_σ_le : T.basicOpen σ ≤ U₀

omit [CommRing R] in
/-- Morphisms `V ⟶ Spec B` of the form `V ⟶ Spec Γ(V) ⟶ Spec B` determine the ring
homomorphism `B → Γ(V)`. -/
lemma eq_of_toSpecΓ_SpecMap_eq {V : T.Opens} {B : CommRingCat.{u}} {φ ψ : B ⟶ Γ(T, V)}
    (h : V.toSpecΓ ≫ Spec.map φ = V.toSpecΓ ≫ Spec.map ψ) : φ = ψ := by
  have := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop] at this
  have h' : (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso Γ(T, V)).hom =
      (Spec.map ψ).appTop ≫ (Scheme.ΓSpecIso Γ(T, V)).hom := by
    simpa only [Category.assoc, cancel_mono] using this
  rw [Scheme.ΓSpecIso_naturality, Scheme.ΓSpecIso_naturality] at h'
  exact (cancel_epi _).mp h'

namespace TwoChartData

variable {T R} (D : TwoChartData T R)

/-- `τ` restricted to `U₀ ∩ U₁`, a unit with inverse `σ`. -/
def unit₀₁ : Γ(T, D.U₀ ⊓ D.U₁)ˣ where
  val := T.presheaf.map (homOfLE inf_le_left : D.U₀ ⊓ D.U₁ ⟶ D.U₀).op D.τ
  inv := T.presheaf.map (homOfLE inf_le_right : D.U₀ ⊓ D.U₁ ⟶ D.U₁).op D.σ
  val_inv := D.mul_eq_one
  inv_val := by rw [mul_comm]; exact D.mul_eq_one

/-- `σ` restricted to `U₁ ∩ U₀`, a unit with inverse `τ`. -/
def unit₁₀ : Γ(T, D.U₁ ⊓ D.U₀)ˣ :=
  Units.map (T.presheaf.map (homOfLE (le_of_eq (inf_comm _ _)) : D.U₁ ⊓ D.U₀ ⟶ D.U₀ ⊓ D.U₁).op).hom
    D.unit₀₁⁻¹

/-- The trivializing cover. -/
def cover : ULift.{u} (Fin 2) → T.Opens := fun i ↦ ![D.U₀, D.U₁] i.down

/-- The transition functions: `g₀₁ = τ`, `g₁₀ = σ`. -/
def trans : ∀ i j : ULift.{u} (Fin 2), Γ(T, D.cover i ⊓ D.cover j)ˣ
  | ⟨0⟩, ⟨0⟩ => 1
  | ⟨0⟩, ⟨1⟩ => D.unit₀₁
  | ⟨1⟩, ⟨0⟩ => D.unit₁₀
  | ⟨1⟩, ⟨1⟩ => 1

omit [CommRing R] in
lemma res_res {U V W : T.Opens} (f : U ⟶ V) (g : V ⟶ W) (x : Γ(T, W)) :
    T.presheaf.map f.op (T.presheaf.map g.op x) = T.presheaf.map (f ≫ g).op x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma cocycle (i j k : ULift.{u} (Fin 2)) :
    T.presheaf.map (homOfLE (inf_le_left : D.cover i ⊓ D.cover j ⊓ D.cover k ≤
        D.cover i ⊓ D.cover j)).op (D.trans i j) *
      T.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        D.cover i ⊓ D.cover j ⊓ D.cover k ≤ D.cover j ⊓ D.cover k)).op (D.trans j k) =
      T.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        D.cover i ⊓ D.cover j ⊓ D.cover k ≤ D.cover i ⊓ D.cover k)).op (D.trans i k) := by
  have key : ∀ (V : T.Opens) (h₀ : V ≤ D.U₀) (h₁ : V ≤ D.U₁),
      T.presheaf.map (homOfLE h₀).op D.τ * T.presheaf.map (homOfLE h₁).op D.σ = 1 := by
    intro V h₀ h₁
    have := congrArg (T.presheaf.map (homOfLE (le_inf h₀ h₁)).op).hom D.mul_eq_one
    rw [map_mul, map_one] at this
    rw [← this, res_res, res_res]
    rfl
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  obtain ⟨k⟩ := k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [trans, Units.val_one, map_one, one_mul, mul_one, unit₁₀, Units.coe_map,
      MonoidHom.coe_coe, unit₀₁, Units.inv_mk, res_res]
  · exact (congrArg₂ (· * ·) (res_res _ _ _) (res_res _ _ _)).trans (key _ _ _)
  · exact (congrArg₂ (· * ·) (res_res _ _ _) (res_res _ _ _)).trans
      ((mul_comm _ _).trans (key _ _ _))

lemma iSup_cover : ⨆ i, D.cover i = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ ?_
  have hx : x ∈ D.U₀ ⊔ D.U₁ := D.sup_eq_top ▸ trivial
  rcases hx with hx | hx
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨0⟩, hx⟩
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨1⟩, hx⟩

/-- The line bundle trivialized on `U₀`, `U₁` with transition function `g₀₁ = τ`. -/
def lineBundle : T.LineBundle where
  ι := ULift.{u} (Fin 2)
  U := D.cover
  iSup_eq_top := D.iSup_cover
  g := D.trans
  cocycle := D.cocycle

/-- The structure homomorphism on `U₀`. -/
def c₀ : R →+* Γ(T, D.U₀) := (T.presheaf.map (homOfLE le_top : D.U₀ ⟶ ⊤).op).hom.comp D.c

/-- The structure homomorphism on `U₁`. -/
def c₁ : R →+* Γ(T, D.U₁) := (T.presheaf.map (homOfLE le_top : D.U₁ ⟶ ⊤).op).hom.comp D.c

/-- The homomorphisms `R[x₀, x₁] → Γ(U₀)`, `(x₀, x₁) ↦ (1, τ)` and `R[x₀, x₁] → Γ(U₁)`,
`(x₀, x₁) ↦ (σ, 1)`. -/
def app : ∀ i : ULift.{u} (Fin 2), MvPolynomial Two.{u} R →+* Γ(T, D.cover i)
  | ⟨0⟩ => eval₂Hom D.c₀ (fun i ↦ ![1, D.τ] i.down)
  | ⟨1⟩ => eval₂Hom D.c₁ (fun i ↦ ![D.σ, 1] i.down)

lemma res_comp_c₀_eq {V : T.Opens} (h₀ : V ≤ D.U₀) (h₁ : V ≤ D.U₁) :
    (T.presheaf.map (homOfLE h₀).op).hom.comp D.c₀ =
      (T.presheaf.map (homOfLE h₁).op).hom.comp D.c₁ := by
  ext r
  simp only [c₀, c₁, RingHom.coe_comp, Function.comp_apply]
  rw [res_res, res_res]
  rfl

lemma app_mem_zero_one (d : ℕ) (P : MvPolynomial Two.{u} R) (hh : P.IsHomogeneous d) :
    T.presheaf.map (homOfLE (inf_le_left : D.U₀ ⊓ D.U₁ ≤ D.U₀)).op
        (eval₂Hom D.c₀ (fun i ↦ ![1, D.τ] i.down) P) =
      (T.presheaf.map (homOfLE (inf_le_left : D.U₀ ⊓ D.U₁ ≤ D.U₀)).op D.τ) ^ d *
        T.presheaf.map (homOfLE (inf_le_right : D.U₀ ⊓ D.U₁ ≤ D.U₁)).op
          (eval₂Hom D.c₁ (fun i ↦ ![D.σ, 1] i.down) P) := by
  rw [coe_eval₂Hom, coe_eval₂Hom, eval₂_comp_left, eval₂_comp_left, ← hh.eval₂_mul_left]
  congr 1
  · exact D.res_comp_c₀_eq _ _
  · funext ⟨i⟩
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Function.comp_apply, Matrix.cons_val_zero, map_one]
      exact D.mul_eq_one.symm
    · simp [Function.comp_apply, Matrix.cons_val_one, map_one, mul_one]

lemma app_mem_one_zero (d : ℕ) (P : MvPolynomial Two.{u} R) (hh : P.IsHomogeneous d) :
    T.presheaf.map (homOfLE (inf_le_left : D.U₁ ⊓ D.U₀ ≤ D.U₁)).op
        (eval₂Hom D.c₁ (fun i ↦ ![D.σ, 1] i.down) P) =
      (T.presheaf.map (homOfLE (le_of_eq (inf_comm _ _)) : D.U₁ ⊓ D.U₀ ⟶ D.U₀ ⊓ D.U₁).op
        (T.presheaf.map (homOfLE (inf_le_right : D.U₀ ⊓ D.U₁ ≤ D.U₁)).op D.σ)) ^ d *
        T.presheaf.map (homOfLE (inf_le_right : D.U₁ ⊓ D.U₀ ≤ D.U₀)).op
          (eval₂Hom D.c₀ (fun i ↦ ![1, D.τ] i.down) P) := by
  rw [coe_eval₂Hom, coe_eval₂Hom, eval₂_comp_left, eval₂_comp_left, ← hh.eval₂_mul_left]
  congr 1
  · exact (D.res_comp_c₀_eq _ _).symm
  · funext ⟨i⟩
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Function.comp_apply, Matrix.cons_val_zero,
        map_one, mul_one]
      rw [res_res]
      rfl
    · simp only [Fin.mk_one, Fin.isValue, Function.comp_apply, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, map_one]
      have := congrArg (T.presheaf.map (homOfLE (le_of_eq (inf_comm _ _)) :
        D.U₁ ⊓ D.U₀ ⟶ D.U₀ ⊓ D.U₁).op).hom D.mul_eq_one
      rw [map_mul, map_one] at this
      rw [← this, mul_comm, res_res, res_res]
      rfl

lemma app_mem (a b : ULift.{u} (Fin 2)) (d : ℕ) (P : MvPolynomial Two.{u} R)
    (hP : P ∈ grading Two.{u} R d) :
    T.presheaf.map (homOfLE (inf_le_left : D.cover a ⊓ D.cover b ≤ D.cover a)).op (D.app a P) =
      (D.trans a b : Γ(T, D.cover a ⊓ D.cover b)) ^ d *
        T.presheaf.map (homOfLE (inf_le_right : D.cover a ⊓ D.cover b ≤ D.cover b)).op
          (D.app b P) := by
  have hh : P.IsHomogeneous d := mem_grading.mp hP
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  fin_cases a <;> fin_cases b
  · simp only [trans, Units.val_one, one_pow, one_mul]
  · exact D.app_mem_zero_one d P hh
  · exact D.app_mem_one_zero d P hh
  · simp only [trans, Units.val_one, one_pow, one_mul]

/-- The graded homomorphism `R[x₀, x₁] → ⊕ₙ Γ(T, L^{⊗n})`, `x₀ ↦ (1, σ)`, `x₁ ↦ (τ, 1)`. -/
def gradedHom : D.lineBundle.GradedHom (grading Two.{u} R) where
  app := D.app
  app_mem := D.app_mem

@[simp]
lemma gradedHom_app (i : ULift.{u} (Fin 2)) : D.gradedHom.app i = D.app i := rfl

lemma app_zero_X_zero : D.app ⟨0⟩ (X Two.zero) = 1 := (eval₂Hom_X' _ _ _).trans rfl

lemma app_zero_X_one : D.app ⟨0⟩ (X Two.one) = D.τ := (eval₂Hom_X' _ _ _).trans rfl

lemma app_one_X_zero : D.app ⟨1⟩ (X Two.zero) = D.σ := (eval₂Hom_X' _ _ _).trans rfl

lemma app_zero_C (r : R) : D.app ⟨0⟩ (C r) = D.c₀ r := eval₂Hom_C _ _ _

lemma app_one_C (r : R) : D.app ⟨1⟩ (C r) = D.c₁ r := eval₂Hom_C _ _ _

lemma app_one_X_one : D.app ⟨1⟩ (X Two.one) = 1 := (eval₂Hom_X' _ _ _).trans rfl

lemma mem_nonvanishingLocus_X_zero (x : T) :
    x ∈ D.lineBundle.nonvanishingLocus (D.gradedHom.sec (X_mem_grading Two.zero)) ↔ x ∈ D.U₀ := by
  rw [Scheme.LineBundle.mem_nonvanishingLocus]
  constructor
  · rintro ⟨⟨i⟩, hi⟩
    fin_cases i
    · change x ∈ T.basicOpen (D.app ⟨0⟩ (X Two.zero)) at hi
      rw [app_zero_X_zero, Scheme.basicOpen_one] at hi
      exact hi
    · change x ∈ T.basicOpen (D.app ⟨1⟩ (X Two.zero)) at hi
      rw [app_one_X_zero] at hi
      exact D.basicOpen_σ_le hi
  · intro hx
    refine ⟨⟨0⟩, ?_⟩
    change x ∈ T.basicOpen (D.app ⟨0⟩ (X Two.zero))
    rw [app_zero_X_zero, Scheme.basicOpen_one]
    exact hx

lemma mem_nonvanishingLocus_X_one (x : T) :
    x ∈ D.lineBundle.nonvanishingLocus (D.gradedHom.sec (X_mem_grading Two.one)) ↔ x ∈ D.U₁ := by
  rw [Scheme.LineBundle.mem_nonvanishingLocus]
  constructor
  · rintro ⟨⟨i⟩, hi⟩
    fin_cases i
    · change x ∈ T.basicOpen (D.app ⟨0⟩ (X Two.one)) at hi
      rw [app_zero_X_one] at hi
      exact D.basicOpen_τ_le hi
    · change x ∈ T.basicOpen (D.app ⟨1⟩ (X Two.one)) at hi
      rw [app_one_X_one, Scheme.basicOpen_one] at hi
      exact hi
  · intro hx
    refine ⟨⟨1⟩, ?_⟩
    change x ∈ T.basicOpen (D.app ⟨1⟩ (X Two.one))
    rw [app_one_X_one, Scheme.basicOpen_one]
    exact hx

lemma exists_mem_nonvanishingLocus (x : T) :
    ∃ (d : ℕ) (t : MvPolynomial Two.{u} R) (_ : 0 < d) (ht : t ∈ grading Two.{u} R d),
      x ∈ D.lineBundle.nonvanishingLocus (D.gradedHom.sec ht) := by
  have hx : x ∈ D.U₀ ⊔ D.U₁ := D.sup_eq_top ▸ trivial
  rcases hx with hx | hx
  · exact ⟨1, X Two.zero, one_pos, X_mem_grading Two.zero,
      (D.mem_nonvanishingLocus_X_zero x).mpr hx⟩
  · exact ⟨1, X Two.one, one_pos, X_mem_grading Two.one,
      (D.mem_nonvanishingLocus_X_one x).mpr hx⟩

/-- **The morphism `T ⟶ ℙ¹_R = Proj R[x₀, x₁]` defined by two charts** (EGA II 4.2.3):
`x ↦ (1 : τ(x))` on `U₀` and `x ↦ (σ(x) : 1)` on `U₁`. -/
def toProj : T ⟶ Proj (grading Two.{u} R) :=
  D.gradedHom.toProj D.exists_mem_nonvanishingLocus

lemma toProj_preimage_basicOpen_zero :
    D.toProj ⁻¹ᵁ Proj.basicOpen (grading Two.{u} R) (X Two.zero) = D.U₀ := by
  rw [toProj,
    Scheme.LineBundle.GradedHom.toProj_preimage_basicOpen _ _ (X_mem_grading Two.zero) one_pos]
  ext x
  exact D.mem_nonvanishingLocus_X_zero x

lemma toProj_preimage_basicOpen_one :
    D.toProj ⁻¹ᵁ Proj.basicOpen (grading Two.{u} R) (X Two.one) = D.U₁ := by
  rw [toProj,
    Scheme.LineBundle.GradedHom.toProj_preimage_basicOpen _ _ (X_mem_grading Two.one) one_pos]
  ext x
  exact D.mem_nonvanishingLocus_X_one x

/-- The chart `(U₀, x₀)` of `toProj`. -/
def chartIndex₀ :
    Scheme.LineBundle.GradedHom.ChartIndex (L := D.lineBundle) (𝒜 := grading Two.{u} R) :=
  ⟨⟨0⟩, 1, X Two.zero, one_pos, X_mem_grading Two.zero⟩

/-- The chart `(U₁, x₁)` of `toProj`. -/
def chartIndex₁ :
    Scheme.LineBundle.GradedHom.ChartIndex (L := D.lineBundle) (𝒜 := grading Two.{u} R) :=
  ⟨⟨1⟩, 1, X Two.one, one_pos, X_mem_grading Two.one⟩

lemma chartOpen₀ : D.gradedHom.chartOpen D.chartIndex₀ = D.U₀ := by
  change T.basicOpen (D.app ⟨0⟩ (X Two.zero)) = D.U₀
  rw [app_zero_X_zero, Scheme.basicOpen_one]
  rfl

lemma chartOpen₁ : D.gradedHom.chartOpen D.chartIndex₁ = D.U₁ := by
  change T.basicOpen (D.app ⟨1⟩ (X Two.one)) = D.U₁
  rw [app_one_X_one, Scheme.basicOpen_one]
  rfl

/-- On the chart `(U, xᵢ)`, `toProj` is given by `awayToSections`. -/
lemma awayToSection_comp_appLE_chartOpen (j : Two.{u}) (a : ULift.{u} (Fin 2))
    (h : T.basicOpen (D.app a (X j)) ≤ D.toProj ⁻¹ᵁ Proj.basicOpen (grading Two.{u} R) (X j)) :
    Proj.awayToSection (grading Two.{u} R) (X j) ≫
        D.toProj.appLE (Proj.basicOpen _ (X j)) (T.basicOpen (D.app a (X j))) h =
      CommRingCat.ofHom (Proj.awayToSections (grading Two.{u} R) (D.app a) (X j)) := by
  let k : Scheme.LineBundle.GradedHom.ChartIndex (L := D.lineBundle) (𝒜 := grading Two.{u} R) :=
    ⟨a, 1, X j, one_pos, X_mem_grading j⟩
  have h1 := Scheme.LineBundle.GradedHom.ι_toProj D.gradedHom D.exists_mem_nonvanishingLocus k
  have h2 := Proj.ι_comp_eq (grading Two.{u} R) D.toProj (X_mem_grading j) one_pos _ h
  change (T.basicOpen (D.app a (X j))).ι ≫ D.toProj = _ at h1
  rw [h2] at h1
  change _ = (T.basicOpen (D.app a (X j))).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (Proj.awayToSections _ (D.app a) (X j))) ≫
      Proj.awayι _ (X j) (X_mem_grading j) one_pos at h1
  rw [← Category.assoc, ← Category.assoc, cancel_mono] at h1
  exact eq_of_toSpecΓ_SpecMap_eq T h1

omit [CommRing R] in
lemma res_self {U V : T.Opens} (h₁ : U ≤ V) (h₂ : V ≤ U) (x : Γ(T, U)) :
    T.presheaf.map (homOfLE h₁).op (T.presheaf.map (homOfLE h₂).op x) = x := by
  rw [res_res, Subsingleton.elim (homOfLE h₁ ≫ homOfLE h₂) (𝟙 U), op_id,
    CategoryTheory.Functor.map_id]
  rfl

lemma awayC_eq_mk (i : Two.{u}) (r : R) :
    awayC (X i : MvPolynomial Two.{u} R) r =
      Away.mk (grading Two.{u} R) (X_mem_grading i) 0 (C r)
        (by rw [zero_smul]; exact mem_grading.mpr (isHomogeneous_C _ r)) := by
  rw [HomogeneousLocalization.ext_iff_val, val_awayC, Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.eq_mk'_iff_mul_eq]
  simp

/-- `awayToSections` on the chart `(U₀, x₀)`, composed with `R[t] ≅ R[x₀, x₁]_(x₀)`, is
`t ↦ τ` (after restriction to `U₀`). -/
lemma res_comp_awayToSections_zero (h : D.U₀ ≤ T.basicOpen (D.app ⟨0⟩ (X Two.zero))) :
    (T.presheaf.map (homOfLE h).op).hom.comp
      ((Proj.awayToSections (grading Two.{u} R) (D.app ⟨0⟩) (X Two.zero)).comp
        (awayHomogenize Two.zero (rfl : (X Two.zero : MvPolynomial Two.{u} R) = X Two.zero))) =
      eval₂Hom D.c₀ (fun _ ↦ D.τ) := by
  have hb : T.basicOpen (D.app ⟨0⟩ (X Two.zero)) ≤ D.U₀ := T.basicOpen_le _
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, awayHomogenize, eval₂Hom_C, coe_eval₂Hom,
      eval₂_C]
    have hmk := Proj.awayToSections_mk (D.app ⟨0⟩) (X_mem_grading Two.zero) 0 (C r)
      (by rw [zero_smul]; exact mem_grading.mpr (isHomogeneous_C _ r))
    rw [pow_zero, mul_one] at hmk
    rw [awayC_eq_mk, hmk, Proj.resBasicOpen_apply, app_zero_C]
    exact res_self h hb (D.c₀ r)
  · obtain ⟨⟨j⟩, hj⟩ := j
    fin_cases j
    · exact absurd rfl hj
    · simp only [RingHom.coe_comp, Function.comp_apply, awayHomogenize, eval₂Hom_X', coe_eval₂Hom,
        eval₂_X]
      have hmk := Proj.awayToSections_mk (D.app ⟨0⟩) (X_mem_grading Two.zero) 1 (X Two.one)
        (by simpa using X_mem_grading Two.one)
      have h1 : (T.presheaf.map (homOfLE (T.basicOpen_le (D.app ⟨0⟩ (X Two.zero)))).op)
          (D.app ⟨0⟩ (X Two.zero)) = 1 :=
        (congrArg (T.presheaf.map (homOfLE (T.basicOpen_le (D.app ⟨0⟩ (X Two.zero)))).op).hom
          D.app_zero_X_zero).trans (map_one _)
      have h2 : (T.presheaf.map (homOfLE (T.basicOpen_le (D.app ⟨0⟩ (X Two.zero)))).op)
          (D.app ⟨0⟩ (X Two.one)) = (T.presheaf.map (homOfLE hb).op) D.τ :=
        congrArg (T.presheaf.map (homOfLE (T.basicOpen_le (D.app ⟨0⟩ (X Two.zero)))).op).hom
          D.app_zero_X_one
      rw [pow_one, Proj.resBasicOpen_apply, Proj.resBasicOpen_apply] at hmk
      rw [h1, mul_one, h2] at hmk
      exact (congrArg (T.presheaf.map (homOfLE h).op).hom hmk).trans (res_self h hb D.τ)

/-- **`toProj` on the chart `U₀`**: the ring homomorphism `R[x₀, x₁]_(x₀) → Γ(U₀)` is
`R[t] → Γ(U₀)`, `t ↦ τ`, via the dehomogenization `R[x₀, x₁]_(x₀) ≅ R[t]` (`awayEquiv`). -/
lemma awayToSection_comp_appLE_zero :
    Proj.awayToSection (grading Two.{u} R) (X Two.zero) ≫
        D.toProj.appLE (Proj.basicOpen _ (X Two.zero)) D.U₀ D.toProj_preimage_basicOpen_zero.ge =
      CommRingCat.ofHom ((eval₂Hom D.c₀ fun _ ↦ D.τ).comp
        (awayEquiv (t := (X Two.zero : MvPolynomial Two.{u} R)) Two.zero rfl).toRingHom) := by
  have hle : D.U₀ ≤ T.basicOpen (D.app ⟨0⟩ (X Two.zero)) := D.chartOpen₀.ge
  have he : T.basicOpen (D.app ⟨0⟩ (X Two.zero)) ≤
      D.toProj ⁻¹ᵁ Proj.basicOpen (grading Two.{u} R) (X Two.zero) :=
    D.chartOpen₀.le.trans D.toProj_preimage_basicOpen_zero.ge
  rw [← Scheme.Hom.appLE_map D.toProj he (homOfLE hle).op, ← Category.assoc,
    awayToSection_comp_appLE_chartOpen]
  ext y
  obtain ⟨p, rfl⟩ := (awayEquiv Two.zero
    (rfl : (X Two.zero : MvPolynomial Two.{u} R) = X Two.zero)).symm.surjective y
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun (D.res_comp_awayToSections_zero hle) p

/-- `awayToSections` on the chart `(U₁, x₁)`, composed with `R[s] ≅ R[x₀, x₁]_(x₁)`, is
`s ↦ σ` (after restriction to `U₁`). -/
lemma res_comp_awayToSections_one (h : D.U₁ ≤ T.basicOpen (D.app ⟨1⟩ (X Two.one))) :
    (T.presheaf.map (homOfLE h).op).hom.comp
      ((Proj.awayToSections (grading Two.{u} R) (D.app ⟨1⟩) (X Two.one)).comp
        (awayHomogenize Two.one (rfl : (X Two.one : MvPolynomial Two.{u} R) = X Two.one))) =
      eval₂Hom D.c₁ (fun _ ↦ D.σ) := by
  have hb : T.basicOpen (D.app ⟨1⟩ (X Two.one)) ≤ D.U₁ := T.basicOpen_le _
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun j ↦ ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, awayHomogenize, eval₂Hom_C, coe_eval₂Hom,
      eval₂_C]
    have hmk := Proj.awayToSections_mk (D.app ⟨1⟩) (X_mem_grading Two.one) 0 (C r)
      (by rw [zero_smul]; exact mem_grading.mpr (isHomogeneous_C _ r))
    rw [pow_zero, mul_one] at hmk
    rw [awayC_eq_mk, hmk, Proj.resBasicOpen_apply, app_one_C]
    exact res_self h hb (D.c₁ r)
  · obtain ⟨⟨j⟩, hj⟩ := j
    fin_cases j
    swap
    · exact absurd rfl hj
    · simp only [RingHom.coe_comp, Function.comp_apply, awayHomogenize, eval₂Hom_X', coe_eval₂Hom,
        eval₂_X]
      have hmk := Proj.awayToSections_mk (D.app ⟨1⟩) (X_mem_grading Two.one) 1 (X Two.zero)
        (by simpa using X_mem_grading Two.zero)
      have h1 : (T.presheaf.map (homOfLE (T.basicOpen_le (D.app ⟨1⟩ (X Two.one)))).op)
          (D.app ⟨1⟩ (X Two.one)) = 1 :=
        (congrArg (T.presheaf.map (homOfLE (T.basicOpen_le (D.app ⟨1⟩ (X Two.one)))).op).hom
          D.app_one_X_one).trans (map_one _)
      have h2 : (T.presheaf.map (homOfLE (T.basicOpen_le (D.app ⟨1⟩ (X Two.one)))).op)
          (D.app ⟨1⟩ (X Two.zero)) = (T.presheaf.map (homOfLE hb).op) D.σ :=
        congrArg (T.presheaf.map (homOfLE (T.basicOpen_le (D.app ⟨1⟩ (X Two.one)))).op).hom
          D.app_one_X_zero
      rw [pow_one, Proj.resBasicOpen_apply, Proj.resBasicOpen_apply] at hmk
      rw [h1, mul_one, h2] at hmk
      exact (congrArg (T.presheaf.map (homOfLE h).op).hom hmk).trans (res_self h hb D.σ)

/-- **`toProj` on the chart `U₁`**: the ring homomorphism `R[x₀, x₁]_(x₁) → Γ(U₁)` is
`R[s] → Γ(U₁)`, `s ↦ σ`, via the dehomogenization `R[x₀, x₁]_(x₁) ≅ R[s]` (`awayEquiv`). -/
lemma awayToSection_comp_appLE_one :
    Proj.awayToSection (grading Two.{u} R) (X Two.one) ≫
        D.toProj.appLE (Proj.basicOpen _ (X Two.one)) D.U₁ D.toProj_preimage_basicOpen_one.ge =
      CommRingCat.ofHom ((eval₂Hom D.c₁ fun _ ↦ D.σ).comp
        (awayEquiv (t := (X Two.one : MvPolynomial Two.{u} R)) Two.one rfl).toRingHom) := by
  have hle : D.U₁ ≤ T.basicOpen (D.app ⟨1⟩ (X Two.one)) := D.chartOpen₁.ge
  have he : T.basicOpen (D.app ⟨1⟩ (X Two.one)) ≤
      D.toProj ⁻¹ᵁ Proj.basicOpen (grading Two.{u} R) (X Two.one) :=
    D.chartOpen₁.le.trans D.toProj_preimage_basicOpen_one.ge
  rw [← Scheme.Hom.appLE_map D.toProj he (homOfLE hle).op, ← Category.assoc,
    awayToSection_comp_appLE_chartOpen]
  ext y
  obtain ⟨p, rfl⟩ := (awayEquiv Two.one
    (rfl : (X Two.one : MvPolynomial Two.{u} R) = X Two.one)).symm.surjective y
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun (D.res_comp_awayToSections_one hle) p

/-- `toProj` on `U₀`, as a morphism `U₀ ⟶ Spec R[x₀, x₁]_(x₀) ⟶ ℙ¹`. -/
lemma ι_toProj_zero : D.U₀.ι ≫ D.toProj = D.U₀.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom ((eval₂Hom D.c₀ fun _ ↦ D.τ).comp
      (awayEquiv (t := (X Two.zero : MvPolynomial Two.{u} R)) Two.zero rfl).toRingHom)) ≫
      Proj.awayι _ (X Two.zero) (X_mem_grading Two.zero) one_pos := by
  rw [Proj.ι_comp_eq _ D.toProj (X_mem_grading Two.zero) one_pos D.U₀
    D.toProj_preimage_basicOpen_zero.ge, awayToSection_comp_appLE_zero]

/-- `toProj` on `U₁`, as a morphism `U₁ ⟶ Spec R[x₀, x₁]_(x₁) ⟶ ℙ¹`. -/
lemma ι_toProj_one : D.U₁.ι ≫ D.toProj = D.U₁.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom ((eval₂Hom D.c₁ fun _ ↦ D.σ).comp
      (awayEquiv (t := (X Two.one : MvPolynomial Two.{u} R)) Two.one rfl).toRingHom)) ≫
      Proj.awayι _ (X Two.one) (X_mem_grading Two.one) one_pos := by
  rw [Proj.ι_comp_eq _ D.toProj (X_mem_grading Two.one) one_pos D.U₁
    D.toProj_preimage_basicOpen_one.ge, awayToSection_comp_appLE_one]

lemma awayC_comp_zero :
    ((eval₂Hom D.c₀ fun _ ↦ D.τ).comp
      (awayEquiv (t := (X Two.zero : MvPolynomial Two.{u} R)) Two.zero rfl).toRingHom).comp
        (awayC (X Two.zero)) = D.c₀ := by
  ext r
  simp

lemma awayC_comp_one :
    ((eval₂Hom D.c₁ fun _ ↦ D.σ).comp
      (awayEquiv (t := (X Two.one : MvPolynomial Two.{u} R)) Two.one rfl).toRingHom).comp
        (awayC (X Two.one)) = D.c₁ := by
  ext r
  simp

/-- `toProj` is a morphism over `Spec R`. -/
lemma toProj_projToSpec :
    D.toProj ≫ projToSpec Two.{u} R = T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom D.c) := by
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  have hx : x ∈ D.U₀ ⊔ D.U₁ := D.sup_eq_top ▸ trivial
  rcases hx with hx | hx
  · refine ⟨D.U₀, hx, ?_⟩
    rw [reassoc_of% D.ι_toProj_zero, awayι_projToSpec, ← Spec.map_comp,
      ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc, ← Spec.map_comp]
    congr 2
    rw [← CommRingCat.ofHom_comp, D.awayC_comp_zero]
    rfl
  · refine ⟨D.U₁, hx, ?_⟩
    rw [reassoc_of% D.ι_toProj_one, awayι_projToSpec, ← Spec.map_comp,
      ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top_assoc, ← Spec.map_comp]
    congr 2
    rw [← CommRingCat.ofHom_comp, D.awayC_comp_one]
    rfl

section Naturality

variable {T' : Scheme.{u}} (h : T' ⟶ T) (D' : TwoChartData T' R)
  (hU₀ : D'.U₀ ≤ h ⁻¹ᵁ D.U₀) (hU₁ : D'.U₁ ≤ h ⁻¹ᵁ D.U₁)
  (hc : ∀ r, D'.c r = h.appTop (D.c r))

include hc in
lemma c₀_eq (r : R) : D'.c₀ r = h.appLE D.U₀ D'.U₀ hU₀ (D.c₀ r) := by
  calc D'.c₀ r = h.appLE ⊤ D'.U₀ (by simp) (D.c r) := by
        rw [c₀, RingHom.comp_apply, hc]
        rfl
    _ = _ := by
        rw [c₀, RingHom.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

include hc in
lemma c₁_eq (r : R) : D'.c₁ r = h.appLE D.U₁ D'.U₁ hU₁ (D.c₁ r) := by
  calc D'.c₁ r = h.appLE ⊤ D'.U₁ (by simp) (D.c r) := by
        rw [c₁, RingHom.comp_apply, hc]
        rfl
    _ = _ := by
        rw [c₁, RingHom.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

include hc in
/-- **Naturality of `toProj`**: if `D'` is the inverse image of `D` under `h : T' ⟶ T` (with
smaller charts allowed), then `h ≫ D.toProj = D'.toProj`. -/
lemma comp_toProj (hτ : D'.τ = h.appLE D.U₀ D'.U₀ hU₀ D.τ)
    (hσ : D'.σ = h.appLE D.U₁ D'.U₁ hU₁ D.σ) : h ≫ D.toProj = D'.toProj := by
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  have hx : x ∈ D'.U₀ ⊔ D'.U₁ := D'.sup_eq_top ▸ trivial
  rcases hx with hx | hx
  · refine ⟨D'.U₀, hx, ?_⟩
    rw [D'.ι_toProj_zero, ← Scheme.Hom.resLE_comp_ι_assoc h hU₀, D.ι_toProj_zero,
      ← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, ← Spec.map_comp_assoc]
    congr 3
    ext y
    obtain ⟨p, rfl⟩ := (awayEquiv (t := (X Two.zero : MvPolynomial Two.{u} R)) Two.zero
      rfl).symm.surjective y
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    induction p using MvPolynomial.induction_on with
    | C r => simp [D.c₀_eq h D' hU₀ hc]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp => simp only [map_mul, hp, eval₂Hom_X', hτ]
  · refine ⟨D'.U₁, hx, ?_⟩
    rw [D'.ι_toProj_one, ← Scheme.Hom.resLE_comp_ι_assoc h hU₁, D.ι_toProj_one,
      ← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, ← Spec.map_comp_assoc]
    congr 3
    ext y
    obtain ⟨p, rfl⟩ := (awayEquiv (t := (X Two.one : MvPolynomial Two.{u} R)) Two.one
      rfl).symm.surjective y
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    induction p using MvPolynomial.induction_on with
    | C r => simp [D.c₁_eq h D' hU₁ hc]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp => simp only [map_mul, hp, eval₂Hom_X', hσ]

end Naturality

/-- `toProj` on `U₀`, for an element `t` equal to `x₀` (to avoid transport). -/
lemma awayToSection_comp_appLE_zero' (t : MvPolynomial Two.{u} R) (ht : t = X Two.zero)
    (h : D.U₀ ≤ D.toProj ⁻¹ᵁ Proj.basicOpen (grading Two.{u} R) t) :
    Proj.awayToSection (grading Two.{u} R) t ≫ D.toProj.appLE (Proj.basicOpen _ t) D.U₀ h =
      CommRingCat.ofHom ((eval₂Hom D.c₀ fun _ ↦ D.τ).comp (awayEquiv Two.zero ht).toRingHom) := by
  subst ht
  exact D.awayToSection_comp_appLE_zero

/-- `toProj` on `U₁`, for an element `t` equal to `x₁` (to avoid transport). -/
lemma awayToSection_comp_appLE_one' (t : MvPolynomial Two.{u} R) (ht : t = X Two.one)
    (h : D.U₁ ≤ D.toProj ⁻¹ᵁ Proj.basicOpen (grading Two.{u} R) t) :
    Proj.awayToSection (grading Two.{u} R) t ≫ D.toProj.appLE (Proj.basicOpen _ t) D.U₁ h =
      CommRingCat.ofHom ((eval₂Hom D.c₁ fun _ ↦ D.σ).comp (awayEquiv Two.one ht).toRingHom) := by
  subst ht
  exact D.awayToSection_comp_appLE_one

section BaseChange

variable {R' : Type u} [CommRing R'] (φ : R' →+* R)

/-- The same chart data, over `R'` via `φ : R' → R`. -/
def comap : TwoChartData T R' where
  c := D.c.comp φ
  U₀ := D.U₀
  U₁ := D.U₁
  sup_eq_top := D.sup_eq_top
  τ := D.τ
  σ := D.σ
  mul_eq_one := D.mul_eq_one
  basicOpen_τ_le := D.basicOpen_τ_le
  basicOpen_σ_le := D.basicOpen_σ_le

lemma comap_c₀ : (D.comap φ).c₀ = D.c₀.comp φ := rfl

lemma comap_c₁ : (D.comap φ).c₁ = D.c₁.comp φ := rfl

/-- **Base change of `toProj`**: composed with `ℙ¹_R ⟶ ℙ¹_{R'}`, `toProj` is the morphism of the
same chart data over `R'`. -/
lemma toProj_comp_map :
    D.toProj ≫ Proj.map (gradingMap Two.{u} φ) (irrelevant_le_map φ) = (D.comap φ).toProj := by
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  have hx : x ∈ D.U₀ ⊔ D.U₁ := D.sup_eq_top ▸ trivial
  rcases hx with hx | hx
  · refine ⟨D.U₀, hx, ?_⟩
    have h₀ : D.U₀ ≤ (D.toProj ≫ Proj.map (gradingMap Two.{u} φ) (irrelevant_le_map φ)) ⁻¹ᵁ
        Proj.basicOpen (grading Two.{u} R') (X Two.zero) := by
      rw [Scheme.Hom.comp_preimage, Proj.map_preimage_basicOpen, gradingMap_apply, map_X]
      exact D.toProj_preimage_basicOpen_zero.ge
    have h₀' : D.U₀ ≤ D.toProj ⁻¹ᵁ Proj.basicOpen (grading Two.{u} R)
        (gradingMap Two.{u} φ (X Two.zero)) := by
      rw [gradingMap_apply, map_X]
      exact D.toProj_preimage_basicOpen_zero.ge
    rw [Proj.ι_comp_eq _ _ (X_mem_grading Two.zero) one_pos D.U₀ h₀,
      show D.U₀.ι ≫ (D.comap φ).toProj = _ from (D.comap φ).ι_toProj_zero,
      ← Scheme.Hom.appLE_comp_appLE _ _ _ (Proj.basicOpen _ (gradingMap Two.{u} φ (X Two.zero)))
        _ le_rfl h₀', Proj.awayToSection_comp_appLE_assoc _ _ (X_mem_grading Two.zero),
      D.awayToSection_comp_appLE_zero' _ (map_X_eq Two.zero φ)]
    congr 3
    ext y
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coe_eval₂Hom]
    rw [awayEquiv_awayMap, eval₂_map]
    rfl
  · refine ⟨D.U₁, hx, ?_⟩
    have h₁ : D.U₁ ≤ (D.toProj ≫ Proj.map (gradingMap Two.{u} φ) (irrelevant_le_map φ)) ⁻¹ᵁ
        Proj.basicOpen (grading Two.{u} R') (X Two.one) := by
      rw [Scheme.Hom.comp_preimage, Proj.map_preimage_basicOpen, gradingMap_apply, map_X]
      exact D.toProj_preimage_basicOpen_one.ge
    have h₁' : D.U₁ ≤ D.toProj ⁻¹ᵁ Proj.basicOpen (grading Two.{u} R)
        (gradingMap Two.{u} φ (X Two.one)) := by
      rw [gradingMap_apply, map_X]
      exact D.toProj_preimage_basicOpen_one.ge
    rw [Proj.ι_comp_eq _ _ (X_mem_grading Two.one) one_pos D.U₁ h₁,
      show D.U₁.ι ≫ (D.comap φ).toProj = _ from (D.comap φ).ι_toProj_one,
      ← Scheme.Hom.appLE_comp_appLE _ _ _ (Proj.basicOpen _ (gradingMap Two.{u} φ (X Two.one)))
        _ le_rfl h₁', Proj.awayToSection_comp_appLE_assoc _ _ (X_mem_grading Two.one),
      D.awayToSection_comp_appLE_one' _ (map_X_eq Two.one φ)]
    congr 3
    ext y
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, coe_eval₂Hom]
    rw [awayEquiv_awayMap, eval₂_map]
    rfl

end BaseChange

end TwoChartData

end AlgebraicGeometry.AmpleLift
