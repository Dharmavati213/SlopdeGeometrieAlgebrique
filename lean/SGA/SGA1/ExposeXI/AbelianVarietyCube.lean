/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Picard.Cube
import SGA.SGA1.ExposeXI.AbelianVariety

/-!
# SGA 1, Exposé XI.2: the cube relation on an abelian variety, and `[n]^* L`

SGA 1 XI.2 uses that multiplication by `n` on an abelian variety is an isogeny, citing Mumford.
Mumford's proof (*Abelian varieties*, §6, Corollaries 2–3, and §8) goes through the theorem of the
cube. For a commutative group object `A` over `k`, a class `c ∈ Pic A` and morphisms
`f, g, h : T ⟶ A` of `k`-schemes, writing `f^* c` for the inverse image along `f`:

* `cubeClass c f g h`: `(f+g+h)^* c ⊗ (f+g)^* c⁻¹ ⊗ (f+h)^* c⁻¹ ⊗ (g+h)^* c⁻¹ ⊗ f^* c ⊗ g^* c ⊗
  h^* c`, and `CubeRelation A`: it is always trivial (Mumford §6, Corollary 2);
  `cubeRelation_of_proj`: it suffices to check this for the three projections of `A × A × A`;
* `cubeRelation_of_theoremOfTheCube`: the cube relation on an abelian variety (proper, smooth,
  connected) from the theorem of the cube (`AlgebraicGeometry.TheoremOfTheCubeStatement`);
  `cubeRelation_of_cubeOpenness` (in `AbelianVarietyCubeOpenness`) derives it from the openness
  step alone;
* `picPullback_pow`: from the cube relation, for `φ : T ⟶ A` and `n ∈ ℕ`,
  `(nφ)^* c = (φ^* c)^{n(n+1)/2} ⊗ ((-φ)^* c)^{n(n-1)/2}` (Mumford §6, Corollary 3; the exponents
  are written `(n + 1).choose 2` and `n.choose 2`), and `picPullback_mulN`:
  `n_A^* c = c^{n(n+1)/2} ⊗ ((-1)^* c)^{n(n-1)/2}`.

Here `f + g` is the product of `f` and `g` in the group `Hom(T, A)` (written multiplicatively in
Lean), and `nφ = φⁿ`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace SGA.SGA1.ExposeXI

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

section PicPullback

/-- The inverse image `φ^* c ∈ Pic T` of a class `c ∈ Pic A` along a morphism `φ : T ⟶ A`. -/
noncomputable def picPullback (c : A.left.Pic) {T : Over (Spec (.of k))} (φ : T ⟶ A) :
    T.left.Pic :=
  Scheme.Pic.pullback φ.left c

variable {A} (c : A.left.Pic) {T T' : Over (Spec (.of k))}

omit [GrpObj A] in
lemma pullback_picPullback (u : T' ⟶ T) (φ : T ⟶ A) :
    Scheme.Pic.pullback u.left (picPullback A c φ) = picPullback A c (u ≫ φ) := by
  rw [picPullback, picPullback, Over.comp_left, Scheme.Pic.pullback_comp_apply]

instance subsingleton_pic_unit : Subsingleton (𝟙_ (Over (Spec (.of k)))).left.Pic :=
  Scheme.Pic.subsingleton_spec_of_isLocalRing (.of k)

/-- The inverse image along the neutral element `1 = (T ⟶ pt ⟶ A)` is trivial. -/
lemma picPullback_one : picPullback A c (1 : T ⟶ A) = 1 := by
  rw [Hom.one_def, ← pullback_picPullback, Subsingleton.elim (picPullback A c η) 1, map_one]

end PicPullback

section Cube

variable {A} [IsCommMonObj A] (c : A.left.Pic) {T T' : Over (Spec (.of k))}

/-- The class `(f+g+h)^* c ⊗ (f+g)^* c⁻¹ ⊗ (f+h)^* c⁻¹ ⊗ (g+h)^* c⁻¹ ⊗ f^* c ⊗ g^* c ⊗ h^* c`
of Mumford, *Abelian varieties*, §6, Corollary 2. -/
noncomputable def cubeClass (f g h : T ⟶ A) : T.left.Pic :=
  picPullback A c (f * g * h) * (picPullback A c (f * g))⁻¹ * (picPullback A c (f * h))⁻¹ *
    (picPullback A c (g * h))⁻¹ * picPullback A c f * picPullback A c g * picPullback A c h

omit [IsCommMonObj A] in
lemma pullback_cubeClass (u : T' ⟶ T) (f g h : T ⟶ A) :
    Scheme.Pic.pullback u.left (cubeClass c f g h) = cubeClass c (u ≫ f) (u ≫ g) (u ≫ h) := by
  simp only [cubeClass, map_mul, map_inv, pullback_picPullback, comp_mul]

lemma cubeClass_one_left (a b : T ⟶ A) : cubeClass c 1 a b = 1 := by
  simp only [cubeClass, _root_.one_mul, picPullback_one, _root_.mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

lemma cubeClass_one_middle (a b : T ⟶ A) : cubeClass c a 1 b = 1 := by
  simp only [cubeClass, _root_.mul_one, _root_.one_mul, picPullback_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

lemma cubeClass_one_right (a b : T ⟶ A) : cubeClass c a b 1 = 1 := by
  simp only [cubeClass, _root_.mul_one, picPullback_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one]
  abel

variable (A) in
/-- Mumford, *Abelian varieties*, §6, Corollary 2, as a property of a commutative group object `A`
over `k`: for every class `c ∈ Pic A` and all morphisms `f, g, h : T ⟶ A` of `k`-schemes,
`(f+g+h)^* c ⊗ (f+g)^* c⁻¹ ⊗ (f+h)^* c⁻¹ ⊗ (g+h)^* c⁻¹ ⊗ f^* c ⊗ g^* c ⊗ h^* c` is trivial. For an
abelian variety it follows from the theorem of the cube (`cubeRelation_of_theoremOfTheCube`). -/
def CubeRelation : Prop :=
  ∀ (c : A.left.Pic) {T : Over (Spec (.of k))} (f g h : T ⟶ A), cubeClass c f g h = 1

/-- The three projections `(A ⊗ A) ⊗ A ⟶ A`, and the restrictions of their cube class to the
three faces through the origin. -/
lemma cubeClass_proj_face₁ :
    Scheme.Pic.pullback (lift (lift (toUnit (A ⊗ A) ≫ η) (fst A A)) (snd A A)).left
      (cubeClass c (fst _ _ ≫ fst _ _ : (A ⊗ A) ⊗ A ⟶ A) (fst _ _ ≫ snd _ _) (snd _ _)) =
    cubeClass c 1 (fst A A) (snd A A) := by
  rw [pullback_cubeClass]
  congr 1 <;> simp [Hom.one_def]

lemma cubeClass_proj_face₂ :
    Scheme.Pic.pullback (lift (lift (fst A A) (toUnit (A ⊗ A) ≫ η)) (snd A A)).left
      (cubeClass c (fst _ _ ≫ fst _ _ : (A ⊗ A) ⊗ A ⟶ A) (fst _ _ ≫ snd _ _) (snd _ _)) =
    cubeClass c (fst A A) 1 (snd A A) := by
  rw [pullback_cubeClass]
  congr 1 <;> simp [Hom.one_def]

lemma cubeClass_proj_face₃ :
    Scheme.Pic.pullback (lift (𝟙 (A ⊗ A)) (toUnit (A ⊗ A) ≫ η)).left
      (cubeClass c (fst _ _ ≫ fst _ _ : (A ⊗ A) ⊗ A ⟶ A) (fst _ _ ≫ snd _ _) (snd _ _)) =
    cubeClass c (fst A A) (snd A A) 1 := by
  rw [pullback_cubeClass]
  congr 1 <;> simp [Hom.one_def]

omit [IsCommMonObj A] in
/-- The cube relation holds as soon as it holds for the three projections of `(A ⊗ A) ⊗ A`. -/
lemma cubeRelation_of_proj
    (h : ∀ c : A.left.Pic, cubeClass c (fst _ _ ≫ fst _ _ : (A ⊗ A) ⊗ A ⟶ A) (fst _ _ ≫ snd _ _)
      (snd _ _) = 1) : CubeRelation A := by
  intro c T f g h'
  have := congrArg (Scheme.Pic.pullback (lift (lift f g) h').left) (h c)
  rw [pullback_cubeClass, map_one] at this
  convert this using 2 <;> simp

variable [IsAlgClosed k] [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left]

/-- Mumford, *Abelian varieties*, §6, Corollary 2, from the theorem of the cube (`hcube`): the
cube relation holds on an abelian variety. -/
theorem cubeRelation_of_theoremOfTheCube (hcube : TheoremOfTheCubeStatement.{u}) :
    CubeRelation A := by
  have : GeometricallyIntegral A.hom := geometricallyIntegral_of_smooth_of_isAlgClosed A.hom
  refine cubeRelation_of_proj fun c ↦ hcube k A A A η η η _ ?_ ?_ ?_
  · rw [cubeClass_proj_face₁, cubeClass_one_left]
  · rw [cubeClass_proj_face₂, cubeClass_one_middle]
  · rw [cubeClass_proj_face₃, cubeClass_one_right]

omit [IsAlgClosed k] [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left]

/-- The recursion behind Mumford, *Abelian varieties*, §6, Corollary 3: for `φ : T ⟶ A`,
`(m+2)φ^* c = ((m+1)φ^* c)² ⊗ (mφ^* c)⁻¹ ⊗ φ^* c ⊗ (-φ)^* c`, from the cube relation (`hrel`)
applied to `(m+1)φ, φ, -φ`. -/
lemma picPullback_pow_add_two (hrel : CubeRelation A) (φ : T ⟶ A) (m : ℕ) :
    picPullback A c (φ ^ (m + 2)) = picPullback A c (φ ^ (m + 1)) ^ 2 *
      (picPullback A c (φ ^ m))⁻¹ * picPullback A c φ * picPullback A c φ⁻¹ := by
  have h := hrel c (φ ^ (m + 1)) φ φ⁻¹
  have e₁ : φ ^ (m + 1) * φ = φ ^ (m + 2) := (_root_.pow_succ φ (m + 1)).symm
  have e₂ : φ ^ (m + 1) * φ⁻¹ = φ ^ m := by rw [_root_.pow_succ, _root_.mul_inv_cancel_right]
  rw [cubeClass, _root_.mul_inv_cancel_right, e₁, e₂, _root_.mul_inv_cancel, picPullback_one,
    inv_one] at h
  rw [← inv_mul_eq_one]
  refine Eq.trans ?_ h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
  abel

/-- Mumford, *Abelian varieties*, §6, Corollary 3, from the cube relation (`hrel`): for
`c ∈ Pic A`, `φ : T ⟶ A` and `n ∈ ℕ`,
`(nφ)^* c = (φ^* c)^{n(n+1)/2} ⊗ ((-φ)^* c)^{n(n-1)/2}`. -/
theorem picPullback_pow (hrel : CubeRelation A) (φ : T ⟶ A) (n : ℕ) :
    picPullback A c (φ ^ n) =
      picPullback A c φ ^ (n + 1).choose 2 * picPullback A c φ⁻¹ ^ n.choose 2 := by
  suffices H : ∀ m : ℕ, (picPullback A c (φ ^ m) =
      picPullback A c φ ^ (m + 1).choose 2 * picPullback A c φ⁻¹ ^ m.choose 2) ∧
      (picPullback A c (φ ^ (m + 1)) =
        picPullback A c φ ^ (m + 2).choose 2 * picPullback A c φ⁻¹ ^ (m + 1).choose 2) from
    (H n).1
  intro m
  induction m with
  | zero => exact ⟨by simp [picPullback_one], by simp⟩
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    rw [show m + 1 + 1 = m + 2 by omega, picPullback_pow_add_two c hrel, ih.1, ih.2,
      show m + 1 + 2 = m + 3 by omega]
    have h₁ : (m + 1).choose 2 = m.choose 2 + m := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    have h₂ : (m + 2).choose 2 = m.choose 2 + m + (m + 1) := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, h₁, add_comm]
    have h₃ : (m + 3).choose 2 = m.choose 2 + m + (m + 1) + (m + 2) := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, h₂, add_comm]
    rw [h₁, h₂, h₃]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

/-- Mumford, *Abelian varieties*, §6, Corollary 3, for `φ = id`, from the cube relation (`hrel`):
`n_A^* c = c^{n(n+1)/2} ⊗ ((-1)^* c)^{n(n-1)/2}` in `Pic A`. -/
theorem picPullback_mulN (hrel : CubeRelation A) (n : ℕ) :
    Scheme.Pic.pullback (mulN A n).left c =
      c ^ (n + 1).choose 2 * Scheme.Pic.pullback ι[A].left c ^ n.choose 2 := by
  have := picPullback_pow c hrel (𝟙 A) n
  simp only [picPullback, Over.id_left, Scheme.Pic.pullback_id, MonoidHom.id_apply] at this
  rw [mulN, this, Hom.inv_def, Category.id_comp]

end Cube

end SGA.SGA1.ExposeXI
