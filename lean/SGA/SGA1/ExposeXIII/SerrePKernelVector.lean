/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.MvPolynomial.Basic
import SGA.SGA1.ExposeXIII.AffineLinePGroups

/-!
# Vector Artin–Schreier coverings and their semilinear automorphisms

For a ring `B` of characteristic `p` and `a ∈ Bʳ`, the vector Artin–Schreier covering
`B[Y₁, …, Y_r]/(Yᵢᵖ - Yᵢ + aᵢ)` (`VectorArtinSchreier`) is a torsor under `(ℤ/p)ʳ` over `Spec B`;
it is finite étale (`etale_vas`, via the submersive presentation `vasPresentation`, whose
Jacobian is `-1`, and `finite_vas`). These coverings give the weak solutions of embedding problems
with elementary abelian kernel (`SGA.SGA1.ExposeXIII.SerrePKernelLift`), as the scalar ones of
XI.6.7 do for central `ℤ/p` (`SGA.SGA1.ExposeXIII.AffineLinePGroups`).

* `vasSemilinearAut`: a group `G` acting on `B` by `ρ` and on `(ℤ/p)ʳ` by matrices `Cm`, together
  with a `1`-cocycle `u` for `g ⋆ w = Cm(g) ρ_g(w)` such that `uᵖ - u = a - g ⋆ a`, acts on the
  covering by semilinear automorphisms `Y ↦ Cm(g)⁻¹ (Y + u(g))`;
* `existsUnique_comp_vasSemilinearAut`: if the action of `G` on `B` factors through a group `H`
  acting simply transitively on the geometric points of `B`, and `u` identifies the kernel with
  `(ℤ/p)ʳ`, then `G` acts simply transitively on the geometric points of the covering.
-/

universe u

namespace SGA.SGA1.ExposeXIII

namespace SerrePKernel

open MvPolynomial

section Basic

variable (p : ℕ) {ι : Type} {B : Type*} [CommRing B] (a : ι → B)

/-- The relations `Xᵢᵖ - Xᵢ + aᵢ` of the vector Artin–Schreier covering. -/
noncomputable def vasRelation (i : ι) : MvPolynomial ι B := X i ^ p - X i + C (a i)

/-- The vector Artin–Schreier covering `B[Y₁, …, Y_r]/(Yᵢᵖ - Yᵢ + aᵢ)`: a torsor under
`(ℤ/p)ʳ` over `Spec B`, the fibre of `℘ = F - 1` over `-a`. -/
abbrev VectorArtinSchreier := MvPolynomial ι B ⧸ Ideal.span (Set.range (vasRelation p a))

/-- The root vector `(Y₁, …, Y_r)`. -/
noncomputable def vasRoot (i : ι) : VectorArtinSchreier p a := Ideal.Quotient.mk _ (X i)

lemma vasRoot_rel (i : ι) :
    vasRoot p a i ^ p - vasRoot p a i + algebraMap B _ (a i) = 0 := by
  have h : Ideal.Quotient.mk (Ideal.span (Set.range (vasRelation p a))) (vasRelation p a i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  rw [vasRelation, map_add, map_sub, map_pow] at h
  exact h

lemma span_vasRelation_le_ker {S : Type*} [CommRing S] (f : B →+* S) (η : ι → S)
    (h : ∀ i, η i ^ p - η i + f (a i) = 0) :
    Ideal.span (Set.range (vasRelation p a)) ≤ RingHom.ker (eval₂Hom f η) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simp [vasRelation, h i]

/-- Ring homomorphisms out of the vector Artin–Schreier covering. -/
noncomputable def vasLift {S : Type*} [CommRing S] (f : B →+* S) (η : ι → S)
    (h : ∀ i, η i ^ p - η i + f (a i) = 0) : VectorArtinSchreier p a →+* S :=
  Ideal.Quotient.lift _ (eval₂Hom f η) fun _ hx ↦
    RingHom.mem_ker.mp (span_vasRelation_le_ker p a f η h hx)

lemma vasLift_algebraMap {S : Type*} [CommRing S] (f : B →+* S) (η : ι → S)
    (h : ∀ i, η i ^ p - η i + f (a i) = 0) (b : B) :
    vasLift p a f η h (algebraMap B _ b) = f b := by
  change Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ (C b)) = f b
  rw [Ideal.Quotient.lift_mk, eval₂Hom_C]

lemma vasLift_root {S : Type*} [CommRing S] (f : B →+* S) (η : ι → S)
    (h : ∀ i, η i ^ p - η i + f (a i) = 0) (i : ι) :
    vasLift p a f η h (vasRoot p a i) = η i := by
  rw [vasLift, vasRoot, Ideal.Quotient.lift_mk, eval₂Hom_X']

lemma vas_ringHom_ext {S : Type*} [CommRing S] {f g : VectorArtinSchreier p a →+* S}
    (h₁ : ∀ b, f (algebraMap B _ b) = g (algebraMap B _ b))
    (h₂ : ∀ i, f (vasRoot p a i) = g (vasRoot p a i)) : f = g := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun b ↦ ?_) fun i ↦ ?_)
  · exact h₁ b
  · exact h₂ i

variable {R : Type*} [CommRing R] [Algebra R B]

/-- `R`-algebra homomorphisms out of the vector Artin–Schreier covering. -/
noncomputable def vasLiftAlgHom {S : Type*} [CommRing S] [Algebra R S] (f : B →ₐ[R] S)
    (η : ι → S) (h : ∀ i, η i ^ p - η i + f (a i) = 0) : VectorArtinSchreier p a →ₐ[R] S :=
  { vasLift p a (f : B →+* S) η h with
    commutes' := fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R B]
      exact (vasLift_algebraMap p a _ η h _).trans (f.commutes r) }

lemma vasLiftAlgHom_algebraMap {S : Type*} [CommRing S] [Algebra R S] (f : B →ₐ[R] S)
    (η : ι → S) (h : ∀ i, η i ^ p - η i + f (a i) = 0) (b : B) :
    vasLiftAlgHom p a f η h (algebraMap B _ b) = f b :=
  vasLift_algebraMap p a _ η h b

lemma vasLiftAlgHom_root {S : Type*} [CommRing S] [Algebra R S] (f : B →ₐ[R] S)
    (η : ι → S) (h : ∀ i, η i ^ p - η i + f (a i) = 0) (i : ι) :
    vasLiftAlgHom p a f η h (vasRoot p a i) = η i :=
  vasLift_root p a _ η h i

lemma vas_algHom_ext {S : Type*} [CommRing S] [Algebra R S]
    {f g : VectorArtinSchreier p a →ₐ[R] S}
    (h₁ : ∀ b, f (algebraMap B _ b) = g (algebraMap B _ b))
    (h₂ : ∀ i, f (vasRoot p a i) = g (vasRoot p a i)) : f = g :=
  AlgHom.coe_ringHom_injective (vas_ringHom_ext p a h₁ h₂)

end Basic

section FiniteEtale

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {B : Type*}
  [CommRing B] [CharP B p] (a : ι → B)

/-- The vector Artin–Schreier covering as a submersive presentation: its Jacobian matrix is `-1`
in characteristic `p`. -/
noncomputable def vasPresentation :
    Algebra.SubmersivePresentation B (VectorArtinSchreier p a) ι ι where
  __ := Algebra.PreSubmersivePresentation.naive (v := vasRelation p a) id Function.injective_id
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have hp0 : ((p : ℕ) : MvPolynomial ι B) = 0 := by
      rw [← map_natCast (algebraMap B (MvPolynomial ι B)), CharP.cast_eq_zero, map_zero]
    have hJ : (Algebra.PreSubmersivePresentation.naive (v := vasRelation p a) id
        Function.injective_id).jacobiMatrix = -1 := by
      ext i j
      rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
      simp only [vasRelation, map_add, map_sub, pderiv_pow, pderiv_C, hp0, zero_mul, zero_sub,
        add_zero, id]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Ne.symm hij]
    rw [hJ, Matrix.det_neg, Matrix.det_one, mul_one]
    exact ((isUnit_one.neg).pow _).map _

omit [Fintype ι] [DecidableEq ι] in
instance finite_vas [Finite ι] : Module.Finite B (VectorArtinSchreier p a) := by
  have hint : ∀ x ∈ Set.range (vasRoot p a), IsIntegral B x := by
    rintro _ ⟨i, rfl⟩
    refine ⟨Polynomial.X ^ p - Polynomial.X + Polynomial.C (a i),
      ExposeXI.ArtinSchreier.monic hp.out (a i), ?_⟩
    rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    exact vasRoot_rel p a i
  have htop : Algebra.adjoin B (Set.range (vasRoot p a)) = ⊤ := by
    have h := MvPolynomial.adjoin_range_X (R := B) (σ := ι)
    have := congrArg (Subalgebra.map (Ideal.Quotient.mkₐ B
      (Ideal.span (Set.range (vasRelation p a))))) h
    rw [AlgHom.map_adjoin, ← Set.range_comp, Algebra.map_top,
      (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective _ _)] at this
    exact this
  have := fg_adjoin_of_finite (Set.finite_range _) hint
  rw [htop, Algebra.top_toSubmodule] at this
  exact Module.finite_def.mpr this

end FiniteEtale

section EtaleInstances

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Finite ι] {B : Type*} [CommRing B] [CharP B p]
  (a : ι → B)

instance isStandardSmoothOfRelativeDimension_vas :
    Algebra.IsStandardSmoothOfRelativeDimension 0 B (VectorArtinSchreier p a) := by
  classical
  have := Fintype.ofFinite ι
  exact (vasPresentation p a).isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

instance etale_vas : Algebra.Etale B (VectorArtinSchreier p a) := inferInstance

end EtaleInstances

section Matrix

open Matrix

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι]

/-- An `𝔽_p`-matrix acting on vectors with entries in a ring of characteristic `p`. -/
abbrev castMat (S : Type*) [CommRing S] [CharP S p] (M : Matrix ι ι (ZMod p)) : Matrix ι ι S :=
  M.map (ZMod.castHom (dvd_refl p) S)

variable {p}

lemma castMat_mul (S : Type*) [CommRing S] [CharP S p] (M N : Matrix ι ι (ZMod p)) :
    castMat p S (M * N) = castMat p S M * castMat p S N :=
  Matrix.map_mul

omit [Fintype ι] in
lemma castMat_one (S : Type*) [CommRing S] [CharP S p] [DecidableEq ι] :
    castMat p S (1 : Matrix ι ι (ZMod p)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

omit hp in
lemma map_castMat_mulVec {S T : Type*} [CommRing S] [CharP S p] [CommRing T] [CharP T p]
    (φ : S →+* T) (M : Matrix ι ι (ZMod p)) (v : ι → S) (i : ι) :
    φ ((castMat p S M *ᵥ v) i) = (castMat p T M *ᵥ (φ ∘ v)) i := by
  rw [RingHom.map_mulVec]
  congr 2
  ext j k
  simp only [Matrix.map_apply]
  exact RingHom.congr_fun (RingHom.ext_zmod (φ.comp (ZMod.castHom (dvd_refl p) S))
    (ZMod.castHom (dvd_refl p) T)) _

lemma castMat_mulVec_pow {S : Type*} [CommRing S] [CharP S p] (M : Matrix ι ι (ZMod p))
    (v : ι → S) (i : ι) :
    (castMat p S M *ᵥ v) i ^ p = (castMat p S M *ᵥ fun j ↦ v j ^ p) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [sum_pow_char]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_pow, ExposeXI.ArtinSchreier.castHom_pow]

end Matrix

section Semilinear

open Matrix

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {R B : Type*}
  [CommRing R] [CommRing B] [Algebra R B] [CharP B p] {G : Type*} [Group G]
  (ρ : G →* (B ≃ₐ[R] B)) (Cm : G →* Matrix ι ι (ZMod p))

/-- The semilinear action `g ⋆ w = Cm(g) ρ_g(w)` of `G` on `Bᶥ`. -/
def vecAct (g : G) (w : ι → B) : ι → B := castMat p B (Cm g) *ᵥ fun i ↦ ρ g (w i)

variable (a : ι → B) (u : G → ι → B)
  (hu : ∀ g i, u g i ^ p - u g i = a i - vecAct p ρ Cm g a i)

/-- The polynomial vector `Cm(g)⁻¹ (X + u(g))` defining the semilinear map attached to `g`. -/
noncomputable def semilinearPoly (g : G) : ι → MvPolynomial ι B :=
  castMat p (MvPolynomial ι B) (Cm g⁻¹) *ᵥ fun i ↦ X i + C (u g i)

include hu in
lemma semilinearPoly_rel (g : G) (i : ι) :
    semilinearPoly p Cm u g i ^ p - semilinearPoly p Cm u g i + C (ρ g (a i)) =
      (castMat p (MvPolynomial ι B) (Cm g⁻¹) *ᵥ vasRelation p a) i := by
  have hC : ∀ w : ι → B, (fun i ↦ C (vecAct p ρ Cm g w i)) =
      castMat p (MvPolynomial ι B) (Cm g) *ᵥ fun i ↦ C (ρ g (w i)) := by
    intro w
    funext i
    exact map_castMat_mulVec (C : B →+* MvPolynomial ι B) (Cm g) _ i
  have hfrob : (fun i ↦ semilinearPoly p Cm u g i ^ p) =
      castMat p (MvPolynomial ι B) (Cm g⁻¹) *ᵥ fun i ↦ X i ^ p + C (u g i ^ p) := by
    funext i
    rw [semilinearPoly, castMat_mulVec_pow]
    congr 2
    funext j
    rw [add_pow_char, map_pow]
  have key : (fun i ↦ semilinearPoly p Cm u g i ^ p - semilinearPoly p Cm u g i +
      C (ρ g (a i))) = castMat p (MvPolynomial ι B) (Cm g⁻¹) *ᵥ vasRelation p a := by
    have h1 : (fun i ↦ semilinearPoly p Cm u g i ^ p - semilinearPoly p Cm u g i +
        C (ρ g (a i))) = (fun i ↦ semilinearPoly p Cm u g i ^ p) -
          semilinearPoly p Cm u g + fun i ↦ C (ρ g (a i)) := rfl
    have h2 : (fun i ↦ X i ^ p + C (u g i ^ p)) - (fun i ↦ X i + C (u g i)) =
        vasRelation p a - fun i ↦ C (vecAct p ρ Cm g a i) := by
      funext i
      simp only [Pi.sub_apply, vasRelation]
      have := congrArg (C : B → MvPolynomial ι B) (hu g i)
      rw [map_sub, map_sub, map_pow] at this
      rw [map_pow]
      linear_combination this
    have h3 : castMat p (MvPolynomial ι B) (Cm g⁻¹) * castMat p (MvPolynomial ι B) (Cm g) = 1 := by
      rw [← castMat_mul, ← map_mul, inv_mul_cancel, map_one, castMat_one]
    rw [h1, hfrob, semilinearPoly, ← mulVec_sub, h2, mulVec_sub, hC, mulVec_mulVec, h3,
      one_mulVec, sub_add_cancel]
  exact congrFun key i

include hu in
lemma semilinear_rel (g : G) (i : ι) :
    Ideal.Quotient.mk (Ideal.span (Set.range (vasRelation p a))) (semilinearPoly p Cm u g i) ^ p -
      Ideal.Quotient.mk _ (semilinearPoly p Cm u g i) +
        ((IsScalarTower.toAlgHom R B (VectorArtinSchreier p a)).comp (ρ g).toAlgHom) (a i) = 0 := by
  have h := semilinearPoly_rel p ρ Cm a u hu g i
  have hmem : (castMat p (MvPolynomial ι B) (Cm g⁻¹) *ᵥ vasRelation p a) i ∈
      Ideal.span (Set.range (vasRelation p a)) := by
    simp only [mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  rw [← h] at hmem
  have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_add, map_sub, map_pow] at this
  exact this

/-- The semilinear vector Artin–Schreier map attached to `g`: it acts on `B` by `ρ g` and sends
the root vector `Y` to `Cm(g)⁻¹ (Y + u(g))`. -/
noncomputable def vasSemilinearHom (g : G) :
    VectorArtinSchreier p a →ₐ[R] VectorArtinSchreier p a :=
  vasLiftAlgHom p a ((IsScalarTower.toAlgHom R B _).comp (ρ g).toAlgHom)
    (fun i ↦ Ideal.Quotient.mk _ (semilinearPoly p Cm u g i)) (semilinear_rel p ρ Cm a u hu g)

lemma vasSemilinearHom_algebraMap (g : G) (b : B) :
    vasSemilinearHom p ρ Cm a u hu g (algebraMap B _ b) = algebraMap B _ (ρ g b) :=
  vasLiftAlgHom_algebraMap p a _ _ _ b

lemma vasSemilinearHom_root (g : G) (i : ι) :
    vasSemilinearHom p ρ Cm a u hu g (vasRoot p a i) =
      Ideal.Quotient.mk _ (semilinearPoly p Cm u g i) :=
  vasLiftAlgHom_root p a _ _ _ i

/-- The substitution `X ↦ Cm(g)⁻¹ (X + u(g))`, twisted by `ρ g` on coefficients. -/
noncomputable def substHom (g : G) : MvPolynomial ι B →+* MvPolynomial ι B :=
  eval₂Hom (C.comp (ρ g : B →+* B)) (semilinearPoly p Cm u g)

lemma vasSemilinearHom_mk (g : G) (Q : MvPolynomial ι B) :
    vasSemilinearHom p ρ Cm a u hu g (Ideal.Quotient.mk _ Q) =
      Ideal.Quotient.mk _ (substHom p ρ Cm u g Q) := by
  have : ((vasSemilinearHom p ρ Cm a u hu g).toRingHom.comp (Ideal.Quotient.mk _)) =
      (Ideal.Quotient.mk _).comp (substHom p ρ Cm u g) := by
    refine MvPolynomial.ringHom_ext (fun b ↦ ?_) fun i ↦ ?_
    · simp only [RingHom.comp_apply, substHom, eval₂Hom_C, RingHom.coe_coe]
      exact vasSemilinearHom_algebraMap p ρ Cm a u hu g b
    · simp only [RingHom.comp_apply, substHom, eval₂Hom_X']
      exact vasSemilinearHom_root p ρ Cm a u hu g i
  exact RingHom.congr_fun this Q

lemma vasSemilinearHom_root_of_eq_one {z : G} (hz : Cm z = 1) (i : ι) :
    vasSemilinearHom p ρ Cm a u hu z (vasRoot p a i) = vasRoot p a i + algebraMap B _ (u z i) := by
  have hz' : Cm z⁻¹ = 1 := by
    have := congrArg (· * Cm z⁻¹) hz
    simp only [one_mul, ← map_mul, mul_inv_cancel, map_one] at this
    exact this.symm
  rw [vasSemilinearHom_root, semilinearPoly, hz', castMat_one, one_mulVec, map_add]
  rfl

variable (hmul : ∀ g h, u (g * h) = u g + vecAct p ρ Cm g (u h))

include hmul in
lemma substHom_semilinearPoly (g h : G) (i : ι) :
    substHom p ρ Cm u g (semilinearPoly p Cm u h i) = semilinearPoly p Cm u (g * h) i := by
  have hfix : ∀ v : ι → MvPolynomial ι B, ∀ (M : Matrix ι ι (ZMod p)) (i : ι),
      substHom p ρ Cm u g ((castMat p (MvPolynomial ι B) M *ᵥ v) i) =
        (castMat p (MvPolynomial ι B) M *ᵥ fun j ↦ substHom p ρ Cm u g (v j)) i :=
    fun v M i ↦ map_castMat_mulVec (substHom p ρ Cm u g) M v i
  have hC : ∀ w : ι → B, (fun i ↦ C (vecAct p ρ Cm g w i)) =
      castMat p (MvPolynomial ι B) (Cm g) *ᵥ fun i ↦ C (ρ g (w i)) := by
    intro w
    funext i
    exact map_castMat_mulVec (C : B →+* MvPolynomial ι B) (Cm g) _ i
  have hsub : (fun j ↦ substHom p ρ Cm u g (X j + C (u h j))) =
      semilinearPoly p Cm u g + fun j ↦ C (ρ g (u h j)) := by
    funext j
    simp [substHom]
  have h3 : castMat p (MvPolynomial ι B) (Cm g⁻¹) * castMat p (MvPolynomial ι B) (Cm g) = 1 := by
    rw [← castMat_mul, ← map_mul, inv_mul_cancel, map_one, castMat_one]
  have key : (fun i ↦ substHom p ρ Cm u g (semilinearPoly p Cm u h i)) =
      semilinearPoly p Cm u (g * h) := by
    funext i
    rw [semilinearPoly, hfix, hsub]
    conv_rhs => rw [semilinearPoly, _root_.mul_inv_rev, map_mul, castMat_mul, ← mulVec_mulVec]
    congr 1
    rw [semilinearPoly, hmul]
    have : (fun i ↦ X i + C ((u g + vecAct p ρ Cm g (u h)) i)) =
        (fun i ↦ X i + C (u g i)) + fun i ↦ C (vecAct p ρ Cm g (u h) i) := by
      funext i
      simp only [Pi.add_apply, map_add]
      ring
    rw [this, mulVec_add, hC, mulVec_mulVec, h3, one_mulVec]
  exact congrFun key i

include hmul in
lemma vasSemilinearHom_mul (g h : G) :
    vasSemilinearHom p ρ Cm a u hu (g * h) =
      (vasSemilinearHom p ρ Cm a u hu g).comp (vasSemilinearHom p ρ Cm a u hu h) := by
  refine vas_algHom_ext p a (fun b ↦ ?_) fun i ↦ ?_
  · rw [AlgHom.comp_apply, vasSemilinearHom_algebraMap, vasSemilinearHom_algebraMap,
      vasSemilinearHom_algebraMap, map_mul, AlgEquiv.mul_apply]
  · rw [AlgHom.comp_apply, vasSemilinearHom_root, vasSemilinearHom_root, vasSemilinearHom_mk,
      substHom_semilinearPoly p ρ Cm u hmul]

include hmul in
lemma vasSemilinearHom_one : vasSemilinearHom p ρ Cm a u hu 1 = AlgHom.id R _ := by
  have h1 : u 1 = 0 := by
    have := hmul 1 1
    rw [mul_one] at this
    have h' : vecAct p ρ Cm 1 (u 1) = u 1 := by
      funext i
      simp [vecAct]
    rw [h'] at this
    exact left_eq_add.mp this
  refine vas_algHom_ext p a (fun b ↦ ?_) fun i ↦ ?_
  · rw [vasSemilinearHom_algebraMap, map_one, AlgEquiv.one_apply, AlgHom.id_apply]
  · rw [vasSemilinearHom_root, AlgHom.id_apply, semilinearPoly, h1, inv_one, map_one, castMat_one,
      one_mulVec]
    simp [vasRoot]

/-- The action of `G` on the vector Artin–Schreier covering by semilinear automorphisms. -/
noncomputable def vasSemilinearAut :
    G →* (VectorArtinSchreier p a ≃ₐ[R] VectorArtinSchreier p a) where
  toFun g := AlgEquiv.ofAlgHom (vasSemilinearHom p ρ Cm a u hu g)
    (vasSemilinearHom p ρ Cm a u hu g⁻¹)
    (by rw [← vasSemilinearHom_mul p ρ Cm a u hu hmul, mul_inv_cancel,
      vasSemilinearHom_one p ρ Cm a u hu hmul])
    (by rw [← vasSemilinearHom_mul p ρ Cm a u hu hmul, inv_mul_cancel,
      vasSemilinearHom_one p ρ Cm a u hu hmul])
  map_one' := AlgEquiv.coe_toAlgHom_injective (vasSemilinearHom_one p ρ Cm a u hu hmul)
  map_mul' g h := AlgEquiv.coe_toAlgHom_injective (vasSemilinearHom_mul p ρ Cm a u hu hmul g h)

lemma vasSemilinearAut_apply (g : G) (y : VectorArtinSchreier p a) :
    vasSemilinearAut p ρ Cm a u hu hmul g y = vasSemilinearHom p ρ Cm a u hu g y :=
  rfl

end Semilinear

section Points

open Matrix

variable (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {R B : Type*}
  [CommRing R] [CommRing B] [Algebra R B] [CharP B p] {H G : Type*} [Group H] [Group G]
  (ρH : H →* (B ≃ₐ[R] B)) (CmH : H →* Matrix ι ι (ZMod p)) (π : G →* H)
  (a : ι → B) (u : G → ι → B)
  (hu : ∀ g i, u g i ^ p - u g i = a i - vecAct p (ρH.comp π) (CmH.comp π) g a i)
  (hmul : ∀ g h, u (g * h) = u g + vecAct p (ρH.comp π) (CmH.comp π) g (u h))
  (Ω : Type*) [Field Ω] [Algebra R Ω] [CharP Ω p]

omit hp [Fintype ι] [DecidableEq ι] [CharP B p] [CharP Ω p] in
lemma vasRoot_pow_sub (x : VectorArtinSchreier p a →ₐ[R] Ω) (i : ι) :
    x (vasRoot p a i) ^ p - x (vasRoot p a i) =
      -(x.comp (IsScalarTower.toAlgHom R B _)) (a i) := by
  have h := congrArg x (vasRoot_rel p a i)
  rw [map_add, map_sub, map_pow, map_zero] at h
  change _ = -x (algebraMap B _ (a i))
  linear_combination h

/-- The geometric points of the vector Artin–Schreier covering: if `H` acts simply transitively
on `Hom_R(B, Ω)`, `π : G → H` is onto, `Cm` factors through `H`, and `u` restricts on `ker π` to
a bijection onto `𝔽_pᶥ`, then `G` acts simply transitively on its `Ω`-points. -/
theorem existsUnique_comp_vasSemilinearAut
    (hH : ∀ x y : B →ₐ[R] Ω, ∃! σ : H, x.comp (ρH σ).toAlgHom = y)
    (hπ : Function.Surjective π) (χ : G → ι → ZMod p)
    (hχ : ∀ z ∈ π.ker, ∀ i, u z i = ZMod.castHom (dvd_refl p) B (χ z i))
    (hχinj : ∀ z ∈ π.ker, χ z = 0 → z = 1) (hχsurj : ∀ k, ∃ z ∈ π.ker, χ z = k)
    (x y : VectorArtinSchreier p a →ₐ[R] Ω) :
    ∃! g : G, x.comp (vasSemilinearAut p (ρH.comp π) (CmH.comp π) a u hu hmul g).toAlgHom = y := by
  set e := vasSemilinearAut p (ρH.comp π) (CmH.comp π) a u hu hmul
  set ι' := IsScalarTower.toAlgHom R B (VectorArtinSchreier p a)
  have he_ι : ∀ g, (e g).toAlgHom.comp ι' = ι'.comp (ρH (π g)).toAlgHom := fun g ↦
    AlgHom.ext fun b ↦ vasSemilinearHom_algebraMap p (ρH.comp π) (CmH.comp π) a u hu g b
  have hres : ∀ (f : VectorArtinSchreier p a →ₐ[R] Ω) g,
      (f.comp (e g).toAlgHom).comp ι' = (f.comp ι').comp (ρH (π g)).toAlgHom := by
    intro f g
    rw [AlgHom.comp_assoc, he_ι, ← AlgHom.comp_assoc]
  have hcast : ∀ (k : ZMod p) (f : VectorArtinSchreier p a →ₐ[R] Ω),
      f (algebraMap B _ (ZMod.castHom (dvd_refl p) B k)) = ZMod.castHom (dvd_refl p) Ω k := by
    intro k f
    exact RingHom.congr_fun (RingHom.ext_zmod ((f.toRingHom.comp (algebraMap B _)).comp
      (ZMod.castHom (dvd_refl p) B)) (ZMod.castHom (dvd_refl p) Ω)) k
  have hker : ∀ z ∈ π.ker, (CmH.comp π) z = 1 := fun z hz ↦ by
    rw [MonoidHom.comp_apply, (MonoidHom.mem_ker).mp hz, map_one]
  have hroot : ∀ z ∈ π.ker, ∀ i, e z (vasRoot p a i) =
      vasRoot p a i + algebraMap B _ (ZMod.castHom (dvd_refl p) B (χ z i)) := fun z hz i ↦ by
    rw [vasSemilinearAut_apply, vasSemilinearHom_root_of_eq_one p (ρH.comp π) (CmH.comp π) a u hu
      (hker z hz), hχ z hz]
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨σ, hσ, -⟩ := hH (x.comp ι') (y.comp ι')
    obtain ⟨g₀, rfl⟩ := hπ σ
    set x' := x.comp (e g₀).toAlgHom
    have hx'B : x'.comp ι' = y.comp ι' := by rw [hres, hσ]
    have hk : ∀ i, ∃ k : ZMod p, y (vasRoot p a i) - x' (vasRoot p a i) =
        ZMod.castHom (dvd_refl p) Ω k := by
      intro i
      set d := y (vasRoot p a i) - x' (vasRoot p a i)
      have hd : d ^ p - d + 0 = 0 := by
        have h₁ := vasRoot_pow_sub p a Ω x' i
        have h₂ := vasRoot_pow_sub p a Ω y i
        rw [hx'B] at h₁
        rw [sub_pow_char]
        linear_combination h₂ - h₁
      have hprod := congrArg (Polynomial.eval d)
        (ExposeXI.ArtinSchreier.X_pow_sub_X_eq_prod (A := Ω) (p := p))
      rw [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, hd, Polynomial.eval_prod] at hprod
      obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hprod.symm
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hk
      exact ⟨k, hk⟩
    choose k hk using hk
    obtain ⟨z, hz, hzk⟩ := hχsurj k
    refine ⟨g₀ * z, vas_algHom_ext p a (fun b ↦ ?_) fun i ↦ ?_⟩
    · rw [map_mul]
      change x' (e z (algebraMap B _ b)) = y (algebraMap B _ b)
      rw [vasSemilinearAut_apply, vasSemilinearHom_algebraMap, MonoidHom.comp_apply,
        (MonoidHom.mem_ker).mp hz, map_one, AlgEquiv.one_apply]
      exact congrArg (fun f ↦ f b) hx'B
    · rw [map_mul]
      change x' (e z (vasRoot p a i)) = y (vasRoot p a i)
      rw [hroot z hz, map_add, hcast, hzk, ← hk i]
      ring
  · intro g g' hg hg'
    obtain ⟨σ, -, hσ⟩ := hH (x.comp ι') (y.comp ι')
    have h₁ : π g = σ := hσ (π g) (by beta_reduce; rw [← hres, hg])
    have h₂ : π g' = σ := hσ (π g') (by beta_reduce; rw [← hres, hg'])
    have hz : g⁻¹ * g' ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h₁, h₂, inv_mul_cancel]
    have hyz : ∀ t, y (e (g⁻¹ * g') t) = y t := by
      intro t
      calc y (e (g⁻¹ * g') t) = (x.comp (e g).toAlgHom) (e (g⁻¹ * g') t) := by rw [hg]
        _ = x (e g (e (g⁻¹ * g') t)) := rfl
        _ = x (e g' t) := by rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]
        _ = y t := by rw [← hg']; rfl
    have h0 : χ (g⁻¹ * g') = 0 := by
      funext i
      have := hyz (vasRoot p a i)
      rw [hroot _ hz, map_add, add_eq_left, hcast] at this
      exact (ZMod.castHom (dvd_refl p) Ω).injective (by rw [this, Pi.zero_apply, map_zero])
    rw [← mul_inv_cancel_left g g', hχinj _ hz h0, mul_one]

end Points

end SerrePKernel

end SGA.SGA1.ExposeXIII
