/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.LocalModel
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Analytification of affine schemes of finite type

Let `A = 𝕜[x₁, …, xₙ]/(g₁, …, g_k)` be a finitely presented `𝕜`-algebra. Its analytification is
the local model `Z(g) ⊆ 𝕜ⁿ` with structure sheaf `(𝒪_{𝕜ⁿ}/(g))|_{Z(g)}`
(`analytification g`), and the canonical morphism of locally ringed spaces
`φ : Spec(A)^an → Spec A` of [SGA 1, XII.1.1] is obtained from the ring homomorphism
`A → Γ(Spec(A)^an, 𝒪)` sending a polynomial to the class of the analytic function it defines
(`toSpec g`), through the adjunction between `Γ` and `Spec`. The point `x ∈ Z(g)` is sent to the
maximal ideal of `A` of polynomials vanishing at `x` (`toSpec_base_asIdeal`).
-/

universe u

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Filter

namespace AnalyticGeometry

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n k : ℕ}

omit [CompleteSpace 𝕜] in
lemma analyticAt_eval_mvPolynomial (p : MvPolynomial (Fin n) 𝕜) (x : Fin n → 𝕜) :
    AnalyticAt 𝕜 (fun z ↦ MvPolynomial.eval z p) x :=
  AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) p x trivial

variable (g : Fin k → MvPolynomial (Fin n) 𝕜)

/-- The local model `Z(g) ⊆ 𝕜ⁿ` defined by polynomials `g₁, …, g_k`. -/
def polynomialModel : LocalModelData 𝕜 (Fin n → 𝕜) where
  U := Set.univ
  isOpen_U := isOpen_univ
  k := k
  f i z := MvPolynomial.eval z (g i)
  analyticAt_f i x _ := analyticAt_eval_mvPolynomial (g i) x

/-- The finitely presented algebra `𝕜[x₁, …, xₙ]/(g₁, …, g_k)`. -/
abbrev PresentedAlgebra : Type u := MvPolynomial (Fin n) 𝕜 ⧸ Ideal.span (Set.range g)

/-- The analytification `Spec(𝕜[x]/(g))^an`: the local model `Z(g) ⊆ 𝕜ⁿ` with the structure sheaf
`(𝒪_{𝕜ⁿ}/(g))|_{Z(g)}`. -/
abbrev analytification : LocallyRingedSpace.{u} := (polynomialModel g).toLocallyRingedSpace

variable {g}

omit [CompleteSpace 𝕜] in
lemma polynomialModel_zeroSet :
    (polynomialModel g).zeroSet = {x | ∀ i, MvPolynomial.eval x (g i) = 0} := by
  ext x
  simp [LocalModelData.zeroSet, polynomialModel]

/-- The global section of `Spec(A)^an` defined by a polynomial. -/
def polynomialSection (p : MvPolynomial (Fin n) 𝕜) : (analytification g).presheaf.obj (op ⊤) :=
  (polynomialModel g).globalSection (fun z ↦ MvPolynomial.eval z p)
    fun x _ ↦ analyticAt_eval_mvPolynomial p x

lemma polynomialSection_apply (p : MvPolynomial (Fin n) 𝕜) (y) :
    (polynomialSection (g := g) p).1 y = (polynomialModel g).classOf y
      (fun z ↦ MvPolynomial.eval z p) (analyticAt_eval_mvPolynomial p _) := rfl

variable (g) in
/-- Polynomials as global sections of `Spec(A)^an`, as a ring homomorphism. -/
def polynomialSectionHom :
    MvPolynomial (Fin n) 𝕜 →+* (analytification g).presheaf.obj (op ⊤) where
  toFun := polynomialSection
  map_one' := Subtype.ext <| funext fun y ↦ by
    rw [polynomialSection_apply, (polynomialModel g).classOf_congr _
      (Eventually.of_forall fun z ↦ (map_one (MvPolynomial.eval z)) :
        (fun z ↦ MvPolynomial.eval z (1 : MvPolynomial (Fin n) 𝕜)) =ᶠ[_] fun _ ↦ 1),
      LocalModelData.classOf_one]
    rfl
  map_mul' p q := Subtype.ext <| funext fun y ↦ by
    change _ = (polynomialSection p).1 y * (polynomialSection q).1 y
    rw [polynomialSection_apply, polynomialSection_apply, polynomialSection_apply,
      (polynomialModel g).classOf_congr _ (Eventually.of_forall fun z ↦
        (map_mul (MvPolynomial.eval z) p q)), ← LocalModelData.classOf_mul]
    rfl
  map_zero' := Subtype.ext <| funext fun y ↦ by
    rw [polynomialSection_apply, (polynomialModel g).classOf_congr _
      (Eventually.of_forall fun z ↦ (map_zero (MvPolynomial.eval z)) :
        (fun z ↦ MvPolynomial.eval z (0 : MvPolynomial (Fin n) 𝕜)) =ᶠ[_] fun _ ↦ 0),
      LocalModelData.classOf_zero]
    rfl
  map_add' p q := Subtype.ext <| funext fun y ↦ by
    change _ = (polynomialSection p).1 y + (polynomialSection q).1 y
    rw [polynomialSection_apply, polynomialSection_apply, polynomialSection_apply,
      (polynomialModel g).classOf_congr _ (Eventually.of_forall fun z ↦
        (map_add (MvPolynomial.eval z) p q)), ← LocalModelData.classOf_add]
    rfl

lemma polynomialSectionHom_g (i : Fin k) : polynomialSectionHom g (g i) = 0 :=
  (polynomialModel g).globalSection_f i

variable (g) in
/-- The ring homomorphism `A → Γ(Spec(A)^an, 𝒪)`. -/
def algebraToSections :
    PresentedAlgebra g →+* LocallyRingedSpace.Γ.obj (op (analytification g)) :=
  Ideal.Quotient.lift _ (polynomialSectionHom g) fun a ha ↦ by
    have : Ideal.span (Set.range g) ≤ RingHom.ker (polynomialSectionHom g) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact polynomialSectionHom_g i
    exact this ha

@[simp] lemma algebraToSections_mk (p : MvPolynomial (Fin n) 𝕜) :
    algebraToSections g (Ideal.Quotient.mk _ p) = polynomialSection p := rfl

variable (g) in
/-- **XII.1.1**: the canonical morphism of locally ringed spaces `φ : Spec(A)^an → Spec A`. -/
def toSpec : analytification g ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of (PresentedAlgebra g)) :=
  (analytification g).toΓSpec ≫ Spec.locallyRingedSpaceMap (CommRingCat.ofHom (algebraToSections g))

/-- Evaluation at a point `x ∈ Z(g)`, as a ring homomorphism `A → 𝕜`. -/
def evalPoint (x : (polynomialModel g).zeroSet) : PresentedAlgebra g →+* 𝕜 :=
  Ideal.Quotient.lift _ (MvPolynomial.eval (x : Fin n → 𝕜)) fun a ha ↦ by
    have : Ideal.span (Set.range g) ≤ RingHom.ker (MvPolynomial.eval (x : Fin n → 𝕜)) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (polynomialModel g).f_eq_zero x i
    exact this ha

omit [CompleteSpace 𝕜] in
@[simp] lemma evalPoint_mk (x : (polynomialModel g).zeroSet) (p : MvPolynomial (Fin n) 𝕜) :
    evalPoint x (Ideal.Quotient.mk _ p) = MvPolynomial.eval (x : Fin n → 𝕜) p := rfl

omit [CompleteSpace 𝕜] in
lemma evalPoint_surjective (x : (polynomialModel g).zeroSet) :
    Function.Surjective (evalPoint x) := fun c ↦
  ⟨Ideal.Quotient.mk _ (MvPolynomial.C c), by simp⟩

lemma isUnit_Γgerm_polynomialSection_iff (x : (polynomialModel g).zeroSet)
    (p : MvPolynomial (Fin n) 𝕜) :
    IsUnit ((analytification g).presheaf.Γgerm x
      (polynomialSection p)) ↔ MvPolynomial.eval (x : Fin n → 𝕜) p ≠ 0 := by
  have h1 : (analytification g).presheaf.Γgerm x
      (polynomialSection p) = (polynomialModel g).presheaf.germ ⊤ x (Set.mem_univ _)
        (polynomialSection p) := rfl
  rw [h1]
  refine (isUnit_map_iff ((polynomialModel g).stalkIso x) _).symm.trans ?_
  change IsUnit ((polynomialModel g).stalkToFiber x _) ↔ _
  rw [polynomialSection, LocalModelData.stalkToFiber_germ_globalSection,
    LocalModelData.isUnit_fiber_iff, LocalModelData.evalFiber_classOf]

/-- **XII.1.1**: `φ` sends a point `x ∈ Z(g)` to the maximal ideal of polynomials vanishing at
`x`. -/
theorem toSpec_base_asIdeal (x : (polynomialModel g).zeroSet) :
    ((toSpec g).base x).asIdeal = RingHom.ker (evalPoint x) := by
  ext a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hb : (toSpec g).base x =
      PrimeSpectrum.comap (algebraToSections g) ((analytification g).toΓSpecFun x) := rfl
  rw [hb, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.mem_ker, evalPoint_mk,
    ← not_iff_not]
  exact (LocallyRingedSpace.notMem_prime_iff_unit_in_stalk _ _ _).trans
    (isUnit_Γgerm_polynomialSection_iff x p)

/-- On stalks, `φ` is induced by `A → Γ(Spec(A)^an, 𝒪) → 𝒪_{Spec(A)^an, x}`. -/
theorem toStalk_stalkMap_toSpec (x : analytification g) :
    StructureSheaf.toStalk (PresentedAlgebra g) ((toSpec g).base x) ≫
        (toSpec g).stalkMap x =
      CommRingCat.ofHom (algebraToSections g) ≫ (analytification g).presheaf.Γgerm x := by
  rw [toSpec, LocallyRingedSpace.stalkMap_comp]
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  have h₁ := stalkMap_toStalk_apply (CommRingCat.ofHom (algebraToSections g))
    ((analytification g).toΓSpec.base x) a
  have h₂ := congrArg (fun φ ↦ φ.hom (algebraToSections g a))
    ((analytification g).toStalk_stalkMap_toΓSpec x)
  exact (congrArg ((analytification g).toΓSpec.stalkMap x).hom h₁).trans h₂

end AnalyticGeometry
