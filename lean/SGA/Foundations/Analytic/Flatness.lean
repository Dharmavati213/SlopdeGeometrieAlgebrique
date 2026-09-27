/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Analytic.JetComparison
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Flatness of the analytification morphism

The canonical morphism `φ : Spec(A)^an → Spec A` (`A = 𝕜[x]/(g)`) is flat: for every point `x`,
the local homomorphism `𝒪_{Spec A, φ(x)} → 𝒪_{Spec(A)^an, x}` is flat
(`flat_stalkMap_toSpec`; [SGA 1, XII.1.1 and XII.2]; [Serre, *GAGA*, §2, Cor. 1 to Prop. 3]).

The proof: `𝕜[z] → 𝕜⟦z⟧` is flat (the formal power series ring is the adic completion of the
polynomial ring), and `𝕜{z} → 𝕜⟦z⟧` is faithfully flat, so `𝕜[z] → 𝕜{z}` is flat by descent
(`Module.Flat.of_flat_of_faithfullyFlat`). After translation, the germs at `x` of polynomials
give a flat map `𝕜[z] → 𝒪_{𝕜ⁿ,x}`; base change by `(g)` and localization at `𝔪ₓ` finish the
proof.
-/

universe u

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing

/-! ### Generalities on flatness -/

section General

/-- **Descent of flatness**: if `R → S → T`, `T` is faithfully flat over `S` and flat over `R`,
then `S` is flat over `R`. -/
theorem Module.Flat.of_flat_of_faithfullyFlat (R S T : Type*) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  rw [← LinearMap.baseChange_eq_ltensor]
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective S T]
  have key : ∀ y, AlgebraTensorModule.cancelBaseChange R S S T P ((f.baseChange S).lTensor T y) =
      f.lTensor T (AlgebraTensorModule.cancelBaseChange R S S T N y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul s n => simp [AlgebraTensorModule.cancelBaseChange_tmul]
      | add z₁ z₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add, map_add, h₁, h₂, map_add, map_add]
    | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  intro y₁ y₂ h
  apply AlgebraTensorModule.cancelBaseChange R S S T N |>.injective
  apply Module.Flat.lTensor_preserves_injective_linearMap f hf
  rw [← key, ← key, h]

/-- Flatness is preserved by reduction modulo an ideal of the base. -/
theorem Module.Flat.quotient_map {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) : Module.Flat (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := by
  have := Module.Flat.baseChange A (A ⧸ I) B
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv

/-- Flatness is preserved by reduction modulo an ideal of the base. -/
theorem RingHom.Flat.quotientMap {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : f.Flat) (I : Ideal A) : (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).Flat := by
  algebraize [f]
  have h := Module.Flat.quotient_map (B := B) I
  rw [← RingHom.flat_algebraMap_iff] at h
  exact h

/-- If `Rₚ` is a localization of `R` and `f : Rₚ → S` is flat after composition with `R → Rₚ`,
then `f` is flat. -/
theorem RingHom.Flat.of_comp_isLocalization {R Rp S : Type*} [CommRing R] [CommRing Rp]
    [CommRing S] [Algebra R Rp] (p : Submonoid R) [IsLocalization p Rp] (f : Rp →+* S)
    (hf : (f.comp (algebraMap R Rp)).Flat) : f.Flat := by
  algebraize [f, f.comp (algebraMap R Rp)]
  exact (Module.flat_iff_of_isLocalization Rp p S).mpr hf

end General

/-! ### Polynomials in convergent power series -/

namespace MvPowerSeries

variable {σ : Type*} [Finite σ] {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- `𝕜{X}` is flat over the polynomial ring `𝕜[X]`. -/
theorem flat_polynomialToConvergent :
    ((polynomialToConvergent (σ := σ) (𝕜 := 𝕜)) : MvPolynomial σ 𝕜 →+* convergent σ 𝕜).Flat := by
  algebraize [((polynomialToConvergent (σ := σ) (𝕜 := 𝕜)) : MvPolynomial σ 𝕜 →+* convergent σ 𝕜)]
  have : IsScalarTower (MvPolynomial σ 𝕜) (convergent σ 𝕜) (MvPowerSeries σ 𝕜) :=
    IsScalarTower.of_algebraMap_eq fun p ↦ by
      change (p : MvPowerSeries σ 𝕜) = algebraMap (convergent σ 𝕜) (MvPowerSeries σ 𝕜)
        (polynomialToConvergent p)
      rw [Subalgebra.algebraMap_eq, RingHom.comp_apply, AlgHom.coe_toRingHom,
        Subalgebra.coe_val, coe_polynomialToConvergent]
      ext d
      rfl
  have : Module.Flat (MvPolynomial σ 𝕜) (MvPowerSeries σ 𝕜) :=
    Module.Flat.of_linearEquiv (toAdicCompletionAlgEquiv σ 𝕜).toLinearEquiv
  exact Module.Flat.of_flat_of_faithfullyFlat _ (convergent σ 𝕜) (MvPowerSeries σ 𝕜)

end MvPowerSeries

/-! ### Flatness of `φ` -/

namespace AnalyticGeometry

open MvPowerSeries

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n k : ℕ}

omit [CompleteSpace 𝕜] in
lemma translate_bijective (a : Fin n → 𝕜) : Function.Bijective (translate a) :=
  ⟨fun p q h ↦ by rw [← translate_neg_translate a p, h, translate_neg_translate],
    fun p ↦ ⟨translate (-a) p, translate_translate_neg a p⟩⟩

/-- The germs at `a` of polynomial functions form a flat `𝕜[x]`-algebra. -/
theorem flat_polyGermHom (a : Fin n → 𝕜) : (polyGermHom (𝕜 := 𝕜) a).Flat := by
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (convergentStalkEquiv a).bijective)
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective (translate_bijective a))
    flat_polynomialToConvergent

variable (g : Fin k → MvPolynomial (Fin n) 𝕜) (x : (polynomialModel g).zeroSet)

lemma ideal_eq_map :
    (polynomialModel g).ideal x ((polynomialModel g).mem_U x) =
      (Ideal.span (Set.range g)).map (polyGermHom (x : Fin n → 𝕜)) := by
  rw [Ideal.map_span, LocalModelData.ideal, ← Set.range_comp]
  congr 1
  ext t
  simp only [Set.mem_range, Function.comp_apply, polyGermHom_apply]
  rfl

/-- `𝒪_{𝕜ⁿ,x}/(g)` is flat over `A = 𝕜[x]/(g)`. -/
theorem flat_fiberHom : (fiberHom g x).Flat := by
  have h := (flat_polyGermHom (x : Fin n → 𝕜)).quotientMap (Ideal.span (Set.range g))
  have e : fiberHom g x = (Ideal.quotEquivOfEq (ideal_eq_map g x).symm : _ →+* _).comp
      (Ideal.quotientMap _ (polyGermHom (x : Fin n → 𝕜)) Ideal.le_comap_map) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p ↦ ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, fiberHom, Ideal.Quotient.lift_mk,
      RingHom.comp_apply, RingHom.comp_apply, Ideal.quotientMap_mk]
    rfl
  rw [e]
  exact h.comp (RingHom.Flat.of_bijective (Ideal.quotEquivOfEq _).bijective)

/-- `𝒪_{Spec(A)^an, x}` is flat over `A = 𝕜[x]/(g)`. -/
theorem flat_stalkGermHom : (stalkGermHom g x).Flat := by
  have e : stalkGermHom g x = ((polynomialModel g).stalkIso x).symm.toRingHom.comp
      (fiberHom g x) := by
    refine RingHom.ext fun a ↦ ?_
    exact (((polynomialModel g).stalkIso x).symm_apply_apply _).symm.trans
      (congrArg _ (stalkIso_stalkGermHom g x a))
  rw [e]
  exact (flat_fiberHom g x).comp
    (RingHom.Flat.of_bijective ((polynomialModel g).stalkIso x).symm.bijective)

omit [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] in
/-- Flatness of a stalk map into an affine scheme can be tested after composition with
`R → 𝒪_{Spec R, p}`. -/
lemma flat_stalkMap_of_flat_comp {R : CommRingCat} {Y : LocallyRingedSpace}
    (f : Y ⟶ Spec.locallyRingedSpaceObj R) (y : Y)
    (h : (StructureSheaf.toStalk R (f.base y) ≫ f.stalkMap y).hom.Flat) :
    (f.stalkMap y).hom.Flat := by
  let P : PrimeSpectrum R := f.base y
  exact RingHom.Flat.of_comp_isLocalization (Rp := (Spec.structureSheaf R).presheaf.stalk P)
    P.asIdeal.primeCompl (f.stalkMap y).hom h

/-- **XII.1.1/XII.2.1: `φ : Spec(A)^an → Spec A` is flat**: the local homomorphisms
`𝒪_{Spec A, φ(x)} → 𝒪_{Spec(A)^an, x}` are flat. -/
theorem flat_stalkMap_toSpec : ((toSpec g).stalkMap x).hom.Flat := by
  refine flat_stalkMap_of_flat_comp (toSpec g) x ?_
  have h := toStalk_stalkMap_toSpec (g := g) x
  exact (congrArg (fun φ ↦ φ.hom.Flat) h).mpr (flat_stalkGermHom g x)

omit [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] in
/-- A flat stalk map of a morphism of locally ringed spaces is faithfully flat. -/
lemma faithfullyFlat_stalkMap_of_flat {X Y : LocallyRingedSpace} (f : X ⟶ Y) (y : X)
    (h : (f.stalkMap y).hom.Flat) : (f.stalkMap y).hom.FaithfullyFlat := by
  algebraize [(f.stalkMap y).hom]
  rw [← RingHom.algebraMap_toAlgebra (f.stalkMap y).hom, RingHom.faithfullyFlat_algebraMap_iff]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base y)) (X.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The local homomorphisms `𝒪_{Spec A, φ(x)} → 𝒪_{Spec(A)^an, x}` are faithfully flat. -/
theorem faithfullyFlat_stalkMap_toSpec : ((toSpec g).stalkMap x).hom.FaithfullyFlat :=
  faithfullyFlat_stalkMap_of_flat (toSpec g) x (flat_stalkMap_toSpec g x)

end AnalyticGeometry

end
