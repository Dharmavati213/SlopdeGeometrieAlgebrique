/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import SGA.SGA1.ExposeI.Etale
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeI.Unibranch

/-!
# SGA 1, Exposé I, §10: étale coverings of a normal scheme

Mathlib's relative normalization `f.normalization` of `Y` in `f_* 𝒪_X` and Zariski's
Main Theorem give the geometric core of I.10.1–I.10.2 directly: a separated
quasi-compact étale `X ⟶ Y` is an open subscheme of the normalization of `Y` in `X`, and
it is finite iff it is that normalization. The affine form of I.10.2 (a finite étale
domain over a normal domain is the integral closure in its fraction field) follows from
I.9.5. The correspondence I.10.3 between connected étale coverings of `Spec A` and
extensions of `Frac(A)` unramified over `A` is proved for a noetherian normal domain `A`
(on objects and morphisms). The sorites I.10.4, the base change of normalizations
I.10.5 and its compositum form I.10.6 are proved in affine form (using mathlib's smooth
base change of integral closures and I.9.5).

The counting of geometric points (I.10.7–I.10.11) is stated here, with the geometric number of
points `geometricFiberCard` defined; the statements are proved in `GeometricPoints` (EGA IV 15.5.1
and the strict localization). SGA's "semi-continue supérieurement" is stated in the direction that
holds (`n(y) ≤ n(y')` near `y`). The local statement I.10.12 is in `SeparableDegreeFibre`.
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- I.10, the preliminaries to I.10.7: étale morphisms (of finite presentation) are
universally open. -/
instance (priority := 100) universallyOpen_of_etale [Etale f] : UniversallyOpen f :=
  inferInstance

/-- I.10.1, via Zariski's Main Theorem: a separated quasi-compact étale morphism
`X ⟶ Y` identifies `X` with an open subscheme of the normalization of `Y` in `X`
(which is integral over `Y`). SGA further identifies this normalization with that of
`Y` in the ring of rational functions `R(X)` when `Y` is normal. -/
instance isOpenImmersion_toNormalization_of_etale [Etale f] [IsSeparated f] [QuasiCompact f] :
    IsOpenImmersion f.toNormalization :=
  inferInstance

/-- I.10.2: a morphism locally of finite type (e.g. a separated quasi-compact étale one)
is finite iff it is the normalization of `Y` in `X`. (Quasi-compactness and
quasi-separatedness are needed for the relative normalization to be defined.) -/
theorem isFinite_iff_isIso_toNormalization [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiSeparated f] :
    IsFinite f ↔ IsIso f.toNormalization := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ?_⟩
  have : IsIntegralHom f := by
    rw [← f.toNormalization_fromNormalization]; infer_instance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mpr ⟨inferInstance, inferInstance⟩

section Affine

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- I.10.2, affine form: if `A` is an integrally closed domain and `B` is a finite étale
`A`-algebra which is a domain, then `B` is the integral closure of `A` in its fraction
field, i.e. `Spec B` is the normalization of `Spec A` in `R(Spec B)`. -/
theorem isIntegralClosure_of_etale [IsDomain A] [IsIntegrallyClosed A] [Algebra.Etale A B]
    [Module.Finite A B] [IsDomain B] :
    IsIntegralClosure B A (FractionRing B) := by
  have : IsIntegrallyClosed B := isIntegrallyClosed_of_etale (A := A)
  refine ⟨IsFractionRing.injective B _, fun {x} ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · have : IsIntegral B x := hx.tower_top
    exact (isIntegrallyClosed_iff (FractionRing B)).mp inferInstance this
  · rintro ⟨y, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := A) y).map (IsScalarTower.toAlgHom A B _)

/-- I.10.3 (affine form): a finite algebra `L` over the fraction field `K` of a normal
domain `A` is *unramified over* `Spec A` if the integral closure of `A` in `L` is étale
over `A`. (SGA also asks `L` separable, which then follows.) -/
def IsUnramifiedOver (L : Type u) [CommRing L] [Algebra A L] : Prop :=
  Algebra.Etale A (integralClosure A L)

/-- I.10.4(i): the fraction field `K` of a normal domain `A` is unramified over `Spec A`. -/
theorem isUnramifiedOver_fractionRing [IsDomain A] [IsIntegrallyClosed A] :
    IsUnramifiedOver A (FractionRing A) := by
  have e : A ≃ₐ[A] integralClosure A (FractionRing A) :=
    (Algebra.botEquivOfInjective (IsFractionRing.injective A (FractionRing A))).symm.trans
      (Subalgebra.equivOfEq _ _ (IsIntegrallyClosed.integralClosure_eq_bot A _).symm)
  exact Algebra.Etale.of_equiv e

/-- I.10.5, in mathlib's form: étale (indeed smooth) base change commutes with integral
closure, `B ⊗_A Ā_C ≅ \overline{B}_{B ⊗_A C}`. SGA's statement (the normalization of
`A'` in `L ⊗_K K'` is `Ā ⊗_A A'` for `Ā` étale over `A`) is obtained from this together
with I.9.5(i). -/
theorem bijective_toIntegralClosure_of_etale [Algebra.Etale A B] (C : Type u) [CommRing C]
    [Algebra A C] : Function.Bijective (TensorProduct.toIntegralClosure A B C) :=
  TensorProduct.toIntegralClosure_bijective_of_smooth

end Affine

section Correspondence

open Algebra

variable (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]

omit [IsIntegrallyClosed A] in
/-- An `A`-algebra map from a domain `B` integral over `A` to a domain into which `A`
injects is injective (a nonzero prime of `B` cannot lie over `0`). -/
lemma injective_of_isIntegral {B B' : Type u} [CommRing B] [CommRing B'] [IsDomain B]
    [IsDomain B'] [Algebra A B] [Algebra A B'] [Algebra.IsIntegral A B]
    [FaithfulSMul A B'] (f : B →ₐ[A] B') : Function.Injective f := by
  rw [injective_iff_map_eq_zero']
  intro x
  refine ⟨fun hx ↦ ?_, fun hx ↦ hx ▸ map_zero f⟩
  have hP : (RingHom.ker f).comap (algebraMap A B) = ⊥ := by
    ext a
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.mem_bot]
    exact ⟨fun h ↦ FaithfulSMul.algebraMap_injective A B' (h.trans (map_zero _).symm),
      fun h ↦ by rw [h, map_zero]⟩
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have := Ideal.eq_bot_of_comap_eq_bot hP
  rw [← RingHom.mem_ker, this, Ideal.mem_bot] at hx
  exact hx


omit [IsIntegrallyClosed A] in
/-- A flat algebra over a domain which is a domain is faithful. -/
lemma faithfulSMul_of_flat (B : Type u) [CommRing B] [IsDomain B] [Algebra A B]
    [Module.Flat A B] : FaithfulSMul A B := by
  rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  have := (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
    (mem_nonZeroDivisors_of_ne_zero h0)).right_eq_zero_of_smul (x := (1 : B))
    (by rw [Algebra.smul_def, mul_one, ha])
  exact one_ne_zero this

variable (B B' : Type u) [CommRing B] [CommRing B'] [IsDomain B] [IsDomain B'] [Algebra A B]
  [Algebra A B'] [Algebra.Etale A B] [Algebra.Etale A B'] [Module.Finite A B]
  [Module.Finite A B']

/-- I.10.3 (affine form), on morphisms: for finite étale `A`-algebras `B`, `B'` which are
domains (connected étale coverings of `Spec A`), `A`-algebra maps `B → B'` correspond
bijectively to maps of their fraction fields (the functor `X ↦ R(X)` is fully faithful). -/
noncomputable def algHomEquivFractionRing :
    (B →ₐ[A] B') ≃ (FractionRing B →ₐ[A] FractionRing B') :=
  have := faithfulSMul_of_flat A B'
  have hB' := isIntegralClosure_of_etale A B'
  have hinj (f : B →ₐ[A] B') :
      Function.Injective ((IsScalarTower.toAlgHom A B' (FractionRing B')).comp f) :=
    (IsFractionRing.injective B' _).comp (injective_of_isIntegral A f)
  let e := IsIntegralClosure.equiv A (integralClosure A (FractionRing B')) (FractionRing B') B'
  have hint (σ : FractionRing B →ₐ[A] FractionRing B') (b : B) :
      σ (algebraMap B (FractionRing B) b) ∈ integralClosure A (FractionRing B') :=
    (Algebra.IsIntegral.isIntegral (R := A) b).map
      (σ.comp (IsScalarTower.toAlgHom A B (FractionRing B)))
  { toFun f := IsFractionRing.liftAlgHom (hinj f)
    invFun σ := e.toAlgHom.comp ((σ.comp (IsScalarTower.toAlgHom A B _)).codRestrict _
      (hint σ))
    left_inv f := by
      ext b
      apply IsFractionRing.injective B' (FractionRing B')
      simp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom, e,
        IsIntegralClosure.algebraMap_equiv]
      change IsFractionRing.liftAlgHom (hinj f) (algebraMap B (FractionRing B) b) = _
      rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
      rfl
    right_inv σ := by
      refine IsLocalization.algHom_ext (nonZeroDivisors B) ?_
      ext b
      change IsFractionRing.liftAlgHom (hinj _) (algebraMap B (FractionRing B) b) =
        σ (algebraMap B (FractionRing B) b)
      rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
      simp [e, IsIntegralClosure.algebraMap_equiv]
      rfl }


/-- I.10.3 (affine form), on objects: the fraction field `R(X)` of a connected étale
covering `X = Spec B` of `Spec A` is unramified over `Spec A`, and `B` is the integral
closure of `A` in it. -/
theorem isUnramifiedOver_fractionRing_of_etale :
    IsUnramifiedOver A (FractionRing B) ∧ Nonempty (integralClosure A (FractionRing B) ≃ₐ[A] B) :=
  have := isIntegralClosure_of_etale A B
  let e := IsIntegralClosure.equiv A (integralClosure A (FractionRing B)) (FractionRing B) B
  ⟨Algebra.Etale.of_equiv e.symm, ⟨e⟩⟩

/-- I.10.3 (affine form), essential surjectivity: if `A` is noetherian and `L` is a finite
separable extension of `K = Frac(A)` unramified over `Spec A`, the normalization of `A` in
`L` is a connected étale covering of `Spec A` with function field `L`. -/
theorem finite_etale_integralClosure [IsNoetherianRing A] (L : Type u) [Field L]
    [Algebra (FractionRing A) L] [Algebra A L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] [Algebra.IsSeparable (FractionRing A) L]
    (h : IsUnramifiedOver A L) :
    Module.Finite A (integralClosure A L) ∧ Algebra.Etale A (integralClosure A L) ∧
      IsFractionRing (integralClosure A L) L :=
  ⟨IsIntegralClosure.finite A (FractionRing A) L (integralClosure A L), h,
    IsIntegralClosure.isFractionRing_of_finite_extension A (FractionRing A) L
      (integralClosure A L)⟩

end Correspondence

section Sorites

open scoped TensorProduct

/-- I.10.4(ii), transitivity (affine form): let `A' ` be the normalization of `A` in an
extension `L` unramified over `A` (so `A'` is integral and étale over `A`), and let `M` be an
`A'`-algebra unramified over `A'`. Then `M` is unramified over `A`. -/
theorem isUnramifiedOver_trans (A A' M : Type u) [CommRing A] [CommRing A'] [CommRing M]
    [Algebra A A'] [Algebra A' M] [Algebra A M] [IsScalarTower A A' M] [Algebra.IsIntegral A A']
    [Algebra.Etale A A'] (h : IsUnramifiedOver A' M) : IsUnramifiedOver A M := by
  have heq : integralClosure A M = (integralClosure A' M).restrictScalars A := by
    ext x
    simp only [mem_integralClosure_iff, Subalgebra.mem_restrictScalars]
    exact ⟨fun hx ↦ hx.tower_top, fun hx ↦ isIntegral_trans x hx⟩
  have : Algebra.Etale A' (integralClosure A' M) := h
  have : Algebra.Etale A (integralClosure A' M) := Algebra.Etale.comp A A' _
  have : Algebra.Etale A ((integralClosure A' M).restrictScalars A) := this
  exact Algebra.Etale.of_equiv (Subalgebra.equivOfEq _ _ heq).symm

/-- I.10.5, SGA's form, and I.10.4(iii) (translation), affine: let `A → A'` be a map of
domains with `A'` integrally closed with fraction field `K'`, and let `Ā` be finite étale
over `A` (e.g. the normalization of `A` in an extension `L` of `K` unramified over `A`).
Then `A' ⊗_A Ā` is étale over `A'` and it is the normalization of `A'` in
`(A' ⊗_A Ā) ⊗_{A'} K'` (which is `L ⊗_K K'` when `Ā` is the normalization of `A` in `L`).
In particular `L ⊗_K K'` is unramified over `A'`. -/
theorem isIntegralClosure_tensor_of_etale (A A' Abar K' : Type u) [CommRing A] [CommRing A']
    [CommRing Abar] [Algebra A A'] [Algebra A Abar] [IsDomain A'] [IsIntegrallyClosed A']
    [Field K'] [Algebra A' K'] [IsFractionRing A' K'] [Algebra.Etale A Abar]
    [Algebra.IsIntegral A Abar] :
    Algebra.Etale A' (A' ⊗[A] Abar) ∧
      IsIntegralClosure (A' ⊗[A] Abar) A' ((A' ⊗[A] Abar) ⊗[A'] K') := by
  refine ⟨inferInstance, ?_⟩
  have hIC := isIntegrallyClosedIn_tensor_fractionRing (A := A') (B := A' ⊗[A] Abar) K'
  refine ⟨hIC.algebraMap_injective, fun {x} ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
  · exact hIC.isIntegral_iff.mp hx.tower_top
  · rintro ⟨y, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := A') y).algebraMap

/-- I.10.6 (affine form): let `A'` be an integrally closed domain over `A` with fraction field
`K'`, `Ā` finite étale over `A` (e.g. the normalization of `A` in an extension `L` unramified
over `A`), and `L₁` a field generated over `K'` by the image of an `A`-algebra map
`ι : Ā → L₁` (e.g. a compositum of `L` and `K'`). Then the normalization of `A'` in `L₁` is
the algebra `A'[ι Ā]` generated by `A'` and `Ā`, and it is étale over `A'`: `L₁` is
unramified over `A'`. -/
theorem integralClosure_eq_adjoin_of_etale (A A' Abar K' L₁ : Type u) [CommRing A]
    [CommRing A'] [CommRing Abar] [Algebra A A'] [Algebra A Abar] [IsDomain A']
    [IsIntegrallyClosed A'] [Algebra.Etale A Abar] [Algebra.IsIntegral A Abar] [Field K']
    [Algebra A' K'] [IsFractionRing A' K'] [Field L₁] [Algebra A' L₁] [Algebra K' L₁]
    [IsScalarTower A' K' L₁] [Algebra A L₁] [IsScalarTower A A' L₁] (ι : Abar →ₐ[A] L₁)
    (hι : Algebra.adjoin K' (Set.range ι) = ⊤) :
    integralClosure A' L₁ = Algebra.adjoin A' (Set.range ι) ∧ IsUnramifiedOver A' L₁ := by
  classical
  let T := A' ⊗[A] Abar
  let E := T ⊗[A'] K'
  obtain ⟨hTet, hIC⟩ := isIntegralClosure_tensor_of_etale A A' Abar K'
  let φ : T →ₐ[A'] L₁ := Algebra.TensorProduct.lift (Algebra.ofId A' L₁) ι
    fun _ _ ↦ Commute.all _ _
  let Φ : E →ₐ[A'] L₁ := Algebra.TensorProduct.lift φ (IsScalarTower.toAlgHom A' K' L₁)
    fun _ _ ↦ Commute.all _ _
  have hΦφ (t : T) : Φ (algebraMap T E t) = φ t := by
    change Φ (t ⊗ₜ 1) = φ t
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  have hφι (b : Abar) : φ (1 ⊗ₜ b) = ι b := by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  -- `Φ` is surjective, since `L₁` is generated over `K'` by `ι Ā`
  have hsurj : Function.Surjective Φ := by
    let S : Subalgebra K' L₁ :=
      { Φ.range.toSubring with
        algebraMap_mem' := fun k ↦ ⟨1 ⊗ₜ k, by
          change Φ (1 ⊗ₜ k) = _
          rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl⟩ }
    have hS : S = ⊤ := by
      rw [_root_.eq_top_iff, ← hι, Algebra.adjoin_le_iff]
      rintro _ ⟨b, rfl⟩
      exact ⟨algebraMap T E (1 ⊗ₜ b), (hΦφ _).trans (hφι b)⟩
    intro y
    have : y ∈ S := hS ▸ Algebra.mem_top
    exact this
  -- `E ≅ K' ⊗_{A'} T` is a reduced artinian ring, so `ker Φ` is cut out by an idempotent
  let eE : E ≃ₐ[A'] K' ⊗[A'] T := Algebra.TensorProduct.comm A' T K'
  have : Module.Finite K' (K' ⊗[A'] T) := Algebra.FormallyUnramified.finite_of_free K' _
  have : IsArtinianRing (K' ⊗[A'] T) := isArtinian_of_tower K' inferInstance
  have : IsReduced (K' ⊗[A'] T) := Algebra.FormallyUnramified.isReduced_of_field K' _
  have : IsArtinianRing E := eE.symm.toRingEquiv.isArtinianRing
  have : IsReduced E := isReduced_of_injective eE.toRingHom eE.injective
  let M := RingHom.ker Φ
  have hM : M.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  let m : MaximalSpectrum E := ⟨M, hM⟩
  let π := IsArtinianRing.equivPi E
  let e : E := π.symm (Pi.single m 1)
  have hπe : π e = Pi.single m 1 := π.apply_symm_apply _
  have he1 : Φ e = 1 := by
    have : 1 - e ∈ M := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change π (1 - e) m = 0
      rw [map_sub, map_one, hπe]
      simp
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  have he2 (x : E) (hx : Φ x = 0) : e * x = 0 := by
    apply π.injective
    rw [map_mul, hπe, map_zero]
    funext m'
    by_cases hm : m' = m
    · subst hm
      simp only [Pi.mul_apply, Pi.single_eq_same, one_mul, Pi.zero_apply]
      change Ideal.Quotient.mk M x = 0
      rwa [Ideal.Quotient.eq_zero_iff_mem]
    · simp [Pi.single_eq_of_ne hm]
  -- the idempotent `e` is integral over `A'`, so it comes from `T`
  obtain ⟨e', he'⟩ := hIC.isIntegral_iff.mp (show IsIntegral A' e from
    ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), by
      have : e * e = e := π.injective (by rw [map_mul, hπe, ← Pi.single_mul, mul_one])
      simp [sq, this]⟩)
  have hφe : φ e' = 1 := by rw [← hΦφ, he', he1]
  -- the normalization of `A'` in `L₁` is the image of `T`
  have hrange : integralClosure A' L₁ = φ.range := by
    refine le_antisymm (fun y hy ↦ ?_) ?_
    · obtain ⟨z, rfl⟩ := hsurj y
      obtain ⟨p, hp, hpz⟩ := (mem_integralClosure_iff _ _).mp hy
      have hw : IsIntegral A' (e * z) := by
        refine ⟨Polynomial.X * p, Polynomial.monic_X.mul hp, ?_⟩
        have h0 : e * Polynomial.aeval (e * z) p = 0 := he2 _ (by
          rw [← Polynomial.aeval_algHom_apply, map_mul, he1, one_mul, Polynomial.aeval_def]
          exact hpz)
        rw [← Polynomial.aeval_def, map_mul, Polynomial.aeval_X, mul_right_comm, h0, zero_mul]
      obtain ⟨t, ht⟩ := hIC.isIntegral_iff.mp hw
      exact ⟨t, show φ t = Φ z by rw [← hΦφ, ht, map_mul, he1, one_mul]⟩
    · rintro _ ⟨t, rfl⟩
      exact (Algebra.IsIntegral.isIntegral (R := A') t).map φ
  -- the image of `T` is the algebra generated by `A'` and `ι Ā`
  have hadj : φ.range = Algebra.adjoin A' (Set.range ι) := by
    refine le_antisymm ?_ (Algebra.adjoin_le ?_)
    · rintro _ ⟨t, rfl⟩
      change φ t ∈ _
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact zero_mem _
      | tmul a b =>
        rw [Algebra.TensorProduct.lift_tmul]
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a)
          (Algebra.subset_adjoin ⟨b, rfl⟩)
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · rintro _ ⟨b, rfl⟩
      exact ⟨1 ⊗ₜ b, hφι b⟩
  -- it is the localization `T[1/e']`, hence étale over `A'`
  have hker (t : T) (ht : φ t = 0) : e' * t = 0 := by
    apply hIC.algebraMap_injective
    rw [map_mul, he', map_zero]
    exact he2 _ (by rw [hΦφ, ht])
  have hpow (s : Submonoid.powers e') : φ s = 1 := by
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    rw [← hn, map_pow, hφe, one_pow]
  let ψ : Localization.Away e' →ₐ[A'] L₁ := IsLocalization.liftAlgHom
    (M := Submonoid.powers e') (f := φ) fun s ↦ by rw [hpow]; exact isUnit_one
  have hψ (t : T) (s : Submonoid.powers e') :
      ψ (IsLocalization.mk' (Localization.Away e') t s) = φ t := by
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec]
    simp [hpow]
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨t, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers e') x
    rw [hψ] at hx
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨e', Submonoid.mem_powers e'⟩, hker t hx⟩
  have hψrange : ψ.range = φ.range := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨⟨t, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers e') x
      exact ⟨t, (hψ t s).symm⟩
    · rintro _ ⟨t, rfl⟩
      refine ⟨algebraMap T _ t, ?_⟩
      change ψ (algebraMap T _ t) = φ t
      rw [← IsLocalization.mk'_one (M := Submonoid.powers e'), hψ]
  refine ⟨hrange.trans hadj, ?_⟩
  exact Algebra.Etale.of_equiv ((AlgEquiv.ofInjective ψ hψinj).trans
    (Subalgebra.equivOfEq _ _ (hrange.trans hψrange.symm).symm))

end Sorites

/-- I.10.7: the geometric number of points of the fibre `f⁻¹(y)`, the sum of the
separable degrees `[κ(x) : κ(y)]_s` over `x ∈ f⁻¹(y)` (zero if the fibre is infinite). -/
noncomputable def geometricFiberCard (y : Y) : ℕ :=
  ∑ᶠ x : f ⁻¹' {y}, letI := (f.residueFieldMap x.1).hom.toAlgebra
    Field.finSepDegree (Y.residueField (f x.1)) (X.residueField x.1)

/-- I.10.11: the degree of `f` at `y`, the sum of the degrees `[κ(x) : κ(y)]` over
`x ∈ f⁻¹(y)`. At the generic point this is SGA's degree `n = ∑ [K_i : K]`. -/
noncomputable def fiberDegree (y : Y) : ℕ :=
  ∑ᶠ x : f ⁻¹' {y}, f.residueDegree x.1

/-- I.10.7 (statement; proved in `SGA.SGA1.ExposeI.GeometricPoints`, EGA IV 15.5.1): for a
quasi-finite separated universally open morphism of finite type, `y ↦ n(y)` is lower
semicontinuous (`n(y) ≤ n(y')` for `y'` near `y`:
geometric points of fibres can merge under specialization, but not disappear), and if it is
constant near `y` then `f` is finite over a neighbourhood of `y`. SGA calls this "semi-continue
supérieurement"; the inequality is stated here in the direction that holds (for an open immersion
`n` is `0` off the image and `1` on it). -/
def geometricFiberCard_upperSemicontinuous_Statement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyQuasiFinite f] [IsSeparated f] [UniversallyOpen f],
    (∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ∀ y' ∈ U, geometricFiberCard f y ≤ geometricFiberCard f y') ∧
    ∀ y : Y, (∃ U : Y.Opens, y ∈ U ∧ ∀ y' ∈ U, geometricFiberCard f y' = geometricFiberCard f y) →
      ∃ U : Y.Opens, y ∈ U ∧ IsFinite (f ∣_ U)

/-- A scheme is geometrically unibranch at every point if all its local rings are
geometrically unibranch local domains (I.11). -/
def IsGeometricallyUnibranchScheme (Y : Scheme.{u}) : Prop :=
  ∀ y : Y, ∃ _ : IsDomain (Y.presheaf.stalk y), IsGeometricallyUnibranch (Y.presheaf.stalk y)

/-- I.10.8 (statement; proved in `SGA.SGA1.ExposeI.GeometricPoints`): under I.10.7, if `n` is
constant and `Y` is geometrically unibranch, the irreducible components of `X` are pairwise
disjoint. -/
def disjoint_irreducibleComponents_Statement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyQuasiFinite f] [IsSeparated f] [UniversallyOpen f],
    IsGeometricallyUnibranchScheme Y → (∀ y y', geometricFiberCard f y = geometricFiberCard f y') →
      ∀ Z₁ ∈ irreducibleComponents X, ∀ Z₂ ∈ irreducibleComponents X, Z₁ ≠ Z₂ → Disjoint Z₁ Z₂

/-- I.10.9 (statement; proved in `SGA.SGA1.ExposeI.GeometricPoints`): for a separated étale
quasi-compact `f`, `n` is lower semicontinuous (see I.10.7 for the direction), and it is constant
near `y` iff `f` is an étale covering (finite) over a neighbourhood of `y`. -/
def geometricFiberCard_etale_Statement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f],
    (∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ∀ y' ∈ U, geometricFiberCard f y ≤ geometricFiberCard f y') ∧
    ∀ y : Y, (∃ U : Y.Opens, y ∈ U ∧ ∀ y' ∈ U, geometricFiberCard f y' = geometricFiberCard f y) ↔
      ∃ U : Y.Opens, y ∈ U ∧ IsFinite (f ∣_ U)

/-- I.10.10 (statement; proved in `SGA.SGA1.ExposeI.GeometricPoints`): a separated étale
quasi-compact morphism to a connected scheme is finite (an étale covering) iff all its fibres
have the same geometric number of points. -/
def isFinite_iff_geometricFiberCard_const_Statement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f]
    [ConnectedSpace Y],
    IsFinite f ↔ ∀ y y', geometricFiberCard f y = geometricFiberCard f y'

/-- I.10.11 (statement; proved in `SGA.SGA1.ExposeI.GeometricPoints`): let `f` be quasi-finite,
separated, of finite type, with `Y` locally noetherian (SGA's standing hypothesis) and irreducible,
`X` reduced and every irreducible component of `X` dominating `Y`, and let `y` be a point where
`Y` is normal. Then `n(y) ≤ n`, the degree at the generic point, with equality iff `f` is an étale
covering over a neighbourhood of `y`. -/
def geometricFiberCard_le_degree_Statement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyQuasiFinite f] [IsSeparated f] [IrreducibleSpace Y] [IsReduced X]
    [IsLocallyNoetherian Y],
    (∀ Z ∈ irreducibleComponents X, Dense (f '' Z)) →
    ∀ y : Y, IsDomain (Y.presheaf.stalk y) → IsIntegrallyClosed (Y.presheaf.stalk y) →
      geometricFiberCard f y ≤ fiberDegree f (genericPoint Y) ∧
      (geometricFiberCard f y = fiberDegree f (genericPoint Y) ↔
        ∃ U : Y.Opens, y ∈ U ∧ IsFinite (f ∣_ U) ∧ Etale (f ∣_ U))

end SGA.SGA1.ExposeI
