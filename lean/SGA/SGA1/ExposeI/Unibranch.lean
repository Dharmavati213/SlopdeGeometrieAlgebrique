/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RingHom.PurelyInseparable
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.SurjectiveOnStalks
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import SGA.SGA1.ExposeI.DominantUnramified
import SGA.Foundations.CompleteLocalQuasiFinite
import SGA.Foundations.HenselianFiniteEtale

/-!
# SGA 1, Exposé I, §11: geometrically unibranch schemes

A local domain is geometrically unibranch when its normalisation has a unique
prime over the maximal ideal and the residue-field extension is purely
inseparable. The exposé's examples (a nodal curve and `ℝ[[s,t]]/(s²+t²)`)
show that without this hypothesis a connected étale covering of an integral
scheme need not be integral.

The theorem of I.11 is proved: if all local rings of `Y` are geometrically unibranch domains,
every connected unramified `Y`-scheme of finite type dominating `Y` is étale and irreducible
(`etale_and_irreducibleSpace_of_formallyUnramified_of_isGeometricallyUnibranch`). SGA's proof
"follows that of I.9.5"; the key point (EGA IV 18.10) is that a local ring `D` of an étale
algebra over a geometrically unibranch `A` at a point over `𝔪_A` is a domain: `D ⊗_A A'`
(`A'` the normalization) is local, since `κ(𝔪')` is purely inseparable over `κ(𝔪_A)`, and it
is a local ring of an étale algebra over the normal domain `A'`, so a domain containing `D`.
No finiteness of the normalization is needed. The complete local example b) is proved as well
(`exists_finite_etale_not_isDomain`): over a complete noetherian local domain which is not
geometrically unibranch there is a finite étale local algebra which is not a domain. A complete
local domain is unibranch (a finite domain over it is local, by lifting idempotents), and a
separable element `α ∉ k` of the residue extension of the normalization gives, with the finite
étale lift `B` of `k(α)`, two maximal ideals of `B ⊗_A A[x]` (`x` a lift of `α`); SGA's proof
uses Nagata's finiteness of the normalization instead. The invariance of the étale site under
universal homeomorphisms (IX.4.10, proved in Exposé IX) is
`etale_baseChange_isEquivalence_of_universalHomeomorph` in `EtaleSiteInvariance`.
-/

universe u

namespace SGA.SGA1.ExposeI

open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped TensorProduct IntermediateField

section PowTensor

variable {A R L : Type*} [CommRing A] [CommRing R] [CommRing L] [Algebra A R] [Algebra A L]

/-- If every element of `L` has a `q^n`-th power coming from `A`, and `R ⊗_A L` has exponential
characteristic `q`, then every element of `R ⊗_A L` has a `q^n`-th power coming from `R`. -/
lemma exists_pow_pow_mem_range_tensorProduct (q : ℕ) [ExpChar (R ⊗[A] L) q]
    (H : ∀ y : L, ∃ (n : ℕ) (a : A), y ^ q ^ n = algebraMap A L a) (x : R ⊗[A] L) :
    ∃ n, x ^ q ^ n ∈ (algebraMap R (R ⊗[A] L)).range := by
  induction x with
  | zero => exact ⟨0, 0, by simp⟩
  | add x y hx hy =>
    simp_rw [RingHom.mem_range, ← RingHom.mem_rangeS, ← Subalgebra.mem_perfectClosure_iff]
      at hx hy ⊢
    exact add_mem hx hy
  | tmul r y =>
    obtain ⟨n, a, ha⟩ := H y
    refine ⟨n, algebraMap A R a * r ^ q ^ n, ?_⟩
    rw [Algebra.TensorProduct.tmul_pow, ha]
    change (algebraMap A R a * r ^ q ^ n) ⊗ₜ[A] (1 : L) = _
    rw [← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

end PowTensor

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]

/-- The integral closure of a local domain in its fraction field. -/
abbrev normalizationRing : Type u := integralClosure A (FractionRing A)

/-- I.11: `A` is unibranch when its normalisation has a unique prime over the
maximal ideal. -/
def IsUnibranch : Prop :=
  Subsingleton ((maximalIdeal A).primesOver (normalizationRing A))

/-- I.11: `A` is geometrically unibranch when it is unibranch and every residue
extension of the normalisation over `A` is purely inseparable. -/
def IsGeometricallyUnibranch : Prop :=
  IsUnibranch A ∧
    ∀ Q : (maximalIdeal A).primesOver (normalizationRing A),
      (Ideal.ResidueField.map (maximalIdeal A) Q.1 (algebraMap A (normalizationRing A))
        Q.2.2.over).IsPurelyInseparable

omit [IsDomain A] in
/-- I.11, example: a normal local domain is geometrically unibranch (its normalization is
itself). -/
theorem isGeometricallyUnibranch_of_isIntegrallyClosed [IsIntegrallyClosed A] :
    IsGeometricallyUnibranch A := by
  have hbij : Function.Bijective (algebraMap A (normalizationRing A)) := by
    refine ⟨fun x y h ↦ IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val h),
      fun ⟨z, hz⟩ ↦ ?_⟩
    obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff (FractionRing A)).mp inferInstance hz
    exact ⟨a, Subtype.ext ha⟩
  refine ⟨⟨fun Q₁ Q₂ ↦ Subtype.ext ?_⟩, fun Q ↦ ?_⟩
  · refine Ideal.comap_injective_of_surjective _ hbij.2 ?_
    change Q₁.1.under A = Q₂.1.under A
    rw [← Q₁.2.2.over, ← Q₂.2.2.over]
  · have := Q.2.1
    have hb := (RingHom.surjectiveOnStalks_of_surjective hbij.2).residueFieldMap_bijective
      (maximalIdeal A) Q.1 Q.2.2.over
    algebraize [(Ideal.ResidueField.map (maximalIdeal A) Q.1 (algebraMap A (normalizationRing A))
      Q.2.2.over)]
    exact (AlgEquiv.ofBijective (Algebra.ofId _ _) hb).isPurelyInseparable

section Normalization

omit [IsLocalRing A] [IsDomain A] in
lemma injective_algebraMap_normalizationRing :
    Function.Injective (algebraMap A (normalizationRing A)) :=
  fun _ _ h ↦ IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val h)

variable {A}

omit [IsDomain A] in
/-- If `A` is geometrically unibranch and `D` is a local `A`-algebra with local structure map, the
ring `D ⊗_A A'` is local, `A'` the normalization of `A`: its maximal ideals lie over `𝔪_D` and
over the unique prime `𝔪'` of `A'` over `𝔪_A`, and `κ(D) ⊗_A κ(𝔪')` has a single prime since
`κ(𝔪')` is purely inseparable over `κ(𝔪_A)`. -/
theorem isLocalRing_tensor_normalizationRing (hA : IsGeometricallyUnibranch A)
    (D : Type u) [CommRing D] [IsLocalRing D] [Algebra A D] [IsLocalHom (algebraMap A D)]
    [Nontrivial (D ⊗[A] normalizationRing A)] :
    IsLocalRing (D ⊗[A] normalizationRing A) := by
  classical
  let A' := normalizationRing A
  let E := D ⊗[A] A'
  suffices H : ∀ (M₁ M₂ : Ideal E), M₁.IsMaximal → M₂.IsMaximal → M₁ = M₂ by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal E
    exact .of_unique_max_ideal ⟨M, hM, fun M' hM' ↦ H _ _ hM' hM⟩
  intro M₁ M₂ hM₁ hM₂
  -- the maximal ideals of `E` lie over `𝔪_D` (`E` is integral over `D`) ...
  have hD (M : Ideal E) [M.IsMaximal] : M.comap (algebraMap D E) = maximalIdeal D :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
  -- ... and over the unique prime `𝔪'` of `A'` over `𝔪_A`
  let Q (M : Ideal E) : Ideal A' := M.comap (Algebra.TensorProduct.includeRight : A' →ₐ[A] E)
  have hQ (M : Ideal E) [M.IsMaximal] : Q M ∈ (maximalIdeal A).primesOver A' := by
    refine ⟨Ideal.comap_isPrime _ _, ⟨?_⟩⟩
    have hcomp : (Algebra.TensorProduct.includeRight : A' →ₐ[A] E).toRingHom.comp
        (algebraMap A A') = (algebraMap D E).comp (algebraMap A D) := by
      ext a
      simp [Algebra.TensorProduct.algebraMap_apply]
      rfl
    have : (Q M).under A = (M.comap (algebraMap D E)).comap (algebraMap A D) := by
      simp only [Q, Ideal.under, Ideal.comap_comap]
      exact congrArg (fun f ↦ Ideal.comap f M) hcomp
    rw [this, hD M, maximalIdeal_comap]
  have hQeq : Q M₁ = Q M₂ := congrArg Subtype.val (@Subsingleton.elim _ hA.1 ⟨_, hQ M₁⟩ ⟨_, hQ M₂⟩)
  let m' := Q M₁
  have hm'p : m'.IsPrime := (hQ M₁).1
  have hm' : m'.IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) m' ?_
    have h := (hQ M₁).2.over
    change maximalIdeal A = m'.comap (algebraMap A A') at h
    rw [← h]
    infer_instance
  let L := m'.ResidueField
  -- `E ⟶ κ(D) ⊗_A κ(𝔪')` has kernel `𝔪_D E + 𝔪' E`, contained in `M₁` and `M₂`
  let T := ResidueField D ⊗[A] L
  let φ : E →ₐ[A] T := Algebra.TensorProduct.map (IsScalarTower.toAlgHom A D (ResidueField D))
    (IsScalarTower.toAlgHom A A' L)
  have hφs : Function.Surjective φ := Algebra.TensorProduct.map_surjective _ _
    residue_surjective m'.algebraMap_residueField_surjective
  have hle (M : Ideal E) [M.IsMaximal] (hQM : Q M = m') : RingHom.ker φ ≤ M := by
    rw [Algebra.TensorProduct.map_ker _ _ residue_surjective m'.algebraMap_residueField_surjective]
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.map_le_iff_le_comap.mpr ?_)
    · change RingHom.ker (residue D) ≤ _
      rw [ker_residue]
      exact (hD M).ge
    · change RingHom.ker (algebraMap A' L) ≤ _
      rw [Ideal.ker_algebraMap_residueField]
      exact hQM.ge
  have hle₁ := hle M₁ rfl
  have hle₂ := hle M₂ hQeq.symm
  have : Nontrivial T := by
    refine ⟨⟨0, 1, fun h ↦ hM₁.ne_top ((Ideal.eq_top_iff_one _).mpr (hle₁ ?_))⟩⟩
    rw [RingHom.mem_ker, map_one, ← h]
  -- `κ(D) ⊗_A κ(𝔪')` has a single prime ideal
  have hT : Subsingleton (PrimeSpectrum T) := by
    let K₀ := (maximalIdeal A).ResidueField
    have hK₀L := hA.2 ⟨m', hQ M₁⟩
    algebraize [Ideal.ResidueField.map (maximalIdeal A) m' (algebraMap A A') (hQ M₁).2.over]
    let q := ringExpChar K₀
    have : ExpChar L q := expChar_of_injective_ringHom (algebraMap K₀ L).injective q
    have : ExpChar T q :=
      expChar_of_injective_ringHom (Algebra.TensorProduct.includeRight (R := A)
        (A := ResidueField D) (B := L)).toRingHom.injective q
    have H (y : L) : ∃ (n : ℕ) (a : A), y ^ q ^ n = algebraMap A L a := by
      obtain ⟨n, x, hx⟩ := IsPurelyInseparable.pow_mem K₀ q y
      obtain ⟨a, rfl⟩ := (maximalIdeal A).algebraMap_residueField_surjective x
      refine ⟨n, a, hx.symm.trans ?_⟩
      rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap,
        ← IsScalarTower.algebraMap_apply]
    have hH (x : T) : ∃ n > 0, x ^ n ∈ (algebraMap (ResidueField D) T).range := by
      obtain ⟨n, hn⟩ := exists_pow_pow_mem_range_tensorProduct q H x
      exact ⟨q ^ n, pow_pos (expChar_pos T q) n, hn⟩
    have hhom := PrimeSpectrum.isHomeomorph_comap (algebraMap (ResidueField D) T) hH (by
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (ResidueField D) T)).mp
        (RingHom.injective _)]
      exact bot_le)
    exact hhom.injective.subsingleton
  have h₁ := Ideal.IsMaximal.map_of_surjective_of_ker_le hφs hle₁
  have h₂ := Ideal.IsMaximal.map_of_surjective_of_ker_le hφs hle₂
  have h := congrArg PrimeSpectrum.asIdeal
    (Subsingleton.elim (⟨_, h₁.isPrime⟩ : PrimeSpectrum T) ⟨_, h₂.isPrime⟩)
  have e₁ := Ideal.comap_map_of_surjective' φ hφs M₁
  have e₂ := Ideal.comap_map_of_surjective' φ hφs M₂
  rw [sup_eq_left.mpr hle₁] at e₁
  rw [sup_eq_left.mpr hle₂] at e₂
  rw [← e₁, ← e₂]
  exact congrArg _ h

/-- The local ring of an étale `A`-algebra at a prime over `𝔪_A`, `A` geometrically unibranch, is
a domain (EGA IV 18.10): it embeds into `D ⊗_A A'`, a local ring of an étale algebra over the
normal domain `A'` (`isLocalRing_tensor_normalizationRing`), hence a normal domain (I.9.5(i)). -/
theorem isDomain_localization_of_etale_of_isGeometricallyUnibranch
    (hA : IsGeometricallyUnibranch A) (C : Type u) [CommRing C] [Algebra A C] [Algebra.Etale A C]
    (P : Ideal C) [P.IsPrime] (hP : P.comap (algebraMap A C) = maximalIdeal A) :
    IsDomain (Localization.AtPrime P) := by
  let A' := normalizationRing A
  let D := Localization.AtPrime P
  have : Module.Flat A D := Module.Flat.trans A C D
  have : IsLocalHom (algebraMap A D) := by
    constructor
    intro a ha
    by_contra h
    have hmem : algebraMap A C a ∈ P := by
      rw [← Ideal.mem_comap, hP, mem_maximalIdeal, mem_nonunits_iff]
      exact h
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff D P (algebraMap A C a)).mpr hmem
    rw [← IsScalarTower.algebraMap_apply] at this
    exact (mem_maximalIdeal _).mp this ha
  have hDE : Function.Injective (algebraMap D (D ⊗[A] A')) :=
    Algebra.TensorProduct.includeLeft_injective (S := A) (injective_algebraMap_normalizationRing A)
  have : Nontrivial (D ⊗[A] A') := hDE.nontrivial
  have := isLocalRing_tensor_normalizationRing hA D
  -- `E = A' ⊗_A D` is a local ring of the étale `A'`-algebra `C' = A' ⊗_A C`
  let E := A' ⊗[A] D
  let e : D ⊗[A] A' ≃ₐ[A] E := Algebra.TensorProduct.comm A D A'
  have : Nontrivial E := e.injective.nontrivial
  have : IsLocalRing E := .of_surjective' e.toRingHom e.surjective
  let C' := A' ⊗[A] C
  let g : C' →ₐ[A'] E := Algebra.TensorProduct.map (AlgHom.id A' A')
    (IsScalarTower.toAlgHom A C D)
  let : Algebra C' E := g.toRingHom.toAlgebra
  have : IsScalarTower A' C' E := IsScalarTower.of_algebraMap_eq fun a ↦ (g.commutes a).symm
  let M' := P.primeCompl.map (Algebra.TensorProduct.includeRight (R := A) (A := A'))
  have : IsLocalization M' E :=
    IsLocalization.tensorProduct_tensorProduct_right A A' P.primeCompl D (by
      ext c
      exact Algebra.TensorProduct.map_tmul _ _ 1 c)
  have : IsLocalization.AtPrime E (maximalIdeal E) :=
    IsLocalization.of_le_isUnit fun x hx ↦ IsLocalRing.notMem_maximalIdeal.mp hx
  let Q := (maximalIdeal E).comap (algebraMap C' E)
  have : IsLocalization.AtPrime E Q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M' E (maximalIdeal E)
  have : IsIntegrallyClosed A' :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing A)
  have hp : IsDomain (Localization.AtPrime (Q.comap (algebraMap A' C'))) ∧
      IsIntegrallyClosed (Localization.AtPrime (Q.comap (algebraMap A' C'))) :=
    ⟨IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _),
      isIntegrallyClosed_of_isLocalization _ _
        (Ideal.primeCompl_le_nonZeroDivisors (Q.comap (algebraMap A' C')))⟩
  obtain ⟨_, -⟩ := isDomain_and_isIntegrallyClosed_localization_of_etale_of_localization
    (R := A') (S := C') Q hp
  have : IsDomain E :=
    (IsLocalization.algEquiv Q.primeCompl E (Localization.AtPrime Q)).injective.isDomain
      (IsLocalization.algEquiv Q.primeCompl E (Localization.AtPrime Q)).toRingHom
  have : IsDomain (D ⊗[A] A') := e.injective.isDomain e.toRingHom
  exact hDE.isDomain _


section Local

variable {B : Type u} [CommRing B] [Algebra A B]

/-- I.11, local form: let `A` be a geometrically unibranch local domain and `B` a local
`A`-algebra, essentially of finite type, unramified over `A`, with `A → B` injective and local.
Then `B` is étale over `A` (flat) and a domain. The proof is that of I.9.5(ii), with the
normality of `A` replaced by `isDomain_localization_of_etale_of_isGeometricallyUnibranch`. -/
theorem flat_and_isDomain_of_injective_of_isGeometricallyUnibranch
    (hA : IsGeometricallyUnibranch A) [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]
    (hinj : Function.Injective (algebraMap A B)) : Module.Flat A B ∧ IsDomain B := by
  obtain ⟨C, _, _, _, P, _, ψ, hsurj, hP⟩ := exists_etale_localization_surjective (A := A)
    (B := B)
  rw [maximalIdeal_comap] at hP
  have := isDomain_localization_of_etale_of_isGeometricallyUnibranch hA C P hP
  have : Module.Flat A (Localization.AtPrime P) := Module.Flat.trans A C _
  have hψ := injective_of_isField_tensor_fractionRing
    (isField_localization_tensor_fractionRing_of_isDomain P) ψ hinj
  let e := AlgEquiv.ofBijective ψ ⟨hψ, hsurj⟩
  exact ⟨Module.Flat.of_linearEquiv e.symm.toLinearEquiv,
    e.symm.injective.isDomain (e.symm : B →+* Localization.AtPrime P)⟩

end Local

end Normalization

open AlgebraicGeometry in
/-- I.11: let `f : X ⟶ Y` be unramified, of finite type (in particular quasi-compact, as for
I.9.11) and dominant, with `X` connected and `Y` locally noetherian with geometrically unibranch
local rings. Then `f` is étale and `X` is irreducible. SGA's proof "follows that of I.9.5" (with
IX.4.10 for the normalization); here I.9.5(ii) is replaced by its unibranch form
`flat_and_isDomain_of_injective_of_isGeometricallyUnibranch`, which needs no finiteness of the
normalization. -/
theorem etale_and_irreducibleSpace_of_formallyUnramified_of_isGeometricallyUnibranch
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    [QuasiCompact f] [FormallyUnramified f] [IsDominant f] [ConnectedSpace X]
    (hY : ∀ y : Y, ∃ _ : IsDomain (Y.presheaf.stalk y),
      IsGeometricallyUnibranch (Y.presheaf.stalk y)) :
    Etale f ∧ IrreducibleSpace X := by
  have key (x : X) (hinj : Function.Injective (f.stalkMap x)) :
      (f.stalkMap x).hom.Flat ∧ IsDomain (X.presheaf.stalk x) := by
    obtain ⟨_, hA⟩ := hY (f x)
    have h₂ := FormallyUnramified.stalkMap f x
    have h₃ := LocallyOfFiniteType.stalkMap f x
    algebraize [(f.stalkMap x).hom]
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    exact flat_and_isDomain_of_injective_of_isGeometricallyUnibranch hA hinj
  have : Etale f := etale_of_dominant_of_flat_of_injective f (fun y ↦ (hY y).1)
    fun x hinj ↦ (key x hinj).1
  refine ⟨this, ?_⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine irreducibleSpace_of_isDomain_stalk fun x ↦ (key x ?_).2
  -- a flat local homomorphism is faithfully flat, hence injective
  obtain ⟨_, _⟩ := hY (f x)
  have h₁ := Flat.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x))
    (B := X.presheaf.stalk x)
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

section Complete

open Polynomial IntermediateField

variable {A} [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]

omit [IsDomain A] in
/-- Over a complete noetherian local ring, a finite algebra which is a domain is local: a finite
algebra splits off the local factor at each maximal ideal (Stacks 04GG (10)). -/
theorem isLocalRing_of_finite_of_isDomain (T : Type*) [CommRing T] [IsDomain T] [Algebra A T]
    [Module.Finite A T] : IsLocalRing T := by
  obtain ⟨q, hq⟩ := Ideal.exists_maximal T
  obtain ⟨e, he, heq, hle⟩ := IsLocalRing.exists_isIdempotentElem_forall_le_of_finite (A := A) T q
  have he1 : e = 1 := by
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp he with h | h
    · exact absurd (h ▸ q.zero_mem) heq
    · exact h
  refine .of_unique_max_ideal ⟨q, hq, fun n hn ↦ hn.eq_of_le hq.ne_top (hle n hn.isPrime ?_)⟩
  rw [he1]
  exact fun h ↦ hn.ne_top ((Ideal.eq_top_iff_one _).mpr h)

omit [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsDomain A] in
lemma isMaximal_of_mem_primesOver_normalizationRing
    (Q : (maximalIdeal A).primesOver (normalizationRing A)) : Q.1.IsMaximal := by
  have := Q.2.1
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) Q.1 ?_
  have h := Q.2.2.over
  change maximalIdeal A = Q.1.comap (algebraMap A (normalizationRing A)) at h
  rw [← h]
  infer_instance

/-- I.11 b), first half: a complete noetherian local domain is unibranch. If the normalization
`A'` had two primes over `𝔪` separated by `x`, the finite domain `A[x] ⊆ A'` would not be
local. -/
theorem isUnibranch_of_isAdicComplete : IsUnibranch A := by
  refine ⟨fun Q₁ Q₂ ↦ Subtype.ext ?_⟩
  let A' := normalizationRing A
  have h₁ := isMaximal_of_mem_primesOver_normalizationRing Q₁
  have h₂ := isMaximal_of_mem_primesOver_normalizationRing Q₂
  by_contra hne
  obtain ⟨x, hx₁, hx₂⟩ : ∃ x ∈ Q₁.1, x ∉ Q₂.1 := by
    by_contra! h
    exact hne (h₁.eq_of_le h₂.ne_top h)
  let T := Algebra.adjoin A {x}
  have : Module.Finite A T :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral x)
  have := isLocalRing_of_finite_of_isDomain (A := A) T
  have key (Q : (maximalIdeal A).primesOver A') : Q.1.comap T.val = maximalIdeal T := by
    have := Q.2.1
    refine IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (R := A) _ ?_)
    have h : (Q.1.comap T.val).comap (algebraMap A T) = maximalIdeal A := by
      refine Eq.trans ?_ Q.2.2.over.symm
      ext a
      simp [Ideal.mem_comap, Ideal.under]
      rfl
    rw [h]
    infer_instance
  have hxT : (⟨x, Algebra.subset_adjoin rfl⟩ : T) ∈ Q₁.1.comap T.val := hx₁
  rw [key Q₁, ← key Q₂] at hxT
  exact hx₂ hxT


omit [IsDomain A] in
/-- The core of I.11 b). Let `x` be integral over the complete noetherian local domain `A`, in its
fraction field, and let `A[x] → L` be a map to a field over `k` sending `x` to an element `α`
separable over `k` and not in `k`. Then the finite étale `A`-algebra `B` with residue field
`k(α)` is local but not a domain: otherwise `B ⊗_A A[x] ⊆ B ⊗_A K` would be a finite domain over
`A`, hence local, while the two `k`-embeddings of `k(α)` sending `α` to `α` and to another root of
its minimal polynomial give two distinct maximal ideals of `B ⊗_A A[x]`. -/
theorem exists_finite_etale_not_isDomain_of_isSeparable {L : Type u} [Field L] [Algebra A L]
    [Algebra (ResidueField A) L] [IsScalarTower A (ResidueField A) L] {x : FractionRing A}
    (hx : IsIntegral A x) (φ : Algebra.adjoin A {x} →ₐ[A] L) {α : L}
    (hφ : φ ⟨x, Algebra.subset_adjoin rfl⟩ = α) (hαsep : IsSeparable (ResidueField A) α)
    (hαk : α ∉ (algebraMap (ResidueField A) L).range) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧
      Algebra.Etale A B ∧ IsLocalRing B ∧ ¬ IsDomain B := by
  classical
  let k := ResidueField A
  let K := FractionRing A
  have hint : IsIntegral k α := hαsep.isIntegral
  have hdeg : 2 ≤ (minpoly k α).natDegree := by
    have h1 := minpoly.natDegree_pos hint
    have h2 : (minpoly k α).natDegree ≠ 1 := fun h ↦ hαk (minpoly.natDegree_eq_one_iff.mp h)
    omega
  -- the finite étale `A`-algebra `B` with residue field `k(α)`
  have : FiniteDimensional k k⟮α⟯ := adjoin.finiteDimensional hint
  have : Algebra.IsSeparable k k⟮α⟯ := (isSeparable_adjoin_simple_iff_isSeparable k L).mpr hαsep
  obtain ⟨B, _, _, hBfin, hBet, ⟨e₁⟩⟩ := IsLocalRing.exists_finite_etale_lift_of_isSeparable A k⟮α⟯
  refine ⟨B, inferInstance, inferInstance, hBfin, hBet, ?_, fun hB ↦ ?_⟩
  · -- `B / 𝔪 B ≅ k(α)` is a field, so `B` is local
    let I := (maximalIdeal A).map (algebraMap A B)
    have hfield : IsField (B ⧸ I) := MulEquiv.isField (Field.toIsField _)
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)).toRingEquiv.trans
        e₁.toRingEquiv).toMulEquiv
    have hImax : I.IsMaximal := Ideal.Quotient.maximal_of_isField I hfield
    refine .of_unique_max_ideal ⟨I, hImax, fun n hn ↦ ?_⟩
    have : I ≤ n := by
      rw [Ideal.map_le_iff_le_comap]
      exact (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n)).ge
    exact (hImax.eq_of_le hn.ne_top this).symm
  -- `R = B ⊗_A A[x]` is a finite domain over `A`, hence local
  let T := Algebra.adjoin A {x}
  have : Module.Finite A T := Algebra.finite_adjoin_simple_of_isIntegral hx
  let R := B ⊗[A] T
  have hRK : Function.Injective (Algebra.TensorProduct.map (AlgHom.id A B) T.val) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := B) T.val.toLinearMap
      Subtype.val_injective
  have : IsDomain (B ⊗[A] K) := by
    refine IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid B
      (nonZeroDivisors A)) _ ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have := (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) ha)
    exact this.right_eq_zero_of_smul (by rwa [Algebra.smul_def, mul_comm])
  have : IsDomain R := hRK.isDomain _
  have := isLocalRing_of_finite_of_isDomain (A := A) R
  -- two `k`-embeddings of `k(α)` into an algebraic closure `Ω` of `L`
  let Ω := AlgebraicClosure L
  let f := minpoly k α
  have hαΩ : algebraMap L Ω α ∈ f.rootSet Ω := by
    rw [mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [aeval_algebraMap_apply, minpoly.aeval, map_zero]
  have hcard : Fintype.card (f.rootSet Ω) = f.natDegree :=
    card_rootSet_eq_natDegree hαsep (IsAlgClosed.splits _)
  obtain ⟨⟨γ, hγ⟩, hγα⟩ := Fintype.exists_ne_of_one_lt_card (α := f.rootSet Ω)
    (by rw [hcard]; exact hdeg) ⟨_, hαΩ⟩
  have hmem (z : Ω) (hz : z ∈ f.rootSet Ω) : z ∈ f.aroots Ω := by
    rw [mem_rootSet] at hz
    exact mem_aroots.mpr hz
  let σ₁ := (algHomAdjoinIntegralEquiv k (K := Ω) hint).symm ⟨_, hmem _ hαΩ⟩
  let σ₂ := (algHomAdjoinIntegralEquiv k (K := Ω) hint).symm ⟨γ, hmem _ hγ⟩
  -- the corresponding `A`-algebra maps `R → Ω`
  let β (σ : k⟮α⟯ →ₐ[k] Ω) : B →ₐ[A] Ω :=
    ((σ.restrictScalars A).comp (e₁.toAlgHom.restrictScalars A)).comp
      Algebra.TensorProduct.includeRight
  let τ : T →ₐ[A] Ω := (IsScalarTower.toAlgHom A L Ω).comp φ
  let χ (σ : k⟮α⟯ →ₐ[k] Ω) : R →ₐ[A] Ω :=
    Algebra.TensorProduct.lift (β σ) τ fun _ _ ↦ .all _ _
  have hker (σ : k⟮α⟯ →ₐ[k] Ω) : RingHom.ker (χ σ) = maximalIdeal R := by
    have : (RingHom.ker (χ σ)).IsPrime := RingHom.ker_isPrime _
    refine IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (R := A) _ ?_)
    have : (RingHom.ker (χ σ)).comap (algebraMap A R) = maximalIdeal A := by
      ext a
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
        IsScalarTower.algebraMap_apply A k Ω, map_eq_zero_iff _ (algebraMap k Ω).injective]
      exact residue_eq_zero_iff a
    rw [this]
    infer_instance
  -- `b₀ ⊗ 1 - 1 ⊗ x` lies in the first kernel but not in the second
  obtain ⟨b₀, hb₀⟩ := Algebra.TensorProduct.includeRight_surjective (R := A) (S := k) B
    residue_surjective (e₁.symm (AdjoinSimple.gen k α))
  let r : R := b₀ ⊗ₜ 1 - 1 ⊗ₜ ⟨x, Algebra.subset_adjoin rfl⟩
  have hχ (σ : k⟮α⟯ →ₐ[k] Ω) : χ σ r = σ (AdjoinSimple.gen k α) - algebraMap L Ω α := by
    simp only [r, map_sub, χ]
    rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one, map_one,
      mul_one, one_mul]
    congr 1
    · simp [β, hb₀]
    · simp [τ, hφ]
  have hr₁ : r ∈ RingHom.ker (χ σ₁) := by
    rw [RingHom.mem_ker, hχ, algHomAdjoinIntegralEquiv_symm_apply_gen, sub_self]
  have hr₂ : r ∉ RingHom.ker (χ σ₂) := by
    rw [RingHom.mem_ker, hχ, algHomAdjoinIntegralEquiv_symm_apply_gen, sub_eq_zero]
    exact fun h ↦ hγα (Subtype.ext h)
  rw [hker σ₁, ← hker σ₂] at hr₁
  exact hr₂ hr₁

/-- I.11 b): if a complete noetherian local domain `A` is not geometrically unibranch, some
finite étale local `A`-algebra is not a domain (a connected étale covering of `Spec A` which is
not irreducible). By `isUnibranch_of_isAdicComplete` the residue extension `κ(𝔪')/k` of the
normalization `A'` is not purely inseparable, so it contains some `α ∉ k` separable over `k`;
conclude by `exists_finite_etale_not_isDomain_of_isSeparable` with a lift `x ∈ A'` of `α`.
(SGA uses the finiteness of `A'` (Nagata) and the ring `A' ⊗_A B`; working with `A[x]` avoids
it.) -/
theorem exists_finite_etale_not_isDomain (hA : ¬ IsGeometricallyUnibranch A) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧
      Algebra.Etale A B ∧ IsLocalRing B ∧ ¬ IsDomain B := by
  classical
  let A' := normalizationRing A
  -- the residue extension at the prime of `A'` over `𝔪` is not purely inseparable
  obtain ⟨Q, hQ⟩ : ∃ Q : (maximalIdeal A).primesOver A', ¬ (Ideal.ResidueField.map
      (maximalIdeal A) Q.1 (algebraMap A A') Q.2.2.over).IsPurelyInseparable := by
    by_contra! h
    exact hA ⟨isUnibranch_of_isAdicComplete, h⟩
  have := Q.2.1
  have := isMaximal_of_mem_primesOver_normalizationRing Q
  let κ := Q.1.ResidueField
  have hsurj : Function.Surjective (algebraMap A' κ) := Q.1.algebraMap_residueField_surjective
  have : Algebra.IsIntegral A κ := ⟨fun y ↦ by
    obtain ⟨z, rfl⟩ := hsurj y
    exact (Algebra.IsIntegral.isIntegral z).map (IsScalarTower.toAlgHom A A' κ)⟩
  let k := ResidueField A
  let : Algebra k κ := IsLocalRing.ResidueField.algebraOfIsIntegral (R := A) (k := κ)
  have : IsScalarTower A k κ := IsLocalRing.ResidueField.isScalarTowerOfIsIntegral
  have : Algebra.IsIntegral k κ := Algebra.IsIntegral.tower_top A
  have hnot : ¬ IsPurelyInseparable k κ := by
    intro h
    let k₀ := (maximalIdeal A).ResidueField
    algebraize [Ideal.ResidueField.map (maximalIdeal A) Q.1 (algebraMap A A') Q.2.2.over]
    have : IsScalarTower k k₀ κ := .of_algebraMap_eq fun a ↦ by
      obtain ⟨a, rfl⟩ := residue_surjective a
      change algebraMap A κ a = Ideal.ResidueField.map (maximalIdeal A) Q.1 (algebraMap A A')
        Q.2.2.over (algebraMap A k₀ a)
      rw [Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply]
    exact hQ (h.tower_top (E := k₀))
  obtain ⟨α, hαsep, hαk⟩ : ∃ α : κ, IsSeparable k α ∧ α ∉ (algebraMap k κ).range := by
    by_contra! h
    exact hnot ⟨inferInstance, h⟩
  obtain ⟨x', rfl⟩ := hsurj α
  have hle : Algebra.adjoin A {(x' : FractionRing A)} ≤ integralClosure A (FractionRing A) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr x'.2)
  exact exists_finite_etale_not_isDomain_of_isSeparable x'.2
    ((IsScalarTower.toAlgHom A A' κ).comp (Subalgebra.inclusion hle)) rfl hαsep hαk

end Complete

end SGA.SGA1.ExposeI
