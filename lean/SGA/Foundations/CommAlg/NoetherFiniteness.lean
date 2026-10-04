/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Finiteness of integral closure over a perfect field (E. Noether)

Let `A` be a domain, finitely generated over a perfect field `k`, and `L` a finite extension of
its fraction field `K`. Then the integral closure of `A` in `L` is a finite `A`-module
(`Algebra.FiniteType.finite_integralClosure`). In particular the normalization of `A` (its
integral closure in `K`) is finite over `A`.

The proof: by Noether normalization `A` is finite over a polynomial ring `B = k[x₁, …, xₙ]`, which
is integrally closed, so it suffices to treat `B`
(`Algebra.FiniteType.finite_integralClosure_of_isIntegrallyClosed`). Let `Kₛ` be the separable
closure of `Frac B` in `L`. The integral closure `Cₛ` of `B` in `Kₛ` is finite over `B`
(`IsIntegralClosure.finite`, the separable case). `L / Kₛ` is purely inseparable of some
exponent `e`, so with `q = pᵉ` the Frobenius `y ↦ y^q` maps the integral closure `C` of `B` in `L`
injectively into `Cₛ`, semilinearly over the Frobenius of `B`. The Frobenius of a finitely
generated algebra over a perfect field is finite (`RingHom.finite_iterateFrobenius`), hence `Cₛ`
is finite over `B` through `b ↦ b^q`, and `C`, a `B`-submodule of it, is finite since `B` is
noetherian (`Module.Finite.of_injective_of_ringHomFinite`). In characteristic `0` the exponent is
`0` and this is the separable case.

For imperfect fields of infinite `p`-degree the statement still holds (Nagata: algebras of finite
type over a field are Japanese) but this proof does not give it.

## References

* [A. Grothendieck, *EGA* IV₂, 7.8.3 (vi)][EGA4]
* [D. Eisenbud, *Commutative algebra*, Corollary 13.13][Eisenbud1995]
-/

open Polynomial
open scoped nonZeroDivisors

/-- If `σ : R →+* R'` is finite, `R` is noetherian and `Φ : M →ₛₗ[σ] M'` is injective with `M'`
a finite `R'`-module, then `M` is a finite `R`-module. -/
theorem Module.Finite.of_injective_of_ringHomFinite {R R' M M' : Type*} [CommRing R] [CommRing R']
    [IsNoetherianRing R] {σ : R →+* R'} (hσ : σ.Finite) [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] [Module.Finite R' M'] (Φ : M →ₛₗ[σ] M')
    (hΦ : Function.Injective Φ) : Module.Finite R M := by
  let : Algebra R R' := σ.toAlgebra
  let : Module R M' := Module.compHom M' σ
  have : IsScalarTower R R' M' := ⟨fun r r' m ↦ by
    change (σ r • r') • m = σ r • r' • m
    rw [smul_assoc]⟩
  have : Module.Finite R R' := hσ
  have : Module.Finite R M' := Module.Finite.trans R' M'
  let Ψ : M →ₗ[R] M' :=
    { toFun := Φ
      map_add' := Φ.map_add
      map_smul' := fun r m ↦ Φ.map_smulₛₗ r m }
  exact Module.Finite.of_injective Ψ hΦ

section Frobenius

variable (k R : Type*) [Field k] [CommRing R] [Algebra k R] (p : ℕ) [ExpChar k p] [ExpChar R p]

/-- The iterated Frobenius `x ↦ x ^ p ^ n` of an algebra of finite type over a perfect field of
exponential characteristic `p` is a finite ring homomorphism: it is integral (`x` is a root of
`X ^ p ^ n - x ^ p ^ n`), and of finite type because its image contains `k`. -/
theorem RingHom.finite_iterateFrobenius [PerfectRing k p] [Algebra.FiniteType k R] (n : ℕ) :
    (iterateFrobenius R p n).Finite := by
  refine RingHom.IsIntegral.to_finite (fun x ↦ ⟨X ^ p ^ n - C x,
    monic_X_pow_sub_C _ (expChar_pow_pos R p n).ne', by simp [iterateFrobenius_def]⟩) ?_
  have h : (iterateFrobenius R p n).comp
      ((algebraMap k R).comp (iterateFrobeniusEquiv k p n).symm.toRingHom) = algebraMap k R := by
    ext c
    change (algebraMap k R ((iterateFrobeniusEquiv k p n).symm c)) ^ p ^ n = algebraMap k R c
    rw [← map_pow, ← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  refine RingHom.FiniteType.of_comp_finiteType (f := (algebraMap k R).comp
    (iterateFrobeniusEquiv k p n).symm.toRingHom) ?_
  rw [h]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

end Frobenius

section Main

/-- The integral closure of an integrally closed domain `B`, finitely generated over a perfect
field `k`, in a finite extension `L` of its fraction field is a finite `B`-module (the separable
closure of `Frac B` in `L` and the Frobenius, see the module docstring). -/
theorem Algebra.FiniteType.finite_integralClosure_of_isIntegrallyClosed (k B K L : Type*)
    [Field k] [PerfectField k] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [IsIntegrallyClosed B]
    [Field K] [Algebra B K] [IsFractionRing B K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra B L] [IsScalarTower B K L] : Module.Finite B (integralClosure B L) := by
  obtain ⟨p, _⟩ := ExpChar.exists k
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : ExpChar B p := expChar_of_injective_algebraMap (algebraMap k B).injective p
  have hBL : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective B K)
  have : ExpChar L p := expChar_of_injective_ringHom hBL p
  let Ks := separableClosure K L
  have : ExpChar K p := expChar_of_injective_algebraMap (IsFractionRing.injective B K) p
  have : ExpChar Ks p := expChar_of_injective_algebraMap (algebraMap K Ks).injective p
  have : IsScalarTower B Ks L := IsScalarTower.of_algebraMap_eq fun b ↦ rfl
  have hfin : Module.Finite B (integralClosure B Ks) :=
    IsIntegralClosure.finite B K Ks (integralClosure B Ks)
  have : FiniteDimensional Ks L := Module.Finite.of_restrictScalars_finite K Ks L
  let e := IsPurelyInseparable.exponent Ks L
  let F : L →+* Ks := IsPurelyInseparable.iterateFrobenius Ks L p le_rfl
  have hF (y : L) : algebraMap Ks L (F y) = y ^ p ^ e :=
    IsPurelyInseparable.algebraMap_iterateFrobenius Ks p le_rfl y
  have hint (y : integralClosure B L) : IsIntegral B (F y) := by
    have : IsIntegral B (algebraMap Ks L (F y)) := by
      rw [hF]; exact y.2.pow _
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom B Ks L)
      (algebraMap Ks L).injective).mp this
  let Φ : integralClosure B L →ₛₗ[iterateFrobenius B p e] integralClosure B Ks :=
    { toFun := fun y ↦ ⟨F y, hint y⟩
      map_add' := fun y z ↦ Subtype.ext (by simp)
      map_smul' := fun b y ↦ Subtype.ext <| (algebraMap Ks L).injective <| by
        change algebraMap Ks L (F ((b • y : integralClosure B L) : L)) =
          algebraMap Ks L ((iterateFrobenius B p e b • (⟨F y, hint y⟩ : integralClosure B Ks) :
            integralClosure B Ks) : Ks)
        rw [hF, Subalgebra.coe_smul, Subalgebra.coe_smul, Algebra.smul_def, Algebra.smul_def,
          map_mul, hF, mul_pow, ← IsScalarTower.algebraMap_apply, iterateFrobenius_def,
          map_pow] }
  exact Module.Finite.of_injective_of_ringHomFinite (RingHom.finite_iterateFrobenius k B p e) Φ
    fun y z h ↦ Subtype.ext (F.injective (congrArg (fun w : integralClosure B Ks ↦ (w : Ks)) h))

end Main

/-- **E. Noether's finiteness theorem** (EGA IV 7.8.3, Eisenbud 13.13; here for perfect fields): the
integral closure of a domain `A`, finitely generated over a perfect field `k`, in a finite
extension `L` of its fraction field is a finite `A`-module. -/
theorem Algebra.FiniteType.finite_integralClosure (k A K L : Type*) [Field k] [PerfectField k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] : Module.Finite A (integralClosure A L) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let B := MvPolynomial (Fin s) k
  algebraize [g.toRingHom]
  have : Module.Finite B A := hfin
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hinj
  let : Algebra B K := ((algebraMap A K).comp g.toRingHom).toAlgebra
  have : IsScalarTower B A K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra B L := ((algebraMap A L).comp g.toRingHom).toAlgebra
  have : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower B K L := IsScalarTower.of_algebraMap_eq fun b ↦ by
    change algebraMap A L (g b) = algebraMap K L (algebraMap A K (g b))
    exact IsScalarTower.algebraMap_apply A K L _
  have hBK : Function.Injective (algebraMap B K) :=
    (IsFractionRing.injective A K).comp hinj
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).mpr hBK
  let KB := FractionRing B
  let : Algebra KB K := FractionRing.liftAlgebra B K
  have : IsScalarTower B KB K := FractionRing.isScalarTower_liftAlgebra B K
  let : Algebra KB L := ((algebraMap K L).comp (algebraMap KB K)).toAlgebra
  have : IsScalarTower KB K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower B KB L := IsScalarTower.of_algebraMap_eq fun b ↦ by
    change algebraMap B L b = algebraMap K L (algebraMap KB K (algebraMap B KB b))
    rw [← IsScalarTower.algebraMap_apply B KB K, ← IsScalarTower.algebraMap_apply B K L]
  have : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have : FiniteDimensional KB K := Module.Finite.of_isLocalization B A B⁰
  have : FiniteDimensional KB L := Module.Finite.trans K L
  have hB := Algebra.FiniteType.finite_integralClosure_of_isIntegrallyClosed k B KB L
  have : IsNoetherianRing B := inferInstance
  let ι : integralClosure A L →ₗ[B] integralClosure B L :=
    { toFun := fun x ↦ ⟨x, isIntegral_trans (R := B) (A := A) _ x.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have : Module.Finite B (integralClosure A L) :=
    Module.Finite.of_injective ι fun x y h ↦
      Subtype.ext (congrArg (fun z : integralClosure B L ↦ (z : L)) h)
  exact Module.Finite.of_restrictScalars_finite B A _

/-- E. Noether's finiteness theorem for an abstract integral closure: if `C` is an integral
closure of `A` (a domain of finite type over a perfect field) in a finite extension `L` of its
fraction field, then `C` is a finite `A`-module. -/
theorem IsIntegralClosure.finite_of_finiteType (k A K L C : Type*) [Field k] [PerfectField k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] [CommRing C] [Algebra C L] [Algebra A C] [IsScalarTower A C L]
    [IsIntegralClosure C A L] : Module.Finite A C :=
  have := Algebra.FiniteType.finite_integralClosure k A K L
  Module.Finite.equiv (IsIntegralClosure.equiv A (integralClosure A L) L C).toLinearEquiv
