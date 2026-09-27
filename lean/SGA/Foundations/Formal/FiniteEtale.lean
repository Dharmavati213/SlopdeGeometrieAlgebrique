/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.TensorProduct.Quotient
import SGA.Foundations.Formal.AdicRing
import SGA.Foundations.Formal.EtaleLift

/-!
# Finite étale algebras over adic rings

Let `A` be a noetherian ring, complete for the `I`-adic topology. Then `B ↦ (A ⧸ I) ⊗[A] B` is an
equivalence from finite étale `A`-algebras to finite étale `A ⧸ I`-algebras
(`CommAlgCat.FiniteEtale.isEquivalence_baseChange_quotient`). Geometrically: the étale coverings
of the formal spectrum `Spf A` and of its reduction `Spec (A ⧸ I)` correspond (EGA IV, §18.3,
SGA 1 I.8.4 in the affine case; the Stacks project proves it more generally for henselian pairs).

Full faithfulness holds for maps from a formally étale algebra to a finite algebra
(`Algebra.FormallyEtale.bijective_map_tensorQuotient`). For essential surjectivity, a finite
étale `A ⧸ I`-algebra `B₀` lifts to an étale `A`-algebra `C`
(`Algebra.Etale.exists_etale_tensorQuotient_equiv`), and the `I`-adic completion of `C` is a
finite étale `A`-algebra with reduction `B₀` (`Algebra.Etale.finite_etale_adicCompletion`).
-/

universe u

open TensorProduct

variable {A : Type u} [CommRing A] {S : Type u} [CommRing S] [Algebra A S]
  (hS : Function.Surjective (algebraMap A S))

namespace Algebra

/-- For `A → S` surjective with kernel `K`, `S ⊗[A] M ≅ M ⧸ K M`. -/
noncomputable def tensorLinearEquivQuotientOfSurjective (M : Type*) [AddCommGroup M]
    [Module A M] :
    S ⊗[A] M ≃ₗ[A] M ⧸ (RingHom.ker (algebraMap A S) • ⊤ : Submodule A M) :=
  (_root_.TensorProduct.congr (quotientKerAlgEquivOfSurjective hS).symm.toLinearEquiv
    (LinearEquiv.refl A M)).trans (TensorProduct.quotTensorEquivQuotSMul M _)

include hS in
/-- Maps out of a formally étale algebra over an adic noetherian ring (EGA IV, §18.3, SGA 1
I.6.2 and I.8.4): let `A` be noetherian, `A → S` surjective with kernel `K`, `A` `K`-adically
complete, `B` formally étale over `A` and `B'` finite over `A`. Then
`Hom_A(B, B') → Hom_S(S ⊗ B, S ⊗ B')` is bijective. -/
theorem FormallyEtale.bijective_map_tensor [IsNoetherianRing A]
    [IsAdicComplete (RingHom.ker (algebraMap A S)) A]
    {B B' : Type*} [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B'] [FormallyEtale A B]
    [Module.Finite A B'] :
    Function.Bijective fun f : B →ₐ[A] B' ↦ Algebra.TensorProduct.map (AlgHom.id S S) f := by
  set K := RingHom.ker (algebraMap A S)
  have : IsAdicComplete K B' := .of_finite K B'
  have hI : IsAdicComplete (K.map (algebraMap A B')) B' :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr this
  let e := (tensorEquivQuotientOfSurjective hS B').symm
  have he (b : B') : e (Ideal.Quotient.mk _ b) = 1 ⊗ₜ b := by
    rw [AlgEquiv.symm_apply_eq, tensorEquivQuotientOfSurjective_one_tmul]
  refine ⟨fun f g hfg ↦ ?_, fun φ ↦ ?_⟩
  · apply FormallyUnramified.ext_of_iInf (I := K.map (algebraMap A B'))
    · have := hI.toIsHausdorff.iInf_pow_smul
      simpa [smul_eq_mul, Ideal.mul_top] using this
    · intro b
      apply e.injective
      have := congr($hfg (1 ⊗ₜ b))
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at this
      rw [he, he]
      exact this
  · obtain ⟨f, hf⟩ := FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (R := A)
      (I := K.map (algebraMap A B'))
      ((e.symm.toAlgHom).comp ((φ.restrictScalars A).comp Algebra.TensorProduct.includeRight))
    refine ⟨f, Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_⟩
    ext b
    have := congr(e ($hf b))
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    rw [he] at this
    simpa using this

end Algebra

namespace AdicCompletion

variable (C : Type u) [CommRing C] [Algebra A C]

/-- The completion `Ĉ` of an `A`-algebra `C` along `K C`, for `A → S` surjective with kernel `K`,
has the same reduction: `S ⊗[A] Ĉ ≅ S ⊗[A] C`, provided `K C` is finitely generated. -/
noncomputable def tensorEquiv
    (hfg : ((RingHom.ker (algebraMap A S)).map (algebraMap A C)).FG) :
    S ⊗[A] AdicCompletion ((RingHom.ker (algebraMap A S)).map (algebraMap A C)) C ≃ₐ[S]
      S ⊗[A] C := by
  let J := (RingHom.ker (algebraMap A S)).map (algebraMap A C)
  let ψ := (Algebra.tensorEquivQuotientOfSurjective hS C).symm
  let φ : AdicCompletion J C →+* S ⊗[A] C := ψ.toRingEquiv.toRingHom.comp (evalOneₐ J).toRingHom
  refine Algebra.tensorEquivOfSurjective hS φ ?_ ?_ ?_
  · exact ψ.surjective.comp (evalOneₐ_surjective J)
  · have : RingHom.ker φ = RingHom.ker (evalOneₐ J).toRingHom :=
      RingHom.ker_comp_of_injective _ ψ.injective
    rw [this, ker_evalOneₐ_eq_map J hfg, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  · intro a
    simp only [φ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply A C (AdicCompletion J C), AlgHom.commutes]
    change ψ (algebraMap C (C ⧸ J) (algebraMap A C a)) = _
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes, IsScalarTower.algebraMap_apply A S]

/-- The completion `Ĉ` of a noetherian `A`-algebra `C` along `I C` is `I`-adically complete as an
`A`-module. -/
theorem isAdicComplete_restrictScalars (I : Ideal A) (C : Type u) [CommRing C] [Algebra A C]
    [IsNoetherianRing C] :
    IsAdicComplete I (AdicCompletion (I.map (algebraMap A C)) C) := by
  let J := I.map (algebraMap A C)
  have h₁ : IsAdicComplete J (AdicCompletion J C) :=
    AdicCompletion.isAdicComplete (I := J) (M := C) (IsNoetherian.noetherian J)
  have h₂ : IsAdicComplete (J.map (algebraMap C (AdicCompletion J C))) (AdicCompletion J C) :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr h₁
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h₂
  exact (IsAdicComplete.map_algebraMap_iff _ _).mp h₂

end AdicCompletion

namespace Algebra.Etale

variable [IsNoetherianRing A] [IsAdicComplete (RingHom.ker (algebraMap A S)) A]

include hS in
/-- Let `A` be noetherian, `A → S` surjective with kernel `K`, `A` `K`-adically complete, and `C`
an étale `A`-algebra whose reduction `S ⊗[A] C` is finite over `S`. Then the completion `Ĉ` of `C`
along `K C` is a finite étale `A`-algebra (with the same reduction,
`AdicCompletion.tensorEquiv`). -/
theorem finite_etale_adicCompletion (C : Type u) [CommRing C] [Algebra A C] [Algebra.Etale A C]
    [Module.Finite S (S ⊗[A] C)] :
    Module.Finite A (AdicCompletion ((RingHom.ker (algebraMap A S)).map (algebraMap A C)) C) ∧
      Algebra.Etale A
        (AdicCompletion ((RingHom.ker (algebraMap A S)).map (algebraMap A C)) C) := by
  set K := RingHom.ker (algebraMap A S)
  let J := K.map (algebraMap A C)
  let Ĉ := AdicCompletion J C
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  have hfg : J.FG := IsNoetherian.noetherian J
  let e := AdicCompletion.tensorEquiv hS C hfg
  have hcomp : IsAdicComplete K Ĉ := AdicCompletion.isAdicComplete_restrictScalars K C
  -- `Ĉ` is finite over `A`
  have : Module.Finite A S := .of_surjective (Algebra.linearMap A S) hS
  have : Module.Finite S (S ⊗[A] Ĉ) := .equiv e.symm.toLinearEquiv
  have : Module.Finite A (S ⊗[A] Ĉ) := .trans S _
  have : Module.Finite A (Ĉ ⧸ (K • ⊤ : Submodule A Ĉ)) :=
    .equiv (Algebra.tensorLinearEquivQuotientOfSurjective hS Ĉ)
  have hfin : Module.Finite A Ĉ := .of_isHausdorff_of_finite_quotient (I := K)
  refine ⟨hfin, ?_⟩
  -- `Ĉ` is flat and of finite presentation over `A`
  have : Module.Flat A Ĉ := .trans A C Ĉ
  have : Algebra.FinitePresentation A Ĉ := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  -- `Ĉ` is unramified over `A`: `Ω[Ĉ⁄A]` vanishes modulo `K`, hence vanishes by Nakayama
  have : Algebra.FormallyUnramified S (S ⊗[A] Ĉ) := .of_equiv e.symm
  have hΩ : Subsingleton (S ⊗[A] Ω[Ĉ⁄A]) := by
    let _ : Algebra Ĉ (S ⊗[A] Ĉ) := Algebra.TensorProduct.rightAlgebra
    exact (KaehlerDifferential.tensorKaehlerEquivBase A S Ĉ (S ⊗[A] Ĉ)).subsingleton
  have hΩ' : (K • ⊤ : Submodule A Ω[Ĉ⁄A]) = ⊤ := by
    have := (Algebra.tensorLinearEquivQuotientOfSurjective hS Ω[Ĉ⁄A]).symm.subsingleton
    exact Submodule.Quotient.subsingleton_iff.mp this
  have : IsAdicComplete (K.map (algebraMap A Ĉ)) Ĉ :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr hcomp
  have hjac : K.map (algebraMap A Ĉ) ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot _
  have : Subsingleton Ω[Ĉ⁄A] := by
    rw [← Submodule.subsingleton_iff Ĉ, ← subsingleton_iff_bot_eq_top, eq_comm]
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ ⊤ (Module.Finite.fg_top) ?_ hjac
    rw [← Submodule.restrictScalars_le A, Submodule.restrictScalars_map_smul_eq,
      Submodule.restrictScalars_top, hΩ']
  have : Algebra.FormallyUnramified A Ĉ := ⟨this⟩
  exact Algebra.Etale.of_formallyUnramified_of_flat

include hS in
/-- Finite étale algebras lift along a surjection `A → S` when `A` is noetherian and complete for
the kernel `K` (EGA IV, §18.3; SGA 1 I.8.4 for `Spf A`): every finite étale `S`-algebra `B₀` is
`S ⊗[A] B` for a finite étale `A`-algebra `B`. -/
theorem exists_finite_etale_tensor_equiv (B₀ : Type u) [CommRing B₀]
    [Algebra S B₀] [Module.Finite S B₀] [Algebra.Etale S B₀] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
      Nonempty (S ⊗[A] B ≃ₐ[S] B₀) := by
  obtain ⟨C, _, _, _, ⟨e⟩⟩ := exists_etale_tensor_equiv hS B₀
  have : Module.Finite S (S ⊗[A] C) := .equiv e.symm.toLinearEquiv
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  obtain ⟨h₁, h₂⟩ := finite_etale_adicCompletion hS C
  exact ⟨_, inferInstance, inferInstance, h₁, h₂,
    ⟨(AdicCompletion.tensorEquiv hS C (IsNoetherian.noetherian _)).trans e⟩⟩

end Algebra.Etale

namespace CommAlgCat.FiniteEtale

open CategoryTheory

include hS in
/-- Étale coverings of `Spf A` and of `Spec S` correspond (EGA IV, §18.3; SGA 1 I.8.4, affine
case): if `A` is noetherian and `A → S` is surjective with kernel `K` such that `A` is `K`-adically
complete, `B ↦ S ⊗[A] B` is an equivalence from finite étale `A`-algebras to finite étale
`S`-algebras. -/
theorem isEquivalence_baseChange_of_surjective [IsNoetherianRing A]
    [IsAdicComplete (RingHom.ker (algebraMap A S)) A] :
    (CommAlgCat.FiniteEtale.baseChange.{u} A S).IsEquivalence where
  faithful := ⟨fun {X Y} f g h ↦ by
    have h' : Algebra.TensorProduct.map (AlgHom.id S S) f.hom.hom =
        Algebra.TensorProduct.map (AlgHom.id S S) g.hom.hom :=
      congr($(h).hom.hom)
    have := (Algebra.FormallyEtale.bijective_map_tensor hS (B := X.obj) (B' := Y.obj)).1 h'
    ext : 2
    exact this⟩
  full := ⟨fun {X Y} φ ↦ by
    obtain ⟨f, hf⟩ :=
      (Algebra.FormallyEtale.bijective_map_tensor hS (B := X.obj) (B' := Y.obj)).2 φ.hom.hom
    refine ⟨⟨CommAlgCat.ofHom f⟩, ?_⟩
    ext : 2
    exact hf⟩
  essSurj := ⟨fun B₀ ↦ by
    obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := Algebra.Etale.exists_finite_etale_tensor_equiv hS B₀.obj
    exact ⟨CommAlgCat.FiniteEtale.of A B, ⟨CommAlgCat.FiniteEtale.isoMk e⟩⟩⟩

variable (I : Ideal A) [IsNoetherianRing A] [IsAdicComplete I A]

/-- Étale coverings of `Spf A` and of `Spec (A ⧸ I)` correspond (EGA IV, §18.3; SGA 1 I.8.4,
affine case): if `A` is noetherian and `I`-adically complete, `B ↦ (A ⧸ I) ⊗[A] B` is an
equivalence from finite étale `A`-algebras to finite étale `A ⧸ I`-algebras. -/
instance isEquivalence_baseChange_quotient :
    (CommAlgCat.FiniteEtale.baseChange.{u} A (A ⧸ I)).IsEquivalence :=
  have : IsAdicComplete (RingHom.ker (algebraMap A (A ⧸ I))) A := by
    rwa [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  isEquivalence_baseChange_of_surjective Ideal.Quotient.mk_surjective

end CommAlgCat.FiniteEtale

namespace Algebra

variable (I : Ideal A)

/-- `Hom_A(B, B') → Hom_{A ⧸ I}(B ⧸ I B, B' ⧸ I B')` is bijective for `B` formally étale and
`B'` finite over a noetherian `I`-adically complete ring `A` (EGA IV, §18.3; SGA 1 I.6.2, I.8.4). -/
theorem FormallyEtale.bijective_map_tensorQuotient [IsNoetherianRing A] [IsAdicComplete I A]
    {B B' : Type*} [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B'] [FormallyEtale A B]
    [Module.Finite A B'] :
    Function.Bijective fun f : B →ₐ[A] B' ↦
      Algebra.TensorProduct.map (AlgHom.id (A ⧸ I) (A ⧸ I)) f :=
  have : IsAdicComplete (RingHom.ker (algebraMap A (A ⧸ I))) A := by
    rwa [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  FormallyEtale.bijective_map_tensor Ideal.Quotient.mk_surjective

/-- Finite étale algebras lift along `A → A ⧸ I` when `A` is noetherian and `I`-adically
complete (EGA IV, §18.3; SGA 1 I.8.4 for `Spf A`). -/
theorem Etale.exists_finite_etale_tensorQuotient_equiv [IsNoetherianRing A] [IsAdicComplete I A]
    (B₀ : Type u) [CommRing B₀] [Algebra (A ⧸ I) B₀] [Module.Finite (A ⧸ I) B₀]
    [Algebra.Etale (A ⧸ I) B₀] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
      Nonempty ((A ⧸ I) ⊗[A] B ≃ₐ[A ⧸ I] B₀) :=
  have : IsAdicComplete (RingHom.ker (algebraMap A (A ⧸ I))) A := by
    rwa [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  Etale.exists_finite_etale_tensor_equiv Ideal.Quotient.mk_surjective B₀

end Algebra
