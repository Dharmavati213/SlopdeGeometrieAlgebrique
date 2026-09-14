/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVII.HomSupportAnnihilator
import SGA.SGA2.ExposeIV.SupportedFunctorRepresentation
import SGA.SGA2.ExposeIV.SupportedExtDiagram
import SGA.SGA2.ExposeIV.SupportedFunctorExactness
import SGA.SGA2.ExposeVI.AffineHomColimit
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# SGA 2, VII.1.1: supported Ext as Hom into local cohomology

Sheaf-level VII.1.1 on an affine noetherian chart: Extⁿ on finite modules
supported in `V(J)` is left exact under Extⁿ⁻¹ vanishing, represented by Hom
into the quotient-Ext colimit (= local cohomology) via IV.1.3, with the
affine Hom-colimit / power-torsion comparison.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV SGA.SGA2.ExposeVI

namespace SGA.SGA2.ExposeVII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- VII.1.1 source functor. -/
def supportedExtFunctor (J : Ideal R) (N : ModuleCat.{u} R) (n : ℕ) :
    (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (supportedFiniteToModule J).op ⋙
    (Abelian.extFunctor (C := ModuleCat.{u} R) n).flip.obj N

instance (J : Ideal R) (N : ModuleCat.{u} R) (n : ℕ) :
    (supportedExtFunctor J N n).Additive where
  map_add {X Y f g} := by
    ext x
    change (Abelian.Ext.mk₀ (f.unop.hom.hom + g.unop.hom.hom)).comp x (zero_add n) = _
    rw [Abelian.Ext.mk₀_add, Abelian.Ext.add_comp]
    rfl

def ExtVanishesOnSupported (J : Ideal R) (N : ModuleCat.{u} R) (n : ℕ) : Prop :=
  ∀ (M : SupportedFGModuleCat J) (i : ℕ), i < n →
    Subsingleton (Abelian.Ext M.obj.obj N i)

theorem supportedExt_leftExact_of_vanishing (J : Ideal R) (N : ModuleCat.{u} R)
    (n : ℕ) (hvan : ExtVanishesOnSupported J N n)
    (S : ShortComplex (SupportedFGModuleCat J)) (hS : S.ShortExact) :
    (S.op.map (supportedExtFunctor J N n)).Exact ∧
      Mono ((S.op.map (supportedExtFunctor J N n)).f) := by
  let S₀ := S.map (supportedFiniteToModule J)
  have hS₀ : S₀.ShortExact := hS.map_of_exact (supportedFiniteToModule J)
  refine ⟨?_, ?_⟩
  · exact Abelian.Ext.contravariant_sequence_exact₂' hS₀ N n
  · apply (AddCommGrpCat.mono_iff_injective _).mpr
    cases n with
    | zero =>
      have : Epi S₀.g := hS₀.epi_g
      exact Abelian.Ext.precomp_mk₀_injective_of_epi N S₀.g
    | succ k =>
      apply (injective_iff_map_eq_zero
        ((Abelian.Ext.mk₀ S₀.g).precomp N (zero_add (k + 1)))).mpr
      intro x hx
      have : Subsingleton (Abelian.Ext S₀.X₁ N k) := hvan S.X₁ k (by omega)
      obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS₀ N x hx
        (show 1 + k = k + 1 by omega)
      rw [Subsingleton.elim y 0, Abelian.Ext.comp_zero] at hy
      exact hy.symm

theorem supportedExtFunctor_exact_middle_of_vanishing (J : Ideal R)
    (N : ModuleCat.{u} R) (n : ℕ) (hvan : ExtVanishesOnSupported J N n)
    (S : ShortComplex (SupportedFGModuleCat J)) (hS : S.ShortExact) :
    (S.op.map (supportedExtFunctor J N n)).Exact :=
  (supportedExt_leftExact_of_vanishing J N n hvan S hS).1

def supportedExtRepresentationIso (J : Ideal R) (N : ModuleCat.{u} R) (n : ℕ)
    [PreservesFiniteLimits (supportedExtFunctor J N n)] :
    supportedExtFunctor J N n ≅
      supportedModuleHomFunctor J (supportedFunctorColimit J (supportedExtFunctor J N n)) ⋙
        forget₂ (ModuleCat R) AddCommGrpCat :=
  additiveSupportedFunctorRepresentationIso J (supportedExtFunctor J N n)

def moduleExtPowerColimit_eq_localCohomology (J : Ideal R) (N : ModuleCat.{u} R)
    (n : ℕ) :
    colimit (moduleExtPowerDiagram J N n) ≅ (_root_.localCohomology J n).obj N :=
  moduleExtPowerColimitIsoLocalCohomology J N n

/-- Affine end: Hom into a supported module is power-torsion (as a submodule
of the underlying linear-map module). -/
theorem exists_pow_annihilates_hom_of_support (J : Ideal R)
    (M H : ModuleCat.{u} R) [Module.Finite R H]
    (hSupp : Module.support R H ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    ∃ k : ℕ, J ^ k ≤ Module.annihilator R (M →ₗ[R] H) :=
  exists_pow_le_annihilator_linearMap_of_support_le J H M hSupp

/-- Consequently every Hom is killed by a power of `J`, so Hom lies in the
power-torsion submodule used by the VI.2.3 / VII.1.1 affine colimit. -/
theorem powerTorsion_hom_eq_top_of_support (J : Ideal R)
    (M H : ModuleCat.{u} R) [Module.Finite R H]
    (hSupp : Module.support R H ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    powerTorsion J (M →ₗ[R] H) = ⊤ := by
  obtain ⟨k, hk⟩ := exists_pow_annihilates_hom_of_support J M H hSupp
  refine top_unique fun f _ ↦
    (mem_powerTorsion_iff J (M →ₗ[R] H) f).mpr ⟨k, fun a ha ↦
      Module.mem_annihilator.mp (hk ha) f⟩

/-- Quotient-Hom colimit recovers the power-torsion of Hom (VI.2.3 / VII.1.1). -/
def adicQuotientHomColimitIsoPowerTorsionHom (J : Ideal R)
    (M H : ModuleCat.{u} R) :
    colimit (adicQuotientHomDiagram J M H) ≅
      ModuleCat.of R (powerTorsion J ((moduleHomDual H).obj (op M))) :=
  adicQuotientHomColimitIsoPowerTorsion J M H

/-- Under the support hypothesis the linear-map Hom is power-torsion, so the
affine colimit of VII.1.1 recovers all of `Hom_R(M,H)`. -/
theorem VII_1_1_affine_hom_colimit_recovers_hom (J : Ideal R)
    (M H : ModuleCat.{u} R) [Module.Finite R H]
    (hSupp : Module.support R H ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    powerTorsion J (M →ₗ[R] H) = ⊤ :=
  powerTorsion_hom_eq_top_of_support J M H hSupp

end SGA.SGA2.ExposeVII
