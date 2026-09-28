/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.ModuleBidualConverse

/-!
# Residue-field converse tests for genuine Hom duality

Canonical biduality forces the dual of each residue field to be the same
residue field. Length preservation gives the same tests directly, without
assuming exactness. The maps and scalar actions are the original linear Hom.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- A nontrivial canonically reflexive module has a nontrivial actual dual. -/
theorem moduleHomDual_nontrivial_of_bidually_reflexive (H M : ModuleCat.{u} R)
    [Nontrivial M] [IsIso (moduleBidualEvaluation H M)] :
    Nontrivial ((moduleHomDual H).obj (op M)) := by
  apply not_subsingleton_iff_nontrivial.mp
  intro h
  have := h
  have hM := isZero_of_moduleHomDual_isZero H M (ModuleCat.isZero_of_subsingleton _)
  exact not_subsingleton M (ModuleCat.isZero_iff_subsingleton.mp hM)

/-- A simple module annihilated by a maximal ideal is isomorphic to that
same residue-field module, with the original scalar action. -/
theorem simpleModule_iso_residue_of_annihilator (m : Ideal R) (hm : m.IsMaximal)
    (S : ModuleCat.{u} R) [IsSimpleModule R S] (hAnn : m ≤ Module.annihilator R S) :
    Nonempty (S ≅ ModuleCat.of R (R ⧸ m)) := by
  have hSupp : supportedModuleProperty m S := by
    change Module.support R S ⊆ PrimeSpectrum.zeroLocus (m : Set R)
    rw [Module.support_eq_zeroLocus]
    exact PrimeSpectrum.zeroLocus_anti_mono hAnn
  obtain ⟨n, hn, hmn, e⟩ := supportedSimple_exists_residue m S hSupp
  have heq : m = n := hm.eq_of_le hn.ne_top hmn
  subst n
  exact e

/-- The original dual of a residue field is annihilated by its maximal ideal. -/
theorem moduleHomDual_residue_annihilator (H : ModuleCat.{u} R) (m : Ideal R) :
    m ≤ Module.annihilator R ((moduleHomDual H).obj (op (ModuleCat.of R (R ⧸ m)))) := by
  simpa only [Ideal.annihilator_quotient] using
    moduleHomDual_annihilator_le H (ModuleCat.of R (R ⧸ m))

/-- Canonical residue-field reflexivity and injectivity of the actual target
force its dual to be simple. A nonzero residue-field map into its dual is
monic, and dualizing gives a quotient of the simple original bidual. -/
theorem moduleHomDual_residue_simple_of_bidually_reflexive
    (H : ModuleCat.{u} R) [Injective H] (m : Ideal R) (hm : m.IsMaximal)
    [IsIso (moduleBidualEvaluation H (ModuleCat.of R (R ⧸ m)))] :
    IsSimpleModule R ((moduleHomDual H).obj (op (ModuleCat.of R (R ⧸ m)))) := by
  let K := ModuleCat.of R (R ⧸ m)
  have : IsSimpleModule R K := by
    change IsSimpleModule R (R ⧸ m)
    exact isSimpleModule_iff_quot_maximal.mpr ⟨m, hm, ⟨LinearEquiv.refl R _⟩⟩
  have : Nontrivial K := IsSimpleModule.nontrivial R K
  have : Nontrivial ((moduleHomDual H).obj (op K)) :=
    moduleHomDual_nontrivial_of_bidually_reflexive H K
  obtain ⟨x, hx⟩ := exists_ne (0 : (moduleHomDual H).obj (op K))
  let f : K ⟶ (moduleHomDual H).obj (op K) := ModuleCat.ofHom
    (m.liftQ (LinearMap.toSpanSingleton R ((moduleHomDual H).obj (op K)) x) (by
      intro r hr
      exact Module.mem_annihilator.mp (moduleHomDual_residue_annihilator H m hr) x))
  have hf₁ : f (Ideal.Quotient.mk m 1) = x := by
    change (1 : R) • x = x
    exact one_smul R x
  have hf : f.hom ≠ 0 := by
    intro h
    apply hx
    have h' := DFunLike.congr_fun h (Ideal.Quotient.mk m 1)
    exact hf₁.symm.trans h'
  have : Mono f := (ModuleCat.mono_iff_injective f).mpr (LinearMap.injective_of_ne_zero hf)
  have hsurj : Function.Surjective ((moduleHomDual H).map f.op) := by
    intro g
    exact ⟨Injective.factorThru g f, Injective.comp_factorThru g f⟩
  have hle := Module.length_le_of_surjective ((moduleHomDual H).map f.op).hom hsurj
  have hlength : Module.length R ((moduleHomBidual H).obj K) = 1 := by
    rw [← (asIso (moduleBidualEvaluation H K)).toLinearEquiv.length_eq]
    exact Module.length_eq_one R K
  change Module.length R ((moduleHomDual H).obj (op K)) ≤
    Module.length R ((moduleHomBidual H).obj K) at hle
  rw [hlength] at hle
  apply Module.length_eq_one_iff.mp
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr Module.length_pos.ne')

/-- The residue-field dual test follows from injectivity and the original
canonical bidual map at that field. -/
theorem moduleHomDual_residue_iso_of_bidually_reflexive
    (H : ModuleCat.{u} R) [Injective H] (m : Ideal R) (hm : m.IsMaximal)
    [IsIso (moduleBidualEvaluation H (ModuleCat.of R (R ⧸ m)))] :
    Nonempty ((moduleHomDual H).obj (op (ModuleCat.of R (R ⧸ m))) ≅
      ModuleCat.of R (R ⧸ m)) := by
  have := moduleHomDual_residue_simple_of_bidually_reflexive H m hm
  exact simpleModule_iso_residue_of_annihilator m hm _ (moduleHomDual_residue_annihilator H m)

/-- Length preservation of the actual supported Hom values, without an
exactness assumption. -/
def SupportedHomLengthPreserving (J : Ideal R) (H : ModuleCat.{u} R) : Prop :=
  ∀ M : ModuleCat.{u} R, Module.Finite R M → supportedModuleProperty J M →
    Module.length R ((moduleHomDual H).obj (op M)) = Module.length R M

/-- Length equality on residue fields already forces the original residue
tests; in particular no exactness or injectivity is assumed here. -/
theorem moduleHomDualResidueTests_of_length_preserving
    (J : Ideal R) (H : ModuleCat.{u} R) (hlen : SupportedHomLengthPreserving J H) :
    moduleHomDualResidueTests J H := by
  intro m hm hJ
  let K := ModuleCat.of R (R ⧸ m)
  have : IsSimpleModule R K :=
    isSimpleModule_iff_quot_maximal.mpr ⟨m, hm, ⟨LinearEquiv.refl R _⟩⟩
  have hK : supportedModuleProperty J K := by
    change Module.support R (R ⧸ m) ⊆ _
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    exact PrimeSpectrum.zeroLocus_anti_mono hJ
  have hlenK := hlen K inferInstance hK
  rw [Module.length_eq_one R K] at hlenK
  have : IsSimpleModule R ((moduleHomDual H).obj (op K)) := Module.length_eq_one_iff.mp hlenK
  exact simpleModule_iso_residue_of_annihilator m hm _ (moduleHomDual_residue_annihilator H m)

variable [IsNoetherianRing R]

/-- **IV.3.1(i) implies the residue-field tests**, for the actual Hom model. -/
theorem moduleHomDualResidueTests_of_supported_bidually_reflexive
    (J : Ideal R) (H : ModuleCat.{u} R) (hH : supportedModuleProperty J H)
    (hfin : FiniteSupportedHomValues J H) (hbid : SupportedModuleBiduality J H) :
    moduleHomDualResidueTests J H := by
  have := injective_of_supported_bidually_reflexive J H hH hfin hbid
  intro m hm hJ
  have hK : supportedModuleProperty J (ModuleCat.of R (R ⧸ m)) := by
    change Module.support R (R ⧸ m) ⊆ _
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    exact PrimeSpectrum.zeroLocus_anti_mono hJ
  have := hbid (ModuleCat.of R (R ⧸ m)) inferInstance hK
  exact moduleHomDual_residue_iso_of_bidually_reflexive H m hm

end SGA.SGA2.ExposeIV
