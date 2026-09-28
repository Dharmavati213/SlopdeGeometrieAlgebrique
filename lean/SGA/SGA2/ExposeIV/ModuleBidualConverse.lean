/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedArtinianDuality
import SGA.SGA2.ExposeIV.SupportedModuleTorsion

/-!
# Canonical supported Hom biduality forces injectivity

The actual cokernel of a dual restriction map remains finite and supported.
Its dual is zero by canonical bidual naturality, and its own canonical
reflexivity forces it to vanish. Thus the original Hom restriction maps are
surjective, giving injectivity by the genuine supported-module criterion.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Finiteness of the actual Hom values on the original finite supported modules. -/
def FiniteSupportedHomValues (J : Ideal R) (H : ModuleCat.{u} R) : Prop :=
  ∀ M : ModuleCat.{u} R, Module.Finite R M → supportedModuleProperty J M →
    Module.Finite R ((moduleHomDual H).obj (op M))

/-- The actual canonical bidual maps are isomorphisms on finite supported modules. -/
def SupportedModuleBiduality (J : Ideal R) (H : ModuleCat.{u} R) : Prop :=
  ∀ M : ModuleCat.{u} R, Module.Finite R M → supportedModuleProperty J M →
    IsIso (moduleBidualEvaluation H M)

/-- An annihilator of a module annihilates its original Hom dual. -/
theorem moduleHomDual_annihilator_le (H M : ModuleCat.{u} R) :
    Module.annihilator R M ≤ Module.annihilator R ((moduleHomDual H).obj (op M)) := by
  intro r hr
  apply Module.mem_annihilator.mpr
  intro f
  apply ModuleCat.hom_ext
  ext x
  change r • ModuleCat.Hom.hom f x = 0
  rw [← (ModuleCat.Hom.hom f).map_smul, Module.mem_annihilator.mp hr x, map_zero]

/-- Finite Hom values have no support outside the original finite source. -/
theorem moduleHomDual_support_subset (H M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R ((moduleHomDual H).obj (op M))] :
    Module.support R ((moduleHomDual H).obj (op M)) ⊆ Module.support R M := by
  rw [Module.support_eq_zeroLocus, Module.support_eq_zeroLocus]
  exact PrimeSpectrum.zeroLocus_anti_mono (moduleHomDual_annihilator_le H M)

/-- Precomposition with an epimorphism is monic for the actual linear Hom functor. -/
theorem moduleHomDual_map_mono (H : ModuleCat.{u} R) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) [Epi f] : Mono ((moduleHomDual H).map f.op) := by
  apply (ModuleCat.mono_iff_injective _).mpr
  intro a b h
  exact (cancel_epi f).mp h

/-- Canonical reflexivity transfers monicity to the actual bidual map. -/
theorem moduleHomBidual_map_mono (H : ModuleCat.{u} R) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) [Mono f] [IsIso (moduleBidualEvaluation H M)]
    [IsIso (moduleBidualEvaluation H N)] : Mono ((moduleHomBidual H).map f) := by
  have h : (moduleHomBidual H).map f =
      inv (moduleBidualEvaluation H M) ≫ f ≫ moduleBidualEvaluation H N := by
    apply (cancel_epi (moduleBidualEvaluation H M)).mp
    simpa only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp] using
      (moduleBidualEvaluation_naturality H f).symm
  rw [h]
  infer_instance

/-- Vanishing of the dual implies vanishing of a canonically reflexive module. -/
theorem isZero_of_moduleHomDual_isZero (H M : ModuleCat.{u} R)
    [IsIso (moduleBidualEvaluation H M)] (h : IsZero ((moduleHomDual H).obj (op M))) :
    IsZero M :=
  ((moduleHomDual H).map_isZero h.op).of_iso (asIso (moduleBidualEvaluation H M))

/-- The actual dual map is epic if its bidual is monic and its actual
cokernel is canonically reflexive. -/
theorem moduleHomDual_map_epi_of_cokernel_bidually_reflexive
    (H : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N)
    [Mono ((moduleHomBidual H).map f)]
    [IsIso (moduleBidualEvaluation H (cokernel ((moduleHomDual H).map f.op)))] :
    Epi ((moduleHomDual H).map f.op) := by
  let d := (moduleHomDual H).map f.op
  let q := cokernel.π d
  have hmono := moduleHomDual_map_mono H q
  have hz : (moduleHomDual H).map q.op = 0 := by
    apply (cancel_mono ((moduleHomBidual H).map f)).mp
    change (moduleHomDual H).map q.op ≫ (moduleHomDual H).map d.op = _
    rw [← Functor.map_comp, ← op_comp, cokernel.condition, op_zero, Functor.map_zero, zero_comp]
  have hzero : IsZero ((moduleHomDual H).obj (op (cokernel d))) := by
    have : Subsingleton ((moduleHomDual H).obj (op (cokernel d))) := ⟨by
      intro a b
      apply ((ModuleCat.mono_iff_injective _).mp hmono)
      rw [hz]
      rfl⟩
    exact ModuleCat.isZero_of_subsingleton _
  have hQ := isZero_of_moduleHomDual_isZero H (cokernel d) hzero
  exact Preadditive.epi_of_cokernel_zero (hQ.eq_of_tgt q 0)

variable [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- Finite canonical supported biduality makes every actual dual restriction
along a monomorphism of finite supported modules surjective. -/
theorem moduleHomDual_map_epi_of_supported_bidually_reflexive
    (J : Ideal R) (H : ModuleCat.{u} R) (hfin : FiniteSupportedHomValues J H)
    (hbid : SupportedModuleBiduality J H) {M N : ModuleCat.{u} R}
    [Module.Finite R M] [Module.Finite R N]
    (hM : supportedModuleProperty J M) (hN : supportedModuleProperty J N)
    (f : M ⟶ N) [Mono f] : Epi ((moduleHomDual H).map f.op) := by
  have := hfin M inferInstance hM
  have := hbid M inferInstance hM
  have := hbid N inferInstance hN
  have := moduleHomBidual_map_mono H f
  let d := (moduleHomDual H).map f.op
  have hQfin : Module.Finite R (cokernel d : ModuleCat R) :=
    Module.Finite.of_surjective (cokernel.π d).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have hQsupp : supportedModuleProperty J (cokernel d) :=
    (supportedModuleProperty J).prop_of_epi (cokernel.π d)
      ((moduleHomDual_support_subset H M).trans hM)
  have := hbid (cokernel d) hQfin hQsupp
  exact moduleHomDual_map_epi_of_cokernel_bidually_reflexive H f

/-- Canonical supported Hom biduality implies the actual Hom extension property. -/
theorem finiteSupportedHomExtension_of_bidually_reflexive
    (J : Ideal R) (H : ModuleCat.{u} R) (hfin : FiniteSupportedHomValues J H)
    (hbid : SupportedModuleBiduality J H) : FiniteSupportedHomExtension J H := by
  intro M hM hSupp N f
  have := hM
  let i : ModuleCat.of R N ⟶ M := ModuleCat.ofHom N.subtype
  have : Mono i := (ModuleCat.mono_iff_injective i).mpr N.injective_subtype
  have hsN : supportedModuleProperty J (ModuleCat.of R N) :=
    (Module.support_subset_of_injective N.subtype N.injective_subtype).trans hSupp
  have hE := moduleHomDual_map_epi_of_supported_bidually_reflexive J H hfin hbid hsN hSupp i
  obtain ⟨g, hg⟩ := ((ModuleCat.epi_iff_surjective _).mp hE) (ModuleCat.ofHom f)
  exact ⟨g.hom, congrArg ModuleCat.Hom.hom hg⟩

/-- **IV.3.1(i) implies injectivity in its actual Hom model.** The target
module is arbitrary apart from its original support; no finiteness of `H`
or assumed exactness is imposed. This direction does not need `R/J` Artinian. -/
theorem injective_of_supported_bidually_reflexive
    (J : Ideal R) (H : ModuleCat.{u} R) (hH : supportedModuleProperty J H)
    (hfin : FiniteSupportedHomValues J H) (hbid : SupportedModuleBiduality J H) :
    Injective H :=
  injective_of_finiteSupportedHomExtension J H
    (powerTorsion_eq_top_of_support_subset_zeroLocus J H hH)
    (finiteSupportedHomExtension_of_bidually_reflexive J H hfin hbid)

end SGA.SGA2.ExposeIV
