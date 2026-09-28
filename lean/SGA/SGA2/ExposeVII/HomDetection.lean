/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.SchemeInternalHom
import SGA.SGA2.ExposeIII.CoherentAffineCharts
import SGA.SGA2.ExposeIV.SupportedHomDetection
import Mathlib.Topology.Sheaves.Abelian

/-!
# SGA 2, VII.1.3: detection by the actual internal Hom sheaf

On a locally noetherian scheme, a coherent source whose support contains
the support of a quasi-coherent target detects whether that target is zero.
The Hom sheaf and the stalk support in this statement are the actual ones.
The target is not assumed coherent or finitely generated.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry
open SGA.SGA2.ExposeIII SGA.SGA2.ExposeVI

namespace SGA.SGA2.ExposeVII

set_option backward.isDefEq.respectTransparency false

/-- The literal stalk support of a scheme module. -/
def schemeModuleSupport {X : Scheme.{u}} (M : X.Modules) : Set X :=
  {x | Nontrivial (M.presheaf.stalk x)}

/-- Genuine module isomorphisms preserve literal stalk support. -/
theorem schemeModuleSupport_eq_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    schemeModuleSupport M = schemeModuleSupport N := by
  ext x
  simp only [schemeModuleSupport, Set.mem_ofPred_eq, ← not_subsingleton_iff_nontrivial]
  exact not_congr (schemeModuleStalkLinearEquiv e x).toEquiv.subsingleton_congr

/-- Restriction pulls literal support back along the actual open immersion. -/
theorem schemeModuleSupport_restrict {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M : X.Modules) :
    schemeModuleSupport (M.restrict f) = f ⁻¹' schemeModuleSupport M := by
  ext x
  simp only [schemeModuleSupport, Set.mem_ofPred_eq, Set.mem_preimage,
    ← not_subsingleton_iff_nontrivial]
  exact not_congr (schemeModuleRestrictStalkAddEquiv f M x).toEquiv.subsingleton_congr

/-- The associated sheaf's literal stalk support is the module's localization support. -/
theorem schemeModuleSupport_tilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    schemeModuleSupport (tilde M) = Module.support R M := by
  ext p
  simp only [schemeModuleSupport, Set.mem_ofPred_eq, Module.support,
    ← not_subsingleton_iff_nontrivial]
  exact not_congr (affineModuleStalkLinearEquiv M p).toEquiv.subsingleton_congr.symm

/-- Canonical affine coefficients have precisely the actual sheaf's support. -/
theorem affineModuleCoefficients_support {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    Module.support R (affineModuleCoefficients M) = schemeModuleSupport M :=
  (schemeModuleSupport_tilde _).symm.trans
    (schemeModuleSupport_eq_of_iso (affineQuasicoherentPresentationIso M))

/-- Literal stalks of a quasi-coherent affine module are the localized coefficients. -/
def affineCoefficientsStalkAddEquiv {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (p : PrimeSpectrum R) :
    LocalizedModule.AtPrime p.asIdeal (affineModuleCoefficients M) ≃+ M.presheaf.stalk p :=
  (affineModuleStalkLinearEquiv (affineModuleCoefficients M) p).toAddEquiv.trans
    (schemeModuleStalkLinearEquiv (affineQuasicoherentPresentationIso M) p).toAddEquiv

/-- Original affine coefficient Hom is actual Hom of the quasi-coherent sheaves. -/
def affineCoefficientsHomEquiv {R : CommRingCat.{u}}
    (P H : (Spec R).Modules) [P.IsQuasicoherent] [H.IsQuasicoherent] :
    (affineModuleCoefficients P ⟶ affineModuleCoefficients H) ≃ (P ⟶ H) :=
  tilde.fullyFaithfulFunctor.homEquiv.trans
    (Iso.homCongr (affineQuasicoherentPresentationIso P) (affineQuasicoherentPresentationIso H))

/-- The affine zero-detection argument allows an arbitrary quasi-coherent target. -/
theorem affineCoefficients_subsingleton_of_hom_support {R : CommRingCat.{u}}
    [IsNoetherianRing R] (P H : (Spec R).Modules)
    [P.IsQuasicoherent] [H.IsQuasicoherent] [Module.Finite R (affineModuleCoefficients P)]
    (hHom : Subsingleton (P ⟶ H))
    (hSupp : schemeModuleSupport H ⊆ schemeModuleSupport P) :
    Subsingleton (affineModuleCoefficients H) := by
  have hcoeff : Subsingleton (affineModuleCoefficients P ⟶ affineModuleCoefficients H) :=
    (affineCoefficientsHomEquiv P H).subsingleton_congr.mpr hHom
  apply (ExposeIV.subsingleton_linearMap_iff_of_support_subset
    (affineModuleCoefficients P) (affineModuleCoefficients H) ?_).mp
      (ModuleCat.homEquiv.subsingleton_congr.mp hcoeff)
  rwa [affineModuleCoefficients_support, affineModuleCoefficients_support]

/-- Vanishing of every actual stalk implies vanishing of the original module sheaf. -/
theorem schemeModule_isZero_of_stalk_subsingleton {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, Subsingleton (M.presheaf.stalk x)) : IsZero M := by
  have hM : IsZero ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) := by
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro x
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr (h x)
  apply (IsZero.iff_id_eq_zero M).mpr
  apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  exact hM.eq_of_src _ _

/-- **VII.1.3 on locally noetherian schemes:** actual internal Hom detects
an arbitrary quasi-coherent target supported on a coherent source. -/
theorem VII_1_3_locallyNoetherian {X : Scheme.{u}} [IsLocallyNoetherian X]
    (P H : X.Modules) [P.IsFinitePresentation] [H.IsQuasicoherent]
    (hHom : IsZero (moduleSheafHomAb (Opens.grothendieckTopology X) P H))
    (hSupp : schemeModuleSupport H ⊆ schemeModuleSupport P) : IsZero H := by
  apply schemeModule_isZero_of_stalk_subsingleton
  intro x
  obtain ⟨U, hU, hxU, _, hfinite⟩ :=
    exists_affine_mem_subset_finiteCoefficients P (V := ⊤) (x := x) (by simp)
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := hfinite
  have hlocal : schemeModuleSupport (H.restrict hU.fromSpec) ⊆
      schemeModuleSupport (P.restrict hU.fromSpec) := by
    rw [schemeModuleSupport_restrict, schemeModuleSupport_restrict]
    exact Set.preimage_mono hSupp
  have hcoeff := affineCoefficients_subsingleton_of_hom_support
    (P.restrict hU.fromSpec) (H.restrict hU.fromSpec)
    (subsingleton_affineChartHom_of_isZero_internalHom P H hHom U hU) hlocal
  let := hcoeff
  have hxrange : x ∈ Set.range hU.fromSpec := hU.range_fromSpec.symm ▸ hxU
  obtain ⟨p, rfl⟩ := hxrange
  apply (schemeModuleRestrictStalkAddEquiv hU.fromSpec H p).toEquiv.subsingleton_congr.mp
  exact (affineCoefficientsStalkAddEquiv (H.restrict hU.fromSpec) p).toEquiv.subsingleton_congr.mp
    inferInstance

end SGA.SGA2.ExposeVII
