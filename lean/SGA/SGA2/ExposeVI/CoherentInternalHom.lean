/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.AffineInternalHom
import SGA.SGA2.ExposeVI.SchemeInternalHomRestriction
import SGA.SGA2.ExposeIII.CoherentAffineCharts
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Quasi-coherence of actual internal Hom with coherent source

On a locally noetherian scheme, the genuine internal Hom module sheaf of a
finitely presented source and a quasi-coherent target is quasi-coherent.
The proof chooses actual finite affine coefficient charts, applies finite-
presentation Hom localization there, and descends across the open cover.
This is the ordinary degree-zero internal-Hom prerequisite for VI.2.1;
it does not assert quasi-coherence of positive supported sheaf Ext.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Transport back from the actual open subscheme preserves quasi-coherence. -/
theorem schemeModuleOverEquivInverse_isQuasicoherent {X : Scheme.{u}} (U : X.Opens)
    (M : U.toScheme.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.overEquiv U).inverse.obj M).IsQuasicoherent := by
  let := U.instIsDenseSubsiteOverSubtypeMemOverGrothendieckTopologyFunctorOverEquivalence
  let : U.overEquivalence.functor.IsContinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) :=
    inferInstanceAs (U.overEquivalence.functor.IsContinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U.carrier))
  let (V : Over U) :
      (Over.post (X := V) U.overEquivalence.functor).IsContinuous
        (((Opens.grothendieckTopology X).over U).over V)
        ((Opens.grothendieckTopology ↥U).over (U.overEquivalence.functor.obj V)) :=
    Functor.isContinuous_iff_coverPreserving.mpr
      ((CoverPreserving.of_isContinuous U.overEquivalence.functor
        ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U)).overPost V)
  exact SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    U.overEquivalence.functor (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)

/-- Quasi-coherence can be checked on the actual restricted modules of an open cover. -/
theorem schemeModule_isQuasicoherent_of_restrict_cover {X : Scheme.{u}}
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hM : ∀ i, (M.restrict (U i).ι).IsQuasicoherent) : M.IsQuasicoherent := by
  let (i : ι) : (M.over (U i)).IsQuasicoherent := by
    let := hM i
    let e := (Scheme.Modules.overEquiv (U i)).inverse.mapIso
      ((Scheme.Modules.overFunctorEquiv (U i)).app M).symm ≪≫
        ((Scheme.Modules.overEquiv (U i)).unitIso.app (M.over (U i))).symm
    exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over (U i))).prop_of_iso e
      (schemeModuleOverEquivInverse_isQuasicoherent (U i) (M.restrict (U i).ι))
  apply SheafOfModules.IsQuasicoherent.of_coversTop M U
  rw [Opens.coversTop_iff]
  exact hU

/-- **VI.2.1, ordinary degree zero:** actual internal Hom from a coherent source
to a quasi-coherent target is quasi-coherent on a locally noetherian scheme. -/
theorem coherent_internalHom_isQuasicoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F G : X.Modules) [F.IsFinitePresentation] [G.IsQuasicoherent] :
    (schemeModuleInternalHom F G).IsQuasicoherent := by
  obtain ⟨ι, U, P, hcov, hP⟩ := ExposeIII.exists_affineOpenCover_finitePresentation F
  apply schemeModule_isQuasicoherent_of_restrict_cover (schemeModuleInternalHom F G) U hcov
  intro i
  let hU := (hP i).1
  have := (hP i).2
  have : IsNoetherianRing Γ(X, U i) := IsLocallyNoetherian.component_noetherian ⟨U i, hU⟩
  have : Module.Finite Γ(X, U i)
      ((moduleSpecΓFunctor (R := Γ(X, U i))).obj (F.restrict hU.fromSpec)) :=
    ExposeIII.affineChart_coefficients_finite F (U i) hU (P i)
  have : Module.FinitePresentation Γ(X, U i)
      ((moduleSpecΓFunctor (R := Γ(X, U i))).obj (F.restrict hU.fromSpec)) :=
    Module.finitePresentation_of_finite _ _
  have hHom := affineInternalHom_isQuasicoherent_of_coefficients
    (F.restrict hU.fromSpec) (G.restrict hU.fromSpec)
  have : ((schemeModuleInternalHom F G).restrict hU.fromSpec).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, U i)).ringCatSheaf).prop_of_iso
      (schemeModuleInternalHomRestrictIso hU.fromSpec F G).symm hHom
  let e : (schemeModuleInternalHom F G).restrict (U i).ι ≅
      ((schemeModuleInternalHom F G).restrict hU.fromSpec).restrict hU.isoSpec.hom :=
    (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec.symm).app _ ≪≫
      (Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app _
  exact (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).prop_of_iso e.symm
    (by infer_instance)

end SGA.SGA2.ExposeVI
