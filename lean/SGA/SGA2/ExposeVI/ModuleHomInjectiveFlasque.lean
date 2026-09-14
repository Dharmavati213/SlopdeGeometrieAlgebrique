/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleOpenSubpresheaf
import SGA.SGA2.ExposeV.RingedModuleInjectiveFlasque
import SGA.SGA2.ExposeI.FlasqueResolution
import SGA.SGA2.ExposeI.LocallyClosedCohomology

/-!
# SGA 2, VI.1.5: local linear Hom into an injective module sheaf is flasque

The open subpresheaf of the source embeds into the original source. Injectivity
of the target module presheaf therefore extends every local linear map globally.
An injective module sheaf has an injective underlying module presheaf, so the
actual additive sheaf of local linear maps is flasque. Consequently it is
acyclic for closed and locally closed supported sections.

This does not use injectivity of the additive sheaf underlying the module sheaf.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- Every local linear map into an injective module presheaf extends globally. -/
theorem exists_modulePresheafHom_of_injective
    {R : (Opens X)ᵒᵖ ⥤ RingCat.{u}} (F G : PresheafOfModules.{u} R) [Injective G]
    (U : Opens X) (φ : moduleLocalHom F G U) :
    ∃ a : F ⟶ G, ∀ (V : Over U) (x : F.obj (op V.left)),
      a.app (op V.left) x = φ.val.app (op V) x := by
  let b := moduleOpenSubpresheafHom φ
  let a := Injective.factorThru b (moduleOpenSubpresheaf F U).ι
  refine ⟨a, fun V x ↦ ?_⟩
  let s : (moduleOpenSubpresheaf F U).toPresheafOfModules.obj (op V.left) :=
    ⟨x, mem_moduleOpenSubpresheaf F U (leOfHom V.hom) x⟩
  have h := congrArg
    (fun c : (moduleOpenSubpresheaf F U).toPresheafOfModules ⟶ G ↦ c.app (op V.left) s)
    (Injective.comp_factorThru b (moduleOpenSubpresheaf F U).ι)
  change a.app (op V.left) x = (moduleOpenSubpresheafHom φ).app (op V.left) s at h
  rw [moduleOpenSubpresheafHom_app_apply φ _ (leOfHom V.hom)] at h
  exact h

/-- Restriction of local linear maps into an injective module presheaf is surjective. -/
theorem moduleLocalHomRestrict_surjective_of_injective
    {R : (Opens X)ᵒᵖ ⥤ RingCat.{u}} (F G : PresheafOfModules.{u} R) [Injective G]
    {U V : Opens X} (i : V ⟶ U) :
    Function.Surjective (moduleLocalHomRestrict F G i) := by
  intro φ
  obtain ⟨a, ha⟩ := exists_modulePresheafHom_of_injective F G V φ
  let ψ : moduleLocalHom F G U :=
    ⟨Functor.whiskerLeft (Over.forget U).op ((PresheafOfModules.toPresheaf R).map a),
      fun W r x ↦ (a.app (op W.left)).hom.map_smul r x⟩
  refine ⟨ψ, ?_⟩
  apply moduleLocalHom_ext
  intro W x
  exact ha W x

variable (R : Sheaf RingCat.{u} X)

/-- **VI.1.5:** the genuine sheaf of local module-linear maps into an injective is flasque. -/
theorem moduleSheafHomAb_isFlasque_of_injective
    (F G : SheafOfModules.{u} R) [Injective G] :
    TopCat.Sheaf.IsFlasque (moduleSheafHomAb (Opens.grothendieckTopology X) F G) := by
  let : Injective G.val := ExposeV.injective_modulePresheaf_of_injective R G
  exact ⟨fun i ↦ (AddCommGrpCat.epi_iff_surjective _).mpr
    (moduleLocalHomRestrict_surjective_of_injective F.val G.val i.unop)⟩

/-- The Hom sheaf of VI.1.5 is acyclic for closed supported sections on every open. -/
theorem moduleSheafHomAb_derivedGammaZ_isZero_of_injective
    (F G : SheafOfModules.{u} R) [Injective G] (Z : Closeds X) (U : Opens X) (n : ℕ) :
    IsZero ((ExposeI.derivedGammaZSections Z U (n + 1)).obj
      (moduleSheafHomAb (Opens.grothendieckTopology X) F G)) := by
  let := moduleSheafHomAb_isFlasque_of_injective R F G
  exact ExposeI.derivedGammaZSections_isZero_of_isFlasque Z U _ n

/-- The same actual Hom sheaf is acyclic for arbitrary locally closed supported sections. -/
theorem moduleSheafHomAb_derivedGammaLocallyClosed_isZero_of_injective
    (F G : SheafOfModules.{u} R) [Injective G] (W : ExposeI.LocallyClosedIn X) (n : ℕ) :
    IsZero ((ExposeI.derivedGammaLocallyClosed W (n + 1)).obj
      (moduleSheafHomAb (Opens.grothendieckTopology X) F G)) := by
  let := moduleSheafHomAb_isFlasque_of_injective R F G
  exact ExposeI.derivedGammaLocallyClosed_isZero_of_isFlasque W _ n

end SGA.SGA2.ExposeVI
