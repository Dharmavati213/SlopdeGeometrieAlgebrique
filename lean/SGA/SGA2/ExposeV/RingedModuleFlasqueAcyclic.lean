/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RingedModulePushforward
import SGA.SGA2.ExposeI.FlasqueResolution

/-!
# SGA 2, V.3.2: module-valued supported acyclicity of flasque sheaves

The cycles in an injective resolution of a flasque module sheaf are flasque.
Supported sections therefore preserve the positive-degree exactness of that
resolution. This proves acyclicity for the actual right-derived module-valued
functor, and supplies the acyclicity input for general ringed-space pushforward.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex
open TopCat.Sheaf (IsFlasque)

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- Right-derived supported sections, computed by injective module resolutions. -/
def derivedModuleGammaZSections (Z : Closeds X) (U : Opens X) (n : ℕ) :
    SheafOfModules.{u} R ⥤ ModuleCat.{u} (R.obj.obj (op U)) :=
  (moduleGammaZSectionsFunctor R Z U).rightDerived n

/-- Degree zero of the derived functor is actual supported sections as modules. -/
def derivedModuleGammaZSectionsZeroIso (Z : Closeds X) (U : Opens X) :
    derivedModuleGammaZSections R Z U 0 ≅ moduleGammaZSectionsFunctor R Z U :=
  (moduleGammaZSectionsFunctor R Z U).rightDerivedZeroIsoSelf

/-- Degree-zero cycles of an injective module resolution recover its coefficient. -/
def moduleInjectiveResolutionCyclesZeroIso (M : SheafOfModules.{u} R)
    (I : InjectiveResolution M) : I.cocomplex.cycles 0 ≅ M :=
  (I.cocomplex.cyclesIsKernel 0 1 (by simp)).conePointUniqueUpToIso I.isLimitKernelFork

/-- All cycles in an injective resolution of a flasque module sheaf are flasque. -/
theorem moduleInjectiveResolution_cycles_isFlasque (M : SheafOfModules.{u} R)
    [IsFlasque ((SheafOfModules.toSheaf R).obj M)] (I : InjectiveResolution M) (n : ℕ) :
    IsFlasque ((SheafOfModules.toSheaf R).obj (I.cocomplex.cycles n)) := by
  induction n with
  | zero =>
    exact ExposeI.isFlasque_of_iso
      ((SheafOfModules.toSheaf R).mapIso (moduleInjectiveResolutionCyclesZeroIso R M I))
  | succ n ih =>
    have : IsFlasque
        ((ExposeI.cochainCyclesSequence I.cocomplex n).map (SheafOfModules.toSheaf R)).X₁ := ih
    have : IsFlasque
        ((ExposeI.cochainCyclesSequence I.cocomplex n).map (SheafOfModules.toSheaf R)).X₂ :=
      moduleIsFlasque_of_injective R (I.cocomplex.X n)
    exact Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
      (moduleToSheaf_map_shortExact R (ExposeI.cochainCyclesSequence_shortExact
        I.cocomplex n (I.cocomplex_exactAt_succ n)))

/-- Supported sections of a flasque module's injective resolution are exact in
every positive degree. -/
theorem moduleGammaZSections_injectiveResolution_exactAt (Z : Closeds X) (U : Opens X)
    (M : SheafOfModules.{u} R) [IsFlasque ((SheafOfModules.toSheaf R).obj M)]
    (I : InjectiveResolution M) (n : ℕ) :
    (((moduleGammaZSectionsFunctor R Z U).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).ExactAt (n + 1) := by
  let K := I.cocomplex
  let G := moduleGammaZSectionsFunctor R Z U
  have : IsFlasque ((SheafOfModules.toSheaf R).obj (ExposeI.cochainCyclesSequence K n).X₁) :=
    moduleInjectiveResolution_cycles_isFlasque R M I n
  have hseq := moduleGammaZSectionsFunctor_map_shortExact R
    (ExposeI.cochainCyclesSequence_shortExact K n (I.cocomplex_exactAt_succ n)) Z U
  have : Epi (G.map (K.toCycles n (n + 1))) := hseq.epi_g
  let A := ShortComplex.mk (G.map (K.d n (n + 1))) (G.map (K.d (n + 1) (n + 2)))
    (by rw [← G.map_comp, K.d_comp_d, G.map_zero])
  let B := ShortComplex.mk (K.iCycles (n + 1)) (K.d (n + 1) (n + 2))
    (K.iCycles_d (n + 1) (n + 2))
  have hB : B.Exact := B.exact_of_f_is_kernel
    (K.cyclesIsKernel (n + 1) (n + 2) (by simp))
  have : Mono B.f := inferInstanceAs (Mono (K.iCycles (n + 1)))
  have hGB := hB.map_of_mono_of_preservesKernel G inferInstance inferInstance
  let ψ : A ⟶ B.map G :=
    { τ₁ := G.map (K.toCycles n (n + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        change G.map (K.toCycles n (n + 1)) ≫ G.map (K.iCycles (n + 1)) =
          G.map (K.d n (n + 1)) ≫ 𝟙 _
        rw [Category.comp_id, ← G.map_comp, K.toCycles_i]
      comm₂₃ := by simp [A, B] }
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  change A.Exact
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr hGB

/-- Flasque module sheaves are acyclic for the actual module-valued supported
section functor on every open and for every closed support. -/
theorem derivedModuleGammaZSections_isZero_of_isFlasque (Z : Closeds X) (U : Opens X)
    (M : SheafOfModules.{u} R) [IsFlasque ((SheafOfModules.toSheaf R).obj M)] (n : ℕ) :
    IsZero ((derivedModuleGammaZSections R Z U (n + 1)).obj M) := by
  let I := InjectiveResolution.of M
  exact IsZero.of_iso
    (moduleGammaZSections_injectiveResolution_exactAt R Z U M I n).isZero_homology
    (I.isoRightDerivedObj (moduleGammaZSectionsFunctor R Z U) (n + 1))

/-- The direct image of an injective module sheaf is acyclic for supported
sections over the target's structure sheaf, without flatness of the map. -/
theorem derivedModuleGammaZSections_isZero_pushforward_injective
    {Y : TopCat.{u}} (f : X ⟶ Y) {S : Sheaf RingCat.{u} Y}
    (φ : S ⟶ (Sheaf.pushforward RingCat f).obj R)
    (Z : Closeds Y) (U : Opens Y) (M : SheafOfModules.{u} R) [Injective M] (n : ℕ) :
    IsZero ((derivedModuleGammaZSections S Z U (n + 1)).obj
      ((ringedModulePushforward f φ).obj M)) := by
  have := ringedModulePushforward_injective_isFlasque f φ M
  exact derivedModuleGammaZSections_isZero_of_isFlasque S Z U _ n

end SGA.SGA2.ExposeV
