/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.GAGA
import SGA.SGA1.ExposeXII.MorphismComparison
import SGA.Foundations.Analytic.ModulesExactness

/-!
# SGA 1, Exposé XII, 1.3.1: `F ↦ F^an` is exact, faithful and conservative

For a separated `ℂ`-scheme `X` locally of finite type and `φ : X^an → X`, the analytification
`F ↦ F^an = φ^* F` of `𝒪_X`-modules (`AnalyticGluing.analytification`, XII.1.3) is

* exact (`AnalyticGluing.exact_analytification`, `preservesFiniteLimits_analytification`): the
  maps `𝒪_{X,φ(x)} → 𝒪_{X^an,x}` are flat (`isComparison_toScheme`), and the stalk of `φ^* F` at
  `x` is `𝒪_{X^an,x} ⊗ F_{φ(x)}` (`LocallyRingedSpace.Modules.pullbackStalkIso`);
* faithful (`faithful_analytification`) and conservative (`reflectsIsomorphisms_analytification`):
  if `F^an = 0` then `F_{φ(x)} = 0` for every `x` by faithful flatness, so `F` vanishes at all
  closed points of `X` (`range_toScheme_base`), hence everywhere since `X` is Jacobson
  (`isZero_of_isZero_analytification`, through
  `LocallyRingedSpace.Modules.isZero_of_forall_closedPoints` in
  `SGA.Foundations.Analytic.ModulesExactness`).

This holds for all `𝒪_X`-modules, as in SGA. Deviation: `X` is separated (`X^an` is only built for
separated `X` here).
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

namespace SGA.SGA1.ExposeXII.AnalyticGluing

open LocallyRingedSpace.Modules

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [IsSeparated (X ↘ Spec (.of ℂ))]

instance : (analytification X).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction (toScheme X)).isLeftAdjoint

instance : (analytification X).Additive := additive_pullback (toScheme X)

/-- XII.1.3.1, exactness: `F ↦ F^an` maps exact sequences of `𝒪_X`-modules to exact sequences,
because `φ : X^an → X` is flat. Deviation: `X` is separated (`X^an` is only built for separated `X`
here). -/
theorem exact_analytification (C : ShortComplex X.Modules) (hC : C.Exact) :
    (C.map (analytification X)).Exact :=
  exact_pullback_of_flat_stalkMap (toScheme X)
    (fun x ↦ (isComparison_toScheme.isComparisonHom x).flat) C hC

/-- XII.1.3.1, exactness: `F ↦ F^an` commutes with finite limits (it commutes with all colimits,
being a left adjoint). Deviation: `X` is separated (`X^an` is only built for separated `X` here). -/
instance preservesFiniteLimits_analytification : PreservesFiniteLimits (analytification X) :=
  preservesFiniteLimits_pullback_of_flat_stalkMap (toScheme X)
    (fun x ↦ (isComparison_toScheme.isComparisonHom x).flat)

/-- XII.1.3.1, exactness: `F ↦ F^an` maps short exact sequences to short exact sequences.
Deviation: `X` is separated (`X^an` is only built for separated `X` here). -/
theorem shortExact_analytification (C : ShortComplex X.Modules) (hC : C.ShortExact) :
    (C.map (analytification X)).ShortExact :=
  hC.map_of_exact (analytification X)

/-- XII.1.3.1: if `F^an = 0`, then `F = 0`. Deviation: `X` is separated (`X^an` is only built for
separated `X` here). -/
theorem isZero_of_isZero_analytification (F : X.Modules)
    (hF : IsZero ((analytification X).obj F)) : IsZero F := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of ℂ))
  have : JacobsonSpace X.toLocallyRingedSpace := ‹JacobsonSpace X›
  refine isZero_of_forall_closedPoints (X := X.toLocallyRingedSpace) F fun y hy ↦ ?_
  have hy' : y ∈ closedPoints X := hy
  rw [← range_toScheme_base] at hy'
  obtain ⟨x, rfl⟩ := hy'
  have h0 := ((isZero_iff_stalkFunctor_obj_isZero _).mp hF x).of_iso
    ((pullbackStalkIso x (toScheme X)).app F).symm
  rw [ModuleCat.isZero_iff_subsingleton] at h0 ⊢
  have hff : Module.FaithfullyFlat (X.presheaf.stalk ((toScheme X).base x))
      ((ModuleCat.restrictScalars ((toScheme X).stalkMap x).hom).obj
        (ModuleCat.of _ ((analyticSpace X).presheaf.stalk x))) :=
    (isComparison_toScheme.isComparisonHom x).faithfullyFlat
  exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right _
    ((ModuleCat.restrictScalars ((toScheme X).stalkMap x).hom).obj
      (ModuleCat.of _ ((analyticSpace X).presheaf.stalk x)))).mp h0

/-- XII.1.3.1: `F ↦ F^an` reflects isomorphisms (it is conservative). Deviation: `X` is separated
(`X^an` is only built for separated `X` here). -/
instance reflectsIsomorphisms_analytification : (analytification X).ReflectsIsomorphisms := by
  refine ⟨fun {F G} f hf ↦ ?_⟩
  have hmono : Mono f := by
    refine Preadditive.mono_of_isZero_kernel' _ (kernelIsKernel f) ?_
    refine isZero_of_isZero_analytification _ ?_
    exact IsZero.of_iso (isZero_kernel_of_mono ((analytification X).map f))
      (PreservesKernel.iso (analytification X) f)
  have hepi : Epi f := by
    refine Preadditive.epi_of_isZero_cokernel' _ (cokernelIsCokernel f) ?_
    refine isZero_of_isZero_analytification _ ?_
    exact IsZero.of_iso (isZero_cokernel_of_epi ((analytification X).map f))
      (PreservesCokernel.iso (analytification X) f)
  exact isIso_of_mono_of_epi f

/-- XII.1.3.1: `F ↦ F^an` is faithful. Deviation: `X` is separated (`X^an` is only built for
separated `X` here). -/
instance faithful_analytification : (analytification X).Faithful := by
  refine ⟨fun {F G} f g hfg ↦ ?_⟩
  rw [← sub_eq_zero]
  have h0 : (analytification X).map (f - g) = 0 := by
    rw [Functor.map_sub, hfg, sub_self]
  -- the kernel of `f - g` becomes an isomorphism after analytification
  have : IsIso (kernel.ι ((analytification X).map (f - g))) := kernel.ι_of_zero h0
  have : IsIso ((analytification X).map (kernel.ι (f - g))) := by
    rw [← kernelComparison_comp_ι]
    infer_instance
  have : IsIso (kernel.ι (f - g)) := isIso_of_reflects_iso _ (analytification X)
  rw [← cancel_epi (kernel.ι (f - g)), kernel.condition, comp_zero]

end SGA.SGA1.ExposeXII.AnalyticGluing
