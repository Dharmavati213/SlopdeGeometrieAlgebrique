/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.LocalDualityFiniteFree
import SGA.SGA2.ExposeV.RegularLocalVanishing
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Right exactness of actual top local cohomology

The original Ext-colimit coefficient sequence, together with upper
vanishing, proves right exactness. Over a regular local ring its degree is
the actual Krull dimension. No global projective-dimension bound for all
modules is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The original local-cohomology coefficient sequence is exact at its
middle term. -/
theorem localCohomology_map_shortExact_exact (J : Ideal R) (i : ℕ)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    (S.map (_root_.localCohomology J i)).Exact :=
  ShortComplex.exact_of_iso (S.mapNatIso (idealPowerExtIsoLocalCohomology J i))
    (extColimit_exact₂ _ S hS i)

/-- Vanishing in the next degree makes the actual local-cohomology map
on the quotient coefficient module surjective. -/
theorem localCohomology_map_shortExact_epi (J : Ideal R) (i : ℕ)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (hzero : IsZero ((_root_.localCohomology J (i + 1)).obj S.X₁)) :
    Epi ((_root_.localCohomology J i).map S.g) := by
  let Q := localCohomology.ringModIdeals (localCohomology.idealPowersDiagram J)
  let e := idealPowerExtIsoLocalCohomology J i
  have hz := hzero.of_iso ((idealPowerExtIsoLocalCohomology J (i + 1)).app S.X₁)
  have : Epi ((extColimitFunctor Q i).map S.g) :=
    (extColimit_exact₃ Q S hS i).epi_f (hz.eq_zero_of_tgt _)
  have : Epi (e.hom.app S.X₂ ≫ (_root_.localCohomology J i).map S.g) := by
    rw [← e.hom.naturality]
    infer_instance
  exact epi_of_epi (e.hom.app S.X₂) _

/-- Upper vanishing implies right exactness of the original functor. -/
theorem localCohomology_preservesFiniteColimits_of_vanishing (J : Ideal R) (i : ℕ)
    (hzero : ∀ M : ModuleCat.{u} R,
      IsZero ((_root_.localCohomology J (i + 1)).obj M)) :
    PreservesFiniteColimits (_root_.localCohomology J i) := by
  apply (Functor.preservesFiniteColimits_tfae (_root_.localCohomology J i)).out 1 4 |>.mp
  intro S hS
  exact ⟨localCohomology_map_shortExact_exact J i S hS,
    localCohomology_map_shortExact_epi J i S hS (hzero S.X₁)⟩

/-- **V.2.1, right exactness input:** local cohomology in the actual
dimension of a regular local ring preserves finite colimits. -/
theorem regularLocal_topLocalCohomology_preservesFiniteColimits [IsRegularLocalRing R]
    (n : ℕ) (hdim : ringKrullDim R = n) :
    PreservesFiniteColimits (_root_.localCohomology (maximalIdeal R) n) :=
  localCohomology_preservesFiniteColimits_of_vanishing (maximalIdeal R) n
    (fun M => regularLocal_localCohomology_isZero_of_gt n hdim M (n + 1) (by omega))

end SGA.SGA2.ExposeV
