/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.Torsion
import SGA.SGA2.ExposeII.FiniteGeneratorColimits
import SGA.SGA2.ExposeII.GeneratorHomColimit
import SGA.SGA2.ExposeII.InjectiveDetection
import SGA.SGA2.ExposeII.LocalCohomologyZero
import SGA.SGA2.ExposeII.LocalizationKernel
import SGA.SGA2.ExposeII.PrincipalSystem
import SGA.SGA2.ExposeII.PrincipalKoszul
import SGA.SGA2.ExposeII.VariableAnnihilators
import SGA.SGA2.ExposeII.VariableQuotients
import SGA.SGA2.ExposeII.KoszulProZero
import SGA.SGA2.ExposeII.KoszulExtComparisonZero
import SGA.SGA2.ExposeII.KoszulRegularResolution
import SGA.SGA2.ExposeII.KoszulTopTransition
import SGA.SGA2.ExposeII.KoszulTopQuotientColimit
import SGA.SGA2.ExposeII.KoszulLocalCohomology
import SGA.SGA2.ExposeII.KoszulLocalCohomologySequence
import SGA.SGA2.ExposeII.CohomologicalComparison
import SGA.SGA2.ExposeII.AffineComparisonZero
import SGA.SGA2.ExposeII.PrincipalCechComparison
import SGA.SGA2.ExposeII.InjectiveFlasque
import SGA.SGA2.ExposeII.AffineCohomologyVanishing
import SGA.SGA2.ExposeII.AffineCohomologyComparison
import SGA.SGA2.ExposeII.AffineRelativeSequence
import SGA.SGA2.ExposeII.Examples
import SGA.SGA2.ExposeII.LocalCohomologyScalarChange
import SGA.SGA2.ExposeII.KoszulSupportedComparison
import SGA.SGA2.ExposeII.AffineExtColimitComparison
import SGA.SGA2.ExposeII.TopologicalNoetherianFlasque
import SGA.SGA2.ExposeII.ExamplesII5
import SGA.SGA2.ExposeII.QuasiCoherentSupported
import SGA.SGA2.ExposeII.GeneralSchemeComparison

/-!
# SGA 2, Exposé II — Algebraic foundations for local cohomology

English translation: `translation/SGA2/ExposeII/` (repo root).

This formalization proves II.8 and II.11, II.9 for the family of all degrees,
and the noetherian affine comparison in every degree. Sheaf-valued and
general-scheme comparisons remain partial:

* `Torsion`: ideal-power torsion, functoriality, radical invariance, and
  `Hom(R/I, M)` identified with the submodule annihilated by `I`;
* `FiniteGenerators`, `FiniteGeneratorColimits`: cofinality of generator powers
  and ideal powers, and the resulting isomorphisms of Ext colimits;
* `TorsionColimit`, `GeneratorHomColimit`: the categorical Hom-colimit
  description of ideal-power torsion, natural in the coefficient module;
* `LocalCohomologyZero`: degree-zero algebraic local cohomology is torsion;
* `LocalizationKernel`: torsion is the kernel of the map to the product
  of the localizations at a finite generating family;
* `AffineSupport`, `AffineComparisonZero`: the actual supported sections of
  the associated sheaf agree with torsion, degree-zero Ext colimits, and
  degree-zero stable Koszul cohomology, including Exposé I's `gammaZ`;
* `EssentiallyZero`, `InjectiveDetection`: both directions of the Hom-colimit
  criterion in II.9, and closure under subobjects, quotients, and extensions;
* `Principal`: the one-generator annihilator argument of II.11;
* `PrincipalSystem`, `PrincipalKoszul`: the actual principal Koszul homology
  systems, their annihilator comparison, and essential vanishing;
* `VariableAnnihilators`: the varying-coefficient system argument in II.11;
* `KoszulComplex`, `KoszulCofiber`, `KoszulProZero`: finite Koszul complexes,
  their natural transitions and scalar short exact sequence, and the full
  induction proving II.11 for noetherian coefficient modules;
* `InjectiveHomology`, `KoszulCohomology`: Hom of homology computes cohomology
  with injective coefficients, proving II.9(b) ⇔ (c) for actual Koszul systems;
* `KoszulDegreeZero`, `KoszulCohomologyZero`: finite-stage and stable
  degree-zero Koszul comparisons without noetherian hypotheses;
* `KoszulAugmentation`, `ProjectiveComplexLift`, `KoszulExtComparison`:
  the actual Ext-to-Koszul map from augmented projective complexes;
* `KoszulExtComparisonZero`: that constructed map is an isomorphism in degree zero;
* `KoszulTopTransition`: the original top cohomology transition for power
  lists becomes multiplication by the product of the power differences on
  the actual quotient module, including IV.5.5's monomial-class shift;
* `KoszulTopQuotientColimit`: the actual power-ideal quotient diagram with
  direct product-multiplication maps has original top local cohomology as
  its colimit over a noetherian ring, retaining the original stage maps;
* `KoszulRegularResolution`: for a genuine regular sequence over a noetherian
  local ring, the original augmentation is a quasi-isomorphism, the original
  Koszul complex is a projective resolution, and the original finite-stage
  Ext comparison is an isomorphism in every degree, naturally in coefficients;
* `CohomologicalComparison`: the dimension-shifting isomorphism criterion;
* `KoszulCoefficientSequence`, `ExtCoefficientSequence`, `ExtColimitSequence`:
  actual coefficient connecting maps and exactness before and after colimits;
* `LocalCohomologyReindexing`, `KoszulLocalCohomologySequence`: the cofinal
  change from ideal powers to generator powers and the resulting canonical
  Ext-to-Koszul comparison commute with coefficient boundaries;
* `KoszulComparisonIsomorphism`, `KoszulLocalCohomology`: the canonical
  comparison is invertible under the equivalent vanishing conditions in
  II.9, hence over a noetherian ring (II.8); reindexing identifies its source
  with mathlib's algebraic local cohomology;
* `InjectiveLocalization`: principal localization of an injective module
  over a noetherian ring is surjective;
* `InjectiveTorsion`, `FiniteFractionCover`, `InjectiveFlasque`: supported
  torsion preserves injectivity over a noetherian ring; sections of injective
  associated sheaves extend globally from every open, proving flasqueness;
* `AffineExactness`, `AffineCohomologyVanishing`: the associated abelian sheaf
  functor is exact over any ring, its global sections recover the module,
  and ordinary higher cohomology vanishes over noetherian affine schemes;
* `ConnectingSequenceExtension`, `AffineCohomologyComparison`: the degree-zero
  comparison extends to a natural isomorphism from actual algebraic local
  cohomology to actual supported sheaf cohomology, over noetherian rings and
  for arbitrary coefficient modules, compatibly with all coefficient boundaries;
* `AffineRelativeSequence`: the noetherian affine four-term low-degree
  sequence and the higher supported/open-complement comparison II.(4.2)–(4.3);
* `LocalizationCokernelColimit`, `PrincipalCechComparison`: stable singleton
  Koszul cohomology in degree one is the cokernel of actual sheaf restriction
  to a principal open, and higher degrees vanish;
* `Examples`: essential vanishing with nonzero homology terms, and empty families.

Open-support derived sheaves are higher direct images (`II_1_open`).
Affine-chart restriction of derived supported sheaves is I.2.7. Quasi-coherence
of higher supported sheaves on general schemes, sheaf Ext colimits off
affines, and II.10 under mere topological noetherianity remain open.
-/
