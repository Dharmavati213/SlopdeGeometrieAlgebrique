/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.GaloisFunctors
import SGA.SGA1.ExposeX.Specialization
import SGA.SGA1.ExposeX.EtaleCoverings
import SGA.SGA1.ExposeX.HomotopySequence
import SGA.SGA1.ExposeX.CoveringOfBase
import SGA.SGA1.ExposeX.ProperOverField
import SGA.SGA1.ExposeX.Product
import SGA.SGA1.ExposeX.ArtinSchreier
import SGA.SGA1.ExposeX.Semicontinuity
import SGA.SGA1.ExposeX.Henselian
import SGA.SGA1.ExposeX.Purity
import SGA.SGA1.ExposeX.PurityFundamentalGroup
import SGA.SGA1.ExposeX.PurityTheorem
import SGA.SGA1.ExposeX.PurityDenseOpen
import SGA.SGA1.ExposeX.PurityBirational
import SGA.SGA1.ExposeX.TameInertia
import SGA.SGA1.ExposeX.TameSpecialization
import SGA.SGA1.ExposeX.SteinEtale
import SGA.SGA1.ExposeX.BaseChangeAlgClosed
import SGA.SGA1.ExposeX.ConstantFamily
import SGA.SGA1.ExposeX.SpecializationGeometric
import SGA.SGA1.ExposeX.SpecializationSurjective
import SGA.SGA1.ExposeX.CurveFiniteSmooth
import SGA.SGA1.ExposeX.NormalCompleteLocalBase
import SGA.SGA1.ExposeX.TameLifting
import SGA.SGA1.ExposeX.TameLiftingAlgebra
import SGA.SGA1.ExposeX.TameLiftingBaseChange
import SGA.SGA1.ExposeX.TameLiftingDescent
import SGA.SGA1.ExposeX.TameLiftingExtension
import SGA.SGA1.ExposeX.TameLiftingFiniteLevel
import SGA.SGA1.ExposeX.TameLiftingGalois
import SGA.SGA1.ExposeX.TameLiftingKummer
import SGA.SGA1.ExposeX.TameLiftingLocal
import SGA.SGA1.ExposeX.TameLiftingNormalization
import SGA.SGA1.ExposeX.TameLiftingProof
import SGA.SGA1.ExposeX.TameLiftingPurity
import SGA.SGA1.ExposeX.TameLiftingReduction
import SGA.SGA1.ExposeX.TameLiftingSpecialization
import SGA.SGA1.ExposeX.TopologicallyFinite
import SGA.SGA1.ExposeX.TopologicallyFiniteBaseChange
import SGA.SGA1.ExposeX.TopologicallyFiniteCharZero
import SGA.SGA1.ExposeX.TopologicallyFiniteComplex
import SGA.SGA1.ExposeX.TopologicallyFiniteReduction

import SGA.SGA1.ExposeX.CurveFinitePlaneModel
import SGA.SGA1.ExposeX.TameLiftingDomination
import SGA.SGA1.ExposeX.TameLiftingGeneral
import SGA.SGA1.ExposeX.TameLiftingSplitting
import SGA.SGA1.ExposeX.TameLiftingUnramified
import SGA.SGA1.ExposeX.TopologicallyFiniteBertini
import SGA.SGA1.ExposeX.TopologicallyFiniteCharZeroDescent
import SGA.SGA1.ExposeX.TopologicallyFiniteHyperplane
import SGA.SGA1.ExposeX.TopologicallyFiniteHyperplaneCovers
/-!
# SGA 1, Exposé X — Theory of specialization of the fundamental group

English translation: `translation/SGA1/ExposeX/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

The inputs of the exposé that are not proved in general are recorded as `…Statement`
propositions: X.2.1 = IX.1.10 (Grothendieck's existence theorem), X.2.4, X.2.9 and X.3.8; each
is proved in special cases, listed below. What is proved:

* `GaloisFunctors`: the dictionary of Exposé V, §6 between functors of Galois categories and
  homomorphisms of fundamental groups (surjectivity, triviality and exactness criteria), which
  is how SGA deduces X.1.4 from X.1.3, X.2.1 from IX.1.10 and X.3.3 (last part) from X.3.1;
* `Specialization`: the group theory of X.1.7, X.2.2–X.2.3 (the specialization homomorphism),
  X.2.12, the core of X.3.6 and X.3.9;
* `EtaleCoverings`: the category of étale coverings of a scheme (Exposé V), separable morphisms
  (X.1.1), and the comparison of connectedness and sections with their categorical versions;
* `HomotopySequence`, `CoveringOfBase`: X.1.3 (necessity unconditionally, sufficiency from X.1.2
  with EGA III 4.3.4), the homotopy exact sequence X.1.4 from X.1.2, the remarks X.1.5;
* `ProperOverField`, `Product`: `Γ(X, 𝒪_X) = k` and `X ⊗ₖ K` connected for `X` proper connected
  over `k` algebraically closed, the surjectivity half of X.1.8, and X.1.7 (rational base point,
  `X` reduced) from X.1.2;
* `ArtinSchreier`: the counterexamples X.1.10;
* `Semicontinuity`: X.2.1 when `X` is finite over `Y`, the statements X.2.1, X.2.4 and X.2.9
  (`CompleteLocalBaseStatement`, `SpecializationSurjectiveStatement`,
  `TopologicallyFiniteStatement`) with their consequences;
* `NormalCompleteLocalBase`: X.2.1 for `X` integral and normal, by Chow's lemma
  (`isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme`,
  `bijective_map_of_isNormalScheme`);
* `Henselian`: the isomorphism `π₁(k) ≅ π₁(Y)` used before X.2.2 (`Y` the spectrum of a
  henselian, e.g. complete, local ring), from `SGA.Foundations.HenselianFiniteEtale`;
* `TopologicallyFinite`, `TopologicallyFiniteBaseChange`: the two formulations of "topologically
  finitely generated" used in the project, independence of the base point, invariance under an
  extension of the algebraically closed base field (from X.1.8), and X.2.12 for a connected
  scheme whose `π₁` is topologically finitely generated (`finite_principalH1_of_isTopologicallyFG`);
* `TopologicallyFiniteCharZero` (with `TopologicallyFiniteComplex`): X.2.9 and X.2.12 for every
  proper connected `X` over an algebraically closed field `k : Type` of characteristic `0` with
  `#k ≤ 𝔠`, in universe `0` (`isTopologicallyFG_etaleFundamentalGroup_of_mk_le_continuum`,
  `finite_principalH1_of_mk_le_continuum`), by comparison with the topological fundamental group
  of `X(ℂ)` (the easy half of XII.5.2 and `ExposeXII.semilocallySimplyConnectedStatement`),
  without the Riemann existence theorem or SGA's reduction to curves;
* `TopologicallyFiniteReduction`, `CurveFiniteSmooth`: SGA's reduction of X.2.9, in every
  characteristic, to the curve case for normal proper curves and the hyperplane step X.2.10 in an
  existence form (for `X` normal, integral, proper, of dimension `≥ 2` and finite over a
  projective space: a proper connected `Y` of smaller dimension over an algebraically closed
  extension `K` of `k`, with a morphism `Y ⟶ X_K` surjective on `π₁`), with Chow's lemma and
  normalization proved (`topologicallyFiniteStatement_of_curve_of_hyperplane_of_isFinite`); a
  normal curve over a perfect field is smooth;
* `Purity`, `PurityFundamentalGroup`, `PurityTheorem`, `PurityDenseOpen`, `PurityBirational`
  (with `SGA.Foundations.CommAlg`, Zariski–Nagata purity in every dimension): X.3.1–X.3.4;
* `TameInertia`: tame inertia groups are cyclic and Abhyankar's lemma X.3.6;
* `TameSpecialization`: statement X.3.8 over a locally noetherian base
  (`TameSpecializationStatement`) and X.3.9 from it
  (`exists_primeToQuotientEquiv_of_tameSpecialization`, and
  `exists_bijective_of_tameSpecialization` in residue characteristic `0`);
* `TameLifting`, `TameLiftingProof`, with `TameLiftingReduction`, `TameLiftingAlgebra`,
  `TameLiftingBaseChange`, `TameLiftingKummer`, `TameLiftingPurity`, `TameLiftingGalois`,
  `TameLiftingLocal`, `TameLiftingNormalization`, `TameLiftingExtension`, `TameLiftingDescent`
  and `TameLiftingFiniteLevel`: the core of X.3.8, the case to which SGA reduces it in X.3.7
  (`TameLiftingDVRStatement`, over a complete discrete valuation ring with separably closed
  residue field), proved as `tameLiftingDVRStatement`;
* `TameLiftingSpecialization`: X.3.8 and X.3.9 for `Y` the spectrum of a complete discrete
  valuation ring with separably closed residue field, `y₀` the closed and `y₁` the generic point
  (`exists_tameSpecialization_of_isDiscreteValuationRing`,
  `exists_primeToQuotientEquiv_of_isDiscreteValuationRing`, and
  `exists_bijective_specialization_of_isDiscreteValuationRing` in residue characteristic `0`);
* `SteinEtale` (with `SGA.Foundations.Cohomology`, EGA III 7.8.10): X.1.2, hence X.1.3, the
  homotopy exact sequence X.1.4, and X.1.7 (rational base point, `X` reduced);
* `BaseChangeAlgClosed` (with `SGA.Foundations.Limits`): X.1.8;
* `ConstantFamily`: X.1.9, from X.1.7, X.1.4 and X.1.8 by an argument with classes of paths;
* `SpecializationGeometric`, `SpecializationSurjective`: X.2.2–X.2.4 (for `X` projective over
  `Y`, and for `X` proper from IX.1.10), X.1.4 at algebraically closed geometric points.

Open: X.2.1 (IX.1.10) for every proper `X`, and X.2.4, which follows from it; X.2.9 in
characteristic `p`, for `#k > 𝔠` and in universes other than `0`; X.2.10–X.2.11 (Bertini's
theorem); X.3.8 over a general base, which needs a discrete valuation ring dominating a
noetherian local domain (EGA II 7.1.7) and its completed strict henselization.

Not formalized: X.1.6 (the homotopy sequence with `π₀`); the remarks X.2.5, X.2.7, X.2.8, X.2.13,
X.2.14, X.3.5 and X.3.11; the theorem X.2.6 (the transcendental computation of `π₁` of a smooth
proper curve); X.3.7 as a criterion (the case of X.3.8 it reduces to is `tameLiftingDVRStatement`);
X.3.10 (it needs X.2.6).
-/
