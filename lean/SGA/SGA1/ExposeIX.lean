/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.Unramified
import SGA.SGA1.ExposeIX.EtaleMorphismDescent
import SGA.SGA1.ExposeIX.NilImmersion
import SGA.SGA1.ExposeIX.CompleteLocal
import SGA.SGA1.ExposeIX.Submersive
import SGA.SGA1.ExposeIX.SubmersiveCompleteLocal
import SGA.SGA1.ExposeIX.FlatBaseChange
import SGA.SGA1.ExposeIX.EffectiveGluing
import SGA.SGA1.ExposeIX.EffectiveNearPoint
import SGA.SGA1.ExposeIX.CompletedLocalRings
import SGA.SGA1.ExposeIX.EtaleEffectiveDescent
import SGA.SGA1.ExposeIX.QuasiAffineDescent
import SGA.SGA1.ExposeIX.FiniteEffectiveDescent
import SGA.SGA1.ExposeIX.StrictlyLocalDescent
import SGA.SGA1.ExposeIX.HenselianFiniteDescent
import SGA.SGA1.ExposeIX.QuasiFiniteDescent
import SGA.SGA1.ExposeIX.UniversallyOpenDescent
import SGA.SGA1.ExposeIX.TopologicalInvariance
import SGA.SGA1.ExposeIX.ConnectedFibres
import SGA.SGA1.ExposeIX.FiniteEtaleDescentDiagram
import SGA.SGA1.ExposeIX.GaloisFunctors
import SGA.SGA1.ExposeIX.FundamentalGroupDescent
import SGA.SGA1.ExposeIX.ExactSequence
import SGA.SGA1.ExposeIX.FiniteEtaleLimit
import SGA.SGA1.ExposeIX.EtaleCoveringsClosedFibre
import SGA.SGA1.ExposeIX.ProperEffectiveDescent
import SGA.SGA1.ExposeIX.ExactSequenceCompleteLocal
import SGA.SGA1.ExposeIX.FiniteEtaleEffectiveDescent
import SGA.SGA1.ExposeIX.ProperDescentRigidity
import SGA.SGA1.ExposeIX.ProperDescentLocal
import SGA.SGA1.ExposeIX.ProperDescentGeometricFibres
import SGA.SGA1.ExposeIX.ProperDescentLimit
import SGA.SGA1.ExposeIX.DescentFiniteGeneration
import SGA.SGA1.ExposeIX.Pinching
import SGA.SGA1.ExposeIX.PinchingCurve
import SGA.SGA1.ExposeIX.PinchingCurveNormalization

/-!
# SGA 1, Exposé IX — Descent of étale morphisms. Application to the fundamental group

English translation: `translation/SGA1/ExposeIX/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

* §1, étale morphisms and sections, nilpotent thickenings, complete local bases: `Unramified`,
  `EtaleMorphismDescent`, `NilImmersion`, `CompleteLocal`;
* §2, submersive and universally submersive morphisms: `Submersive`, `SubmersiveCompleteLocal`;
* §3, descent of morphisms of étale schemes: `EtaleMorphismDescent`;
* §4, effective descent of étale schemes: `FlatBaseChange`, `EffectiveGluing`,
  `EffectiveNearPoint`, `CompletedLocalRings`, `EtaleEffectiveDescent`, `QuasiAffineDescent`,
  `FiniteEffectiveDescent`, `QuasiFiniteDescent`, `TopologicalInvariance`; IX.4.6 with separably
  closed residue fields: `StrictlyLocalDescent`; IX.4.7 over an arbitrary base:
  `HenselianFiniteDescent`; IX.4.9 from quasi-sections (`QuasiSectionStatement`):
  `UniversallyOpenDescent`;
* §5, translation into the language of the fundamental group: `ConnectedFibres`,
  `FiniteEtaleDescentDiagram`, `GaloisFunctors`, `FundamentalGroupDescent` (IX.5.6, which is
  IX.5.1 when `S'` and `S''` are connected, and IX.5.2 in that case in the abstract
  Galois-category form, `DescentDiagram.DiagonalPoint.exists_finite_topologicalClosure_eq_top`);
* IX.5.2 with `S'` and `S''` not necessarily connected, when `S` is noetherian and connected
  and `g` is proper and surjective, by a direct argument without the presentation
  IX.5.1 (`isTopologicallyFG_etaleFundamentalGroup_of_isProper_of_surjective`, and a form for a
  finite family of proper morphisms used in the reduction of X.2.9 to curves):
  `DescentFiniteGeneration`;
* a consequence of IX.5.4 (pinching), "`π₁(S')` is topologically finitely generated if `π₁(S)`
  is", under hypotheses that replace SGA's (`isTopologicallyFG_etaleFundamentalGroup_of_pinching`):
  `Pinching`; the replacement hypotheses are checked for a finite surjective morphism over an
  algebraically closed field which is an isomorphism off finitely many closed points
  (`PinchingCurve`) and for the normalization of a curve (`PinchingCurveNormalization`);
* §6, a fundamental exact sequence: `ExactSequence`, `FiniteEtaleLimit`,
  `ExactSequenceCompleteLocal` (IX.6.1, 6.7, 6.8, 6.11 over a complete local base);
* IX.4 in the form of IX.5 (IX.4.12, IX.5.6 for proper coverings, IX.6.8 (a)–(c), IX.6.9 over a
  locally noetherian base): `FiniteEtaleEffectiveDescent`;
* IX.6.7, IX.6.8 and IX.6.11 over a locally noetherian base: `ProperDescentRigidity`,
  `ProperDescentLocal`, `ProperDescentGeometricFibres`; IX.6.9 over an arbitrary base:
  `ProperDescentLimit`;
* IX.1.10 (with `SGA.Foundations.Cohomology`, the Grothendieck existence theorem):
  `EtaleCoveringsClosedFibre`, for `X` projective, and full faithfulness for `X` proper (for `X`
  integral and normal it is proved as X.2.1 in `SGA.SGA1.ExposeX.NormalCompleteLocalBase`);
  IX.4.12 over a locally noetherian base: `ProperEffectiveDescent`.

Not formalized: IX.5.1 when `S'` or `S''` is not connected, IX.5.3, IX.5.4 itself (the
presentation of `π₁(S)`), IX.5.5 and IX.5.7; of IX.5.8 only the group-theoretic translation;
IX.6.6 (only its case for an étale covering over `Spec 𝒪̂_{S,s}`, a step of the proof of IX.6.7,
is proved: `exists_isActAt_fromSpecCompletedStalk`); the remarks IX.6.3 and IX.6.12 and the
counterexample IX.6.10.
The items still stated as `…Statement` are listed in `docs/formalization.md`.
-/
