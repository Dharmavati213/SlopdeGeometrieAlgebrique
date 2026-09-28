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
  `FiniteEffectiveDescent`, `QuasiFiniteDescent`, `TopologicalInvariance`;
* §5, translation into the language of the fundamental group: `ConnectedFibres`,
  `FiniteEtaleDescentDiagram`, `GaloisFunctors`, `FundamentalGroupDescent`;
* §6, a fundamental exact sequence: `ExactSequence`, `FiniteEtaleLimit`,
  `ExactSequenceCompleteLocal` (IX.6.1, 6.7, 6.8, 6.11 over a complete local base);
* IX.4 in the form of IX.5 (IX.4.12, IX.5.6 for proper coverings, IX.6.8 (a)–(c), IX.6.9 over a
  locally noetherian base): `FiniteEtaleEffectiveDescent`;
* IX.6.7, IX.6.8 and IX.6.11 over a locally noetherian base: `ProperDescentRigidity`,
  `ProperDescentLocal`, `ProperDescentGeometricFibres`; IX.6.9 over an arbitrary base:
  `ProperDescentLimit`;
* IX.1.10 (with `SGA.Foundations.Cohomology`, the Grothendieck existence theorem):
  `EtaleCoveringsClosedFibre`, for `X` projective, and full faithfulness for `X` proper;
  IX.4.12 over a locally noetherian base: `ProperEffectiveDescent`.

The items still stated as `…Statement` are listed in `docs/formalization.md`.
-/
