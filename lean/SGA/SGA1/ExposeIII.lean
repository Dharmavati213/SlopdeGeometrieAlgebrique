/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.FormallySmooth
import SGA.SGA1.ExposeIII.Descent
import SGA.SGA1.ExposeIII.PowerSeries
import SGA.SGA1.ExposeIII.PowerSeriesCompletion
import SGA.SGA1.ExposeIII.PowerSeriesStructure
import SGA.SGA1.ExposeIII.ResidueLift
import SGA.SGA1.ExposeIII.Semilocal
import SGA.SGA1.ExposeIII.LocalComponents
import SGA.SGA1.ExposeIII.LiftingCriteria
import SGA.SGA1.ExposeIII.FlatFibre
import SGA.SGA1.ExposeIII.Completion
import SGA.SGA1.ExposeIII.SmoothLocal
import SGA.SGA1.ExposeIII.Lifting
import SGA.SGA1.ExposeIII.Torsor
import SGA.SGA1.ExposeIII.Deformation
import SGA.SGA1.ExposeIII.Schemes
import SGA.SGA1.ExposeIII.Thickening
import SGA.SGA1.ExposeIII.ExtensionSheaf
import SGA.SGA1.ExposeIII.ExtensionCharts
import SGA.SGA1.ExposeIII.LocalizationHom
import SGA.SGA1.ExposeIII.DerivationSheaf
import SGA.SGA1.ExposeIII.GlobalExtension
import SGA.SGA1.ExposeIII.ExtensionTorsor
import SGA.SGA1.ExposeIII.FormalExtension
import SGA.SGA1.ExposeIII.AffineLift
import SGA.SGA1.ExposeIII.SmoothLift
import SGA.SGA1.ExposeIII.FormalLift
import SGA.SGA1.ExposeIII.ArtinianCriterion
import SGA.SGA1.ExposeIII.LiftingCriterion
import SGA.SGA1.ExposeIII.FormalIsomorphism
import SGA.SGA1.ExposeIII.TwoChartLift
import SGA.SGA1.ExposeIII.FormalUniqueness
import SGA.SGA1.ExposeIII.RelativeDerivation
import SGA.SGA1.ExposeIII.RelativeExtension

import SGA.SGA1.ExposeIII.CurveLiftAssembly
import SGA.SGA1.ExposeIII.CurveLiftBase
import SGA.SGA1.ExposeIII.CurveLiftCharts
import SGA.SGA1.ExposeIII.CurveLiftCurve
import SGA.SGA1.ExposeIII.CurveLiftFinite
import SGA.SGA1.ExposeIII.CurveLiftFlat
import SGA.SGA1.ExposeIII.CurveLiftSmooth
import SGA.SGA1.ExposeIII.CurveLiftStage
import SGA.SGA1.ExposeIII.CurveLiftSystem
/-!
# SGA 1, Exposé III — Smooth morphisms: extension properties

English translation: `translation/SGA1/ExposeIII/` (repo root).
This module is the barrel for the Lean formalization of the exposé:

* `FormallySmooth`: formal smoothness for adic topologies, lifting into complete rings,
  power series rings, Definition III.1.1 and Lemma III.1.3 (§§1–2);
* `Descent`: Proposition III.1.4 (ii) for the lifting property (descent along a finite free
  extension);
* `PowerSeries`: Corollaries III.2.2 (v) ⇒ (i) and III.2.3, recognising power series rings;
* `PowerSeriesCompletion`: powers of the maximal ideal of `A⟦t⟧`, and its completeness;
* `PowerSeriesStructure`: III.1.5, and III.2.1–III.2.2 for trivial residue extensions;
* `ResidueLift`: finite free lifts of residue field extensions (the lemma of III.1.6);
* `Semilocal`: local components of complete semi-local rings, and formal smoothness of them;
* `LocalComponents`: III.1.4 (i), (ii) (Definition III.1.1), III.1.6, III.2.1 (i) ⇔ (iii), for a
  finite residue extension;
* `LiftingCriteria`: Theorem III.2.1, (i) ⇔ (ii) ⇔ (iii) ⇔ (iv) ⇔ (iv bis);
* `FlatFibre`: Corollary III.1.7 (flatness and formal smoothness of the closed fibre);
* `Completion`: Remark III.1.2 (formal smoothness only depends on the completions) and
  Proposition III.1.9 in the form of Definition III.1.1;
* `SmoothLocal`: Proposition III.1.9, formal smoothness versus smoothness, and III.1.7 for
  localizations of algebras of finite type;
* `Lifting`: infinitesimal extension of morphisms into smooth and étale algebras (§3);
* `Torsor`: the torsor of extensions under derivations, and automorphisms of lifts
  (III.5.1, III.5.2, III.6.1, affine case);
* `Deformation`: Lemma III.4.2, existence and uniqueness of smooth lifts (III.4.1, III.6.8),
  and extension of morphisms to formal completions (III.5.6), affine case;
* `Schemes`: scheme-theoretic forms: local extension of morphisms along nil thickenings and its
  uniqueness for étale morphisms (III.3.1, III.3.2), local existence of smooth lifts (III.4.1),
  sections through rational points over a complete local ring (III.3.3);
* `Thickening`: Lemma III.4.2 for schemes, and the local uniqueness of smooth lifts (III.4.1);
* `ExtensionSheaf`: the sheaf of extensions (III.5.1) and gluing of morphisms over opens;
* `ExtensionCharts`: extensions described on affine charts;
* `LocalizationHom`: `Hom(M, -)` and `Der(A, -)` commute with localization;
* `DerivationSheaf`: the sheaf `𝒢 = ℋom(g₀^* Ω, 𝒥)` of III.5.2 on charts, the difference of
  two extensions, the action of `𝒢` on extensions, and the quasi-coherence of `𝒢`;
* `GlobalExtension`: Theorem III.5.5 (global extensions over affine schemes), via Čech
  cohomology of `𝒢` for standard covers;
* `ExtensionTorsor`: `𝒢` is a sheaf, the extensions form a torsor under `𝒢` (III.5.1, III.5.2),
  and its class in `H¹` vanishes exactly when a global extension exists;
* `FormalExtension`: III.5.4–III.5.6 for affine thickenings: extension of morphisms to formal
  completions;
* `AffineLift`: uniqueness and existence of smooth lifts of affine schemes over an affine base
  (III.4.1, III.6.8);
* `SmoothLift`: existence of smooth lifts of smooth affine schemes (III.6.8), by gluing local
  lifts two basic opens at a time;
* `FormalLift`: formal smooth lifts of affine schemes (III.6.10, affine case);
* `ArtinianCriterion`: III.2.1, (iii) ⇔ (iv) for noetherian local rings which need not be
  complete;
* `LiftingCriterion`: Theorem III.3.1, (i) ⇔ (iii), and Corollary III.3.2, (i) ⇔ (iii), for
  schemes (lifting over spectra of local artinian rings finite over local rings of `Y`);
* `FormalIsomorphism`: Proposition III.5.8 for affine formal schemes;
* `TwoChartLift`: Corollary III.6.7 (existence) and III.6.10 for schemes which are the union of
  two affine opens with affine intersection, and the variant of Lemma III.4.2 for open immersions;
* `FormalUniqueness`: the uniqueness in Proposition III.5.8 for affine formal schemes, and III.5.6
  for `H⁰` on affine charts;
* `RelativeDerivation`: the sheaf `𝒢 = ℋom(g₀^* Ω_{X/S}, 𝒥)` on charts over an affine base `S`,
  for a thickening `T` which need not be affine (III.5.2);
* `RelativeExtension`: III.5.3–5.4 in Čech form for a non-affine thickening;
* `CurveLift*`: III.7.4 (`smoothProperCurveLiftStatement`), by a finite flat map to `ℙ¹`.

The remaining global statements of §§6–7 need coherent cohomology and formal schemes. See
`docs/formalization.md`.
-/
