/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIV.TorOne
import SGA.SGA1.ExposeIV.FlatModules
import SGA.SGA1.ExposeIV.FaithfullyFlat
import SGA.SGA1.ExposeIV.Completion
import SGA.SGA1.ExposeIV.Graded
import SGA.SGA1.ExposeIV.FreeModules
import SGA.SGA1.ExposeIV.LocalCriterion
import SGA.SGA1.ExposeIV.CompletionCriterion
import SGA.SGA1.ExposeIV.Constructible
import SGA.SGA1.ExposeIV.OpenMorphisms
import SGA.SGA1.ExposeIV.GenericFreeness
import SGA.SGA1.ExposeIV.FlatLocus
import SGA.SGA1.ExposeIV.Schemes
import SGA.SGA1.ExposeIV.CoherentModules

/-!
# SGA 1, Exposé IV — Flat morphisms

English translation: `translation/SGA1/ExposeIV/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

* `TorOne`: vanishing of `Tor₁` without derived functors, and the criteria of IV.1;
* `FlatModules`: IV.1.1–IV.1.3 and the permanence properties of flatness;
* `FaithfullyFlat`: IV.2.1–IV.2.6, including going down for a finite flat module of full support;
* `Completion`: IV.3.1–IV.3.2;
* `Graded`: the map `gr⁰_I(M) ⊗ gr_I(A) → gr_I(M)` and IV.5.1;
* `FreeModules`: IV.4.1–IV.4.4, and the generalization of IV.4.4 to reduced rings;
* `LocalCriterion`: IV.5.2–IV.5.7 and IV.5.9 (the local flatness criterion);
* `CompletionCriterion`: IV.5.8 (flatness and completion);
* `Constructible`: IV.6.1–IV.6.4 (constructible sets, Chevalley's theorem);
* `OpenMorphisms`: IV.6.5–IV.6.6 (flat morphisms are open);
* `GenericFreeness`: IV.6.7 (generic freeness);
* `FlatLocus`: IV.6.8–IV.6.11 (openness of the flat locus);
* `Schemes`: IV.6.5, IV.6.10 and IV.6.11 for schemes (with `F = 𝒪_X`);
* `CoherentModules`: IV.6.6, IV.6.10 and IV.6.11 for a coherent sheaf `F` on a scheme.

Mathlib's `Module.Flat` and `Module.FaithfullyFlat` are used throughout. The statements of §6
about a coherent sheaf `F` are proved first for a finite module over a finitely generated algebra
(the affine case), then for a quasi-coherent module of finite type on a scheme, through the
description of its stalks over affine opens (`SGA.Foundations.QuasiCoherent.StalkModule`).
-/
