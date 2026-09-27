/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVIII.ModuleDescent
import SGA.SGA1.ExposeVIII.ModuleDescentIso
import SGA.SGA1.ExposeVIII.SubmoduleDescent
import SGA.SGA1.ExposeVIII.QuasiCoherentDescent
import SGA.SGA1.ExposeVIII.ModuleProperties
import SGA.SGA1.ExposeVIII.AffineDescent
import SGA.SGA1.ExposeVIII.AffineSchemeDescent
import SGA.SGA1.ExposeVIII.AffineHomDescent
import SGA.SGA1.ExposeVIII.PropertyDescent
import SGA.SGA1.ExposeVIII.TopologicalDescent
import SGA.SGA1.ExposeVIII.MorphismDescent
import SGA.SGA1.ExposeVIII.FiniteDescent
import SGA.SGA1.ExposeVIII.Effectiveness
import SGA.SGA1.ExposeVIII.AmpleEffectiveness
import SGA.SGA1.ExposeVIII.LineBundleDescent
import SGA.SGA1.ExposeVIII.FiniteSpreadingOut
import SGA.SGA1.ExposeVIII.FiniteSubalgebraGluing
import SGA.SGA1.ExposeVIII.QuasiFiniteOpenInFinite

/-!
# SGA 1, Exposé VIII — Faithfully flat descent

English translation: `translation/SGA1/ExposeVIII/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

* §1, descent of quasi-coherent Modules: `ModuleDescent`, `ModuleDescentIso`,
  `SubmoduleDescent`, `QuasiCoherentDescent`, `ModuleProperties`;
* §2, descent of preschemes affine over the base: `AffineDescent`, `AffineSchemeDescent`,
  `AffineHomDescent`;
* §3, set-theoretic and finiteness properties: `PropertyDescent`;
* §4, topological properties: `TopologicalDescent`;
* §5, properties of morphisms: `MorphismDescent`;
* §6, finite and quasi-finite morphisms: `FiniteDescent`, `FiniteSpreadingOut`,
  `FiniteSubalgebraGluing`, `QuasiFiniteOpenInFinite`;
* §7, effectiveness criteria: `Effectiveness`, `AmpleEffectiveness`, `LineBundleDescent`.

Every numbered statement of the exposé is proved: VIII.6.4 over a noetherian base, as in SGA
(and over an affine base without that hypothesis), the others over an arbitrary base.
Ampleness, norms and quasi-projectivity come from `SGA.Foundations.Projective`.
-/
