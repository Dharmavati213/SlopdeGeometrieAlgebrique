/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVII.HomVanishing
import SGA.SGA2.ExposeVII.HomSupportAnnihilator
import SGA.SGA2.ExposeVII.DepthCodimension
import SGA.SGA2.ExposeVII.ExactContravariantCoherence
import SGA.SGA2.ExposeVII.RegularUpperExt
import SGA.SGA2.ExposeVII.SupportedExtHomComparison
import SGA.SGA2.ExposeVII.VanishingCriteria
import SGA.SGA2.ExposeVII.CohenMacaulayCodimension
import SGA.SGA2.ExposeVII.SupportedExtCoherence
import SGA.SGA2.ExposeVII.RegularSupportedExtBounds
import SGA.SGA2.ExposeVII.DimensionSetInterval
import SGA.SGA2.ExposeVII.ExtCoherenceGap

/-!
# SGA 2, Exposé VII: vanishing criteria; coherence of Ext̲

English translation: `translation/SGA2/ExposeVII/` (repo root).

* `HomVanishing`: VII.1.3 — `Hom(P,H)=0` and `Supp H ⊆ Supp P` force `H=0`;
* `HomSupportAnnihilator`: affine end of VII.1.1 — maps into a module
  supported in `V(J)` are annihilated by a power of `J`;
* `SupportedExtHomComparison`: sheaf-level VII.1.1 — Extⁿ on finite modules
  supported in `V(J)` is left exact under Extⁿ⁻¹ vanishing, represented by
  Hom into the quotient-Ext colimit (= local cohomology) via IV.1.3, with
  the affine Hom-colimit comparison;
* `VanishingCriteria`: VII.1.2 — equivalence of local-cohomology / Ext
  vanishing conditions with a depth bound;
* `DepthCodimension` / `CohenMacaulayCodimension`: VII.1.4 — depth versus
  support-dimension / codimension for Cohen–Macaulay modules;
* `ExactContravariantCoherence`: VII.1.5 — finite generation transfers across
  exact sequences;
* `SupportedExtCoherence`: VII.1.6–VII.1.7 — finiteness of Ext and the
  depth-triggered coherence criterion on the torsion quotient;
* `RegularUpperExt` / `RegularSupportedExtBounds`: VII.2.1 — Ext vanishes
  above the regular dimension; local cohomology and Ext are coherent;
* `DimensionSetInterval`: VII.2.2 — `D(P)` is an interval (order-connected
  height sets; unions of meeting intervals);
* `ExtCoherenceGap`: VII.2.3 — Ext into the ring is coherent outside `D(P)`,
  by the high-degree vanishing / low-degree depth branches.
-/
