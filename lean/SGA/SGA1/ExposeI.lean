/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeI.Differentials
import SGA.SGA1.ExposeI.Completion
import SGA.SGA1.ExposeI.QuasiFinite
import SGA.SGA1.ExposeI.Unramified
import SGA.SGA1.ExposeI.Etale
import SGA.SGA1.ExposeI.Discriminant
import SGA.SGA1.ExposeI.Fundamental
import SGA.SGA1.ExposeI.FiberStalk
import SGA.SGA1.ExposeI.Fibrewise
import SGA.SGA1.ExposeI.PrimitiveElement
import SGA.SGA1.ExposeI.StandardEtale
import SGA.SGA1.ExposeI.LocalStructure
import SGA.SGA1.ExposeI.CompleteLocal
import SGA.SGA1.ExposeI.Infinitesimal
import SGA.SGA1.ExposeI.TraceFormulas
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeI.DominantUnramified
import SGA.SGA1.ExposeI.Unibranch
import SGA.SGA1.ExposeI.NormalCoverings
import SGA.SGA1.ExposeI.SeparableDegreeFibre
import SGA.SGA1.ExposeI.CompletionCriteria
import SGA.SGA1.ExposeI.EtaleSiteInvariance
import SGA.SGA1.ExposeI.GeometricPoints

/-!
# SGA 1, Exposé I — Étale morphisms

English translation: `translation/SGA1/ExposeI/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

* §1 `Differentials`: `Ω¹` as the conormal module of the diagonal.
* §2 `QuasiFinite`: quasi-finite algebras and morphisms; I.2.2 over a complete base.
* §3 `Unramified`: unramified (net) morphisms, the local definition I.3.2 b), the
  unramified locus of a scheme morphism (I.3.3), and I.3.7 in truncated form (the completed
  form is in `CompletionCriteria`).
* §4 `Etale`: étale morphisms, local definition, I.4.4, the étale locus (I.4.5);
  `Discriminant`: the discriminant criterion I.4.10.
* §5 `Fundamental`: I.5.1–I.5.6 in full (étale + radicial = open immersion, sections,
  and extension of morphisms along surjective closed immersions); `Fibrewise`: I.5.7–I.5.9
  in full, using `FiberStalk` (the local ring of a fibre is `𝒪_{X,x}/𝔪_y 𝒪_{X,x}`).
* §6 `CompleteLocal`: I.6.1, finite étale algebras over a complete noetherian local ring
  are equivalent to finite étale algebras over its residue field.
* §7 `StandardEtale`: the algebras `A[t]/(F)`: I.7.1–I.7.4, I.7.5 (for `B` local, and for an
  infinite residue field, using `PrimitiveElement`), I.7.6–I.7.7 in Zariski-local form;
  `LocalStructure`: I.7.8 for schemes.
* §8 `Infinitesimal`: I.8.1 (affine), I.8.2 (local base), I.8.3 (affine, nilpotent ideal, and
  full faithfulness in general), I.8.4 for an adic noetherian ring (`Spf A`);
  `EtaleSiteInvariance`: I.8.3 in general and the invariance statement of I.11 (from IX).
* §9 `Permanence`: dimension, regularity, reducedness and normality under étale maps
  (I.9.1–I.9.3, I.9.5, I.9.10), the trace formulas I.9.6–I.9.9 over a field, and I.9.12;
  `DominantUnramified`: I.9.11 (a dominant unramified morphism of finite type from a
  connected scheme to a normal one is étale, and its source is normal and irreducible);
  `TraceFormulas`: I.9.6–I.9.8 over an arbitrary base ring.
* §10 `NormalCoverings`: normalization and étale coverings (I.10.1–I.10.6, affine forms),
  geometric number of points; `GeometricPoints` (with `SGA.Foundations.Limits`, EGA IV
  15.5.1, and the strict henselization): I.10.7–I.10.12;
  `SeparableDegreeFibre`: I.10.12 for an infinite residue field, by SGA's argument.
* §11 `Unibranch`: geometrically unibranch local rings; a connected unramified scheme of
  finite type dominating a geometrically unibranch one is étale and irreducible (EGA IV 18.10:
  étale local rings over a geometrically unibranch local domain are domains); example b), a
  complete local domain which is not geometrically unibranch has a finite étale local algebra
  which is not a domain.
* `Completion`: the map `Â → B̂` of completions induced by a local homomorphism;
  `CompletionCriteria`: the criteria through completions I.2.1 (iii), I.3.7, I.4.2, I.4.4, I.9.4.

Numbering follows Grothendieck (`I.3.1`, `I.5.1`, …). See `docs/formalization.md`.

The exposé works throughout with locally noetherian schemes (after no. I.2).
Mathlib's étale morphisms are locally of finite presentation; this agrees
with SGA's finite-type definition on a locally noetherian base
(`etale_of_flat_unramified_locallyNoetherian`).
-/
