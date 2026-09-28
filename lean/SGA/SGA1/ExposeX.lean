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

/-!
# SGA 1, Exposé X — Theory of specialization of the fundamental group

English translation: `translation/SGA1/ExposeX/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

The geometric inputs of the exposé that are still missing are recorded as `…Statement`
propositions: X.2.1 = IX.1.10 (Grothendieck's existence theorem), X.2.4,
X.2.9 (via the transcendental X.2.6) and X.3.8. What is proved:

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
* `Semicontinuity`: X.2.1 when `X` is finite over `Y`, statements X.2.1, X.2.4 and X.2.9 with
  their consequences;
* `Henselian`: the isomorphism `π₁(k) ≅ π₁(Y)` used before X.2.2 (`Y` the spectrum of a
  henselian, e.g. complete, local ring), from `SGA.Foundations.HenselianFiniteEtale`;
* `Purity`, `PurityFundamentalGroup`, `PurityTheorem`, `PurityDenseOpen`, `PurityBirational`
  (with `SGA.Foundations.CommAlg`, Zariski–Nagata purity in every dimension): X.3.1–X.3.4;
* `TameInertia`: tame inertia groups are cyclic and Abhyankar's lemma X.3.6;
* `TameSpecialization`: statement X.3.8 and X.3.9 from it;
* `SteinEtale` (with `SGA.Foundations.Cohomology`, EGA III 7.8.10): X.1.2, hence X.1.3, the
  homotopy exact sequence X.1.4, and X.1.7 (rational base point, `X` reduced);
* `BaseChangeAlgClosed` (with `SGA.Foundations.Limits`): X.1.8;
* `ConstantFamily`: X.1.9, from X.1.7, X.1.4 and X.1.8 by an argument with classes of paths;
* `SpecializationGeometric`, `SpecializationSurjective`: X.2.2–X.2.4 (for `X` projective over
  `Y`, and for `X` proper from IX.1.10), X.1.4 at algebraically closed geometric points.
-/
