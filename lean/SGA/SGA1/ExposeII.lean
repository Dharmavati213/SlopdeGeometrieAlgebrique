/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeII.Generalities
import SGA.SGA1.ExposeII.QuasiFinite
import SGA.SGA1.ExposeII.RelativeDimension
import SGA.SGA1.ExposeII.Criteria
import SGA.SGA1.ExposeII.FibrewiseCriterion
import SGA.SGA1.ExposeII.Permanence
import SGA.SGA1.ExposeII.PermanenceSmooth
import SGA.SGA1.ExposeII.Depth
import SGA.SGA1.ExposeII.Differentials
import SGA.SGA1.ExposeII.SchemeDifferentials
import SGA.SGA1.ExposeII.SheafDifferentials
import SGA.SGA1.ExposeII.Jacobian
import SGA.SGA1.ExposeII.SmoothDescent
import SGA.SGA1.ExposeII.Coordinates
import SGA.SGA1.ExposeII.RegularImmersion
import SGA.SGA1.ExposeII.RegularSequence
import SGA.SGA1.ExposeII.RegularSystemFiltration
import SGA.SGA1.ExposeII.SmoothnessAux
import SGA.SGA1.ExposeII.RegularImmersionSmooth
import SGA.SGA1.ExposeII.DifferentiallySmooth
import SGA.SGA1.ExposeII.PrincipalParts
import SGA.SGA1.ExposeII.Field
import SGA.SGA1.ExposeII.FieldEtale
import SGA.SGA1.ExposeII.FieldSmooth
import SGA.SGA1.ExposeII.Equidimensional
import SGA.SGA1.ExposeII.FiberDifferentials
import SGA.SGA1.ExposeII.EquidimensionalScheme
import SGA.SGA1.ExposeII.FibreMultiplicity

/-!
# SGA 1, Exposé II — Smooth morphisms: generalities, differential properties

English translation: `translation/SGA1/ExposeII/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

SGA defines `f` smooth at `x` when a neighbourhood of `x` is étale over an affine space
`Y[t₁,…,tₙ]`. Mathlib's `AlgebraicGeometry.Smooth` (formal smoothness plus finite presentation)
is shown to agree with it (`smooth_iff_forall_locallyEtaleOverAffineSpaceAt`). The files follow
the sections of the exposé:

* `Generalities`: §1, the definition II.1.1 and its comparison with mathlib, II.1.1–II.1.5;
* `QuasiFinite`: §1, étale = smooth + quasi-finite (II.1.4);
* `RelativeDimension`: §1, the relative dimension is the dimension of the fibres (II.1.5);
* `Criteria`: §2, smooth ⇔ flat with smooth fibres (II.2.1), base change of smoothness at a
  point;
* `FibrewiseCriterion`: §2, the fibrewise criterion II.2.2 (via the local flatness criterion);
* `Equidimensional`: §2, II.2.3: necessity for schemes, sufficiency in affine form;
* `FiberDifferentials`: `Ω¹` of `X/Y` and of the fibre have the same number of generators;
* `EquidimensionalScheme`: §2, II.2.3 for schemes;
* `FibreMultiplicity`: §2, II.2.6, necessity (components of multiplicity 1);
* `Permanence`: §3, regularity, reducedness and normality under smooth morphisms (II.3.1), global
  forms and flat descent;
* `PermanenceSmooth`: §3, the pointwise statement II.3.1;
* `Depth`: §3, the depth and codepth formulas (3.1)–(3.2) at a smooth point, and the
  Cohen–Macaulay property (via EGA IV 6.3.1, `SGA.Foundations.CommAlg.FlatDepth`);
* `Differentials`: §4, `Ω¹` of smooth morphisms and the differential criteria II.4.1–II.4.8;
* `SchemeDifferentials`: §4, the sheaf `Ω¹_{X/Y}`: (4.2 bis), II.4.1 and II.4.3 (ii) for schemes;
* `SheafDifferentials`: §4, `f^* Ω¹_{Y/S} → Ω¹_{X/S}` on affine opens; II.4.3 (i) and II.4.6 for
  schemes, II.4.4 on affine opens;
* `Jacobian`: §4, the Jacobian criterion II.4.10, II.4.12, II.4.14 and descent II.4.13;
* `SmoothDescent`: §4, II.4.13 at a point (via `H¹(L)` and `Ω¹`) and globally;
* `Coordinates`: §4, étale coordinates adapted to a smooth subscheme II.4.9–II.4.11, and along
  a section (II.4.17 (iv));
* `RegularImmersion`: §4, regular systems of generators and regular immersions II.4.14–II.4.18;
* `RegularSequence`: §4, regular sequences are regular systems of generators, and conversely in
  noetherian local rings (II.4.14);
* `RegularSystemFiltration`: §4, regular systems of generators and the `J`-adic completion
  (II.4.14, II.4.17 (ii) ⇔ (iii));
* `SmoothnessAux`: general lemmas (graded flatness criterion input, flatness of formally smooth
  algebras essentially of finite type) used for the converse of II.4.15;
* `RegularImmersionSmooth`: §4, II.4.15 (ii) ⇒ (i) by the local flatness criterion, II.4.16,
  II.4.17 (i) ⇔ (ii);
* `DifferentiallySmooth`: §4, remarks II.4.18: smooth ⇔ flat and differentially smooth;
* `PrincipalParts`: §4, formula (4.4) of the remarks II.4.18;
* `Field`: §5, smooth schemes over a field are regular, separably generated extensions;
* `FieldEtale`: §5, the criterion II.5.1 for étale coordinates over a field;
* `FieldSmooth`: §5, II.5.5 and its corollaries (smoothness in terms of `Ω¹` and dimension).

The exposé assumes throughout that rings are noetherian and schemes locally noetherian; the
Lean statements use mathlib's finite presentation hypotheses instead and add noetherian
hypotheses only where needed.
-/
