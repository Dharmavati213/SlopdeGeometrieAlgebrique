/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.AffineHomColimit
import SGA.SGA2.ExposeVI.ModuleSupportedExt
import SGA.SGA2.ExposeVI.ModuleHomInjectiveFlasque
import SGA.SGA2.ExposeVI.ModuleSheafExtLocal
import SGA.SGA2.ExposeVI.Excision
import SGA.SGA2.ExposeVI.SupportObjectHom
import SGA.SGA2.ExposeVI.SpectralFunctors
import SGA.SGA2.ExposeVI.SupportExactSequences
import SGA.SGA2.ExposeVI.AffineExtComparison
import SGA.SGA2.ExposeVI.Examples

/-!
# SGA 2, Exposé VI: Ext with support

The affine degree-zero algebra in VI.2.3 is proved:
the actual direct system `Hom_R(M / IⁿM, N)` has colimit the submodule
of `Hom_R(M,N)` killed by powers of `I`. The comparison retains the original
quotient-precomposition maps, and holds for arbitrary modules over any
commutative ring.

The actual sheaf of local module-linear morphisms is constructed over arbitrary
ringed spaces, with its additive structure, proved gluing, original maps in
both variables, and left exactness. Its global sections are the original
module-sheaf Hom. The actual supported-section submodules give a module sheaf,
naturally the original supported additive kernel after forgetting scalars.
For closed support, VI.1.4.3 is proved with the original factorization maps,
natural in both variables and with a sectionwise-compatible sheaf form.

VI.1.1's supported Ext groups and underlying additive sheaves are right-derived
in the module-sheaf category, for closed and arbitrary locally closed support.
Degree zero and positive-degree vanishing on injective module sheaves are
proved. The closed supported-Hom comparison is natural after derivation.

VI.1.5's flasqueness assertion is proved: local linear maps into an injective
module sheaf extend globally through the open subpresheaf of the source.
The genuine Hom sheaf is therefore acyclic for closed and locally closed
supported sections, without assuming additive-sheaf injectivity.

VI.1.2 is proved: sheaf Ext is sheafification of local module Ext.
VI.1.3 is excision of supported cohomology of the Hom sheaf. VI.1.4.1 and
VI.1.4.3 are the closed Hom representation and supported factorization.
VI.1.8–VI.1.9 are nested-support sequences of the Hom sheaf. VI.2.3 compares
Ext-colimits with supported cohomology for the structure sheaf on a
noetherian affine, and in degree zero for arbitrary modules. The tensor
form VI.1.4.2, the three spectral functors of VI.1.6, and general VI.2.3
remain open.
-/
