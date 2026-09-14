/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.AffineHomColimit
import SGA.SGA2.ExposeVI.ModuleSupportedExt
import SGA.SGA2.ExposeVI.ModuleHomInjectiveFlasque

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

The internal Hom and derived sheaves still need their structure-ring module
actions. VI.1.2's local Ext comparison, excision, the locally closed extension
of VI.1.4.3, tensor/support-object comparisons, the three spectral sequences,
support exact sequences, quasi-coherence, and VI.2.3's higher-degree/sheaf
comparison remain open.
-/
