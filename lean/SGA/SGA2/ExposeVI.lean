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
import SGA.SGA2.ExposeVI.ModuleSupportIndependence
import SGA.SGA2.ExposeVI.LocallyClosedTensorSupportHom
import SGA.SGA2.ExposeVI.ModuleSupportedSheafInjective
import SGA.SGA2.ExposeVI.TensorSupportExtNaturality
import SGA.SGA2.ExposeVI.ModuleOpenRestrictionLocallyClosed
import SGA.SGA2.ExposeVI.ModuleOpenRestrictionComplement
import SGA.SGA2.ExposeVI.ModuleRelativeExtSequence
import SGA.SGA2.ExposeVI.ModuleRelativeExtCompatibility
import SGA.SGA2.ExposeVI.AffineInternalHom
import SGA.SGA2.ExposeVI.AffineInternalHomNaturality
import SGA.SGA2.ExposeVI.CoherentInternalHom
import SGA.SGA2.ExposeVI.ModuleSheafExtLinear
import SGA.SGA2.ExposeVI.ModuleLocallyClosedSheafExtLinear
import SGA.SGA2.ExposeVI.ModuleLocallyClosedSupportedSheafInjective
import SGA.SGA2.ExposeVI.ModuleLocallyClosedSupportedHom
import SGA.SGA2.ExposeVI.AffineExtComparison
import SGA.SGA2.ExposeVI.TensorSupportObjectSequence
import SGA.SGA2.ExposeVI.QuasiCoherentSupportedModules
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
Ordinary and arbitrarily locally supported sheaf Ext have genuine module-valued
derived functors, and global supported Ext has its global-ring module structure.
Exact forgetting of scalars recovers the unchanged additive versions.

VI.1.5's flasqueness assertion is proved: local linear maps into an injective
module sheaf extend globally through the open subpresheaf of the source.
The genuine Hom sheaf is therefore acyclic for closed and locally closed
supported sections, without assuming additive-sheaf injectivity.

Actual open and nested-open module restriction are exact and preserve
injectives. VI.1.2 identifies the local Ext values with derived supported
Hom in the actual restricted module categories, with the original sheaf Ext
as their sheafification. VI.1.3 gives coefficient-natural excision for
arbitrary locally closed supports in every degree. Higher nested-restriction
and connecting-map compatibility of these comparisons remain open.

Over a commutative structure sheaf, the actual support module and sheafified
tensor product prove VI.1.4.1–2 for every locally closed support. The
comparison with ordinary Ext from that tensor source is natural in both
variables in every degree. The actual closed module-support functor preserves
injectives through a proved mono-preserving quotient left adjoint. The
locally closed module-support functor preserves injectives through its actual
restriction/direct-image factorization, and VI.1.4.3 holds for that functor.

VI.1.6.1–3 have actual spectral functors, E₂ identifications, original Ext
abutments and finite convergence for arbitrary locally closed support, with
coefficient naturality of E₂ and abutment for VI.1.6.3. VI.1.7 gives the
actual module support-object short exact sequence and its tensor version,
with the original source maps. VI.1.8 gives actual long exact sequences of
supported Ext groups and supported sheaf Ext, natural in both variables,
with the original degree-zero maps. VI.1.9 has a genuine exact sequence with
ordinary Ext endpoints; its restriction arrow is the standard Ext map of
the exact open-restriction functor in every degree.

The actual affine internal Hom is the associated sheaf of module Hom for
finitely presented sources over arbitrary commutative rings. It commutes with
open restriction and is quasi-coherent for coherent source and quasi-coherent
target on locally noetherian schemes. Degree-zero closed-supported Hom and
sheaf Ext⁰ are quasi-coherent for coherent source and quasi-coherent target
on locally noetherian schemes.

The remaining higher-map comparisons, higher supported sheaf Ext
quasi-coherence, and general VI.2.3 remain open. VI.2.3 currently includes
the affine degree-zero quotient-Hom colimit and the structure-sheaf
local-cohomology comparison.
-/
