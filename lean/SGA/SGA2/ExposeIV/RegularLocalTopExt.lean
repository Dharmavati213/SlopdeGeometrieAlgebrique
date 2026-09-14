/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.KoszulTopCohomology
import SGA.SGA2.ExposeIII.RegularLocalRegularSequence
import SGA.SGA2.ExposeIV.ModuleExtDerivedComparison
import SGA.SGA2.ExposeIV.ModuleExtDerivedLinear

/-!
# The top residue Ext value over an actual regular local ring

The original Koszul augmentation is a genuine resolution, and its original
top Hom cohomology is the coefficient quotient. Applying these constructions
to the proved regular parameters computes the top residue Ext value from
the actual regular-local-ring hypothesis. The resulting isomorphism depends
on the chosen ordered parameters; no choice-independent orientation is
claimed. Both the original module-valued and derived-category Ext values
are compared with the actual residue field.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing RingTheory.Sequence
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Top Ext out of a regular-sequence quotient is the actual coefficient
quotient, computed using the original finite-stage Ext-to-Koszul map. -/
def regularSequence_topModuleExtIsoQuotient [IsNoetherianRing R] [IsLocalRing R]
    (fs : List R) (hreg : IsRegular R fs) (E : ModuleCat.{u} R) :
    (((_root_.Ext R (ModuleCat.{u} R) fs.length).obj
      (op (ModuleCat.of R (R ⧸ koszulIdeal fs)))).obj E) ≅
      ModuleCat.of R (E ⧸ koszulIdeal fs • (⊤ : Submodule R E)) :=
  (koszulExtComparisonIsoOfIsRegular fs hreg fs.length).app E ≪≫
    koszulTopCohomologyIsoQuotient fs E

/-- With ring coefficients the actual top quotient Ext is the quotient
ring with its original `R`-module structure. -/
def regularSequence_topModuleExtRingIsoQuotient [IsNoetherianRing R] [IsLocalRing R]
    (fs : List R) (hreg : IsRegular R fs) :
    (((_root_.Ext R (ModuleCat.{u} R) fs.length).obj
      (op (ModuleCat.of R (R ⧸ koszulIdeal fs)))).obj (ModuleCat.of R R)) ≅
      ModuleCat.of R (R ⧸ koszulIdeal fs) :=
  (koszulExtComparisonIsoOfIsRegular fs hreg fs.length).app (ModuleCat.of R R) ≪≫
    koszulTopCohomologyRingIsoQuotient fs

/-- **IV.5.3–5.4, the residue test:** for an actual regular local ring of
dimension `n`, the original module-valued `Extⁿ_R(k,R)` is the residue field
as an actual `R`-module. The parameters are constructed, not assumed. -/
def regularLocal_topResidueModuleExtIso [IsRegularLocalRing R] (n : ℕ)
    (hdim : ringKrullDim R = n) :
    (((_root_.Ext R (ModuleCat.{u} R) n).obj
      (op (ModuleCat.of R (ResidueField R)))).obj (ModuleCat.of R R)) ≅
      ModuleCat.of R (ResidueField R) := by
  let fs := Classical.choose (regularLocal_exists_regular_parameters n hdim)
  have hfs := Classical.choose_spec (regularLocal_exists_regular_parameters n hdim)
  have hlen : fs.length = n := hfs.1
  have hs : koszulIdeal fs = maximalIdeal R := hfs.2.1
  have hreg : IsRegular R fs := hfs.2.2
  let e : ModuleCat.of R (R ⧸ koszulIdeal fs) ≅ ModuleCat.of R (ResidueField R) :=
    (Ideal.quotientEquivAlgOfEq R hs).toLinearEquiv.toModuleIso
  refine ((_root_.Ext R (ModuleCat.{u} R) n).mapIso e.op).app (ModuleCat.of R R) ≪≫ ?_ ≪≫ e
  simpa only [hlen] using regularSequence_topModuleExtRingIsoQuotient fs hreg

/-- The same genuine top residue value for derived-category Ext, using
the actual shared-projective-resolution comparison of the two Ext models. -/
def regularLocal_topResidueExtAddEquiv [IsRegularLocalRing R] (n : ℕ)
    (hdim : ringKrullDim R = n) :
    Abelian.Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) n ≃+
      ResidueField R :=
  (moduleExtAddEquivAbelianExt (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) n).symm.trans
    (regularLocal_topResidueModuleExtIso n hdim).toLinearEquiv.toAddEquiv

/-- The top residue value as an isomorphism in abelian groups, matching
the original group-valued Ext functor used for IV.5.4. -/
def regularLocal_topResidueExtIso [IsRegularLocalRing R] (n : ℕ)
    (hdim : ringKrullDim R = n) :
    AddCommGrpCat.of (Abelian.Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) n) ≅
      AddCommGrpCat.of (ResidueField R) :=
  AddEquiv.toAddCommGrpIso (regularLocal_topResidueExtAddEquiv n hdim)

/-- The top residue comparison is linear for the canonical derived Ext
action, not just an additive equivalence of its underlying group. -/
def regularLocal_topResidueExtLinearEquiv [IsRegularLocalRing R] (n : ℕ)
    (hdim : ringKrullDim R = n) :
    Abelian.Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) n ≃ₗ[R]
      ResidueField R :=
  (moduleExtLinearEquivAbelianExt (ModuleCat.of R (ResidueField R))
    (ModuleCat.of R R) n).symm.trans
      (regularLocal_topResidueModuleExtIso n hdim).toLinearEquiv

/-- The linear upgrade has exactly the previously constructed underlying
additive map and the same chosen parameter orientation. -/
theorem regularLocal_topResidueExtLinearEquiv_toAddEquiv [IsRegularLocalRing R] (n : ℕ)
    (hdim : ringKrullDim R = n) :
    (regularLocal_topResidueExtLinearEquiv n hdim).toAddEquiv =
      regularLocal_topResidueExtAddEquiv n hdim := by
  change (moduleExtLinearEquivAbelianExt (ModuleCat.of R (ResidueField R))
    (ModuleCat.of R R) n).toAddEquiv.symm.trans
      (regularLocal_topResidueModuleExtIso n hdim).toLinearEquiv.toAddEquiv = _
  rw [moduleExtLinearEquivAbelianExt_toAddEquiv]
  rfl

/-- The genuine residue test as an isomorphism of original `R`-modules,
with canonical derived Ext scalar action. -/
def regularLocal_topResidueExtModuleIso [IsRegularLocalRing R] (n : ℕ)
    (hdim : ringKrullDim R = n) :
    ModuleCat.of R (Abelian.Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) n) ≅
      ModuleCat.of R (ResidueField R) :=
  (regularLocal_topResidueExtLinearEquiv n hdim).toModuleIso

end SGA.SGA2.ExposeIV
