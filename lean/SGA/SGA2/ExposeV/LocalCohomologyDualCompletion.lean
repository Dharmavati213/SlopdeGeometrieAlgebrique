/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.LocalDualityTranspose
import SGA.SGA2.ExposeV.ModuleExtFinite
import SGA.SGA2.ExposeIV.MatlisCompleteDuality

/-!
# V.3, formula (22): dual local cohomology and complementary Ext

Over any regular local ring, the dual of original local cohomology is the
actual completion of complementary Ext. The original transpose becomes
the actual completion map. Over a complete regular local ring, it is an
isomorphism with the original Ext module itself, naturally in finite
coefficient modules. No completeness of a noncomplete ring is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing Functor
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Local duality with the actual categorical Hom target. -/
def regularLocal_localCohomologyHomIso (n : ℕ) (hdim : ringKrullDim R = n)
    (i j : ℕ) (h : i + j = n) (M : ModuleCat.{u} R) [Module.Finite R M] :
    (_root_.localCohomology (maximalIdeal R) i).obj M ≅
      (moduleHomDual ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R))).obj
        (op (moduleExtValue M (ModuleCat.of R R) j)) := by
  have := regularLocal_localDualityMap_isIso n hdim i j h M
  exact asIso (localDualityHomMap (maximalIdeal R) M (ModuleCat.of R R) i j n h)

/-- Without completeness of the base, dual local cohomology is the
original adic completion of complementary Ext. -/
def regularLocal_localCohomologyDualCompletionIso (n : ℕ) (hdim : ringKrullDim R = n)
    (i j : ℕ) (h : i + j = n) (M : ModuleCat.{u} R) [Module.Finite R M] :
    (moduleHomDual ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R))).obj
        (op ((_root_.localCohomology (maximalIdeal R) i).obj M)) ≅
      ModuleCat.of R (AdicCompletion (maximalIdeal R) (moduleExtValue M (ModuleCat.of R R) j)) := by
  let H := (_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R)
  have hH := regularLocal_localCohomology_dualizing n hdim
  have := regularLocal_localDualityMap_isIso n hdim i j h M
  exact (asIso ((moduleHomDual H).map
    (localDualityHomMap (maximalIdeal R) M (ModuleCat.of R R) i j n h).op)).symm ≪≫
      finiteBidualCompletionIso (maximalIdeal R) H (moduleExtValue M (ModuleCat.of R R) j)
        hH.1 hH.2.2

/-- The canonical transpose becomes the original completion map under
the specified comparison, rather than an unspecified isomorphism. -/
@[reassoc]
theorem regularLocal_localCohomologyDualCompletionIso_transpose
    (n : ℕ) (hdim : ringKrullDim R = n) (i j : ℕ) (h : i + j = n)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    localDualityTransposeMap (maximalIdeal R) M (ModuleCat.of R R) i j n h ≫
        (regularLocal_localCohomologyDualCompletionIso n hdim i j h M).hom =
      ModuleCat.ofHom
        (AdicCompletion.of (maximalIdeal R) (moduleExtValue M (ModuleCat.of R R) j)) := by
  have := regularLocal_localDualityMap_isIso n hdim i j h M
  dsimp only [localDualityTransposeMap, regularLocal_localCohomologyDualCompletionIso,
    Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [Category.assoc, IsIso.hom_inv_id_assoc]
  exact finiteBidualCompletionIso_evaluation _ _ _ _ _

variable [IsAdicComplete (maximalIdeal R) R]

/-- **V, formula (22), canonical map:** completeness makes the original transpose
an isomorphism from complementary Ext to dual local cohomology. -/
theorem regularLocal_localDualityTransposeMap_isIso
    (n : ℕ) (hdim : ringKrullDim R = n) (i j : ℕ) (h : i + j = n)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsIso (localDualityTransposeMap (maximalIdeal R) M (ModuleCat.of R R) i j n h) := by
  let H := (_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R)
  have := (regularLocal_localCohomology_dualizing n hdim).finite_moduleBidualEvaluation_isIso
    H (moduleExtValue M (ModuleCat.of R R) j)
  have := regularLocal_localDualityMap_isIso n hdim i j h M
  unfold localDualityTransposeMap
  infer_instance

/-- **V, formula (22).** The dual of local cohomology is the original complementary
Ext module over a complete regular local ring. -/
def regularLocal_localCohomologyDualIsoExt
    (n : ℕ) (hdim : ringKrullDim R = n) (i j : ℕ) (h : i + j = n)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    (moduleHomDual ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R))).obj
        (op ((_root_.localCohomology (maximalIdeal R) i).obj M)) ≅
      moduleExtValue M (ModuleCat.of R R) j := by
  have := regularLocal_localDualityTransposeMap_isIso n hdim i j h M
  exact (asIso (localDualityTransposeMap (maximalIdeal R) M (ModuleCat.of R R) i j n h)).symm

/-- The inverse comparison is literally evaluation of the canonical pairing. -/
@[simp]
theorem regularLocal_localCohomologyDualIsoExt_inv
    (n : ℕ) (hdim : ringKrullDim R = n) (i j : ℕ) (h : i + j = n)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    (regularLocal_localCohomologyDualIsoExt n hdim i j h M).inv =
      localDualityTransposeMap (maximalIdeal R) M (ModuleCat.of R R) i j n h := rfl

/-- The complete-ring comparison is natural on the actual finite-module category. -/
def regularLocal_localDualityTransposeNatIso
    (n : ℕ) (hdim : ringKrullDim R = n) (i j : ℕ) (h : i + j = n) :
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).op ⋙
        (_root_.Ext R (ModuleCat.{u} R) j).flip.obj (ModuleCat.of R R) ≅
      (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).op ⋙
        (_root_.localCohomology (maximalIdeal R) i).op ⋙
          moduleHomDual ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R)) := by
  let α := whiskerLeft (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).op
    (localDualityTransposeNatTrans (maximalIdeal R) (ModuleCat.of R R) i j n h)
  have (M : (FGModuleCat.{u} R)ᵒᵖ) : IsIso (α.app M) :=
    regularLocal_localDualityTransposeMap_isIso n hdim i j h M.unop.obj
  exact NatIso.ofComponents (fun M => asIso (α.app M)) (fun f => α.naturality f)

end SGA.SGA2.ExposeV
