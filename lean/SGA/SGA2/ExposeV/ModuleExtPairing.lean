/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.ModuleExtDerivedNaturality
import SGA.SGA2.ExposeIV.ModuleExtDerivedCoefficientNaturality

/-!
# Yoneda pairing on the original module-valued Ext objects

The canonical linear comparison with derived-category Ext transports its
actual Yoneda composition to the module-valued Ext functors defining local
cohomology. Naturality uses the already proved comparison of original maps
in both variables; no independently chosen Ext values or naturality
hypotheses are introduced.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The original module-valued Ext object. -/
abbrev moduleExtValue (N M : ModuleCat.{u} R) (i : ℕ) : ModuleCat.{u} R :=
  (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).obj M)

/-- The original Yoneda product, transported through the canonical linear
comparison of the two actual Ext constructions. -/
def moduleExtPairing (N M P : ModuleCat.{u} R) (i j n : ℕ) (h : i + j = n) :
    moduleExtValue N M i →ₗ[R]
      (moduleExtValue M P j →ₗ[R] moduleExtValue N P n) where
  toFun x :=
    { toFun y := (moduleExtLinearEquivAbelianExt N P n).symm
        ((moduleExtLinearEquivAbelianExt N M i x).comp
          (moduleExtLinearEquivAbelianExt M P j y) h)
      map_add' y z := by simp [Abelian.Ext.comp_add]
      map_smul' r y := by simp [Abelian.Ext.comp_smul] }
  map_add' x y := by ext z; simp [Abelian.Ext.add_comp]
  map_smul' r x := by ext z; simp [Abelian.Ext.smul_comp]

@[simp]
theorem moduleExtPairing_apply (N M P : ModuleCat.{u} R) (i j n : ℕ) (h : i + j = n)
    (x : moduleExtValue N M i) (y : moduleExtValue M P j) :
    moduleExtPairing N M P i j n h x y =
      (moduleExtLinearEquivAbelianExt N P n).symm
        ((moduleExtLinearEquivAbelianExt N M i x).comp
          (moduleExtLinearEquivAbelianExt M P j y) h) := rfl

/-- First-variable naturality retains the original contravariant Ext maps. -/
theorem moduleExtPairing_naturality_first {N' N : ModuleCat.{u} R}
    (q : N' ⟶ N) (M P : ModuleCat.{u} R) (i j n : ℕ) (h : i + j = n)
    (x : moduleExtValue N M i) (y : moduleExtValue M P j) :
    moduleExtPairing N' M P i j n h
        (((_root_.Ext R (ModuleCat.{u} R) i).map q.op).app M x) y =
      ((_root_.Ext R (ModuleCat.{u} R) n).map q.op).app P
        (moduleExtPairing N M P i j n h x y) := by
  apply (moduleExtLinearEquivAbelianExt N' P n).injective
  simp only [moduleExtPairing_apply, LinearEquiv.apply_symm_apply,
    moduleExtLinearEquivAbelianExt_naturality_first]
  exact Abelian.Ext.comp_assoc _ _ _ (zero_add i) h (by omega)

/-- Middle-variable naturality compares the original coefficient map with
the original contravariant map on the other factor. -/
theorem moduleExtPairing_naturality_middle (N : ModuleCat.{u} R)
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') (P : ModuleCat.{u} R)
    (i j n : ℕ) (h : i + j = n)
    (x : moduleExtValue N M i) (y : moduleExtValue M' P j) :
    moduleExtPairing N M' P i j n h
        (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).map f x) y =
      moduleExtPairing N M P i j n h x
        (((_root_.Ext R (ModuleCat.{u} R) j).map f.op).app P y) := by
  apply (moduleExtLinearEquivAbelianExt N P n).injective
  simp only [moduleExtPairing_apply, LinearEquiv.apply_symm_apply,
    moduleExtLinearEquivAbelianExt_naturality_coefficient,
    moduleExtLinearEquivAbelianExt_naturality_first]
  exact Abelian.Ext.comp_assoc _ _ _ (add_zero i) (zero_add j) h

/-- Final-variable naturality retains the original covariant Ext maps. -/
theorem moduleExtPairing_naturality_last (N M : ModuleCat.{u} R)
    {P P' : ModuleCat.{u} R} (g : P ⟶ P') (i j n : ℕ) (h : i + j = n)
    (x : moduleExtValue N M i) (y : moduleExtValue M P j) :
    moduleExtPairing N M P' i j n h x
        (((_root_.Ext R (ModuleCat.{u} R) j).obj (op M)).map g y) =
      ((_root_.Ext R (ModuleCat.{u} R) n).obj (op N)).map g
        (moduleExtPairing N M P i j n h x y) := by
  apply (moduleExtLinearEquivAbelianExt N P' n).injective
  simp only [moduleExtPairing_apply, LinearEquiv.apply_symm_apply,
    moduleExtLinearEquivAbelianExt_naturality_coefficient]
  exact (Abelian.Ext.comp_assoc _ _ _ h (add_zero j) (by omega)).symm

end SGA.SGA2.ExposeV
