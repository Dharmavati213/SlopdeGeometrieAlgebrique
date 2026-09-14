/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.ExtPairing
import SGA.SGA2.ExposeV.ModuleExtPairing

/-!
# Yoneda boundaries on the original module-valued Ext objects

The canonical linear Ext comparison transports the actual Yoneda boundaries
to the unchanged original module-valued Ext objects. Their maps in the
other variables are the original Ext maps. The signed identification of the
covariant boundary with the separately constructed Hom-complex boundary is
proved in `ModuleExtCoefficientBoundaryComparison`. Actual contravariant Hom
boundaries are compared to the derived connecting arrow in the companion
`HomComplexContravariantBoundary` and `SourceHomContravariantBoundary` files;
`InjectiveHomModuleExtBoundary` specializes both comparisons to the original
module-valued boundaries defined here, using the fixed augmentation equivalences
of a supplied augmented short exact resolution sequence. Existence of that
resolution sequence is separate work.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The covariant Yoneda boundary on original Ext objects. -/
def moduleExtYonedaCovariantBoundary (N : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    moduleExtValue N S.X₃ i ⟶ moduleExtValue N S.X₁ (i + 1) :=
  (moduleExtLinearIsoAbelianExt N S.X₃ i).hom ≫
    ModuleCat.ofHom (extCovariantBoundary N S hS i (i + 1) rfl) ≫
      (moduleExtLinearIsoAbelianExt N S.X₁ (i + 1)).inv

/-- The contravariant Yoneda boundary on original Ext objects. -/
def moduleExtYonedaContravariantBoundary (P : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (j : ℕ) :
    moduleExtValue S.X₁ P j ⟶ moduleExtValue S.X₃ P (j + 1) :=
  (moduleExtLinearIsoAbelianExt S.X₁ P j).hom ≫
    ModuleCat.ofHom (extContravariantBoundary P S hS j (j + 1) (Nat.add_comm 1 j)) ≫
      (moduleExtLinearIsoAbelianExt S.X₃ P (j + 1)).inv

@[simp]
theorem moduleExtYonedaCovariantBoundary_compare (N : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ)
    (x : moduleExtValue N S.X₃ i) :
    moduleExtLinearEquivAbelianExt N S.X₁ (i + 1)
        (moduleExtYonedaCovariantBoundary N S hS i x) =
      (moduleExtLinearEquivAbelianExt N S.X₃ i x).comp hS.extClass rfl := by
  change (moduleExtLinearEquivAbelianExt N S.X₁ (i + 1))
    ((moduleExtLinearEquivAbelianExt N S.X₁ (i + 1)).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

@[simp]
theorem moduleExtYonedaContravariantBoundary_compare (P : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (j : ℕ)
    (x : moduleExtValue S.X₁ P j) :
    moduleExtLinearEquivAbelianExt S.X₃ P (j + 1)
        (moduleExtYonedaContravariantBoundary P S hS j x) =
      hS.extClass.comp (moduleExtLinearEquivAbelianExt S.X₁ P j x) (Nat.add_comm 1 j) := by
  change (moduleExtLinearEquivAbelianExt S.X₃ P (j + 1))
    ((moduleExtLinearEquivAbelianExt S.X₃ P (j + 1)).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- The covariant boundary commutes with the original first-variable maps. -/
@[reassoc]
theorem moduleExtYonedaCovariantBoundary_naturality {N N' : ModuleCat.{u} R}
    (f : N' ⟶ N) (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    ((_root_.Ext R (ModuleCat.{u} R) i).map f.op).app S.X₃ ≫
        moduleExtYonedaCovariantBoundary N' S hS i =
      moduleExtYonedaCovariantBoundary N S hS i ≫
        ((_root_.Ext R (ModuleCat.{u} R) (i + 1)).map f.op).app S.X₁ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (moduleExtLinearEquivAbelianExt N' S.X₁ (i + 1)).injective
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    moduleExtYonedaCovariantBoundary_compare, moduleExtLinearEquivAbelianExt_naturality_first]
  exact Abelian.Ext.comp_assoc _ _ _ (zero_add i) rfl (by omega)

/-- Yoneda associativity gives the boundary identity for the unchanged
canonical pairing. -/
theorem moduleExtPairing_yoneda_connecting (N P : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (i j n : ℕ) (hleft : (i + 1) + j = n) (hright : i + (j + 1) = n)
    (x : moduleExtValue N S.X₃ i) (y : moduleExtValue S.X₁ P j) :
    moduleExtPairing N S.X₁ P (i + 1) j n hleft
        (moduleExtYonedaCovariantBoundary N S hS i x) y =
      moduleExtPairing N S.X₃ P i (j + 1) n hright x
        (moduleExtYonedaContravariantBoundary P S hS j y) := by
  apply (moduleExtLinearEquivAbelianExt N P n).injective
  simp only [moduleExtPairing_apply, LinearEquiv.apply_symm_apply,
    moduleExtYonedaCovariantBoundary_compare, moduleExtYonedaContravariantBoundary_compare]
  exact Abelian.Ext.comp_assoc _ _ _ rfl (Nat.add_comm 1 j) (by omega)

end SGA.SGA2.ExposeV
