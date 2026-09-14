/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.RegularLocalExtVanishing
import SGA.SGA2.ExposeIV.SupportedFunctorExactness

/-!
# Exactness of the actual top Ext functor

This uses genuine derived-category Ext with its original precomposition
maps and connecting sequences. Off-degree vanishing over an actual regular
local ring makes the top Ext functor exact on all finite supported modules.
The residue value, and therefore duality, is not assumed here.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

local instance regularTopExtResidueField : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _

/-- The actual derived-category Ext functor of IV.5.4, on its original
finite closed-point-supported source and with its original abelian groups. -/
def regularLocalTopExtFunctor (n : ℕ) :
    (SupportedFGModuleCat (maximalIdeal R))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (supportedFiniteToModule (maximalIdeal R)).op ⋙
    (Abelian.extFunctor (C := ModuleCat.{u} R) n).flip.obj (ModuleCat.of R R)

instance (n : ℕ) : (regularLocalTopExtFunctor (R := R) n).Additive where
  map_add {X Y f g} := by
    ext x
    change (Abelian.Ext.mk₀ (f.unop.hom.hom + g.unop.hom.hom)).comp x (zero_add n) = _
    rw [Abelian.Ext.mk₀_add, Abelian.Ext.add_comp]
    rfl

/-- The functor's canonical source-induced scalar action is the original
linear Ext action, not just an abstract action on the same additive group. -/
def regularLocalTopExtValueIso (n : ℕ) (M : SupportedFGModuleCat (maximalIdeal R)) :
    supportedFunctorValue (maximalIdeal R) (regularLocalTopExtFunctor (R := R) n) M ≅
      ModuleCat.of R (Abelian.Ext M.obj.obj (ModuleCat.of R R) n) :=
  LinearEquiv.toModuleIso
    (X₁ := supportedFunctorValue (maximalIdeal R) (regularLocalTopExtFunctor (R := R) n) M)
    (X₂ := ModuleCat.of R (Abelian.Ext M.obj.obj (ModuleCat.of R R) n))
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change (Abelian.Ext.mk₀ (r • 𝟙 M.obj.obj)).comp x (zero_add n) =
          r • (show Abelian.Ext M.obj.obj (ModuleCat.of R R) n from x)
        simp only [Abelian.Ext.mk₀_smul, Abelian.Ext.smul_comp, Abelian.Ext.mk₀_id_comp] }

@[simp] theorem regularLocalTopExtValueIso_hom_apply (n : ℕ)
    (M : SupportedFGModuleCat (maximalIdeal R))
    (x : supportedFunctorValue (maximalIdeal R) (regularLocalTopExtFunctor (R := R) n) M) :
    (regularLocalTopExtValueIso n M).hom x = x := rfl

/-- Actual top Ext carries every finite-length short exact sequence to
the original contravariant short exact sequence. -/
theorem regularLocal_topExt_shortExact (n : ℕ) (hdim : ringKrullDim R = n)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (h₁ : IsFiniteLength R S.X₁) (h₃ : IsFiniteLength R S.X₃) :
    (S.op.map ((Abelian.extFunctor (C := ModuleCat.{u} R) n).flip.obj
      (ModuleCat.of R R))).ShortExact := by
  let Y := ModuleCat.of R R
  refine ShortComplex.ShortExact.mk'
    (Abelian.Ext.contravariant_sequence_exact₂' hS Y n) ?_ ?_
  · apply (AddCommGrpCat.mono_iff_injective _).mpr
    cases n with
    | zero =>
      have := hS.epi_g
      exact Abelian.Ext.precomp_mk₀_injective_of_epi Y S.g
    | succ k =>
      apply (injective_iff_map_eq_zero
        ((Abelian.Ext.mk₀ S.g).precomp Y (zero_add (k + 1)))).mpr
      intro x hx
      have := regularLocal_ext_ring_subsingleton_of_finiteLength_of_lt
        (k + 1) hdim S.X₁ h₁ k (Nat.lt_succ_self k)
      obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y x hx
        (show 1 + k = k + 1 by omega)
      rw [Subsingleton.elim y 0, Abelian.Ext.comp_zero] at hy
      exact hy.symm
  · apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro x
    have := regularLocal_ext_subsingleton_of_finiteLength_of_gt
      n hdim S.X₃ Y h₃ (n + 1) (Nat.lt_succ_self n)
    exact Abelian.Ext.contravariant_sequence_exact₁ hS Y x
      (show 1 + n = n + 1 by omega) (Subsingleton.elim _ _)

/-- **IV.5.4, exactness:** the actual top Ext functor is exact; no residue
value or duality assertion is included as a hypothesis. -/
theorem regularLocalTopExtFunctor_exact (n : ℕ) (hdim : ringKrullDim R = n) :
    SupportedFunctorExact (maximalIdeal R) (regularLocalTopExtFunctor (R := R) n) := by
  intro S hS
  exact regularLocal_topExt_shortExact n hdim (S.map (supportedFiniteToModule (maximalIdeal R)))
    (hS.map_of_exact (supportedFiniteToModule (maximalIdeal R)))
    (supportedFinite_isFiniteLength (maximalIdeal R) S.X₁)
    (supportedFinite_isFiniteLength (maximalIdeal R) S.X₃)

theorem regularLocalTopExtFunctor_preservesHomology (n : ℕ)
    (hdim : ringKrullDim R = n) : (regularLocalTopExtFunctor (R := R) n).PreservesHomology :=
  (supportedFunctorExact_iff_preservesHomology _ _).mp (regularLocalTopExtFunctor_exact n hdim)

theorem regularLocalTopExtFunctor_preservesFiniteLimits (n : ℕ)
    (hdim : ringKrullDim R = n) : PreservesFiniteLimits (regularLocalTopExtFunctor (R := R) n) := by
  have := regularLocalTopExtFunctor_preservesHomology n hdim
  exact (regularLocalTopExtFunctor (R := R) n).preservesFiniteLimits_of_preservesHomology

/-- The actual original quotient-Ext colimit, with its canonical scalar action. -/
abbrev regularLocalTopExtModule (n : ℕ) : ModuleCat.{u} R :=
  supportedFunctorColimit (maximalIdeal R) (regularLocalTopExtFunctor (R := R) n)

/-- Its closed-point support follows from the original colimit construction. -/
theorem regularLocalTopExtModule_supported (n : ℕ) :
    supportedModuleProperty (maximalIdeal R) (regularLocalTopExtModule (R := R) n) :=
  supportedFunctorColimit_support _ _

/-- The actual top quotient-Ext colimit is injective among all modules, by
the already proved IV.2.1 and actual top-Ext exactness. -/
theorem regularLocalTopExtModule_injective (n : ℕ) (hdim : ringKrullDim R = n) :
    Injective (regularLocalTopExtModule (R := R) n) := by
  have := regularLocalTopExtFunctor_preservesFiniteLimits n hdim
  exact (supportedFunctorExact_iff_injective_colimit _ _).mp
    (regularLocalTopExtFunctor_exact n hdim)

/-- Canonical evaluation represents the actual top Ext functor by its
actual quotient-Ext colimit, not by an unspecified injective coefficient. -/
def regularLocalTopExtRepresentationIso (n : ℕ) (hdim : ringKrullDim R = n) :
    regularLocalTopExtFunctor (R := R) n ≅
      supportedModuleHomFunctor (maximalIdeal R) (regularLocalTopExtModule (R := R) n) ⋙
        forget₂ (ModuleCat R) AddCommGrpCat := by
  have := regularLocalTopExtFunctor_preservesFiniteLimits n hdim
  exact additiveSupportedFunctorRepresentationIso _ _

end SGA.SGA2.ExposeIV
