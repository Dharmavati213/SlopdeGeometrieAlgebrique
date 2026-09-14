/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.InjectiveHomCovariantBoundary
import SGA.SGA2.ExposeV.ModuleExtYonedaBoundary

/-! # Chosen injective Hom boundaries on the original module-valued Ext objects

The additive comparisons below compose the previously specified actual
augmentation equivalences with the unchanged canonical linear Ext comparison.
Their boundary identities compare actual Hom connecting maps with the
previously defined module-valued Yoneda maps, not newly defined boundaries.
An augmented short exact sequence of resolutions is supplied explicitly.
-/

noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
open SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {A : Type u} [CommRing A] {X Y : ModuleCat.{u} A}

/-- The original standard double-resolution comparison followed by the
unchanged canonical comparison to module-valued Ext, as additive groups. -/
def injectiveHomologyModuleExtAddEquiv (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (n : ℕ) :
    (HomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ) ≃+
      moduleExtValue X Y n :=
  (injectiveHomologyExtAddEquiv I J n).trans (moduleExtLinearEquivAbelianExt X Y n).toAddEquiv.symm

/-- The same comparison using the existing normalized source augmentation. -/
def sourceInjectiveHomologyModuleExtAddEquiv (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (n : ℕ) :
    (sourceHomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ) ≃+
      moduleExtValue X Y n :=
  (sourceInjectiveHomologyExtAddEquiv I J n).trans
    (moduleExtLinearEquivAbelianExt X Y n).toAddEquiv.symm

@[simp]
theorem injectiveHomologyModuleExtAddEquiv_compare (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (n : ℕ)
    (x : (HomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    moduleExtLinearEquivAbelianExt X Y n (injectiveHomologyModuleExtAddEquiv I J n x) =
      injectiveHomologyExtAddEquiv I J n x :=
  (moduleExtLinearEquivAbelianExt X Y n).apply_symm_apply _

@[simp]
theorem sourceInjectiveHomologyModuleExtAddEquiv_compare (I : InjectiveResolution X)
    (J : InjectiveResolution Y) (n : ℕ)
    (x : (sourceHomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    moduleExtLinearEquivAbelianExt X Y n (sourceInjectiveHomologyModuleExtAddEquiv I J n x) =
      sourceInjectiveHomologyExtAddEquiv I J n x :=
  (moduleExtLinearEquivAbelianExt X Y n).apply_symm_apply _

variable {S : ShortComplex (ModuleCat.{u} A)} (R : InjectiveResolutionSequence S)

/-- The previously defined module-valued contravariant Yoneda boundary is
the signed actual standard Hom boundary under the fixed augmentation comparison. -/
theorem injectiveHomologyModuleExtAddEquiv_contravariantδ (J : InjectiveResolution Y)
    (hS : S.ShortExact) (n : ℕ)
    (x : (HomComplex R.I₁.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    moduleExtYonedaContravariantBoundary Y S hS n
        (injectiveHomologyModuleExtAddEquiv R.I₁ J n x) =
      (n + 1 : ℤ).negOnePow • injectiveHomologyModuleExtAddEquiv R.I₃ J (n + 1)
        (homComplexContravariantδ R.cochainShortComplex R.shortExact
          J.cochainComplex (n : ℤ) x) := by
  apply (moduleExtLinearEquivAbelianExt S.X₃ Y (n + 1)).injective
  simp only [moduleExtYonedaContravariantBoundary_compare, Units.smul_def, map_zsmul,
    injectiveHomologyModuleExtAddEquiv_compare]
  exact injectiveHomologyExtAddEquiv_contravariantδ R J hS n x

/-- The module-valued contravariant comparison for the existing normalized
source augmentation and the actual literal-source Hom boundary. -/
theorem sourceInjectiveHomologyModuleExtAddEquiv_contravariantδ (J : InjectiveResolution Y)
    (hS : S.ShortExact) (n : ℕ)
    (x : (sourceHomComplex R.I₁.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    moduleExtYonedaContravariantBoundary Y S hS n
        (sourceInjectiveHomologyModuleExtAddEquiv R.I₁ J n x) =
      (n + 1 : ℤ).negOnePow • sourceInjectiveHomologyModuleExtAddEquiv R.I₃ J (n + 1)
        (sourceHomContravariantδ R.cochainShortComplex R.shortExact
          J.cochainComplex (n : ℤ) x) := by
  apply (moduleExtLinearEquivAbelianExt S.X₃ Y (n + 1)).injective
  simp only [moduleExtYonedaContravariantBoundary_compare, Units.smul_def, map_zsmul,
    sourceInjectiveHomologyModuleExtAddEquiv_compare]
  exact sourceInjectiveHomologyExtAddEquiv_contravariantδ R J hS n x

/-- The original module-valued coefficient Yoneda boundary equals the actual
standard double-resolution Hom boundary under the fixed comparison. -/
theorem injectiveHomologyModuleExtAddEquiv_covariantδ (I : InjectiveResolution X)
    (hS : S.ShortExact) (n : ℕ)
    (x : (HomComplex I.cochainComplex R.I₃.cochainComplex).homology (n : ℤ)) :
    moduleExtYonedaCovariantBoundary X S hS n (injectiveHomologyModuleExtAddEquiv I R.I₃ n x) =
      injectiveHomologyModuleExtAddEquiv I R.I₁ (n + 1)
        (homComplexCovariantδ I.cochainComplex R.cochainShortComplex R.shortExact (n : ℤ) x) := by
  apply (moduleExtLinearEquivAbelianExt X S.X₁ (n + 1)).injective
  simp only [moduleExtYonedaCovariantBoundary_compare, injectiveHomologyModuleExtAddEquiv_compare]
  exact injectiveHomologyExtAddEquiv_covariantδ R I hS n x

/-- The original module-valued coefficient Yoneda boundary equals the actual
literal-source Hom boundary under the existing normalized augmentation comparison. -/
theorem sourceInjectiveHomologyModuleExtAddEquiv_covariantδ (I : InjectiveResolution X)
    (hS : S.ShortExact) (n : ℕ)
    (x : (sourceHomComplex I.cochainComplex R.I₃.cochainComplex).homology (n : ℤ)) :
    moduleExtYonedaCovariantBoundary X S hS n
        (sourceInjectiveHomologyModuleExtAddEquiv I R.I₃ n x) =
      sourceInjectiveHomologyModuleExtAddEquiv I R.I₁ (n + 1)
        (sourceHomCovariantδ I.cochainComplex R.cochainShortComplex R.shortExact (n : ℤ) x) := by
  apply (moduleExtLinearEquivAbelianExt X S.X₁ (n + 1)).injective
  simp only [moduleExtYonedaCovariantBoundary_compare,
    sourceInjectiveHomologyModuleExtAddEquiv_compare]
  exact sourceInjectiveHomologyExtAddEquiv_covariantδ R I hS n x

end SGA.SGA2.ExposeV
