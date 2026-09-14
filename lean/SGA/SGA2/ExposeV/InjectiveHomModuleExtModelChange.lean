/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.InjectiveHomExtNaturality
import SGA.SGA2.ExposeV.InjectiveHomModuleExtBoundary

/-! # Model independence on the original module-valued Ext objects

The unchanged canonical module-valued Ext comparison identifies actual
augmentation-compatible changes of either injective resolution with the
identity on the original Ext object, for both Hom differential conventions.
-/

noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex SGA.SGA2.ExposeI SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {A : Type u} [CommRing A] {X Y : ModuleCat.{u} A}
  (I : InjectiveResolution X) (J : InjectiveResolution Y)

/-- First-resolution change preserves the unchanged original module-valued Ext comparison. -/
theorem injectiveHomologyModuleExtAddEquiv_precomp_modelChange (K : InjectiveResolution X)
    (φ : I.cochainComplex ⟶ K.cochainComplex) (hφ : I.ι' ≫ φ = K.ι') (n : ℕ)
    (z : (HomComplex K.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    injectiveHomologyModuleExtAddEquiv I J n
        (homologyMap (homComplexPrecomp φ J.cochainComplex) n z) =
      injectiveHomologyModuleExtAddEquiv K J n z := by
  apply (moduleExtLinearEquivAbelianExt X Y n).injective
  simp only [injectiveHomologyModuleExtAddEquiv_compare]
  exact injectiveHomologyExtAddEquiv_precomp_modelChange I J K φ hφ n z

/-- Second-resolution change preserves the unchanged original module-valued Ext comparison. -/
theorem injectiveHomologyModuleExtAddEquiv_postcomp_modelChange (K : InjectiveResolution Y)
    (ψ : J.cochainComplex ⟶ K.cochainComplex) (hψ : J.ι' ≫ ψ = K.ι') (n : ℕ)
    (z : (HomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    injectiveHomologyModuleExtAddEquiv I K n
        (homologyMap (homComplexPostcomp I.cochainComplex ψ) n z) =
      injectiveHomologyModuleExtAddEquiv I J n z := by
  apply (moduleExtLinearEquivAbelianExt X Y n).injective
  simp only [injectiveHomologyModuleExtAddEquiv_compare]
  exact injectiveHomologyExtAddEquiv_postcomp_modelChange I J K ψ hψ n z

/-- First-resolution change preserves the fixed normalized-source module-valued comparison. -/
theorem sourceInjectiveHomologyModuleExtAddEquiv_precomp_modelChange (K : InjectiveResolution X)
    (φ : I.cochainComplex ⟶ K.cochainComplex) (hφ : I.ι' ≫ φ = K.ι') (n : ℕ)
    (z : (sourceHomComplex K.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    sourceInjectiveHomologyModuleExtAddEquiv I J n
        (homologyMap (sourceHomPrecomp φ J.cochainComplex) n z) =
      sourceInjectiveHomologyModuleExtAddEquiv K J n z := by
  apply (moduleExtLinearEquivAbelianExt X Y n).injective
  simp only [sourceInjectiveHomologyModuleExtAddEquiv_compare]
  exact sourceInjectiveHomologyExtAddEquiv_precomp_modelChange I J K φ hφ n z

/-- Second-resolution change preserves the fixed normalized-source module-valued comparison. -/
theorem sourceInjectiveHomologyModuleExtAddEquiv_postcomp_modelChange (K : InjectiveResolution Y)
    (ψ : J.cochainComplex ⟶ K.cochainComplex) (hψ : J.ι' ≫ ψ = K.ι') (n : ℕ)
    (z : (sourceHomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    sourceInjectiveHomologyModuleExtAddEquiv I K n
        (homologyMap (sourceHomPostcomp I.cochainComplex ψ) n z) =
      sourceInjectiveHomologyModuleExtAddEquiv I J n z := by
  apply (moduleExtLinearEquivAbelianExt X Y n).injective
  simp only [sourceInjectiveHomologyModuleExtAddEquiv_compare]
  exact sourceInjectiveHomologyExtAddEquiv_postcomp_modelChange I J K ψ hψ n z

end SGA.SGA2.ExposeV
