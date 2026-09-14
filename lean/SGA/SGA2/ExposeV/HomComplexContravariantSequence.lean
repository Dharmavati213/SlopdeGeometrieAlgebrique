/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.HomComplexPrecomposition
import SGA.SGA2.ExposeV.HomComplexContravariantConnecting
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # V.1: the original contravariant Hom-complex exact sequence -/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The original reversed Hom sequence of a short complex of complexes. -/
def homComplexContravariantSequence (S : ShortComplex (CochainComplex C ℤ))
    (P : CochainComplex C ℤ) : ShortComplex (CochainComplex AddCommGrpCat ℤ) :=
  ShortComplex.mk (homComplexPrecomp S.g P) (homComplexPrecomp S.f P) (by
    ext n z
    change (Cochain.ofHom S.f).comp
      ((Cochain.ofHom S.g).comp z (zero_add n)) (zero_add n) = 0
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, S.zero]
    simp)

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
  (P : CochainComplex C ℤ)

include hS

/-- Original cochains factoring through the quotient are determined uniquely. -/
theorem homCochainPrecomp_injective (n : ℤ) :
    Function.Injective (fun z : Cochain S.X₃ P n =>
      (Cochain.ofHom S.g).comp z (zero_add n)) := by
  have (p : ℤ) : Epi (S.g.f p) :=
    ((shortExact_iff_degreewise_shortExact S).mp hS p).epi_g
  intro z w hz
  ext p q hpq
  apply (cancel_epi (S.g.f p)).mp
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    Cochain.congr_v hz p q hpq

/-- A cochain vanishing on the subcomplex factors through the original
quotient complex degree by degree. -/
theorem exists_homCochainQuotient (n : ℤ) (b : Cochain S.X₂ P n)
    (hb : (Cochain.ofHom S.f).comp b (zero_add n) = 0) :
    ∃ a : Cochain S.X₃ P n, (Cochain.ofHom S.g).comp a (zero_add n) = b := by
  have (p : ℤ) : Epi (S.map (eval C (ComplexShape.up ℤ) p)).g :=
    ((shortExact_iff_degreewise_shortExact S).mp hS p).epi_g
  have hz (p q : ℤ) (hpq : p + n = q) : S.f.f p ≫ b.v p q hpq = 0 := by
    simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] using
      Cochain.congr_v hb p q hpq
  refine ⟨Cochain.mk (fun p q hpq =>
    ((shortExact_iff_degreewise_shortExact S).mp hS p).exact.desc
      (b.v p q hpq) (hz p q hpq)), ?_⟩
  ext p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
  exact ((shortExact_iff_degreewise_shortExact S).mp hS p).exact.g_desc _ _

/-- Into a degreewise injective target, every original cochain on the
subcomplex extends to the middle complex. -/
theorem exists_homCochainExtension [∀ q, Injective (P.X q)]
    (n : ℤ) (c : Cochain S.X₁ P n) :
    ∃ b : Cochain S.X₂ P n, (Cochain.ofHom S.f).comp b (zero_add n) = c := by
  have (p : ℤ) : Mono (S.f.f p) :=
    ((shortExact_iff_degreewise_shortExact S).mp hS p).mono_f
  refine ⟨Cochain.mk (fun p q hpq => Injective.factorThru (c.v p q hpq) (S.f.f p)), ?_⟩
  ext p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v,
    Injective.comp_factorThru]

/-- The actual Hom complexes form a short exact sequence whenever the
fixed target complex has injective terms; no splitting is assumed. -/
theorem homComplexContravariantSequence_shortExact [∀ q, Injective (P.X q)] :
    (homComplexContravariantSequence S P).ShortExact := by
  apply (shortExact_iff_degreewise_shortExact _).mpr
  intro n
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff]
    intro b hb
    exact exists_homCochainQuotient S hS P n b hb
  · exact (AddCommGrpCat.mono_iff_injective _).mpr (homCochainPrecomp_injective S hS P n)
  · exact (AddCommGrpCat.epi_iff_surjective _).mpr (exists_homCochainExtension S hS P n)

end SGA.SGA2.ExposeV
