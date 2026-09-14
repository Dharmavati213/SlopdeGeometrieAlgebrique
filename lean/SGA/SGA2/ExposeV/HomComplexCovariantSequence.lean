/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.HomComplexContravariantSequence
import SGA.SGA2.ExposeI.HomComplexNaturality

/-! # V.1: the covariant Hom sequence on degreewise-injective complexes -/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
open SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The original covariant Hom sequence, with actual postcomposition maps. -/
def homComplexCovariantSequence (F : CochainComplex C ℤ)
    (S : ShortComplex (CochainComplex C ℤ)) : ShortComplex (CochainComplex AddCommGrpCat ℤ) :=
  ShortComplex.mk (homComplexPostcomp F S.f) (homComplexPostcomp F S.g) (by
    ext n z
    change (z.comp (Cochain.ofHom S.f) (add_zero n)).comp
      (Cochain.ofHom S.g) (add_zero n) = 0
    rw [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, S.zero]
    simp)

variable (F : CochainComplex C ℤ) (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)

include hS

/-- Postcomposition with the original subcomplex inclusion is injective on
cochains, without any injectivity hypothesis on the objects. -/
theorem homCochainPostcomp_injective (n : ℤ) :
    Function.Injective (fun z : Cochain F S.X₁ n =>
      z.comp (Cochain.ofHom S.f) (add_zero n)) := by
  have (q : ℤ) : Mono (S.f.f q) :=
    ((shortExact_iff_degreewise_shortExact S).mp hS q).mono_f
  intro z w hz
  ext p q hpq
  apply (cancel_mono (S.f.f q)).mp
  simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using
    Cochain.congr_v hz p q hpq

/-- A cochain into the middle complex which vanishes in the quotient
factors through the original subcomplex, degree by degree. -/
theorem exists_homCochainSubcomplex (n : ℤ) (b : Cochain F S.X₂ n)
    (hb : b.comp (Cochain.ofHom S.g) (add_zero n) = 0) :
    ∃ a : Cochain F S.X₁ n, a.comp (Cochain.ofHom S.f) (add_zero n) = b := by
  have (q : ℤ) : Mono (S.map (eval C (ComplexShape.up ℤ) q)).f :=
    ((shortExact_iff_degreewise_shortExact S).mp hS q).mono_f
  have hz (p q : ℤ) (hpq : p + n = q) : b.v p q hpq ≫ S.g.f q = 0 := by
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.zero_v] using
      Cochain.congr_v hb p q hpq
  refine ⟨Cochain.mk (fun p q hpq =>
    ((shortExact_iff_degreewise_shortExact S).mp hS q).exact.lift
      (b.v p q hpq) (hz p q hpq)), ?_⟩
  ext p q hpq
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.mk_v]
  exact ((shortExact_iff_degreewise_shortExact S).mp hS q).exact.lift_f _ _

/-- Original quotient cochains lift through the actual degreewise splitting
provided by injectivity of the subcomplex terms. No chain splitting is assumed. -/
theorem exists_homCochainLift [∀ q, Injective (S.X₁.X q)]
    (n : ℤ) (c : Cochain F S.X₃ n) :
    ∃ b : Cochain F S.X₂ n, b.comp (Cochain.ofHom S.g) (add_zero n) = c := by
  have (q : ℤ) : Injective (S.map (eval C (ComplexShape.up ℤ) q)).X₁ :=
    show Injective (S.X₁.X q) from inferInstance
  let s (q : ℤ) := ((shortExact_iff_degreewise_shortExact S).mp hS q).splittingOfInjective
  refine ⟨Cochain.mk (fun p q hpq => c.v p q hpq ≫ (s q).s), ?_⟩
  ext p q hpq
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.mk_v, Category.assoc]
  exact (congrArg (c.v p q hpq ≫ ·) (s q).s_g).trans (Category.comp_id _)

/-- The covariant Hom sequence is short exact for arbitrary source complex
as soon as the first coefficient complex has injective terms. In particular,
this gives the source's assertion on degreewise-injective coefficient complexes. -/
theorem homComplexCovariantSequence_shortExact [∀ q, Injective (S.X₁.X q)] :
    (homComplexCovariantSequence F S).ShortExact := by
  apply (shortExact_iff_degreewise_shortExact _).mpr
  intro n
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff]
    intro b hb
    exact exists_homCochainSubcomplex F S hS n b hb
  · exact (AddCommGrpCat.mono_iff_injective _).mpr (homCochainPostcomp_injective F S hS n)
  · exact (AddCommGrpCat.epi_iff_surjective _).mpr (exists_homCochainLift F S hS n)

end SGA.SGA2.ExposeV
