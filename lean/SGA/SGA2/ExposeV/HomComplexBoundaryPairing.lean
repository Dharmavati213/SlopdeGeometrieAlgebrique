/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.HomComplexCovariantNaturality
import SGA.SGA2.ExposeV.HomComplexContravariantNaturality

/-! # V.1: the original Hom pairing and both original connecting maps

The actual composite of two lifted cochains gives the coboundary witnessing
the boundary-pairing identity. Both conventions are retained: the standard
differential contributes the sign of the second target degree, and the
literal source differential contributes the sign of the first target degree.
No K-injectivity or derived-category hypothesis is used in these identities.
-/

noncomputable section
universe v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]
  {F P : CochainComplex C ℤ} (S : ShortComplex (CochainComplex C ℤ)) {i j : ℤ}
  (a : Cocycle F S.X₁ (i + 1)) (b : Cochain F S.X₂ i) (c : Cocycle F S.X₃ i)
  (d : Cocycle S.X₁ P j) (e : Cochain S.X₂ P j) (f : Cocycle S.X₃ P (j + 1))

/-- The original two lifts have a composite whose standard differential
is the sum of the two original boundary composites with the exact sign. -/
theorem homConnectingPairing_δ
    (hb : δ i (i + 1) b = a.1.comp (Cochain.ofHom S.f) (add_zero (i + 1)))
    (hc : b.comp (Cochain.ofHom S.g) (add_zero i) = c.1)
    (he : δ j (j + 1) e = (Cochain.ofHom S.g).comp f.1 (zero_add (j + 1)))
    (hd : (Cochain.ofHom S.f).comp e (zero_add j) = d.1) :
    δ (i + j) (i + j + 1) (b.comp e rfl) =
      (homCocycleComp c f (by omega)).1 +
        j.negOnePow • (homCocycleComp a d (by omega)).1 := by
  rw [δ_comp b e rfl (i + 1) (j + 1) (i + j + 1) rfl rfl rfl, hb, he]
  rw [Cochain.comp_assoc_of_second_is_zero_cochain, hd,
    ← Cochain.comp_assoc_of_second_is_zero_cochain, hc]
  rfl

/-- The literal source differential of the original composite of lifts. -/
theorem sourceHomConnectingPairing_δ
    (hb : sourceHomδ i (i + 1) b = a.1.comp (Cochain.ofHom S.f) (add_zero (i + 1)))
    (hc : b.comp (Cochain.ofHom S.g) (add_zero i) = c.1)
    (he : sourceHomδ j (j + 1) e = (Cochain.ofHom S.g).comp f.1 (zero_add (j + 1)))
    (hd : (Cochain.ofHom S.f).comp e (zero_add j) = d.1) :
    sourceHomδ (i + j) (i + j + 1) (b.comp e rfl) =
      (homCocycleComp a d (by omega)).1 +
        i.negOnePow • (homCocycleComp c f (by omega)).1 := by
  rw [sourceHomδ_comp, hb, he]
  rw [Cochain.comp_assoc_of_second_is_zero_cochain, hd,
    ← Cochain.comp_assoc_of_second_is_zero_cochain, hc]
  rfl

/-- The original standard boundary representatives give the signed pairing
identity on the original cohomology classes, via their explicit coboundary. -/
theorem homConnectingPairing_class
    (hb : δ i (i + 1) b = a.1.comp (Cochain.ofHom S.f) (add_zero (i + 1)))
    (hc : b.comp (Cochain.ofHom S.g) (add_zero i) = c.1)
    (he : δ j (j + 1) e = (Cochain.ofHom S.g).comp f.1 (zero_add (j + 1)))
    (hd : (Cochain.ofHom S.f).comp e (zero_add j) = d.1) :
    CohomologyClass.mk (homCocycleComp a d (k := i + j + 1) (by omega)) =
      (j + 1).negOnePow • CohomologyClass.mk (homCocycleComp c f (by omega)) := by
  have hz : CohomologyClass.mk (homCocycleComp c f (k := i + j + 1) (by omega) +
      j.negOnePow • homCocycleComp a d (by omega)) = 0 := by
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (i + j) rfl]
    exact ⟨b.comp e rfl, homConnectingPairing_δ S a b c d e f hb hc he hd⟩
  change (CohomologyClass.mkAddMonoidHom _ _ _) (_ + (j.negOnePow : ℤ) • _) = 0 at hz
  rw [map_add, map_zsmul] at hz
  change CohomologyClass.mk (homCocycleComp c f (k := i + j + 1) (by omega)) +
    j.negOnePow • CohomologyClass.mk (homCocycleComp a d (by omega)) = 0 at hz
  have ht := congrArg (j.negOnePow • ·) hz
  simp only [smul_add, smul_smul, Int.units_mul_self,
    one_smul, smul_zero] at ht
  rw [Int.negOnePow_succ, Units.neg_smul, eq_neg_iff_add_eq_zero]
  exact (add_comm _ _).trans ht

/-- The displayed source differential has the first target-degree sign
in its boundary-pairing identity, with an explicit original coboundary. -/
theorem sourceHomConnectingPairing_class
    (hb : sourceHomδ i (i + 1) b = a.1.comp (Cochain.ofHom S.f) (add_zero (i + 1)))
    (hc : b.comp (Cochain.ofHom S.g) (add_zero i) = c.1)
    (he : sourceHomδ j (j + 1) e = (Cochain.ofHom S.g).comp f.1 (zero_add (j + 1)))
    (hd : (Cochain.ofHom S.f).comp e (zero_add j) = d.1) :
    CohomologyClass.mk (homCocycleComp a d (k := i + j + 1) (by omega)) =
      (i + 1).negOnePow • CohomologyClass.mk (homCocycleComp c f (by omega)) := by
  have hz : CohomologyClass.mk (homCocycleComp a d (k := i + j + 1) (by omega) +
      i.negOnePow • homCocycleComp c f (by omega)) = 0 := by
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (i + j) rfl]
    refine ⟨(i + j + 1).negOnePow • b.comp e rfl, ?_⟩
    rw [δ_units_smul]
    exact sourceHomConnectingPairing_δ S a b c d e f hb hc he hd
  change (CohomologyClass.mkAddMonoidHom _ _ _) (_ + (i.negOnePow : ℤ) • _) = 0 at hz
  rw [map_add, map_zsmul] at hz
  rw [Int.negOnePow_succ, Units.neg_smul, eq_neg_iff_add_eq_zero]
  exact hz

omit a b c d e f in
/-- The two independently constructed standard Hom connecting maps satisfy
the original pairing identity on actual homology, with the precise sign.
Only degreewise injectivity is required; complexes need not be bounded. -/
theorem homologyComp_connecting (hS : S.ShortExact)
    [∀ q, Injective (S.X₁.X q)] [∀ q, Injective (P.X q)]
    (x : (HomComplex F S.X₃).homology i) (y : (HomComplex S.X₁ P).homology j) :
    homologyComp (k := i + j + 1) (by omega) (homComplexCovariantδ F S hS i x) y =
      (j + 1).negOnePow •
        homologyComp (by omega) x (homComplexContravariantδ S hS P j y) := by
  obtain ⟨c, rfl⟩ := homComplexHomologyMk_surjective F S.X₃ i x
  obtain ⟨d, rfl⟩ := homComplexHomologyMk_surjective S.X₁ P j y
  obtain ⟨b, a, hb, hc⟩ := exists_homComplexCovariantBoundary F S hS i c
  obtain ⟨e, f, he, hd⟩ := exists_homComplexContravariantBoundary S hS P j d
  rw [homComplexCovariantδ_mk F S hS i a b c hb hc,
    homComplexContravariantδ_mk S hS P j f e d he hd]
  apply (HomComplex.homologyAddEquiv F P (i + j + 1)).injective
  simpa only [Units.smul_def, map_zsmul, homologyAddEquiv_homologyComp,
    homComplexHomologyMk_compare, homClassComp_mk] using
    homConnectingPairing_class S a b c d e f hb hc he hd

omit a b c d e f in
/-- The original displayed-source pairing and its two actual connecting
maps satisfy the first target-degree signed identity on actual homology.
The proof uses the explicit composite of original lifts, not a transported
derived pairing, and requires no boundedness or K-injectivity hypothesis. -/
theorem sourceHomologyComp_connecting (hS : S.ShortExact)
    [∀ q, Injective (S.X₁.X q)] [∀ q, Injective (P.X q)]
    (x : (sourceHomComplex F S.X₃).homology i)
    (y : (sourceHomComplex S.X₁ P).homology j) :
    sourceHomologyComp (k := i + j + 1) (by omega) (sourceHomCovariantδ F S hS i x) y =
      (i + 1).negOnePow •
        sourceHomologyComp (by omega) x (sourceHomContravariantδ S hS P j y) := by
  obtain ⟨c, rfl⟩ := sourceHomologyMk_surjective S.X₃ F i x
  obtain ⟨d, rfl⟩ := sourceHomologyMk_surjective P S.X₁ j y
  obtain ⟨b, a, hb, hc⟩ := exists_sourceHomCovariantBoundary F S hS i c
  obtain ⟨e, f, he, hd⟩ := exists_sourceHomContravariantBoundary S hS P j d
  rw [sourceHomCovariantδ_mk F S hS i a b c hb hc,
    sourceHomContravariantδ_mk S hS P j f e d he hd,
    sourceHomologyComp_mk, sourceHomologyComp_mk]
  apply (sourceHomologyUnscaledAddEquiv F P (i + j + 1)).injective
  simpa only [Units.smul_def, map_zsmul, sourceHomologyMk, AddEquiv.apply_symm_apply] using
    sourceHomConnectingPairing_class S a b c d e f hb hc he hd

end SGA.SGA2.ExposeV
