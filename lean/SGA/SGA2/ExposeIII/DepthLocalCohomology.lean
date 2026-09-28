/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.Depth
import SGA.SGA2.ExposeIII.AssociatedPrimes
import SGA.SGA2.ExposeII.ExtColimitSequence
import SGA.SGA2.ExposeII.LocalCohomologyZero
import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Depth and algebraic local cohomology

The depth bound `n ≤ depth I M` is equivalent, over a noetherian ring for
finite `M`, to vanishing of the actual ideal-power local cohomology modules
in every degree below `n`. The proof uses the two Ext constructions through
their common projective-resolution computation, and the genuine coefficient
exact sequence of the Ext colimits.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite HomologicalComplex
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- The module-valued Ext used in algebraic local cohomology vanishes exactly
when derived-category Ext vanishes. Both are computed by the same resolution. -/
theorem isZero_moduleExt_iff_subsingleton_ext (N M : ModuleCat.{u} R) (i : ℕ) :
    IsZero (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).obj M) ↔
      Subsingleton (Abelian.Ext N M i) := by
  cases i with
  | zero =>
    have e := (extZeroIsoHom M).app (op N)
    constructor
    · intro h
      have : Subsingleton (N ⟶ M) := ModuleCat.subsingleton_of_isZero (h.of_iso e.symm)
      exact Abelian.Ext.addEquiv₀.subsingleton
    · intro h
      have : Subsingleton (N ⟶ M) := Abelian.Ext.addEquiv₀.subsingleton_congr.mp h
      exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (N ⟶ M))).of_iso e
  | succ i =>
    let P := projectiveResolution N
    have e := P.isoExt (R := R) (i + 1) M
    have hcomp :
        IsZero ((P.complex.linearYonedaObj R M).homology (i + 1)) ↔
        ∀ (f : P.complex.X (i + 1) ⟶ M), P.complex.d (i + 2) (i + 1) ≫ f = 0 →
          ∃ (g : P.complex.X i ⟶ M), P.complex.d (i + 1) i ≫ g = f := by
      rw [← exactAt_iff_isZero_homology,
        exactAt_iff' _ i (i + 1) (i + 2) (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff]
      rfl
    constructor
    · intro h
      apply subsingleton_of_forall_eq 0
      intro x
      obtain ⟨f, hf, rfl⟩ := P.extMk_surjective x (i + 2) rfl
      exact (P.extMk_eq_zero_iff f (i + 2) rfl hf i rfl).mpr
        (hcomp.mp (h.of_iso e.symm) f hf)
    · intro h
      apply IsZero.of_iso _ e
      apply hcomp.mpr
      intro f hf
      exact (P.extMk_eq_zero_iff f (i + 2) rfl hf i rfl).mp (h.elim _ _)

/-- Pointwise Ext colimits and mathlib's colimit of coefficient functors
are canonically isomorphic for the actual ideal-power diagram. -/
def idealPowerExtIsoLocalCohomology (I : Ideal R) (i : ℕ) :
    extColimitFunctor (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)) i ≅
      _root_.localCohomology I i :=
  (colimitIsoFlipCompColim (localCohomology.diagram
    (localCohomology.idealPowersDiagram I) i)).symm

set_option backward.isDefEq.respectTransparency false in
/-- A depth bound forces vanishing of actual algebraic local cohomology.
This implication holds for arbitrary modules over any commutative ring. -/
theorem isZero_localCohomology_of_lt_depth (I : Ideal R) (M : ModuleCat.{u} R)
    (n : ℕ) (hdepth : (n : ℕ∞) ≤ depth I M) (i : ℕ) (hi : i < n) :
    IsZero ((_root_.localCohomology I i).obj M) := by
  let Q := localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)
  apply IsZero.of_iso _ ((idealPowerExtIsoLocalCohomology I i).app M).symm
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 (colimit ((extColimitDiagramFunctor Q i).obj M)) = 0
  apply colimit.hom_ext
  intro j
  have hpow : I ^ j.unop.unop ≤ Module.annihilator R (Q.obj j.unop) := by
    change I ^ j.unop.unop ≤ Module.annihilator R (R ⧸ I ^ j.unop.unop)
    rw [Ideal.annihilator_quotient]
  have hExt := (le_depth_iff I M n).mp hdepth (Q.obj j.unop)
    (inferInstanceAs (Module.Finite R (R ⧸ I ^ j.unop.unop)))
    ⟨j.unop.unop, hpow⟩ i hi
  have hz := (isZero_moduleExt_iff_subsingleton_ext (Q.obj j.unop) M i).mpr hExt
  exact hz.eq_of_src _ _

/-- Vanishing of degree-zero local cohomology rules out any nonzero
element annihilated by the whole ideal. -/
theorem idealRegular_of_isZero_localCohomology_zero (I : Ideal R) (M : ModuleCat.{u} R)
    (h : IsZero ((_root_.localCohomology I 0).obj M)) : IdealRegular M I := by
  have : Subsingleton (powerTorsion I M) := ModuleCat.subsingleton_of_isZero
    (h.of_iso (localCohomologyZeroIsoPowerTorsion I M).symm)
  intro m hm
  have hmem : m ∈ powerTorsion I M := (mem_powerTorsion_iff I M m).mpr
    ⟨1, by simpa only [pow_one] using hm⟩
  exact congrArg Subtype.val (Subsingleton.elim (⟨m, hmem⟩ : powerTorsion I M) 0)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine coefficient exact sequence: vanishing of `Hⁱ_I(S.X₂)`
and `Hⁱ⁺¹_I(S.X₁)` forces vanishing of `Hⁱ_I(S.X₃)`. -/
theorem isZero_localCohomology_of_shortExact (I : Ideal R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ)
    (h₂ : IsZero ((_root_.localCohomology I i).obj S.X₂))
    (h₁ : IsZero ((_root_.localCohomology I (i + 1)).obj S.X₁)) :
    IsZero ((_root_.localCohomology I i).obj S.X₃) := by
  let Q := localCohomology.ringModIdeals (localCohomology.idealPowersDiagram I)
  have h₂' := h₂.of_iso ((idealPowerExtIsoLocalCohomology I i).app S.X₂)
  have h₁' := h₁.of_iso ((idealPowerExtIsoLocalCohomology I (i + 1)).app S.X₁)
  have h₃' := ShortComplex.Exact.isZero_of_both_zeros (extColimit_exact₃ Q S hS i)
    (h₂'.eq_zero_of_src _) (h₁'.eq_zero_of_tgt _)
  exact h₃'.of_iso ((idealPowerExtIsoLocalCohomology I i).app S.X₃).symm

/-- Depth is detected by vanishing of actual algebraic local cohomology,
with no restriction excluding infinite depth. -/
theorem le_depth_iff_localCohomology_vanishes [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔
      ∀ i < n, IsZero ((_root_.localCohomology I i).obj M) := by
  constructor
  · exact isZero_localCohomology_of_lt_depth I M n
  · intro h
    induction n generalizing M with
    | zero => exact bot_le
    | succ n ih =>
      obtain ⟨f, hf, hreg⟩ := (idealRegular_iff_exists_regular M I).mp
        (idealRegular_of_isZero_localCohomology_zero I M (h 0 (by omega)))
      apply (succ_le_depth_iff I M hf hreg n).mpr
      apply ih
      intro i hi
      exact isZero_localCohomology_of_shortExact I (M.smulShortComplex f)
        hreg.smulShortComplex_shortExact i (h i (by omega)) (h (i + 1) (by omega))

/-- The same criterion on the underlying local cohomology modules. -/
theorem le_depth_iff_subsingleton_localCohomology [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔
      ∀ i < n, Subsingleton ((_root_.localCohomology I i).obj M) := by
  simp_rw [← ModuleCat.isZero_iff_subsingleton]
  exact le_depth_iff_localCohomology_vanishes I M n

/-- Infinite depth is equivalent to vanishing of every algebraic local cohomology module. -/
theorem depth_eq_top_iff_localCohomology_vanishes [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth I M = ⊤ ↔ ∀ i, IsZero ((_root_.localCohomology I i).obj M) := by
  constructor
  · intro h i
    exact isZero_localCohomology_of_lt_depth I M (i + 1) (by simp [h]) i (by omega)
  · intro h
    apply top_unique
    rw [← ENat.iSup_natCast]
    exact iSup_le fun n ↦ (le_depth_iff_localCohomology_vanishes I M n).mpr (fun i _ ↦ h i)

/-- The first possibly nonzero algebraic local cohomology degree equals depth. -/
theorem depth_eq_iInf_localCohomology [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth I M = ⨅ (i : ℕ) (_ : ¬ IsZero ((_root_.localCohomology I i).obj M)), (i : ℕ∞) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [le_depth_iff_localCohomology_vanishes]
  simp only [le_iInf_iff, ENat.natCast_le_natCast]
  constructor
  · intro h i hi
    by_contra hn
    exact hi (h i (Nat.lt_of_not_ge hn))
  · intro h i hi
    by_contra hzero
    exact (Nat.not_le_of_gt hi) (h i hzero)

end SGA.SGA2.ExposeIII
