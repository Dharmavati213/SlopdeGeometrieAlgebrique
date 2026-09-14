/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.ResidueFieldLocalization
import Mathlib.CategoryTheory.Abelian.Injective.Dimension

/-!
# Global projective dimension and arbitrary-module Ext vanishing

Baer's criterion and actual injective dimension shifting promote cyclic Ext
tests to arbitrary modules. Thus the proved finite-module bound over a
regular local ring is a genuine global bound, with neither Ext argument
required finite. The original residue field attains the bound. This supplies
the global-dimension and arbitrary-module upper vanishing used in IV.5.3.
-/

noncomputable section
universe u
open CategoryTheory Limits Abelian IsLocalRing
open SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Baer's criterion, expressed with the original derived Ext classes of
the actual cyclic quotients. -/
theorem injective_of_cyclic_ext_one (N : ModuleCat.{u} R)
    (h : ∀ I : Ideal R, Subsingleton (Abelian.Ext (ModuleCat.of R (R ⧸ I)) N 1)) :
    Injective N := by
  have hBaer : Module.Baer R N := by
    intro I g
    let S := ModuleCat.shortComplexOfCompEqZero I.subtype I.mkQ (by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem.mpr x.property)
    have hS : S.ShortExact :=
      { exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker S).mpr
          (I.range_subtype.trans I.ker_mkQ.symm)
        mono_f := (ModuleCat.mono_iff_injective _).mpr I.injective_subtype
        epi_g := (ModuleCat.epi_iff_surjective _).mpr I.mkQ_surjective }
    have := h I
    obtain ⟨φ, hφ⟩ := Ext.contravariant_sequence_exact₁ hS N
      (Ext.mk₀ (ModuleCat.ofHom g)) (zero_add 1) (by subsingleton)
    obtain ⟨f, rfl⟩ := Ext.homEquiv₀.symm.surjective φ
    have hf : S.f ≫ f = ModuleCat.ofHom g :=
      Ext.homEquiv₀.symm.injective (by simpa using hφ)
    exact ⟨f.hom, fun x hx ↦ DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hf) ⟨x, hx⟩⟩
  have := hBaer.injective
  exact Module.injective_object_of_injective_module R N

/-- Cyclic Ext in degree `n+1` detects injective dimension at most `n`,
without noetherianity or finiteness of the coefficient module. -/
theorem hasInjectiveDimensionLE_of_cyclic_ext (N : ModuleCat.{u} R) (n : ℕ)
    (h : ∀ I : Ideal R, Subsingleton (Abelian.Ext (ModuleCat.of R (R ⧸ I)) N (n + 1))) :
    HasInjectiveDimensionLE N n := by
  induction n generalizing N with
  | zero =>
    have := injective_of_cyclic_ext_one N h
    infer_instance
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι N))
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι N) }
    have hQ : HasInjectiveDimensionLE S.X₃ n := by
      apply ih
      intro I
      have := h I
      apply subsingleton_of_forall_eq 0
      intro e
      obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃ (ModuleCat.of R (R ⧸ I)) hS
        e rfl (by subsingleton)
      rw [Ext.eq_zero_of_injective a, Ext.zero_comp] at ha
      exact ha.symm
    exact (hS.hasInjectiveDimensionLT_X₃_iff n inferInstance).mp hQ

/-- A uniform projective-dimension bound on cyclic quotients gives the
same bound on every module, not just finitely generated modules. -/
theorem hasProjectiveDimensionLE_of_cyclic_bound (n : ℕ)
    (hcyclic : ∀ I : Ideal R, HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ I)) n)
    (M : ModuleCat.{u} R) : HasProjectiveDimensionLE M n := by
  apply HasProjectiveDimensionLT.mk
  intro i hi N e
  have : HasInjectiveDimensionLE N n := hasInjectiveDimensionLE_of_cyclic_ext N n (fun I ↦ by
    have := hcyclic I
    exact HasProjectiveDimensionLT.subsingleton (ModuleCat.of R (R ⧸ I)) (n + 1)
      (n + 1) le_rfl N)
  exact e.eq_zero_of_hasInjectiveDimensionLT (n + 1) hi

/-- The global projective dimension is the supremum of the actual
projective dimensions of all modules in the original module category. -/
def moduleGlobalDimension (R : Type u) [CommRing R] : WithBot ℕ∞ :=
  ⨆ M : ModuleCat.{u} R, projectiveDimension M

/-- The residue field alone controls the dimension of arbitrary modules
over a noetherian local ring, not just finite modules. -/
theorem hasProjectiveDimensionLE_of_residueField [IsNoetherianRing R] [IsLocalRing R]
    (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n]
    (M : ModuleCat.{u} R) : HasProjectiveDimensionLE M n :=
  hasProjectiveDimensionLE_of_cyclic_bound n
    (fun I ↦ finite_hasProjectiveDimensionLE_of_residueField n (ModuleCat.of R (R ⧸ I))) M

/-- A noetherian local ring's global projective dimension is the actual
projective dimension of its residue field, also when that dimension is infinite. -/
theorem moduleGlobalDimension_eq_residueField [IsNoetherianRing R] [IsLocalRing R] :
    moduleGlobalDimension R = projectiveDimension (ModuleCat.of R (ResidueField R)) := by
  apply le_antisymm
  · apply le_of_forall_ge
    intro b hb
    cases b with
    | bot =>
      have hz := (projectiveDimension_eq_bot_iff _).mp (le_bot_iff.mp hb)
      have : Subsingleton (ResidueField R) := ModuleCat.subsingleton_of_isZero hz
      exact False.elim (zero_ne_one (Subsingleton.elim (0 : ResidueField R) 1))
    | coe b =>
      cases b using ENat.recTopCoe with
      | top => exact le_top
      | coe n =>
        have : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n :=
          (projectiveDimension_le_iff _ n).mp hb
        exact iSup_le fun M ↦ (projectiveDimension_le_iff M n).mpr
          (hasProjectiveDimensionLE_of_residueField n M)
  · exact le_iSup (fun M : ModuleCat.{u} R ↦ projectiveDimension M)
      (ModuleCat.of R (ResidueField R))

variable [IsRegularLocalRing R]

/-- **IV.5.3, global bound:** every module over an actual regular local ring
has projective dimension bounded by the ring's actual Krull dimension. -/
theorem regularLocal_hasProjectiveDimensionLE (n : ℕ) (hdim : ringKrullDim R = n)
    (M : ModuleCat.{u} R) : HasProjectiveDimensionLE M n :=
  hasProjectiveDimensionLE_of_cyclic_bound n
    (fun I ↦ regularLocal_finite_hasProjectiveDimensionLE n hdim (ModuleCat.of R (R ⧸ I))) M

/-- **IV.5.3, arbitrary-module upper vanishing:** both original Ext
arguments are arbitrary, with no finite-length or finiteness hypothesis. -/
theorem regularLocal_ext_subsingleton_of_gt (n : ℕ) (hdim : ringKrullDim R = n)
    (M N : ModuleCat.{u} R) (i : ℕ) (hi : n < i) : Subsingleton (Abelian.Ext M N i) := by
  have := regularLocal_hasProjectiveDimensionLE n hdim M
  exact HasProjectiveDimensionLT.subsingleton M (n + 1) i hi N

/-- The same unrestricted vanishing for the original module-valued Ext. -/
theorem regularLocal_moduleExt_isZero_of_gt (n : ℕ) (hdim : ringKrullDim R = n)
    (M N : ModuleCat.{u} R) (i : ℕ) (hi : n < i) :
    IsZero (((_root_.Ext R (ModuleCat.{u} R) i).obj (Opposite.op M)).obj N) :=
  (isZero_moduleExt_iff_subsingleton_ext M N i).mpr
    (regularLocal_ext_subsingleton_of_gt n hdim M N i hi)

/-- **IV.5.3:** global dimension equals Krull dimension. The upper bound
is proved on all modules; the actual residue field realizes equality. -/
theorem regularLocal_moduleGlobalDimension_eq (n : ℕ) (hdim : ringKrullDim R = n) :
    moduleGlobalDimension R = n :=
  moduleGlobalDimension_eq_residueField.trans (regularLocal_residueField_projectiveDimension n hdim)

/-- The dimension-free formulation of the same global-dimension equality. -/
theorem regularLocal_moduleGlobalDimension_eq_ringKrullDim :
    moduleGlobalDimension R = ringKrullDim R :=
  (regularLocal_moduleGlobalDimension_eq (maximalIdeal R).spanFinrank
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm).trans
      IsRegularLocalRing.spanFinrank_maximalIdeal

/-- All modules over every actual prime localization have a uniform
projective-dimension bound, without assuming that localization regular. -/
theorem regularLocal_atPrime_hasProjectiveDimensionLE
    (n : ℕ) (hdim : ringKrullDim R = n) (p : Ideal R) [p.IsPrime]
    (M : ModuleCat.{u} (Localization.AtPrime p)) : HasProjectiveDimensionLE M n := by
  have := regularLocal_residueField_atPrime_hasProjectiveDimensionLE n hdim p
  exact hasProjectiveDimensionLE_of_residueField n M

/-- The actual prime localizations have finite global dimension. The
identification with their own Krull dimensions is not assumed here. -/
theorem regularLocal_atPrime_moduleGlobalDimension_le
    (n : ℕ) (hdim : ringKrullDim R = n) (p : Ideal R) [p.IsPrime] :
    moduleGlobalDimension (Localization.AtPrime p) ≤ n :=
  iSup_le fun M ↦ (projectiveDimension_le_iff M n).mpr
    (regularLocal_atPrime_hasProjectiveDimensionLE n hdim p M)

end SGA.SGA2.ExposeV
