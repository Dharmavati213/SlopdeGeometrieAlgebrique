/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import SGA.SGA2.ExposeI.DerivedFunctors
import SGA.SGA2.ExposeI.Flasque
import SGA.SGA2.ExposeI.GammaZ

/-!
# SGA 2, Exposé I, §1–2: degree-zero exactness and vanishing criteria

This file proves degree-zero statements and records generic Ext exactness.

* **I.1.8:** for closed `Z' ≤ Z`, exactness at `Γ_{Z'}` / `Γ_Z`; flasque extension.
* **I.2.8–I.2.10:** the generic contravariant Ext exact-sequence theorem is
  available, conditional on a supplied short exact sequence of sheaves.
* **I.2.12:** flasque restriction surjectivity and injective Ext vanishing.
* **I.2.13–I.2.14:** the kernel/cokernel criteria for a monomorphism/isomorphism,
  and injectivity on sections of the unit to the complement pushforward.

The short exact sequence of support sheaves, its comparison with local
cohomology, the sheafified long exact sequence, the flasque vanishing
equivalence, and higher-degree restriction criteria are not proved here.

Numbering follows Grothendieck. English: `translation/SGA2/ExposeI/`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-! ## I.1.8 Exact sequence for closed supports -/

/-- **I.1.8 (exactness at `Γ_{Z'}` and `Γ_Z`):** for closed `Z' ≤ Z`,
`Γ_{Z'}(F) = Γ_Z(F) ∩ ker(Γ(X,F) → Γ(X\Z', F))`. -/
theorem exact_at_gammaZ_of_le {Z' Z : Closeds X} (h : Z' ≤ Z)
    (F : Sheaf AddCommGrpCat.{u} X) :
    gammaZ F Z' = gammaZ F Z ⊓ (restrictToComplement F Z' ⊤).hom.ker :=
  exact_gammaZ_of_le F h

/-- **I.1.8 (flasque extension):** every section over `X \ Z'` extends when `F` is flasque. -/
theorem exists_extension_for_I_1_8 (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F]
    (Z' : Closeds X) (t : F.1.obj (op Z'.compl)) :
    ∃ s : F.1.obj (op (⊤ : Opens X)),
      (F.1.map (homOfLE (le_top : Z'.compl ≤ ⊤)).op).hom s = t :=
  exists_extension_of_isFlasque F Z' t

/-- **I.1.8 (closed case, degree 0 exactness + flasque input):** packaging. -/
theorem I_1_8_package {Z' Z : Closeds X} (h : Z' ≤ Z)
    (F : Sheaf AddCommGrpCat.{u} X) :
    gammaZ F Z' = gammaZ F Z ⊓ (restrictToComplement F Z' ⊤).hom.ker ∧
      (IsFlasque F →
        ∀ t : F.1.obj (op Z'.compl),
          ∃ s : F.1.obj (op (⊤ : Opens X)),
            (F.1.map (homOfLE (le_top : Z'.compl ≤ ⊤)).op).hom s = t) :=
  ⟨exact_gammaZ_of_le F h, fun _ t => exists_extension_of_isFlasque F Z' t⟩

/-! ## I.2.8–I.2.9 Long exact sequences via Ext -/

/-- Generic contravariant Ext exactness for a supplied short exact sequence.
Specializing this to I.2.8 requires constructing the short exact sequence of
support sheaves and comparing its maps with local cohomology maps. -/
theorem ext_contravariant_exact
    {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (F : Sheaf AddCommGrpCat.{u} X)
    (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    (Ext.contravariantSequence hS F n₀ n₁ h).Exact :=
  Ext.contravariantSequence_exact hS F n₀ n₁ h

/-- **I.2.9:** the special case `Z = X`, `Z' = A` closed gives the relative
cohomology sequence. Degree 0 exactness at `Γ_A` / `Γ` is
`exact_gammaZ_of_le` with `Z = ⊤`. -/
theorem I_2_9_degree_zero (A : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    gammaZ F A = gammaZ F (⊤ : Closeds X) ⊓ (restrictToComplement F A ⊤).hom.ker :=
  exact_gammaZ_of_le F le_top

/-! ## Degree-zero sections related to I.2.10 -/

/-- The kernel intersection formula on global sections for nested closed
supports. This does not assert an exact sequence of sheaves. -/
theorem I_2_10_degree_zero_sections {Z' Z : Closeds X} (h : Z' ≤ Z)
    (F : Sheaf AddCommGrpCat.{u} X) :
    gammaZ F Z' = gammaZ F Z ⊓ (restrictToComplement F Z' ⊤).hom.ker :=
  exact_gammaZ_of_le F h

/-! ## I.2.11 Degree 0 / 1 of `ℋ_A` -/

/-- **I.2.11 (degree 0):** `ℋ_A^0(F) = ker(F → j_* j^* F) = Γ̲_A(F)`. -/
noncomputable abbrev sheafH_A_zero (A : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    Sheaf AddCommGrpCat.{u} X :=
  sheafH_Z_n A F 0

/-- **I.2.11 (degree 1):** `ℋ_A^1(F) = coker(F → j_* j^* F)`. -/
noncomputable abbrev sheafH_A_one (A : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    Sheaf AddCommGrpCat.{u} X :=
  sheafH_Z_n A F 1

/-- **I.2.11 (degree ≥ 2):** `ℋ_A^{i}(F) = R^{i-1} j_*(F|_{X\A})` for `i ≥ 2`. -/
noncomputable abbrev sheafH_A_ge_two (A : Closeds X) (F : Sheaf AddCommGrpCat.{u} X)
    (i : ℕ) : Sheaf AddCommGrpCat.{u} X :=
  sheafH_Z_n A F (i + 2)

/-- **I.2.11 (unit):** the unit `F → j_* j^* F` whose kernel/cokernel are
`ℋ_A^0` / `ℋ_A^1`. -/
noncomputable abbrev toComplement_for_I_2_11 (A : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) :=
  toComplementPushforward F A

/-- The defining zero-composite condition of the kernel inclusion in I.2.11. -/
theorem I_2_11_kernel_condition (A : Closeds X) (F : Sheaf AddCommGrpCat.{u} X) :
    underlineGammaZ_ι F A ≫ toComplementPushforward F A = 0 :=
  underlineGammaZ_ι_comp_toComplement F A

/-! ## I.2.12 Flasque vanishing / characterisation -/

/-- **I.2.12 (⇒, degree 0):** if `F` is flasque then restriction
`Γ(X,F) → Γ(X\Z, F)` is surjective for every closed `Z`. -/
theorem surjective_restrict_of_isFlasque_closed (F : Sheaf AddCommGrpCat.{u} X)
    [IsFlasque F] (Z : Closeds X) :
    Function.Surjective (F.1.map (homOfLE (le_top : Z.compl ≤ ⊤)).op).hom :=
  surjective_restrict_of_isFlasque F Z.compl

/-- Restrictions to closed complements being surjective implies the same for
every open, since every open is the complement of a closed subset. -/
theorem surjective_to_opens_of_surjective_to_closed_complements
    (F : Sheaf AddCommGrpCat.{u} X)
    (h : ∀ Z : Closeds X,
      Function.Surjective (F.1.map (homOfLE (le_top : Z.compl ≤ ⊤)).op).hom)
    (U : Opens X) :
    Function.Surjective (F.1.map (homOfLE (le_top : U ≤ ⊤)).op).hom := by
  let Z : Closeds X := ⟨(U : Set X)ᶜ, isClosed_compl_iff.mpr U.isOpen⟩
  have hUZ : Z.compl = U := by
    ext x
    simp [Z, Closeds.compl]
  have := h Z
  convert this using 1
  · rw [hUZ]

/-- **I.2.12:** injective ⇒ higher `H_Z` vanish. -/
theorem H_Z_vanishing_of_injective (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] (n : ℕ) :
    Subsingleton (H_Z Z F (n + 1)) :=
  Ext.subsingleton_of_injective (zZX_closed Z) F n

/-! ## I.2.13–I.2.14 Vanishing criteria -/

/-- **I.2.13–I.2.14 (degree 0):** vanishing of `ℋ_Z^0` relates to the kernel of
`F → j_* j^* F`. -/
theorem vanishing_criteria_degree_zero (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    underlineGammaZ_ι F Z ≫ toComplementPushforward F Z = 0 :=
  underlineGammaZ_ι_comp_toComplement F Z

/-- **I.2.13 (i) ⇒ local vanishing of `H_Z^0`:** if `ℋ_Z^0(F) = 0` then
`Γ̲_Z(F) = 0`. -/
theorem I_2_13_sheafH_zero_isZero (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (h : IsZero (sheafH_Z_n Z F 0)) :
    IsZero (underlineGammaZ F Z) :=
  (sheafH_Z_zero_isZero_iff Z F).mp h

/-- **I.2.13 (equivalence at degree 0):** `ℋ_Z^0(F) = 0` iff the unit
`F → j_* j^* F` is a monomorphism (kernel vanishes). -/
theorem I_2_13_degree_zero_mono_iff (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    IsZero (sheafH_Z_n Z F 0) ↔ Mono (toComplementPushforward F Z) :=
  (Preadditive.mono_iff_isZero_kernel (toComplementPushforward F Z)).symm

/-- **I.2.13 (equivalence at degree 0–1 via I.2.11):** `ℋ_Z^0 = ℋ_Z^1 = 0` iff
`F → j_* j^* F` is an isomorphism (kernel and cokernel vanish). -/
theorem I_2_13_degree_zero_one_iso_criterion (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (IsZero (sheafH_Z_n Z F 0) ∧ IsZero (sheafH_Z_n Z F 1)) ↔
      IsIso (toComplementPushforward F Z) := by
  rw [isIso_iff_mono_and_epi, ← I_2_13_degree_zero_mono_iff,
    Preadditive.epi_iff_isZero_cokernel]
  rfl

/-- **I.2.14 (degree zero, unit on sections):** vanishing of the kernel sheaf
makes the unit `F → j_* j^* F` injective on every open, in particular on global
sections by taking `U = ⊤`. The target here is the pushforward of the categorical
pullback; its identification with the explicit complement restriction is separate. -/
theorem I_2_14_unit_sections_injective (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (h0 : IsZero (sheafH_Z_n Z F 0))
    (U : Opens X) :
    Function.Injective ((toComplementPushforward F Z).hom.app (op U)).hom := by
  have hmono : Mono (toComplementPushforward F Z) :=
    (I_2_13_degree_zero_mono_iff Z F).mp h0
  exact (AddCommGrpCat.mono_iff_injective _).mp
    ((NatTrans.mono_iff_mono_app _).mp
      ((CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _
        (toComplementPushforward F Z)).mp hmono) (op U))

/-- Supported sections vanish exactly when the explicit restriction to the
complement is injective. This criterion uses the concrete subgroup `gammaZ`. -/
theorem gammaZ_eq_bot_iff_restrict_injective (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    gammaZ F Z = ⊥ ↔ Function.Injective (restrictToComplement F Z ⊤).hom :=
  AddMonoidHom.ker_eq_bot_iff _

end SGA.SGA2.ExposeI
