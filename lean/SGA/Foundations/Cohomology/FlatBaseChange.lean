/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.SteinFactorization

/-!
# Flat base change for `f_* 𝒪_X`

Flat base change in degree `0` for the structure sheaf (EGA III 1.4.15; Stacks Tag 02KH): for
`f : X ⟶ Y` quasi-compact and quasi-separated and `g : Y' ⟶ Y` flat, the formation of `f_* 𝒪_X`
commutes with the base change `g`:

* `CohomologyAux.isPushout_app_pullback_snd`: for affine `V ⊆ Y` and `V' ⊆ Y'` with `g(V') ⊆ V`,
  `Γ(X ×_Y Y', f'⁻¹ V') = Γ(X, f⁻¹ V) ⊗_{Γ(Y, V)} Γ(Y', V')`; this is mathlib's
  `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`;
* `CohomologyAux.isIso_app_pullback_snd`: if `𝒪_Y ≅ f_* 𝒪_X` then `𝒪_{Y'} ≅ f'_* 𝒪_{X'}`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

section FlatBaseChange

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- **Flat base change for `f_* 𝒪_X` over affine opens** (EGA III 1.4.15, degree `0`; Stacks
02KH): for `f` quasi-compact and quasi-separated, `g` flat, `V ⊆ Y` and `V' ⊆ Y'` affine with
`g(V') ⊆ V`, the square `Γ(Y, V) → Γ(X, f⁻¹ V)`, `Γ(Y, V) → Γ(Y', V')` of rings is a pushout
with fourth vertex `Γ(X ×_Y Y', pr₂⁻¹ V')`: `Γ(X', f'⁻¹ V') = Γ(X, f⁻¹ V) ⊗_{Γ(Y, V)} Γ(Y', V')`.
(Mathlib's `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`.) -/
theorem isPushout_app_pullback_snd [Flat g] [QuasiCompact f] [QuasiSeparated f] {V : Y.Opens}
    (hV : IsAffineOpen V) {V' : Y'.Opens} (hV' : IsAffineOpen V') (hVV' : V' ≤ g ⁻¹ᵁ V) :
    IsPushout (f.app V) (g.appLE V V' hVV')
      ((pullback.fst f g).appLE (f ⁻¹ᵁ V) (pullback.snd f g ⁻¹ᵁ V') (by
        rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
        exact (pullback.snd f g).preimage_mono hVV'))
      ((pullback.snd f g).app V') := by
  have hUY : pullback.snd f g ⁻¹ᵁ V' =
      pullback.fst f g ⁻¹ᵁ (f ⁻¹ᵁ V) ⊓ pullback.snd f g ⁻¹ᵁ V' := by
    refine (inf_eq_right.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
    exact (pullback.snd f g).preimage_mono hVV'
  have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f g) hVV' le_rfl hUY hV hV'
    (f.isCompact_preimage hV.isCompact) (f.isQuasiSeparated_preimage hV.isQuasiSeparated)
  rw [isIso_pushoutSection_iff] at h
  simpa only [Scheme.Hom.app_eq_appLE] using h

/-- **`𝒪_Y ≅ f_* 𝒪_X` is stable under flat base change** (EGA III 1.4.15): for `f` quasi-compact
and quasi-separated with `f^♯ : 𝒪_Y → f_* 𝒪_X` an isomorphism and `g : Y' ⟶ Y` flat, the base
change `f' : X ×_Y Y' ⟶ Y'` again has `f'^♯` an isomorphism. -/
theorem isIso_app_pullback_snd [Flat g] [QuasiCompact f] [QuasiSeparated f]
    (hf : ∀ V : Y.Opens, IsIso (f.app V)) (V' : Y'.Opens) :
    IsIso ((pullback.snd f g).app V') := by
  refine isIso_app_of_basis (pullback.snd f g) (fun V' y' hy' ↦ ?_) V'
  obtain ⟨V, hV, hyV, -⟩ : ∃ V : Y.Opens, IsAffineOpen V ∧ g y' ∈ V ∧ V ≤ ⊤ :=
    Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (show g y' ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨W, hW, hyW, hWV⟩ := Opens.isBasis_iff_nbhd.mp Y'.isBasis_affineOpens
    (show y' ∈ V' ⊓ g ⁻¹ᵁ V from ⟨hy', hyV⟩)
  have h := isPushout_app_pullback_snd f g hV hW (hWV.trans inf_le_right)
  have := hf V
  exact ⟨W, hyW, hWV.trans inf_le_left, h.isIso_inr_of_isIso⟩

end FlatBaseChange

end AlgebraicGeometry.CohomologyAux
