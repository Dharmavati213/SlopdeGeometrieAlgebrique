/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.SteinFactorization

/-!
# Flat base change for `f_* 𝒪_X`

Flat base change in degree `0` for the structure sheaf (EGA III 1.4.15; Stacks Tag 02KH): for
`f : X ⟶ Y` quasi-compact and quasi-separated and `g : Y' ⟶ Y` flat, the formation of `f_* 𝒪_X`
commutes with the base change `g`:

* `CohomologyAux.isPushout_app_pullback_snd`: for affine `V ⊆ Y` and `V' ⊆ Y'` with `g(V') ⊆ V`,
  `Γ(X ×_Y Y', f'⁻¹ V') = Γ(X, f⁻¹ V) ⊗_{Γ(Y, V)} Γ(Y', V')`; this is mathlib's
  `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`, and `isPushout_app_of_isPullback` is
  the same for an arbitrary pullback square;
* `CohomologyAux.isIso_app_pullback_snd`: if `𝒪_Y ≅ f_* 𝒪_X` then `𝒪_{Y'} ≅ f'_* 𝒪_{X'}`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

section FlatBaseChange

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- **Flat base change for `f_* 𝒪_X` over affine opens**, for an arbitrary pullback square
(EGA III 1.4.15, degree `0`; Stacks 02KH): let `P` (with `fst : P ⟶ X'`, `snd : P ⟶ Y'`) be a
pullback of `f : X' ⟶ Y` quasi-compact and quasi-separated along `g : Y' ⟶ Y` flat, and
`O ⊆ Y`, `O' ⊆ Y'` affine with `g(O') ⊆ O`. Then the square of rings `Γ(Y, O) → Γ(X', f⁻¹ O)`,
`Γ(Y, O) → Γ(Y', O')` is a pushout with fourth vertex `Γ(P, snd⁻¹ O')`. (Mathlib's
`isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`.) Working with an abstract pullback
square can keep elaboration fast when `P` is given by other means. -/
theorem isPushout_app_of_isPullback {P X' Y Y' : Scheme.{u}} {fst : P ⟶ X'} {snd : P ⟶ Y'}
    {f : X' ⟶ Y} {g : Y' ⟶ Y} (h : IsPullback fst snd f g) [Flat g] [QuasiCompact f]
    [QuasiSeparated f] {O : Y.Opens} (hO : IsAffineOpen O) {O' : Y'.Opens} (hO' : IsAffineOpen O')
    (hOO' : O' ≤ g ⁻¹ᵁ O) :
    IsPushout (f.app O) (g.appLE O O' hOO')
      (fst.appLE (f ⁻¹ᵁ O) (snd ⁻¹ᵁ O') (by
        rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]
        exact snd.preimage_mono hOO'))
      (snd.app O') := by
  have hUY : snd ⁻¹ᵁ O' = fst ⁻¹ᵁ (f ⁻¹ᵁ O) ⊓ snd ⁻¹ᵁ O' := by
    refine (inf_eq_right.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage]
    exact snd.preimage_mono hOO'
  have h' := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right h hOO' le_rfl hUY hO hO'
    (f.isCompact_preimage hO.isCompact) (f.isQuasiSeparated_preimage hO.isQuasiSeparated)
  rw [isIso_pushoutSection_iff] at h'
  simpa only [Scheme.Hom.app_eq_appLE] using h'

/-- **Flat base change for `f_* 𝒪_X` over affine opens** (EGA III 1.4.15, degree `0`; Stacks
02KH): for `f` quasi-compact and quasi-separated, `g` flat, `V ⊆ Y` and `V' ⊆ Y'` affine with
`g(V') ⊆ V`, the square `Γ(Y, V) → Γ(X, f⁻¹ V)`, `Γ(Y, V) → Γ(Y', V')` of rings is a pushout
with fourth vertex `Γ(X ×_Y Y', pr₂⁻¹ V')`: `Γ(X', f'⁻¹ V') = Γ(X, f⁻¹ V) ⊗_{Γ(Y, V)} Γ(Y', V')`.
(The case of the canonical pullback in `isPushout_app_of_isPullback`.) -/
theorem isPushout_app_pullback_snd [Flat g] [QuasiCompact f] [QuasiSeparated f] {V : Y.Opens}
    (hV : IsAffineOpen V) {V' : Y'.Opens} (hV' : IsAffineOpen V') (hVV' : V' ≤ g ⁻¹ᵁ V) :
    IsPushout (f.app V) (g.appLE V V' hVV')
      ((pullback.fst f g).appLE (f ⁻¹ᵁ V) (pullback.snd f g ⁻¹ᵁ V') (by
        rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
        exact (pullback.snd f g).preimage_mono hVV'))
      ((pullback.snd f g).app V') :=
  isPushout_app_of_isPullback (IsPullback.of_hasPullback f g) hV hV' hVV'

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
