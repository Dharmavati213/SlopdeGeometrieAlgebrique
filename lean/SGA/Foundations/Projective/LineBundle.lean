/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import SGA.Foundations.Ample

/-!
# Inverse images of sections of line bundles, and relative ampleness

We complement `SGA.Foundations.Ample` (line bundles presented by transition functions) with the
functoriality of sections and of non-vanishing loci, and with the permanence properties of
(relative) ampleness that do not need the extension of sections over non-affine opens.

## Main definitions and results

- `Scheme.LineBundle.sections.pullback`: the inverse image of a section of `L^{⊗n}`, whose
  non-vanishing locus is the inverse image of the non-vanishing locus
  (`Scheme.LineBundle.nonvanishingLocus_pullback`).
- `Scheme.LineBundle.pullback_comp`: `(g ∘ f)^* L = f^* g^* L`.
- `Scheme.LineBundle.IsAmple.pullback`: the inverse image of an ample line bundle under an affine
  morphism is ample (EGA II 4.5.10 (ii) for affine morphisms).
- `Scheme.LineBundle.IsRelativelyAmple.pullback`: if `L` is `f`-ample and `g` is affine, then
  `g^* L` is `f ∘ g`-ample (EGA II 4.6.13 (i), for affine `g`).
- `Scheme.LineBundle.isRelativelyAmple_of_isAffineHom`: `L` is `f`-ample as soon as the
  non-vanishing loci of global sections of positive powers of `L`, affine over the base, cover
  `X` (EGA II 4.6.6, sufficiency, in the form of Stacks 01VJ).
- `IsQuasiProjective.comp_of_isAffineHom`: an affine morphism of finite type followed by a
  quasi-projective morphism is quasi-projective; in particular closed subschemes of
  quasi-projective schemes are quasi-projective (EGA II 5.3.4 (i)).
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

namespace Scheme

namespace LineBundle

variable {X Y Z : Scheme.{u}} (L : X.LineBundle)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image `f^* s` of a section `s` of `L^{⊗n}`, a section of `(f^* L)^{⊗n}`. -/
noncomputable def sections.pullback (f : Y ⟶ X) {n : ℕ} (s : L.sections n) :
    (L.pullback f).sections n :=
  ⟨fun i ↦ f.appLE (L.U i) (f ⁻¹ᵁ L.U i) le_rfl (s.1 i), fun i j ↦ by
    have := congrArg (f.appLE (L.U i ⊓ L.U j) (f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j)
      f.preimage_inf.ge).hom (s.2 i j)
    simp only [map_mul, map_pow, ← CommRingCat.comp_apply] at this
    simp only [Scheme.Hom.map_appLE] at this
    simp only [LineBundle.pullback, Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply]
    simp only [Scheme.Hom.appLE_map]
    exact this⟩

@[simp]
lemma sections.pullback_apply (f : Y ⟶ X) {n : ℕ} (s : L.sections n) (i : L.ι) :
    (s.pullback L f).1 i = f.appLE (L.U i) (f ⁻¹ᵁ L.U i) le_rfl (s.1 i) :=
  rfl

/-- The non-vanishing locus of `f^* s` is the inverse image of the non-vanishing locus of `s`. -/
@[simp]
lemma nonvanishingLocus_pullback (f : Y ⟶ X) {n : ℕ} (s : L.sections n) :
    (L.pullback f).nonvanishingLocus (s.pullback L f) = f ⁻¹ᵁ L.nonvanishingLocus s := by
  simp only [nonvanishingLocus, Scheme.Hom.preimage_iSup]
  refine iSup_congr fun (i : L.ι) ↦ ?_
  change Y.basicOpen (f.appLE (L.U i) (f ⁻¹ᵁ L.U i) le_rfl (s.1 i)) = _
  rw [Scheme.basicOpen_appLE, inf_eq_right]
  exact f.preimage_mono (X.basicOpen_le _)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of line bundles is compatible with composition. -/
lemma pullback_comp (f : Z ⟶ Y) (g : Y ⟶ X) :
    L.pullback (f ≫ g) = (L.pullback g).pullback f := by
  simp only [pullback]
  congr
  funext i j
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE]
  rfl

section Ample

variable {L}

/-- EGA II 4.5.10 (ii), for affine morphisms: the inverse image of an ample line bundle under an
affine morphism is ample. -/
theorem IsAmple.pullback (hL : L.IsAmple) (f : Y ⟶ X) [IsAffineHom f] :
    (L.pullback f).IsAmple := by
  have := hL.1
  refine ⟨QuasiCompact.compactSpace_of_compactSpace f, fun y ↦ ?_⟩
  obtain ⟨n, hn, s, hs, hs'⟩ := hL.2 (f y)
  exact ⟨n, hn, s.pullback L f, by simpa using hs, by simpa using hs'.preimage f⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- EGA II 4.6.13 (i), for affine morphisms: if `L` is ample relative to `f` and `g` is affine,
then `g^* L` is ample relative to `g ≫ f`. -/
theorem IsRelativelyAmple.pullback {f : X ⟶ Y} (hL : L.IsRelativelyAmple f) (g : Z ⟶ X)
    [IsAffineHom g] : (L.pullback g).IsRelativelyAmple (g ≫ f) := by
  have := hL.1
  refine ⟨inferInstance, fun V hV ↦ ?_⟩
  have hg : IsAffineHom (g ∣_ (f ⁻¹ᵁ V)) := IsZariskiLocalAtTarget.restrict ‹_› _
  have h : ((g ≫ f) ⁻¹ᵁ V).ι ≫ g = (g ∣_ (f ⁻¹ᵁ V)) ≫ (f ⁻¹ᵁ V).ι :=
    (morphismRestrict_ι g (f ⁻¹ᵁ V)).symm
  rw [← pullback_comp, show L.pullback (((g ≫ f) ⁻¹ᵁ V).ι ≫ g) =
    L.pullback ((g ∣_ (f ⁻¹ᵁ V)) ≫ (f ⁻¹ᵁ V).ι) from congrArg _ h, pullback_comp]
  exact @IsAmple.pullback _ _ _ (hL.2 V hV) _ hg

/-- Stacks 01VJ (sufficiency; compare EGA II 4.6.6): let `f : X ⟶ Y` be quasi-compact, and let
`sₖ` be sections of positive powers of `L` whose non-vanishing loci `X_{sₖ}` cover `X` and are
affine over `Y`. Then `L` is ample relative to `f`. -/
theorem isRelativelyAmple_of_isAffineHom (f : X ⟶ Y) [QuasiCompact f] {κ : Type*}
    (n : κ → ℕ) (hn : ∀ k, 0 < n k) (s : ∀ k, L.sections (n k))
    (hcov : ∀ x, ∃ k, x ∈ L.nonvanishingLocus (s k))
    (haff : ∀ k, IsAffineHom ((L.nonvanishingLocus (s k)).ι ≫ f)) :
    L.IsRelativelyAmple f := by
  refine ⟨inferInstance, fun V hV ↦ ⟨?_, fun y ↦ ?_⟩⟩
  · exact isCompact_iff_compactSpace.mp (f.isCompact_preimage hV.isCompact)
  obtain ⟨k, hk⟩ := hcov y.1
  refine ⟨n k, hn k, (s k).pullback L (f ⁻¹ᵁ V).ι, by rw [nonvanishingLocus_pullback]; exact hk,
    ?_⟩
  rw [nonvanishingLocus_pullback, ← (f ⁻¹ᵁ V).ι.isAffineOpen_iff_of_isOpenImmersion,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have := (hV.preimage ((L.nonvanishingLocus (s k)).ι ≫ f))
  rw [← (L.nonvanishingLocus (s k)).ι.isAffineOpen_iff_of_isOpenImmersion,
    Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι] at this
  rwa [inf_comm]

end Ample

end LineBundle

end Scheme

variable {X Y Z : Scheme.{u}}

/-- EGA II 5.3.4 (i), for affine morphisms: an affine morphism of finite type (for example a
closed immersion) followed by a quasi-projective morphism is quasi-projective. -/
theorem IsQuasiProjective.comp_of_isAffineHom (g : Z ⟶ X) (f : X ⟶ Y) [IsAffineHom g]
    [LocallyOfFiniteType g] [IsQuasiProjective f] : IsQuasiProjective (g ≫ f) := by
  obtain ⟨L, hL⟩ := IsQuasiProjective.exists_isRelativelyAmple (f := f)
  exact ⟨inferInstance, inferInstance, ⟨_, hL.pullback g⟩⟩

end AlgebraicGeometry
