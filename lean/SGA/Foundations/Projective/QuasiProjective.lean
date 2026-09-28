/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Projective.AmpleLocal
import SGA.Foundations.Projective.Morphisms

/-!
# Quasi-projective morphisms

- `IsQuasiProjective.of_isPullback`: quasi-projective morphisms are stable under base change
  (EGA II 5.3.4 (iii)), the inverse image of a relatively ample line bundle being relatively
  ample (`Scheme.LineBundle.IsRelativelyAmple.of_isPullback`, EGA II 4.6.13 (iii)).
- `IsHQuasiProjective.isQuasiProjective`: an H-quasi-projective morphism (a quasi-compact
  immersion into some `ℙ(σ; S)` followed by the projection) is quasi-projective, the inverse image
  of `𝒪(1)` being relatively ample (EGA II 5.3.2, 4.6.13 (ii)).
- `IsQuasiProjective.comp_isFinite`: a quasi-projective morphism followed by a finite one is
  quasi-projective.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- EGA II 5.3.4 (iii): quasi-projective morphisms are stable under base change. -/
theorem IsQuasiProjective.of_isPullback {X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {fst : X' ⟶ X} {snd : X' ⟶ Y'} (H : IsPullback fst snd f g) [IsQuasiProjective f] :
    IsQuasiProjective snd := by
  obtain ⟨L, hL⟩ := IsQuasiProjective.exists_isRelativelyAmple (f := f)
  exact ⟨MorphismProperty.of_isPullback H inferInstance,
    MorphismProperty.of_isPullback H inferInstance, ⟨_, hL.of_isPullback H⟩⟩

instance IsQuasiProjective.isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsQuasiProjective where
  of_isPullback sq hg := by
    have := hg
    exact IsQuasiProjective.of_isPullback sq

/-- A quasi-projective morphism is quasi-separated. -/
instance (priority := 900) IsQuasiProjective.quasiSeparated (f : X ⟶ Y) [IsQuasiProjective f] :
    QuasiSeparated f :=
  (IsQuasiProjective.exists_isRelativelyAmple (f := f)).choose_spec.quasiSeparated

/-- The composition of a quasi-projective morphism and a finite morphism is quasi-projective, a
line bundle ample relative to the first one being ample relative to the composition. -/
theorem IsQuasiProjective.comp_isFinite (f : X ⟶ Y) (g : Y ⟶ S) [IsQuasiProjective f]
    [IsFinite g] : IsQuasiProjective (f ≫ g) := by
  obtain ⟨L, hL⟩ := IsQuasiProjective.exists_isRelativelyAmple (f := f)
  exact ⟨inferInstance, inferInstance, ⟨L, hL.comp g⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- EGA II 5.3.2: an H-quasi-projective morphism is quasi-projective; the inverse image of `𝒪(1)`
is relatively ample. -/
instance (priority := 900) IsHQuasiProjective.isQuasiProjective (f : X ⟶ S)
    [h : IsHQuasiProjective f] : IsQuasiProjective f := by
  obtain ⟨σ, _, i, _, _, rfl⟩ := h.exists_isImmersion
  refine ⟨inferInstance, inferInstance, ⟨(ProjectiveSpace.twistingSheaf σ S).pullback i, ?_⟩⟩
  have hO := ProjectiveSpace.isRelativelyAmple_twistingSheaf (σ := σ) S
  refine ⟨inferInstance, fun V hV ↦ ?_⟩
  change (((ProjectiveSpace.twistingSheaf σ S).pullback i).pullback
    (i ⁻¹ᵁ (ℙ(σ; S) ↘ S) ⁻¹ᵁ V).ι).IsAmple
  rw [← Scheme.LineBundle.pullback_comp, ← morphismRestrict_ι,
    Scheme.LineBundle.pullback_comp]
  exact (hO.2 V hV).pullback_of_isImmersion _

end AlgebraicGeometry
