/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Projective.ProjectiveSpaceHom

/-!
# Projective morphisms

We define projective morphisms in the sense of Hartshorne (II.4): `f : X ⟶ S` is *H-projective*
(Stacks 01W8) if it factors as a closed immersion `X ⟶ ℙ(σ; S)` followed by the projection, for
some finite `σ`; and *H-quasi-projective* if it factors as a quasi-compact immersion into some
`ℙ(σ; S)`.

EGA II 5.5.2 calls `f` projective if `X` is isomorphic to a closed subscheme of `ℙ(ℰ)` for a
quasi-coherent `𝒪_S`-module of finite type `ℰ`; over an affine base the two notions agree, and
over a quasi-compact base EGA-projective means proper and quasi-projective (EGA II 5.5.3). We do
not have `ℙ(ℰ)`; we prove that H-projective morphisms are proper and quasi-projective
(`IsHProjective.isProper`, `IsHProjective.isQuasiProjective`, the easy half of EGA II 5.5.3).

## Main results

- `IsHProjective.isProper`: H-projective morphisms are proper (EGA II 5.5.3).
- `IsHProjective.isQuasiProjective`: H-projective morphisms are quasi-projective, `𝒪(1)` being
  relatively ample (EGA II 5.5.3, 4.6.18).
- `IsHProjective.comp_isClosedImmersion`: a closed immersion followed by an H-projective morphism
  is H-projective.
- `IsHProjective.isStableUnderBaseChange`: H-projective morphisms are stable under base change
  (EGA II 5.5.5 (iii)).
- The same for H-quasi-projective morphisms, except quasi-projectivity.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y S T : Scheme.{u}}

/-- A morphism `f : X ⟶ S` is H-projective (Hartshorne II.4, Stacks 01W8) if it factors as a
closed immersion `X ⟶ ℙ(σ; S)` followed by the projection `ℙ(σ; S) ⟶ S`, for some finite
type `σ` (`ℙ(Fin (n + 1); S) = ℙⁿ_S`). -/
@[mk_iff]
class IsHProjective (f : X ⟶ S) : Prop where
  exists_isClosedImmersion : ∃ (σ : Type u) (_ : Finite σ) (i : X ⟶ ℙ(σ; S)),
    IsClosedImmersion i ∧ i ≫ ℙ(σ; S) ↘ S = f

/-- A morphism `f : X ⟶ S` is H-quasi-projective (Stacks 01W8) if it factors as a quasi-compact
immersion `X ⟶ ℙ(σ; S)` followed by the projection, for some finite type `σ`. -/
@[mk_iff]
class IsHQuasiProjective (f : X ⟶ S) : Prop where
  exists_isImmersion : ∃ (σ : Type u) (_ : Finite σ) (i : X ⟶ ℙ(σ; S)),
    IsImmersion i ∧ QuasiCompact i ∧ i ≫ ℙ(σ; S) ↘ S = f

namespace IsHProjective

/-- The projective space over `S` is H-projective over `S`. -/
instance (σ : Type u) [Finite σ] : IsHProjective (ℙ(σ; S) ↘ S) :=
  ⟨σ, inferInstance, 𝟙 _, inferInstance, Category.id_comp _⟩

/-- EGA II 5.5.3: H-projective morphisms are proper. -/
instance (priority := 900) isProper (f : X ⟶ S) [h : IsHProjective f] : IsProper f := by
  obtain ⟨σ, _, i, _, rfl⟩ := h
  infer_instance

/-- EGA II 5.5.3, 4.6.18: H-projective morphisms are quasi-projective; the inverse image of
`𝒪(1)` is relatively ample. -/
instance (priority := 900) isQuasiProjective (f : X ⟶ S) [h : IsHProjective f] :
    IsQuasiProjective f := by
  obtain ⟨σ, _, i, _, rfl⟩ := h
  exact IsQuasiProjective.comp_of_isAffineHom i _

instance (priority := 900) isHQuasiProjective (f : X ⟶ S) [h : IsHProjective f] :
    IsHQuasiProjective f := by
  obtain ⟨σ, _, i, _, rfl⟩ := h
  exact ⟨σ, inferInstance, i, inferInstance, inferInstance, rfl⟩

/-- A closed immersion followed by an H-projective morphism is H-projective. -/
instance comp_isClosedImmersion (i : Y ⟶ X) (f : X ⟶ S) [IsClosedImmersion i]
    [h : IsHProjective f] : IsHProjective (i ≫ f) := by
  obtain ⟨σ, _, j, _, rfl⟩ := h
  exact ⟨σ, inferInstance, i ≫ j, inferInstance, Category.assoc _ _ _⟩

variable {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}

set_option backward.isDefEq.respectTransparency.types false in
/-- EGA II 5.5.5 (iii): H-projective morphisms are stable under base change. -/
theorem of_isPullback (H : IsPullback fst snd f g) [h : IsHProjective f] : IsHProjective snd := by
  obtain ⟨σ, _, i, hi, rfl⟩ := h
  have hpb := ProjectiveSpace.isPullback_map (σ := σ) (S := S) g
  let i' : P ⟶ ℙ(σ; T) := hpb.lift (fst ≫ i) snd (by simp [H.w])
  have top : IsPullback fst i' i (ProjectiveSpace.map S g) :=
    IsPullback.of_bot (by simpa [i'] using H) (hpb.lift_fst _ _ _).symm hpb
  exact ⟨σ, inferInstance, i', MorphismProperty.of_isPullback top hi, hpb.lift_snd _ _ _⟩

instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsHProjective where
  of_isPullback sq hg := of_isPullback (h := hg) sq

end IsHProjective

namespace IsHQuasiProjective

instance (priority := 900) (f : X ⟶ S) [h : IsHQuasiProjective f] : LocallyOfFiniteType f := by
  obtain ⟨σ, _, i, _, _, rfl⟩ := h
  infer_instance

instance (priority := 900) (f : X ⟶ S) [h : IsHQuasiProjective f] : IsSeparated f := by
  obtain ⟨σ, _, i, _, _, rfl⟩ := h
  infer_instance

/-- A quasi-compact immersion followed by an H-quasi-projective morphism is H-quasi-projective. -/
instance comp_isImmersion (i : Y ⟶ X) (f : X ⟶ S) [IsImmersion i] [QuasiCompact i]
    [h : IsHQuasiProjective f] : IsHQuasiProjective (i ≫ f) := by
  obtain ⟨σ, _, j, _, _, rfl⟩ := h
  exact ⟨σ, inferInstance, i ≫ j, inferInstance, inferInstance, Category.assoc _ _ _⟩

variable {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}

set_option backward.isDefEq.respectTransparency.types false in
/-- H-quasi-projective morphisms are stable under base change. -/
theorem of_isPullback (H : IsPullback fst snd f g) [h : IsHQuasiProjective f] :
    IsHQuasiProjective snd := by
  obtain ⟨σ, _, i, hi, hi', rfl⟩ := h
  have hpb := ProjectiveSpace.isPullback_map (σ := σ) (S := S) g
  let i' : P ⟶ ℙ(σ; T) := hpb.lift (fst ≫ i) snd (by simp [H.w])
  have top : IsPullback fst i' i (ProjectiveSpace.map S g) :=
    IsPullback.of_bot (by simpa [i'] using H) (hpb.lift_fst _ _ _).symm hpb
  exact ⟨σ, inferInstance, i', MorphismProperty.of_isPullback top hi,
    MorphismProperty.of_isPullback top hi', hpb.lift_snd _ _ _⟩

instance isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsHQuasiProjective where
  of_isPullback sq hg := of_isPullback (h := hg) sq

end IsHQuasiProjective

end AlgebraicGeometry
