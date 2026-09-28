/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.CleavageConstructions

/-!
# SGA 1, Exposé VI, end of VI.8: change of base in terms of pseudofunctors

SGA leaves to the reader "to interpret, in terms of pseudofunctors, the notion of inverse image of
a cloven category `𝒳` over `E` by a change of base functor `L : E' ⥤ E`". The answer: the
pseudofunctor of `𝒳' = 𝒳 ×_E E'` with the induced cleavage is the pseudofunctor of `𝒳` composed
with `L`. Precisely, the isomorphisms `i_S : 𝒳'_S ≅ 𝒳_{L S}` (`baseChangeFiberIso`) satisfy
`i_R ∘ f^* = (L f)^* ∘ i_S` (`Cleavage.baseChange_pullback_comp`) and send the comparisons
`c_{f,g}` of `𝒳'` to the comparisons `c_{L f, L g}` of `𝒳` (up to the identification
`L(g ≫ f) = L g ≫ L f`, `Cleavage.baseChange_comparison`).
-/

universe v v₁ v₂ u u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E] {D : Type u₂} [Category.{v₂} D]
  {Y : BasedCategory.{v₁, u₁} E} (K : Cleavage Y.p) (L : D ⥤ E)

namespace Cleavage

theorem baseChangeFiberFunctor_obj_eq {S : D} (ξ : Fiber (changeOfBase Y L).p S) :
    (baseChangeFiberFunctor Y.p L S).obj ξ = fiberBase ξ := rfl

/-- End of VI.8: the inverse image functors of the cleavage of `𝒳 ×_E E'` are those of `𝒳` along
`L`: `i_R ∘ f^* = (L f)^* ∘ i_S`. -/
theorem baseChange_pullback_comp {R S : D} (f : R ⟶ S) :
    (K.baseChange L).pullback f ⋙ baseChangeFiberFunctor Y.p L R =
      baseChangeFiberFunctor Y.p L S ⋙ K.pullback (L.map f) := by
  refine CategoryTheory.Functor.ext (fun ξ ↦ Subtype.ext rfl) fun ξ η u ↦ ?_
  apply Subtype.ext
  simp only [Functor.comp_map, fiber_comp_val, fiber_eqToHom_val]
  erw [fiber_eqToHom_val, eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  have h₀ : IsHomLift Y.p (𝟙 (L.obj R)) (((K.baseChange L).pullback f).map u).val.left := by
    have h := BaseChange.isHomLift_left (𝟙 R) ((K.baseChange L).pullback f |>.map u).val
    rwa [L.map_id] at h
  have h₀' : IsHomLift Y.p (𝟙 (L.obj R))
      ((K.pullback (L.map f)).map ((baseChangeFiberFunctor Y.p L S).map u)).val :=
    ((K.pullback (L.map f)).map ((baseChangeFiberFunctor Y.p L S).map u)).property
  refine @IsCartesian.ext _ _ _ _ Y.p _ _ _ _ (L.map f) (K.transport (L.map f) (fiberBase η))
    inferInstance _ _ _ h₀ h₀' ?_
  have h₁ : (((K.baseChange L).pullback f).map u).val.left ≫
      K.transport (L.map f) (fiberBase η) = K.transport (L.map f) (fiberBase ξ) ≫ u.val.left :=
    congrArg BaseChange.Hom.left ((K.baseChange L).transport_naturality f u)
  erw [K.transport_naturality]
  exact h₁

/-- End of VI.8: the comparisons of the cleavage of `𝒳 ×_E E'` are the comparisons
`c_{L f, L g}` of `𝒳` (up to the identification `L (g ≫ f) = L g ≫ L f`). -/
theorem baseChange_comparison {U T S : D} (f : T ⟶ S) (g : U ⟶ T)
    (ξ : Fiber (changeOfBase Y L).p S) :
    ((K.baseChange L).comparison f g ξ).val.left ≫
        eqToHom (congrArg (fun k ↦ ((K.pullback k).obj (fiberBase ξ)).val) (L.map_comp g f)) =
      (K.comparison (L.map f) (L.map g) (fiberBase ξ)).val := by
  have h₀ : IsHomLift Y.p (𝟙 (L.obj U)) (((K.baseChange L).comparison f g ξ).val.left ≫
      eqToHom (congrArg (fun k ↦ ((K.pullback k).obj (fiberBase ξ)).val) (L.map_comp g f))) := by
    have h := BaseChange.isHomLift_left (𝟙 U) ((K.baseChange L).comparison f g ξ).val
    rw [L.map_id] at h
    exact IsHomLift.eqToHom_comp_lift (p := Y.p) (𝟙 (L.obj U))
      ((K.baseChange L).comparison f g ξ).val.left _
  have h₀' : IsHomLift Y.p (𝟙 (L.obj U)) (K.comparison (L.map f) (L.map g) (fiberBase ξ)).val :=
    (K.comparison (L.map f) (L.map g) (fiberBase ξ)).property
  refine @IsCartesian.ext _ _ _ _ Y.p _ _ _ _ (L.map g ≫ L.map f)
    (K.transport (L.map g ≫ L.map f) (fiberBase ξ)) inferInstance _ _ _ h₀ h₀' ?_
  have h₁ : ((K.baseChange L).comparison f g ξ).val.left ≫
      K.transport (L.map (g ≫ f)) (fiberBase ξ) =
        K.transport (L.map g) (fiberBase ((K.baseChange L).pullback f |>.obj ξ)) ≫
          K.transport (L.map f) (fiberBase ξ) :=
    congrArg BaseChange.Hom.left ((K.baseChange L).comparison_fac f g ξ)
  rw [K.transport_congr (L.map_comp g f)] at h₁
  erw [Category.assoc, Cleavage.comparison_fac]
  exact h₁

end Cleavage

end SGA.SGA1.ExposeVI
