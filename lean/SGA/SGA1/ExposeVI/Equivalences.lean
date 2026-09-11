/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Category.Cat.Limit

/-!
# SGA 1, Exposé VI, §1: universes and equivalences of categories

Lean universe levels replace the set-theoretic universes of the text;
`Category.{v} C` allows separate universes for objects and morphisms.
Categories, functor categories, opposites, and small limits of small
categories are supplied by mathlib. We expose the equivalence criterion
in SGA's elementary language and construct a quasi-inverse with prescribed
object preimages and prescribed counit, as required later in VI.4.2.

Both quasi-inverse identities are required. The English draft's sentence
listing only `GF ≅ id` is insufficient; see `docs/formalization.md`.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- VI.1: faithfulness means injectivity on each set of morphisms. -/
theorem faithful_iff_map_injective (F : C ⥤ D) : F.Faithful ↔
    ∀ X Y, Function.Injective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  ⟨fun _ _ _ ↦ F.map_injective, fun h ↦ ⟨fun {X Y} ↦ h X Y⟩⟩

/-- VI.1: full faithfulness means bijectivity on each set of morphisms. -/
theorem fullyFaithful_iff_map_bijective (F : C ⥤ D) : (F.Full ∧ F.Faithful) ↔
    ∀ X Y, Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  constructor
  · rintro ⟨hfull, hfaithful⟩ X Y
    exact ⟨F.map_injective, F.map_surjective⟩
  · intro h
    exact ⟨⟨fun {X Y} ↦ (h X Y).surjective⟩, ⟨fun {X Y} ↦ (h X Y).injective⟩⟩

/-- VI.1: an equivalence is fully faithful and essentially surjective. -/
theorem isEquivalence_iff (F : C ⥤ D) : F.IsEquivalence ↔
    (∀ X Y, Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) ∧
      ∀ Y, ∃ X, Nonempty (F.obj X ≅ Y) := by
  constructor
  · intro h
    exact ⟨fun _ _ ↦ ⟨F.map_injective, F.map_surjective⟩,
      fun Y ↦ ⟨F.objPreimage Y, ⟨F.objObjPreimageIso Y⟩⟩⟩
  · rintro ⟨hmap, hobj⟩
    obtain ⟨hfull, hfaithful⟩ := (fullyFaithful_iff_map_bijective F).mpr hmap
    exact { essSurj := ⟨hobj⟩ }

/-- VI.1: the equivalence criterion using a two-sided quasi-inverse. -/
theorem isEquivalence_iff_quasiInverse (F : C ⥤ D) : F.IsEquivalence ↔
    ∃ G : D ⥤ C, Nonempty (𝟭 C ≅ F ⋙ G) ∧ Nonempty (G ⋙ F ≅ 𝟭 D) := by
  constructor
  · intro h
    exact ⟨F.asEquivalence.inverse, ⟨F.asEquivalence.unitIso⟩,
      ⟨F.asEquivalence.counitIso⟩⟩
  · rintro ⟨G, ⟨η⟩, ⟨ε⟩⟩
    exact Functor.IsEquivalence.mk' G η ε

section Choices

variable (F : C ⥤ D) [F.Full] [F.Faithful] (g : D → C) (ε : ∀ Y, F.obj (g Y) ≅ Y)

/-- VI.1: extend chosen inverse images of objects to a quasi-inverse functor.
Unlike `Functor.inv`, this construction keeps the supplied choices. -/
noncomputable def inverseOfChoices : D ⥤ C where
  obj := g
  map {X Y} f := F.preimage ((ε X).hom ≫ f ≫ (ε Y).inv)
  map_id X := by apply F.map_injective; simp
  map_comp f h := by apply F.map_injective; simp

/-- VI.1: the prescribed object isomorphisms form the counit. -/
noncomputable def counitOfChoices : inverseOfChoices F g ε ⋙ F ≅ 𝟭 D :=
  NatIso.ofComponents ε (by simp [inverseOfChoices])

/-- VI.1: the corresponding unit, recovered by full faithfulness. -/
noncomputable def unitOfChoices : 𝟭 C ≅ F ⋙ inverseOfChoices F g ε :=
  NatIso.ofComponents (fun X ↦ (F.preimageIso (ε (F.obj X))).symm)
    (fun f ↦ F.map_injective (by simp [inverseOfChoices]))

/-- VI.1: prescribed preimages and isomorphisms give an equivalence. -/
noncomputable def equivalenceOfChoices : C ≌ D where
  functor := F
  inverse := inverseOfChoices F g ε
  unitIso := unitOfChoices F g ε
  counitIso := counitOfChoices F g ε
  functor_unitIso_comp X := by
    change F.map (F.preimage (ε (F.obj X)).inv) ≫ (ε (F.obj X)).hom = _
    simp

/-- VI.1: naturality of the prescribed counit uniquely determines the map on arrows. -/
theorem inverseOfChoices_map_unique {X Y : D} (f : X ⟶ Y) (u : g X ⟶ g Y)
    (hu : F.map u ≫ (ε Y).hom = (ε X).hom ≫ f) :
    u = (inverseOfChoices F g ε).map f := by
  apply F.map_injective
  dsimp [inverseOfChoices]
  rw [F.map_preimage, ← Category.assoc, ← hu]
  simp

end Choices

/-- VI.1, last assertion: once a counit is fixed, precisely one unit satisfies
the triangle identity. Existence uses mathlib's adjointification. -/
theorem existsUnique_compatible_unit (F : C ⥤ D) (G : D ⥤ C)
    (η₀ : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) :
    ∃! η : 𝟭 C ≅ F ⋙ G,
      ∀ X, F.map (η.hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 (F.obj X) := by
  let e := CategoryTheory.Equivalence.mk F G η₀ ε
  have : F.Faithful := e.faithful_functor
  refine ⟨e.unitIso, e.functor_unitIso_comp, ?_⟩
  intro η hη
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply F.map_injective
  apply (cancel_mono (ε.hom.app (F.obj X))).mp
  exact (hη X).trans (e.functor_unitIso_comp X).symm

/-- VI.1, last paragraph: for a two-sided quasi-inverse the two triangle
compatibility conditions are equivalent. -/
theorem triangle_identities_iff (F : C ⥤ D) (G : D ⥤ C)
    (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) :
    (∀ X, F.map (η.hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 (F.obj X)) ↔
      (∀ Y, η.hom.app (G.obj Y) ≫ G.map (ε.hom.app Y) = 𝟙 (G.obj Y)) := by
  constructor
  · intro h
    let e : C ≌ D :=
      { functor := F, inverse := G, unitIso := η, counitIso := ε,
        functor_unitIso_comp := h }
    exact e.unit_inverse_comp
  · intro h
    let e : D ≌ C :=
      { functor := G, inverse := F, unitIso := ε.symm, counitIso := η.symm,
        functor_unitIso_comp := fun Y ↦ by
          let i := η.app (G.obj Y) ≪≫ G.mapIso (ε.app Y)
          have hi : i.hom = 𝟙 _ := h Y
          change i.inv = 𝟙 _
          calc
            i.inv = i.inv ≫ 𝟙 _ := (Category.comp_id _).symm
            _ = i.inv ≫ i.hom := by rw [hi]
            _ = 𝟙 _ := i.inv_hom_id }
    intro X
    let i := F.mapIso (η.app X) ≪≫ ε.app (F.obj X)
    have hi : i.inv = 𝟙 _ := e.unit_inverse_comp X
    change i.hom = 𝟙 _
    calc
      i.hom = i.hom ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = i.hom ≫ i.inv := by rw [hi]
      _ = 𝟙 _ := i.hom_inv_id

/-- VI.1: small limits exist in the category of small categories. -/
theorem smallCategories_have_limits : CategoryTheory.Limits.HasLimitsOfSize.{u₁, u₁}
    Cat.{u₁, u₁} := inferInstance

end SGA.SGA1.ExposeVI
