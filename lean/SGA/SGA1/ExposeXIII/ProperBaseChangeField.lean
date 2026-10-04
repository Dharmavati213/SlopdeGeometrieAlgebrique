/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Fields.GeometricallyConnected
import SGA.SGA1.ExposeIX.ConnectedFibres
import SGA.SGA1.ExposeIX.ExactSequence

/-!
# Sections of étale schemes under extension of a separably closed field

Used in the proof of XIII 1.4 (`SGA.SGA1.ExposeXIII.ProperBaseChangeRepresentable`). Let `k` be a
separably closed field and `Ω ⊇ k` an algebraically closed field. Then `Spec Ω ⟶ Spec k` has
geometrically connected fibres (`geometricallyConnected_specMap_of_isSepClosed`): it factors
through the algebraic closure `k'` of `k` in `Ω`, which is purely inseparable over `k` (so
`Spec k' ⟶ Spec k` is a universal homeomorphism,
`ExposeIX.universally_isHomeomorph_of_universallyClosed`), and `Spec Ω` is geometrically connected
over the algebraically closed `k'` (`AlgebraicGeometry.geometricallyConnected_of_isAlgClosed`).
By IX.3.4
(`ExposeIX.existsUnique_hom_of_geometricallyConnected`), for a `k`-scheme `T`, every
morphism `T ⊗_k Ω ⟶ E` over `T` into an étale `T`-scheme comes from `T`
(`exists_hom_of_isPullback_specMap_of_isSepClosed`; Stacks 0A3I for represented sheaves; for
every sheaf it follows from xiii3's Stacks 0A3H,
`AlgebraicGeometry.Scheme.isIso_etaleAdjunction_unit_app_of_geometricallyConnected`, and
`geometricallyConnected_specMap_of_isSepClosed`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXIII

open ExposeIX

/-- `Spec Ω ⟶ Spec k` has geometrically connected fibres when `k` is separably closed and `Ω` is
algebraically closed. -/
theorem geometricallyConnected_specMap_of_isSepClosed (k Ω : Type u) [Field k] [IsSepClosed k]
    [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
  let k' := algebraicClosure k Ω
  have : IsAlgClosed k' := IsAlgClosure.isAlgClosed k
  let a := Spec.map (CommRingCat.ofHom (algebraMap k' Ω))
  let b := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have hab : a ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
    rw [← Spec.map_comp]
    congr 1
  have : ConnectedSpace (Spec (.of Ω)) :=
    { isPreconnected_univ := Set.subsingleton_of_subsingleton.isPreconnected
      toNonempty := inferInstance }
  have : GeometricallyConnected a := geometricallyConnected_of_isAlgClosed a
  have : UniversallySubmersive a := ExposeIX.universallySubmersive_specMap_field _ _
  have : UniversallyInjective b := ExposeIX.universallyInjective_specMap_of_isPurelyInseparable _ _
  have : Surjective b := ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  -- `k'` is algebraic over `k`, so `b` is integral, hence universally closed
  have : IsIntegralHom b := IsIntegralHom.SpecMap_iff.mpr (Algebra.IsIntegral.isIntegral (R := k))
  have : GeometricallyConnected b := ExposeIX.geometricallyConnected_of_universally_isHomeomorph b
    (ExposeIX.universally_isHomeomorph_of_universallyClosed b)
  rw [← hab]
  exact ExposeIX.geometricallyConnected_comp a b

/-- Morphisms into étale schemes extend along a universally submersive morphism `ι : W₀ ⟶ W` with
geometrically connected fibres (IX.3.4): for `π : W ⟶ X` and an étale `X`-scheme `E`, every
`w : W₀ ⟶ E` over `ι ≫ π` is `ι ≫ v` for some `v : W ⟶ E` over `π`. -/
lemma exists_hom_of_geometricallyConnected {W₀ W X : Scheme.{u}} (ι : W₀ ⟶ W)
    [UniversallySubmersive ι] [GeometricallyConnected ι] (π : W ⟶ X) (E : X.Etale)
    (w : W₀ ⟶ E.left) (hw : w ≫ E.hom = ι ≫ π) :
    ∃ v : W ⟶ E.left, v ≫ E.hom = π ∧ ι ≫ v = w := by
  let φ' : pullback (𝟙 W) ι ⟶ pullback E.hom π :=
    pullback.lift (pullback.snd _ _ ≫ w) (pullback.fst _ _) (by
      rw [Category.assoc, hw, ← Category.assoc, ← pullback.condition, Category.comp_id])
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩, -⟩ := ExposeIX.existsUnique_hom_of_geometricallyConnected ι (𝟙 _)
    (pullback.snd E.hom π) φ' ((pullback.lift_snd _ _ _).trans (Category.comp_id _).symm)
  refine ⟨φ ≫ pullback.fst _ _, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, reassoc_of% hφ₁]
  · let σ : W₀ ⟶ pullback (𝟙 W) ι :=
      pullback.lift ι (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    have hσ : σ ≫ pullback.fst _ _ = ι := pullback.lift_fst _ _ _
    rw [← hσ, Category.assoc, reassoc_of% hφ₂]
    change σ ≫ pullback.lift _ _ _ ≫ pullback.fst _ _ = w
    rw [pullback.lift_fst, ← Category.assoc, pullback.lift_snd, Category.id_comp]

/-- Sections of étale schemes are invariant under extension from a separably closed field `k` to
an algebraically closed field `Ω` (Stacks 0A3I, for represented sheaves): if `W₀ = T ⊗_k Ω`
(a cartesian square), every morphism `W₀ ⟶ E` over `W₀ ⟶ T ⟶ X` into an étale `X`-scheme comes
from a morphism `T ⟶ E` over `X`. -/
theorem exists_hom_of_isPullback_specMap_of_isSepClosed {k Ω : Type u} [Field k] [IsSepClosed k]
    [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] {W₀ T X : Scheme.{u}} {ι : W₀ ⟶ T}
    {q : W₀ ⟶ Spec (.of Ω)} {t : T ⟶ Spec (.of k)}
    (hsq : IsPullback ι q t (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) (π : T ⟶ X)
    (E : X.Etale) (w : W₀ ⟶ E.left) (hw : w ≫ E.hom = ι ≫ π) :
    ∃ v : T ⟶ E.left, v ≫ E.hom = π ∧ ι ≫ v = w := by
  have : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    geometricallyConnected_specMap_of_isSepClosed k Ω
  have : UniversallySubmersive (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    ExposeIX.universallySubmersive_specMap_field _ _
  have : GeometricallyConnected ι := MorphismProperty.of_isPullback hsq.flip inferInstance
  have : UniversallySubmersive ι := MorphismProperty.of_isPullback hsq.flip inferInstance
  exact exists_hom_of_geometricallyConnected ι π E w hw

end SGA.SGA1.ExposeXIII
