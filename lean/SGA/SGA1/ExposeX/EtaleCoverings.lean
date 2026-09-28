/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeV.FundamentalGroupFunctoriality

/-!
# SGA 1, Exposé X: étale coverings and separable morphisms

The language used to state the results of Exposé X on schemes.

* `FEt X`: the category of étale coverings (finite étale morphisms) of a scheme `X`, and the
  inverse-image functor `FEt.pullback f : FEt Y ⥤ FEt X` along `f : X ⟶ Y` (those of
  Exposé V, `SGA.SGA1.ExposeV.FEt`; `FEt X` is a Galois category when `X` is connected, with
  fibre functors at geometric points). By V.6.10, a
  homomorphism of fundamental groups is an isomorphism iff the corresponding functor is an
  equivalence, so several statements of Exposé X (X.1.8, X.2.1, X.3.3) are recorded as the
  assertion that such a functor is an equivalence; `autWhiskerLeft_bijective_of_isEquivalence` then
  gives the isomorphism of fundamental groups.
* Connected objects and sections: an object of `FEt X` which is connected in the sense of
  Galois categories (not initial, no non-trivial subobjects) has a connected underlying scheme
  (`FEt.connectedSpace_of_isConnected`), and a morphism from the final object is a section
  (`FEt.exists_section_of_hom`). These translate the hypotheses of the Galois-category
  criteria (`GaloisFunctors`) into the language of X.1.3.
* `geometricPoint Y y`: the geometric point `Spec κ(y)^alg → Y` above `y`.
* X.1.1: separable morphisms (`IsSeparable`), i.e. flat morphisms with geometrically reduced
  fibres (mathlib's `GeometricallyReduced`), their stability under change of base, and the
  remark that a scheme étale over a separable one is separable (`isSeparable_comp`, from I.9.2).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeX

/-- The class of *étale coverings* (V.7): finite étale morphisms
(`SGA.SGA1.ExposeV.finiteEtaleHom`). -/
abbrev finiteEtale : MorphismProperty Scheme.{u} := ExposeV.finiteEtaleHom

/-- The category of étale coverings of a scheme `X` (`SGA.SGA1.ExposeV.FEt`). -/
abbrev FEt (X : Scheme.{u}) : Type (u + 1) := ExposeV.FEt X

/-- The inverse-image functor `X' ↦ X' ×_Y X` on étale coverings along `f : X ⟶ Y`. -/
noncomputable abbrev FEt.pullback {X Y : Scheme.{u}} (f : X ⟶ Y) : FEt Y ⥤ FEt X :=
  ExposeV.FEt.pullback f

namespace FEt

variable {X : Scheme.{u}}

instance (Y : FEt X) : IsFinite Y.hom := Y.prop.1

instance (Y : FEt X) : Etale Y.hom := Y.prop.2

/-- The final étale covering `X → X`. -/
noncomputable abbrev top (X : Scheme.{u}) : FEt X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) ⟨inferInstance, inferInstance⟩

/-- `X → X` is the final object of `FEt X`. -/
noncomputable def isTerminalTop : IsTerminal (top X) :=
  IsTerminal.ofUniqueHom
    (fun Z ↦ MorphismProperty.Over.homMk Z.hom (by exact Category.comp_id _) trivial)
    (fun Z m ↦ by
      ext
      change m.left = Z.hom
      exact (Category.comp_id m.left).symm.trans (MorphismProperty.Over.w m))

/-- The empty étale covering. -/
noncomputable abbrev bot (X : Scheme.{u}) : FEt X :=
  MorphismProperty.Over.mk ⊤ (Scheme.emptyTo X) ⟨inferInstance, inferInstance⟩

/-- An étale covering with empty underlying scheme is an initial object. -/
noncomputable def isInitialOfIsEmpty (Z : FEt X) [IsEmpty Z.left] : IsInitial Z :=
  IsInitial.ofUniqueHom
    (fun W ↦ MorphismProperty.Over.homMk (AlgebraicGeometry.isInitialOfIsEmpty.to _)
      (AlgebraicGeometry.isInitialOfIsEmpty.hom_ext _ _) trivial)
    (fun W m ↦ by
      ext
      exact AlgebraicGeometry.isInitialOfIsEmpty.hom_ext _ _)

/-- The underlying scheme of an initial object of `FEt X` is empty. -/
lemma isEmpty_of_isInitial {Z : FEt X} (h : IsInitial Z) : IsEmpty Z.left :=
  ⟨fun z ↦ isEmptyElim (α := (∅ : Scheme.{u})) ((h.to (bot X)).left z)⟩

/-- An object of `FEt X` that is connected in the sense of Galois categories has a connected
underlying scheme. -/
theorem connectedSpace_of_isConnected (Y : FEt X) [PreGaloisCategory.IsConnected Y] :
    ConnectedSpace Y.left := by
  rw [connectedSpace_iff_clopen]
  refine ⟨?_, fun U hU ↦ ?_⟩
  · by_contra h
    rw [not_nonempty_iff] at h
    exact PreGaloisCategory.IsConnected.notInitial (isInitialOfIsEmpty Y)
  · by_contra hne
    rw [not_or] at hne
    let V : Y.left.Opens := ⟨U, hU.isOpen⟩
    have : IsClosedImmersion V.ι := .of_isPreimmersion _ (by simpa [V] using hU.isClosed)
    let Z : FEt X := MorphismProperty.Over.mk ⊤ (V.ι ≫ Y.hom) ⟨inferInstance, inferInstance⟩
    let i : Z ⟶ Y := MorphismProperty.Over.homMk V.ι rfl trivial
    have : Mono i := by
      have : Mono ((MorphismProperty.Over.forget finiteEtale ⊤ X ⋙ Over.forget X).map i) := by
        change Mono V.ι
        infer_instance
      exact Functor.mono_of_mono_map _ this
    have hZ : IsInitial Z → False := fun h ↦ by
      have := isEmpty_of_isInitial h
      obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.mpr hne.1
      exact IsEmpty.false (α := Z.left) ⟨u, hu⟩
    have hi := PreGaloisCategory.IsConnected.noTrivialComponent Z i hZ
    have : IsIso V.ι :=
      inferInstanceAs (IsIso ((MorphismProperty.Over.forget finiteEtale ⊤ X ⋙
        Over.forget X).map i))
    apply hne.2
    rw [Set.eq_univ_iff_forall]
    intro y
    obtain ⟨v, rfl⟩ := (asIso V.ι).hom.homeomorph.surjective y
    exact v.2

/-- A morphism from the final object to `Z` in `FEt X` gives a section of `Z.left → X`. -/
lemma exists_section_of_hom [HasTerminal (FEt X)] {Z : FEt X} (t : ⊤_ (FEt X) ⟶ Z) :
    ∃ s : X ⟶ Z.left, s ≫ Z.hom = 𝟙 X :=
  ⟨(terminal.from (top X) ≫ t).left, MorphismProperty.Over.w _⟩

end FEt

/-- The geometric point `Spec κ(y)^alg → Y` above a point `y`, with values in an algebraic
closure of the residue field. -/
noncomputable def geometricPoint (Y : Scheme.{u}) (y : Y) :
    Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
    (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y

/-- X.1.1: a morphism `f : X ⟶ Y` is *separable* if it is flat and its fibres `X ⊗_Y κ(y)` are
separable over `κ(y)`, i.e. `X ⊗_Y K` is reduced for every field `K` over `Y`
(mathlib's `GeometricallyReduced`). -/
class IsSeparable {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop extends Flat f, GeometricallyReduced f

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)

lemma isSeparable_iff : IsSeparable f ↔ Flat f ∧ GeometricallyReduced f :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ ⟨⟩⟩

/-- X.1.1, the definition as written: `f` is separable iff it is flat and for every `y ∈ Y` the
fibre `X ⊗_Y κ(y)` is separable (geometrically reduced) over `κ(y)`. -/
lemma isSeparable_iff_fiber :
    IsSeparable f ↔ Flat f ∧ ∀ y : Y, GeometricallyReduced (f.fiberToSpecResidueField y) := by
  rw [isSeparable_iff, geometricallyReduced_iff, geometrically_iff_forall_fiberToSpecResidueField]
  simp_rw [← geometricallyReduced_iff]

/-- X.1.1: over a field (a reduced and irreducible one-point scheme), separable just means
geometrically reduced, flatness being automatic. -/
lemma isSeparable_iff_of_field [Subsingleton Y] [IsIntegral Y] :
    IsSeparable f ↔ GeometricallyReduced f :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨⟩⟩

/-- X.1.1: separability is stable under change of base. -/
instance (g : Z ⟶ Y) [IsSeparable f] : IsSeparable (pullback.snd f g) where

instance (g : Z ⟶ Y) [IsSeparable f] : IsSeparable (pullback.fst g f) where

/-- X.1.1 (remark): if `X` is separable over `Y` and `X'` is étale over `X`, then `X'` is separable
over `Y`, by I.9.2 (étale over reduced is reduced). SGA works with locally noetherian preschemes;
here `X → Y` is assumed locally of finite type, so that the fibres `X ⊗_Y K` are locally
noetherian. -/
theorem isSeparable_comp {X' : Scheme.{u}} (g : X' ⟶ X) [Etale g] [IsSeparable f]
    [LocallyOfFiniteType f] : IsSeparable (g ≫ f) := by
  have : GeometricallyReduced (g ≫ f) := by
    constructor
    intro K _ y W fst snd h
    let t : W ⟶ pullback f y := pullback.lift (fst ≫ g) snd (by rw [Category.assoc, h.w])
    have hsq : IsPullback fst t g (pullback.fst f y) := by
      refine IsPullback.of_bot (v₂₁ := pullback.snd f y) (v₂₂ := f) ?_
        (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback f y)
      rw [pullback.lift_snd]
      exact h
    have : Etale t := MorphismProperty.of_isPullback hsq inferInstance
    have : IsReduced (pullback f y) :=
      GeometricallyReduced.geometrically_isReduced (f := f) y _ _ (IsPullback.of_hasPullback f y)
    exact SGA.SGA1.ExposeI.isReduced_of_etale t
  exact ⟨⟩

end SGA.SGA1.ExposeX
