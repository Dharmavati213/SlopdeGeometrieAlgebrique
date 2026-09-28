/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeV.FiniteEtaleSpec
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono


/-!
# SGA 1, Exposé V, §7: fiber functors and fundamental groups of schemes

For a scheme `S` and a geometric point `s̄ : Spec Ω ⟶ S` (`Ω` a field, separably closed for the
Galois theory) we define the fiber functor `FEt.fiber Ω s̄ : FEt S ⥤ FintypeCat` of étale
coverings, as base change to `Spec Ω` followed by the fiber functor of `Spec Ω`. Its underlying
functor to sets is the functor of geometric points over `s̄` (`FEt.fiberInclIso`).

* V.7, change of base: `FEt.pullback f` (the functor `f^•`) satisfies
  `F_{t̄} ∘ f^• ≅ F_{f ∘ t̄}` (`FEt.pullbackFiberIso`); the compatibility of `f^•` with
  composition is mathlib's `MorphismProperty.Over.pullbackComp`.
* V.7: `π₁(S, s̄) := Aut F_{s̄}` (`etaleFundamentalGroup`) with the continuous homomorphisms
  `π₁(f; t̄) : π₁(T, t̄) → π₁(S, f ∘ t̄)` (`etaleFundamentalGroup.map`).
* For `S = Spec R` connected, `F_{s̄}` is a fiber functor of the Galois category `FEt S` for
  every geometric point (instance), and `FEt S` is equivalent to the finite continuous
  `π₁(S, s̄)`-sets (`FEt.equivContAction`).

For a non-affine connected `S`, the Galois category structure of `FEt S` is in
`SGA.SGA1.ExposeV.SchemeGaloisCategory`, with the axiom on quotients by finite groups proved in
`SGA.SGA1.ExposeV.QuotientHasQuotients`. We also prove the remark of V.7 that an étale covering is
connected in `FEt S` iff it is connected as a scheme (`FEt.isConnected_iff_connectedSpace`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeV

variable {S T : Scheme.{u}}

/-- V.7: base change of étale coverings along `f : T ⟶ S` (the functor `f^•`). -/
noncomputable abbrev FEt.pullback (f : T ⟶ S) : FEt S ⥤ FEt T :=
  MorphismProperty.Over.pullback _ ⊤ f

/-- Morphisms into a pullback in over categories: `Hom_T(W, Y ×_S T) ≃ Hom_S(W, Y)`. -/
noncomputable def overPullbackHomEquiv {W Y : Scheme.{u}} (g : Y ⟶ S) (f : T ⟶ S)
    (t : W ⟶ T) :
    (Over.mk t ⟶ Over.mk (pullback.snd g f)) ≃ (Over.mk (t ≫ f) ⟶ Over.mk g) where
  toFun a := Over.homMk (a.left ≫ pullback.fst g f) (by
    have := Over.w a
    simp only [Over.mk_hom] at this
    simp [pullback.condition, ← this])
  invFun b := Over.homMk (pullback.lift b.left t (Over.w b)) (pullback.lift_snd _ _ _)
  left_inv a := by
    ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans (Over.w a).symm
  right_inv b := by
    ext
    exact pullback.lift_fst _ _ _

/-- V.7: the geometric points of the base change `X ×_S T` over `t : W ⟶ T` are the
geometric points of `X` over `t ≫ f`. -/
noncomputable def pullbackGeometricPointsIso (f : T ⟶ S) {W : Scheme.{u}} (t : W ⟶ T) :
    FEt.pullback f ⋙ geometricPoints t ≅ geometricPoints (t ≫ f) :=
  NatIso.ofComponents (fun X ↦ (overPullbackHomEquiv X.hom f t).toIso)
    (fun {X X'} φ ↦ by
      ext (a : Over.mk t ⟶ Over.mk (pullback.snd X.hom f))
      apply Over.OverMorphism.ext
      change (a.left ≫ pullback.lift (pullback.fst X.hom f ≫ φ.left) (pullback.snd X.hom f) _) ≫
        pullback.fst X'.hom f = (a.left ≫ pullback.fst X.hom f) ≫ φ.left
      simp only [Category.assoc]
      erw [pullback.lift_fst])

section Fiber

variable (Ω : Type u) [Field Ω]

/-- V.7: the fiber functor of étale coverings of `S` at a geometric point
`s̄ : Spec Ω ⟶ S` (`Ω` separably closed): `X ↦` the finite set of geometric points of `X`
over `s̄`. It is defined as base change to `Spec Ω` followed by the fiber functor of
`Spec Ω`; see `FEt.fiberInclIso` for the identification with geometric points. -/
noncomputable def FEt.fiber (s : Spec (CommRingCat.of Ω) ⟶ S) : FEt S ⥤ FintypeCat.{u} :=
  FEt.pullback s ⋙ geometricFiber (CommRingCat.of Ω) Ω

lemma specPoint_self : specPoint (CommRingCat.of Ω) Ω = 𝟙 _ := by
  simp only [specPoint, Algebra.algebraMap_self]
  exact Spec.map_id _

/-- V.7: the fiber functor at `s̄` is the functor of geometric points over `s̄`. -/
noncomputable def FEt.fiberInclIso (s : Spec (CommRingCat.of Ω) ⟶ S) :
    FEt.fiber Ω s ⋙ FintypeCat.incl ≅ geometricPoints s :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (geometricFiberInclIso (CommRingCat.of Ω) Ω) ≪≫
    pullbackGeometricPointsIso s _ ≪≫
    eqToIso (by rw [specPoint_self, Category.id_comp])

/-- V.7: base change of étale coverings is compatible with the fiber functors:
`F_{t̄} ∘ f^• ≅ F_{f ∘ t̄}`. -/
noncomputable def FEt.pullbackFiberIso (f : T ⟶ S) (t : Spec (CommRingCat.of Ω) ⟶ T) :
    FEt.pullback f ⋙ FEt.fiber Ω t ≅ FEt.fiber Ω (t ≫ f) :=
  Functor.fullyFaithfulCancelRight FintypeCat.incl
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (FEt.fiberInclIso Ω t) ≪≫
      pullbackGeometricPointsIso f t ≪≫ (FEt.fiberInclIso Ω (t ≫ f)).symm)

end Fiber

section AffineFiber

variable (R : CommRingCat.{u}) (Ω : Type u) [Field Ω]

/-- The ring map `R → Ω` corresponding to a geometric point `Spec Ω ⟶ Spec R`. -/
noncomputable abbrev algebraOfPoint (s : Spec (CommRingCat.of Ω) ⟶ Spec R) : Algebra R Ω :=
  (Spec.preimage s).hom.toAlgebra

lemma specPoint_algebraOfPoint (s : Spec (CommRingCat.of Ω) ⟶ Spec R) :
    letI := algebraOfPoint R Ω s
    specPoint R Ω = s :=
  Spec.map_preimage s

/-- For `S = Spec R`, the fiber functor at `s̄ : Spec Ω ⟶ Spec R` is `A ↦ Hom_R(A, Ω)` for the
algebra structure on `Ω` given by `s̄`. -/
noncomputable def FEt.fiberSpecIso (s : Spec (CommRingCat.of Ω) ⟶ Spec R) :
    letI := algebraOfPoint R Ω s
    FEt.fiber Ω s ≅ geometricFiber R Ω :=
  letI := algebraOfPoint R Ω s
  Functor.fullyFaithfulCancelRight FintypeCat.incl
    (FEt.fiberInclIso Ω s ≪≫ eqToIso (by rw [specPoint_algebraOfPoint]) ≪≫
      (geometricFiberInclIso R Ω).symm)

variable [ConnectedSpace (PrimeSpectrum R)] [IsSepClosed Ω]

/-- V.7 (affine connected base): the fiber functor at any geometric point is a fiber functor
of the Galois category `FEt (Spec R)`. -/
instance (s : Spec (CommRingCat.of Ω) ⟶ Spec R) : FiberFunctor (FEt.fiber Ω s) :=
  letI := algebraOfPoint R Ω s
  fiberFunctor_of_iso (FEt.fiberSpecIso R Ω s).symm

end AffineFiber

section FundamentalGroup

variable (Ω : Type u) [Field Ω]

/-- V.7: the fundamental group `π₁(S, s̄)` of a scheme at a geometric point `s̄ : Spec Ω ⟶ S`,
the automorphism group of the fiber functor at `s̄` (a topological group). For `S` affine and
connected it is profinite and classifies the étale coverings (`FEt.equivContAction`). -/
abbrev etaleFundamentalGroup (s : Spec (CommRingCat.of Ω) ⟶ S) := Aut (FEt.fiber Ω s)

/-- V.7: the homomorphism `π₁(f; t̄) : π₁(T, t̄) → π₁(S, f ∘ t̄)` induced by `f : T ⟶ S`,
defined through the inverse image functor `f^•` and the isomorphism `F_{t̄} ∘ f^• ≅ F_{f ∘ t̄}`. -/
noncomputable def etaleFundamentalGroup.map (f : T ⟶ S) (t : Spec (CommRingCat.of Ω) ⟶ T) :
    etaleFundamentalGroup Ω t →* etaleFundamentalGroup Ω (t ≫ f) :=
  autMap (FEt.pullback f) (FEt.pullbackFiberIso Ω f t)

/-- V.7: the homomorphism `π₁(f; t̄)` is continuous. -/
lemma etaleFundamentalGroup.continuous_map (f : T ⟶ S) (t : Spec (CommRingCat.of Ω) ⟶ T) :
    Continuous (etaleFundamentalGroup.map Ω f t) :=
  continuous_autMap _ _

open scoped FintypeCatDiscrete in
/-- V.7 (affine connected base): the étale coverings of `Spec R` are equivalent to finite sets
with a continuous action of `π₁(Spec R, s̄)`. -/
noncomputable def FEt.equivContAction [IsSepClosed Ω] (R : CommRingCat.{u})
    [ConnectedSpace (PrimeSpectrum R)] (s : Spec (CommRingCat.of Ω) ⟶ Spec R) :
    FEt (Spec R) ≌ ContAction FintypeCat (etaleFundamentalGroup Ω s) :=
  (functorToContAction (FEt.fiber Ω s)).asEquivalence

end FundamentalGroup

section Connected

variable {S : Scheme.{u}}

/-- The empty covering, as the target of the unique morphism from an initial object. -/
private noncomputable def FEt.emptyObj (S : Scheme.{u}) : FEt S :=
  MorphismProperty.Over.mk ⊤ (Scheme.emptyTo S) ⟨inferInstance, inferInstance⟩

lemma FEt.isEmpty_left_of_isInitial {X : FEt S} (h : IsInitial X) : IsEmpty X.left :=
  ⟨fun x ↦ (inferInstance : IsEmpty (∅ : Scheme.{u})).false ((h.to (FEt.emptyObj S)).left x)⟩

/-- An étale covering with empty source is initial. -/
noncomputable def FEt.isInitialOfIsEmpty (X : FEt S) [IsEmpty X.left] : IsInitial X :=
  IsInitial.ofUniqueHom
    (fun Y ↦ MorphismProperty.Over.homMk (AlgebraicGeometry.isInitialOfIsEmpty.to Y.left)
      (AlgebraicGeometry.isInitialOfIsEmpty.hom_ext _ _))
    (fun Y m ↦ by
      ext
      exact AlgebraicGeometry.isInitialOfIsEmpty.hom_ext _ _)

lemma FEt.nonempty_left_iff_not_isInitial (X : FEt S) :
    Nonempty X.left ↔ (IsInitial X → False) := by
  refine ⟨fun ⟨x⟩ h ↦ (FEt.isEmpty_left_of_isInitial h).false x, fun h ↦ ?_⟩
  by_contra hX
  rw [not_nonempty_iff] at hX
  exact h (FEt.isInitialOfIsEmpty X)

/-- V.7: an étale covering whose source is connected is a connected object of `FEt S`. -/
lemma FEt.isConnected_of_connectedSpace (X : FEt S) [ConnectedSpace X.left] : IsConnected X where
  notInitial := (FEt.nonempty_left_iff_not_isInitial X).mp inferInstance
  noTrivialComponent Y i _ hY := by
    have : Nonempty Y.left := (FEt.nonempty_left_iff_not_isInitial Y).mpr hY
    have : Mono i.left := inferInstanceAs
      (Mono ((MorphismProperty.Over.forget finiteEtaleHom ⊤ S ⋙ Over.forget S).map i))
    have : IsFinite X.hom := X.prop.1
    have : Etale X.hom := X.prop.2
    have hw : i.left ≫ X.hom = Y.hom := MorphismProperty.Over.w i
    have : Etale (i.left ≫ X.hom) := by rw [hw]; exact Y.prop.2
    have : Etale i.left := Etale.of_comp i.left X.hom
    have : IsFinite (i.left ≫ X.hom) := by rw [hw]; exact Y.prop.1
    have : IsFinite i.left := IsFinite.of_comp i.left X.hom
    have : IsOpenImmersion i.left := IsOpenImmersion.of_flat_of_mono _
    have hsurj : Function.Surjective i.left := by
      have hc : IsClopen (Set.range i.left) :=
        ⟨i.left.isClosedMap.isClosed_range, i.left.isOpenEmbedding.isOpen_range⟩
      exact Set.range_eq_univ.mp ((isClopen_iff.mp hc).resolve_left
        (Set.nonempty_iff_ne_empty.mp (Set.range_nonempty _)))
    have : IsIso i.left :=
      (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨hsurj⟩⟩
    have : IsIso ((MorphismProperty.Over.forget finiteEtaleHom ⊤ S ⋙ Over.forget S).map i) :=
      this
    exact isIso_of_reflects_iso i (MorphismProperty.Over.forget finiteEtaleHom ⊤ S ⋙ Over.forget S)

/-- V.7: the source of a connected object of `FEt S` is connected. -/
lemma FEt.connectedSpace_of_isConnected (X : FEt S) [IsConnected X] : ConnectedSpace X.left := by
  have hne : Nonempty X.left :=
    (FEt.nonempty_left_iff_not_isInitial X).mpr IsConnected.notInitial
  refine connectedSpace_iff_clopen.mpr ⟨hne, fun s hs ↦ ?_⟩
  by_contra! hs'
  obtain ⟨x, hx⟩ := hs'.1
  let U : X.left.Opens := ⟨s, hs.isOpen⟩
  have : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa [U] using hs.isClosed)
  have : IsFinite X.hom := X.prop.1
  have : Etale X.hom := X.prop.2
  let Y : FEt S := MorphismProperty.Over.mk ⊤ (U.ι ≫ X.hom) ⟨inferInstance, inferInstance⟩
  let i : Y ⟶ X := MorphismProperty.Over.homMk U.ι rfl
  have : Mono i := by
    apply (MorphismProperty.Over.forget finiteEtaleHom ⊤ S ⋙ Over.forget S).mono_of_mono_map
    exact inferInstanceAs (Mono U.ι)
  have hY : IsInitial Y → False := (FEt.nonempty_left_iff_not_isInitial Y).mp ⟨⟨x, hx⟩⟩
  have := IsConnected.noTrivialComponent Y i hY
  have : IsIso U.ι :=
    inferInstanceAs (IsIso ((MorphismProperty.Over.forget finiteEtaleHom ⊤ S ⋙
      Over.forget S).map i))
  apply hs'.2
  have h := Set.range_eq_univ.mpr U.ι.surjective
  rwa [Scheme.Opens.range_ι] at h

/-- V.7: an étale covering is connected in the category `FEt S` if and only if it is connected
as a scheme ("since the topological connected components of an étale covering are also étale
coverings"). -/
theorem FEt.isConnected_iff_connectedSpace (X : FEt S) : IsConnected X ↔ ConnectedSpace X.left :=
  ⟨fun _ ↦ FEt.connectedSpace_of_isConnected X, fun _ ↦ FEt.isConnected_of_connectedSpace X⟩

end Connected

end SGA.SGA1.ExposeV
