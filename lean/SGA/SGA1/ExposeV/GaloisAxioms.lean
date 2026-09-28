/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Galois.FullSubcategory
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import SGA.Foundations.Pro.Representable

/-!
# SGA 1, Exposé V, §4: axiomatic conditions for a Galois theory

SGA states six conditions (G 1)–(G 6) on a category `C` and a functor `F` from `C` to finite
sets, and proves (V.4.1) that `F` induces an equivalence of `C` with the category `C(π)` of
finite sets with a continuous action of a profinite group `π`.

Mathlib's `PreGaloisCategory` and `FiberFunctor` follow Lenstra's variant of the axioms, which
differs from SGA in two places:

* SGA's (G 3) asks that every morphism factor as a strict epimorphism followed by the
  inclusion of a direct summand; mathlib only asks that monomorphisms be inclusions of direct
  summands;
* SGA's (G 5) asks that `F` send strict epimorphisms to epimorphisms; mathlib asks that `F`
  preserve all epimorphisms.

`GaloisCategoryAxioms` and `FiberFunctorAxioms` record SGA's conditions literally, and
`galoisCategoryAxioms_and_fiberFunctorAxioms_iff` proves that they are equivalent to mathlib's.
A strict epimorphism is mathlib's `EffectiveEpi` (in presence of fibre products this is the
same as being the coequalizer of its kernel pair, the definition given in V.3.6).

The fundamental theorem V.4.1 and most of steps a)–n) are in mathlib; this file records them,
and adds (G 3) in mathlib's setting, artinianity (step b)), SGA's form of step c) (the fibre
functor is strictly pro-representable, by Grothendieck's theorem), SGA's notion of connected object,
steps e) and f), the fact that `C(π)` satisfies the axioms, and Remark V.4.2 (finite colimits
exist and `F` commutes with them).
-/

universe u₁ u₂ w v

namespace SGA.SGA1.ExposeV

open CategoryTheory Limits PreGaloisCategory Functor

variable {C : Type u₁} [Category.{u₂} C]

/-! ### SGA's axioms (G 1)–(G 6) -/

/-- V.4, (G 1)–(G 3): SGA's conditions on the category `C`. The quotient of an object by a
finite group of automorphisms is the colimit over `SingleObj G`. -/
structure GaloisCategoryAxioms (C : Type u₁) [Category.{u₂} C] : Prop where
  /-- (G 1): `C` has a final object. -/
  hasTerminal : HasTerminal C
  /-- (G 1): fibre products exist in `C`. -/
  hasPullbacks : HasPullbacks C
  /-- (G 2): finite sums exist in `C`. -/
  hasFiniteCoproducts : HasFiniteCoproducts C
  /-- (G 2): quotients by finite groups of automorphisms exist in `C`. -/
  hasQuotients (G : Type u₂) [Group G] [Finite G] : HasColimitsOfShape (SingleObj G) C
  /-- (G 3): every morphism is a strict epimorphism followed by a monomorphism which is the
  inclusion of a direct summand. -/
  factorization {X Y : C} (u : X ⟶ Y) : ∃ (Y' Z : C) (u' : X ⟶ Y') (u'' : Y' ⟶ Y) (v : Z ⟶ Y),
    EffectiveEpi u' ∧ Mono u'' ∧ u' ≫ u'' = u ∧ Nonempty (IsColimit (BinaryCofan.mk u'' v))

/-- V.4, (G 4)–(G 6): SGA's conditions on the functor `F` to finite sets. -/
structure FiberFunctorAxioms (F : C ⥤ FintypeCat.{w}) : Prop where
  /-- (G 4): `F` transforms a final object into a final object. -/
  preservesTerminal : PreservesLimitsOfShape (Discrete PEmpty.{1}) F
  /-- (G 4): `F` commutes with fibre products. -/
  preservesPullbacks : PreservesLimitsOfShape WalkingCospan F
  /-- (G 5): `F` commutes with finite sums. -/
  preservesFiniteCoproducts : PreservesFiniteCoproducts F
  /-- (G 5): `F` transforms strict epimorphisms into epimorphisms. -/
  epi_map_of_effectiveEpi {X Y : C} (u : X ⟶ Y) [EffectiveEpi u] : Epi (F.map u)
  /-- (G 5): `F` commutes with quotients by finite groups of automorphisms. -/
  preservesQuotients (G : Type u₂) [Group G] [Finite G] : PreservesColimitsOfShape (SingleObj G) F
  /-- (G 6): `F` is conservative. -/
  reflectsIsomorphisms : F.ReflectsIsomorphisms

/-- In a colimit binary cofan preserved by a functor to finite sets, the images of the two
inclusions are disjoint. -/
lemma disjoint_range_map_of_isColimit (F : C ⥤ FintypeCat.{w}) {A B X : C} {i : A ⟶ X}
    {j : B ⟶ X} (hc : IsColimit (BinaryCofan.mk i j)) [PreservesColimit (pair A B) F] :
    Disjoint (Set.range (F.map i)) (Set.range (F.map j)) := by
  have h := (isColimitMapCoconeBinaryCofanEquiv (F ⋙ FintypeCat.incl) i j)
    (isColimitOfPreserves (F ⋙ FintypeCat.incl) hc)
  exact ((Types.binaryCofan_isColimit_iff _).1 ⟨h⟩).2.2.1

/-- In a colimit binary cofan preserved by a functor to finite sets, the images of the two
inclusions cover the fibre. -/
lemma range_map_union_of_isColimit (F : C ⥤ FintypeCat.{w}) {A B X : C} {i : A ⟶ X}
    {j : B ⟶ X} (hc : IsColimit (BinaryCofan.mk i j)) [PreservesColimit (pair A B) F] :
    Set.range (F.map i) ∪ Set.range (F.map j) = Set.univ := by
  have h := (isColimitMapCoconeBinaryCofanEquiv (F ⋙ FintypeCat.incl) i j)
    (isColimitOfPreserves (F ⋙ FintypeCat.incl) hc)
  exact codisjoint_iff.1 ((Types.binaryCofan_isColimit_iff _).1 ⟨h⟩).2.2.codisjoint

namespace GaloisCategoryAxioms

variable (h : GaloisCategoryAxioms C)
include h

/-- Under (G 1)–(G 3), every monomorphism is the inclusion of a direct summand
(mathlib's form of (G 3)). -/
lemma monoInducesIsoOnDirectSummand {X Y : C} (i : X ⟶ Y) [Mono i] :
    ∃ (Z : C) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  obtain ⟨Y', Z, u', u'', v, hu', -, rfl, ⟨hc⟩⟩ := h.factorization i
  have : Mono u' := mono_of_mono u' u''
  have : IsIso u' := isIso_of_mono_of_strongEpi u'
  exact ⟨Z, v, ⟨(BinaryCofan.mk u'' v).isColimitCompLeftIso u' hc⟩⟩

/-- (G 1)–(G 3) imply mathlib's axioms for a pre-Galois category. -/
lemma preGaloisCategory : PreGaloisCategory C where
  hasTerminal := h.hasTerminal
  hasPullbacks := h.hasPullbacks
  hasFiniteCoproducts := h.hasFiniteCoproducts
  hasQuotientsByFiniteGroups := h.hasQuotients
  monoInducesIsoOnDirectSummand i _ := h.monoInducesIsoOnDirectSummand i

end GaloisCategoryAxioms

namespace FiberFunctorAxioms

variable {F : C ⥤ FintypeCat.{w}} (hF : FiberFunctorAxioms F) (h : GaloisCategoryAxioms C)
include hF h

/-- Under (G 1)–(G 6), `F` transforms every epimorphism into an epimorphism: in the
factorization (G 3) of an epimorphism, the complementary summand has empty fibre. -/
lemma epi_map {X Y : C} (u : X ⟶ Y) [Epi u] : Epi (F.map u) := by
  have := hF.preservesFiniteCoproducts
  have := h.hasFiniteCoproducts
  obtain ⟨Y', Z, u', u'', v, hu', -, rfl, ⟨hc⟩⟩ := h.factorization u
  have : Epi u'' := epi_of_epi u' u''
  have : Epi (F.map u') := hF.epi_map_of_effectiveEpi u'
  have hZ : IsEmpty (F.obj Z) := by
    refine ⟨fun z ↦ ?_⟩
    obtain ⟨b, hb₁, hb₂⟩ := BinaryCofan.IsColimit.desc' hc (u'' ≫ coprod.inl) (v ≫ coprod.inr)
    have hab : b = coprod.inl := (cancel_epi u'').1 hb₁
    have hv : v ≫ coprod.inl = v ≫ coprod.inr := by
      subst hab
      exact hb₂
    have hz : F.map coprod.inl (F.map v z) = F.map coprod.inr (F.map v z) := by
      simp only [← FintypeCat.comp_apply, ← F.map_comp, hv]
    exact Set.disjoint_left.1 (disjoint_range_map_of_isColimit F (coprodIsCoprod Y Y))
      ⟨_, hz⟩ ⟨_, rfl⟩
  have hs : Function.Surjective (F.map u'') := by
    intro y
    have : y ∈ Set.range (F.map u'') ∪ Set.range (F.map v) := by
      rw [range_map_union_of_isColimit F hc]; trivial
    rcases this with hy | ⟨z, -⟩
    · exact hy
    · exact (hZ.false z).elim
  have : Epi (F.map u'') := ConcreteCategory.epi_of_surjective _ hs
  rw [F.map_comp]
  exact epi_comp _ _

/-- (G 1)–(G 6) imply that `F` is a fibre functor in mathlib's sense. -/
lemma fiberFunctor : @FiberFunctor C _ h.preGaloisCategory F :=
  @FiberFunctor.mk C _ h.preGaloisCategory F hF.preservesTerminal hF.preservesPullbacks
    hF.preservesFiniteCoproducts ⟨fun u _ ↦ hF.epi_map h u⟩ hF.preservesQuotients
    hF.reflectsIsomorphisms

end FiberFunctorAxioms

/-- A pre-Galois category with a fibre functor (in any universe) is a Galois category. -/
theorem galoisCategory_of_fiberFunctor [PreGaloisCategory C] (F : C ⥤ FintypeCat.{w})
    [FiberFunctor F] : GaloisCategory C where
  hasFiberFunctor := ⟨F ⋙ FintypeCat.uSwitch, FiberFunctor.comp_right _⟩

section PreGalois

variable [PreGaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism of a Galois category which is surjective on fibres is a strict (effective)
epimorphism: a morphism compatible with the kernel pair descends on fibres, equivariantly for
`Aut F`, hence in `C` since `F` is fully faithful into `Aut F`-sets. -/
theorem effectiveEpi_of_surjective {X Y : C} (f : X ⟶ Y) (hf : Function.Surjective (F.map f)) :
    EffectiveEpi f := by
  have := galoisCategory_of_fiberFunctor F
  have : Epi f := F.epi_of_epi_map (ConcreteCategory.epi_of_surjective _ hf)
  suffices IsRegularEpi f from inferInstance
  refine IsRegularEpi.of_epi_of_exists fun Z g hg ↦ ?_
  choose s hs using hf
  have key (x : F.obj X) : F.map g (s (F.map f x)) = F.map g x := by
    let p := (fiberPullbackEquiv F f f).symm ⟨(s (F.map f x), x), hs _⟩
    simpa [p] using congrArg (fun h ↦ F.map h p) hg
  let φ : (functorToAction F).obj Y ⟶ (functorToAction F).obj Z :=
    { hom := FintypeCat.homMk fun y ↦ F.map g (s y)
      comm := fun σ ↦ by
        ext (y : F.obj Y)
        change F.map g (s (σ • y)) = σ • (F.map g (s y))
        conv_lhs => rw [← hs y, mulAction_naturality, key]
        rw [mulAction_naturality] }
  obtain ⟨h, hh⟩ := (functorToAction F).map_surjective φ
  refine ⟨h, (functorToAction F).map_injective ?_⟩
  rw [Functor.map_comp, hh]
  ext x
  exact key x

/-- In a Galois category a morphism is an epimorphism iff it is surjective on fibres. -/
theorem epi_iff_surjective_map {X Y : C} (f : X ⟶ Y) : Epi f ↔ Function.Surjective (F.map f) :=
  ⟨fun _ ↦ surjective_on_fiber_of_epi F f,
    fun hf ↦ F.epi_of_epi_map (ConcreteCategory.epi_of_surjective _ hf)⟩

include F in
/-- In a Galois category every epimorphism is strict. -/
theorem effectiveEpi_iff_epi {X Y : C} (f : X ⟶ Y) : EffectiveEpi f ↔ Epi f :=
  ⟨fun _ ↦ inferInstance,
    fun h ↦ effectiveEpi_of_surjective F f ((epi_iff_surjective_map F f).1 h)⟩

include F in
set_option backward.isDefEq.respectTransparency.types false in
/-- V.4, (G 3) in a Galois category in mathlib's sense: every morphism is a strict epimorphism
followed by the inclusion of a direct summand. The image is lifted from `Aut F`-sets using
that the fibre functor is fully faithful into `Aut F`-sets. -/
theorem exists_effectiveEpi_comp_summand {X Y : C} (u : X ⟶ Y) :
    ∃ (Y' Z : C) (u' : X ⟶ Y') (u'' : Y' ⟶ Y) (v : Z ⟶ Y), EffectiveEpi u' ∧ Mono u'' ∧
      u' ≫ u'' = u ∧ Nonempty (IsColimit (BinaryCofan.mk u'' v)) := by
  have := galoisCategory_of_fiberFunctor F
  let S : SubMulAction (Aut F) (F.obj Y) :=
    { carrier := Set.range (F.map u)
      smul_mem' := by
        rintro σ _ ⟨x, rfl⟩
        exact ⟨σ • x, (mulAction_naturality F σ u x).symm⟩ }
  let T : Action FintypeCat.{w} (Aut F) := Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of S)
  let i : T ⟶ (functorToAction F).obj Y :=
    { hom := FintypeCat.homMk Subtype.val
      comm := fun _ ↦ rfl }
  have : Mono i := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  obtain ⟨Z, f, e, hf, hfe⟩ := exists_lift_of_mono F Y T i
  let φ : (functorToAction F).obj X ⟶ T :=
    { hom := FintypeCat.homMk fun x ↦ (⟨F.map u x, x, rfl⟩ : S)
      comm := fun σ ↦ by
        ext (x : F.obj X)
        exact Subtype.ext (mulAction_naturality F σ u x).symm }
  obtain ⟨u', hu'⟩ := (functorToAction F).map_surjective (φ ≫ e.hom)
  have hcomp : u' ≫ f = u := (functorToAction F).map_injective <| by
    rw [Functor.map_comp, hu', Category.assoc, hfe]
    rfl
  have hsurj : Function.Surjective (F.map u') := by
    intro z
    obtain ⟨x, hx⟩ := (e.inv.hom z).2
    refine ⟨x, ?_⟩
    have h1 : φ.hom x = e.inv.hom z := Subtype.ext hx
    change ((functorToAction F).map u').hom x = z
    rw [hu']
    change e.hom.hom (φ.hom x) = z
    rw [h1]
    exact congrArg (fun g ↦ g.hom z) e.inv_hom_id
  obtain ⟨Z', v, hc⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand f
  exact ⟨Z, Z', u', f, v, effectiveEpi_of_surjective F u' hsurj, hf, hcomp, hc⟩

end PreGalois

/-- V.4: SGA's axioms (G 1)–(G 6) for `(C, F)` are equivalent to mathlib's: `C` is a
`PreGaloisCategory` and `F` is a `FiberFunctor`. -/
theorem galoisCategoryAxioms_and_fiberFunctorAxioms_iff (F : C ⥤ FintypeCat.{w}) :
    GaloisCategoryAxioms C ∧ FiberFunctorAxioms F ↔
      ∃ _ : PreGaloisCategory C, FiberFunctor F := by
  refine ⟨fun ⟨h, hF⟩ ↦ ⟨h.preGaloisCategory, hF.fiberFunctor h⟩, fun ⟨_, _⟩ ↦ ⟨?_, ?_⟩⟩
  · exact
      { hasTerminal := inferInstance
        hasPullbacks := inferInstance
        hasFiniteCoproducts := inferInstance
        hasQuotients := fun _ _ _ ↦ inferInstance
        factorization := exists_effectiveEpi_comp_summand F }
  · exact
      { preservesTerminal := inferInstance
        preservesPullbacks := inferInstance
        preservesFiniteCoproducts := inferInstance
        epi_map_of_effectiveEpi := fun _ _ ↦ inferInstance
        preservesQuotients := fun _ _ _ ↦ inferInstance
        reflectsIsomorphisms := inferInstance }

/-! ### Steps a)–h) -/

section Steps

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- V.4 a): a morphism is a monomorphism iff its image under `F` is one. -/
theorem mono_iff_mono_map {X Y : C} (u : X ⟶ Y) : Mono u ↔ Mono (F.map u) :=
  (F.mono_map_iff_mono u).symm

include F in
/-- V.4 b): every object of a Galois category is artinian: along a strict inclusion of
subobjects, the cardinality of the fibre strictly increases. -/
theorem isArtinianObject (X : C) : IsArtinianObject X := by
  have hmono : StrictMono (fun s : Subobject X ↦ Nat.card (F.obj (s : C))) := by
    intro s t hst
    apply lt_card_fiber_of_mono_of_notIso F (Subobject.ofLE s t hst.le)
    intro hi
    refine hst.ne (le_antisymm hst.le (Subobject.le_of_comm (inv (Subobject.ofLE s t hst.le)) ?_))
    rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow]
  have : WellFoundedLT (Subobject X) := hmono.wellFoundedLT
  exact ⟨this⟩

/-- V.4 c) (mathlib): the fibre functor is pro-representable, by the cofiltered system of
pointed Galois objects. The transition maps of this system are epimorphisms
(`epi_of_nonempty_of_isConnected`). -/
theorem isColimit_coyoneda (F : C ⥤ FintypeCat.{u₂}) [FiberFunctor F] :
    Nonempty (IsColimit (PointedGaloisObject.cocone F)) :=
  ⟨PointedGaloisObject.isColimit F⟩

omit [FiberFunctor F] in
/-- V.4 c): a Galois category has finite limits. -/
theorem hasFiniteLimits : HasFiniteLimits C :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- V.4 c): the fibre functor is strictly pro-representable. As in SGA this follows from b) and
(G 4) by Grothendieck's theorem (Séminaire Bourbaki 195, Prop. 3.1,
`Functor.isStrictlyProRepresentable_of_preservesFiniteLimits`): `F` is pro-represented by the
cofiltered system of its minimal elements, with epimorphic transition morphisms. As for all
categories in SGA, `C` is assumed essentially small (relative to the universe of its morphisms);
this cannot be dropped, since `Hom(P, P) ≅ π` must be small. -/
theorem isStrictlyProRepresentable_fiberFunctor [EssentiallySmall.{u₂} C]
    (F : C ⥤ FintypeCat.{u₂}) [FiberFunctor F] :
    (F ⋙ FintypeCat.incl).IsStrictlyProRepresentable := by
  have := hasFiniteLimits (C := C)
  have (X : C) : IsArtinianObject X := isArtinianObject F X
  have := comp_preservesFiniteLimits F FintypeCat.incl
  exact Functor.isStrictlyProRepresentable_of_preservesFiniteLimits

omit [GaloisCategory C] [FiberFunctor F] in
/-- An object isomorphic to a connected object is connected. -/
lemma isConnected_of_iso {X Y : C} (e : Y ≅ X) [IsConnected Y] : IsConnected X where
  notInitial h := IsConnected.notInitial (h.ofIso e.symm)
  noTrivialComponent Z j _ hZ := by
    have : IsIso (j ≫ e.inv) := IsConnected.noTrivialComponent Z (j ≫ e.inv) hZ
    exact IsIso.of_isIso_comp_right j e.inv

/-- V.4 c), d): the minimal elements of the fibre functor (points `x ∈ F(X)` which do not come
from a proper subobject of `X`) are exactly the points of the fibres of connected objects. Hence
the terms of the pro-object of V.4 c) are the connected objects. -/
theorem isMinimalElement_iff_isConnected {X : C} (x : F.obj X) :
    (F ⋙ FintypeCat.incl).IsMinimalElement (X := X) x ↔ IsConnected X := by
  refine ⟨fun h ↦ ?_, fun _ Y i _ ⟨y, _⟩ ↦ ?_⟩
  · obtain ⟨Y, i, y, hy, hY, _⟩ := fiber_in_connected_component F X x
    have : IsIso i := h i ⟨y, hy⟩
    exact isConnected_of_iso (asIso i)
  · exact IsConnected.noTrivialComponent Y i fun hY ↦
      ((initial_iff_fiber_empty F Y).1 ⟨hY⟩).false y

/-- V.4, definition before d): SGA calls `X` connected if it is not the sum of two objects which
are both non-initial. Unlike mathlib's `IsConnected`, this allows `X` to be initial. -/
def IsIndecomposable (X : C) : Prop :=
  ∀ {A B : C} {i : A ⟶ X} {j : B ⟶ X}, IsColimit (BinaryCofan.mk i j) →
    Nonempty (IsInitial A) ∨ Nonempty (IsInitial B)

include F in
/-- V.4: mathlib's connected objects are SGA's connected objects which are not initial. -/
theorem isConnected_iff_isIndecomposable (X : C) :
    IsConnected X ↔ IsIndecomposable X ∧ ¬ Nonempty (IsInitial X) := by
  refine ⟨fun hX ↦ ⟨fun {A B i j} hc ↦ ?_, fun ⟨h⟩ ↦ hX.notInitial h⟩, fun ⟨hX, hX'⟩ ↦ ?_⟩
  · by_contra! hAB
    have : Mono i := MonoCoprod.binaryCofan_inl _ hc
    have : IsIso i := hX.noTrivialComponent A i hAB.1.false
    obtain ⟨b⟩ := (not_initial_iff_fiber_nonempty F B).1 hAB.2.false
    obtain ⟨a, ha⟩ := ((ConcreteCategory.isIso_iff_bijective (F.map i)).1 inferInstance).2
      (F.map j b)
    exact Set.disjoint_left.1 (disjoint_range_map_of_isColimit F hc) ⟨a, ha⟩ ⟨b, rfl⟩
  · refine ⟨fun h ↦ hX' ⟨h⟩, fun Y i _ hY ↦ ?_⟩
    obtain ⟨Z, u, ⟨hc⟩⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand i
    obtain h | h := hX hc
    · exact (hY h.some).elim
    · exact (BinaryCofan.isColimit_iff_isIso_inl h.some _).1 ⟨hc⟩

/-- V.4 d) (mathlib): a Galois object, in particular each `P_i`, is connected. -/
theorem isConnected_of_isGalois (X : C) [IsGalois X] : IsConnected X := inferInstance

include F in
/-- V.4 e): a morphism from a non-initial object to a connected object is a strict
epimorphism. -/
theorem effectiveEpi_of_isConnected {X Y : C} [IsConnected Y] (hX : IsInitial X → False)
    (u : X ⟶ Y) : EffectiveEpi u :=
  have : Nonempty (F.obj X) := (not_initial_iff_fiber_nonempty F X).1 hX
  effectiveEpi_of_surjective F u (surjective_of_nonempty_fiber_of_isConnected F u)

include F in
/-- V.4 e): every endomorphism of a connected object is an automorphism. -/
theorem isIso_of_isConnected {X : C} [IsConnected X] (u : X ⟶ X) : IsIso u := by
  have hs : Function.Surjective (F.map u) := surjective_of_nonempty_fiber_of_isConnected F u
  have : IsIso (F.map u) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨Finite.injective_iff_surjective.2 hs, hs⟩
  exact isIso_of_reflects_iso u F

/-- V.4 f): for a connected object `A` and `a ∈ F(A)`, the following are equivalent:
`A` is Galois; every `b ∈ F(A)` is `F(v)(a)` for an endomorphism `v`; `Aut A` acts transitively
on `F(A)`; `Aut A` acts simply transitively on `F(A)`. -/
theorem isGalois_tfae (A : C) [IsConnected A] (a : F.obj A) :
    List.TFAE [IsGalois A, Function.Surjective (fun v : A ⟶ A ↦ F.map v a),
      MulAction.IsPretransitive (Aut A) (F.obj A),
      Function.Bijective (fun σ : Aut A ↦ F.map σ.hom a)] := by
  tfae_have 1 ↔ 3 := isGalois_iff_pretransitive F A
  tfae_have 2 → 3 := fun h ↦ by
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨f, rfl⟩ := h x
    obtain ⟨g, rfl⟩ := h y
    have := isIso_of_isConnected F f
    have := isIso_of_isConnected F g
    refine ⟨(asIso f).symm ≪≫ asIso g, ?_⟩
    change F.map (inv f ≫ g) (F.map f a) = F.map g a
    rw [← FintypeCat.comp_apply, ← F.map_comp, IsIso.hom_inv_id_assoc]
  tfae_have 3 → 4 := fun _ ↦
    ⟨evaluation_aut_injective_of_isConnected F A a, MulAction.IsPretransitive.exists_smul_eq a⟩
  tfae_have 4 → 2 := fun h b ↦ by
    obtain ⟨σ, rfl⟩ := h.2 b
    exact ⟨σ.hom, rfl⟩
  tfae_finish

/-- V.4 g) (mathlib): for every `X` there is a Galois object `A` and `a ∈ F(A)` such that
evaluation at `a` is a bijection `Hom(A, X) ≃ F(X)`. -/
theorem exists_isGalois_representative (X : C) : ∃ (A : C) (a : F.obj A),
    IsGalois A ∧ Function.Bijective (fun f : A ⟶ X ↦ F.map f a) :=
  exists_galois_representative F X

/-- V.4 h) (mathlib): `Aut F` is the projective limit of the automorphism groups of the Galois
objects (up to passing to the opposite group). -/
noncomputable def autMulEquiv (F : C ⥤ FintypeCat.{u₂}) [FiberFunctor F] :
    Aut F ≃* (AutGalois F)ᵐᵒᵖ :=
  autMulEquivAutGalois F

omit [GaloisCategory C] [FiberFunctor F] in
/-- V.4 h) (mathlib): the fundamental group `Aut F` is a profinite group. -/
theorem aut_profinite : CompactSpace (Aut F) ∧ T2Space (Aut F) ∧
    TotallyDisconnectedSpace (Aut F) ∧ IsTopologicalGroup (Aut F) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

omit [GaloisCategory C] [FiberFunctor F] in
/-- V.4 h) (mathlib): `Aut F` acts continuously on every fibre. -/
theorem continuousSMul_fiber (X : C) : ContinuousSMul (Aut F) (F.obj X) :=
  continuousSMul_aut_fiber F X

end Steps

/-! ### The category `C(π)` -/

section ContAction

open scoped FintypeCatDiscrete

variable {π : Type v} [Group π]

lemma Action.hom_smul {X Y : Action FintypeCat.{w} π} (f : X ⟶ Y) (g : π) (x : X.V) :
    f.hom (g • x) = g • f.hom x :=
  ConcreteCategory.congr_hom (f.comm g) x

variable [TopologicalSpace π] [IsTopologicalGroup π]

/-- A finite `π`-set is continuous iff the stabilizers of its points are open. -/
lemma isContinuous_iff_isOpen_stabilizer (X : Action FintypeCat.{w} π) :
    X.IsContinuous ↔ ∀ x : X.V, IsOpen (MulAction.stabilizer π x : Set π) :=
  continuousSMul_iff_stabilizer_isOpen (M := π) (X := X.V)

lemma isContinuous_of_jointly_surjective {ι : Type*} {X : Action FintypeCat.{w} π}
    {Y : ι → Action FintypeCat.{w} π} (hY : ∀ i, (Y i).IsContinuous) (f : ∀ i, Y i ⟶ X)
    (hf : ∀ x : X.V, ∃ i y, (f i).hom y = x) : X.IsContinuous := by
  rw [isContinuous_iff_isOpen_stabilizer]
  intro x
  obtain ⟨i, y, rfl⟩ := hf x
  refine Subgroup.isOpen_mono (fun g (hg : g • y = y) ↦ ?_)
    ((isContinuous_iff_isOpen_stabilizer _).1 (hY i) y)
  change g • (f i).hom y = (f i).hom y
  rw [← Action.hom_smul, hg]

lemma isContinuous_of_jointly_injective {ι : Type*} [Finite ι] {X : Action FintypeCat.{w} π}
    {Y : ι → Action FintypeCat.{w} π} (hY : ∀ i, (Y i).IsContinuous) (f : ∀ i, X ⟶ Y i)
    (hf : ∀ x x' : X.V, (∀ i, (f i).hom x = (f i).hom x') → x = x') : X.IsContinuous := by
  rw [isContinuous_iff_isOpen_stabilizer]
  intro x
  let U : Set π := ⋂ i, (MulAction.stabilizer π ((f i).hom x) : Set π)
  have hU : IsOpen U := isOpen_iInter_of_finite fun i ↦
    (isContinuous_iff_isOpen_stabilizer _).1 (hY i) _
  have hUx : U ⊆ MulAction.stabilizer π x := fun g hg ↦
    hf _ _ fun i ↦ by rw [Action.hom_smul]; exact Set.mem_iInter.1 hg i
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ?_ hUx)
  exact hU.mem_nhds (Set.mem_iInter.2 fun i ↦ Subgroup.one_mem _)

lemma isClosedUnderLimitsOfShape_isContinuous (J : Type) [SmallCategory J] [FinCategory J] :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (Action.IsContinuous : ObjectProperty (Action FintypeCat.{w} π)) J where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    exact isContinuous_of_jointly_injective p.prop_diag_obj (fun j ↦ p.π.app j)
      fun x x' h ↦ Concrete.isLimit_ext _ p.isLimit x x' h

lemma isClosedUnderColimitsOfShape_isContinuous (J : Type*) [Category J]
    [HasColimitsOfShape J FintypeCat.{w}] [PreservesColimitsOfShape J FintypeCat.incl.{w}] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (Action.IsContinuous : ObjectProperty (Action FintypeCat.{w} π)) J where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    have hc := isColimitOfPreserves (Action.forget FintypeCat.{w} π ⋙ FintypeCat.incl)
      p.isColimit
    exact isContinuous_of_jointly_surjective p.prop_diag_obj (fun j ↦ p.ι.app j)
      fun x ↦ Types.jointly_surjective_of_isColimit hc x

instance (J : Type) [SmallCategory J] [FinCategory J] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (Action.IsContinuous : ObjectProperty (Action FintypeCat.{w} π)) J :=
  isClosedUnderColimitsOfShape_isContinuous J

instance : ObjectProperty.IsClosedUnderSubobjects
    (Action.IsContinuous : ObjectProperty (Action FintypeCat.{w} π)) where
  prop_of_mono {X Y} f _ hY := by
    have hf : Function.Injective f.hom :=
      (mono_iff_injective _).1 (inferInstanceAs (Mono ((forget (Action FintypeCat.{w} π)).map f)))
    exact isContinuous_of_jointly_injective (ι := Unit) (fun _ ↦ hY) (fun _ ↦ f)
      fun x x' h ↦ hf (h ())

/-- Epimorphisms of continuous finite `π`-sets are surjective. -/
lemma surjective_of_epi_contAction {X Y : ContAction FintypeCat.{w} π} (f : X ⟶ Y) [Epi f] :
    Function.Surjective f.hom.hom := by
  let T₀ : Action FintypeCat.{w} π := Action.trivial π (FintypeCat.of (ULift.{w} Prop))
  have hT₀ : T₀.IsContinuous := by
    rw [isContinuous_iff_isOpen_stabilizer]
    intro x
    convert isOpen_univ
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_univ, iff_true]
    rfl
  let T : ContAction FintypeCat.{w} π := ⟨T₀, hT₀⟩
  let a : Y ⟶ T := ObjectProperty.homMk
    { hom := FintypeCat.homMk fun _ ↦ ULift.up True
      comm := fun _ ↦ rfl }
  let b : Y ⟶ T := ObjectProperty.homMk
    { hom := FintypeCat.homMk fun y ↦ ULift.up (y ∈ Set.range f.hom.hom)
      comm := fun g ↦ by
        ext (y : Y.obj.V)
        change ULift.up (g • y ∈ Set.range f.hom.hom) = ULift.up (y ∈ Set.range f.hom.hom)
        congr 1
        refine propext ⟨fun ⟨x, hx⟩ ↦ ⟨g⁻¹ • x, ?_⟩, fun ⟨x, hx⟩ ↦ ⟨g • x, ?_⟩⟩
        · rw [Action.hom_smul]
          exact (congrArg (g⁻¹ • ·) hx).trans (inv_smul_smul g y)
        · rw [Action.hom_smul]
          exact congrArg (g • ·) hx }
  have hab : a = b := (cancel_epi f).1 <| by
    ext (x : X.obj.V)
    change ULift.up True = ULift.up (f.hom.hom x ∈ Set.range f.hom.hom)
    simp
  intro y
  have := congrArg (fun φ : Y ⟶ T ↦ (φ.hom.hom y).down) hab
  change True = (y ∈ Set.range f.hom.hom) at this
  exact cast this trivial

instance : (ObjectProperty.ι
    (Action.IsContinuous : ObjectProperty (Action FintypeCat.{w} π))).PreservesEpimorphisms where
  preserves f _ := (forget (Action FintypeCat.{w} π)).epi_of_epi_map
    ((epi_iff_surjective _).2 (surjective_of_epi_contAction f))

instance : ObjectProperty.IsGaloisSubcategory
    (Action.IsContinuous : ObjectProperty (Action FintypeCat.{w} π)) where
  isClosedUnderLimitsOfShape_discrete_pEmpty := isClosedUnderLimitsOfShape_isContinuous _
  isClosedUnderLimitsOfShape_walkingCospan := isClosedUnderLimitsOfShape_isContinuous _
  isClosedUnderColimitsOfShape_discrete _ _ := isClosedUnderColimitsOfShape_isContinuous _
  isClosedUnderColimitsOfShape_singleObj _ _ _ := isClosedUnderColimitsOfShape_isContinuous _

/-- V.4: for a topological group `π`, the category `C(π)` of finite sets with a continuous
action of `π` is a Galois category. -/
instance galoisCategory_contAction : GaloisCategory (ContAction FintypeCat.{w} π) :=
  inferInstance

/-- V.4: the forgetful functor `C(π) → (finite sets)` is a fibre functor; together with
`galoisCategory_contAction` and `galoisCategoryAxioms_and_fiberFunctorAxioms_iff` this says
that `C(π)` satisfies (G 1)–(G 6). -/
instance fiberFunctor_contAction :
    FiberFunctor (ObjectProperty.ι _ ⋙ Action.forget FintypeCat.{w} π :
      ContAction FintypeCat.{w} π ⥤ FintypeCat.{w}) :=
  inferInstance

end ContAction

/-! ### The fundamental theorem V.4.1 and Remark V.4.2 -/

section Fundamental

open scoped FintypeCatDiscrete

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- V.4.1 (mathlib): a fibre functor `F` induces an equivalence of `C` with the category
`C(π)` of finite sets with continuous action of the profinite group `π = Aut F`. -/
noncomputable def equivalenceContAction : C ≌ ContAction FintypeCat.{w} (Aut F) :=
  (functorToContAction F).asEquivalence

omit [GaloisCategory C] [FiberFunctor F] in
/-- V.4.1: the equivalence transforms `F` into the forgetful functor of `C(π)`. -/
theorem functorToContAction_comp_forget :
    functorToContAction F ⋙ ObjectProperty.ι _ ⋙ Action.forget _ _ = F :=
  rfl

include F in
/-- V.4.2, (G' 2): a Galois category has finite colimits. -/
theorem hasFiniteColimits : HasFiniteColimits C :=
  ⟨fun _ _ _ ↦ Adjunction.hasColimitsOfShape_of_equivalence (functorToContAction F)⟩

/-- V.4.2, (G' 5): a fibre functor commutes with finite colimits. -/
theorem preservesFiniteColimits : PreservesFiniteColimits F := by
  have := hasFiniteColimits F
  have : PreservesFiniteColimits (ObjectProperty.ι
      (Action.IsContinuous : ObjectProperty (Action FintypeCat.{w} (Aut F)))) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have := comp_preservesFiniteColimits (ObjectProperty.ι
      (Action.IsContinuous : ObjectProperty (Action FintypeCat.{w} (Aut F))))
    (Action.forget FintypeCat.{w} (Aut F))
  rw [← functorToContAction_comp_forget F]
  exact comp_preservesFiniteColimits _ _

end Fundamental

end SGA.SGA1.ExposeV
