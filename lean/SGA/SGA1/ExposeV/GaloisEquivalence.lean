/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts


/-!
# Galois categories are invariant under equivalence

SGA 1 V.5.1 defines a Galois category as a category *equivalent* to a category `𝒞(π)`. Mathlib's
`PreGaloisCategory` is given by axioms, so we record that the axioms and fiber functors transfer
along an equivalence of categories. This is used to pass from finite étale algebras to finite
étale schemes over an affine base.

We also define the continuous homomorphism of fundamental groups `autMap` induced by a functor
`H` together with an isomorphism `H ⋙ F ≅ F'` of fiber functors (the map `π₁(f)` of V.6 and
V.7), and show that it is an isomorphism of topological groups when `H` is an equivalence.
-/

universe u₁ u₂ v₁ v₂ w

open CategoryTheory Limits Functor

namespace SGA.SGA1.ExposeV

variable {C : Type u₁} [Category.{u₂} C] {D : Type v₁} [Category.{v₂} D]

/-- A category equivalent to a pre-Galois category is pre-Galois. -/
lemma preGaloisCategory_of_equivalence (e : C ≌ D) [PreGaloisCategory D] :
    PreGaloisCategory C where
  hasTerminal := Adjunction.hasLimitsOfShape_of_equivalence e.functor
  hasPullbacks := Adjunction.hasLimitsOfShape_of_equivalence e.functor
  hasFiniteCoproducts := ⟨fun _ ↦ Adjunction.hasColimitsOfShape_of_equivalence e.functor⟩
  hasQuotientsByFiniteGroups _ _ _ := Adjunction.hasColimitsOfShape_of_equivalence e.functor
  monoInducesIsoOnDirectSummand {X Y} i _ := by
    obtain ⟨Z', u', ⟨hc⟩⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand (e.functor.map i)
    refine ⟨e.inverse.obj Z', e.inverse.map u' ≫ e.unitInv.app Y, ⟨?_⟩⟩
    have h : e.functor.map (e.inverse.map u' ≫ e.unitInv.app Y) = e.counit.app Z' ≫ u' := by
      simp
    refine isColimitOfReflects e.functor ((isColimitMapCoconeBinaryCofanEquiv e.functor _ _).symm
      ?_)
    rw [h]
    exact BinaryCofan.isColimitCompRightIso (BinaryCofan.mk _ u') (e.counit.app Z') hc

/-- Precomposing a fiber functor with an equivalence gives a fiber functor. -/
lemma fiberFunctor_comp_of_equivalence (e : C ≌ D) [PreGaloisCategory D] (F : D ⥤ FintypeCat.{w})
    [PreGaloisCategory.FiberFunctor F] :
    letI := preGaloisCategory_of_equivalence e
    PreGaloisCategory.FiberFunctor (e.functor ⋙ F) := by
  let _ := preGaloisCategory_of_equivalence e
  exact
    { preservesTerminalObjects := comp_preservesLimitsOfShape _ _
      preservesPullbacks := comp_preservesLimitsOfShape _ _
      preservesFiniteCoproducts := comp_preservesFiniteCoproducts _ _
      preservesEpis := inferInstance
      preservesQuotientsByFiniteGroups _ _ _ := comp_preservesColimitsOfShape _ _
      reflectsIsos := inferInstance }

/-- A category equivalent to a Galois category is Galois. -/
lemma galoisCategory_of_equivalence (e : C ≌ D) [GaloisCategory D] : GaloisCategory C :=
  letI := preGaloisCategory_of_equivalence e
  { hasFiberFunctor := by
      obtain ⟨F, hF⟩ := GaloisCategory.hasFiberFunctor D
      have := fiberFunctor_comp_of_equivalence e F
      exact ⟨(e.functor ⋙ F) ⋙ FintypeCat.uSwitch.{v₂, u₂},
        PreGaloisCategory.FiberFunctor.comp_right _⟩ }

section Connected

open PreGaloisCategory

/-- Connected objects (in the sense of Galois categories) are preserved by equivalences. -/
lemma isConnected_functor_obj (e : C ≌ D) (X : C) [IsConnected X] :
    IsConnected (e.functor.obj X) where
  notInitial h := IsConnected.notInitial (IsInitial.isInitialOfObj e.functor X h)
  noTrivialComponent Y i _ hY := by
    let j : e.inverse.obj Y ⟶ X := e.inverse.map i ≫ e.unitInv.app X
    have : Mono j := mono_comp _ _
    have hY' : IsInitial (e.inverse.obj Y) → False := fun h ↦
      hY ((IsInitial.isInitialObj e.functor _ h).ofIso (e.counitIso.app Y))
    have : IsIso j := IsConnected.noTrivialComponent _ j hY'
    have : IsIso (e.inverse.map i) := by
      have : e.inverse.map i = j ≫ e.unit.app X := by simp [j]
      rw [this]
      infer_instance
    exact isIso_of_reflects_iso i e.inverse

/-- Connectedness is invariant under isomorphism. (Private: the public version is
`SGA.SGA1.ExposeV.isConnected_of_iso` in `SGA.SGA1.ExposeV.GaloisAxioms`.) -/
private lemma isConnected_of_iso {X Y : C} (i : X ≅ Y) [IsConnected X] : IsConnected Y := by
  exact
    { notInitial h := IsConnected.notInitial (X := X) (h.ofIso i.symm)
      noTrivialComponent Z f _ hZ := by
        have : IsIso (f ≫ i.inv) := IsConnected.noTrivialComponent Z (f ≫ i.inv) hZ
        have : f = (f ≫ i.inv) ≫ i.hom := by simp
        rw [this]
        infer_instance }

lemma isConnected_functor_obj_iff (e : C ≌ D) (X : C) :
    IsConnected (e.functor.obj X) ↔ IsConnected X :=
  ⟨fun _ ↦
    have : IsConnected (e.inverse.obj (e.functor.obj X)) :=
      isConnected_functor_obj e.symm (e.functor.obj X)
    isConnected_of_iso (X := e.inverse.obj (e.functor.obj X)) (e.unitIso.app X).symm,
    fun _ ↦ isConnected_functor_obj e X⟩

end Connected

section AutMap

open PreGaloisCategory

/-- The homomorphism of automorphism groups of functors to finite sets induced by a functor
`H : C ⥤ D` and an isomorphism `H ⋙ F ≅ F'`: an automorphism `σ` of `F` is sent to the
automorphism `σ_{H(-)}` of `F'`, transported along the isomorphism. -/
noncomputable def autMap (H : C ⥤ D) {F : D ⥤ FintypeCat.{w}} {F' : C ⥤ FintypeCat.{w}}
    (e : H ⋙ F ≅ F') : Aut F →* Aut F' where
  toFun σ := e.symm ≪≫ isoWhiskerLeft H σ ≪≫ e
  map_one' := by
    apply Iso.ext
    refine NatTrans.ext (funext fun X ↦ ?_)
    change e.inv.app X ≫ 𝟙 _ ≫ e.hom.app X = 𝟙 _
    simp
  map_mul' σ τ := by
    apply Iso.ext
    refine NatTrans.ext (funext fun X ↦ ?_)
    change e.inv.app X ≫ (τ.hom.app (H.obj X) ≫ σ.hom.app (H.obj X)) ≫ e.hom.app X =
      (e.inv.app X ≫ τ.hom.app _ ≫ e.hom.app X) ≫ (e.inv.app X ≫ σ.hom.app _ ≫ e.hom.app X)
    simp

lemma autMap_hom_app (H : C ⥤ D) {F : D ⥤ FintypeCat.{w}} {F' : C ⥤ FintypeCat.{w}}
    (e : H ⋙ F ≅ F') (σ : Aut F) (X : C) :
    (autMap H e σ).hom.app X = e.inv.app X ≫ σ.hom.app (H.obj X) ≫ e.hom.app X :=
  rfl

/-- The homomorphism `autMap` is continuous. -/
lemma continuous_autMap (H : C ⥤ D) {F : D ⥤ FintypeCat.{w}} {F' : C ⥤ FintypeCat.{w}}
    (e : H ⋙ F ≅ F') : Continuous (autMap H e) := by
  apply continuous_induced_rng.mpr
  refine continuous_pi fun X ↦ ?_
  let g : Aut (F.obj (H.obj X)) → Aut (F'.obj X) :=
    fun τ ↦ (e.app X).symm ≪≫ τ ≪≫ e.app X
  have hg : Continuous g := continuous_of_discreteTopology
  have : (fun σ ↦ (autEmbedding F' ∘ autMap H e) σ X) =
      g ∘ (fun τ ↦ τ (H.obj X)) ∘ autEmbedding F := by
    ext σ : 1
    apply Iso.ext
    rfl
  change Continuous (fun σ ↦ (autEmbedding F' ∘ autMap H e) σ X)
  rw [this]
  exact hg.comp ((continuous_apply _).comp continuous_induced_dom)

/-- Along an equivalence of categories, `autMap` is bijective. -/
lemma autMap_bijective (H : C ⥤ D) [H.IsEquivalence] {F : D ⥤ FintypeCat.{w}}
    {F' : C ⥤ FintypeCat.{w}} (e : H ⋙ F ≅ F') : Function.Bijective (autMap H e) := by
  let Φ := (H.asEquivalence.congrLeft (E := FintypeCat.{w})).fullyFaithfulInverse
  constructor
  · intro σ τ h
    have h' (X : C) : σ.hom.app (H.obj X) = τ.hom.app (H.obj X) := by
      have := congr_arg (fun ρ : Aut F' ↦ (Iso.hom (ρ : F' ≅ F')).app X) h
      change e.inv.app X ≫ (Iso.hom (σ : F ≅ F)).app (H.obj X) ≫ e.hom.app X =
        e.inv.app X ≫ (Iso.hom (τ : F ≅ F)).app (H.obj X) ≫ e.hom.app X at this
      exact (cancel_mono (e.hom.app X)).mp ((cancel_epi (e.inv.app X)).mp this)
    apply Iso.ext
    apply Φ.map_injective
    exact NatTrans.ext (funext h')
  · intro τ
    refine ⟨Φ.preimageIso (e ≪≫ τ ≪≫ e.symm), ?_⟩
    have h := Φ.map_preimage (e ≪≫ τ ≪≫ e.symm).hom
    apply Iso.ext
    refine NatTrans.ext (funext fun X ↦ ?_)
    change e.inv.app X ≫ (Φ.preimageIso (e ≪≫ τ ≪≫ e.symm)).hom.app (H.obj X) ≫ e.hom.app X =
      (Iso.hom (τ : F' ≅ F')).app X
    have := congr_arg (fun ρ ↦ NatTrans.app ρ X) h
    change (Φ.preimageIso (e ≪≫ τ ≪≫ e.symm)).hom.app (H.obj X) = _ at this
    rw [this]
    change e.inv.app X ≫ e.hom.app X ≫ (Iso.hom (τ : F' ≅ F')).app X ≫ e.inv.app X ≫
      e.hom.app X = _
    simp

/-- Along an equivalence of Galois categories, fiber functors have isomorphic fundamental
groups, as topological groups. -/
noncomputable def autContinuousMulEquiv [PreGaloisCategory D] (H : C ⥤ D) [H.IsEquivalence]
    {F : D ⥤ FintypeCat.{w}} [FiberFunctor F] {F' : C ⥤ FintypeCat.{w}}
    (e : H ⋙ F ≅ F') : Aut F ≃ₜ* Aut F' :=
  { MulEquiv.ofBijective (autMap H e) (autMap_bijective H e) with
    continuous_toFun := continuous_autMap H e
    continuous_invFun := by
      have : IsHomeomorph (autMap H e) := (isHomeomorph_iff_continuous_bijective).mpr
        ⟨continuous_autMap H e, autMap_bijective H e⟩
      exact this.homeomorph.symm.continuous }

/-- V.6 (surjectivity criterion, one direction): if an exact functor `H` between Galois
categories with `H ⋙ F ≅ F'` sends connected objects to connected objects, the induced
homomorphism of fundamental groups `Aut F → Aut F'` is surjective. -/
lemma autMap_surjective [PreGaloisCategory C] [PreGaloisCategory D] (H : C ⥤ D)
    {F : D ⥤ FintypeCat.{w}} [FiberFunctor F] {F' : C ⥤ FintypeCat.{w}} [FiberFunctor F']
    (e : H ⋙ F ≅ F') (hH : ∀ X : C, IsConnected X → IsConnected (H.obj X)) :
    Function.Surjective (autMap H e) := by
  have : GaloisCategory C :=
    { hasFiberFunctor := ⟨F' ⋙ FintypeCat.uSwitch.{w, u₂}, FiberFunctor.comp_right _⟩ }
  have : GaloisCategory D :=
    { hasFiberFunctor := ⟨F ⋙ FintypeCat.uSwitch.{w, v₂}, FiberFunctor.comp_right _⟩ }
  let _ (X : C) : MulAction (Aut F) (F'.obj X) := MulAction.compHom _ (autMap H e)
  have : IsNaturalSMul F' (Aut F) :=
    ⟨fun σ _ _ f x ↦ (FunctorToFintypeCat.naturality F' F' (autMap H e σ).hom f x).symm⟩
  have (X : C) : ContinuousSMul (Aut F) (F'.obj X) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    exact (stabilizer_isOpen (Aut F') x).preimage (continuous_autMap H e)
  have hsurj := toAut_surjective_of_isPretransitive F' (Aut F) fun X _ ↦ by
    have := hH X inferInstance
    have := FiberFunctor.isPretransitive_of_isConnected F (H.obj X)
    refine ⟨fun x y ↦ ?_⟩
    let x' : F.obj (H.obj X) := e.inv.app X x
    let y' : F.obj (H.obj X) := e.inv.app X y
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) x' y'
    refine ⟨σ, ?_⟩
    change (e.inv.app X ≫ σ.hom.app (H.obj X) ≫ e.hom.app X) x = y
    simp only [FintypeCat.comp_apply]
    change e.hom.app X (σ • x') = y
    rw [hσ]
    simp [y']
  have heq : toAut F' (Aut F) = autMap H e := by
    ext σ X x
    rfl
  rwa [heq] at hsurj

end AutMap

end SGA.SGA1.ExposeV
