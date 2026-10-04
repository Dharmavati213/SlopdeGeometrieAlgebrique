/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.LocalAcyclicity
import SGA.Foundations.Etale.LocalAcyclicityStrictLocalization
import SGA.Foundations.Fields.GeometricallyConnected
import SGA.Foundations.StrictLocalizationFunctorialFlat

/-!
# From the Milnor-fibre form to the base-change form of local `0`-acyclicity

Let `g : Y' ⟶ Y` be locally `0`-acyclic in the sense of SGA 4 XV 1.11
(`AlgebraicGeometry.Scheme.Hom.IsLocallyZeroAcyclic`: its Milnor fibres over algebraic geometric
points are nonempty and connected). Then for every geometric point `ȳ'` of `Y'` the morphism of
strict localizations `Ỹ' ⟶ Ỹ` is geometrically connected
(`AlgebraicGeometry.Scheme.Hom.geometricallyConnected_strictLocalizationMap`): its fibre over a
point `Spec L ⟶ Ỹ` becomes, after the extension `L ⊆ L̄`, a base change of a Milnor fibre over an
algebraically closed field, which is geometrically connected
(`AlgebraicGeometry.geometricallyConnected_of_isAlgClosed`).

If moreover the morphisms of strict localizations of `g` are flat (true for `g` flat,
`AlgebraicGeometry.Scheme.Hom.flat_strictLocalizationMap`), base change along `g` holds for
direct images of étale sheaves of sets: for a cartesian square `X' = X ×_Y Y'` with `f`
quasi-compact, `g^* f_* F ⟶ f'_* h^* F` is a monomorphism
(`Scheme.mono_etaleBaseChangeMap_of_isLocallyZeroAcyclic_of_flat_strictLocalizationMap`),
and an isomorphism if `f` is moreover quasi-separated
(`Scheme.isIso_etaleBaseChangeMap_of_isLocallyZeroAcyclic_of_flat_strictLocalizationMap`):
through
`AlgebraicGeometry.Scheme.pushforwardStalkToStrictLocalization_sheafFiber_etaleBaseChangeMap` the
stalks compare sections over `Ỹ ×_Y X` and `Ỹ' ×_Y X`, and Stacks 0A3H applies to `Ỹ' ⟶ Ỹ`.
This is a degree-`0` analogue of base change along a locally acyclic morphism (the mechanism of
the smooth base change theorem, SGA 4 XV §1 and XVI), proved here with the flatness hypothesis,
which Stacks 0A3H needs; SGA's own route applies its results on locally `0`-acyclic coherent
morphisms to `Ỹ' ⟶ Ỹ` and needs no flatness. With SGA 4 XV 2.1 (smooth morphisms are locally
acyclic) it gives smooth base change in degree `0`. For flat `g` the flatness hypothesis is
automatic: `AlgebraicGeometry.Scheme.mono_etaleBaseChangeMap_of_flat_of_isLocallyZeroAcyclic`,
`AlgebraicGeometry.Scheme.isIso_etaleBaseChangeMap_of_flat_of_isLocallyZeroAcyclic`. Hence a flat
universally locally `0`-acyclic morphism satisfies the base-change form of
`AlgebraicGeometry.Scheme.Hom.IsUniversallyZeroAcyclicBaseChange` for all quasi-compact
quasi-separated `g` (`Scheme.Hom.IsUniversallyLocallyZeroAcyclic.isIso_etaleBaseChangeMap`).

## References

* [SGA 4, Exposé XV, 1.11][sga4]
* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
-/

universe u

open CategoryTheory Limits

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-- The geometric point `Spec K ⟶ T` given by a point `t` and an embedding `κ(t) ⟶ K` is algebraic
if the embedding is integral. -/
lemma AlgebraicGeometry.Scheme.isAlgebraicPoint_SpecToEquivOfField_symm {T : Scheme.{u}}
    {K : Type u} [Field K] (t : T) (ψ : T.residueField t ⟶ .of K) (hψ : ψ.hom.IsIntegral) :
    ((SpecToEquivOfField K T).symm ⟨t, ψ⟩).IsAlgebraicPoint := by
  have key : ∀ q : Σ x, T.residueField x ⟶ .of K, q = ⟨t, ψ⟩ → q.2.hom.IsIntegral := by
    rintro q rfl
    exact hψ
  exact key _ (Equiv.apply_symm_apply _ _)

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism `σ : A ⟶ B` all of whose fibres over algebraically closed algebraic geometric points
of `B` are connected (and nonempty) is geometrically connected: for `Spec L ⟶ B` over `b ∈ B`,
the fibre `A ×_B Spec L̄` is the base change of the fibre over `Spec κ(b)‾`, which is geometrically
connected over the algebraically closed field `κ(b)‾`, and maps onto `A ×_B Spec L`. -/
theorem geometricallyConnected_of_forall_isAlgClosed {A B : Scheme.{u}} (σ : A ⟶ B)
    (H : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ B), t.IsAlgebraicPoint →
      ConnectedSpace ↥(pullback σ t : Scheme.{u})) :
    GeometricallyConnected σ := by
  refine ⟨(geometrically_iff_of_isClosedUnderIsomorphisms (P := (ConnectedSpace ·))).mpr
    fun L _ y ↦ ?_⟩
  obtain ⟨⟨b, φ⟩, rfl⟩ := (SpecToEquivOfField L B).symm.surjective y
  let κ := B.residueField b
  let K := AlgebraicClosure κ
  let M := AlgebraicClosure L
  let := φ.hom.toAlgebra
  let ι : K →ₐ[κ] M := IsAlgClosed.lift
  let t : Spec (.of K) ⟶ B := (SpecToEquivOfField K B).symm ⟨b, CommRingCat.ofHom (algebraMap κ K)⟩
  have ht : t.IsAlgebraicPoint := isAlgebraicPoint_SpecToEquivOfField_symm b _
    (Algebra.IsIntegral.isIntegral (R := κ) (A := K))
  have : ConnectedSpace ↥(pullback σ t : Scheme.{u}) := H K t ht
  have : GeometricallyConnected (pullback.snd σ t) := geometricallyConnected_of_isAlgClosed _
  -- the two maps `Spec M ⟶ B` agree
  have hcomm : Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ t =
      Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫
        (SpecToEquivOfField L B).symm ⟨b, φ⟩ := by
    simp only [t, SpecToEquivOfField, Equiv.coe_fn_symm_mk, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext x
    exact (ι.commutes x).trans (IsScalarTower.algebraMap_apply κ L M x)
  -- `A ×_B Spec M` is connected
  let ι' := Spec.map (CommRingCat.ofHom ι.toRingHom)
  let j := Spec.map (CommRingCat.ofHom (algebraMap L M))
  have h₁ : ConnectedSpace ↥(pullback σ (ι' ≫ t) : Scheme.{u}) := by
    have : ConnectedSpace ↥(pullback (pullback.snd σ t) ι' : Scheme.{u}) :=
      pullback_of_geometrically
        (GeometricallyConnected.geometrically_connectedSpace (f := pullback.snd σ t)) _ _
    exact (pullbackLeftPullbackSndIso σ t ι').hom.homeomorph.connectedSpace_iff.mp this
  rw [hcomm] at h₁
  -- and maps onto `A ×_B Spec L`
  have : Surjective j := ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : ConnectedSpace
      ↥(pullback (pullback.snd σ ((SpecToEquivOfField L B).symm ⟨b, φ⟩)) j : Scheme.{u}) :=
    (pullbackLeftPullbackSndIso σ _ j).hom.homeomorph.connectedSpace_iff.mpr h₁
  let π := pullback.fst (pullback.snd σ ((SpecToEquivOfField L B).symm ⟨b, φ⟩)) j
  exact (Scheme.Hom.surjective π).connectedSpace π.continuous

/-- If `g` is locally `0`-acyclic (Milnor-fibre form), its morphisms of strict localizations
`Spec 𝒪^{sh}_{Y',ȳ'} ⟶ Spec 𝒪^{sh}_{Y,g(ȳ')}` are geometrically connected. -/
theorem geometricallyConnected_strictLocalizationMap {Y' Y : Scheme.{u}} {g : Y' ⟶ Y}
    (hg : g.IsLocallyZeroAcyclic) {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y') :
    GeometricallyConnected (g.strictLocalizationMap y) :=
  geometricallyConnected_of_forall_isAlgClosed _ fun K _ _ t ht ↦ hg Ω y K t ht

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}

/-- **Local `0`-acyclicity implies base change, injectivity** (degree `0`, with a flatness
hypothesis): let `g : Y' ⟶ Y` be locally `0`-acyclic (Milnor-fibre form) with flat morphisms of
strict localizations. For a cartesian square `X' = X ×_Y Y'` with `f` quasi-compact,
the base change morphism `g^* f_* F ⟶ f'_* h^* F` is a monomorphism. -/
theorem mono_etaleBaseChangeMap_of_isLocallyZeroAcyclic_of_flat_strictLocalizationMap
    (hsq : IsPullback h f' f g)
    [QuasiCompact f] (hg : g.IsLocallyZeroAcyclic)
    (hflat : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y'),
      Flat (g.strictLocalizationMap y))
    (F : Sheaf X.smallEtaleTopology (Type u)) : Mono ((etaleBaseChangeMap hsq.w).app F) :=
  mono_etaleBaseChangeMap_of_forall_injective F hsq.w fun Ω _ _ y ↦
    have := hflat Ω y
    have := Hom.geometricallyConnected_strictLocalizationMap hg y
    (bijective_etaleSquareRestrict_of_flat_of_geometricallyConnected y hsq F).1

/-- **Local `0`-acyclicity implies base change** (degree `0`, with a flatness hypothesis): let
`g : Y' ⟶ Y` be locally `0`-acyclic (Milnor-fibre form) with flat morphisms of strict
localizations. For a cartesian square `X' = X ×_Y Y'` with `f` quasi-compact and quasi-separated,
the base change morphism `g^* f_* F ⟶ f'_* h^* F` is an isomorphism (through SGA 4 VIII 5.2,
`AlgebraicGeometry.Scheme.Hom.bijective_pushforwardStalkToStrictLocalization`). -/
theorem isIso_etaleBaseChangeMap_of_isLocallyZeroAcyclic_of_flat_strictLocalizationMap
    (hsq : IsPullback h f' f g)
    [QuasiCompact f] [QuasiSeparated f] (hg : g.IsLocallyZeroAcyclic)
    (hflat : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y'),
      Flat (g.strictLocalizationMap y))
    (F : Sheaf X.smallEtaleTopology (Type u)) : IsIso ((etaleBaseChangeMap hsq.w).app F) :=
  isIso_etaleBaseChangeMap_of_forall_bijective_of_quasiSeparated F hsq fun Ω _ _ y ↦
    have := hflat Ω y
    have := Hom.geometricallyConnected_strictLocalizationMap hg y
    bijective_etaleSquareRestrict_of_flat_of_geometricallyConnected y hsq F

/-- **Base change along a flat locally `0`-acyclic morphism, injectivity** (degree `0`): let
`g : Y' ⟶ Y` be flat and locally `0`-acyclic (Milnor-fibre form). For a cartesian square
`X' = X ×_Y Y'` with `f` quasi-compact, the base change morphism `g^* f_* F ⟶ f'_* h^* F` is a
monomorphism. -/
theorem mono_etaleBaseChangeMap_of_flat_of_isLocallyZeroAcyclic (hsq : IsPullback h f' f g)
    [QuasiCompact f] [Flat g] (hg : g.IsLocallyZeroAcyclic)
    (F : Sheaf X.smallEtaleTopology (Type u)) : Mono ((etaleBaseChangeMap hsq.w).app F) :=
  mono_etaleBaseChangeMap_of_isLocallyZeroAcyclic_of_flat_strictLocalizationMap hsq hg
    (fun _ _ _ _ ↦ inferInstance) F

/-- **Base change along a flat locally `0`-acyclic morphism** (degree `0`): let `g : Y' ⟶ Y` be
flat and locally `0`-acyclic (Milnor-fibre form). For a cartesian square `X' = X ×_Y Y'` with `f`
quasi-compact and quasi-separated, the base change morphism `g^* f_* F ⟶ f'_* h^* F` is an
isomorphism. -/
theorem isIso_etaleBaseChangeMap_of_flat_of_isLocallyZeroAcyclic (hsq : IsPullback h f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] (hg : g.IsLocallyZeroAcyclic)
    (F : Sheaf X.smallEtaleTopology (Type u)) : IsIso ((etaleBaseChangeMap hsq.w).app F) :=
  isIso_etaleBaseChangeMap_of_isLocallyZeroAcyclic_of_flat_strictLocalizationMap hsq hg
    (fun _ _ _ _ ↦ inferInstance) F

/-- **Milnor-fibre form ⇒ base-change form** (degree `0`, for flat morphisms and quasi-compact
quasi-separated `g`): let `f : X ⟶ S` be flat and universally locally `0`-acyclic (Milnor-fibre
form). For every base change `f' : X' ⟶ S'` of `f`, every quasi-compact quasi-separated
`g : T ⟶ S'` and every étale sheaf of sets `F` on `T`, the base change morphism
`f'^* g_* F ⟶ h_* e^* F` is an isomorphism. This is the condition of
`AlgebraicGeometry.Scheme.Hom.IsUniversallyZeroAcyclicBaseChange` restricted to quasi-compact
quasi-separated `g`. -/
theorem Hom.IsUniversallyLocallyZeroAcyclic.isIso_etaleBaseChangeMap {S X : Scheme.{u}}
    {f : X ⟶ S} [Flat f] (hf : f.IsUniversallyLocallyZeroAcyclic) {S' X' : Scheme.{u}}
    (s : S' ⟶ S) (s' : X' ⟶ X) (f' : X' ⟶ S') (h₁ : IsPullback s' f' f s) {T Y : Scheme.{u}}
    (g : T ⟶ S') [QuasiCompact g] [QuasiSeparated g] (h : Y ⟶ X') (e : Y ⟶ T)
    (hsq : IsPullback h e f' g) (F : Sheaf T.smallEtaleTopology (Type u)) :
    IsIso ((etaleBaseChangeMap hsq.flip.w).app F) :=
  have : Flat f' := MorphismProperty.of_isPullback h₁ ‹_›
  isIso_etaleBaseChangeMap_of_flat_of_isLocallyZeroAcyclic hsq.flip (hf s s' f' h₁) F

end AlgebraicGeometry.Scheme
