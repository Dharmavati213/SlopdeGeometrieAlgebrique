/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.LocalAcyclicityStrictLocalization
import SGA.SGA1.ExposeX.SpecializationGeometric
import SGA.SGA1.ExposeXIII.LocalAcyclicityField

/-!
# SGA 1, Exposé XIII, 3.2 1) over any field, from SGA 4 VIII 5.2

XIII.3.2 1) (`SGA.SGA1.ExposeXIII.FieldCohomologicalPropernessStatement`): for a coherent
`f : X ⟶ Spec k`, `k` any field, the formation of `f_* F` commutes with every base change, for
every étale sheaf of sets `F` on `X`. We prove it from SGA 4 VIII 5.2
(`AlgebraicGeometry.Scheme.Hom.bijective_pushforwardStalkToStrictLocalization`):
`SGA.SGA1.ExposeXIII.fieldCohomologicalPropernessStatement`. Its dimension
`≤ -1` part (the base change morphisms are monomorphisms) holds for every quasi-compact `f`
(`SGA.SGA1.ExposeXIII.isCohomologicallyProperLENegOne_of_field`).

This is not SGA's proof (which goes through XIII 3.1, i.e. the proper base change theorem and
constructibility, then a passage to the limit), but that of Stacks 0EZY, made pointwise: at a
geometric point `ȳ'` of the base change `Y' ⟶ Spec k`, the stalk of the base change morphism is
the restriction `Γ(X ×_k Ỹ, F) ⟶ Γ(X ×_k Ỹ', F)` along the morphism of strict localizations
`Ỹ' ⟶ Ỹ`
(`AlgebraicGeometry.Scheme.pushforwardStalkToStrictLocalization_sheafFiber_etaleBaseChangeMap`).
Here `Ỹ` is the strict localization of `Spec k`, the spectrum of a separably closed field, and
`Ỹ'` is local, so `Ỹ' ⟶ Ỹ` is flat, quasi-compact and geometrically connected
(`SGA.SGA1.ExposeXIII.geometricallyConnected_of_isSepClosed`), and the restriction is bijective by
Stacks 0A3H (`SGA.SGA1.ExposeXIII.bijective_etaleSquareRestrict_of_field`).

The same geometric connectedness shows that every morphism to the spectrum of a field is locally
`0`-acyclic in the Milnor-fibre sense (`SGA.SGA1.ExposeXIII.isLocallyZeroAcyclic_of_field`; the
universal version is SGA 4 XV 2.1 and 4.1).

## References

* [SGA 4, Exposé VIII, 5.2][sga4]
* [Stacks Project, Tag 0EZY](https://stacks.math.columbia.edu/tag/0EZY)
* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA1.ExposeXIII

variable {k : Type u} [Field k] {Y' : Scheme.{u}} (g : Y' ⟶ Spec (.of k)) {Ω : Type u} [Field Ω]
  [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y')

/-- For `g : Y' ⟶ Spec k` and a geometric point `ȳ'` of `Y'`, the morphism of strict localizations
`Ỹ' ⟶ Ỹ` is flat, quasi-compact and geometrically connected: `Ỹ` is the spectrum of a separably
closed field and `Ỹ'` is local. -/
lemma flat_quasiCompact_geometricallyConnected_strictLocalizationMap :
    Flat (g.strictLocalizationMap y) ∧ QuasiCompact (g.strictLocalizationMap y) ∧
      GeometricallyConnected (g.strictLocalizationMap y) := by
  let R := (y ≫ g).strictLocalization
  have hbij : Function.Bijective (IsLocalRing.residue R) :=
    (y ≫ g).bijective_residue_strictLocalization
      (Scheme.isField_stalk_spec k (y ≫ g).imagePoint)
  let ψ : R ⟶ CommRingCat.of (IsLocalRing.ResidueField R) :=
    CommRingCat.ofHom (IsLocalRing.residue R)
  have : IsIso ψ := (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
  have : IsIso (Spec.map ψ) := inferInstance
  let σ' := g.strictLocalizationMap y ≫ inv (Spec.map ψ)
  have hσ : g.strictLocalizationMap y = σ' ≫ Spec.map ψ := by simp [σ']
  -- `ExposeX.connectedSpace_primeSpectrum_of_isLocalRing`
  have : ConnectedSpace (Spec y.strictLocalization) :=
    inferInstanceAs (ConnectedSpace (PrimeSpectrum y.strictLocalization))
  have h₁ : GeometricallyConnected σ' := geometricallyConnected_of_isSepClosed σ'
  have h₂ : Flat σ' := by
    rw [← Spec.map_preimage σ', Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField _) _
  have h₃ : QuasiCompact σ' :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance
  rw [hσ]
  exact ⟨inferInstance, inferInstance,
    (MorphismProperty.cancel_right_of_respectsIso (P := @GeometricallyConnected) _ _).mpr h₁⟩

variable {X X' : Scheme.{u}} {f : X ⟶ Spec (.of k)} {h : X' ⟶ X} {f' : X' ⟶ Y'}

/-- **Stacks 0A3H at strict localizations over a field**: for a cartesian square
`X' = X ×_k Y'` and a geometric point `ȳ'` of `Y'`, the restriction
`Γ(X ×_k Ỹ, F) ⟶ Γ(X' ×_{Y'} Ỹ', h^* F)` along the morphism of strict localizations is bijective. -/
theorem bijective_etaleSquareRestrict_of_field (hsq : IsPullback h f' f g)
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    Function.Bijective (Scheme.etaleSquareRestrict F (pullback.snd _ _) (pullback.snd _ _) h
      (Scheme.strictLocalizationPullbackMap hsq.w y)
      (Scheme.strictLocalizationPullbackMap_snd hsq.w y)) := by
  obtain ⟨h₁, -, h₃⟩ := flat_quasiCompact_geometricallyConnected_strictLocalizationMap g y
  exact Scheme.bijective_etaleSquareRestrict_of_flat_of_geometricallyConnected y hsq F

/-- XIII.3.2 1) in dimension `≤ -1`, unconditionally: for a quasi-compact morphism
`f : X ⟶ Spec k` to the spectrum of a field and every étale sheaf of sets `F` on `X`, the base
change morphisms `g^* f_* F ⟶ f'_* h^* F` are monomorphisms, for every base change
`Y' ⟶ Spec k`. -/
theorem isCohomologicallyProperLENegOne_of_field (f : X ⟶ Spec (.of k)) [QuasiCompact f]
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    IsCohomologicallyProperLENegOne (𝟙 _) f F := by
  intro S' Y' X' t s' g h f' _ hX
  exact Scheme.mono_etaleBaseChangeMap_of_forall_injective F hX.w
    fun Ω _ _ y ↦ (bijective_etaleSquareRestrict_of_field g y hX F).1

/-- **XIII.3.2 1)** (`FieldCohomologicalPropernessStatement`): for every field `k`, every coherent
(quasi-compact and quasi-separated) `f : X ⟶ Spec k` and every étale sheaf of sets `F` on `X`, the
formation of `f_* F` commutes with every change of base `S' ⟶ Spec k`. (SGA proves it for coherent
`f` through XIII 3.1 and a limit argument; here through the stalks at strict localizations, SGA 4
VIII 5.2, and Stacks 0A3H.) -/
theorem fieldCohomologicalPropernessStatement : FieldCohomologicalPropernessStatement.{u} := by
  intro k _ X f _ _ F S' Y' X' t s' g h f' _ hX
  exact Scheme.isIso_etaleBaseChangeMap_of_forall_bijective_of_quasiSeparated F hX
    fun Ω _ _ y ↦ bijective_etaleSquareRestrict_of_field g y hX F

/-- Over a field, every morphism is locally `0`-acyclic (SGA 4 XV 1.11, Milnor-fibre form; not
*universally*, which is the content of SGA 4 XV 2.1 and 4.1): the strict localization of `Spec k` is
the spectrum of a separably closed field, over which the local scheme `Spec 𝒪^{sh}_{X,x̄}` is
geometrically connected, so all its Milnor fibres are nonempty and connected. -/
theorem isLocallyZeroAcyclic_of_field {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    f.IsLocallyZeroAcyclic := by
  intro Ω _ _ x K _ _ t _
  obtain ⟨-, -, h₃⟩ := flat_quasiCompact_geometricallyConnected_strictLocalizationMap f x
  exact pullback_of_geometrically h₃.geometrically_connectedSpace K t

end SGA.SGA1.ExposeXIII
