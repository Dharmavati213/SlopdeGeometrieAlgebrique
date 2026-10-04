/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.GabberHenselian
import SGA.Foundations.HenselizationNoetherian
import SGA.Foundations.StrictLocalizationLift
import SGA.SGA1.ExposeXIII.CohomologicalProperness
import SGA.SGA1.ExposeXIII.ProperBaseChangeField

/-!
# SGA 1, Exposé XIII, 1.4 over a locally noetherian base

Let `f : X ⟶ Y` be proper with `Y` locally noetherian. Every étale sheaf of sets `F` on `X` is
cohomologically proper for `f` in dimension `≤ 0`
(`SGA.SGA1.ExposeXIII.isCohomologicallyProperLEZero_of_isProper_of_isLocallyNoetherian`): for
every cartesian square `X' = X ×_Y Y'`, `Y'` arbitrary, the base change morphism
`g^* f_* F ⟶ f'_* h^* F` is an isomorphism (`isIso_etaleBaseChangeMap_of_isProper`). This is
XIII 1.4 (the proper base change theorem for `f_*`, SGA 4 XII 5.1) for a locally noetherian `Y`;
SGA states it for every `Y` (`ProperBaseChangeStatement`), which needs the reduction to the
noetherian case by the limit theorems of EGA IV 8 (not done).

The proof is SGA 4's. By the criterion of xiii3
(`AlgebraicGeometry.Scheme.isIso_etaleBaseChangeMap_of_forall_bijective_of_quasiSeparated`, a
consequence of SGA 4 VIII 5.2, registry rows A2 and A31), it suffices that for every geometric
point `ȳ'` of `Y'` the restriction `Γ(P, F) ⟶ Γ(P', F)` is bijective, where
`P = Spec 𝒪^{sh}_{Y,g(ȳ')} ×_Y X` and
`P' = Spec 𝒪^{sh}_{Y',ȳ'} ×_{Y'} X' = Spec 𝒪^{sh}_{Y',ȳ'} ×_Y X`
(`bijective_etaleSectionsRestrict_strictLocalizationPullbackMap`). Both are proper over strictly
henselian local rings, the first one noetherian. Let `P'_Ω` be the fibre of `P'` over the
geometric point `Spec Ω`; it is also the fibre of `P` over `Spec Ω ⟶ Spec 𝒪^{sh}_{Y,g(ȳ')}`.

* `Γ(P, F) ⟶ Γ(P'_Ω, F)` is bijective (`bijective_etaleSectionsRestrict_of_isSepClosed`): it is
  the composite of `Γ(P, F) ⟶ Γ(P₀, F)`, `P₀` the closed fibre (Gabber's theorem, Stacks 0A3S,
  `AlgebraicGeometry.bijective_etaleSectionsRestrict_of_henselianLocalRing`), and of
  `Γ(P₀, F) ⟶ Γ(P'_Ω, F)` (Stacks 0A3H for the geometrically connected `Spec Ω ⟶ Spec κ`, `κ`
  separably closed; xiii3's
  `AlgebraicGeometry.Scheme.bijective_etaleSectionsRestrict_of_geometricallyConnected`).
* `Γ(P', F) ⟶ Γ(P'_Ω, F)` is injective
  (`AlgebraicGeometry.injective_etaleSectionsRestrict_of_range_eq_closedPoint`).

Hence `Γ(P, F) ⟶ Γ(P', F)` is bijective.
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry IsLocalRing
open Scheme (etalePullback etalePullbackComp etaleSectionsRestrict etaleBaseChangeMap)

-- See the comment in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA1.ExposeXIII

section Restrict

variable {T T' T'' : Scheme.{u}}

/-- The components of the isomorphism `c^* b^* G ≅ (c ≫ b)^* G` on global sections are
bijective. -/
lemma bijective_etalePullbackComp_hom_app (c : T'' ⟶ T') (b : T' ⟶ T)
    (G : Sheaf T.smallEtaleTopology (Type u)) :
    Function.Bijective (((etalePullbackComp c b).hom.app G).hom.app (op (Scheme.Etale.top T''))) :=
  (((sheafToPresheaf _ _).mapIso ((etalePullbackComp c b).app G)).app _).toEquiv.bijective

/-- Restriction of global sections along a composite `c ≫ b` is bijective if the restrictions
along `b` and `c` are. -/
lemma bijective_etaleSectionsRestrict_comp (c : T'' ⟶ T') (b : T' ⟶ T)
    (G : Sheaf T.smallEtaleTopology (Type u)) (hb : Function.Bijective (etaleSectionsRestrict b G))
    (hc : Function.Bijective (etaleSectionsRestrict c ((etalePullback b).obj G))) :
    Function.Bijective (etaleSectionsRestrict (c ≫ b) G) := by
  have e : etaleSectionsRestrict (c ≫ b) G =
      ((etalePullbackComp c b).hom.app G).hom.app (op (Scheme.Etale.top T'')) ∘
        etaleSectionsRestrict c ((etalePullback b).obj G) ∘ etaleSectionsRestrict b G :=
    funext fun x ↦
      (Scheme.etalePullbackComp_hom_app_etaleSectionsRestrict_etaleSectionsRestrict c b G x).symm
  rw [e]
  exact (bijective_etalePullbackComp_hom_app c b G).comp (hc.comp hb)

/-- Restriction of global sections along `b` is bijective if the restriction along `c ≫ b` is
bijective and the restriction along `c` is injective. -/
lemma bijective_etaleSectionsRestrict_of_comp (c : T'' ⟶ T') (b : T' ⟶ T)
    (G : Sheaf T.smallEtaleTopology (Type u))
    (hcb : Function.Bijective (etaleSectionsRestrict (c ≫ b) G))
    (hc : Function.Injective (etaleSectionsRestrict c ((etalePullback b).obj G))) :
    Function.Bijective (etaleSectionsRestrict b G) := by
  let φ := ((etalePullbackComp c b).hom.app G).hom.app (op (Scheme.Etale.top T''))
  have hφ := bijective_etalePullbackComp_hom_app c b G
  have e (x) : φ (etaleSectionsRestrict c _ (etaleSectionsRestrict b G x)) =
      etaleSectionsRestrict (c ≫ b) G x :=
    Scheme.etalePullbackComp_hom_app_etaleSectionsRestrict_etaleSectionsRestrict c b G x
  refine ⟨fun x x' h ↦ hcb.1 ?_, fun y ↦ ?_⟩
  · rw [← e, ← e, h]
  · obtain ⟨x, hx⟩ := hcb.2 (φ (etaleSectionsRestrict c _ y))
    exact ⟨x, hc (hφ.1 ((e x).trans hx))⟩

/-- Bijectivity of the restriction along `m` only depends on `m` up to equality. -/
lemma bijective_etaleSectionsRestrict_of_eq {m b : T' ⟶ T} (h : m = b)
    (G : Sheaf T.smallEtaleTopology (Type u)) (H : Function.Bijective (etaleSectionsRestrict b G)) :
    Function.Bijective (etaleSectionsRestrict m G) := by
  subst h
  exact H

end Restrict

/-- **Sections over a geometric fibre of a proper scheme over a strictly henselian noetherian
local ring** (Stacks 0A3S with 0A3H): let `A` be a noetherian henselian local ring with
separably closed residue field, `q : Z ⟶ Spec A` proper, `α : A ⟶ Ω` a local homomorphism to an
algebraically closed field and `Z_Ω = Z ×_A Spec Ω`. Then `Γ(Z, F) ⟶ Γ(Z_Ω, F)` is bijective for
every étale sheaf of sets `F` on `Z`. -/
theorem bijective_etaleSectionsRestrict_of_isSepClosed {A : CommRingCat.{u}}
    [HenselianLocalRing A] [IsNoetherianRing A] [IsSepClosed (ResidueField A)] {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (α : A ⟶ .of Ω) [IsLocalHom α.hom] {Z T : Scheme.{u}}
    (q : Z ⟶ Spec A) [IsProper q] {i : T ⟶ Z} {qT : T ⟶ Spec (.of Ω)}
    (hi : IsPullback i qT q (Spec.map α)) (F : Sheaf Z.smallEtaleTopology (Type u)) :
    Function.Bijective (etaleSectionsRestrict i F) := by
  let κ := ResidueField A
  let _ : Algebra κ Ω := (ResidueField.lift α.hom).toAlgebra
  let a := Spec.map (CommRingCat.ofHom (algebraMap κ Ω))
  let r := Spec.map (CommRingCat.ofHom (residue A))
  have har : a ≫ r = Spec.map α := by
    rw [← Spec.map_comp]
    congr 1
  let i₀ := pullback.fst q r
  let b : T ⟶ pullback q r := pullback.lift i (qT ≫ a) (by rw [Category.assoc, har, hi.w])
  have hbi : b ≫ i₀ = i := pullback.lift_fst _ _ _
  have hb : IsPullback b qT (pullback.snd q r) a := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q r)
    rw [hbi, har]
    exact hi
  have : GeometricallyConnected a := geometricallyConnected_specMap_of_isSepClosed κ Ω
  have : Flat a := Flat.SpecMap_iff.mpr (by
    change (algebraMap κ Ω).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance)
  have : Flat b := MorphismProperty.of_isPullback hb.flip inferInstance
  have : QuasiCompact b := MorphismProperty.of_isPullback hb.flip inferInstance
  have : GeometricallyConnected b :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hb.flip inferInstance
  exact bijective_etaleSectionsRestrict_of_eq hbi.symm F
    (bijective_etaleSectionsRestrict_comp b i₀ F
      (bijective_etaleSectionsRestrict_of_henselianLocalRing q (IsPullback.of_hasPullback q r) F)
      (Scheme.bijective_etaleSectionsRestrict_of_geometricallyConnected b _))

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}
  [IsProper f] [IsLocallyNoetherian Y]

/-- **XIII 1.4, the stalk computation** (SGA 4 XII 5.1, over a locally noetherian base): for a
cartesian square `X' = X ×_Y Y'` with `f` proper and `Y` locally noetherian, and a geometric point
`ȳ'` of `Y'` (`Ω` algebraically closed), the restriction
`Γ(Spec 𝒪^{sh}_{Y,g(ȳ')} ×_Y X, F) ⟶ Γ(Spec 𝒪^{sh}_{Y',ȳ'} ×_{Y'} X', F)` is bijective. -/
theorem bijective_etaleSectionsRestrict_strictLocalizationPullbackMap
    (hsq : IsPullback h f' f g) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y') (F : Sheaf X.smallEtaleTopology (Type u)) :
    Function.Bijective (etaleSectionsRestrict (Scheme.strictLocalizationPullbackMap hsq.w y)
      ((etalePullback (pullback.snd (y ≫ g).fromSpecStrictLocalization f)).obj F)) := by
  let A := (y ≫ g).strictLocalization
  have : IsNoetherianRing A := by
    let := (y ≫ g).residueFieldAlgebra
    let := (y ≫ g).stalkAlgebra
    have := Scheme.Hom.isScalarTower_stalkAlgebra (y ≫ g)
    have := isLocalHom_algebraMap_of_isScalarTower
      (R := Y.presheaf.stalk (y ≫ g).imagePoint) (K := Ω)
    exact inferInstanceAs
      (IsNoetherianRing (StrictHenselization (Y.presheaf.stalk (y ≫ g).imagePoint) Ω))
  let qP := pullback.fst (y ≫ g).fromSpecStrictLocalization f
  let qP' := pullback.fst y.fromSpecStrictLocalization f'
  have : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
  let Q := Scheme.strictLocalizationPullbackMap hsq.w y
  have hQ : IsPullback Q qP' qP (g.strictLocalizationMap y) :=
    Scheme.isPullback_strictLocalizationPullbackMap y hsq
  let α' := y.strictLocalizationToField
  let α := (y ≫ g).strictLocalizationToField
  have hαα : Spec.map α' ≫ g.strictLocalizationMap y = Spec.map α :=
    Scheme.Hom.toSpecStrictLocalization_strictLocalizationMap y g
  let c := pullback.fst qP' (Spec.map α')
  have hc : IsPullback c (pullback.snd qP' (Spec.map α')) qP' (Spec.map α') :=
    IsPullback.of_hasPullback _ _
  have hcQ : IsPullback (c ≫ Q) (pullback.snd qP' (Spec.map α')) qP (Spec.map α) := by
    rw [← hαα]
    exact hc.paste_horiz hQ
  exact bijective_etaleSectionsRestrict_of_comp c Q _
    (bijective_etaleSectionsRestrict_of_isSepClosed α qP hcQ _)
    (injective_etaleSectionsRestrict_of_range_eq_closedPoint qP' hc
      (range_specMap_eq_singleton_closedPoint α') _)

/-- **XIII 1.4, base change form** (SGA 4 XII 5.1, over a locally noetherian base): for a
cartesian square `X' = X ×_Y Y'` with `f` proper and `Y` locally noetherian (`Y'` arbitrary), the
base change morphism `g^* f_* F ⟶ f'_* h^* F` is an isomorphism for every étale sheaf of sets
`F` on `X`. -/
theorem isIso_etaleBaseChangeMap_of_isProper (hsq : IsPullback h f' f g)
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    IsIso ((etaleBaseChangeMap hsq.w).app F) :=
  Scheme.isIso_etaleBaseChangeMap_of_forall_bijective_of_quasiSeparated F hsq fun _ _ _ y ↦
    Scheme.bijective_etaleSquareRestrict F _ _ _ _ _
      (bijective_etaleSectionsRestrict_strictLocalizationPullbackMap hsq y F)

variable (f) in
/-- **SGA 1 XIII 1.4 for a locally noetherian base**: for `f : X ⟶ Y` proper with `Y` locally
noetherian, every étale sheaf of sets `F` on `X` is cohomologically proper for `f` in dimension
`≤ 0` (relative to `Y`). (SGA states this for every `Y`, `ProperBaseChangeStatement`; the extra
hypothesis is that `Y` be locally noetherian.) -/
theorem isCohomologicallyProperLEZero_of_isProper_of_isLocallyNoetherian
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    IsCohomologicallyProperLEZero (𝟙 Y) f F :=
  fun _ _ _ _ _ _ _ _ _ hX ↦ isIso_etaleBaseChangeMap_of_isProper hX F

end BaseChange

section Consequences

variable {S Z X Y : Scheme.{u}}

/-- XIII 1.8 for sheaves of sets, dimension `≤ 0`, over a locally noetherian base (from 1.6 1) and
1.4 over a locally noetherian base): if `(F, f)` is cohomologically proper relative to `S` in
dimension `≤ 0` and `g : Y ⟶ Z` is proper with `Z` locally noetherian, then `(F, f ≫ g)` is
cohomologically proper relative to `S` in dimension `≤ 0`.
(`IsCohomologicallyProperLEZero.comp_of_isProper` takes XIII 1.4 for every base as a hypothesis
instead.) -/
theorem IsCohomologicallyProperLEZero.comp_of_isProper_of_isLocallyNoetherian {sZ : Z ⟶ S}
    {f : X ⟶ Y} {g : Y ⟶ Z} [IsProper g] [IsLocallyNoetherian Z]
    {F : Sheaf X.smallEtaleTopology (Type u)} (hf : IsCohomologicallyProperLEZero (g ≫ sZ) f F) :
    IsCohomologicallyProperLEZero sZ (f ≫ g) F :=
  hf.comp ((isCohomologicallyProperLEZero_of_isProper_of_isLocallyNoetherian g _).of_id sZ)

/-- XIII 1.4 for sheaves coming from a locally noetherian base: if `X = X₀ ×_{Y₀} Y` with
`f₀ : X₀ ⟶ Y₀` proper and `Y₀` locally noetherian (`Y` arbitrary), then for every étale sheaf of
sets `F₀` on `X₀` the inverse image `h^* F₀` is cohomologically proper for `f : X ⟶ Y` in dimension
`≤ 0` (XIII 1.5 c) applied to 1.4 over `Y₀`). -/
theorem isCohomologicallyProperLEZero_etalePullback_of_isLocallyNoetherian {X₀ Y₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Y₀) [IsProper f₀] [IsLocallyNoetherian Y₀] {g : Y ⟶ Y₀} {h : X ⟶ X₀}
    {f : X ⟶ Y} (hsq : IsPullback h f f₀ g) (F₀ : Sheaf X₀.smallEtaleTopology (Type u)) :
    IsCohomologicallyProperLEZero (𝟙 Y) f ((etalePullback h).obj F₀) :=
  (isCohomologicallyProperLEZero_of_isProper_of_isLocallyNoetherian f₀ F₀).baseChange
    (IsPullback.of_vert_isIso ⟨(Category.comp_id g).trans (Category.id_comp g).symm⟩ :
      IsPullback g (𝟙 Y) (𝟙 Y₀) g) hsq

end Consequences

end SGA.SGA1.ExposeXIII
