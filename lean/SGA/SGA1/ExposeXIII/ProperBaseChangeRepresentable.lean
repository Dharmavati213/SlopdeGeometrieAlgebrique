/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.EtaleStalkProperLimit
import SGA.Foundations.HenselizationNoetherian
import SGA.SGA1.ExposeXIII.LocallyConstantSheaves
import SGA.SGA1.ExposeXIII.ProperBaseChange
import SGA.SGA1.ExposeXIII.ProperBaseChangeField
import SGA.SGA1.ExposeXIII.ProperBaseChangeHenselian

/-!
# SGA 1, Exposé XIII, 1.4 for sheaves represented by étale schemes

Let `f : X ⟶ Y` be proper with `Y` locally noetherian, and `E` an étale `X`-scheme which is
separated over `X` (for instance a finite étale covering of `X`, or an affine étale `X`-scheme).
We prove that the sheaf `h_E` represented by `E` is cohomologically proper for `f` in dimension
`≤ 0` (`isCohomologicallyProperLEZero_etaleYoneda`): the formation of `f_* h_E` commutes with
every base change `Y' ⟶ Y`, `Y'` arbitrary. Hence so are the constant sheaves with finite values
(`isCohomologicallyProperLEZero_constantSheaf`) and the locally constant sheaves with finite
values (`isCohomologicallyProperLEZero_of_isLocallyConstantFiniteSheaf`).

By `AlgebraicGeometry.Scheme.isIso_etaleBaseChangeMap_etaleYoneda_of_extendsAlongGeometricFibres`
it suffices that every `X`-morphism `X_ȳ ⟶ E` from a geometric fibre extends to `X ×_Y V` for an
étale neighbourhood `V` of `ȳ` (`extendsAlongGeometricFibres_of_isProper`). This is the
composite of three steps, with `A = 𝒪^{sh}_{Y,ȳ}` (noetherian and strictly henselian), `κ` its
residue field (separably closed) and `P = X ×_Y Spec A`:

* from `X_ȳ = P ×_κ Spec Ω` to the closed fibre `P₀ = P ×_A κ`: `Spec Ω ⟶ Spec κ` has
  geometrically connected fibres (`exists_hom_of_isPullback_specMap_of_isSepClosed`);
* from `P₀` to `P`: henselian lifting of sections (`exists_section_of_henselianLocalRing`);
* from `P` to some `X ×_Y V`: passage to the limit
  (`AlgebraicGeometry.Scheme.extendsAlongGeometricFibres_of_strictLocalization`).

This avoids Gabber's lemma, which the general case of XIII 1.4 needs (non-separated sheaves); the
general case over a locally noetherian base is `SGA.SGA1.ExposeXIII.ProperBaseChangeNoetherian`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open Scheme (etalePullback etalePushforward etaleBaseChangeMap etaleYoneda)

-- See the comment in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA1.ExposeXIII

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section Extension

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)

omit [IsSepClosed Ω] in
/-- The geometric fibre `X_ȳ` is the fibre of `P = X ×_Y Spec 𝒪^{sh}_{Y,ȳ}` over `Spec Ω`. -/
lemma isPullback_geometricFibreToStrictLocalization :
    IsPullback (f.geometricFibreToStrictLocalization y) (pullback.snd f y)
      (pullback.fst y.fromSpecStrictLocalization f) y.toSpecStrictLocalization := by
  refine IsPullback.of_right (h₁₂ := pullback.snd y.fromSpecStrictLocalization f)
    (h₂₂ := y.fromSpecStrictLocalization) (v₁₃ := f) ?_
    (f.geometricFibreToStrictLocalization_fst y)
    (IsPullback.of_hasPullback y.fromSpecStrictLocalization f).flip
  rw [f.geometricFibreToStrictLocalization_snd y,
    Scheme.Hom.toSpecStrictLocalization_fromSpecStrictLocalization]
  exact IsPullback.of_hasPullback f y

variable [IsProper f] [IsLocallyNoetherian Y]

/-- **XIII 1.4 for represented sheaves, the stalk computation** (Stacks 0A3T, surjectivity, for
`h_E`): for `f` proper with `Y` locally noetherian, every `X`-morphism from a geometric fibre
`X_ȳ` to an étale `X`-scheme `E`, separated over `X`, extends to `X ×_Y V` for an étale
neighbourhood `V` of `ȳ`. -/
theorem extendsAlongGeometricFibres_of_isProper (E : X.Etale) [IsSeparated E.hom] :
    Scheme.ExtendsAlongGeometricFibres f E := by
  refine Scheme.extendsAlongGeometricFibres_of_strictLocalization E fun Ω _ _ y τ hτ ↦ ?_
  -- notation: `A = 𝒪^{sh}_{Y,ȳ}`, `P = Spec A ×_Y X`, `P₀ = P ×_A κ`
  let A := y.strictLocalization
  have : IsNoetherianRing A := by
    let := y.residueFieldAlgebra
    let := y.stalkAlgebra
    have := Scheme.Hom.isScalarTower_stalkAlgebra y
    have := isLocalHom_algebraMap_of_isScalarTower (R := Y.presheaf.stalk y.imagePoint) (K := Ω)
    exact inferInstanceAs
      (IsNoetherianRing (StrictHenselization (Y.presheaf.stalk y.imagePoint) Ω))
  let p := pullback.fst y.fromSpecStrictLocalization f
  let r := Spec.map (CommRingCat.ofHom (residue A))
  let i := pullback.fst p r
  let πX := pullback.snd y.fromSpecStrictLocalization f
  -- the residue field `κ` of `A` embeds into `Ω`
  let ψ : ResidueField A →+* Ω := ResidueField.lift y.strictLocalizationToField.hom
  let : Algebra (ResidueField A) Ω := ψ.toAlgebra
  let a := Spec.map (CommRingCat.ofHom (algebraMap (ResidueField A) Ω))
  have har : a ≫ r = y.toSpecStrictLocalization := by
    rw [← Spec.map_comp]
    congr 1
  -- the geometric fibre is `P₀ ×_κ Spec Ω`
  let ι : pullback f y ⟶ pullback p r :=
    pullback.lift (f.geometricFibreToStrictLocalization y) (pullback.snd f y ≫ a) (by
      rw [Category.assoc, har]
      exact f.geometricFibreToStrictLocalization_fst y)
  have hιi : ι ≫ i = f.geometricFibreToStrictLocalization y := pullback.lift_fst _ _ _
  have hι : IsPullback ι (pullback.snd f y) (pullback.snd p r) a := by
    refine (IsPullback.of_bot (v₂₁ := i) (v₂₂ := r) (h₃₁ := p) ?_ (pullback.lift_snd _ _ _).symm
      (IsPullback.of_hasPullback p r).flip).flip
    rw [hιi, har]
    exact (isPullback_geometricFibreToStrictLocalization f y).flip
  -- descend `τ` to the closed fibre `P₀`
  obtain ⟨v, hv, hιv⟩ := exists_hom_of_isPullback_specMap_of_isSepClosed hι (i ≫ πX) E τ (by
    rw [hτ, ← Category.assoc, hιi]
    exact (f.geometricFibreToStrictLocalization_snd y).symm)
  -- extend it from `P₀` to `P` (henselian lifting for `E ×_X P ⟶ P`)
  let EP := (Scheme.Etale.pullback πX).obj E
  have : IsSeparated EP.hom := inferInstanceAs (IsSeparated (pullback.snd E.hom πX))
  obtain ⟨s, hs, his⟩ := exists_section_of_henselianLocalRing p EP
    (pullback.lift v i hv) (pullback.lift_snd _ _ _)
  refine ⟨s ≫ pullback.fst E.hom πX, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (s ≫ EP.hom) ≫ πX = πX
    rw [hs, Category.id_comp]
  · rw [← hιi, Category.assoc, ← Category.assoc i, his, pullback.lift_fst, hιv]

end Extension

section BaseChange

variable {X' Y' : Scheme.{u}} {f} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}
  [IsProper f] [IsLocallyNoetherian Y]

/-- Base change for the sheaf represented by a separated étale `X`-scheme `E`,
along a proper `f : X ⟶ Y` with `Y` locally noetherian: for every cartesian square, the base
change morphism `g^* f_* h_E ⟶ f'_* h^* h_E` is an isomorphism (`Y'` arbitrary). -/
theorem isIso_etaleBaseChangeMap_etaleYoneda_of_isProper (hsq : IsPullback h f' f g)
    (E : X.Etale) [IsSeparated E.hom] :
    IsIso ((etaleBaseChangeMap hsq.w).app ((etaleYoneda X).obj E)) :=
  Scheme.isIso_etaleBaseChangeMap_etaleYoneda_of_extendsAlongGeometricFibres hsq E
    (extendsAlongGeometricFibres_of_isProper f E)

variable (f) in
/-- XIII 1.4 for represented sheaves: for `f : X ⟶ Y` proper with `Y` locally noetherian and `E`
an étale `X`-scheme which is separated over `X`, the sheaf of sets `h_E` represented by `E` is
cohomologically proper for `f` in dimension `≤ 0`. (SGA 1 states 1.4 for every sheaf of sets
and every `Y`; this is the case of the sheaves `h_E` with `E` separated, which include the
constant sheaves and the locally constant sheaves with finite values, over a locally noetherian
base.) -/
theorem isCohomologicallyProperLEZero_etaleYoneda (E : X.Etale) [IsSeparated E.hom] :
    IsCohomologicallyProperLEZero (𝟙 Y) f ((etaleYoneda X).obj E) :=
  fun _ _ _ _ _ _ _ _ _ hX ↦ isIso_etaleBaseChangeMap_etaleYoneda_of_isProper hX E

variable (f) in
/-- XIII 1.4 for constant sheaves with finite values: for `f : X ⟶ Y` proper with `Y` locally
noetherian and `C` a finite set, the constant sheaf `C_X` is cohomologically proper for `f` in
dimension `≤ 0`. (It is represented by the finite étale `X`-scheme `∐_C X`.) -/
theorem isCohomologicallyProperLEZero_constantSheaf (C : Type u) [Finite C] :
    IsCohomologicallyProperLEZero (𝟙 Y) f
      ((constantSheaf X.smallEtaleTopology (Type u)).obj C) :=
  have : IsSeparated (Scheme.Etale.constant X C).hom :=
    inferInstanceAs (IsSeparated (Scheme.constantSchemeHom X C))
  (isCohomologicallyProperLEZero_etaleYoneda f (Scheme.Etale.constant X C)).of_iso
    (Scheme.constantSheafIsoYoneda X C).symm

variable (f) in
/-- XIII 1.4 for locally constant sheaves with finite values: for `f : X ⟶ Y` proper with `Y`
locally noetherian, every locally constant sheaf of finite sets on `X` is cohomologically proper
for `f` in dimension `≤ 0`. (It is represented by a finite étale `X`-scheme, SGA 4 IX 2.2,
`exists_etaleYoneda_iso`.) -/
theorem isCohomologicallyProperLEZero_of_isLocallyConstantFiniteSheaf
    {F : Sheaf X.smallEtaleTopology (Type u)} (hF : Scheme.IsLocallyConstantFiniteSheaf F) :
    IsCohomologicallyProperLEZero (𝟙 Y) f F := by
  obtain ⟨V, _, ⟨e⟩⟩ := exists_etaleYoneda_iso hF
  exact (isCohomologicallyProperLEZero_etaleYoneda f V).of_iso e

end BaseChange

end SGA.SGA1.ExposeXIII
