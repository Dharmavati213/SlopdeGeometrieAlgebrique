/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import SGA.Foundations.StrictlyHenselianLift

/-!
# Functoriality of the strict localization

Let `x̄ : Spec Ω ⟶ X` be a geometric point and `𝒪^{sh}_{X,x̄}` the strict localization
(`AlgebraicGeometry.Scheme.Hom.strictLocalization`). We prove its universal property among
henselian local schemes with a geometric point at the closed point
(`AlgebraicGeometry.Scheme.Hom.existsUnique_lift_strictLocalization`): a morphism
`g : Spec A ⟶ X`, with `A` henselian local and `α : A → Ω` local such that `Spec α ≫ g = x̄`,
lifts uniquely to `Spec A ⟶ Spec 𝒪^{sh}_{X,x̄}` compatibly with the geometric points, provided the
residue field of `A` contains, inside `Ω`, the separable closure of `κ(x)`. Consequently a
morphism `f : X ⟶ S` induces a unique morphism of strict localizations
`Spec 𝒪^{sh}_{X,x̄} ⟶ Spec 𝒪^{sh}_{S,f(x̄)}` over `f` compatible with the geometric points
(`AlgebraicGeometry.Scheme.Hom.strictLocalizationMap`), and it is an isomorphism when `f` is
étale (`AlgebraicGeometry.Scheme.Hom.isIso_strictLocalizationMap`).

The ring-level statement is
`IsLocalRing.StrictHenselization.existsUnique_algHom_comp_pointHom`: an algebra map from a
henselian local `R`-algebra `A` to `K` whose image contains the values of the point of
`StrictHenselization R K` receives a unique map from `StrictHenselization R K` over it.

## References

* [EGA IV, 18.6, 18.8][ega4]
* [SGA 4, Exposé VIII, 4][sga4]
* [Stacks Project, Section 04GN (henselization and strict henselization)][stacks]
-/

universe u

open CategoryTheory IsLocalRing

noncomputable section

-- The carrier of `Spec R` is only defeq to `PrimeSpectrum R` beyond instance transparency (as in
-- `SGA.Foundations.StrictLocalizationLift`).
set_option backward.isDefEq.respectTransparency false

namespace IsLocalRing.StrictHenselization

variable {R : Type u} [CommRing R] {K : Type u} [Field K] [Algebra R K]
  {A : Type*} [CommRing A] [HenselianLocalRing A] [Algebra R A]

/-- Let `A` be a henselian local `R`-algebra and `α : A → K` a local `R`-algebra map whose image
contains the values of the point of `StrictHenselization R K`. Then there is a unique `R`-algebra
map `φ : StrictHenselization R K → A` with `α ∘ φ` the point (EGA IV 18.8; Stacks 04GG). -/
theorem existsUnique_algHom_comp_pointHom (α : A →ₐ[R] K) [IsLocalHom (α : A →+* K)]
    (hα : ∀ z : StrictHenselization R K, pointHom z ∈ Set.range α) :
    ∃! φ : StrictHenselization R K →ₐ[R] A, α.comp φ = pointHom := by
  let ᾱ : ResidueField A →+* K := ResidueField.lift (α : A →+* K)
  have hᾱ (a : A) : ᾱ (residue A a) = α a := ResidueField.lift_residue_apply _ a
  have hrange (z : StrictHenselization R K) : pointHom z ∈ ᾱ.range := by
    obtain ⟨a, ha⟩ := hα z
    exact ⟨residue A a, by rw [hᾱ, ha]⟩
  let e : ResidueField A ≃+* ᾱ.range :=
    RingEquiv.ofBijective ᾱ.rangeRestrict
      ⟨fun a b hab ↦ ᾱ.injective (congrArg Subtype.val hab), ᾱ.rangeRestrict_surjective⟩
  have he (b : ᾱ.range) : ᾱ (e.symm b) = b := by
    change ((e (e.symm b) : ᾱ.range) : K) = b
    rw [RingEquiv.apply_symm_apply]
  let τ : StrictHenselization R K →ₐ[R] ResidueField A :=
    { (e.symm : ᾱ.range →+* ResidueField A).comp
        ((pointHom : StrictHenselization R K →ₐ[R] K).toRingHom.codRestrict ᾱ.range hrange) with
      commutes' := fun r ↦ by
        apply ᾱ.injective
        change ᾱ (e.symm _) = _
        rw [he, IsScalarTower.algebraMap_apply R A (ResidueField A), ResidueField.algebraMap_eq,
          hᾱ, AlgHom.commutes]
        exact (pointHom : StrictHenselization R K →ₐ[R] K).commutes r }
  have hτ (z : StrictHenselization R K) : ᾱ (τ z) = pointHom z := he _
  have key (φ : StrictHenselization R K →ₐ[R] A) :
      α.comp φ = pointHom ↔ (IsScalarTower.toAlgHom R A (ResidueField A)).comp φ = τ := by
    constructor
    · intro h
      refine AlgHom.ext fun z ↦ ?_
      apply ᾱ.injective
      change ᾱ (residue A (φ z)) = ᾱ (τ z)
      rw [hᾱ, hτ, ← h]
      rfl
    · intro h
      refine AlgHom.ext fun z ↦ ?_
      rw [AlgHom.comp_apply, ← hᾱ, ← hτ, ← h]
      rfl
  obtain ⟨φ, hφ, hφu⟩ := existsUnique_lift (A := A) τ
  exact ⟨φ, (key φ).2 hφ, fun ψ hψ ↦ hφu ψ ((key ψ).1 hψ)⟩

variable [IsLocalRing R] [Algebra (ResidueField R) K] [IsScalarTower R (ResidueField R) K]
  {R' : Type u} [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
  [Algebra R' K] [Algebra (ResidueField R') K] [IsScalarTower R' (ResidueField R') K]
  [IsScalarTower R R' K]

omit [IsLocalHom (algebraMap R R')] in
private lemma isScalarTower_residueField [IsLocalHom (algebraMap R R')] :
    IsScalarTower (ResidueField R) (ResidueField R') K := by
  refine .of_algebraMap_eq fun x ↦ ?_
  obtain ⟨r, rfl⟩ := residue_surjective x
  rw [ResidueField.algebraMap_residue, ← ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply, ← ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R R' K]

/-- For a local homomorphism `R → R'` compatible with the maps to `K`, the values of the point of
`StrictHenselization R K` (the elements of `K` separable over `κ(R)`) are values of the point of
`StrictHenselization R' K` (they are separable over `κ(R')`). -/
theorem range_pointHom_subset :
    Set.range (pointHom : StrictHenselization R K →ₐ[R] K) ⊆
      Set.range (pointHom : StrictHenselization R' K →ₐ[R'] K) := by
  have := isScalarTower_residueField (R := R) (R' := R') (K := K)
  rw [range_pointHom, range_pointHom]
  exact fun y hy ↦ IsSeparable.tower_top (ResidueField R') hy

/-- If moreover `κ(R')` is separable over `κ(R)`, the two points have the same values. -/
theorem range_pointHom_eq [Algebra.IsSeparable (ResidueField R) (ResidueField R')] :
    Set.range (pointHom : StrictHenselization R K →ₐ[R] K) =
      Set.range (pointHom : StrictHenselization R' K →ₐ[R'] K) := by
  refine (range_pointHom_subset (R := R) (R' := R')).antisymm ?_
  have := isScalarTower_residueField (R := R) (R' := R') (K := K)
  rw [range_pointHom, range_pointHom]
  exact fun y hy ↦ IsSeparable.of_algebra_isSeparable_of_isSeparable (F := ResidueField R)
    (E := ResidueField R') hy

end IsLocalRing.StrictHenselization

namespace AlgebraicGeometry

namespace Scheme

/-- Two ring maps from a stalk `𝒪_{X,x}` to a ring `A` are equal if the induced morphisms
`Spec A ⟶ X` through `Spec 𝒪_{X,x}` are equal (`X.fromSpecStalk x` is a monomorphism). -/
lemma SpecMap_comp_fromSpecStalk_injective {X : Scheme.{u}} {x : X} {A : CommRingCat.{u}}
    {a b : X.presheaf.stalk x ⟶ A}
    (h : Spec.map a ≫ X.fromSpecStalk x = Spec.map b ≫ X.fromSpecStalk x) : a = b :=
  Spec.map_injective ((cancel_mono _).1 h)

/-- A morphism `g : Spec A ⟶ X` from a local scheme whose closed point maps to `x` is `Spec` of a
local homomorphism `𝒪_{X,x} → A` followed by `Spec 𝒪_{X,x} ⟶ X`. -/
lemma exists_SpecMap_fromSpecStalk_eq {X : Scheme.{u}} {A : CommRingCat.{u}} [IsLocalRing A]
    (g : Spec A ⟶ X) {x : X} (hg : g (closedPoint A) = x) :
    ∃ β : X.presheaf.stalk x ⟶ A, IsLocalHom β.hom ∧ Spec.map β ≫ X.fromSpecStalk x = g := by
  subst hg
  exact ⟨Scheme.stalkClosedPointTo g, inferInstance,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk g⟩

/-- A local ring map `c : 𝒪_{S,s} → 𝒪_{X,x}` over a formally unramified morphism of finite type
`f : X ⟶ S` (i.e. `Spec c` is `f` on the local schemes) is formally unramified and essentially of
finite type: it is the stalk map of `f` at `x`. -/
lemma Hom.formallyUnramified_of_SpecMap_fromSpecStalk {X S : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] {x : X} {s : S}
    (c : S.presheaf.stalk s ⟶ X.presheaf.stalk x) [IsLocalHom c.hom]
    (hc : Spec.map c ≫ S.fromSpecStalk s = X.fromSpecStalk x ≫ f) :
    c.hom.FormallyUnramified ∧ c.hom.EssFiniteType := by
  have hs : f x = s := by
    have := congrArg (fun g ↦ g (closedPoint (X.presheaf.stalk x))) hc
    dsimp only at this
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Spec_closedPoint, fromSpecStalk_closedPoint,
      fromSpecStalk_closedPoint] at this
    exact this.symm
  subst hs
  obtain rfl : c = f.stalkMap x :=
    SpecMap_comp_fromSpecStalk_injective (hc.trans (SpecMap_stalkMap_fromSpecStalk f).symm)
  exact ⟨FormallyUnramified.stalkMap f x, LocallyOfFiniteType.stalkMap f x⟩

/-- Two morphisms from a local scheme `Spec A` to a scheme which is formally unramified and of
finite type over `S` are equal if they agree over `S` and on a point `Spec K ⟶ Spec A` at the
closed point (EGA IV 17.4: the diagonal of `f` is an open immersion). -/
lemma Hom.eq_of_comp_eq_of_formallyUnramified {X S : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] {A : CommRingCat.{u}} [IsLocalRing A]
    {K : Type u} [Field K] (α : A ⟶ .of K) [IsLocalHom α.hom] {g₁ g₂ : Spec A ⟶ X}
    (h : g₁ ≫ f = g₂ ≫ f) (hα : Spec.map α ≫ g₁ = Spec.map α ≫ g₂) : g₁ = g₂ := by
  have hc : g₂ (closedPoint A) = g₁ (closedPoint A) := by
    have := congrArg (fun g ↦ g (closedPoint K)) hα
    dsimp only at this
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Spec_closedPoint] at this
    exact this.symm
  set x := g₁ (closedPoint A)
  obtain ⟨β₁, hβ₁, hg₁⟩ := exists_SpecMap_fromSpecStalk_eq g₁ (x := x) rfl
  obtain ⟨β₂, hβ₂, hg₂⟩ := exists_SpecMap_fromSpecStalk_eq g₂ hc
  rw [← hg₁, ← hg₂] at h hα ⊢
  rw [Category.assoc, Category.assoc, ← SpecMap_stalkMap_fromSpecStalk f, ← Category.assoc,
    ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp] at h
  have h := SpecMap_comp_fromSpecStalk_injective h
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp] at hα
  have hα := SpecMap_comp_fromSpecStalk_injective hα
  obtain ⟨hu, he⟩ := f.formallyUnramified_of_SpecMap_fromSpecStalk (f.stalkMap x)
    (SpecMap_stalkMap_fromSpecStalk f)
  algebraize [(f.stalkMap x).hom]
  let _ : Algebra (S.presheaf.stalk (f x)) A := (f.stalkMap x ≫ β₁).hom.toAlgebra
  let γ₁ : X.presheaf.stalk x →ₐ[S.presheaf.stalk (f x)] A := ⟨β₁.hom, fun _ ↦ rfl⟩
  let γ₂ : X.presheaf.stalk x →ₐ[S.presheaf.stalk (f x)] A :=
    ⟨β₂.hom, fun r ↦ congrArg (fun φ ↦ φ.hom r) h.symm⟩
  have : γ₁ = γ₂ := Algebra.FormallyUnramified.algHom_ext_of_residue fun a ↦ by
    apply (ResidueField.lift α.hom).injective
    rw [ResidueField.lift_residue_apply, ResidueField.lift_residue_apply]
    exact congrArg (fun φ ↦ φ.hom a) hα
  congr 2
  ext a
  exact DFunLike.congr_fun this a

end Scheme

namespace Scheme.Hom

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X)

attribute [local instance] residueFieldAlgebra stalkAlgebra isScalarTower_stalkAlgebra

/-- The geometric point `x̄` factors through `Spec 𝒪_{X,x}` by the map `𝒪_{X,x} → κ(x) → Ω`. -/
lemma SpecMap_algebraMap_fromSpecStalk :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk ξ.imagePoint) Ω)) ≫
      X.fromSpecStalk ξ.imagePoint = ξ := by
  conv_rhs => rw [← ξ.fromSpecResidueField_eq]
  rw [Scheme.fromSpecResidueField, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- **Universal property of the strict localization** (EGA IV 18.8, Stacks 04GG). Let `A` be a
henselian local ring, `α : A → Ω` a local homomorphism (a geometric point at the closed point)
and `g : Spec A ⟶ X` with `Spec α ≫ g = x̄`. If the values of the point
`𝒪^{sh}_{X,x̄} → Ω` lie in the image of `α` (that is, the residue field of `A` contains the
separable closure of `κ(x)` in `Ω`), then `g` lifts uniquely to a morphism
`Spec A ⟶ Spec 𝒪^{sh}_{X,x̄}` compatible with the geometric points. -/
theorem existsUnique_lift_strictLocalization {A : CommRingCat.{u}} [HenselianLocalRing A]
    (α : A ⟶ .of Ω) [IsLocalHom α.hom] (g : Spec A ⟶ X) (hg : Spec.map α ≫ g = ξ)
    (hα : ∀ z, ξ.strictLocalizationToField z ∈ Set.range α) :
    ∃! ψ : Spec A ⟶ Spec ξ.strictLocalization,
      ψ ≫ ξ.fromSpecStrictLocalization = g ∧
        Spec.map α ≫ ψ = ξ.toSpecStrictLocalization := by
  have hgx : g (closedPoint A) = ξ.imagePoint := by
    rw [← ξ.apply_eq_imagePoint (closedPoint Ω), ← hg, Scheme.Hom.comp_apply, Spec_closedPoint]
  obtain ⟨β, hβl, hβ⟩ := Scheme.exists_SpecMap_fromSpecStalk_eq g hgx
  let _ : Algebra (X.presheaf.stalk ξ.imagePoint) A := β.hom.toAlgebra
  -- `α` is a map of `𝒪_{X,x}`-algebras
  have hαβ : β ≫ α = CommRingCat.ofHom (algebraMap (X.presheaf.stalk ξ.imagePoint) Ω) := by
    apply Scheme.SpecMap_comp_fromSpecStalk_injective
    rw [SpecMap_algebraMap_fromSpecStalk, Spec.map_comp, Category.assoc, hβ, hg]
  let αA : A →ₐ[X.presheaf.stalk ξ.imagePoint] Ω :=
    { α.hom with commutes' := fun r ↦ congrArg (fun φ ↦ φ.hom r) hαβ }
  have : IsLocalHom (αA : A →+* Ω) := inferInstanceAs (IsLocalHom α.hom)
  obtain ⟨φ, hφ, hφu⟩ := StrictHenselization.existsUnique_algHom_comp_pointHom αA hα
  -- translating between ring maps and scheme maps
  have hfrom (ψ : ξ.strictLocalization ⟶ A) :
      Spec.map ψ ≫ ξ.fromSpecStrictLocalization = g ↔ ξ.toStrictLocalization ≫ ψ = β := by
    rw [fromSpecStrictLocalization, ← Category.assoc, ← Spec.map_comp, ← hβ]
    exact ⟨Scheme.SpecMap_comp_fromSpecStalk_injective, fun h ↦ by rw [h]⟩
  have hto (ψ : ξ.strictLocalization ⟶ A) :
      Spec.map α ≫ Spec.map ψ = ξ.toSpecStrictLocalization ↔
        ψ ≫ α = ξ.strictLocalizationToField := by
    rw [toSpecStrictLocalization, ← Spec.map_comp]
    exact ⟨fun h ↦ Spec.map_injective h, fun h ↦ by rw [h]⟩
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), ⟨(hfrom _).2 ?_, (hto _).2 ?_⟩, ?_⟩
  · ext r
    exact φ.commutes r
  · ext z
    exact DFunLike.congr_fun hφ z
  · rintro ψ ⟨h₁, h₂⟩
    obtain ⟨ψ, rfl⟩ := Spec.map_surjective ψ
    rw [hfrom] at h₁
    rw [hto] at h₂
    let ψA : ξ.strictLocalization →ₐ[X.presheaf.stalk ξ.imagePoint] A :=
      { ψ.hom with commutes' := fun r ↦ congrArg (fun φ ↦ φ.hom r) h₁ }
    have := hφu ψA (AlgHom.ext fun z ↦ congrArg (fun φ ↦ φ.hom z) h₂)
    congr 1
    ext z
    exact DFunLike.congr_fun this z

section Functorial

variable {S : Scheme.{u}} (f : X ⟶ S)

lemma imagePoint_comp : (ξ ≫ f).imagePoint = f ξ.imagePoint := by
  rw [← (ξ ≫ f).apply_eq_imagePoint (closedPoint Ω), Scheme.Hom.comp_apply,
    ξ.apply_eq_imagePoint]

/-- The stalk map of `f` at the image of `x̄`, as a local homomorphism
`𝒪_{S,s} → 𝒪_{X,x}` with `s` the image of `f ∘ x̄`, compatible with the maps to `Ω`. -/
lemma exists_stalkMap_imagePoint :
    ∃ c : S.presheaf.stalk (ξ ≫ f).imagePoint ⟶ X.presheaf.stalk ξ.imagePoint,
      IsLocalHom c.hom ∧ Spec.map c ≫ S.fromSpecStalk _ = X.fromSpecStalk ξ.imagePoint ≫ f ∧
      c ≫ CommRingCat.ofHom (algebraMap (X.presheaf.stalk ξ.imagePoint) Ω) =
        CommRingCat.ofHom (algebraMap (S.presheaf.stalk (ξ ≫ f).imagePoint) Ω) := by
  obtain ⟨c, hcl, hc⟩ := Scheme.exists_SpecMap_fromSpecStalk_eq
    (X.fromSpecStalk ξ.imagePoint ≫ f) (x := (ξ ≫ f).imagePoint)
    (by rw [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint, imagePoint_comp])
  refine ⟨c, hcl, hc, Scheme.SpecMap_comp_fromSpecStalk_injective ?_⟩
  rw [SpecMap_algebraMap_fromSpecStalk (ξ ≫ f), Spec.map_comp, Category.assoc, hc,
    ← Category.assoc, SpecMap_algebraMap_fromSpecStalk]

/-- The values of the point of `𝒪^{sh}_{S,f(x̄)}` are values of the point of `𝒪^{sh}_{X,x̄}`:
the separable closure of `κ(s)` in `Ω` is contained in that of `κ(x)`. -/
lemma strictLocalizationToField_mem_range (z : (ξ ≫ f).strictLocalization) :
    (ξ ≫ f).strictLocalizationToField z ∈ Set.range ξ.strictLocalizationToField := by
  obtain ⟨c, hcl, -, hc⟩ := ξ.exists_stalkMap_imagePoint f
  let _ : Algebra (S.presheaf.stalk (ξ ≫ f).imagePoint) (X.presheaf.stalk ξ.imagePoint) :=
    c.hom.toAlgebra
  have : IsLocalHom (algebraMap (S.presheaf.stalk (ξ ≫ f).imagePoint)
      (X.presheaf.stalk ξ.imagePoint)) := hcl
  have : IsScalarTower (S.presheaf.stalk (ξ ≫ f).imagePoint) (X.presheaf.stalk ξ.imagePoint) Ω :=
    .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hc).symm
  exact StrictHenselization.range_pointHom_subset ⟨z, rfl⟩

/-- The morphism of strict localizations `Spec 𝒪^{sh}_{X,x̄} ⟶ Spec 𝒪^{sh}_{S,f(x̄)}` induced by
`f : X ⟶ S` (EGA IV 18.8): the unique morphism over `f` compatible with the
geometric points (`eq_strictLocalizationMap`). -/
def strictLocalizationMap (f : X ⟶ S) (ξ : Spec (.of Ω) ⟶ X) :
    Spec ξ.strictLocalization ⟶ Spec (ξ ≫ f).strictLocalization :=
  ((ξ ≫ f).existsUnique_lift_strictLocalization ξ.strictLocalizationToField
    (ξ.fromSpecStrictLocalization ≫ f)
    (toSpecStrictLocalization_fromSpecStrictLocalization_assoc ξ f)
    (ξ.strictLocalizationToField_mem_range f)).exists.choose

@[reassoc (attr := simp)]
lemma strictLocalizationMap_fromSpecStrictLocalization :
    f.strictLocalizationMap ξ ≫ (ξ ≫ f).fromSpecStrictLocalization =
      ξ.fromSpecStrictLocalization ≫ f :=
  ((ξ ≫ f).existsUnique_lift_strictLocalization ξ.strictLocalizationToField
    (ξ.fromSpecStrictLocalization ≫ f)
    (toSpecStrictLocalization_fromSpecStrictLocalization_assoc ξ f)
    (ξ.strictLocalizationToField_mem_range f)).exists.choose_spec.1

@[reassoc (attr := simp)]
lemma toSpecStrictLocalization_strictLocalizationMap :
    ξ.toSpecStrictLocalization ≫ f.strictLocalizationMap ξ =
      (ξ ≫ f).toSpecStrictLocalization :=
  ((ξ ≫ f).existsUnique_lift_strictLocalization ξ.strictLocalizationToField
    (ξ.fromSpecStrictLocalization ≫ f)
    (toSpecStrictLocalization_fromSpecStrictLocalization_assoc ξ f)
    (ξ.strictLocalizationToField_mem_range f)).exists.choose_spec.2

/-- Uniqueness of the morphism of strict localizations: a morphism
`Spec 𝒪^{sh}_{X,x̄} ⟶ Spec 𝒪^{sh}_{S,f(x̄)}` over `f` compatible with the geometric points is
`strictLocalizationMap f x̄`. -/
lemma eq_strictLocalizationMap {φ : Spec ξ.strictLocalization ⟶ Spec (ξ ≫ f).strictLocalization}
    (h₁ : φ ≫ (ξ ≫ f).fromSpecStrictLocalization = ξ.fromSpecStrictLocalization ≫ f)
    (h₂ : ξ.toSpecStrictLocalization ≫ φ = (ξ ≫ f).toSpecStrictLocalization) :
    φ = f.strictLocalizationMap ξ :=
  ((ξ ≫ f).existsUnique_lift_strictLocalization ξ.strictLocalizationToField
    (ξ.fromSpecStrictLocalization ≫ f)
    (toSpecStrictLocalization_fromSpecStrictLocalization_assoc ξ f)
    (ξ.strictLocalizationToField_mem_range f)).unique ⟨h₁, h₂⟩
    ⟨strictLocalizationMap_fromSpecStrictLocalization ξ f,
      toSpecStrictLocalization_strictLocalizationMap ξ f⟩

/-- The strict localization of `X` at `x̄` is the limit of the étale neighbourhoods, so the
identity of `Spec 𝒪^{sh}_{X,x̄}` is the only endomorphism over `X` fixing the geometric point. -/
lemma eq_id_of_strictLocalization {φ : Spec ξ.strictLocalization ⟶ Spec ξ.strictLocalization}
    (h₁ : φ ≫ ξ.fromSpecStrictLocalization = ξ.fromSpecStrictLocalization)
    (h₂ : ξ.toSpecStrictLocalization ≫ φ = ξ.toSpecStrictLocalization) : φ = 𝟙 _ :=
  (ξ.existsUnique_lift_strictLocalization ξ.strictLocalizationToField
    ξ.fromSpecStrictLocalization (toSpecStrictLocalization_fromSpecStrictLocalization ξ)
    (fun z ↦ ⟨z, rfl⟩)).unique ⟨h₁, h₂⟩ ⟨Category.id_comp _, Category.comp_id _⟩

/-- For `f` étale, the residue field extensions are separable, so the strict localization of `S`
at `f(x̄)` has the same residue field as that of `X` at `x̄`. -/
lemma strictLocalizationToField_mem_range_of_etale [Etale f] (z : ξ.strictLocalization) :
    ξ.strictLocalizationToField z ∈ Set.range (ξ ≫ f).strictLocalizationToField := by
  obtain ⟨c, hcl, hcf, hc⟩ := ξ.exists_stalkMap_imagePoint f
  obtain ⟨hu, he⟩ := f.formallyUnramified_of_SpecMap_fromSpecStalk c hcf
  algebraize [c.hom]
  have : IsScalarTower (S.presheaf.stalk (ξ ≫ f).imagePoint) (X.presheaf.stalk ξ.imagePoint) Ω :=
    .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hc).symm
  change StrictHenselization.pointHom z ∈ Set.range StrictHenselization.pointHom
  rw [StrictHenselization.range_pointHom_eq (R := S.presheaf.stalk (ξ ≫ f).imagePoint)
    (R' := X.presheaf.stalk ξ.imagePoint) (K := Ω)]
  exact ⟨z, rfl⟩

/-- For `f` étale, the morphism of strict localizations is an isomorphism (EGA IV 18.8):
`X` and `S` have the same étale neighbourhoods at `x̄` and `f(x̄)`. -/
instance isIso_strictLocalizationMap [Etale f] : IsIso (f.strictLocalizationMap ξ) := by
  obtain ⟨g, hgf, hg⟩ := (ξ ≫ f).exists_comp_toSpecStrictLocalization f ξ rfl
  obtain ⟨ψ, ⟨hψ₁, hψ₂⟩, -⟩ := ξ.existsUnique_lift_strictLocalization
    (ξ ≫ f).strictLocalizationToField g hg (ξ.strictLocalizationToField_mem_range_of_etale f)
  refine ⟨ψ, ?_, ?_⟩
  · refine ξ.eq_id_of_strictLocalization ?_ ?_
    swap
    · rw [toSpecStrictLocalization_strictLocalizationMap_assoc]
      exact hψ₂
    rw [Category.assoc, hψ₁]
    refine Scheme.Hom.eq_of_comp_eq_of_formallyUnramified f ξ.strictLocalizationToField ?_ ?_
    · rw [Category.assoc, hgf, strictLocalizationMap_fromSpecStrictLocalization]
    · change ξ.toSpecStrictLocalization ≫ _ = ξ.toSpecStrictLocalization ≫ _
      rw [toSpecStrictLocalization_strictLocalizationMap_assoc, hg,
        toSpecStrictLocalization_fromSpecStrictLocalization]
  · refine (ξ ≫ f).eq_id_of_strictLocalization ?_ ?_
    · rw [Category.assoc, strictLocalizationMap_fromSpecStrictLocalization, ← Category.assoc, hψ₁,
        hgf]
    · change Spec.map (ξ ≫ f).strictLocalizationToField ≫ _ = _
      rw [← Category.assoc, hψ₂, toSpecStrictLocalization_strictLocalizationMap]

/-- Equal geometric points have isomorphic strict localizations. -/
def strictLocalizationIsoOfEq {ξ₁ ξ₂ : Spec (.of Ω) ⟶ X} (h : ξ₁ = ξ₂) :
    Spec ξ₁.strictLocalization ≅ Spec ξ₂.strictLocalization :=
  eqToIso (by rw [h])

@[reassoc (attr := simp)]
lemma strictLocalizationIsoOfEq_hom_fromSpecStrictLocalization {ξ₁ ξ₂ : Spec (.of Ω) ⟶ X}
    (h : ξ₁ = ξ₂) :
    (strictLocalizationIsoOfEq h).hom ≫ ξ₂.fromSpecStrictLocalization =
      ξ₁.fromSpecStrictLocalization := by
  subst h
  simp [strictLocalizationIsoOfEq]

@[reassoc (attr := simp)]
lemma toSpecStrictLocalization_strictLocalizationIsoOfEq_hom {ξ₁ ξ₂ : Spec (.of Ω) ⟶ X}
    (h : ξ₁ = ξ₂) :
    ξ₁.toSpecStrictLocalization ≫ (strictLocalizationIsoOfEq h).hom =
      ξ₂.toSpecStrictLocalization := by
  subst h
  simp [strictLocalizationIsoOfEq]

/-- Functoriality of the morphism of strict localizations, up to the identification
`Spec 𝒪^{sh}_{S,(x̄ ≫ e) ≫ f} ≅ Spec 𝒪^{sh}_{S,x̄ ≫ e ≫ f}`. -/
lemma strictLocalizationMap_comp {X' : Scheme.{u}} (e : X' ⟶ X) (ξ : Spec (.of Ω) ⟶ X') :
    (e ≫ f).strictLocalizationMap ξ = e.strictLocalizationMap ξ ≫
      f.strictLocalizationMap (ξ ≫ e) ≫ (strictLocalizationIsoOfEq (Category.assoc ξ e f)).hom := by
  symm
  apply eq_strictLocalizationMap
  · simp
  · simp

end Functorial

end Scheme.Hom

end AlgebraicGeometry
