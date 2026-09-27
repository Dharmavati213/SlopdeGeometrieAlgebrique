/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Adjoin.Tower
import SGA.SGA1.ExposeV.FiniteQuotient

/-!
# SGA 1, Exposé V, §1: properties of quotients by a finite group (V.1.4–V.1.8)

We work in the situation of V.1.3: a finite group `G` acting on the right on `X` (`T`), and an
invariant affine morphism `p : X ⟶ Y` with `Γ(Y, U) = Γ(X, p⁻¹ U)^G` for affine opens `U`.

* V.1.4: `p⁻¹ U ⟶ U` is again a quotient (`isQuotient_restrict`).
* V.1.5: `X` is affine (resp. separated) over `Z` iff `Y` is; if `X` is of finite type over `Z`
  it is finite over `Y`, and `Y` is of finite type over `Z` when `Z` is locally noetherian.
  The descent of separatedness along surjective universally closed morphisms is proved for any
  such morphism.
* V.1.6: `X` is affine (resp. separated) iff `Y` is. The affine half holds for any quotient.
* V.1.7: admissible actions (`IsAdmissible`); for a subgroup see `RelativeQuotient.lean`.
* V.1.8: the necessity half; the sufficiency half (gluing the quotients of `G`-stable affine
  opens) and the proof of `IsAdmissibleIffStatement` are in `QuotientGluing.lean`.
* Cor. V.1.8 for affine `X`; the case of `X` affine over an arbitrary base is
  `RelativeQuotient.lean`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace SGA.SGA1.ExposeV

section Invariants

variable (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A]

instance : Algebra.IsInvariant (FixedPoints.subring A G) A G :=
  ⟨fun a ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩

instance : SMulCommClass G (FixedPoints.subring A G) A :=
  ⟨fun g b a ↦ by
    change g • (b.1 * a) = b.1 * g • a
    rw [smul_mul', b.2 g]⟩

end Invariants

variable {G : Type*} {X Y Z : Scheme.{u}} {T : G → (X ⟶ X)} {p : X ⟶ Y}

/-- `SectionsAreInvariant` is transported along an equivariant isomorphism `X' ≅ X`. -/
lemma SectionsAreInvariant.iso_comp {X' : Scheme.{u}} {hTp : ∀ g, T g ≫ p = p} {W : Y.Opens}
    (hW : SectionsAreInvariant T p hTp W) {T' : G → (X' ⟶ X')} (e : X' ≅ X)
    (he : ∀ g, T' g ≫ e.hom = e.hom ≫ T g) (hT'p : ∀ g, T' g ≫ e.hom ≫ p = e.hom ≫ p) :
    SectionsAreInvariant T' (e.hom ≫ p) hT'p W := by
  have hbij : Function.Bijective (e.hom.app (p ⁻¹ᵁ W)) :=
    ConcreteCategory.bijective_of_isIso (e.hom.app (p ⁻¹ᵁ W))
  have key : ∀ g s₀, (T' g).appLE _ _ (preimage_le_preimage_of_comp_eq (hT'p g) W)
      (e.hom.app (p ⁻¹ᵁ W) s₀) = e.hom.app (p ⁻¹ᵁ W)
        ((T g).appLE _ _ (preimage_le_preimage_of_comp_eq (hTp g) W) s₀) := by
    intro g s₀
    have h1 := Scheme.Hom.appLE_comp_appLE (T' g) e.hom (p ⁻¹ᵁ W) ((e.hom ≫ p) ⁻¹ᵁ W)
      ((e.hom ≫ p) ⁻¹ᵁ W) le_rfl (preimage_le_preimage_of_comp_eq (hT'p g) W)
    have h2 := Scheme.Hom.appLE_comp_appLE e.hom (T g) (p ⁻¹ᵁ W) (p ⁻¹ᵁ W) ((e.hom ≫ p) ⁻¹ᵁ W)
      (preimage_le_preimage_of_comp_eq (hTp g) W) le_rfl
    have hle : (e.hom ≫ p) ⁻¹ᵁ W ≤ (e.hom ≫ T g) ⁻¹ᵁ p ⁻¹ᵁ W := by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
      exact Scheme.Hom.preimage_mono _ (preimage_le_preimage_of_comp_eq (hTp g) W)
    have h3 := appLE_congr_hom (he g) (p ⁻¹ᵁ W) ((e.hom ≫ p) ⁻¹ᵁ W) ((he g) ▸ hle) hle
    rw [Scheme.Hom.app_eq_appLE]
    exact congr($(h1.trans (h3.trans h2.symm)) s₀)
  refine ⟨hbij.1.comp hW.1, fun s hs ↦ ?_⟩
  obtain ⟨s₀, rfl⟩ := hbij.2 s
  obtain ⟨t, rfl⟩ := hW.2 s₀ fun g ↦ hbij.1 ((key g s₀).symm.trans (hs g))
  exact ⟨t, rfl⟩


section Affine

variable [Group G]

/-- The equivariant isomorphism `X ≅ Spec Γ(X, ⊤)` for an affine `X` with a right action. -/
lemma isoSpec_hom_comp_specAction (hT : IsRightAction T) [IsAffine X] (g : G) :
    letI := sectionsAction hT ⊤ fun _ ↦ le_top
    T g ≫ X.isoSpec.hom = X.isoSpec.hom ≫ specAction Γ(X, ⊤) G g := by
  let _ := sectionsAction hT ⊤ fun _ ↦ le_top
  have hA : (T g).appTop = CommRingCat.ofHom (MulSemiringAction.toRingHom G Γ(X, ⊤) g) := by
    ext a
    change (T g).app ⊤ a = (T g).appLE ⊤ ((T g) ⁻¹ᵁ ⊤) le_rfl a
    rw [Scheme.Hom.appLE_eq_app]
  rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality, hA]

variable [Finite G]

/-- V.1.6: if `X` is affine, any quotient of `X` by a finite group is affine: it is
`Spec Γ(X, ⊤)^G`. -/
theorem isAffine_of_isQuotient (hT : IsRightAction T) (hp : IsQuotient T p) [IsAffine X] :
    IsAffine Y := by
  let A : CommRingCat.{u} := Γ(X, ⊤)
  let _ : MulSemiringAction G A := sectionsAction hT ⊤ fun _ ↦ le_top
  let B : CommRingCat.{u} := CommRingCat.of (FixedPoints.subring A G)
  have hq : IsQuotient (specAction A G) (specMap A B) :=
    isQuotient_specMap (G := G) (B := B) Subtype.val_injective
  have e := hp.uniqueIso (hq.iso_comp X.isoSpec (isoSpec_hom_comp_specAction hT))
  exact .of_isIso e.hom

end Affine

section Restrict

variable (hTp : ∀ g, T g ≫ p = p)

/-- The restriction of `T g` to the invariant open `p⁻¹ U`. -/
noncomputable abbrev restrictAction (U : Y.Opens) (g : G) :
    (p ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme :=
  (T g).resLE (p ⁻¹ᵁ U) (p ⁻¹ᵁ U) (preimage_le_preimage_of_comp_eq (hTp g) U)

lemma restrictAction_comp (U : Y.Opens) (g : G) : restrictAction hTp U g ≫ p ∣_ U = p ∣_ U := by
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc,
    hTp g]

lemma isRightAction_restrictAction [Group G] (hT : IsRightAction T) (U : Y.Opens) :
    IsRightAction (restrictAction hTp U) where
  map_one := by
    rw [← cancel_mono (p ⁻¹ᵁ U).ι, Scheme.Hom.resLE_comp_ι, hT.map_one]
    simp
  map_mul g h := by
    rw [← cancel_mono (p ⁻¹ᵁ U).ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, hT.map_mul]

lemma SectionsAreInvariant.of_eq {V : Y.Opens} (hV : SectionsAreInvariant T p hTp V)
    {E : X.Opens} (hE : E = p ⁻¹ᵁ V) :
    Function.Injective (p.appLE V E hE.le) ∧ ∀ s : Γ(X, E),
      (∀ g, (T g).appLE E E (hE ▸ preimage_le_preimage_of_comp_eq (hTp g) V) s = s) →
        ∃ t, p.appLE V E hE.le t = s := by
  subst hE
  rw [Scheme.Hom.appLE_eq_app]
  exact hV

lemma sectionsAreInvariant_restrict {U : Y.Opens} {V : U.toScheme.Opens}
    (hV : SectionsAreInvariant T p hTp (U.ι ''ᵁ V)) :
    SectionsAreInvariant (restrictAction hTp U) (p ∣_ U) (restrictAction_comp hTp U) V := by
  have key := hV.of_eq hTp (image_morphismRestrict_preimage p U V)
  refine ⟨?_, fun s hs ↦ ?_⟩
  · rw [morphismRestrict_app']
    exact key.1
  · rw [morphismRestrict_app']
    refine key.2 s fun g ↦ ?_
    have := hs g
    rwa [Scheme.Hom.resLE_appLE] at this

variable [Group G] [Finite G]

/-- V.1.4: for every open `U` of `Y`, `U` is the quotient of `p⁻¹ U` by `G`. -/
theorem isQuotient_restrict (hT : IsRightAction T) [IsAffineHom p]
    (hsec : ∀ V, IsAffineOpen V → SectionsAreInvariant T p hTp V) (U : Y.Opens) :
    IsQuotient (restrictAction hTp U) (p ∣_ U) :=
  have : IsAffineHom (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹IsAffineHom p›
  isQuotient_of_sectionsAreInvariant (isRightAction_restrictAction hTp hT U)
    fun V hV ↦ sectionsAreInvariant_restrict hTp (hsec _ (hV.image_of_isOpenImmersion U.ι))

end Restrict

section Separated

set_option backward.isDefEq.respectTransparency.types false in
/-- V.1.5, "a lemma to be singled out": if `p : X ⟶ Y` is surjective and universally closed and
`X` is separated over `Z`, then so is `Y`. The image of the diagonal of `X` under the closed map
`p ×_Z p` is the diagonal of `Y`. -/
theorem isSeparated_of_surjective_of_universallyClosed (p : X ⟶ Y) (q : Y ⟶ Z) [Surjective p]
    [UniversallyClosed p] [IsSeparated (p ≫ q)] : IsSeparated q := by
  refine ⟨IsClosedImmersion.of_isPreimmersion _ ?_⟩
  let m := pullback.map (p ≫ q) (p ≫ q) q q p p (𝟙 Z) (by simp) (by simp)
  have : UniversallyClosed m :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed) ‹_› ‹_› rfl rfl
  have hc : ∀ x, pullback.diagonal q (p x) = m (pullback.diagonal (p ≫ q) x) := fun x ↦ by
    rw [← Scheme.Hom.comp_apply, pullback.comp_diagonal, Scheme.Hom.comp_apply]
  have hrange : Set.range (pullback.diagonal q) = m '' Set.range (pullback.diagonal (p ≫ q)) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := p.surjective y
      exact ⟨_, ⟨x, rfl⟩, (hc x).symm⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨p x, hc x⟩
  rw [hrange]
  exact m.isClosedMap _ (pullback.diagonal (p ≫ q)).isClosedEmbedding.isClosed_range

end Separated

section FiniteType

/-- V.1.5, ring version (Noether's theorem via Artin–Tate): if `A` is of finite type over a
noetherian ring `R` and integral over a subring `B` containing the image of `R`, then `B` is of
finite type over `R`. -/
theorem finiteType_of_finiteType_of_isIntegral {R B A : Type*} [CommRing R] [CommRing B]
    [CommRing A] [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.IsIntegral B A]
    (hinj : Function.Injective (algebraMap B A)) : Algebra.FiniteType R B := by
  have : Algebra.FiniteType B A := .of_restrictScalars_finiteType R B A
  have : Module.Finite B A := Algebra.IsIntegral.finite
  exact ⟨fg_of_fg_of_fg R B A Algebra.FiniteType.out Module.Finite.fg_top hinj⟩

theorem RingHom.finiteType_of_comp_of_isIntegral {R B A : Type*} [CommRing R] [CommRing B]
    [CommRing A] [IsNoetherianRing R] (f : R →+* B) (g : B →+* A) (hgf : (g.comp f).FiniteType)
    (hg : g.IsIntegral) (hinj : Function.Injective g) : f.FiniteType := by
  algebraize [f, g, g.comp f]
  have : Algebra.IsIntegral B A := ⟨hg⟩
  exact finiteType_of_finiteType_of_isIntegral (R := R) (B := B) (A := A) hinj

/-- If `p` is surjective and `p ≫ q` is quasi-compact, then `q` is quasi-compact. -/
theorem quasiCompact_of_surjective_comp (p : X ⟶ Y) (q : Y ⟶ Z) [Surjective p]
    [QuasiCompact (p ≫ q)] : QuasiCompact q where
  isCompact_preimage U hU hc := by
    rw [← Set.image_preimage_eq (q ⁻¹' U) p.surjective, ← Set.preimage_comp]
    exact (QuasiCompact.isCompact_preimage (f := p ≫ q) U hU hc).image p.continuous

end FiniteType

section Properties

variable [Group G] [Finite G] (hT : IsRightAction T) (hTp : ∀ g, T g ≫ p = p) [IsAffineHom p]
  (hsec : ∀ U, IsAffineOpen U → SectionsAreInvariant T p hTp U)

include hT hsec

lemma surjective_of_sectionsAreInvariant : Surjective p :=
  ⟨(surjective_and_orbit_of_sectionsAreInvariant hT hsec).1⟩

/-- V.1.5: `X` is affine over `Z` iff `Y` is. -/
theorem isAffineHom_comp_iff (q : Y ⟶ Z) : IsAffineHom (p ≫ q) ↔ IsAffineHom q := by
  refine ⟨fun _ ↦ ⟨fun V hV ↦ ?_⟩, fun _ ↦ inferInstance⟩
  have : IsAffine (p ⁻¹ᵁ q ⁻¹ᵁ V).toScheme := hV.preimage (p ≫ q)
  exact isAffine_of_isQuotient (isRightAction_restrictAction hTp hT _)
    (isQuotient_restrict hTp hT hsec _)

/-- V.1.5: `X` is separated over `Z` iff `Y` is. -/
theorem isSeparated_comp_iff (q : Y ⟶ Z) : IsSeparated (p ≫ q) ↔ IsSeparated q := by
  have := isIntegralHom_of_sectionsAreInvariant hT hsec
  have := surjective_of_sectionsAreInvariant hT hTp hsec
  exact ⟨fun _ ↦ isSeparated_of_surjective_of_universallyClosed p q, fun _ ↦ inferInstance⟩

/-- V.1.5: if `X` is of finite type over `Z`, it is finite over `Y`. -/
theorem isFinite_of_locallyOfFiniteType_comp (q : Y ⟶ Z) [LocallyOfFiniteType (p ≫ q)] :
    IsFinite p := by
  have := isIntegralHom_of_sectionsAreInvariant hT hsec
  have := locallyOfFiniteType_of_comp p q
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType p).mpr ⟨inferInstance, inferInstance⟩

/-- V.1.6: `X` is affine iff `Y` is. -/
theorem isAffine_iff : IsAffine X ↔ IsAffine Y :=
  ⟨fun _ ↦ isAffine_of_isQuotient hT (isQuotient_of_sectionsAreInvariant hT hsec),
    fun _ ↦ isAffine_of_isAffineHom p⟩

/-- V.1.6: `X` is a scheme (i.e. separated) iff `Y` is. -/
theorem isSeparated_iff : X.IsSeparated ↔ Y.IsSeparated := by
  rw [Scheme.isSeparated_iff, Scheme.isSeparated_iff, ← terminal.comp_from p]
  exact isSeparated_comp_iff hT hTp hsec _

/-- V.1.5: if `Z` is locally noetherian and `X` is locally of finite type over `Z`, so is `Y`. -/
theorem locallyOfFiniteType_of_comp [IsLocallyNoetherian Z] (q : Y ⟶ Z)
    [LocallyOfFiniteType (p ≫ q)] : LocallyOfFiniteType q := by
  have hp := isIntegralHom_of_sectionsAreInvariant hT hsec
  refine ⟨fun {U} hU {V} hV e ↦ ?_⟩
  have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hc : (p ≫ q).appLE U (p ⁻¹ᵁ V) (Scheme.Hom.preimage_mono p e) =
      q.appLE U V e ≫ p.app V := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  refine RingHom.finiteType_of_comp_of_isIntegral _ (p.app V).hom ?_
    (hp.isIntegral_app V hV) (hsec V hV).1
  rw [← CommRingCat.hom_comp, ← hc]
  exact (p ≫ q).finiteType_appLE hU (hV.preimage p) _

/-- V.1.5: if `Z` is locally noetherian and `X` is of finite type over `Z`, so is `Y`. -/
theorem locallyOfFiniteType_and_quasiCompact_of_comp [IsLocallyNoetherian Z] (q : Y ⟶ Z)
    [LocallyOfFiniteType (p ≫ q)] [QuasiCompact (p ≫ q)] :
    LocallyOfFiniteType q ∧ QuasiCompact q := by
  have := surjective_of_sectionsAreInvariant hT hTp hsec
  exact ⟨locallyOfFiniteType_of_comp hT hTp hsec q, quasiCompact_of_surjective_comp p q⟩

end Properties

section Admissible

/-- V.1.7: `G` acts admissibly on `X` if there is an invariant affine morphism `p : X ⟶ Y`
with `𝒪_Y = p_*(𝒪_X)^G`, as in V.1.3. Then `Y` is the quotient `X/G`
(`IsAdmissible.exists_isQuotient`). -/
def IsAdmissible (T : G → (X ⟶ X)) : Prop :=
  ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (hTp : ∀ g, T g ≫ p = p),
    IsAffineHom p ∧ ∀ U, SectionsAreInvariant T p hTp U

variable [Group G] [Finite G]

/-- V.1.7: if `G` acts admissibly, the quotient `X/G` exists. -/
theorem IsAdmissible.exists_isQuotient (hT : IsRightAction T) (h : IsAdmissible T) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y), IsQuotient T p := by
  obtain ⟨Y, p, hTp, _, hsec⟩ := h
  exact ⟨Y, p, isQuotient_of_sectionsAreInvariant hT fun U _ ↦ hsec U⟩

/-- Cor. V.1.8, for affine `X` (i.e. `X` affine over an affine `Z`): a finite group acts
admissibly on an affine scheme, with quotient `Spec Γ(X, ⊤)^G`. -/
theorem isAdmissible_of_isAffine (hT : IsRightAction T) [IsAffine X] : IsAdmissible T := by
  let A : CommRingCat.{u} := Γ(X, ⊤)
  let _ : MulSemiringAction G A := sectionsAction hT ⊤ fun _ ↦ le_top
  let B : CommRingCat.{u} := CommRingCat.of (FixedPoints.subring A G)
  have he := isoSpec_hom_comp_specAction hT (X := X)
  have hTp : ∀ g, T g ≫ X.isoSpec.hom ≫ specMap A B = X.isoSpec.hom ≫ specMap A B := fun g ↦ by
    rw [reassoc_of% (he g), specAction_comp_specMap]
  exact ⟨Spec B, X.isoSpec.hom ≫ specMap A B, hTp, inferInstance, fun W ↦
    (sectionsAreInvariant_specMap (G := G) (B := B) Subtype.val_injective W).iso_comp
      X.isoSpec he hTp⟩

omit [Group G] [Finite G] in
/-- V.1.8, necessity: if `G` acts admissibly, `X` is a union of `G`-stable affine opens. -/
theorem IsAdmissible.exists_isAffineOpen (h : IsAdmissible T) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ (∀ g, T g ⁻¹ᵁ U = U) ∧ x ∈ U := by
  obtain ⟨Y, p, hTp, _, -⟩ := h
  obtain ⟨V, hV, hxV⟩ := exists_isAffineOpen_mem (p x)
  refine ⟨p ⁻¹ᵁ V, hV.preimage p, fun g ↦ ?_, hxV⟩
  rw [← Scheme.Hom.comp_preimage, hTp]

omit [Group G] [Finite G] in
/-- V.1.8, necessity (second form): every orbit lies in an affine open. -/
theorem IsAdmissible.exists_isAffineOpen_orbit (h : IsAdmissible T) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g, T g x ∈ U := by
  obtain ⟨U, hU, hTU, hxU⟩ := h.exists_isAffineOpen x
  exact ⟨U, hU, fun g ↦ show x ∈ T g ⁻¹ᵁ U from (hTU g).symm ▸ hxU⟩

/-- V.1.8: a finite group acting on the right on `X` acts admissibly iff `X` is a union of
`G`-stable affine opens, iff every orbit lies in an affine open. The necessity is
`IsAdmissible.exists_isAffineOpen`; the whole statement is proved as `isAdmissibleIffStatement`
in `QuotientGluing.lean`. -/
def IsAdmissibleIffStatement : Prop :=
  ∀ (X : Scheme.{u}) (G : Type u) [Group G] [Finite G] (T : G → (X ⟶ X)), IsRightAction T →
    (IsAdmissible T ↔ ∀ x, ∃ U : X.Opens, IsAffineOpen U ∧ (∀ g, T g ⁻¹ᵁ U = U) ∧ x ∈ U) ∧
    (IsAdmissible T ↔ ∀ x, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g, T g x ∈ U)

omit [Finite G] in
lemma IsRightAction.subgroup (hT : IsRightAction T) (H : Subgroup G) :
    IsRightAction fun h : H ↦ T h where
  map_one := hT.map_one
  map_mul g h := hT.map_mul g h

end Admissible

end SGA.SGA1.ExposeV
