/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.Lifting
import SGA.SGA1.ExposeIII.Deformation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# SGA 1, Exposé III, §§3–4: infinitesimal extensions of schemes and morphisms

Scheme-theoretic forms of Theorem III.3.1, (i) ⇒ (ii), Corollaries III.3.2 and III.3.3, and
the existence part of Theorem III.4.1:

* `exists_extension_of_smooth`: if `X → Y` is smooth, `Y'₀ ⊆ Y'` is a closed subscheme with the
  same underlying space, and `g₀ : Y'₀ → X` is a `Y`-morphism, then `g₀` extends to a
  `Y`-morphism on a neighbourhood of any point. As in SGA the question is local; on affine
  pieces it is `Smooth.exists_lift_of_surjective`;
* `exists_extension_of_isAffine`: the global extension of III.5.5 when `X`, `Y`, `Y'` are
  affine; the general case (`GlobalExtensionStatement`) is proved in `GlobalExtension.lean` with
  the sheaf `ℋom(g₀^* Ω_{X/Y}, 𝒥)` of III.5.2 and Čech cohomology;
* `ext_of_formallyUnramified`, `existsUnique_extension_of_etale`: uniqueness of the extension
  for unramified morphisms, hence III.3.2 (i) ⇒ (ii);
* `exists_smooth_lift_local`: the local existence of smooth lifts, III.4.1 (local uniqueness is
  `exists_iso_of_smooth` in `Thickening.lean`);
* `exists_section_of_mem_smoothLocus`: a scheme over a complete local ring `A`, smooth at a
  rational point `x` of the closed fibre, has a section through `x` (III.3.3).

The equivalences (i) ⇔ (iii) of III.3.1 and III.3.2 (lifting over spectra of local artinian
rings) are in `LiftingCriterion.lean`. Corollary III.7.4 (lifting smooth proper curves) is recorded
as a statement.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TensorProduct

namespace SGA.SGA1.ExposeIII


/-- If `i : Y'₀ → Y'` is a surjective closed immersion, the kernel of `Γ(Y', U) → Γ(Y'₀, i⁻¹ U)`
is a nil ideal for every quasi-compact open `U`. -/
lemma ker_appLE_le_nilradical {Y' Y'₀ : Scheme.{u}} (i : Y'₀ ⟶ Y') (hi : Function.Surjective i)
    {U : Y'.Opens} (hU : IsCompact (U : Set Y')) :
    RingHom.ker (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom ≤ nilradical Γ(Y', U) := by
  intro c hc
  refine (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU c).mpr ?_
  have hpre : i ⁻¹ᵁ Y'.basicOpen c = ⊥ := by
    rw [Scheme.preimage_basicOpen, Scheme.Hom.app_eq_appLE]
    rw [RingHom.mem_ker] at hc
    rw [hc, Scheme.basicOpen_zero]
  refine eq_bot_iff.mpr fun y hy ↦ ?_
  obtain ⟨w, rfl⟩ := hi y
  have : w ∈ i ⁻¹ᵁ Y'.basicOpen c := hy
  rw [hpre] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
/-- III.3.1, (i) ⇒ (ii), on affine opens: given affine opens `W ⊆ Y`, `V ⊆ f⁻¹ W` and
`U ⊆ p⁻¹ W` with `i⁻¹ U ⊆ g₀⁻¹ V`, the restriction of `g₀` to `i⁻¹ U` extends to `U`. -/
theorem exists_extension_of_affineOpens {X Y Y' Y'₀ : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (p : Y' ⟶ Y) (i : Y'₀ ⟶ Y') [IsClosedImmersion i] (hi : Function.Surjective i)
    (g₀ : Y'₀ ⟶ X) (hg₀ : g₀ ≫ f = i ≫ p) {W : Y.Opens} {V : X.Opens} {U : Y'.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen V) (hU : IsAffineOpen U) (hVW : V ≤ f ⁻¹ᵁ W)
    (hUW : U ≤ p ⁻¹ᵁ W) (hU'V : i ⁻¹ᵁ U ≤ g₀ ⁻¹ᵁ V) :
    ∃ g : U.toScheme ⟶ X, g ≫ f = U.ι ≫ p ∧ (i ∣_ U) ≫ g = (i ⁻¹ᵁ U).ι ≫ g₀ := by
  have hU' : IsAffineOpen (i ⁻¹ᵁ U) := hU.preimage i
  -- the ring maps
  set α := f.appLE W V hVW
  set β := p.appLE W U hUW
  set ρ := i.appLE U (i ⁻¹ᵁ U) le_rfl
  set γ := g₀.appLE V (i ⁻¹ᵁ U) hU'V
  have hcomm : α ≫ γ = β ≫ ρ := by
    simp only [α, β, γ, ρ, Scheme.Hom.appLE_comp_appLE]
    congr 1
  have hsm : α.hom.Smooth := HasRingHomProperty.appLE @Smooth f inferInstance ⟨W, hW⟩ ⟨V, hV⟩ hVW
  have hρ : Function.Surjective ρ := by
    have := i.app_surjective U hU
    rwa [Scheme.Hom.app_eq_appLE] at this
  have hker := ker_appLE_le_nilradical i hi hU.isCompact
  -- lift `γ` through `ρ`
  algebraize [α.hom, β.hom, (β ≫ ρ).hom]
  let ρ' : Γ(Y', U) →ₐ[Γ(Y, W)] Γ(Y'₀, i ⁻¹ᵁ U) := { ρ.hom with commutes' := fun _ ↦ rfl }
  let γ' : Γ(X, V) →ₐ[Γ(Y, W)] Γ(Y'₀, i ⁻¹ᵁ U) :=
    { γ.hom with commutes' := fun r ↦ congr($hcomm r) }
  obtain ⟨ψ, hψ⟩ := Smooth.exists_lift_of_surjective ρ' hρ hker γ'
  have hψα : α ≫ CommRingCat.ofHom ψ.toRingHom = β := by ext r; exact ψ.commutes r
  have hψρ : CommRingCat.ofHom ψ.toRingHom ≫ ρ = γ := by ext b; exact congr($hψ b)
  refine ⟨hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hW hV hVW,
      ← Spec.map_comp_assoc, hψα, IsAffineOpen.SpecMap_appLE_fromSpec p hW hU hUW,
      IsAffineOpen.isoSpec_hom_fromSpec_assoc]
  · have hL : (i ∣_ U) ≫ hU.isoSpec.hom = hU'.isoSpec.hom ≫ Spec.map ρ := by
      rw [← cancel_mono hU.fromSpec, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
        morphismRestrict_ι, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec i hU hU' le_rfl,
        IsAffineOpen.isoSpec_hom_fromSpec_assoc]
    rw [← Category.assoc, hL, Category.assoc, ← Spec.map_comp_assoc, hψρ,
      IsAffineOpen.SpecMap_appLE_fromSpec g₀ hV hU' hU'V, IsAffineOpen.isoSpec_hom_fromSpec_assoc]




set_option backward.isDefEq.respectTransparency false in
/-- III.3.1, (i) ⇒ (ii): let `f : X → Y` be smooth, `p : Y' → Y`, and `i : Y'₀ → Y'` a closed
immersion which is surjective (so `Y'₀` has the same underlying space as `Y'`). Every
`Y`-morphism `g₀ : Y'₀ → X` extends, on an open neighbourhood `U` of any point of `Y'`, to a
`Y`-morphism `U → X`. -/
theorem exists_extension_of_smooth {X Y Y' Y'₀ : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (p : Y' ⟶ Y) (i : Y'₀ ⟶ Y') [IsClosedImmersion i] (hi : Function.Surjective i)
    (g₀ : Y'₀ ⟶ X) (hg₀ : g₀ ≫ f = i ≫ p) (z : Y'₀) :
    ∃ (U : Y'.Opens) (_ : i z ∈ U) (g : U.toScheme ⟶ X),
      g ≫ f = U.ι ≫ p ∧ (i ∣_ U) ≫ g = (i ⁻¹ᵁ U).ι ≫ g₀ := by
  -- affine opens around `g₀ z` and its image
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f (g₀ z))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxW (f ⁻¹ᵁ W).2
  -- an affine open `U` of `Y'` around `i z` with `i⁻¹ U ⊆ g₀⁻¹ V` and `U ⊆ p⁻¹ W`
  have hcl : IsClosed (i '' (g₀ ⁻¹ᵁ V : Set Y'₀)ᶜ) :=
    i.isClosedEmbedding.isClosedMap _ (g₀ ⁻¹ᵁ V).2.isClosed_compl
  have hzO : i z ∈ (p ⁻¹ᵁ W : Set Y') ∩ (i '' (g₀ ⁻¹ᵁ V : Set Y'₀)ᶜ)ᶜ := by
    refine ⟨?_, ?_⟩
    · change p (i z) ∈ W
      rw [← Scheme.Hom.comp_apply, ← hg₀, Scheme.Hom.comp_apply]
      exact hxW
    · rintro ⟨w, hw, hwz⟩
      exact hw (i.isClosedEmbedding.injective hwz ▸ hxV)
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, hUO⟩ := Y'.isBasis_affineOpens.exists_subset_of_mem_open hzO
    ((p ⁻¹ᵁ W).2.inter hcl.isOpen_compl)
  have hUW : U ≤ p ⁻¹ᵁ W := fun y hy ↦ (hUO hy).1
  have hU'V : i ⁻¹ᵁ U ≤ g₀ ⁻¹ᵁ V := by
    intro w hw
    by_contra h
    exact (hUO hw).2 ⟨w, h, rfl⟩
  exact ⟨U, hzU, exists_extension_of_affineOpens f p i hi g₀ hg₀ hW hV hU hVW hUW hU'V⟩

/-- III.5.5, special case where `X`, `Y` and `Y'` are affine: a `Y`-morphism `g₀ : Y'₀ → X`
into a smooth `Y`-scheme extends to a global `Y`-morphism `Y' → X`, for `Y'₀ ⊆ Y'` with the same
underlying space. -/
theorem exists_extension_of_isAffine {X Y Y' Y'₀ : Scheme.{u}} [IsAffine X] [IsAffine Y]
    [IsAffine Y'] (f : X ⟶ Y) [Smooth f] (p : Y' ⟶ Y) (i : Y'₀ ⟶ Y') [IsClosedImmersion i]
    (hi : Function.Surjective i) (g₀ : Y'₀ ⟶ X) (hg₀ : g₀ ≫ f = i ≫ p) :
    ∃ g : Y' ⟶ X, g ≫ f = p ∧ i ≫ g = g₀ := by
  obtain ⟨g, hg₁, hg₂⟩ := exists_extension_of_affineOpens f p i hi g₀ hg₀ (isAffineOpen_top Y)
    (isAffineOpen_top X) (isAffineOpen_top Y') le_rfl le_rfl le_rfl
  refine ⟨Y'.topIso.inv ≫ g, ?_, ?_⟩
  · rw [Category.assoc, hg₁, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  · have : IsIso (i ⁻¹ᵁ ⊤).ι := inferInstanceAs (IsIso Y'₀.topIso.hom)
    rw [← cancel_epi (i ⁻¹ᵁ ⊤).ι, ← hg₂, ← Category.assoc, ← morphismRestrict_ι,
      Category.assoc]
    congr 1
    rw [← Category.assoc, Scheme.ι_toIso_inv, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- III.3.2, (i) ⇒ (ii), uniqueness: two `Y`-morphisms `Y' → X` into an unramified `Y`-scheme
which agree on a closed subscheme `Y'₀ ⊆ Y'` with the same underlying space are equal. Applied
to an open `U ⊆ Y'`, with `exists_extension_of_smooth`, it gives III.3.2 (i) ⇒ (ii) for étale
morphisms. -/
theorem ext_of_formallyUnramified {X Y Y' Y'₀ : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f]
    [LocallyOfFiniteType f] (p : Y' ⟶ Y) (i : Y'₀ ⟶ Y') [IsClosedImmersion i]
    (hi : Function.Surjective i) {g g' : Y' ⟶ X} (hg : g ≫ f = p) (hg' : g' ≫ f = p)
    (h : i ≫ g = i ≫ g') : g = g' := by
  refine Scheme.hom_ext_of_forall g g' fun y ↦ ?_
  have hpt : g y = g' y := by
    obtain ⟨w, rfl⟩ := hi y
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f (g y))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxW (f ⁻¹ᵁ W).2
  obtain ⟨_, ⟨N, hN, rfl⟩, hyN, hNO⟩ := Y'.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ (g ⁻¹ᵁ V ⊓ g' ⁻¹ᵁ V : Y'.Opens) from ⟨hxV, show g' y ∈ V from hpt ▸ hxV⟩)
    (g ⁻¹ᵁ V ⊓ g' ⁻¹ᵁ V).2
  have hNg : N ≤ g ⁻¹ᵁ V := fun z hz ↦ (hNO hz).1
  have hNg' : N ≤ g' ⁻¹ᵁ V := fun z hz ↦ (hNO hz).2
  have hNW : N ≤ p ⁻¹ᵁ W := by
    rw [← hg]; exact fun z hz ↦ hVW (hNg hz)
  refine ⟨N, hyN, ?_⟩
  -- it suffices to compare the ring maps `Γ(X, V) → Γ(Y', N)`
  suffices e : g.appLE V N hNg = g'.appLE V N hNg' by
    rw [← IsAffineOpen.isoSpec_hom_fromSpec hN, Category.assoc, Category.assoc,
      ← IsAffineOpen.SpecMap_appLE_fromSpec g hV hN hNg,
      ← IsAffineOpen.SpecMap_appLE_fromSpec g' hV hN hNg', e]
  set α := f.appLE W V hVW
  set β := p.appLE W N hNW
  set ρ := i.appLE N (i ⁻¹ᵁ N) le_rfl
  have hα : α ≫ g.appLE V N hNg = β := by
    simp only [α, β, Scheme.Hom.appLE_comp_appLE]; congr 1
  have hα' : α ≫ g'.appLE V N hNg' = β := by
    simp only [α, β, Scheme.Hom.appLE_comp_appLE]; congr 1
  have hρ : g.appLE V N hNg ≫ ρ = g'.appLE V N hNg' ≫ ρ := by
    simp only [ρ, Scheme.Hom.appLE_comp_appLE]; congr 1
  have hfu : α.hom.FormallyUnramified :=
    HasRingHomProperty.appLE @FormallyUnramified f inferInstance ⟨W, hW⟩ ⟨V, hV⟩ hVW
  have hft : α.hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨W, hW⟩ ⟨V, hV⟩ hVW
  algebraize [α.hom, β.hom]
  let G : Γ(X, V) →ₐ[Γ(Y, W)] Γ(Y', N) :=
    { (g.appLE V N hNg).hom with commutes' := fun r ↦ congr($hα r) }
  let G' : Γ(X, V) →ₐ[Γ(Y, W)] Γ(Y', N) :=
    { (g'.appLE V N hNg').hom with commutes' := fun r ↦ congr($hα' r) }
  have : G = G' := FormallyUnramified.ext_of_le_nilradical (RingHom.ker ρ.hom)
    (ker_appLE_le_nilradical i hi hN.isCompact) (AlgHom.ext fun x ↦ by
      change Ideal.Quotient.mk _ (G x) = Ideal.Quotient.mk _ (G' x)
      rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
      exact congr($hρ x))
  ext x
  exact congr($this x)

/-- III.3.2, (i) ⇒ (ii): for `f : X → Y` étale, the extension of `g₀` given by III.3.1 is unique
on every open `U` on which it exists. -/
theorem existsUnique_extension_of_etale {X Y Y' Y'₀ : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (p : Y' ⟶ Y) (i : Y'₀ ⟶ Y') [IsClosedImmersion i] (hi : Function.Surjective i)
    (g₀ : Y'₀ ⟶ X) (hg₀ : g₀ ≫ f = i ≫ p) (z : Y'₀) :
    ∃ (U : Y'.Opens) (_ : i z ∈ U), ∃! g : U.toScheme ⟶ X,
      g ≫ f = U.ι ≫ p ∧ (i ∣_ U) ≫ g = (i ⁻¹ᵁ U).ι ≫ g₀ := by
  obtain ⟨U, hzU, g, hg⟩ := exists_extension_of_smooth f p i hi g₀ hg₀ z
  refine ⟨U, hzU, g, hg, fun g' hg' ↦ ?_⟩
  have hi' : Function.Surjective (i ∣_ U) := by
    intro u
    obtain ⟨w, hw⟩ := hi u.1
    have hwU : w ∈ i ⁻¹ᵁ U := by
      change i w ∈ U
      rw [hw]; exact u.2
    obtain ⟨w', hw'⟩ : w ∈ Set.range (i ⁻¹ᵁ U).ι := by rwa [Scheme.Opens.range_ι]
    refine ⟨w', U.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hw', hw]
    rfl
  exact (ext_of_formallyUnramified f (U.ι ≫ p) (i ∣_ U) hi' hg.1 hg'.1
    (hg.2.trans hg'.2.symm)).symm

set_option backward.isDefEq.respectTransparency false in
/-- III.4.1, existence: let `Y` be locally noetherian, `j : Y₀ → Y` a closed immersion with the
same underlying space, and `X₀` smooth over `Y₀`. Every point `x` of `X₀` has an open
neighbourhood `U₀` which is the reduction of a smooth `Y`-scheme `X`: the square
`U₀ → X`, `U₀ → Y₀`, `X → Y`, `Y₀ → Y` is cartesian, i.e. `U₀ ≅ X ×_Y Y₀` over `Y₀`.

As in SGA the proof is local: on an affine `Y` it lifts a standard smooth presentation of
`X₀` near `x` (`exists_smooth_lift_localizationAway`). -/
theorem exists_smooth_lift_local {Y Y₀ X₀ : Scheme.{u}} [IsLocallyNoetherian Y] (j : Y₀ ⟶ Y)
    [IsClosedImmersion j] (hj : Function.Surjective j) (f₀ : X₀ ⟶ Y₀) [Smooth f₀] (x : X₀) :
    ∃ (U₀ : X₀.Opens) (_ : x ∈ U₀) (X : Scheme.{u}) (f : X ⟶ Y) (_ : Smooth f)
      (k : U₀.toScheme ⟶ X), IsPullback k (U₀.ι ≫ f₀) f j := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (j (f₀ x))) isOpen_univ
  have hW₀ : IsAffineOpen (j ⁻¹ᵁ W) := hW.preimage j
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV₀, hV₀W₀⟩ := X₀.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ f₀ ⁻¹ᵁ (j ⁻¹ᵁ W) from hxW) (f₀ ⁻¹ᵁ (j ⁻¹ᵁ W)).2
  set ρ := j.appLE W (j ⁻¹ᵁ W) le_rfl
  set φ := f₀.appLE (j ⁻¹ᵁ W) V₀ hV₀W₀
  have hsm : φ.hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f₀ inferInstance ⟨_, hW₀⟩ ⟨V₀, hV₀⟩ hV₀W₀
  have hρs : Function.Surjective ρ := by
    have := j.app_surjective W hW
    rwa [Scheme.Hom.app_eq_appLE] at this
  have : IsNoetherianRing Γ(Y, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hnil : IsNilpotent (RingHom.ker ρ.hom) :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).mpr
      (ker_appLE_le_nilradical j hj hW.isCompact)
  algebraize [ρ.hom, φ.hom, (ρ ≫ φ).hom]
  have : IsScalarTower Γ(Y, W) Γ(Y₀, j ⁻¹ᵁ W) Γ(X₀, V₀) := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨s, hs, hlift⟩ := exists_smooth_lift_localizationAway (R := Γ(Y, W))
    (R₀ := Γ(Y₀, j ⁻¹ᵁ W)) (S₀ := Γ(X₀, V₀)) hρs hnil
  obtain ⟨t, hxt⟩ : ∃ t : s, x ∈ X₀.basicOpen (t : Γ(X₀, V₀)) := by
    rw [← hV₀.iSup_basicOpen_eq_self_iff.mpr hs] at hxV₀
    exact TopologicalSpace.Opens.mem_iSup.mp hxV₀
  obtain ⟨S, _, _, hSsm, ⟨e⟩⟩ := hlift t t.2
  -- the open `U₀ = D(t)` and its ring of sections, a localization of `Γ(X₀, V₀)`
  set t' : Γ(X₀, V₀) := t.1
  have hU₀ : IsAffineOpen (X₀.basicOpen t') := hV₀.basicOpen t'
  have hU₀V₀ : X₀.basicOpen t' ≤ V₀ := X₀.basicOpen_le t'
  let : Algebra Γ(X₀, V₀) Γ(X₀, X₀.basicOpen t') :=
    (X₀.presheaf.map (homOfLE hU₀V₀).op).hom.toAlgebra
  have : IsLocalization.Away t' Γ(X₀, X₀.basicOpen t') := hV₀.isLocalization_basicOpen t'
  let ι : Localization.Away t' ≃ₐ[Γ(X₀, V₀)] Γ(X₀, X₀.basicOpen t') :=
    IsLocalization.algEquiv (Submonoid.powers t') _ _
  let E : Γ(Y₀, j ⁻¹ᵁ W) ⊗[Γ(Y, W)] S ≃+* Γ(X₀, X₀.basicOpen t') :=
    e.toRingEquiv.trans ι.toRingEquiv
  set ρ₀ := f₀.appLE (j ⁻¹ᵁ W) (X₀.basicOpen t') (hU₀V₀.trans hV₀W₀)
  have hE (r : Γ(Y₀, j ⁻¹ᵁ W)) : E (r ⊗ₜ 1) = ρ₀ r := by
    change ι (e (algebraMap _ _ r)) = _
    rw [e.commutes, IsScalarTower.algebraMap_apply Γ(Y₀, j ⁻¹ᵁ W) Γ(X₀, V₀)
      (Localization.Away t'), ι.commutes]
    exact congr($(Scheme.Hom.appLE_map f₀ hV₀W₀ (homOfLE hU₀V₀).op) r)
  -- the affine pushout square
  let a : Γ(Y, W) ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap Γ(Y, W) S)
  let σ : CommRingCat.of S ⟶ Γ(X₀, X₀.basicOpen t') :=
    CommRingCat.ofHom (E.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := Γ(Y, W)) (A := Γ(Y₀, j ⁻¹ᵁ W))
        (B := S)).toRingHom)
  have hpo : IsPushout ρ a ρ₀ σ :=
    (CommRingCat.isPushout_tensorProduct Γ(Y, W) Γ(Y₀, j ⁻¹ᵁ W) S).of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) E.toCommRingCatIso (by ext; rfl) (by ext; rfl)
      (by ext r; exact hE r) (by ext; rfl)
  have hA := (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip
  -- the square `Spec Γ(Y₀, j⁻¹ W) → Spec Γ(Y, W)` over `j`
  have hB : IsPullback (Spec.map ρ) hW₀.fromSpec hW.fromSpec j := by
    refine (isPullback_morphismRestrict j W).of_iso hW₀.isoSpec hW.isoSpec (Iso.refl _)
      (Iso.refl _) ?_ (by simp) (by simp) (by simp)
    rw [← cancel_mono hW.fromSpec, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
      morphismRestrict_ι, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec j hW hW₀ le_rfl,
      IsAffineOpen.isoSpec_hom_fromSpec_assoc]
  have hSsm' : Smooth (Spec.map a) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hSsm
  refine ⟨X₀.basicOpen t', hxt, Spec (.of S), Spec.map a ≫ hW.fromSpec, inferInstance,
    hU₀.isoSpec.hom ≫ Spec.map σ, ?_⟩
  refine (hA.paste_vert hB).of_iso hU₀.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) ?_ (by simp) (by simp)
  rw [Iso.symm_hom, Iso.refl_hom, Category.comp_id, IsAffineOpen.SpecMap_appLE_fromSpec f₀ hW₀ hU₀,
    ← IsAffineOpen.isoSpec_inv_ι_assoc]

/-- III.5.5: in Theorem III.3.1 (ii) one may take `Y'` affine and ask for a global extension.
That is, smooth morphisms have the infinitesimal lifting property for affine test schemes `Y'`
and closed subschemes `Y'₀ ⊆ Y'` defined by a nilpotent ideal (in SGA's locally noetherian
setting, "same underlying space"). SGA deduces this from III.5.2 and the vanishing of `H¹` of
quasi-coherent sheaves on affine schemes. Proved in `GlobalExtension.lean`
(`globalExtensionStatement`); the case where `X` and `Y` are also affine is
`exists_extension_of_isAffine` above. -/
def GlobalExtensionStatement : Prop :=
  ∀ ⦃X Y Y' Y'₀ : Scheme.{u}⦄ (f : X ⟶ Y) [Smooth f] (p : Y' ⟶ Y) [IsAffine Y']
    (i : Y'₀ ⟶ Y') [IsClosedImmersion i], IsNilpotent i.ker →
      ∀ g₀ : Y'₀ ⟶ X, g₀ ≫ f = i ≫ p → ∃ g : Y' ⟶ X, g ≫ f = p ∧ i ≫ g = g₀

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]

set_option backward.isDefEq.respectTransparency false in
/-- III.3.3: let `X` be locally of finite presentation over a complete local ring `A`, and `x₀`
a rational point of the closed fibre (a `Spec A`-morphism `Spec k → X`). If `X` is smooth over
`A` at `x₀`, there is a section `s` of `X` over `Spec A` through `x₀`. -/
theorem exists_section_of_mem_smoothLocus {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFinitePresentation f] (x₀ : Spec (.of (ResidueField A)) ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (residue A)))
    (hx : x₀ default ∈ f.smoothLocus) :
    ∃ s : Spec (.of A) ⟶ X, s ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue A)) ≫ s = x₀ := by
  obtain ⟨U, hU, V, hV, hVU, hxV, hsm⟩ :=
    exists_smooth_of_formallySmooth_stalk f (x₀ default) (Scheme.Hom.mem_smoothLocus.mp hx)
  -- `U` contains the closed point, hence is everything
  have : IsLocalHom (CommRingCat.ofHom (residue A)).hom := inferInstanceAs (IsLocalHom (residue A))
  have hfx : f (x₀ default) = closedPoint A := by
    rw [← Scheme.Hom.comp_apply, hx₀,
      show (default : Spec (.of (ResidueField A))) = closedPoint _ from Subsingleton.elim _ _,
      Spec_closedPoint]
  have hUtop : U = ⊤ := (IsLocalRing.closed_point_mem_iff (R := A)).mp (hfx ▸ hVU hxV)
  subst hUtop
  -- the point factors through `Spec Γ(X, V)`
  have hrange : Set.range x₀ ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    rwa [Subsingleton.elim p default]
  set y₀ := IsOpenImmersion.lift hV.fromSpec x₀ hrange
  have hy₀ : y₀ ≫ hV.fromSpec = x₀ := IsOpenImmersion.lift_fac _ _ _
  -- the ring maps
  set a : CommRingCat.of A ⟶ Γ(X, V) := (Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ V hVU with ha_def
  have key : Spec.map a = hV.fromSpec ≫ f := by
    rw [ha_def, Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU,
      show hU.fromSpec = (isAffineOpen_top _).fromSpec from rfl, IsAffineOpen.fromSpec_top,
      Scheme.isoSpec_Spec_inv]
  set φ₀ := Spec.preimage y₀
  have hφ₀ : a ≫ φ₀ = CommRingCat.ofHom (residue A) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, key, ← Category.assoc, hy₀, hx₀]
  -- `Γ(X, V)` is smooth over `A`
  have hsm' : a.hom.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.bijective)
    hsm
  algebraize [a.hom]
  let φ₀' : Γ(X, V) →ₐ[A] ResidueField A :=
    { φ₀.hom with commutes' := fun r ↦ congr($hφ₀ r) }
  obtain ⟨φ, hφ⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete φ₀'
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, ← key, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact φ.commutes r
  · rw [← Category.assoc, ← Spec.map_comp, ← hy₀]
    congr 1
    rw [← Spec.map_preimage y₀]
    congr 1
    ext b
    exact congr($hφ b)


/-- III.3.3, "in particular": if `X` is smooth over a complete local ring `A`, every rational
point of the closed fibre `X ⊗ k` lifts to a section of `X` over `Spec A`. -/
theorem exists_section_of_smooth {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Smooth f]
    (x₀ : Spec (.of (ResidueField A)) ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (residue A))) :
    ∃ s : Spec (.of A) ⟶ X, s ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue A)) ≫ s = x₀ :=
  exists_section_of_mem_smoothLocus f x₀ hx₀ (by rw [f.smoothLocus_eq_top]; trivial)

/-- III.7.4 (statement only): every smooth proper curve over the residue field `k` of a complete
noetherian local ring `A` is the closed fibre of a smooth proper curve over `A`. SGA obtains it
from III.6.10 (the obstructions lie in `H²` of coherent sheaves on a curve, which vanish) and
Grothendieck's existence theorem (III.7.2).

The formal lift is available for curves which are the union of two affine opens with affine
intersection (`exists_smooth_lift_seq_of_isUnionOfTwoAffines`, `TwoChartLift.lean`). Still
missing: that a smooth proper curve over `k` is projective and such a union; the lifting of an
ample line bundle to the `Xₙ` (III.7.1); the essential surjectivity of Grothendieck's existence
theorem for coherent sheaves on `ℙⁿ_A` (only the fully faithful half and the locally free case
are in `SGA.Foundations.Cohomology`), needed to algebraize the formal curve embedded in the
formal completion of `ℙⁿ_A` (III.7.2); and the smoothness and properness of the algebraization. -/
def SmoothProperCurveLiftStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (.of (ResidueField A)))
    [SmoothOfRelativeDimension 1 f₀] [IsProper f₀],
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), SmoothOfRelativeDimension 1 f ∧ IsProper f ∧
      ∃ e : pullback f (Spec.map (CommRingCat.ofHom (residue A))) ≅ X₀,
        e.hom ≫ f₀ = pullback.snd _ _

end SGA.SGA1.ExposeIII
