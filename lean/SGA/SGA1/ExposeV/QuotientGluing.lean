/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.QuasiAffine
import SGA.SGA1.ExposeV.RelativeQuotient

/-!
# SGA 1, Exposé V, V.1.8: existence of the quotient by gluing

A finite group `G` acts admissibly on `X` iff `X` is a union of `G`-stable affine open subsets,
iff every orbit lies in an affine open subset (V.1.8).

* Necessity is `IsAdmissible.exists_isAffineOpen` (in `FiniteQuotientProperties`).
* Sufficiency (`isAdmissible_of_forall_exists_isAffineOpen`): the quotients `W/G` of the
  `G`-stable affine opens `W` (Cor. V.1.8) are glued along the open immersions `W₁/G ⟶ W₂/G` for
  `W₁ ⊆ W₂`, which identify `W₁/G` with the image of `W₁` (V.1.4). This is a locally directed
  diagram of open immersions, and its colimit is the quotient. The condition
  `𝒪_Y = p_*(𝒪_X)^G` is checked on the charts (`SectionsAreInvariant.image`).
* From orbits to stable affine opens (`exists_isAffineOpen_stable_of_orbit`), by SGA's argument:
  a finite subset of an open subset of an affine scheme lies in a basic open contained in it
  (`exists_basicOpen_le_of_finite`, prime avoidance), and finite intersections of affine opens
  of an affine scheme are affine.
* For V.3.1: finite subsets of a quasi-affine scheme lie in affine opens, so a finite group
  acting by automorphisms of a quasi-affine `Y`-scheme acts admissibly
  (`isAdmissible_of_isQuasiAffineHom`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace SGA.SGA1.ExposeV

section Stable

variable {G : Type*} {X Y : Scheme.{u}} {T : G → (X ⟶ X)}

section Group

variable [Group G]

lemma IsRightAction.comp_inv (hT : IsRightAction T) (g : G) : T g ≫ T g⁻¹ = 𝟙 X := by
  rw [← hT.map_mul, mul_inv_cancel, hT.map_one]

lemma IsRightAction.apply_inv_apply (hT : IsRightAction T) (g : G) (x : X) :
    T g⁻¹ (T g x) = x := by
  rw [← Scheme.Hom.comp_apply, hT.comp_inv]
  rfl

lemma IsRightAction.isIso (hT : IsRightAction T) (g : G) : IsIso (T g) :=
  ⟨T g⁻¹, hT.comp_inv g, by rw [← hT.map_mul, inv_mul_cancel, hT.map_one]⟩

/-- An open subset `U` with `U ⊆ (T g)⁻¹ U` for every `g` is `G`-stable. -/
lemma IsRightAction.preimage_eq_of_le (hT : IsRightAction T) {U : X.Opens}
    (h : ∀ g, U ≤ T g ⁻¹ᵁ U) (g : G) : T g ⁻¹ᵁ U = U := by
  refine le_antisymm (fun x hx ↦ ?_) (h g)
  have := h g⁻¹ hx
  rwa [Scheme.Hom.mem_preimage, hT.apply_inv_apply] at this

end Group

lemma mem_iInf_preimage [Finite G] {O : X.Opens} {y : X} :
    y ∈ ⨅ g, T g ⁻¹ᵁ O ↔ ∀ g, T g y ∈ O := by
  rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  rfl

/-- The largest `G`-stable open subset `⋂ (T g)⁻¹ O` of an open subset `O` is `G`-stable. -/
lemma preimage_iInf_preimage [Group G] [Finite G] (hT : IsRightAction T) (O : X.Opens) (g : G) :
    T g ⁻¹ᵁ (⨅ h, T h ⁻¹ᵁ O) = ⨅ h, T h ⁻¹ᵁ O := by
  refine hT.preimage_eq_of_le (fun g y hy ↦ ?_) g
  rw [Scheme.Hom.mem_preimage, mem_iInf_preimage]
  intro h
  rw [← Scheme.Hom.comp_apply, ← hT.map_mul]
  exact mem_iInf_preimage.mp hy _

/-- The image `p(U)` of an open subset, defined as the complement of `p(X ∖ U)`; it is open when
`p` is closed. For `G`-stable `U` and `p` with orbits as fibres, `p⁻¹(p(U)) = U`
(`preimage_imageOpen`). -/
def imageOpen {p : X ⟶ Y} (hp : IsClosedMap p) (U : X.Opens) : Y.Opens :=
  ⟨(p '' (U : Set X)ᶜ)ᶜ, (hp _ U.isOpen.isClosed_compl).isOpen_compl⟩

lemma preimage_imageOpen {p : X ⟶ Y} (hp : IsClosedMap p)
    (horb : ∀ x x', p x = p x' → ∃ g, T g x = x') {U : X.Opens} (hU : ∀ g, T g ⁻¹ᵁ U = U) :
    p ⁻¹ᵁ imageOpen hp U = U := by
  ext x
  change p x ∈ (p '' (U : Set X)ᶜ)ᶜ ↔ x ∈ U
  constructor
  · intro h
    by_contra hx
    exact h ⟨x, hx, rfl⟩
  · rintro hx ⟨x', hx', hpx⟩
    obtain ⟨g, rfl⟩ := horb x x' hpx.symm
    apply hx'
    change x ∈ T g ⁻¹ᵁ U
    rwa [hU g]

lemma mem_imageOpen {p : X ⟶ Y} (hp : IsClosedMap p)
    (horb : ∀ x x', p x = p x' → ∃ g, T g x = x') {U : X.Opens} (hU : ∀ g, T g ⁻¹ᵁ U = U)
    {x : X} (hx : x ∈ U) : p x ∈ imageOpen hp U := by
  change x ∈ p ⁻¹ᵁ imageOpen hp U
  rwa [preimage_imageOpen hp horb hU]

end Stable

section Transfer

variable {G : Type*} {X Y X' Y' : Scheme.{u}} {T : G → (X ⟶ X)} {p : X ⟶ Y}
  {T' : G → (X' ⟶ X')} {p' : X' ⟶ Y'}

/-- The condition `𝒪_Y = p_*(𝒪_X)^G` of V.1.3 is local on `Y`: it can be read on the open
subschemes of `Y` and their inverse images. Precisely, given a cartesian square of open
immersions `j : X' ⟶ X`, `ι : Y' ⟶ Y` over `p`, `p'`, with `j` equivariant, the condition for
`p'` over `V'` implies that for `p` over `ι(V')`. -/
lemma SectionsAreInvariant.image {hT'p : ∀ g, T' g ≫ p' = p'} (j : X' ⟶ X) (ι : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion ι] (sq : j ≫ p = p' ≫ ι)
    (hpre : p ⁻¹ᵁ ι.opensRange = j.opensRange) (hTj : ∀ g, T' g ≫ j = j ≫ T g)
    {hTp : ∀ g, T g ≫ p = p} {V' : Y'.Opens} (h : SectionsAreInvariant T' p' hT'p V') :
    SectionsAreInvariant T p hTp (ι ''ᵁ V') := by
  let W' := p' ⁻¹ᵁ V'
  have hE : j ''ᵁ W' = p ⁻¹ᵁ (ι ''ᵁ V') := by
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      change p (j x') ∈ ι ''ᵁ V'
      rw [← Scheme.Hom.comp_apply, sq, Scheme.Hom.comp_apply]
      exact ⟨_, hx', rfl⟩
    · intro hx
      have hx' : x ∈ p ⁻¹ᵁ ι.opensRange := by
        obtain ⟨y', -, hy'⟩ := hx
        exact ⟨y', hy'⟩
      rw [hpre] at hx'
      obtain ⟨x', rfl⟩ := hx'
      refine ⟨x', ?_, rfl⟩
      obtain ⟨y', hy'V, hy'⟩ := hx
      change p' x' ∈ V'
      rw [← Scheme.Hom.comp_apply, sq, Scheme.Hom.comp_apply] at hy'
      rwa [← ι.isOpenEmbedding.injective hy']
  rw [sectionsAreInvariant_iff_of_eq hE]
  let α := ι.appLE (ι ''ᵁ V') V' (ι.preimage_image_eq V').ge
  let β := j.appLE (j ''ᵁ W') W' (j.preimage_image_eq W').ge
  have hα : Function.Bijective α := by
    have : α = (ι.appIso V').hom := (Scheme.Hom.appIso_hom' ι V').symm
    rw [this]
    exact ConcreteCategory.bijective_of_isIso _
  have hβ : Function.Bijective β := by
    have : β = (j.appIso W').hom := (Scheme.Hom.appIso_hom' j W').symm
    rw [this]
    exact ConcreteCategory.bijective_of_isIso _
  have h1 : ∀ t, β (p.appLE (ι ''ᵁ V') (j ''ᵁ W') hE.le t) = p'.app V' (α t) := by
    intro t
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact congr($(appLE_congr_hom sq _ _ _ _) t)
  have h2 : ∀ g s, β ((T g).appLE (j ''ᵁ W') (j ''ᵁ W')
      (hE ▸ preimage_le_preimage_of_comp_eq (hTp g) (ι ''ᵁ V')) s) =
      (T' g).appLE W' W' (preimage_le_preimage_of_comp_eq (hT'p g) V') (β s) := by
    intro g s
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    exact congr($(appLE_congr_hom (hTj g).symm _ _ _ _) s)
  refine ⟨fun t₁ t₂ ht ↦ hα.1 (h.1 ?_), fun s hs ↦ ?_⟩
  · rw [← h1, ← h1, ht]
  · obtain ⟨t', ht'⟩ := h.2 (β s) fun g ↦ by rw [← h2, hs g]
    obtain ⟨t, rfl⟩ := hα.2 t'
    exact ⟨t, hβ.1 (by rw [h1, ht'])⟩

end Transfer

section FiniteSubsets

/-- In an affine open `U`, a finite subset of an open `U' ⊆ U` lies in a basic open
`D(f) ⊆ U'` (prime avoidance). -/
lemma exists_basicOpen_le_of_finite {X : Scheme.{u}} {U U' : X.Opens} (hU : IsAffineOpen U)
    (hU' : U' ≤ U) {F : Set X} (hF : F.Finite) (hFU' : F ⊆ U') :
    ∃ f : Γ(X, U), F ⊆ X.basicOpen f ∧ X.basicOpen f ≤ U' := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | ⟨x₀, -⟩
  · exact ⟨0, Set.empty_subset _, by rw [Scheme.basicOpen_zero]; exact bot_le⟩
  let Z : Set (PrimeSpectrum Γ(X, U)) := hU.fromSpec ⁻¹' (U' : Set X)ᶜ
  have hZ : IsClosed Z := U'.isOpen.isClosed_compl.preimage hU.fromSpec.continuous
  let I := PrimeSpectrum.vanishingIdeal Z
  have hIZ : PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) = Z := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq]
  let P : X → Ideal Γ(X, U) := fun x ↦
    if h : x ∈ U then (hU.primeIdealOf ⟨x, h⟩).asIdeal else ⊤
  have hP : ∀ x (hx : x ∈ U), P x = (hU.primeIdealOf ⟨x, hx⟩).asIdeal := fun x hx ↦ by simp [P, hx]
  have hnot : ¬ ((I : Set Γ(X, U)) ⊆ ⋃ x ∈ F, (P x : Set Γ(X, U))) := by
    rw [Ideal.subset_union_prime_finite hF x₀ x₀ fun x hx _ _ ↦ by
      rw [hP x (hU' (hFU' hx))]; infer_instance]
    rintro ⟨x, hxF, hIx⟩
    have hxU := hU' (hFU' hxF)
    rw [hP x hxU] at hIx
    have : hU.primeIdealOf ⟨x, hxU⟩ ∈ Z := by
      rw [← hIZ]
      exact hIx
    apply this
    change hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) ∈ U'
    rw [hU.fromSpec_primeIdealOf]
    exact hFU' hxF
  obtain ⟨r, hrI, hr⟩ := Set.not_subset.mp hnot
  simp only [Set.mem_iUnion, not_exists] at hr
  refine ⟨r, fun x hxF ↦ ?_, fun y hy ↦ ?_⟩
  · have hxU := hU' (hFU' hxF)
    have h1 : hU.primeIdealOf ⟨x, hxU⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r := by
      rw [hU.fromSpec_preimage_basicOpen]
      change r ∉ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
      rw [← hP x hxU]
      exact hr x hxF
    change hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) ∈ X.basicOpen r at h1
    rwa [hU.fromSpec_primeIdealOf] at h1
  · have hyU : y ∈ (U : Set X) := X.basicOpen_le r hy
    rw [← hU.range_fromSpec] at hyU
    obtain ⟨q, rfl⟩ := hyU
    have hq : q ∈ PrimeSpectrum.basicOpen r := by
      rw [← hU.fromSpec_preimage_basicOpen]
      exact hy
    by_contra h
    have : q ∈ PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) := by
      rw [hIZ]
      exact h
    exact hq (this hrI)


variable {G : Type*} [Group G] [Finite G] {X : Scheme.{u}} {T : G → (X ⟶ X)}

/-- V.1.8: if the orbit of `x` lies in an affine open subset `U`, then `x` has a `G`-stable
affine open neighbourhood. As in SGA: the `G`-stable open `U' = ⋂ (T g)⁻¹ U ⊆ U` contains the
orbit, hence a basic open `V` of `U` containing the orbit; then `⋂ (T g)⁻¹ V` is `G`-stable, and
affine as a finite intersection of affine opens of the affine (hence separated) scheme `U`. -/
lemma exists_isAffineOpen_stable_of_orbit (hT : IsRightAction T) {x : X}
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : ∀ g, T g x ∈ U) :
    ∃ W : X.Opens, IsAffineOpen W ∧ (∀ g, T g ⁻¹ᵁ W = W) ∧ x ∈ W := by
  let U' := ⨅ h, T h ⁻¹ᵁ U
  have hU'U : U' ≤ U := fun y hy ↦ by
    have := mem_iInf_preimage.mp hy 1
    rwa [hT.map_one] at this
  have hF : Set.range (fun g ↦ T g x) ⊆ U' := by
    rintro _ ⟨g, rfl⟩
    refine mem_iInf_preimage.mpr fun h ↦ ?_
    rw [← Scheme.Hom.comp_apply, ← hT.map_mul]
    exact hxU _
  obtain ⟨f, hfF, hfU'⟩ := exists_basicOpen_le_of_finite hU hU'U (Set.finite_range _) hF
  let V := X.basicOpen f
  have hV : IsAffineOpen V := hU.basicOpen f
  refine ⟨⨅ h, T h ⁻¹ᵁ V, ?_, preimage_iInf_preimage hT V,
    mem_iInf_preimage.mpr fun h ↦ hfF ⟨h, rfl⟩⟩
  have hle : ∀ h, T h ⁻¹ᵁ V ≤ U := fun h y hy ↦ by
    have := mem_iInf_preimage.mp (hfU' hy) h⁻¹
    rwa [hT.apply_inv_apply] at this
  have himage : ∀ h, U.ι ''ᵁ (U.ι ⁻¹ᵁ (T h ⁻¹ᵁ V)) = T h ⁻¹ᵁ V := fun h ↦ by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (hle h)]
  have hV' : ∀ h, IsAffineOpen (U.ι ⁻¹ᵁ (T h ⁻¹ᵁ V)) := fun h ↦ by
    have := hT.isIso h
    rw [← U.ι.isAffineOpen_iff_of_isOpenImmersion, himage]
    exact hV.preimage (T h)
  have : IsAffine U.toScheme := hU
  have hinf := IsAffineOpen.iInf hV'
  rw [← U.ι.isAffineOpen_iff_of_isOpenImmersion] at hinf
  convert hinf using 1
  apply SetLike.coe_injective
  rw [TopologicalSpace.Opens.coe_iInf, Scheme.Hom.coe_image, TopologicalSpace.Opens.coe_iInf,
    (U.ι.isOpenEmbedding.injective.injOn).image_iInter_eq]
  refine Set.iInter_congr fun h ↦ ?_
  rw [← Scheme.Hom.coe_image, himage]

end FiniteSubsets

section Gluing

variable {G : Type*} {X : Scheme.{u}} {T : G → (X ⟶ X)}

variable (T) in
/-- (Implementation) The `G`-stable affine open subsets of `X`, ordered by inclusion. -/
abbrev StableAffineOpens : Type u := {W : X.Opens // IsAffineOpen W ∧ ∀ g, T g ⁻¹ᵁ W = W}

namespace StableAffineOpens

variable (W : StableAffineOpens T)

instance : IsAffine W.1.toScheme := W.2.1

/-- The action of `G` on a stable open subset. -/
noncomputable def action (g : G) : W.1.toScheme ⟶ W.1.toScheme :=
  (T g).resLE W.1 W.1 (W.2.2 g).ge

@[reassoc (attr := simp)]
lemma action_ι (g : G) : W.action g ≫ W.1.ι = W.1.ι ≫ T g :=
  Scheme.Hom.resLE_comp_ι ..

lemma isRightAction_action [Group G] (hT : IsRightAction T) : IsRightAction W.action where
  map_one := by rw [← cancel_mono W.1.ι, action_ι, hT.map_one]; simp
  map_mul g h := by rw [← cancel_mono W.1.ι, Category.assoc, action_ι, action_ι, action_ι_assoc,
    hT.map_mul]

@[reassoc]
lemma action_homOfLE {W₁ W₂ : StableAffineOpens T} (h : W₁ ≤ W₂) (g : G) :
    W₁.action g ≫ X.homOfLE h = X.homOfLE h ≫ W₂.action g := by
  rw [← cancel_mono W₂.1.ι, Category.assoc, Scheme.homOfLE_ι, action_ι, Category.assoc,
    action_ι, Scheme.homOfLE_ι_assoc]

lemma action_apply_coe (g : G) (x : W.1.toScheme) : (W.action g x).1 = T g x.1 :=
  Scheme.Hom.coe_resLE_apply ..

/-- The trace on `W` of a `G`-stable open subset `O` of `X` is stable. -/
lemma preimage_ι_stable {O : X.Opens} (hO : ∀ g, T g ⁻¹ᵁ O = O) (g : G) :
    W.action g ⁻¹ᵁ (W.1.ι ⁻¹ᵁ O) = W.1.ι ⁻¹ᵁ O := by
  rw [← Scheme.Hom.comp_preimage, action_ι, Scheme.Hom.comp_preimage, hO]

variable [Finite G]

lemma isAdmissible : IsAdmissible W.action :=
  isAdmissible_of_isAffineHom (f := terminal.from W.1.toScheme) fun _ ↦ terminal.hom_ext _ _

/-- (Implementation) The quotient of the stable affine open `W` by `G`. -/
noncomputable def quot : Scheme.{u} := W.isAdmissible.choose

/-- (Implementation) The quotient morphism of `W`. -/
noncomputable def proj : W.1.toScheme ⟶ W.quot := W.isAdmissible.choose_spec.choose

@[reassoc]
lemma proj_comp (g : G) : W.action g ≫ W.proj = W.proj :=
  W.isAdmissible.choose_spec.choose_spec.choose g

instance : IsAffineHom W.proj := W.isAdmissible.choose_spec.choose_spec.choose_spec.1

lemma sectionsAreInvariant_proj (U : W.quot.Opens) :
    SectionsAreInvariant W.action W.proj W.proj_comp U :=
  W.isAdmissible.choose_spec.choose_spec.choose_spec.2 U

variable [Group G] (hT : IsRightAction T)
include hT

lemma isQuotient_proj : IsQuotient W.action W.proj :=
  isQuotient_of_sectionsAreInvariant (W.isRightAction_action hT) fun U _ ↦
    W.sectionsAreInvariant_proj U

lemma surjective_proj : Function.Surjective W.proj :=
  (surjective_and_orbit_of_sectionsAreInvariant (W.isRightAction_action hT) fun U _ ↦
    W.sectionsAreInvariant_proj U).1

lemma exists_action_eq (x x' : W.1.toScheme) (h : W.proj x = W.proj x') :
    ∃ g, W.action g x = x' :=
  (surjective_and_orbit_of_sectionsAreInvariant (W.isRightAction_action hT) fun U _ ↦
    W.sectionsAreInvariant_proj U).2 x x' h

lemma isClosedMap_proj : IsClosedMap W.proj :=
  have := isIntegralHom_of_sectionsAreInvariant (W.isRightAction_action hT) fun U _ ↦
    W.sectionsAreInvariant_proj U
  W.proj.isClosedMap

lemma isAffine_quot : IsAffine W.quot :=
  isAffine_of_isQuotient (W.isRightAction_action hT) (W.isQuotient_proj hT)

variable {W₁ W₂ W₃ : StableAffineOpens T}

/-- (Implementation) The morphism `W₁/G ⟶ W₂/G` induced by `W₁ ⊆ W₂`. -/
noncomputable def transition (h : W₁ ≤ W₂) : W₁.quot ⟶ W₂.quot :=
  (W₁.isQuotient_proj hT).desc (X.homOfLE h ≫ W₂.proj) fun g ↦ by
    rw [action_homOfLE_assoc, proj_comp]

@[reassoc (attr := simp)]
lemma proj_transition (h : W₁ ≤ W₂) :
    W₁.proj ≫ transition hT h = X.homOfLE h ≫ W₂.proj :=
  IsQuotient.fac _ _ _

lemma transition_id : transition hT (le_refl W₁) = 𝟙 _ :=
  (W₁.isQuotient_proj hT).hom_ext (by simp)

lemma transition_comp (h₁₂ : W₁ ≤ W₂) (h₂₃ : W₂ ≤ W₃) :
    transition hT h₁₂ ≫ transition hT h₂₃ = transition hT (h₁₂.trans h₂₃) :=
  (W₁.isQuotient_proj hT).hom_ext (by simp)

/-- (Implementation) The image of `W₁` in `W₂/G`, for `W₁ ⊆ W₂`. -/
noncomputable def imageIn (W₁ W₂ : StableAffineOpens T) : W₂.quot.Opens :=
  imageOpen (W₂.isClosedMap_proj hT) (W₂.1.ι ⁻¹ᵁ W₁.1)

lemma proj_preimage_imageIn (W₁ W₂ : StableAffineOpens T) :
    W₂.proj ⁻¹ᵁ imageIn hT W₁ W₂ = W₂.1.ι ⁻¹ᵁ W₁.1 :=
  preimage_imageOpen _ (W₂.exists_action_eq hT) (W₂.preimage_ι_stable W₁.2.2)

lemma range_transition (h : W₁ ≤ W₂) :
    Set.range (transition hT h) = imageIn hT W₁ W₂ := by
  ext y
  constructor
  · rintro ⟨y₁, rfl⟩
    obtain ⟨x, rfl⟩ := W₁.surjective_proj hT y₁
    rw [← Scheme.Hom.comp_apply, proj_transition, Scheme.Hom.comp_apply]
    change X.homOfLE h x ∈ W₂.proj ⁻¹ᵁ imageIn hT W₁ W₂
    rw [proj_preimage_imageIn]
    change (X.homOfLE h ≫ W₂.1.ι) x ∈ W₁.1
    rw [Scheme.homOfLE_ι]
    exact x.2
  · intro hy
    obtain ⟨x, rfl⟩ := W₂.surjective_proj hT y
    have hx : x ∈ W₂.proj ⁻¹ᵁ imageIn hT W₁ W₂ := hy
    rw [proj_preimage_imageIn] at hx
    have hx' : X.homOfLE h ⟨W₂.1.ι x, hx⟩ = x := Subtype.ext (Scheme.homOfLE_apply h _)
    refine ⟨W₁.proj ⟨W₂.1.ι x, hx⟩, ?_⟩
    calc transition hT h (W₁.proj ⟨W₂.1.ι x, hx⟩)
        = (W₁.proj ≫ transition hT h) ⟨W₂.1.ι x, hx⟩ := rfl
      _ = (X.homOfLE h ≫ W₂.proj) ⟨W₂.1.ι x, hx⟩ := by rw [proj_transition]
      _ = W₂.proj x := congr_arg W₂.proj hx'

instance isOpenImmersion_transition (h : W₁ ≤ W₂) : IsOpenImmersion (transition hT h) := by
  let V := imageIn hT W₁ W₂
  have hV := proj_preimage_imageIn hT W₁ W₂
  have hq := isQuotient_restrict W₂.proj_comp (W₂.isRightAction_action hT)
    (fun U _ ↦ W₂.sectionsAreInvariant_proj U) V
  have hrange : Set.range (X.homOfLE h) = Set.range (W₂.proj ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι, hV, ← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
  let e := IsOpenImmersion.isoOfRangeEq (X.homOfLE h) (W₂.proj ⁻¹ᵁ V).ι hrange
  have he : ∀ g, W₁.action g ≫ e.hom = e.hom ≫ restrictAction W₂.proj_comp V g := fun g ↦ by
    rw [← cancel_mono (W₂.proj ⁻¹ᵁ V).ι, Category.assoc, Category.assoc,
      Scheme.Hom.resLE_comp_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc,
      IsOpenImmersion.isoOfRangeEq_hom_fac, action_homOfLE]
  have hq' := hq.iso_comp e he
  let φ := (W₁.isQuotient_proj hT).uniqueIso hq'
  have : transition hT h = φ.hom ≫ V.ι := by
    refine (W₁.isQuotient_proj hT).hom_ext ?_
    rw [proj_transition, IsQuotient.comp_uniqueIso_hom_assoc, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
  rw [this]
  infer_instance

lemma transition_apply (h : W₁ ≤ W₂) (a : W₁.1.toScheme) :
    transition hT h (W₁.proj a) = W₂.proj (X.homOfLE h a) := by
  change (W₁.proj ≫ transition hT h) a = (X.homOfLE h ≫ W₂.proj) a
  rw [proj_transition]

/-- A `G`-stable affine open `W` and a `G`-stable open `O`: every point of `W ∩ O` has a
`G`-stable affine open neighbourhood inside `W ∩ O`. It is the inverse image of an affine open
of the affine scheme `W/G`, contained in the image of `W ∩ O`. -/
lemma exists_le_inf (W : StableAffineOpens T) {O : X.Opens} (hO : ∀ g, T g ⁻¹ᵁ O = O) {z : X}
    (hz : z ∈ W.1 ⊓ O) : ∃ W' : StableAffineOpens T, W'.1 ≤ W.1 ⊓ O ∧ z ∈ W'.1 := by
  let U := W.1.ι ⁻¹ᵁ O
  have hU := W.preimage_ι_stable hO
  let V := imageOpen (W.isClosedMap_proj hT) U
  have hV : W.proj ⁻¹ᵁ V = U := preimage_imageOpen _ (W.exists_action_eq hT) hU
  let z' : W.1.toScheme := ⟨z, hz.1⟩
  have hz'V : W.proj z' ∈ V := mem_imageOpen _ (W.exists_action_eq hT) hU hz.2
  have := W.isAffine_quot hT
  obtain ⟨V', hV', hzV', hV'V⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.quot.isBasis_affineOpens) hz'V
  let S := W.proj ⁻¹ᵁ V'
  have hS : IsAffineOpen S := hV'.preimage W.proj
  have hSU : S ≤ U := hV ▸ W.proj.preimage_mono hV'V
  have hSstab : ∀ g, S ≤ W.action g ⁻¹ᵁ S := fun g s hs ↦ by
    change W.proj (W.action g s) ∈ V'
    rw [← Scheme.Hom.comp_apply, proj_comp]
    exact hs
  refine ⟨⟨W.1.ι ''ᵁ S, hS.image_of_isOpenImmersion _,
    hT.preimage_eq_of_le fun g ↦ ?_⟩, ?_, ⟨z', hzV', rfl⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨W.action g s, hSstab g hs, congr($(W.action_ι g) s)⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact ⟨s.2, hSU hs⟩

end StableAffineOpens

variable [Finite G] [Group G] (hT : IsRightAction T)

/-- (Implementation) The diagram of the quotients `W/G` of the `G`-stable affine opens `W`. -/
noncomputable abbrev quotientDiagram : StableAffineOpens T ⥤ Scheme.{u} where
  obj W := W.quot
  map φ := StableAffineOpens.transition hT (leOfHom φ)
  map_id _ := StableAffineOpens.transition_id hT
  map_comp _ _ := (StableAffineOpens.transition_comp hT _ _).symm

instance {W₁ W₂ : StableAffineOpens T} (φ : W₁ ⟶ W₂) :
    IsOpenImmersion ((quotientDiagram hT).map φ) :=
  StableAffineOpens.isOpenImmersion_transition hT _

instance : (quotientDiagram hT ⋙ Scheme.forget).IsLocallyDirected where
  cond {W₁ W₂ W₃} f₁ f₂ x₁ x₂ e := by
    change StableAffineOpens.transition hT (leOfHom f₁) x₁ =
      StableAffineOpens.transition hT (leOfHom f₂) x₂ at e
    obtain ⟨a₁, rfl⟩ := W₁.surjective_proj hT x₁
    obtain ⟨a₂, rfl⟩ := W₂.surjective_proj hT x₂
    rw [StableAffineOpens.transition_apply, StableAffineOpens.transition_apply] at e
    obtain ⟨g, hg⟩ := W₃.exists_action_eq hT _ _ e
    have hga : T g a₁.1 = a₂.1 :=
      (congr_arg (T g) (Scheme.homOfLE_apply (leOfHom f₁) a₁).symm).trans
        ((W₃.action_apply_coe g _).symm.trans
          ((congr_arg Subtype.val hg).trans (Scheme.homOfLE_apply (leOfHom f₂) a₂)))
    have ha₂ : a₂.1 ∈ W₁.1 := by
      rw [← hga]
      change a₁.1 ∈ T g ⁻¹ᵁ W₁.1
      rw [W₁.2.2 g]
      exact a₁.2
    obtain ⟨W₄, h₄, hz⟩ := W₁.exists_le_inf hT W₂.2.2 ⟨ha₂, a₂.2⟩
    have h₄₁ : W₄ ≤ W₁ := h₄.trans inf_le_left
    have h₄₂ : W₄ ≤ W₂ := h₄.trans inf_le_right
    refine ⟨W₄, homOfLE h₄₁, homOfLE h₄₂, W₄.proj ⟨a₂.1, hz⟩, ?_, ?_⟩
    · refine (StableAffineOpens.transition_apply hT h₄₁ _).trans
        (Eq.trans ?_ congr($(W₁.proj_comp g) a₁))
      exact congr_arg W₁.proj (Subtype.ext ((Scheme.homOfLE_apply _ _).trans
        (hga.symm.trans (W₁.action_apply_coe g a₁).symm)))
    · exact (StableAffineOpens.transition_apply hT h₄₂ _).trans
        (congr_arg W₂.proj (Subtype.ext (Scheme.homOfLE_apply _ _)))

@[reassoc]
lemma homOfLE_proj_ι {W₁ W₂ : StableAffineOpens T} (h : W₁ ≤ W₂) :
    X.homOfLE h ≫ W₂.proj ≫ colimit.ι (quotientDiagram hT) W₂ =
      W₁.proj ≫ colimit.ι (quotientDiagram hT) W₁ :=
  (StableAffineOpens.proj_transition_assoc hT h _).symm.trans
    (congrArg (W₁.proj ≫ ·) (colimit.w (quotientDiagram hT) (homOfLE h)))

variable (hcov : ⨆ W : StableAffineOpens T, W.1 = ⊤)

/-- (Implementation) The quotient morphism `X ⟶ X/G`, glued from the `W ⟶ W/G`. -/
noncomputable def toGluedQuotient : X ⟶ colimit (quotientDiagram hT) :=
  (X.openCoverOfIsOpenCover (fun W : StableAffineOpens T ↦ W.1) hcov).glueMorphisms
    (fun W ↦ W.proj ≫ colimit.ι (quotientDiagram hT) W) fun (W₁ W₂ : StableAffineOpens T) ↦ by
      change pullback.fst W₁.1.ι W₂.1.ι ≫ W₁.proj ≫ colimit.ι (quotientDiagram hT) W₁ =
        pullback.snd W₁.1.ι W₂.1.ι ≫ W₂.proj ≫ colimit.ι (quotientDiagram hT) W₂
      refine Scheme.hom_ext_of_forall _ _ fun pt ↦ ?_
      let z := (pullback.fst W₁.1.ι W₂.1.ι ≫ W₁.1.ι) pt
      have hz : z ∈ W₁.1 ⊓ W₂.1 := by
        refine ⟨(pullback.fst W₁.1.ι W₂.1.ι pt).2, ?_⟩
        change (pullback.fst W₁.1.ι W₂.1.ι ≫ W₁.1.ι) pt ∈ W₂.1
        rw [pullback.condition]
        exact (pullback.snd W₁.1.ι W₂.1.ι pt).2
      obtain ⟨W₄, h₄, hz₄⟩ := W₁.exists_le_inf hT W₂.2.2 hz
      let O := (pullback.fst W₁.1.ι W₂.1.ι ≫ W₁.1.ι) ⁻¹ᵁ W₄.1
      have hr : Set.range (O.ι ≫ pullback.fst W₁.1.ι W₂.1.ι ≫ W₁.1.ι) ⊆ Set.range W₄.1.ι := by
        rintro _ ⟨o, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact o.2
      let m := IsOpenImmersion.lift W₄.1.ι _ hr
      have hm : m ≫ W₄.1.ι = O.ι ≫ pullback.fst W₁.1.ι W₂.1.ι ≫ W₁.1.ι :=
        IsOpenImmersion.lift_fac _ _ _
      have hm₁ : m ≫ X.homOfLE (h₄.trans inf_le_left) = O.ι ≫ pullback.fst _ _ := by
        rw [← cancel_mono W₁.1.ι, Category.assoc, Scheme.homOfLE_ι, hm, Category.assoc]
      have hm₂ : m ≫ X.homOfLE (h₄.trans inf_le_right) = O.ι ≫ pullback.snd _ _ := by
        rw [← cancel_mono W₂.1.ι, Category.assoc, Scheme.homOfLE_ι, hm, pullback.condition,
          Category.assoc]
      have e₁ : O.ι ≫ pullback.fst W₁.1.ι W₂.1.ι ≫ W₁.proj ≫ colimit.ι (quotientDiagram hT) W₁ =
          m ≫ W₄.proj ≫ colimit.ι (quotientDiagram hT) W₄ := by
        rw [← Category.assoc, ← hm₁, Category.assoc, homOfLE_proj_ι]
      have e₂ : O.ι ≫ pullback.snd W₁.1.ι W₂.1.ι ≫ W₂.proj ≫ colimit.ι (quotientDiagram hT) W₂ =
          m ≫ W₄.proj ≫ colimit.ι (quotientDiagram hT) W₄ := by
        rw [← Category.assoc, ← hm₂, Category.assoc, homOfLE_proj_ι]
      exact ⟨O, hz₄, e₁.trans e₂.symm⟩

@[reassoc]
lemma ι_toGluedQuotient (W : StableAffineOpens T) :
    W.1.ι ≫ toGluedQuotient hT hcov = W.proj ≫ colimit.ι (quotientDiagram hT) W :=
  Scheme.Cover.ι_glueMorphisms (X.openCoverOfIsOpenCover (fun W : StableAffineOpens T ↦ W.1)
    hcov) _ _ W

lemma toGluedQuotient_apply (W : StableAffineOpens T) (x : W.1.toScheme) :
    toGluedQuotient hT hcov x.1 = colimit.ι (quotientDiagram hT) W (W.proj x) :=
  congr($(ι_toGluedQuotient hT hcov W) x)

lemma preimage_opensRange_ι (W : StableAffineOpens T) :
    toGluedQuotient hT hcov ⁻¹ᵁ (colimit.ι (quotientDiagram hT) W).opensRange = W.1 := by
  apply le_antisymm
  · rintro x ⟨y, hy⟩
    obtain ⟨W₀, hx₀⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
    have hx := toGluedQuotient_apply hT hcov W₀ ⟨x, hx₀⟩
    obtain ⟨W₁, f₀, f, z, hz₀, rfl⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (quotientDiagram hT)).mp (hy.trans hx).symm
    obtain ⟨a, rfl⟩ := W₁.surjective_proj hT z
    change StableAffineOpens.transition hT (leOfHom f₀) (W₁.proj a) = _ at hz₀
    rw [StableAffineOpens.transition_apply] at hz₀
    obtain ⟨g, hg⟩ := W₀.exists_action_eq hT _ _ hz₀
    have hga : T g a.1 = x :=
      (congr_arg (T g) (Scheme.homOfLE_apply (leOfHom f₀) a).symm).trans
        ((W₀.action_apply_coe g _).symm.trans (congr_arg Subtype.val hg))
    apply leOfHom f
    rw [← hga]
    change a.1 ∈ T g ⁻¹ᵁ W₁.1
    rw [W₁.2.2 g]
    exact a.2
  · intro x hx
    exact ⟨_, (toGluedQuotient_apply hT hcov W ⟨x, hx⟩).symm⟩

lemma isPullback_ι_toGluedQuotient (W : StableAffineOpens T) :
    IsPullback W.proj W.1.ι (colimit.ι (quotientDiagram hT) W) (toGluedQuotient hT hcov) :=
  IsOpenImmersion.isPullback _ _ _ _ (ι_toGluedQuotient hT hcov W)
    (by rw [preimage_opensRange_ι, Scheme.Opens.opensRange_ι])

lemma comp_toGluedQuotient (g : G) : T g ≫ toGluedQuotient hT hcov = toGluedQuotient hT hcov :=
  Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover (fun W : StableAffineOpens T ↦ W.1) hcov) _ _
    fun (W : StableAffineOpens T) ↦ by
      change W.1.ι ≫ T g ≫ _ = W.1.ι ≫ _
      rw [← StableAffineOpens.action_ι_assoc, ι_toGluedQuotient, W.proj_comp_assoc]

lemma iSup_opensRange_ι :
    ⨆ W : StableAffineOpens T, (colimit.ι (quotientDiagram hT) W).opensRange = ⊤ := by
  refine top_le_iff.mp fun y _ ↦ ?_
  obtain ⟨W, y', rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (quotientDiagram hT) y
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨W, y', rfl⟩

set_option backward.isDefEq.respectTransparency false in
instance : IsAffineHom (toGluedQuotient hT hcov) := by
  have (W : StableAffineOpens T) : IsAffine W.quot := W.isAffine_quot hT
  refine HasAffineProperty.of_iSup_eq_top (P := @IsAffineHom)
    (fun W : StableAffineOpens T ↦ ⟨(colimit.ι (quotientDiagram hT) W).opensRange,
      isAffineOpen_opensRange _⟩) (iSup_opensRange_ι hT) fun W ↦ ?_
  change IsAffine (toGluedQuotient hT hcov ⁻¹ᵁ (colimit.ι (quotientDiagram hT) W).opensRange)
  rw [preimage_opensRange_ι]
  exact W.2.1

lemma sectionsAreInvariant_toGluedQuotient (U : (colimit (quotientDiagram hT)).Opens) :
    SectionsAreInvariant T (toGluedQuotient hT hcov) (comp_toGluedQuotient hT hcov) U := by
  refine sectionsAreInvariant_of_basis (fun y N hyN ↦ ?_) U
  obtain ⟨W, y', rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (quotientDiagram hT) y
  let ι := colimit.ι (quotientDiagram hT) W
  refine ⟨ι ''ᵁ (ι ⁻¹ᵁ N), Scheme.Hom.image_preimage_le _ _, ⟨y', hyN, rfl⟩, ?_⟩
  exact SectionsAreInvariant.image W.1.ι ι (ι_toGluedQuotient hT hcov W)
    (by rw [preimage_opensRange_ι, Scheme.Opens.opensRange_ι]) (StableAffineOpens.action_ι W)
    (W.sectionsAreInvariant_proj _)

include hT in
/-- V.1.8, sufficiency: if `X` is a union of `G`-stable affine open subsets, then `G` acts
admissibly. The quotient is glued from the quotients `W/G` of the `G`-stable affine opens `W`
along the open immersions `W₁/G ⟶ W₂/G` for `W₁ ⊆ W₂` (V.1.4), with mathlib's colimits of
locally directed diagrams of open immersions. -/
theorem isAdmissible_of_forall_exists_isAffineOpen
    (H : ∀ x, ∃ U : X.Opens, IsAffineOpen U ∧ (∀ g, T g ⁻¹ᵁ U = U) ∧ x ∈ U) :
    IsAdmissible T := by
  have hcov : ⨆ W : StableAffineOpens T, W.1 = ⊤ := by
    refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨U, hU, hUs, hxU⟩ := H x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU, hUs⟩, hxU⟩
  exact ⟨_, toGluedQuotient hT hcov, comp_toGluedQuotient hT hcov, inferInstance,
    sectionsAreInvariant_toGluedQuotient hT hcov⟩

include hT in
/-- V.1.8 (first form): a finite group acts admissibly iff `X` is a union of `G`-stable affine
open subsets. -/
theorem isAdmissible_iff_forall_exists_isAffineOpen :
    IsAdmissible T ↔ ∀ x, ∃ U : X.Opens, IsAffineOpen U ∧ (∀ g, T g ⁻¹ᵁ U = U) ∧ x ∈ U :=
  ⟨IsAdmissible.exists_isAffineOpen, isAdmissible_of_forall_exists_isAffineOpen hT⟩

end Gluing


section Main

variable {G : Type*} [Group G] [Finite G] {X : Scheme.{u}} {T : G → (X ⟶ X)}

/-- V.1.8 (second form): a finite group acts admissibly iff every orbit lies in an affine open
subset. -/
theorem isAdmissible_iff_forall_exists_isAffineOpen_orbit (hT : IsRightAction T) :
    IsAdmissible T ↔ ∀ x, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g, T g x ∈ U := by
  refine ⟨IsAdmissible.exists_isAffineOpen_orbit, fun H ↦ ?_⟩
  refine isAdmissible_of_forall_exists_isAffineOpen hT fun x ↦ ?_
  obtain ⟨U, hU, hxU⟩ := H x
  exact exists_isAffineOpen_stable_of_orbit hT hU hxU

section QuasiAffine

/-- Every finite subset of a quasi-affine scheme lies in an affine open subset. -/
lemma exists_isAffineOpen_superset_of_finite {X : Scheme.{u}} [X.IsQuasiAffine] {F : Set X}
    (hF : F.Finite) : ∃ U : X.Opens, IsAffineOpen U ∧ F ⊆ U := by
  let j := X.toSpecΓ
  obtain ⟨r, hrF, hrU⟩ := exists_basicOpen_le_of_finite (isAffineOpen_top (Spec Γ(X, ⊤)))
    le_top (hF.image j) (Set.image_subset_iff.mpr fun x _ ↦ ⟨x, rfl⟩ : j '' F ⊆ j.opensRange)
  refine ⟨j ⁻¹ᵁ (Spec Γ(X, ⊤)).basicOpen r, ?_, fun x hx ↦ hrF ⟨x, hx, rfl⟩⟩
  rw [← j.isAffineOpen_iff_of_isOpenImmersion, Scheme.Hom.image_preimage_eq_opensRange_inf,
    inf_eq_right.mpr hrU]
  exact (isAffineOpen_top (Spec Γ(X, ⊤))).basicOpen r

variable {Y : Scheme.{u}}

/-- If `X` is quasi-affine over `Y` (e.g. quasi-finite and separated, VIII.6.2) and `G` acts by
`Y`-automorphisms, then `G` acts admissibly: every orbit lies in a fibre, hence in the inverse
image of an affine open of `Y`, which is quasi-affine; so V.1.8 applies. This is the argument of
SGA for V.3.1, with "quasi-affine" in place of "quasi-projective". -/
theorem isAdmissible_of_isQuasiAffineHom (hT : IsRightAction T) (f : X ⟶ Y) [IsQuasiAffineHom f]
    (hTf : ∀ g, T g ≫ f = f) : IsAdmissible T := by
  refine (isAdmissible_iff_forall_exists_isAffineOpen_orbit hT).mpr fun x ↦ ?_
  obtain ⟨V, hV, hxV⟩ := exists_isAffineOpen_mem (f x)
  have := hV.isQuasiAffine_preimage f
  obtain ⟨U, hU, hFU⟩ := exists_isAffineOpen_superset_of_finite (X := (f ⁻¹ᵁ V).toScheme)
    (Set.finite_range fun g ↦ (⟨T g x, show f (T g x) ∈ V by
      rw [← Scheme.Hom.comp_apply, hTf]; exact hxV⟩ : (f ⁻¹ᵁ V).toScheme))
  exact ⟨(f ⁻¹ᵁ V).ι ''ᵁ U, hU.image_of_isOpenImmersion _, fun g ↦ ⟨_, hFU ⟨g, rfl⟩, rfl⟩⟩

end QuasiAffine

end Main

/-- V.1.8 holds. -/
theorem isAdmissibleIffStatement : IsAdmissibleIffStatement.{u} := fun _ _ _ _ _ hT ↦
  ⟨isAdmissible_iff_forall_exists_isAffineOpen hT,
    isAdmissible_iff_forall_exists_isAffineOpen_orbit hT⟩

end SGA.SGA1.ExposeV
