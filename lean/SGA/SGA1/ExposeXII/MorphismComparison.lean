/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeI.CompletionCriteria
import SGA.SGA1.ExposeXII.LocalRings

/-!
# SGA 1, Exposé XII, 3.1 (i)–(iv): comparison squares of local rings

SGA proves XII.3.1 (i)–(iv) by comparing, for `x ∈ X^an` and `y = f^an(x)`, the local
homomorphism `𝒪_{Y^an, y} → 𝒪_{X^an, x}` with `𝒪_{Y, ψ(y)} → 𝒪_{X, φ(x)}`: they become equal
after completion (XII.1.1). This file is the commutative algebra behind that argument.

A local homomorphism `a : A → A'` of local rings is a *comparison homomorphism*
(`IsComparisonHom`) if it is flat, `𝔪_A A' = 𝔪_{A'}`, and it induces a bijection of residue
fields. These are the properties of `𝒪_{X, φ(x)} → 𝒪_{X^an, x}` proved in XII.2.1
(`AffineAnalytification.map_maximalIdeal_stalkComparison`, `faithfullyFlat_stalkMap_toSpec`,
`residueFieldEquiv`). For noetherian local rings, a comparison homomorphism induces an isomorphism
of completions (`bijective_completionHom`, from I.4.4).

Given a commutative square of local homomorphisms of noetherian local rings
```
A₀ --u--> B₀
|a        |b
v         v
A₁ --v--> B₁
```
with `a` and `b` comparison homomorphisms:

* `flat_iff_flat_of_comparison`: `u` is flat iff `v` is (through the completions, IV.5.8);
* `map_maximalIdeal_eq_iff_of_comparison`: `𝔪_{A₀} B₀ = 𝔪_{B₀}` iff `𝔪_{A₁} B₁ = 𝔪_{B₁}`
  (faithful flatness of `b`);
* `isRegularLocalRing_fibre_iff_of_comparison`: the closed fibres `B₀/𝔪_{A₀}B₀` and
  `B₁/𝔪_{A₁}B₁` are regular together (I.9.1).

References: SGA 1 XII.3.1 and its proof; Bourbaki, *Algèbre commutative*, III §5 prop. 4;
EGA IV 17.4.4.
-/

universe u

noncomputable section

open IsLocalRing AdicCompletion

namespace SGA.SGA1.ExposeXII

section CompletionHom

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [IsLocalRing A] [IsLocalRing B]
  [IsLocalRing C]

/-- The map of `𝔪`-adic completions `Â → B̂` induced by a local homomorphism `a : A → B`
(`ExposeI.completionMap` for the algebra structure defined by `a`). -/
def completionHom (a : A →+* B) [IsLocalHom a] :
    AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B :=
  letI := a.toAlgebra
  haveI : IsLocalHom (algebraMap A B) := ‹IsLocalHom a›
  ExposeI.completionMap A B

lemma map_maximalIdeal_pow_le_comap (a : A →+* B) [IsLocalHom a] (n : ℕ) :
    maximalIdeal A ^ n ≤ (maximalIdeal B ^ n).comap a := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (map_maximalIdeal_le a) n

lemma evalₐ_completionHom (a : A →+* B) [IsLocalHom a] (n : ℕ)
    (x : AdicCompletion (maximalIdeal A) A) :
    evalₐ (maximalIdeal B) n (completionHom a x) =
      Ideal.quotientMap _ a (map_maximalIdeal_pow_le_comap a n) (evalₐ (maximalIdeal A) n x) :=
  let := a.toAlgebra
  have : IsLocalHom (algebraMap A B) := ‹IsLocalHom a›
  ExposeI.evalₐ_completionMap A B n x

/-- Functoriality of `completionHom`. -/
lemma completionHom_comp (a : A →+* B) (b : B →+* C) [IsLocalHom a] [IsLocalHom b] :
    completionHom (b.comp a) = (completionHom b).comp (completionHom a) := by
  refine RingHom.ext fun x ↦ ext_evalₐ fun n ↦ ?_
  rw [RingHom.comp_apply, evalₐ_completionHom, evalₐ_completionHom, evalₐ_completionHom]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal A) n x)
  rw [← hy, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk, RingHom.comp_apply]

variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- I.4.2, flatness, for a ring homomorphism: `a : A → B` is flat iff `Â → B̂` is. -/
lemma flat_iff_flat_completionHom (a : A →+* B) [IsLocalHom a] :
    a.Flat ↔ (completionHom a).Flat := by
  let := a.toAlgebra
  have : IsLocalHom (algebraMap A B) := ‹IsLocalHom a›
  exact ExposeI.flat_iff_flat_completion A B

end CompletionHom

section Comparison

variable {A A' : Type u} [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A']

/-- A local homomorphism `a : A → A'` of local rings is a *comparison homomorphism* if it is flat,
`𝔪_A A' = 𝔪_{A'}`, and it induces a bijection of residue fields. These are the properties of
`𝒪_{X, φ(x)} → 𝒪_{X^an, x}` for `X` locally of finite type over `ℂ` (XII.2.1); for noetherian
local rings they mean that `a` induces an isomorphism of completions
(`IsComparisonHom.bijective_completionHom`).

This is `ExposeI.IsEtaleLocalHom` (flat and unramified, I.3.1, I.4.1) plus bijectivity of the
residue field map, stated for a ring homomorphism rather than an algebra structure; it is kept
because the comparison squares below compose ring homomorphisms. Use it (and
`ExposeI.isEtaleLocalHom_iff_bijective_completionMap`, which `bijective_completionHom` wraps)
rather than introducing a third variant. -/
structure IsComparisonHom (a : A →+* A') [IsLocalHom a] : Prop where
  flat : a.Flat
  map_maximalIdeal : (maximalIdeal A).map a = maximalIdeal A'
  bijective_residueFieldMap : Function.Bijective (ResidueField.map a)

namespace IsComparisonHom

variable {a : A →+* A'} [IsLocalHom a]

lemma of_eq {a' : A →+* A'} (h : IsComparisonHom a) (e : a = a') :
    haveI : IsLocalHom a' := e ▸ ‹IsLocalHom a›
    IsComparisonHom a' := by
  subst e
  exact h

lemma faithfullyFlat (h : IsComparisonHom a) : a.FaithfullyFlat := by
  algebraize [a]
  have : IsLocalHom (algebraMap A A') := ‹IsLocalHom a›
  have : Module.Flat A A' := h.flat
  rw [← RingHom.algebraMap_toAlgebra a, RingHom.faithfullyFlat_algebraMap_iff]
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- `I A' ∩ A = I` for every ideal `I` of `A`. -/
lemma comap_map (h : IsComparisonHom a) (I : Ideal A) : (I.map a).comap a = I := by
  algebraize [a]
  have : IsLocalHom (algebraMap A A') := ‹IsLocalHom a›
  have : Module.Flat A A' := h.flat
  have : Module.FaithfullyFlat A A' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

/-- I.4.4: a comparison homomorphism of noetherian local rings induces an isomorphism of
completions. -/
theorem bijective_completionHom [IsNoetherianRing A] [IsNoetherianRing A']
    (h : IsComparisonHom a) : Function.Bijective (completionHom a) := by
  let := a.toAlgebra
  have : IsLocalHom (algebraMap A A') := ‹IsLocalHom a›
  have hk : Function.Bijective (ResidueField.map (algebraMap A A')) := h.bijective_residueFieldMap
  refine (ExposeI.isEtaleLocalHom_iff_bijective_completionMap A A' hk).mp ⟨h.flat, ?_, ?_, ?_⟩
  · exact h.map_maximalIdeal
  · let e : ResidueField A →ₗ[ResidueField A] ResidueField A' := Algebra.linearMap _ _
    exact Module.Finite.of_surjective e hk.2
  · refine ⟨fun x ↦ ?_⟩
    obtain ⟨c, rfl⟩ := hk.2 x
    exact isSeparable_algebraMap c

/-- Precomposing a comparison homomorphism with a ring isomorphism gives a comparison
homomorphism. -/
lemma comp_of_bijective {R : Type u} [CommRing R] [IsLocalRing R] {s : R →+* A} [IsLocalHom s]
    (hs : Function.Bijective s) (h : IsComparisonHom a) : IsComparisonHom (a.comp s) where
  flat := (RingHom.Flat.comp_iff_of_bijective_right hs).mpr h.flat
  map_maximalIdeal := by
    rw [← Ideal.map_map, map_maximalIdeal_of_surjective s hs.2, h.map_maximalIdeal]
  bijective_residueFieldMap := by
    rw [ResidueField.map_comp]
    exact h.bijective_residueFieldMap.comp
      (ResidueField.mapEquiv (RingEquiv.ofBijective s hs)).bijective

/-- Postcomposing a comparison homomorphism with a ring isomorphism gives a comparison
homomorphism. -/
lemma bijective_comp {R : Type u} [CommRing R] [IsLocalRing R] {t : A' →+* R} [IsLocalHom t]
    (ht : Function.Bijective t) (h : IsComparisonHom a) : IsComparisonHom (t.comp a) where
  flat := (RingHom.Flat.comp_iff_of_bijective_left ht).mpr h.flat
  map_maximalIdeal := by
    rw [← Ideal.map_map, h.map_maximalIdeal, map_maximalIdeal_of_surjective t ht.2]
  bijective_residueFieldMap := by
    rw [ResidueField.map_comp]
    exact (ResidueField.mapEquiv (RingEquiv.ofBijective t ht)).bijective.comp
      h.bijective_residueFieldMap

end IsComparisonHom

end Comparison

section Square

variable {A₀ B₀ A₁ B₁ : Type u} [CommRing A₀] [CommRing B₀] [CommRing A₁] [CommRing B₁]
  [IsLocalRing A₀] [IsLocalRing B₀] [IsLocalRing A₁] [IsLocalRing B₁]
  (u : A₀ →+* B₀) (v : A₁ →+* B₁) (a : A₀ →+* A₁) (b : B₀ →+* B₁)
  [IsLocalHom u] [IsLocalHom v] [IsLocalHom a] [IsLocalHom b]

/-- XII.3.1 (i), local form: in a commutative square of local homomorphisms of noetherian local
rings whose vertical maps are comparison homomorphisms, the top map is flat iff the bottom one is.
Both become the same map after completion (XII.1.1), and flatness can be read on completions
(IV.5.8). -/
theorem flat_iff_flat_of_comparison [IsNoetherianRing A₀] [IsNoetherianRing B₀]
    [IsNoetherianRing A₁] [IsNoetherianRing B₁] (hsq : v.comp a = b.comp u)
    (ha : IsComparisonHom a) (hb : IsComparisonHom b) : u.Flat ↔ v.Flat := by
  have h₁ := completionHom_comp a v
  have h₂ := completionHom_comp u b
  have hsq' : (completionHom v).comp (completionHom a) =
      (completionHom b).comp (completionHom u) := by
    rw [← h₁, ← h₂]
    congr 1
  rw [flat_iff_flat_completionHom u, flat_iff_flat_completionHom v,
    ← RingHom.Flat.comp_iff_of_bijective_left hb.bijective_completionHom,
    ← RingHom.Flat.comp_iff_of_bijective_right (f := completionHom v)
      ha.bijective_completionHom, hsq']

omit [IsLocalHom u] [IsLocalHom v] in
/-- XII.3.1 (ii), local form: in a commutative square of local homomorphisms whose vertical maps
are comparison homomorphisms, `𝔪_{A₀} B₀ = 𝔪_{B₀}` iff `𝔪_{A₁} B₁ = 𝔪_{B₁}`. -/
theorem map_maximalIdeal_eq_iff_of_comparison (hsq : v.comp a = b.comp u)
    (ha : IsComparisonHom a) (hb : IsComparisonHom b) :
    (maximalIdeal A₀).map u = maximalIdeal B₀ ↔ (maximalIdeal A₁).map v = maximalIdeal B₁ := by
  have key : (maximalIdeal A₁).map v = ((maximalIdeal A₀).map u).map b := by
    rw [← ha.map_maximalIdeal, Ideal.map_map, Ideal.map_map, hsq]
  rw [key, ← hb.map_maximalIdeal]
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← hb.comap_map ((maximalIdeal A₀).map u), h, hb.comap_map]

/-- The local ring structure on the closed fibre `B ⧸ 𝔪_A B` of a local homomorphism. -/
lemma isLocalRing_fibre {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] : IsLocalRing (B ⧸ (maximalIdeal A).map f) :=
  have : Nontrivial (B ⧸ (maximalIdeal A).map f) :=
    Ideal.Quotient.nontrivial_iff.mpr (map_maximalIdeal_lt_top f).ne
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- XII.3.1 (iv), local form: in a commutative square of local homomorphisms of noetherian local
rings whose vertical maps are comparison homomorphisms, the closed fibres `B₀/𝔪_{A₀}B₀` and
`B₁/𝔪_{A₁}B₁` are regular together (the induced map between them is flat with
`𝔪 B₁/𝔪_{A₁}B₁ = 𝔪_{B₀} · B₁/𝔪_{A₁}B₁`, I.9.1). -/
theorem isRegularLocalRing_fibre_iff_of_comparison [IsNoetherianRing B₀] [IsNoetherianRing B₁]
    (hsq : v.comp a = b.comp u) (ha : IsComparisonHom a) (hb : IsComparisonHom b) :
    IsRegularLocalRing (B₀ ⧸ (maximalIdeal A₀).map u) ↔
      IsRegularLocalRing (B₁ ⧸ (maximalIdeal A₁).map v) := by
  set I := (maximalIdeal A₀).map u
  have key : I.map b = (maximalIdeal A₁).map v := by
    rw [← ha.map_maximalIdeal, Ideal.map_map, Ideal.map_map, hsq]
  have := isLocalRing_fibre u
  have := isLocalRing_fibre v
  have : IsLocalRing (B₁ ⧸ I.map b) := key ▸ ‹IsLocalRing (B₁ ⧸ (maximalIdeal A₁).map v)›
  let c : B₀ ⧸ I →+* B₁ ⧸ I.map b := Ideal.quotientMap (I.map b) b Ideal.le_comap_map
  have hc : (maximalIdeal (B₀ ⧸ I)).map c = maximalIdeal (B₁ ⧸ I.map b) := by
    have h₁ := map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have h₂ := map_maximalIdeal_of_surjective (Ideal.Quotient.mk (I.map b))
      Ideal.Quotient.mk_surjective
    rw [← h₁, ← h₂, ← hb.map_maximalIdeal, Ideal.map_map (Ideal.Quotient.mk I) c,
      Ideal.map_map b (Ideal.Quotient.mk (I.map b))]
    rfl
  have : IsLocalHom c := ⟨fun x hx ↦ by
    by_contra h
    have hx' : x ∈ maximalIdeal (B₀ ⧸ I) := h
    exact hc.le (Ideal.mem_map_of_mem c hx') hx⟩
  algebraize [c]
  have : IsLocalHom (algebraMap (B₀ ⧸ I) (B₁ ⧸ I.map b)) := ‹IsLocalHom c›
  have : Module.Flat (B₀ ⧸ I) (B₁ ⧸ I.map b) := hb.flat.quotientMap I
  have hreg := ExposeI.isRegularLocalRing_iff_of_flat (A := B₀ ⧸ I) (B := B₁ ⧸ I.map b) hc
  rw [hreg]
  constructor
  · intro h
    exact IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq key)
  · intro h
    exact IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq key).symm

end Square

/-! ### Comparison squares of locally ringed spaces -/

namespace LocallyRingedSpaceComparison

open CategoryTheory AlgebraicGeometry

variable {X Y X' Y' : LocallyRingedSpace.{u}}

/-- A morphism of locally ringed spaces `φ : X' → X` is a *comparison morphism* if its stalk maps
`𝒪_{X, φ(x)} → 𝒪_{X', x}` are comparison homomorphisms of noetherian local rings
(`IsComparisonHom`). This holds for the canonical morphism `φ : X^an → X` of a scheme locally of
finite type over `ℂ` (XII.2.1). -/
structure IsComparison (φ : X' ⟶ X) : Prop where
  isNoetherianRing_stalk : ∀ x, IsNoetherianRing (X'.presheaf.stalk x)
  isNoetherianRing_stalk_base : ∀ x, IsNoetherianRing (X.presheaf.stalk (φ.base x))
  isComparisonHom : ∀ x, IsComparisonHom (φ.stalkMap x).hom

/-- A bijective ring homomorphism is local. -/
lemma isLocalHom_of_bijective {R S : Type*} [CommRing R] [CommRing S] {s : R →+* S}
    (hs : Function.Bijective s) : IsLocalHom s :=
  ⟨fun x hx ↦ (isLocalHom_equiv (RingEquiv.ofBijective s hs)).map_nonunit x hx⟩

lemma bijective_stalkMap_of_isOpenImmersion {Z W : LocallyRingedSpace.{u}} (e : Z ⟶ W)
    [LocallyRingedSpace.IsOpenImmersion e] (z : Z) : Function.Bijective (e.stalkMap z).hom :=
  ConcreteCategory.bijective_of_isIso (e.stalkMap z)

/-- A comparison morphism followed by an open immersion (for instance an isomorphism, by
`LocallyRingedSpace.IsOpenImmersion.of_isIso`) is a comparison morphism. -/
lemma IsComparison.comp_isOpenImmersion {Z : LocallyRingedSpace.{u}} {φ : X' ⟶ X}
    (h : IsComparison φ) (e : X ⟶ Z) [LocallyRingedSpace.IsOpenImmersion e] :
    IsComparison (φ ≫ e) where
  isNoetherianRing_stalk := h.isNoetherianRing_stalk
  isNoetherianRing_stalk_base x :=
    have := h.isNoetherianRing_stalk_base x
    isNoetherianRing_of_ringEquiv _ (RingEquiv.ofBijective _
      (bijective_stalkMap_of_isOpenImmersion e (φ.base x))).symm
  isComparisonHom x := by
    have := h.isNoetherianRing_stalk_base x
    have hb := bijective_stalkMap_of_isOpenImmersion e (φ.base x)
    have := isLocalHom_of_bijective hb
    have key : ((φ ≫ e).stalkMap x).hom = (φ.stalkMap x).hom.comp (e.stalkMap (φ.base x)).hom := by
      rw [LocallyRingedSpace.stalkMap_comp]
      rfl
    exact ((h.isComparisonHom x).comp_of_bijective hb).of_eq key.symm

/-- An open immersion followed by a comparison morphism is a comparison morphism. -/
lemma IsComparison.isOpenImmersion_comp {U : LocallyRingedSpace.{u}} {φ : X' ⟶ X}
    (h : IsComparison φ) (ι : U ⟶ X') [LocallyRingedSpace.IsOpenImmersion ι] :
    IsComparison (ι ≫ φ) where
  isNoetherianRing_stalk x :=
    have := h.isNoetherianRing_stalk (ι.base x)
    isNoetherianRing_of_ringEquiv _ (RingEquiv.ofBijective _
      (bijective_stalkMap_of_isOpenImmersion ι x))
  isNoetherianRing_stalk_base x := h.isNoetherianRing_stalk_base (ι.base x)
  isComparisonHom x := by
    have hb := bijective_stalkMap_of_isOpenImmersion ι x
    have key : ((ι ≫ φ).stalkMap x).hom = (ι.stalkMap x).hom.comp (φ.stalkMap (ι.base x)).hom := by
      rw [LocallyRingedSpace.stalkMap_comp]
      rfl
    exact ((h.isComparisonHom (ι.base x)).bijective_comp hb).of_eq key.symm

/-- A morphism whose composites with the members of an open cover are comparison morphisms is a
comparison morphism. -/
lemma IsComparison.of_cover {Z : LocallyRingedSpace.{u}} {φ : Z ⟶ X} {α : Type*}
    {W : α → LocallyRingedSpace.{u}} (ιs : ∀ a, W a ⟶ Z)
    [∀ a, LocallyRingedSpace.IsOpenImmersion (ιs a)] (hcov : ∀ z, ∃ a w, (ιs a).base w = z)
    (h : ∀ a, IsComparison (ιs a ≫ φ)) : IsComparison φ := by
  have key (a : α) (w : W a) : IsNoetherianRing (Z.presheaf.stalk ((ιs a).base w)) ∧
      IsNoetherianRing (X.presheaf.stalk (φ.base ((ιs a).base w))) ∧
      IsComparisonHom (φ.stalkMap ((ιs a).base w)).hom := by
    have hb := bijective_stalkMap_of_isOpenImmersion (ιs a) w
    let e := RingEquiv.ofBijective _ hb
    have := (h a).isNoetherianRing_stalk w
    have := (h a).isNoetherianRing_stalk_base w
    refine ⟨isNoetherianRing_of_ringEquiv _ e.symm, (h a).isNoetherianRing_stalk_base w, ?_⟩
    have := isNoetherianRing_of_ringEquiv _ e.symm
    let t : (W a).presheaf.stalk w →+* Z.presheaf.stalk ((ιs a).base w) := e.symm.toRingHom
    have ht : Function.Bijective t := e.symm.bijective
    have := isLocalHom_of_bijective ht
    have key : t.comp ((ιs a ≫ φ).stalkMap w).hom = (φ.stalkMap ((ιs a).base w)).hom := by
      rw [LocallyRingedSpace.stalkMap_comp]
      ext x
      exact e.symm_apply_apply _
    exact (((h a).isComparisonHom w).bijective_comp ht).of_eq key
  refine ⟨fun z ↦ ?_, fun z ↦ ?_, fun z ↦ ?_⟩ <;> obtain ⟨a, w, rfl⟩ := hcov z
  · exact (key a w).1
  · exact (key a w).2.1
  · exact (key a w).2.2

/-- The stalk map of a morphism along an equality of points is an isomorphism. -/
lemma bijective_stalkSpecializes {Z : LocallyRingedSpace.{u}} {z z' : Z} (h : z = z')
    (hs : z ⤳ z') : Function.Bijective (Z.presheaf.stalkSpecializes hs).hom := by
  subst h
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

variable (f : X ⟶ Y) (f' : X' ⟶ Y') (φX : X' ⟶ X) (φY : Y' ⟶ Y)

lemma base_apply_eq (hsq : f' ≫ φY = φX ≫ f) (x' : X') :
    f.base (φX.base x') = φY.base (f'.base x') :=
  (congrArg (fun g : X' ⟶ Y ↦ g.base x') hsq).symm

/-- The identification of the stalks of `Y` at `φY(f'(x'))` and `f(φX(x'))`. -/
def stalkSpecializesOfSquare (hsq : f' ≫ φY = φX ≫ f) (x' : X') :
    Y.presheaf.stalk (φY.base (f'.base x')) ⟶ Y.presheaf.stalk (f.base (φX.base x')) :=
  Y.presheaf.stalkSpecializes (specializes_of_eq (base_apply_eq f f' φX φY hsq x'))

lemma bijective_stalkSpecializesOfSquare (hsq : f' ≫ φY = φX ≫ f) (x' : X') :
    Function.Bijective (stalkSpecializesOfSquare f f' φX φY hsq x').hom :=
  bijective_stalkSpecializes (base_apply_eq f f' φX φY hsq x') _

/-- The algebraic stalk map of `f` at `φX(x')`, seen as a map out of the stalk of `Y` at
`φY(f'(x'))` (the same point, by commutativity of the square). -/
def algStalkMap (hsq : f' ≫ φY = φX ≫ f) (x' : X') :
    Y.presheaf.stalk (φY.base (f'.base x')) →+* X.presheaf.stalk (φX.base x') :=
  (f.stalkMap (φX.base x')).hom.comp (stalkSpecializesOfSquare f f' φX φY hsq x').hom

instance (hsq : f' ≫ φY = φX ≫ f) (x' : X') :
    IsLocalHom (stalkSpecializesOfSquare f f' φX φY hsq x').hom :=
  isLocalHom_of_bijective (bijective_stalkSpecializesOfSquare f f' φX φY hsq x')

instance (hsq : f' ≫ φY = φX ≫ f) (x' : X') : IsLocalHom (algStalkMap f f' φX φY hsq x') := by
  unfold algStalkMap
  infer_instance

/-- The square of stalk maps of a commutative square of locally ringed spaces. -/
lemma stalkMap_comp_eq (hsq : f' ≫ φY = φX ≫ f) (x' : X') :
    (f'.stalkMap x').hom.comp (φY.stalkMap (f'.base x')).hom =
      (φX.stalkMap x').hom.comp (algStalkMap f f' φX φY hsq x') := by
  have h := LocallyRingedSpace.stalkMap_congr_hom (f' ≫ φY) (φX ≫ f) hsq x'
  rw [LocallyRingedSpace.stalkMap_comp, LocallyRingedSpace.stalkMap_comp] at h
  exact RingHom.ext fun t ↦ congrArg (fun φ ↦ φ.hom t) h

variable {f f' φX φY}

/-- XII.3.1 (i), pointwise: in a commutative square of locally ringed spaces whose horizontal maps
`φX`, `φY` are comparison morphisms (for instance the canonical morphisms `X^an → X`,
`Y^an → Y`), `f` is flat at `φX(x')` iff `f'` is flat at `x'`. -/
theorem flat_stalkMap_iff (hsq : f' ≫ φY = φX ≫ f) (hX : IsComparison φX) (hY : IsComparison φY)
    (x' : X') : (f.stalkMap (φX.base x')).hom.Flat ↔ (f'.stalkMap x').hom.Flat := by
  have := hX.isNoetherianRing_stalk x'
  have := hX.isNoetherianRing_stalk_base x'
  have := hY.isNoetherianRing_stalk (f'.base x')
  have := hY.isNoetherianRing_stalk_base (f'.base x')
  have key := flat_iff_flat_of_comparison (algStalkMap f f' φX φY hsq x') _ _ _
    (stalkMap_comp_eq f f' φX φY hsq x') (hY.isComparisonHom _) (hX.isComparisonHom x')
  rwa [algStalkMap, RingHom.Flat.comp_iff_of_bijective_right
    (bijective_stalkSpecializesOfSquare f f' φX φY hsq x')] at key

lemma map_maximalIdeal_algStalkMap (hsq : f' ≫ φY = φX ≫ f) (x' : X') :
    (maximalIdeal _).map (algStalkMap f f' φX φY hsq x') =
      (maximalIdeal _).map (f.stalkMap (φX.base x')).hom := by
  have hs := bijective_stalkSpecializesOfSquare f f' φX φY hsq x'
  rw [algStalkMap, ← Ideal.map_map, map_maximalIdeal_of_surjective _ hs.2]

/-- XII.3.1 (ii), pointwise: in a commutative square of locally ringed spaces whose horizontal
maps are comparison morphisms, `f` is unramified at `φX(x')` in the sense
`𝔪_{f(φX x')} 𝒪_{φX x'} = 𝔪_{φX x'}` iff `f'` is unramified at `x'` in the same sense. -/
theorem map_maximalIdeal_stalkMap_eq_iff (hsq : f' ≫ φY = φX ≫ f) (hX : IsComparison φX)
    (hY : IsComparison φY) (x' : X') :
    (maximalIdeal _).map (f.stalkMap (φX.base x')).hom = maximalIdeal _ ↔
      (maximalIdeal _).map (f'.stalkMap x').hom = maximalIdeal _ := by
  rw [← map_maximalIdeal_algStalkMap hsq x']
  exact map_maximalIdeal_eq_iff_of_comparison (algStalkMap f f' φX φY hsq x') _ _ _
    (stalkMap_comp_eq f f' φX φY hsq x') (hY.isComparisonHom _) (hX.isComparisonHom x')

/-- XII.3.1 (iv), pointwise: in a commutative square of locally ringed spaces whose horizontal
maps are comparison morphisms, the closed fibre `𝒪_{X, φX x'}/𝔪_{f(φX x')}𝒪_{X, φX x'}` of `f` is
regular iff the closed fibre `𝒪_{X', x'}/𝔪_{f'(x')}𝒪_{X', x'}` of `f'` is. -/
theorem isRegularLocalRing_fibre_iff (hsq : f' ≫ φY = φX ≫ f) (hX : IsComparison φX)
    (hY : IsComparison φY) (x' : X') :
    IsRegularLocalRing (X.presheaf.stalk (φX.base x') ⧸
        (maximalIdeal _).map (f.stalkMap (φX.base x')).hom) ↔
      IsRegularLocalRing (X'.presheaf.stalk x' ⧸ (maximalIdeal _).map (f'.stalkMap x').hom) := by
  have := hX.isNoetherianRing_stalk x'
  have := hX.isNoetherianRing_stalk_base x'
  have e := Ideal.quotEquivOfEq (map_maximalIdeal_algStalkMap hsq x')
  rw [← isRegularLocalRing_fibre_iff_of_comparison (algStalkMap f f' φX φY hsq x') _ _ _
    (stalkMap_comp_eq f f' φX φY hsq x') (hY.isComparisonHom _) (hX.isComparisonHom x')]
  exact ⟨fun _ ↦ IsRegularLocalRing.of_ringEquiv e.symm,
    fun _ ↦ IsRegularLocalRing.of_ringEquiv e⟩

end LocallyRingedSpaceComparison

/-! ### The canonical morphism `φ : X^an → X` is a comparison morphism (XII.2.1) -/

namespace AffineAnalytification

open CategoryTheory AlgebraicGeometry AnalyticGeometry LocallyRingedSpaceComparison

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n k : ℕ}
  (g : Fin k → MvPolynomial (Fin n) 𝕜)

/-- XII.2.1: the map `𝒪_{X, φ(x)} → 𝒪_{X^an, x}` induces an isomorphism of residue fields (both
are `𝕜`). -/
lemma bijective_residueFieldMap_stalkComparison (x : (polynomialModel g).zeroSet) :
    Function.Bijective (ResidueField.map (stalkComparison g x)) := by
  refine ⟨(ResidueField.map (stalkComparison g x)).injective, fun r ↦ ?_⟩
  obtain ⟨t, rfl⟩ := residue_surjective r
  obtain ⟨a', ha'⟩ := (jetComparison g x 1).2 (Ideal.Quotient.mk _ t)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, pow_one] at ha'
  refine ⟨residue _ (algebraMap (PresentedAlgebra g) (algStalk g x) a), ?_⟩
  rw [ResidueField.map_residue, ← RingHom.comp_apply (stalkComparison g x),
    stalkComparison_comp_algebraMap]
  exact Ideal.Quotient.eq.mpr ha'

/-- XII.2.1: `φ : Spec(A)^an → Spec A` is a comparison morphism: its stalk maps are flat, local,
with `𝔪_{φ(x)} 𝒪_{X^an, x} = 𝔪_x` and trivial residue field extension, between noetherian local
rings. -/
theorem isComparison_toSpec : IsComparison (toSpec g) where
  isNoetherianRing_stalk x := isNoetherianRing_stalk g x
  isNoetherianRing_stalk_base x := inferInstanceAs (IsNoetherianRing (algStalk g x))
  isComparisonHom x :=
    have : IsLocalHom ((toSpec g).stalkMap x).hom := (toSpec g).prop x
    ⟨flat_stalkMap_toSpec g x, map_maximalIdeal_stalkComparison g x,
      bijective_residueFieldMap_stalkComparison g x⟩

variable (𝕜) (A : Type) [CommRing A] [Algebra 𝕜 A] [Algebra.FinitePresentation 𝕜 A]

/-- XII.2.1: the canonical morphism `φ : X^an → X` of an affine scheme `X = Spec A` of finite
presentation over `𝕜` is a comparison morphism. -/
theorem isComparison_affineToSpec : IsComparison (affineToSpec 𝕜 A) := by
  have : IsIso (Spec.locallyRingedSpaceMap
      (CommRingCat.ofHom (presentationEquiv 𝕜 A).symm.toRingHom)) := by
    let e := (presentationEquiv 𝕜 A).toRingEquiv.toCommRingCatIso
    have h₁ : CommRingCat.ofHom (presentationEquiv 𝕜 A).symm.toRingHom = e.inv := rfl
    have : IsIso (Spec.toLocallyRingedSpace.map e.inv.op) := inferInstance
    rw [h₁]
    exact this
  exact (isComparison_toSpec _).comp_isOpenImmersion _

end AffineAnalytification

end SGA.SGA1.ExposeXII
