/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.RingTheory.Invariant.Galois

/-!
# SGA 1, Exposé V, §1: quotient of a prescheme by a finite group

A family of endomorphisms `T g` of a scheme `X` has a quotient `p : X ⟶ Y` when every
`T`-invariant morphism out of `X` factors uniquely through `p` (`IsQuotient`); a quotient is
unique up to unique isomorphism (`IsQuotient.uniqueIso`).

* `isQuotient_of_isClosedMap`: `p` is a quotient as soon as it is invariant, surjective and
  closed, its fibres are orbits, and `Y` has a basis of opens `U` with `Γ(Y, U) = Γ(X, p⁻¹ U)^G`.
  The morphism out of `Y` is glued from its restrictions to these opens.
* V.1.1 for `Spec A ⟶ Spec A^G`: integral, surjective, fibres are orbits, quotient topology,
  and (iv) it is a quotient in the category of all schemes (`isQuotient_specMap`). The
  residue field statements (iii) are in mathlib.
* V.1.2: `𝒪_Y = p_*(𝒪_X)^G` for `Spec A ⟶ Spec A^G` (`sectionsAreInvariant_specMap`), from the
  formula `(S⁻¹A)^G = S⁻¹(A^G)` (`injective_and_invariants_of_away`).
* V.1.3 in full generality: for a right action of a finite group and an invariant affine `p`
  with `𝒪_Y = p_*(𝒪_X)^G`, `p` is integral, surjective, its fibres are the orbits, and it is a
  quotient (`isQuotient_of_sectionsAreInvariant`). The surjectivity in (iii) of the map from the
  decomposition group to `Aut(κ(x)/κ(y))` for non-affine `X` is
  `exists_fromSpecResidueField_comp_eq` (`InertiaGroups.lean`), and the normality of `κ(x)/κ(y)`
  is `normal_residueFieldMap` (`QuotientResidueField.lean`; affine case: `normal_residueField`).
-/

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped Pointwise
open Opposite

namespace SGA.SGA1.ExposeV

section Quotient

variable {G : Type*} {X Y Z : Scheme.{u}}

/-- V.1: `(Y, p)` is a quotient of `X` by the endomorphisms `T g`: `p` is invariant and every
invariant morphism `f : X ⟶ Z` factors uniquely as `p ≫ h`. SGA lets a finite group act on
the right; here `T` is any family of endomorphisms, which is all the definition uses. -/
structure IsQuotient (T : G → (X ⟶ X)) (p : X ⟶ Y) : Prop where
  comp_eq : ∀ g, T g ≫ p = p
  existsUnique : ∀ {Z : Scheme.{u}} (f : X ⟶ Z), (∀ g, T g ≫ f = f) → ∃! h : Y ⟶ Z, p ≫ h = f

namespace IsQuotient

variable {T : G → (X ⟶ X)} {p : X ⟶ Y}

lemma hom_ext (hp : IsQuotient T p) {h₁ h₂ : Y ⟶ Z} (e : p ≫ h₁ = p ≫ h₂) : h₁ = h₂ := by
  have hf : ∀ g, T g ≫ p ≫ h₁ = p ≫ h₁ := fun g ↦ by rw [← Category.assoc, hp.comp_eq]
  exact (hp.existsUnique _ hf).unique rfl e.symm

/-- The factorization of an invariant morphism through the quotient. -/
noncomputable def desc (hp : IsQuotient T p) (f : X ⟶ Z) (hf : ∀ g, T g ≫ f = f) : Y ⟶ Z :=
  (hp.existsUnique f hf).exists.choose

@[reassoc (attr := simp)]
lemma fac (hp : IsQuotient T p) (f : X ⟶ Z) (hf : ∀ g, T g ≫ f = f) : p ≫ hp.desc f hf = f :=
  (hp.existsUnique f hf).exists.choose_spec

/-- V.1: a quotient is determined up to unique isomorphism. -/
noncomputable def uniqueIso {Y' : Scheme.{u}} {p' : X ⟶ Y'} (hp : IsQuotient T p)
    (hp' : IsQuotient T p') : Y ≅ Y' where
  hom := hp.desc p' hp'.comp_eq
  inv := hp'.desc p hp.comp_eq
  hom_inv_id := hp.hom_ext (by simp)
  inv_hom_id := hp'.hom_ext (by simp)

@[reassoc (attr := simp)]
lemma comp_uniqueIso_hom {Y' : Scheme.{u}} {p' : X ⟶ Y'} (hp : IsQuotient T p)
    (hp' : IsQuotient T p') : p ≫ (hp.uniqueIso hp').hom = p' :=
  hp.fac p' hp'.comp_eq

/-- A quotient composed with an isomorphism is a quotient. -/
lemma comp_iso (hp : IsQuotient T p) {Y' : Scheme.{u}} (e : Y ≅ Y') :
    IsQuotient T (p ≫ e.hom) := by
  refine ⟨fun g ↦ by rw [← Category.assoc, hp.comp_eq], fun f hf ↦ ?_⟩
  refine ⟨e.inv ≫ hp.desc f hf, by simp, fun h hh ↦ ?_⟩
  rw [Iso.eq_inv_comp]
  exact hp.hom_ext (by rw [hp.fac, ← Category.assoc, hh])

/-- A quotient transported along an equivariant isomorphism `X' ≅ X` is a quotient. -/
lemma iso_comp (hp : IsQuotient T p) {X' : Scheme.{u}} {T' : G → (X' ⟶ X')} (e : X' ≅ X)
    (he : ∀ g, T' g ≫ e.hom = e.hom ≫ T g) : IsQuotient T' (e.hom ≫ p) := by
  have hT : ∀ g, T g = e.inv ≫ T' g ≫ e.hom := fun g ↦ by rw [he, Iso.inv_hom_id_assoc]
  refine ⟨fun g ↦ by rw [reassoc_of% (he g), hp.comp_eq], fun f hf ↦ ?_⟩
  have hf' : ∀ g, T g ≫ e.inv ≫ f = e.inv ≫ f := fun g ↦ by simp [hT, hf]
  refine ⟨hp.desc _ hf', by simp, fun h hh ↦ hp.hom_ext ?_⟩
  rw [hp.fac, ← hh]
  simp

end IsQuotient

lemma preimage_le_preimage_of_comp_eq {t : X ⟶ X} {p : X ⟶ Y} (h : t ≫ p = p) (U : Y.Opens) :
    p ⁻¹ᵁ U ≤ t ⁻¹ᵁ p ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, h]

/-- `Γ(Y, U) → Γ(X, p⁻¹ U)` is injective with image the `T`-invariant sections: the condition
`𝒪_Y ≅ p_*(𝒪_X)^G` of V.1.3 over the open `U`. -/
def SectionsAreInvariant (T : G → (X ⟶ X)) (p : X ⟶ Y) (hT : ∀ g, T g ≫ p = p)
    (U : Y.Opens) : Prop :=
  Function.Injective (p.app U) ∧ ∀ s : Γ(X, p ⁻¹ᵁ U),
    (∀ g, (T g).appLE (p ⁻¹ᵁ U) (p ⁻¹ᵁ U) (preimage_le_preimage_of_comp_eq (hT g) U) s = s) →
      ∃ t, p.app U t = s

lemma appLE_res_eq {T : G → (X ⟶ X)} {p : X ⟶ Y} {hTp : ∀ g, T g ≫ p = p} {U V : Y.Opens}
    (h : V ≤ U) (g : G) (s : Γ(X, p ⁻¹ᵁ U)) :
    (T g).appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) (preimage_le_preimage_of_comp_eq (hTp g) V)
      (X.presheaf.map (homOfLE (p.preimage_mono h)).op s) =
    X.presheaf.map (homOfLE (p.preimage_mono h)).op
      ((T g).appLE (p ⁻¹ᵁ U) (p ⁻¹ᵁ U) (preimage_le_preimage_of_comp_eq (hTp g) U) s) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

lemma res_res {U V W : Z.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (t : Γ(Z, U)) :
    Z.presheaf.map (homOfLE h₂).op (Z.presheaf.map (homOfLE h₁).op t) =
      Z.presheaf.map (homOfLE (h₂.trans h₁)).op t := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma app_res_eq {p : X ⟶ Y} {U V : Y.Opens} (h : V ≤ U) (t : Γ(Y, U)) :
    p.app V (Y.presheaf.map (homOfLE h).op t) =
      X.presheaf.map (homOfLE (p.preimage_mono h)).op (p.app U t) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, p.naturality]
  rfl

/-- `SectionsAreInvariant` holds on every open once it holds on a basis (sheaf property). -/
theorem sectionsAreInvariant_of_basis {T : G → (X ⟶ X)} {p : X ⟶ Y} {hTp : ∀ g, T g ≫ p = p}
    (hbasis : ∀ (y : Y) (N : Y.Opens), y ∈ N → ∃ U ≤ N, y ∈ U ∧ SectionsAreInvariant T p hTp U)
    (W : Y.Opens) : SectionsAreInvariant T p hTp W := by
  have hinj : ∀ W : Y.Opens, Function.Injective (p.app W) := by
    intro W t t' htt'
    refine Y.IsSheaf.section_ext fun y hy ↦ ?_
    obtain ⟨V, hVW, hyV, hV⟩ := hbasis y W hy
    refine ⟨V, hVW, hyV, hV.1 ?_⟩
    rw [app_res_eq, app_res_eq, htt']
  refine ⟨hinj W, fun s hs ↦ ?_⟩
  choose U hUW hyU hU using fun y : W ↦ hbasis y.1 W y.2
  have ht : ∀ y : W, ∃ t : Γ(Y, U y), p.app (U y) t =
      X.presheaf.map (homOfLE (p.preimage_mono (hUW y))).op s := fun y ↦
    (hU y).2 _ fun g ↦ by rw [appLE_res_eq (hTp := hTp) (hUW y), hs g]
  choose t ht using ht
  have hcompat : TopCat.Presheaf.IsCompatible Y.sheaf.1 U t := by
    intro y z
    refine Y.IsSheaf.section_ext fun w hw ↦ ?_
    obtain ⟨V, hV, hwV, hVg⟩ := hbasis w (U y ⊓ U z) hw
    refine ⟨V, hV, hwV, hVg.1 ?_⟩
    change p.app V (Y.presheaf.map (homOfLE hV).op (Y.presheaf.map (homOfLE inf_le_left).op
      (t y))) = p.app V (Y.presheaf.map (homOfLE hV).op (Y.presheaf.map
        (homOfLE inf_le_right).op (t z)))
    rw [res_res, res_res, app_res_eq, app_res_eq, ht, ht, res_res, res_res]
  obtain ⟨t₀, ht₀, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf U W (fun y ↦ homOfLE (hUW y))
    (fun y hy ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyU ⟨y, hy⟩⟩) t hcompat
  refine ⟨t₀, X.IsSheaf.section_ext fun x hx ↦ ?_⟩
  have hx' : p x ∈ W := hx
  refine ⟨p ⁻¹ᵁ U ⟨p x, hx'⟩, p.preimage_mono (hUW _), hyU ⟨p x, hx'⟩, ?_⟩
  exact (app_res_eq (hUW _) t₀).symm.trans ((congr_arg (p.app _) (ht₀ ⟨p x, hx'⟩)).trans (ht _))

lemma appLE_congr_hom {a b : X ⟶ Z} (hab : a = b) (V : Z.Opens) (W : X.Opens) (e e') :
    a.appLE V W e = b.appLE V W e' := by
  subst hab; rfl

/-- An invariant morphism restricted to `p⁻¹ U` factors through `U` when `U` satisfies
`SectionsAreInvariant` and `f(p⁻¹ U)` lies in an affine open. -/
lemma exists_comp_eq_of_sectionsAreInvariant {T : G → (X ⟶ X)} {p : X ⟶ Y}
    {hT : ∀ g, T g ≫ p = p} {U : Y.Opens} (hU : SectionsAreInvariant T p hT U)
    (f : X ⟶ Z) (hf : ∀ g, T g ≫ f = f) {V : Z.Opens} (hV : IsAffineOpen V)
    (hUV : p ⁻¹ᵁ U ≤ f ⁻¹ᵁ V) : ∃ h : U.toScheme ⟶ Z, p ∣_ U ≫ h = (p ⁻¹ᵁ U).ι ≫ f := by
  let ψ := f.appLE V (p ⁻¹ᵁ U) hUV
  have hψ : ∀ s, ψ s ∈ (p.app U).hom.range := by
    intro s
    obtain ⟨t, ht⟩ := hU.2 (ψ s) fun g ↦ by
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
      exact congr($(appLE_congr_hom (hf g) V (p ⁻¹ᵁ U) _ hUV) s)
    exact ⟨t, ht⟩
  let e := RingEquiv.ofBijective (p.app U).hom.rangeRestrict
    ⟨fun a b hab ↦ hU.1 (congr_arg Subtype.val hab), (p.app U).hom.rangeRestrict_surjective⟩
  let χ : Γ(Z, V) ⟶ Γ(Y, U) := CommRingCat.ofHom
    (e.symm.toRingHom.comp (ψ.hom.codRestrict _ hψ))
  have hχ : χ ≫ p.app U = ψ := by
    ext s
    exact congr_arg Subtype.val (e.apply_symm_apply ⟨ψ s, hψ s⟩)
  refine ⟨U.toSpecΓ ≫ Spec.map χ ≫ hV.fromSpec, ?_⟩
  rw [← Scheme.Opens.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, hχ,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec,
    Scheme.Hom.resLE_comp_ι]

lemma injective_appTop_morphismRestrict {p : X ⟶ Y} {U : Y.Opens}
    (h : Function.Injective (p.app U)) : Function.Injective (p ∣_ U).appTop := by
  rw [morphismRestrict_appTop]
  have key : ∀ U' : Y.Opens, U' = U → Function.Injective (p.app U') := by
    rintro _ rfl; exact h
  have hiso : Function.Injective (X.presheaf.map
      (eqToHom (image_morphismRestrict_preimage p U ⊤)).op) :=
    (asIso (X.presheaf.map
      (eqToHom (image_morphismRestrict_preimage p U ⊤)).op)).commRingCatIsoToRingEquiv.injective
  exact hiso.comp (key _ U.ι_image_top)

lemma surjective_morphismRestrict {p : X ⟶ Y} (hp : Function.Surjective p) (U : Y.Opens) :
    Function.Surjective (p ∣_ U) := by
  intro u
  obtain ⟨x, hx⟩ := hp u.1
  exact ⟨⟨x, show p x ∈ U from hx ▸ u.2⟩,
    Subtype.ext ((morphismRestrict_base_coe p U _).trans hx)⟩

/-- Two morphisms `U ⟶ Z` into an affine open agreeing after `p ∣_ U` are equal, when `p` is
surjective and `Γ(Y, U) → Γ(X, p⁻¹ U)` is injective. -/
lemma eq_of_comp_eq_of_injective {p : X ⟶ Y} (hp : Function.Surjective p) {U : Y.Opens}
    (hU : Function.Injective (p.app U)) {V : Z.Opens} (hV : IsAffineOpen V)
    {c₁ c₂ : U.toScheme ⟶ Z} (h : p ∣_ U ≫ c₁ = p ∣_ U ≫ c₂)
    (hV' : ∀ x, (p ∣_ U ≫ c₁) x ∈ V) : c₁ = c₂ := by
  have hmem : ∀ c : U.toScheme ⟶ Z, p ∣_ U ≫ c = p ∣_ U ≫ c₁ →
      Set.range c ⊆ Set.range V.ι := by
    rintro c hc _ ⟨u, rfl⟩
    obtain ⟨x, rfl⟩ := surjective_morphismRestrict hp U u
    rw [Scheme.Opens.range_ι]
    have := hV' x
    rwa [← hc] at this
  have h₁ := IsOpenImmersion.lift_fac V.ι c₁ (hmem c₁ rfl)
  have h₂ := IsOpenImmersion.lift_fac V.ι c₂ (hmem c₂ h.symm)
  have : IsAffine V.toScheme := hV
  rw [← h₁, ← h₂]
  congr 1
  apply ext_of_isAffine
  have hc : p ∣_ U ≫ IsOpenImmersion.lift V.ι c₁ (hmem c₁ rfl) =
      p ∣_ U ≫ IsOpenImmersion.lift V.ι c₂ (hmem c₂ h.symm) := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, h₁, h₂, h]
  ext s
  apply injective_appTop_morphismRestrict hU
  have := congr((Scheme.Hom.appTop $hc) s)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at this
  exact this

lemma hom_ext_of_forall_homOfLE {W : Y.Opens} (a b : W.toScheme ⟶ Z)
    (H : ∀ y ∈ W, ∃ (U : Y.Opens) (h : U ≤ W), y ∈ U ∧ Y.homOfLE h ≫ a = Y.homOfLE h ≫ b) :
    a = b := by
  choose U hUW hyU hU using H
  let 𝒰 : W.toScheme.OpenCover := {
    I₀ := W
    X i := U i.1 i.2
    f i := Y.homOfLE (hUW i.1 i.2)
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun w ↦ ⟨w, ⟨w.1, hyU w.1 w.2⟩, Subtype.ext ?_⟩, inferInstance⟩
      exact Scheme.homOfLE_apply (hUW w.1 w.2) _ }
  exact 𝒰.hom_ext _ _ fun i ↦ hU i.1 i.2

/-- If `p` is closed and its fibres are `T`-orbits, a `T`-invariant `f` maps the preimage of a
neighbourhood of `p x` into any open containing `f x`. -/
lemma exists_open_preimage_le (T : G → (X ⟶ X)) (p : X ⟶ Y)
    (horb : ∀ x x', p x = p x' → ∃ g, T g x = x') (hcl : IsClosedMap p)
    (f : X ⟶ Z) (hf : ∀ g, T g ≫ f = f) (V : Z.Opens) (x : X) (hx : f x ∈ V) :
    ∃ N : Y.Opens, p x ∈ N ∧ p ⁻¹ᵁ N ≤ f ⁻¹ᵁ V := by
  refine ⟨⟨(p '' (f ⁻¹ᵁ V : Set X)ᶜ)ᶜ, (hcl _ (f ⁻¹ᵁ V).isOpen.isClosed_compl).isOpen_compl⟩,
    ?_, ?_⟩
  · rintro ⟨x', hx', hxx'⟩
    obtain ⟨g, rfl⟩ := horb x x' hxx'.symm
    apply hx'
    change f (T g x) ∈ V
    rwa [← Scheme.Hom.comp_apply, hf g]
  · intro x' hx'
    by_contra h
    exact hx' ⟨x', h, rfl⟩

lemma exists_isAffineOpen_mem (z : Z) : ∃ V : Z.Opens, IsAffineOpen V ∧ z ∈ V := by
  obtain ⟨V, hV, hzV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens)
    (show z ∈ (⊤ : Z.Opens) from trivial)
  exact ⟨V, hV, hzV⟩

/-- V.1.3 (iv), in the form proved in SGA: `p` is a quotient of `X` by `T` if it is invariant,
surjective and closed, its fibres are orbits, and `Y` has a basis of opens `U` with
`Γ(Y, U) = Γ(X, p⁻¹ U)^T`. The morphism out of `Y` is glued from its restrictions to these
opens. -/
theorem isQuotient_of_isClosedMap (T : G → (X ⟶ X)) (p : X ⟶ Y) (hT : ∀ g, T g ≫ p = p)
    (hsurj : Function.Surjective p) (horb : ∀ x x', p x = p x' → ∃ g, T g x = x')
    (hcl : IsClosedMap p)
    (hbasis : ∀ (y : Y) (N : Y.Opens), y ∈ N →
      ∃ U ≤ N, y ∈ U ∧ SectionsAreInvariant T p hT U) :
    IsQuotient T p := by
  refine ⟨hT, fun {Z} f hf ↦ ?_⟩
  have key : ∀ (y : Y) (N : Y.Opens), y ∈ N → ∃ (U : Y.Opens) (V : Z.Opens), U ≤ N ∧ y ∈ U ∧
      SectionsAreInvariant T p hT U ∧ IsAffineOpen V ∧ p ⁻¹ᵁ U ≤ f ⁻¹ᵁ V := by
    intro y N hyN
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨V, hV, hxV⟩ := exists_isAffineOpen_mem (f x)
    obtain ⟨N', hxN', hN'⟩ := exists_open_preimage_le T p horb hcl f hf V x hxV
    obtain ⟨U, hUN, hxU, hU⟩ := hbasis _ (N ⊓ N') ⟨hyN, hxN'⟩
    exact ⟨U, V, hUN.trans inf_le_left, hxU, hU, hV,
      (Scheme.Hom.preimage_mono p (hUN.trans inf_le_right)).trans hN'⟩
  -- Two local factorizations of `f` over the same open agree.
  have locally_eq : ∀ (W : Y.Opens) (a b : W.toScheme ⟶ Z), p ∣_ W ≫ a = (p ⁻¹ᵁ W).ι ≫ f →
      p ∣_ W ≫ b = (p ⁻¹ᵁ W).ι ≫ f → a = b := by
    intro W a b ha hb
    refine hom_ext_of_forall_homOfLE a b fun y hy ↦ ?_
    obtain ⟨U, V, hUW, hyU, hU, hV, hUV⟩ := key y W hy
    refine ⟨U, hUW, hyU, ?_⟩
    have hc : ∀ c : W.toScheme ⟶ Z, p ∣_ W ≫ c = (p ⁻¹ᵁ W).ι ≫ f →
        p ∣_ U ≫ Y.homOfLE hUW ≫ c = (p ⁻¹ᵁ U).ι ≫ f := by
      intro c hc
      rw [morphismRestrict_homOfLE_assoc, hc, Scheme.homOfLE_ι_assoc]
    refine eq_of_comp_eq_of_injective hsurj hU.1 hV ((hc a ha).trans (hc b hb).symm) ?_
    intro x
    rw [hc a ha]
    exact hUV x.2
  have uniq : ∀ h₁ h₂ : Y ⟶ Z, p ≫ h₁ = f → p ≫ h₂ = f → h₁ = h₂ := by
    intro h₁ h₂ e₁ e₂
    refine Scheme.hom_ext_of_forall h₁ h₂ fun y ↦ ⟨⊤, trivial, locally_eq ⊤ _ _ ?_ ?_⟩
    · rw [morphismRestrict_ι_assoc, e₁]
    · rw [morphismRestrict_ι_assoc, e₂]
  -- Existence: glue the local factorizations.
  choose U V _ hyU hU hV hUV using fun y : Y ↦ key y ⊤ trivial
  have hcov : TopologicalSpace.IsOpenCover U :=
    eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
  choose c hc using fun y ↦ exists_comp_eq_of_sectionsAreInvariant (hU y) f hf (hV y) (hUV y)
  let 𝒰 := Y.openCoverOfIsOpenCover U hcov
  have compat : ∀ i j : 𝒰.I₀, pullback.fst (𝒰.f i) (𝒰.f j) ≫ c i =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ c j := fun (i j : Y) ↦ by
    change pullback.fst (U i).ι (U j).ι ≫ c i = pullback.snd (U i).ι (U j).ι ≫ c j
    rw [← cancel_epi (isPullback_opens_inf (U i) (U j)).isoPullback.hom,
      IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
    refine locally_eq _ _ _ ?_ ?_
    · rw [morphismRestrict_homOfLE_assoc, hc, Scheme.homOfLE_ι_assoc]
    · rw [morphismRestrict_homOfLE_assoc, hc, Scheme.homOfLE_ι_assoc]
  refine ⟨𝒰.glueMorphisms c compat, ?_, fun h' e' ↦ uniq h' _ e' ?_⟩ <;>
  · refine Scheme.hom_ext_of_forall _ _ fun x ↦ ⟨p ⁻¹ᵁ U (p x), hyU (p x), ?_⟩
    rw [← morphismRestrict_ι_assoc]
    have h1 : (U (p x)).ι ≫ 𝒰.glueMorphisms c compat = c (p x) :=
      𝒰.ι_glueMorphisms c compat (p x)
    rw [h1, hc]

end Quotient

section Localization

variable {R A R' A' : Type*} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R R'] [Algebra A A'] {G : Type*} [Finite G]

/-- V.1.2, for a basic open `D(r)`: if `R → A` identifies `R` with the invariants of a finite
family of endomorphisms `σ g` of `A`, then `R_r → A_r` identifies `R_r` with the invariants of
the localized endomorphisms. This is the formula `(S⁻¹A)^G = S⁻¹(A^G)` of the proof of V.1.2,
for `S` generated by one element. -/
theorem injective_and_invariants_of_away (φ : R →+* A) (σ : G → A →+* A)
    (hσ : ∀ g r, σ g (φ r) = φ r) (hφ : Function.Injective φ)
    (hinv : ∀ a, (∀ g, σ g a = a) → ∃ r, φ r = a) (r : R)
    [IsLocalization.Away r R'] [IsLocalization.Away (φ r) A']
    (φ' : R' →+* A') (hφ' : ∀ x, φ' (algebraMap R R' x) = algebraMap A A' (φ x))
    (σ' : G → A' →+* A') (hσ' : ∀ g a, σ' g (algebraMap A A' a) = algebraMap A A' (σ g a)) :
    Function.Injective φ' ∧ ∀ a', (∀ g, σ' g a' = a') → ∃ x, φ' x = a' := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj r z
    have h0 : algebraMap A A' (φ x) = algebraMap A A' (φ 0) := by
      rw [← hφ', ← hx, map_mul, hz, zero_mul, map_zero, map_zero]
    obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (φ r) h0
    have hrx : r ^ m * x = 0 := hφ (by simpa using hm)
    have hu := (IsLocalization.Away.algebraMap_pow_isUnit (S := R') r m).mul
      (IsLocalization.Away.algebraMap_pow_isUnit (S := R') r n)
    have h1 : z * (algebraMap R R' r ^ m * algebraMap R R' r ^ n) = 0 := by
      rw [mul_left_comm, hx, ← map_pow, ← map_mul, hrx, map_zero]
    exact hu.mul_left_eq_zero.mp h1
  · intro a' ha'
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (φ r) a'
    have hk : ∀ g, ∃ k : ℕ, φ r ^ k * σ g a = φ r ^ k * a := by
      intro g
      have : algebraMap A A' (σ g a) = algebraMap A A' a := by
        rw [← hσ', ← ha, map_mul, map_pow, hσ', hσ, ha' g]
      exact IsLocalization.Away.exists_of_eq (φ r) this
    choose k hk using hk
    have : Fintype G := Fintype.ofFinite G
    set K := ∑ g, k g
    have hK : ∀ g, σ g (φ r ^ K * a) = φ r ^ K * a := by
      intro g
      have hle : k g ≤ K := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ g)
      rw [map_mul, map_pow, hσ, ← Nat.sub_add_cancel hle, pow_add, mul_assoc, mul_assoc, hk g]
    obtain ⟨t, ht⟩ := hinv _ hK
    let s : Submonoid.powers r := ⟨r ^ (n + K), pow_mem (Submonoid.mem_powers r) _⟩
    refine ⟨IsLocalization.mk' R' t s, ?_⟩
    have hu := IsLocalization.Away.algebraMap_pow_isUnit (S := A') (φ r) (n + K)
    refine (hu.mul_left_inj).mp ?_
    have h1 : φ' (IsLocalization.mk' R' t s) * algebraMap A A' (φ r) ^ (n + K)
        = algebraMap A A' (φ t) := by
      rw [← hφ', ← map_pow, ← hφ', ← map_mul, ← map_pow, IsLocalization.mk'_spec]
    rw [h1, ht, pow_add, ← mul_assoc, ha, map_mul, map_pow, mul_comm]

end Localization

section ResidueField

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (G : Type*) [Group G] [Finite G]
  [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
  (P : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]
  (K L : Type*) [Field K] [Field L] [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
  [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L] [Algebra (A ⧸ P) L]
  [IsScalarTower (A ⧸ P) (B ⧸ Q) L] [Algebra K L] [IsScalarTower (A ⧸ P) K L]

omit [SMulCommClass G A B] in
include G P Q in
/-- V.1.1 (iii) (mathlib): the residue extension `κ(Q)/κ(P)` is quasi-Galois (normal). Here
`K`, `L` are the fraction fields of `A/P`, `B/Q`, i.e. the residue fields. -/
theorem normal_residueField [P.IsPrime] : Normal K L :=
  Ideal.IsFractionRing.normal G P Q K L

/-- V.1.1 (iii) (mathlib): the stabilizer of `Q` surjects onto `Aut(κ(Q)/κ(P))`. -/
theorem stabilizerHom_surjective :
    Function.Surjective (IsFractionRing.stabilizerHom G P Q K L) :=
  IsFractionRing.stabilizerHom_surjective G P Q K L

end ResidueField

section Spec

lemma SpecMap_appLE_algebraMap {R S : CommRingCat.{u}} (f : R ⟶ S) (U : (Spec R).Opens)
    (V : (Spec S).Opens) (e : V ≤ Spec.map f ⁻¹ᵁ U) (r : R) :
    (Spec.map f).appLE U V e (algebraMap R Γ(Spec R, U) r) = algebraMap S Γ(Spec S, V) (f r) := by
  have h := congr(CommRingCat.Hom.hom $(Scheme.ΓSpecIso_inv_naturality f) r)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  simp only [IsAffineOpen.algebraMap_Spec_obj, CommRingCat.hom_comp, RingHom.comp_apply, h]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE, ← CommRingCat.comp_apply]
  rfl

variable {A B : CommRingCat.{u}} [Algebra B A] (G : Type*) [Group G] [MulSemiringAction G A]

variable (A B) in
/-- The morphism `p : Spec A ⟶ Spec B` induced by `B → A`. -/
noncomputable abbrev specMap : Spec A ⟶ Spec B :=
  Spec.map (CommRingCat.ofHom (algebraMap B A) : B ⟶ A)

variable (A) in
/-- `g ∈ G` acts on `Spec A` by `Spec(g)`; this is a right action, as in SGA. -/
noncomputable abbrev specAction (g : G) : Spec A ⟶ Spec A :=
  Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G A g) : A ⟶ A)

variable {G}

lemma asIdeal_specAction (g : G) (x : Spec A) :
    PrimeSpectrum.asIdeal (R := A) (specAction A G g x) =
      g⁻¹ • PrimeSpectrum.asIdeal (R := A) x := by
  ext a
  change g • a ∈ PrimeSpectrum.asIdeal (R := A) x ↔ _
  rw [Ideal.mem_inv_pointwise_smul_iff]

variable [SMulCommClass G B A]

lemma specAction_comp_specMap (g : G) : specAction A G g ≫ specMap A B = specMap A B := by
  rw [← Spec.map_comp]
  congr 1
  ext b
  exact smul_algebraMap g b

variable [Finite G] [Algebra.IsInvariant B A G]

omit [SMulCommClass G B A] in
variable (G) in
include G in
/-- V.1.1 (ii): `Spec A ⟶ Spec A^G` is surjective. -/
theorem specMap_surjective (hinj : Function.Injective (algebraMap B A)) :
    Function.Surjective (specMap A B) :=
  RingHom.IsIntegral.comap_surjective (Algebra.IsInvariant.isIntegral B A G).1 hinj

/-- V.1.1 (ii): the fibres of `Spec A ⟶ Spec A^G` are the orbits of `G`. -/
theorem specMap_eq_iff (x x' : Spec A) :
    specMap A B x = specMap A B x' ↔ ∃ g, specAction A G g x = x' := by
  constructor
  · intro h
    let P : PrimeSpectrum A := x
    let P' : PrimeSpectrum A := x'
    have : P.asIdeal.under B = P'.asIdeal.under B := congr_arg PrimeSpectrum.asIdeal h
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq B A G P.asIdeal P'.asIdeal this
    refine ⟨g⁻¹, PrimeSpectrum.ext ?_⟩
    rw [asIdeal_specAction, inv_inv]
    exact hg.symm
  · rintro ⟨g, rfl⟩
    rw [← Scheme.Hom.comp_apply, specAction_comp_specMap]

omit [SMulCommClass G B A] in
variable (G) in
include G in
/-- V.1.1 (ii): `Spec A ⟶ Spec A^G` is closed (it is integral). -/
theorem isClosedMap_specMap : IsClosedMap (specMap A B) :=
  PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (Algebra.IsInvariant.isIntegral B A G).1

set_option backward.isDefEq.respectTransparency.types false in
/-- V.1.2 on the basic open `D(b)`: `Γ(Spec A^G, D(b)) = Γ(Spec A, D(b))^G`. -/
theorem sectionsAreInvariant_basicOpen (hinj : Function.Injective (algebraMap B A)) (b : B) :
    SectionsAreInvariant (specAction A G) (specMap A B) specAction_comp_specMap
      (PrimeSpectrum.basicOpen b) := by
  have : IsLocalization.Away (algebraMap B A b)
      Γ(Spec A, specMap A B ⁻¹ᵁ (PrimeSpectrum.basicOpen b)) :=
    inferInstanceAs (IsLocalization.Away (algebraMap B A b)
      Γ(Spec A, PrimeSpectrum.basicOpen (algebraMap B A b)))
  refine injective_and_invariants_of_away (G := G) (algebraMap B A)
    (fun g ↦ MulSemiringAction.toRingHom G A g) (fun g b ↦ smul_algebraMap g b) hinj
    (fun a ha ↦ Algebra.IsInvariant.isInvariant a ha) b _ ?_ _ ?_
  · intro x
    rw [Scheme.Hom.app_eq_appLE]
    exact SpecMap_appLE_algebraMap _ _ _ _ x
  · intro g a
    exact SpecMap_appLE_algebraMap _ _ _ _ a

/-- V.1.2: `𝒪_Y → p_*(𝒪_X)^G` is an isomorphism for `p : Spec A ⟶ Spec A^G`: over every open
`W`, `Γ(Spec A^G, W) = Γ(Spec A, p⁻¹ W)^G`. -/
theorem sectionsAreInvariant_specMap (hinj : Function.Injective (algebraMap B A))
    (W : (Spec B).Opens) :
    SectionsAreInvariant (specAction A G) (specMap A B) specAction_comp_specMap W := by
  refine sectionsAreInvariant_of_basis (fun y N hyN ↦ ?_) W
  obtain ⟨_, ⟨b, rfl⟩, hyb, hbN⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hyN N.isOpen
  exact ⟨PrimeSpectrum.basicOpen b, hbN, hyb, sectionsAreInvariant_basicOpen hinj b⟩

/-- V.1.1 (iv): `Spec A^G` is the quotient of `Spec A` by `G` in the category of schemes. -/
theorem isQuotient_specMap (hinj : Function.Injective (algebraMap B A)) :
    IsQuotient (specAction A G) (specMap A B) := by
  refine isQuotient_of_isClosedMap _ _ specAction_comp_specMap (specMap_surjective G hinj)
    (fun x x' h ↦ (specMap_eq_iff x x').mp h) (isClosedMap_specMap G) ?_
  intro y N hyN
  obtain ⟨_, ⟨b, rfl⟩, hyb, hbN⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hyN N.isOpen
  exact ⟨PrimeSpectrum.basicOpen b, hbN, hyb, sectionsAreInvariant_basicOpen hinj b⟩

omit [SMulCommClass G B A] in
variable (G) in
include G in
/-- V.1.1 (i): `A` is integral over `A^G`, i.e. `Spec A ⟶ Spec A^G` is an integral morphism. -/
theorem isIntegralHom_specMap : IsIntegralHom (specMap A B) :=
  IsIntegralHom.SpecMap_iff.mpr (Algebra.IsInvariant.isIntegral B A G).1

omit [SMulCommClass G B A] in
variable (G) in
include G in
/-- V.1.1 (ii): the topology of `Spec A^G` is the quotient topology of `Spec A`. -/
theorem isQuotientMap_specMap (hinj : Function.Injective (algebraMap B A)) :
    Topology.IsQuotientMap (specMap A B) :=
  (isClosedMap_specMap G).isQuotientMap (specMap A B).continuous (specMap_surjective G hinj)

end Spec

section RightAction

variable {G : Type*} [Group G] {X Y : Scheme.{u}}

/-- `G` acting on the right on `X` through `T`, as in SGA: `T 1 = 𝟙` and `T (g * h) = T g ≫ T h`. -/
structure IsRightAction (T : G → (X ⟶ X)) : Prop where
  map_one : T 1 = 𝟙 X
  map_mul : ∀ g h, T (g * h) = T g ≫ T h

/-- The action of `G` on the sections over a `T`-stable open `W`: `g • s = (T g)^* s`. -/
@[reducible]
noncomputable def sectionsAction {T : G → (X ⟶ X)} (hT : IsRightAction T) (W : X.Opens)
    (hW : ∀ g, W ≤ T g ⁻¹ᵁ W) : MulSemiringAction G Γ(X, W) where
  smul g s := (T g).appLE W W (hW g) s
  one_smul s := by
    change (T 1).appLE W W (hW 1) s = s
    rw [appLE_congr_hom hT.map_one W W (hW 1) le_rfl]
    change (X.presheaf.map (homOfLE (le_refl W)).op) s = s
    rw [show homOfLE (le_refl W) = 𝟙 W from rfl, op_id, X.presheaf.map_id]
    rfl
  mul_smul g h s := by
    change (T (g * h)).appLE W W (hW _) s = (T g).appLE W W (hW g) ((T h).appLE W W (hW h) s)
    rw [appLE_congr_hom (hT.map_mul g h) W W (hW _)
        ((hW g).trans (Scheme.Hom.preimage_mono _ (hW h))),
      ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  smul_zero g := map_zero ((T g).appLE W W (hW g)).hom
  smul_add g := map_add ((T g).appLE W W (hW g)).hom
  smul_one g := map_one ((T g).appLE W W (hW g)).hom
  smul_mul g := map_mul ((T g).appLE W W (hW g)).hom

variable [Finite G] {T : G → (X ⟶ X)} (hT : IsRightAction T) {p : X ⟶ Y}
  {hTp : ∀ g, T g ≫ p = p}

include hT in
/-- V.1.3 (i): under the hypotheses of V.1.3, `p` is integral. -/
theorem isIntegralHom_of_sectionsAreInvariant [IsAffineHom p]
    (hsec : ∀ U, IsAffineOpen U → SectionsAreInvariant T p hTp U) : IsIntegralHom p where
  isIntegral_app U hU := by
    let := (p.app U).hom.toAlgebra
    let := sectionsAction hT (p ⁻¹ᵁ U) (fun g ↦ preimage_le_preimage_of_comp_eq (hTp g) U)
    have : Algebra.IsInvariant Γ(Y, U) Γ(X, p ⁻¹ᵁ U) G := ⟨fun s hs ↦ (hsec U hU).2 s hs⟩
    exact (Algebra.IsInvariant.isIntegral Γ(Y, U) Γ(X, p ⁻¹ᵁ U) G).1

include hT in
/-- V.1.3 (ii): under the hypotheses of V.1.3, `p` is surjective and its fibres are the orbits
of `G`. -/
theorem surjective_and_orbit_of_sectionsAreInvariant [IsAffineHom p]
    (hsec : ∀ U, IsAffineOpen U → SectionsAreInvariant T p hTp U) :
    Function.Surjective p ∧ ∀ x x', p x = p x' → ∃ g, T g x = x' := by
  have key : ∀ (U : Y.Opens), IsAffineOpen U → (Function.Surjective (p ∣_ U) ∧
      ∀ w w' : (p ⁻¹ᵁ U).toScheme, (p ∣_ U) w = (p ∣_ U) w' →
        ∃ g, (T g).resLE (p ⁻¹ᵁ U) (p ⁻¹ᵁ U)
          (preimage_le_preimage_of_comp_eq (hTp g) U) w = w') := by
    intro U hU
    have hW : IsAffineOpen (p ⁻¹ᵁ U) := hU.preimage p
    let := (p.app U).hom.toAlgebra
    let := sectionsAction hT (p ⁻¹ᵁ U) (fun g ↦ preimage_le_preimage_of_comp_eq (hTp g) U)
    have : Algebra.IsInvariant Γ(Y, U) Γ(X, p ⁻¹ᵁ U) G := ⟨fun s hs ↦ (hsec U hU).2 s hs⟩
    have : SMulCommClass G Γ(Y, U) Γ(X, p ⁻¹ᵁ U) := ⟨fun g r s ↦ by
      change (T g).appLE _ _ _ (p.app U r * s) = p.app U r * (T g).appLE _ _ _ s
      rw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (hTp g) _ _ _ le_rfl]⟩
    have hsq : (p ⁻¹ᵁ U).toSpecΓ ≫ specMap Γ(X, p ⁻¹ᵁ U) Γ(Y, U) = p ∣_ U ≫ U.toSpecΓ :=
      Scheme.Opens.toSpecΓ_naturality p U
    have hsqT : ∀ g, (p ⁻¹ᵁ U).toSpecΓ ≫ specAction Γ(X, p ⁻¹ᵁ U) G g =
        (T g).resLE _ _ (preimage_le_preimage_of_comp_eq (hTp g) U) ≫ (p ⁻¹ᵁ U).toSpecΓ :=
      fun g ↦ Scheme.Opens.toSpecΓ_SpecMap_appLE _ _ _ _
    have : IsIso U.toSpecΓ := inferInstanceAs (IsIso hU.isoSpec.hom)
    have : IsIso (p ⁻¹ᵁ U).toSpecΓ := inferInstanceAs (IsIso hW.isoSpec.hom)
    have hinjU : Function.Injective U.toSpecΓ := U.toSpecΓ.isOpenEmbedding.injective
    have hinjW : Function.Injective (p ⁻¹ᵁ U).toSpecΓ :=
      (p ⁻¹ᵁ U).toSpecΓ.isOpenEmbedding.injective
    refine ⟨fun u ↦ ?_, fun w w' h ↦ ?_⟩
    · obtain ⟨P, hP⟩ := specMap_surjective (A := Γ(X, p ⁻¹ᵁ U)) (B := Γ(Y, U)) G (hsec U hU).1
        (U.toSpecΓ u)
      obtain ⟨w, rfl⟩ := (p ⁻¹ᵁ U).toSpecΓ.surjective P
      refine ⟨w, hinjU ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply, hP]
    · have h' : specMap Γ(X, p ⁻¹ᵁ U) Γ(Y, U) ((p ⁻¹ᵁ U).toSpecΓ w) =
          specMap Γ(X, p ⁻¹ᵁ U) Γ(Y, U) ((p ⁻¹ᵁ U).toSpecΓ w') := by
        rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply, h, ← Scheme.Hom.comp_apply,
          ← hsq, Scheme.Hom.comp_apply]
      obtain ⟨g, hg⟩ := (specMap_eq_iff (G := G) _ _).mp h'
      refine ⟨g, hinjW ?_⟩
      rw [← hg, ← Scheme.Hom.comp_apply, ← hsqT, Scheme.Hom.comp_apply]
  refine ⟨fun y ↦ ?_, fun x x' hxx' ↦ ?_⟩
  · obtain ⟨U, hU, hyU⟩ := exists_isAffineOpen_mem y
    obtain ⟨w, hw⟩ := (key U hU).1 ⟨y, hyU⟩
    exact ⟨w.1, (morphismRestrict_base_coe p U w).symm.trans (congr_arg Subtype.val hw)⟩
  · obtain ⟨U, hU, hxU⟩ := exists_isAffineOpen_mem (p x)
    have hx'U : p x' ∈ U := hxx' ▸ hxU
    let w : (p ⁻¹ᵁ U).toScheme := ⟨x, show x ∈ p ⁻¹ᵁ U from hxU⟩
    let w' : (p ⁻¹ᵁ U).toScheme := ⟨x', show x' ∈ p ⁻¹ᵁ U from hx'U⟩
    obtain ⟨g, hg⟩ := (key U hU).2 w w' (Subtype.ext ((morphismRestrict_base_coe p U w).trans
        (hxx'.trans (morphismRestrict_base_coe p U w').symm)))
    exact ⟨g, (Scheme.Hom.coe_resLE_apply ..).symm.trans (congr_arg Subtype.val hg)⟩

include hT in
/-- V.1.3 (iv): an invariant affine morphism `p` with `𝒪_Y = p_*(𝒪_X)^G` (on affine opens) is a
quotient of `X` by `G`. -/
theorem isQuotient_of_sectionsAreInvariant [IsAffineHom p]
    (hsec : ∀ U, IsAffineOpen U → SectionsAreInvariant T p hTp U) : IsQuotient T p := by
  have := isIntegralHom_of_sectionsAreInvariant hT hsec
  obtain ⟨hsurj, horb⟩ := surjective_and_orbit_of_sectionsAreInvariant hT hsec
  refine isQuotient_of_isClosedMap T p hTp hsurj horb p.isClosedMap fun y N hyN ↦ ?_
  obtain ⟨U, hU, hyU, hUN⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hyN
  exact ⟨U, hUN, hyU, hsec U hU⟩


omit [Finite G] in
/-- The action of `G` on `Spec A` is a right action. -/
lemma isRightAction_specAction {A : CommRingCat.{u}} [MulSemiringAction G A] :
    IsRightAction (specAction A G) where
  map_one := by
    rw [specAction, ← Spec.map_id]
    congr 1
    ext a
    exact one_smul G a
  map_mul g h := by
    rw [specAction, specAction, specAction, ← Spec.map_comp]
    congr 1
    ext a
    exact mul_smul g h a

end RightAction

end SGA.SGA1.ExposeV
