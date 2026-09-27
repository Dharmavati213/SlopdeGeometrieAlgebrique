/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.SeparatingSections

/-!
# Zariski's connectedness theorem

`AlgebraicGeometry.zariskiConnectednessStatement` (EGA III 4.3.1; Stacks Tag 03H0; Hartshorne
III.11.3): if `f : X ⟶ Y` is proper, `Y` locally noetherian and `𝒪_Y → f_* 𝒪_X` an isomorphism,
then every fibre of `f` is connected and non-empty.

Proof. Non-emptiness: over the open complement of the (closed) image of `f`, `f_* 𝒪_X` is zero
(`CohomologyAux.nonempty_preimage_singleton`). Connectedness is local on `Y`, so let `Y` be affine
and noetherian (`isPreconnected_preimage_singleton_of_isAffine`). If the fibre `f⁻¹(y)` is split by
closed `G₁, G₂`, then over a neighbourhood `V = D(s)` of `y` the closed set
`f⁻¹(cl {y} ∩ V)` is split by `G₁, G₂` as well (`CohomologyAux.not_mem_image_closure`, using the
finitely many irreducible components of the noetherian space `X`). Over `V`, with `I` the prime of
`y`, `CohomologyAux.exists_section_separating'` (the theorem on formal functions) gives a function
on `f⁻¹(V)` which is invertible on `G₁ ∩ f⁻¹(y)` and vanishes on `G₂ ∩ f⁻¹(y)`; it comes from `V`
as `f_* 𝒪_X = 𝒪_Y`, which is absurd since both pieces lie over the same point.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Spreading out from the fibre over a generic point.** Let `f : X → Y` be continuous with `X`
noetherian and quasi-sober and `Y` a `T₀` space, `y ∈ Y` and `T ⊆ X` open, disjoint from the fibre
`f⁻¹(y)`. Then no point of the closure of `T ∩ f⁻¹(cl {y})` lies over `y`. (Its irreducible
components meet `T`, and their generic points would lie over `y`.) -/
lemma not_mem_image_closure [NoetherianSpace X] [QuasiSober X] [T0Space Y] {f : X → Y}
    (hf : Continuous f) (y : Y) {T : Set X} (hT : IsOpen T) (hTF : ∀ x ∈ T, f x ≠ y) :
    y ∉ f '' closure (f ⁻¹' closure {y} ∩ T) := by
  rintro ⟨t, ht, hty⟩
  set T₀ := f ⁻¹' closure {y} ∩ T
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_closure (s := T₀))
  -- some component through `t` meets `T₀`
  obtain ⟨K, hKS, htK, hKT⟩ : ∃ K ∈ S, t ∈ K ∧ (K ∩ T₀).Nonempty := by
    by_contra h
    push Not at h
    let D := ⋃₀ {K ∈ S | (K ∩ T₀).Nonempty}
    have hD : IsClosed D := by
      change IsClosed (⋃₀ {K | K ∈ S ∧ (K ∩ T₀).Nonempty})
      rw [Set.sUnion_eq_biUnion]
      exact Set.Finite.isClosed_biUnion (hSf.subset fun K (hK : K ∈ S ∧ _) ↦ hK.1)
        fun K (hK : K ∈ S ∧ _) ↦ hSc K hK.1
    have hT₀D : T₀ ⊆ D := by
      intro x hx
      have : x ∈ ⋃₀ S := hSU ▸ subset_closure hx
      obtain ⟨K, hKS, hxK⟩ := this
      exact ⟨K, ⟨hKS, x, hxK, hx⟩, hxK⟩
    obtain ⟨K, ⟨hKS, hKT⟩, htK⟩ := closure_minimal hT₀D hD ht
    exact Set.nonempty_iff_ne_empty.mp hKT (h K hKS htK)
  obtain ⟨k, hk⟩ := QuasiSober.sober (hSi K hKS) (hSc K hKS)
  have hkT : k ∈ T := (hk.mem_open_set_iff hT).mpr (hKT.mono fun x hx ↦ ⟨hx.1, hx.2.2⟩)
  have hKsub : K ⊆ f ⁻¹' closure {y} := by
    have : K ⊆ closure T₀ := hSU ▸ Set.subset_sUnion_of_mem hKS
    exact this.trans (closure_minimal Set.inter_subset_left
      (isClosed_closure.preimage hf))
  have h₁ : y ⤳ f k := specializes_iff_mem_closure.mpr (hKsub (hk.mem))
  have h₂ : f k ⤳ y := hty ▸ (specializes_iff_mem_closure.mpr (hk.def ▸ htK)).map hf
  exact hTF k hkT (h₂.antisymm h₁).eq

end Topology

section Affine

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma specStructureRingHom_comp_isoSpec [IsAffine Y] (a : Γ(Y, ⊤)) :
    (f ≫ Y.isoSpec.hom).specStructureRingHom a = f.appTop a := by
  rw [Scheme.Hom.specStructureRingHom, Scheme.Hom.comp_appTop, Scheme.isoSpec_hom,
    Scheme.toSpecΓ_appTop, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- `exists_section_separating` over an affine noetherian base `Y`, with `f⁻¹ V(I)` described by
basic opens of `Y`. -/
theorem exists_section_separating' [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)] [IsProper f]
    (I : Ideal Γ(Y, ⊤)) (G₁ G₂ : Set X) (hG₁ : IsClosed G₁) (hG₂ : IsClosed G₂)
    (hcov : ∀ x, (∀ a ∈ I, f x ∉ Y.basicOpen a) → x ∈ G₁ ∪ G₂)
    (hdisj : ∀ x, (∀ a ∈ I, f x ∉ Y.basicOpen a) → x ∈ G₁ → x ∉ G₂) :
    ∃ a : Γ(X, ⊤), (∀ x, (∀ a ∈ I, f x ∉ Y.basicOpen a) → x ∈ G₁ → x ∈ X.basicOpen a) ∧
      (∀ x, (∀ a ∈ I, f x ∉ Y.basicOpen a) → x ∈ G₂ → x ∉ X.basicOpen a) := by
  have hW : ∀ x, x ∈ zeroLocusPreimage I (f ≫ Y.isoSpec.hom) ↔
      ∀ a ∈ I, f x ∉ Y.basicOpen a := by
    intro x
    refine forall₂_congr fun a _ ↦ ?_
    rw [specStructureRingHom_comp_isoSpec]
    have e : X.basicOpen (f.appTop a) = f ⁻¹ᵁ Y.basicOpen a := (Scheme.preimage_basicOpen f a).symm
    rw [e]
    rfl
  obtain ⟨a, ha₁, ha₂⟩ := exists_section_separating I (f ≫ Y.isoSpec.hom) G₁ G₂ hG₁ hG₂
    (fun x hx ↦ hcov x ((hW x).mp hx)) (fun x hx ↦ hdisj x ((hW x).mp hx))
  exact ⟨a, fun x hx ↦ ha₁ x ((hW x).mpr hx), fun x hx ↦ ha₂ x ((hW x).mpr hx)⟩

end Affine

section Restrict

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma isIso_app_morphismRestrict (hf : ∀ V : Y.Opens, IsIso (f.app V)) (U : Y.Opens)
    (V : U.toScheme.Opens) : IsIso ((f ∣_ U).app V) := by
  have h₂ : IsIso (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op) :=
    inferInstance
  rw [morphismRestrict_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hf _) h₂

/-- The fibre of `f` over `y ∈ U` is the image of the fibre of `f ∣_ U`. -/
lemma preimage_singleton_eq_image (U : Y.Opens) (y : U) :
    f ⁻¹' {(y : Y)} = (f ⁻¹ᵁ U).ι '' ((f ∣_ U) ⁻¹' {y}) := by
  ext x
  constructor
  · intro hx
    have hxU : x ∈ f ⁻¹ᵁ U := by
      change f x ∈ U
      rw [show f x = y from hx]
      exact y.2
    exact ⟨⟨x, hxU⟩, Subtype.ext ((morphismRestrict_base_coe f U ⟨x, hxU⟩).trans hx), rfl⟩
  · rintro ⟨x', hx', rfl⟩
    change f x'.1 = y
    rw [← morphismRestrict_base_coe]
    exact congrArg Subtype.val hx'

/-- Fibres of proper `f` with `f_* 𝒪_X = 𝒪_Y` are non-empty. -/
lemma nonempty_preimage_singleton [IsProper f] (hf : ∀ V : Y.Opens, IsIso (f.app V)) (y : Y) :
    (f ⁻¹' {y}).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hy : y ∉ Set.range f := by
    rintro ⟨x, hx⟩
    have : x ∈ f ⁻¹' {y} := hx
    rw [h] at this
    exact this
  let N : Y.Opens := ⟨(Set.range f)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩
  have hN : f ⁻¹ᵁ N = ⊥ := le_bot_iff.mp fun x hx ↦ (hx ⟨x, rfl⟩).elim
  have : Nonempty N := ⟨⟨y, hy⟩⟩
  have hinj := (ConcreteCategory.bijective_of_isIso (f.app N)).1
  have : Subsingleton Γ(X, f ⁻¹ᵁ N) := by rw [hN]; infer_instance
  exact not_subsingleton Γ(Y, N) hinj.subsingleton

end Restrict

section Zariski

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Zariski's connectedness theorem over an affine base.** -/
theorem isPreconnected_preimage_singleton_of_isAffine [IsAffine Y] [IsLocallyNoetherian Y]
    [IsProper f] (hf : ∀ V : Y.Opens, IsIso (f.app V)) (y : Y) :
    _root_.IsPreconnected (f ⁻¹' {y}) := by
  rw [isPreconnected_closed_iff]
  intro G₁ G₂ hG₁ hG₂ hF ⟨x₁, hx₁F, hx₁G⟩ ⟨x₂, hx₂F, hx₂G⟩
  by_contra hne
  have hdF : ∀ x, f x = y → x ∈ G₁ → x ∉ G₂ := fun x hx h₁ h₂ ↦ hne ⟨x, hx, h₁, h₂⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  -- the bad loci, closed and not meeting the fibre
  set C := G₁ ∩ G₂ ∩ f ⁻¹' closure {y}
  have hC : IsClosed C := (hG₁.inter hG₂).inter (isClosed_closure.preimage f.continuous)
  have hyC : y ∉ f '' C := fun ⟨c, hc, hcy⟩ ↦ hdF c hcy hc.1.1 hc.1.2
  set T := (G₁ ∪ G₂)ᶜ
  have hT : IsOpen T := (hG₁.union hG₂).isOpen_compl
  have hTF : ∀ x ∈ T, f x ≠ y := fun x hx hxy ↦ hx (hF hxy)
  have hyB := not_mem_image_closure f.continuous y hT hTF
  let N : Y.Opens := ⟨(f '' C ∪ f '' closure (f ⁻¹' closure {y} ∩ T))ᶜ,
    ((f.isClosedMap _ hC).union (f.isClosedMap _ isClosed_closure)).isOpen_compl⟩
  have hyN : y ∈ N := fun h ↦ h.elim hyC hyB
  obtain ⟨_, ⟨s, rfl⟩, hys, hsN⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen Y) hyN
  -- restrict to the basic open `V = D(s)`
  set V := Y.basicOpen s
  have hVaff : IsAffineOpen V := (isAffineOpen_top Y).basicOpen s
  have : IsAffine V.toScheme := hVaff
  have : IsNoetherianRing Γ(V.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian (X := V.toScheme) ⟨⊤, isAffineOpen_top _⟩
  let g := f ∣_ V
  let y' : V.toScheme := ⟨y, hys⟩
  let I := pointIdeal (X := V.toScheme) (U := ⊤) (x := y') trivial
  have hI : ∀ a, a ∈ I ↔ y' ∉ V.toScheme.basicOpen a := fun a ↦ mem_pointIdeal _ a
  -- points of `X_V` over `V(I)` lie over the closure of `y`, inside `N`
  have hW : ∀ x' : (f ⁻¹ᵁ V).toScheme, (∀ a ∈ I, g x' ∉ V.toScheme.basicOpen a) →
      f x'.1 ∈ closure {y} ∧ f x'.1 ∈ N := by
    intro x' hx'
    have hcl : g x' ∈ closure {y'} := by
      rw [mem_closure_iff]
      intro o ho hxo
      obtain ⟨_, ⟨b, rfl⟩, hxb, hbo⟩ :=
        Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen V.toScheme)
          (show g x' ∈ (⟨o, ho⟩ : Opens _) from hxo)
      by_cases hyb : y' ∈ V.toScheme.basicOpen b
      · exact ⟨y', hbo hyb, rfl⟩
      · exact absurd hxb (hx' b ((hI b).mpr hyb))
    have h1 : f x'.1 = (g x').1 := (morphismRestrict_base_coe f V x').symm
    refine ⟨?_, hsN ?_⟩
    · rw [h1]
      have := image_closure_subset_closure_image V.ι.continuous ⟨g x', hcl, rfl⟩
      rwa [Set.image_singleton] at this
    · rw [h1]
      exact (g x').2
  let G₁' : Set (f ⁻¹ᵁ V).toScheme := (f ⁻¹ᵁ V).ι ⁻¹' G₁
  let G₂' : Set (f ⁻¹ᵁ V).toScheme := (f ⁻¹ᵁ V).ι ⁻¹' G₂
  obtain ⟨a, ha₁, ha₂⟩ := exists_section_separating' g I G₁' G₂'
    (hG₁.preimage (f ⁻¹ᵁ V).ι.continuous) (hG₂.preimage (f ⁻¹ᵁ V).ι.continuous)
    (fun x' hx' ↦ by
      obtain ⟨hcl, hN⟩ := hW x' hx'
      by_contra h
      refine hN (Or.inr ⟨x'.1, subset_closure ⟨hcl, fun h' ↦ h ?_⟩, rfl⟩)
      exact h'.imp id id)
    (fun x' hx' h₁ h₂ ↦ by
      obtain ⟨hcl, hN⟩ := hW x' hx'
      exact hN (Or.inl ⟨x'.1, ⟨⟨h₁, h₂⟩, hcl⟩, rfl⟩))
  -- the two points of the fibre
  have hxV : ∀ x, f x = y → x ∈ f ⁻¹ᵁ V := fun x hx ↦ by
    change f x ∈ V
    rw [hx]
    exact hys
  have hgx : ∀ x (hx : f x = y), g ⟨x, hxV x hx⟩ = y' := fun x hx ↦
    Subtype.ext ((morphismRestrict_base_coe f V _).trans hx)
  have hWx : ∀ x (hx : f x = y), ∀ b ∈ I, g ⟨x, hxV x hx⟩ ∉ V.toScheme.basicOpen b :=
    fun x hx b hb ↦ by rw [hgx x hx]; exact (hI b).mp hb
  have h₁ := ha₁ ⟨x₁, hxV x₁ hx₁F⟩ (hWx x₁ hx₁F) hx₁G
  have h₂ := ha₂ ⟨x₂, hxV x₂ hx₂F⟩ (hWx x₂ hx₂F) hx₂G
  -- `a` comes from `V`
  have := isIso_app_morphismRestrict f hf V ⊤
  have : IsIso g.appTop := this
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso g.appTop).2 a
  have e : (f ⁻¹ᵁ V).toScheme.basicOpen (g.appTop b) = g ⁻¹ᵁ V.toScheme.basicOpen b :=
    (Scheme.preimage_basicOpen g b).symm
  rw [e] at h₁ h₂
  change g _ ∈ V.toScheme.basicOpen b at h₁
  change g _ ∉ V.toScheme.basicOpen b at h₂
  rw [hgx x₁ hx₁F] at h₁
  rw [hgx x₂ hx₂F] at h₂
  exact h₂ h₁

end Zariski

end AlgebraicGeometry.CohomologyAux

namespace AlgebraicGeometry

open CohomologyAux

/-- **Zariski's connectedness theorem** (EGA III 4.3.1; Stacks Tag 03H0; Hartshorne III.11.3): for
`f : X ⟶ Y` proper, `Y` locally noetherian and `𝒪_Y ≅ f_* 𝒪_X`, every fibre of `f` is connected
and non-empty. -/
theorem zariskiConnectednessStatement : ZariskiConnectednessStatement.{u} := by
  intro X Y f _ _ hf y
  obtain ⟨V₀, hV₀, hyV₀, -⟩ : ∃ V₀ : Y.Opens, IsAffineOpen V₀ ∧ y ∈ V₀ ∧ V₀ ≤ ⊤ :=
    Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (show y ∈ (⊤ : Y.Opens) from trivial)
  have : IsAffine V₀.toScheme := hV₀
  have hpre : _root_.IsPreconnected (f ⁻¹' {y}) := by
    have h := isPreconnected_preimage_singleton_of_isAffine (f ∣_ V₀)
      (fun V ↦ isIso_app_morphismRestrict f hf V₀ V) ⟨y, hyV₀⟩
    rw [show f ⁻¹' {y} = _ from preimage_singleton_eq_image f V₀ ⟨y, hyV₀⟩]
    exact h.image _ (f ⁻¹ᵁ V₀).ι.continuous.continuousOn
  have hconn : _root_.IsConnected (f ⁻¹' {y}) := ⟨nonempty_preimage_singleton f hf y, hpre⟩
  have : ConnectedSpace (f ⁻¹' {y}) := isConnected_iff_connectedSpace.mp hconn
  exact (f.fiberHomeo y).symm.surjective.connectedSpace (f.fiberHomeo y).symm.continuous

end AlgebraicGeometry
