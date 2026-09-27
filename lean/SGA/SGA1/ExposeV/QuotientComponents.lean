/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeV.InertiaGroups

/-!
# SGA 1, Exposé V, V.3.1 and V.3.2 in general

Let `f : X ⟶ Z` be étale and separated (and quasi-compact) with `Z` locally noetherian, and let a
finite group `G` act on `X` by `Z`-automorphisms. Then `G` acts admissibly, `X ⟶ X/G` is étale
(V.3.2, `etale_of_etale_of_isLocallyNoetherian`) and `X/G ⟶ Z` is étale (V.3.1,
`etaleQuotientStatement`).

SGA's proof reduces to `X` connected and `G` faithful. We follow it:
* connected components of a locally noetherian scheme are open
  (`isClopen_connectedComponent_of_isLocallyNoetherian`);
* for an open `C` whose translates are equal to it or disjoint from it and cover `X`, the quotient
  of `C` by its stabilizer is `X/G` (`isIso_desc_of_isQuotient_stabilizer`);
* when every element of every inertia group acts trivially, the quotient morphism is étale
  (`etale_of_inertiaGroup_eq_id`, a form of V.2.3 not requiring `G` faithful); on a connected
  component this holds by I.5.4.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace SGA.SGA1.ExposeV

section Components

/-- In a noetherian topological space, connected components are open: the complement of a
component is the union of the finitely many irreducible components not meeting it. -/
lemma isOpen_connectedComponent_of_noetherianSpace {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] (x : α) : IsOpen (connectedComponent x) := by
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := α)
  have hc : (connectedComponent x)ᶜ =
      ⋃₀ {Z ∈ irreducibleComponents α | Disjoint Z (connectedComponent x)} := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_sep_iff]
    constructor
    · intro hy
      refine ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        Set.disjoint_left.mpr fun z hz hzC ↦ hy ?_⟩, mem_irreducibleComponent⟩
      have h1 : irreducibleComponent y ⊆ connectedComponent z :=
        (IsIrreducible.isConnected isIrreducible_irreducibleComponent).isPreconnected
          |>.subset_connectedComponent hz
      rw [← connectedComponent_eq hzC] at h1
      exact h1 mem_irreducibleComponent
    · rintro ⟨Z, ⟨-, hZ⟩, hyZ⟩ hyC
      exact Set.disjoint_left.mp hZ hyZ hyC
  rw [← isClosed_compl_iff, hc, Set.sUnion_eq_biUnion]
  exact (hfin.subset fun Z hZ ↦ hZ.1).isClosed_biUnion fun Z hZ ↦
    isClosed_of_mem_irreducibleComponents Z hZ.1

/-- In a locally noetherian scheme, connected components are open (and closed). -/
lemma isClopen_connectedComponent_of_isLocallyNoetherian {X : Scheme.{u}} [IsLocallyNoetherian X]
    (x : X) : IsClopen (connectedComponent x) := by
  refine ⟨isClosed_connectedComponent, isOpen_iff_forall_mem_open.mpr fun y hy ↦ ?_⟩
  obtain ⟨U, hU, hyU⟩ := exists_isAffineOpen_mem y
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hN : TopologicalSpace.NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
  let y' : U := ⟨y, hyU⟩
  refine ⟨Subtype.val '' connectedComponent y', ?_, ?_, ⟨y', mem_connectedComponent, rfl⟩⟩
  · rw [connectedComponent_eq hy]
    exact (isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn)
      |>.subset_connectedComponent ⟨y', mem_connectedComponent, rfl⟩
  · exact U.isOpen.isOpenMap_subtype_val _
      (@isOpen_connectedComponent_of_noetherianSpace _ _ hN y')

end Components

end SGA.SGA1.ExposeV

namespace SGA.SGA1.ExposeV

section Trivial

variable {G : Type*} [Group G] {X Y : Scheme.{u}} {T : G → (X ⟶ X)}
  (hT : IsRightAction T) {p : X ⟶ Y} (hTp : ∀ g, T g ≫ p = p)

set_option backward.isDefEq.respectTransparency false in
include hT in
/-- V.2.3, with inertia acting trivially instead of being trivial: under the conditions of V.1.3,
if every element of every inertia group acts trivially on `X`, then `p` is étale. (The action
factors through the quotient of `G` by the kernel `K`, whose quotient `X/G = X/(G/K)` has trivial
inertia.) -/
theorem etale_of_inertiaGroup_eq_id [IsAffineHom p] [Finite G]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U)
    (h : ∀ x g, g ∈ inertiaGroup T x → T g = 𝟙 X) : Etale p := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Etale) _ (iSup_affineOpens_eq_top Y)
    fun V ↦ ?_
  let W := p ⁻¹ᵁ V.1
  have : IsAffine W.toScheme := V.2.preimage p
  have hR := isRightAction_restrictAction hTp hT V.1
  have hq := isQuotient_restrict hTp hT (fun U _ ↦ hsec U) V.1
  let A : CommRingCat.{u} := Γ(W.toScheme, ⊤)
  let _ : MulSemiringAction G A := sectionsAction hR ⊤ fun _ ↦ le_top
  let B : CommRingCat.{u} := .of (FixedPoints.subring A G)
  have hq' : IsQuotient (restrictAction hTp V.1) (W.toScheme.isoSpec.hom ≫ specMap A B) :=
    (isQuotient_specMap (G := G) (B := B) Subtype.val_injective).iso_comp _
      (isoSpec_hom_comp_specAction hR)
  have hpe : p ∣_ V.1 = (W.toScheme.isoSpec.hom ≫ specMap A B) ≫ (hq.uniqueIso hq').inv := by
    rw [Iso.eq_comp_inv]
    exact hq.comp_uniqueIso_hom hq'
  -- the group of automorphisms of `A` induced by `G`
  let G' : Subgroup (RingAut A) := (MulSemiringAction.toRingAut G A).range
  have : Finite G' :=
    Finite.of_surjective _ (MulSemiringAction.toRingAut G A).rangeRestrict_surjective
  have : Algebra.IsInvariant B A G' := ⟨fun a ha ↦ ⟨⟨a, fun g ↦ by
    have := ha ⟨MulSemiringAction.toRingAut G A g, g, rfl⟩
    exact this⟩, rfl⟩⟩
  have : SMulCommClass G' B A := ⟨fun σ b a ↦ by
    obtain ⟨_, g, rfl⟩ := σ
    change (MulSemiringAction.toRingAut G A g) (b.1 * a) = b.1 * _
    rw [map_mul]
    congr 1
    exact b.2 g⟩
  have hfree : ∀ m : Ideal A, m.IsMaximal → ∀ σ ∈ m.inertia G', σ = 1 := by
    rintro m hm ⟨_, g, rfl⟩ hσ
    have hg : g ∈ m.inertia G := fun a ↦ hσ a
    let w : W.toScheme := W.toScheme.isoSpec.inv ⟨m, hm.isPrime⟩
    have hw : W.toScheme.isoSpec.hom w = ⟨m, hm.isPrime⟩ := by
      simp [w, ← Scheme.Hom.comp_apply]
    have key := fromSpecResidueField_comp_eq_of_mem_inertia hR w g (by rw [hw]; exact hg)
    have hTg := h (W.ι w) g (by
      have hι := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField W.ι w
      change X.fromSpecResidueField (W.ι w) ≫ T g = X.fromSpecResidueField (W.ι w)
      rw [← cancel_epi (Spec.map (W.ι.residueFieldMap w)), reassoc_of% hι, hι,
        ← Scheme.Hom.resLE_comp_ι (T g) (preimage_le_preimage_of_comp_eq (hTp g) V.1),
        ← Category.assoc]
      exact congr_arg (· ≫ W.ι) key)
    have hRg : restrictAction hTp V.1 g = 𝟙 _ := by
      rw [← cancel_mono W.ι, Scheme.Hom.resLE_comp_ι, hTg, Category.id_comp, Category.comp_id]
    apply Subtype.ext
    ext a
    change (restrictAction hTp V.1 g).appLE ⊤ ⊤ _ a = a
    rw [appLE_congr_hom hRg ⊤ ⊤ _ le_rfl]
    change (Scheme.Hom.appLE (𝟙 _) ⊤ ⊤ le_rfl) a = a
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    simp
    rfl
  have := (etale_of_inertia_eq_bot (B := B) (A := A) (G := G') Subtype.val_injective hfree).1
  have : Etale (specMap A B) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr this)
  rw [hpe]
  infer_instance

end Trivial

end SGA.SGA1.ExposeV

namespace SGA.SGA1.ExposeV

section Stabilizer

variable {G : Type*} [Group G] {X : Scheme.{u}} {T : G → (X ⟶ X)} (hT : IsRightAction T)
  (C : X.Opens)

/-- The stabilizer of an open subset `C` for a right action. -/
def openStabilizer : Subgroup G where
  carrier := {g | T g ⁻¹ᵁ C = C}
  mul_mem' {g h} hg hh := by
    change T (g * h) ⁻¹ᵁ C = C
    rw [hT.map_mul, Scheme.Hom.comp_preimage, hh, hg]
  one_mem' := by
    change T 1 ⁻¹ᵁ C = C
    rw [hT.map_one]
    rfl
  inv_mem' {g} hg := by
    change T g⁻¹ ⁻¹ᵁ C = C
    conv_lhs => rw [← hg]
    rw [← Scheme.Hom.comp_preimage, ← hT.map_mul, inv_mul_cancel, hT.map_one]
    rfl

lemma mem_openStabilizer {g : G} : g ∈ openStabilizer hT C ↔ T g ⁻¹ᵁ C = C := Iff.rfl

/-- The action of the stabilizer of `C` on `C`. -/
noncomputable def stabilizerAction (h : openStabilizer hT C) : C.toScheme ⟶ C.toScheme :=
  (T h).resLE C C h.2.ge

@[reassoc]
lemma stabilizerAction_ι (h : openStabilizer hT C) :
    stabilizerAction hT C h ≫ C.ι = C.ι ≫ T h :=
  Scheme.Hom.resLE_comp_ι ..

lemma isRightAction_stabilizerAction : IsRightAction (stabilizerAction hT C) where
  map_one := by
    rw [← cancel_mono C.ι, stabilizerAction_ι]
    simp [hT.map_one]
  map_mul g h := by
    rw [← cancel_mono C.ι, Category.assoc, stabilizerAction_ι, stabilizerAction_ι,
      stabilizerAction_ι_assoc]
    exact congrArg (C.ι ≫ ·) (hT.map_mul g h)

variable {C} {p : X ⟶ Y} (hTp : ∀ g, T g ≫ p = p)

include hT in
/-- The quotient of a union of translates of an open subset `C` whose translates are pairwise
equal or disjoint: the quotient of `C` by its stabilizer `H` is the quotient of `X` by `G`, i.e.
`C/H ≅ X/G` (end of V.1 and proof of V.3.2 in SGA). -/
theorem isIso_desc_of_isQuotient_stabilizer [Finite G] [IsAffineHom p]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U)
    (hdisj : ∀ g, T g ⁻¹ᵁ C = C ∨ Disjoint (T g ⁻¹ᵁ C) C) (hcov : ⨆ g, T g ⁻¹ᵁ C = ⊤)
    {Q : Scheme.{u}} {q : C.toScheme ⟶ Q} (hq : IsQuotient (stabilizerAction hT C) q) :
    IsIso (hq.desc (C.ι ≫ p) fun h ↦ by rw [stabilizerAction_ι_assoc, hTp]) := by
  have hp := isQuotient_of_sectionsAreInvariant hT fun U _ ↦ hsec U
  let 𝒰 := X.openCoverOfIsOpenCover (fun g : G ↦ T g ⁻¹ᵁ C) hcov
  let f : ∀ g : G, (T g ⁻¹ᵁ C).toScheme ⟶ Q := fun g ↦ (T g).resLE C (T g ⁻¹ᵁ C) le_rfl ≫ q
  -- two pieces agree on their overlap
  have hf : ∀ g₁ g₂ : G, pullback.fst (𝒰.f g₁) (𝒰.f g₂) ≫ f g₁ =
      pullback.snd (𝒰.f g₁) (𝒰.f g₂) ≫ f g₂ := by
    intro g₁ g₂
    change pullback.fst (T g₁ ⁻¹ᵁ C).ι (T g₂ ⁻¹ᵁ C).ι ≫ f g₁ =
      pullback.snd (T g₁ ⁻¹ᵁ C).ι (T g₂ ⁻¹ᵁ C).ι ≫ f g₂
    rcases isEmpty_or_nonempty (pullback (T g₁ ⁻¹ᵁ C).ι (T g₂ ⁻¹ᵁ C).ι : Scheme.{u}) with
      hE | ⟨⟨z⟩⟩
    · exact Scheme.hom_ext_of_forall _ _ fun z ↦ (hE.false z).elim
    let a := pullback.fst (T g₁ ⁻¹ᵁ C).ι (T g₂ ⁻¹ᵁ C).ι ≫ (T g₁).resLE C (T g₁ ⁻¹ᵁ C) le_rfl
    let b := pullback.snd (T g₁ ⁻¹ᵁ C).ι (T g₂ ⁻¹ᵁ C).ι ≫ (T g₂).resLE C (T g₂ ⁻¹ᵁ C) le_rfl
    have hab : b ≫ C.ι = a ≫ C.ι ≫ T (g₁⁻¹ * g₂) := by
      simp only [a, b, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]
      rw [← pullback.condition_assoc, ← hT.map_mul, mul_inv_cancel_left]
    have hH : g₁⁻¹ * g₂ ∈ openStabilizer hT C := by
      refine (hdisj _).resolve_right fun hd ↦ ?_
      have hmem : (a ≫ C.ι) z ∈ T (g₁⁻¹ * g₂) ⁻¹ᵁ C ⊓ C := by
        refine ⟨?_, (a z).2⟩
        change (a ≫ C.ι ≫ T (g₁⁻¹ * g₂)) z ∈ C
        rw [← hab]
        exact (b z).2
      rw [hd.eq_bot] at hmem
      exact hmem
    have hb : b = a ≫ stabilizerAction hT C ⟨_, hH⟩ := by
      rw [← cancel_mono C.ι, hab, Category.assoc a, stabilizerAction_ι]
    change a ≫ q = b ≫ q
    rw [hb, Category.assoc a, hq.comp_eq]
  let q' := 𝒰.glueMorphisms f hf
  have hq'g : ∀ g, (T g ⁻¹ᵁ C).ι ≫ q' = f g := 𝒰.ι_glueMorphisms f hf
  have hq' : ∀ k, T k ≫ q' = q' := by
    intro k
    refine 𝒰.hom_ext _ _ fun (g : G) ↦ ?_
    change (T g ⁻¹ᵁ C).ι ≫ T k ≫ q' = (T g ⁻¹ᵁ C).ι ≫ q'
    have hle : T g ⁻¹ᵁ C ≤ T k ⁻¹ᵁ (T (k⁻¹ * g) ⁻¹ᵁ C) := by
      rw [← Scheme.Hom.comp_preimage, ← hT.map_mul, mul_inv_cancel_left]
    rw [← Scheme.Hom.resLE_comp_ι_assoc (T k) hle, hq'g, hq'g]
    simp only [f, ← Category.assoc]
    congr 1
    rw [← cancel_mono C.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
      Scheme.Hom.resLE_comp_ι, ← hT.map_mul, mul_inv_cancel_left]
  have hq'C : C.ι ≫ q' = q := by
    have hle : C ≤ T 1 ⁻¹ᵁ C := by rw [hT.map_one]; exact le_rfl
    rw [← X.homOfLE_ι hle, Category.assoc, hq'g]
    change X.homOfLE hle ≫ (T 1).resLE C (T 1 ⁻¹ᵁ C) le_rfl ≫ q = q
    rw [← Category.assoc]
    convert Category.id_comp q
    rw [← cancel_mono C.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc,
      hT.map_one]
    simp
  let ψ := hq.desc (C.ι ≫ p) fun h ↦ by rw [stabilizerAction_ι_assoc, hTp]
  let ψ' := hp.desc q' hq'
  refine ⟨ψ', ?_, ?_⟩
  · refine hq.hom_ext ?_
    rw [hq.fac_assoc, Category.assoc, hp.fac, hq'C, Category.comp_id]
  · refine hp.hom_ext ?_
    rw [hp.fac_assoc, Category.comp_id]
    refine 𝒰.hom_ext _ _ fun (g : G) ↦ ?_
    change (T g ⁻¹ᵁ C).ι ≫ q' ≫ ψ = (T g ⁻¹ᵁ C).ι ≫ p
    rw [reassoc_of% (hq'g g), Category.assoc, hq.fac, Scheme.Hom.resLE_comp_ι_assoc, hTp]

end Stabilizer

end SGA.SGA1.ExposeV

namespace SGA.SGA1.ExposeV

section General

variable {G : Type*} [Group G] {X : Scheme.{u}} {T : G → (X ⟶ X)} (hT : IsRightAction T)

include hT in
/-- The translates of a connected component under a right action are equal to it or disjoint
from it. -/
lemma preimage_connectedComponent_eq_or_disjoint (x : X) (hC : IsOpen (connectedComponent x))
    (g : G) : T g ⁻¹ᵁ ⟨connectedComponent x, hC⟩ = ⟨connectedComponent x, hC⟩ ∨
      Disjoint (T g ⁻¹ᵁ ⟨connectedComponent x, hC⟩) ⟨connectedComponent x, hC⟩ := by
  refine or_iff_not_imp_right.mpr fun hd ↦ ?_
  obtain ⟨z, hz₁, hz₂⟩ : ∃ z, T g z ∈ connectedComponent x ∧ z ∈ connectedComponent x := by
    by_contra! h
    refine hd (disjoint_iff.mpr (le_bot_iff.mp fun y hy ↦ ?_))
    exact (h y hy.1 hy.2).elim
  have hcz : connectedComponent x = connectedComponent z := connectedComponent_eq hz₂
  have hcTz : connectedComponent x = connectedComponent (T g z) := connectedComponent_eq hz₁
  apply le_antisymm
  · intro y hy
    change T g y ∈ connectedComponent x at hy
    have : T g⁻¹ (T g y) ∈ connectedComponent (T g⁻¹ (T g z)) := by
      apply (T g⁻¹).continuous.image_connectedComponent_subset (T g z)
      refine ⟨T g y, ?_, rfl⟩
      rw [← hcTz]
      exact hy
    rwa [hT.apply_inv_apply, hT.apply_inv_apply, ← hcz] at this
  · intro y hy
    change T g y ∈ connectedComponent x
    rw [hcTz]
    apply (T g).continuous.image_connectedComponent_subset z
    refine ⟨y, ?_, rfl⟩
    rw [← hcz]
    exact hy

include hT in
/-- V.3.2: let `f : X ⟶ Z` be étale and separated with `Z` locally noetherian, and let a finite
group `G` act on `X` by `Z`-automorphisms. Then the quotient morphism `p : X ⟶ Y` of V.1.3 is
étale. As in SGA, one reduces to a connected component `C` of `X` and its stabilizer `H`: the
quotient `C/H` is the open and closed part of `Y` over which `G • C` lies
(`isIso_desc_of_isQuotient_stabilizer`), and the inertia groups of `H` on `C` act trivially by
I.5.4, so `C ⟶ C/H` is étale (`etale_of_inertiaGroup_eq_id`). -/
theorem etale_of_etale_of_isLocallyNoetherian [Finite G] {Y Z : Scheme.{u}} {p : X ⟶ Y}
    (hTp : ∀ g, T g ≫ p = p) [IsAffineHom p] (hsec : ∀ U, SectionsAreInvariant T p hTp U)
    [IsLocallyNoetherian Z] (f : X ⟶ Z) [Etale f] [IsSeparated f] (hTf : ∀ g, T g ≫ f = f) :
    Etale p := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hclopen := isClopen_connectedComponent_of_isLocallyNoetherian (X := X)
  let Cx : X → X.Opens := fun x ↦ ⟨connectedComponent x, (hclopen x).isOpen⟩
  have hcov : ⨆ x, Cx x = ⊤ :=
    top_le_iff.mp fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, mem_connectedComponent⟩
  have : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale) Cx hcov fun x ↦ ?_
  let C := Cx x
  have hdisj : ∀ g, T g ⁻¹ᵁ C = C ∨ Disjoint (T g ⁻¹ᵁ C) C :=
    preimage_connectedComponent_eq_or_disjoint hT x (hclopen x).isOpen
  have := isIntegralHom_of_sectionsAreInvariant hT fun U _ ↦ hsec U
  have horb := (surjective_and_orbit_of_sectionsAreInvariant hT fun U _ ↦ hsec U).2
  -- the `G`-saturation `N` of `C` and its image `V₀` in `Y`
  let N : X.Opens := ⨆ g, T g ⁻¹ᵁ C
  have hN : ∀ g, T g ⁻¹ᵁ N = N := hT.preimage_eq_of_le fun k y hy ↦ by
    obtain ⟨g, hg⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨k⁻¹ * g, ?_⟩
    change T (k⁻¹ * g) (T k y) ∈ C
    rw [← Scheme.Hom.comp_apply, ← hT.map_mul, mul_inv_cancel_left]
    exact hg
  let V₀ := imageOpen p.isClosedMap N
  have hV₀ : p ⁻¹ᵁ V₀ = N := preimage_imageOpen _ horb hN
  -- restriction of everything to `X' = p⁻¹ V₀`
  let ι := (p ⁻¹ᵁ V₀).ι
  have hT' := isRightAction_restrictAction hTp hT V₀
  have hTp' := restrictAction_comp hTp V₀
  have : IsAffineHom (p ∣_ V₀) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p V₀).flip ‹IsAffineHom p›
  have hsec' : ∀ U, SectionsAreInvariant (restrictAction hTp V₀) (p ∣_ V₀) hTp' U :=
    fun U ↦ sectionsAreInvariant_restrict hTp (hsec _)
  have hTι : ∀ g, restrictAction hTp V₀ g ≫ ι = ι ≫ T g := fun g ↦ Scheme.Hom.resLE_comp_ι ..
  let C' : (p ⁻¹ᵁ V₀).toScheme.Opens := ι ⁻¹ᵁ C
  have hpre : ∀ g, restrictAction hTp V₀ g ⁻¹ᵁ C' = ι ⁻¹ᵁ (T g ⁻¹ᵁ C) := fun g ↦ by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hTι]
  have hdisj' : ∀ g, restrictAction hTp V₀ g ⁻¹ᵁ C' = C' ∨
      Disjoint (restrictAction hTp V₀ g ⁻¹ᵁ C') C' := fun g ↦ by
    rw [hpre]
    rcases hdisj g with h | h
    · left; rw [h]
    · right
      exact disjoint_iff.mpr (le_bot_iff.mp fun y hy ↦ h.le_bot ⟨hy.1, hy.2⟩)
  have hcov' : ⨆ g, restrictAction hTp V₀ g ⁻¹ᵁ C' = ⊤ := by
    refine top_le_iff.mp fun y _ ↦ ?_
    have hy : ι y ∈ N := hV₀ ▸ (y.2 : ι y ∈ p ⁻¹ᵁ V₀)
    obtain ⟨g, hg⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨g, ?_⟩
    rw [hpre]
    exact hg
  -- the quotient of `C'` by its stabilizer, relative to `V₀`
  let S := stabilizerAction hT' C'
  have hS := isRightAction_stabilizerAction hT' C'
  have hSf : ∀ h, S h ≫ C'.ι ≫ p ∣_ V₀ = C'.ι ≫ p ∣_ V₀ := fun h ↦ by
    rw [stabilizerAction_ι_assoc, hTp']
  have hC'closed : IsClosed (Set.range C'.ι) := by
    rw [Scheme.Opens.range_ι]
    exact (hclopen x).isClosed.preimage ι.continuous
  have : IsClosedImmersion C'.ι := .of_isPreimmersion _ hC'closed
  let q := toQuotient hSf
  have hq := isQuotient_toQuotient hSf hS
  -- `C'` is connected
  have hC'conn : PreconnectedSpace C'.toScheme := by
    refine Subtype.preconnectedSpace ?_
    refine Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_
    have : Subtype.val '' (C' : Set (p ⁻¹ᵁ V₀).toScheme) = connectedComponent x := by
      ext y
      refine ⟨fun ⟨z, hz, hzy⟩ ↦ hzy ▸ hz, fun hy ↦ ⟨⟨y, ?_⟩, hy, rfl⟩⟩
      change y ∈ p ⁻¹ᵁ V₀
      rw [hV₀]
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨1, ?_⟩
      change T 1 y ∈ C
      rw [hT.map_one]
      exact hy
    exact this ▸ isPreconnected_connectedComponent
  let fC : C'.toScheme ⟶ Z := C'.ι ≫ ι ≫ f
  have hSfC : ∀ h, S h ≫ fC = fC := fun h ↦ by
    simp only [fC, S, stabilizerAction_ι_assoc]
    rw [reassoc_of% (hTι h), hTf]
  have hqet : Etale q := etale_of_inertiaGroup_eq_id hS (comp_toQuotient hSf)
    (sectionsAreInvariant_toQuotient hSf) fun c h hh ↦ eq_id_of_mem_inertiaGroup fC hSfC c h hh
  have hψ := isIso_desc_of_isQuotient_stabilizer hT' hTp' hsec' hdisj' hcov' hq
  have h₁ : Etale (C'.ι ≫ p ∣_ V₀) := by
    rw [← hq.fac (C'.ι ≫ p ∣_ V₀) (fun h ↦ by rw [stabilizerAction_ι_assoc, hTp'])]
    infer_instance
  -- back to `C`
  have hrange : Set.range C.ι = Set.range (C'.ι ≫ ι) := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      have hc : C.ι c ∈ p ⁻¹ᵁ V₀ := by
        rw [hV₀]
        refine TopologicalSpace.Opens.mem_iSup.mpr ⟨1, ?_⟩
        change T 1 (C.ι c) ∈ C
        rw [hT.map_one]
        exact c.2
      exact ⟨⟨⟨C.ι c, hc⟩, c.2⟩, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨⟨(C'.ι ≫ ι) c, c.2⟩, rfl⟩
  let e := IsOpenImmersion.isoOfRangeEq C.ι (C'.ι ≫ ι) hrange
  have : C.ι ≫ p = e.hom ≫ (C'.ι ≫ p ∣_ V₀) ≫ V₀.ι := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc C'.ι,
      IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
  change Etale (C.ι ≫ p)
  rw [this]
  infer_instance

end General

end SGA.SGA1.ExposeV

namespace SGA.SGA1.ExposeV

section Statement

variable {G : Type*} [Group G] [Finite G] {X Z : Scheme.{u}} {T : G → (X ⟶ X)}
  (hT : IsRightAction T) (f : X ⟶ Z) (hTf : ∀ g, T g ≫ f = f)

include hT in
/-- V.3.1 and V.3.2: let `f : X ⟶ Z` be étale, separated and quasi-compact with `Z` locally
noetherian, and `G` a finite group acting by `Z`-automorphisms. Then for any quotient
`p : X ⟶ Y` of `X` by `G` (which exists, `isAdmissible_of_etale`), both `p` and `Y ⟶ Z` are
étale. -/
theorem etale_and_etale_of_isQuotient [Etale f] [IsSeparated f] [QuasiCompact f]
    [IsLocallyNoetherian Z] {Y : Scheme.{u}} {p : X ⟶ Y} (hp : IsQuotient T p) :
    Etale p ∧ Etale (hp.desc f hTf) := by
  obtain ⟨Y₀, p₀, hTp₀, _, hsec⟩ := isAdmissible_of_etale hT hTf (f := f)
  have hp₀ := isQuotient_of_sectionsAreInvariant hT fun U _ ↦ hsec U
  have : Etale p₀ := etale_of_etale_of_isLocallyNoetherian hT hTp₀ hsec f hTf
  have : Etale (p₀ ≫ hp₀.desc f hTf) := by rw [hp₀.fac]; infer_instance
  have : Etale (hp₀.desc f hTf) := etale_desc_of_etale hT hTp₀ hsec _
  let e := hp.uniqueIso hp₀
  have h₁ : p = p₀ ≫ e.inv := by rw [Iso.eq_comp_inv]; exact hp.comp_uniqueIso_hom hp₀
  have h₂ : hp.desc f hTf = e.hom ≫ hp₀.desc f hTf :=
    hp.hom_ext (by rw [hp.fac, IsQuotient.comp_uniqueIso_hom_assoc, hp₀.fac])
  constructor
  · rw [h₁]; infer_instance
  · rw [h₂]; infer_instance

end Statement

/-- V.3.1 and V.3.2 hold. -/
theorem etaleQuotientStatement : EtaleQuotientStatement.{u} := by
  intro X Y f _ _ _ _ G _ _ T hT hf
  exact ⟨isAdmissible_of_etale hT hf, fun Z p hp ↦ etale_and_etale_of_isQuotient hT f hf hp⟩

end SGA.SGA1.ExposeV
