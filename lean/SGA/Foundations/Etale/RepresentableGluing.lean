/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Etale.LocallyConstant
import SGA.Foundations.Etale.Points

/-!
# Representability of étale sheaves: restriction and disjoint unions

Let `e : S' ⟶ S` be étale, `G` a sheaf of sets on the small étale site of `S` and `Y` an
étale `S'`-scheme with an isomorphism `φ : yoneda Y ≅ e^! G` (the restriction of `G` to `S'`).
Then `φ` identifies `T`-points of `Y` with sections of `G` over `T`
(`Scheme.etaleRepresentsEquiv`), naturally in `T`; in particular `G` has a universal section
over `Y`.

* If `κ : Y ⟶ Z` is a cartesian morphism over `e` to an étale `S`-scheme `Z`, and `s` is a
  section of `G` over `Z` restricting to the universal section over `Y`, then the morphism
  `yoneda Z ⟶ G` defined by `s` becomes an isomorphism after restriction to `S'`
  (`Scheme.isIso_etaleRestrict_map_yonedaEquiv_symm`). Together with the conservativity of
  restriction along jointly surjective étale families (`Scheme.isIso_of_forall_isIso_etaleRestrict`)
  this is the basic tool to recognize representing objects.
* Representability is local on disjoint unions: if the restriction of `G` to each `Wᵢ` is
  represented by `Xᵢ`, then `G` is represented on `∐ Wᵢ` by `∐ Xᵢ`
  (`Scheme.nonempty_etaleYoneda_sigma_iso`), which is finite over `∐ Wᵢ` if the `Xᵢ` are.

These are the steps of the proof that locally constant sheaves with finite values are
representable (SGA 4 IX 2.2), which is completed with descent in
`SGA.SGA1.ExposeXIII.LocallyConstantSheaves`.

## References

* [SGA 4, Exposé IX, 2.2][sga4]
-/

universe u

open CategoryTheory Limits Opposite

-- See the comment in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

section Points

variable {S S' : Scheme.{u}} (e : S' ⟶ S) [Etale e] {G : Sheaf S.smallEtaleTopology (Type u)}
  {Y : S'.Etale} (φ : (etaleYoneda S').obj Y ≅ (etaleRestrict e).obj G)

/-- An isomorphism `yoneda Y ≅ e^! G` identifies the `T`-points of `Y` with the sections of `G`
over `T`. -/
noncomputable def etaleRepresentsEquiv (T : S'.Etale) :
    (T ⟶ Y) ≃ G.obj.obj (op ((Etale.map e).obj T)) where
  toFun u := φ.hom.hom.app (op T) u
  invFun x := φ.inv.hom.app (op T) x
  left_inv u := by
    change (φ.hom ≫ φ.inv).hom.app (op T) u = u
    rw [φ.hom_inv_id]
    rfl
  right_inv x := by
    change (φ.inv ≫ φ.hom).hom.app (op T) x = x
    rw [φ.inv_hom_id]
    rfl

lemma etaleRepresentsEquiv_comp {T₁ T₂ : S'.Etale} (h : T₁ ⟶ T₂) (u : T₂ ⟶ Y) :
    etaleRepresentsEquiv e φ T₁ (h ≫ u) =
      G.obj.map ((Etale.map e).map h).op (etaleRepresentsEquiv e φ T₂ u) :=
  ConcreteCategory.congr_hom (φ.hom.hom.naturality h.op) u

lemma etaleRepresentsEquiv_apply {T : S'.Etale} (u : T ⟶ Y) :
    etaleRepresentsEquiv e φ T u =
      G.obj.map ((Etale.map e).map u).op (etaleRepresentsEquiv e φ Y (𝟙 Y)) := by
  rw [← etaleRepresentsEquiv_comp, Category.comp_id]

section Cartesian

variable {e φ} {Z : S.Etale} (κ : (Etale.map e).obj Y ⟶ Z)
  (hκ : IsPullback κ.left Y.hom Z.hom e) {s : G.obj.obj (op Z)}
  (hs : G.obj.map κ.op s = etaleRepresentsEquiv e φ Y (𝟙 Y))

include hs in
lemma map_map_comp_apply {T : S'.Etale} (w : T ⟶ Y) :
    G.obj.map ((Etale.map e).map w ≫ κ).op s = etaleRepresentsEquiv e φ T w := by
  rw [etaleRepresentsEquiv_apply, ← hs, op_comp, Functor.map_comp_apply]

/-- The lift of `u : T ⟶ Z` (over `S`) to `T ⟶ Y` (over `S'`), for a cartesian `κ`. -/
noncomputable def cartesianLift {T : S'.Etale} (u : (Etale.map e).obj T ⟶ Z) : T ⟶ Y :=
  MorphismProperty.Over.homMk (hκ.lift u.left T.hom (MorphismProperty.Over.w u)) (by simp) trivial

lemma map_cartesianLift_comp {T : S'.Etale} (u : (Etale.map e).obj T ⟶ Z) :
    (Etale.map e).map (cartesianLift κ hκ u) ≫ κ = u :=
  MorphismProperty.Over.Hom.ext (hκ.lift_fst _ _ _)

include hκ hs in
lemma bijective_map_apply (T : S'.Etale) :
    Function.Bijective (fun u : (Etale.map e).obj T ⟶ Z ↦ G.obj.map u.op s) := by
  have key (u : (Etale.map e).obj T ⟶ Z) :
      G.obj.map u.op s = etaleRepresentsEquiv e φ T (cartesianLift κ hκ u) := by
    conv_lhs => rw [← map_cartesianLift_comp κ hκ u]
    exact map_map_comp_apply κ hs _
  refine ⟨fun u₁ u₂ h ↦ ?_, fun x ↦ ⟨(Etale.map e).map ((etaleRepresentsEquiv e φ T).symm x) ≫ κ,
    by simp only [map_map_comp_apply κ hs, Equiv.apply_symm_apply]⟩⟩
  simp only [key] at h
  rw [← map_cartesianLift_comp κ hκ u₁, ← map_cartesianLift_comp κ hκ u₂,
    (etaleRepresentsEquiv e φ T).injective h]

include hκ hs in
/-- If `yoneda Y ≅ e^! G` and `κ : Y ⟶ Z` is cartesian over `e`, a section `s` of `G` over `Z`
restricting to the universal section of `Y` gives an isomorphism `e^! (yoneda Z) ≅ e^! G`. -/
lemma isIso_etaleRestrict_map_yonedaEquiv_symm :
    IsIso ((etaleRestrict e).map (S.smallEtaleTopology.yonedaEquiv.symm s)) := by
  have : IsIso ((sheafToPresheaf _ _).map
      ((etaleRestrict e).map (S.smallEtaleTopology.yonedaEquiv.symm s))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨T⟩
    rw [isIso_iff_bijective]
    exact bijective_map_apply κ hκ hs T
  exact isIso_of_fully_faithful (sheafToPresheaf _ _) _

end Cartesian

end Points

variable {S : Scheme.{u}}

/-- A morphism of étale sheaves of sets is an isomorphism as soon as its restrictions along a
jointly surjective family of étale morphisms are. -/
lemma isIso_of_forall_isIso_etaleRestrict {ι : Type*} {V : ι → Scheme.{u}} (f : ∀ i, V i ⟶ S)
    [∀ i, Etale (f i)] (hf : ∀ x : S, ∃ i v, f i v = x) {A B : Sheaf S.smallEtaleTopology (Type u)}
    (ψ : A ⟶ B) (h : ∀ i, IsIso ((etaleRestrict (f i)).map ψ)) : IsIso ψ :=
  isIso_of_forall_isIso_etalePullback f hf ψ fun i ↦
    (NatIso.isIso_map_iff (etalePullbackIsoRestrict (f i)) ψ).mpr (h i)

/-- Two sections of an étale sheaf over an object with empty underlying scheme agree. -/
lemma subsingleton_obj_of_isEmpty (G : Sheaf S.smallEtaleTopology (Type u)) {Z : S.Etale}
    [IsEmpty Z.left] : Subsingleton (G.obj.obj (op Z)) :=
  ⟨fun _ _ ↦ (((isSheaf_iff_isSheaf_of_type _ _).1 G.property) _
    (mem_smallEtaleTopology_of_isEmpty S (⊥ : Sieve Z))).isSeparatedFor.ext
      fun _ _ h ↦ h.elim⟩

section Sigma

variable {ι : Type u} {X W : ι → Scheme.{u}} (f : ∀ i, X i ⟶ W i)

lemma isPullback_sigmaι_sigmaMap (i : ι) :
    IsPullback (Sigma.ι X i) (f i) (Limits.Sigma.map f) (Sigma.ι W i) := by
  refine (IsOpenImmersion.isPullback _ _ _ _ (Sigma.ι_map f i) ?_).flip
  ext x
  obtain ⟨⟨j, y⟩, rfl⟩ := (sigmaMk X).surjective x
  rw [sigmaMk_mk]
  constructor
  · rintro ⟨z, hz⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_map, Scheme.Hom.comp_apply, sigmaι_eq_iff] at hz
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 hz
    exact ⟨y, rfl⟩
  · rintro ⟨z, hz⟩
    rw [sigmaι_eq_iff] at hz
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 hz
    exact ⟨f i y, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Sigma.ι_map]⟩

instance [∀ i, Etale (f i)] : Etale (Limits.Sigma.map f) :=
  IsZariskiLocalAtSource.of_openCover (sigmaOpenCover X) fun i ↦ by
    change Etale (Sigma.ι X i ≫ Limits.Sigma.map f)
    rw [Sigma.ι_map]
    infer_instance

instance [∀ i, IsFinite (f i)] : IsFinite (Limits.Sigma.map f) :=
  IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover W) fun i ↦ by
    have h := isPullback_sigmaι_sigmaMap f i
    change IsFinite (pullback.snd (Limits.Sigma.map f) (Sigma.ι W i))
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite h.isoPullback.hom,
      h.isoPullback_hom_snd]
    infer_instance

end Sigma

section Coproduct

variable {ι : Type u} (W : ι → Scheme.{u}) (X : ∀ i, (W i).Etale)

/-- The étale `∐ Wᵢ`-scheme `∐ Xᵢ`, for étale `Wᵢ`-schemes `Xᵢ`. -/
noncomputable def Etale.sigma : (∐ W).Etale :=
  Etale.mk (Limits.Sigma.map fun i ↦ (X i).hom)

/-- The inclusion of `Xᵢ` into `∐ Xᵢ`, over `Wᵢ ⟶ ∐ Wᵢ`. -/
noncomputable def Etale.sigmaι (i : ι) : (Etale.map (Sigma.ι W i)).obj (X i) ⟶ Etale.sigma W X :=
  MorphismProperty.Over.homMk (Sigma.ι (fun i ↦ (X i).left) i)
    (Sigma.ι_map (fun i ↦ (X i).hom) i) trivial

lemma Etale.sigmaι_left (i : ι) :
    (Etale.sigmaι W X i).left = Sigma.ι (fun i ↦ (X i).left) i :=
  rfl

lemma isPullback_etaleSigmaι (i : ι) :
    IsPullback (Etale.sigmaι W X i).left (X i).hom (Etale.sigma W X).hom (Sigma.ι W i) :=
  isPullback_sigmaι_sigmaMap (fun i ↦ (X i).hom) i

instance [∀ i, IsFinite (X i).hom] : IsFinite (Etale.sigma W X).hom :=
  inferInstanceAs (IsFinite (Limits.Sigma.map fun i ↦ (X i).hom))

lemma exists_iff_sigmaι (x : (Etale.sigma W X).left) :
    ∃ i y, (Etale.sigmaι W X i).left y = x := by
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk fun i ↦ (X i).left).surjective x
  refine ⟨i, y, ?_⟩
  rw [sigmaMk_mk]
  rfl

variable {W X} {G : Sheaf (∐ W).smallEtaleTopology (Type u)}
  (φ : ∀ i, (etaleYoneda (W i)).obj (X i) ≅ (etaleRestrict (Sigma.ι W i)).obj G)

lemma exists_section_sigma : ∃ t : G.obj.obj (op (Etale.sigma W X)), ∀ i,
    G.obj.map (Etale.sigmaι W X i).op t = etaleRepresentsEquiv _ (φ i) _ (𝟙 (X i)) := by
  have hG := (isSheaf_iff_isSheaf_of_type _ _).1 G.property
  have hcov : Sieve.ofArrows _ (Etale.sigmaι W X) ∈ (∐ W).smallEtaleTopology _ := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun x ↦ by
      obtain ⟨i, y, hy⟩ := exists_iff_sigmaι W X x
      exact Set.mem_iUnion.2 ⟨i, y, hy⟩
  have hS := (Presieve.isSheafFor_iff_generate _).2 (hG _ hcov)
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hS
    (fun i ↦ etaleRepresentsEquiv _ (φ i) _ (𝟙 (X i))) (fun i j Z gi gj h ↦ by
      have h' : gi.left ≫ Sigma.ι (fun i ↦ (X i).left) i =
          gj.left ≫ Sigma.ι (fun i ↦ (X i).left) j :=
        congrArg (fun k ↦ k.left) h
      by_cases hij : i = j
      · subst hij
        have : gi = gj := MorphismProperty.Over.Hom.ext ((cancel_mono _).1 h')
        rw [this]
      · have : IsEmpty Z.left := isEmpty_of_commSq_sigmaι_of_ne ⟨h'⟩ hij
        exact (subsingleton_obj_of_isEmpty G).elim _ _)
  exact ⟨t, ht⟩

omit φ in
lemma exists_sigmaι_eq (x : (∐ W : Scheme.{u})) : ∃ i v, Sigma.ι W i v = x := by
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk W).surjective x
  exact ⟨i, y, (sigmaMk_mk W i y).symm⟩

include φ in
/-- If each `Xᵢ` represents the restriction of `G` to `Wᵢ`, then `∐ Xᵢ` represents `G` on
`∐ Wᵢ`. -/
theorem nonempty_etaleYoneda_sigma_iso :
    Nonempty ((etaleYoneda (∐ W)).obj (Etale.sigma W X) ≅ G) := by
  obtain ⟨t, ht⟩ := exists_section_sigma φ
  have : IsIso ((∐ W).smallEtaleTopology.yonedaEquiv.symm t) :=
    isIso_of_forall_isIso_etaleRestrict (Sigma.ι W) exists_sigmaι_eq _ fun i ↦
      isIso_etaleRestrict_map_yonedaEquiv_symm (φ := φ i) (Etale.sigmaι W X i)
        (isPullback_etaleSigmaι W X i) (ht i)
  exact ⟨asIso ((∐ W).smallEtaleTopology.yonedaEquiv.symm t)⟩

end Coproduct

end AlgebraicGeometry.Scheme
