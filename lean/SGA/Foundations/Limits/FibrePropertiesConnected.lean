/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Limits.FibrePropertiesConstructible
import SGA.Foundations.Limits.PropertiesLimitSurjective

/-!
# Fibres that are not geometrically connected spread out from the generic point

Half of the generic step of EGA IV 9.7.7 for geometric connectedness: let `A` be a noetherian
domain with generic point `η ∈ Spec A`, and `f : X ⟶ Spec A` of finite type. If the generic fibre
`X_η` is not geometrically connected, then neither is `X_s` for all `s` in a nonempty open subset
of `Spec A` (`AlgebraicGeometry.Scheme.exists_isOpen_forall_not_geometricallyConnected`).

Proof. Some base change `X_K = X ×_A Spec K` to a field `K ⊇ κ(η)` is not connected.
* If `X_K` is empty, then `η ∉ f(X)`, a constructible set (Chevalley), so a neighbourhood of `η`
  misses `f(X)` and the fibres there are empty.
* Otherwise `X_K = U ⊔ V` with `U`, `V` nonempty, open and closed. Write `Spec K` as the limit of
  the `Spec R`, `R ⊆ K` finitely generated over `A` (`Algebra.FGSubalgebra`); then `U`, `V` are the
  preimages of opens `U_R`, `V_R` of `X_R = X ×_A Spec R` which, for `R` large, are disjoint and
  cover `X_R` (EGA IV 8.3.4, `Scheme.exists_preimage_eq_empty_of_isConstructible`). The set `C` of
  points of `Spec R` over which both `U_R` and `V_R` have points is constructible (Chevalley) and
  contains the image of `Spec K`; its image in `Spec A` is constructible and contains `η`, hence
  contains a neighbourhood `W` of `η` (EGA 0_III 9.2.2,
  `Topology.IsConstructible.exists_isOpen_of_isGenericPoint`). For `s ∈ W` and `r ∈ C` over `s`,
  the fibre `X_r = X_s ⊗_{κ(s)} κ(r)` is disconnected, so `X_s` is not geometrically connected.

## References

* [EGA IV₃, 9.7.7][EGA4]
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

/-- If the fibre `f.fiber s` is not connected (for instance empty), the fibre is not
geometrically connected. -/
lemma not_geometricallyConnected_fiberToSpecResidueField_of_not_connectedSpace {X S : Scheme.{u}}
    (f : X ⟶ S) (s : S) (h : ¬ ConnectedSpace (f.fiber s)) :
    ¬ GeometricallyConnected (f.fiberToSpecResidueField s) := fun _ ↦
  h (GeometricallyConnected.connectedSpace_of_subsingleton (f.fiberToSpecResidueField s))

set_option backward.isDefEq.respectTransparency false in
/-- If the fibre of `f` at `s` is not geometrically connected, there are a field `K` and
`y : Spec K ⟶ S` with image `s` such that `X ×_S Spec K` is not connected. -/
lemma exists_isPullback_not_connectedSpace_of_not_geometricallyConnected {X S : Scheme.{u}}
    (f : X ⟶ S) (s : S) (h : ¬ GeometricallyConnected (f.fiberToSpecResidueField s)) :
    ∃ (K : Type u) (_ : Field K) (y : Spec (.of K) ⟶ S) (Z : Scheme.{u}) (e : Z ⟶ X)
      (q : Z ⟶ Spec (.of K)), IsPullback e q f y ∧ (∀ t, y t = s) ∧ ¬ ConnectedSpace Z := by
  rw [geometricallyConnected_iff, geometrically_iff_of_isClosedUnderIsomorphisms] at h
  push Not at h
  obtain ⟨K, _, y, hy⟩ := h
  refine ⟨K, inferInstance, y ≫ S.fromSpecResidueField s, _,
    pullback.fst (f.fiberToSpecResidueField s) y ≫ f.fiberι s,
    pullback.snd (f.fiberToSpecResidueField s) y,
    (IsPullback.of_hasPullback _ y).paste_horiz (IsPullback.of_hasPullback f _), fun t ↦ ?_, hy⟩
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Half of the generic step of EGA IV 9.7.7 for geometric connectedness: let `A` be a noetherian
domain, `η` the generic point of `Spec A` and `f : X ⟶ Spec A` of finite type. If the fibre at `η`
is not geometrically connected, then neither is the fibre at any point of some open neighbourhood
of `η`. -/
theorem Scheme.exists_isOpen_forall_not_geometricallyConnected {A : CommRingCat.{u}}
    [IsNoetherianRing A] [IsDomain A] {X : Scheme.{u}} (f : X ⟶ Spec A) [LocallyOfFiniteType f]
    [QuasiCompact f] {η : Spec A} (hη : IsGenericPoint η Set.univ)
    (h : ¬ GeometricallyConnected (f.fiberToSpecResidueField η)) :
    ∃ U : Set (Spec A), IsOpen U ∧ η ∈ U ∧
      ∀ s ∈ U, ¬ GeometricallyConnected (f.fiberToSpecResidueField s) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨K, _, y, Z, eZ, qZ, hZ, hy, hZc⟩ :=
    exists_isPullback_not_connectedSpace_of_not_geometricallyConnected f η h
  by_cases hne : Nonempty Z
  swap
  · -- `X_K` is empty: `η` is not in the image of `f`
    have hη' : η ∉ Set.range f := by
      rintro ⟨x, hx⟩
      obtain ⟨t⟩ : Nonempty (Spec (.of K)) := inferInstance
      obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := y) x t
        (by rw [hx, hy])
      exact hne ⟨hZ.isoPullback.inv z⟩
    have hC : IsConstructible (Set.range f)ᶜ := by
      have := f.isConstructible_image (s := Set.univ) IsConstructible.univ
      rw [Set.image_univ] at this
      exact this.compl
    obtain ⟨U, hU, hηU, hUE⟩ := hC.exists_isOpen_of_isGenericPoint isClosed_univ hη hη'
    refine ⟨U, hU, hηU, fun s hs ↦ ?_⟩
    apply not_geometricallyConnected_fiberToSpecResidueField_of_not_connectedSpace
    intro hconn
    obtain ⟨p⟩ := hconn.toNonempty
    have hp : f.fiberι s p ∈ f ⁻¹' {s} := f.range_fiberι s ▸ Set.mem_range_self p
    exact hUE ⟨hs, trivial⟩ ⟨f.fiberι s p, hp⟩
  -- `X_K = U ⊔ Uᶜ` with `U` open, closed, nonempty and not everything
  have hpc : ¬ PreconnectedSpace Z := fun h ↦ hZc { toPreconnectedSpace := h, toNonempty := hne }
  rw [preconnectedSpace_iff_clopen] at hpc
  push Not at hpc
  obtain ⟨U, hUc, hU0, hU1⟩ := hpc
  obtain ⟨u, hu⟩ := hU0
  obtain ⟨v, hv⟩ : (Uᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    exact hU1
  -- `Spec K` is the limit of the `Spec R`, `R ⊆ K` finitely generated over `A`
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  algebraize [φ.hom]
  let E := Algebra.FGSubalgebra.schemeDiagram A K
  let c := Algebra.FGSubalgebra.specCone A K
  have hc : IsLimit c := Algebra.FGSubalgebra.isLimitSpecCone A K
  let j₀ : (Algebra.FGSubalgebra A K)ᵒᵖ := Opposite.op ⟨⊥, Subalgebra.fg_bot⟩
  let b₀ : E.obj j₀ ⟶ Spec A :=
    Spec.map (CommRingCat.ofHom (algebraMap A (⊥ : Subalgebra A K)))
  have hb₀ : c.π.app j₀ ≫ b₀ = Spec.map φ := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have hZ' : IsPullback eZ qZ f (c.π.app j₀ ≫ b₀) := by rwa [hb₀]
  let p₀ : pullback f b₀ ⟶ E.obj j₀ := pullback.snd f b₀
  have h₀ : IsPullback (pullback.lift eZ (qZ ≫ c.π.app j₀) (by rw [hZ'.w, Category.assoc]))
      qZ p₀ (c.π.app j₀) :=
    IsPullback.of_right (by rw [pullback.lift_fst]; exact hZ') (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback f b₀)
  let D := Scheme.baseChangeDiagram E p₀
  let cD := Scheme.baseChangeCone (c := c) h₀
  have hcD : IsLimit cD := Scheme.isLimitBaseChangeCone (c := c) hc h₀
  have (k : Over j₀) : CompactSpace (D.obj k) := Scheme.compactSpace_baseChangeDiagram p₀ k
  have (k : Over j₀) : QuasiSeparatedSpace (D.obj k) :=
    Scheme.quasiSeparatedSpace_baseChangeDiagram p₀ k
  have : QuasiCompact qZ := MorphismProperty.of_isPullback hZ inferInstance
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace qZ
  -- `U` and `Uᶜ` come from opens at a finite level
  let U' : Z.Opens := ⟨U, hUc.isOpen⟩
  let V' : Z.Opens := ⟨Uᶜ, hUc.compl.isOpen⟩
  obtain ⟨i₁, U₁, hU₁c, hU₁⟩ :=
    AlgebraicGeometry.exists_preimage_eq D cD hcD U' hUc.isClosed.isCompact
  obtain ⟨i₂, V₂, hV₂c, hV₂⟩ :=
    AlgebraicGeometry.exists_preimage_eq D cD hcD V' hUc.compl.isClosed.isCompact
  let i₃ := IsCofiltered.min i₁ i₂
  let a₁ : i₃ ⟶ i₁ := IsCofiltered.minToLeft i₁ i₂
  let a₂ : i₃ ⟶ i₂ := IsCofiltered.minToRight i₁ i₂
  let U₃ : Set (D.obj i₃) := D.map a₁ ⁻¹' U₁
  let V₃ : Set (D.obj i₃) := D.map a₂ ⁻¹' V₂
  have hU₃ : cD.π.app i₃ ⁻¹' U₃ = U := by
    change (cD.π.app i₃ ≫ D.map a₁) ⁻¹' U₁ = U
    rw [cD.w a₁]
    exact congrArg SetLike.coe hU₁
  have hV₃ : cD.π.app i₃ ⁻¹' V₃ = Uᶜ := by
    change (cD.π.app i₃ ≫ D.map a₂) ⁻¹' V₂ = Uᶜ
    rw [cD.w a₂]
    exact congrArg SetLike.coe hV₂
  have hU₃c : IsConstructible U₃ := (D.map a₁).isConstructible_preimage (hU₁c.isConstructible U₁.2)
  have hV₃c : IsConstructible V₃ := (D.map a₂).isConstructible_preimage (hV₂c.isConstructible V₂.2)
  -- at a lower level they are disjoint and cover (EGA IV 8.3.4)
  have hT : IsConstructible ((U₃ ∩ V₃) ∪ (U₃ ∪ V₃)ᶜ) :=
    (hU₃c.inter hV₃c).union (hU₃c.union hV₃c).compl
  obtain ⟨k, hk⟩ := Scheme.exists_preimage_eq_empty_of_isConstructible hcD hT (by
    rw [Set.preimage_union, Set.preimage_inter, Set.preimage_compl, Set.preimage_union, hU₃, hV₃]
    simp)
  let i₄ := k.left
  let U₄ : Set (D.obj i₄) := D.map k.hom ⁻¹' U₃
  let V₄ : Set (D.obj i₄) := D.map k.hom ⁻¹' V₃
  have hdisj : U₄ ∩ V₄ = ∅ := by
    rw [Set.preimage_union] at hk
    exact Set.subset_eq_empty (Set.subset_union_left) (by rw [← Set.preimage_inter]; exact hk)
  have hcov : U₄ ∪ V₄ = Set.univ := by
    rw [Set.preimage_union, Set.union_empty_iff, Set.preimage_compl, Set.compl_empty_iff,
      Set.preimage_union] at hk
    exact hk.2
  -- the set `C ⊆ Spec R` over which both `U₄` and `V₄` have points, and its image in `Spec A`
  let q₄ : D.obj i₄ ⟶ E.obj i₄.left := pullback.snd p₀ (E.map i₄.hom)
  let β : E.obj i₄.left ⟶ Spec A := E.map i₄.hom ≫ b₀
  have hβ : β = Spec.map (CommRingCat.ofHom (algebraMap A i₄.left.unop.1)) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have : LocallyOfFiniteType β := by
    rw [hβ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    have : Algebra.FiniteType A i₄.left.unop.1 :=
      (Subalgebra.fg_iff_finiteType _).mp i₄.left.unop.2
    exact RingHom.finiteType_algebraMap.mpr this
  have : QuasiCompact β := inferInstance
  have hU₄c : IsConstructible U₄ := (D.map k.hom).isConstructible_preimage hU₃c
  have hV₄c : IsConstructible V₄ := (D.map k.hom).isConstructible_preimage hV₃c
  let C : Set (E.obj i₄.left) := q₄ '' U₄ ∩ q₄ '' V₄
  have hC : IsConstructible C :=
    (q₄.isConstructible_image hU₄c).inter (q₄.isConstructible_image hV₄c)
  have hW' : IsConstructible (β '' C) := β.isConstructible_image hC
  -- `η` lies in the image of `C`
  let π₃ : Z ⟶ D.obj i₃ := cD.π.app i₃
  let π₄ : Z ⟶ D.obj i₄ := cD.π.app i₄
  have hπ₄ : π₄ ≫ q₄ = qZ ≫ c.π.app i₄.left := by
    simp only [π₄, cD, q₄, Scheme.baseChangeCone_π_app]
    exact pullback.lift_snd _ _ _
  have hw : π₄ ≫ D.map k.hom = π₃ := cD.w k.hom
  have hU₃' : π₃ ⁻¹' U₃ = U := hU₃
  have hV₃' : π₃ ⁻¹' V₃ = Uᶜ := hV₃
  have hU₄ : π₄ ⁻¹' U₄ = U := by
    change (π₄ ≫ D.map k.hom) ⁻¹' U₃ = U
    rw [hw, hU₃']
  have hV₄ : π₄ ⁻¹' V₄ = Uᶜ := by
    change (π₄ ≫ D.map k.hom) ⁻¹' V₃ = Uᶜ
    rw [hw, hV₃']
  have hu₄ : π₄ u ∈ U₄ := by
    rw [← Set.mem_preimage, hU₄]
    exact hu
  have hv₄ : π₄ v ∈ V₄ := by
    rw [← Set.mem_preimage, hV₄]
    exact hv
  have hξ : q₄ (π₄ v) = q₄ (π₄ u) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hπ₄, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact congrArg _ (Subsingleton.elim _ _)
  have hηW : η ∈ β '' C := by
    refine ⟨q₄ (π₄ u), ⟨⟨_, hu₄, rfl⟩, ⟨_, hv₄, hξ⟩⟩, ?_⟩
    have e : π₄ ≫ q₄ ≫ β = qZ ≫ Spec.map φ := by
      have hw' : c.π.app i₄.left ≫ E.map i₄.hom = c.π.app j₀ := c.w i₄.hom
      rw [← Category.assoc, hπ₄, Category.assoc, show β = E.map i₄.hom ≫ b₀ from rfl,
        ← Category.assoc (c.π.app i₄.left), hw', hb₀]
    have := congrArg (fun g ↦ g u) e
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, hy]
  obtain ⟨W, hWo, hηW', hWsub⟩ := hW'.exists_isOpen_of_isGenericPoint isClosed_univ hη hηW
  refine ⟨W, hWo, hηW', fun s hs ↦ ?_⟩
  obtain ⟨r, ⟨⟨u', hu', hur⟩, ⟨v', hv', hvr⟩⟩, rfl⟩ := hWsub ⟨hs, trivial⟩
  -- the fibre of `q₄` at `r` is not connected
  have hU₄o : IsOpen U₄ :=
    (U₁.2.preimage (D.map a₁).continuous).preimage (D.map k.hom).continuous
  have hV₄o : IsOpen V₄ :=
    (V₂.2.preimage (D.map a₂).continuous).preimage (D.map k.hom).continuous
  have hdisc : ¬ ConnectedSpace (q₄.fiber r) := by
    intro hconn
    let P : Set (q₄.fiber r) := q₄.fiberι r ⁻¹' U₄
    have hPo : IsOpen P := hU₄o.preimage (q₄.fiberι r).continuous
    have hPc : IsClosed P := by
      have hUV : U₄ᶜ = V₄ := by
        ext x
        refine ⟨fun hx ↦ ?_, fun hx hxU ↦ ?_⟩
        · have : x ∈ U₄ ∪ V₄ := hcov ▸ trivial
          exact this.resolve_left hx
        · have : x ∈ U₄ ∩ V₄ := ⟨hxU, hx⟩
          rw [hdisj] at this
          exact this
      have : Pᶜ = q₄.fiberι r ⁻¹' V₄ := by
        rw [← Set.preimage_compl, hUV]
      exact isOpen_compl_iff.mp (this ▸ hV₄o.preimage (q₄.fiberι r).continuous)
    have hu'f : u' ∈ Set.range (q₄.fiberι r) := by
      rw [q₄.range_fiberι]
      exact hur
    have hv'f : v' ∈ Set.range (q₄.fiberι r) := by
      rw [q₄.range_fiberι]
      exact hvr
    obtain ⟨pu, hpu⟩ := hu'f
    obtain ⟨pv, hpv⟩ := hv'f
    rcases isClopen_iff.mp ⟨hPc, hPo⟩ with hP | hP
    · have : pu ∈ P := by
        change q₄.fiberι r pu ∈ U₄
        rw [hpu]
        exact hu'
      rw [hP] at this
      exact this
    · have : pv ∈ P := by rw [hP]; trivial
      have h1 : v' ∈ U₄ := by
        rw [← hpv]
        exact this
      have h2 : v' ∈ U₄ ∩ V₄ := ⟨h1, hv'⟩
      rw [hdisj] at h2
      exact h2
  have sq : IsPullback (pullback.fst p₀ (E.map i₄.hom) ≫ pullback.fst f b₀) q₄ f β :=
    (IsPullback.of_hasPullback p₀ (E.map i₄.hom)).paste_horiz (IsPullback.of_hasPullback f b₀)
  exact fun hgc ↦ not_geometricallyConnected_fiberToSpecResidueField_of_not_connectedSpace q₄ r
    hdisc ((geometricallyConnected_fiberToSpecResidueField_iff_of_isPullback sq r).mpr hgc)

end AlgebraicGeometry
