/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Limits.FiniteEtale
import SGA.Foundations.Limits.PropertiesLimit

/-!
# Descending properties over a limit: reduction to affine diagrams

For a property `P` of morphisms which is local on the target and stable under base change,
EGA IV 8.10.5 for `P` (`Scheme.LimitDescendsStatement P`) follows from the case of diagrams of
affine schemes (`Scheme.LimitDescendsAffineStatement P`): cover a member of the diagram by finitely
many affine opens `V` and work with the restricted diagrams `k ↦ E k ×_{E j} V`
(`Scheme.limitDescends_of_affine`).

* `CategoryTheory.IsPullback.resLE`: restricting a cartesian square of schemes to an open of the
  base gives a cartesian square.

## References

* [EGA IV₃, 8.10.5][EGA4]
* [Stacks Project, Limits of schemes, Section 32.8][stacks]
-/

universe u

open CategoryTheory Limits

namespace CategoryTheory.IsPullback

open AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a cartesian square `P = X ×_S W` to an open `V ⊆ S` and an open `W' ⊆ W` mapping
into `V`: `h⁻¹(W') = f⁻¹(V) ×_V W'`. -/
lemma resLE {P X W S : Scheme.{u}} {e : P ⟶ X} {h : P ⟶ W} {f : X ⟶ S} {g : W ⟶ S}
    (H : IsPullback e h f g) (V : S.Opens) (W' : W.Opens) (hW : W' ≤ g ⁻¹ᵁ V) :
    IsPullback (e.resLE (f ⁻¹ᵁ V) (h ⁻¹ᵁ W') (fun x hx ↦ by
        change f (e x) ∈ V
        rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
        exact hW hx))
      (h ∣_ W') (f ∣_ V) (g.resLE V W' hW) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict f V).flip
  · rw [Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι]
    exact (isPullback_morphismRestrict h W').flip.paste_horiz H
  · rw [← cancel_mono V.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.resLE_comp_ι_assoc, H.w]
    rw [morphismRestrict_ι_assoc]

end CategoryTheory.IsPullback

namespace AlgebraicGeometry

/-- EGA IV 8.10.5 for a property `P` over diagrams of affine schemes: as
`Scheme.LimitDescendsStatement P`, with every member `E i` of the diagram affine. -/
def Scheme.LimitDescendsAffineStatement (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ ⦃I : Type u⦄ [Category.{u} I] [IsCofiltered I] (E : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, IsAffine (E.obj i)] (c : Cone E)
    (_ : IsLimit c) ⦃j : I⦄ ⦃X Xj : Scheme.{u}⦄ (qj : Xj ⟶ E.obj j)
    [LocallyOfFinitePresentation qj] [QuasiCompact qj] [QuasiSeparated qj] (e : X ⟶ Xj)
    (q : X ⟶ c.pt), IsPullback e q qj (c.π.app j) → P q →
      ∃ (k : I) (g : k ⟶ j), P (pullback.snd qj (E.map g))

/-- A base change of a morphism with a property `P` stable under base change, along a further
morphism, has `P`: `X ×_S T' ⟶ T'` is a base change of `X ×_S T ⟶ T` along `T' ⟶ T`. -/
lemma Scheme.pullback_snd_comp_of_isStableUnderBaseChange {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] {X S T T' : Scheme.{u}} (q : X ⟶ S) (a : T' ⟶ T) (b : T ⟶ S)
    (h : P (pullback.snd q b)) : P (pullback.snd q (a ≫ b)) :=
  MorphismProperty.of_isPullback (IsPullback.of_right' (IsPullback.of_hasPullback q (a ≫ b))
    (IsPullback.of_hasPullback q b)) h

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5 for a property local on the target and stable under base change reduces to
diagrams of affine schemes. -/
theorem Scheme.limitDescends_of_affine {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange]
    (H : Scheme.LimitDescendsAffineStatement.{u} P) : Scheme.LimitDescendsStatement.{u} P := by
  intro I _ _ E _ _ _ c hc j X Xj qj _ _ _ e q h hq
  classical
  -- for each affine open `V` of `E j`, a level below which `P` holds over `V`
  have key (V : (E.obj j).affineOpens) : ∃ k : Over j, ∀ (m : Over j), (m ⟶ k) →
      P (pullback.snd qj (E.map m.hom) ∣_ (E.map m.hom ⁻¹ᵁ (V : (E.obj j).Opens))) := by
    let D := opensDiagram E j V
    have hDa (l : Over j) : IsAffine (D.obj l) := V.2.preimage (E.map l.hom)
    let o : Over j := Over.mk (𝟙 j)
    have hV : (c.π.app j ⁻¹ᵁ (V : (E.obj j).Opens)) ≤ c.π.app j ⁻¹ᵁ (E.map o.hom ⁻¹ᵁ V) := by
      intro x hx
      change E.map (𝟙 j) (c.π.app j x) ∈ (V : (E.obj j).Opens)
      simpa using hx
    have sq := h.resLE (E.map o.hom ⁻¹ᵁ V) (c.π.app j ⁻¹ᵁ (V : (E.obj j).Opens)) hV
    obtain ⟨l, f, hf⟩ := H D (opensCone E c j V) (isLimitOpensCone E c hc j V) (j := o)
      (qj ∣_ (E.map o.hom ⁻¹ᵁ V)) _ _ sq (IsZariskiLocalAtTarget.restrict hq _)
    refine ⟨l, fun m ψ ↦ ?_⟩
    have h1 := Scheme.pullback_snd_comp_of_isStableUnderBaseChange (qj ∣_ (E.map o.hom ⁻¹ᵁ V))
      (D.map ψ) (D.map f) hf
    rw [← D.map_comp] at h1
    -- `qj` restricted over `D.obj m` is a base change of `qj ∣_ (E.map o.hom ⁻¹ᵁ V)`
    have hm : (ψ ≫ f).left = m.hom := by simpa [o] using Over.w (ψ ≫ f)
    have hle : E.map m.hom ⁻¹ᵁ (V : (E.obj j).Opens) ≤ E.map m.hom ⁻¹ᵁ (E.map o.hom ⁻¹ᵁ V) := by
      intro x hx
      change E.map (𝟙 j) (E.map m.hom x) ∈ (V : (E.obj j).Opens)
      simpa using hx
    have sq' := (IsPullback.of_hasPullback qj (E.map m.hom)).resLE (E.map o.hom ⁻¹ᵁ V)
      (E.map m.hom ⁻¹ᵁ (V : (E.obj j).Opens)) hle
    have e1 : (E.map m.hom).resLE (E.map o.hom ⁻¹ᵁ V) (E.map m.hom ⁻¹ᵁ (V : (E.obj j).Opens)) hle =
        D.map (ψ ≫ f) := by
      rw [← cancel_mono (E.map o.hom ⁻¹ᵁ (V : (E.obj j).Opens)).ι]
      simp [D, hm]
    rw [e1] at sq'
    exact (MorphismProperty.arrow_mk_iso_iff P
      (Arrow.isoMk (sq'.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)) (Iso.refl _)
        (by simp))).mpr h1
  choose k hk using key
  -- a finite affine cover of `E j`
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun V : (E.obj j).affineOpens ↦ ((V : (E.obj j).Opens) : Set (E.obj j)))
    (fun V ↦ (V : (E.obj j).Opens).2) (fun x _ ↦ by
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := (E.obj j).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩)
  obtain ⟨m, fm⟩ := IsCofiltered.inf_objs_exists (S.image k)
  replace fm (V : S) : m ⟶ k V := (@fm (k V) (Finset.mem_image_of_mem k V.2)).some
  refine ⟨m.left, m.hom, IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun V : S ↦ E.map m.hom ⁻¹ᵁ ((V : (E.obj j).affineOpens) : (E.obj j).Opens)) ?_
    fun V ↦ hk V m (fm V)⟩
  rw [← Scheme.Hom.preimage_iSup]
  refine top_le_iff.mp fun x _ ↦ ?_
  have := hS (Set.mem_univ (E.map m.hom x))
  simp only [Set.mem_iUnion] at this
  obtain ⟨V, hVS, hxV⟩ := this
  rw [Scheme.Hom.mem_preimage, TopologicalSpace.Opens.mem_iSup]
  exact ⟨⟨V, hVS⟩, hxV⟩

end AlgebraicGeometry
