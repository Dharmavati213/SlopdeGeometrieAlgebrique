/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.SteinFactorization
import SGA.Foundations.HenselianFinite

/-!
# Proper schemes over a henselian local ring: clopen subsets of the closed fibre

Let `A` be a local ring with closed point `m` and `q : Z ⟶ Spec A` universally closed.

* `AlgebraicGeometry.eq_empty_of_isClosed_of_forall_ne_closedPoint`: a closed subset of `Z` which
  does not meet the closed fibre `q⁻¹(m)` is empty (its image is closed in `Spec A`, and every
  nonempty closed subset of `Spec A` contains `m`).
* `AlgebraicGeometry.eq_of_comp_eq_of_isPullback_closedFibre`: hence two morphisms from `Z` into a
  separated étale scheme agree as soon as they agree on the closed fibre.

Let moreover `A` be noetherian and henselian and `q` proper.

* `AlgebraicGeometry.exists_isClopen_inter_eq_of_henselianLocalRing`: every subset of the closed
  fibre which is closed in `Z` and open in the closed fibre is the trace of a clopen subset of `Z`;
* `AlgebraicGeometry.exists_isClopen_preimage_closedFibre_of_henselianLocalRing`: equivalently,
  every clopen subset of the scheme-theoretic closed fibre `Z₀ = Z ×_A κ` is the preimage of a
  clopen subset of `Z`. This is the henselian analogue of
  `AlgebraicGeometry.existsUnique_isClopen_preimage_closedFibre` (complete `A`).

The proof uses the Stein factorization `Z ⟶ Z' ⟶ Spec A` (`steinFactorizationStatement`, `A`
noetherian): `Z' ⟶ Spec A` is finite, so the points of its closed fibre have clopen neighbourhoods
separating them (`AlgebraicGeometry.exists_isClopen_of_isFinite`, `A` henselian), and the fibres of
`Z ⟶ Z'` are connected.

## References

* [Stacks Project, Tag 0A0B](https://stacks.math.columbia.edu/tag/0A0B)
* [EGA IV, 18.5.19][ega-iv-4]
-/

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry

/-- A closed subset of a scheme universally closed over a local ring which does not meet the closed
fibre is empty. -/
lemma eq_empty_of_isClosed_of_forall_ne_closedPoint {A : CommRingCat.{u}} [IsLocalRing A]
    {Z : Scheme.{u}} (q : Z ⟶ Spec A) [UniversallyClosed q] {T : Set Z} (hT : IsClosed T)
    (h : ∀ z ∈ T, q z ≠ closedPoint A) : T = ∅ := by
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hc : IsClosed (q '' T) := q.isClosedMap T hT
  have : closedPoint A ∈ q '' T :=
    (specializes_closedPoint (q z)).mem_closed hc ⟨z, hz, rfl⟩
  obtain ⟨z', hz', hz'm⟩ := this
  exact h z' hz' hz'm

/-- The image of the closed fibre `Z₀ = Z ×_A κ` of `q : Z ⟶ Spec A` (any cartesian square) is
`q⁻¹(m)`. -/
lemma range_eq_preimage_closedPoint_of_isPullback {A : CommRingCat.{u}} [IsLocalRing A]
    {Z Z₀ : Scheme.{u}} {q : Z ⟶ Spec A} {ι : Z₀ ⟶ Z}
    {q₀ : Z₀ ⟶ Spec (.of (ResidueField A))}
    (h : IsPullback ι q₀ q (Spec.map (CommRingCat.ofHom (residue A)))) :
    Set.range ι = q ⁻¹' {closedPoint A} := by
  have : IsLocalHom (CommRingCat.ofHom (residue A)).hom := inferInstanceAs (IsLocalHom (residue A))
  ext z
  constructor
  · rintro ⟨z₀, rfl⟩
    change q (ι z₀) = closedPoint A
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply,
      Subsingleton.elim (q₀ z₀) (closedPoint _)]
    exact Spec_closedPoint
  · intro hz
    obtain ⟨z₀, hz₀, -⟩ := Scheme.exists_preimage_of_isPullback h z (closedPoint _)
      (by rw [Spec_closedPoint]; exact hz)
    exact ⟨z₀, hz₀⟩

-- `simp` needs to see through `Scheme.Etale` objects, as in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false in
/-- Two morphisms `a b : P ⟶ E` over `X` into a separated étale `X`-scheme agree if they agree on
the closed fibre `P₀ = P ×_A κ` of `P`, for `P` universally closed over a local ring `A`: the
locus where they differ is closed (`E` separated) and misses the closed fibre (it is open, since
the diagonal of `E` is an open immersion). -/
theorem eq_of_comp_eq_of_isPullback_closedFibre {A : CommRingCat.{u}} [IsLocalRing A]
    {P P₀ X : Scheme.{u}} {p : P ⟶ Spec A} [UniversallyClosed p] {ι : P₀ ⟶ P}
    {q₀ : P₀ ⟶ Spec (.of (ResidueField A))}
    (h : IsPullback ι q₀ p (Spec.map (CommRingCat.ofHom (residue A)))) (E : X.Etale)
    [IsSeparated E.hom] (a b : P ⟶ E.left) (hab : a ≫ E.hom = b ≫ E.hom) (hι : ι ≫ a = ι ≫ b) :
    a = b := by
  let d := pullback.lift a b hab
  have hT := eq_empty_of_isClosed_of_forall_ne_closedPoint p
    ((pullback.diagonal E.hom).isOpenEmbedding.isOpen_range.preimage d.continuous).isClosed_compl
    fun x hx hxm ↦ by
      obtain ⟨x₀, rfl⟩ := (range_eq_preimage_closedPoint_of_isPullback h).ge hxm
      refine hx ⟨(ι ≫ a) x₀, ?_⟩
      have e : (ι ≫ a) ≫ pullback.diagonal E.hom = ι ≫ d := by
        apply pullback.hom_ext <;> simp [d, hι]
      have := congrArg (fun φ ↦ φ x₀) e
      simp only [Scheme.Hom.comp_apply] at this ⊢
      exact this
  have hd : Set.range d ⊆ Set.range (pullback.diagonal E.hom) := by
    rintro _ ⟨x, rfl⟩
    by_contra hx
    have : x ∈ (d ⁻¹' Set.range (pullback.diagonal E.hom))ᶜ := hx
    rw [hT] at this
    exact this
  have hl := IsOpenImmersion.lift_fac (pullback.diagonal E.hom) d hd
  have ha := congrArg (· ≫ pullback.fst E.hom E.hom) hl
  have hb := congrArg (· ≫ pullback.snd E.hom E.hom) hl
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    d, pullback.lift_fst, pullback.lift_snd] at ha hb
  rw [← ha, hb]

variable {A : CommRingCat.{u}} [HenselianLocalRing A] [IsNoetherianRing A] {Z : Scheme.{u}}
  (q : Z ⟶ Spec A) [IsProper q]

/-- **Clopen subsets lift from the closed fibre over a noetherian henselian local ring**: a subset
`V` of the closed fibre `q⁻¹(m)` of a proper `q : Z ⟶ Spec A`, closed in `Z` and open in
`q⁻¹(m)`, is the trace on `q⁻¹(m)` of a clopen subset of `Z`. -/
theorem exists_isClopen_inter_eq_of_henselianLocalRing (V : Set Z)
    (hV : V ⊆ q ⁻¹' {closedPoint A}) (hVc : IsClosed V) (O : Set Z) (hO : IsOpen O)
    (hOV : O ∩ q ⁻¹' {closedPoint A} = V) :
    ∃ U : Set Z, IsClopen U ∧ U ∩ q ⁻¹' {closedPoint A} = V := by
  classical
  obtain ⟨Z', g, h, -, hh, hgh, -, hconn⟩ := steinFactorizationStatement Z (Spec A) q
  have hpre (b : Z') : _root_.IsPreconnected (g ⁻¹' {b}) := by
    rw [← g.range_fiberι b]
    exact isPreconnected_range (g.fiberι b).continuous
  let F : Set Z' := h ⁻¹' {closedPoint A}
  have hF : F.Finite := h.finite_preimage_singleton _
  have : Finite F := hF.to_subtype
  choose W hW using fun b : F ↦ exists_isClopen_of_isFinite h b.1 b.2
  let S : Set F := {b | g ⁻¹' {b.1} ⊆ V}
  let U' : Set Z' := ⋃ b ∈ S.toFinite.toFinset, W b
  have hU' : IsClopen U' := isClopen_biUnion_finset fun b _ ↦ (hW b).1
  have hqm : IsClosed (q ⁻¹' {closedPoint A}) :=
    (isClosed_singleton_closedPoint A).preimage q.continuous
  refine ⟨g ⁻¹' U', hU'.preimage g.continuous, Set.Subset.antisymm ?_ fun z hz ↦ ?_⟩
  · rintro z ⟨hzU, hzm⟩
    obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.mp hzU
    rw [Set.Finite.mem_toFinset] at hb
    have hgz : h (g z) = closedPoint A := by
      rw [← Scheme.Hom.comp_apply, hgh]
      exact hzm
    have := (hW b).2.2 (g z) hzb hgz
    exact hb (show z ∈ g ⁻¹' {b.1} from this)
  · have hzm : q z = closedPoint A := hV hz
    have hgz : g z ∈ F := by
      change h (g z) = closedPoint A
      rw [← Scheme.Hom.comp_apply, hgh]
      exact hzm
    let b : F := ⟨g z, hgz⟩
    have hsub : g ⁻¹' {g z} ⊆ q ⁻¹' {closedPoint A} := fun z' hz' ↦ by
      change q z' = closedPoint A
      rw [← hgh, Scheme.Hom.comp_apply]
      exact (congrArg h hz').trans hgz
    have hbS : b ∈ S := by
      have hcover : g ⁻¹' {g z} ⊆ V ∪ (Oᶜ ∩ q ⁻¹' {closedPoint A}) := fun z' hz' ↦ by
        by_cases hO' : z' ∈ O
        · exact Or.inl (hOV ▸ ⟨hO', hsub hz'⟩)
        · exact Or.inr ⟨hO', hsub hz'⟩
      have hdisj : g ⁻¹' {g z} ∩ (V ∩ (Oᶜ ∩ q ⁻¹' {closedPoint A})) = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun z' ⟨_, hz'V, hz'O, _⟩ ↦ hz'O ?_
        rw [← hOV] at hz'V
        exact hz'V.1
      rcases (isPreconnected_iff_subset_of_disjoint_closed.mp (hpre (g z))) V
          (Oᶜ ∩ q ⁻¹' {closedPoint A}) hVc (hO.isClosed_compl.inter hqm) hcover hdisj with
        hV' | hV'
      · exact hV'
      · exact absurd (hOV ▸ hz).1 (hV' rfl).1
    exact ⟨Set.mem_iUnion₂.mpr ⟨b, (Set.Finite.mem_toFinset _).mpr hbS, (hW b).2.1⟩, hzm⟩

/-- **Clopen subsets of the closed fibre lift over a noetherian henselian local ring** (henselian
analogue of `existsUnique_isClopen_preimage_closedFibre`): for `q : Z ⟶ Spec A` proper, every
clopen subset of the closed fibre `Z₀ = Z ×_A κ` is the preimage of a clopen subset of `Z`. -/
theorem exists_isClopen_preimage_closedFibre_of_henselianLocalRing
    (V₀ : Set ↥(pullback q (Spec.map (CommRingCat.ofHom (residue A)))))
    (hV₀ : IsClopen V₀) :
    ∃ U : Set Z, IsClopen U ∧
      pullback.fst q (Spec.map (CommRingCat.ofHom (residue A))) ⁻¹' U = V₀ := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (residue A))) :=
    IsClosedImmersion.spec_of_surjective _ residue_surjective
  let ι := pullback.fst q (Spec.map (CommRingCat.ofHom (residue A)))
  have hι : Topology.IsClosedEmbedding ι := ι.isClosedEmbedding
  have hrange : Set.range ι = q ⁻¹' {closedPoint A} :=
    range_eq_preimage_closedPoint_of_isPullback (IsPullback.of_hasPullback _ _)
  have hVc : IsClosed (ι '' V₀) := hι.isClosedMap _ hV₀.1
  obtain ⟨O, hO, hOV⟩ := hι.isInducing.isOpen_iff.mp hV₀.2
  obtain ⟨U, hU, hUV⟩ := exists_isClopen_inter_eq_of_henselianLocalRing q (ι '' V₀)
    (fun z ⟨y, _, hy⟩ ↦ hy ▸ hrange.le ⟨y, rfl⟩) hVc O hO (by
      rw [← hrange, ← hOV]
      ext z
      constructor
      · rintro ⟨hzO, y, rfl⟩
        exact ⟨y, hzO, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨hy, y, rfl⟩)
  refine ⟨U, hU, ?_⟩
  ext y
  constructor
  · intro hy
    have : ι y ∈ U ∩ q ⁻¹' {closedPoint A} := ⟨hy, hrange.le ⟨y, rfl⟩⟩
    rw [hUV] at this
    obtain ⟨y', hy', hyy'⟩ := this
    rwa [← hι.injective hyy']
  · intro hy
    have : ι y ∈ ι '' V₀ := ⟨y, hy, rfl⟩
    rw [← hUV] at this
    exact this.1

/-- Variant of `exists_isClopen_preimage_closedFibre_of_henselianLocalRing` for any cartesian
square `Z₀ = Z ×_A κ`. -/
theorem exists_isClopen_preimage_of_isPullback_of_henselianLocalRing {Z₀ : Scheme.{u}}
    {ι : Z₀ ⟶ Z} {q₀ : Z₀ ⟶ Spec (.of (ResidueField A))}
    (h : IsPullback ι q₀ q (Spec.map (CommRingCat.ofHom (residue A)))) (V₀ : Set Z₀)
    (hV₀ : IsClopen V₀) : ∃ U : Set Z, IsClopen U ∧ ι ⁻¹' U = V₀ := by
  let e := h.isoPullback
  obtain ⟨U, hU, hUV⟩ := exists_isClopen_preimage_closedFibre_of_henselianLocalRing q
    (e.inv ⁻¹' V₀) (hV₀.preimage e.inv.continuous)
  refine ⟨U, hU, ?_⟩
  have he : ι = e.hom ≫ pullback.fst q (Spec.map (CommRingCat.ofHom (residue A))) :=
    (h.isoPullback_hom_fst).symm
  rw [he, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, hUV, ← Set.preimage_comp,
    ← TopCat.coe_comp, ← Scheme.Hom.comp_base, e.hom_inv_id, Scheme.Hom.id_base, TopCat.coe_id,
    Set.preimage_id]

end AlgebraicGeometry
