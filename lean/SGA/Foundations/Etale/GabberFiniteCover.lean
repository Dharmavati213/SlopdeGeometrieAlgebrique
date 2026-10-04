/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import SGA.Foundations.Limits.GeometricFiberCard
import SGA.SGA1.ExposeI.Unramified
import SGA.SGA1.ExposeV.QuotientDescent
import SGA.SGA1.ExposeVIII.QuasiFiniteOpenInFinite

/-!
# Finite covers refining étale covers

Stacks 09Z0: for a quasi-compact and quasi-separated scheme `X` and a surjective étale
`U ⟶ X`, there is a finite surjective `X' ⟶ X` (of finite presentation) which Zariski-locally on
`X'` factors through `U`. This turns étale-local data into Zariski-local data after a finite base
change, the key step of Gabber's theorem on sections over henselian pairs (Stacks 09ZF).

We prove the noetherian case, for finitely many affine étale `X`-schemes jointly surjective onto
`X`: `AlgebraicGeometry.etaleFiniteRefinementStatement` (the statement is
`AlgebraicGeometry.EtaleFiniteRefinementStatement`, registry row A37). The proof follows Stacks,
by induction on a bound `d` for the geometric number of points `n_w` of a quasi-compact separated
étale `w : W ⟶ X` (`exists_finite_refinement_of_geometricFiberCard_le`, with an open `V ⊆ X` of
points that need no factorization):

* `W` is open in a scheme `K` finite over `X` (SGA 1 VIII.6.4,
  `SGA.SGA1.ExposeVIII.exists_isOpenImmersion_isFinite_of_isNoetherian`), and dense after passing
  to the scheme-theoretic closure;
* `W ×_X K` is the disjoint union of the graph of `W ⟶ K` (open since `W ×_X K ⟶ K` is étale,
  closed since `K` is separated) and of `W₁`, and `n_{W₁} ≤ d - 1`: this holds on the dense open
  `W` (`Scheme.Hom.geometricFiberCard_comp_add_one_le`) and the set where `n_{W₁} ≥ d` is open
  (lower semicontinuity, `Scheme.Hom.isOpen_setOf_le_geometricFiberCard`);
* the induction hypothesis applied to `K`, `W₁` and the open `W ∪ (K ×_X V)` gives finite covers
  of `K`, which together with the reduced closed complement of the image of `W` give the finite
  covers of `X`.

A uniform bound `d` exists over a noetherian base (`Scheme.Hom.exists_forall_geometricFiberCard_le`,
by lower semicontinuity at the generic points of the irreducible components). The finitely many
finite covers produced are combined into one by a coproduct (`SGA.SGA1.ExposeV.isFinite_sigmaDesc`).

This file imports SGA 1 (Exposés I, V and VIII) for the quasi-finiteness of étale morphisms, the
finiteness of finite coproducts of finite morphisms, and VIII.6.4.

## References

* [Stacks Project, Tag 09Z0](https://stacks.math.columbia.edu/tag/09Z0)
* [SGA 1, Exposé VIII, 6.4][sga1]
-/

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

/-- **Stacks 09Z0, noetherian case**: for a noetherian scheme `X` and finitely
many affine étale `X`-schemes `U j` jointly surjective onto `X`, there is a finite surjective
morphism `π : X' ⟶ X` such that every point of `X'` has an open neighbourhood `W` on which `π`
factors through some `U j ⟶ X`. Proved as `etaleFiniteRefinementStatement`. -/
def EtaleFiniteRefinementStatement : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X] (ι : Type u) [Finite ι] (U : ι → X.Etale)
    [∀ j, IsAffine (U j).left], (∀ x : X, ∃ j u, (U j).hom u = x) →
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X), IsFinite π ∧ Surjective π ∧
      ∀ x' : X', ∃ (W : X'.Opens) (j : ι) (g : (W : Scheme.{u}) ⟶ (U j).left),
        x' ∈ W ∧ g ≫ (U j).hom = W.ι ≫ π

/-- Removing a point of a fibre lowers the geometric number of points: for an open immersion
`ι : O ⟶ P` and a point `z` of `P` outside `O`, `n_{ι ≫ q}(q z) + 1 ≤ n_q(q z)`. -/
lemma Scheme.Hom.geometricFiberCard_comp_add_one_le {O P K : Scheme.{u}} (ι : O ⟶ P)
    [IsOpenImmersion ι] (q : P ⟶ K) [LocallyQuasiFinite q] (hq : ∀ y, (q ⁻¹' {y}).Finite) (z : P)
    (hz : z ∉ Set.range ι) :
    (ι ≫ q).geometricFiberCard (q z) + 1 ≤ q.geometricFiberCard (q z) := by
  let Ω := AlgebraicClosure (K.residueField (q z))
  let t := K.fromSpecAlgClosure (q z)
  have ht : t (IsLocalRing.closedPoint Ω) = q z := Scheme.fromSpecAlgClosure_apply _ _
  have hfin : (q ⁻¹' {t (IsLocalRing.closedPoint Ω)}).Finite := hq _
  have hfin' : ((ι ≫ q) ⁻¹' {t (IsLocalRing.closedPoint Ω)}).Finite :=
    (hq (t (IsLocalRing.closedPoint Ω))).preimage (f := ι) ι.isOpenEmbedding.injective.injOn
  have : Finite (q.PointsOver t) := q.finite_pointsOver' t hfin
  obtain ⟨a, ha⟩ := q.exists_pointsOver_apply_eq' t z ht.symm
  let e : (ι ≫ q).PointsOver t → q.PointsOver t := fun b ↦
    ⟨b.1 ≫ ι, by rw [Category.assoc]; exact b.2⟩
  have he : Function.Injective e := fun b b' h ↦
    Subtype.ext ((cancel_mono ι).1 (congrArg Subtype.val h))
  have hne : a ∉ Set.range e := by
    rintro ⟨b, hb⟩
    apply hz
    have h := congrArg (fun c : q.PointsOver t ↦ c.1 (IsLocalRing.closedPoint Ω)) hb
    exact ⟨b.1 (IsLocalRing.closedPoint Ω), h.trans ha⟩
  have : Finite ((ι ≫ q).PointsOver t) := Finite.of_injective e he
  have := Fintype.ofFinite (q.PointsOver t)
  have := Fintype.ofFinite ((ι ≫ q).PointsOver t)
  rw [← ht, ← q.natCard_pointsOver' t hfin, ← (ι ≫ q).natCard_pointsOver' t hfin',
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_not_surjective e he fun hs ↦ hne (hs a)

/-- Over a noetherian scheme, the geometric number of points of a separated, universally open,
locally quasi-finite morphism with finite fibres is bounded: by lower semicontinuity, `n(x)` is at
most `n` at the generic point of an irreducible component through `x`. -/
lemma Scheme.Hom.exists_forall_geometricFiberCard_le {X W : Scheme.{u}} [IsNoetherian X]
    (w : W ⟶ X) [IsSeparated w] [UniversallyOpen w] [LocallyQuasiFinite w]
    (hf : ∀ x, (w ⁻¹' {x}).Finite) : ∃ d, ∀ x, w.geometricFiberCard x ≤ d := by
  classical
  let n : Set X → ℕ := fun Z ↦
    if h : IsIrreducible Z then w.geometricFiberCard h.genericPoint else 0
  obtain ⟨d, hd⟩ := ((TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (α := X)).image n).bddAbove
  refine ⟨d, fun x ↦ ?_⟩
  have hZ := irreducibleComponent_mem_irreducibleComponents x
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hgen := hirr.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents _ hZ).closure_eq] at hgen
  have hsp := hgen.specializes (mem_irreducibleComponent (x := x))
  have hle : w.geometricFiberCard x ≤ w.geometricFiberCard hirr.genericPoint :=
    hsp.mem_open (w.isOpen_setOf_le_geometricFiberCard _ hf)
      (show w.geometricFiberCard x ≤ w.geometricFiberCard x from le_rfl)
  refine hle.trans ?_
  have := hd ⟨_, hZ, rfl⟩
  simpa [n, hirr] using this

/-- The induction of Stacks 09Z0 (noetherian case), on a bound `d` for the geometric number of
points of `w`: for a noetherian scheme `X`, an open `V ⊆ X` and a quasi-compact separated étale
`w : W ⟶ X` with `V ∪ w(W) = X` and `n_w ≤ d`, there are finitely many finite morphisms
`π k : X' k ⟶ X`, jointly surjective, such that every point of every `X' k` has an open
neighbourhood which `π k` maps into `V` or on which `π k` factors through `w`. -/
theorem exists_finite_refinement_of_geometricFiberCard_le (d : ℕ) :
    ∀ {X W : Scheme.{u}} [IsNoetherian X] (w : W ⟶ X) [Etale w] [IsSeparated w] [CompactSpace W]
      (V : Set X), IsOpen V → (∀ x, x ∈ V ∨ x ∈ Set.range w) →
      (∀ x, w.geometricFiberCard x ≤ d) →
      ∃ (κ : Type u) (_ : Finite κ) (X' : κ → Scheme.{u}) (π : ∀ k, X' k ⟶ X),
        (∀ k, IsFinite (π k)) ∧ (∀ x, ∃ k x', π k x' = x) ∧
        ∀ k (x' : X' k), ∃ O : (X' k).Opens, x' ∈ O ∧
          ((π k) '' O ⊆ V ∨ ∃ g : (O : Scheme.{u}) ⟶ W, g ≫ w = O.ι ≫ π k) := by
  induction d with
  | zero =>
    intro X W _ w _ _ _ V hV hcov hd
    have hW : IsEmpty W := w.isEmpty_of_geometricFiberCard_eq_zero
      (fun _ ↦ w.finite_preimage_singleton _) (fun x ↦ Nat.le_zero.1 (hd x))
    refine ⟨PUnit, inferInstance, fun _ ↦ X, fun _ ↦ 𝟙 X, fun _ ↦ inferInstance,
      fun x ↦ ⟨⟨⟩, x, rfl⟩, fun _ x' ↦ ⟨⊤, trivial, Or.inl ?_⟩⟩
    rintro _ ⟨x, -, rfl⟩
    rcases hcov x with h | ⟨a, -⟩
    · exact h
    · exact (hW.false a).elim
  | succ d ih =>
    intro X W _ w _ _ _ V hV hcov hd
    obtain ⟨K₀, j₀, p₀, hj₀, hp₀, hjp₀⟩ :=
      SGA.SGA1.ExposeVIII.exists_isOpenImmersion_isFinite_of_isNoetherian w
    have : QuasiCompact j₀ := by
      have : QuasiCompact (j₀ ≫ p₀) := hjp₀ ▸ inferInstance
      exact QuasiCompact.of_comp j₀ p₀
    -- `K`: the closure of `W` in `K₀`, finite over `X`, with `W` open and dense in it
    obtain ⟨K, j, p, _, _, hjp, hdense⟩ : ∃ (K : Scheme.{u}) (j : W ⟶ K) (p : K ⟶ X),
        IsOpenImmersion j ∧ IsFinite p ∧ j ≫ p = w ∧ DenseRange j :=
      ⟨j₀.image, j₀.toImage, j₀.imageι ≫ p₀, inferInstance, inferInstance, by simp [hjp₀],
        j₀.toImage.denseRange⟩
    have : IsNoetherian K :=
      have := LocallyOfFiniteType.isLocallyNoetherian p
      have := QuasiCompact.compactSpace_of_compactSpace p
      { }
    -- `W ×_X K` is the disjoint union of the graph of `j` and of `W₁`
    let P := pullback w p
    let Γ : W ⟶ P := pullback.lift (𝟙 W) j (by rw [Category.id_comp, hjp])
    have hΓ₁ : Γ ≫ pullback.fst w p = 𝟙 W := pullback.lift_fst _ _ _
    have hΓ₂ : Γ ≫ pullback.snd w p = j := pullback.lift_snd _ _ _
    have : IsClosedImmersion Γ := by
      have : IsClosedImmersion (Γ ≫ pullback.fst w p) := hΓ₁ ▸ inferInstance
      exact IsClosedImmersion.of_comp Γ (pullback.fst w p)
    have : Etale Γ := by
      have : Etale (Γ ≫ pullback.snd w p) := hΓ₂ ▸ inferInstance
      exact Etale.of_comp Γ (pullback.snd w p)
    have hΓo : IsOpen (Set.range Γ) := Γ.isOpenMap.isOpen_range
    let O : P.Opens := ⟨(Set.range Γ)ᶜ, Γ.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    let w₁ : (O : Scheme.{u}) ⟶ K := O.ι ≫ pullback.snd w p
    have : CompactSpace O := by
      rw [← isCompact_univ_iff, O.ι.isOpenEmbedding.isInducing.isCompact_iff, Set.image_univ,
        Scheme.Opens.range_ι]
      exact hΓo.isClosed_compl.isCompact
    -- `n_{w₁} ≤ d`: on the dense open `W`, `n_{w₁} = n_w - 1`
    have hd₁ : ∀ y, w₁.geometricFiberCard y ≤ d := by
      by_contra! h
      obtain ⟨y, hy⟩ := h
      have hD := w₁.isOpen_setOf_le_geometricFiberCard (d + 1)
        (fun y ↦ w₁.finite_preimage_singleton y)
      obtain ⟨a, ha⟩ := hdense.exists_mem_open hD ⟨y, hy⟩
      have hz : Γ a ∉ Set.range O.ι := by
        rw [Scheme.Opens.range_ι]
        exact fun h ↦ h ⟨a, rfl⟩
      have h₁ := Scheme.Hom.geometricFiberCard_comp_add_one_le O.ι (pullback.snd w p)
        (fun y ↦ (pullback.snd w p).finite_preimage_singleton y) (Γ a) hz
      have h₂ := w.geometricFiberCard_of_isPullback (fun x ↦ w.finite_preimage_singleton x)
        (IsPullback.of_hasPullback w p) ((pullback.snd w p) (Γ a))
      have e₁ : (pullback.snd w p) (Γ a) = j a := by rw [← Scheme.Hom.comp_apply, hΓ₂]
      have e₂ : p (j a) = w a := by rw [← Scheme.Hom.comp_apply, hjp]
      rw [e₁] at h₁ h₂
      rw [e₂] at h₂
      have h₃ := hd (w a)
      have h₄ : d + 1 ≤ w₁.geometricFiberCard (j a) := ha
      change (O.ι ≫ pullback.snd w p).geometricFiberCard (j a) + 1 ≤ _ at h₁
      change d + 1 ≤ (O.ι ≫ pullback.snd w p).geometricFiberCard (j a) at h₄
      omega
    -- the cover of `K` by `W ∪ p⁻¹(V)` and `W₁`
    let V₁ : Set K := Set.range j ∪ p ⁻¹' V
    have hV₁ : IsOpen V₁ := j.isOpenEmbedding.isOpen_range.union (hV.preimage p.continuous)
    have hcov₁ : ∀ y, y ∈ V₁ ∨ y ∈ Set.range w₁ := by
      intro y
      by_cases hy : y ∈ V₁
      · exact Or.inl hy
      right
      rcases hcov (p y) with h | ⟨a, ha⟩
      · exact (hy (Or.inr h)).elim
      obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := w) (g := p) a y ha
      have hzO : z ∈ O := by
        rintro ⟨b, rfl⟩
        refine hy (Or.inl ⟨b, ?_⟩)
        rw [← hz₂, ← Scheme.Hom.comp_apply, hΓ₂]
      refine ⟨⟨z, hzO⟩, ?_⟩
      change (pullback.snd w p) z = y
      exact hz₂
    obtain ⟨κ₁, _, X₁, π₁, hπ₁, hsurj₁, hloc₁⟩ := ih w₁ V₁ hV₁ hcov₁ hd₁
    -- the closed complement `T` of `w(W)`, which lies in `V`
    have hT : IsClosed (Set.range w)ᶜ := w.isOpenMap.isOpen_range.isClosed_compl
    let I := Scheme.IdealSheafData.vanishingIdeal ⟨(Set.range w)ᶜ, hT⟩
    have hrange : Set.range I.subschemeι = (Set.range w)ᶜ := by
      rw [Scheme.IdealSheafData.range_subschemeι]
      simp [I]
    let X' : Option κ₁ → Scheme.{u} := fun k ↦ k.elim I.subscheme X₁
    let π : ∀ k, X' k ⟶ X := fun k ↦ match k with
      | none => I.subschemeι
      | some k => π₁ k ≫ p
    refine ⟨Option κ₁, inferInstance, X', π, ?_, ?_, ?_⟩
    · rintro (_ | k)
      · exact inferInstanceAs (IsFinite I.subschemeι)
      · have := hπ₁ k
        exact inferInstanceAs (IsFinite (π₁ k ≫ p))
    · intro x
      by_cases hx : x ∈ Set.range w
      · obtain ⟨a, rfl⟩ := hx
        obtain ⟨k, x', hx'⟩ := hsurj₁ (j a)
        refine ⟨some k, x', ?_⟩
        change p (π₁ k x') = w a
        rw [hx', ← Scheme.Hom.comp_apply, hjp]
      · obtain ⟨t, ht⟩ : x ∈ Set.range I.subschemeι := hrange ▸ hx
        exact ⟨none, t, ht⟩
    · rintro (_ | k) x'
      · refine ⟨⊤, trivial, Or.inl ?_⟩
        rintro _ ⟨t, -, rfl⟩
        have ht : I.subschemeι t ∈ (Set.range w)ᶜ := hrange ▸ ⟨t, rfl⟩
        rcases hcov (I.subschemeι t) with h | h
        · exact h
        · exact (ht h).elim
      · obtain ⟨U, hx'U, hU | ⟨g, hg⟩⟩ := hloc₁ k x'
        · rcases hU ⟨x', hx'U, rfl⟩ with ⟨a, ha⟩ | h
          · -- near `x'`, `π₁ k` lands in `W ⊆ K`
            let U' : (X₁ k).Opens := U ⊓ π₁ k ⁻¹ᵁ j.opensRange
            have hrg : Set.range (U'.ι ≫ π₁ k) ⊆ Set.range j := by
              rintro _ ⟨u, rfl⟩
              exact u.2.2
            refine ⟨U', ⟨hx'U, a, ha⟩, Or.inr ⟨IsOpenImmersion.lift j (U'.ι ≫ π₁ k) hrg, ?_⟩⟩
            change _ ≫ w = U'.ι ≫ π₁ k ≫ p
            have h := IsOpenImmersion.lift_fac j (U'.ι ≫ π₁ k) hrg
            calc IsOpenImmersion.lift j (U'.ι ≫ π₁ k) hrg ≫ w
                _ = (IsOpenImmersion.lift j (U'.ι ≫ π₁ k) hrg ≫ j) ≫ p := by
                  rw [Category.assoc, hjp]
                _ = U'.ι ≫ π₁ k ≫ p := by rw [h, Category.assoc]
          · -- near `x'`, `π₁ k ≫ p` lands in `V`
            let U' : (X₁ k).Opens := U ⊓ (π₁ k ≫ p) ⁻¹ᵁ ⟨V, hV⟩
            refine ⟨U', ⟨hx'U, h⟩, Or.inl ?_⟩
            rintro _ ⟨u, hu, rfl⟩
            exact hu.2
        · refine ⟨U, hx'U, Or.inr ⟨g ≫ O.ι ≫ pullback.fst w p, ?_⟩⟩
          change _ = U.ι ≫ π₁ k ≫ p
          calc (g ≫ O.ι ≫ pullback.fst w p) ≫ w
              _ = (g ≫ w₁) ≫ p := by
                simp only [w₁, Category.assoc, pullback.condition]
              _ = U.ι ≫ π₁ k ≫ p := by rw [hg, Category.assoc]

/-- **Stacks 09Z0, noetherian case**: for a noetherian scheme `X` and finitely
many affine étale `X`-schemes `U j` jointly surjective onto `X`, there is a finite surjective
`π : X' ⟶ X` such that every point of `X'` has an open neighbourhood on which `π` factors through
some `U j ⟶ X`. -/
theorem exists_isFinite_surjective_forall_exists_factor {X : Scheme.{u}} [IsNoetherian X]
    {ι : Type u} [Finite ι] (U : ι → X.Etale) [∀ j, IsAffine (U j).left]
    (hU : ∀ x : X, ∃ j u, (U j).hom u = x) :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X), IsFinite π ∧ Surjective π ∧
      ∀ x' : X', ∃ (W : X'.Opens) (j : ι) (g : (W : Scheme.{u}) ⟶ (U j).left),
        x' ∈ W ∧ g ≫ (U j).hom = W.ι ≫ π := by
  let w : (∐ fun j ↦ (U j).left) ⟶ X := Sigma.desc fun j ↦ (U j).hom
  have : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have : Etale w := IsZariskiLocalAtSource.sigmaDesc fun j ↦ inferInstance
  obtain ⟨d, hd⟩ := w.exists_forall_geometricFiberCard_le fun x ↦ w.finite_preimage_singleton x
  obtain ⟨κ, _, X', π, hπ, hsurj, hloc⟩ := exists_finite_refinement_of_geometricFiberCard_le d w ∅
    isOpen_empty (fun x ↦ Or.inr (by
      obtain ⟨j, u, rfl⟩ := hU x
      exact ⟨Sigma.ι (fun j ↦ (U j).left) j u, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩))
    hd
  refine ⟨∐ X', Sigma.desc π, SGA.SGA1.ExposeV.isFinite_sigmaDesc π hπ, ⟨fun x ↦ ?_⟩,
    fun x'' ↦ ?_⟩
  · obtain ⟨k, x', rfl⟩ := hsurj x
    exact ⟨Sigma.ι X' k x', by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩
  · obtain ⟨⟨k, x'⟩, rfl⟩ := (sigmaMk X').surjective x''
    rw [sigmaMk_mk]
    obtain ⟨O, hx'O, hO | ⟨g, hg⟩⟩ := hloc k x'
    · exact (hO ⟨x', hx'O, rfl⟩).elim
    obtain ⟨⟨j, u⟩, hu⟩ := (sigmaMk fun j ↦ (U j).left).surjective (g ⟨x', hx'O⟩)
    rw [sigmaMk_mk] at hu
    let O' : (O : Scheme.{u}).Opens := g ⁻¹ᵁ (Sigma.ι (fun j ↦ (U j).left) j).opensRange
    have hrg : Set.range (O'.ι ≫ g) ⊆ Set.range (Sigma.ι (fun j ↦ (U j).left) j) := by
      rintro _ ⟨v, rfl⟩
      exact v.2
    let h : (O' : Scheme.{u}) ⟶ (U j).left := IsOpenImmersion.lift _ (O'.ι ≫ g) hrg
    let f : (O' : Scheme.{u}) ⟶ ∐ X' := O'.ι ≫ O.ι ≫ Sigma.ι X' k
    have hx : ⟨x', hx'O⟩ ∈ O' := ⟨u, hu⟩
    refine ⟨f.opensRange, j, f.isoOpensRange.inv ≫ h, ⟨⟨⟨x', hx'O⟩, hx⟩, rfl⟩, ?_⟩
    have hh : h ≫ (U j).hom = f ≫ Sigma.desc π := by
      have e₁ : h ≫ Sigma.ι (fun j ↦ (U j).left) j = O'.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
      calc h ≫ (U j).hom
          _ = (h ≫ Sigma.ι (fun j ↦ (U j).left) j) ≫ w := by
            rw [Category.assoc, Sigma.ι_desc]
          _ = f ≫ Sigma.desc π := by
            rw [e₁, Category.assoc, hg]
            simp [f]
    calc (f.isoOpensRange.inv ≫ h) ≫ (U j).hom
        _ = f.isoOpensRange.inv ≫ f ≫ Sigma.desc π := by rw [Category.assoc, hh]
        _ = f.isoOpensRange.inv ≫ (f.isoOpensRange.hom ≫ f.opensRange.ι) ≫ Sigma.desc π := by
          rw [Scheme.Hom.isoOpensRange_hom_ι]
        _ = f.opensRange.ι ≫ Sigma.desc π := by simp

/-- **Stacks 09Z0, noetherian case**: `EtaleFiniteRefinementStatement` holds. -/
theorem etaleFiniteRefinementStatement : EtaleFiniteRefinementStatement.{u} :=
  fun _ _ _ _ U _ hU ↦ exists_isFinite_surjective_forall_exists_factor U hU

end AlgebraicGeometry
