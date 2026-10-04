/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.FundamentalGroup
import SGA.SGA1.ExposeXII.SchemeLimits
import SGA.SGA1.ExposeIX.EtaleMorphismDescent

/-!
# SGA 1, Exposé XII, 5.1, step 1): the functor `Ψ` is fully faithful

Step 1) of the proof of XII.5.1: for `X` locally of finite type over `ℂ`, the functor
`Ψ : Y ↦ Y(ℂ)` from finite étale coverings of `X` to finite coverings of `X(ℂ)` is fully
faithful. Faithfulness is in `SGA.SGA1.ExposeXII.FundamentalGroup`; here we prove fullness
(instance), following SGA: an `X`-morphism `Y → Y'` is a clopen subscheme of `Y ×_X Y'` mapping
isomorphically to `Y`. More generally, for `Y' → S` finite étale and any `Y₁ → S` locally of finite
type over `ℂ`, every continuous map `Y₁(ℂ) → Y'(ℂ)` over `S(ℂ)` comes from an `S`-morphism
(`SchemePoints.exists_hom_map_eq`). The steps:

* the graph of a map of coverings `Y(ℂ) → Y'(ℂ)` is clopen in `(Y ×_X Y')(ℂ)` (a covering map is
  separated and locally injective);
* a clopen subset of `Z(ℂ)` is the set of `ℂ`-points of a clopen subset of `Z`
  (`SchemePoints.exists_isClopen_preimage_pt_eq`, from XII.2.4/XII.2.6:
  the Zariski closures of a clopen set of `ℂ`-points and of its complement are disjoint);
* an étale morphism, quasi-compact and quasi-separated, which is bijective on `ℂ`-points is an
  isomorphism (`SchemePoints.isIso_of_bijective_map`: it is surjective, and its diagonal is
  surjective, by the Jacobson property).

No connectedness or local topology of `X(ℂ)` is needed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology Set AlgebraicGeometry

namespace SGA.SGA1.ExposeXII

namespace SchemePoints

section IsIso

variable {K : Type u} [Field K] [IsAlgClosed K] {W Y : Scheme.{u}} [W.Over (Spec (.of K))]
  [Y.Over (Spec (.of K))] [LocallyOfFiniteType (W ↘ Spec (.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K))]

attribute [local instance] pullbackOver isOver_pullback_fst isOver_pullback_snd

/-- XII.3.1 (ix) for étale morphisms, on the scheme side (with XII.3.1 (vii)): a quasi-compact,
quasi-separated étale morphism `q : W → Y` of schemes locally of finite type over an
algebraically closed field `K` which is bijective on `K`-points is an isomorphism (its image and
its diagonal are determined by the `K`-points, `W`, `Y` and `W ×_Y W` being Jacobson). SGA states
(ix) with `q^an` an isomorphism of analytic spaces; for `q` étale this is bijectivity on points,
`q^an` being a local isomorphism. -/
theorem isIso_of_bijective_map (q : W ⟶ Y) [q.IsOver (Spec (.of K))] [Etale q] [QuasiCompact q]
    [QuasiSeparated q] (h : Function.Bijective (map (K := K) q)) : IsIso q := by
  have : Surjective q := ⟨surjective_of_surjective_map q h.2⟩
  have : LocallyOfFiniteType (pullback.fst q q ≫ W ↘ Spec (.of K)) := by
    have : LocallyOfFiniteType (pullback.fst q q) := inferInstance
    infer_instance
  have : LocallyOfFiniteType (pullback q q ↘ Spec (.of K)) := this
  have : UniversallyInjective q := by
    rw [UniversallyInjective.iff_diagonal]
    refine ⟨surjective_of_surjective_map (K := K) (pullback.diagonal q) fun r ↦ ?_⟩
    have h₁ : map (pullback.fst q q) r = map (pullback.snd q q) r := h.1 <| ext (by
      change (r.1 ≫ pullback.fst q q) ≫ q = (r.1 ≫ pullback.snd q q) ≫ q
      rw [Category.assoc, Category.assoc, pullback.condition])
    refine ⟨map (pullback.fst q q) r, ext (pullback.hom_ext ?_ ?_)⟩
    · change ((r.1 ≫ pullback.fst q q) ≫ pullback.diagonal q) ≫ pullback.fst q q =
        r.1 ≫ pullback.fst q q
      rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · have h₁' := congrArg Subtype.val h₁
      change ((r.1 ≫ pullback.fst q q) ≫ pullback.diagonal q) ≫ pullback.snd q q =
        r.1 ≫ pullback.snd q q
      rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      exact h₁'
  exact ExposeIX.isIso_of_etale_of_universallyInjective_of_surjective q

end IsIso

section Clopen

variable {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))]

/-- XII.2.6, clopen sets: every clopen subset `Γ` of `Z(ℂ)` is the set of `ℂ`-points of a
clopen subset of `Z` (the Zariski closure of `Γ`). -/
theorem exists_isClopen_preimage_pt_eq {Γ : Set (SchemePoints ℂ Z)} (hΓ : IsClopen Γ) :
    ∃ W : Set Z, IsClopen W ∧ pt ⁻¹' W = Γ := by
  have hdisj := disjoint_closure_image_pt_of_isClopen hΓ
  have hunion : closure (pt '' Γ) ∪ closure (pt '' Γᶜ) = univ := by
    rw [← closure_union, ← image_union, union_compl_self, image_univ]
    exact (denseRange_pt (K := ℂ)).closure_range
  have hcompl : (closure (pt '' Γ))ᶜ = closure (pt '' Γᶜ) :=
    IsCompl.compl_eq ⟨hdisj, codisjoint_iff.mpr hunion⟩
  refine ⟨closure (pt '' Γ), ⟨isClosed_closure, ?_⟩, ?_⟩
  · rw [← isClosed_compl_iff, hcompl]
    exact isClosed_closure
  · refine subset_antisymm (fun r hr ↦ ?_) fun r hr ↦ subset_closure (mem_image_of_mem _ hr)
    by_contra hrΓ
    exact Set.disjoint_left.mp hdisj hr (subset_closure (mem_image_of_mem _ hrΓ))

end Clopen

end SchemePoints

namespace SchemePoints

section Hom

variable {S Y₁ Y' : Scheme.{0}} [S.Over (Spec (.of ℂ))] [Y₁.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y₁ ↘ Spec (.of ℂ))] (f : Y₁ ⟶ S) (q : Y' ⟶ S)
  [f.IsOver (Spec (.of ℂ))] [q.IsOver (Spec (.of ℂ))] [IsFinite q] [Etale q]

attribute [local instance] pullbackOver isOver_pullback_fst isOver_pullback_snd in
/-- XII.5.1, proof of 1), in the form of SGA: for `q : Y' → S` finite étale and any
`f : Y₁ → S` with `Y₁` locally of finite type over `ℂ`, every continuous map `u : Y₁(ℂ) → Y'(ℂ)`
over `S(ℂ)` comes from an `S`-morphism `g : Y₁ → Y'`. The graph of `u` is clopen in
`(Y₁ ×_S Y')(ℂ)` (`Y'(ℂ) → S(ℂ)` is a covering map), hence (XII.2.6) is the set of `ℂ`-points of
a clopen subscheme `W` of `Y₁ ×_S Y'`; the projection `W → Y₁` is étale and bijective on
`ℂ`-points, hence an isomorphism, and `Y₁ ≅ W → Y'` is the morphism sought. (It is unique,
`SchemePoints.eq_of_forall_comp_eq`.) The `ℂ`-structure of `Y₁` makes `g` a morphism over `ℂ`,
so that `map g` is defined. -/
theorem exists_hom_map_eq (u : SchemePoints ℂ Y₁ → SchemePoints ℂ Y') (hu : Continuous u)
    (hpu : ∀ y, map q (u y) = map f y) :
    ∃ g : Y₁ ⟶ Y', g ≫ q = f ∧ ∃ _ : g.IsOver (Spec (.of ℂ)), ∀ y, map g y = u y := by
  -- the fibre product and the graph of `u`
  let Z := pullback f q
  have : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (pullback.fst f q ≫ Y₁ ↘ Spec (.of ℂ))
    infer_instance
  let Γ : Set (SchemePoints ℂ Z) :=
    {r | map (pullback.snd f q) r = u (map (pullback.fst f q) r)}
  have he : map (K := ℂ) q ∘ map (pullback.snd f q) =
      map q ∘ (u ∘ map (pullback.fst f q)) := by
    funext r
    simp only [Function.comp_apply]
    rw [hpu]
    exact ext (by
      change (r.1 ≫ pullback.snd _ _) ≫ q = (r.1 ≫ pullback.fst _ _) ≫ f
      rw [Category.assoc, Category.assoc, pullback.condition])
  have hcov := isCoveringMap_map (K := ℂ) q
  have hΓ : IsClopen Γ :=
    ⟨hcov.isSeparatedMap.isClosed_eqLocus (continuous_map _) (hu.comp (continuous_map _)) he,
      hcov.isLocalHomeomorph.isLocallyInjective.isOpen_eqLocus (continuous_map _)
        (hu.comp (continuous_map _)) he⟩
  obtain ⟨W, hW, hWΓ⟩ := exists_isClopen_preimage_pt_eq hΓ
  -- the clopen subscheme `V` with `V(ℂ) = Γ`, and its projection `p` to `Y₁`
  let V : Z.Opens := ⟨W, hW.isOpen⟩
  let : V.toScheme.Over (Spec (.of ℂ)) := .ofHom (V.ι ≫ Z ↘ Spec (.of ℂ))
  have : V.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (V.ι ≫ Z ↘ Spec (.of ℂ))
    infer_instance
  let p : V.toScheme ⟶ Y₁ := V.ι ≫ pullback.fst f q
  have : p.IsOver (Spec (.of ℂ)) := ⟨by
    change (V.ι ≫ pullback.fst _ _) ≫ Y₁ ↘ Spec (.of ℂ) = V.ι ≫ Z ↘ Spec (.of ℂ)
    rw [Category.assoc]
    rfl⟩
  have : QuasiCompact V.ι := ⟨fun U _ hU ↦ by
    have hce : IsClosedEmbedding V.ι :=
      ⟨V.ι.isOpenEmbedding.isEmbedding, by rw [Scheme.Opens.range_ι]; exact hW.isClosed⟩
    exact hce.isCompact_preimage hU⟩
  have hmemV (r : SchemePoints ℂ Z) : r.pt ∈ W ↔ r ∈ Γ := by
    rw [← hWΓ]
    rfl
  have hΓι (a : SchemePoints ℂ V.toScheme) : map V.ι a ∈ Γ := (hmemV _).mp (by
    rw [pt_map]
    change V.ι a.pt ∈ (V : Set Z)
    rw [← Scheme.Opens.range_ι]
    exact mem_range_self _)
  have hp (c : SchemePoints ℂ V.toScheme) :
      map (pullback.fst f q) (map V.ι c) = map p c := rfl
  have hbij : Function.Bijective (map (K := ℂ) p) := by
    constructor
    · intro a b hab
      apply map_injective V.ι
      apply (pullbackEquiv (K := ℂ) f q).injective
      refine Subtype.ext (Prod.ext ?_ ?_)
      · change map (pullback.fst _ _) (map V.ι a) = map (pullback.fst _ _) (map V.ι b)
        rw [hp, hp, hab]
      · change map (pullback.snd _ _) (map V.ι a) = map (pullback.snd _ _) (map V.ι b)
        rw [hΓι a, hΓι b, hp, hp, hab]
    · intro y
      let r : SchemePoints ℂ Z := (pullbackEquiv (K := ℂ) f q).symm ⟨(y, u y), (hpu y).symm⟩
      have hr := (pullbackEquiv (K := ℂ) f q).apply_symm_apply ⟨(y, u y), (hpu y).symm⟩
      have hr₁ : map (pullback.fst f q) r = y := congrArg (fun x ↦ x.1.1) hr
      have hr₂ : map (pullback.snd f q) r = u y := congrArg (fun x ↦ x.1.2) hr
      have hrΓ : r ∈ Γ := by
        change map (pullback.snd _ _) r = u (map (pullback.fst _ _) r)
        rw [hr₁, hr₂]
      obtain ⟨a, ha⟩ := exists_map_eq V.ι r (by
        rw [Scheme.Opens.range_ι]
        exact (hmemV r).mpr hrΓ)
      refine ⟨a, ?_⟩
      rw [← hp, ha, hr₁]
  have : IsIso p := isIso_of_bijective_map p hbij
  -- the morphism `Y₁ ≅ V → Y'`
  let g : Y₁ ⟶ Y' := inv p ≫ V.ι ≫ pullback.snd f q
  have hg : g ≫ q = f := by
    change inv p ≫ (V.ι ≫ pullback.snd _ _) ≫ q = f
    rw [Category.assoc, ← pullback.condition, ← Category.assoc V.ι]
    exact IsIso.inv_hom_id_assoc p f
  have hgo : g.IsOver (Spec (.of ℂ)) := ⟨by
    rw [← comp_over q (Spec (.of ℂ)), ← Category.assoc, hg, comp_over]⟩
  refine ⟨g, hg, hgo, fun y ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hbij.2 y
  have h1 : map g (map p a) = map (pullback.snd f q) (map V.ι a) := ext (by
    change a.1 ≫ p ≫ inv p ≫ V.ι ≫ pullback.snd _ _ = (a.1 ≫ V.ι) ≫ pullback.snd _ _
    rw [IsIso.hom_inv_id_assoc, Category.assoc])
  rw [h1, hΓι a, hp]

end Hom

end SchemePoints

section Full

variable (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]

/-- XII.5.1, proof of 1), fullness: every map of finite coverings `u : Y(ℂ) → Y'(ℂ)` of `X(ℂ)`
comes from an `X`-morphism `Y → Y'` of finite étale coverings (`SchemePoints.exists_hom_map_eq`). -/
theorem exists_map_eq_schemePointsFunctor (Y Y' : FiniteEtaleCovering X)
    (f : (schemePointsFunctor ℂ X).obj Y ⟶ (schemePointsFunctor ℂ X).obj Y') :
    ∃ g : Y ⟶ Y', (schemePointsFunctor ℂ X).map g = f := by
  let := overOfCovering ℂ X Y
  let := overOfCovering ℂ X Y'
  have := isOver_hom ℂ X Y
  have := isOver_hom ℂ X Y'
  have : IsFinite Y.hom' := Y.prop.1
  have : IsFinite Y'.hom' := Y'.prop.1
  have : Etale Y'.hom' := Y'.prop.2
  have : LocallyOfFiniteType (Y.left ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (Y.hom' ≫ X ↘ Spec (.of ℂ))
    infer_instance
  obtain ⟨g, hg, _, hgu⟩ := SchemePoints.exists_hom_map_eq Y.hom' Y'.hom'
    (f.hom.left : SchemePoints ℂ Y.left → SchemePoints ℂ Y'.left) f.hom.left.hom.continuous
    fun y ↦ congr($(Over.w f.hom) y)
  refine ⟨MorphismProperty.Over.homMk g (by simpa using hg), ?_⟩
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (TopCat.hom_ext (ContinuousMap.ext
    fun y ↦ ?_)))
  exact hgu y

/-- XII.5.1, proof of 1): for `X` locally of finite type over `ℂ`, the functor
`Ψ : Y ↦ Y(ℂ)` from finite étale coverings of `X` to finite coverings of `X(ℂ)` is full. -/
instance : (schemePointsFunctor ℂ X).Full where
  map_surjective {Y Y'} f := exists_map_eq_schemePointsFunctor X Y Y' f

/-- XII.5.1, proof of 1): for `X` locally of finite type over `ℂ`, the functor
`Ψ : Y ↦ Y(ℂ)` from finite étale coverings of `X` to finite coverings of `X(ℂ)` is fully
faithful. -/
def schemePointsFunctorFullyFaithful : (schemePointsFunctor ℂ X).FullyFaithful :=
  .ofFullyFaithful _

end Full

end SGA.SGA1.ExposeXII
