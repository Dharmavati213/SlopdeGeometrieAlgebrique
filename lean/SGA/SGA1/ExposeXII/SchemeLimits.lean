/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.SchemePoints
import SGA.SGA1.ExposeXII.FiniteLimits
import SGA.SGA1.ExposeXII.Separated

/-!
# SGA 1, Exposé XII, 1.2: the space of points of a fibre product

XII.1.2 states that `X ↦ X^an` commutes with finite projective limits, i.e. with fibre products.
On points: for `K`-morphisms `f : Y → X` and `g : Z → X`, the space `(Y ×_X Z)(K)` is the
subspace of `Y(K) × Z(K)` of pairs with the same image in `X(K)`
(`SchemePoints.pullbackHomeomorph`).

The inverse map is continuous locally: for affine opens `U ⊆ Y`, `V ⊆ Z`, the pairs of points
of `U` and `V` are the points of `T = Spec (Γ(U) ⊗_K Γ(V))`, and those with the same image in `X`
are the points of the preimage `E ⊆ T` of the diagonal of `X`, which embeds in `T(K)` (the
diagonal is an immersion) and maps to `Y ×_X Z`.

As a consequence, with XII.2.2 (`ClosureComparisonStatement`, a consequence of Rückert's
Nullstellensatz by `Nullstellensatz.lean`), XII.3.1 (viii): a morphism `f : X → Y` is separated if
and only if `X(ℂ) → Y(ℂ)` is a separated map (`isSeparated_iff_isSeparatedMap`; the direct
implication, over any `K`, is `isSeparatedMap_map`); for `Y = Spec ℂ`, `X` is separated if and only
if `X(ℂ)` is Hausdorff (`isSeparated_iff_t2Space`).
-/

universe u

noncomputable section

namespace SGA.SGA1.ExposeXII

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology Set
open scoped TensorProduct

namespace SchemePoints

attribute [local instance] sectionsAlgebra specOver

variable {K : Type u} [Field K] {X Y Z : Scheme.{u}} [X.Over (Spec (.of K))]
  [Y.Over (Spec (.of K))] [Z.Over (Spec (.of K))] (f : Y ⟶ X) (g : Z ⟶ X)
  [f.IsOver (Spec (.of K))] [g.IsOver (Spec (.of K))]

/-- The fibre product `Y ×_X Z` as a `K`-scheme. -/
abbrev pullbackOver : (pullback f g).Over (Spec (.of K)) :=
  .ofHom (pullback.fst f g ≫ Y ↘ Spec (.of K))

attribute [local instance] pullbackOver

omit [X.Over (Spec (.of K))] [Z.Over (Spec (.of K))] [f.IsOver (Spec (.of K))]
  [g.IsOver (Spec (.of K))] in
lemma isOver_pullback_fst : (pullback.fst f g).IsOver (Spec (.of K)) := ⟨rfl⟩

lemma isOver_pullback_snd : (pullback.snd f g).IsOver (Spec (.of K)) := ⟨by
  change pullback.snd f g ≫ Z ↘ Spec (.of K) = pullback.fst f g ≫ Y ↘ Spec (.of K)
  rw [← comp_over g (Spec (.of K)), ← comp_over f (Spec (.of K)), ← Category.assoc,
    ← Category.assoc, pullback.condition]⟩

attribute [local instance] isOver_pullback_fst isOver_pullback_snd

omit [X.Over (Spec (.of K))] [Z.Over (Spec (.of K))] [f.IsOver (Spec (.of K))]
  [g.IsOver (Spec (.of K))] in
lemma pullback_lift_over {p : Spec (.of K) ⟶ Y} {q : Spec (.of K) ⟶ Z}
    (hp : p ≫ Y ↘ Spec (.of K) = 𝟙 _) (h : p ≫ f = q ≫ g) :
    pullback.lift p q h ≫ pullback.fst f g ≫ Y ↘ Spec (.of K) = 𝟙 _ := by
  rw [pullback.lift_fst_assoc, hp]

variable (K) in
/-- XII.1.2: the pairs of `K`-points of `Y` and `Z` with the same image in `X`. -/
abbrev FiberProduct : Set (SchemePoints K Y × SchemePoints K Z) := {x | map f x.1 = map g x.2}

/-- XII.1.2: the `K`-points of `Y ×_X Z` are the pairs of `K`-points of `Y` and `Z` with the
same image in `X` (universal property of the fibre product). -/
def pullbackEquiv : SchemePoints K (pullback f g) ≃ FiberProduct K f g where
  toFun r := ⟨(map (pullback.fst f g) r, map (pullback.snd f g) r),
    ext (by simp only [map, Category.assoc, pullback.condition])⟩
  invFun x := ⟨pullback.lift x.1.1.1 x.1.2.1 (congr_arg Subtype.val x.2),
    pullback_lift_over f g x.1.1.2 _⟩
  left_inv r := ext (pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _))
  right_inv x := Subtype.ext (Prod.ext (ext (pullback.lift_fst _ _ _))
    (ext (pullback.lift_snd _ _ _)))

/-! ### Local charts of the fibre product -/

section Local

variable {U : Y.Opens} (hU : IsAffineOpen U) {V : Z.Opens} (hV : IsAffineOpen V)

variable (K U V) in
/-- The ring of `U ×_K V`. -/
abbrev locRing : Type u := Γ(Y, U) ⊗[K] Γ(Z, V)

/-- The projection `U ×_K V → Y`. -/
def locFst : Spec (.of (locRing K U V)) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := K) (S := K)).toRingHom) ≫
    hU.fromSpec

/-- The projection `U ×_K V → Z`. -/
def locSnd : Spec (.of (locRing K U V)) ⟶ Z :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K)).toRingHom) ≫
    hV.fromSpec

omit [X.Over (Spec (.of K))] [f.IsOver (Spec (.of K))] [g.IsOver (Spec (.of K))] in
lemma locFst_over : locFst hU (V := V) ≫ Y ↘ Spec (.of K) =
    Spec.map (CommRingCat.ofHom (algebraMap K (locRing K U V))) := by
  rw [locFst, Category.assoc, fromSpec_over, ← Spec.map_comp]
  congr 1

omit [X.Over (Spec (.of K))] [f.IsOver (Spec (.of K))] [g.IsOver (Spec (.of K))] in
lemma locSnd_over : locSnd (U := U) hV ≫ Z ↘ Spec (.of K) =
    Spec.map (CommRingCat.ofHom (algebraMap K (locRing K U V))) := by
  rw [locSnd, Category.assoc, fromSpec_over, ← Spec.map_comp]
  congr 1
  ext c
  exact (Algebra.TensorProduct.includeRight (R := K) (A := Γ(Y, U))).commutes c

variable (K) in
/-- The locus of `U ×_K V` where the two maps to `X` agree: the preimage of the diagonal. -/
abbrev locEq : Scheme.{u} :=
  pullback (pullback.diagonal (X ↘ Spec (.of K)))
    (pullback.lift (locFst hU (V := V) ≫ f) (locSnd (U := U) hV ≫ g)
      (by rw [Category.assoc, comp_over, locFst_over, Category.assoc, comp_over, locSnd_over]))

variable (K) in
/-- The immersion of the equalizer locus into `U ×_K V`. -/
abbrev locEqι : locEq K f g hU hV ⟶ Spec (.of (locRing K U V)) := pullback.snd _ _

abbrev locEqOver : (locEq K f g hU hV).Over (Spec (.of K)) :=
  .ofHom (locEqι K f g hU hV ≫ Spec.map (CommRingCat.ofHom (algebraMap K (locRing K U V))))

attribute [local instance] locEqOver

lemma isOver_locEqι : (locEqι K f g hU hV).IsOver (Spec (.of K)) := ⟨rfl⟩

attribute [local instance] isOver_locEqι

lemma locEqι_comp : locEqι K f g hU hV ≫ locFst hU ≫ f = locEqι K f g hU hV ≫ locSnd hV ≫ g := by
  have h := pullback.condition (f := pullback.diagonal (X ↘ Spec (.of K)))
    (g := pullback.lift (locFst hU (V := V) ≫ f) (locSnd (U := U) hV ≫ g)
      (by rw [Category.assoc, comp_over, locFst_over, Category.assoc, comp_over, locSnd_over]))
  have h₁ := congr($h ≫ pullback.fst _ _)
  have h₂ := congr($h ≫ pullback.snd _ _)
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, pullback.lift_fst,
    pullback.lift_snd, Category.comp_id] at h₁ h₂
  exact h₁.symm.trans h₂

variable (K) in
/-- The map from the equalizer locus to `Y ×_X Z`. -/
def locMap : locEq K f g hU hV ⟶ pullback f g :=
  pullback.lift (locEqι K f g hU hV ≫ locFst hU) (locEqι K f g hU hV ≫ locSnd hV)
    (by simpa only [Category.assoc] using locEqι_comp (K := K) f g hU hV)

lemma isOver_locMap : (locMap K f g hU hV).IsOver (Spec (.of K)) := ⟨by
  change locMap K f g hU hV ≫ pullback.fst f g ≫ Y ↘ Spec (.of K) = _
  rw [locMap, pullback.lift_fst_assoc, Category.assoc, locFst_over]
  rfl⟩

attribute [local instance] isOver_locMap

lemma mem_range_map_locEqι (t : SchemePoints K (Spec (.of (locRing K U V))))
    (h : t.1 ≫ locFst hU ≫ f = t.1 ≫ locSnd hV ≫ g) :
    t ∈ range (map (K := K) (locEqι K f g hU hV)) := by
  obtain ⟨t, ht⟩ := t
  refine ⟨⟨pullback.lift (t ≫ locFst hU ≫ f) t ?_, ?_⟩, ext (pullback.lift_snd _ _ _)⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd]
      exact h
  · change pullback.lift _ _ _ ≫ locEqι K f g hU hV ≫ _ = _
    rw [pullback.lift_snd_assoc]
    exact ht

omit [X.Over (Spec (.of K))] in
lemma subsingleton_points_self' (φ ψ : Points K K) : φ = ψ :=
  Points.ext fun a ↦ by
    rw [show a = algebraMap K K a from rfl, Points.apply_algebraMap, Points.apply_algebraMap]

/-- The point `(φ, ψ)` of `U ×_K V`. -/
def pairPt (x : Points K Γ(Y, U) × Points K Γ(Z, V)) :
    SchemePoints K (Spec (.of (locRing K U V))) :=
  specPoint _ (Points.pair (A := K) ⟨x, subsingleton_points_self' _ _⟩)

lemma pairPt_fst (x : Points K Γ(Y, U) × Points K Γ(Z, V)) :
    (pairPt x).1 ≫ locFst hU = (chart hU x.1).1 := by
  simp only [pairPt, specPoint, locFst, chart, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  change Points.pair _ (a ⊗ₜ 1) = x.1 a
  simp

lemma pairPt_snd (x : Points K Γ(Y, U) × Points K Γ(Z, V)) :
    (pairPt x).1 ≫ locSnd hV = (chart hV x.2).1 := by
  simp only [pairPt, specPoint, locSnd, chart, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  change Points.pair _ (1 ⊗ₜ a) = x.2 a
  simp

end Local

/-! ### The homeomorphism -/

attribute [local instance] locEqOver isOver_locEqι isOver_locMap

variable [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]

lemma continuous_pullbackEquiv : Continuous (pullbackEquiv (K := K) f g) :=
  ((continuous_map _).prodMk (continuous_map _)).subtype_mk _

lemma continuousAt_pullbackEquiv_symm (x₀ : FiberProduct K f g) :
    ContinuousAt (pullbackEquiv f g).symm x₀ := by
  obtain ⟨U, hU, hU₀⟩ := exists_isAffineOpen_mem x₀.1.1
  obtain ⟨V, hV, hV₀⟩ := exists_isAffineOpen_mem x₀.1.2
  let N : Set (FiberProduct K f g) := {x | x.1.1.pt ∈ U ∧ x.1.2.pt ∈ V}
  have hN : IsOpen N :=
    ((continuous_pt.comp (continuous_fst.comp continuous_subtype_val)).isOpen_preimage _
      U.2).inter
    ((continuous_pt.comp (continuous_snd.comp continuous_subtype_val)).isOpen_preimage _ V.2)
  refine ContinuousOn.continuousAt ?_ (hN.mem_nhds ⟨hU₀, hV₀⟩)
  rw [continuousOn_iff_continuous_domRestrict]
  let eU := (isOpenEmbedding_chart (K := K) hU).isEmbedding.toHomeomorph
  let eV := (isOpenEmbedding_chart (K := K) hV).isEmbedding.toHomeomorph
  let eE := (isEmbedding_map (K := K) (locEqι K f g hU hV)).toHomeomorph
  have hmemU : ∀ x : N, x.1.1.1 ∈ range (chart (K := K) hU) := fun x ↦ by
    rw [range_chart]; exact x.2.1
  have hmemV : ∀ x : N, x.1.1.2 ∈ range (chart (K := K) hV) := fun x ↦ by
    rw [range_chart]; exact x.2.2
  let φ : N → Points K Γ(Y, U) := fun x ↦ eU.symm ⟨x.1.1.1, hmemU x⟩
  let ψ : N → Points K Γ(Z, V) := fun x ↦ eV.symm ⟨x.1.1.2, hmemV x⟩
  have hφ (x : N) : chart hU (φ x) = x.1.1.1 := congr_arg Subtype.val (eU.apply_symm_apply _)
  have hψ (x : N) : chart hV (ψ x) = x.1.1.2 := congr_arg Subtype.val (eV.apply_symm_apply _)
  let t : N → SchemePoints K (Spec (.of (locRing K U V))) := fun x ↦ pairPt (φ x, ψ x)
  have ht (x : N) : t x ∈ range (map (K := K) (locEqι K f g hU hV)) :=
    mem_range_map_locEqι f g hU hV (t x) (by
      rw [← Category.assoc, pairPt_fst, hφ x, ← Category.assoc, pairPt_snd, hψ x]
      exact congr_arg Subtype.val x.1.2)
  let e : N → SchemePoints K (locEq K f g hU hV) := fun x ↦ eE.symm ⟨t x, ht x⟩
  have he (x : N) : (e x).1 ≫ locEqι K f g hU hV = (t x).1 :=
    congr_arg Subtype.val (congr_arg Subtype.val (eE.apply_symm_apply ⟨t x, ht x⟩))
  have heq : N.domRestrict (pullbackEquiv f g).symm = map (locMap K f g hU hV) ∘ e := by
    funext x
    refine (pullbackEquiv f g).symm_apply_eq.mpr (Subtype.ext (Prod.ext (ext ?_) (ext ?_)))
    · change x.1.1.1.1 = ((e x).1 ≫ locMap K f g hU hV) ≫ pullback.fst f g
      rw [Category.assoc, locMap, pullback.lift_fst, ← Category.assoc, he, pairPt_fst, hφ]
    · change x.1.1.2.1 = ((e x).1 ≫ locMap K f g hU hV) ≫ pullback.snd f g
      rw [Category.assoc, locMap, pullback.lift_snd, ← Category.assoc, he, pairPt_snd, hψ]
  rw [heq]
  have hφc : Continuous φ := eU.symm.continuous.comp
    ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)
  have hψc : Continuous ψ := eV.symm.continuous.comp
    ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)
  have hpair : Continuous fun y : Points K Γ(Y, U) × Points K Γ(Z, V) ↦
      (⟨y, subsingleton_points_self' _ _⟩ : Points.FiberProduct K K Γ(Y, U) Γ(Z, V)) :=
    continuous_id.subtype_mk _
  have htc : Continuous t := (continuous_specPoint _).comp
    (Points.homeomorphTensorProduct.symm.continuous.comp (hpair.comp (hφc.prodMk hψc)))
  exact (continuous_map _).comp (eE.symm.continuous.comp (htc.subtype_mk _))

/-- XII.1.2, "`Φ` commutes with fibre products", on points: `(Y ×_X Z)(K)` is homeomorphic to
the subspace of `Y(K) × Z(K)` of pairs with the same image in `X(K)`. -/
def pullbackHomeomorph : SchemePoints K (pullback f g) ≃ₜ FiberProduct K f g where
  toEquiv := pullbackEquiv f g
  continuous_toFun := continuous_pullbackEquiv f g
  continuous_invFun := continuous_iff_continuousAt.mpr (continuousAt_pullbackEquiv_symm f g)

end SchemePoints

/-! ### Separatedness and Hausdorffness (XII.3.1 (viii)) -/

namespace SchemePoints

attribute [local instance] pullbackOver isOver_pullback_fst isOver_pullback_snd

/-- Locally closed subsets of a locally noetherian scheme are locally constructible. -/
lemma isLocallyConstructible_of_isLocallyClosed {X : Scheme.{u}} [IsLocallyNoetherian X]
    {T : Set X} (hT : IsLocallyClosed T) : IsLocallyConstructible T := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hT
  refine IsLocallyConstructible.inter ?_ (isLocallyConstructible_of_isClosed hZ)
  have := IsLocallyConstructible.compl (isLocallyConstructible_of_isClosed hU.isClosed_compl)
  rwa [compl_compl] at this

/-- XII.3.1 (viii) for `X → Spec ℂ`, converse, from XII.2.2: if `X(ℂ)` is Hausdorff, then `X` is
separated. The diagonal is an immersion whose `ℂ`-points form the (closed) diagonal of
`X(ℂ) × X(ℂ) = (X ×_ℂ X)(ℂ)`; by XII.2.3 its image is closed. -/
theorem isSeparated_of_t2Space (H : ClosureComparisonStatement) (X : Scheme.{0})
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    [T2Space (SchemePoints ℂ X)] : IsSeparated (X ↘ Spec (.of ℂ)) := by
  let S := Spec (.of ℂ)
  let : S.Over S := .ofHom (𝟙 S)
  have : (X ↘ S).IsOver S := ⟨Category.comp_id _⟩
  let P := pullback (X ↘ S) (X ↘ S)
  have : LocallyOfFiniteType (P ↘ S) :=
    show LocallyOfFiniteType (pullback.fst (X ↘ S) (X ↘ S) ≫ X ↘ S) from inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (P ↘ S)
  let Δ := pullback.diagonal (X ↘ S)
  have : Δ.IsOver S := ⟨by
    change Δ ≫ pullback.fst (X ↘ S) (X ↘ S) ≫ X ↘ S = X ↘ S
    rw [pullback.diagonal_fst_assoc]⟩
  let h := pullbackHomeomorph (K := ℂ) (X ↘ S) (X ↘ S)
  have hΔ : ∀ p : SchemePoints ℂ X, (h (map Δ p)).1 = (p, p) := fun p ↦ by
    refine Prod.ext (ext ?_) (ext ?_)
    · change (p.1 ≫ Δ) ≫ pullback.fst _ _ = p.1
      rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · change (p.1 ≫ Δ) ≫ pullback.snd _ _ = p.1
      rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
  have hrange : range (map (K := ℂ) Δ) = h ⁻¹' {x | x.1.1 = x.1.2} := by
    ext r
    constructor
    · rintro ⟨p, rfl⟩
      simp [hΔ p]
    · intro hr
      refine ⟨(h r).1.1, h.injective (Subtype.ext ?_)⟩
      rw [hΔ]
      exact Prod.ext rfl hr
  have hpre : pt ⁻¹' range Δ = range (map (K := ℂ) Δ) := by
    ext r
    refine ⟨fun hr ↦ exists_map_eq Δ r hr, ?_⟩
    rintro ⟨p, rfl⟩
    exact ⟨p.pt, (pt_map Δ p).symm⟩
  have hclosed : IsClosed (pt ⁻¹' range Δ : Set (SchemePoints ℂ P)) := by
    rw [hpre, hrange]
    exact (isClosed_diagonal.preimage continuous_subtype_val).preimage h.continuous
  have := (isClosed_iff_of_closureComparison H
    (isLocallyConstructible_of_isLocallyClosed Δ.isLocallyClosed_range)).mpr hclosed
  exact ⟨IsClosedImmersion.of_isPreimmersion Δ this⟩

/-- XII.3.1 (viii) for `X → Spec ℂ`, from XII.2.2: `X` is separated if and only if `X(ℂ)` is
Hausdorff. -/
theorem isSeparated_iff_t2Space (H : ClosureComparisonStatement) (X : Scheme.{0})
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] :
    IsSeparated (X ↘ Spec (.of ℂ)) ↔ T2Space (SchemePoints ℂ X) :=
  ⟨fun _ ↦ t2Space ℂ X, fun _ ↦ isSeparated_of_t2Space H X⟩

section Relative

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] (f : X ⟶ Y)
  [f.IsOver (Spec (.of K))]

instance isOver_diagonal : (pullback.diagonal f).IsOver (Spec (.of K)) := ⟨by
  change pullback.diagonal f ≫ pullback.fst f f ≫ X ↘ Spec (.of K) = X ↘ Spec (.of K)
  rw [pullback.diagonal_fst_assoc]⟩

/-- The pairs of `K`-points of `X` with the same image in `Y` which are equal are the `K`-points
of the diagonal `X → X ×_Y X`. -/
lemma pullbackDiagonal_eq_preimage_range :
    (map (K := K) f).pullbackDiagonal =
      (fun p : Function.Pullback (map (K := K) f) (map f) ↦
        (pullbackHomeomorph (K := K) f f).symm ⟨p.1, p.2⟩) ⁻¹'
          range (map (K := K) (pullback.diagonal f)) := by
  let h := pullbackHomeomorph (K := K) f f
  have hΔ : ∀ p : SchemePoints K X, (h (map (pullback.diagonal f) p)).1 = (p, p) := fun p ↦ by
    refine Prod.ext (ext ?_) (ext ?_)
    · change (p.1 ≫ pullback.diagonal f) ≫ pullback.fst _ _ = p.1
      rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · change (p.1 ≫ pullback.diagonal f) ≫ pullback.snd _ _ = p.1
      rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
  ext ⟨⟨a, b⟩, hab⟩
  simp only [Function.pullbackDiagonal, mem_ofPred_eq, mem_preimage, mem_range]
  constructor
  · intro hab'
    refine ⟨a, h.injective ?_⟩
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext (by rw [hΔ]; exact Prod.ext rfl hab')
  · rintro ⟨p, hp⟩
    have := congrArg (fun r ↦ (h r).1) hp
    rw [Homeomorph.apply_symm_apply, hΔ] at this
    change (p, p) = (a, b) at this
    rw [Prod.ext_iff] at this
    exact this.1.symm.trans this.2

/-- XII.3.1 (viii), direct implication: a separated `K`-morphism `f : X → Y` induces a separated
map `X(K) → Y(K)` (the diagonal of `X(K)` over `Y(K)` is closed). -/
theorem isSeparatedMap_map [IsSeparated f] : IsSeparatedMap (map (K := K) f) := by
  rw [isSeparatedMap_iff_isClosed_diagonal, pullbackDiagonal_eq_preimage_range]
  refine (isClosedEmbedding_map (pullback.diagonal f)).isClosed_range.preimage ?_
  exact (pullbackHomeomorph (K := K) f f).symm.continuous.comp
    (continuous_induced_rng.mpr continuous_subtype_val)

/-- XII.3.1 (viii), from XII.2.2: a morphism `f : X → Y` of `ℂ`-schemes locally of finite type is
separated if and only if `X(ℂ) → Y(ℂ)` is a separated map. -/
theorem isSeparated_iff_isSeparatedMap (H : ClosureComparisonStatement) {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] :
    IsSeparated f ↔ IsSeparatedMap (map (K := ℂ) f) := by
  refine ⟨fun _ ↦ isSeparatedMap_map (K := ℂ) f, fun hsep ↦ ?_⟩
  have : LocallyOfFiniteType (f ≫ Y ↘ Spec (.of ℂ)) := by rw [comp_over]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of ℂ))
  let P := pullback f f
  have : LocallyOfFiniteType (P ↘ Spec (.of ℂ)) :=
    show LocallyOfFiniteType (pullback.fst f f ≫ X ↘ Spec (.of ℂ)) from inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (P ↘ Spec (.of ℂ))
  let Δ := pullback.diagonal f
  let h := pullbackHomeomorph (K := ℂ) f f
  let e₀ : FiberProduct ℂ f f ≃ₜ Function.Pullback (map (K := ℂ) f) (map f) :=
    { toFun x := ⟨x.1, x.2⟩
      invFun x := ⟨x.1, x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := continuous_induced_rng.mpr continuous_subtype_val
      continuous_invFun := continuous_induced_rng.mpr continuous_subtype_val }
  let e : SchemePoints ℂ P ≃ₜ Function.Pullback (map (K := ℂ) f) (map f) := h.trans e₀
  have hrange : range (map (K := ℂ) Δ) = e ⁻¹' (map (K := ℂ) f).pullbackDiagonal := by
    rw [pullbackDiagonal_eq_preimage_range]
    ext r
    simp only [mem_preimage]
    change _ ↔ h.symm (h r) ∈ _
    rw [Homeomorph.symm_apply_apply]
  have hpre : pt ⁻¹' range Δ = range (map (K := ℂ) Δ) := by
    ext r
    refine ⟨fun hr ↦ exists_map_eq Δ r hr, ?_⟩
    rintro ⟨p, rfl⟩
    exact ⟨p.pt, (pt_map Δ p).symm⟩
  have hclosed : IsClosed (pt ⁻¹' range Δ : Set (SchemePoints ℂ P)) := by
    rw [hpre, hrange]
    exact (isSeparatedMap_iff_isClosed_diagonal.mp hsep).preimage e.continuous
  have := (isClosed_iff_of_closureComparison H
    (isLocallyConstructible_of_isLocallyClosed Δ.isLocallyClosed_range)).mpr hclosed
  exact ⟨IsClosedImmersion.of_isPreimmersion Δ this⟩

end Relative

end SchemePoints

end SGA.SGA1.ExposeXII
