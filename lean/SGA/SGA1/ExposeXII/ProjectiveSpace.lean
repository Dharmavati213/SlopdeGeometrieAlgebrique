/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Projective.ProjectiveSpaceSpec
import SGA.Foundations.Projective.Dehomogenization
import SGA.Foundations.Projective.Morphisms
import SGA.SGA1.ExposeXII.SchemePoints
import SGA.SGA1.ExposeXII.SchemeLimits

/-!
# SGA 1, Exposé XII: points of projective space

For `K` a proper nontrivially normed field (`ℂ`), the space of `K`-points of the projective space
`ℙ(σ; K)` (`σ` finite) is compact (`ProjectivePoints.compactSpace_projectiveSpace`): it is
covered by the finitely many compact polydiscs `{|xⱼ/xₖ| ≤ 1}` of the standard charts
`D₊(xₖ)(K) ≅ K^σ`, every point lying in the polydisc of a chart where `|xₖ|` is maximal.

Consequently (XII.3.2 (v) for projective morphisms), for a `K`-scheme `Y`, the projection
`ℙ(σ; Y)(K) → Y(K)` is proper (`ProjectivePoints.isProperMap_map_projectiveSpace`, through the
base change `ℙ(σ; Y) = ℙ(σ; K) ×_K Y` and `SchemePoints.isProperMap_map_of_isPullback`), and so is
`X(K) → Y(K)` for every H-projective `f : X ⟶ Y`
(`ProjectivePoints.isProperMap_map_of_isHProjective`).
-/

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology Set MvPolynomial
open HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpace

namespace SGA.SGA1.ExposeXII

namespace SchemePoints

section General

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]

attribute [local instance] specOver

/-- Every `K`-point of `Spec R` comes from a `K`-algebra map `R → K`. -/
lemma exists_specPoint_eq (R : Type u) [CommRing R] [Algebra K R]
    (q : SchemePoints K (Spec (.of R))) : ∃ χ : Points K R, specPoint R χ = q := by
  obtain ⟨q, hq⟩ := q
  let ψ := Spec.preimage q
  have hψ : Spec.map ψ = q := Spec.map_preimage q
  have hc : ∀ c : K, ψ.hom (algebraMap K R c) = c := by
    have : Spec.map (CommRingCat.ofHom (algebraMap K R) ≫ ψ) = Spec.map (𝟙 _) := by
      rw [Spec.map_comp, hψ, Spec.map_id]
      exact hq
    intro c
    exact congr($(Spec.map_injective this).hom c)
  refine ⟨Points.ofAlgHom { ψ.hom with commutes' := hc }, Subtype.ext ?_⟩
  exact hψ

/-- A `K`-point of `X` in the image of an open immersion `f : Y ⟶ X` comes from `Y`. -/
lemma exists_map_eq_of_isOpenImmersion (f : Y ⟶ X) [IsOpenImmersion f]
    [f.IsOver (Spec (.of K))] (p : SchemePoints K X) (hp : p.pt ∈ range f) :
    ∃ q : SchemePoints K Y, map f q = p := by
  obtain ⟨p, hp'⟩ := p
  have hr : range p.base ⊆ range f.base := by
    rintro _ ⟨z, rfl⟩
    have : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst this
    exact hp
  refine ⟨⟨IsOpenImmersion.lift f p hr, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac f p hr)⟩
  rw [← comp_over f (Spec (.of K)), ← Category.assoc, IsOpenImmersion.lift_fac]
  exact hp'

omit [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] in
/-- The map on `K`-points induced by an isomorphism of `K`-schemes is surjective. -/
lemma surjective_map_of_isIso (f : X ⟶ Y) [IsIso f] [X.Over (Spec (.of K))]
    [Y.Over (Spec (.of K))] [f.IsOver (Spec (.of K))] : Function.Surjective (map (K := K) f) := by
  have : (inv f).IsOver (Spec (.of K)) := ⟨by rw [IsIso.inv_comp_eq, comp_over]⟩
  intro p
  refine ⟨map (inv f) p, ext ?_⟩
  change (p.1 ≫ inv f) ≫ f = p.1
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- `Spec K`, as a `K`-scheme through the identity. -/
abbrev selfOver : (Spec (.of K)).Over (Spec (.of K)) := .ofHom (𝟙 _)

lemma subsingleton_selfOver :
    letI := selfOver (K := K)
    Subsingleton (SchemePoints K (Spec (.of K))) :=
  letI := selfOver (K := K)
  ⟨fun p q ↦ ext ((Category.comp_id _).symm.trans
    (p.2.trans (q.2.symm.trans (Category.comp_id _))))⟩

variable [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]

/-- An isomorphism of `K`-schemes induces a homeomorphism on `K`-points. -/
def homeomorphOfIso (e : X ≅ Y) [e.hom.IsOver (Spec (.of K))] :
    SchemePoints K X ≃ₜ SchemePoints K Y :=
  have : e.inv.IsOver (Spec (.of K)) := ⟨by rw [Iso.inv_comp_eq, comp_over]⟩
  { toFun := map e.hom
    invFun := map e.inv
    left_inv p := ext (by change (p.1 ≫ e.hom) ≫ e.inv = p.1; simp)
    right_inv p := ext (by change (p.1 ≫ e.inv) ≫ e.hom = p.1; simp)
    continuous_toFun := continuous_map _
    continuous_invFun := continuous_map _ }

@[simp] lemma homeomorphOfIso_apply (e : X ≅ Y) [e.hom.IsOver (Spec (.of K))]
    (p : SchemePoints K X) : homeomorphOfIso e p = map e.hom p := rfl

/-- The base change `P = P₀ ×_K Y ⟶ Y` of a `K`-scheme `P₀` whose `K`-points form a compact space
induces a proper map `P(K) → Y(K)`. -/
theorem isProperMap_map_of_isPullback {P P₀ : Scheme.{u}} [P.Over (Spec (.of K))]
    [P₀.Over (Spec (.of K))] (a : P ⟶ P₀) (π : P ⟶ Y) [a.IsOver (Spec (.of K))]
    [π.IsOver (Spec (.of K))]
    (h : IsPullback a π (P₀ ↘ Spec (.of K)) (Y ↘ Spec (.of K)))
    [CompactSpace (SchemePoints K P₀)] : IsProperMap (map (K := K) π) := by
  let f : P₀ ⟶ Spec (.of K) := P₀ ↘ Spec (.of K)
  let g : Y ⟶ Spec (.of K) := Y ↘ Spec (.of K)
  let := selfOver (K := K)
  have := subsingleton_selfOver (K := K)
  have : Scheme.Hom.IsOver f (Spec (.of K)) := ⟨Category.comp_id _⟩
  have : Scheme.Hom.IsOver g (Spec (.of K)) := ⟨Category.comp_id _⟩
  let := pullbackOver (K := K) f g
  have := isOver_pullback_fst (K := K) f g
  have := isOver_pullback_snd (K := K) f g
  let e := h.isoPullback
  have : e.hom.IsOver (Spec (.of K)) := ⟨by
    change e.hom ≫ pullback.fst f g ≫ P₀ ↘ Spec (.of K) = _
    rw [IsPullback.isoPullback_hom_fst_assoc, comp_over]⟩
  have hsnd : map (K := K) π = (fun x ↦ x.1.2) ∘ pullbackHomeomorph (K := K) f g ∘ map e.hom := by
    funext p
    refine ext ?_
    change p.1 ≫ π = (p.1 ≫ e.hom) ≫ pullback.snd f g
    rw [Category.assoc, IsPullback.isoPullback_hom_snd]
  have huniv : FiberProduct K f g = univ := eq_univ_of_forall fun _ ↦ Subsingleton.elim _ _
  have hclosed : IsClosed (FiberProduct K f g) := huniv ▸ isClosed_univ
  rw [hsnd]
  exact (isProperMap_snd_of_compactSpace.comp hclosed.isClosedEmbedding_subtypeVal.isProperMap).comp
    ((pullbackHomeomorph f g).isProperMap.comp (homeomorphOfIso (K := K) e).isProperMap)

end General

end SchemePoints

namespace ProjectivePoints

variable (K : Type u) [NontriviallyNormedField K] (σ : Type u)

/-- `Proj K[xᵢ : i ∈ σ]` as a `K`-scheme. -/
abbrev projOver : (Proj (grading σ K)).Over (Spec (.of K)) := .ofHom (projToSpec σ K)

/-- The `K`-algebra structure of `K[xᵢ]_(t)`. -/
abbrev awayAlgebra (t : MvPolynomial σ K) : Algebra K (Away (grading σ K) t) :=
  (awayC t).toAlgebra

attribute [local instance] projOver awayAlgebra SchemePoints.specOver

variable {K σ}

/-- The standard open immersion `D₊(xᵢ) = Spec K[xⱼ/xᵢ] ⟶ Proj K[x]`. -/
abbrev awayι (i : σ) : Spec (.of (Away (grading σ K) (X i))) ⟶ Proj (grading σ K) :=
  Proj.awayι (grading σ K) (X i) (X_mem_grading i) one_pos

instance isOver_awayι (i : σ) : (awayι (K := K) i).IsOver (Spec (.of K)) :=
  ⟨awayι_projToSpec (X_mem_grading i)⟩

/-- The chart `D₊(xᵢ)(K) → ℙ(K)`. -/
def chart (i : σ) (χ : Points K (Away (grading σ K) (X i))) : SchemePoints K (Proj (grading σ K)) :=
  SchemePoints.map (awayι i) (SchemePoints.specPoint _ χ)

lemma continuous_chart (i : σ) : Continuous (chart (K := K) i) :=
  (SchemePoints.continuous_map _).comp (SchemePoints.continuous_specPoint _)

lemma exists_chart_eq (p : SchemePoints K (Proj (grading σ K))) :
    ∃ i χ, chart (K := K) i χ = p := by
  have : p.pt ∈ (⊤ : (Proj (grading σ K)).Opens) := trivial
  rw [← iSup_basicOpen_X, TopologicalSpace.Opens.mem_iSup] at this
  obtain ⟨i, hi⟩ := this
  rw [← Proj.opensRange_awayι _ _ (X_mem_grading i) one_pos] at hi
  obtain ⟨q, rfl⟩ := SchemePoints.exists_map_eq_of_isOpenImmersion (awayι i) p hi
  obtain ⟨χ, rfl⟩ := SchemePoints.exists_specPoint_eq _ q
  exact ⟨i, χ, rfl⟩

/-- The coordinate `xⱼ / xᵢ` on `D₊(xᵢ)`. -/
abbrev coord (i j : σ) : Away (grading σ K) (X i) := awayX i rfl j

lemma coord_self (i : σ) : coord (K := K) i i = 1 := by
  ext
  simp only [coord, awayX, Away.val_mk, val_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

/-- The change of coordinates on `D₊(xᵢxₖ)`: `xⱼ/xᵢ = (xₖ/xᵢ) (xⱼ/xₖ)`. -/
lemma awayMap_coord (i k j : σ) :
    awayMap (grading σ K) (X_mem_grading k) (rfl : X i * X k = X i * X k) (coord i j) =
      awayMap (grading σ K) (X_mem_grading k) rfl (coord i k) *
        awayMap (grading σ K) (X_mem_grading i) (mul_comm (X i) (X k)) (coord k j) := by
  simp only [coord, awayX, awayMap_mk]
  ext
  simp only [val_mul, Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/-- The `K`-algebra `K[xⱼ/xᵢ]` is generated by the coordinates `xⱼ/xᵢ`. -/
lemma surjective_aeval_coord (i : σ) :
    Function.Surjective (aeval (R := K) (coord (K := K) i)) := by
  intro y
  refine ⟨rename Subtype.val (awayDehomogenize i rfl y), ?_⟩
  rw [aeval_rename]
  have : (aeval (R := K) (coord (K := K) i ∘ Subtype.val)).toRingHom =
      (awayHomogenize i (rfl : (X i : MvPolynomial σ K) = X i)) := rfl
  change (aeval (R := K) (coord (K := K) i ∘ Subtype.val)).toRingHom _ = y
  rw [this]
  exact congr($(awayHomogenize_comp_awayDehomogenize i rfl) y)

/-- The closed polydisc `{|xⱼ/xᵢ| ≤ 1}` in the chart `D₊(xᵢ)(K)`. -/
def unitPolydisc (i : σ) : Set (Points K (Away (grading σ K) (X i))) :=
  {χ | ∀ j, ‖χ (coord i j)‖ ≤ 1}

lemma isCompact_unitPolydisc [ProperSpace K] (i : σ) : IsCompact (unitPolydisc (K := K) i) := by
  have h := Points.isClosedEmbedding_coords (surjective_aeval_coord (K := K) i)
  have : unitPolydisc (K := K) i =
      Points.coords (aeval (coord i)) ⁻¹' univ.pi fun _ ↦ Metric.closedBall 0 1 := by
    ext χ
    simp [unitPolydisc, Points.coords]
  rw [this]
  exact h.isCompact_preimage (isCompact_univ_pi fun _ ↦ isCompact_closedBall 0 1)

/-- Every `K`-point of `Proj K[x]` lies in the closed polydisc `{|xⱼ/xₖ| ≤ 1}` of some chart
`D₊(xₖ)`: take `k` with `|xₖ|` maximal. -/
lemma exists_chart_mem_unitPolydisc [Finite σ] (p : SchemePoints K (Proj (grading σ K))) :
    ∃ k, ∃ ψ ∈ unitPolydisc (K := K) k, chart k ψ = p := by
  obtain ⟨i, χ, rfl⟩ := exists_chart_eq p
  have : Nonempty σ := ⟨i⟩
  obtain ⟨k, hk⟩ := Finite.exists_max fun j ↦ ‖χ (coord i j)‖
  have hk1 : 1 ≤ ‖χ (coord i k)‖ := by
    have := hk i
    rwa [coord_self, map_one, norm_one] at this
  have hk0 : χ (coord i k) ≠ 0 := norm_pos_iff.mp (one_pos.trans_le hk1)
  have hXi : (X i : MvPolynomial σ K) ∈ grading σ K 1 := X_mem_grading i
  have hXk : (X k : MvPolynomial σ K) ∈ grading σ K 1 := X_mem_grading k
  let φik := awayMap (grading σ K) hXk (rfl : X i * X k = X i * X k)
  let φki := awayMap (grading σ K) hXi (mul_comm (X i) (X k))
  let := φik.toAlgebra
  have := Away.isLocalization_mul hXi hXk (rfl : X i * X k = X i * X k) one_ne_zero
  have helem : Away.isLocalizationElem hXi hXk = coord (K := K) i k := by
    ext
    simp [coord, awayX, Away.val_mk]
  have hu : IsUnit (χ.toRingHom (Away.isLocalizationElem hXi hXk)) := by
    rw [helem]
    exact hk0.isUnit
  let χ' : Away (grading σ K) (X i * X k) →+* K := IsLocalization.Away.lift _ hu
  have hχ' : χ'.comp φik = χ.toRingHom := IsLocalization.Away.lift_comp _ hu
  have hC (c : K) : φki (awayC (X k) c) = φik (awayC (X i) c) := by
    simp only [φki, φik, awayC, RingHom.comp_apply, awayMap_fromZeroRingHom]
  let ψ : Points K (Away (grading σ K) (X k)) := Points.ofAlgHom
    { χ'.comp φki with
      commutes' := fun c ↦ by
        change χ' (φki (awayC (X k) c)) = c
        rw [hC, ← RingHom.comp_apply, hχ']
        exact χ.apply_algebraMap c }
  have hchart : chart k ψ = chart i χ := by
    apply SchemePoints.ext
    change Spec.map (CommRingCat.ofHom (χ'.comp φki)) ≫ awayι k =
      Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ awayι i
    rw [← hχ', CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
      Category.assoc, Category.assoc, awayι, awayι, Proj.SpecMap_awayMap_awayι,
      Proj.SpecMap_awayMap_awayι]
  refine ⟨k, ψ, fun j ↦ ?_, hchart⟩
  have hrel := congrArg χ' (awayMap_coord (K := K) i k j)
  rw [map_mul] at hrel
  have e (a) : χ' (φik a) = χ a := congr($hχ' a)
  change χ' (φik (coord i j)) = χ' (φik (coord i k)) * χ' (φki (coord k j)) at hrel
  rw [e, e] at hrel
  change ‖χ' (φki (coord k j))‖ ≤ 1
  have h1 : ‖χ (coord i k)‖ * ‖χ' (φki (coord k j))‖ ≤ ‖χ (coord i k)‖ * 1 := by
    rw [← norm_mul, ← hrel, mul_one]
    exact hk j
  exact le_of_mul_le_mul_left h1 (one_pos.trans_le hk1)

/-- The `K`-points of projective space form a compact space (`K` a proper normed field, e.g.
`ℂ`): they are covered by the finitely many compact polydiscs `{|xⱼ/xₖ| ≤ 1}`. -/
instance compactSpace [Finite σ] [ProperSpace K] :
    CompactSpace (SchemePoints K (Proj (grading σ K))) := by
  have : (univ : Set (SchemePoints K (Proj (grading σ K)))) =
      ⋃ k, chart k '' unitPolydisc (K := K) k := by
    refine (eq_univ_of_forall fun p ↦ ?_).symm
    obtain ⟨k, ψ, hψ, rfl⟩ := exists_chart_mem_unitPolydisc p
    exact mem_iUnion.mpr ⟨k, ψ, hψ, rfl⟩
  exact ⟨this ▸ isCompact_iUnion fun k ↦ (isCompact_unitPolydisc k).image (continuous_chart k)⟩

variable (σ) in
/-- The `K`-points of the projective space `ℙ(σ; Spec K)` form a compact space. -/
instance compactSpace_projectiveSpace [Finite σ] [ProperSpace K] :
    CompactSpace (SchemePoints K ℙ(σ; Spec (.of K))) :=
  have : (isoProj σ K).hom.IsOver (Spec (.of K)) := ⟨isoProj_hom_over σ K⟩
  (SchemePoints.homeomorphOfIso (K := K) (isoProj σ K)).compactSpace

end ProjectivePoints

namespace ProjectivePoints

variable {K : Type u} [NontriviallyNormedField K] {σ : Type u}

variable (K σ) in
/-- `ℙ(σ; Y)` as a `K`-scheme, for a `K`-scheme `Y`. -/
abbrev projectiveSpaceOver (Y : Scheme.{u}) [Y.Over (Spec (.of K))] :
    ℙ(σ; Y).Over (Spec (.of K)) :=
  .ofHom (ℙ(σ; Y) ↘ Y ≫ Y ↘ Spec (.of K))

/-- XII.3.2 (v) for projective space: for a `K`-scheme `Y`, the projection `ℙ(σ; Y)(K) → Y(K)`
is proper (`ℙ(σ; Y) = ℙ(σ; K) ×_K Y` and `ℙ(σ; K)(K)` is compact). -/
theorem isProperMap_map_projectiveSpace [Finite σ] [ProperSpace K] (Y : Scheme.{u})
    [Y.Over (Spec (.of K))] [ℙ(σ; Y).Over (Spec (.of K))] [(ℙ(σ; Y) ↘ Y).IsOver (Spec (.of K))] :
    IsProperMap (SchemePoints.map (K := K) (ℙ(σ; Y) ↘ Y)) := by
  have : (ProjectiveSpace.map (Spec (.of K)) (Y ↘ Spec (.of K)) :
      ℙ(σ; Y) ⟶ ℙ(σ; Spec (.of K))).IsOver (Spec (.of K)) := ⟨by
    rw [map_over, comp_over]⟩
  exact SchemePoints.isProperMap_map_of_isPullback _ _ (isPullback_map (Y ↘ Spec (.of K)))

/-- XII.3.2 (v) for H-projective morphisms: an H-projective `K`-morphism `f : X ⟶ Y` (a closed
subscheme of some `ℙ(σ; Y)`) induces a proper map `X(K) → Y(K)`. -/
theorem isProperMap_map_of_isHProjective [ProperSpace K] {X Y : Scheme.{u}}
    [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] (f : X ⟶ Y) [f.IsOver (Spec (.of K))]
    [hf : IsHProjective f] : IsProperMap (SchemePoints.map (K := K) f) := by
  obtain ⟨σ', _, i, _, hi⟩ := hf.exists_isClosedImmersion
  let := projectiveSpaceOver K σ' Y
  have : (ℙ(σ'; Y) ↘ Y).IsOver (Spec (.of K)) := ⟨rfl⟩
  have : i.IsOver (Spec (.of K)) := ⟨by
    change i ≫ ℙ(σ'; Y) ↘ Y ≫ Y ↘ Spec (.of K) = _
    rw [← Category.assoc, hi, comp_over]⟩
  have : SchemePoints.map (K := K) f = SchemePoints.map (ℙ(σ'; Y) ↘ Y) ∘ SchemePoints.map i := by
    funext p
    exact SchemePoints.ext (by
      change p.1 ≫ f = (p.1 ≫ i) ≫ ℙ(σ'; Y) ↘ Y
      rw [Category.assoc, hi])
  rw [this]
  exact (isProperMap_map_projectiveSpace Y).comp
    (SchemePoints.isClosedEmbedding_map i).isProperMap

end ProjectivePoints

end SGA.SGA1.ExposeXII
