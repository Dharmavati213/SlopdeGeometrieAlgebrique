/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.Analysis.Complex.Polynomial.Basic
import SGA.SGA1.ExposeXII.Points
import SGA.SGA1.ExposeXII.Etale
import SGA.SGA1.ExposeXII.Comparison
import SGA.SGA1.ExposeXII.JacobsonConstructible
import SGA.SGA1.ExposeXII.ProperMapLocal
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# SGA 1, Exposé XII, §§1–3: the space `X(K)` of a `K`-scheme

XII.1.1 attaches to a scheme `X` locally of finite type over `ℂ` an analytic space `X^an`
with underlying set `X(ℂ)`. Here we build its underlying topological space for any `K`-scheme
`X` (`K` a topological field, for instance `ℂ`): `SchemePoints K X` is the set of `K`-points,
with the finest topology making every affine chart `U(K) → X(K)` continuous.

* The charts are open embeddings (`isOpenEmbedding_chart`): on an affine open `U`, the topology
  is that of `Points K Γ(X, U)`, i.e. the subspace topology of any presentation. This is the
  gluing step of XII.1.1; for `X` affine, `X(K) ≃ₜ Points K Γ(X, ⊤)` (`homeomorphPoints`).
  For `X` locally of finite type over an algebraically closed `K`, `X(K)` is the set of closed
  points of `X` (`equivClosedPoints`).
* XII.1.2: `K`-morphisms give continuous maps (`continuous_map`); XII.2.3, direct implications:
  `X(K) → X` is continuous (`continuous_pt`).
* XII.3.1 (iii), (vii), (x), (xi) and XII.3.2 (iii), (iv), (vi), direct implications:
  étale morphisms give local homeomorphisms, injective morphisms injective maps, monomorphisms
  injective maps, open (closed) immersions open (closed) embeddings, immersions embeddings,
  finite morphisms maps with finite fibres. XII.3.2 (i): a quasi-compact `f` is surjective if and
  only if `f(K)` is (`surjective_map_iff`, via Chevalley's theorem and the Jacobson property);
  XII.2.3 and XII.3.2 (ii) follow from XII.2.2 (`isClosed_iff_of_closureComparison`,
  `isOpen_iff_of_closureComparison`, `dense_iff_of_closureComparison`, `denseRange_map_iff`).
* XII.2.1 (i'), with (viii) in dimension `0`: `discreteTopology_iff` (over `ℂ`);
  XII.2.1 (i), XII.2.4 and XII.2.6 (one direction each): `nonempty_iff`,
  `connectedSpace_of_connectedSpace`, `connectedComponentsMap_surjective`; the analytic
  statements XII.2.2, XII.2.4, XII.2.6 are recorded over `ℂ`.
* For `K` a proper nontrivially normed field (`ℂ`): finite morphisms give proper maps
  (`isProperMap_map`, XII.3.2 (v), (vi) direct), and a finite étale morphism `Y → X` gives a
  covering map `Y(K) → X(K)` with finite fibres (`isCoveringMap_map`): the functor of XII.5.1.

Separated schemes have Hausdorff spaces of points: see `Separated.lean`.
-/

universe u

noncomputable section

namespace SGA.SGA1.ExposeXII

open AlgebraicGeometry CategoryTheory Topology Set Opposite

variable (K : Type u) [Field K]

/-- XII.1.1: the set `X(K)` of `K`-points of a `K`-scheme `X`. -/
def SchemePoints (X : Scheme.{u}) [X.Over (Spec (.of K))] : Type u :=
  {p : Spec (.of K) ⟶ X // p ≫ X ↘ Spec (.of K) = 𝟙 _}

namespace SchemePoints

variable {K} {X : Scheme.{u}} [X.Over (Spec (.of K))]

/-- The point of `X` underlying a `K`-point. -/
def pt (p : SchemePoints K X) : X := p.1 (IsLocalRing.closedPoint K)

lemma ext {p q : SchemePoints K X} (h : p.1 = q.1) : p = q := Subtype.ext h

/-- XII.1.1: for `X` locally of finite type over an algebraically closed field `K`, the
`K`-points of `X` are its closed points (mathlib's `pointEquivClosedPoint`). -/
def equivClosedPoints [IsAlgClosed K] [LocallyOfFiniteType (X ↘ Spec (.of K))] :
    SchemePoints K X ≃ closedPoints X :=
  pointEquivClosedPoint (X ↘ Spec (.of K))

@[simp] lemma coe_equivClosedPoints [IsAlgClosed K] [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (p : SchemePoints K X) : (equivClosedPoints p : X) = p.pt := rfl

variable (K) in
/-- The structure map `K → Γ(X, U)`. -/
def structureMap (U : X.Opens) : CommRingCat.of K ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (.of K)).inv ≫
    (X ↘ Spec (.of K)).appLE ⊤ U (le_top.trans_eq (Scheme.Hom.preimage_top _).symm)

/-- The `K`-algebra structure on sections. -/
abbrev sectionsAlgebra (U : X.Opens) : Algebra K Γ(X, U) := (structureMap K U).hom.toAlgebra

attribute [local instance] sectionsAlgebra

lemma algebraMap_sections (U : X.Opens) :
    algebraMap K Γ(X, U) = (structureMap K U).hom := rfl

lemma structureMap_map {U V : X.Opens} (h : V ≤ U) :
    structureMap K U ≫ X.presheaf.map (homOfLE h).op = structureMap K V := by
  rw [structureMap, structureMap, Category.assoc, Scheme.Hom.appLE_map]

lemma fromSpec_over {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ X ↘ Spec (.of K) = Spec.map (structureMap K U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec (X ↘ Spec (.of K)) (isAffineOpen_top _) hU (by simp),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-! ### Affine charts -/

section Chart

variable {U : X.Opens} (hU : IsAffineOpen U)

/-- The `K`-point of `X` attached to a `K`-point of an affine open `U`. -/
def chart (φ : Points K Γ(X, U)) : SchemePoints K X :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec, by
    rw [Category.assoc, fromSpec_over, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    exact φ.apply_algebraMap c⟩

lemma chart_injective : Function.Injective (chart (K := K) hU) := by
  intro φ ψ h
  have h' := congr_arg Subtype.val h
  simp only [chart] at h'
  have := Spec.map_injective ((cancel_mono hU.fromSpec).mp h')
  ext a
  exact congr($this a)

lemma pt_chart (φ : Points K Γ(X, U)) : (chart hU φ).pt ∈ U := by
  change (chart hU φ).pt ∈ (U : Set X)
  rw [← hU.range_fromSpec]
  exact ⟨_, rfl⟩

/-- Every `K`-point of `X` lying in `U` comes from a `K`-point of `U`. -/
lemma exists_chart_eq (p : SchemePoints K X) (hp : p.pt ∈ U) : ∃ φ, chart hU φ = p := by
  have hle : ⊤ ≤ p.1 ⁻¹ᵁ U := fun x _ ↦ by
    rwa [Subsingleton.elim x (IsLocalRing.closedPoint K)]
  let g : Γ(X, U) ⟶ CommRingCat.of K := p.1.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (.of K)).hom
  have hp' : Spec.map g ≫ hU.fromSpec = p.1 := by
    rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec p.1 hU
      (isAffineOpen_top _), IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
      ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
  have hg : structureMap K U ≫ g = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← fromSpec_over hU, reassoc_of% hp', p.2, Spec.map_id]
  refine ⟨Points.ofAlgHom { g.hom with commutes' := fun c ↦ congr($hg c) }, Subtype.ext ?_⟩
  exact hp'

lemma range_chart : range (chart (K := K) hU) = {p : SchemePoints K X | p.pt ∈ U} :=
  Subset.antisymm (range_subset_iff.mpr (pt_chart hU)) fun p hp ↦ exists_chart_eq hU p hp

/-- Restriction of sections, as a `K`-algebra map. -/
def resAlgHom {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →ₐ[K] Γ(X, V) :=
  { (X.presheaf.map (homOfLE h).op).hom with
    commutes' := fun c ↦ congr($(structureMap_map (K := K) h) c) }

@[simp] lemma resAlgHom_apply {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    resAlgHom (K := K) h a = X.presheaf.map (homOfLE h).op a := rfl

lemma chart_map {V : X.Opens} (hV : IsAffineOpen V) (h : V ≤ U) (φ : Points K Γ(X, V)) :
    chart hU (Points.map (resAlgHom h) φ) = chart hV φ := by
  apply Subtype.ext
  simp only [chart]
  rw [← IsAffineOpen.map_fromSpec hU hV (homOfLE h).op, ← Category.assoc, ← Spec.map_comp]
  rfl

lemma exists_isAffineOpen_mem (p : SchemePoints K X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ p.pt ∈ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (mem_univ p.pt) isOpen_univ
  exact ⟨U, hU, hpU⟩

/-- The `K`-points of a basic open `D(s)` of an affine open `U` form an open subset of `U(K)`. -/
lemma exists_basicOpen_chart {V : X.Opens} {φ : Points K Γ(X, U)}
    (hφ : (chart hU φ).pt ∈ V) : ∃ (s : Γ(X, U)) (w : Points K Γ(X, X.basicOpen s)),
      X.basicOpen s ≤ V ∧ Points.map (resAlgHom (X.basicOpen_le s)) w = φ := by
  obtain ⟨s, hsV, hs⟩ := hU.exists_basicOpen_le ⟨_, hφ⟩ (pt_chart hU φ)
  obtain ⟨w, hw⟩ := exists_chart_eq (hU.basicOpen s) (chart hU φ) hs
  exact ⟨s, w, hsV, chart_injective hU (by rw [chart_map hU (hU.basicOpen s), hw])⟩

end Chart

/-! ### The topology on `X(K)` -/

section Topology

variable [TopologicalSpace K]

variable (K X) in
/-- XII.1.1: the topology of `X(K)`: the finest topology making the charts `U(K) → X(K)`,
`U` an affine open, continuous. -/
instance : TopologicalSpace (SchemePoints K X) :=
  ⨆ U : X.affineOpens, .coinduced (chart (K := K) U.2) inferInstance

variable {U : X.Opens} (hU : IsAffineOpen U)

lemma continuous_chart : Continuous (chart (K := K) hU) :=
  continuous_iff_coinduced_le.mpr (le_iSup_of_le (⟨U, hU⟩ : X.affineOpens) le_rfl)

/-- A map out of `X(K)` is continuous if and only if it is on every affine chart. -/
lemma continuous_iff' {Z : Type*} [TopologicalSpace Z] {F : SchemePoints K X → Z} :
    Continuous F ↔ ∀ (U : X.Opens) (hU : IsAffineOpen U), Continuous (F ∘ chart hU) := by
  refine ⟨fun hF U hU ↦ hF.comp (continuous_chart hU), fun h ↦ ?_⟩
  exact continuous_iSup_dom.mpr fun U ↦ continuous_coinduced_dom.mpr (h U.1 U.2)


variable [IsTopologicalDivisionRing K] [T1Space K]

include hU in
/-- The restriction from an affine open to a basic open is an open embedding on points. -/
lemma isOpenEmbedding_map_resAlgHom_basicOpen (f : Γ(X, U)) {W : X.Opens}
    (hW : W = X.basicOpen f) (h : W ≤ U) :
    IsOpenEmbedding (Points.map (K := K) (resAlgHom (K := K) h)) :=
  Points.isOpenEmbedding_map_of_isLocalization f _
    (hU.isLocalization_of_eq_basicOpen f (homOfLE h) hW)

lemma isOpen_chart_preimage_image {V : X.Opens} (hV : IsAffineOpen V)
    {O : Set (Points K Γ(X, U))} (hO : IsOpen O) :
    IsOpen (chart hV ⁻¹' (chart hU '' O)) := by
  rw [isOpen_iff_forall_mem_open]
  rintro φ ⟨ψ, hψO, hψφ⟩
  have hx : (chart hV φ).pt ∈ U ⊓ V := ⟨hψφ ▸ pt_chart hU ψ, pt_chart hV φ⟩
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter hU hV _ hx
  have hW : IsAffineOpen (X.basicOpen g) := hV.basicOpen g
  have hWV : X.basicOpen g ≤ V := X.basicOpen_le g
  have hWU : X.basicOpen g ≤ U := hfg ▸ X.basicOpen_le f
  have heV := isOpenEmbedding_map_resAlgHom_basicOpen (K := K) hV g rfl hWV
  have heU := isOpenEmbedding_map_resAlgHom_basicOpen (K := K) hU f hfg.symm hWU
  refine ⟨Points.map (resAlgHom hWV) '' (Points.map (resAlgHom hWU) ⁻¹' O), ?_,
    heV.isOpenMap _ (hO.preimage heU.continuous), ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨_, hw, by rw [chart_map hU hW, chart_map hV hW]⟩
  · obtain ⟨w, hw⟩ := exists_chart_eq hW (chart hV φ) (hfg ▸ hxf)
    refine ⟨w, ?_, chart_injective hV (by rw [chart_map hV hW, hw])⟩
    change Points.map (resAlgHom hWU) w ∈ O
    rwa [chart_injective hU (show chart hU (Points.map (resAlgHom hWU) w) = chart hU ψ by
      rw [chart_map hU hW, hw, hψφ])]

/-- XII.1.1: the chart `U(K) → X(K)` of an affine open `U` is an open embedding, whose image is
the set of `K`-points lying in `U`. In particular the topology of `X(K)` restricts, on each affine
open, to the topology of `Points` (the subspace topology for any presentation). -/
theorem isOpenEmbedding_chart : IsOpenEmbedding (chart (K := K) hU) :=
  .of_continuous_injective_isOpenMap (continuous_chart hU) (chart_injective hU) fun O hO ↦ by
    rw [isOpen_iSup_iff]
    rintro ⟨V, hV⟩
    rw [isOpen_coinduced]
    exact isOpen_chart_preimage_image hU hV hO

/-- For an affine scheme `X`, `X(K)` is the space of `K`-points of `Γ(X, ⊤)`. -/
def homeomorphPoints [IsAffine X] : SchemePoints K X ≃ₜ Points K Γ(X, ⊤) :=
  ((isOpenEmbedding_chart (K := K) (isAffineOpen_top X)).isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr (by rw [range_chart]; ext; simp)).trans (Homeomorph.Set.univ _))).symm

/-- XII.2.3, direct implications: the map `X(K) → X` is continuous; Zariski open subsets of `X`
have open sets of `K`-points. -/
theorem continuous_pt : Continuous (pt : SchemePoints K X → X) := by
  refine continuous_iff'.mpr fun U hU ↦ continuous_def.mpr fun V hV ↦ ?_
  rw [isOpen_iff_forall_mem_open]
  intro φ hφ
  obtain ⟨s, w, hsV, rfl⟩ := exists_basicOpen_chart hU (V := ⟨V, hV⟩) hφ
  have he := isOpenEmbedding_map_resAlgHom_basicOpen (K := K) hU s rfl (X.basicOpen_le s)
  refine ⟨range (Points.map (resAlgHom (X.basicOpen_le s))), ?_, he.isOpen_range, mem_range_self w⟩
  rintro _ ⟨w', rfl⟩
  change (chart hU (Points.map (resAlgHom (X.basicOpen_le s)) w')).pt ∈ V
  rw [chart_map hU (hU.basicOpen s)]
  exact hsV (pt_chart _ w')

end Topology

/-! ### Functoriality -/

section Functoriality

variable {Y : Scheme.{u}} [Y.Over (Spec (.of K))] (f : X ⟶ Y) [f.IsOver (Spec (.of K))]

/-- XII.1.2: the map `X(K) → Y(K)` induced by a `K`-morphism `X → Y`. -/
def map (p : SchemePoints K X) : SchemePoints K Y :=
  ⟨p.1 ≫ f, by rw [Category.assoc, comp_over, p.2]⟩

@[simp] lemma pt_map (p : SchemePoints K X) : (map f p).pt = f p.pt := rfl

omit [Y.Over (Spec (.of K))] [f.IsOver (Spec (.of K))] in
@[simp] lemma map_id : map (K := K) (𝟙 X) = id := by
  funext p; exact ext (Category.comp_id _)

lemma map_comp {Z : Scheme.{u}} [Z.Over (Spec (.of K))] (g : Y ⟶ Z) [g.IsOver (Spec (.of K))] :
    map (K := K) (f ≫ g) = map g ∘ map f := by
  funext p; exact ext (Category.assoc _ _ _).symm

/-- `f.appLE`, as a `K`-algebra map. -/
def appLEAlgHom {U : X.Opens} {V : Y.Opens} (e : U ≤ f ⁻¹ᵁ V) : Γ(Y, V) →ₐ[K] Γ(X, U) :=
  { (f.appLE V U e).hom with
    commutes' := fun c ↦ by
      change (structureMap K V ≫ f.appLE V U e) c = structureMap K U c
      congr 1
      simp only [structureMap, Category.assoc, Scheme.Hom.appLE_comp_appLE]
      congr 2
      have H : ∀ (g : X ⟶ Spec (.of K)) (_ : g = X ↘ Spec (.of K)) (e₁ : U ≤ g ⁻¹ᵁ ⊤)
          (e₂ : U ≤ (X ↘ Spec (.of K)) ⁻¹ᵁ ⊤),
          g.appLE ⊤ U e₁ = (X ↘ Spec (.of K)).appLE ⊤ U e₂ := by
        rintro g rfl _ _; rfl
      exact H _ (comp_over f _) _ _ }

lemma map_chart {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (φ : Points K Γ(X, U)) :
    map f (chart hU φ) = chart hV (Points.map (appLEAlgHom f e) φ) := by
  apply Subtype.ext
  simp only [map, chart]
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e, ← Category.assoc,
    ← Spec.map_comp]
  rfl

variable [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]

/-- XII.1.2: a `K`-morphism induces a continuous map on `K`-points. -/
theorem continuous_map : Continuous (map (K := K) f) := by
  refine continuous_iff'.mpr fun U hU ↦ continuous_iff_continuousAt.mpr fun φ ↦ ?_
  obtain ⟨V, hV, hxV⟩ := exists_isAffineOpen_mem (map f (chart hU φ))
  obtain ⟨s, w, hsV, rfl⟩ := exists_basicOpen_chart hU (V := f ⁻¹ᵁ V) hxV
  have he := isOpenEmbedding_map_resAlgHom_basicOpen (K := K) hU s rfl (X.basicOpen_le s)
  rw [← he.continuousAt_iff]
  have : (map f ∘ chart hU) ∘ Points.map (resAlgHom (X.basicOpen_le s)) =
      chart hV ∘ Points.map (appLEAlgHom (K := K) f hsV) := by
    funext w'
    simp only [Function.comp_apply]
    rw [chart_map hU (hU.basicOpen s), map_chart f (hU.basicOpen s) hV hsV]
  rw [this]
  exact ((continuous_chart hV).comp (Points.continuous_map _)).continuousAt

section Immersions

omit [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K] in
lemma map_injective [Mono f] : Function.Injective (map (K := K) f) := fun _ _ h ↦
  ext ((cancel_mono f).mp congr($h.1))

/-- XII.3.1 (xi), direct implication: an open immersion induces an open embedding on
`K`-points. -/
theorem isOpenEmbedding_map [IsOpenImmersion f] : IsOpenEmbedding (map (K := K) f) := by
  refine .of_continuous_injective_isOpenMap (continuous_map f) (map_injective f) fun O hO ↦ ?_
  have hO' : O = ⋃ (U : X.affineOpens), chart U.2 '' (chart U.2 ⁻¹' O) := by
    refine Subset.antisymm (fun p hp ↦ ?_) (iUnion_subset fun U ↦ image_preimage_subset _ _)
    obtain ⟨U, hU, hpU⟩ := exists_isAffineOpen_mem p
    obtain ⟨φ, rfl⟩ := exists_chart_eq hU p hpU
    exact mem_iUnion.mpr ⟨⟨U, hU⟩, φ, hp, rfl⟩
  rw [hO', image_iUnion]
  refine isOpen_iUnion fun ⟨U, hU⟩ ↦ ?_
  have hV : IsAffineOpen (f ''ᵁ U) := hU.image_of_isOpenImmersion f
  have e : U ≤ f ⁻¹ᵁ f ''ᵁ U := (f.preimage_image_eq U).ge
  have hbij : Function.Bijective (appLEAlgHom (K := K) f e) := by
    have : IsIso (f.appLE (f ''ᵁ U) U e) := by rw [← f.appIso_hom']; infer_instance
    exact ConcreteCategory.bijective_of_isIso (f.appLE (f ''ᵁ U) U e)
  let h := Points.homeomorph (K := K) (AlgEquiv.ofBijective _ hbij)
  have : map f '' (chart hU '' (chart hU ⁻¹' O)) =
      chart hV '' (h '' (chart hU ⁻¹' O)) := by
    rw [image_image, image_image]
    refine image_congr fun φ _ ↦ ?_
    rw [map_chart f hU hV e]
    congr 1
  rw [this]
  exact (isOpenEmbedding_chart hV).isOpenMap _ (h.isOpenMap _ ((hO.preimage (continuous_chart hU))))

/-- XII.3.2 (iii), direct implication: a closed immersion induces a closed embedding on
`K`-points. -/
theorem isClosedEmbedding_map [IsClosedImmersion f] : IsClosedEmbedding (map (K := K) f) := by
  refine .of_continuous_injective_isClosedMap (continuous_map f) (map_injective f) fun C hC ↦ ?_
  refine isClosed_iSup_iff.mpr fun ⟨V, hV⟩ ↦ isClosed_coinduced.mpr ?_
  have hW : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  let a := appLEAlgHom (K := K) f (le_refl (f ⁻¹ᵁ V))
  have ha : Function.Surjective a := by
    have := f.app_surjective V hV
    rwa [Scheme.Hom.app_eq_appLE] at this
  have : chart hV ⁻¹' (map f '' C) = Points.map a '' (chart hW ⁻¹' C) := by
    ext φ
    constructor
    · rintro ⟨p, hp, hpφ⟩
      have hpt : p.pt ∈ f ⁻¹ᵁ V := by
        have : (map f p).pt ∈ V := hpφ ▸ pt_chart hV φ
        exact this
      obtain ⟨ψ, rfl⟩ := exists_chart_eq hW p hpt
      exact ⟨ψ, hp, chart_injective hV ((map_chart f hW hV le_rfl ψ).symm.trans hpφ)⟩
    · rintro ⟨ψ, hψ, rfl⟩
      exact ⟨chart hW ψ, hψ, map_chart f hW hV le_rfl ψ⟩
  rw [this]
  exact (Points.isClosedEmbedding_map_of_surjective ha).isClosedMap _
    (hC.preimage (continuous_chart hW))

/-- XII.3.2 (iv), direct implication: an immersion induces an embedding on `K`-points. -/
theorem isEmbedding_map [IsImmersion f] : IsEmbedding (map (K := K) f) := by
  let U := f.coborderRange
  let : U.toScheme.Over (Spec (.of K)) := .ofHom (U.ι ≫ Y ↘ Spec (.of K))
  have : U.ι.IsOver (Spec (.of K)) := ⟨rfl⟩
  have : f.liftCoborder.IsOver (Spec (.of K)) := ⟨by
    change f.liftCoborder ≫ U.ι ≫ Y ↘ Spec (.of K) = X ↘ Spec (.of K)
    rw [← Category.assoc, f.liftCoborder_ι, comp_over]⟩
  have : map (K := K) f = map U.ι ∘ map f.liftCoborder :=
    funext fun p ↦ ext (by simp [map, U, f.liftCoborder_ι])
  rw [this]
  exact (isOpenEmbedding_map U.ι).isEmbedding.comp
    (isClosedEmbedding_map f.liftCoborder).isEmbedding

end Immersions

end Functoriality

/-! ### Finite morphisms have finite fibres on points -/

section Finite

variable {Y : Scheme.{u}} [Y.Over (Spec (.of K))] (f : Y ⟶ X) [f.IsOver (Spec (.of K))]

/-- XII.3.2 (vi), direct implication (fibres): a finite `K`-morphism `f : Y → X` has finite fibres
on `K`-points. -/
theorem finite_map_preimage_of_isFinite [IsFinite f] (x : SchemePoints K X) :
    (map f ⁻¹' {x}).Finite := by
  obtain ⟨U, hU, hxU⟩ := exists_isAffineOpen_mem x
  obtain ⟨φ, rfl⟩ := exists_chart_eq hU x hxU
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  let g := appLEAlgHom (K := K) f (le_refl (f ⁻¹ᵁ U))
  let : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := g.toRingHom.toAlgebra
  have : IsScalarTower K Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := .of_algebraMap_eq fun c ↦ (g.commutes c).symm
  have hint : (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.IsIntegral := by
    have := IsIntegralHom.isIntegral_app f U hU
    rwa [Scheme.Hom.app_eq_appLE] at this
  have : Module.Finite Γ(X, U) Γ(Y, f ⁻¹ᵁ U) :=
    RingHom.finite_algebraMap.mp (hint.to_finite (f.finiteType_appLE hU hV le_rfl))
  refine ((Points.finite_proj_preimage_of_finite (A := Γ(X, U)) (B := Γ(Y, f ⁻¹ᵁ U))
    φ).image (chart hV)).subset fun p hp ↦ ?_
  have hpt : p.pt ∈ f ⁻¹ᵁ U := by
    have : (map f p).pt ∈ U := by rw [mem_singleton_iff.mp hp]; exact pt_chart hU φ
    exact this
  obtain ⟨ψ, rfl⟩ := exists_chart_eq hV p hpt
  exact ⟨ψ, chart_injective hU ((map_chart f hV hU le_rfl ψ).symm.trans hp), rfl⟩

end Finite

/-! ### Comparison statements over an algebraically closed field -/

section AlgClosed

variable [IsAlgClosed K] [LocallyOfFiniteType (X ↘ Spec (.of K))]

include K in
omit [IsAlgClosed K] in
lemma jacobsonSpace : JacobsonSpace X :=
  LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of K))

lemma range_pt : range (pt : SchemePoints K X → X) = closedPoints X := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    rw [← coe_equivClosedPoints]
    exact (equivClosedPoints p).2
  · intro hx
    exact ⟨equivClosedPoints.symm ⟨x, hx⟩, by
      rw [← coe_equivClosedPoints, Equiv.apply_symm_apply]⟩

/-- The `K`-points are dense in `X` (`X` is a Jacobson scheme). -/
lemma denseRange_pt : DenseRange (pt : SchemePoints K X → X) := by
  have := jacobsonSpace (K := K) (X := X)
  rw [DenseRange, range_pt, dense_iff_closure_eq]
  exact closure_closedPoints

/-- XII.2.1 (i): `X` is nonempty if and only if `X(K)` is. -/
theorem nonempty_iff : Nonempty (SchemePoints K X) ↔ Nonempty X := by
  refine ⟨fun ⟨p⟩ ↦ ⟨p.pt⟩, fun ⟨x⟩ ↦ ?_⟩
  obtain ⟨p, -⟩ := (denseRange_pt (K := K) (X := X)).exists_mem_open isOpen_univ
    ⟨x, mem_univ x⟩
  exact ⟨p⟩

/-- XII.3.1 (vii), one direction: if `f` is injective, so is `X(K) → Y(K)`. -/
theorem injective_map_of_injective {Y : Scheme.{u}} [Y.Over (Spec (.of K))] (f : X ⟶ Y)
    [f.IsOver (Spec (.of K))] (hf : Function.Injective f) :
    Function.Injective (map (K := K) f) := fun p q h ↦ by
  have : f p.pt = f q.pt := by rw [← pt_map, h, pt_map]
  exact equivClosedPoints.injective (Subtype.ext (hf this))

/-- A `K`-point of `X` lying in the image of `f : Y → X` lifts to a `K`-point of `Y`: the fibre
over a closed point is a nonempty Jacobson scheme, so it has a closed point, which is closed in
`Y`. -/
theorem exists_map_eq {Y : Scheme.{u}} [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] (f : Y ⟶ X) [f.IsOver (Spec (.of K))]
    (x : SchemePoints K X) (hx : x.pt ∈ range f) : ∃ q : SchemePoints K Y, map f q = x := by
  have : LocallyOfFiniteType (f ≫ X ↘ Spec (.of K)) := by rw [comp_over]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (X ↘ Spec (.of K))
  obtain ⟨y₀, hy₀⟩ := hx
  have hne : (closedPoints (f.fiber x.pt)).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := closure_closedPoints (X := f.fiber x.pt)
    rw [h, closure_empty] at this
    exact (this ▸ mem_univ ((f.fiberHomeo x.pt).symm ⟨y₀, hy₀⟩) : _ ∈ (∅ : Set _))
  obtain ⟨z, hz⟩ := hne
  have hx : IsClosed ({x.pt} : Set X) := by
    rw [← coe_equivClosedPoints]; exact (equivClosedPoints x).2
  have hclosed : IsClosed ({f.fiberι x.pt z} : Set Y) := by
    have := (hx.preimage f.continuous).isClosedMap_subtype_val _
      ((f.fiberHomeo x.pt).isClosedMap _ hz)
    rwa [image_image, image_singleton, Scheme.Hom.fiberHomeo_apply] at this
  refine ⟨equivClosedPoints.symm ⟨_, hclosed⟩, equivClosedPoints.injective (Subtype.ext ?_)⟩
  have h₁ : (equivClosedPoints.symm ⟨_, hclosed⟩ : SchemePoints K Y).pt = f.fiberι x.pt z := by
    rw [← coe_equivClosedPoints, Equiv.apply_symm_apply]
  have h₂ : f (f.fiberι x.pt z) = x.pt := by
    have := (f.fiberHomeo x.pt z).2
    rwa [Scheme.Hom.fiberHomeo_apply] at this
  rw [coe_equivClosedPoints, coe_equivClosedPoints, pt_map, h₁, h₂]

/-- XII.3.2 (i), direct implication: if `f : Y → X` is surjective, so is `Y(K) → X(K)`. -/
theorem surjective_map_of_surjective {Y : Scheme.{u}} [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] (f : Y ⟶ X) [f.IsOver (Spec (.of K))]
    (hf : Function.Surjective f) : Function.Surjective (map (K := K) f) :=
  fun x ↦ exists_map_eq f x (hf x.pt)

/-- XII.3.2 (i), converse: if `f : Y → X` is quasi-compact (for instance of finite type) and
`Y(K) → X(K)` is surjective, then `f` is surjective. The image of `f` is locally constructible
(Chevalley) and contains every closed point, hence is everything (`X` is Jacobson). -/
theorem surjective_of_surjective_map {Y : Scheme.{u}} [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] (f : Y ⟶ X) [f.IsOver (Spec (.of K))]
    [QuasiCompact f] (h : Function.Surjective (map (K := K) f)) : Function.Surjective f := by
  have : LocallyOfFiniteType (f ≫ X ↘ Spec (.of K)) := by rw [comp_over]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (X ↘ Spec (.of K))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have := jacobsonSpace (K := K) (X := X)
  have hlc : IsLocallyConstructible (range f) := by
    have := f.isLocallyConstructible_image (s := univ) IsLocallyConstructible.univ
    rwa [image_univ] at this
  rw [← Set.range_eq_univ]
  refine IsLocallyConstructible.eq_univ_of_closedPoints_subset hlc fun x hx ↦ ?_
  obtain ⟨p, hp⟩ : ∃ p : SchemePoints K X, p.pt = x :=
    ⟨equivClosedPoints.symm ⟨x, hx⟩, by rw [← coe_equivClosedPoints, Equiv.apply_symm_apply]⟩
  obtain ⟨q, rfl⟩ := h p
  exact ⟨q.pt, by rw [← hp, pt_map]⟩

/-- XII.3.2 (i): for `f : Y → X` quasi-compact, `f` is surjective if and only if `Y(K) → X(K)`
is. -/
theorem surjective_map_iff {Y : Scheme.{u}} [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] (f : Y ⟶ X) [f.IsOver (Spec (.of K))]
    [QuasiCompact f] : Function.Surjective (map (K := K) f) ↔ Function.Surjective f :=
  ⟨surjective_of_surjective_map f, surjective_map_of_surjective f⟩

variable [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]

/-- XII.2.4, one direction: if `X(K)` is connected, so is `X`. -/
theorem connectedSpace_of_connectedSpace [ConnectedSpace (SchemePoints K X)] :
    ConnectedSpace X := by
  have h := (isConnected_range (continuous_pt (K := K) (X := X))).closure
  rw [denseRange_pt.closure_range] at h
  exact connectedSpace_iff_univ.mpr h

/-- XII.2.6, surjectivity: `π₀(X(K)) → π₀(X)` is surjective. -/
theorem connectedComponentsMap_surjective :
    Function.Surjective (continuous_pt (K := K) (X := X)).connectedComponentsMap := by
  have := jacobsonSpace (K := K) (X := X)
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints ⟨x, mem_connectedComponent⟩
    isClosed_connectedComponent.isLocallyClosed
  rw [← range_pt (K := K)] at hyc
  obtain ⟨p, rfl⟩ := hyc
  refine ⟨p, ?_⟩
  rw [Continuous.connectedComponentsMap_mk]
  exact ConnectedComponents.coe_eq_coe'.mpr hy

end AlgClosed

/-! ### Statements over `ℂ` -/

section Complex

/-- XII.2.2 (statement only): for `X` locally of finite type over `ℂ` and `T` a locally
constructible subset of `X`, the closure of `T(ℂ)` in `X(ℂ)` is the set of `ℂ`-points of the
Zariski closure of `T`. The inclusion `⊆` is `continuous_pt.closure_preimage_subset`. -/
def ClosureComparisonStatement : Prop :=
  ∀ (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    (T : Set X), IsLocallyConstructible T →
      closure (pt ⁻¹' T : Set (SchemePoints ℂ X)) = pt ⁻¹' closure T

/-- XII.2.4: if `X`, locally of finite type over `ℂ`, is connected, so is `X(ℂ)` (proved as
`SchemePoints.connectedComparison` in `Connected.lean`). The converse is
`connectedSpace_of_connectedSpace`. -/
def ConnectedComparisonStatement : Prop :=
  ∀ (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))],
    ConnectedSpace X → ConnectedSpace (SchemePoints ℂ X)

/-- XII.2.6: the map `π₀(X(ℂ)) → π₀(X)` is bijective (proved as
`SchemePoints.connectedComponentsComparison` in `Connected.lean`). Surjectivity is
`connectedComponentsMap_surjective`. -/
def ConnectedComponentsComparisonStatement : Prop :=
  ∀ (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))],
    Function.Bijective (continuous_pt (K := ℂ) (X := X)).connectedComponentsMap

/-- XII.3.2 (ii), from XII.2.2: for `f : Y → X` quasi-compact between schemes locally of finite
type over `ℂ`, `f` is dominant if and only if `Y(ℂ) → X(ℂ)` has dense image. -/
theorem denseRange_map_iff (H : ClosureComparisonStatement) {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (f : Y ⟶ X) [f.IsOver (Spec (.of ℂ))]
    [QuasiCompact f] : DenseRange (map (K := ℂ) f) ↔ DenseRange f := by
  have : LocallyOfFiniteType (f ≫ X ↘ Spec (.of ℂ)) := by rw [comp_over]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (X ↘ Spec (.of ℂ))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  have := jacobsonSpace (K := ℂ) (X := X)
  have hlc : IsLocallyConstructible (range f) := by
    have := f.isLocallyConstructible_image (s := univ) IsLocallyConstructible.univ
    rwa [image_univ] at this
  have hpre : pt ⁻¹' range f = range (map (K := ℂ) f) := by
    ext x
    refine ⟨fun hx ↦ exists_map_eq f x hx, ?_⟩
    rintro ⟨q, rfl⟩
    exact ⟨q.pt, (pt_map f q).symm⟩
  have hc := H X (range f) hlc
  rw [hpre] at hc
  rw [DenseRange, DenseRange, dense_iff_closure_eq, dense_iff_closure_eq, hc]
  constructor
  · intro h
    refine eq_univ_of_univ_subset ?_
    rw [← closure_closedPoints, isClosed_closure.closure_subset_iff]
    intro x hx
    obtain ⟨p, hp⟩ : ∃ p : SchemePoints ℂ X, p.pt = x :=
      ⟨equivClosedPoints.symm ⟨x, hx⟩, by rw [← coe_equivClosedPoints, Equiv.apply_symm_apply]⟩
    have : p ∈ pt ⁻¹' closure (range f) := h ▸ mem_univ p
    rwa [mem_preimage, hp] at this
  · intro h
    rw [h, preimage_univ]

/-- Closed subsets of a locally noetherian scheme are locally constructible. -/
lemma isLocallyConstructible_of_isClosed {X : Scheme.{u}} [IsLocallyNoetherian X] {Z : Set X}
    (hZ : IsClosed Z) : IsLocallyConstructible Z := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : TopologicalSpace.NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  refine ⟨U, U.2.mem_nhds hxU, U.2, ?_⟩
  rw [← isConstructible_compl]
  exact IsRetrocompact.isConstructible (hZ.preimage continuous_subtype_val).isOpen_compl
    fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _

section ClosureComparison

variable (H : ClosureComparisonStatement) {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
  [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
include H

omit H in
lemma exists_pt_eq {x : X} (hx : x ∈ closedPoints X) : ∃ p : SchemePoints ℂ X, p.pt = x :=
  ⟨equivClosedPoints.symm ⟨x, hx⟩, by rw [← coe_equivClosedPoints, Equiv.apply_symm_apply]⟩

/-- XII.2.3, closed case, from XII.2.2: a locally constructible subset `T` of `X` is closed if and
only if `T(ℂ)` is closed in `X(ℂ)`. -/
theorem isClosed_iff_of_closureComparison {T : Set X} (hT : IsLocallyConstructible T) :
    IsClosed T ↔ IsClosed (pt ⁻¹' T : Set (SchemePoints ℂ X)) := by
  refine ⟨fun h ↦ h.preimage continuous_pt, fun h ↦ ?_⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  have := jacobsonSpace (K := ℂ) (X := X)
  have hc := H X T hT
  rw [h.closure_eq] at hc
  have hD : IsLocallyConstructible (closure T ∩ Tᶜ) :=
    (isLocallyConstructible_of_isClosed isClosed_closure).inter
      (IsLocallyConstructible.compl hT)
  have hempty : closure T ∩ Tᶜ = ∅ := by
    by_contra hne
    obtain ⟨x, ⟨hxc, hxT⟩, hx⟩ :=
      IsLocallyConstructible.nonempty_inter_closedPoints hD (nonempty_iff_ne_empty.mpr hne)
    obtain ⟨p, rfl⟩ := exists_pt_eq hx
    have : p ∈ pt ⁻¹' closure T := hxc
    rw [← hc] at this
    exact hxT this
  refine isClosed_of_closure_subset fun x hx ↦ ?_
  by_contra hxT
  exact (eq_empty_iff_forall_notMem.mp hempty) x ⟨hx, hxT⟩

/-- XII.2.3, open case, from XII.2.2. -/
theorem isOpen_iff_of_closureComparison {T : Set X} (hT : IsLocallyConstructible T) :
    IsOpen T ↔ IsOpen (pt ⁻¹' T : Set (SchemePoints ℂ X)) := by
  rw [← isClosed_compl_iff, isClosed_iff_of_closureComparison H (IsLocallyConstructible.compl hT),
    preimage_compl, isClosed_compl_iff]

/-- XII.2.3, dense case, from XII.2.2. -/
theorem dense_iff_of_closureComparison {T : Set X} (hT : IsLocallyConstructible T) :
    Dense T ↔ Dense (pt ⁻¹' T : Set (SchemePoints ℂ X)) := by
  have := jacobsonSpace (K := ℂ) (X := X)
  rw [dense_iff_closure_eq, dense_iff_closure_eq, H X T hT]
  constructor
  · intro h; rw [h, preimage_univ]
  · intro h
    refine eq_univ_of_univ_subset ?_
    rw [← closure_closedPoints, isClosed_closure.closure_subset_iff]
    intro x hx
    obtain ⟨p, rfl⟩ := exists_pt_eq hx
    exact (h ▸ mem_univ p : p ∈ pt ⁻¹' closure T)

end ClosureComparison

/-- The sections over an affine open of a `K`-scheme locally of finite type form a `K`-algebra of
finite type. -/
lemma finiteType_sections {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] {U : X.Opens} (hU : IsAffineOpen U) :
    Algebra.FiniteType K Γ(X, U) := by
  rw [← RingHom.finiteType_algebraMap]
  refine RingHom.FiniteType.comp ((X ↘ Spec (.of K)).finiteType_appLE (isAffineOpen_top _) hU
    (le_top.trans_eq (Scheme.Hom.preimage_top _).symm)) (RingHom.FiniteType.of_surjective _ ?_)
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2

/-- XII.2.1 (i'), with (viii) in dimension `0`: for `X` locally of finite type over `ℂ`, `X(ℂ)`
is discrete if and only if `X` has dimension `≤ 0` (every affine open does). -/
theorem discreteTopology_iff (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] :
    DiscreteTopology (SchemePoints ℂ X) ↔
      ∀ U : X.Opens, IsAffineOpen U → Ring.KrullDimLE 0 Γ(X, U) := by
  constructor
  · intro _ U hU
    have := finiteType_sections (K := ℂ) hU
    have : DiscreteTopology (Points ℂ Γ(X, U)) :=
      (isOpenEmbedding_chart hU).isEmbedding.discreteTopology
    exact Points.discreteTopology_iff_krullDimLE_complex.mp this
  · intro h
    refine discreteTopology_iff_isOpen_singleton.mpr fun p ↦ ?_
    obtain ⟨U, hU, hpU⟩ := exists_isAffineOpen_mem p
    obtain ⟨φ, rfl⟩ := exists_chart_eq hU p hpU
    have := finiteType_sections (K := ℂ) hU
    have := h U hU
    have : DiscreteTopology (Points ℂ Γ(X, U)) :=
      Points.discreteTopology_iff_krullDimLE_complex.mpr inferInstance
    rw [← image_singleton]
    exact (isOpenEmbedding_chart hU).isOpenMap _ (isOpen_discrete _)

theorem connectedSpace_iff (H : ConnectedComparisonStatement) (X : Scheme.{0})
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] :
    ConnectedSpace (SchemePoints ℂ X) ↔ ConnectedSpace X :=
  ⟨fun _ ↦ connectedSpace_of_connectedSpace (K := ℂ), H X⟩

end Complex

end SchemePoints

/-! ### Points of `Spec R` -/

namespace SchemePoints

section SpecPoint

variable {K : Type u} [Field K] (R : Type u) [CommRing R] [Algebra K R]

/-- `Spec R` as a `K`-scheme, for a `K`-algebra `R`. -/
abbrev specOver : (Spec (.of R)).Over (Spec (.of K)) :=
  .ofHom (Spec.map (CommRingCat.ofHom (algebraMap K R)))

attribute [local instance] specOver sectionsAlgebra

/-- The `K`-point of `Spec R` attached to a `K`-point of `R`. -/
def specPoint (χ : Points K R) : SchemePoints K (Spec (.of R)) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K R)) = _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    exact χ.apply_algebraMap c⟩

/-- `Γ(Spec R, ⊤) ≅ R`, as a `K`-algebra map. -/
def ΓSpecAlgHom : Γ(Spec (.of R), ⊤) →ₐ[K] R :=
  { (Scheme.ΓSpecIso (.of R)).hom.hom with
    commutes' := fun c ↦ by
      change ((structureMap K ⊤) ≫ (Scheme.ΓSpecIso (.of R)).hom) c = _
      have : structureMap K (⊤ : (Spec (.of R)).Opens) = (Scheme.ΓSpecIso (.of K)).inv ≫
          (Spec.map (CommRingCat.ofHom (algebraMap K R))).appTop := rfl
      rw [this, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
      rfl }

/-- `Γ(Spec R, ⊤) ≅ R`, as a `K`-algebra isomorphism. -/
def ΓSpecAlgEquiv : Γ(Spec (.of R), ⊤) ≃ₐ[K] R :=
  AlgEquiv.ofBijective (ΓSpecAlgHom R)
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom)

lemma specPoint_eq_chart (χ : Points K R) :
    specPoint R χ = chart (isAffineOpen_top _) (Points.map (ΓSpecAlgHom R) χ) := by
  apply Subtype.ext
  change Spec.map _ = Spec.map _ ≫ (isAffineOpen_top _).fromSpec
  have : CommRingCat.ofHom (Points.map (ΓSpecAlgHom (K := K) R) χ).toRingHom =
      (Scheme.ΓSpecIso (.of R)).hom ≫ CommRingCat.ofHom χ.toRingHom := rfl
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, this,
    Iso.inv_hom_id_assoc]

lemma continuous_specPoint [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K] :
    Continuous (specPoint (K := K) R) := by
  rw [show specPoint (K := K) R = chart (isAffineOpen_top _) ∘ Points.map (ΓSpecAlgHom R) from
    funext (specPoint_eq_chart R)]
  exact (continuous_chart _).comp (Points.continuous_map _)

end SpecPoint

end SchemePoints

/-! ### Étale morphisms give local homeomorphisms -/

namespace SchemePoints

section Etale

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
  (f : Y ⟶ X) [f.IsOver (Spec (.of K))]

attribute [local instance] sectionsAlgebra

/-- XII.3.1 (iii), XII.3.3 a): an étale `K`-morphism `f : Y → X` induces a local homeomorphism
`Y(K) → X(K)` (`K = ℂ`, or any complete nontrivially normed field). -/
theorem isLocalHomeomorph_map_of_etale [Etale f] : IsLocalHomeomorph (map (K := K) f) := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  intro y _
  obtain ⟨V, hV, hyV⟩ := exists_isAffineOpen_mem (map f y)
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show y.pt ∈ f ⁻¹ᵁ V from hyV) (f ⁻¹ᵁ V).2
  have hU : IsAffineOpen U := hU
  have e : U ≤ f ⁻¹ᵁ V := hUV
  let g := appLEAlgHom (K := K) f e
  let : Algebra Γ(X, V) Γ(Y, U) := g.toRingHom.toAlgebra
  have : IsScalarTower K Γ(X, V) Γ(Y, U) := .of_algebraMap_eq fun c ↦ (g.commutes c).symm
  have : Algebra.Etale Γ(X, V) Γ(Y, U) :=
    HasRingHomProperty.appLE @Etale f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ e
  have hP : IsLocalHomeomorph (Points.map (K := K) g) :=
    Points.isLocalHomeomorph_proj_of_etale (A := Γ(X, V)) (B := Γ(Y, U))
  have hcomp : map (K := K) f ∘ chart hU = chart hV ∘ Points.map g :=
    funext (map_chart (K := K) f hU hV e)
  have h₁ : IsLocalHomeomorphOn (map (K := K) f ∘ chart hU) univ := by
    rw [hcomp]
    exact ((isOpenEmbedding_chart hV).isLocalHomeomorph.comp hP).isLocalHomeomorphOn
  have h₂ := h₁.of_comp_right
    (isOpenEmbedding_chart (K := K) hU).isLocalHomeomorph.isLocalHomeomorphOn
  obtain ⟨φ, rfl⟩ := exists_chart_eq hU y hyU
  exact h₂ _ ⟨φ, mem_univ _, rfl⟩

end Etale

/-! ### Finite étale morphisms give finite coverings -/

variable {K : Type u} [NontriviallyNormedField K] [ProperSpace K]
  {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
  (f : Y ⟶ X) [f.IsOver (Spec (.of K))]

attribute [local instance] sectionsAlgebra

lemma isCoveringMap_points_appLE [IsFinite f] [Etale f] {U : X.Opens} (hU : IsAffineOpen U) :
    IsCoveringMap (Points.map (appLEAlgHom (K := K) f (le_refl (f ⁻¹ᵁ U)))) ∧
      ∀ φ, (Points.map (appLEAlgHom (K := K) f (le_refl (f ⁻¹ᵁ U))) ⁻¹' {φ}).Finite := by
  let g := appLEAlgHom (K := K) f (le_refl (f ⁻¹ᵁ U))
  let : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := g.toRingHom.toAlgebra
  have : IsScalarTower K Γ(X, U) Γ(Y, f ⁻¹ᵁ U) :=
    .of_algebraMap_eq fun c ↦ (g.commutes c).symm
  have : Algebra.IsIntegral Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := ⟨fun x ↦ by
    have := IsIntegralHom.isIntegral_app f U hU x
    rwa [Scheme.Hom.app_eq_appLE] at this⟩
  have : Algebra.Etale Γ(X, U) Γ(Y, f ⁻¹ᵁ U) :=
    HasRingHomProperty.appLE @Etale f ‹_› ⟨U, hU⟩ ⟨_, hU.preimage f⟩ le_rfl
  exact ⟨Points.isCoveringMap_proj (A := Γ(X, U)) (B := Γ(Y, f ⁻¹ᵁ U)),
    Points.finite_proj_preimage (A := Γ(X, U)) (B := Γ(Y, f ⁻¹ᵁ U))⟩

/-- XII.5.1, the functor `Ψ` on points: a finite étale `K`-morphism `f : Y → X` induces a
covering map `Y(K) → X(K)` (`K = ℂ`, or any proper nontrivially normed field). Over an affine
open `U` of `X`, `f⁻¹(U)` is affine and `Γ(Y, f⁻¹ U)` is finite étale over `Γ(X, U)`; this
reduces to `Points.isCoveringMap_proj`. -/
theorem isCoveringMap_map [IsFinite f] [Etale f] : IsCoveringMap (map (K := K) f) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  intro x _
  obtain ⟨U, hU, hxU⟩ := exists_isAffineOpen_mem x
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hfs : map f ⁻¹' range (chart (K := K) hU) = range (chart (K := K) hV) := by
    ext p
    simp only [mem_preimage, range_chart, mem_ofPred_eq, pt_map]
    rfl
  refine IsCoveringMapOn.of_isCoveringMap_restrictPreimage _
    (isOpenEmbedding_chart hU).isOpen_range (hfs ▸ (isOpenEmbedding_chart hV).isOpen_range) ?_ x
    (by rw [range_chart]; exact hxU)
  let eX := (isOpenEmbedding_chart (K := K) hU).isEmbedding.toHomeomorph
  let eY := (isOpenEmbedding_chart (K := K) hV).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hfs.symm)
  have hcomm : (range (chart (K := K) hU)).restrictPreimage (map f) ∘ eY =
      eX ∘ Points.map (appLEAlgHom (K := K) f (le_refl (f ⁻¹ᵁ U))) := by
    funext φ
    apply Subtype.ext
    exact map_chart f hV hU le_rfl φ
  rw [← IsCoveringMap.comp_homeomorph_iff (g := eY), hcomm, IsCoveringMap.homeomorph_comp_iff]
  exact (isCoveringMap_points_appLE f hU).1

/-- XII.3.2 (v), (vi), direct implication for finite morphisms: a finite `K`-morphism
`f : Y → X` induces a proper map `Y(K) → X(K)`. Over an affine open this is
`Points.isProperMap_proj_of_isIntegral`, and properness is local on the target. -/
theorem isProperMap_map [IsFinite f] : IsProperMap (map (K := K) f) := by
  refine isProperMap_of_isProperMap_restrictPreimage (continuous_map f) fun x ↦ ?_
  obtain ⟨U, hU, hxU⟩ := exists_isAffineOpen_mem x
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hfs : map f ⁻¹' range (chart (K := K) hU) = range (chart (K := K) hV) := by
    ext p
    simp only [mem_preimage, range_chart, mem_ofPred_eq, pt_map]
    rfl
  refine ⟨_, (isOpenEmbedding_chart hU).isOpen_range, by rw [range_chart]; exact hxU, ?_⟩
  let eX := (isOpenEmbedding_chart (K := K) hU).isEmbedding.toHomeomorph
  let eY := (isOpenEmbedding_chart (K := K) hV).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hfs.symm)
  let g := appLEAlgHom (K := K) f (le_refl (f ⁻¹ᵁ U))
  have hcomm : (range (chart (K := K) hU)).restrictPreimage (map f) =
      eX ∘ Points.map g ∘ eY.symm := by
    funext q
    obtain ⟨φ, rfl⟩ := eY.surjective q
    apply Subtype.ext
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
    exact map_chart f hV hU le_rfl φ
  let : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := g.toRingHom.toAlgebra
  have : IsScalarTower K Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := .of_algebraMap_eq fun c ↦ (g.commutes c).symm
  have : Algebra.IsIntegral Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := ⟨fun x ↦ by
    have := IsIntegralHom.isIntegral_app f U hU x
    rwa [Scheme.Hom.app_eq_appLE] at this⟩
  rw [hcomm]
  exact eX.isProperMap.comp ((Points.isProperMap_proj_of_isIntegral (A := Γ(X, U))
    (B := Γ(Y, f ⁻¹ᵁ U))).comp eY.symm.isProperMap)

/-- The fibres of `Y(K) → X(K)` are finite for `f : Y → X` finite étale. -/
theorem finite_map_preimage [IsFinite f] [Etale f] (x : SchemePoints K X) :
    (map f ⁻¹' {x}).Finite := by
  obtain ⟨U, hU, hxU⟩ := exists_isAffineOpen_mem x
  obtain ⟨φ, rfl⟩ := exists_chart_eq hU x hxU
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  refine (((isCoveringMap_points_appLE f hU).2 φ).image (chart hV)).subset fun p hp ↦ ?_
  have hpt : p.pt ∈ f ⁻¹ᵁ U := by
    have : (map f p).pt ∈ U := by rw [mem_singleton_iff.mp hp]; exact pt_chart hU φ
    exact this
  obtain ⟨ψ, rfl⟩ := exists_chart_eq hV p hpt
  exact ⟨ψ, chart_injective hU ((map_chart f hV hU le_rfl ψ).symm.trans hp), rfl⟩

end SchemePoints

end SGA.SGA1.ExposeXII
