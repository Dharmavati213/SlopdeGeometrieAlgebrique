/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.GroupTheory.CoprodI
import SGA.Foundations.Topology.VanKampenPushout

/-!
# Seifert–van Kampen with path-connected triple intersections

Hatcher's form of the Seifert–van Kampen theorem. Let `X` be covered by open sets `W i`, each
containing the base point `x`, such that every triple intersection `W i ∩ W j ∩ W k` is
path-connected (taking repeated indices, so are the `W i` and the `W i ∩ W j`). Then
homomorphisms `f i : π₁(W i, x) →* G` that agree on every `π₁(W i ∩ W j, x)` extend uniquely to a
homomorphism `π₁(X, x) →* G`
(`FundamentalGroup.existsUnique_hom_of_isOpen_cover_of_isPathConnected_inter`). In other words,
`π₁(X, x)` is the colimit of the groups `π₁(W i, x)` and `π₁(W i ∩ W j, x)`.

This generalizes `FundamentalGroup.existsUnique_hom_of_isOpen_cover`
(`Foundations/Topology/VanKampenPushout.lean`), which asks all pairwise intersections to be one
path-connected set.

## Proof

The groupoid form `FundamentalGroupoid.existsUnique_functor_of_isOpen_cover` glues functors
`π(W i) ⥤ G` that agree on paths in the overlaps. Each `f i` extends to such a functor once paths
`T i y` from `x` to the points `y ∈ W i` are chosen in `W i`. These extensions do not agree on the
overlaps as they stand: we choose `T i y` inside `W i ∩ W (c y)` for a fixed index `c y` with
`y ∈ W (c y)`, and conjugate the extension of `f i` by the correction
`f (c y) (T i y · (T (c y) y)⁻¹)`. Comparing two corrected extensions at a point `y ∈ W i ∩ W j`
goes through a path from `x` to `y` inside `W i ∩ W j ∩ W (c y)`; this is where triple
intersections are used.

## References

* [A. Hatcher, *Algebraic Topology*, Theorem 1.20][hatcher02]
-/

open Set Topology CategoryTheory FundamentalGroupoid

universe u v w

namespace FundamentalGroup

variable {X : Type u} [TopologicalSpace X]

/-- The class of a path, as an arrow of the fundamental groupoid. -/
local notation "⌈" γ "⌉" => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ)

namespace VanKampenTriple

/-! ### Paths in a subset as arrows of its fundamental groupoid -/

/-- A path in `X` with values in `s`, as an arrow of the fundamental groupoid of `s`. -/
noncomputable abbrev arr {s : Set X} {y z : X} (γ : Path y z) (h : range γ ⊆ s) :
    FundamentalGroupoid.mk (⟨y, h ⟨0, γ.source⟩⟩ : s) ⟶
      FundamentalGroupoid.mk (⟨z, h ⟨1, γ.target⟩⟩ : s) :=
  ⌈γ.codRestrict h⌉

lemma range_subset_of_trans_left {s : Set X} {y z w : X} {γ : Path y z} {δ : Path z w}
    (h : range (γ.trans δ) ⊆ s) : range γ ⊆ s := by
  rw [Path.trans_range] at h
  exact subset_union_left.trans h

lemma range_subset_of_trans_right {s : Set X} {y z w : X} {γ : Path y z} {δ : Path z w}
    (h : range (γ.trans δ) ⊆ s) : range δ ⊆ s := by
  rw [Path.trans_range] at h
  exact subset_union_right.trans h

lemma range_subset_of_symm {s : Set X} {y z : X} {γ : Path y z} (h : range γ.symm ⊆ s) :
    range γ ⊆ s := by
  rwa [Path.symm_range] at h

lemma range_trans_subset {s : Set X} {y z w : X} {γ : Path y z} {δ : Path z w}
    (hγ : range γ ⊆ s) (hδ : range δ ⊆ s) : range (γ.trans δ) ⊆ s := by
  rw [Path.trans_range]
  exact union_subset hγ hδ

lemma range_symm_subset {s : Set X} {y z : X} {γ : Path y z} (h : range γ ⊆ s) :
    range γ.symm ⊆ s := by
  rwa [Path.symm_range]

lemma arr_trans {s : Set X} {y z w : X} (γ : Path y z) (δ : Path z w)
    (h : range (γ.trans δ) ⊆ s) :
    arr (γ.trans δ) h =
      arr γ (range_subset_of_trans_left h) ≫ arr δ (range_subset_of_trans_right h) := by
  rw [arr, Path.codRestrict_trans _ _ h (range_subset_of_trans_left h)
    (range_subset_of_trans_right h), fromPath_mk_trans]

lemma arr_symm {s : Set X} {y z : X} (γ : Path y z) (h : range γ.symm ⊆ s) :
    arr γ.symm h = inv (arr γ (range_subset_of_symm h)) := by
  rw [arr, Path.codRestrict_symm _ h (range_subset_of_symm h), fromPath_mk_symm]

/-! ### Values of the `f i` on loops in `X` -/

variable {ι : Type w} {W : ι → Set X} {x : X} {G : Type v} [Group G] {hx : ∀ i, x ∈ W i}
  (f : ∀ i, FundamentalGroup (W i) ⟨x, hx i⟩ →* G)

open Classical in
/-- `f i` evaluated on a loop at `x` in `X` with values in `W i` (and `1` on other loops). -/
noncomputable def loopValue (i : ι) (γ : Path x x) : G :=
  if h : range γ ⊆ W i then f i (arr γ h) else 1

lemma loopValue_eq {i : ι} {γ : Path x x} (h : range γ ⊆ W i) :
    loopValue f i γ = f i (arr γ h) :=
  dite_eq_left h

/-- `a · d⁻¹ = (a · b⁻¹)(b · d⁻¹)` (as loops in `W i`; the group law of `π₁` is reversed). -/
lemma loopValue_trans_symm {i : ι} {y : X} (a b d : Path x y) (ha : range a ⊆ W i)
    (hb : range b ⊆ W i) (hd : range d ⊆ W i) :
    loopValue f i (a.trans d.symm) =
      loopValue f i (b.trans d.symm) * loopValue f i (a.trans b.symm) := by
  rw [loopValue_eq f (range_trans_subset ha (range_symm_subset hd)),
    loopValue_eq f (range_trans_subset hb (range_symm_subset hd)),
    loopValue_eq f (range_trans_subset ha (range_symm_subset hb)), ← map_mul, End.mul_def]
  refine congrArg (f i) ?_
  simp only [arr_trans, arr_symm, Category.assoc, IsIso.inv_hom_id_assoc]

lemma loopValue_trans_symm_self {i : ι} {y : X} (a : Path x y) (ha : range a ⊆ W i) :
    loopValue f i (a.trans a.symm) = 1 := by
  rw [loopValue_eq f (range_trans_subset ha (range_symm_subset ha))]
  simp only [arr_trans, arr_symm, IsIso.hom_inv_id]
  exact (f i).map_one

lemma loopValue_trans_symm_inv {i : ι} {y : X} (a b : Path x y) (ha : range a ⊆ W i)
    (hb : range b ⊆ W i) :
    loopValue f i (a.trans b.symm) = (loopValue f i (b.trans a.symm))⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← loopValue_trans_symm f b a b hb ha hb,
    loopValue_trans_symm_self f b hb]

/-- `a · p · b⁻¹ = (a · e⁻¹)(e · p · e'⁻¹)(e' · b⁻¹)`. -/
lemma loopValue_trans_trans_symm {i : ι} {y z : X} (a e : Path x y) (p : Path y z)
    (b e' : Path x z) (ha : range a ⊆ W i) (he : range e ⊆ W i) (hp : range p ⊆ W i)
    (hb : range b ⊆ W i) (he' : range e' ⊆ W i) :
    loopValue f i ((a.trans p).trans b.symm) =
      loopValue f i (e'.trans b.symm) * loopValue f i ((e.trans p).trans e'.symm) *
        loopValue f i (a.trans e.symm) := by
  rw [loopValue_eq f (range_trans_subset (range_trans_subset ha hp) (range_symm_subset hb)),
    loopValue_eq f (range_trans_subset he' (range_symm_subset hb)),
    loopValue_eq f (range_trans_subset (range_trans_subset he hp) (range_symm_subset he')),
    loopValue_eq f (range_trans_subset ha (range_symm_subset he)), ← map_mul, ← map_mul,
    End.mul_def, End.mul_def]
  refine congrArg (f i) ?_
  simp only [arr_trans, arr_symm, Category.assoc, IsIso.inv_hom_id_assoc]

variable (hf : ∀ i j, (f i).comp
    (map (ContinuousMap.inclusion (inter_subset_left : W i ∩ W j ⊆ W i))
      ⟨x, mem_inter (hx i) (hx j)⟩) =
  (f j).comp (map (ContinuousMap.inclusion (inter_subset_right : W i ∩ W j ⊆ W j))
    ⟨x, mem_inter (hx i) (hx j)⟩))
include hf

/-- On loops in `W i ∩ W j`, `f i` and `f j` agree. -/
lemma loopValue_eq_of_subset_inter {i j : ι} {γ : Path x x} (h : range γ ⊆ W i ∩ W j) :
    loopValue f i γ = loopValue f j γ := by
  rw [loopValue_eq f (h.trans inter_subset_left), loopValue_eq f (h.trans inter_subset_right)]
  exact DFunLike.congr_fun (hf i j) (arr γ h)

omit hf

/-! ### The corrected extensions of the `f i` -/

variable (c : X → ι) (T : ι → ∀ y, Path x y)

/-- The correction `f (c y) (T i y · (T (c y) y)⁻¹)`. -/
noncomputable def corr (i : ι) (y : X) : G :=
  loopValue f (c y) ((T i y).trans (T (c y) y).symm)

variable {c T} (hT : ∀ i y, y ∈ W i → range (T i y) ⊆ W i ∩ W (c y))

/-- The extension of `f i` to a functor `π(W i) ⥤ G`: a path `p` from `y` to `z` goes to
`corr i z * f i (T i y · p · (T i z)⁻¹) * (corr i y)⁻¹`. -/
noncomputable def localFunctor (i : ι) : FundamentalGroupoid (W i) ⥤ SingleObj G where
  obj _ := SingleObj.star G
  map {a b} p := corr f c T i b.as * f i (arr (T i a.as) (fun _ h ↦ (hT i a.as a.as.2 h).1) ≫ p ≫
    arr (T i b.as).symm (range_symm_subset fun _ h ↦ (hT i b.as b.as.2 h).1)) *
      (corr f c T i a.as)⁻¹
  map_id a := by
    simp only [arr_symm, Category.id_comp, IsIso.hom_inv_id]
    have h1 : f i (𝟙 (FundamentalGroupoid.mk (⟨x, hx i⟩ : W i))) = 1 := (f i).map_one
    rw [h1, mul_one, mul_inv_cancel]
    rfl
  map_comp {a b d} p q := by
    rw [SingleObj.comp_as_mul]
    have h : f i (arr (T i a.as) (fun _ h ↦ (hT i a.as a.as.2 h).1) ≫ (p ≫ q) ≫
        arr (T i d.as).symm (range_symm_subset fun _ h ↦ (hT i d.as d.as.2 h).1)) =
        f i (arr (T i b.as) (fun _ h ↦ (hT i b.as b.as.2 h).1) ≫ q ≫
          arr (T i d.as).symm (range_symm_subset fun _ h ↦ (hT i d.as d.as.2 h).1)) *
        f i (arr (T i a.as) (fun _ h ↦ (hT i a.as a.as.2 h).1) ≫ p ≫
          arr (T i b.as).symm (range_symm_subset fun _ h ↦ (hT i b.as b.as.2 h).1)) := by
      rw [← map_mul, End.mul_def]
      refine congrArg (f i) ?_
      simp only [arr_symm, Category.assoc, IsIso.inv_hom_id_assoc]
    rw [h]
    group

/-- The corrected extension on a path `p` in `W i`, in terms of loops in `X`. -/
lemma localFunctor_map_arr (i : ι) {y z : X} (p : Path y z) (hp : range p ⊆ W i) :
    ((localFunctor f hT i).map (arr p hp) : G) =
      corr f c T i z * loopValue f i (((T i y).trans p).trans (T i z).symm) *
        (corr f c T i y)⁻¹ := by
  have hy : y ∈ W i := hp ⟨0, p.source⟩
  have hz : z ∈ W i := hp ⟨1, p.target⟩
  rw [loopValue_eq f (range_trans_subset (range_trans_subset (fun _ h ↦ (hT i y hy h).1) hp)
    (range_symm_subset fun _ h ↦ (hT i z hz h).1)), arr_trans, arr_trans, Category.assoc]
  rfl

include hf hT in
/-- The correction absorbs the change of base paths at `y`: for paths `ε` in `W k` and `θ` in
`W k ∩ W (c y)` from `x` to `y`, `corr k y · f k (ε · (T k y)⁻¹)` only depends on `ε` and `θ`
through `f (c y) (θ · (T (c y) y)⁻¹)` and `f k (ε · θ⁻¹)`. -/
lemma corr_mul_loopValue {k : ι} {y : X} (hy : y ∈ W k) (ε θ : Path x y) (hε : range ε ⊆ W k)
    (hθ : range θ ⊆ W k ∩ W (c y)) :
    corr f c T k y * loopValue f k (ε.trans (T k y).symm) =
      loopValue f (c y) (θ.trans (T (c y) y).symm) * loopValue f k (ε.trans θ.symm) := by
  have hTk := hT k y hy
  have hTc : range (T (c y) y) ⊆ W (c y) := fun _ h ↦ (hT (c y) y (hθ ⟨1, θ.target⟩).2 h).1
  rw [loopValue_trans_symm f ε θ (T k y) hε (hθ.trans inter_subset_left)
    (hTk.trans inter_subset_left),
    loopValue_eq_of_subset_inter f hf (i := k) (j := c y)
      (range_trans_subset hθ (range_symm_subset hTk)), corr, ← mul_assoc,
    ← loopValue_trans_symm f θ (T k y) (T (c y) y) (hθ.trans inter_subset_right)
      (hTk.trans inter_subset_right) hTc]

include hf in
/-- The corrected extension of `f k` on a path `p` in `W k`, in terms of auxiliary paths `ε` (in
`W k`) and `θ` (in `W k ∩ W (c ·)`) from `x` to the endpoints of `p`. -/
lemma localFunctor_map_arr_eq {k : ι} {y z : X} (p : Path y z) (hp : range p ⊆ W k)
    (εy θy : Path x y) (εz θz : Path x z) (hεy : range εy ⊆ W k) (hεz : range εz ⊆ W k)
    (hθy : range θy ⊆ W k ∩ W (c y)) (hθz : range θz ⊆ W k ∩ W (c z)) :
    ((localFunctor f hT k).map (arr p hp) : G) =
      (loopValue f (c z) (θz.trans (T (c z) z).symm) * loopValue f k (εz.trans θz.symm)) *
        loopValue f k ((εy.trans p).trans εz.symm) *
          (loopValue f (c y) (θy.trans (T (c y) y).symm) * loopValue f k (εy.trans θy.symm))⁻¹ := by
  have hy : y ∈ W k := hp ⟨0, p.source⟩
  have hz : z ∈ W k := hp ⟨1, p.target⟩
  rw [localFunctor_map_arr, loopValue_trans_trans_symm f (T k y) εy p (T k z) εz
    ((hT k y hy).trans inter_subset_left) hεy hp ((hT k z hz).trans inter_subset_left) hεz,
    loopValue_trans_symm_inv f (T k y) εy ((hT k y hy).trans inter_subset_left) hεy,
    ← corr_mul_loopValue f hf hT hy εy θy hεy hθy, ← corr_mul_loopValue f hf hT hz εz θz hεz hθz]
  group

end VanKampenTriple

open VanKampenTriple in
/-- **Seifert–van Kampen** (Hatcher, Theorem 1.20; universal property). Let `X` be covered by
open sets `W i`, all containing `x`, such that every triple intersection `W i ∩ W j ∩ W k` is
path-connected (with repeated indices: so are the `W i` and the `W i ∩ W j`). Then homomorphisms
`f i : π₁(W i, x) →* G` that agree on `π₁(W i ∩ W j, x)` for all `i`, `j` extend uniquely to a
homomorphism `π₁(X, x) →* G`. -/
theorem existsUnique_hom_of_isOpen_cover_of_isPathConnected_inter {ι : Type w} {W : ι → Set X}
    {x : X} {G : Type v} [Group G] (hWo : ∀ i, IsOpen (W i)) (hcov : ∀ y, ∃ i, y ∈ W i)
    (hx : ∀ i, x ∈ W i) (hW : ∀ i j k, IsPathConnected (W i ∩ W j ∩ W k))
    (f : ∀ i, FundamentalGroup (W i) ⟨x, hx i⟩ →* G)
    (hf : ∀ i j, (f i).comp
        (map (ContinuousMap.inclusion (inter_subset_left : W i ∩ W j ⊆ W i))
          ⟨x, mem_inter (hx i) (hx j)⟩) =
      (f j).comp (map (ContinuousMap.inclusion (inter_subset_right : W i ∩ W j ⊆ W j))
        ⟨x, mem_inter (hx i) (hx j)⟩)) :
    ∃! g : FundamentalGroup X x →* G, ∀ i, g.comp (mapSubtypeVal (hx i)) = f i := by
  classical
  have hW2 (i j : ι) : IsPathConnected (W i ∩ W j) := by
    have := hW i j j
    rwa [inter_assoc, inter_self] at this
  have hW1 (i : ι) : IsPathConnected (W i) := by
    have := hW2 i i
    rwa [inter_self] at this
  -- the standard paths
  choose c hc using hcov
  have hpath (i : ι) (y : X) : ∃ r : Path x y, y ∈ W i → range r ⊆ W i ∩ W (c y) := by
    by_cases hy : y ∈ W i
    · obtain ⟨r, hr⟩ := (hW2 i (c y)).joinedIn x ⟨hx i, hx (c y)⟩ y ⟨hy, hc y⟩
      exact ⟨r, fun _ ↦ range_subset_iff.mpr hr⟩
    · obtain ⟨r, -⟩ := (hW1 (c y)).joinedIn x (hx (c y)) y (hc y)
      exact ⟨r, fun h ↦ absurd h hy⟩
  choose r hr using hpath
  let T : ι → ∀ y, Path x y := fun i y ↦ if h : y = x then (Path.refl x).cast rfl h else r i y
  have hTx (i : ι) : T i x = Path.refl x := by simp [T]
  have hT (i : ι) (y : X) (hy : y ∈ W i) : range (T i y) ⊆ W i ∩ W (c y) := by
    by_cases h : y = x
    · subst h
      rw [hTx]
      rintro _ ⟨t, rfl⟩
      exact ⟨hx i, hx (c y)⟩
    · simp only [T, h, dite_false]
      exact hr i y hy
  -- the glued functor
  let F : ∀ i, FundamentalGroupoid (W i) ⥤ SingleObj G := fun i ↦ localFunctor f hT i
  have hF : ∀ i j {y z : X} (p : Path y z) (hi : range p ⊆ W i) (hj : range p ⊆ W j),
      ((F i).map ⌈p.codRestrict hi⌉ : G) = (F j).map ⌈p.codRestrict hj⌉ := by
    intro i j y z p hi hj
    have hy : y ∈ W i ∩ W j := ⟨hi ⟨0, p.source⟩, hj ⟨0, p.source⟩⟩
    have hz : z ∈ W i ∩ W j := ⟨hi ⟨1, p.target⟩, hj ⟨1, p.target⟩⟩
    obtain ⟨εy, hεy⟩ := (hW2 i j).joinedIn x ⟨hx i, hx j⟩ y hy
    obtain ⟨εz, hεz⟩ := (hW2 i j).joinedIn x ⟨hx i, hx j⟩ z hz
    obtain ⟨θy, hθy⟩ := (hW i j (c y)).joinedIn x ⟨⟨hx i, hx j⟩, hx (c y)⟩ y ⟨hy, hc y⟩
    obtain ⟨θz, hθz⟩ := (hW i j (c z)).joinedIn x ⟨⟨hx i, hx j⟩, hx (c z)⟩ z ⟨hz, hc z⟩
    replace hεy := range_subset_iff.mpr hεy
    replace hεz := range_subset_iff.mpr hεz
    replace hθy := range_subset_iff.mpr hθy
    replace hθz := range_subset_iff.mpr hθz
    have hθy' (k : ι) (hk : W i ∩ W j ⊆ W k) : range θy ⊆ W k ∩ W (c y) :=
      fun _ h ↦ ⟨hk (hθy h).1, (hθy h).2⟩
    have hθz' (k : ι) (hk : W i ∩ W j ⊆ W k) : range θz ⊆ W k ∩ W (c z) :=
      fun _ h ↦ ⟨hk (hθz h).1, (hθz h).2⟩
    change ((F i).map (arr p hi) : G) = (F j).map (arr p hj)
    rw [localFunctor_map_arr_eq f hf hT p hi εy θy εz θz (hεy.trans inter_subset_left)
        (hεz.trans inter_subset_left) (hθy' i inter_subset_left) (hθz' i inter_subset_left),
      localFunctor_map_arr_eq f hf hT p hj εy θy εz θz (hεy.trans inter_subset_right)
        (hεz.trans inter_subset_right) (hθy' j inter_subset_right) (hθz' j inter_subset_right),
      loopValue_eq_of_subset_inter f hf (i := i) (j := j)
        (range_trans_subset hεy (range_symm_subset fun _ h ↦ (hθy h).1)),
      loopValue_eq_of_subset_inter f hf (i := i) (j := j)
        (range_trans_subset hεz (range_symm_subset fun _ h ↦ (hθz h).1)),
      loopValue_eq_of_subset_inter f hf (i := i) (j := j)
        (range_trans_subset (range_trans_subset hεy (subset_inter hi hj))
          (range_symm_subset hεz))]
  obtain ⟨F', hF', -⟩ := FundamentalGroupoid.existsUnique_functor_of_isOpen_cover hWo
    (fun y ↦ ⟨c y, hc y⟩) F hF
  let g : FundamentalGroup X x →* G :=
    { toFun a := (F'.map a : G)
      map_one' := F'.map_id _
      map_mul' a b := by
        rw [End.mul_def, F'.map_comp, SingleObj.comp_as_mul] }
  have hres : ∀ i (b : FundamentalGroup (W i) ⟨x, hx i⟩),
      g (mapSubtypeVal (hx i) b) = f i b := by
    intro i b
    induction b using Path.Homotopic.Quotient.ind with | mk ℓ => ?_
    have h₁ : g (mapSubtypeVal (hx i) ⌈ℓ⌉) = (F'.map ⌈ℓ.map continuous_subtype_val⌉ : G) :=
      rfl
    rw [h₁, hF' i _ (Path.range_map_subtypeVal_subset ℓ)]
    have hcorr : corr f c T i x = 1 := by
      rw [corr, hTx, hTx]
      exact loopValue_trans_symm_self f (Path.refl x) (fun _ ⟨_, h⟩ ↦ h ▸ hx (c x))
    have harr : ∀ (γ : Path x x) (hγ : range γ ⊆ W i), γ = Path.refl x →
        arr γ hγ = 𝟙 (FundamentalGroupoid.mk (⟨x, hx i⟩ : W i)) := by
      rintro γ hγ rfl
      rfl
    have hTi : range (T i x) ⊆ W i := fun _ h ↦ (hT i x (hx i) h).1
    change ((localFunctor f hT i).map
      (arr (ℓ.map continuous_subtype_val) (Path.range_map_subtypeVal_subset ℓ)) : G) = _
    rw [localFunctor_map_arr, hcorr, one_mul, inv_one, mul_one,
      loopValue_eq f (range_trans_subset (range_trans_subset hTi
        (Path.range_map_subtypeVal_subset ℓ)) (range_symm_subset hTi)),
      arr_trans, arr_trans, arr_symm, harr (T i x) _ (hTx i), IsIso.inv_id, Category.id_comp,
      Category.comp_id]
    rfl
  refine ⟨g, fun i ↦ MonoidHom.ext (hres i), fun g' hg' ↦ ?_⟩
  refine MonoidHom.ext fun a ↦ ?_
  have hgen := iSup_range_map_subtypeVal_eq_top W hWo (fun y ↦ ⟨c y, hc y⟩) hx hW2
  have hle : ⨆ i, (mapSubtypeVal (hx i)).range ≤ g'.eqLocus g := by
    refine iSup_le fun i ↦ ?_
    rintro _ ⟨b, rfl⟩
    exact (DFunLike.congr_fun (hg' i) b).trans (hres i b).symm
  rw [hgen] at hle
  exact hle (Subgroup.mem_top a)


/-! ### The presentation -/

section Presentation

variable {ι : Type w} {W : ι → Set X} {x : X} (hx : ∀ i, x ∈ W i)

/-- `π₁(W i ∩ W j, x) → π₁(W i, x)` and `π₁(W i ∩ W j, x) → π₁(W j, x)` followed by
`π₁(W i, x) → π₁(X, x)`, `π₁(W j, x) → π₁(X, x)` agree. -/
lemma mapSubtypeVal_map_inclusion_inter (i j : ι)
    (ω : FundamentalGroup (W i ∩ W j : Set X) ⟨x, mem_inter (hx i) (hx j)⟩) :
    mapSubtypeVal (hx i) (map (ContinuousMap.inclusion inter_subset_left) _ ω) =
      mapSubtypeVal (hx j) (map (ContinuousMap.inclusion inter_subset_right) _ ω) := by
  induction ω using Path.Homotopic.Quotient.ind with | mk ℓ => ?_
  rfl

/-- The van Kampen relations `ι_{ij}(ω) ι_{ji}(ω)⁻¹` (`ω ∈ π₁(W i ∩ W j, x)`, `ι_{ij}` induced by
`W i ∩ W j ⊆ W i`) in the free product of the `π₁(W i, x)`. -/
def vanKampenRelators : Set (Monoid.CoprodI fun i ↦ FundamentalGroup (W i) ⟨x, hx i⟩) :=
  {r | ∃ (i j : ι) (ω : FundamentalGroup (W i ∩ W j : Set X) ⟨x, mem_inter (hx i) (hx j)⟩),
    r = Monoid.CoprodI.of (i := i) (map (ContinuousMap.inclusion inter_subset_left) _ ω) *
      (Monoid.CoprodI.of (i := j) (map (ContinuousMap.inclusion inter_subset_right) _ ω))⁻¹}

/-- **Seifert–van Kampen, presentation form** (Hatcher, Theorem 1.20). Let `X` be covered by open
sets `W i`, all containing `x`, with path-connected triple intersections `W i ∩ W j ∩ W k`. Then
`π₁(X, x)` is the free product of the `π₁(W i, x)` modulo the normal subgroup generated by the
relations `ι_{ij}(ω) = ι_{ji}(ω)`, `ω ∈ π₁(W i ∩ W j, x)`; the isomorphism is induced by the
inclusions `W i ⊆ X` (`vanKampenMulEquiv_mk_of`). -/
noncomputable def vanKampenMulEquiv (hWo : ∀ i, IsOpen (W i)) (hcov : ∀ y, ∃ i, y ∈ W i)
    (hW : ∀ i j k, IsPathConnected (W i ∩ W j ∩ W k)) :
    (Monoid.CoprodI fun i ↦ FundamentalGroup (W i) ⟨x, hx i⟩) ⧸
        Subgroup.normalClosure (vanKampenRelators hx) ≃* FundamentalGroup X x := by
  let N := Subgroup.normalClosure (vanKampenRelators hx)
  let φ := Monoid.CoprodI.lift fun i ↦ mapSubtypeVal (hx i)
  have hN : N ≤ φ.ker := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨i, j, ω, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    have h₁ := Monoid.CoprodI.lift_of (M := fun i ↦ FundamentalGroup (W i) ⟨x, hx i⟩)
      (fun i ↦ mapSubtypeVal (hx i)) (i := i) (map (ContinuousMap.inclusion inter_subset_left) _ ω)
    have h₂ := Monoid.CoprodI.lift_of (M := fun i ↦ FundamentalGroup (W i) ⟨x, hx i⟩)
      (fun i ↦ mapSubtypeVal (hx i)) (i := j) (map (ContinuousMap.inclusion inter_subset_right) _ ω)
    exact h₁.trans ((mapSubtypeVal_map_inclusion_inter hx i j ω).trans h₂.symm)
  let φ' : _ ⧸ N →* FundamentalGroup X x := QuotientGroup.lift N φ hN
  let f : ∀ i, FundamentalGroup (W i) ⟨x, hx i⟩ →* _ ⧸ N := fun i ↦
    (QuotientGroup.mk' N).comp
      (Monoid.CoprodI.of (M := fun i ↦ FundamentalGroup (W i) ⟨x, hx i⟩) (i := i))
  have hf : ∀ i j, (f i).comp
        (map (ContinuousMap.inclusion (inter_subset_left : W i ∩ W j ⊆ W i))
          ⟨x, mem_inter (hx i) (hx j)⟩) =
      (f j).comp (map (ContinuousMap.inclusion (inter_subset_right : W i ∩ W j ⊆ W j))
        ⟨x, mem_inter (hx i) (hx j)⟩) := by
    intro i j
    ext ω
    change (QuotientGroup.mk _ : _ ⧸ N) = QuotientGroup.mk _
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    exact Subgroup.subset_normalClosure ⟨i, j, ω, rfl⟩
  have hu := existsUnique_hom_of_isOpen_cover_of_isPathConnected_inter hWo hcov hx hW f hf
  let ψ := hu.exists.choose
  have hψ : ∀ i, ψ.comp (mapSubtypeVal (hx i)) = f i := hu.exists.choose_spec
  refine MonoidHom.toMulEquiv φ' ψ ?_ ?_
  · refine QuotientGroup.monoidHom_ext N (Monoid.CoprodI.ext_hom _ _ fun i ↦
      MonoidHom.ext fun a ↦ ?_)
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, φ', QuotientGroup.lift_mk, φ,
      Monoid.CoprodI.lift_of]
    exact DFunLike.congr_fun (hψ i) a
  · have hu' := existsUnique_hom_of_isOpen_cover_of_isPathConnected_inter hWo hcov hx hW
      (fun i ↦ mapSubtypeVal (hx i)) fun i j ↦ MonoidHom.ext fun ω ↦
        mapSubtypeVal_map_inclusion_inter hx i j ω
    refine hu'.unique (fun i ↦ ?_) (fun i ↦ MonoidHom.id_comp _)
    rw [MonoidHom.comp_assoc, hψ]
    ext a
    simp only [MonoidHom.comp_apply, f, QuotientGroup.mk'_apply, φ', QuotientGroup.lift_mk, φ,
      Monoid.CoprodI.lift_of]

@[simp] lemma vanKampenMulEquiv_mk_of (hWo : ∀ i, IsOpen (W i)) (hcov : ∀ y, ∃ i, y ∈ W i)
    (hW : ∀ i j k, IsPathConnected (W i ∩ W j ∩ W k)) {i : ι}
    (a : FundamentalGroup (W i) ⟨x, hx i⟩) :
    vanKampenMulEquiv hx hWo hcov hW (QuotientGroup.mk
      (Monoid.CoprodI.of (M := fun i ↦ FundamentalGroup (W i) ⟨x, hx i⟩) a)) =
      mapSubtypeVal (hx i) a :=
  Monoid.CoprodI.lift_of (M := fun i ↦ FundamentalGroup (W i) ⟨x, hx i⟩)
    (fun i ↦ mapSubtypeVal (hx i)) a

end Presentation

end FundamentalGroup
