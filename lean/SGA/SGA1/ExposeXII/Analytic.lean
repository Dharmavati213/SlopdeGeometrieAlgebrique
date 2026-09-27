/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import SGA.SGA1.ExposeXII.SchemePoints

/-!
# SGA 1, Exposé XII, 1.1: the analytic space of a scheme (reduced version)

XII.1.1 attaches to a scheme `X` locally of finite type over `ℂ` an analytic space `X^an` with
underlying set `X(ℂ)` and a morphism of locally ringed spaces `φ : X^an → X`. Mathlib has no
complex analytic spaces; here we build the reduced analytic space `(X^an)_red`, over any
complete nontrivially normed field `K`:

* `IsAnalyticAt g x`: near `x`, `g` is an analytic function of finitely many sections of `𝒪_X`
  over an affine open containing `x`; this does not depend on the affine open
  (`IsAnalyticAt.exists_of_isAffineOpen`), and analytic functions form a ring stable under
  analytic operations and inversion of non-vanishing functions;
* `analyticSheaf K X`: the sheaf of analytic functions on `X(K)`, whose stalks are local rings;
  `analytification K X` is `X(K)` as a locally ringed space;
* `toSchemeHom K X : analytification K X ⟶ X`: the canonical morphism `φ` of XII.1.1, sending a
  section of `𝒪_X` to its values at `K`-points;
* `analytificationMap f`: a `K`-morphism `f : X → Y` induces a morphism of locally ringed spaces
  `X(K)^an → Y(K)^an`, compatible with `φ` (XII.1.2, `analytificationMap_comp_toSchemeHom`).

For `K = ℂ` the analytic functions are the holomorphic functions on `(X^an)_red`. The nilpotent
structure of `X^an` for non-reduced `X` (the sheaf `𝒪_{ℂⁿ}/I·𝒪_{ℂⁿ}`) needs the sheaf of
holomorphic functions on `ℂⁿ` and coherence of ideal sheaves, which mathlib does not have.
-/

universe u

noncomputable section

namespace SGA.SGA1.ExposeXII

open AlgebraicGeometry CategoryTheory Topology Set Opposite Filter

namespace SchemePoints

attribute [local instance] sectionsAlgebra

section Eval

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  {U : X.Opens} (hU : IsAffineOpen U)

open Classical in
/-- The value at a `K`-point `p` of a section `s` over an affine open `U` (defined as `0` when `p`
is not in `U`). -/
def eval (s : Γ(X, U)) (p : SchemePoints K X) : K :=
  if h : p.pt ∈ U then (exists_chart_eq hU p h).choose s else 0

@[simp] lemma eval_chart (s : Γ(X, U)) (φ : Points K Γ(X, U)) : eval hU s (chart hU φ) = φ s := by
  rw [eval, dite_eq_left_of_eq_true (eq_true (pt_chart hU φ))]
  congr 1
  exact chart_injective hU (exists_chart_eq hU _ (pt_chart hU φ)).choose_spec

lemma eval_res {V : X.Opens} (hV : IsAffineOpen V) (h : V ≤ U) (s : Γ(X, U))
    {p : SchemePoints K X} (hp : p.pt ∈ V) :
    eval hV (X.presheaf.map (homOfLE h).op s) p = eval hU s p := by
  obtain ⟨φ, rfl⟩ := exists_chart_eq hV p hp
  rw [eval_chart, ← chart_map hU hV h, eval_chart]
  rfl

lemma eval_eq_div {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hWU : W ≤ U)
    (hWV : W ≤ V) (a : Γ(X, U)) (c s : Γ(X, V)) (k : ℕ)
    (h : X.presheaf.map (homOfLE hWU).op a * (X.presheaf.map (homOfLE hWV).op s) ^ k =
      X.presheaf.map (homOfLE hWV).op c)
    (hs : IsUnit (X.presheaf.map (homOfLE hWV).op s)) {y : SchemePoints K X} (hy : y.pt ∈ W) :
    eval hU a y = eval hV c y / eval hV s y ^ k := by
  rw [← eval_res hU hW hWU a hy, ← eval_res hV hW hWV c hy, ← eval_res hV hW hWV s hy]
  obtain ⟨w, rfl⟩ := exists_chart_eq hW y hy
  simp only [eval_chart]
  have := congr(w $h)
  rw [map_mul, map_pow] at this
  rw [← this, mul_div_cancel_right₀]
  exact pow_ne_zero _ (hs.map w).ne_zero

lemma eval_ne_zero {s : Γ(X, U)} {y : SchemePoints K X} (hy : y.pt ∈ X.basicOpen s) :
    eval hU s y ≠ 0 := by
  have hW := hU.basicOpen s
  have := hU.isLocalization_basicOpen s
  rw [← eval_res hU hW (X.basicOpen_le s) s hy]
  obtain ⟨w, rfl⟩ := exists_chart_eq hW y hy
  rw [eval_chart]
  exact ((IsLocalization.Away.algebraMap_isUnit (R := Γ(X, U)) (S := Γ(X, X.basicOpen s)) s).map
    w).ne_zero

variable [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]

lemma continuousAt_eval (s : Γ(X, U)) {p : SchemePoints K X} (hp : p.pt ∈ U) :
    ContinuousAt (eval hU s) p := by
  obtain ⟨φ, rfl⟩ := exists_chart_eq hU p hp
  rw [← (isOpenEmbedding_chart hU).continuousAt_iff]
  have : eval hU s ∘ chart hU = fun φ : Points K Γ(X, U) ↦ φ s := funext (eval_chart hU s)
  rw [this]
  exact (Points.continuous_apply s).continuousAt

lemma mem_nhds_pt {p : SchemePoints K X} (hp : p.pt ∈ U) :
    {q : SchemePoints K X | q.pt ∈ U} ∈ 𝓝 p :=
  (continuous_pt.isOpen_preimage _ U.2).mem_nhds hp

end Eval

/-! ### Analytic functions on `X(K)` -/

section Analytic

variable {K : Type u} [NontriviallyNormedField K] {X : Scheme.{u}} [X.Over (Spec (.of K))]

/-- A function `g` on `X(K)` is analytic at `x` if, near `x`, it is an analytic function of
finitely many sections of `𝒪_X` over an affine open containing `x`. For `K = ℂ` these are the
holomorphic functions on the reduced analytic space `(X^an)_red`. -/
def IsAnalyticAt (g : SchemePoints K X → K) (x : SchemePoints K X) : Prop :=
  ∃ (U : X.Opens) (hU : IsAffineOpen U) (_ : x.pt ∈ U) (n : ℕ) (a : Fin n → Γ(X, U))
    (G : (Fin n → K) → K), AnalyticAt K G (fun i ↦ eval hU (a i) x) ∧
      ∀ᶠ y in 𝓝 x, g y = G (fun i ↦ eval hU (a i) y)

/-- The analyticity of a function at a point may be tested in any affine chart. -/
theorem IsAnalyticAt.exists_of_isAffineOpen {g : SchemePoints K X → K} {x : SchemePoints K X}
    (hg : IsAnalyticAt g x) {V : X.Opens} (hV : IsAffineOpen V) (hxV : x.pt ∈ V) :
    ∃ (n : ℕ) (a : Fin n → Γ(X, V)) (G : (Fin n → K) → K),
      AnalyticAt K G (fun i ↦ eval hV (a i) x) ∧
        ∀ᶠ y in 𝓝 x, g y = G (fun i ↦ eval hV (a i) y) := by
  obtain ⟨U, hU, hxU, n, a, G, hG, hgG⟩ := hg
  obtain ⟨f, s, hfs, hxs⟩ := exists_basicOpen_le_affine_inter hU hV x.pt ⟨hxU, hxV⟩
  have hW : IsAffineOpen (X.basicOpen s) := hV.basicOpen s
  have hWV : X.basicOpen s ≤ V := X.basicOpen_le s
  have hWU : X.basicOpen s ≤ U := hfs ▸ X.basicOpen_le f
  have hloc := hV.isLocalization_basicOpen s
  have hsx : x.pt ∈ X.basicOpen s := hfs ▸ hxs
  have hex : ∀ i : Fin n, ∃ (c : Γ(X, V)) (k : ℕ),
      X.presheaf.map (homOfLE hWU).op (a i) * (X.presheaf.map (homOfLE hWV).op s) ^ k =
        X.presheaf.map (homOfLE hWV).op c := fun i ↦ by
    obtain ⟨⟨c, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers s)
      (X.presheaf.map (homOfLE hWU).op (a i))
    exact ⟨c, k, by simpa [RingHom.algebraMap_toAlgebra] using h⟩
  choose c k hck using hex
  have hunit : IsUnit (X.presheaf.map (homOfLE hWV).op s) :=
    IsLocalization.Away.algebraMap_isUnit (R := Γ(X, V)) (S := Γ(X, X.basicOpen s)) s
  have key : ∀ y : SchemePoints K X, y.pt ∈ X.basicOpen s → ∀ i,
      eval hU (a i) y = eval hV (c i) y / eval hV s y ^ k i := fun y hy i ↦
    eval_eq_div hU hV hW hWU hWV (a i) (c i) s (k i) (hck i) hunit hy
  let b : Fin (n + 1) → Γ(X, V) := Fin.snoc c s
  let H : (Fin (n + 1) → K) → Fin n → K := fun z i ↦ z (Fin.castSucc i) / z (Fin.last n) ^ k i
  refine ⟨n + 1, b, G ∘ H, ?_, ?_⟩
  · have hHx : H (fun j ↦ eval hV (b j) x) = fun i ↦ eval hU (a i) x := by
      funext i
      simp [H, b, key x hsx i]
    refine AnalyticAt.comp (hHx ▸ hG) (AnalyticAt.pi fun i ↦ ?_)
    have hlast : eval hV (b (Fin.last n)) x ≠ 0 := by
      simpa [b] using eval_ne_zero hV hsx
    exact ((ContinuousLinearMap.proj (R := K) (φ := fun _ : Fin (n + 1) ↦ K)
      (Fin.castSucc i)).analyticAt _).div
      (((ContinuousLinearMap.proj (R := K) (φ := fun _ : Fin (n + 1) ↦ K)
        (Fin.last n)).analyticAt _).pow _) (pow_ne_zero _ hlast)
  · filter_upwards [hgG, mem_nhds_pt hsx] with y hy hyW
    rw [hy]
    simp only [Function.comp_apply, H, b, Fin.snoc_castSucc, Fin.snoc_last]
    congr 1
    funext i
    exact key y hyW i

variable {g g₁ g₂ : SchemePoints K X → K} {x : SchemePoints K X}

lemma IsAnalyticAt.congr (hg : IsAnalyticAt g x) (h : g =ᶠ[𝓝 x] g₁) : IsAnalyticAt g₁ x := by
  obtain ⟨U, hU, hxU, n, a, G, hG, hgG⟩ := hg
  exact ⟨U, hU, hxU, n, a, G, hG, h.symm.trans hgG⟩

lemma isAnalyticAt_const (c : K) (x : SchemePoints K X) : IsAnalyticAt (fun _ ↦ c) x := by
  obtain ⟨U, hU, hxU⟩ := exists_isAffineOpen_mem x
  exact ⟨U, hU, hxU, 0, Fin.elim0, fun _ ↦ c, analyticAt_const, Eventually.of_forall fun _ ↦ rfl⟩

/-- Sections of `𝒪_X` over an affine open are analytic functions on its `K`-points. -/
lemma isAnalyticAt_eval {U : X.Opens} (hU : IsAffineOpen U) (s : Γ(X, U)) (hx : x.pt ∈ U) :
    IsAnalyticAt (eval hU s) x :=
  ⟨U, hU, hx, 1, fun _ ↦ s, fun z ↦ z 0,
    (ContinuousLinearMap.proj (R := K) (φ := fun _ : Fin 1 ↦ K) 0).analyticAt _,
    Eventually.of_forall fun _ ↦ rfl⟩

/-- An analytic function of two analytic functions is analytic. -/
theorem IsAnalyticAt.comp₂ (h₁ : IsAnalyticAt g₁ x) (h₂ : IsAnalyticAt g₂ x) {H : K × K → K}
    (hH : AnalyticAt K H (g₁ x, g₂ x)) : IsAnalyticAt (fun y ↦ H (g₁ y, g₂ y)) x := by
  obtain ⟨U, hU, hxU, n, a, G₁, hG₁, hg₁⟩ := h₁
  obtain ⟨m, b, G₂, hG₂, hg₂⟩ := h₂.exists_of_isAffineOpen hU hxU
  let L₁ : (Fin (n + m) → K) → Fin n → K := fun z i ↦ z (Fin.castAdd m i)
  let L₂ : (Fin (n + m) → K) → Fin m → K := fun z j ↦ z (Fin.natAdd n j)
  have hL₁ : AnalyticAt K L₁ (fun i ↦ eval hU (Fin.append a b i) x) :=
    AnalyticAt.pi fun i ↦ (ContinuousLinearMap.proj (R := K)
      (φ := fun _ : Fin (n + m) ↦ K) (Fin.castAdd m i)).analyticAt _
  have hL₂ : AnalyticAt K L₂ (fun i ↦ eval hU (Fin.append a b i) x) :=
    AnalyticAt.pi fun j ↦ (ContinuousLinearMap.proj (R := K)
      (φ := fun _ : Fin (n + m) ↦ K) (Fin.natAdd n j)).analyticAt _
  have e₁ : L₁ (fun i ↦ eval hU (Fin.append a b i) x) = fun i ↦ eval hU (a i) x := by
    funext i; simp [L₁]
  have e₂ : L₂ (fun i ↦ eval hU (Fin.append a b i) x) = fun i ↦ eval hU (b i) x := by
    funext i; simp [L₂]
  refine ⟨U, hU, hxU, n + m, Fin.append a b, fun z ↦ H (G₁ (L₁ z), G₂ (L₂ z)), ?_, ?_⟩
  · refine AnalyticAt.comp₂ (f := fun z ↦ G₁ (L₁ z)) (g := fun z ↦ G₂ (L₂ z)) ?_
      (AnalyticAt.comp (e₁ ▸ hG₁) hL₁) (AnalyticAt.comp (e₂ ▸ hG₂) hL₂)
    simp only [e₁, e₂]
    rwa [← hg₁.self_of_nhds, ← hg₂.self_of_nhds]
  · filter_upwards [hg₁, hg₂] with y h1 h2
    simp [L₁, L₂, h1, h2]

theorem IsAnalyticAt.comp (h : IsAnalyticAt g x) {H : K → K} (hH : AnalyticAt K H (g x)) :
    IsAnalyticAt (fun y ↦ H (g y)) x :=
  h.comp₂ h (H := fun p ↦ H p.1)
    (AnalyticAt.comp (g := H) (f := fun p : K × K ↦ p.1) (x := (g x, g x)) hH analyticAt_fst)

theorem IsAnalyticAt.add (h₁ : IsAnalyticAt g₁ x) (h₂ : IsAnalyticAt g₂ x) :
    IsAnalyticAt (g₁ + g₂) x :=
  h₁.comp₂ h₂ (H := fun p ↦ p.1 + p.2) (analyticAt_fst.add analyticAt_snd)

theorem IsAnalyticAt.mul (h₁ : IsAnalyticAt g₁ x) (h₂ : IsAnalyticAt g₂ x) :
    IsAnalyticAt (g₁ * g₂) x :=
  h₁.comp₂ h₂ (H := fun p ↦ p.1 * p.2) (analyticAt_fst.mul analyticAt_snd)

theorem IsAnalyticAt.neg (h : IsAnalyticAt g x) : IsAnalyticAt (-g) x :=
  h.comp (H := fun t ↦ -t) analyticAt_id.neg

theorem IsAnalyticAt.sub (h₁ : IsAnalyticAt g₁ x) (h₂ : IsAnalyticAt g₂ x) :
    IsAnalyticAt (g₁ - g₂) x :=
  h₁.comp₂ h₂ (H := fun p ↦ p.1 - p.2) (analyticAt_fst.sub analyticAt_snd)

theorem IsAnalyticAt.inv [CompleteSpace K] (h : IsAnalyticAt g x) (hx : g x ≠ 0) :
    IsAnalyticAt (fun y ↦ (g y)⁻¹) x :=
  h.comp (analyticAt_inv hx)

theorem IsAnalyticAt.continuousAt (h : IsAnalyticAt g x) : ContinuousAt g x := by
  obtain ⟨U, hU, hxU, n, a, G, hG, hgG⟩ := h
  have : ContinuousAt (fun y ↦ G (fun i ↦ eval hU (a i) y)) x :=
    hG.continuousAt.comp (continuousAt_pi.mpr fun i ↦ continuousAt_eval hU (a i) hxU)
  exact this.congr (hgG.mono fun _ h ↦ h.symm)

end Analytic

/-! ### The sheaf of analytic functions -/

section Sheaf

variable (K : Type u) [NontriviallyNormedField K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

open Classical in
/-- Extension by zero of a function on a subset of `X(K)`. -/
def extend {W : Set (SchemePoints K X)} (f : W → K) (y : SchemePoints K X) : K :=
  if h : y ∈ W then f ⟨y, h⟩ else 0

variable {K X}

lemma extend_of_mem {W : Set (SchemePoints K X)} (f : W → K) {y : SchemePoints K X}
    (hy : y ∈ W) : extend K X f y = f ⟨y, hy⟩ := by
  simp [extend, hy]

lemma extend_of_notMem {W : Set (SchemePoints K X)} (f : W → K) {y : SchemePoints K X}
    (hy : y ∉ W) : extend K X f y = 0 := by
  simp [extend, hy]

variable (K X)

/-- The local predicate "analytic" on functions defined on open subsets of `X(K)`. -/
def analyticPredicate : TopCat.LocalPredicate fun _ : TopCat.of (SchemePoints K X) ↦ K where
  pred {W} f := ∀ x : W, IsAnalyticAt (extend K X f) x
  res {W V} i f hf x := (hf ⟨x.1, leOfHom i x.2⟩).congr (by
    filter_upwards [W.2.mem_nhds x.2] with y hy
    rw [extend_of_mem f (leOfHom i hy), extend_of_mem _ hy]
    rfl)
  locality {W} f hf x := by
    obtain ⟨V, hxV, i, hV⟩ := hf x
    refine (hV ⟨x, hxV⟩).congr ?_
    filter_upwards [V.2.mem_nhds hxV] with y hy
    rw [extend_of_mem _ hy, extend_of_mem f (leOfHom i hy)]
    rfl

/-- The analytic functions on an open subset of `X(K)` form a subring of all functions. -/
def analyticSubring (W : TopologicalSpace.Opens (TopCat.of (SchemePoints K X))) :
    Subring (W → K) where
  carrier := {f | (analyticPredicate K X).pred f}
  zero_mem' := by
    intro x
    exact (isAnalyticAt_const 0 x.1).congr (Eventually.of_forall fun y ↦ by
      by_cases hy : y ∈ W <;> simp [extend, hy])
  one_mem' := by
    intro x
    exact (isAnalyticAt_const 1 x.1).congr (by
      filter_upwards [W.2.mem_nhds x.2] with y hy
      simp [extend, show y ∈ W from hy])
  add_mem' {f g} hf hg := by
    intro x
    exact ((hf x).add (hg x)).congr (Eventually.of_forall fun y ↦ by
      by_cases hy : y ∈ W <;> simp [extend, hy])
  mul_mem' {f g} hf hg := by
    intro x
    exact ((hf x).mul (hg x)).congr (Eventually.of_forall fun y ↦ by
      by_cases hy : y ∈ W <;> simp [extend, hy])
  neg_mem' {f} hf := by
    intro x
    exact (hf x).neg.congr (Eventually.of_forall fun y ↦ by
      by_cases hy : y ∈ W <;> simp [extend, hy])

/-- The presheaf of analytic functions on `X(K)`, as a presheaf of commutative rings. -/
def analyticPresheaf : TopCat.Presheaf CommRingCat.{u} (TopCat.of (SchemePoints K X)) where
  obj W := CommRingCat.of (analyticSubring K X W.unop)
  map {W V} i := CommRingCat.ofHom
    { toFun f := ⟨fun x ↦ f.1 ⟨x.1, leOfHom i.unop x.2⟩,
        (analyticPredicate K X).res i.unop f.1 f.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }

/-- XII.1.1, reduced version: the sheaf of analytic functions on `X(K)` (for `K = ℂ`, the
structure sheaf of the reduced analytic space `(X^an)_red`). -/
def analyticSheaf : TopCat.Sheaf CommRingCat.{u} (TopCat.of (SchemePoints K X)) where
  obj := analyticPresheaf K X
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (TopCat.subsheafToTypes (analyticPredicate K X)).property

/-! ### Stalks: `X(K)` as a locally ringed space -/

open CategoryTheory.Limits

/-- Evaluation at `x` of analytic functions on a neighbourhood of `x`. -/
def evalAt (x : TopCat.of (SchemePoints K X)) (W : TopologicalSpace.OpenNhds x) :
    (analyticPresheaf K X).obj (op W.1) ⟶ CommRingCat.of K :=
  CommRingCat.ofHom
    { toFun f := f.1 ⟨x, W.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }

/-- Evaluation at `x`, on the stalk of the sheaf of analytic functions. -/
def evalHom (x : TopCat.of (SchemePoints K X)) :
    (analyticPresheaf K X).stalk x ⟶ CommRingCat.of K :=
  colimit.desc ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ analyticPresheaf K X)
    { pt := CommRingCat.of K
      ι :=
        { app W := evalAt K X x W.unop
          naturality _ _ _ := rfl } }

lemma evalHom_germ (W : TopologicalSpace.Opens (TopCat.of (SchemePoints K X)))
    (x : TopCat.of (SchemePoints K X)) (hx : x ∈ W) (f : (analyticPresheaf K X).obj (op W)) :
    evalHom K X x ((analyticPresheaf K X).germ W x hx f) = f.1 ⟨x, hx⟩ := by
  change (colimit.ι ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ analyticPresheaf K X)
    (op ⟨W, hx⟩) ≫ evalHom K X x) f = _
  rw [evalHom, colimit.ι_desc]
  rfl

variable [CompleteSpace K]

/-- The units of the stalk at `x` are the germs that do not vanish at `x`. -/
theorem isUnit_stalk_iff {x : TopCat.of (SchemePoints K X)}
    (f : (analyticPresheaf K X).stalk x) : IsUnit f ↔ evalHom K X x f ≠ 0 := by
  constructor
  · rintro ⟨⟨f, g, hf, hg⟩, rfl⟩ h
    have := congr_arg (evalHom K X x) hf
    rw [map_mul, map_one] at this
    simp [h] at this
  · intro hf
    obtain ⟨W, hxW, f, rfl⟩ := (analyticPresheaf K X).exists_germ_eq f
    rw [evalHom_germ] at hf
    have hcont : ContinuousAt (extend K X f.1) x := (f.2 ⟨x, hxW⟩).continuousAt
    have hne : extend K X f.1 x ≠ 0 := by rwa [extend_of_mem _ hxW]
    obtain ⟨V₀, hV₀, hV₀o, hxV₀⟩ := mem_nhds_iff.mp
      ((hcont.eventually_ne hne).and (W.2.mem_nhds hxW))
    let V : TopologicalSpace.Opens (TopCat.of (SchemePoints K X)) := ⟨V₀, hV₀o⟩
    have hVW : V ≤ W := fun y hy ↦ (hV₀ hy).2
    have hVf : ∀ y : V, f.1 ⟨y.1, hVW y.2⟩ ≠ 0 := fun y ↦ by
      have := (hV₀ y.2).1
      rwa [extend_of_mem _ (hVW y.2)] at this
    let g : (analyticPresheaf K X).obj (op V) := ⟨fun y ↦ (f.1 ⟨y.1, hVW y.2⟩)⁻¹, fun y ↦ by
      refine ((f.2 ⟨y.1, hVW y.2⟩).inv (by rw [extend_of_mem _ (hVW y.2)]; exact hVf y)).congr ?_
      filter_upwards [V.2.mem_nhds y.2] with z hz
      rw [extend_of_mem _ (hVW hz), extend_of_mem _ hz]⟩
    let fV := (analyticPresheaf K X).map (homOfLE hVW).op f
    have hfg : fV * g = 1 := Subtype.ext (funext fun y ↦ mul_inv_cancel₀ (hVf y))
    have hgerm : (analyticPresheaf K X).germ V x hxV₀ fV =
        (analyticPresheaf K X).germ W x hxW f :=
      TopCat.Presheaf.germ_res_apply _ (homOfLE hVW) x hxV₀ f
    rw [← hgerm]
    refine IsUnit.of_mul_eq_one ((analyticPresheaf K X).germ V x hxV₀ g) ?_
    rw [← map_mul, hfg, map_one]

omit [CompleteSpace K] in
instance (x : TopCat.of (SchemePoints K X)) : Nontrivial ((analyticPresheaf K X).stalk x) :=
  ⟨⟨0, 1, fun h ↦ by simpa using congr_arg (evalHom K X x) h⟩⟩

instance isLocalRing_stalk (x : TopCat.of (SchemePoints K X)) :
    IsLocalRing ((analyticPresheaf K X).stalk x) := by
  apply IsLocalRing.of_nonunits_add
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_stalk_iff, not_not] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]

/-- XII.1.1, reduced version: `X(K)` with its sheaf of analytic functions, as a locally ringed
space. For `K = ℂ` this is the reduced analytic space `(X^an)_red` associated with `X`. -/
def analytification : LocallyRingedSpace where
  carrier := TopCat.of (SchemePoints K X)
  presheaf := analyticPresheaf K X
  IsSheaf := (analyticSheaf K X).property
  isLocalRing := isLocalRing_stalk K X

end Sheaf

/-! ### Values of sections of `𝒪_X` at `K`-points -/

section Value

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]

lemma top_le_preimage {p : SchemePoints K X} {V : X.Opens} (hp : p.pt ∈ V) : ⊤ ≤ p.1 ⁻¹ᵁ V :=
  fun x _ ↦ by rwa [Subsingleton.elim x (IsLocalRing.closedPoint K)]

/-- The value at a `K`-point `p ∈ V` of a section `s` of `𝒪_X` over `V`. -/
def value {V : X.Opens} (s : Γ(X, V)) (p : SchemePoints K X) (hp : p.pt ∈ V) : K :=
  (Scheme.ΓSpecIso (.of K)).hom (p.1.appLE V ⊤ (top_le_preimage hp) s)

lemma value_res {V V' : X.Opens} (h : V' ≤ V) (s : Γ(X, V)) (p : SchemePoints K X)
    (hp : p.pt ∈ V') :
    value (X.presheaf.map (homOfLE h).op s) p hp = value s p (h hp) := by
  obtain ⟨p, hp'⟩ := p
  change (Scheme.ΓSpecIso (.of K)).hom (p.appLE V' ⊤ _ (X.presheaf.map (homOfLE h).op s)) =
    (Scheme.ΓSpecIso (.of K)).hom (p.appLE V ⊤ _ s)
  rw [← CommRingCat.comp_apply (X.presheaf.map (homOfLE h).op), Scheme.Hom.map_appLE]

lemma value_chart {U V : X.Opens} (hU : IsAffineOpen U) (h : U ≤ V) (s : Γ(X, V))
    (φ : Points K Γ(X, U)) :
    value s (chart hU φ) (h (pt_chart hU φ)) = φ (X.presheaf.map (homOfLE h).op s) := by
  simp only [value, chart]
  rw [Scheme.Hom.comp_appLE, IsAffineOpen.fromSpec_app_of_le hU V h]
  simp only [Category.assoc]
  change ((Scheme.ΓSpecIso Γ(X, U)).inv ≫
      (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop ≫
        (Scheme.ΓSpecIso (.of K)).hom) (X.presheaf.map (homOfLE h).op s) = _
  rw [Scheme.ΓSpecIso_naturality]
  erw [Iso.inv_hom_id_assoc]
  rfl

/-- On an affine open, the value of a section is its evaluation in the chart. -/
lemma value_eq_eval {U V : X.Opens} (hU : IsAffineOpen U) (h : U ≤ V) (s : Γ(X, V))
    {p : SchemePoints K X} (hp : p.pt ∈ U) :
    value s p (h hp) = eval hU (X.presheaf.map (homOfLE h).op s) p := by
  obtain ⟨φ, rfl⟩ := exists_chart_eq hU p hp
  rw [value_chart hU h s φ, eval_chart]

lemma mem_basicOpen_of_value_ne_zero {V : X.Opens} (s : Γ(X, V)) {p : SchemePoints K X}
    (hp : p.pt ∈ V) (h : value s p hp ≠ 0) : p.pt ∈ X.basicOpen s := by
  have ht : IsUnit (p.1.appLE V ⊤ (top_le_preimage hp) s) :=
    (MulEquiv.isUnit_map (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv).mp (Ne.isUnit h)
  have := Scheme.basicOpen_appLE p.1 ⊤ V (top_le_preimage hp) s
  rw [Scheme.basicOpen_of_isUnit _ ht, top_inf_eq] at this
  have hmem : IsLocalRing.closedPoint K ∈ p.1 ⁻¹ᵁ X.basicOpen s := this ▸ trivial
  exact hmem

end Value

/-! ### The canonical morphism `X(K)^an → X` -/

section Morphism

variable (K : Type u) [NontriviallyNormedField K] (X : Scheme.{u}) [X.Over (Spec (.of K))]

lemma isAnalyticAt_value {V : X.Opens} (s : Γ(X, V))
    {W : TopologicalSpace.Opens (TopCat.of (SchemePoints K X))}
    (hW : ∀ z ∈ W, (z : SchemePoints K X).pt ∈ V) (y : W) :
    IsAnalyticAt (extend K X (W := W) fun z ↦ value s z.1 (hW z.1 z.2)) y := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (hW y.1 y.2) V.2
  have hUV' : U ≤ V := hUV
  refine (isAnalyticAt_eval hU (X.presheaf.map (homOfLE hUV').op s) hyU).congr ?_
  filter_upwards [W.2.mem_nhds y.2, mem_nhds_pt hyU] with z hzW hzU
  rw [extend_of_mem _ hzW, ← value_eq_eval hU hUV' s hzU]

/-- The continuous map `X(K) → X`. -/
def ptHom : TopCat.of (SchemePoints K X) ⟶ X.toPresheafedSpace.carrier :=
  TopCat.ofHom ⟨pt, continuous_pt⟩

/-- Values of sections of `𝒪_X` over `V`, as analytic functions on `V(K)`. -/
def valueHom (V : X.Opens) :
    Γ(X, V) →+* analyticSubring K X ((TopologicalSpace.Opens.map (ptHom K X)).obj V) where
  toFun s := ⟨fun z ↦ value s z.1 z.2, fun y ↦ isAnalyticAt_value K X s (fun z hz ↦ hz) y⟩
  map_one' := Subtype.ext (funext fun z ↦ by simp [value])
  map_mul' a b := Subtype.ext (funext fun z ↦ by simp [value])
  map_zero' := Subtype.ext (funext fun z ↦ by simp [value])
  map_add' a b := Subtype.ext (funext fun z ↦ by simp [value])

variable [CompleteSpace K]

/-- XII.1.1, the canonical morphism `φ : X^an → X`, reduced version: the map of ringed spaces
`X(K) → X` sending a section of `𝒪_X` to its values at `K`-points. -/
def toScheme : (analytification K X).toPresheafedSpace.Hom X.toPresheafedSpace where
  base := ptHom K X
  c :=
    { app V := CommRingCat.ofHom (valueHom K X V.unop)
      naturality {V V'} i := by
        ext s
        apply Subtype.ext
        funext z
        exact value_res (leOfHom i.unop) s z.1 z.2 }

/-- XII.1.1, the canonical morphism `φ : X^an → X` (reduced version), as a morphism of locally
ringed spaces: a germ of `𝒪_X` whose value at a `K`-point does not vanish is invertible. -/
def toSchemeHom : analytification K X ⟶ X.toLocallyRingedSpace :=
  ⟨toScheme K X, fun y ↦ by
    refine ⟨fun t ht ↦ ?_⟩
    obtain ⟨V, hyV, s, rfl⟩ := X.presheaf.exists_germ_eq t
    rw [PresheafedSpace.stalkMap_germ_apply] at ht
    have h₁ := (isUnit_stalk_iff K X _).mp ht
    erw [evalHom_germ] at h₁
    exact (X.mem_basicOpen s _ hyV).mp (mem_basicOpen_of_value_ne_zero s hyV h₁)⟩

end Morphism

/-! ### Functoriality (XII.1.2) -/

section Functoriality

variable {K : Type u} [NontriviallyNormedField K] {X Y : Scheme.{u}} [X.Over (Spec (.of K))]
  [Y.Over (Spec (.of K))] (f : X ⟶ Y) [f.IsOver (Spec (.of K))]

/-- Analytic functions pull back to analytic functions along `K`-morphisms. -/
theorem IsAnalyticAt.comp_map {g : SchemePoints K Y → K} {x : SchemePoints K X}
    (hg : IsAnalyticAt g (map f x)) : IsAnalyticAt (g ∘ map f) x := by
  obtain ⟨V, hV, hxV, n, a, G, hG, hgG⟩ := hg
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x.pt ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).2
  have hU : IsAffineOpen U := hU
  have e : U ≤ f ⁻¹ᵁ V := hUV
  have key : ∀ y : SchemePoints K X, y.pt ∈ U → ∀ i,
      eval hV (a i) (map f y) = eval hU (f.appLE V U e (a i)) y := by
    intro y hy i
    obtain ⟨φ, rfl⟩ := exists_chart_eq hU y hy
    rw [map_chart f hU hV e, eval_chart, eval_chart]
    rfl
  refine ⟨U, hU, hxU, n, fun i ↦ f.appLE V U e (a i), G, ?_, ?_⟩
  · simpa only [key x hxU] using hG
  · filter_upwards [((continuous_map f).tendsto x).eventually hgG, mem_nhds_pt hxU] with y hy hyU
    simp only [Function.comp_apply, hy, key y hyU]

variable [CompleteSpace K]

/-- The pull-back of an analytic function along `f`. -/
def pullbackAnalytic (W : TopologicalSpace.Opens (TopCat.of (SchemePoints K Y)))
    (hW : IsOpen (map (K := K) f ⁻¹' W)) : analyticSubring K Y W →+*
      analyticSubring K X ⟨map f ⁻¹' W, hW⟩ where
  toFun g := ⟨fun z ↦ g.1 ⟨map f z.1, z.2⟩, fun z ↦ by
    refine (IsAnalyticAt.comp_map f (g.2 ⟨map f z.1, z.2⟩)).congr ?_
    filter_upwards [hW.mem_nhds z.2] with y hy
    have h₁ : map f y ∈ (W : Set (SchemePoints K Y)) := hy
    have h₂ : y ∈ ((⟨map f ⁻¹' W, hW⟩ : TopologicalSpace.Opens (TopCat.of (SchemePoints K X))) :
      Set (SchemePoints K X)) := hy
    simp only [Function.comp_apply, extend, h₁, h₂, ↓reduceDIte]⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The continuous map `X(K) → Y(K)` in `TopCat`. -/
def mapHom : TopCat.of (SchemePoints K X) ⟶ TopCat.of (SchemePoints K Y) :=
  TopCat.ofHom ⟨map f, continuous_map f⟩

/-- XII.1.2: the morphism of ringed spaces `X(K)^an → Y(K)^an` induced by `f`. -/
def analytificationHom :
    (analytification K X).toPresheafedSpace.Hom (analytification K Y).toPresheafedSpace where
  base := mapHom f
  c :=
    { app W := CommRingCat.ofHom
        (pullbackAnalytic f W.unop ((TopologicalSpace.Opens.map (mapHom f)).obj W.unop).2)
      naturality _ _ _ := rfl }

/-- XII.1.2: a `K`-morphism `f : X → Y` induces a morphism of locally ringed spaces
`X(K)^an → Y(K)^an` (pull-back of analytic functions). -/
def analytificationMap : analytification K X ⟶ analytification K Y :=
  ⟨analytificationHom f, fun y ↦ by
    refine ⟨fun t ht ↦ ?_⟩
    obtain ⟨W, hyW, g, rfl⟩ := (analytification K Y).presheaf.exists_germ_eq t
    rw [PresheafedSpace.stalkMap_germ_apply] at ht
    have h₁ := (isUnit_stalk_iff K X _).mp ht
    erw [evalHom_germ] at h₁
    exact (isUnit_stalk_iff K Y _).mpr (by erw [evalHom_germ]; exact h₁)⟩

omit [CompleteSpace K] in
lemma value_map {V : Y.Opens} (s : Γ(Y, V)) (p : SchemePoints K X) (hp : (map f p).pt ∈ V) :
    value s (map f p) hp = value (f.app V s) p hp := by
  have H : ∀ (q : Spec (.of K) ⟶ X) (e₁ : ⊤ ≤ (q ≫ f) ⁻¹ᵁ V) (e₂ : ⊤ ≤ q ⁻¹ᵁ (f ⁻¹ᵁ V)),
      (q ≫ f).appLE V ⊤ e₁ s = q.appLE (f ⁻¹ᵁ V) ⊤ e₂ (f.app V s) := by
    intro q e₁ e₂
    rw [Scheme.Hom.comp_appLE]
    rfl
  exact congr_arg (Scheme.ΓSpecIso (.of K)).hom (H p.1 _ _)

/-- XII.1.2: the square `X^an → X`, `Y^an → Y` commutes with `f^an` and `f`. -/
theorem analytificationMap_comp_toSchemeHom :
    analytificationMap f ≫ toSchemeHom K Y = toSchemeHom K X ≫ f.toLRSHom := by
  apply LocallyRingedSpace.Hom.ext'
  refine PresheafedSpace.Hom.ext _ _ rfl ?_
  ext V s
  apply Subtype.ext
  funext z
  exact value_map f s z.1 z.2

@[simp] lemma analytificationMap_base_apply (x : SchemePoints K X) :
    (analytificationMap f).base x = map f x := rfl

end Functoriality

end SchemePoints

end SGA.SGA1.ExposeXII
