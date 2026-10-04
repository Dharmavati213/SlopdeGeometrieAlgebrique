/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.CoherentKernel
import SGA.Foundations.Analytic.Oka

/-!
# Coherent sheaves of modules (Serre's definition) and Oka's theorem at sheaf level

For a sheaf of modules `M` on a locally ringed space `X` and an open `Ω ⊆ X`, following Serre
(*Faisceaux algébriques cohérents*, §2, no. 12–13) we say:

* finitely many sections `s₁, …, s_p` of `M` over `W` *generate `M` at `x ∈ W`* if their germs
  span the stalk `M_x` over `𝒪_{X,x}` (`LocallyRingedSpace.Modules.GeneratesAt`);
* `M` is *of finite type on `Ω`* (`IsFiniteTypeOn`) if every point of `Ω` has an open
  neighbourhood `W ⊆ Ω` with finitely many sections over `W` generating `M` at every point of `W`;
* the *relations* of `s₁, …, s_p` over `W` are of finite type (`HasFiniteRelations`) if every
  point of `W` has an open neighbourhood `W' ⊆ W` with finitely many relations
  `rₖ ∈ 𝒪_X(W')^p`, `∑ᵢ rₖᵢ sᵢ = 0` on `W'`, whose germs generate, at every point `y ∈ W'`, the
  module `stalkRelations M s y` of all relations `∑ aᵢ (sᵢ)_y = 0` with `aᵢ ∈ 𝒪_{X,y}`;
* `M` is *coherent on `Ω`* (`IsCoherentOn`) if it is of finite type on `Ω` and the relations of
  every finite family of sections over every open `W ⊆ Ω` are of finite type.

**Oka's theorem at sheaf level** (`AnalyticGeometry.isCoherentOn_structureModule_modelSpace`):
the structure sheaf of `𝕜^σ` (`AnalyticGeometry.modelSpace 𝕜 (σ → 𝕜)`, the sheaf of analytic
functions) is a coherent module over itself, for any complete nontrivially normed field `𝕜`. It is
`AnalyticGeometry.hasFiniteRelationsNear` (one row) read through the identification of the stalks
with germs of analytic functions.

References: J.-P. Serre, *Faisceaux algébriques cohérents*, Ann. of Math. 61 (1955), §2;
Grauert–Remmert, *Coherent analytic sheaves*, 2.5; Stacks Project, Tag 01BU (coherent modules).
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}} (M : X.Modules)

/-- The restriction of a section of `M` to a smaller open, as an element of the module of sections
over the smaller open. -/
abbrev resSection {W W' : Opens X} (h : W' ≤ W) (s : M.presheaf.obj (op W)) :
    M.presheaf.obj (op W') :=
  M.presheaf.map (homOfLE h).op s

/-- The module of relations `∑ᵢ aᵢ (sᵢ)ₓ = 0`, `aᵢ ∈ 𝒪_{X,x}`, between the germs at `x` of
finitely many sections over `W ∋ x`. -/
def stalkRelations {ι : Type*} [Fintype ι] {W : Opens X} (s : ι → M.presheaf.obj (op W)) (x : X)
    (hx : x ∈ W) : Submodule (X.presheaf.stalk x) (ι → X.presheaf.stalk x) :=
  LinearMap.ker (Fintype.linearCombination (X.presheaf.stalk x)
    (fun i ↦ M.presheaf.germ W x hx (s i)))

lemma mem_stalkRelations {ι : Type*} [Fintype ι] {W : Opens X} {s : ι → M.presheaf.obj (op W)}
    {x : X} {hx : x ∈ W} {a : ι → X.presheaf.stalk x} :
    a ∈ M.stalkRelations s x hx ↔ ∑ i, a i • M.presheaf.germ W x hx (s i) = 0 := by
  simp [stalkRelations, Fintype.linearCombination_apply]

/-- Finitely many sections over `W` generate `M` at `x ∈ W`: their germs span the stalk. -/
def GeneratesAt {ι : Type*} {W : Opens X} (s : ι → M.presheaf.obj (op W)) (x : X) (hx : x ∈ W) :
    Prop :=
  Submodule.span (X.presheaf.stalk x) (Set.range fun i ↦ M.presheaf.germ W x hx (s i)) = ⊤

/-- `M` is of finite type on the open `Ω`: near every point of `Ω`, finitely many sections
generate `M` at every point. -/
def IsFiniteTypeOn (Ω : Opens X) : Prop :=
  ∀ x ∈ Ω, ∃ W : Opens X, W ≤ Ω ∧ x ∈ W ∧ ∃ (p : ℕ) (s : Fin p → M.presheaf.obj (op W)),
    ∀ y (hy : y ∈ W), M.GeneratesAt s y hy

/-- The relations of finitely many sections over `W` are of finite type: near every point of `W`
there are finitely many relations `rₖ ∈ 𝒪_X(W')^p`, `∑ᵢ rₖᵢ sᵢ = 0` on `W'`, whose germs generate
the module of relations of the germs at every point of `W'`. -/
def HasFiniteRelations {W : Opens X} {p : ℕ} (s : Fin p → M.presheaf.obj (op W)) : Prop :=
  ∀ x ∈ W, ∃ (W' : Opens X) (h : W' ≤ W), x ∈ W' ∧ ∃ (m : ℕ)
    (r : Fin m → Fin p → X.presheaf.obj (op W')),
    (∀ k, ∑ i, r k i • M.resSection h (s i) = 0) ∧
    ∀ y (hy : y ∈ W'), M.stalkRelations s y (h hy) =
      Submodule.span _ (Set.range fun k i ↦ X.presheaf.germ W' y hy (r k i))

/-- `M` is **coherent on `Ω`** (Serre): of finite type on `Ω`, and the relations of every finite
family of sections over an open `W ⊆ Ω` are of finite type. -/
def IsCoherentOn (Ω : Opens X) : Prop :=
  M.IsFiniteTypeOn Ω ∧
    ∀ (W : Opens X), W ≤ Ω → ∀ (p : ℕ) (s : Fin p → M.presheaf.obj (op W)), M.HasFiniteRelations s

variable {M}

lemma IsFiniteTypeOn.mono {Ω Ω' : Opens X} (h : M.IsFiniteTypeOn Ω) (hΩ : Ω' ≤ Ω) :
    M.IsFiniteTypeOn Ω' := by
  intro x hx
  obtain ⟨W, hWΩ, hxW, p, s, hs⟩ := h x (hΩ hx)
  refine ⟨W ⊓ Ω', inf_le_right, ⟨hxW, hx⟩, p, fun i ↦ M.resSection inf_le_left (s i),
    fun y hy ↦ ?_⟩
  have := hs y hy.1
  unfold GeneratesAt at this ⊢
  convert this using 3
  funext i
  exact M.presheaf.germ_res_apply (homOfLE inf_le_left) y hy (s i)

lemma IsCoherentOn.mono {Ω Ω' : Opens X} (h : M.IsCoherentOn Ω) (hΩ : Ω' ≤ Ω) :
    M.IsCoherentOn Ω' :=
  ⟨h.1.mono hΩ, fun W hW p s ↦ h.2 W (hW.trans hΩ) p s⟩

/-- Two sections of a module sheaf with the same germs everywhere are equal. -/
lemma section_ext_germ {W : Opens X} {s t : M.presheaf.obj (op W)}
    (h : ∀ (x : X) (hx : x ∈ W), M.presheaf.germ W x hx s = M.presheaf.germ W x hx t) : s = t :=
  TopCat.Presheaf.section_ext M.toAbSheaf W s t h

/-- The germ of `∑ᵢ rᵢ • sᵢ` is `∑ᵢ (rᵢ)ₓ • (sᵢ)ₓ`. -/
lemma germ_sum_smul {ι : Type*} [Fintype ι] {W : Opens X} (r : ι → X.presheaf.obj (op W))
    (s : ι → M.presheaf.obj (op W)) (x : X) (hx : x ∈ W) :
    M.presheaf.germ W x hx (∑ i, r i • s i) =
      ∑ i, X.presheaf.germ W x hx (r i) • M.presheaf.germ W x hx (s i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ germ_smul M x W hx (r i) (s i)

/-- A family of sections `rₖ ∈ 𝒪_X(W)^p` whose germs are relations of the germs of `s` everywhere
is a family of relations of sections. -/
lemma sum_smul_eq_zero_of_germ {W : Opens X} {p : ℕ} {s : Fin p → M.presheaf.obj (op W)}
    {r : Fin p → X.presheaf.obj (op W)}
    (h : ∀ x (hx : x ∈ W), (fun i ↦ X.presheaf.germ W x hx (r i)) ∈ M.stalkRelations s x hx) :
    ∑ i, r i • s i = 0 := by
  refine M.section_ext_germ fun x hx ↦ ?_
  rw [germ_sum_smul, map_zero]
  exact (M.mem_stalkRelations).mp (h x hx)

/-- Restricting sections does not change the relations between their germs. -/
lemma stalkRelations_resSection {ι : Type*} [Fintype ι] {W W' : Opens X} (h : W' ≤ W)
    (s : ι → M.presheaf.obj (op W)) (x : X) (hx : x ∈ W') :
    M.stalkRelations (fun i ↦ M.resSection h (s i)) x hx = M.stalkRelations s x (h hx) := by
  ext a
  rw [mem_stalkRelations, mem_stalkRelations]
  refine Iff.of_eq (congrArg (fun t ↦ t = 0) (Finset.sum_congr rfl fun i _ ↦ ?_))
  exact congrArg (a i • ·) (M.presheaf.germ_res_apply (homOfLE h) x hx (s i))

variable (X) in
/-- The structure sheaf `𝒪_X` as an `𝒪_X`-module. -/
abbrev structureModule : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

variable (X) in
/-- For the structure sheaf, `∑ aᵢ (sᵢ)ₓ = 0` in the stalk of the module `𝒪_X` iff it holds in the
local ring. -/
lemma mem_stalkRelations_structureModule {ι : Type*} [Fintype ι] {W : Opens X}
    (s : ι → (structureModule X).presheaf.obj (op W)) (x : X) (hx : x ∈ W)
    (a : ι → X.presheaf.stalk x) :
    a ∈ (structureModule X).stalkRelations s x hx ↔
      ∑ i, a i * X.presheaf.germ W x hx (s i) = 0 := by
  have e : stalkUnitLinearEquiv x
      (∑ i, a i • (structureModule X).presheaf.germ W x hx (s i)) =
      ∑ i, a i * X.presheaf.germ W x hx (s i) := by
    refine (map_sum (stalkUnitLinearEquiv x) _ _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    exact ((stalkUnitLinearEquiv x).map_smul (a i) _).trans
      (congrArg (a i * ·) (stalkUnitLinearEquiv_germ x W hx (s i)))
  rw [mem_stalkRelations]
  exact (LinearEquiv.map_eq_zero_iff (stalkUnitLinearEquiv x)).symm.trans
    (Iff.of_eq (congrArg (fun t ↦ t = 0) e))

end AlgebraicGeometry.LocallyRingedSpace.Modules

namespace AnalyticGeometry

open AlgebraicGeometry LocallyRingedSpace Modules

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {σ : Type u} [Fintype σ]

/-- **Oka's theorem, sheaf form, relations**: the relations between finitely many sections of the
structure sheaf of `𝕜^σ` over an open `W` are of finite type. -/
theorem hasFiniteRelations_structureModule_modelSpace {W : Opens (modelSpace 𝕜 (σ → 𝕜))}
    {p : ℕ} (s : Fin p → (structureModule (modelSpace 𝕜 (σ → 𝕜))).presheaf.obj (op W)) :
    (structureModule (modelSpace 𝕜 (σ → 𝕜))).HasFiniteRelations s := by
  intro x hx
  let S : Fin p → analyticSections 𝕜 (E := σ → 𝕜) W := fun i ↦ s i
  let A : Unit → Fin p → (σ → 𝕜) → 𝕜 := fun _ i ↦ extendByZero (S i).1
  obtain ⟨V, hV, hxV, hA, n, g, hg, hgen⟩ :=
    hasFiniteRelationsNear A x fun _ i ↦ (S i).2 ⟨x, hx⟩
  let W' : Opens (modelSpace 𝕜 (σ → 𝕜)) := ⟨V, hV⟩ ⊓ W
  have hW' : W' ≤ W := inf_le_right
  let r : Fin n → Fin p → (modelSpace 𝕜 (σ → 𝕜)).presheaf.obj (op W') := fun k i ↦
    ofAnalyticOnNhd (E := σ → 𝕜) (U := W') (g k i) fun y hy ↦ hg k i y hy.1
  -- germs of the `sᵢ` and of the `rₖᵢ`
  have hs : ∀ y (hy : y ∈ W) i, (modelSpace 𝕜 (σ → 𝕜)).presheaf.germ W y hy (s i) =
      germOf (extendByZero (S i).1) ((S i).2 ⟨y, hy⟩) := fun y hy i ↦
    germ_eq_germOf W hy (s i)
  have hr : ∀ y (hy : y ∈ W') k i, (modelSpace 𝕜 (σ → 𝕜)).presheaf.germ W' y hy (r k i) =
      germOf (g k i) (hg k i y hy.1) := fun y hy k i ↦ by
    refine (germ_eq_germOf W' hy (r k i)).trans (germOf_congr _ ?_)
    filter_upwards [W'.2.mem_nhds hy] with z hz
    rw [extendByZero_of_mem _ hz]
    rfl
  -- the relations at `y ∈ W'`
  have hrel : ∀ y (hy : y ∈ W'), (structureModule _).stalkRelations s y (hW' hy) =
      Submodule.span _ (Set.range fun k i ↦ (modelSpace 𝕜 (σ → 𝕜)).presheaf.germ W' y hy (r k i))
      := fun y hy ↦ by
    have key : ∀ a : Fin p → (analyticPresheaf 𝕜 (σ → 𝕜)).stalk y,
        (∑ i, a i * germOf (A () i) (hA () i y hy.1) = 0 ↔
          a ∈ Submodule.span ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk y)
            (Set.range fun k i ↦ germOf (g k i) (hg k i y hy.1))) := by
      intro a
      rw [← hgen y hy.1, mem_matrixRelationModule]
      exact ⟨fun h _ ↦ h, fun h ↦ h ()⟩
    ext a
    rw [mem_stalkRelations_structureModule]
    simp only [hs y (hW' hy), hr y hy]
    exact key a
  refine ⟨W', hW', ⟨hxV, hx⟩, n, r, fun k ↦ ?_, hrel⟩
  refine sum_smul_eq_zero_of_germ fun y hy ↦ ?_
  rw [stalkRelations_resSection, hrel y hy]
  exact Submodule.subset_span ⟨k, rfl⟩

/-- **Oka's coherence theorem, sheaf form**: the structure sheaf of `𝕜^σ` (the sheaf of analytic
functions, `AnalyticGeometry.modelSpace`) is a coherent module over itself. -/
theorem isCoherentOn_structureModule_modelSpace (Ω : Opens (modelSpace 𝕜 (σ → 𝕜))) :
    (structureModule (modelSpace 𝕜 (σ → 𝕜))).IsCoherentOn Ω := by
  let one : (structureModule (modelSpace 𝕜 (σ → 𝕜))).presheaf.obj (op Ω) :=
    show (modelSpace 𝕜 (σ → 𝕜)).presheaf.obj (op Ω) from 1
  refine ⟨fun x hx ↦ ⟨Ω, le_rfl, hx, 1, fun _ ↦ one, fun y hy ↦ ?_⟩,
    fun W _ p s ↦ hasFiniteRelations_structureModule_modelSpace s⟩
  rw [GeneratesAt, eq_top_iff]
  intro m _
  have h1 : stalkUnitLinearEquiv y
      ((structureModule (modelSpace 𝕜 (σ → 𝕜))).presheaf.germ Ω y hy one) = 1 :=
    (stalkUnitLinearEquiv_germ y Ω hy _).trans (map_one _)
  have hm : m = stalkUnitLinearEquiv y m •
      (structureModule (modelSpace 𝕜 (σ → 𝕜))).presheaf.germ Ω y hy one := by
    apply (stalkUnitLinearEquiv y).injective
    refine Eq.trans ?_ ((stalkUnitLinearEquiv y).map_smul _ _).symm
    rw [h1, smul_eq_mul, mul_one]
  rw [hm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)

end AnalyticGeometry
