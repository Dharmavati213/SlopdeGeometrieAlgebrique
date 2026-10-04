/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.DolbeaultLocal

/-!
# The Dolbeault resolution on `ℂ^σ` as sheaves

The smooth `(0, q)`-forms on the opens of `ℂ^σ` form the sheaf
`AnalyticGeometry.formSheaf σ q = 𝒞^∞(ℂ^σ, FormCoeff σ q)` (smooth maps to the space of
coefficients `(φ_I)_{|I| = q}`), which is fine, hence acyclic (`H'_smoothSheaf_subsingleton`). The
`∂̄`-closed forms form the sheaf `AnalyticGeometry.closedFormSheaf σ q`. The Dolbeault–Grothendieck
lemma (`exists_dbarForm_eq_near`) says that

  `0 → Zᵠ → 𝒞^{0,q} → Z^{q+1} → 0`

is a short exact sequence of abelian sheaves (`AnalyticGeometry.dolbeaultSeq_shortExact`).
Dimension shifting along these sequences shows: if on an open `V` every smooth `∂̄`-closed
`(0, q + 1)`-form is `∂̄` of a smooth `(0, q)`-form on `V`, for all `q`, then `Hⁿ(V, Zᵠ) = 0` for
all `n > 0` and all `q` (`AnalyticGeometry.H'_closedFormSheaf_subsingleton`).

References: Hörmander, *An introduction to complex analysis in several variables*, 7.4;
Godement, *Théorie des faisceaux*, II.4.7; Wells, *Differential analysis on complex manifolds*,
II.3.
-/

noncomputable section

open CategoryTheory Topology TopologicalSpace Opposite Filter Set Metric
open scoped ContDiff

namespace AnalyticGeometry

variable (σ : Type) [Fintype σ] [LinearOrder σ]

/-- The coefficients `(φ_I)_{|I| = q}` of a `(0, q)`-form on `ℂ^σ`. -/
abbrev FormCoeff (q : ℕ) : Type := {I : Finset σ // I.card = q} → ℂ

/-- The sheaf `𝒞^{0,q}` of smooth `(0, q)`-forms on `ℂ^σ`. -/
abbrev formSheaf (q : ℕ) : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (σ → ℂ)) :=
  smoothSheaf (σ → ℂ) (FormCoeff σ q)

variable {σ}

/-- The coefficient family (extended by zero, and zero in the other degrees) of a `(0, q)`-form
`φ` on `U`. -/
def formCoeffs {q : ℕ} {U : Set (σ → ℂ)} (φ : U → FormCoeff σ q) :
    Finset σ → (σ → ℂ) → ℂ :=
  fun I y ↦ if h : I.card = q then extendByZero φ y ⟨I, h⟩ else 0

omit [Fintype σ] [LinearOrder σ] in
lemma formCoeffs_of_card {q : ℕ} {U : Set (σ → ℂ)} (φ : U → FormCoeff σ q) {I : Finset σ}
    (h : I.card = q) (y : σ → ℂ) : formCoeffs φ I y = extendByZero φ y ⟨I, h⟩ := by
  simp [formCoeffs, h]

omit [Fintype σ] [LinearOrder σ] in
lemma formCoeffs_of_card_ne {q : ℕ} {U : Set (σ → ℂ)} (φ : U → FormCoeff σ q) {I : Finset σ}
    (h : I.card ≠ q) : formCoeffs φ I = 0 := by
  funext y
  simp [formCoeffs, h]

omit [LinearOrder σ] in
lemma IsSmoothOn.isSmoothFormAt {q : ℕ} {U : Set (σ → ℂ)} {φ : U → FormCoeff σ q}
    (hφ : IsSmoothOn φ) {x : σ → ℂ} (hx : x ∈ U) : IsSmoothFormAt (formCoeffs φ) x := by
  intro I
  by_cases h : I.card = q
  · have : formCoeffs φ I = fun y ↦ extendByZero φ y ⟨I, h⟩ := by
      funext y
      exact formCoeffs_of_card φ h y
    rw [this]
    exact (contDiff_apply ℝ ℂ (⟨I, h⟩ : {I : Finset σ // I.card = q})).contDiffAt.comp x
      (hφ ⟨x, hx⟩)
  · rw [formCoeffs_of_card_ne φ h]
    exact contDiffAt_const

omit [Fintype σ] [LinearOrder σ] in
/-- The coefficients of a form agree, near a point of an open set, with those of its
restriction. -/
lemma formCoeffs_restrict_eventuallyEq {q : ℕ} {U V : Set (σ → ℂ)} (hV : IsOpen V) (h : V ⊆ U)
    (φ : U → FormCoeff σ q) {x : σ → ℂ} (hx : x ∈ V) (I : Finset σ) :
    formCoeffs (fun y : V ↦ φ ⟨y, h y.2⟩) I =ᶠ[𝓝 x] formCoeffs φ I := by
  filter_upwards [hV.mem_nhds hx] with y hy
  by_cases hI : I.card = q
  · rw [formCoeffs_of_card _ hI, formCoeffs_of_card _ hI, extendByZero_of_mem _ hy,
      extendByZero_of_mem _ (h hy)]
  · rw [formCoeffs_of_card_ne _ hI, formCoeffs_of_card_ne _ hI]

/-- `∂̄` of a form on `U`, as a form on `U`. -/
def dbarOn {q : ℕ} {U : Set (σ → ℂ)} (φ : U → FormCoeff σ q) : U → FormCoeff σ (q + 1) :=
  fun x J ↦ dbarForm (formCoeffs φ) J.1 x

lemma IsSmoothOn.dbarOn {q : ℕ} {U : Set (σ → ℂ)} (hU : IsOpen U) {φ : U → FormCoeff σ q}
    (hφ : IsSmoothOn φ) : IsSmoothOn (dbarOn φ) := by
  refine isSmoothOn_restrict (g := fun x (J : {J : Finset σ // J.card = q + 1}) ↦
    dbarForm (formCoeffs φ) J.1 x) hU fun x hx ↦ ?_
  exact contDiffAt_pi.mpr fun J ↦ (hφ.isSmoothFormAt hx).dbarForm J.1

omit [Fintype σ] in
/-- Away from degree `q + 1` the coefficients of `∂̄φ` vanish, so near every point of `U` the
coefficient family of `dbarOn φ` is `∂̄` of that of `φ`. -/
lemma formCoeffs_dbarOn_eventuallyEq {q : ℕ} {U : Set (σ → ℂ)} (hU : IsOpen U)
    (φ : U → FormCoeff σ q) {x : σ → ℂ} (hx : x ∈ U) (I : Finset σ) :
    formCoeffs (dbarOn φ) I =ᶠ[𝓝 x] dbarForm (formCoeffs φ) I := by
  filter_upwards [hU.mem_nhds hx] with y hy
  by_cases hI : I.card = q + 1
  · rw [formCoeffs_of_card _ hI, extendByZero_of_mem _ hy]
    rfl
  · rw [formCoeffs_of_card_ne _ hI]
    exact (dbarForm_eq_zero_of_card_ne isOpen_univ
      (fun I' hI' y _ ↦ by rw [formCoeffs_of_card_ne φ hI']; rfl) hI (mem_univ y)).symm

/-- `∂̄ ∘ ∂̄ = 0` on smooth forms on an open set. -/
lemma dbarOn_dbarOn {q : ℕ} {U : Set (σ → ℂ)} (hU : IsOpen U) {φ : U → FormCoeff σ q}
    (hφ : IsSmoothOn φ) : dbarOn (dbarOn φ) = 0 := by
  funext x J
  change dbarForm (formCoeffs (dbarOn φ)) J.1 x = 0
  rw [dbarForm_congr (formCoeffs_dbarOn_eventuallyEq hU φ x.2), dbarForm_dbarForm
    (hφ.isSmoothFormAt x.2)]

omit [Fintype σ] in
/-- `∂̄` commutes with restriction. -/
lemma dbarOn_restrict {q : ℕ} {U V : Set (σ → ℂ)} (hV : IsOpen V) (h : V ⊆ U)
    (φ : U → FormCoeff σ q) (y : V) :
    dbarOn (fun y : V ↦ φ ⟨y, h y.2⟩) y = dbarOn φ ⟨y, h y.2⟩ := by
  funext J
  exact dbarForm_congr (formCoeffs_restrict_eventuallyEq hV h φ y.2) J.1

/-! ### The sheaf of `∂̄`-closed forms -/

/-- A form on `U` is smooth and `∂̄`-closed. -/
def IsClosedSmoothOn {q : ℕ} {U : Set (σ → ℂ)} (φ : U → FormCoeff σ q) : Prop :=
  IsSmoothOn φ ∧ dbarOn φ = 0

variable (σ) in
/-- The `∂̄`-closed smooth `(0, q)`-forms on an open set form a subgroup. -/
def closedFormSections (q : ℕ) (U : Opens (σ → ℂ)) : AddSubgroup (U → FormCoeff σ q) where
  carrier := {φ | IsClosedSmoothOn φ}
  add_mem' {φ ψ} hφ hψ := by
    refine ⟨(smoothSections (σ → ℂ) (FormCoeff σ q) U).add_mem hφ.1 hψ.1, ?_⟩
    funext x J
    have hφ' := congrFun (congrFun hφ.2 x) J
    have hψ' := congrFun (congrFun hψ.2 x) J
    change dbarForm (formCoeffs (φ + ψ)) J.1 x = 0
    have : formCoeffs (φ + ψ) = fun I y ↦ formCoeffs φ I y + formCoeffs ψ I y := by
      funext I y
      by_cases hI : I.card = q
      · simp only [formCoeffs_of_card _ hI]
        by_cases hy : y ∈ (U : Set (σ → ℂ)) <;> simp [extendByZero, hy]
      · simp only [formCoeffs_of_card_ne _ hI, Pi.zero_apply, add_zero]
    rw [this, dbarForm_add ((hφ.1.isSmoothFormAt x.2).differentiableAt)
      ((hψ.1.isSmoothFormAt x.2).differentiableAt)]
    change dbarOn φ x J + dbarOn ψ x J = 0
    rw [hφ', hψ']
    simp
  zero_mem' := by
    refine ⟨(smoothSections (σ → ℂ) (FormCoeff σ q) U).zero_mem, ?_⟩
    funext x J
    change dbarForm (formCoeffs (0 : U → FormCoeff σ q)) J.1 x = 0
    have : formCoeffs (0 : U → FormCoeff σ q) = fun _ _ ↦ 0 := by
      funext I y
      by_cases hI : I.card = q
      · simp [formCoeffs_of_card _ hI, extendByZero_zero]
      · simp [formCoeffs_of_card_ne _ hI]
    rw [this]
    exact Finset.sum_eq_zero fun j _ ↦ by
      rw [show (fun _ : σ → ℂ ↦ (0 : ℂ)) = 0 from rfl, dbarPartial_zero, mul_zero]
  neg_mem' {φ} hφ := by
    refine ⟨(smoothSections (σ → ℂ) (FormCoeff σ q) U).neg_mem hφ.1, ?_⟩
    funext x J
    have hφ' := congrFun (congrFun hφ.2 x) J
    change dbarForm (formCoeffs (-φ)) J.1 x = 0
    have : formCoeffs (-φ) = fun I y ↦ formCoeffs (0 : U → FormCoeff σ q) I y -
        formCoeffs φ I y := by
      funext I y
      by_cases hI : I.card = q
      · simp only [formCoeffs_of_card _ hI]
        by_cases hy : y ∈ (U : Set (σ → ℂ)) <;> simp [extendByZero, hy]
      · simp [formCoeffs_of_card_ne _ hI]
    have h0 : IsSmoothOn (0 : U → FormCoeff σ q) :=
      (smoothSections (σ → ℂ) (FormCoeff σ q) U).zero_mem
    rw [this, dbarForm_sub ((h0.isSmoothFormAt x.2).differentiableAt)
      ((hφ.1.isSmoothFormAt x.2).differentiableAt)]
    change dbarOn (0 : U → FormCoeff σ q) x J - dbarOn φ x J = 0
    rw [hφ']
    simp only [Pi.zero_apply, sub_zero]
    change dbarForm (formCoeffs (0 : U → FormCoeff σ q)) J.1 x = 0
    have : formCoeffs (0 : U → FormCoeff σ q) = fun _ _ ↦ 0 := by
      funext I y
      by_cases hI : I.card = q
      · simp [formCoeffs_of_card _ hI, extendByZero_zero]
      · simp [formCoeffs_of_card_ne _ hI]
    rw [this]
    exact Finset.sum_eq_zero fun j _ ↦ by
      rw [show (fun _ : σ → ℂ ↦ (0 : ℂ)) = 0 from rfl, dbarPartial_zero, mul_zero]

/-- Restriction of closed forms. -/
lemma IsClosedSmoothOn.restrict {q : ℕ} {U V : Set (σ → ℂ)} (hV : IsOpen V) (h : V ⊆ U)
    {φ : U → FormCoeff σ q} (hφ : IsClosedSmoothOn φ) :
    IsClosedSmoothOn (fun y : V ↦ φ ⟨y, h y.2⟩) := by
  refine ⟨hφ.1.restrict hV h, funext fun y ↦ ?_⟩
  rw [dbarOn_restrict hV h φ y, hφ.2]
  rfl

variable (σ) in
/-- The local predicate "smooth and `∂̄`-closed". -/
def closedFormPredicate (q : ℕ) : TopCat.LocalPredicate fun _ : TopCat.of (σ → ℂ) ↦
    FormCoeff σ q where
  pred {U} φ := IsClosedSmoothOn φ
  res {U V} i φ hφ := hφ.restrict U.2 (leOfHom i)
  locality {U} φ hφ := by
    refine ⟨fun x ↦ ?_, funext fun x ↦ ?_⟩
    · obtain ⟨V, hxV, i, hV⟩ := hφ x
      exact (hV.1 ⟨x, hxV⟩).congr_of_eventuallyEq
        (extendByZero_eventuallyEq V.2 (leOfHom i) _ _ (fun _ ↦ rfl) hxV).symm
    · obtain ⟨V, hxV, i, hV⟩ := hφ x
      have h1 := congrFun hV.2 ⟨x, hxV⟩
      have h2 : dbarOn (fun y : V ↦ φ ⟨y, leOfHom i y.2⟩) ⟨x, hxV⟩ = dbarOn φ x :=
        dbarOn_restrict V.2 (leOfHom i) φ ⟨x, hxV⟩
      rw [← h2]
      exact h1

variable (σ) in
/-- The presheaf of `∂̄`-closed smooth `(0, q)`-forms. -/
def closedFormPresheaf (q : ℕ) : TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of (σ → ℂ)) where
  obj U := AddCommGrpCat.of (closedFormSections σ q U.unop)
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun φ ↦ ⟨fun x ↦ φ.1 ⟨x, leOfHom i.unop x.2⟩,
        φ.2.restrict V.unop.2 (leOfHom i.unop)⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

variable (σ) in
/-- The sheaf `Zᵠ` of `∂̄`-closed smooth `(0, q)`-forms on `ℂ^σ`. -/
def closedFormSheaf (q : ℕ) : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (σ → ℂ)) where
  obj := closedFormPresheaf σ q
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat)]
    exact (TopCat.subsheafToTypes (closedFormPredicate σ q)).property

/-! ### The sequence `0 → Zᵠ → 𝒞^{0,q} → Z^{q+1} → 0` -/

variable (σ) in
/-- The inclusion `Zᵠ ⟶ 𝒞^{0,q}`. -/
def closedFormInclusion (q : ℕ) : closedFormSheaf σ q ⟶ formSheaf σ q :=
  ObjectProperty.homMk
    { app := fun _ ↦ AddCommGrpCat.ofHom
        { toFun := fun φ ↦ ⟨φ.1, φ.2.1⟩
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }

variable (σ) in
/-- `∂̄ : 𝒞^{0,q} ⟶ Z^{q+1}`. -/
def dbarFormHom (q : ℕ) : formSheaf σ q ⟶ closedFormSheaf σ (q + 1) :=
  ObjectProperty.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun φ ↦ ⟨dbarOn φ.1, φ.2.dbarOn U.unop.2, dbarOn_dbarOn U.unop.2 φ.2⟩
          map_zero' := by
            refine Subtype.ext (funext fun x ↦ funext fun J ↦ ?_)
            change dbarForm (formCoeffs (0 : U.unop → FormCoeff σ q)) J.1 x = 0
            have : formCoeffs (0 : U.unop → FormCoeff σ q) = fun _ _ ↦ 0 := by
              funext I y
              by_cases hI : I.card = q
              · simp [formCoeffs_of_card _ hI, extendByZero_zero]
              · simp [formCoeffs_of_card_ne _ hI]
            rw [this]
            exact Finset.sum_eq_zero fun j _ ↦ by
              rw [show (fun _ : σ → ℂ ↦ (0 : ℂ)) = 0 from rfl, dbarPartial_zero, mul_zero]
          map_add' := fun φ ψ ↦ by
            refine Subtype.ext (funext fun x ↦ funext fun J ↦ ?_)
            change dbarForm (formCoeffs (φ.1 + ψ.1)) J.1 x =
              dbarForm (formCoeffs φ.1) J.1 x + dbarForm (formCoeffs ψ.1) J.1 x
            have : formCoeffs (φ.1 + ψ.1) = fun I y ↦ formCoeffs φ.1 I y + formCoeffs ψ.1 I y := by
              funext I y
              by_cases hI : I.card = q
              · simp only [formCoeffs_of_card _ hI]
                by_cases hy : y ∈ (U.unop : Set (σ → ℂ)) <;> simp [extendByZero, hy]
              · simp only [formCoeffs_of_card_ne _ hI, Pi.zero_apply, add_zero]
            rw [this]
            exact dbarForm_add ((φ.2.isSmoothFormAt x.2).differentiableAt)
              ((ψ.2.isSmoothFormAt x.2).differentiableAt) J.1 }
      naturality := fun U V i ↦ by
        ext φ
        refine Subtype.ext (funext fun y ↦ ?_)
        exact dbarOn_restrict V.unop.2 (leOfHom i.unop) φ.1 y }

lemma closedFormInclusion_comp_dbarFormHom (q : ℕ) :
    closedFormInclusion σ q ≫ dbarFormHom σ q = 0 := by
  refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))
  ext φ
  refine Subtype.ext ?_
  change dbarOn φ.1 = 0
  exact φ.2.2

variable (σ) in
/-- The Dolbeault sequence `0 → Zᵠ → 𝒞^{0,q} → Z^{q+1} → 0`. -/
def dolbeaultSeq (q : ℕ) :
    ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (σ → ℂ)))
      AddCommGrpCat.{0}) :=
  ShortComplex.mk (closedFormInclusion σ q) (dbarFormHom σ q)
    (closedFormInclusion_comp_dbarFormHom q)

omit [Fintype σ] [LinearOrder σ] in
/-- An open set of `ℂ^σ` contains a product of open discs around each of its points. -/
lemma exists_pi_ball_subset [Finite σ] {U : Set (σ → ℂ)} (hU : IsOpen U) {x : σ → ℂ}
    (hx : x ∈ U) : ∃ r > 0, univ.pi (fun i ↦ ball (x i) r) ⊆ U := by
  have := Fintype.ofFinite σ
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨r, hr, fun y hy ↦ hrU ?_⟩
  rw [ball_pi x hr]
  exact hy

/-- **Local exactness of the Dolbeault complex**: `∂̄ : 𝒞^{0,q} ⟶ Z^{q+1}` is locally surjective
(the Dolbeault–Grothendieck lemma, `exists_dbarForm_eq_near`). -/
lemma isLocallySurjective_dbarFormHom (q : ℕ) :
    TopCat.Presheaf.IsLocallySurjective (dbarFormHom σ q).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  obtain ⟨r, hr, hrU⟩ := exists_pi_ball_subset U.2 hx
  set W : σ → Set ℂ := fun i ↦ ball (x i) r
  have hWU : ∀ z ∈ univ.pi W, z ∈ (U : Set (σ → ℂ)) := fun z hz ↦ hrU hz
  have hcl : ∀ J, ∀ z ∈ univ.pi W, dbarForm (formCoeffs t.1) J z = 0 := by
    intro J z hz
    by_cases hJ : J.card = q + 1 + 1
    · have := congrFun (congrFun t.2.2 ⟨z, hWU z hz⟩) ⟨J, hJ⟩
      exact this
    · exact dbarForm_eq_zero_of_card_ne isOpen_univ
        (fun I hI y _ ↦ by rw [formCoeffs_of_card_ne _ hI]; rfl) hJ (mem_univ z)
  obtain ⟨W', hW'o, hxW', hW'W, u, hus, hudeg, hdu⟩ := exists_dbarForm_eq_near
    (fun i ↦ isOpen_ball) (x := x) (fun i _ ↦ mem_ball_self hr)
    (fun z hz ↦ t.2.1.isSmoothFormAt (hWU z hz))
    (fun J hJ z _ ↦ by rw [formCoeffs_of_card_ne _ hJ]; rfl) hcl
  have hV : IsOpen (univ.pi W') := isOpen_set_pi finite_univ fun i _ ↦ hW'o i
  have hVU : univ.pi W' ⊆ (U : Set (σ → ℂ)) := fun z hz ↦
    hWU z fun i _ ↦ hW'W i (hz i (mem_univ i))
  let V : Opens (σ → ℂ) := ⟨univ.pi W', hV⟩
  have hVU' : V ≤ U := hVU
  -- the form `u` as a section over `V`
  let s : V → FormCoeff σ q := fun y I ↦ u I.1 y
  have hs : IsSmoothOn s := isSmoothOn_restrict (g := fun y (I : {I : Finset σ // I.card = q}) ↦
    u I.1 y) hV fun y hy ↦ contDiffAt_pi.mpr fun I ↦ hus y hy I.1
  have hcoeff : ∀ y ∈ (V : Set (σ → ℂ)), ∀ I, formCoeffs s I =ᶠ[𝓝 y] u I := by
    intro y hy I
    filter_upwards [hV.mem_nhds hy] with z hz
    by_cases hI : I.card = q
    · rw [formCoeffs_of_card _ hI, extendByZero_of_mem _ hz]
    · rw [formCoeffs_of_card_ne _ hI, hudeg I hI]
  refine ⟨V, hVU', ⟨⟨s, hs⟩, ?_⟩, hxW'⟩
  refine Subtype.ext (funext fun y ↦ funext fun J ↦ ?_)
  change dbarForm (formCoeffs s) J.1 y = t.1 ⟨y, hVU' y.2⟩ J
  rw [dbarForm_congr (hcoeff y y.2), hdu J.1 y y.2, formCoeffs_of_card _ J.2,
    extendByZero_of_mem _ (hVU' y.2)]

/-- **The Dolbeault resolution**: `0 → Zᵠ → 𝒞^{0,q} → Z^{q+1} → 0` is a short exact sequence of
abelian sheaves on `ℂ^σ`. -/
theorem dolbeaultSeq_shortExact (q : ℕ) : (dolbeaultSeq σ q).ShortExact := by
  refine TopCat.Sheaf.shortExact_of_sections (fun U φ ψ h ↦ ?_) (fun U φ hφ ↦ ?_)
    (isLocallySurjective_dbarFormHom q)
  · exact Subtype.ext (congrArg Subtype.val h :)
  · exact ⟨⟨φ.1, φ.2, congrArg Subtype.val hφ⟩, rfl⟩

/-! ### Cohomology of the sheaves of closed forms -/

/-- `∂̄`-exactness on `V` in degree `q + 1`: every smooth `∂̄`-closed `(0, q + 1)`-form on `V` is
`∂̄` of a smooth `(0, q)`-form on `V`. -/
def DbarExactOn (V : Set (σ → ℂ)) (q : ℕ) : Prop :=
  ∀ g : V → FormCoeff σ (q + 1), IsClosedSmoothOn g →
    ∃ u : V → FormCoeff σ q, IsSmoothOn u ∧ dbarOn u = g

variable [HasExt.{0} (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (σ → ℂ)))
  AddCommGrpCat.{0})]

/-- **Cohomology of `∂̄`-closed forms from global `∂̄`-exactness**, refined: if on an open
`V ⊆ ℂ^σ` every smooth `∂̄`-closed form of degree `≥ q + 1` is `∂̄`-exact, then `Hⁿ(V, Zᵠ) = 0` for
all `n > 0`. -/
theorem H'_closedFormSheaf_subsingleton_of_le (V : Opens (TopCat.of (σ → ℂ))) (n q : ℕ)
    (hV : ∀ q', q ≤ q' → DbarExactOn (V : Set (σ → ℂ)) q') :
    Subsingleton ((closedFormSheaf σ q).H' (n + 1) V) := by
  induction n generalizing q with
  | zero =>
    refine TopCat.Sheaf.subsingleton_H'_one_of_shortExact (dolbeaultSeq_shortExact q) V
      (H'_smoothSheaf_subsingleton 0 V) fun g ↦ ?_
    obtain ⟨u, hu, hdu⟩ := hV q le_rfl g.1 g.2
    exact ⟨⟨u, hu⟩, Subtype.ext hdu⟩
  | succ n ih =>
    exact TopCat.Sheaf.subsingleton_H'_succ_succ_of_shortExact (dolbeaultSeq_shortExact q) V n
      (ih (q + 1) fun q' hq' ↦ hV q' (by omega)) (H'_smoothSheaf_subsingleton (n + 1) V)

/-- **Cohomology of `∂̄`-closed forms from global `∂̄`-exactness** (Dolbeault, Hörmander 7.4):
if on an open `V ⊆ ℂ^σ` every smooth `∂̄`-closed form of positive degree is `∂̄`-exact, then
`Hⁿ(V, Zᵠ) = 0` for all `n > 0` and all `q`. -/
theorem H'_closedFormSheaf_subsingleton (V : Opens (TopCat.of (σ → ℂ)))
    (hV : ∀ q, DbarExactOn (V : Set (σ → ℂ)) q) (n q : ℕ) :
    Subsingleton ((closedFormSheaf σ q).H' (n + 1) V) :=
  H'_closedFormSheaf_subsingleton_of_le V n q fun q' _ ↦ hV q'

end AnalyticGeometry
