/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigherProductCovering
import SGA.Foundations.Topology.FiniteCoveringBaseChange

/-!
# Transport of coverings along the base of a locally trivial family

Let `π : P → B` be continuous, and `C₁ → P`, `C₂ → P` covering maps. Over a subset `N ⊆ B` with
a trivialization `Θ : π⁻¹(N) ≃ N × F` (over `N`), a path `γ` in `N` gives a homeomorphism from the
part of `C` over `π⁻¹(γ 0)` to the part over `π⁻¹(γ 1)`, compatible with the coordinates in `F`
(`RiemannHigher.fibreTransport`): pull `C` back to `I × F` along `(t, f) ↦ Θ⁻¹(γ t, f)` and use
`RiemannHigher.intervalSliceHomeomorph` (a covering of `I × F` is the product of `I` with its slice
over `0`). Consequently, whether `C₁` and `C₂` are isomorphic over `π⁻¹(b)` (`FibreIso`) does not
change along paths in `N` (`FibreIso.iff_of_path`), and if `π` is trivial over path-connected
neighbourhoods of all points, the set of such `b` is clopen (`isClopen_setOf_fibreIso`).

This is the topological step of the parameter-space argument for XII.5.1 in higher dimension
(`SGA.SGA1.ExposeXII.RiemannHigher`): the parameters `q` for which an algebraic family matches a
given covering on the fibre over `q` form a clopen set. General topology.
-/

noncomputable section

open Topology unitInterval Set

namespace SGA.SGA1.ExposeXII.RiemannHigher

section Interval

/-- The contraction `(t, s) ↦ t * s` of `I` to `0`. -/
def intervalContraction : C(I × I, I) where
  toFun x := x.1 * x.2
  continuous_toFun := by fun_prop

lemma intervalContraction_zero (s : I) : intervalContraction (0, s) = 0 := zero_mul s

lemma intervalContraction_one (s : I) : intervalContraction (1, s) = s := one_mul s

variable {F D : Type*} [TopologicalSpace F] [TopologicalSpace D] {q : D → I × F}
  (hq : IsCoveringMap q)

/-- A covering of `I × F` is the product of `I` with its slice over `{0} × F`. -/
abbrev intervalTriv : I × SliceSpace q 0 ≃ₜ D :=
  sliceHomeomorph hq intervalContraction intervalContraction_zero intervalContraction_one

lemma proj_intervalTriv (x : I × SliceSpace q 0) : q (intervalTriv hq x) = (x.1, (q x.2.1).2) :=
  proj_sliceHomeomorph hq _ _ _ x

/-- For a covering of `I × F`, the slices over `{0} × F` and over `{s} × F` are homeomorphic over
`F`. -/
def intervalSliceHomeomorph (s : I) : SliceSpace q 0 ≃ₜ SliceSpace q s where
  toFun c := ⟨intervalTriv hq (s, c), by rw [proj_intervalTriv hq]⟩
  invFun c := ((intervalTriv hq).symm c.1).2
  left_inv c := by
    change ((intervalTriv hq).symm (intervalTriv hq (s, c))).2 = c
    rw [Homeomorph.symm_apply_apply]
  right_inv c := by
    set x := (intervalTriv hq).symm c.1 with hx
    have hcx : intervalTriv hq x = c.1 := Homeomorph.apply_symm_apply _ _
    have h₁ : x.1 = s := by
      have := proj_intervalTriv hq x
      rw [hcx] at this
      exact (congrArg Prod.fst this).symm.trans c.2
    refine Subtype.ext ?_
    change intervalTriv hq (s, x.2) = c.1
    rw [← hcx, ← h₁]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma snd_intervalSliceHomeomorph (s : I) (c : SliceSpace q 0) :
    (q (intervalSliceHomeomorph hq s c).1).2 = (q c.1).2 := by
  change (q (intervalTriv hq (s, c))).2 = _
  rw [proj_intervalTriv hq]

end Interval

section Family

variable {B P F C : Type*} [TopologicalSpace B] [TopologicalSpace P] [TopologicalSpace F]
  [TopologicalSpace C] {π : P → B} {N : Set B}
  (Θ : {x : P // π x ∈ N} ≃ₜ N × F) (hΘ : ∀ x, ((Θ x).1 : B) = π x)
  {p : C → P} (hp : IsCoveringMap p)

/-- The part of a covering `p : C → P` over the fibre `π⁻¹(b)` of `π : P → B`. -/
abbrev FibreSpace (p : C → P) (π : P → B) (b : B) : Type _ := {c : C // π (p c) = b}

/-- The coordinate in `F` of a point of `FibreSpace p π b`, `b ∈ N`. -/
def fibreCoord {b : B} (hb : b ∈ N) (c : FibreSpace p π b) : F :=
  (Θ ⟨p c.1, by rw [c.2]; exact hb⟩).2

include hp in
lemma continuous_fibreCoord {b : B} (hb : b ∈ N) : Continuous (fibreCoord Θ (p := p) hb) := by
  have := hp.continuous
  unfold fibreCoord
  fun_prop

variable (γ : C(I, N))

/-- The map `I × F → P`, `(t, f) ↦ Θ⁻¹(γ t, f)`. -/
def pathChart : C(I × F, P) where
  toFun x := (Θ.symm (γ x.1, x.2)).1
  continuous_toFun := by fun_prop

include hΘ in
lemma proj_pathChart (x : I × F) : π (pathChart Θ γ x) = γ x.1 := by
  have := hΘ (Θ.symm (γ x.1, x.2))
  rw [Homeomorph.apply_symm_apply] at this
  exact this.symm

lemma trivialization_pathChart (x : I × F) (hx : π (pathChart Θ γ x) ∈ N) :
    Θ ⟨pathChart Θ γ x, hx⟩ = (γ x.1, x.2) := by
  have : (⟨pathChart Θ γ x, hx⟩ : {x : P // π x ∈ N}) = Θ.symm (γ x.1, x.2) := Subtype.ext rfl
  rw [this, Homeomorph.apply_symm_apply]

/-- The slice of the pullback of `C` along `pathChart` over `{s} × F` is the part of `C` over
`π⁻¹(γ s)`. -/
def pathSliceEquiv (s : I) :
    SliceSpace (fun d : (⇑(pathChart Θ γ)).Pullback p ↦ d.1.1) s ≃ₜ
      FibreSpace p π (γ s : B) where
  toFun d := ⟨d.1.1.2, by
    rw [← d.1.2, proj_pathChart Θ hΘ, show d.1.1.1.1 = s from d.2]⟩
  invFun c := ⟨⟨((s, fibreCoord Θ (γ s).2 c), c.1), by
    let x : {x : P // π x ∈ N} := ⟨p c.1, by rw [c.2]; exact (γ s).2⟩
    have h : (γ s, (Θ x).2) = Θ x := Prod.ext (Subtype.ext ((hΘ x).trans c.2).symm) rfl
    change (Θ.symm (γ s, (Θ x).2)).1 = p c.1
    rw [h, Homeomorph.symm_apply_apply]⟩, rfl⟩
  left_inv d := by
    obtain ⟨⟨⟨⟨t, f⟩, c⟩, hd⟩, ht⟩ := d
    change t = s at ht
    subst ht
    refine Subtype.ext (Subtype.ext (Prod.ext (Prod.ext rfl ?_) rfl))
    change (Θ ⟨p c, _⟩).2 = f
    generalize_proofs h₁
    have hd' : pathChart Θ γ (t, f) = p c := hd
    have e : (⟨p c, h₁⟩ : {x : P // π x ∈ N}) = ⟨pathChart Θ γ (t, f), by rw [hd']; exact h₁⟩ :=
      Subtype.ext hd'.symm
    rw [e, trivialization_pathChart]
  right_inv c := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    have := continuous_fibreCoord Θ hp (γ s).2
    fun_prop

lemma fibreCoord_pathSliceEquiv (s : I)
    (d : SliceSpace (fun d : (⇑(pathChart Θ γ)).Pullback p ↦ d.1.1) s) :
    fibreCoord Θ (γ s).2 (pathSliceEquiv Θ hΘ hp γ s d) = d.1.1.1.2 := by
  obtain ⟨⟨⟨⟨t, f⟩, c⟩, hd⟩, ht⟩ := d
  change t = s at ht
  subst ht
  change (Θ ⟨p c, _⟩).2 = f
  generalize_proofs h₁
  have hd' : pathChart Θ γ (t, f) = p c := hd
  have e : (⟨p c, h₁⟩ : {x : P // π x ∈ N}) = ⟨pathChart Θ γ (t, f), by rw [hd']; exact h₁⟩ :=
    Subtype.ext hd'.symm
  rw [e, trivialization_pathChart]

/-- Transport along a path `γ` in `N`: the parts of `C` over `π⁻¹(γ 0)` and over `π⁻¹(γ 1)` are
homeomorphic, compatibly with the coordinates in `F`. -/
def fibreTransport : FibreSpace p π (γ 0 : B) ≃ₜ FibreSpace p π (γ 1 : B) :=
  (pathSliceEquiv Θ hΘ hp γ 0).symm.trans
    ((intervalSliceHomeomorph (q := fun d : (⇑(pathChart Θ γ)).Pullback p ↦ d.1.1)
      (hp.pullbackFst (pathChart Θ γ).continuous) 1).trans (pathSliceEquiv Θ hΘ hp γ 1))

lemma fibreCoord_fibreTransport (c : FibreSpace p π (γ 0 : B)) :
    fibreCoord Θ (γ 1).2 (fibreTransport Θ hΘ hp γ c) = fibreCoord Θ (γ 0).2 c := by
  unfold fibreTransport
  simp only [Homeomorph.trans_apply]
  rw [fibreCoord_pathSliceEquiv]
  have := snd_intervalSliceHomeomorph (q := fun d : (⇑(pathChart Θ γ)).Pullback p ↦ d.1.1)
    (hp.pullbackFst (pathChart Θ γ).continuous) 1 ((pathSliceEquiv Θ hΘ hp γ 0).symm c)
  refine this.trans ?_
  conv_rhs => rw [← (pathSliceEquiv Θ hΘ hp γ 0).apply_symm_apply c]
  rw [fibreCoord_pathSliceEquiv]

end Family

section FibreIso

variable {B P C₁ C₂ : Type*} [TopologicalSpace B] [TopologicalSpace P] [TopologicalSpace C₁]
  [TopologicalSpace C₂] (p₁ : C₁ → P) (p₂ : C₂ → P) (π : P → B)

/-- The coverings `C₁` and `C₂` of `P` are isomorphic over the fibre `π⁻¹(b)`. -/
def FibreIso (b : B) : Prop :=
  ∃ φ : FibreSpace p₁ π b ≃ₜ FibreSpace p₂ π b, ∀ c, p₂ (φ c).1 = p₁ c.1

variable {p₁ p₂ π} {F : Type*} [TopologicalSpace F] {N : Set B}
  (Θ : {x : P // π x ∈ N} ≃ₜ N × F) (hΘ : ∀ x, ((Θ x).1 : B) = π x)
  (hp₁ : IsCoveringMap p₁) (hp₂ : IsCoveringMap p₂)

include hΘ in
lemma fibreSpace_eq_of_fibreCoord_eq {b : B} (hb : b ∈ N) {x y : P} (hx : π x = b)
    (hy : π y = b) (h : (Θ ⟨x, by rw [hx]; exact hb⟩).2 = (Θ ⟨y, by rw [hy]; exact hb⟩).2) :
    x = y := by
  have h₁ : (Θ ⟨x, by rw [hx]; exact hb⟩).1 = (Θ ⟨y, by rw [hy]; exact hb⟩).1 :=
    Subtype.ext ((hΘ _).trans (hx.trans ((hΘ _).trans hy).symm))
  exact congrArg Subtype.val (Θ.injective (Prod.ext h₁ h))

include hΘ hp₁ hp₂ in
lemma FibreIso.of_path (γ : C(I, N)) (h : FibreIso p₁ p₂ π (γ 0 : B)) :
    FibreIso p₁ p₂ π (γ 1 : B) := by
  obtain ⟨φ, hφ⟩ := h
  let τ₁ := fibreTransport Θ hΘ hp₁ γ
  let τ₂ := fibreTransport Θ hΘ hp₂ γ
  refine ⟨τ₁.symm.trans (φ.trans τ₂), fun c ↦ ?_⟩
  refine fibreSpace_eq_of_fibreCoord_eq Θ hΘ (γ 1).2 (τ₁.symm.trans (φ.trans τ₂) c).2 c.2 ?_
  change fibreCoord Θ (γ 1).2 (τ₂ (φ (τ₁.symm c))) = fibreCoord Θ (γ 1).2 c
  rw [fibreCoord_fibreTransport]
  have hφc : fibreCoord Θ (γ 0).2 (φ (τ₁.symm c)) = fibreCoord Θ (γ 0).2 (τ₁.symm c) := by
    unfold fibreCoord
    congr 2
    exact Subtype.ext (hφ _)
  rw [hφc, ← fibreCoord_fibreTransport Θ hΘ hp₁ γ (τ₁.symm c), Homeomorph.apply_symm_apply]

include hΘ hp₁ hp₂ in
lemma FibreIso.iff_of_path (γ : C(I, N)) :
    FibreIso p₁ p₂ π (γ 0 : B) ↔ FibreIso p₁ p₂ π (γ 1 : B) := by
  refine ⟨FibreIso.of_path Θ hΘ hp₁ hp₂ γ, fun h ↦ ?_⟩
  have := FibreIso.of_path Θ hΘ hp₁ hp₂ (γ.comp ⟨σ, continuous_symm⟩) (by simpa using h)
  simpa using this

include hΘ hp₁ hp₂ in
lemma FibreIso.iff_of_isPathConnected (hN : IsPathConnected N) {b b' : B} (hb : b ∈ N)
    (hb' : b' ∈ N) : FibreIso p₁ p₂ π b ↔ FibreIso p₁ p₂ π b' := by
  let γ := ((hN.joinedIn b hb b' hb').joined_subtype).somePath
  have := FibreIso.iff_of_path Θ hΘ hp₁ hp₂ ⟨γ, γ.continuous⟩
  simpa using this

omit [TopologicalSpace F] in
variable (p₁ p₂ π) in
/-- If `π : P → B` is trivial over path-connected neighbourhoods of every point, the set of
`b ∈ B` over which two coverings of `P` are isomorphic is clopen. -/
theorem isClopen_setOf_fibreIso
    (hloc : ∀ b₀ : B, ∃ N ∈ 𝓝 b₀, IsPathConnected N ∧ ∃ (F : Type*) (_ : TopologicalSpace F)
      (Θ : {x : P // π x ∈ N} ≃ₜ N × F), ∀ x, ((Θ x).1 : B) = π x)
    (hp₁ : IsCoveringMap p₁) (hp₂ : IsCoveringMap p₂) :
    IsClopen {b | FibreIso p₁ p₂ π b} := by
  have key (b₀ : B) : ∃ N ∈ 𝓝 b₀, ∀ b ∈ N, FibreIso p₁ p₂ π b ↔ FibreIso p₁ p₂ π b₀ := by
    obtain ⟨N, hN, hpc, F, _, Θ, hΘ⟩ := hloc b₀
    exact ⟨N, hN, fun b hb ↦
      FibreIso.iff_of_isPathConnected Θ hΘ hp₁ hp₂ hpc hb (mem_of_mem_nhds hN)⟩
  refine ⟨⟨isOpen_iff_mem_nhds.mpr fun b₀ hb₀ ↦ ?_⟩, isOpen_iff_mem_nhds.mpr fun b₀ hb₀ ↦ ?_⟩
  · obtain ⟨N, hN, h⟩ := key b₀
    exact Filter.mem_of_superset hN fun b hb hb' ↦ hb₀ ((h b hb).mp hb')
  · obtain ⟨N, hN, h⟩ := key b₀
    exact Filter.mem_of_superset hN fun b hb ↦ (h b hb).mpr hb₀

end FibreIso

end SGA.SGA1.ExposeXII.RiemannHigher
