/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.SurfacePresentation
import SGA.Foundations.Topology.SurfaceFilling

/-!
# The fundamental group of the Riemann sphere minus finitely many points

For every finite `T ⊆ ℙ¹(ℂ) = OnePoint ℂ` with `m` points and every base point `x` of
`ℙ¹(ℂ) ∖ T`, there are an enumeration `T = {t₁, …, t_m}` and loops `σᵢ` around `tᵢ` such that
`⟨x₁, …, x_m | x₁ ⋯ x_m⟩ → π₁(ℙ¹(ℂ) ∖ T, x)`, `xᵢ ↦ σᵢ`, is well defined and bijective
(`Complex.exists_presentation_fundamentalGroup_compl`). For `T = ∅` this says that `ℙ¹(ℂ)` is
simply connected. A loop around `t` is a loop around `0` in the standard coordinate at `t`
(`Complex.IsLoopAroundAt`, `Complex.sphereCoord`).

The case `∞ ∈ T` is `Complex.exists_presentation_fundamentalGroup_compl_of_infty_mem`. For
`∞ ∉ T`, fill in `∞` in `ℙ¹(ℂ) ∖ (T ∪ {∞})`
(`FundamentalGroup.existsUnique_hom_of_range_eq_compl_singleton`, with the chart `z ↦ 1 / z` at
`∞`, `Complex.inftyChart`): this kills the loop around `∞`, which is the last generator of the
presentation, and an algebraic lemma
(`FreeGroup.bijective_toGroup_prodRelator_of_kill_last`) gives the presentation.

* `PresentedGroup.exists_bijective_toGroup_mulEquiv`: presentations are transported by
  isomorphisms;
* `FreeGroup.bijective_toGroup_prodRelator_of_kill_last`: killing the last generator of
  `⟨x₀, …, x_m | x₀ ⋯ x_m⟩` gives `⟨x₀, …, x_{m-1} | x₀ ⋯ x_{m-1}⟩`;
* `Complex.inftyNhd R`, `Complex.inftyChart R`: the chart `z ↦ 1 / z` of `ℙ¹(ℂ)` at `∞`, on
  `ℙ¹(ℂ) ∖ D̄(0, R)`;
* `Homeomorph.preimageSubtypeVal`: a subset `W ⊆ S` of a space, seen in the subspace `S`.

## References

* [A. Hatcher, *Algebraic Topology*, §1.2][hatcher02]
* [SGA 1, Exposé XIII, 2.12][grothendieck1971]
-/

open Set Topology CategoryTheory Metric OnePoint FundamentalGroup

noncomputable section

namespace PresentedGroup

variable {α G G' : Type*} [Group G] [Group G'] {rels : Set (FreeGroup α)}

/-- **Presentations are transported by isomorphisms**: if `σ : α → G` presents `G` with relators
`rels`, then `ψ ∘ σ` presents `G'` for every isomorphism `ψ : G ≃* G'`. -/
theorem exists_bijective_toGroup_mulEquiv {σ : α → G} {h : ∀ r ∈ rels, FreeGroup.lift σ r = 1}
    (hb : Function.Bijective (toGroup h)) (ψ : G ≃* G') :
    ∃ h' : ∀ r ∈ rels, FreeGroup.lift (fun a ↦ ψ (σ a)) r = 1,
      Function.Bijective (toGroup h') := by
  have h' : ∀ r ∈ rels, FreeGroup.lift (fun a ↦ ψ (σ a)) r = 1 := fun r hr ↦ by
    have : FreeGroup.lift (fun a ↦ ψ (σ a)) = (ψ : G →* G').comp (FreeGroup.lift σ) :=
      FreeGroup.ext_hom _ _ fun a ↦ by simp
    rw [this, MonoidHom.comp_apply, h r hr, map_one]
  refine ⟨h', ?_⟩
  have : toGroup h' = (ψ : G →* G').comp (toGroup h) := ext fun a ↦ by simp
  rw [this, MonoidHom.coe_comp]
  exact ψ.bijective.comp hb

end PresentedGroup

namespace FreeGroup

open PresentedGroup

variable {G G' : Type*} [Group G] [Group G'] {m : ℕ}

/-- **Killing the last generator of `⟨x₀, …, x_m | x₀ ⋯ x_m⟩`.** Let `σ` present `G'` with the
single relation `σ₀ ⋯ σ_m = 1`, and let `π : G' → G` be surjective, kill `σ_m`, and be universal
for this (every homomorphism killing `σ_m` factors through `π`). Then `π ∘ σ₀, …, π ∘ σ_{m-1}`
present `G` with the single relation `x₀ ⋯ x_{m-1} = 1`. -/
theorem bijective_toGroup_prodRelator_of_kill_last {σ : Fin (m + 1) → G'}
    {h : ∀ r ∈ ({prodRelator (m + 1)} : Set (FreeGroup (Fin (m + 1)))), lift σ r = 1}
    (hb : Function.Bijective (toGroup h)) (π : G' →* G) (hπs : Function.Surjective π)
    (hπσ : π (σ (Fin.last m)) = 1)
    (hπu : ∀ f : G' →* PresentedGroup ({prodRelator m} : Set (FreeGroup (Fin m))),
      f (σ (Fin.last m)) = 1 → ∃ f' : G →* _, f'.comp π = f) :
    ∃ h' : ∀ r ∈ ({prodRelator m} : Set (FreeGroup (Fin m))),
      lift (fun i ↦ π (σ i.castSucc)) r = 1, Function.Bijective (toGroup h') := by
  -- the relation
  have hrel : (List.ofFn fun i : Fin m ↦ σ i.castSucc).prod * σ (Fin.last m) = 1 := by
    have := h _ (Set.mem_singleton _)
    rw [lift_prodRelator, List.ofFn_succ', List.concat_eq_append, List.prod_append,
      List.prod_singleton] at this
    exact this
  have h' : ∀ r ∈ ({prodRelator m} : Set (FreeGroup (Fin m))),
      lift (fun i ↦ π (σ i.castSucc)) r = 1 := by
    rintro r rfl
    rw [lift_prodRelator]
    have : (List.ofFn fun i : Fin m ↦ π (σ i.castSucc)) =
        (List.ofFn fun i : Fin m ↦ σ i.castSucc).map π := by
      rw [List.map_ofFn]
      rfl
    rw [this, ← map_list_prod, eq_inv_of_mul_eq_one_left hrel, _root_.map_inv, hπσ, inv_one]
  refine ⟨h', ?_⟩
  -- the inverse map
  set P := PresentedGroup ({prodRelator m} : Set (FreeGroup (Fin m)))
  have hκ : ∀ r ∈ ({prodRelator (m + 1)} : Set (FreeGroup (Fin (m + 1)))),
      lift (Fin.lastCases (1 : P) fun i ↦ PresentedGroup.of i) r = 1 := by
    rintro r rfl
    rw [lift_prodRelator, List.ofFn_succ', List.concat_eq_append, List.prod_append,
      List.prod_singleton]
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc, mul_one]
    have := PresentedGroup.one_of_mem (rels := ({prodRelator m} : Set (FreeGroup (Fin m))))
      (Set.mem_singleton _)
    rw [prodRelator, map_list_prod, List.map_ofFn] at this
    exact this
  set κ : PresentedGroup ({prodRelator (m + 1)} : Set (FreeGroup (Fin (m + 1)))) →* P :=
    toGroup hκ
  set Φ := MulEquiv.ofBijective (toGroup h) hb
  have hΦ (j : Fin (m + 1)) : Φ (PresentedGroup.of j) = σ j := toGroup.of h
  obtain ⟨f', hf'⟩ := hπu (κ.comp Φ.symm.toMonoidHom) (by
    change κ (Φ.symm (σ (Fin.last m))) = 1
    rw [← hΦ, MulEquiv.symm_apply_apply, toGroup.of hκ, Fin.lastCases_last])
  have hf'π (g : G') : f' (π g) = κ (Φ.symm g) := DFunLike.congr_fun hf' g
  -- `f'` is a left inverse
  have hleft : f'.comp (toGroup h') = MonoidHom.id P := PresentedGroup.ext fun i ↦ by
    change f' (toGroup h' (PresentedGroup.of i)) = PresentedGroup.of i
    rw [toGroup.of h', hf'π, ← hΦ, MulEquiv.symm_apply_apply, toGroup.of hκ,
      Fin.lastCases_castSucc]
  -- and a right inverse
  have hcomp (w : PresentedGroup ({prodRelator (m + 1)} : Set (FreeGroup (Fin (m + 1))))) :
      toGroup h' (κ w) = π (Φ w) := by
    have : (toGroup h').comp κ = π.comp Φ.toMonoidHom := PresentedGroup.ext fun j ↦ by
      change toGroup h' (κ (PresentedGroup.of j)) = π (Φ (PresentedGroup.of j))
      induction j using Fin.lastCases with
      | last => rw [toGroup.of hκ, Fin.lastCases_last, _root_.map_one, hΦ, hπσ]
      | cast i => rw [toGroup.of hκ, Fin.lastCases_castSucc, toGroup.of h', hΦ]
    exact DFunLike.congr_fun this w
  refine ⟨fun a b hab ↦ ?_, fun g ↦ ⟨f' g, ?_⟩⟩
  · have := congrArg f' hab
    rwa [← MonoidHom.comp_apply, hleft, ← MonoidHom.comp_apply, hleft] at this
  · obtain ⟨g', rfl⟩ := hπs g
    rw [hf'π, hcomp, MulEquiv.apply_symm_apply]

end FreeGroup

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X] {S W : Set X}

/-- A subset `W ⊆ S` of a space, seen as a subset of the subspace `S`, is homeomorphic to `W`. -/
def preimageSubtypeVal (hWS : W ⊆ S) : ↥(Subtype.val ⁻¹' W : Set S) ≃ₜ W where
  toFun y := ⟨y.1.1, y.2⟩
  invFun w := ⟨⟨w, hWS w.2⟩, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] lemma preimageSubtypeVal_apply (hWS : W ⊆ S) (y : ↥(Subtype.val ⁻¹' W : Set S)) :
    (preimageSubtypeVal hWS y : X) = y.1 :=
  rfl

end Homeomorph

namespace Complex

/-- The neighbourhood `ℙ¹(ℂ) ∖ D̄(0, R)` of `∞`. -/
def inftyNhd (R : ℝ) : Set (OnePoint ℂ) := ((↑) '' closedBall (0 : ℂ) R)ᶜ

lemma isOpen_inftyNhd (R : ℝ) : IsOpen (inftyNhd R) :=
  (isClosed_image_coe.mpr ⟨isClosed_closedBall, isCompact_closedBall 0 R⟩).isOpen_compl

lemma infty_mem_inftyNhd (R : ℝ) : (∞ : OnePoint ℂ) ∈ inftyNhd R := by
  simp [inftyNhd]

lemma coe_mem_inftyNhd {R : ℝ} {w : ℂ} : (w : OnePoint ℂ) ∈ inftyNhd R ↔ R < ‖w‖ := by
  simp [inftyNhd, OnePoint.coe_injective.eq_iff]

/-- `sphereCoord ∞` (`z ↦ 1 / z`, `∞ ↦ 0`) is continuous away from `0`. -/
lemma continuousAt_sphereCoord_infty {z : OnePoint ℂ} (hz : z ≠ ((0 : ℂ) : OnePoint ℂ)) :
    ContinuousAt (sphereCoord ∞) z := by
  induction z using OnePoint.rec with
  | infty =>
    rw [OnePoint.continuousAt_infty']
    have : (sphereCoord ∞ ∘ ((↑) : ℂ → OnePoint ℂ)) = fun w ↦ w⁻¹ := rfl
    rw [this, Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_cobounded
  | coe w =>
    rw [OnePoint.continuousAt_coe]
    have : (sphereCoord ∞ ∘ ((↑) : ℂ → OnePoint ℂ)) = fun w ↦ w⁻¹ := rfl
    rw [this]
    exact continuousAt_inv₀ (fun h ↦ hz (by rw [h]))

/-- The inverse of `z ↦ 1 / z`: `w ↦ 1 / w`, `0 ↦ ∞`. -/
def sphereInv (w : ℂ) : OnePoint ℂ := if w = 0 then ∞ else ((w⁻¹ : ℂ) : OnePoint ℂ)

lemma continuous_sphereInv : Continuous sphereInv := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    rw [ContinuousAt, show sphereInv 0 = ∞ by simp [sphereInv]]
    have h1 : Filter.Tendsto (fun w : ℂ ↦ ((w⁻¹ : ℂ) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 ∞) := by
      refine OnePoint.tendsto_coe_infty.comp ?_
      rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      exact Filter.tendsto_inv₀_nhdsNE_zero
    have h2 : Filter.Tendsto sphereInv (𝓝[≠] 0) (𝓝 ∞) :=
      h1.congr' (eventually_nhdsWithin_of_forall fun w hw ↦ by
        simp [sphereInv, show w ≠ 0 from hw])
    have h3 : Filter.Tendsto sphereInv (pure (0 : ℂ) : Filter ℂ) (𝓝 ∞) :=
      Filter.tendsto_pure_left.mpr fun s hs ↦ by simpa [sphereInv] using mem_of_mem_nhds hs
    have := h2.sup h3
    rwa [nhdsNE_sup_pure] at this
  · have : sphereInv =ᶠ[𝓝 w] fun w ↦ ((w⁻¹ : ℂ) : OnePoint ℂ) :=
      (isOpen_compl_singleton.eventually_mem hw).mono fun v hv ↦ by
        simp [sphereInv, show v ≠ 0 from hv]
    rw [continuousAt_congr this]
    exact OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hw)

lemma sphereCoord_infty_sphereInv (w : ℂ) : sphereCoord ∞ (sphereInv w) = w := by
  by_cases hw : w = 0
  · simp [sphereInv, hw, sphereCoord]
  · simp [sphereInv, hw]

/-- **The chart `z ↦ 1 / z` of `ℙ¹(ℂ)` at `∞`**, on `ℙ¹(ℂ) ∖ D̄(0, R)`, onto `D(0, 1 / R)`. -/
def inftyChart (R : ℝ) (hR : 0 < R) : inftyNhd R ≃ₜ ball (0 : ℂ) R⁻¹ where
  toFun z := ⟨sphereCoord ∞ z, by
    obtain ⟨z, hz⟩ := z
    induction z using OnePoint.rec with
    | infty => simpa [sphereCoord] using inv_pos.mpr hR
    | coe w =>
      have hw := coe_mem_inftyNhd.mp hz
      rw [sphereCoord_infty_coe, mem_ball_zero_iff, norm_inv]
      exact inv_strictAnti₀ hR hw⟩
  invFun w := ⟨sphereInv w, by
    by_cases hw : (w : ℂ) = 0
    · simp [sphereInv, hw, infty_mem_inftyNhd]
    · simp only [sphereInv, hw, ↓reduceIte, coe_mem_inftyNhd, norm_inv]
      have h := mem_ball_zero_iff.mp w.2
      rw [lt_inv_comm₀ hR (norm_pos_iff.mpr hw)]
      exact h⟩
  left_inv z := by
    obtain ⟨z, hz⟩ := z
    induction z using OnePoint.rec with
    | infty => ext; simp [sphereInv, sphereCoord]
    | coe w =>
      have hw : w ≠ 0 := by
        rintro rfl
        simpa using (coe_mem_inftyNhd.mp hz).trans_le' hR.le
      ext
      simp [sphereInv, hw]
  right_inv w := Subtype.ext (sphereCoord_infty_sphereInv w)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    rw [continuous_iff_continuousAt]
    rintro ⟨z, hz⟩
    refine (continuousAt_sphereCoord_infty ?_).comp continuous_subtype_val.continuousAt
    rintro rfl
    exact absurd ((coe_mem_inftyNhd.mp hz).trans_le (by simp)) (not_lt.mpr hR.le)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_sphereInv.comp continuous_subtype_val

lemma inftyChart_apply (R : ℝ) (hR : 0 < R) (z : inftyNhd R) :
    (inftyChart R hR z : ℂ) = sphereCoord ∞ z :=
  rfl


/-- The conclusion of `exists_presentation_fundamentalGroup_compl` at the base point `x`. -/
private def HasSpherePresentation (T : Finset (OnePoint ℂ))
    (x : ((↑T : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ))) : Prop :=
  ∃ (m : ℕ) (e : Fin m ≃ T) (σ : Fin m → FundamentalGroup ((↑T : Set (OnePoint ℂ))ᶜ : Set _) x),
    (∀ i, IsLoopAroundAt Subtype.val (e i : OnePoint ℂ) (σ i)) ∧
    ∃ h : ∀ r ∈ ({FreeGroup.prodRelator m} : Set (FreeGroup (Fin m))), FreeGroup.lift σ r = 1,
      Function.Bijective (PresentedGroup.toGroup h)

private lemma HasSpherePresentation.transport {T : Finset (OnePoint ℂ)}
    {x x' : ((↑T : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ))} (p : Path x x')
    (h : HasSpherePresentation T x) : HasSpherePresentation T x' := by
  obtain ⟨m, e, σ, hσ, h, hb⟩ := h
  obtain ⟨h', hb'⟩ :=
    PresentedGroup.exists_bijective_toGroup_mulEquiv hb (fundamentalGroupMulEquivOfPath p)
  exact ⟨m, e, _, fun i ↦ IsLoopAround.conj p (hσ i), h', hb'⟩

/-- **`π₁` of the Riemann sphere minus finitely many points.** For every finite `T ⊆ ℙ¹(ℂ)` and
every base point `x` of `ℙ¹(ℂ) ∖ T`, there are an enumeration `e : Fin m ≃ T` (`m = |T|`) and
loops `σ₁, …, σ_m` (`σᵢ` around `e i`, `Complex.IsLoopAroundAt`) such that
`⟨x₁, …, x_m | x₁ ⋯ x_m⟩ → π₁(ℙ¹(ℂ) ∖ T, x)`, `xᵢ ↦ σᵢ`, is well defined and bijective. The order
of the points is the one produced by the proof. For `T = ∅` (`m = 0`) this says that `ℙ¹(ℂ)` is
simply connected. -/
theorem exists_presentation_fundamentalGroup_compl (T : Finset (OnePoint ℂ))
    (x : ((↑T : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ))) :
    ∃ (m : ℕ) (e : Fin m ≃ T) (σ : Fin m → FundamentalGroup ((↑T : Set (OnePoint ℂ))ᶜ : Set _) x),
      (∀ i, IsLoopAroundAt Subtype.val (e i : OnePoint ℂ) (σ i)) ∧
      ∃ h : ∀ r ∈ ({FreeGroup.prodRelator m} : Set (FreeGroup (Fin m))), FreeGroup.lift σ r = 1,
        Function.Bijective (PresentedGroup.toGroup h) := by
  by_cases hT : (∞ : OnePoint ℂ) ∈ T
  · exact exists_presentation_fundamentalGroup_compl_of_infty_mem T hT x
  classical
  -- `ℙ¹(ℂ) ∖ (T ∪ {∞}) ≅ ℂ ∖ S`
  set T' := insert (∞ : OnePoint ℂ) T with hT'
  have hinfT : (∞ : OnePoint ℂ) ∈ T' := Finset.mem_insert_self _ _
  obtain ⟨j, hj, hjr, hjy⟩ := exists_coord_of_infty_mem T' hinfT
  set S := finitePart T'
  have hST (a : ℂ) : a ∈ S ↔ (a : OnePoint ℂ) ∈ T := by
    rw [mem_finitePart, Finset.mem_insert, or_iff_right (OnePoint.coe_ne_infty a)]
  -- the inclusion `ℙ¹(ℂ) ∖ (T ∪ {∞}) → ℙ¹(ℂ) ∖ T`, onto the complement of `q = ∞`
  have hTT' : ((↑T' : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ)) ⊆ (↑T : Set (OnePoint ℂ))ᶜ :=
    compl_subset_compl.mpr (Finset.coe_subset.mpr (Finset.subset_insert _ _))
  let ι : C(((↑T' : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ)), ((↑T : Set (OnePoint ℂ))ᶜ : Set _)) :=
    ⟨Set.inclusion hTT', continuous_inclusion hTT'⟩
  have hι : IsEmbedding ι := IsEmbedding.inclusion hTT'
  set q : ((↑T : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ)) := ⟨∞, hT⟩
  have hιr : range ι = {q}ᶜ := by
    ext y
    change y ∈ range (Set.inclusion hTT') ↔ y ≠ q
    rw [Set.range_inclusion, mem_ofPred_eq, Ne, Subtype.ext_iff, mem_compl_iff, Finset.mem_coe,
      Finset.mem_insert, not_or]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, y.2⟩⟩
  -- the chart at `∞`
  set R : ℝ := 1 + ∑ t ∈ S, ‖t‖
  have hR : 0 < R := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  have hsub : inftyNhd R ⊆ (↑T : Set (OnePoint ℂ))ᶜ := by
    intro z hz hzT
    induction z using OnePoint.rec with
    | infty => exact hT hzT
    | coe a =>
      have h1 := coe_mem_inftyNhd.mp hz
      have h2 : ‖a‖ ≤ ∑ t ∈ S, ‖t‖ :=
        Finset.single_le_sum (f := fun t ↦ ‖t‖) (fun _ _ ↦ norm_nonneg _) ((hST a).mpr hzT)
      linarith
  set W : Set ((↑T : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ)) := Subtype.val ⁻¹' inftyNhd R
  have hW : IsOpen W := (isOpen_inftyNhd R).preimage continuous_subtype_val
  have hqW : q ∈ W := infty_mem_inftyNhd R
  let φ : W ≃ₜ ball (0 : ℂ) R⁻¹ := (Homeomorph.preimageSubtypeVal hsub).trans (inftyChart R hR)
  have hφ : (φ ⟨q, hqW⟩ : ℂ) = 0 := rfl
  have hφy (y : ((↑T : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ))) (hy : y ∈ W) :
      chartCoord φ y = sphereCoord ∞ y := by
    rw [chartCoord_of_mem φ hy]
    rfl
  -- `ℙ¹(ℂ) ∖ (T ∪ {∞})` is path-connected and nonempty
  have hne : ((↑S : Set ℂ)ᶜ).Nonempty := S.finite_toSet.infinite_compl.nonempty
  have : Nonempty ((↑T' : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ)) := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨y, -⟩ := hjr ▸ ha
    exact ⟨y⟩
  have : PathConnectedSpace ((↑T' : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ)) :=
    pathConnectedSpace_of_isOpenEmbedding_of_range_eq_diff (C := univ) convex_univ isOpen_univ
      (subset_univ _) hj (by rw [hjr, compl_eq_univ_sdiff])
  have : PathConnectedSpace ((↑T : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ)) :=
    pathConnectedSpace_of_range_eq_compl_singleton ι hιr hqW φ hφ
  -- the presentation at a base point `ι x'`
  have key (x' : ((↑T' : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ))) :
      HasSpherePresentation T (ι x') := by
    obtain ⟨e₀, σ', hσ', hinf, h', hb'⟩ := exists_presentation_of_isOpenEmbedding hj hjr x'
    have hlast : IsLoopAround (fun y ↦ chartCoord φ (ι y)) 0 (σ' (Fin.last _)) := by
      refine hinf.congr (inv_pos.mpr hR) fun y hy ↦ ?_
      have hjy0 : j y ≠ 0 := fun h ↦ hy.2 (by rw [h, inv_zero]; rfl)
      have hlt : R < ‖j y‖ := by
        have := mem_ball_zero_iff.mp hy.1
        rw [norm_inv] at this
        exact (inv_lt_inv₀ (norm_pos_iff.mpr hjy0) hR).mp this
      have hyW : ι y ∈ W := by
        change ((y : OnePoint ℂ)) ∈ inftyNhd R
        rw [hjy y]
        exact coe_mem_inftyNhd.mpr hlt
      rw [hφy _ hyW]
      change sphereCoord ∞ (y : OnePoint ℂ) = _
      rw [hjy y, sphereCoord_infty_coe]
    obtain ⟨h'', hb''⟩ := FreeGroup.bijective_toGroup_prodRelator_of_kill_last hb' (map ι x')
      (surjective_map_of_range_eq_compl_singleton hι hιr hW hqW φ hφ x')
      (map_eq_one_of_isLoopAround_chartCoord φ ι hlast)
      fun f hf ↦ (existsUnique_hom_of_range_eq_compl_singleton hι hιr hW hqW φ hφ x' hlast f
        hf).exists
    -- the enumeration of `T`
    let g : Fin S.card → T := fun i ↦ ⟨((e₀ i : ℂ) : OnePoint ℂ), (hST _).mp (e₀ i).2⟩
    have hg : Function.Bijective g := by
      refine ⟨fun a b hab ↦ e₀.injective (Subtype.ext (OnePoint.coe_injective
        (congrArg Subtype.val hab))), fun t ↦ ?_⟩
      obtain ⟨t, ht⟩ := t
      induction t using OnePoint.rec with
      | infty => exact absurd ht hT
      | coe a =>
        obtain ⟨i, hi⟩ := e₀.surjective ⟨a, (hST a).mpr ht⟩
        exact ⟨i, by simp [g, hi]⟩
    refine ⟨S.card, Equiv.ofBijective g hg, _, fun i ↦ ?_, h'', hb''⟩
    change IsLoopAround (fun y : ((↑T : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ)) ↦
      sphereCoord ((e₀ i : ℂ) : OnePoint ℂ) y) 0 (map ι x' (σ' i.castSucc))
    refine (hσ' i).sub.map ι fun y ↦ ?_
    change sphereCoord ((e₀ i : ℂ) : OnePoint ℂ) (y : OnePoint ℂ) = _
    rw [hjy y, sphereCoord_coe_coe]
  -- transport to `x`
  obtain ⟨x'⟩ := ‹Nonempty ((↑T' : Set (OnePoint ℂ))ᶜ : Set (OnePoint ℂ))›
  exact (key x').transport (PathConnectedSpace.somePath _ x)

end Complex
