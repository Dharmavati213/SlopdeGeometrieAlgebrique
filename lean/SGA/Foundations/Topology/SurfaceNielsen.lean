/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.Commutator
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Data.List.Rotate

/-!
# Free families, Nielsen moves and surface bases

We work with finite families of elements of a group `G`, given as lists.

* `Nielsen.IsFreeList l`: the elements of `l` are distinct and freely generate a subgroup;
  `Nielsen.spanOf l` is that subgroup.
* `Nielsen.IsFreeList.nielsen`: a *Nielsen move* `a ↦ y a^{±1} z`, with `y`, `z` in the span of
  the other elements, keeps a free family free and does not change its span.
* `Nielsen.Interchangeable l base`: `l` and `base` span the same subgroup and `l` may replace
  `base` in every free family `base ++ m`. This is how a free basis of a subgroup is propagated
  through an induction without naming the subgroup.
* `Nielsen.IsSurfaceBasis base hs cs`: *handles* `hs = [(a₁, b₁), …]` and *boundary elements*
  `cs = [c₁, …, cₙ]` with `∏ᵢ [aᵢ, bᵢ] ∏ⱼ cⱼ = 1`, such that the `aᵢ, bᵢ` and all but one of the
  `cⱼ` are interchangeable with `base`; `Nielsen.IsSurfaceBasis.forall` shows that any `cⱼ` can be
  the one left out.
* `Nielsen.IsSurfaceBasis.split` and `Nielsen.IsSurfaceBasis.handle`: the two moves of the
  classification of surfaces on the level of groups: adding a free generator `e` either splits a
  boundary element `c = s (u v) s⁻¹` into `s (u e) s⁻¹` and `s (e⁻¹ v) s⁻¹`, or merges two
  boundary elements `s U s⁻¹` and `r V r⁻¹` into one conjugate of `ε U ε⁻¹ V` (`ε = e^{±1}`)
  and a new handle.

These are used in `Foundations/Topology/SurfaceOneVertex.lean` to compute the fundamental group of
a punctured compact orientable surface from a one-vertex ribbon graph.

## References

* [W. Magnus, A. Karrass, D. Solitar, *Combinatorial Group Theory*, §3.2 (Nielsen
  transformations)][magnus1966]
* [W. S. Massey, *Algebraic Topology: An Introduction*, Chapter 1][massey1967]
-/

open Function

namespace Nielsen

variable {G : Type*} [Group G]

/-- The subgroup spanned by the elements of a list. -/
def spanOf (l : List G) : Subgroup G := Subgroup.closure {a | a ∈ l}

/-- The elements of `l` are distinct and freely generate a subgroup. -/
def IsFreeList (l : List G) : Prop :=
  l.Nodup ∧ Injective (FreeGroup.lift ((↑) : {a | a ∈ l} → G))

lemma mem_spanOf {l : List G} {a : G} (h : a ∈ l) : a ∈ spanOf l :=
  Subgroup.subset_closure h

lemma spanOf_mono {l l' : List G} (h : ∀ a ∈ l, a ∈ l') : spanOf l ≤ spanOf l' :=
  Subgroup.closure_mono fun a ha ↦ h a ha

lemma spanOf_perm {l l' : List G} (h : l.Perm l') : spanOf l = spanOf l' :=
  le_antisymm (spanOf_mono fun _ ha ↦ h.mem_iff.mp ha) (spanOf_mono fun _ ha ↦ h.mem_iff.mpr ha)

lemma spanOf_le {l : List G} {K : Subgroup G} : spanOf l ≤ K ↔ ∀ a ∈ l, a ∈ K :=
  Subgroup.closure_le K

lemma IsFreeList.perm {l l' : List G} (h : IsFreeList l) (hp : l.Perm l') : IsFreeList l' := by
  have hs : {a | a ∈ l} = {a | a ∈ l'} := Set.ext fun _ ↦ hp.mem_iff
  refine ⟨hp.nodup_iff.mp h.1, ?_⟩
  have := h.2
  rw [hs] at this
  exact this

lemma IsFreeList.sublist {l l' : List G} (h : IsFreeList l') (hl : l.Sublist l') :
    IsFreeList l := by
  refine ⟨h.1.sublist hl, ?_⟩
  let inc : {a | a ∈ l} → {a | a ∈ l'} := fun a ↦ ⟨a, hl.subset a.2⟩
  have hinc : Injective inc := fun a b h ↦ by simpa [inc, Subtype.ext_iff] using h
  have : FreeGroup.lift ((↑) : {a | a ∈ l} → G) =
      (FreeGroup.lift ((↑) : {a | a ∈ l'} → G)).comp (FreeGroup.map inc) :=
    FreeGroup.ext_hom _ _ fun a ↦ by simp [inc]
  rw [this, MonoidHom.coe_comp]
  exact h.2.comp (FreeGroup.map_injective hinc)

/-- In a free family `a :: k`, the element `a` is not in the span of `k`. -/
lemma IsFreeList.not_mem_spanOf {a : G} {k : List G} (h : IsFreeList (a :: k)) :
    a ∉ spanOf k := by
  classical
  intro ha
  have hak : a ∉ k := (List.nodup_cons.mp h.1).1
  rw [spanOf, FreeGroup.closure_eq_range] at ha
  obtain ⟨w, hw⟩ := ha
  let inc : {b | b ∈ k} → {b | b ∈ a :: k} := fun b ↦ ⟨b, List.mem_cons_of_mem _ b.2⟩
  have hcomp : (FreeGroup.lift ((↑) : {b | b ∈ a :: k} → G)).comp (FreeGroup.map inc) =
      FreeGroup.lift ((↑) : {b | b ∈ k} → G) := FreeGroup.ext_hom _ _ fun b ↦ by simp [inc]
  have heq : FreeGroup.map inc w = FreeGroup.of ⟨a, List.mem_cons_self ..⟩ := by
    apply h.2
    rw [← MonoidHom.comp_apply, hcomp, hw]
    simp
  let χ : FreeGroup {b | b ∈ a :: k} →* Multiplicative ℤ :=
    FreeGroup.lift fun b ↦ if (b : G) = a then Multiplicative.ofAdd 1 else 1
  have h1 : χ (FreeGroup.map inc w) = 1 := by
    have : χ.comp (FreeGroup.map inc) = 1 := FreeGroup.ext_hom _ _ fun b ↦ by
      have hb : (b : G) ≠ a := fun hb ↦ hak (hb ▸ b.2)
      simp [χ, inc, hb]
    rw [← MonoidHom.comp_apply, this, MonoidHom.one_apply]
  rw [heq] at h1
  simp [χ] at h1

/-- Nielsen moves do not change the span. -/
lemma spanOf_nielsen_cons {a y z : G} {k : List G} {ε : ℤ} (hy : y ∈ spanOf k)
    (hz : z ∈ spanOf k) (hε : ε * ε = 1) :
    spanOf ((y * a ^ ε * z) :: k) = spanOf (a :: k) := by
  set a' := y * a ^ ε * z with ha'
  have hka : spanOf k ≤ spanOf (a :: k) := spanOf_mono fun b hb ↦ List.mem_cons_of_mem _ hb
  have haa : a = (y⁻¹ * a' * z⁻¹) ^ ε := by
    rw [ha', show y⁻¹ * (y * a ^ ε * z) * z⁻¹ = a ^ ε by group, ← zpow_mul, hε, zpow_one]
  apply le_antisymm
  · rw [spanOf_le]
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hka hy)
        (Subgroup.zpow_mem _ (mem_spanOf (List.mem_cons_self ..)) _)) (hka hz)
    · exact mem_spanOf (List.mem_cons_of_mem _ hb)
  · rw [spanOf_le]
    intro b hb
    have hk' : spanOf k ≤ spanOf (a' :: k) := spanOf_mono fun b hb ↦ List.mem_cons_of_mem _ hb
    rcases List.mem_cons.mp hb with rfl | hb
    · rw [haa]
      exact Subgroup.zpow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ (hk' hy)) (mem_spanOf (List.mem_cons_self ..)))
        (Subgroup.inv_mem _ (hk' hz))) _
    · exact mem_spanOf (List.mem_cons_of_mem _ hb)

/-- **Nielsen moves.** If `a :: k` is a free family and `y`, `z` lie in the span of `k`, then
`(y * a ^ ε * z) :: k` (`ε = ±1`) is a free family with the same span. -/
theorem IsFreeList.nielsen_cons {a y z : G} {k : List G} {ε : ℤ} (h : IsFreeList (a :: k))
    (hy : y ∈ spanOf k) (hz : z ∈ spanOf k) (hε : ε * ε = 1) :
    IsFreeList ((y * a ^ ε * z) :: k) ∧ spanOf ((y * a ^ ε * z) :: k) = spanOf (a :: k) := by
  classical
  set a' := y * a ^ ε * z with ha'
  have hak : a ∉ k := (List.nodup_cons.mp h.1).1
  have hkk : k.Nodup := (List.nodup_cons.mp h.1).2
  have hka : spanOf k ≤ spanOf (a :: k) := spanOf_mono fun b hb ↦ List.mem_cons_of_mem _ hb
  have haa : a = (y⁻¹ * a' * z⁻¹) ^ ε := by
    rw [ha', show y⁻¹ * (y * a ^ ε * z) * z⁻¹ = a ^ ε by group, ← zpow_mul, hε, zpow_one]
  have hspan : spanOf (a' :: k) = spanOf (a :: k) := spanOf_nielsen_cons hy hz hε
  -- the new element is not in `k`
  have ha'k : a' ∉ k := fun h' ↦ h.not_mem_spanOf (by
    rw [haa]
    exact Subgroup.zpow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy)
      (mem_spanOf h')) (Subgroup.inv_mem _ hz)) _)
  refine ⟨⟨List.nodup_cons.mpr ⟨ha'k, hkk⟩, ?_⟩, hspan⟩
  -- words for `y` and `z` in the letters of `k`
  have hyr : y ∈ (FreeGroup.lift ((↑) : {b | b ∈ k} → G)).range := by
    rwa [← FreeGroup.closure_eq_range]
  have hzr : z ∈ (FreeGroup.lift ((↑) : {b | b ∈ k} → G)).range := by
    rwa [← FreeGroup.closure_eq_range]
  obtain ⟨Y₀, hY₀⟩ := hyr
  obtain ⟨Z₀, hZ₀⟩ := hzr
  let S := {b | b ∈ a :: k}
  let S' := {b | b ∈ a' :: k}
  let inc : {b | b ∈ k} → S := fun b ↦ ⟨b, List.mem_cons_of_mem _ b.2⟩
  let inc' : {b | b ∈ k} → S' := fun b ↦ ⟨b, List.mem_cons_of_mem _ b.2⟩
  have hlinc : (FreeGroup.lift ((↑) : S → G)).comp (FreeGroup.map inc) =
      FreeGroup.lift ((↑) : {b | b ∈ k} → G) := FreeGroup.ext_hom _ _ fun b ↦ by simp [inc]
  have hmem (b : S') (hb : (b : G) ≠ a') : (b : G) ∈ k :=
    (List.mem_cons.mp b.2).resolve_left hb
  let ψ : FreeGroup S' →* FreeGroup S := FreeGroup.lift fun b ↦
    if hb : (b : G) = a' then FreeGroup.map inc Y₀ * FreeGroup.of ⟨a, List.mem_cons_self ..⟩ ^ ε *
      FreeGroup.map inc Z₀
    else FreeGroup.of ⟨b, List.mem_cons_of_mem _ (hmem b hb)⟩
  have hψ : (FreeGroup.lift ((↑) : S → G)).comp ψ = FreeGroup.lift ((↑) : S' → G) := by
    refine FreeGroup.ext_hom _ _ fun b ↦ ?_
    simp only [MonoidHom.comp_apply, ψ, FreeGroup.lift_apply_of]
    split_ifs with hb
    · rw [map_mul, map_mul, ← MonoidHom.comp_apply, hlinc, hY₀, ← MonoidHom.comp_apply, hlinc,
        hZ₀, map_zpow, FreeGroup.lift_apply_of, hb]
    · simp
  have hmem' (b : S) (hb : (b : G) ≠ a) : (b : G) ∈ k :=
    (List.mem_cons.mp b.2).resolve_left hb
  let χ : FreeGroup S →* FreeGroup S' := FreeGroup.lift fun b ↦
    if hb : (b : G) = a then
      ((FreeGroup.map inc' Y₀)⁻¹ * FreeGroup.of ⟨a', List.mem_cons_self ..⟩ *
        (FreeGroup.map inc' Z₀)⁻¹) ^ ε
    else FreeGroup.of ⟨b, List.mem_cons_of_mem _ (hmem' b hb)⟩
  have hχinc : χ.comp (FreeGroup.map inc) = FreeGroup.map inc' := by
    refine FreeGroup.ext_hom _ _ fun b ↦ ?_
    have hb : ((inc b : S) : G) ≠ a := fun hb ↦ hak (hb ▸ b.2)
    simp only [MonoidHom.comp_apply, FreeGroup.map.of, χ, FreeGroup.lift_apply_of, hb,
      ↓reduceDIte]
    rfl
  have hχψ : χ.comp ψ = MonoidHom.id _ := by
    refine FreeGroup.ext_hom _ _ fun b ↦ ?_
    simp only [MonoidHom.comp_apply, ψ, FreeGroup.lift_apply_of, MonoidHom.id_apply]
    split_ifs with hb
    · rw [map_mul, map_mul, ← MonoidHom.comp_apply, hχinc, ← MonoidHom.comp_apply χ, hχinc,
        map_zpow]
      simp only [χ, FreeGroup.lift_apply_of, ↓reduceDIte]
      rw [← zpow_mul, hε, zpow_one]
      have : (⟨a', List.mem_cons_self ..⟩ : S') = b := Subtype.ext hb.symm
      rw [this]
      group
    · have hba : (b : G) ≠ a := fun h' ↦ hak (h' ▸ hmem b hb)
      simp only [χ, FreeGroup.lift_apply_of, hba, ↓reduceDIte]
  have hψinj : Injective ψ := by
    intro u v huv
    have := congrArg χ huv
    rwa [← MonoidHom.comp_apply, hχψ, ← MonoidHom.comp_apply, hχψ] at this
  rw [← hψ, MonoidHom.coe_comp]
  exact h.2.comp hψinj

/-- **Nielsen moves**, up to reordering: if `l ~ a :: k` is a free family and `y`, `z` lie in the
span of `k`, then every reordering `l'` of `(y * a ^ ε * z) :: k` (`ε = ±1`) is a free family with
the same span as `l`. -/
theorem IsFreeList.nielsen {l l' k : List G} {a y z : G} {ε : ℤ} (h : IsFreeList l)
    (hl : l.Perm (a :: k)) (hl' : l'.Perm ((y * a ^ ε * z) :: k)) (hy : y ∈ spanOf k)
    (hz : z ∈ spanOf k) (hε : ε * ε = 1) : IsFreeList l' ∧ spanOf l' = spanOf l := by
  obtain ⟨h1, h2⟩ := (h.perm hl).nielsen_cons hy hz hε
  exact ⟨h1.perm hl'.symm, by rw [spanOf_perm hl', h2, spanOf_perm hl]⟩

/-- `l` may replace `base`: same span, and `l ++ m` is free whenever `base ++ m` is. -/
def Interchangeable (l base : List G) : Prop :=
  spanOf l = spanOf base ∧ ∀ m : List G, IsFreeList (base ++ m) → IsFreeList (l ++ m)

lemma Interchangeable.refl (l : List G) : Interchangeable l l := ⟨rfl, fun _ h ↦ h⟩

lemma Interchangeable.trans {l l' l'' : List G} (h : Interchangeable l l')
    (h' : Interchangeable l' l'') : Interchangeable l l'' :=
  ⟨h.1.trans h'.1, fun m hm ↦ h.2 m (h'.2 m hm)⟩

lemma Interchangeable.perm_left {l l' base : List G} (h : Interchangeable l base)
    (hp : l.Perm l') : Interchangeable l' base :=
  ⟨(spanOf_perm hp).symm.trans h.1, fun m hm ↦ (h.2 m hm).perm (hp.append_right m)⟩

lemma Interchangeable.perm_right {l base base' : List G} (h : Interchangeable l base)
    (hp : base.Perm base') : Interchangeable l base' :=
  ⟨h.1.trans (spanOf_perm hp), fun m hm ↦ h.2 m (hm.perm (hp.symm.append_right m))⟩

/-- A free generator can be added on both sides. -/
lemma Interchangeable.append {l base : List G} (h : Interchangeable l base) (e : List G) :
    Interchangeable (l ++ e) (base ++ e) := by
  refine ⟨?_, fun m hm ↦ ?_⟩
  · apply le_antisymm
    · rw [spanOf_le]
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact spanOf_mono (fun b hb ↦ List.mem_append_left _ hb) (h.1 ▸ mem_spanOf ha)
      · exact mem_spanOf (List.mem_append_right _ ha)
    · rw [spanOf_le]
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact spanOf_mono (fun b hb ↦ List.mem_append_left _ hb) (h.1.symm ▸ mem_spanOf ha)
      · exact mem_spanOf (List.mem_append_right _ ha)
  · rw [List.append_assoc] at hm ⊢
    exact h.2 _ hm

/-- Nielsen moves on an interchangeable family. -/
lemma Interchangeable.nielsen {l l' k base : List G} {a y z : G} {ε : ℤ}
    (h : Interchangeable l base) (hl : l.Perm (a :: k)) (hl' : l'.Perm ((y * a ^ ε * z) :: k))
    (hy : y ∈ spanOf k) (hz : z ∈ spanOf k) (hε : ε * ε = 1) : Interchangeable l' base := by
  have hk (m : List G) : spanOf k ≤ spanOf (k ++ m) :=
    spanOf_mono fun _ hb ↦ List.mem_append_left _ hb
  refine ⟨?_, fun m hm ↦ ?_⟩
  · rw [spanOf_perm hl', spanOf_nielsen_cons hy hz hε, ← spanOf_perm hl, h.1]
  · exact ((h.2 m hm).nielsen (hl.append_right m) (hl'.append_right m) (hk m hy) (hk m hz) hε).1


/-- `a` is conjugate to `b` by an element of `K`. -/
def IsConjIn (K : Subgroup G) (a b : G) : Prop := ∃ k ∈ K, a = k * b * k⁻¹

lemma IsConjIn.refl (K : Subgroup G) (a : G) : IsConjIn K a a := ⟨1, K.one_mem, by group⟩

lemma IsConjIn.mono {K K' : Subgroup G} (hKK' : K ≤ K') {a b : G} (h : IsConjIn K a b) :
    IsConjIn K' a b := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k, hKK' hk, rfl⟩

lemma IsConjIn.trans {K : Subgroup G} {a b c : G} (h : IsConjIn K a b) (h' : IsConjIn K b c) :
    IsConjIn K a c := by
  obtain ⟨k, hk, rfl⟩ := h
  obtain ⟨k', hk', rfl⟩ := h'
  exact ⟨k * k', K.mul_mem hk hk', by group⟩

lemma IsConjIn.symm {K : Subgroup G} {a b : G} (h : IsConjIn K a b) : IsConjIn K b a := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k⁻¹, K.inv_mem hk, by group⟩

lemma isConjIn_mul_comm {K : Subgroup G} {a b : G} (ha : a ∈ K) : IsConjIn K (a * b) (b * a) :=
  ⟨a, ha, by group⟩

/-- The product of a list with values in `K` is conjugate in `K` to the product of a rotation. -/
lemma isConjIn_prod_of_isRotated {K : Subgroup G} {l l' : List G} (h : List.IsRotated l l')
    (hK : ∀ a ∈ l, a ∈ K) : IsConjIn K l.prod l'.prod := by
  obtain ⟨n, rfl⟩ := h
  by_cases hl : l = []
  · subst hl
    simpa using IsConjIn.refl K 1
  rw [← List.rotate_mod, List.rotate_eq_drop_append_take
    (Nat.mod_lt _ (List.length_pos_iff.mpr hl)).le]
  conv_lhs => rw [← List.take_append_drop (n % l.length) l]
  rw [List.prod_append, List.prod_append]
  exact isConjIn_mul_comm (list_prod_mem fun a ha ↦ hK a (List.mem_of_mem_take ha))

omit [Group G] in
/-- `l = P ++ a :: S` is a reordering of `a :: (P ++ S)`. -/
lemma perm_cons_of_eq {l k P S : List G} {a : G} (hl : l = P ++ a :: S) (hk : k = P ++ S) :
    l.Perm (a :: k) := by
  subst hl hk
  exact List.perm_middle

/-- The commutator product `∏ᵢ aᵢ bᵢ aᵢ⁻¹ bᵢ⁻¹` of a list of handles `(aᵢ, bᵢ)`. -/
def handleProd (hs : List (G × G)) : G := (hs.map fun p ↦ p.1 * p.2 * p.1⁻¹ * p.2⁻¹).prod

/-- The elements `a₁, b₁, a₂, b₂, …` of a list of handles. -/
def handleList (hs : List (G × G)) : List G := hs.flatMap fun p ↦ [p.1, p.2]

lemma handleProd_append (hs hs' : List (G × G)) :
    handleProd (hs ++ hs') = handleProd hs * handleProd hs' := by
  simp [handleProd]

lemma handleProd_mem_spanOf (hs : List (G × G)) : handleProd hs ∈ spanOf (handleList hs) := by
  refine list_prod_mem fun a ha ↦ ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  have h1 : p.1 ∈ handleList hs := List.mem_flatMap.mpr ⟨p, hp, by simp⟩
  have h2 : p.2 ∈ handleList hs := List.mem_flatMap.mpr ⟨p, hp, by simp⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_spanOf h1)
    (mem_spanOf h2)) (Subgroup.inv_mem _ (mem_spanOf h1))) (Subgroup.inv_mem _ (mem_spanOf h2))

/-- **Surface basis.** Handles `hs = [(a₁, b₁), …, (a_g, b_g)]` and boundary elements
`cs = [c₁, …, cₙ]` with `∏ᵢ [aᵢ, bᵢ] ∏ⱼ cⱼ = 1`, such that the `aᵢ, bᵢ` together with all
`cⱼ` but one are interchangeable with `base` (`Interchangeable`). If `base` is a free basis of a
group, then the handles and the boundary elements present it with the single relation
`∏ᵢ [aᵢ, bᵢ] ∏ⱼ cⱼ = 1`. -/
def IsSurfaceBasis (base : List G) (hs : List (G × G)) (cs : List G) : Prop :=
  handleProd hs * cs.prod = 1 ∧
    ∃ A c B, cs = A ++ c :: B ∧ Interchangeable (handleList hs ++ (A ++ B)) base

/-- In a surface basis, any boundary element can be the one left out. -/
theorem IsSurfaceBasis.forall {base : List G} {hs : List (G × G)} {cs : List G}
    (h : IsSurfaceBasis base hs cs) {A : List G} {c : G} {B : List G} (hcs : cs = A ++ c :: B) :
    Interchangeable (handleList hs ++ (A ++ B)) base := by
  obtain ⟨hrel, A₀, c₀, B₀, h₀, hI⟩ := h
  set H := handleList hs
  set Hp := handleProd hs
  have hHp : Hp ∈ spanOf H := handleProd_mem_spanOf hs
  rw [h₀] at hcs
  rcases List.append_eq_append_iff.mp hcs with ⟨as, hA, has⟩ | ⟨bs, hA, hbs⟩
  · obtain _ | ⟨a₁, as'⟩ := as
    · simp only [List.nil_append, List.cons.injEq] at has
      obtain ⟨rfl, rfl⟩ := has
      simp only [List.append_nil] at hA
      subst hA
      exact hI
    · simp only [List.cons_append, List.cons.injEq] at has
      obtain ⟨rfl, rfl⟩ := has
      subst hA
      -- `cs = A₀ ++ c₀ :: as' ++ c :: B`: replace `c` by `c₀`
      rw [h₀] at hrel
      simp only [List.prod_append, List.prod_cons] at hrel
      have hc₀ : c₀ = ((Hp * A₀.prod)⁻¹ * B.prod⁻¹) * c ^ (-1 : ℤ) * as'.prod⁻¹ := by
        rw [zpow_neg_one]
        calc c₀ = (Hp * A₀.prod)⁻¹ * (Hp * (A₀.prod * (c₀ * (as'.prod * (c * B.prod))))) *
              (as'.prod * (c * B.prod))⁻¹ := by group
          _ = _ := by rw [hrel]; group
      set k := H ++ (A₀ ++ (as' ++ B))
      have hk : ∀ l : List G, (∀ a ∈ l, a ∈ k) → l.prod ∈ spanOf k := fun l hl ↦
        list_prod_mem fun a ha ↦ mem_spanOf (hl a ha)
      refine hI.nielsen (a := c) (k := k) (ε := -1) (y := (Hp * A₀.prod)⁻¹ * B.prod⁻¹)
        (z := as'.prod⁻¹) ?_ ?_ ?_ ?_ (by norm_num)
      · exact perm_cons_of_eq (P := H ++ A₀ ++ as') (S := B) (by simp) (by simp [k])
      · rw [← hc₀]
        exact perm_cons_of_eq (P := H ++ A₀) (S := as' ++ B) (by simp) (by simp [k])
      · refine Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
          (spanOf_mono (fun a ha ↦ List.mem_append_left _ ha) hHp) (hk _ ?_)))
          (Subgroup.inv_mem _ (hk _ ?_)) <;> intro a ha <;> simp [k, ha]
      · exact Subgroup.inv_mem _ (hk _ fun a ha ↦ by simp [k, ha])
  · obtain _ | ⟨b₁, bs'⟩ := bs
    · simp only [List.nil_append, List.cons.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      simp only [List.append_nil] at hA
      subst hA
      exact hI
    · simp only [List.cons_append, List.cons.injEq] at hbs
      obtain ⟨rfl, rfl⟩ := hbs
      subst hA
      -- `cs = A ++ c :: bs' ++ c₀ :: B₀`: replace `c` by `c₀`
      rw [h₀] at hrel
      simp only [List.append_assoc, List.cons_append, List.prod_append, List.prod_cons,
        List.prod_cons] at hrel
      have hc₀ : c₀ = bs'.prod⁻¹ * c ^ (-1 : ℤ) * ((Hp * A.prod)⁻¹ * B₀.prod⁻¹) := by
        rw [zpow_neg_one]
        calc c₀ = (Hp * (A.prod * (c * bs'.prod)))⁻¹ *
              (Hp * (A.prod * (c * (bs'.prod * (c₀ * B₀.prod))))) * B₀.prod⁻¹ := by group
          _ = _ := by rw [hrel]; group
      set k := H ++ (A ++ (bs' ++ B₀))
      have hk : ∀ l : List G, (∀ a ∈ l, a ∈ k) → l.prod ∈ spanOf k := fun l hl ↦
        list_prod_mem fun a ha ↦ mem_spanOf (hl a ha)
      refine hI.nielsen (a := c) (k := k) (ε := -1) (y := bs'.prod⁻¹)
        (z := (Hp * A.prod)⁻¹ * B₀.prod⁻¹) ?_ ?_ ?_ ?_ (by norm_num)
      · exact perm_cons_of_eq (P := H ++ A) (S := bs' ++ B₀) (by simp) (by simp [k])
      · rw [← hc₀]
        exact perm_cons_of_eq (P := H ++ A ++ bs') (S := B₀) (by simp) (by simp [k])
      · exact Subgroup.inv_mem _ (hk _ fun a ha ↦ by simp [k, ha])
      · refine Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
          (spanOf_mono (fun a ha ↦ List.mem_append_left _ ha) hHp) (hk _ ?_)))
          (Subgroup.inv_mem _ (hk _ ?_)) <;> intro a ha <;> simp [k, ha]


/-- **Splitting a boundary element.** Let `(hs, X ++ c :: Y)` be a surface basis relative to
`base` with `c = s (u v) s⁻¹`, `s, u` in the span of `base`. Adding a new generator `e`, the
boundary element `c` splits into `s (u e) s⁻¹` and `s (e⁻¹ v) s⁻¹`: this is a surface basis
relative to `e :: base`. (Topologically: an edge between two distinct faces.) -/
theorem IsSurfaceBasis.split {base : List G} {hs : List (G × G)} {X Y : List G} {c s u v e : G}
    (h : IsSurfaceBasis base hs (X ++ c :: Y)) (hc : c = s * (u * v) * s⁻¹)
    (hsb : s ∈ spanOf base) (hub : u ∈ spanOf base) :
    IsSurfaceBasis (e :: base) hs (X ++ (s * (u * e) * s⁻¹) :: (s * (e⁻¹ * v) * s⁻¹) :: Y) := by
  refine ⟨?_, X ++ [s * (u * e) * s⁻¹], s * (e⁻¹ * v) * s⁻¹, Y, by simp, ?_⟩
  · have := h.1
    simp only [List.prod_append, List.prod_cons] at this ⊢
    rw [← this, hc]
    group
  · have hI := (h.forall rfl).append [e]
    set k := handleList hs ++ (X ++ Y)
    have hk : spanOf k = spanOf base := (h.forall rfl).1
    refine (hI.nielsen (a := e) (k := k) (ε := 1) (y := s * u) (z := s⁻¹)
      (perm_cons_of_eq (P := k) (S := []) (by simp) (by simp)) ?_ ?_ ?_ (by norm_num)).perm_right
        (perm_cons_of_eq (P := base) (S := []) (by simp) (by simp))
    · exact perm_cons_of_eq (P := handleList hs ++ X) (S := Y) (by simp [mul_assoc])
        (by simp [k])
    · rw [hk]
      exact Subgroup.mul_mem _ hsb hub
    · rw [hk]
      exact Subgroup.inv_mem _ hsb

/-- **Creating a handle.** Let `(hs, X ++ s U s⁻¹ :: Y ++ r V r⁻¹ :: Z)` be a surface basis
relative to `base`, with `s, r, V` in the span of `base`, and let `ε = ±1`. Adding a new
generator `e`, the two boundary elements merge into the single boundary element
`r' (V e^ε U e^{-ε}) r'⁻¹` (`r' = (∏ Y) r`) and a new handle appears: this is a surface basis
relative to `e :: base`. (Topologically: an edge with the same face on both sides.) -/
theorem IsSurfaceBasis.handle {base : List G} {hs : List (G × G)} {X Y Z : List G}
    {s r U V e : G} {ε : ℤ} (hε : ε * ε = 1)
    (h : IsSurfaceBasis base hs (X ++ (s * U * s⁻¹) :: (Y ++ (r * V * r⁻¹) :: Z)))
    (hsb : s ∈ spanOf base) (hrb : r ∈ spanOf base) (hVb : V ∈ spanOf base) :
    IsSurfaceBasis (e :: base)
      (hs ++ [(X.prod * (s * U * s⁻¹) * X.prod⁻¹,
        X.prod * (Y.prod * r * V * e ^ ε * s⁻¹) * X.prod⁻¹)])
      (X ++ (Y.prod * r * (V * e ^ ε * U * e ^ (-ε)) * (Y.prod * r)⁻¹) :: (Y ++ Z)) := by
  refine ⟨?_, X, _, Y ++ Z, rfl, ?_⟩
  · have := h.1
    simp only [handleProd_append, List.prod_append, List.prod_cons] at this ⊢
    rw [← this]
    simp only [handleProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    group
  · -- old basis: `c_V` left out
    have hI := h.forall (A := X ++ (s * U * s⁻¹) :: Y) (c := r * V * r⁻¹) (B := Z) (by simp)
    set k₁ := handleList hs ++ (X ++ (s * U * s⁻¹) :: Y ++ Z)
    have hk₁ : spanOf k₁ = spanOf base := hI.1
    have hX : X.prod ∈ spanOf base := by
      rw [← hk₁]
      exact list_prod_mem fun a ha ↦ mem_spanOf (by simp [k₁, ha])
    have hY : Y.prod ∈ spanOf base := by
      rw [← hk₁]
      exact list_prod_mem fun a ha ↦ mem_spanOf (by simp [k₁, ha])
    -- first move: `e ↦ P (Q r V) e^ε (s⁻¹ P⁻¹)`
    set B' := X.prod * (Y.prod * r * V) * e ^ ε * (s⁻¹ * X.prod⁻¹)
    have hB' : B' = X.prod * (Y.prod * r * V * e ^ ε * s⁻¹) * X.prod⁻¹ := by
      simp only [B']
      group
    have hI₂ := (hI.append [e]).nielsen (a := e) (k := k₁) (ε := ε)
      (y := X.prod * (Y.prod * r * V)) (z := s⁻¹ * X.prod⁻¹) (l' := k₁ ++ [B'])
      (perm_cons_of_eq (P := k₁) (S := []) (by simp) (by simp))
      (perm_cons_of_eq (P := k₁) (S := []) (by simp [B']) (by simp))
      (by
        rw [hk₁]
        exact Subgroup.mul_mem _ hX (Subgroup.mul_mem _ (Subgroup.mul_mem _ hY hrb) hVb))
      (by rw [hk₁]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hsb) (Subgroup.inv_mem _ hX)) hε
    -- second move: `s U s⁻¹ ↦ P (s U s⁻¹) P⁻¹`
    set k₂ := handleList hs ++ X ++ (Y ++ Z ++ [B'])
    have hP : X.prod ∈ spanOf k₂ := list_prod_mem fun a ha ↦ mem_spanOf (by simp [k₂, ha])
    refine (hI₂.nielsen (a := s * U * s⁻¹) (k := k₂) (ε := 1) (y := X.prod) (z := X.prod⁻¹)
      (perm_cons_of_eq (P := handleList hs ++ X) (S := Y ++ Z ++ [B']) (by simp [k₁])
        (by simp [k₂])) ?_ hP (Subgroup.inv_mem _ hP) (by norm_num)).perm_right
      (perm_cons_of_eq (P := base) (S := []) (by simp) (by simp))
    have h1 : handleList (hs ++ [(X.prod * (s * U * s⁻¹) * X.prod⁻¹,
        X.prod * (Y.prod * r * V * e ^ ε * s⁻¹) * X.prod⁻¹)]) ++ (X ++ (Y ++ Z)) =
        handleList hs ++ (X.prod * (s * U * s⁻¹) ^ (1 : ℤ) * X.prod⁻¹) ::
          (B' :: (X ++ (Y ++ Z))) := by
      simp [handleList, hB']
    rw [h1]
    refine (List.perm_middle).trans (List.Perm.cons _ ?_)
    have h2 : (handleList hs ++ B' :: (X ++ (Y ++ Z))).Perm
        (B' :: (handleList hs ++ X ++ (Y ++ Z))) :=
      perm_cons_of_eq (P := handleList hs) (S := X ++ (Y ++ Z)) rfl (by simp)
    have h3 : k₂.Perm (B' :: (handleList hs ++ X ++ (Y ++ Z))) :=
      perm_cons_of_eq (P := handleList hs ++ X ++ (Y ++ Z)) (S := []) (by simp [k₂]) (by simp)
    exact h2.trans h3.symm

end Nielsen
