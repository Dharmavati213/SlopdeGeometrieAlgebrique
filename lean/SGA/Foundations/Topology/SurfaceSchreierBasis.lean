/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.SurfaceSchreierFree

/-!
# Surface bases of the stabilizers of a free group acting on a finite set

Let `F` be free on `σ₀, …, σₙ` and put `σ_{n+1} = (σ₀ ⋯ σₙ)⁻¹` (`Ribbon.Schreier.extGen`), so
that `F = ⟨σ₀, …, σ_{n+1} | σ₀ ⋯ σ_{n+1}⟩` is the fundamental group of the sphere minus `n + 2`
points. For a transitive action of `F` on a finite set `Φ` of `d` points (a connected covering of
degree `d`) and `φ₀ ∈ Φ`, the stabilizer `H` of `φ₀` (the fundamental group of the covering) has a
*surface basis* (`Nielsen.IsSurfaceBasis`): handles `(aᵢ, bᵢ)` and boundary elements `cⱼ`, one
for each pair (`j ≤ n + 1`, orbit of `σⱼ` on `Φ`), with `∏ [aᵢ, bᵢ] ∏ cⱼ = 1`, such that the
`aᵢ, bᵢ` and all `cⱼ` but one freely generate `H`; each `cⱼ` is conjugate in `H` to
`g⁻¹ σⱼ ^ e g`, where `g • φ₀` lies in the orbit and `e` is its length; and
`2g + #{boundary elements} = d n + 2` (`Ribbon.Schreier.exists_surfaceBasis_stabilizer`).

This is the algebraic core of the presentation of the fundamental group of a compact Riemann
surface minus finitely many points, seen as a branched covering of the sphere (Riemann–Hurwitz:
`2 - 2g = 2d - ∑ (e - 1)`).

## References

* [W. S. Massey, *Algebraic Topology: An Introduction*, Chapter 1][massey1967]
* [W. Magnus, A. Karrass, D. Solitar, *Combinatorial Group Theory*, §2.3][magnus1966]
-/

open Function Nielsen

/- Membership in lists of edges and darts is decided with the `BEq` instance coming from
`DecidableEq`, as in `Ribbon.IsRibbon.contract_tree`. -/
attribute [local instance 2000] instBEqOfDecidableEq

namespace List

/-- A permutation of a mapped list is the mapped list of a permutation, matched entrywise. -/
theorem exists_perm_forall₂_of_perm_map {α β γ : Type*} (π : α → γ) (g : β → γ) :
    ∀ (L : List α) (D : List β), (L.map π).Perm (D.map g) →
      ∃ D', D'.Perm D ∧ Forall₂ (fun a b ↦ π a = g b) L D'
  | [], D, h => ⟨[], by simpa using h.symm, Forall₂.nil⟩
  | a :: L, D, h => by
    classical
    obtain ⟨b, hb, hab⟩ := List.mem_map.mp (h.subset (List.mem_cons_self ..))
    have hD := List.perm_cons_erase hb
    have h' : (L.map π).Perm ((D.erase b).map g) := by
      have := h.trans (hD.map g)
      rw [List.map_cons, List.map_cons, hab] at this
      exact this.cons_inv
    obtain ⟨D', hD', hF⟩ := exists_perm_forall₂_of_perm_map π g L (D.erase b) h'
    exact ⟨b :: D', ((hD'.cons b).trans hD.symm), Forall₂.cons hab.symm hF⟩

/-- Filtering out the elements of a sublist `S` (without repetitions) shortens a list without
repetitions by the length of `S`. -/
theorem length_filter_not_mem_add {α : Type*} [DecidableEq α] {l S : List α} (hl : l.Nodup)
    (hS : S.Nodup) (hSl : ∀ a ∈ S, a ∈ l) :
    (l.filter fun a ↦ a ∉ S).length + S.length = l.length := by
  have h1 := List.length_eq_length_filter_add (l := l) (fun a ↦ a ∈ S)
  have h2 : (l.filter fun a ↦ a ∈ S).Perm S :=
    (List.perm_ext_iff_of_nodup (hl.filter _) hS).mpr fun a ↦ by simpa using hSl a
  rw [h2.length_eq] at h1
  have h3 : (l.filter fun a ↦ !decide (a ∈ S)) = l.filter fun a ↦ a ∉ S := by
    refine List.filter_congr fun a _ ↦ ?_
    simp
  rw [h3] at h1
  omega

end List

namespace Ribbon.Schreier

variable {F : Type*} [Group F] {Φ : Type*} [MulAction F Φ] {n : ℕ} (σ : Fin (n + 1) → F)

/-- The generators `σ₀, …, σₙ` followed by `σ_{n+1} = (σ₀ ⋯ σₙ)⁻¹`. -/
def extGen : Fin (n + 2) → F := Fin.snoc (α := fun _ ↦ F) σ (tau σ)⁻¹

@[simp] lemma extGen_castSucc (i : Fin (n + 1)) : extGen σ i.castSucc = σ i := by
  simp [extGen]

@[simp] lemma extGen_last : extGen σ (Fin.last (n + 1)) = (tau σ)⁻¹ := by
  simp [extGen]

/-- The data of a face: `(i, ψ)` for the face of `out i ψ` (`i ≤ n`), `(n + 1, ψ)` for the face of
`in n ψ`. -/
def faceData : Dart Φ n → Fin (n + 2) × Φ
  | ((ψ, i), true) => (i.castSucc, ψ)
  | ((w, i), false) => (Fin.last (n + 1), (σ i)⁻¹ • w)

@[simp] lemma faceData_inn (ψ : Φ) : faceData σ (inn σ (Fin.last n) ψ) = (Fin.last (n + 1), ψ) := by
  simp [faceData, inn]

lemma sameOrbit_inv_iff {g : F} {ψ ψ' : Φ} : SameOrbit g⁻¹ ψ ψ' ↔ SameOrbit g ψ ψ' := by
  constructor <;> rintro ⟨k, rfl⟩ <;> exact ⟨-k, by simp⟩

variable [Finite Φ] [DecidableEq Φ]

lemma mem_faceDarts_data {d : Dart Φ n} (hd : d ∈ faceDarts σ) :
    (∃ i, ∃ r ∈ (orbitReps (σ i) : List Φ), d = ((r, i), true) ∧
      faceData σ d = (i.castSucc, r)) ∨
    ∃ r ∈ (orbitReps (tau σ) : List Φ), d = inn σ (Fin.last n) r ∧
      faceData σ d = (Fin.last (n + 1), r) := by
  rcases (mem_faceDarts σ).mp hd with ⟨i, r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · exact Or.inl ⟨i, r, hr, rfl, rfl⟩
  · exact Or.inr ⟨r, hr, rfl, faceData_inn σ r⟩

lemma faceData_injOn {d d' : Dart Φ n} (hd : d ∈ faceDarts σ) (hd' : d' ∈ faceDarts σ)
    (h : faceData σ d = faceData σ d') : d = d' := by
  rcases mem_faceDarts_data σ hd with ⟨i, r, -, rfl, h1⟩ | ⟨r, -, rfl, h1⟩ <;>
    rcases mem_faceDarts_data σ hd' with ⟨i', r', -, rfl, h2⟩ | ⟨r', -, rfl, h2⟩ <;>
    rw [h1, h2] at h <;> simp only [Prod.mk.injEq] at h
  · obtain ⟨h₁, rfl⟩ := h
    rw [Fin.castSucc_inj.mp h₁]
  · exact absurd h.1 (Fin.castSucc_ne_last _)
  · exact absurd h.1.symm (Fin.castSucc_ne_last _)
  · rw [h.2]

lemma existsUnique_faceData (j : Fin (n + 2)) (ψ : Φ) :
    ∃! q, q ∈ (faceDarts σ).map (faceData σ) ∧ q.1 = j ∧ SameOrbit (extGen σ j) q.2 ψ := by
  induction j using Fin.lastCases with
  | last =>
    obtain ⟨r, hr, hrψ⟩ := exists_mem_orbitReps (tau σ) ψ
    refine ⟨(Fin.last (n + 1), r), ⟨List.mem_map.mpr ⟨inn σ (Fin.last n) r,
      (mem_faceDarts σ).mpr (Or.inr ⟨r, hr, rfl⟩), faceData_inn σ r⟩, rfl, ?_⟩, ?_⟩
    · rw [extGen_last, sameOrbit_inv_iff]
      exact hrψ
    · rintro q ⟨hq, hq1, hq2⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      rw [extGen_last, sameOrbit_inv_iff] at hq2
      rcases mem_faceDarts_data σ hd with ⟨i, r', -, -, h1⟩ | ⟨r', hr', -, h1⟩ <;>
        rw [h1] at hq1 hq2 ⊢
      · exact absurd hq1 (Fin.castSucc_ne_last _)
      · rw [eq_of_mem_orbitReps hr' hr (hq2.trans hrψ.symm)]
  | cast i =>
    obtain ⟨r, hr, hrψ⟩ := exists_mem_orbitReps (σ i) ψ
    refine ⟨(i.castSucc, r), ⟨List.mem_map.mpr ⟨((r, i), true),
      (mem_faceDarts σ).mpr (Or.inl ⟨i, r, hr, rfl⟩), rfl⟩, rfl, ?_⟩, ?_⟩
    · rw [extGen_castSucc]
      exact hrψ
    · rintro q ⟨hq, hq1, hq2⟩
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
      rw [extGen_castSucc] at hq2
      rcases mem_faceDarts_data σ hd with ⟨i', r', hr', -, h1⟩ | ⟨r', -, -, h1⟩ <;>
        rw [h1] at hq1 hq2 ⊢
      · obtain rfl := Fin.castSucc_inj.mp hq1
        rw [eq_of_mem_orbitReps hr' hr (hq2.trans hrψ.symm)]
      · exact absurd hq1.symm (Fin.castSucc_ne_last _)

omit [DecidableEq Φ] in
lemma card_eq_length {Φl : List Φ} (hnd : Φl.Nodup) (hall : ∀ ψ, ψ ∈ Φl) :
    Nat.card Φ = Φl.length := by
  classical
  have := Fintype.ofFinite Φ
  rw [Nat.card_eq_fintype_card, ← List.toFinset_card_of_nodup hnd, ← Finset.card_univ]
  congr 1
  exact (Finset.eq_univ_iff_forall.mpr fun ψ ↦ List.mem_toFinset.mpr (hall ψ)).symm

omit [DecidableEq Φ] in
/-- **Surface bases of stabilizers** (the algebraic core of the presentation of `π₁` of a punctured
compact Riemann surface). Let `F` be free on `σ₀, …, σₙ`, acting transitively on the finite set
`Φ`, and `φ₀ ∈ Φ`. Then there are a free basis `base` of the stabilizer `H` of `φ₀`, handles `hs`
and a list `P` of boundary elements `c` with data `(j, ψ)`, such that

* `(hs, P.map fst)` is a surface basis relative to `base` (`Nielsen.IsSurfaceBasis`:
  `∏ [aᵢ, bᵢ] ∏ c = 1`, and the `aᵢ, bᵢ` with all `c` but one may replace `base`);
* each `c` is conjugate in `H` to `g⁻¹ σⱼ ^ e g` with `g • φ₀ = ψ` and `e` the length of the orbit
  of `ψ` under `σⱼ` (`σ_{n+1} = (σ₀ ⋯ σₙ)⁻¹`, `Ribbon.Schreier.extGen`);
* the data `(j, ψ)` are distinct and, for each `j`, meet each orbit of `σⱼ` exactly once;
* `2 #hs + #P = d n + 2`, `d` the number of points of `Φ`. -/
theorem exists_surfaceBasis_stabilizer (hfree : Bijective (FreeGroup.lift σ)) (φ₀ : Φ)
    (htrans : ∀ ψ : Φ, ∃ g : F, g • φ₀ = ψ) :
    ∃ (base : List F) (hs : List (F × F)) (P : List (F × (Fin (n + 2) × Φ))),
      IsFreeList base ∧ spanOf base = MulAction.stabilizer F φ₀ ∧
      IsSurfaceBasis base hs (P.map Prod.fst) ∧
      (∀ p ∈ P, ∃ g : F, g • φ₀ = p.2.2 ∧ IsConjIn (MulAction.stabilizer F φ₀) p.1
        (g⁻¹ * extGen σ p.2.1 ^ MulAction.period (extGen σ p.2.1) p.2.2 * g)) ∧
      (P.map Prod.snd).Nodup ∧
      (∀ j ψ, ∃! q, q ∈ P.map Prod.snd ∧ q.1 = j ∧ SameOrbit (extGen σ j) q.2 ψ) ∧
      2 * hs.length + P.length = Nat.card Φ * n + 2 := by
  classical
  obtain ⟨rest, T, t, hinv, hall⟩ := exists_tree σ (mem_closure_of_bijective σ hfree) φ₀ htrans
  have hinv' := hinv
  obtain ⟨hnd, hT, ht0, htψ, hTn, hlab⟩ := hinv
  have ht : ∀ ψ, t ψ • φ₀ = ψ := fun ψ ↦ htψ ψ (hall ψ)
  set x := edgeLabel σ t with hx
  set φ := facePerm (rot (Φ := Φ) σ) with hφ
  -- the ribbon graph and its spanning tree
  have hrib : IsRibbon (rotList σ φ₀ :: rest.map (rotList σ)) ((faceDarts σ).map (cyc φ)) :=
    isRibbon σ hnd hall
  have hTD : IsTreeDarts (rotList σ φ₀) T (rest.map (rotList σ)) :=
    hT.isTreeDarts σ fun d hd ↦ (mem_rotList σ).mpr (List.mem_singleton.mp hd)
  have hlen : ∀ r ∈ rest.map (rotList σ), 2 ≤ r.length := fun r hr ↦ by
    obtain ⟨ψ, -, rfl⟩ := List.mem_map.mp hr
    exact two_le_length_rotList σ ψ
  have hflat : ∀ d : Dart Φ n, d ∈ (rotList σ φ₀ :: rest.map (rotList σ)).flatten := fun d ↦
    List.mem_flatten.mpr ⟨rotList σ (vtx σ d), by
      rw [← List.map_cons]; exact List.mem_map_of_mem (hall _), (mem_rotList σ).mpr rfl⟩
  -- the edges off the tree
  have hTsub : ∀ e ∈ T.map Prod.fst, e ∈ (φ₀ :: rest) ×ˢ List.finRange (n + 1) := fun e _ ↦
    List.mem_product.mpr ⟨hall _, List.mem_finRange _⟩
  have hNlen : (nonTree (φ₀ :: rest) T).length + T.length = (φ₀ :: rest).length * (n + 1) := by
    have := List.length_filter_not_mem_add (hnd.product (List.nodup_finRange (n + 1))) hTn hTsub
    rw [List.length_map, List.length_product, List.length_finRange] at this
    exact this
  have hTlen : T.length = rest.length := hT.length_eq σ
  have hNpos : (nonTree (φ₀ :: rest) T) ≠ [] := by
    intro h0
    rw [h0, hTlen, List.length_cons] at hNlen
    simp only [List.length_nil, zero_add] at hNlen
    have : (rest.length + 1) * (n + 1) = rest.length + 1 + (rest.length + 1) * n := by ring
    omega
  obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil (nonTree (φ₀ :: rest) T) hNpos
  have hR : ∃ d ∈ (rotList σ φ₀ :: rest.map (rotList σ)).flatten, d.1 ∉ T.map Prod.fst :=
    ⟨(e₀, true), hflat _, by simpa using (List.mem_filter.mp he₀).2⟩
  obtain ⟨R, hRperm, hHSB, -⟩ := hrib.hasSurfaceBasis_of_tree x hTD hlen
    (fun d hd ↦ (hlab d hd).1) hR
  obtain ⟨F', hs, hF', hconj, hsb, hcount⟩ := hHSB
  -- the free basis
  have hRn : R.Nodup := hRperm.nodup_iff.mpr (hrib.nodup.filter _)
  have hedges : (edges R).Perm (nonTree (φ₀ :: rest) T) := by
    refine (List.perm_ext_iff_of_nodup ?_ ((hnd.product (List.nodup_finRange _)).filter _)).mpr
      fun e ↦ ?_
    · refine (hRn.filter _).map_on fun a ha b hb hab ↦ ?_
      obtain ⟨a, c⟩ := a
      obtain ⟨b, c'⟩ := b
      have hc : c = true := by simpa using (List.mem_filter.mp ha).2
      have hc' : c' = true := by simpa using (List.mem_filter.mp hb).2
      simp only at hab
      rw [hab, hc, hc']
    · have hprod : e ∈ (φ₀ :: rest) ×ˢ List.finRange (n + 1) :=
        List.mem_product.mpr ⟨hall _, List.mem_finRange _⟩
      constructor
      · intro he
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
        have hdR := (List.mem_filter.mp hd).1
        have := (List.mem_filter.mp (hRperm.mem_iff.mp hdR)).2
        exact List.mem_filter.mpr ⟨List.mem_product.mpr ⟨hall _, List.mem_finRange _⟩, this⟩
      · intro he
        have h1 := (List.mem_filter.mp he).2
        have hR' : (e, true) ∈ R := hRperm.mem_iff.mpr (List.mem_filter.mpr ⟨hflat _, h1⟩)
        exact List.mem_map.mpr ⟨(e, true), List.mem_filter.mpr ⟨hR', rfl⟩, rfl⟩
  obtain ⟨hfreeN, hspanN⟩ := isFreeList_nonTree hfree hinv' hall ht
  have hbaseperm : ((edges R).map x).Perm ((nonTree (φ₀ :: rest) T).map x) := hedges.map x
  have hspan : spanOf ((edges R).map x) = MulAction.stabilizer F φ₀ := by
    rw [spanOf_perm hbaseperm, hspanN]
  -- the boundary elements and their data
  have hF'' : (F'.map Prod.fst).Perm
      ((faceDarts σ).map fun f ↦ (cyc φ f).filter fun d ↦ d.1 ∉ T.map Prod.fst) := by
    rw [List.map_map] at hF'
    exact hF'
  obtain ⟨D', hD', hF2⟩ := List.exists_perm_forall₂_of_perm_map Prod.fst
    (fun f ↦ (cyc φ f).filter fun d ↦ d.1 ∉ T.map Prod.fst) F' (faceDarts σ) hF''
  obtain ⟨hlenFD, hzip⟩ := List.forall₂_iff_zip.mp hF2
  refine ⟨(edges R).map x, hs, (F'.zip D').map fun q ↦ (q.1.2, faceData σ q.2),
    hfreeN.perm hbaseperm.symm, hspan, ?_, ?_, ?_, ?_, ?_⟩
  · have : ((F'.zip D').map fun q ↦ (q.1.2, faceData σ q.2)).map Prod.fst = F'.map Prod.snd := by
      have e : ((F'.zip D').map fun q ↦ (q.1.2, faceData σ q.2)).map Prod.fst =
          ((F'.zip D').map Prod.fst).map Prod.snd := by
        simp [List.map_map, Function.comp_def]
      rw [e, List.map_fst_zip hlenFD.le]
    rw [this]
    exact hsb
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hq1, hq2⟩ := List.of_mem_zip hq
    have hgq := hzip hq
    have hc := hconj q.1 hq1
    rw [hgq, hspan] at hc
    have hw : word x ((cyc φ q.2).filter fun d ↦ d.1 ∉ T.map Prod.fst) = word x (cyc φ q.2) :=
      word_filter x _ (fun i hi ↦ by
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hi
        exact (hlab d hd).1) _
    rw [hw] at hc
    rcases mem_faceDarts_data σ (hD'.subset hq2) with ⟨i, r, -, hd, hdata⟩ | ⟨r, -, hd, hdata⟩
    · rw [hd, word_cyc_true] at hc
      refine ⟨t r, by rw [hdata]; exact ht r, ?_⟩
      simp only [hdata, extGen_castSucc]
      exact hc
    · rw [hd, word_cyc_inn] at hc
      refine ⟨t r, by rw [hdata]; exact ht r, ?_⟩
      simp only [hdata, extGen_last, MulAction.period_inv]
      exact hc
  · have : ((F'.zip D').map fun q ↦ (q.1.2, faceData σ q.2)).map Prod.snd =
        D'.map (faceData σ) := by
      have e : ((F'.zip D').map fun q ↦ (q.1.2, faceData σ q.2)).map Prod.snd =
          ((F'.zip D').map Prod.snd).map (faceData σ) := by
        simp [List.map_map, Function.comp_def]
      rw [e, List.map_snd_zip hlenFD.ge]
    rw [this]
    refine (hD'.map _).nodup_iff.mpr ((List.nodup_dedup _).map_on fun a ha b hb hab ↦ ?_)
    exact faceData_injOn σ ha hb hab
  · intro j ψ
    have : ((F'.zip D').map fun q ↦ (q.1.2, faceData σ q.2)).map Prod.snd =
        D'.map (faceData σ) := by
      have e : ((F'.zip D').map fun q ↦ (q.1.2, faceData σ q.2)).map Prod.snd =
          ((F'.zip D').map Prod.snd).map (faceData σ) := by
        simp [List.map_map, Function.comp_def]
      rw [e, List.map_snd_zip hlenFD.ge]
    rw [this]
    simpa only [(hD'.map (faceData σ)).mem_iff] using existsUnique_faceData σ j ψ
  · rw [List.length_map, List.length_zip, ← hlenFD, min_self, card_eq_length hnd hall,
      List.length_cons]
    have h1 := hedges.length_eq
    rw [hTlen, List.length_cons] at hNlen
    have : (rest.length + 1) * (n + 1) = rest.length + 1 + (rest.length + 1) * n := by ring
    omega

end Ribbon.Schreier
