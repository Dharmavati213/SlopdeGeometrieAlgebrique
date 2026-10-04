/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.SurfaceOneVertex

/-!
# Contracting a spanning tree of a ribbon graph

A ribbon graph with several vertices is given by the list `Vs` of its vertex rotations and the list
`L` of its faces (cyclic lists of darts `(i, b)`), compatible through the exchange `Ribbon.flip`
of the two darts of an edge (`Ribbon.IsRibbon`). Contracting an edge `e` joining two distinct
vertices merges their rotations and deletes the two darts of `e` from the faces
(`Ribbon.IsRibbon.contract`); on the level of lists this is the same splice as the deletion of an
edge between two faces (`List.formPerm_splice`), on the vertex side.

Contracting the edges of a spanning tree one after the other (`Ribbon.IsRibbon.contract_tree`)
gives a one-vertex ribbon graph whose faces are the old faces without the darts of the tree; when
the labels of the tree edges are `1`, the face words do not change (`Ribbon.word_filter`). This
reduces the classification of ribbon graphs, on the level of groups, to the one-vertex case
(`Ribbon.IsOneVertex.hasSurfaceBasis`).

## References

* [B. Mohar, C. Thomassen, *Graphs on Surfaces*, §3.2–3.3][mohar2001]
-/

open Function Nielsen

namespace List

variable {α : Type*} [DecidableEq α]

/-- Erasing an element from the faces of a partition is erasing it from the whole list. -/
theorem flatten_map_erase {L : List (List α)} (h : L.flatten.Nodup) (a : α) :
    (L.map (·.erase a)).flatten = L.flatten.erase a := by
  induction L with
  | nil => simp
  | cons f L ih =>
    rw [map_cons, flatten_cons, flatten_cons]
    have h' : (f ++ L.flatten).Nodup := by simpa using h
    by_cases ha : a ∈ f
    · have haL : a ∉ L.flatten := fun h'' ↦ (nodup_append.mp h').2.2 a ha a h'' rfl
      rw [erase_append_left _ ha, ih (nodup_append.mp h').2.1, erase_of_not_mem haL]
    · rw [erase_append_right _ ha, erase_of_not_mem ha, ih (nodup_append.mp h').2.1]

end List

namespace Ribbon

variable {ι : Type*} [DecidableEq ι] {G : Type*} [Group G]

/- Lists of darts are erased with the `BEq` instance coming from `DecidableEq`, as in
`Ribbon.FaceCompat.erase`. -/
attribute [local instance 2000] instBEqOfDecidableEq

/-- **Ribbon graphs** with nonempty faces: `Vs` lists the rotations at the vertices (cyclic lists
of darts), `L` the faces; together the rotations contain each dart once, the darts come in pairs
`(i, true)`, `(i, false)`, the faces partition the darts and are nonempty, and the successor of a
dart `d` in its face is the successor of `flip d` in its rotation. -/
structure IsRibbon (Vs L : List (List (ι × Bool))) : Prop where
  nodup : Vs.flatten.Nodup
  flip_mem : ∀ d ∈ Vs.flatten, flip d ∈ Vs.flatten
  perm : L.flatten.Perm Vs.flatten
  ne_nil : ∀ f ∈ L, f ≠ []
  compat : FaceCompat L Vs flip

/-- A ribbon graph with one vertex and at least one dart is a one-vertex ribbon graph. -/
theorem IsRibbon.isOneVertex {R : List (ι × Bool)} {L : List (List (ι × Bool))}
    (h : IsRibbon [R] L) (hR : R ≠ []) : IsOneVertex R L where
  nodup := by simpa using h.nodup
  flip_mem d hd := by simpa using h.flip_mem d (by simpa using hd)
  perm := by simpa using h.perm
  ne_nil _ := h.ne_nil
  nil hR' := absurd hR' hR
  compat := h.compat

lemma IsRibbon.face_nodup {Vs L : List (List (ι × Bool))} (h : IsRibbon Vs L)
    {f : List (ι × Bool)} (hf : f ∈ L) : f.Nodup :=
  (h.perm.nodup_iff.mpr h.nodup).sublist (List.sublist_flatten_of_mem hf)

lemma IsRibbon.vertex_nodup {Vs L : List (List (ι × Bool))} (h : IsRibbon Vs L)
    {r : List (ι × Bool)} (hr : r ∈ Vs) : r.Nodup :=
  h.nodup.sublist (List.sublist_flatten_of_mem hr)

/-- The vertex rotations of a ribbon graph may be reordered. -/
theorem IsRibbon.perm_vertices {Vs Vs' L : List (List (ι × Bool))} (h : IsRibbon Vs L)
    (hp : Vs.Perm Vs') : IsRibbon Vs' L where
  nodup := hp.flatten.nodup_iff.mp h.nodup
  flip_mem d hd := hp.flatten.mem_iff.mp (h.flip_mem d (hp.flatten.mem_iff.mpr hd))
  perm := h.perm.trans hp.flatten
  ne_nil := h.ne_nil
  compat := h.compat.mono (fun f hf ↦ ⟨f, hf, h.face_nodup hf, List.IsRotated.refl f⟩)
    (fun r hr ↦ ⟨r, hp.mem_iff.mpr hr, h.vertex_nodup (hp.mem_iff.mpr hr), List.IsRotated.refl r⟩)

/-- Deleting both darts of the edge `e` from faces and rotations compatible with `twist e`. -/
lemma faceCompat_delete_twist {e : ι} {M Vs : List (List (ι × Bool))}
    (hc : FaceCompat M Vs (twist e)) (hM : ∀ f ∈ M, f.Nodup) (hV : ∀ r ∈ Vs, r.Nodup) :
    FaceCompat (M.map fun f ↦ (f.erase (e, false)).erase (e, true))
      (Vs.map fun r ↦ (r.erase (e, false)).erase (e, true)) flip := by
  have h1 := hc.erase hM hV (twist_injective e) (t := (e, false)) (twist_of_fst_eq rfl)
  have h2 := h1.erase (fun f hf ↦ by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact (hM g hg).erase _)
    (fun r hr ↦ by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
      exact (hV g hg).erase _) (twist_injective e) (t := (e, true)) (twist_of_fst_eq rfl)
  simp only [List.map_map, Function.comp_def] at h2
  refine h2.congr fun f hf d hd ↦ twist_of_fst_ne ?_
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  have hd1 : d ≠ (e, true) := fun h ↦ ((hM g hg).erase _).not_mem_erase (h ▸ hd)
  have hd2 : d ≠ (e, false) := fun h ↦ (hM g hg).not_mem_erase
    (h ▸ List.mem_of_mem_erase hd)
  exact fst_ne_of_not_mem hd1 hd2

omit [DecidableEq ι] in
lemma flatten_cons_cons_nodup {r₁ r₂ : List (ι × Bool)} {Vs : List (List (ι × Bool))}
    (h : (r₁ :: r₂ :: Vs).flatten.Nodup) :
    r₁.Nodup ∧ r₂.Nodup ∧ Vs.flatten.Nodup ∧ (∀ d ∈ r₁, d ∉ r₂) ∧ (∀ d ∈ r₁, d ∉ Vs.flatten) ∧
      (∀ d ∈ r₂, d ∉ Vs.flatten) := by
  simp only [List.flatten_cons] at h
  have h1 := List.nodup_append.mp h
  have h2 := List.nodup_append.mp h1.2.1
  exact ⟨h1.1, h2.1, h2.2.1, fun d hd hd' ↦ h1.2.2 d hd d (List.mem_append_left _ hd') rfl,
    fun d hd hd' ↦ h1.2.2 d hd d (List.mem_append_right _ hd') rfl,
    fun d hd hd' ↦ h2.2.2 d hd d hd' rfl⟩

/-- **Contracting an edge** joining two distinct vertices: the rotations `r₁ ∋ (e, true)` and
`r₂ ∋ (e, false)` merge into one rotation `r` with the darts of both but those of `e`, and the
two darts of `e` are deleted from the faces. The hypothesis `hne` (one of the two vertices has
another dart) excludes an isolated edge, whose face would become empty. -/
theorem IsRibbon.contract {r₁ r₂ : List (ι × Bool)} {Vs L : List (List (ι × Bool))} {e : ι}
    (h : IsRibbon (r₁ :: r₂ :: Vs) L) (h₁ : (e, true) ∈ r₁) (h₂ : (e, false) ∈ r₂)
    (hne : ∃ d ∈ r₁ ++ r₂, d.1 ≠ e) :
    ∃ r, r.Perm (r₁.erase (e, true) ++ r₂.erase (e, false)) ∧
      IsRibbon (r :: Vs) (L.map fun f ↦ (f.erase (e, false)).erase (e, true)) := by
  obtain ⟨hr₁, hr₂, hVs, h12, h13, h23⟩ := flatten_cons_cons_nodup h.nodup
  obtain ⟨u, hu⟩ := List.exists_isRotated_cons h₁
  obtain ⟨v, hv⟩ := List.exists_isRotated_cons h₂
  have hu' : ((e, true) :: u).Nodup := hu.nodup_iff.mp hr₁
  have hv' : ((e, false) :: v).Nodup := hv.nodup_iff.mp hr₂
  have hepu : (e, true) ∉ u := (List.nodup_cons.mp hu').1
  have hemv : (e, false) ∉ v := (List.nodup_cons.mp hv').1
  have hmem₁ : ∀ d ∈ u, d ∈ r₁ := fun d hd ↦ hu.mem_iff.mpr (List.mem_cons_of_mem _ hd)
  have hmem₂ : ∀ d ∈ v, d ∈ r₂ := fun d hd ↦ hv.mem_iff.mpr (List.mem_cons_of_mem _ hd)
  have hemu : (e, false) ∉ u := fun h' ↦ h12 _ (hmem₁ _ h') h₂
  have hepv : (e, true) ∉ v := fun h' ↦ h12 _ h₁ (hmem₂ _ h')
  have hu_fst : ∀ d ∈ u, d.1 ≠ e := fun d hd ↦
    fst_ne_of_not_mem (fun h' ↦ hepu (h' ▸ hd)) (fun h' ↦ hemu (h' ▸ hd))
  have hv_fst : ∀ d ∈ v, d.1 ≠ e := fun d hd ↦
    fst_ne_of_not_mem (fun h' ↦ hepv (h' ▸ hd)) (fun h' ↦ hemv (h' ▸ hd))
  have hVs_fst : ∀ r ∈ Vs, ∀ d ∈ r, d.1 ≠ e := fun r hr d hd ↦
    fst_ne_of_not_mem (fun h' ↦ h13 _ h₁ (h' ▸ List.mem_flatten_of_mem hr hd))
      (fun h' ↦ h23 _ h₂ (h' ▸ List.mem_flatten_of_mem hr hd))
  have huv : ∀ d ∈ u, d ∉ v := fun d hd hd' ↦ h12 d (hmem₁ d hd) (hmem₂ d hd')
  -- the merged rotation, with both darts of `e`
  set M := (e, false) :: (u ++ (e, true) :: v) with hMdef
  have hMn : M.Nodup := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨(List.nodup_cons.mp hu').2,
      List.nodup_cons.mpr ⟨hepv, (List.nodup_cons.mp hv').2⟩, ?_⟩⟩
    · intro h'
      rcases List.mem_append.mp h' with h' | h'
      · exact hemu h'
      · rcases List.mem_cons.mp h' with h' | h'
        · exact absurd h' (by simp)
        · exact hemv h'
    · intro a ha b hb hab
      subst hab
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hepu ha
      · exact huv a ha hb
  obtain ⟨hsu, hsv, hsx, hsy⟩ := List.formPerm_splice hMn
  have hc₁ : ∀ f ∈ L, ∀ d ∈ f, flip d ∈ (e, true) :: u →
      f.formPerm d = ((e, true) :: u).formPerm (flip d) := fun f hf d hd hd' ↦ by
    rw [← List.formPerm_eq_of_isRotated hr₁ hu]
    exact h.compat f hf r₁ (List.mem_cons_self ..) d hd (hu.mem_iff.mpr hd')
  have hc₂ : ∀ f ∈ L, ∀ d ∈ f, flip d ∈ (e, false) :: v →
      f.formPerm d = ((e, false) :: v).formPerm (flip d) := fun f hf d hd hd' ↦ by
    rw [← List.formPerm_eq_of_isRotated hr₂ hv]
    exact h.compat f hf r₂ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) d hd
      (hv.mem_iff.mpr hd')
  have hcompat : FaceCompat L (M :: Vs) (twist e) := by
    intro f hf r hr d hd hβd
    rcases List.mem_cons.mp hr with rfl | hr
    · by_cases hde : d.1 = e
      · rw [twist_of_fst_eq hde] at hβd ⊢
        obtain ⟨i, b⟩ := d
        simp only at hde
        subst hde
        cases b
        · rw [hsx, hc₁ f hf _ hd (List.mem_cons_self ..)]
          rfl
        · rw [hsy, hc₂ f hf _ hd (List.mem_cons_self ..)]
          rfl
      · rw [twist_of_fst_ne hde] at hβd ⊢
        have hfd : (flip d).1 ≠ e := by simpa [flip] using hde
        rcases List.mem_cons.mp hβd with h' | h'
        · exact absurd (by rw [h']) hfd
        rcases List.mem_append.mp h' with h' | h'
        · rw [hsu _ h', hc₁ f hf d hd (List.mem_cons_of_mem _ h')]
        rcases List.mem_cons.mp h' with h' | h'
        · exact absurd (by rw [h']) hfd
        · rw [hsv _ h', hc₂ f hf d hd (List.mem_cons_of_mem _ h')]
    · have hde : d.1 ≠ e := by
        intro hde
        rw [twist_of_fst_eq hde] at hβd
        exact hVs_fst r hr d hβd hde
      rw [twist_of_fst_ne hde] at hβd ⊢
      exact h.compat f hf r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)) d hd hβd
  have hdel := faceCompat_delete_twist hcompat (fun f hf ↦ h.face_nodup hf) (fun r hr ↦ by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hMn
    · exact h.vertex_nodup (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
  have hVs_erase : (Vs.map fun r ↦ (r.erase (e, false)).erase (e, true)) = Vs := by
    conv_rhs => rw [← List.map_id Vs]
    refine List.map_congr_left fun r hr ↦ ?_
    rw [List.erase_of_not_mem (fun h' ↦ hVs_fst r hr _ h' rfl),
      List.erase_of_not_mem (fun h' ↦ hVs_fst r hr _ h' rfl), id]
  have hM_erase : (M.erase (e, false)).erase (e, true) = u ++ v := by
    rw [hMdef, List.erase_cons_head, List.erase_append_right _ hepu, List.erase_cons_head]
  simp only [List.map_cons, hM_erase, hVs_erase] at hdel
  -- the dart sets
  have hold : (r₁ :: r₂ :: Vs).flatten.Perm
      ((e, true) :: (u ++ (e, false) :: (v ++ Vs.flatten))) := by
    simp only [List.flatten_cons]
    refine (hu.perm.append (hv.perm.append_right _)).trans ?_
    simp
  have hnew : ((u ++ v) :: Vs).flatten.Perm
      ((((r₁ :: r₂ :: Vs).flatten).erase (e, false)).erase (e, true)) := by
    have heq : ((((e, true) :: (u ++ (e, false) :: (v ++ Vs.flatten))).erase (e, false)).erase
        (e, true)) = ((u ++ v) :: Vs).flatten := by
      rw [List.erase_cons_tail (by simp), List.erase_append_right _ hemu, List.erase_cons_head,
        List.erase_cons_head]
      simp
    rw [← heq]
    exact ((hold.erase _).erase _).symm
  refine ⟨u ++ v, ?_, ⟨?_, fun d hd ↦ ?_, ?_, fun f hf ↦ ?_, hdel⟩⟩
  · refine List.Perm.append ?_ ?_
    · have := hu.perm.erase (e, true)
      rw [List.erase_cons_head] at this
      exact this.symm
    · have := hv.perm.erase (e, false)
      rw [List.erase_cons_head] at this
      exact this.symm
  · exact hnew.nodup_iff.mpr ((h.nodup.erase _).erase _)
  · -- `flip` preserves the remaining darts
    have hd' := hnew.mem_iff.mp hd
    have hdo : d ∈ (r₁ :: r₂ :: Vs).flatten := List.mem_of_mem_erase (List.mem_of_mem_erase hd')
    have hde : d.1 ≠ e := by
      have : d ∈ u ++ v ++ Vs.flatten := by simpa using hd
      rcases List.mem_append.mp this with h' | h'
      · rcases List.mem_append.mp h' with h' | h'
        · exact hu_fst d h'
        · exact hv_fst d h'
      · obtain ⟨r, hr, hdr⟩ := List.mem_flatten.mp h'
        exact hVs_fst r hr d hdr
    have hfd : (flip d).1 ≠ e := by simpa [flip] using hde
    refine hnew.mem_iff.mpr ?_
    rw [List.mem_erase_of_ne (fun h' ↦ hfd (by rw [h'])),
      List.mem_erase_of_ne (fun h' ↦ hfd (by rw [h']))]
    exact h.flip_mem d hdo
  · -- the faces partition the remaining darts
    have hLn : L.flatten.Nodup := h.perm.nodup_iff.mpr h.nodup
    have e1 : (L.map fun f ↦ (f.erase (e, false)).erase (e, true)).flatten =
        ((L.flatten).erase (e, false)).erase (e, true) := by
      rw [← List.flatten_map_erase hLn, ← List.flatten_map_erase]
      · simp [List.map_map, Function.comp_def]
      · rw [List.flatten_map_erase hLn]
        exact hLn.erase _
    rw [e1]
    exact ((h.perm.erase _).erase _).trans hnew.symm
  · -- no face consists of darts of `e` only
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    intro hnil
    have hgn := h.face_nodup hg
    have hsub : ∀ d ∈ g, d = (e, true) ∨ d = (e, false) := by
      intro d hd
      by_contra hd'
      have : d ∈ (g.erase (e, false)).erase (e, true) :=
        (List.mem_erase_of_ne fun h ↦ hd' (Or.inl h)).mpr
          ((List.mem_erase_of_ne fun h ↦ hd' (Or.inr h)).mpr hd)
      rw [hnil] at this
      exact List.not_mem_nil this
    have hgne := h.ne_nil g hg
    -- the successor of `(e, true)` in `g` lies in `r₂`
    have key₁ : (e, true) ∈ g → (e, false) ∈ g ∧ r₂ = [(e, false)] := by
      intro hp
      have hs := hc₂ g hg _ hp (List.mem_cons_self ..)
      rw [← List.formPerm_eq_of_isRotated hr₂ hv] at hs
      have hsg : g.formPerm (e, true) ∈ g := List.formPerm_apply_mem_of_mem hp
      have hsr : r₂.formPerm (e, false) ∈ r₂ := List.formPerm_apply_mem_of_mem h₂
      rcases hsub _ hsg with h' | h'
      · rw [hs] at h'
        exact absurd (h' ▸ hsr) (h12 _ h₁)
      · refine ⟨h' ▸ hsg, ?_⟩
        rw [hs] at h'
        have hlen := (List.formPerm_apply_mem_eq_self_iff _ hr₂ _ h₂).mp h'
        obtain _ | ⟨a, _ | ⟨b, t⟩⟩ := r₂
        · simp at h₂
        · simp only [List.mem_singleton] at h₂
          rw [h₂]
        · simp at hlen
    have key₂ : (e, false) ∈ g → (e, true) ∈ g ∧ r₁ = [(e, true)] := by
      intro hm
      have hs := hc₁ g hg _ hm (List.mem_cons_self ..)
      rw [← List.formPerm_eq_of_isRotated hr₁ hu] at hs
      have hsg : g.formPerm (e, false) ∈ g := List.formPerm_apply_mem_of_mem hm
      have hsr : r₁.formPerm (e, true) ∈ r₁ := List.formPerm_apply_mem_of_mem h₁
      rcases hsub _ hsg with h' | h'
      · refine ⟨h' ▸ hsg, ?_⟩
        rw [hs] at h'
        have hlen := (List.formPerm_apply_mem_eq_self_iff _ hr₁ _ h₁).mp h'
        obtain _ | ⟨a, _ | ⟨b, t⟩⟩ := r₁
        · simp at h₁
        · simp only [List.mem_singleton] at h₁
          rw [h₁]
        · simp at hlen
      · rw [hs] at h'
        exact absurd (h₂) (h12 _ (h' ▸ hsr))
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil g hgne
    have hboth : r₁ = [(e, true)] ∧ r₂ = [(e, false)] := by
      rcases hsub d hd with rfl | rfl
      · exact ⟨(key₂ (key₁ hd).1).2, (key₁ hd).2⟩
      · exact ⟨(key₂ hd).2, (key₁ (key₂ hd).1).2⟩
    obtain ⟨d', hd', hd'e⟩ := hne
    rw [hboth.1, hboth.2] at hd'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hd'
    rcases hd' with rfl | rfl <;> exact hd'e rfl

omit [DecidableEq ι] in
/-- In a list without `(e, !b)`, erasing `(e, b)` is erasing all darts of `e`. -/
lemma erase_eq_filter_fst {l : List (ι × Bool)} (hl : l.Nodup) {e : ι} {b : Bool}
    (h : (e, !b) ∉ l) [DecidableEq ι] : l.erase (e, b) = l.filter (fun d ↦ d.1 ≠ e) := by
  rw [hl.erase_eq_filter]
  refine List.filter_congr fun d hd ↦ ?_
  obtain ⟨i, c⟩ := d
  by_cases hi : i = e
  · subst hi
    have hc : c = b := by
      by_contra hc
      have : c = !b := by cases b <;> cases c <;> simp_all
      exact h (this ▸ hd)
    subst hc
    simp
  · have : (i, c) ≠ (e, b) := fun h' ↦ hi (congrArg Prod.fst h')
    simp [hi, this]

/-- **Contracting an edge**, with the deletions written as filters. -/
theorem IsRibbon.contract_filter {r₁ r₂ : List (ι × Bool)} {Vs L : List (List (ι × Bool))}
    {e : ι} (h : IsRibbon (r₁ :: r₂ :: Vs) L) (h₁ : (e, true) ∈ r₁) (h₂ : (e, false) ∈ r₂)
    (hne : ∃ d ∈ r₁ ++ r₂, d.1 ≠ e) :
    ∃ r, r.Perm ((r₁ ++ r₂).filter fun d ↦ d.1 ≠ e) ∧
      IsRibbon (r :: Vs) (L.map (·.filter fun d ↦ d.1 ≠ e)) := by
  obtain ⟨hr₁, hr₂, -, h12, -, -⟩ := flatten_cons_cons_nodup h.nodup
  obtain ⟨r, hr, h'⟩ := h.contract h₁ h₂ hne
  refine ⟨r, ?_, ?_⟩
  · rw [List.filter_append, ← erase_eq_filter_fst hr₁ (b := true) (fun h' ↦ h12 _ h' h₂),
      ← erase_eq_filter_fst hr₂ (b := false) (fun h' ↦ h12 _ h₁ h')]
    exact hr
  · convert h' using 1
    refine List.map_congr_left fun f hf ↦ ?_
    have hfn := h.face_nodup hf
    rw [hfn.erase_eq_filter, (hfn.filter _).erase_eq_filter, List.filter_filter]
    refine List.filter_congr fun d _ ↦ ?_
    obtain ⟨i, c⟩ := d
    by_cases hi : i = e
    · subst hi
      cases c <;> simp
    · have h1 : (i, c) ≠ (e, true) := fun h' ↦ hi (congrArg Prod.fst h')
      have h2 : (i, c) ≠ (e, false) := fun h' ↦ hi (congrArg Prod.fst h')
      simp [hi, h1, h2]

/-- **Tree darts.** `IsTreeDarts A T rs`: the `k`-th dart of `T` lies in the `k`-th rotation of
`rs`, and its partner lies in `A` or in one of the earlier rotations of `rs`. In a ribbon graph
`r₀ :: rs` with `IsTreeDarts r₀ T rs`, the edges of `T` form a spanning tree. -/
def IsTreeDarts : List (ι × Bool) → List (ι × Bool) → List (List (ι × Bool)) → Prop
  | _, [], [] => True
  | A, t :: T, r :: rs => t ∈ r ∧ flip t ∈ A ∧ IsTreeDarts (A ++ r) T rs
  | _, _, _ => False

omit [DecidableEq ι] in
lemma IsTreeDarts.mem_flatten : ∀ {A T : List (ι × Bool)} {rs : List (List (ι × Bool))},
    IsTreeDarts A T rs → ∀ t ∈ T, t ∈ rs.flatten
  | _, [], [], _, t, ht => by simp at ht
  | A, t' :: T, r :: rs, h, t, ht => by
    obtain ⟨h1, -, h3⟩ := h
    rcases List.mem_cons.mp ht with rfl | ht
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ (h3.mem_flatten t ht)
  | _, [], _ :: _, h, _, _ => h.elim
  | _, _ :: _, [], h, _, _ => h.elim

omit [DecidableEq ι] in
lemma IsTreeDarts.mono {P : ι × Bool → Prop} : ∀ {A A' T : List (ι × Bool)}
    {rs : List (List (ι × Bool))}, IsTreeDarts A T rs → (∀ d ∈ A, P d → d ∈ A') →
    (∀ t ∈ T, P (flip t)) → IsTreeDarts A' T rs
  | _, _, [], [], _, _, _ => trivial
  | A, A', t :: T, r :: rs, h, hA, hP => by
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, hA _ h2 (hP t (List.mem_cons_self ..)), h3.mono (fun d hd hPd ↦ ?_)
      fun t' ht' ↦ hP t' (List.mem_cons_of_mem _ ht')⟩
    rcases List.mem_append.mp hd with hd | hd
    · exact List.mem_append_left _ (hA d hd hPd)
    · exact List.mem_append_right _ hd
  | _, _, [], _ :: _, h, _, _ => h.elim
  | _, _, _ :: _, [], h, _, _ => h.elim

omit [DecidableEq ι] in
lemma exists_mem_ne_of_two_le {l : List (ι × Bool)} (hl : l.Nodup) (h2 : 2 ≤ l.length)
    (a : ι × Bool) : ∃ d ∈ l, d ≠ a := by
  obtain _ | ⟨x, _ | ⟨y, t⟩⟩ := l
  · simp at h2
  · simp at h2
  · by_cases hx : x = a
    · refine ⟨y, by simp, fun hy ↦ ?_⟩
      exact (List.nodup_cons.mp hl).1 (by rw [hx, ← hy]; simp)
    · exact ⟨x, List.mem_cons_self .., hx⟩

/-- **Contracting a spanning tree.** If the darts `T` are tree darts for the rotations `rs` hanging
off `r₀` (`Ribbon.IsTreeDarts`) and every rotation of `rs` has at least two darts, contracting the
edges of `T` gives a one-vertex ribbon graph: its rotation has the darts of all the rotations but
those of `T`, and its faces are the old faces without the darts of `T`. -/
theorem IsRibbon.contract_tree : ∀ (rs : List (List (ι × Bool))) {r₀ : List (ι × Bool)}
    {L : List (List (ι × Bool))} {T : List (ι × Bool)}, IsRibbon (r₀ :: rs) L →
    IsTreeDarts r₀ T rs → (∀ r ∈ rs, 2 ≤ r.length) →
    ∃ R, R.Perm ((r₀ :: rs).flatten.filter fun d ↦ d.1 ∉ T.map Prod.fst) ∧
      IsRibbon [R] (L.map (·.filter fun d ↦ d.1 ∉ T.map Prod.fst))
  | [], r₀, L, T, h, hT, _ => by
    obtain rfl : T = [] := by
      cases T
      · rfl
      · exact hT.elim
    refine ⟨r₀, by simp, ?_⟩
    simpa using h
  | r :: rs, r₀, L, T, h, hT, hlen => by
    obtain _ | ⟨t, T⟩ := T
    · exact hT.elim
    obtain ⟨ht, hft, hT'⟩ := hT
    obtain ⟨hr₀n, hrn, -, h0r, h0s, hrs⟩ := flatten_cons_cons_nodup h.nodup
    obtain ⟨e, b⟩ := t
    have hlen' : 2 ≤ r.length := hlen r (List.mem_cons_self ..)
    obtain ⟨d, hd, hdt⟩ := exists_mem_ne_of_two_le hrn hlen' (e, b)
    have hde : d.1 ≠ e := by
      intro hde
      obtain ⟨i, c⟩ := d
      simp only at hde
      subst hde
      by_cases hc : c = b
      · exact hdt (by rw [hc])
      · have : c = !b := by cases b <;> cases c <;> simp_all
        subst this
        exact h0r _ (by simpa [flip] using hft) hd
    -- contract the edge `e`
    obtain ⟨R₁, hR₁, h₁⟩ : ∃ R₁, R₁.Perm ((r₀ ++ r).filter fun d ↦ d.1 ≠ e) ∧
        IsRibbon (R₁ :: rs) (L.map (·.filter fun d ↦ d.1 ≠ e)) := by
      cases b
      · exact h.contract_filter (by simpa [flip] using hft) ht
          ⟨d, List.mem_append_right _ hd, hde⟩
      · obtain ⟨R₁, hR₁, h₁⟩ := (h.perm_vertices (List.Perm.swap _ _ _)).contract_filter ht
          (by simpa [flip] using hft) ⟨d, List.mem_append_left _ hd, hde⟩
        exact ⟨R₁, hR₁.trans (List.perm_append_comm.filter _), h₁⟩
    -- the remaining tree darts
    have hrs_fst : ∀ d ∈ rs.flatten, d.1 ≠ e := by
      intro d hd hde'
      obtain ⟨i, c⟩ := d
      simp only at hde'
      subst hde'
      by_cases hc : c = b
      · subst hc
        exact hrs _ ht hd
      · have : c = !b := by cases b <;> cases c <;> simp_all
        subst this
        exact h0s _ (by simpa [flip] using hft) hd
    have hT'' : IsTreeDarts R₁ T rs := hT'.mono (P := fun d ↦ d.1 ≠ e)
      (fun d hd hPd ↦ hR₁.mem_iff.mpr (List.mem_filter.mpr ⟨hd, by simpa using hPd⟩))
      (fun t' ht' ↦ by simpa [flip] using hrs_fst t' (hT'.mem_flatten t' ht'))
    obtain ⟨R, hR, hR'⟩ := contract_tree rs h₁ hT'' fun r' hr' ↦
      hlen r' (List.mem_cons_of_mem _ hr')
    refine ⟨R, hR.trans ?_, ?_⟩
    · simp only [List.flatten_cons, List.filter_append]
      refine ((hR₁.filter _).append_right _).trans ?_
      rw [List.filter_filter, ← List.append_assoc, List.filter_append]
      refine List.Perm.append (List.Perm.of_eq ?_) (List.Perm.of_eq ?_)
      · rw [← List.filter_append, ← List.filter_append]
        refine List.filter_congr fun d _ ↦ ?_
        rw [Bool.eq_iff_iff]
        simp only [List.map_cons, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons, not_or]
        tauto
      · refine List.filter_congr fun d hd ↦ ?_
        simp [hrs_fst d hd]
    · convert hR' using 1
      rw [List.map_map]
      refine List.map_congr_left fun f _ ↦ ?_
      simp only [Function.comp_apply, List.filter_filter]
      refine List.filter_congr fun d _ ↦ ?_
      rw [Bool.eq_iff_iff]
      simp only [List.map_cons, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons, not_or]
      tauto

/-- Deleting darts of edges labelled `1` does not change the word of a face. -/
lemma word_filter (x : ι → G) (S : List ι) (hS : ∀ i ∈ S, x i = 1) (f : List (ι × Bool)) :
    word x (f.filter fun d ↦ d.1 ∉ S) = word x f := by
  induction f with
  | nil => rfl
  | cons d f ih =>
    by_cases hd : d.1 ∈ S
    · rw [List.filter_cons_of_neg (by simpa using hd), ih, word_cons]
      obtain ⟨i, b⟩ := d
      cases b <;> simp [label, hS i hd]
    · rw [List.filter_cons_of_pos (by simpa using hd), word_cons, word_cons, ih]

/-- **Classification of ribbon graphs, on the level of groups.** Let `r₀ :: rs` be a ribbon graph
with a spanning tree of darts `T` (`Ribbon.IsTreeDarts`), every rotation of `rs` having at least
two darts, and labels `x : ι → G` equal to `1` on the tree edges. If some dart is not on the tree,
then the group spanned by the labels of the edges off the tree has a surface basis whose boundary
elements are conjugate to the words of the faces, one for each face (`Ribbon.HasSurfaceBasis` for
the one-vertex ribbon graph obtained by contracting the tree, whose face words are those of `L`). -/
theorem IsRibbon.hasSurfaceBasis_of_tree (x : ι → G) {rs : List (List (ι × Bool))}
    {r₀ : List (ι × Bool)} {L : List (List (ι × Bool))} {T : List (ι × Bool)}
    (h : IsRibbon (r₀ :: rs) L) (hT : IsTreeDarts r₀ T rs) (hlen : ∀ r ∈ rs, 2 ≤ r.length)
    (hx : ∀ t ∈ T, x t.1 = 1) (hR : ∃ d ∈ (r₀ :: rs).flatten, d.1 ∉ T.map Prod.fst) :
    ∃ R, R.Perm ((r₀ :: rs).flatten.filter fun d ↦ d.1 ∉ T.map Prod.fst) ∧
      HasSurfaceBasis x R (L.map (·.filter fun d ↦ d.1 ∉ T.map Prod.fst)) ∧
      (L.map (·.filter fun d ↦ d.1 ∉ T.map Prod.fst)).map (word x) = L.map (word x) := by
  obtain ⟨R, hR', h'⟩ := h.contract_tree rs hT hlen
  have hRne : R ≠ [] := by
    obtain ⟨d, hd, hdT⟩ := hR
    intro hR0
    rw [hR0] at hR'
    have := hR'.symm.subset (List.mem_filter.mpr ⟨hd, by simpa using hdT⟩)
    simp at this
  refine ⟨R, hR', (h'.isOneVertex hRne).hasSurfaceBasis x, ?_⟩
  rw [List.map_map]
  refine List.map_congr_left fun f _ ↦ ?_
  exact word_filter x _ (fun i hi ↦ by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hi
    exact hx t ht) f

end Ribbon
