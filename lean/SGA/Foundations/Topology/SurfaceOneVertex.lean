/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.SurfaceRibbon
import SGA.Foundations.Topology.SurfaceNielsen

/-!
# The classification of one-vertex ribbon graphs, on the level of fundamental groups

A *one-vertex ribbon graph* has a single vertex, edges `i` (loops at the vertex) with two darts
`(i, true)` (the start of `i`) and `(i, false)` (its end), a *rotation* `R` (all darts, in their
cyclic order around the vertex) and *faces* `L`: the successor of a dart `d` in its face is the
successor in `R` of the other dart of the same edge (`Ribbon.IsOneVertex`). Its fundamental group
is free on the edges, and each face `f` has a *word*: the product of the labels of its darts,
`x i` for `(i, true)` and `(x i)⁻¹` for `(i, false)` (`Ribbon.word`).

**Theorem** (`Ribbon.IsOneVertex.hasSurfaceBasis`). The group spanned by the `x i` has a surface
basis whose boundary elements are conjugate (in that group) to the face words, one for each face:
handles `(aⱼ, bⱼ)`, `j < g`, and boundary elements `c_f` with `∏ⱼ [aⱼ, bⱼ] ∏_f c_f = 1`, such
that the `aⱼ, bⱼ` and all `c_f` but one may replace the `x i` in every free family
(`Nielsen.IsSurfaceBasis`), with `2g + #faces = #edges + 1` (Euler's formula `1 - E + F = 2 - 2g`).

The proof is by induction on the number of edges: delete the edge `e` of the first dart. If the
two darts of `e` lie on different faces `e u` and `e⁻¹ v`, these merge into `u v` and the boundary
element `c ~ u v` splits as `(s u e s⁻¹)(s e⁻¹ v s⁻¹)` (`Nielsen.IsSurfaceBasis.split`); if they
lie on the same face `e u e⁻¹ v`, it splits into `u` and `v`, and the two boundary elements merge
back into one and a new handle (`Nielsen.IsSurfaceBasis.handle`). On the level of ribbon graphs
both are `Ribbon.FaceCompat.erase` after a splice (`List.formPerm_splice`).

This is the algebraic core of the presentation of the fundamental group of a punctured compact
orientable surface: a punctured surface retracts onto a ribbon graph, which a spanning tree turns
into a one-vertex ribbon graph without changing the face words.

## References

* [W. S. Massey, *Algebraic Topology: An Introduction*, Chapter 1][massey1967]
* [B. Mohar, C. Thomassen, *Graphs on Surfaces*, §3.3 (classification via ribbon graphs)][mohar2001]
-/

open Function Nielsen

namespace Ribbon

/- Lists of darts are erased with the `BEq` instance coming from `DecidableEq`, as in
`Ribbon.FaceCompat.erase`, not with the structural instance on products. -/
attribute [local instance 2000] instBEqOfDecidableEq

variable {ι : Type*} {G : Type*} [Group G]

/-- The other dart of the same edge. -/
def flip (d : ι × Bool) : ι × Bool := (d.1, !d.2)

@[simp] lemma flip_flip (d : ι × Bool) : flip (flip d) = d := by simp [flip]

lemma flip_injective : Injective (flip : ι × Bool → ι × Bool) :=
  fun a b h ↦ by simpa using congrArg flip h

lemma flip_ne (d : ι × Bool) : flip d ≠ d := by
  obtain ⟨i, b⟩ := d
  simp [flip]

/-- The label of a dart: `x i` for the start `(i, true)` of `i`, `(x i)⁻¹` for its end. -/
def label (x : ι → G) (d : ι × Bool) : G := if d.2 then x d.1 else (x d.1)⁻¹

/-- The word of a face: the product of the labels of its darts. -/
def word (x : ι → G) (f : List (ι × Bool)) : G := (f.map (label x)).prod

@[simp] lemma word_nil (x : ι → G) : word x [] = 1 := rfl

@[simp] lemma word_cons (x : ι → G) (d : ι × Bool) (f : List (ι × Bool)) :
    word x (d :: f) = label x d * word x f := by
  simp [word]

@[simp] lemma word_append (x : ι → G) (f f' : List (ι × Bool)) :
    word x (f ++ f') = word x f * word x f' := by
  simp [word]

@[simp] lemma label_true (x : ι → G) (i : ι) : label x (i, true) = x i := rfl

@[simp] lemma label_false (x : ι → G) (i : ι) : label x (i, false) = (x i)⁻¹ := rfl

/-- The edges of a list of darts: one entry per positive dart. -/
def edges (R : List (ι × Bool)) : List ι := (R.filter (·.2)).map Prod.fst

lemma edges_perm {R R' : List (ι × Bool)} (h : R.Perm R') : (edges R).Perm (edges R') :=
  (h.filter _).map _

lemma edges_cons_append (e : ι) (A B : List (ι × Bool)) :
    edges ((e, true) :: (A ++ (e, false) :: B)) = e :: edges (A ++ B) := by
  simp [edges, List.filter_append]

/-- The conclusion of the classification theorem for `(R, L)`: a surface basis of the group spanned
by the edge labels whose boundary elements are conjugate to the face words, one per face, with
`2g + #faces = #edges + 1`. -/
def HasSurfaceBasis (x : ι → G) (R : List (ι × Bool)) (L : List (List (ι × Bool))) : Prop :=
  ∃ (F : List (List (ι × Bool) × G)) (hs : List (G × G)), (F.map Prod.fst).Perm L ∧
    (∀ p ∈ F, IsConjIn (spanOf ((edges R).map x)) p.2 (word x p.1)) ∧
    IsSurfaceBasis ((edges R).map x) hs (F.map Prod.snd) ∧
    2 * hs.length + F.length = (edges R).length + 1

lemma HasSurfaceBasis.of_perm {x : ι → G} {R R' : List (ι × Bool)} {L : List (List (ι × Bool))}
    (h : HasSurfaceBasis x R L) (hR : R.Perm R') : HasSurfaceBasis x R' L := by
  obtain ⟨F, hs, hF, hconj, hsb, hcount⟩ := h
  have he := (edges_perm hR).map x
  refine ⟨F, hs, hF, fun p hp ↦ (spanOf_perm he) ▸ hconj p hp, ⟨hsb.1, ?_⟩, ?_⟩
  · obtain ⟨A, c, B, hcs, hI⟩ := hsb.2
    exact ⟨A, c, B, hcs, hI.perm_right he⟩
  · rw [← (edges_perm hR).length_eq, hcount]

variable [DecidableEq ι]

/-- **One-vertex ribbon graphs.** `R` lists all the darts in their cyclic order around the vertex;
the darts come in pairs `(i, true)`, `(i, false)`; the faces `L` partition the darts, are nonempty
(or, if there are no darts, there is exactly one, empty, face), and the successor of `d` in its
face is the successor of `flip d` in `R`. -/
structure IsOneVertex (R : List (ι × Bool)) (L : List (List (ι × Bool))) : Prop where
  nodup : R.Nodup
  flip_mem : ∀ d ∈ R, flip d ∈ R
  perm : L.flatten.Perm R
  ne_nil : R ≠ [] → ∀ f ∈ L, f ≠ []
  nil : R = [] → L = [[]]
  compat : FaceCompat L [R] flip

lemma IsOneVertex.flatten_nodup {R : List (ι × Bool)} {L : List (List (ι × Bool))}
    (h : IsOneVertex R L) : L.flatten.Nodup :=
  h.perm.nodup_iff.mpr h.nodup

lemma IsOneVertex.face_nodup {R : List (ι × Bool)} {L : List (List (ι × Bool))}
    (h : IsOneVertex R L) {f : List (ι × Bool)} (hf : f ∈ L) : f.Nodup :=
  h.flatten_nodup.sublist (List.sublist_flatten_of_mem hf)

lemma IsOneVertex.of_isRotated {R R' : List (ι × Bool)} {L : List (List (ι × Bool))}
    (h : IsOneVertex R L) (hr : R.IsRotated R') : IsOneVertex R' L where
  nodup := hr.nodup_iff.mp h.nodup
  flip_mem d hd := hr.mem_iff.mp (h.flip_mem d (hr.mem_iff.mpr hd))
  perm := h.perm.trans hr.perm
  ne_nil hR := h.ne_nil fun h' ↦ hR (List.isRotated_nil_iff'.mp (h' ▸ hr)).symm
  nil hR := h.nil (List.isRotated_nil_iff.mp (hR ▸ hr))
  compat := h.compat.mono (fun f hf ↦ ⟨f, hf, h.face_nodup hf, List.IsRotated.refl f⟩)
    (fun r hr' ↦ ⟨R, List.mem_singleton_self R, h.nodup, by
      rw [List.mem_singleton.mp hr']; exact hr⟩)


lemma FaceCompat.congr {L Vs : List (List (ι × Bool))} {β β' : ι × Bool → ι × Bool}
    (hc : FaceCompat L Vs β) (h : ∀ f ∈ L, ∀ d ∈ f, β d = β' d) : FaceCompat L Vs β' := by
  intro f hf r hr d hd hβd
  rw [← h f hf d hd] at hβd ⊢
  exact hc f hf r hr d hd hβd

omit [DecidableEq ι] in
lemma label_mem_spanOf (x : ι → G) {R : List (ι × Bool)} (hR : ∀ d ∈ R, flip d ∈ R)
    {d : ι × Bool} (hd : d ∈ R) : label x d ∈ spanOf ((edges R).map x) := by
  obtain ⟨i, b⟩ := d
  have hi : (i, true) ∈ R := by
    cases b
    · exact hR _ hd
    · exact hd
  have hx : x i ∈ (edges R).map x :=
    List.mem_map.mpr ⟨i, List.mem_map.mpr ⟨(i, true), List.mem_filter.mpr ⟨hi, rfl⟩, rfl⟩, rfl⟩
  cases b
  · exact Subgroup.inv_mem _ (mem_spanOf hx)
  · exact mem_spanOf hx

omit [DecidableEq ι] in
lemma word_mem_spanOf (x : ι → G) {R : List (ι × Bool)} (hR : ∀ d ∈ R, flip d ∈ R)
    {f : List (ι × Bool)} (hf : ∀ d ∈ f, d ∈ R) : word x f ∈ spanOf ((edges R).map x) :=
  list_prod_mem fun a ha ↦ by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    exact label_mem_spanOf x hR (hf d hd)

omit [DecidableEq ι] in
lemma isConjIn_word_of_isRotated (x : ι → G) {K : Subgroup G} {f f' : List (ι × Bool)}
    (h : f.IsRotated f') (hK : ∀ d ∈ f, label x d ∈ K) : IsConjIn K (word x f) (word x f') :=
  isConjIn_prod_of_isRotated (h.map _) fun a ha ↦ by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp ha
    exact hK d hd

/-- The involution `flip`, twisted to fix the two darts of the edge `e`. -/
def twist (e : ι) (d : ι × Bool) : ι × Bool := if d.1 = e then d else flip d

lemma twist_injective (e : ι) : Injective (twist e) := by
  intro a b h
  unfold twist at h
  split_ifs at h with ha hb hb
  · exact h
  · exact absurd (by simpa [flip] using congrArg Prod.fst h.symm ▸ ha) hb
  · exact absurd (by simpa [flip] using congrArg Prod.fst h ▸ hb) ha
  · exact flip_injective h

lemma twist_of_fst_eq {e : ι} {d : ι × Bool} (h : d.1 = e) : twist e d = d := by
  simp [twist, h]

lemma twist_of_fst_ne {e : ι} {d : ι × Bool} (h : d.1 ≠ e) : twist e d = flip d := by
  simp [twist, h]

/-- Deleting both darts of the edge `e` from faces compatible with `twist e`. -/
lemma faceCompat_delete {e : ι} {A B : List (ι × Bool)} {M : List (List (ι × Bool))}
    (hR : ((e, true) :: (A ++ (e, false) :: B)).Nodup)
    (hc : FaceCompat M [(e, true) :: (A ++ (e, false) :: B)] (twist e))
    (hM : ∀ f ∈ M, f.Nodup) :
    FaceCompat (M.map fun f ↦ (f.erase (e, false)).erase (e, true)) [A ++ B] flip := by
  have h1 := hc.erase hM (by simpa using hR) (twist_injective e) (t := (e, false))
    (twist_of_fst_eq rfl)
  have h2 := h1.erase (fun f hf ↦ by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact (hM g hg).erase _)
    (fun r hr ↦ by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
      rw [List.mem_singleton.mp hg]
      exact hR.erase _) (twist_injective e) (t := (e, true)) (twist_of_fst_eq rfl)
  have hemA : (e, false) ∉ A := fun h ↦ by
    have := (List.nodup_cons.mp hR).2
    exact (List.nodup_append.mp this).2.2 _ h _ (List.mem_cons_self ..) rfl
  have hRe : (((e, true) :: (A ++ (e, false) :: B)).erase (e, false)).erase (e, true) = A ++ B := by
    rw [List.erase_cons_tail (by simp), List.erase_append_right _ hemA, List.erase_cons_head,
      List.erase_cons_head]
  simp only [List.map_map, List.map_cons, List.map_nil, Function.comp_def, hRe] at h2
  refine h2.congr fun f hf d hd ↦ twist_of_fst_ne ?_
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  have hd1 : d ≠ (e, true) := fun h ↦ ((hM g hg).erase _).not_mem_erase (h ▸ hd)
  have hd2 : d ≠ (e, false) := fun h ↦ (hM g hg).not_mem_erase
    (h ▸ List.mem_of_mem_erase hd)
  obtain ⟨i, b⟩ := d
  rintro rfl
  cases b
  · exact hd2 rfl
  · exact hd1 rfl


omit [DecidableEq ι] in
lemma exists_eq_append_of_mem_map {β : Type*} {F : List (List (ι × Bool) × β)}
    {a : List (ι × Bool)} (h : a ∈ F.map Prod.fst) : ∃ F₁ b F₂, F = F₁ ++ (a, b) :: F₂ := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  obtain ⟨F₁, F₂, rfl⟩ := List.append_of_mem hp
  exact ⟨F₁, p.2, F₂, rfl⟩

section Step

variable {x : ι → G} {e : ι} {A B : List (ι × Bool)} {L : List (List (ι × Bool))}

omit [DecidableEq ι] in
lemma fst_ne_of_mem_rest (hR : ((e, true) :: (A ++ (e, false) :: B)).Nodup) {d : ι × Bool}
    (hd : d ∈ A ++ B) : d.1 ≠ e := by
  obtain ⟨i, b⟩ := d
  rintro rfl
  have h1 := (List.nodup_cons.mp hR).1
  have h2 := (List.nodup_append.mp (List.nodup_cons.mp hR).2)
  rcases List.mem_append.mp hd with hd | hd <;> cases b
  · exact h2.2.2 _ hd _ (List.mem_cons_self ..) rfl
  · exact h1 (List.mem_append_left _ hd)
  · exact (List.nodup_cons.mp h2.2.1).1 hd
  · exact h1 (List.mem_append_right _ (List.mem_cons_of_mem _ hd))

omit [DecidableEq ι] in
lemma mem_rest_of_mem {d : ι × Bool} (hd : d ∈ (e, true) :: (A ++ (e, false) :: B))
    (h1 : d.1 ≠ e) : d ∈ A ++ B := by
  rcases List.mem_cons.mp hd with rfl | hd
  · exact absurd rfl h1
  rcases List.mem_append.mp hd with hd | hd
  · exact List.mem_append_left _ hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact absurd rfl h1
  · exact List.mem_append_right _ hd

/-- The relevant facts about the rotation `(e, true) :: (A ++ (e, false) :: B)`. -/
lemma IsOneVertex.rest (h : IsOneVertex ((e, true) :: (A ++ (e, false) :: B)) L) :
    (A ++ B).Nodup ∧ (∀ d ∈ A ++ B, flip d ∈ A ++ B) ∧
      edges ((e, true) :: (A ++ (e, false) :: B)) = e :: edges (A ++ B) := by
  have hR := h.nodup
  refine ⟨?_, fun d hd ↦ ?_, edges_cons_append e A B⟩
  · have := (List.nodup_cons.mp hR).2
    rw [List.nodup_append] at this ⊢
    exact ⟨this.1, (List.nodup_cons.mp this.2.1).2,
      fun a ha b hb ↦ this.2.2 a ha b (List.mem_cons_of_mem _ hb)⟩
  · have hd' : d ∈ (e, true) :: (A ++ (e, false) :: B) := by
      rcases List.mem_append.mp hd with hd | hd
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hd)
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hd))
    exact mem_rest_of_mem (h.flip_mem d hd') (by simpa [flip] using fst_ne_of_mem_rest hR hd)


/-- The successor of `d ∈ R` in a face of a one-vertex ribbon graph. -/
lemma IsOneVertex.compat' {R : List (ι × Bool)} (h : IsOneVertex R L) {f : List (ι × Bool)}
    (hf : f ∈ L) {d : ι × Bool} (hd : d ∈ f) : f.formPerm d = R.formPerm (flip d) := by
  have hdR : d ∈ R := h.perm.subset (List.mem_flatten_of_mem hf hd)
  exact h.compat f hf R (List.mem_singleton_self _) d hd (h.flip_mem d hdR)

lemma IsOneVertex.mem_of_mem_face {R : List (ι × Bool)} (h : IsOneVertex R L)
    {f : List (ι × Bool)} (hf : f ∈ L) {d : ι × Bool} (hd : d ∈ f) : d ∈ R :=
  h.perm.subset (List.mem_flatten_of_mem hf hd)

/-- Rotating a face does not change the compatibility. -/
lemma IsOneVertex.compat_of_isRotated {R : List (ι × Bool)} (h : IsOneVertex R L)
    {f f₀ : List (ι × Bool)} (hf : f ∈ L) (hr : f.IsRotated f₀) {d : ι × Bool} (hd : d ∈ f₀) :
    f₀.formPerm d = R.formPerm (flip d) := by
  rw [← List.formPerm_eq_of_isRotated (h.face_nodup hf) hr]
  exact h.compat' hf (hr.mem_iff.mpr hd)

/-- In a one-vertex ribbon graph with at least two darts, the rotation has no fixed points. -/
lemma IsOneVertex.formPerm_ne {R : List (ι × Bool)} (h : IsOneVertex R L) {d : ι × Bool}
    (hd : d ∈ R) : R.formPerm d ≠ d := by
  rw [List.formPerm_apply_mem_ne_self_iff _ h.nodup d hd]
  have hfd := h.flip_mem d hd
  have hne := flip_ne d
  rcases R with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp at hd
  · simp only [List.mem_singleton] at hd hfd
    exact absurd (hfd.trans hd.symm) hne
  · simp


omit [DecidableEq ι] in
lemma fst_ne_of_not_mem {d : ι × Bool} (h1 : d ≠ (e, true)) (h2 : d ≠ (e, false)) : d.1 ≠ e := by
  obtain ⟨i, b⟩ := d
  rintro rfl
  cases b
  · exact h2 rfl
  · exact h1 rfl

/-- **Induction step, both darts of `e` on the same face.** The face `e u e⁻¹ v` splits into `u`
and `v`; their boundary elements merge with the new generator into one boundary element and a
handle (`Nielsen.IsSurfaceBasis.handle`). -/
lemma IsOneVertex.step_same (h : IsOneVertex ((e, true) :: (A ++ (e, false) :: B)) L)
    (ih : ∀ L', IsOneVertex (A ++ B) L' → HasSurfaceBasis x (A ++ B) L')
    {f₁ : List (ι × Bool)} (hf₁ : f₁ ∈ L) (hp : (e, true) ∈ f₁) (hm : (e, false) ∈ f₁) :
    HasSurfaceBasis x ((e, true) :: (A ++ (e, false) :: B)) L := by
  set R := (e, true) :: (A ++ (e, false) :: B) with hRdef
  obtain ⟨hR'n, hR'flip, hedges⟩ := h.rest
  have hRn := h.nodup
  obtain ⟨u, v, hrot⟩ := List.exists_isRotated_cons_append hp hm (by simp)
  set f₀ := (e, true) :: (u ++ (e, false) :: v) with hf₀def
  have hf₀n : f₀.Nodup := hrot.nodup_iff.mp (h.face_nodup hf₁)
  have hc₀ : ∀ d ∈ f₀, f₀.formPerm d = R.formPerm (flip d) := fun d hd ↦
    h.compat_of_isRotated hf₁ hrot hd
  obtain ⟨hsu, hsv, hsx, hsy⟩ := List.formPerm_splice hf₀n
  have hepu : (e, true) ∉ u := fun h' ↦ (List.nodup_cons.mp hf₀n).1 (List.mem_append_left _ h')
  have hepv : (e, true) ∉ v := fun h' ↦
    (List.nodup_cons.mp hf₀n).1 (List.mem_append_right _ (List.mem_cons_of_mem _ h'))
  have huv := (List.nodup_cons.mp hf₀n).2
  have hemu : (e, false) ∉ u := fun h' ↦
    (List.nodup_append.mp huv).2.2 _ h' _ (List.mem_cons_self ..) rfl
  have hemv : (e, false) ∉ v := (List.nodup_cons.mp (List.nodup_append.mp huv).2.1).1
  have hu_fst : ∀ d ∈ u, d.1 ≠ e := fun d hd ↦
    fst_ne_of_not_mem (fun h' ↦ hepu (h' ▸ hd)) (fun h' ↦ hemu (h' ▸ hd))
  have hv_fst : ∀ d ∈ v, d.1 ≠ e := fun d hd ↦
    fst_ne_of_not_mem (fun h' ↦ hepv (h' ▸ hd)) (fun h' ↦ hemv (h' ▸ hd))
  have hepR : (e, true) ∈ R := List.mem_cons_self ..
  have hemR : (e, false) ∈ R := by simp [hRdef]
  -- `u` and `v` are nonempty: the rotation has no fixed points
  have hu : u ≠ [] := by
    rintro rfl
    have h1 := hc₀ (e, true) (List.mem_cons_self ..)
    rw [hsx] at h1
    simp only [List.formPerm_singleton, Equiv.Perm.one_apply, flip, Bool.not_true] at h1
    exact h.formPerm_ne hemR h1.symm
  have hv : v ≠ [] := by
    rintro rfl
    have h1 := hc₀ (e, false) (by simp [hf₀def])
    rw [hsy] at h1
    simp only [List.formPerm_singleton, Equiv.Perm.one_apply, flip, Bool.not_false] at h1
    exact h.formPerm_ne hepR h1.symm
  -- the other faces
  set L₃ := L.erase f₁
  have hL : L.Perm (f₁ :: L₃) := List.perm_cons_erase hf₁
  have hL₃ : ∀ f ∈ L₃, f ∈ L := fun f hf ↦ List.mem_of_mem_erase hf
  have hflat : (f₁ ++ L₃.flatten).Nodup := by
    have := h.flatten_nodup
    rwa [hL.flatten.nodup_iff, List.flatten_cons] at this
  have hdisj : ∀ f ∈ L₃, ∀ d ∈ f, d ∉ f₁ := fun f hf d hd hd' ↦
    (List.nodup_append.mp hflat).2.2 d hd' d (List.mem_flatten_of_mem hf hd) rfl
  have hL₃_fst : ∀ f ∈ L₃, ∀ d ∈ f, d.1 ≠ e := fun f hf d hd ↦
    fst_ne_of_not_mem (fun h' ↦ hdisj f hf d hd (h' ▸ hp)) (fun h' ↦ hdisj f hf d hd (h' ▸ hm))
  -- the new faces `u`, `v` and `L₃` are compatible with `A ++ B`
  have hcompat : FaceCompat (((e, false) :: u) :: ((e, true) :: v) :: L₃) [R] (twist e) := by
    intro f hf r hr d hd hβd
    rw [List.mem_singleton.mp hr]
    rcases List.mem_cons.mp hf with rfl | hf
    · rcases List.mem_cons.mp hd with rfl | hd
      · rw [twist_of_fst_eq (e := e) (d := (e, false)) rfl, ← hsx, hc₀ _ (List.mem_cons_self ..)]
        rfl
      · rw [twist_of_fst_ne (hu_fst d hd), ← hsu d hd, hc₀ d (by simp [hf₀def, hd])]
    rcases List.mem_cons.mp hf with rfl | hf
    · rcases List.mem_cons.mp hd with rfl | hd
      · rw [twist_of_fst_eq (e := e) (d := (e, true)) rfl, ← hsy, hc₀ _ (by simp [hf₀def])]
        rfl
      · rw [twist_of_fst_ne (hv_fst d hd), ← hsv d hd, hc₀ d (by simp [hf₀def, hd])]
    · rw [twist_of_fst_ne (hL₃_fst f hf d hd)]
      exact h.compat' (hL₃ f hf) hd
  have hM : ∀ f ∈ (((e, false) :: u) :: ((e, true) :: v) :: L₃), f.Nodup := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact List.nodup_cons.mpr ⟨hemu, (List.nodup_append.mp huv).1⟩
    rcases List.mem_cons.mp hf with rfl | hf
    · exact List.nodup_cons.mpr ⟨hepv, (List.nodup_cons.mp (List.nodup_append.mp huv).2.1).2⟩
    · exact h.face_nodup (hL₃ f hf)
  have hdel := faceCompat_delete hRn hcompat hM
  have hmap : ((((e, false) :: u) :: ((e, true) :: v) :: L₃).map
      fun f ↦ (f.erase (e, false)).erase (e, true)) = u :: v :: L₃ := by
    simp only [List.map_cons, List.erase_cons_head]
    rw [List.erase_of_not_mem hepu, List.erase_cons_tail (by simp), List.erase_of_not_mem hemv,
      List.erase_cons_head]
    congr 2
    conv_rhs => rw [← List.map_id L₃]
    refine List.map_congr_left fun f hf ↦ ?_
    rw [List.erase_of_not_mem (fun h' ↦ hdisj f hf _ h' hm),
      List.erase_of_not_mem (fun h' ↦ hdisj f hf _ h' hp), id]
  rw [hmap] at hdel
  -- the perm
  have hperm : (u :: v :: L₃).flatten.Perm (A ++ B) := by
    have h1 : (f₀ ++ L₃.flatten).Perm R := by
      have := (hL.flatten.symm.trans h.perm)
      rw [List.flatten_cons] at this
      exact (hrot.perm.append_right _).symm.trans this
    have h2 := h1.cons_inv
    have h3 : ((e, false) :: (u ++ (v ++ L₃.flatten))).Perm ((e, false) :: (A ++ B)) := by
      have e1 : u ++ (e, false) :: (v ++ L₃.flatten) = (u ++ (e, false) :: v) ++ L₃.flatten := by
        simp
      refine List.perm_middle.symm.trans ?_
      rw [e1]
      exact h2.trans List.perm_middle
    simpa using h3.cons_inv
  have h' : IsOneVertex (A ++ B) (u :: v :: L₃) := by
    refine ⟨hR'n, hR'flip, hperm, fun _ f hf ↦ ?_, fun hR' ↦ ?_, hdel⟩
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact hu
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hv
      · exact h.ne_nil (List.cons_ne_nil _ _) f (hL₃ f hf)
    · exfalso
      obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil u hu
      have := hperm.subset (List.mem_flatten_of_mem (List.mem_cons_self ..) hd)
      rw [hR'] at this
      simp at this
  obtain ⟨F', hs', hF', hconj', hsb', hcount'⟩ := ih _ h'
  -- the groups
  set base' := (edges (A ++ B)).map x
  have hbase : (edges R).map x = x e :: base' := by rw [hedges, List.map_cons]
  have hKK : spanOf base' ≤ spanOf ((edges R).map x) := by
    rw [hbase]
    exact spanOf_mono fun a ha ↦ List.mem_cons_of_mem _ ha
  have hlabel : ∀ d ∈ R, label x d ∈ spanOf ((edges R).map x) := fun d hd ↦
    label_mem_spanOf x h.flip_mem hd
  have hwf₀ : IsConjIn (spanOf ((edges R).map x)) (word x f₀) (word x f₁) :=
    isConjIn_word_of_isRotated x hrot.symm fun d hd ↦ hlabel d (h.mem_of_mem_face hf₁
      (hrot.mem_iff.mpr hd))
  have hword₀ : word x f₀ = x e * word x u * (x e)⁻¹ * word x v := by
    simp [hf₀def, mul_assoc]
  have hxe : x e ∈ spanOf ((edges R).map x) := by
    rw [hbase]
    exact mem_spanOf (List.mem_cons_self ..)
  have hwu : word x u ∈ spanOf base' := word_mem_spanOf x hR'flip fun d hd ↦
    h'.mem_of_mem_face (List.mem_cons_self ..) hd
  have hwv : word x v ∈ spanOf base' := word_mem_spanOf x hR'flip fun d hd ↦
    h'.mem_of_mem_face (List.mem_cons_of_mem _ (List.mem_cons_self ..)) hd
  have hcs' : ∀ c ∈ F'.map Prod.snd, c ∈ spanOf base' := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    obtain ⟨k, hk, hpk⟩ := hconj' p hp
    have hw : word x p.1 ∈ spanOf base' := word_mem_spanOf x hR'flip fun d hd ↦
      h'.mem_of_mem_face (hF'.subset (List.mem_map_of_mem hp)) hd
    rw [hpk]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hw) (Subgroup.inv_mem _ hk)
  have hprod : ∀ Y : List G, (∀ c ∈ Y, c ∈ spanOf base') → Y.prod ∈ spanOf base' :=
    fun Y hY ↦ list_prod_mem hY
  -- locate the faces `u` and `v`
  obtain ⟨F₁, cu, F₂, rfl⟩ := exists_eq_append_of_mem_map (hF'.mem_iff.mpr (List.mem_cons_self ..))
  have hF₁₂ : ((F₁ ++ F₂).map Prod.fst).Perm (v :: L₃) := by
    have h1 := hF'
    simp only [List.map_append, List.map_cons] at h1 ⊢
    exact (List.perm_middle.symm.trans h1).cons_inv
  obtain ⟨s', hs'K, hcu⟩ := hconj' (u, cu) (by simp)
  simp only at hcu
  subst hcu
  have hvF : v ∈ (F₁ ++ F₂).map Prod.fst := hF₁₂.mem_iff.mpr (List.mem_cons_self ..)
  rw [List.map_append, List.mem_append] at hvF
  rcases hvF with hvF | hvF
  · -- `v` before `u`
    obtain ⟨F₁₁, cv, F₁₂, rfl⟩ := exists_eq_append_of_mem_map hvF
    obtain ⟨r', hr'K, hcv⟩ := hconj' (v, cv) (by simp)
    simp only at hcv
    subst hcv
    have hsb'' : IsSurfaceBasis base' hs' (F₁₁.map Prod.snd ++ (r' * word x v * r'⁻¹) ::
        (F₁₂.map Prod.snd ++ (s' * word x u * s'⁻¹) :: F₂.map Prod.snd)) := by
      simpa using hsb'
    have hnew := hsb''.handle (e := x e) (ε := -1) (by norm_num) hr'K hs'K hwu
    set cf := (F₁₂.map Prod.snd).prod * s' *
      (word x u * x e ^ (-1 : ℤ) * word x v * x e ^ (-(-1 : ℤ))) * ((F₁₂.map Prod.snd).prod * s')⁻¹
    obtain ⟨hs₂, hlen, hnew⟩ : ∃ hs₂ : List (G × G), hs₂.length = hs'.length + 1 ∧
        IsSurfaceBasis (x e :: base') hs₂
          (F₁₁.map Prod.snd ++ cf :: (F₁₂.map Prod.snd ++ F₂.map Prod.snd)) := ⟨_, by simp, hnew⟩
    refine ⟨F₁₁ ++ (f₁, cf) :: (F₁₂ ++ F₂), hs₂, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_append, List.map_cons]
      refine List.perm_middle.trans ((List.Perm.cons _ ?_).trans hL.symm)
      have := hF₁₂
      simp only [List.map_append, List.map_cons, List.append_assoc] at this ⊢
      exact (List.perm_middle.symm.trans this).cons_inv
    · intro p hp
      simp only [List.mem_append, List.mem_cons] at hp
      rcases hp with hp | rfl | hp | hp
      · exact (hconj' p (by simp [hp])).mono hKK
      · refine IsConjIn.trans ?_ hwf₀
        refine ⟨(F₁₂.map Prod.snd).prod * s' * (x e)⁻¹, ?_, ?_⟩
        · exact Subgroup.mul_mem _ (hKK (Subgroup.mul_mem _ (hprod _ fun c hc ↦ hcs' c
            (by simp only [List.map_append, List.map_cons]; simp [hc])) hs'K))
            (Subgroup.inv_mem _ hxe)
        · rw [hword₀]
          simp only [cf]
          group
      · exact (hconj' p (by simp [hp])).mono hKK
      · exact (hconj' p (by simp [hp])).mono hKK
    · rw [hbase]
      simpa using hnew
    · simp only [List.length_append, List.length_cons] at hcount' ⊢
      rw [hedges, List.length_cons, hlen]
      omega
  · -- `u` before `v`
    obtain ⟨F₂₁, cv, F₂₂, rfl⟩ := exists_eq_append_of_mem_map hvF
    obtain ⟨r', hr'K, hcv⟩ := hconj' (v, cv) (by simp)
    simp only at hcv
    subst hcv
    have hsb'' : IsSurfaceBasis base' hs' (F₁.map Prod.snd ++ (s' * word x u * s'⁻¹) ::
        (F₂₁.map Prod.snd ++ (r' * word x v * r'⁻¹) :: F₂₂.map Prod.snd)) := by
      simpa using hsb'
    have hnew := hsb''.handle (e := x e) (ε := 1) (by norm_num) hs'K hr'K hwv
    set cf := (F₂₁.map Prod.snd).prod * r' *
      (word x v * x e ^ (1 : ℤ) * word x u * x e ^ (-(1 : ℤ))) * ((F₂₁.map Prod.snd).prod * r')⁻¹
    obtain ⟨hs₂, hlen, hnew⟩ : ∃ hs₂ : List (G × G), hs₂.length = hs'.length + 1 ∧
        IsSurfaceBasis (x e :: base') hs₂
          (F₁.map Prod.snd ++ cf :: (F₂₁.map Prod.snd ++ F₂₂.map Prod.snd)) := ⟨_, by simp, hnew⟩
    refine ⟨F₁ ++ (f₁, cf) :: (F₂₁ ++ F₂₂), hs₂, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_append, List.map_cons]
      refine List.perm_middle.trans ((List.Perm.cons _ ?_).trans hL.symm)
      have := hF₁₂
      simp only [List.map_append, List.map_cons] at this
      rw [← List.append_assoc] at this
      have h2 := (List.perm_middle.symm.trans this).cons_inv
      simpa using h2
    · intro p hp
      simp only [List.mem_append, List.mem_cons] at hp
      rcases hp with hp | rfl | hp | hp
      · exact (hconj' p (by simp [hp])).mono hKK
      · refine IsConjIn.trans ?_ hwf₀
        refine ⟨(F₂₁.map Prod.snd).prod * r' * word x v, ?_, ?_⟩
        · exact hKK (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hprod _ fun c hc ↦ hcs' c
            (by simp only [List.map_append, List.map_cons]; simp [hc])) hr'K) hwv)
        · rw [hword₀]
          simp only [cf]
          group
      · exact (hconj' p (by simp [hp])).mono hKK
      · exact (hconj' p (by simp [hp])).mono hKK
    · rw [hbase]
      simpa using hnew
    · simp only [List.length_append, List.length_cons] at hcount' ⊢
      rw [hedges, List.length_cons, hlen]
      omega


/-- In the rotation `(e, true) :: (A ++ (e, false) :: B)`, the successor of `(e, true)` is
`(e, false)` only if `A = []`, and the successor of `(e, false)` is `(e, true)` only if
`B = []`. -/
lemma formPerm_rest_eq (hR : ((e, true) :: (A ++ (e, false) :: B)).Nodup) :
    (((e, true) :: (A ++ (e, false) :: B)).formPerm (e, true) = (e, false) → A = []) ∧
      (((e, true) :: (A ++ (e, false) :: B)).formPerm (e, false) = (e, true) → B = []) := by
  obtain ⟨-, -, hsx, hsy⟩ := List.formPerm_splice hR
  have h1 := (List.nodup_cons.mp hR).1
  have h2 := List.nodup_append.mp (List.nodup_cons.mp hR).2
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [hsx] at h
    obtain _ | ⟨a, A'⟩ := A
    · rfl
    · have hnd : ((e, false) :: a :: A').Nodup := List.nodup_cons.mpr
        ⟨fun h' ↦ h2.2.2 _ h' _ (List.mem_cons_self ..) rfl, h2.1⟩
      rw [List.formPerm_apply_head _ _ _ hnd] at h
      exact absurd h (h2.2.2 a (List.mem_cons_self ..) _ (List.mem_cons_self ..))
  · rw [hsy] at h
    obtain _ | ⟨b, B'⟩ := B
    · rfl
    · have hnd : ((e, true) :: b :: B').Nodup := List.nodup_cons.mpr
        ⟨fun h' ↦ h1 (List.mem_append_right _ (List.mem_cons_of_mem _ h')),
          (List.nodup_cons.mp h2.2.1).2⟩
      rw [List.formPerm_apply_head _ _ _ hnd] at h
      exact absurd (h ▸ List.mem_cons_self ..)
        (fun h' ↦ h1 (List.mem_append_right _ (List.mem_cons_of_mem _ h')))

/-- **Induction step, the darts of `e` on different faces.** The faces `e u` and `e⁻¹ v` merge into
`u v`; its boundary element splits into two with the new generator
(`Nielsen.IsSurfaceBasis.split`). -/
lemma IsOneVertex.step_diff (h : IsOneVertex ((e, true) :: (A ++ (e, false) :: B)) L)
    (ih : ∀ L', IsOneVertex (A ++ B) L' → HasSurfaceBasis x (A ++ B) L')
    {f₁ f₂ : List (ι × Bool)} (hf₁ : f₁ ∈ L) (hf₂ : f₂ ∈ L) (hp : (e, true) ∈ f₁)
    (hm : (e, false) ∈ f₂) (hm₁ : (e, false) ∉ f₁) :
    HasSurfaceBasis x ((e, true) :: (A ++ (e, false) :: B)) L := by
  set R := (e, true) :: (A ++ (e, false) :: B) with hRdef
  obtain ⟨hR'n, hR'flip, hedges⟩ := h.rest
  have hRn := h.nodup
  obtain ⟨u, hu⟩ := List.exists_isRotated_cons hp
  obtain ⟨v, hv⟩ := List.exists_isRotated_cons hm
  have hf₁₂ : f₁ ≠ f₂ := fun h' ↦ hm₁ (h' ▸ hm)
  set L₃ := (L.erase f₁).erase f₂
  have hL : L.Perm (f₁ :: f₂ :: L₃) :=
    (List.perm_cons_erase hf₁).trans (List.Perm.cons _
      (List.perm_cons_erase (List.mem_erase_of_ne hf₁₂.symm |>.mpr hf₂)))
  have hL₃ : ∀ f ∈ L₃, f ∈ L := fun f hf ↦ List.mem_of_mem_erase (List.mem_of_mem_erase hf)
  have hflat : (f₁ ++ (f₂ ++ L₃.flatten)).Nodup := by
    have := h.flatten_nodup
    rwa [hL.flatten.nodup_iff, List.flatten_cons, List.flatten_cons] at this
  have hu' : ((e, true) :: u).Nodup := hu.nodup_iff.mp (h.face_nodup hf₁)
  have hv' : ((e, false) :: v).Nodup := hv.nodup_iff.mp (h.face_nodup hf₂)
  have hdisj12 : ∀ d ∈ f₁, d ∉ f₂ := fun d hd hd' ↦
    (List.nodup_append.mp hflat).2.2 d hd d (List.mem_append_left _ hd') rfl
  have hdisj3 : ∀ f ∈ L₃, ∀ d ∈ f, d ∉ f₁ ∧ d ∉ f₂ := fun f hf d hd ↦
    ⟨fun hd' ↦ (List.nodup_append.mp hflat).2.2 d hd' d
      (List.mem_append_right _ (List.mem_flatten_of_mem hf hd)) rfl,
     fun hd' ↦ (List.nodup_append.mp (List.nodup_append.mp hflat).2.1).2.2 d hd' d
      (List.mem_flatten_of_mem hf hd) rfl⟩
  have hepu : (e, true) ∉ u := (List.nodup_cons.mp hu').1
  have hemv : (e, false) ∉ v := (List.nodup_cons.mp hv').1
  have hemu : (e, false) ∉ u := fun h' ↦ hm₁ (hu.mem_iff.mpr (List.mem_cons_of_mem _ h'))
  have hepv : (e, true) ∉ v := fun h' ↦ hdisj12 _ hp (hv.mem_iff.mpr (List.mem_cons_of_mem _ h'))
  have hu_fst : ∀ d ∈ u, d.1 ≠ e := fun d hd ↦
    fst_ne_of_not_mem (fun h' ↦ hepu (h' ▸ hd)) (fun h' ↦ hemu (h' ▸ hd))
  have hv_fst : ∀ d ∈ v, d.1 ≠ e := fun d hd ↦
    fst_ne_of_not_mem (fun h' ↦ hepv (h' ▸ hd)) (fun h' ↦ hemv (h' ▸ hd))
  have hL₃_fst : ∀ f ∈ L₃, ∀ d ∈ f, d.1 ≠ e := fun f hf d hd ↦
    fst_ne_of_not_mem (fun h' ↦ (hdisj3 f hf d hd).1 (h' ▸ hp))
      (fun h' ↦ (hdisj3 f hf d hd).2 (h' ▸ hm))
  have huv : ∀ d ∈ u, d ∉ v := fun d hd hd' ↦ hdisj12 d (hu.mem_iff.mpr (List.mem_cons_of_mem _ hd))
    (hv.mem_iff.mpr (List.mem_cons_of_mem _ hd'))
  -- the merged face, with both darts of `e`
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
  have hc₁ : ∀ d ∈ (e, true) :: u, ((e, true) :: u).formPerm d = R.formPerm (flip d) :=
    fun d hd ↦ h.compat_of_isRotated hf₁ hu hd
  have hc₂ : ∀ d ∈ (e, false) :: v, ((e, false) :: v).formPerm d = R.formPerm (flip d) :=
    fun d hd ↦ h.compat_of_isRotated hf₂ hv hd
  have hcompat : FaceCompat (M :: L₃) [R] (twist e) := by
    intro f hf r hr d hd hβd
    rw [List.mem_singleton.mp hr]
    rcases List.mem_cons.mp hf with rfl | hf
    · rcases List.mem_cons.mp hd with rfl | hd
      · rw [twist_of_fst_eq (e := e) (d := (e, false)) rfl, hsx, hc₁ _ (List.mem_cons_self ..)]
        rfl
      rcases List.mem_append.mp hd with hd | hd
      · rw [twist_of_fst_ne (hu_fst d hd), hsu d hd, hc₁ d (List.mem_cons_of_mem _ hd)]
      rcases List.mem_cons.mp hd with rfl | hd
      · rw [twist_of_fst_eq (e := e) (d := (e, true)) rfl, hsy, hc₂ _ (List.mem_cons_self ..)]
        rfl
      · rw [twist_of_fst_ne (hv_fst d hd), hsv d hd, hc₂ d (List.mem_cons_of_mem _ hd)]
    · rw [twist_of_fst_ne (hL₃_fst f hf d hd)]
      exact h.compat' (hL₃ f hf) hd
  have hM : ∀ f ∈ M :: L₃, f.Nodup := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hMn
    · exact h.face_nodup (hL₃ f hf)
  have hdel := faceCompat_delete hRn hcompat hM
  have hmap : ((M :: L₃).map fun f ↦ (f.erase (e, false)).erase (e, true)) = (u ++ v) :: L₃ := by
    simp only [List.map_cons, hMdef, List.erase_cons_head]
    rw [List.erase_append_right _ hepu, List.erase_cons_head]
    congr 1
    conv_rhs => rw [← List.map_id L₃]
    refine List.map_congr_left fun f hf ↦ ?_
    rw [List.erase_of_not_mem (fun h' ↦ (hdisj3 f hf _ h').2 hm),
      List.erase_of_not_mem (fun h' ↦ (hdisj3 f hf _ h').1 hp), id]
  rw [hmap] at hdel
  -- the perm
  have hperm : ((u ++ v) :: L₃).flatten.Perm (A ++ B) := by
    have h1 : (((e, true) :: u) ++ (((e, false) :: v) ++ L₃.flatten)).Perm R := by
      have := (hL.flatten.symm.trans h.perm)
      rw [List.flatten_cons, List.flatten_cons] at this
      exact ((hu.perm.append (hv.perm.append_right _)).symm).trans this
    have h2 := h1.cons_inv
    have h3 : ((e, false) :: (u ++ (v ++ L₃.flatten))).Perm ((e, false) :: (A ++ B)) := by
      refine List.perm_middle.symm.trans ?_
      exact h2.trans List.perm_middle
    simpa using h3.cons_inv
  -- the faces `e u` and `e⁻¹ v` are not both trivial
  obtain ⟨hA, hB⟩ := formPerm_rest_eq hRn
  have hne : A ++ B ≠ [] → u ++ v ≠ [] := by
    intro hAB huv'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp huv'
    have h1 := hc₁ (e, true) (List.mem_cons_self ..)
    have h2 := hc₂ (e, false) (List.mem_cons_self ..)
    simp only [List.formPerm_singleton, Equiv.Perm.one_apply, flip, Bool.not_true,
      Bool.not_false] at h1 h2
    exact hAB (by rw [hA h2.symm, hB h1.symm]; rfl)
  have h' : IsOneVertex (A ++ B) ((u ++ v) :: L₃) := by
    refine ⟨hR'n, hR'flip, hperm, fun hR' f hf ↦ ?_, fun hR' ↦ ?_, hdel⟩
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact hne hR'
      · exact h.ne_nil (List.cons_ne_nil _ _) f (hL₃ f hf)
    · have hflat' := hperm
      rw [hR'] at hflat'
      have hnil := hflat'.eq_nil
      rw [List.flatten_cons, List.append_eq_nil_iff] at hnil
      obtain ⟨h₁, h₂⟩ := hnil
      rw [h₁]
      obtain _ | ⟨g, L₄⟩ := L₃
      · rfl
      · exfalso
        have hg : g ≠ [] := h.ne_nil (List.cons_ne_nil _ _) g (hL₃ g (List.mem_cons_self ..))
        exact hg (List.flatten_eq_nil_iff.mp h₂ g (List.mem_cons_self ..))
  obtain ⟨F', hs', hF', hconj', hsb', hcount'⟩ := ih _ h'
  -- the groups
  set base' := (edges (A ++ B)).map x
  have hbase : (edges R).map x = x e :: base' := by rw [hedges, List.map_cons]
  have hKK : spanOf base' ≤ spanOf ((edges R).map x) := by
    rw [hbase]
    exact spanOf_mono fun a ha ↦ List.mem_cons_of_mem _ ha
  have hlabel : ∀ d ∈ R, label x d ∈ spanOf ((edges R).map x) := fun d hd ↦
    label_mem_spanOf x h.flip_mem hd
  have hxe : x e ∈ spanOf ((edges R).map x) := by
    rw [hbase]
    exact mem_spanOf (List.mem_cons_self ..)
  have hwu : word x u ∈ spanOf base' := word_mem_spanOf x hR'flip fun d hd ↦
    h'.mem_of_mem_face (List.mem_cons_self ..) (List.mem_append_left _ hd)
  -- locate the face `u ++ v`
  obtain ⟨F₁, c, F₂, rfl⟩ :=
    exists_eq_append_of_mem_map (hF'.mem_iff.mpr (List.mem_cons_self ..))
  have hF₁₂ : ((F₁ ++ F₂).map Prod.fst).Perm L₃ := by
    have h1 := hF'
    simp only [List.map_append, List.map_cons] at h1 ⊢
    exact (List.perm_middle.symm.trans h1).cons_inv
  obtain ⟨s', hs'K, hc⟩ := hconj' (u ++ v, c) (by simp)
  simp only at hc
  have hsb'' : IsSurfaceBasis base' hs' (F₁.map Prod.snd ++ c :: F₂.map Prod.snd) := by
    simpa using hsb'
  have hnew := hsb''.split (s := s') (u := word x u) (v := word x v) (e := x e)
    (by rw [hc, word_append]) hs'K hwu
  refine ⟨F₁ ++ (f₁, s' * (word x u * x e) * s'⁻¹) :: (f₂, s' * ((x e)⁻¹ * word x v) * s'⁻¹) ::
    F₂, hs', ?_, ?_, ?_, ?_⟩
  · simp only [List.map_append, List.map_cons]
    exact List.perm_middle.trans ((List.Perm.cons _ (List.perm_middle.trans
      (List.Perm.cons _ (by simpa using hF₁₂)))).trans hL.symm)
  · intro p hp
    simp only [List.mem_append, List.mem_cons] at hp
    rcases hp with hp | rfl | rfl | hp
    · exact (hconj' p (by simp [hp])).mono hKK
    · refine IsConjIn.trans ?_ (isConjIn_word_of_isRotated x hu.symm fun d hd ↦
        hlabel d (h.mem_of_mem_face hf₁ (hu.mem_iff.mpr hd)))
      refine ⟨s' * (x e)⁻¹, Subgroup.mul_mem _ (hKK hs'K) (Subgroup.inv_mem _ hxe), ?_⟩
      simp only [word_cons, label_true]
      group
    · refine IsConjIn.trans ?_ (isConjIn_word_of_isRotated x hv.symm fun d hd ↦
        hlabel d (h.mem_of_mem_face hf₂ (hv.mem_iff.mpr hd)))
      refine ⟨s', hKK hs'K, ?_⟩
      simp only [word_cons, label_false]
    · exact (hconj' p (by simp [hp])).mono hKK
  · rw [hbase]
    simpa using hnew
  · simp only [List.length_append, List.length_cons] at hcount' ⊢
    rw [hedges, List.length_cons]
    omega

/-- **Classification of one-vertex ribbon graphs, on the level of groups.** For a one-vertex ribbon
graph `(R, L)` and any labels `x : ι → G`, the group spanned by the labels of the edges has a
surface basis whose boundary elements are conjugate (in that group) to the face words, one for each
face, with `2g + #faces = #edges + 1` (`Ribbon.HasSurfaceBasis`). -/
theorem IsOneVertex.hasSurfaceBasis (x : ι → G) {R : List (ι × Bool)}
    {L : List (List (ι × Bool))} (h : IsOneVertex R L) : HasSurfaceBasis x R L := by
  induction hn : R.length using Nat.strong_induction_on generalizing R L with
  | _ n ih =>
  obtain _ | ⟨d, R₀⟩ := R
  · rw [h.nil rfl]
    refine ⟨[([], 1)], [], by simp, fun p hp ↦ ?_, ⟨by simp [handleProd], [], 1, [], rfl, ?_⟩,
      by simp [edges]⟩
    · rw [List.mem_singleton.mp hp]
      exact IsConjIn.refl _ _
    · exact Interchangeable.refl _
  set R := d :: R₀ with hRdef
  -- a positive dart
  have hpos : ∃ e, (e, true) ∈ R := by
    obtain ⟨i, b⟩ := d
    cases b
    · exact ⟨i, h.flip_mem _ (List.mem_cons_self ..)⟩
    · exact ⟨i, List.mem_cons_self ..⟩
  obtain ⟨e, he⟩ := hpos
  have he' : (e, false) ∈ R := h.flip_mem _ he
  obtain ⟨A, B, hrot⟩ := List.exists_isRotated_cons_append he he' (by simp)
  have h₁ := h.of_isRotated hrot
  refine HasSurfaceBasis.of_perm ?_ hrot.perm.symm
  have hlen : (A ++ B).length < n := by
    rw [← hn, hrot.perm.length_eq]
    simp only [List.length_append, List.length_cons]
    omega
  have ih' : ∀ L', IsOneVertex (A ++ B) L' → HasSurfaceBasis x (A ++ B) L' :=
    fun L' h' ↦ ih _ hlen h' rfl
  obtain ⟨f₁, hf₁, hp⟩ := List.mem_flatten.mp (h₁.perm.mem_iff.mpr (List.mem_cons_self ..))
  obtain ⟨f₂, hf₂, hm⟩ := List.mem_flatten.mp (h₁.perm.mem_iff.mpr
    (show (e, false) ∈ (e, true) :: (A ++ (e, false) :: B) by simp))
  by_cases hm₁ : (e, false) ∈ f₁
  · exact h₁.step_same ih' hf₁ hp hm₁
  · exact h₁.step_diff ih' hf₁ hf₂ hp hm hm₁

end Step

end Ribbon
