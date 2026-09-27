/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.InvertibleSheaf
import SGA.Foundations.Projective.LineBundle

/-!
# Extension of sections of powers of a line bundle

Let `L` be a line bundle on a scheme `X`, given by a trivializing cover `(Uᵢ)` and transition
units `gᵢⱼ`. A section of `L^{⊗n}` over an open `V` is a family `sᵢ ∈ Γ(V ∩ Uᵢ, 𝒪_X)` with
`sᵢ = gᵢⱼⁿ sⱼ` (`Scheme.LineBundle.IsSection`). All these families live in the ring
`L.Fam V = ∏ᵢ Γ(V ∩ Uᵢ, 𝒪_X)`, in which sections of different degrees can be multiplied.

We prove the extension lemma EGA I 9.3.1 for the powers of `L`: if `U` is quasi-compact and
quasi-separated, `s` is a section of `L^{⊗d}` over `U` and `t` a section of `L^{⊗m}` over the
non-vanishing locus `U_s`, then `sᵏ t` extends to a section of `L^{⊗(m + kd)}` over `U` for
some `k` (`Scheme.LineBundle.exists_isSection_famRes_eq`); and if `U` is quasi-compact, a section
over `U` vanishing on `U_s` is killed by a power of `s`
(`Scheme.LineBundle.exists_pow_mul_eq_zero`).
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.LineBundle

variable {X : Scheme.{u}} (L : X.LineBundle)

/-- The ring `∏ᵢ Γ(V ∩ Uᵢ, 𝒪_X)` containing the sections of all powers of `L` over `V`. -/
abbrev Fam (V : X.Opens) : Type u :=
  ∀ i, Γ(X, V ⊓ L.U i)

variable {L}

section Fam

variable {V V' V'' : X.Opens}

variable (L) in
/-- Restriction of families from `V` to `V' ≤ V`. -/
noncomputable def famRes (h : V' ≤ V) : L.Fam V →+* L.Fam V' :=
  RingHom.pi fun i ↦ (X.presheaf.map (homOfLE (inf_le_inf_right (L.U i) h)).op).hom.comp
    (Pi.evalRingHom _ i)

lemma famRes_apply (h : V' ≤ V) (s : L.Fam V) (i : L.ι) :
    L.famRes h s i = X.presheaf.map (homOfLE (inf_le_inf_right (L.U i) h)).op (s i) :=
  rfl

lemma famRes_famRes (h : V' ≤ V) (h' : V'' ≤ V') (s : L.Fam V) :
    L.famRes h' (L.famRes h s) = L.famRes (h'.trans h) s := by
  funext i
  simp only [famRes_apply, CohomologyAux.presheaf_map_map]

@[simp]
lemma famRes_self (h : V ≤ V) (s : L.Fam V) : L.famRes h s = s := by
  funext i
  simp only [famRes_apply, CohomologyAux.presheaf_map_self]

variable (L) in
/-- The family of restrictions of a function on `V`. -/
noncomputable def famConst (V : X.Opens) : Γ(X, V) →+* L.Fam V :=
  RingHom.pi fun i ↦ (X.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op).hom

lemma famConst_apply (r : Γ(X, V)) (i : L.ι) :
    L.famConst V r i = X.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op r :=
  rfl

lemma famRes_famConst (h : V' ≤ V) (r : Γ(X, V)) :
    L.famRes h (L.famConst V r) = L.famConst V' (X.presheaf.map (homOfLE h).op r) := by
  funext i
  simp only [famRes_apply, famConst_apply, CohomologyAux.presheaf_map_map]

lemma trans_add (a b : ℤ) (i j : L.ι) : L.trans (a + b) i j = L.trans a i j * L.trans b i j := by
  simp only [trans, zpow_add, Units.val_mul]

lemma trans_zero (i j : L.ι) : L.trans 0 i j = 1 := by
  simp only [trans, zpow_zero, Units.val_one]

lemma IsSection.mul {a b : ℤ} {s t : L.Fam V} (hs : L.IsSection a V s) (ht : L.IsSection b V t) :
    L.IsSection (a + b) V (s * t) := by
  intro i j
  simp only [Pi.mul_apply, map_mul, hs i j, ht i j, trans_add]
  ring

lemma IsSection.pow {a : ℤ} {s : L.Fam V} (hs : L.IsSection a V s) (k : ℕ) :
    L.IsSection (k * a) V (s ^ k) := by
  induction k with
  | zero =>
    intro i j
    simp [trans_zero]
  | succ k ih =>
    rw [pow_succ]
    convert ih.mul hs using 1
    push_cast
    ring

lemma IsSection.famRes {n : ℤ} {s : L.Fam V} (hs : L.IsSection n V s) (h : V' ≤ V) :
    L.IsSection n V' (L.famRes h s) :=
  (L.resHom n h ⟨s, hs⟩).2

lemma IsSection.sub {n : ℤ} {s t : L.Fam V} (hs : L.IsSection n V s) (ht : L.IsSection n V t) :
    L.IsSection n V (s - t) :=
  (L.sectionsAddSubgroup n V).sub_mem hs ht

lemma isSection_zero (n : ℤ) : L.IsSection n V 0 :=
  (L.sectionsAddSubgroup n V).zero_mem

lemma isSection_famConst (r : Γ(X, V)) : L.IsSection 0 V (L.famConst V r) := by
  intro i j
  simp only [famConst_apply, trans_zero, map_one, one_mul, CohomologyAux.presheaf_map_map]

lemma IsSection.of_eq {m n : ℤ} {s : L.Fam V} (hs : L.IsSection m V s) (h : m = n) :
    L.IsSection n V s :=
  h ▸ hs

end Fam

section Locus

variable {V V' : X.Opens}

variable (L) in
/-- The non-vanishing locus `⋃ᵢ D(sᵢ)` of a family `s`. -/
def famLocus (V : X.Opens) (s : L.Fam V) : X.Opens :=
  ⨆ i, X.basicOpen (s i)

lemma famLocus_le (s : L.Fam V) : L.famLocus V s ≤ V :=
  iSup_le fun _ ↦ (X.basicOpen_le _).trans inf_le_left

lemma famLocus_famRes (h : V' ≤ V) (s : L.Fam V) :
    L.famLocus V' (L.famRes h s) = V' ⊓ L.famLocus V s := by
  simp only [famLocus, famRes_apply, Scheme.basicOpen_res, inf_iSup_eq]
  refine iSup_congr fun i ↦ ?_
  exact le_antisymm (inf_le_inf_right _ inf_le_left)
    (le_inf (le_inf inf_le_left (inf_le_right.trans ((X.basicOpen_le _).trans inf_le_right)))
      inf_le_right)

lemma famLocus_famConst (r : Γ(X, V)) : L.famLocus V (L.famConst V r) = X.basicOpen r := by
  simp only [famLocus, famConst_apply, Scheme.basicOpen_res, ← iSup_inf_eq]
  refine le_antisymm inf_le_right (le_inf ?_ le_rfl)
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (L.iSup_eq_top.ge (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨i, ⟨X.basicOpen_le r hx, hi⟩⟩

lemma basicOpen_inf_U {n : ℤ} {s : L.Fam V} (hs : L.IsSection n V s) (i j : L.ι) :
    X.basicOpen (s i) ⊓ L.U j ≤ X.basicOpen (s j) := by
  intro x ⟨hx, hxj⟩
  have hxV : x ∈ V ⊓ (L.U i ⊓ L.U j) :=
    ⟨((X.basicOpen_le _).trans inf_le_left) hx,
      ((X.basicOpen_le _).trans inf_le_right) hx, hxj⟩
  have h := congrArg X.basicOpen (hs i j)
  simp only [Scheme.basicOpen_mul, Scheme.basicOpen_res] at h
  rw [show X.basicOpen (L.trans n i j) = L.U i ⊓ L.U j from
    X.basicOpen_of_isUnit (Units.isUnit _)] at h
  have : x ∈ V ⊓ (L.U i ⊓ L.U j) ⊓ X.basicOpen (s i) := ⟨hxV, hx⟩
  rw [h] at this
  exact this.2.2

lemma famLocus_inf_U {n : ℤ} {s : L.Fam V} (hs : L.IsSection n V s) (i : L.ι) :
    L.famLocus V s ⊓ L.U i = X.basicOpen (s i) := by
  refine le_antisymm ?_ ?_
  · rw [famLocus, iSup_inf_eq]
    exact iSup_le fun j ↦ basicOpen_inf_U hs j i
  · exact le_inf (le_iSup (fun j ↦ X.basicOpen (s j)) i)
      ((X.basicOpen_le _).trans inf_le_right)

lemma mem_famLocus_iff {n : ℤ} {s : L.Fam V} (hs : L.IsSection n V s) {i : L.ι} {x : X}
    (hx : x ∈ L.U i) : x ∈ L.famLocus V s ↔ x ∈ X.basicOpen (s i) := by
  rw [← famLocus_inf_U hs i]
  exact ⟨fun h ↦ ⟨h, hx⟩, fun h ↦ h.1⟩

lemma famLocus_mul {b : ℤ} (s : L.Fam V) {t : L.Fam V} (ht : L.IsSection b V t) :
    L.famLocus V (s * t) = L.famLocus V s ⊓ L.famLocus V t := by
  ext x
  simp only [famLocus, Pi.mul_apply, Scheme.basicOpen_mul, Opens.coe_inf, Set.mem_inter_iff,
    SetLike.mem_coe]
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨Opens.mem_iSup.mpr ⟨i, hi.1⟩, Opens.mem_iSup.mpr ⟨i, hi.2⟩⟩
  · rintro ⟨hx, hx'⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have hxi : x ∈ L.U i := ((X.basicOpen_le _).trans inf_le_right) hi
    exact Opens.mem_iSup.mpr ⟨i, hi, (mem_famLocus_iff ht hxi).mp hx'⟩

lemma famLocus_pow (s : L.Fam V) {k : ℕ} (hk : 0 < k) :
    L.famLocus V (s ^ k) = L.famLocus V s := by
  simp only [famLocus, Pi.pow_apply, Scheme.basicOpen_pow _ _ hk]

@[simp]
lemma famLocus_zero : L.famLocus V (0 : L.Fam V) = ⊥ := by
  simp only [famLocus, Pi.zero_apply, Scheme.basicOpen_zero, iSup_bot]

lemma famLocus_add_le (s t : L.Fam V) :
    L.famLocus V (s + t) ≤ L.famLocus V s ⊔ L.famLocus V t := by
  simp only [famLocus, Pi.add_apply]
  refine iSup_le fun i ↦ (Scheme.basicOpen_add_le ..).trans ?_
  exact sup_le_sup (le_iSup (fun i ↦ X.basicOpen (s i)) i) (le_iSup (fun i ↦ X.basicOpen (t i)) i)

lemma famLocus_le_famLocus_pow (s : L.Fam V) (k : ℕ) : L.famLocus V s ≤ L.famLocus V (s ^ k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, famLocus, Pi.one_apply, Scheme.basicOpen_one]
    exact iSup_mono fun i ↦ X.basicOpen_le _
  · exact (famLocus_pow s hk).ge

lemma famLocus_famRes_self (s : L.Fam V) :
    L.famLocus _ (L.famRes (famLocus_le s) s) = L.famLocus V s := by
  rw [famLocus_famRes, inf_idem]

end Locus

section Trivial

variable {V V' : X.Opens} (k : L.ι)

variable (L) in
/-- On an open `V ⊆ Uₖ`, the `k`-th component of a family, as a function on `V`. -/
noncomputable def famUnit (hV : V ≤ L.U k) : L.Fam V →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE (le_inf le_rfl hV : V ≤ V ⊓ L.U k)).op).hom.comp (Pi.evalRingHom _ k)

lemma famUnit_apply (hV : V ≤ L.U k) (s : L.Fam V) :
    L.famUnit k hV s = X.presheaf.map (homOfLE (le_inf le_rfl hV : V ≤ V ⊓ L.U k)).op (s k) :=
  rfl

lemma famUnit_famRes (h : V' ≤ V) (hV : V ≤ L.U k) (s : L.Fam V) :
    L.famUnit k (h.trans hV) (L.famRes h s) = X.presheaf.map (homOfLE h).op (L.famUnit k hV s) := by
  simp only [famUnit_apply, famRes_apply, CohomologyAux.presheaf_map_map]

lemma IsSection.ext_famUnit {n : ℤ} {s t : L.Fam V} (hs : L.IsSection n V s)
    (ht : L.IsSection n V t) (hV : V ≤ L.U k) (h : L.famUnit k hV s = L.famUnit k hV t) :
    s = t := by
  have hs' := L.ofUnit_toUnit k hV ⟨s, hs⟩
  have ht' := L.ofUnit_toUnit k hV ⟨t, ht⟩
  have : L.toUnit k hV ⟨s, hs⟩ = L.toUnit k hV ⟨t, ht⟩ := h
  rw [this] at hs'
  exact congrArg Subtype.val (hs'.symm.trans ht')

lemma exists_isSection_famUnit_eq (n : ℤ) (hV : V ≤ L.U k) (y : Γ(X, V)) :
    ∃ s : L.Fam V, L.IsSection n V s ∧ L.famUnit k hV s = y :=
  ⟨(L.ofUnit n k hV y).1, (L.ofUnit n k hV y).2, L.toUnit_ofUnit k hV y⟩

lemma famLocus_eq_basicOpen_famUnit {n : ℤ} {s : L.Fam V} (hs : L.IsSection n V s)
    (hV : V ≤ L.U k) : L.famLocus V s = X.basicOpen (L.famUnit k hV s) := by
  rw [famUnit_apply, Scheme.basicOpen_res, ← famLocus_inf_U hs k,
    inf_eq_left.mpr ((famLocus_le s).trans hV), inf_eq_right.mpr (famLocus_le s)]

end Trivial

section Glue

variable {U : X.Opens} {ι' : Type*} (W : ι' → X.Opens) (hW : ∀ a, W a ≤ U)
  (hcov : U ≤ ⨆ a, W a)
include hcov

/-- Families over `U` agreeing on an open cover are equal. -/
lemma famRes_injective {s t : L.Fam U} (h : ∀ a, L.famRes (hW a) s = L.famRes (hW a) t) :
    s = t := by
  funext i
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun a ↦ W a ⊓ L.U i) (U ⊓ L.U i)
    (fun a ↦ homOfLE (inf_le_inf_right _ (hW a))) ?_ _ _ fun a ↦ congrFun (h a) i
  rw [← iSup_inf_eq]
  exact inf_le_inf_right _ hcov

/-- Compatible sections of `L^{⊗n}` over an open cover glue. -/
lemma exists_isSection_glue {n : ℤ} (sf : ∀ a, L.Fam (W a))
    (hsf : ∀ a, L.IsSection n (W a) (sf a))
    (hcomp : ∀ a b, L.famRes (inf_le_left : W a ⊓ W b ≤ W a) (sf a) =
      L.famRes (inf_le_right : W a ⊓ W b ≤ W b) (sf b)) :
    ∃ s : L.Fam U, L.IsSection n U s ∧ ∀ a, L.famRes (hW a) s = sf a := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨L.sectionsPresheaf n, L.isSheaf_sectionsPresheaf n⟩
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' F W U (fun a ↦ homOfLE (hW a)) hcov
    (fun a ↦ (⟨sf a, hsf a⟩ : L.sectionsAddSubgroup n (W a))) (fun a b ↦ Subtype.ext (hcomp a b))
  exact ⟨s.1, s.2, fun a ↦ congrArg Subtype.val (hs a)⟩

end Glue

variable (L) in
/-- A quasi-compact open subset is covered by finitely many affine open subsets on which `L` is
trivial. -/
lemma exists_finite_cover {U : X.Opens} (hU : IsCompact (U : Set X)) :
    ∃ (ι' : Type u) (_ : Finite ι') (W : ι' → X.Opens) (k : ι' → L.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ L.U (k a)) ∧ (∀ a, W a ≤ U) ∧ U ≤ ⨆ a, W a := by
  have H (x : U) : ∃ (k : L.ι) (W : X.Opens), IsAffineOpen W ∧ x.1 ∈ W ∧ W ≤ U ⊓ L.U k := by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (L.iSup_eq_top.ge (Set.mem_univ x.1))
    obtain ⟨W, hW, hxW, hWle⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x.1 ∈ U ⊓ L.U k from ⟨x.2, hk⟩)
    exact ⟨k, W, hW, hxW, hWle⟩
  choose k W hWa hxW hWle using H
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : U ↦ (W x : Set X)) (fun x ↦ (W x).2)
    fun y hy ↦ Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxW _⟩
  refine ⟨t, inferInstance, fun a ↦ W a.1, fun a ↦ k a.1, fun a ↦ hWa a.1,
    fun a ↦ (hWle a.1).trans inf_le_right, fun a ↦ (hWle a.1).trans inf_le_left, fun y hy ↦ ?_⟩
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨ha, rfl⟩, hya⟩ := ht hy
  exact Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hya⟩

/-- EGA I 9.3.1 (ii) for the powers of a line bundle: over a quasi-compact open `U`, a section `t`
of `L^{⊗m}` vanishing on the non-vanishing locus of a section `s` of `L^{⊗d}` is killed by a power
of `s`. -/
theorem exists_pow_mul_eq_zero {U : X.Opens} (hU : IsCompact (U : Set X)) {d m : ℤ}
    {s t : L.Fam U} (hs : L.IsSection d U s) (ht : L.IsSection m U t)
    (h0 : L.famRes (famLocus_le s) t = 0) : ∃ k : ℕ, s ^ k * t = 0 := by
  obtain ⟨ι', _, W, k, hWa, hWk, hWU, hcov⟩ := L.exists_finite_cover hU
  have key (a : ι') : ∃ N : ℕ, L.famRes (hWU a) (s ^ N * t) = 0 := by
    have hD : X.basicOpen (L.famUnit (k a) (hWk a) (L.famRes (hWU a) s)) =
        W a ⊓ L.famLocus U s := by
      rw [← famLocus_eq_basicOpen_famUnit _ (hs.famRes _), famLocus_famRes]
    have hle : X.basicOpen (L.famUnit (k a) (hWk a) (L.famRes (hWU a) s)) ≤ L.famLocus U s :=
      hD.le.trans inf_le_right
    have hτ : X.presheaf.map (homOfLE (X.basicOpen_le
        (L.famUnit (k a) (hWk a) (L.famRes (hWU a) s)))).op
        (L.famUnit (k a) (hWk a) (L.famRes (hWU a) t)) = 0 := by
      rw [← famUnit_famRes, famRes_famRes, ← famRes_famRes (famLocus_le s) hle, h0, map_zero,
        map_zero]
    obtain ⟨N, hN⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (hWa a)
      _ _ hτ
    refine ⟨N, ((hs.pow N).mul ht).famRes (hWU a) |>.ext_famUnit (k a)
      (isSection_zero _) (hWk a) ?_⟩
    rw [map_mul, map_pow, map_mul, map_pow, map_zero]
    exact hN
  choose N hN using key
  have := Fintype.ofFinite ι'
  refine ⟨Finset.univ.sup N, famRes_injective W hWU hcov fun a ↦ ?_⟩
  have e : s ^ Finset.univ.sup N * t = s ^ (Finset.univ.sup N - N a) * (s ^ N a * t) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ a))]
  rw [e, map_mul, hN a, mul_zero, map_zero]

/-- EGA I 9.3.1 (i) for the powers of a line bundle: let `U` be quasi-compact and
quasi-separated, `s` a section of `L^{⊗d}` over `U` and `t` a section of `L^{⊗m}` over the
non-vanishing locus `U_s`. Then for some `k`, `sᵏ t` is the restriction of a section of
`L^{⊗(m + kd)}` over `U`. -/
theorem exists_isSection_famRes_eq {U : X.Opens} (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) {d m : ℤ} {s : L.Fam U} (hs : L.IsSection d U s)
    {t : L.Fam (L.famLocus U s)} (ht : L.IsSection m _ t) :
    ∃ (k : ℕ) (y : L.Fam U), L.IsSection (m + k * d) U y ∧
      L.famRes (famLocus_le s) y = L.famRes (famLocus_le s) s ^ k * t := by
  obtain ⟨ι', _, W, k, hWa, hWk, hWU, hcov⟩ := L.exists_finite_cover hU
  have := Fintype.ofFinite ι'
  let f (a : ι') : Γ(X, W a) := L.famUnit (k a) (hWk a) (L.famRes (hWU a) s)
  have hD (a : ι') : X.basicOpen (f a) = W a ⊓ L.famLocus U s := by
    rw [← famLocus_eq_basicOpen_famUnit _ (hs.famRes _), famLocus_famRes]
  have hle (a : ι') : X.basicOpen (f a) ≤ L.famLocus U s := (hD a).le.trans inf_le_right
  -- Local extensions on the affine opens `W a`.
  have loc (a : ι') : ∃ (N : ℕ) (Y : L.Fam (W a)), L.IsSection (m + N * d) (W a) Y ∧
      L.famRes (X.basicOpen_le (f a)) Y =
        L.famRes ((X.basicOpen_le (f a)).trans (hWU a)) s ^ N * L.famRes (hle a) t := by
    obtain ⟨N, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X (W a) (hWa a) (f a)
      (L.famUnit (k a) ((X.basicOpen_le (f a)).trans (hWk a)) (L.famRes (hle a) t))
    obtain ⟨Y, hY, hYy⟩ := L.exists_isSection_famUnit_eq (k a) (m + N * d) (hWk a) y
    refine ⟨N, Y, hY, (hY.famRes (X.basicOpen_le (f a))).ext_famUnit (k a)
      ((((hs.famRes _).pow N).mul (ht.famRes (hle a))).of_eq (by ring))
      ((X.basicOpen_le (f a)).trans (hWk a)) ?_⟩
    rw [famUnit_famRes (k a) (X.basicOpen_le (f a)) (hWk a), hYy, map_mul, map_pow,
      ← famRes_famRes (hWU a) (X.basicOpen_le (f a)),
      famUnit_famRes (k a) (X.basicOpen_le (f a)) (hWk a)]
    exact hy
  choose N Y hY hYt using loc
  set K := Finset.univ.sup N
  let Y' (a : ι') : L.Fam (W a) := L.famRes (hWU a) s ^ (K - N a) * Y a
  have hY' (a : ι') : L.IsSection (m + K * d) (W a) (Y' a) :=
    (((hs.famRes (hWU a)).pow (K - N a)).mul (hY a)).of_eq (by
      rw [Nat.cast_sub (Finset.le_sup (Finset.mem_univ a))]
      ring)
  have hY't (a : ι') : L.famRes (X.basicOpen_le (f a)) (Y' a) =
      L.famRes ((X.basicOpen_le (f a)).trans (hWU a)) s ^ K * L.famRes (hle a) t := by
    rw [map_mul, hYt, map_pow, famRes_famRes, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ a))]
  -- The local extensions agree on `W a ⊓ W b` after multiplication by a power of `s`.
  have comp (a b : ι') : ∃ M : ℕ, L.famRes (inf_le_left.trans (hWU a) : W a ⊓ W b ≤ U) s ^ M *
      (L.famRes inf_le_left (Y' a) - L.famRes inf_le_right (Y' b)) = 0 := by
    have hs' := hs.famRes (inf_le_left.trans (hWU a) : W a ⊓ W b ≤ U)
    have hloc : L.famLocus _ (L.famRes (inf_le_left.trans (hWU a) : W a ⊓ W b ≤ U) s) =
        W a ⊓ W b ⊓ L.famLocus U s := famLocus_famRes _ _
    have ha : L.famLocus _ (L.famRes (inf_le_left.trans (hWU a) : W a ⊓ W b ≤ U) s) ≤
        X.basicOpen (f a) := by
      rw [hloc, hD]
      exact inf_le_inf_right _ inf_le_left
    have hb : L.famLocus _ (L.famRes (inf_le_left.trans (hWU a) : W a ⊓ W b ≤ U) s) ≤
        X.basicOpen (f b) := by
      rw [hloc, hD]
      exact inf_le_inf_right _ inf_le_right
    refine exists_pow_mul_eq_zero (hU' _ _ (hWU a) (W a).2 (hWa a).isCompact (hWU b) (W b).2
      (hWa b).isCompact) hs' (((hY' a).famRes _).sub ((hY' b).famRes _)) ?_
    rw [map_sub, famRes_famRes, famRes_famRes, ← famRes_famRes (X.basicOpen_le (f a)) ha,
      ← famRes_famRes (X.basicOpen_le (f b)) hb, hY't, hY't, sub_eq_zero, map_mul, map_mul,
      map_pow, map_pow, famRes_famRes, famRes_famRes, famRes_famRes, famRes_famRes]
  choose M hM using comp
  set K' := Finset.univ.sup fun p : ι' × ι' ↦ M p.1 p.2
  let Z (a : ι') : L.Fam (W a) := L.famRes (hWU a) s ^ K' * Y' a
  have hZ (a : ι') : L.IsSection (K' * d + (m + K * d)) (W a) (Z a) :=
    ((hs.famRes (hWU a)).pow K').mul (hY' a)
  obtain ⟨y, hy, hyZ⟩ := exists_isSection_glue W hWU hcov Z hZ fun a b ↦ by
    rw [← sub_eq_zero]
    have hle' : M a b ≤ K' := Finset.le_sup (f := fun p : ι' × ι' ↦ M p.1 p.2)
      (Finset.mem_univ (a, b))
    have e : L.famRes (inf_le_left : W a ⊓ W b ≤ W a) (Z a) -
        L.famRes (inf_le_right : W a ⊓ W b ≤ W b) (Z b) =
        L.famRes (inf_le_left.trans (hWU a) : W a ⊓ W b ≤ U) s ^ (K' - M a b) *
          (L.famRes (inf_le_left.trans (hWU a) : W a ⊓ W b ≤ U) s ^ M a b *
            (L.famRes inf_le_left (Y' a) - L.famRes inf_le_right (Y' b))) := by
      simp only [Z, map_mul, map_pow, famRes_famRes]
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle', mul_sub]
    rw [e, hM, mul_zero]
  refine ⟨K + K', y, hy.of_eq (by push_cast; ring), ?_⟩
  refine famRes_injective (fun a ↦ X.basicOpen (f a)) hle ?_ fun a ↦ ?_
  · intro x hx
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (hcov (famLocus_le s hx))
    exact Opens.mem_iSup.mpr ⟨a, by rw [hD]; exact ⟨ha, hx⟩⟩
  · rw [famRes_famRes, ← famRes_famRes (hWU a) (X.basicOpen_le (f a)), hyZ]
    change L.famRes _ (L.famRes (hWU a) s ^ K' * Y' a) = _
    rw [map_mul, map_pow, hY't, famRes_famRes, map_mul, map_pow, famRes_famRes, pow_add]
    ring

section Global

variable {n : ℕ}

lemma trans_natCast (i j : L.ι) : L.trans (n : ℤ) i j = (L.g i j : Γ(X, L.U i ⊓ L.U j)) ^ n := by
  simp only [trans, zpow_natCast, Units.val_pow_eq_pow_val]

/-- A global section of `L^{⊗n}`, as a family over `⊤`. -/
noncomputable def sections.toFam (s : L.sections n) : L.Fam ⊤ :=
  fun i ↦ X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ L.U i ≤ L.U i)).op (s.1 i)

lemma sections.isSection_toFam (s : L.sections n) : L.IsSection n ⊤ s.toFam := by
  intro i j
  have h := congrArg (X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ (L.U i ⊓ L.U j) ≤
    L.U i ⊓ L.U j)).op) (s.2 i j)
  simp only [map_mul, map_pow, CohomologyAux.presheaf_map_map] at h
  simp only [sections.toFam, CohomologyAux.presheaf_map_map, trans_natCast, map_pow]
  exact h

lemma sections.famLocus_toFam (s : L.sections n) :
    L.famLocus ⊤ s.toFam = L.nonvanishingLocus s := by
  simp only [famLocus, nonvanishingLocus, sections.toFam, Scheme.basicOpen_res]
  refine iSup_congr fun i ↦ inf_eq_right.mpr ?_
  exact le_inf le_top (X.basicOpen_le _)

variable (L) in
/-- A family over `⊤` which is a section of `L^{⊗n}`, as a global section. -/
noncomputable def sectionsOfFam (s : L.Fam ⊤) (hs : L.IsSection n ⊤ s) : L.sections n :=
  ⟨fun i ↦ X.presheaf.map (homOfLE (le_inf le_top le_rfl : L.U i ≤ ⊤ ⊓ L.U i)).op (s i),
    fun i j ↦ by
      apply CohomologyAux.presheaf_map_injective_of_eq
        (show ⊤ ⊓ (L.U i ⊓ L.U j) = L.U i ⊓ L.U j from top_inf_eq _)
      have h := hs i j
      simp only [map_mul, map_pow, CohomologyAux.presheaf_map_map, trans_natCast] at h ⊢
      exact h⟩

lemma nonvanishingLocus_sectionsOfFam (s : L.Fam ⊤) (hs : L.IsSection n ⊤ s) :
    L.nonvanishingLocus (L.sectionsOfFam s hs) = L.famLocus ⊤ s := by
  simp only [famLocus, nonvanishingLocus, sectionsOfFam, Scheme.basicOpen_res]
  refine iSup_congr fun i ↦ inf_eq_right.mpr ?_
  exact (X.basicOpen_le _).trans inf_le_right

end Global

section Pullback

variable {Y : Scheme.{u}} (f : Y ⟶ X) {V : X.Opens} {V' : Y.Opens}

variable (L) in
/-- The inverse image of families along `f : Y ⟶ X`, from `V` to `V' ≤ f⁻¹ V`. -/
noncomputable def famPullback (h : V' ≤ f ⁻¹ᵁ V) : L.Fam V →+* (L.pullback f).Fam V' :=
  RingHom.pi fun (i : L.ι) ↦ (f.appLE (V ⊓ L.U i) (V' ⊓ f ⁻¹ᵁ L.U i)
    ((le_inf (inf_le_left.trans h) inf_le_right).trans f.preimage_inf.ge)).hom.comp
      (Pi.evalRingHom _ i)

lemma famPullback_apply (h : V' ≤ f ⁻¹ᵁ V) (s : L.Fam V) (i : L.ι) :
    L.famPullback f h s i = f.appLE (V ⊓ L.U i) (V' ⊓ f ⁻¹ᵁ L.U i)
      ((le_inf (inf_le_left.trans h) inf_le_right).trans f.preimage_inf.ge) (s i) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma IsSection.famPullback {m : ℤ} {s : L.Fam V} (hs : L.IsSection m V s)
    (h : V' ≤ f ⁻¹ᵁ V) : (L.pullback f).IsSection m V' (L.famPullback f h s) := by
  intro i j
  have := congrArg (f.appLE (V ⊓ (L.U i ⊓ L.U j)) (V' ⊓ (f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j))
    (le_inf (inf_le_left.trans h) (inf_le_right.trans f.preimage_inf.ge))).hom (hs i j)
  simp only [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE] at this
  change Y.presheaf.map _ (f.appLE (V ⊓ L.U i) (V' ⊓ f ⁻¹ᵁ L.U i) _ (s i)) =
    Y.presheaf.map _ ((((Units.map (f.appLE (L.U i ⊓ L.U j) (f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j)
      f.preimage_inf.ge).hom) (L.g i j)) ^ m : Γ(Y, f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j)ˣ) :
        Γ(Y, f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j)) *
      Y.presheaf.map _ (f.appLE (V ⊓ L.U j) (V' ⊓ f ⁻¹ᵁ L.U j) _ (s j))
  simp only [← map_zpow, Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map]
  exact this

lemma famLocus_famPullback (h : V' ≤ f ⁻¹ᵁ V) (s : L.Fam V) :
    (L.pullback f).famLocus V' (L.famPullback f h s) = V' ⊓ f ⁻¹ᵁ L.famLocus V s := by
  change ⨆ (i : L.ι), Y.basicOpen (f.appLE (V ⊓ L.U i) (V' ⊓ f ⁻¹ᵁ L.U i) _ (s i)) = _
  simp only [famLocus, Scheme.basicOpen_appLE, Scheme.Hom.preimage_iSup, inf_iSup_eq]
  refine iSup_congr fun (i : L.ι) ↦ ?_
  refine le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf (le_inf inf_le_left ?_) inf_le_right)
  exact inf_le_right.trans (f.preimage_mono ((X.basicOpen_le _).trans inf_le_right))

lemma famRes_famPullback {V'' : Y.Opens} (h : V' ≤ f ⁻¹ᵁ V) (h' : V'' ≤ V') (s : L.Fam V) :
    (L.pullback f).famRes h' (L.famPullback f h s) = L.famPullback f (h'.trans h) s := by
  funext (i : L.ι)
  change Y.presheaf.map (homOfLE (inf_le_inf_right (f ⁻¹ᵁ L.U i) h')).op
      (f.appLE (V ⊓ L.U i) (V' ⊓ f ⁻¹ᵁ L.U i) _ (s i)) =
    f.appLE (V ⊓ L.U i) (V'' ⊓ f ⁻¹ᵁ L.U i) _ (s i)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma famPullback_famRes {V₀ : X.Opens} (h : V' ≤ f ⁻¹ᵁ V) (h₀ : V ≤ V₀) (s : L.Fam V₀) :
    L.famPullback f h (L.famRes h₀ s) = L.famPullback f (h.trans (f.preimage_mono h₀)) s := by
  funext (i : L.ι)
  simp only [famRes_apply, famPullback_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

end Pullback

section OpenImmersion

variable {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

omit L in
lemma bijective_appLE_of_isOpenImmersion {U : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (hU : U ≤ f.opensRange) (hV : f ⁻¹ᵁ U ≤ V) : Function.Bijective (f.appLE U V e) := by
  have : IsIso (f.app U) := f.isIso_app U hU
  have : IsIso (homOfLE e).op := ⟨(homOfLE hV).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have : IsIso (f.appLE U V e) := by rw [Scheme.Hom.appLE]; infer_instance
  exact ConcreteCategory.bijective_of_isIso _

set_option backward.isDefEq.respectTransparency false in
/-- Over an open immersion `f : Y ⟶ X`, every section of `(f^* L)^{⊗n}` over `Y` is the inverse
image of a section of `L^{⊗n}` over the image of `f`. -/
lemma exists_isSection_famPullback_eq {n : ℤ} {s' : (L.pullback f).Fam ⊤}
    (hs' : (L.pullback f).IsSection n ⊤ s') :
    ∃ s : L.Fam f.opensRange, L.IsSection n f.opensRange s ∧
      L.famPullback f (f.preimage_opensRange).ge s = s' := by
  have hb (i : L.ι) := bijective_appLE_of_isOpenImmersion f
    ((le_inf (inf_le_left.trans (f.preimage_opensRange).ge) inf_le_right).trans
      f.preimage_inf.ge : ⊤ ⊓ f ⁻¹ᵁ L.U i ≤ f ⁻¹ᵁ (f.opensRange ⊓ L.U i)) inf_le_left
    (le_inf le_top (f.preimage_inf.le.trans inf_le_right))
  choose s hs using fun (i : L.ι) ↦ (hb i).surjective (s' i)
  have e : L.famPullback f (f.preimage_opensRange).ge s = s' := funext fun (i : L.ι) ↦ hs i
  refine ⟨s, fun i j ↦ ?_, e⟩
  apply (bijective_appLE_of_isOpenImmersion f
    ((le_inf (inf_le_left.trans (f.preimage_opensRange).ge)
      (inf_le_right.trans f.preimage_inf.ge)) :
        ⊤ ⊓ (f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j) ≤ f ⁻¹ᵁ (f.opensRange ⊓ (L.U i ⊓ L.U j)))
    inf_le_left (le_inf le_top ((f.preimage_inf.le.trans inf_le_right).trans
      f.preimage_inf.le))).injective
  have h := hs' i j
  rw [← e] at h
  change Y.presheaf.map _ (f.appLE (f.opensRange ⊓ L.U i) (⊤ ⊓ f ⁻¹ᵁ L.U i) _ (s i)) =
    Y.presheaf.map _ ((((Units.map (f.appLE (L.U i ⊓ L.U j) (f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j)
      f.preimage_inf.ge).hom) (L.g i j)) ^ n : Γ(Y, f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j)ˣ) :
        Γ(Y, f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j)) *
      Y.presheaf.map _ (f.appLE (f.opensRange ⊓ L.U j) (⊤ ⊓ f ⁻¹ᵁ L.U j) _ (s j)) at h
  simp only [← map_zpow, Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map] at h
  simp only [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  exact h

end OpenImmersion

section Consequences

variable {U : X.Opens}

/-- The non-vanishing locus of a section over a quasi-compact open is quasi-compact. -/
lemma isCompact_famLocus (hU : IsCompact (U : Set X)) {n : ℤ} {s : L.Fam U}
    (hs : L.IsSection n U s) : IsCompact (L.famLocus U s : Set X) := by
  obtain ⟨ι', _, W, k, hWa, hWk, hWU, hcov⟩ := L.exists_finite_cover hU
  have e : L.famLocus U s = ⨆ a, X.basicOpen (L.famUnit (k a) (hWk a) (L.famRes (hWU a) s)) := by
    simp_rw [← famLocus_eq_basicOpen_famUnit _ (hs.famRes _), famLocus_famRes, ← iSup_inf_eq]
    exact (inf_eq_right.mpr ((famLocus_le s).trans hcov)).symm
  rw [e, Opens.coe_iSup]
  exact isCompact_iUnion fun a ↦ ((hWa a).basicOpen _).isCompact

/-- If `y` extends `sᵏ t` (as in `exists_isSection_famRes_eq`), the non-vanishing locus of `s y`
is that of `t`. -/
lemma famLocus_mul_eq {s y : L.Fam U} {t : L.Fam (L.famLocus U s)} {m m' : ℤ}
    (hy : L.IsSection m' U y) (ht : L.IsSection m _ t) {k : ℕ}
    (e : L.famRes (famLocus_le s) y = L.famRes (famLocus_le s) s ^ k * t) :
    L.famLocus U (s * y) = L.famLocus _ t := by
  rw [famLocus_mul s hy, ← famLocus_famRes (famLocus_le s), e, famLocus_mul _ ht,
    inf_eq_right]
  exact (famLocus_le t).trans ((famLocus_famRes_self s).ge.trans
    (famLocus_le_famLocus_pow _ k))

end Consequences

end AlgebraicGeometry.Scheme.LineBundle
