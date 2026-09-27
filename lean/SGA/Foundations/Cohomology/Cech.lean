/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Čech complexes of presheaves on a topological space

For a family of opens `U : ι → Opens X` and a presheaf of abelian groups `P` on `X`, the Čech
complex `TopCat.Presheaf.cechComplex U P` has in degree `n` the group
`CechCochain U P n = ∏_{x : Fin (n+1) → ι} P(U_{x₀} ∩ ⋯ ∩ U_{xₙ})` of families of sections over
the `(n+1)`-fold intersections (the full, ordered Čech complex: repeated indices are allowed), with
the alternating differential `(dc)_{x₀…x_{n+1}} = ∑ᵢ (-1)ⁱ c_{x₀…x̂ᵢ…x_{n+1}}|`
(Stacks Project, Section 20.9, Tag 01ED; EGA 0_III 11.8; Godement II.5.1). It is defined as the
alternating
coface complex of a cosimplicial abelian group (`cechCosimplicialObject`), and is functorial in
`P` (`cechComplexFunctor`).

The alternating Čech complex (strictly increasing indices) and its comparison with this one
(Stacks Project, Section 20.23) are not formalized.

## Main results

* `TopCat.Presheaf.cechD_apply`, `cechComplex_d_apply`: the explicit differential, and
  `cechComplex_exactAt_succ_iff`, an elementwise description of exactness in positive degrees.
* `TopCat.Presheaf.cechD_cons`: the "cone identity" behind the standard contracting homotopy.
* `TopCat.Presheaf.cechComplex_exactAt_of_le`: if a member of the family contains all the
  others, the Čech complex is exact in positive degrees (Stacks Project, Section 20.9).
* `TopCat.Presheaf.cechAugmentation_injective`, `exists_cechAugmentation_eq`: for a sheaf, the
  degree-zero Čech cohomology is the group of sections over the union.
-/

universe w v u

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology Simplicial

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {ι : Type w} (U : ι → Opens X)

/-- The intersection `⋂ₐ U (x a)` of the members of a family of opens indexed by `x`. -/
def cechOpen {α : Type*} (x : α → ι) : Opens X := ⨅ a, U (x a)

lemma cechOpen_le {α : Type*} (x : α → ι) (a : α) : cechOpen U x ≤ U (x a) := iInf_le _ a

lemma cechOpen_le_comp {α β : Type*} (x : β → ι) (f : α → β) :
    cechOpen U x ≤ cechOpen U (x ∘ f) :=
  le_iInf fun a ↦ iInf_le _ (f a)

variable (P : TopCat.Presheaf AddCommGrpCat.{v} X)

/-- Čech cochains of degree `n`: families of sections over the `(n+1)`-fold intersections. -/
abbrev CechCochain (n : ℕ) : Type (max w v) :=
  ∀ x : Fin (n + 1) → ι, P.obj (op (cechOpen U x))

/-- Restriction of a family of sections along an equality of index tuples. -/
lemma map_apply_eq_of_eq {α : Type*} {x x' : α → ι} (h : x = x')
    (hle : cechOpen U x' ≤ cechOpen U x) (c : ∀ x : α → ι, P.obj (op (cechOpen U x))) :
    P.map (homOfLE hle).op (c x) = c x' := by
  subst h
  simp

@[simp]
lemma map_map_apply {V₁ V₂ V₃ : Opens X} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (s : P.obj (op V₁)) :
    P.map (homOfLE h₂).op (P.map (homOfLE h₁).op s) = P.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp]
  rfl

/-- The map of Čech cochains induced by a map `θ` of index sets: `(θ^* c)_y = c_{y ∘ θ}|`. -/
noncomputable def cechMap {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    CechCochain U P m →+ CechCochain U P n :=
  AddMonoidHom.pi fun y ↦ (P.map (homOfLE (cechOpen_le_comp U y θ)).op).hom.comp
    (Pi.evalAddMonoidHom (fun x : Fin (m + 1) → ι ↦ P.obj (op (cechOpen U x))) (y ∘ θ))

@[simp]
lemma cechMap_apply {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (c : CechCochain U P m)
    (y : Fin (n + 1) → ι) :
    cechMap U P θ c y = P.map (homOfLE (cechOpen_le_comp U y θ)).op (c (y ∘ θ)) :=
  rfl

lemma cechMap_id {n : ℕ} (c : CechCochain U P n) : cechMap U P id c = c := by
  funext y
  exact map_apply_eq_of_eq U P rfl _ c

lemma cechMap_comp_apply {l m n : ℕ} (θ : Fin (l + 1) → Fin (m + 1))
    (θ' : Fin (m + 1) → Fin (n + 1))
    (c : CechCochain U P l) :
    cechMap U P θ' (cechMap U P θ c) = cechMap U P (θ' ∘ θ) c := by
  funext y
  rw [cechMap_apply, cechMap_apply, map_map_apply, cechMap_apply]
  rfl

/-- The cosimplicial abelian group of Čech cochains. -/
@[simps]
noncomputable def cechCosimplicialObject : CosimplicialObject AddCommGrpCat.{max w v} where
  obj Δ := AddCommGrpCat.of (CechCochain U P Δ.len)
  map θ := AddCommGrpCat.ofHom (cechMap U P θ.toOrderHom)
  map_id _ := AddCommGrpCat.ext fun c ↦ cechMap_id U P c
  map_comp θ θ' := AddCommGrpCat.ext fun c ↦
    (cechMap_comp_apply U P θ.toOrderHom θ'.toOrderHom c).symm

/-- The Čech differential `(d c)_{x₀ … x_{n+1}} = ∑ᵢ (-1)ⁱ c_{x₀ … x̂ᵢ … x_{n+1}}|`. -/
noncomputable def cechD (n : ℕ) : CechCochain U P n →+ CechCochain U P (n + 1) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • cechMap U P (Fin.succAbove i)

lemma cechD_apply {n : ℕ} (c : CechCochain U P n) (x : Fin (n + 2) → ι) :
    cechD U P n c x = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      P.map (homOfLE (cechOpen_le_comp U x (Fin.succAbove i))).op (c (x ∘ Fin.succAbove i)) := by
  simp [cechD, Finset.sum_apply]

/-- The Čech complex of a presheaf of abelian groups with respect to a family of opens: the
alternating coface complex of `cechCosimplicialObject`. In degree `n` it is the group of families
of sections over the `(n+1)`-fold intersections; its differential is `cechD`. -/
noncomputable def cechComplex : CochainComplex AddCommGrpCat.{max w v} ℕ :=
  (alternatingCofaceMapComplex AddCommGrpCat.{max w v}).obj (cechCosimplicialObject U P)

lemma cechComplex_X (n : ℕ) : (cechComplex U P).X n = AddCommGrpCat.of (CechCochain U P n) := rfl

lemma alternatingCofaceMapComplex_obj_d' {C : Type*} [Category* C]
    [Preadditive C] (K : CosimplicialObject C) (n : ℕ) :
    ((alternatingCofaceMapComplex C).obj K).d n (n + 1) = AlternatingCofaceMapComplex.objD K n :=
  CochainComplex.of_d (fun n ↦ K.obj ⦋n⦌) (AlternatingCofaceMapComplex.objD K) n

lemma addCommGrpCat_sum_apply {M N : AddCommGrpCat} {α : Type*} (s : Finset α)
    (f : α → (M ⟶ N)) (x : M) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  change AddCommGrpCat.homAddEquiv (∑ i ∈ s, f i) x = _
  rw [map_sum, AddMonoidHom.finsetSum_apply]
  rfl

lemma alternatingCofaceMapComplex_objD_apply
    (K : CosimplicialObject AddCommGrpCat) (n : ℕ) (c : K.obj ⦋n⦌) :
    AlternatingCofaceMapComplex.objD K n c = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • K.δ i c := by
  simp [AlternatingCofaceMapComplex.objD, addCommGrpCat_sum_apply]

lemma cechComplex_d_apply (n : ℕ) (c : CechCochain U P n) :
    (cechComplex U P).d n (n + 1) c = cechD U P n c := by
  have h₁ := congrArg (fun (f : (cechComplex U P).X n ⟶ (cechComplex U P).X (n + 1)) ↦ f c)
    (alternatingCofaceMapComplex_obj_d' (cechCosimplicialObject U P) n)
  refine h₁.trans
    ((alternatingCofaceMapComplex_objD_apply (cechCosimplicialObject U P) n c).trans ?_)
  simp only [cechD, AddMonoidHom.finsetSum_apply]
  rfl

@[simp]
lemma cechD_cechD (n : ℕ) (c : CechCochain U P n) : cechD U P (n + 1) (cechD U P n c) = 0 := by
  have h := congrArg (fun (f : (cechComplex U P).X n ⟶ (cechComplex U P).X (n + 2)) ↦ f c)
    ((cechComplex U P).d_comp_d n (n + 1) (n + 2))
  refine Eq.trans ?_ (h.trans rfl)
  exact ((cechComplex_d_apply U P (n + 1) _).trans
    (congrArg _ (cechComplex_d_apply U P n c))).symm

lemma cechComplex_exactAt_succ_iff (n : ℕ) :
    (cechComplex U P).ExactAt (n + 1) ↔ ∀ c : CechCochain U P (n + 1),
      cechD U P (n + 1) c = 0 → ∃ b : CechCochain U P n, cechD U P n b = c := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  refine ⟨fun h c hc ↦ ?_, fun h c hc ↦ ?_⟩
  · obtain ⟨b, hb⟩ := h c ((cechComplex_d_apply U P (n + 1) c).trans hc)
    exact ⟨b, (cechComplex_d_apply U P n b).symm.trans hb⟩
  · obtain ⟨b, hb⟩ := h c ((cechComplex_d_apply U P (n + 1) c).symm.trans hc)
    exact ⟨b, (cechComplex_d_apply U P n b).trans hb⟩

/-- Restrictions of a Čech cochain at two equal index tuples agree. -/
lemma map_apply_congr {α : Type*} {V : Opens X} {x x' : α → ι} (h : x = x')
    (hx : V ≤ cechOpen U x) (hx' : V ≤ cechOpen U x')
    (c : ∀ x : α → ι, P.obj (op (cechOpen U x))) :
    P.map (homOfLE hx).op (c x) = P.map (homOfLE hx').op (c x') := by
  subst h
  rfl

lemma cechOpen_cons_le {n : ℕ} (k : ι) (x : Fin n → ι) :
    cechOpen U (Fin.cons k x : Fin (n + 1) → ι) ≤ cechOpen U x :=
  cechOpen_le_comp U (Fin.cons k x : Fin (n + 1) → ι) Fin.succ

lemma cechOpen_cons_le_self {n : ℕ} (k : ι) (x : Fin n → ι) :
    cechOpen U (Fin.cons k x : Fin (n + 1) → ι) ≤ U k :=
  cechOpen_le U (Fin.cons k x : Fin (n + 1) → ι) 0

lemma cechOpen_cons_eq {n : ℕ} (k : ι) (x : Fin n → ι) :
    cechOpen U (Fin.cons k x : Fin (n + 1) → ι) = U k ⊓ cechOpen U x :=
  le_antisymm (le_inf (cechOpen_cons_le_self U k x) (cechOpen_cons_le U k x))
    (le_iInf fun a ↦ Fin.cases (inf_le_left) (fun b ↦ inf_le_right.trans (cechOpen_le U x b)) a)

lemma cons_comp_succAbove_zero {n : ℕ} (k : ι) (x : Fin (n + 1) → ι) :
    (Fin.cons k x : Fin (n + 2) → ι) ∘ Fin.succAbove 0 = x := by
  funext a
  simp

lemma cons_comp_succAbove_succ {n : ℕ} (k : ι) (x : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    (Fin.cons k x : Fin (n + 2) → ι) ∘ Fin.succAbove j.succ =
      Fin.cons k (x ∘ Fin.succAbove j) := by
  funext a
  induction a using Fin.cases <;> simp [Fin.succ_succAbove_succ]

/-- The cone identity: the Čech differential evaluated at `(k, x₀, …, x_{n+1})`. This is the
formula behind the contracting homotopy `c ↦ c_{k, -}` of the Čech complex. -/
lemma cechD_cons (k : ι) {n : ℕ} (c : CechCochain U P (n + 1)) (x : Fin (n + 2) → ι) :
    cechD U P (n + 1) c (Fin.cons k x) =
      P.map (homOfLE (cechOpen_cons_le U k x)).op (c x) -
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • P.map (homOfLE (le_trans
          (le_inf (cechOpen_cons_le_self U k x) ((cechOpen_cons_le U k x).trans
            (cechOpen_le_comp U x (Fin.succAbove j)))) (cechOpen_cons_eq U k _).ge)).op
          (c (Fin.cons k (x ∘ Fin.succAbove j))) := by
  rw [cechD_apply, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_smul]
    exact map_apply_congr U P (cons_comp_succAbove_zero k x) _ _ c
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, ← smul_neg, smul_neg]
    congr 2
    exact map_apply_congr U P (cons_comp_succAbove_succ k x j) _ _ c

lemma le_cechOpen_cons {n : ℕ} {k : ι} (hk : ∀ i, U i ≤ U k) (x : Fin (n + 1) → ι) :
    cechOpen U x ≤ cechOpen U (Fin.cons k x : Fin (n + 2) → ι) := by
  rw [cechOpen_cons_eq]
  exact le_inf ((cechOpen_le U x 0).trans (hk _)) le_rfl

/-- If one member `U k` of the family contains all the others, the Čech complex is exact in
positive degrees: `c ↦ (c_{k, -})` is a contracting homotopy. -/
theorem cechComplex_exactAt_of_le (k : ι) (hk : ∀ i, U i ≤ U k) (n : ℕ) :
    (cechComplex U P).ExactAt (n + 1) := by
  rw [cechComplex_exactAt_succ_iff]
  intro c hc
  refine ⟨fun y ↦ P.map (homOfLE (le_cechOpen_cons U hk y)).op (c (Fin.cons k y)),
    funext fun x ↦ ?_⟩
  have h := congrArg (P.map (homOfLE (le_cechOpen_cons U hk x)).op)
    ((cechD_cons U P k c x).symm.trans (congrFun hc (Fin.cons k x)))
  rw [map_sub, map_sum, Pi.zero_apply, map_zero, map_map_apply,
    map_apply_eq_of_eq U P rfl, sub_eq_zero] at h
  rw [h, cechD_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, map_map_apply, map_map_apply]

section Functoriality

variable {P} {Q R : TopCat.Presheaf AddCommGrpCat.{v} X}

/-- The map on Čech cochains induced by a morphism of presheaves. -/
noncomputable def cechCochainMap (φ : P ⟶ Q) (n : ℕ) : CechCochain U P n →+ CechCochain U Q n :=
  AddMonoidHom.pi fun x ↦ (φ.app (op (cechOpen U x))).hom.comp
    (Pi.evalAddMonoidHom (fun x : Fin (n + 1) → ι ↦ P.obj (op (cechOpen U x))) x)

@[simp]
lemma cechCochainMap_apply (φ : P ⟶ Q) {n : ℕ} (c : CechCochain U P n) (x : Fin (n + 1) → ι) :
    cechCochainMap U φ n c x = φ.app _ (c x) :=
  rfl

@[simp]
lemma cechCochainMap_id {n : ℕ} (c : CechCochain U P n) : cechCochainMap U (𝟙 P) n c = c :=
  rfl

lemma cechCochainMap_comp (φ : P ⟶ Q) (ψ : Q ⟶ R) {n : ℕ} (c : CechCochain U P n) :
    cechCochainMap U (φ ≫ ψ) n c = cechCochainMap U ψ n (cechCochainMap U φ n c) :=
  rfl

lemma cechCochainMap_cechMap (φ : P ⟶ Q) {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1))
    (c : CechCochain U P m) :
    cechCochainMap U φ n (cechMap U P θ c) = cechMap U Q θ (cechCochainMap U φ m c) := by
  funext y
  simp only [cechCochainMap_apply, cechMap_apply]
  exact NatTrans.naturality_apply φ _ _

/-- Morphisms of presheaves commute with the Čech differential. -/
lemma cechD_cechCochainMap (φ : P ⟶ Q) {n : ℕ} (c : CechCochain U P n) :
    cechD U Q n (cechCochainMap U φ n c) = cechCochainMap U φ (n + 1) (cechD U P n c) := by
  simp only [cechD, AddMonoidHom.finsetSum_apply, map_sum, AddMonoidHom.smul_apply, map_zsmul,
    cechCochainMap_cechMap]

variable (P) in
/-- The Čech construction as a functor from presheaves of abelian groups to cosimplicial abelian
groups. -/
@[simps]
noncomputable def cechCosimplicialFunctor :
    TopCat.Presheaf AddCommGrpCat.{v} X ⥤ CosimplicialObject AddCommGrpCat.{max w v} where
  obj P := cechCosimplicialObject U P
  map φ :=
    { app Δ := AddCommGrpCat.ofHom (cechCochainMap U φ Δ.len)
      naturality _ _ θ := AddCommGrpCat.ext fun c ↦
        cechCochainMap_cechMap U φ θ.toOrderHom c }

/-- The Čech complex as a functor from presheaves of abelian groups to cochain complexes. -/
noncomputable def cechComplexFunctor :
    TopCat.Presheaf AddCommGrpCat.{v} X ⥤ CochainComplex AddCommGrpCat.{max w v} ℕ :=
  cechCosimplicialFunctor U ⋙ alternatingCofaceMapComplex _

lemma cechComplexFunctor_obj (P : TopCat.Presheaf AddCommGrpCat.{v} X) :
    (cechComplexFunctor U).obj P = cechComplex U P :=
  rfl

end Functoriality

section Augmentation

/-- The augmentation `P(⋃ᵢ Uᵢ) → Č⁰(U, P)`, restricting a section to each member of the family. -/
noncomputable def cechAugmentation : P.obj (op (⨆ i, U i)) →+ CechCochain U P 0 :=
  AddMonoidHom.pi fun x ↦ (P.map (homOfLE ((cechOpen_le U x 0).trans (le_iSup U (x 0)))).op).hom

lemma cechAugmentation_apply (s : P.obj (op (⨆ i, U i))) (x : Fin 1 → ι) :
    cechAugmentation U P s x =
      P.map (homOfLE ((cechOpen_le U x 0).trans (le_iSup U (x 0)))).op s :=
  rfl

@[simp]
lemma cechD_cechAugmentation (s : P.obj (op (⨆ i, U i))) :
    cechD U P 0 (cechAugmentation U P s) = 0 := by
  funext x
  rw [cechD_apply]
  simp [Fin.sum_univ_succ, cechAugmentation_apply, map_map_apply]

lemma cechOpen_const (i : ι) : cechOpen U (fun _ : Fin 1 ↦ i) = U i :=
  iInf_const

lemma cechOpen_le_const {α : Type*} (x : α → ι) (a : α) :
    cechOpen U x ≤ cechOpen U (fun _ : Fin 1 ↦ x a) :=
  (cechOpen_le U x a).trans (cechOpen_const U (x a)).ge

/-- The differential in degree `0`: `(d c)_{x₀ x₁} = c_{x₁}| - c_{x₀}|`. -/
lemma cechD_zero_apply (c : CechCochain U P 0) (x : Fin 2 → ι) :
    cechD U P 0 c x =
      P.map (homOfLE (cechOpen_le_const U x 1)).op (c fun _ ↦ x 1) -
        P.map (homOfLE (cechOpen_le_const U x 0)).op (c fun _ ↦ x 0) := by
  have h₀ : x ∘ Fin.succAbove 0 = fun _ ↦ x 1 := funext fun a ↦ by fin_cases a; rfl
  have h₁ : x ∘ Fin.succAbove 1 = fun _ ↦ x 0 := funext fun a ↦ by fin_cases a; rfl
  rw [cechD_apply, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_one_zsmul, ← sub_eq_add_neg, map_apply_congr U P h₀ _ (cechOpen_le_const U x 1) c,
    map_apply_congr U P h₁ _ (cechOpen_le_const U x 0) c]

variable (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- For a sheaf, the augmentation is injective: sections are determined by their restrictions to a
cover. -/
lemma cechAugmentation_injective : Function.Injective (cechAugmentation U F.obj) := by
  intro s t h
  refine TopCat.Sheaf.eq_of_locally_eq F U s t fun i ↦ ?_
  have h' := congrArg (F.obj.map (homOfLE (cechOpen_const U i).ge).op)
    (congrFun h (fun _ ↦ i))
  simp only [cechAugmentation_apply, map_map_apply] at h'
  exact h'

/-- For a sheaf, the kernel of the first Čech differential is the image of the augmentation:
Čech cocycles of degree `0` glue. -/
lemma exists_cechAugmentation_eq (c : CechCochain U F.obj 0)
    (hc : cechD U F.obj 0 c = 0) : ∃ s, cechAugmentation U F.obj s = c := by
  let sf : ∀ i, F.obj.obj (op (U i)) := fun i ↦
    F.obj.map (homOfLE (cechOpen_const U i).ge).op (c fun _ ↦ i)
  have hsf : TopCat.Presheaf.IsCompatible F.obj U sf := by
    intro i j
    have hle : U i ⊓ U j ≤ cechOpen U ![i, j] :=
      le_iInf fun a ↦ Fin.cases inf_le_left (fun b ↦ by simp) a
    have h := congrArg (F.obj.map (homOfLE hle).op) (congrFun hc ![i, j])
    rw [cechD_zero_apply, Pi.zero_apply, map_zero, map_sub, sub_eq_zero, map_map_apply,
      map_map_apply] at h
    change F.obj.map (homOfLE inf_le_left).op (sf i) =
      F.obj.map (homOfLE inf_le_right).op (sf j)
    simp only [sf, map_map_apply]
    exact h.symm
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing F U sf hsf
  refine ⟨s, funext fun x ↦ ?_⟩
  have hx : x = fun _ ↦ x 0 := funext fun a ↦ by fin_cases a; rfl
  have h₀ : F.obj.map (homOfLE (le_iSup U (x 0))).op s = sf (x 0) := hs (x 0)
  have h := congrArg (F.obj.map (homOfLE (cechOpen_le U x 0)).op) h₀
  simp only [sf, map_map_apply] at h
  rw [cechAugmentation_apply]
  exact h.trans (map_apply_eq_of_eq U F.obj hx.symm _ c)

end Augmentation

end TopCat.Presheaf
