/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import SGA.Foundations.Cohomology.Helpers
import SGA.Foundations.Picard.KunnethAlgebra
import SGA.Foundations.Picard.ProductSections

/-!
# Čech cochains of `𝒪` on product covers

Let `k` be a field, `X`, `W` schemes over `Spec k`, `(Pᵢ)` a finite family of affine opens of `X`
with affine intersections, and `V' ⊆ W` an affine open. The Čech cochains of `𝒪` on the boxes
`Pᵢ ⊠ V' ⊆ X ×ₖ W` are the Čech cochains of `𝒪_X` on `(Pᵢ)` tensored with `Γ(W, V')`
(`AlgebraicGeometry.OverField.bijective_tensorPi`, from `Γ(P ⊠ V') = Γ(P) ⊗ₖ Γ(V')`), compatibly
with the differentials (`tensorPi_comp_rTensor_cechD₀`, `tensorPi_comp_rTensor_cechD₁`), with
restriction in `V'` (`tensorPi_comp_lTensor`) and with the section `x ↦ (x, y₀)` at a rational
point `y₀ ∈ V'` (`appLE_sectionAt_mulTensor`).

As a first application: if `Γ(X, 𝒪_X) = k`, a family of functions on the boxes `Pᵢ ⊠ V'` which
agree on the overlaps modulo an ideal `𝔍 ⊆ Γ(W, V')` is congruent modulo `𝔍` to a function
pulled back from `V'` (`exists_sub_mem_of_sub_mem`; the degree-`0` case of flat base change,
`H⁰(X ×ₖ Spec(Γ(V')/𝔍), 𝒪) = Γ(V')/𝔍`, in Čech form).

## References

* [A. Grothendieck, J. Dieudonné, *EGA* III 6.7.8][EGA]
* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite
open TensorProduct
open scoped AlgebraicGeometry.OverField

namespace AlgebraicGeometry.OverField

variable {k : Type u} [Field k]

section Cech

variable {S : Over (Spec (.of k))} {I : Type*}

/-- The Čech differential in degree `0`, for opens `O₁ (i, j) ⊆ O₀ i ∩ O₀ j`:
`a ↦ (a i - a j)|_{O₁ (i, j)}`. -/
noncomputable def cechD₀ (O₀ : I → S.left.Opens) (O₁ : I × I → S.left.Opens)
    (h : ∀ p, O₁ p ≤ O₀ p.1 ⊓ O₀ p.2) :
    (∀ i, Γ(S.left, O₀ i)) →ₗ[k] ∀ p, Γ(S.left, O₁ p) :=
  LinearMap.pi fun p ↦ (resAlgHom S ((h p).trans inf_le_left)).toLinearMap ∘ₗ LinearMap.proj p.1 -
    (resAlgHom S ((h p).trans inf_le_right)).toLinearMap ∘ₗ LinearMap.proj p.2

lemma cechD₀_apply (O₀ : I → S.left.Opens) (O₁ : I × I → S.left.Opens)
    (h : ∀ p, O₁ p ≤ O₀ p.1 ⊓ O₀ p.2) (a : ∀ i, Γ(S.left, O₀ i)) (p : I × I) :
    cechD₀ O₀ O₁ h a p = S.left.presheaf.map (homOfLE ((h p).trans inf_le_left)).op (a p.1) -
      S.left.presheaf.map (homOfLE ((h p).trans inf_le_right)).op (a p.2) :=
  rfl

/-- The Čech differential in degree `1`, for opens `O₂ (i, j, l)` inside the three relevant
`O₁`: `c ↦ (c (i, j) + c (j, l) - c (i, l))|_{O₂ (i, j, l)}`. -/
noncomputable def cechD₁ (O₁ : I × I → S.left.Opens) (O₂ : I × I × I → S.left.Opens)
    (h : ∀ t, O₂ t ≤ O₁ (t.1, t.2.1) ⊓ O₁ (t.2.1, t.2.2) ⊓ O₁ (t.1, t.2.2)) :
    (∀ p, Γ(S.left, O₁ p)) →ₗ[k] ∀ t, Γ(S.left, O₂ t) :=
  LinearMap.pi fun t ↦
    (resAlgHom S ((h t).trans (inf_le_left.trans inf_le_left))).toLinearMap ∘ₗ
        LinearMap.proj (t.1, t.2.1) +
      (resAlgHom S ((h t).trans (inf_le_left.trans inf_le_right))).toLinearMap ∘ₗ
        LinearMap.proj (t.2.1, t.2.2) -
      (resAlgHom S ((h t).trans inf_le_right)).toLinearMap ∘ₗ LinearMap.proj (t.1, t.2.2)

lemma cechD₁_apply (O₁ : I × I → S.left.Opens) (O₂ : I × I × I → S.left.Opens)
    (h : ∀ t, O₂ t ≤ O₁ (t.1, t.2.1) ⊓ O₁ (t.2.1, t.2.2) ⊓ O₁ (t.1, t.2.2))
    (c : ∀ p, Γ(S.left, O₁ p)) (t : I × I × I) :
    cechD₁ O₁ O₂ h c t =
      S.left.presheaf.map (homOfLE ((h t).trans (inf_le_left.trans inf_le_left))).op
          (c (t.1, t.2.1)) +
        S.left.presheaf.map (homOfLE ((h t).trans (inf_le_left.trans inf_le_right))).op
          (c (t.2.1, t.2.2)) -
        S.left.presheaf.map (homOfLE ((h t).trans inf_le_right)).op (c (t.1, t.2.2)) :=
  rfl

end Cech

section Overlaps

variable {S : Scheme.{u}} {I : Type*} (P : I → S.Opens)

/-- Pairwise intersections `P i ∩ P j`. -/
abbrev ov₁ (p : I × I) : S.Opens := P p.1 ⊓ P p.2

/-- Triple intersections `P i ∩ P j ∩ P l`. -/
abbrev ov₂ (t : I × I × I) : S.Opens := P t.1 ⊓ P t.2.1 ⊓ P t.2.2

lemma ov₁_le (p : I × I) : ov₁ P p ≤ P p.1 ⊓ P p.2 := le_rfl

lemma ov₂_le (t : I × I × I) :
    ov₂ P t ≤ ov₁ P (t.1, t.2.1) ⊓ ov₁ P (t.2.1, t.2.2) ⊓ ov₁ P (t.1, t.2.2) :=
  le_inf (le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)

end Overlaps

section Tensor

variable {X W : Over (Spec (.of k))} {ι : Type*}

lemma mulTensor_res {V₁ : X.left.Opens} (V₂ : X.left.Opens) {V₁' : W.left.Opens} (V₂' : W.left.Opens)
    (h : V₂ ≤ V₁) (h' : V₂' ≤ V₁')
    (a : Γ(X.left, V₁)) (b : Γ(W.left, V₁')) :
    (X ⊗ W).left.presheaf.map (homOfLE (box_mono h h')).op (mulTensor V₁ V₁' (a ⊗ₜ b)) =
      mulTensor V₂ V₂' (X.left.presheaf.map (homOfLE h).op a ⊗ₜ
        W.left.presheaf.map (homOfLE h').op b) := by
  rw [mulTensor_tmul, mulTensor_tmul, map_mul, ← CommRingCat.comp_apply,
    ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE, Scheme.Hom.map_appLE]

variable (O : ι → X.left.Opens) (V' : W.left.Opens)

/-- The map `(∏ᵢ Γ(X, Oᵢ)) ⊗ₖ Γ(W, V') → ∏ᵢ Γ(X ×ₖ W, Oᵢ ⊠ V')`. -/
noncomputable def tensorPi :
    (∀ i, Γ(X.left, O i)) ⊗[k] Γ(W.left, V') →ₗ[k] ∀ i, Γ((X ⊗ W).left, box X W (O i) V') :=
  LinearMap.pi fun i ↦ (mulTensor (O i) V').toLinearMap ∘ₗ (LinearMap.proj i).rTensor _

lemma tensorPi_tmul (a : ∀ i, Γ(X.left, O i)) (b : Γ(W.left, V')) (i : ι) :
    tensorPi O V' (a ⊗ₜ b) i = mulTensor (O i) V' (a i ⊗ₜ b) :=
  rfl

/-- `tensorPi` is bijective for a finite family of affine opens and an affine `V'`. -/
theorem bijective_tensorPi [Fintype ι] [DecidableEq ι] (hO : ∀ i, IsAffineOpen (O i))
    {V' : W.left.Opens} (hV' : IsAffineOpen V') : Function.Bijective (tensorPi O V') := by
  let e := (TensorProduct.piLeft k Γ(W.left, V') fun i ↦ Γ(X.left, O i)).trans
    (LinearEquiv.piCongrRight fun i ↦ LinearEquiv.ofBijective (mulTensor (O i) V').toLinearMap
      (bijective_mulTensor (hO i) hV'))
  have he : (e : _ → _) = tensorPi O V' := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      funext i
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [← he]
  exact e.bijective

lemma tensorPi_rTensor_apply {ι' : Type*} (O' : ι' → X.left.Opens)
    (φ : (∀ i, Γ(X.left, O i)) →ₗ[k] ∀ i, Γ(X.left, O' i))
    (ψ : (∀ i, Γ((X ⊗ W).left, box X W (O i) V')) →ₗ[k] ∀ i, Γ((X ⊗ W).left, box X W (O' i) V'))
    (H : ∀ (a : ∀ i, Γ(X.left, O i)) (b : Γ(W.left, V')),
      tensorPi O' V' (φ a ⊗ₜ b) = ψ (tensorPi O V' (a ⊗ₜ b))) :
    tensorPi O' V' ∘ₗ φ.rTensor _ = ψ ∘ₗ tensorPi O V' := by
  apply TensorProduct.ext'
  intro a b
  exact H a b

lemma tensorPi_apply (x : (∀ i, Γ(X.left, O i)) ⊗[k] Γ(W.left, V')) (i : ι) :
    tensorPi O V' x i = mulTensor (O i) V' ((LinearMap.proj i).rTensor _ x) :=
  rfl

section Differentials

variable {I : Type*} (P : I → X.left.Opens)

lemma box_ov₁_le (p : I × I) :
    box X W (ov₁ P p) V' ≤ box X W (P p.1) V' ⊓ box X W (P p.2) V' :=
  le_inf (box_mono inf_le_left le_rfl) (box_mono inf_le_right le_rfl)

lemma box_ov₂_le (t : I × I × I) :
    box X W (ov₂ P t) V' ≤ box X W (ov₁ P (t.1, t.2.1)) V' ⊓ box X W (ov₁ P (t.2.1, t.2.2)) V' ⊓
      box X W (ov₁ P (t.1, t.2.2)) V' :=
  le_inf (le_inf (box_mono ((ov₂_le P t).trans (inf_le_left.trans inf_le_left)) le_rfl)
      (box_mono ((ov₂_le P t).trans (inf_le_left.trans inf_le_right)) le_rfl))
    (box_mono ((ov₂_le P t).trans inf_le_right) le_rfl)

/-- `tensorPi` intertwines the Čech differentials in degree `0`. -/
theorem tensorPi_comp_rTensor_cechD₀ :
    tensorPi (ov₁ P) V' ∘ₗ (cechD₀ P (ov₁ P) (ov₁_le P)).rTensor Γ(W.left, V') =
      cechD₀ (S := X ⊗ W) (fun i ↦ box X W (P i) V') (fun p ↦ box X W (ov₁ P p) V')
        (box_ov₁_le V' P) ∘ₗ tensorPi P V' := by
  refine tensorPi_rTensor_apply _ _ _ _ _ fun a b ↦ ?_
  funext p
  simp only [tensorPi_tmul, cechD₀_apply, sub_tmul, map_sub]
  rw [mulTensor_res (ov₁ P p) V' inf_le_left le_rfl, mulTensor_res (ov₁ P p) V' inf_le_right le_rfl,
    CohomologyAux.presheaf_map_self]

/-- `tensorPi` intertwines the Čech differentials in degree `1`. -/
theorem tensorPi_comp_rTensor_cechD₁ :
    tensorPi (ov₂ P) V' ∘ₗ (cechD₁ (ov₁ P) (ov₂ P) (ov₂_le P)).rTensor Γ(W.left, V') =
      cechD₁ (S := X ⊗ W) (fun p ↦ box X W (ov₁ P p) V') (fun t ↦ box X W (ov₂ P t) V')
        (box_ov₂_le V' P) ∘ₗ tensorPi (ov₁ P) V' := by
  refine tensorPi_rTensor_apply _ _ _ _ _ fun a b ↦ ?_
  funext t
  simp only [tensorPi_tmul, cechD₁_apply, sub_tmul, add_tmul, map_sub, map_add]
  rw [mulTensor_res (ov₂ P t) V' ((ov₂_le P t).trans (inf_le_left.trans inf_le_left)) le_rfl,
    mulTensor_res (ov₂ P t) V' ((ov₂_le P t).trans (inf_le_left.trans inf_le_right)) le_rfl,
    mulTensor_res (ov₂ P t) V' ((ov₂_le P t).trans inf_le_right) le_rfl,
    CohomologyAux.presheaf_map_self]

end Differentials

/-- `tensorPi` is natural in the affine open `V'` of `W`. -/
theorem tensorPi_comp_lTensor {V₁' V₂' : W.left.Opens} (h : V₂' ≤ V₁') :
    tensorPi O V₂' ∘ₗ (resAlgHom W h).toLinearMap.lTensor _ =
      (LinearMap.pi fun i ↦ (resAlgHom (X ⊗ W) (box_mono le_rfl h :
        box X W (O i) V₂' ≤ box X W (O i) V₁')).toLinearMap ∘ₗ LinearMap.proj i) ∘ₗ
        tensorPi O V₁' := by
  apply TensorProduct.ext'
  intro a b
  funext i
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, tensorPi_tmul, AlgHom.toLinearMap_apply,
    resAlgHom_apply, LinearMap.pi_apply, LinearMap.proj_apply]
  rw [mulTensor_res (O i) V₂' le_rfl h, CohomologyAux.presheaf_map_self]

end Tensor

section Glue

variable {S : Scheme.{u}} {ι : Type*}

/-- Compatible sections of `𝒪_S` on an open cover glue. -/
lemma exists_glue (U : ι → S.Opens) {V : S.Opens} (hUV : ∀ i, U i ≤ V) (hcov : V ≤ ⨆ i, U i)
    (sf : ∀ i, Γ(S, U i))
    (h : ∀ i j, S.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (sf i) =
      S.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (sf j)) :
    ∃ s : Γ(S, V), ∀ i, S.presheaf.map (homOfLE (hUV i)).op s = sf i := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' S.sheaf U V (fun i ↦ homOfLE (hUV i))
    hcov sf h
  exact ⟨s, hs⟩

/-- Sections of `𝒪_S` agreeing on an open cover are equal. -/
lemma eq_of_forall_res_eq (U : ι → S.Opens) {V : S.Opens} (hUV : ∀ i, U i ≤ V)
    (hcov : V ≤ ⨆ i, U i) {s t : Γ(S, V)}
    (h : ∀ i, S.presheaf.map (homOfLE (hUV i)).op s = S.presheaf.map (homOfLE (hUV i)).op t) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq' S.sheaf U V (fun i ↦ homOfLE (hUV i)) hcov s t h

end Glue

section Constants

variable {X : Over (Spec (.of k))} {I : Type*} (P : I → X.left.Opens)

/-- If `Γ(X, 𝒪_X) = k`, the Čech `0`-cocycles of `𝒪_X` on an open cover are the constants:
`k → ∏ Γ(Pᵢ) → ∏ Γ(Pᵢ ∩ Pⱼ)` is exact. -/
theorem exact_algebraMap_cechD₀ (hX : IsIso (X.hom.app ⊤)) (hPcov : ⨆ i, P i = ⊤) :
    Function.Exact (Algebra.linearMap k (∀ i, Γ(X.left, P i))) (cechD₀ P (ov₁ P) (ov₁_le P)) := by
  intro a
  constructor
  · intro ha
    have hcomp (i j : I) : X.left.presheaf.map (homOfLE (inf_le_left : P i ⊓ P j ≤ P i)).op (a i) =
        X.left.presheaf.map (homOfLE (inf_le_right : P i ⊓ P j ≤ P j)).op (a j) := by
      have := congrFun ha (i, j)
      rw [cechD₀_apply, Pi.zero_apply, sub_eq_zero] at this
      exact this
    obtain ⟨g, hg⟩ := exists_glue P (V := X.hom ⁻¹ᵁ ⊤) (fun i _ _ ↦ trivial)
      (fun x _ ↦ by rw [hPcov]; trivial) a hcomp
    obtain ⟨r, rfl⟩ := (ConcreteCategory.bijective_of_isIso (X.hom.app ⊤)).2 g
    refine ⟨Scheme.ΓSpecIso (.of k) |>.hom r, funext fun i ↦ ?_⟩
    rw [← hg i, Algebra.linearMap_apply, Pi.algebraMap_apply, algebraMap_eq]
    change (X.hom.appLE ⊤ (P i) _) ((Scheme.ΓSpecIso (.of k)).inv
      ((Scheme.ΓSpecIso (.of k)).hom r)) = _
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (.of k)).hom, Iso.hom_inv_id,
      CommRingCat.id_apply]
    rfl
  · rintro ⟨c, rfl⟩
    funext p
    rw [cechD₀_apply, Algebra.linearMap_apply, Pi.algebraMap_apply, Pi.algebraMap_apply,
      Pi.zero_apply, ← resAlgHom_apply, ← resAlgHom_apply, AlgHom.commutes, AlgHom.commutes,
      sub_self]

end Constants

section Ideal

variable {X W : Over (Spec (.of k))}

lemma mulTensor_one_tmul (V : X.left.Opens) (V' : W.left.Opens) (b : Γ(W.left, V')) :
    mulTensor V V' (1 ⊗ₜ b) = (snd X W).left.appLE V' _ (box_le_snd V V') b := by
  rw [mulTensor_tmul, map_one, one_mul]

/-- For affine `V`, `V'` and an ideal `𝔍 ⊆ Γ(W, V')`, a function `mulTensor w` on `V ⊠ V'` lies in
the ideal generated by `𝔍` iff `w` vanishes in `Γ(X, V) ⊗ₖ Γ(W, V') / 𝔍`. -/
theorem mulTensor_mem_map_iff {V : X.left.Opens} {V' : W.left.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen V') (𝔍 : Ideal Γ(W.left, V')) (w : Γ(X.left, V) ⊗[k] Γ(W.left, V')) :
    mulTensor V V' w ∈ 𝔍.map ((snd X W).left.appLE V' _ (box_le_snd V V')).hom ↔
      (Ideal.Quotient.mkₐ k 𝔍).toLinearMap.lTensor _ w = 0 := by
  let e := RingEquiv.ofBijective (mulTensor V V') (bijective_mulTensor hV hV')
  have hsnd : ((snd X W).left.appLE V' _ (box_le_snd V V')).hom =
      e.toRingHom.comp (Algebra.TensorProduct.includeRight (A := Γ(X.left, V)) :
        _ →ₐ[k] _).toRingHom := by
    ext b
    exact (mulTensor_one_tmul V V' b).symm
  have hker := Algebra.TensorProduct.lTensor_ker (A := Γ(X.left, V))
    (Ideal.Quotient.mkₐ k 𝔍) (Ideal.Quotient.mkₐ_surjective k 𝔍)
  rw [show RingHom.ker (Ideal.Quotient.mkₐ k 𝔍) = 𝔍 from Ideal.Quotient.mkₐ_ker k 𝔍] at hker
  rw [hsnd, ← Ideal.map_map, RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv,
    Ideal.mem_comap]
  change e.symm (e w) ∈ _ ↔ _
  rw [RingEquiv.symm_apply_apply]
  change w ∈ Ideal.map (Algebra.TensorProduct.includeRight (A := Γ(X.left, V)) :
    _ →ₐ[k] _) 𝔍 ↔ _
  rw [← hker, RingHom.mem_ker]
  rfl

end Ideal

section Helpers

lemma rTensor_lTensor_apply {R M N M' N' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') (x : M ⊗[R] N) :
    f.rTensor N' (g.lTensor M x) = g.lTensor M' (f.rTensor N x) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_apply]

/-- An element of `(∏ₚ Mₚ) ⊗ N` all of whose components vanish is zero. -/
lemma eq_zero_of_forall_rTensor_proj_eq_zero {R N : Type*} [CommRing R] [AddCommGroup N]
    [Module R N] {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (u : (∀ i, M i) ⊗[R] N)
    (h : ∀ i, (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i).rTensor N u = 0) : u = 0 := by
  have he : ∀ v : (∀ i, M i) ⊗[R] N, TensorProduct.piLeft R N M v =
      fun i ↦ (LinearMap.proj i : (∀ i, M i) →ₗ[R] M i).rTensor N v := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => funext i; simp
    | tmul a b => rfl
    | add x y hx hy => rw [map_add, hx, hy]; funext i; simp
  apply (TensorProduct.piLeft R N M).injective
  rw [he, map_zero]
  exact funext h

end Helpers

section Constant

variable {X W : Over (Spec (.of k))} {I : Type*} [Fintype I] [DecidableEq I]

/-- **Functions compatible modulo `𝔍` are constant modulo `𝔍`** (the degree-`0` case of flat base
change, `H⁰(X ×ₖ Spec (Γ(W, V') / 𝔍), 𝒪) = Γ(W, V') / 𝔍` for `Γ(X, 𝒪_X) = k`, in Čech form): let
`(Pᵢ)` be a finite affine open cover of `X` with affine pairwise intersections, `V' ⊆ W` affine
and `𝔍 ⊆ Γ(W, V')` an ideal. If functions `eᵢ` on the boxes `Pᵢ ⊠ V'` agree on the overlaps
modulo `𝔍`, there is `c ∈ Γ(W, V')` with `eᵢ ≡ pr₂^* c` modulo `𝔍` for every `i`. -/
theorem exists_sub_mem_of_sub_mem (hX : IsIso (X.hom.app ⊤)) (P : I → X.left.Opens)
    (hPcov : ⨆ i, P i = ⊤) (hP : ∀ i, IsAffineOpen (P i)) (hP₁ : ∀ p, IsAffineOpen (ov₁ P p))
    {V' : W.left.Opens} (hV' : IsAffineOpen V') (𝔍 : Ideal Γ(W.left, V'))
    (e : ∀ i, Γ((X ⊗ W).left, box X W (P i) V'))
    (he : ∀ p : I × I, cechD₀ (S := X ⊗ W) (fun i ↦ box X W (P i) V')
      (fun p ↦ box X W (ov₁ P p) V') (box_ov₁_le V' P) e p ∈
        𝔍.map ((snd X W).left.appLE V' _ (box_le_snd (ov₁ P p) V')).hom) :
    ∃ c : Γ(W.left, V'), ∀ i, e i - (snd X W).left.appLE V' _ (box_le_snd (P i) V') c ∈
      𝔍.map ((snd X W).left.appLE V' _ (box_le_snd (P i) V')).hom := by
  classical
  let q : Γ(W.left, V') →ₗ[k] Γ(W.left, V') ⧸ 𝔍 := (Ideal.Quotient.mkₐ k 𝔍).toLinearMap
  obtain ⟨x, rfl⟩ := (bijective_tensorPi P hP hV').2 e
  have hcoc : (cechD₀ P (ov₁ P) (ov₁_le P)).rTensor _ (q.lTensor _ x) = 0 := by
    refine eq_zero_of_forall_rTensor_proj_eq_zero _ fun p ↦ ?_
    rw [rTensor_lTensor_apply, rTensor_lTensor_apply, ← mulTensor_mem_map_iff (hP₁ p) hV' 𝔍]
    have h1 := congrArg (fun φ ↦ φ x p) (tensorPi_comp_rTensor_cechD₀ V' P)
    simp only [LinearMap.comp_apply] at h1
    rw [tensorPi_apply] at h1
    rw [h1]
    exact he p
  obtain ⟨u, hu⟩ := (Module.Flat.rTensor_exact (Γ(W.left, V') ⧸ 𝔍)
    (exact_algebraMap_cechD₀ P hX hPcov) (q.lTensor _ x)).1 hcoc
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (TensorProduct.lid k _ u)
  have hu' : u = 1 ⊗ₜ q g := by
    rw [← (TensorProduct.lid k _).symm_apply_apply u, TensorProduct.lid_symm_apply, ← hg]
    rfl
  have hx : q.lTensor _ (x - 1 ⊗ₜ g) = 0 := by
    rw [map_sub, ← hu, hu', LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, Algebra.linearMap_apply,
      map_one, sub_self]
  refine ⟨g, fun i ↦ ?_⟩
  have h2 : (LinearMap.proj i).rTensor _ (q.lTensor _ (x - 1 ⊗ₜ g)) = 0 := by
    rw [hx, map_zero]
  rw [rTensor_lTensor_apply, ← mulTensor_mem_map_iff (hP i) hV' 𝔍, map_sub, map_sub,
    LinearMap.rTensor_tmul] at h2
  rw [tensorPi_apply]
  convert h2 using 2
  rw [LinearMap.proj_apply, Pi.one_apply, mulTensor_one_tmul]

end Constant

end AlgebraicGeometry.OverField
