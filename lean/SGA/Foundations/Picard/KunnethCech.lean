/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Picard.CechProduct
import SGA.Foundations.Picard.Seesaw

/-!
# `H¹(X ×ₖ Y, 𝒪) → H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)` is injective, in Čech form

Let `k` be a field and `X`, `Y` schemes over `Spec k` with `Γ(X, 𝒪_X) = Γ(Y, 𝒪_Y) = k` (for
instance proper and geometrically integral over `k = k̄`), with rational points `x₀`, `y₀`. Let
`(Pᵢ)` and `(Qⱼ)` be affine open covers of `X` and `Y` with affine pairwise intersections (and
affine triple intersections for `X`), `(Pᵢ)` finite. A Čech `1`-cocycle of `𝒪` on the product
cover `(Pᵢ ⊠ Qⱼ)` of `X ×ₖ Y` whose restrictions to the axes `X × {y₀}` and `{x₀} × Y` are
coboundaries is a coboundary (`AlgebraicGeometry.OverField.exists_eq_cechD₀_of_cechD₁_eq_zero`).

This is the Künneth formula `H¹(X ×ₖ Y, 𝒪) = H¹(X, 𝒪) ⊗ Γ(Y, 𝒪) ⊕ Γ(X, 𝒪) ⊗ H¹(Y, 𝒪)` in the
form used in the proof of the theorem of the cube (Mumford, *Abelian varieties*, §6; Milne,
*Abelian varieties*, Lemma 5.3). The proof is direct: on each slice `X × Qⱼ` the cocycle is
`∑ eₜ ⊗ φⱼ,ₜ` plus a coboundary, with `(eₜ)` cocycles representing a basis of `Ȟ¹((Pᵢ), 𝒪_X)`
(`Γ(Pᵢ ⊠ Qⱼ) = Γ(Pᵢ) ⊗ Γ(Qⱼ)`, `KunnethAlgebra`); the `φⱼ,ₜ` glue to global functions on `Y`,
hence constants, which vanish at `y₀`. What is left descends to a cocycle on `Y`
(`Γ(X × V, 𝒪) = Γ(V, 𝒪)`), a coboundary by the `x₀`-axis hypothesis.

## References

* [D. Mumford, *Abelian varieties*, §5, §6][mumford1970]
* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace Opposite
open TensorProduct
open scoped AlgebraicGeometry.OverField

namespace AlgebraicGeometry.OverField

/-- Inclusions between finite intersections of opens. -/
local macro "ov_le" : tactic => `(tactic| (intro x hx; simp only [ov₁, ov₂,
  TopologicalSpace.Opens.mem_inf] at hx ⊢; tauto))

variable {k : Type u} [Field k]

lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) : f.appLE U V e x = g.appLE U V (hfg ▸ e) x := by
  subst hfg
  rfl

lemma appLE_appLE_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (V : Y.Opens)
    (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (x : Γ(Z, U)) :
    f.appLE V W e₂ (g.appLE U V e₁ x) =
      (f ≫ g).appLE U W (e₂.trans ((Opens.map f.base).map (homOfLE e₁)).le) x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

lemma appLE_res_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} (h : U' ≤ U) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U') (x : Γ(Y, U)) :
    f.appLE U' V e (Y.presheaf.map (homOfLE h).op x) =
      f.appLE U V (e.trans (f.preimage_mono h)) x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

lemma res_appLE_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) {V V' : X.Opens} (h : V' ≤ V)
    (e : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    X.presheaf.map (homOfLE h).op (f.appLE U V e x) = f.appLE U V' (h.trans e) x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

section Point

variable (X : Over (Spec (.of k))) {W : Over (Spec (.of k))} (y₀ : 𝟙_ (Over (Spec (.of k))) ⟶ W)

/-- The section `x ↦ (x, y₀)` of the projection `X ×ₖ W → X`. -/
noncomputable def sectionAt : X ⟶ X ⊗ W := lift (𝟙 X) (toUnit X ≫ y₀)

lemma sectionAt_fst_left : (sectionAt X y₀).left ≫ (fst X W).left = 𝟙 X.left := by
  rw [← Over.comp_left, sectionAt, lift_fst, Over.id_left]

lemma sectionAt_snd_left : (sectionAt X y₀).left ≫ (snd X W).left = X.hom ≫ y₀.left := by
  rw [← Over.comp_left, sectionAt, lift_snd, Over.comp_left]
  rfl

variable {X y₀} in
lemma le_preimage_sectionAt (O : X.left.Opens) {V' : W.left.Opens} (hy : ⊤ ≤ y₀.left ⁻¹ᵁ V') :
    O ≤ (sectionAt X y₀).left ⁻¹ᵁ box X W O V' := by
  rw [box, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    sectionAt_fst_left, sectionAt_snd_left, Scheme.Hom.id_preimage, Scheme.Hom.comp_preimage]
  exact le_inf le_rfl fun x _ ↦ hy trivial

variable {y₀} in
lemma appLE_appLE_algebraMap {V' : W.left.Opens} (hy : ⊤ ≤ y₀.left ⁻¹ᵁ V') (r : k) :
    (Scheme.ΓSpecIso (.of k)).hom (y₀.left.appLE V' ⊤ hy (algebraMap k Γ(W.left, V') r)) = r := by
  rw [algebraMap_eq, CommRingCat.comp_apply, appLE_appLE_apply,
    Scheme.Hom.appLE_apply_of_eq_id (Over.w y₀), ← CommRingCat.comp_apply, Iso.inv_hom_id,
    CommRingCat.id_apply]

variable {y₀} in
/-- Evaluation of functions on `V'` at a rational point `y₀ ∈ V'`. -/
noncomputable def evalAt {V' : W.left.Opens} (hy : ⊤ ≤ y₀.left ⁻¹ᵁ V') : Γ(W.left, V') →ₐ[k] k where
  toRingHom := (Scheme.ΓSpecIso (.of k)).hom.hom.comp (y₀.left.appLE V' ⊤ hy).hom
  commutes' r := appLE_appLE_algebraMap hy r

variable {y₀} in
lemma evalAt_apply {V' : W.left.Opens} (hy : ⊤ ≤ y₀.left ⁻¹ᵁ V') (b : Γ(W.left, V')) :
    evalAt hy b = (Scheme.ΓSpecIso (.of k)).hom (y₀.left.appLE V' ⊤ hy b) :=
  rfl

variable {y₀} in
lemma algebraMap_evalAt {V' : W.left.Opens} (hy : ⊤ ≤ y₀.left ⁻¹ᵁ V') (O : X.left.Opens)
    (b : Γ(W.left, V')) :
    algebraMap k Γ(X.left, O) (evalAt hy b) =
      X.hom.appLE ⊤ O (le_preimage_top _ _) (y₀.left.appLE V' ⊤ hy b) := by
  rw [algebraMap_eq, evalAt_apply, CommRingCat.comp_apply, ← CommRingCat.comp_apply
    (Scheme.ΓSpecIso (.of k)).hom, Iso.hom_inv_id, CommRingCat.id_apply]

variable {y₀} in
/-- The section `x ↦ (x, y₀)` pulls back `a ⊗ b` to `b(y₀) a`. -/
theorem sectionAt_appLE_mulTensor (O : X.left.Opens) {V' : W.left.Opens}
    (hy : ⊤ ≤ y₀.left ⁻¹ᵁ V') (a : Γ(X.left, O)) (b : Γ(W.left, V')) :
    (sectionAt X y₀).left.appLE (box X W O V') O (le_preimage_sectionAt O hy)
      (mulTensor O V' (a ⊗ₜ b)) = evalAt hy b • a := by
  rw [mulTensor_tmul, map_mul, appLE_appLE_apply, appLE_appLE_apply]
  rw [Scheme.Hom.appLE_apply_of_eq_id (sectionAt_fst_left X y₀)]
  rw [appLE_eq_of_eq (sectionAt_snd_left X y₀)]
  rw [← appLE_appLE_apply (e₁ := hy) (e₂ := le_preimage_top _ _)]
  rw [Algebra.smul_def, algebraMap_evalAt, mul_comm]

variable {y₀} in
lemma sectionAt_appLE_tensorPi {ι : Type*} (O : ι → X.left.Opens) {V' : W.left.Opens}
    (hy : ⊤ ≤ y₀.left ⁻¹ᵁ V') (z : (∀ i, Γ(X.left, O i)) ⊗[k] Γ(W.left, V')) :
    (fun i ↦ (sectionAt X y₀).left.appLE _ (O i) (le_preimage_sectionAt (O i) hy)
      (tensorPi O V' z i)) = TensorProduct.rid k _ ((evalAt hy).toLinearMap.lTensor _ z) := by
  induction z using TensorProduct.induction_on with
  | zero => funext i; simp
  | tmul a b =>
    funext i
    rw [tensorPi_tmul, sectionAt_appLE_mulTensor, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    rfl
  | add x y hx hy' =>
    funext i
    rw [map_add, map_add, map_add, ← hx, ← hy', Pi.add_apply, map_add]
    rfl

end Point

section PointLeft

variable {X : Over (Spec (.of k))} (Y : Over (Spec (.of k))) (x₀ : 𝟙_ (Over (Spec (.of k))) ⟶ X)

/-- The section `y ↦ (x₀, y)` of the projection `X ×ₖ Y → Y`. -/
noncomputable def sectionAt' : Y ⟶ X ⊗ Y := lift (toUnit Y ≫ x₀) (𝟙 Y)

lemma sectionAt'_snd_left : (sectionAt' Y x₀).left ≫ (snd X Y).left = 𝟙 Y.left := by
  rw [← Over.comp_left, sectionAt', lift_snd, Over.id_left]

lemma sectionAt'_fst_left : (sectionAt' Y x₀).left ≫ (fst X Y).left = Y.hom ≫ x₀.left := by
  rw [← Over.comp_left, sectionAt', lift_fst, Over.comp_left]
  rfl

variable {Y x₀} in
lemma le_preimage_sectionAt' (O' : Y.left.Opens) {V : X.left.Opens} (hx : ⊤ ≤ x₀.left ⁻¹ᵁ V) :
    O' ≤ (sectionAt' Y x₀).left ⁻¹ᵁ box X Y V O' := by
  rw [box, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    sectionAt'_fst_left, sectionAt'_snd_left, Scheme.Hom.id_preimage, Scheme.Hom.comp_preimage]
  exact le_inf (fun x _ ↦ hx trivial) le_rfl

end PointLeft

section Cocycle

variable {S : Over (Spec (.of k))} {I : Type*}

lemma cechD₁_cechD₀ (O₀ : I → S.left.Opens) (O₁ : I × I → S.left.Opens)
    (O₂ : I × I × I → S.left.Opens) (h₁ : ∀ p, O₁ p ≤ O₀ p.1 ⊓ O₀ p.2)
    (h₂ : ∀ t, O₂ t ≤ O₁ (t.1, t.2.1) ⊓ O₁ (t.2.1, t.2.2) ⊓ O₁ (t.1, t.2.2))
    (a : ∀ i, Γ(S.left, O₀ i)) : cechD₁ O₁ O₂ h₂ (cechD₀ O₀ O₁ h₁ a) = 0 := by
  funext t
  simp only [cechD₁_apply, cechD₀_apply, map_sub, CohomologyAux.presheaf_map_map, Pi.zero_apply]
  abel

/-- The cocycle condition `c (i, j) + c (j, l) - c (i, l) = 0`, restricted to an open `T` inside the
triple overlap. -/
lemma cechD₁_res_eq_zero {O₁ : I × I → S.left.Opens} {O₂ : I × I × I → S.left.Opens}
    {h : ∀ t, O₂ t ≤ O₁ (t.1, t.2.1) ⊓ O₁ (t.2.1, t.2.2) ⊓ O₁ (t.1, t.2.2)}
    {c : ∀ p, Γ(S.left, O₁ p)} (hc : cechD₁ O₁ O₂ h c = 0) (t : I × I × I) {T : S.left.Opens}
    (hT : T ≤ O₂ t) :
    S.left.presheaf.map (homOfLE (hT.trans ((h t).trans (inf_le_left.trans inf_le_left)))).op
        (c (t.1, t.2.1)) +
      S.left.presheaf.map (homOfLE (hT.trans ((h t).trans (inf_le_left.trans inf_le_right)))).op
        (c (t.2.1, t.2.2)) -
      S.left.presheaf.map (homOfLE (hT.trans ((h t).trans inf_le_right))).op (c (t.1, t.2.2)) =
        0 := by
  have h1 := congrFun hc t
  rw [cechD₁_apply, Pi.zero_apply] at h1
  have h2 := congrArg (S.left.presheaf.map (homOfLE hT).op) h1
  rw [map_sub, map_add, map_zero, CohomologyAux.presheaf_map_map,
    CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_map] at h2
  exact h2

/-- `cechD₀`, restricted to an open `T` inside the overlap. -/
lemma cechD₀_res (O₀ : I → S.left.Opens) (O₁ : I × I → S.left.Opens)
    (h : ∀ p, O₁ p ≤ O₀ p.1 ⊓ O₀ p.2) (a : ∀ i, Γ(S.left, O₀ i)) (p : I × I)
    {T : S.left.Opens} (hT : T ≤ O₁ p) :
    S.left.presheaf.map (homOfLE hT).op (cechD₀ O₀ O₁ h a p) =
      S.left.presheaf.map (homOfLE (hT.trans ((h p).trans inf_le_left))).op (a p.1) -
        S.left.presheaf.map (homOfLE (hT.trans ((h p).trans inf_le_right))).op (a p.2) := by
  rw [cechD₀_apply, map_sub, CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_map]

end Cocycle

section ProductCover

variable {X Y : Over (Spec (.of k))} {I J : Type*} (P : I → X.left.Opens) (Q : J → Y.left.Opens)

/-- The product cover `Pᵢ ⊠ Qⱼ` of `X ×ₖ Y`. -/
noncomputable abbrev prodOv₀ (q : I × J) : (X ⊗ Y).left.Opens := box X Y (P q.1) (Q q.2)

/-- Pairwise intersections of the product cover. -/
noncomputable abbrev prodOv₁ (p : (I × J) × (I × J)) : (X ⊗ Y).left.Opens :=
  box X Y (ov₁ P (p.1.1, p.2.1)) (ov₁ Q (p.1.2, p.2.2))

/-- Triple intersections of the product cover. -/
noncomputable abbrev prodOv₂ (t : (I × J) × (I × J) × (I × J)) : (X ⊗ Y).left.Opens :=
  box X Y (ov₂ P (t.1.1, t.2.1.1, t.2.2.1)) (ov₂ Q (t.1.2, t.2.1.2, t.2.2.2))

lemma prodOv₁_le (p : (I × J) × (I × J)) :
    prodOv₁ P Q p ≤ prodOv₀ P Q p.1 ⊓ prodOv₀ P Q p.2 :=
  le_inf (box_mono inf_le_left inf_le_left) (box_mono inf_le_right inf_le_right)

lemma prodOv₂_le (t : (I × J) × (I × J) × (I × J)) :
    prodOv₂ P Q t ≤ prodOv₁ P Q (t.1, t.2.1) ⊓ prodOv₁ P Q (t.2.1, t.2.2) ⊓
      prodOv₁ P Q (t.1, t.2.2) :=
  le_inf (le_inf
      (box_mono ((ov₂_le P _).trans (inf_le_left.trans inf_le_left))
        ((ov₂_le Q _).trans (inf_le_left.trans inf_le_left)))
      (box_mono ((ov₂_le P _).trans (inf_le_left.trans inf_le_right))
        ((ov₂_le Q _).trans (inf_le_left.trans inf_le_right))))
    (box_mono ((ov₂_le P _).trans inf_le_right) ((ov₂_le Q _).trans inf_le_right))

lemma box_inf_box_le {X Y : Over (Spec (.of k))} (V₁ V₂ : X.left.Opens) (V₁' V₂' : Y.left.Opens) :
    box X Y V₁ V₁' ⊓ box X Y V₂ V₂' ≤ box X Y (V₁ ⊓ V₂) (V₁' ⊓ V₂') := by
  rintro x ⟨⟨h₁, h₁'⟩, ⟨h₂, h₂'⟩⟩
  exact ⟨⟨h₁, h₂⟩, ⟨h₁', h₂'⟩⟩

lemma le_iSup_box {X Y : Over (Spec (.of k))} {I : Type*} (P : I → X.left.Opens)
    (hPcov : ⨆ i, P i = ⊤) (V' : Y.left.Opens) :
    (snd X Y).left ⁻¹ᵁ V' ≤ ⨆ i, box X Y (P i) V' := by
  intro x hx
  have : (fst X Y).left x ∈ ⨆ i, P i := by rw [hPcov]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 this
  exact Opens.mem_iSup.2 ⟨i, ⟨hi, hx⟩⟩

end ProductCover

section Linear

variable {K₀ K₁ M N : Type*} [AddCommGroup K₀] [Module k K₀] [AddCommGroup K₁] [Module k K₁]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

lemma lTensor_finsupp_sum {ι : Type*} (e : ι → K₁) (g : M →ₗ[k] N) (φ : ι →₀ M) :
    g.lTensor K₁ (φ.sum fun t c ↦ e t ⊗ₜ c) =
      (φ.mapRange g (map_zero g)).sum fun t c ↦ e t ⊗ₜ c := by
  rw [Finsupp.sum_mapRange_index (fun t ↦ tmul_zero _ (e t)), map_finsuppSum]
  simp only [LinearMap.lTensor_tmul]

lemma rid_rTensor (d : K₀ →ₗ[k] K₁) (u : K₀ ⊗[k] k) :
    TensorProduct.rid k K₁ (d.rTensor k u) = d (TensorProduct.rid k K₀ u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

lemma rid_finsupp_sum {ι : Type*} (e : ι → K₁) (φ : ι →₀ k) :
    TensorProduct.rid k K₁ (φ.sum fun t c ↦ e t ⊗ₜ c) = φ.sum fun t a ↦ a • e t := by
  rw [map_finsuppSum]
  simp only [TensorProduct.rid_tmul]

end Linear

section Kunneth

variable {X Y : Over (Spec (.of k))} {I J : Type*} [Fintype I] [DecidableEq I]
  (P : I → X.left.Opens) (Q : J → Y.left.Opens)

lemma le_ov₁_self {S : Scheme.{u}} {ι : Type*} (O : ι → S.Opens) (i : ι) : O i ≤ ov₁ O (i, i) :=
  le_inf le_rfl le_rfl

-- The Čech comparison is one long linear combination; the default heartbeat limit stops it.
set_option maxHeartbeats 1000000 in
/-- **Künneth for `H¹(𝒪)` on product covers, in Čech form.** Let `X`, `Y` be schemes over a field
`k` with `Γ(X, 𝒪_X) = Γ(Y, 𝒪_Y) = k` (`X` quasi-compact and quasi-separated over `k`), `x₀`, `y₀`
rational points, `(Pᵢ)` a finite affine open cover of `X` with affine pairwise and triple
intersections and `(Qⱼ)` an affine open cover of `Y` with affine pairwise intersections, with
`x₀ ∈ P i₀` and `y₀ ∈ Q j₀`. Let `c` be a Čech `1`-cocycle of `𝒪` on the product cover
`(Pᵢ ⊠ Qⱼ)` of `X ×ₖ Y` whose restriction to the axis `X × {y₀}` (on the cover `(Pᵢ × {y₀})`) is the
coboundary of `a` and whose restriction to `{x₀} × Y` (on `({x₀} × Qⱼ)`) is the coboundary of `b`.
Then `c` is a coboundary. -/
theorem exists_eq_cechD₀_of_cechD₁_eq_zero [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (hX : ∀ V : (Spec (.of k)).Opens, IsIso (X.hom.app V)) (hY : IsIso (Y.hom.app ⊤))
    (x₀ : 𝟙_ (Over (Spec (.of k))) ⟶ X) (y₀ : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (hPcov : ⨆ i, P i = ⊤) (hQcov : ⨆ j, Q j = ⊤)
    (hP : ∀ i, IsAffineOpen (P i)) (hP₁ : ∀ p, IsAffineOpen (ov₁ P p))
    (hP₂ : ∀ t, IsAffineOpen (ov₂ P t)) (hQ : ∀ j, IsAffineOpen (Q j))
    (hQ₁ : ∀ p, IsAffineOpen (ov₁ Q p))
    (i₀ : I) (hi₀ : ⊤ ≤ x₀.left ⁻¹ᵁ P i₀) (j₀ : J) (hj₀ : ⊤ ≤ y₀.left ⁻¹ᵁ Q j₀)
    (c : ∀ p, Γ((X ⊗ Y).left, prodOv₁ P Q p))
    (hc : cechD₁ (prodOv₁ P Q) (prodOv₂ P Q) (prodOv₂_le P Q) c = 0)
    (a : ∀ i, Γ(X.left, P i))
    (ha : ∀ i i', (sectionAt X y₀).left.appLE _ (ov₁ P (i, i'))
      (le_preimage_sectionAt _ (hj₀.trans (y₀.left.preimage_mono (le_ov₁_self Q j₀))))
        (c ((i, j₀), (i', j₀))) = cechD₀ P (ov₁ P) (ov₁_le P) a (i, i'))
    (b : ∀ j, Γ(Y.left, Q j))
    (hb : ∀ j j', (sectionAt' Y x₀).left.appLE _ (ov₁ Q (j, j'))
      (le_preimage_sectionAt' _ (hi₀.trans (x₀.left.preimage_mono (le_ov₁_self P i₀))))
        (c ((i₀, j), (i₀, j'))) = cechD₀ Q (ov₁ Q) (ov₁_le Q) b (j, j')) :
    ∃ v : ∀ q, Γ((X ⊗ Y).left, prodOv₀ P Q q),
      c = cechD₀ (prodOv₀ P Q) (prodOv₁ P Q) (prodOv₁_le P Q) v := by
  classical
  set d₀ := cechD₀ P (ov₁ P) (ov₁_le P) with hd₀
  set d₁ := cechD₁ (ov₁ P) (ov₂ P) (ov₂_le P) with hd₁
  obtain ⟨-, hspan, hind⟩ := LinearMap.cocycleBasis_spec d₀ d₁
  set e := LinearMap.cocycleBasis d₀ d₁ with he
  -- the slices `c|_{X × Qⱼ}`
  let cs (j : J) : ∀ p : I × I, Γ((X ⊗ Y).left, box X Y (ov₁ P p) (Q j)) := fun p ↦
    (X ⊗ Y).left.presheaf.map (homOfLE (show box X Y (ov₁ P p) (Q j) ≤
      prodOv₁ P Q ((p.1, j), (p.2, j)) from box_mono le_rfl (le_ov₁_self Q j))).op
      (c ((p.1, j), (p.2, j)))
  have hcs (j : J) : cechD₁ (S := X ⊗ Y) (fun p ↦ box X Y (ov₁ P p) (Q j))
      (fun t ↦ box X Y (ov₂ P t) (Q j)) (box_ov₂_le (Q j) P) (cs j) = 0 := by
    funext t
    have h := cechD₁_res_eq_zero hc ((t.1, j), (t.2.1, j), (t.2.2, j))
      (show box X Y (ov₂ P t) (Q j) ≤ prodOv₂ P Q ((t.1, j), (t.2.1, j), (t.2.2, j)) from
        box_mono le_rfl (le_inf (le_ov₁_self Q j) le_rfl))
    rw [cechD₁_apply, Pi.zero_apply]
    simp only [cs, CohomologyAux.presheaf_map_map]
    exact h
  choose z hz using fun j ↦ (bijective_tensorPi (ov₁ P) hP₁ (hQ j)).2 (cs j)
  have hzc (j : J) : d₁.rTensor _ (z j) = 0 := by
    apply (bijective_tensorPi (ov₂ P) hP₂ (hQ j)).1
    rw [map_zero, ← LinearMap.comp_apply (tensorPi (ov₂ P) (Q j)), hd₁,
      tensorPi_comp_rTensor_cechD₁, LinearMap.comp_apply, hz, hcs]
  choose φ w hφ using fun j ↦
    LinearMap.exists_eq_finsupp_sum_tmul_add_of_rTensor_eq_zero d₀ d₁ e hspan (z j) (hzc j)
  -- the slices agree on overlaps up to coboundaries
  have hA (j j' : J) : ∃ w', (resAlgHom Y (show ov₁ Q (j, j') ≤ Q j from inf_le_left)).toLinearMap.lTensor
      _ (z j) - (resAlgHom Y (show ov₁ Q (j, j') ≤ Q j' from inf_le_right)).toLinearMap.lTensor _ (z j') =
        d₀.rTensor _ w' := by
    obtain ⟨w', hw'⟩ := (bijective_tensorPi P hP (hQ₁ (j, j'))).2 (fun α ↦
      (X ⊗ Y).left.presheaf.map (homOfLE (show box X Y (P α) (ov₁ Q (j, j')) ≤
        prodOv₁ P Q ((α, j), (α, j')) from box_mono (le_ov₁_self P α) le_rfl)).op
        (c ((α, j), (α, j'))))
    refine ⟨w', (bijective_tensorPi (ov₁ P) hP₁ (hQ₁ (j, j'))).1 ?_⟩
    rw [LinearMap.map_sub, ← LinearMap.comp_apply (tensorPi (ov₁ P) (ov₁ Q (j, j'))),
      ← LinearMap.comp_apply (tensorPi (ov₁ P) (ov₁ Q (j, j'))),
      ← LinearMap.comp_apply (tensorPi (ov₁ P) (ov₁ Q (j, j'))), tensorPi_comp_lTensor,
      tensorPi_comp_lTensor, hd₀, tensorPi_comp_rTensor_cechD₀]
    simp only [LinearMap.comp_apply, hz, hw']
    funext p
    have h1 := cechD₁_res_eq_zero hc ((p.1, j), (p.2, j), (p.2, j'))
      (show box X Y (ov₁ P p) (ov₁ Q (j, j')) ≤ prodOv₂ P Q ((p.1, j), (p.2, j), (p.2, j')) from
        box_mono (by ov_le) (by ov_le))
    have h2 := cechD₁_res_eq_zero hc ((p.1, j), (p.1, j'), (p.2, j'))
      (show box X Y (ov₁ P p) (ov₁ Q (j, j')) ≤ prodOv₂ P Q ((p.1, j), (p.1, j'), (p.2, j')) from
        box_mono (by ov_le) (by ov_le))
    dsimp only at h1 h2
    rw [Pi.sub_apply, cechD₀_apply]
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      AlgHom.toLinearMap_apply, resAlgHom_apply, cs, CohomologyAux.presheaf_map_map]
    linear_combination h1 - h2
  -- hence the coefficients agree on overlaps
  have hcompat (j j' : J) : (φ j).mapRange (resAlgHom Y (show ov₁ Q (j, j') ≤ Q j from inf_le_left))
      (map_zero _) = (φ j').mapRange (resAlgHom Y (show ov₁ Q (j, j') ≤ Q j' from inf_le_right))
      (map_zero _) := by
    obtain ⟨w', hw'⟩ := hA j j'
    rw [← sub_eq_zero]
    apply LinearMap.eq_zero_of_finsupp_sum_tmul_mem_range_rTensor d₀ e hind
    set r₁ := resAlgHom Y (show ov₁ Q (j, j') ≤ Q j from inf_le_left)
    set r₂ := resAlgHom Y (show ov₁ Q (j, j') ≤ Q j' from inf_le_right)
    have e₁ : ((φ j).mapRange r₁ (map_zero _)).sum (fun t c ↦ e t ⊗ₜ c) =
        r₁.toLinearMap.lTensor _ (z j) - d₀.rTensor _ (r₁.toLinearMap.lTensor _ (w j)) := by
      rw [hφ j, map_add, lTensor_finsupp_sum, rTensor_lTensor_apply]
      abel
    have e₂ : ((φ j').mapRange r₂ (map_zero _)).sum (fun t c ↦ e t ⊗ₜ c) =
        r₂.toLinearMap.lTensor _ (z j') - d₀.rTensor _ (r₂.toLinearMap.lTensor _ (w j')) := by
      rw [hφ j', map_add, lTensor_finsupp_sum, rTensor_lTensor_apply]
      abel
    have hsub : ((φ j).mapRange r₁ (map_zero _) - (φ j').mapRange r₂ (map_zero _)).sum
        (fun t c ↦ e t ⊗ₜ c) = ((φ j).mapRange r₁ (map_zero _)).sum (fun t c ↦ e t ⊗ₜ c) -
          ((φ j').mapRange r₂ (map_zero _)).sum (fun t c ↦ e t ⊗ₜ c) :=
      Finsupp.sum_sub_index (fun t c c' ↦ TensorProduct.tmul_sub (R := k) (e t) c c')
    rw [hsub, e₁, e₂]
    refine ⟨w' - r₁.toLinearMap.lTensor _ (w j) + r₂.toLinearMap.lTensor _ (w j'), ?_⟩
    rw [map_add, map_sub, ← hw']
    abel
  -- the coefficients are constants
  have hconst (t : LinearMap.CocycleBasisIndex d₀ d₁) :
      ∃ r : k, (fun j ↦ φ j t) = algebraMap k (∀ j, Γ(Y.left, Q j)) r := by
    obtain ⟨r, hr⟩ := ((exact_algebraMap_cechD₀ Q hY hQcov) (fun j ↦ φ j t)).1 (by
      funext p
      have := congrArg (fun φ' ↦ φ' t) (hcompat p.1 p.2)
      simp only [Finsupp.mapRange_apply, resAlgHom_apply] at this
      rw [cechD₀_apply, Pi.zero_apply, sub_eq_zero]
      exact this)
    exact ⟨r, hr.symm⟩
  choose r hr using hconst
  -- which vanish, by the `y₀`-axis hypothesis
  have hy₀ : ⊤ ≤ y₀.left ⁻¹ᵁ Q j₀ := hj₀
  have hev : TensorProduct.rid k _ ((evalAt hy₀).toLinearMap.lTensor _ (z j₀)) = d₀ a := by
    rw [← sectionAt_appLE_tensorPi X (ov₁ P) hy₀, hz]
    funext p
    rw [← ha p.1 p.2]
    simp only [cs]
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have hr0 (t) : r t = 0 := by
    have h1 : (φ j₀).mapRange (evalAt hy₀) (map_zero _) = 0 := by
      apply hind
      have := hev
      rw [hφ j₀, map_add, lTensor_finsupp_sum, map_add, rid_finsupp_sum,
        ← rTensor_lTensor_apply, rid_rTensor] at this
      refine ⟨a - TensorProduct.rid k _ ((evalAt hy₀).toLinearMap.lTensor _ (w j₀)), ?_⟩
      rw [map_sub, ← this]
      abel
    have h2 := congrArg (fun ψ ↦ ψ t) h1
    have h3 := congrFun (hr t) j₀
    simp only [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply] at h2
    simp only [Pi.algebraMap_apply] at h3
    rw [h3, AlgHom.commutes] at h2
    exact h2
  have hφ0 (j : J) : φ j = 0 := by
    ext t
    have := congrFun (hr t) j
    simp only [Pi.algebraMap_apply, hr0, map_zero] at this
    exact this
  -- so every slice is a coboundary
  let A : ∀ q : I × J, Γ((X ⊗ Y).left, prodOv₀ P Q q) := fun q ↦ tensorPi P (Q q.2) (w q.2) q.1
  have hAs (j : J) (p : I × I) : cs j p = cechD₀ (S := X ⊗ Y) (fun i ↦ box X Y (P i) (Q j))
      (fun p ↦ box X Y (ov₁ P p) (Q j)) (box_ov₁_le (Q j) P) (tensorPi P (Q j) (w j)) p := by
    rw [← hz, hφ j, hφ0 j, Finsupp.sum_zero_index, zero_add, ← LinearMap.comp_apply
      (tensorPi (ov₁ P) (Q j)), hd₀, tensorPi_comp_rTensor_cechD₀, LinearMap.comp_apply]
  set c' := c - cechD₀ (prodOv₀ P Q) (prodOv₁ P Q) (prodOv₁_le P Q) A with hc'def
  have hc' : cechD₁ (prodOv₁ P Q) (prodOv₂ P Q) (prodOv₂_le P Q) c' = 0 := by
    rw [hc'def, map_sub, hc, cechD₁_cechD₀, sub_zero]
  have hc'0 (α α' : I) (j : J) : c' ((α, j), (α', j)) = 0 := by
    have heq : box X Y (ov₁ P (α, α')) (Q j) = prodOv₁ P Q ((α, j), (α', j)) :=
      le_antisymm (box_mono le_rfl (le_ov₁_self Q j)) (box_mono le_rfl inf_le_left)
    apply CohomologyAux.presheaf_map_injective_of_eq heq
    have := hAs j (α, α')
    simp only [cs] at this
    rw [hc'def, Pi.sub_apply, map_sub, map_zero, this, sub_eq_zero, cechD₀_res, cechD₀_apply]
  -- the remaining cocycle descends to `Y`
  have hD (j j' : J) : ∃ D : Γ((X ⊗ Y).left, (snd X Y).left ⁻¹ᵁ ov₁ Q (j, j')), ∀ α,
      (X ⊗ Y).left.presheaf.map (homOfLE (box_le_snd (P α) (ov₁ Q (j, j')))).op D =
        (X ⊗ Y).left.presheaf.map (homOfLE (show box X Y (P α) (ov₁ Q (j, j')) ≤
          prodOv₁ P Q ((α, j), (α, j')) from box_mono (le_ov₁_self P α) le_rfl)).op
          (c' ((α, j), (α, j'))) := by
    refine exists_glue _ (fun α ↦ box_le_snd (P α) _) (le_iSup_box P hPcov _) _ fun α α' ↦ ?_
    have hle := box_inf_box_le (X := X) (Y := Y) (P α) (P α') (ov₁ Q (j, j')) (ov₁ Q (j, j'))
    have h1 := cechD₁_res_eq_zero hc' ((α, j), (α', j), (α', j'))
      (show box X Y (P α) (ov₁ Q (j, j')) ⊓ box X Y (P α') (ov₁ Q (j, j')) ≤
        prodOv₂ P Q ((α, j), (α', j), (α', j')) from hle.trans (box_mono (by ov_le) (by ov_le)))
    have h2 := cechD₁_res_eq_zero hc' ((α, j), (α, j'), (α', j'))
      (show box X Y (P α) (ov₁ Q (j, j')) ⊓ box X Y (P α') (ov₁ Q (j, j')) ≤
        prodOv₂ P Q ((α, j), (α, j'), (α', j')) from hle.trans (box_mono (by ov_le) (by ov_le)))
    dsimp only at h1 h2
    rw [hc'0, map_zero] at h1
    rw [hc'0, map_zero] at h2
    simp only [CohomologyAux.presheaf_map_map]
    linear_combination h2 - h1
  choose D hDres using hD
  have hsurj (j j' : J) : ∃ d, (snd X Y).left.app (ov₁ Q (j, j')) d = D j j' := by
    have := isIso_app_snd_tensor X Y hX (ov₁ Q (j, j'))
    exact (ConcreteCategory.bijective_of_isIso _).2 (D j j')
  choose dY hdY using hsurj
  -- `dY` is computed on the axis `{x₀} × Y`
  have hx₀ : ⊤ ≤ x₀.left ⁻¹ᵁ P i₀ := hi₀
  let b' : ∀ j, Γ(Y.left, Q j) := fun j ↦ b j - (sectionAt' Y x₀).left.appLE (prodOv₀ P Q (i₀, j))
    (Q j) (le_preimage_sectionAt' (Q j) hx₀) (A (i₀, j))
  have hdYb (j j' : J) : dY j j' = cechD₀ Q (ov₁ Q) (ov₁_le Q) b' (j, j') := by
    have hid : (sectionAt' Y x₀).left.appLE ((snd X Y).left ⁻¹ᵁ ov₁ Q (j, j')) (ov₁ Q (j, j'))
        (by rw [← Scheme.Hom.comp_preimage, sectionAt'_snd_left, Scheme.Hom.id_preimage])
        (D j j') = dY j j' := by
      rw [← hdY, Scheme.Hom.app_eq_appLE, appLE_appLE_apply,
        Scheme.Hom.appLE_apply_of_eq_id (sectionAt'_snd_left Y x₀)]
    rw [← hid]
    have h1 := congrArg ((sectionAt' Y x₀).left.appLE (box X Y (P i₀) (ov₁ Q (j, j')))
      (ov₁ Q (j, j')) (le_preimage_sectionAt' _ hx₀)) (hDres j j' i₀)
    rw [appLE_res_apply, appLE_res_apply] at h1
    rw [h1, hc'def, Pi.sub_apply, map_sub, hb j j', cechD₀_apply, cechD₀_apply, cechD₀_apply,
      map_sub, appLE_res_apply, appLE_res_apply]
    simp only [b', map_sub, res_appLE_apply]
    abel
  -- the coboundary
  refine ⟨fun q ↦ A q + (snd X Y).left.appLE (Q q.2) (prodOv₀ P Q q) (box_le_snd _ _) (b' q.2),
    ?_⟩
  funext p
  obtain ⟨⟨α, j⟩, ⟨α', j'⟩⟩ := p
  have hT : prodOv₂ P Q ((α, j), (α, j'), (α', j')) = prodOv₁ P Q ((α, j), (α', j')) :=
    le_antisymm (box_mono (by ov_le) (by ov_le)) (box_mono (by ov_le) (by ov_le))
  have key : c' ((α, j), (α', j')) = (X ⊗ Y).left.presheaf.map (homOfLE
      ((prodOv₁_le P Q ((α, j), (α', j'))).trans inf_le_left)).op
      ((snd X Y).left.appLE (Q j) (prodOv₀ P Q (α, j)) (box_le_snd _ _) (b' j)) -
      (X ⊗ Y).left.presheaf.map (homOfLE ((prodOv₁_le P Q ((α, j), (α', j'))).trans
        inf_le_right)).op
        ((snd X Y).left.appLE (Q j') (prodOv₀ P Q (α', j')) (box_le_snd _ _) (b' j')) := by
    apply CohomologyAux.presheaf_map_injective_of_eq hT
    have h1 := cechD₁_res_eq_zero hc' ((α, j), (α, j'), (α', j')) (le_refl _)
    dsimp only at h1
    rw [hc'0, map_zero] at h1
    have h2 := congrArg ((X ⊗ Y).left.presheaf.map (homOfLE (show
      prodOv₂ P Q ((α, j), (α, j'), (α', j')) ≤ box X Y (P α) (ov₁ Q (j, j')) from
        box_mono (by ov_le) (by ov_le))).op) (hDres j j' α)
    rw [← hdY, hdYb j j', CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_map,
      cechD₀_apply, Scheme.Hom.app_eq_appLE, res_appLE_apply, map_sub, appLE_res_apply,
      appLE_res_apply] at h2
    rw [map_sub, res_appLE_apply, res_appLE_apply, res_appLE_apply, res_appLE_apply]
    linear_combination -h1 - h2
  have hcc : c ((α, j), (α', j')) = c' ((α, j), (α', j')) +
      cechD₀ (prodOv₀ P Q) (prodOv₁ P Q) (prodOv₁_le P Q) A ((α, j), (α', j')) := by
    rw [hc'def, Pi.sub_apply, sub_add_cancel]
  rw [hcc, key, cechD₀_apply, cechD₀_apply, map_add, map_add]
  abel

end Kunneth

end AlgebraicGeometry.OverField
