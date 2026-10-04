/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.Picard
import SGA.Foundations.Projective.LineBundle
import SGA.Foundations.Projective.NormLineBundle

/-!
# Functoriality of the Picard group, and trivial line bundles

Line bundles are presented by transition functions (`Scheme.LineBundle`, in
`SGA.Foundations.Ample`) and `Pic X` is the group of their classes (`Scheme.Pic`,
`Scheme.LineBundle.class`, in `SGA.Foundations.Etale.Picard`). We add:

* `Scheme.LineBundle.pullback_tensor`, `Scheme.LineBundle.pullback_dual`: the inverse image
  commutes with tensor products and duals;
* `Scheme.LineBundle.class_pullback_eq_one`: the inverse image of a trivial line bundle is
  trivial;
* `Scheme.Pic.pullback f : Pic X →* Pic Y` for `f : Y ⟶ X`, with
  `Scheme.Pic.pullback_class : Pic.pullback f L.class = (L.pullback f).class`,
  `Scheme.Pic.pullback_comp` and `Scheme.Pic.pullback_id` (EGA 0_I 5.4.8; Hartshorne II.6.13);
* `Scheme.LineBundle.class_eq_one_iff_nonempty_trivialization`: `L` is trivial iff it has a
  section vanishing nowhere;
* `Scheme.LineBundle.class_eq_one_of_top_le`: a line bundle trivialized by a chart which is the
  whole scheme is trivial; consequently `Pic` of a local scheme is trivial
  (`Scheme.Pic.subsingleton_of_forall_eq_top`, `Scheme.Pic.subsingleton_spec_of_isLocalRing`),
  and `Scheme.LineBundle.class_pullback_eq_one_of_range_subset`: the inverse image along a
  morphism whose image lies in a chart is trivial;
* `Scheme.LineBundle.pow n` (`n ∈ ℤ`, same charts, transition functions `gᵢⱼⁿ`) with
  `Scheme.LineBundle.class_pow : (L.pow n).class = L.class ^ n`, and
  `Scheme.LineBundle.exists_isSection_isUnit_of_class_zpow_eq_one`: if `L^{⊗n}` is trivial, `L`
  has an invertible section of `L^{⊗n}`;
* `Scheme.LineBundle.famLocus_eq_top_of_class_pow_eq_one`: on an integral scheme universally
  closed over a field, a section of a line bundle some positive power of which is trivial, and
  which does not vanish at one point, vanishes nowhere (`Γ(X, 𝒪_X)` is a field,
  `Scheme.LineBundle.basicOpen_eq_top_or_eq_zero`).

## References

* [A. Grothendieck, J. Dieudonné, *EGA* 0_I 5.4][EGA]
* [R. Hartshorne, *Algebraic geometry*, II.6][hartshorne1977]
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

namespace LineBundle

variable {X Y Z : Scheme.{u}}

section Pullback

variable (L M : X.LineBundle) (f : Y ⟶ X)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image commutes with tensor products. -/
lemma pullback_tensor : (L.tensor M).pullback f = (L.pullback f).tensor (M.pullback f) := by
  simp only [pullback, tensor]
  congr
  funext p q
  ext
  simp only [tensorG, Units.coe_map, MonoidHom.coe_coe, Units.val_mul, map_mul,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image commutes with duals. -/
lemma pullback_dual : L.dual.pullback f = (L.pullback f).dual := by
  simp only [pullback, dual]
  congr

lemma map_appLE_resUnits {U V : X.Opens} {V' : Y.Opens} (h : V ≤ U) (hV : V' ≤ f ⁻¹ᵁ V)
    (a : (Γ(X, U))ˣ) :
    Units.map (f.appLE V V' hV).hom.toMonoidHom (resUnits h a) =
      Units.map (f.appLE U V' (hV.trans (f.preimage_mono h))).hom.toMonoidHom a := by
  apply Units.ext
  change (X.presheaf.map (homOfLE h).op ≫ f.appLE V V' hV) a = f.appLE U V' _ a
  rw [Scheme.Hom.map_appLE]

lemma resUnits_map_appLE {U : X.Opens} {U' V' : Y.Opens} (hU : U' ≤ f ⁻¹ᵁ U) (h : V' ≤ U')
    (a : (Γ(X, U))ˣ) :
    resUnits h (Units.map (f.appLE U U' hU).hom.toMonoidHom a) =
      Units.map (f.appLE U V' (h.trans hU)).hom.toMonoidHom a := by
  apply Units.ext
  change (f.appLE U U' hU ≫ Y.presheaf.map (homOfLE h).op) a = f.appLE U V' _ a
  rw [Scheme.Hom.appLE_map]

/-- The inverse image of a trivial line bundle is trivial. -/
lemma class_pullback_eq_one {L : X.LineBundle} (hL : L.class = 1) : (L.pullback f).class = 1 := by
  obtain ⟨u, hu⟩ := (class_eq_one_iff L).1 hL
  refine (class_eq_one_iff _).2 ⟨fun i ↦ Units.map
    (f.appLE (L.U i) (f ⁻¹ᵁ L.U i) le_rfl).hom.toMonoidHom (u i), fun i j ↦ ?_⟩
  change Units.map (f.appLE (L.U i ⊓ L.U j) (f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j)
    f.preimage_inf.ge).hom.toMonoidHom (L.g i j) = _
  rw [hu i j, map_mul, map_inv, map_appLE_resUnits, map_appLE_resUnits]
  beta_reduce
  erw [resUnits_map_appLE, resUnits_map_appLE]
  rfl

/-- Line bundles with the same class have inverse images with the same class. -/
lemma class_pullback_eq_class_pullback {L L' : X.LineBundle} (h : L.class = L'.class) :
    (L.pullback f).class = (L'.pullback f).class := by
  have h1 : (L.tensor L'.dual).class = 1 := by rw [class_tensor, class_dual, h, mul_inv_cancel]
  have := class_pullback_eq_one f h1
  rwa [pullback_tensor, pullback_dual, class_tensor, class_dual, mul_inv_eq_one] at this

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image along the identity. -/
lemma pullback_id : L.pullback (𝟙 X) = L := by
  simp only [pullback]
  congr
  funext i j
  ext
  change (X.presheaf.map (homOfLE _).op) (L.g i j : Γ(X, L.U i ⊓ L.U j)) = _
  rw [show (homOfLE (le_refl (L.U i ⊓ L.U j))).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

end Pullback

end LineBundle

namespace Pic

variable {X Y Z : Scheme.{u}}

/-- The inverse image `f^* : Pic X →* Pic Y` along `f : Y ⟶ X` (EGA 0_I 5.4.8), defined on
representatives by `LineBundle.pullback`. -/
noncomputable def pullback (f : Y ⟶ X) : X.Pic →* Y.Pic where
  toFun c := ((LineBundle.class_surjective X c).choose.pullback f).class
  map_one' := LineBundle.class_pullback_eq_one f (LineBundle.class_surjective X 1).choose_spec
  map_mul' c d := by
    have hc := (LineBundle.class_surjective X c).choose_spec
    have hd := (LineBundle.class_surjective X d).choose_spec
    have hcd := (LineBundle.class_surjective X (c * d)).choose_spec
    rw [← LineBundle.class_tensor, ← LineBundle.pullback_tensor]
    refine LineBundle.class_pullback_eq_class_pullback f ?_
    rw [hcd, LineBundle.class_tensor, hc, hd]

/-- The inverse image of the class of `L` is the class of the inverse image of `L`. -/
lemma pullback_class (f : Y ⟶ X) (L : X.LineBundle) : pullback f L.class = (L.pullback f).class :=
  LineBundle.class_pullback_eq_class_pullback f (LineBundle.class_surjective X _).choose_spec

lemma pullback_comp (f : Z ⟶ Y) (g : Y ⟶ X) :
    pullback (f ≫ g) = (pullback f).comp (pullback g) := by
  ext c
  obtain ⟨L, rfl⟩ := LineBundle.class_surjective X c
  simp only [MonoidHom.coe_comp, Function.comp_apply, pullback_class, LineBundle.pullback_comp]

lemma pullback_comp_apply (f : Z ⟶ Y) (g : Y ⟶ X) (c : X.Pic) :
    pullback (f ≫ g) c = pullback f (pullback g c) := by
  rw [pullback_comp]
  rfl

@[simp]
lemma pullback_id : pullback (𝟙 X) = MonoidHom.id X.Pic := by
  ext c
  obtain ⟨L, rfl⟩ := LineBundle.class_surjective X c
  simp only [pullback_class, LineBundle.pullback_id, MonoidHom.id_apply]

lemma pullback_congr {f g : Y ⟶ X} (h : f = g) : pullback f = pullback g := by
  rw [h]

end Pic

namespace LineBundle

variable {X Y : Scheme.{u}} (L : X.LineBundle)

section Cocycle

lemma resUnits_g_mul_resUnits_g {T : X.Opens} {i j k : L.ι} (hij : T ≤ L.U i ⊓ L.U j)
    (hjk : T ≤ L.U j ⊓ L.U k) (hik : T ≤ L.U i ⊓ L.U k) :
    resUnits hij (L.g i j) * resUnits hjk (L.g j k) = resUnits hik (L.g i k) :=
  L.oneCocycle.ev_trans i j k (homOfLE (hij.trans inf_le_left)) (homOfLE (hij.trans inf_le_right))
    (homOfLE (hjk.trans inf_le_right))

lemma resUnits_g_self {T : X.Opens} {i : L.ι} (h : T ≤ L.U i ⊓ L.U i) :
    resUnits h (L.g i i) = 1 := by
  have := L.resUnits_g_mul_resUnits_g h h h
  rwa [mul_eq_right] at this

lemma resUnits_g_symm {T : X.Opens} {i j : L.ι} (hij : T ≤ L.U i ⊓ L.U j)
    (hji : T ≤ L.U j ⊓ L.U i) : resUnits hji (L.g j i) = (resUnits hij (L.g i j))⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, mul_comm, L.resUnits_g_mul_resUnits_g hij hji
    (le_inf (hij.trans inf_le_left) (hij.trans inf_le_left)), resUnits_g_self]

end Cocycle

section Trivial

omit L in
lemma presheaf_map_homOfLE_self {U : X.Opens} (h : U ≤ U) (x : Γ(X, U)) :
    X.presheaf.map (homOfLE h).op x = x := by
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- A line bundle is trivial iff it has a section vanishing nowhere. -/
theorem class_eq_one_iff_nonempty_trivialization :
    L.class = 1 ↔ Nonempty (L.Trivialization ⊤) := by
  rw [class_eq_one_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨⟨fun i ↦ X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ L.U i ≤ L.U i)).op (u i),
      fun i j ↦ ?_, ?_⟩⟩
    · have h1 := congrArg Units.val (congrArg (resUnits (inf_le_right :
        ⊤ ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j)) (hu i j))
      simp only [map_mul, map_inv, resUnits_resUnits, Units.val_mul, coe_resUnits] at h1
      simp only [trans, zpow_natCast, pow_one, CohomologyAux.presheaf_map_map]
      rw [h1, mul_assoc]
      have e : ∀ (V W : X.Opens) (h : W ≤ V) (a : (Γ(X, V))ˣ),
          ((resUnits h a)⁻¹ : (Γ(X, W))ˣ).val * X.presheaf.map (homOfLE h).op a.val = 1 :=
        fun V W h a ↦ Units.inv_mul (resUnits h a)
      rw [e, mul_one]
    · exact Pi.isUnit_iff.2 fun i ↦ (u i).isUnit.map _
  · rintro ⟨τ⟩
    have hτ (i : L.ι) : IsUnit (X.presheaf.map (homOfLE (le_inf le_top le_rfl :
        L.U i ≤ ⊤ ⊓ L.U i)).op (τ.e i)) := (Pi.isUnit_iff.1 τ.isUnit i).map _
    refine ⟨fun i ↦ (hτ i).unit, fun i j ↦ ?_⟩
    apply Units.ext
    have h := congrArg (X.presheaf.map (homOfLE (le_inf le_top le_rfl :
      L.U i ⊓ L.U j ≤ ⊤ ⊓ (L.U i ⊓ L.U j))).op) (τ.isSection i j)
    simp only [map_mul, CohomologyAux.presheaf_map_map, trans, zpow_natCast, pow_one] at h
    rw [presheaf_map_homOfLE_self] at h
    rw [Units.val_mul, Units.eq_mul_inv_iff_mul_eq, coe_resUnits, IsUnit.unit_spec,
      CohomologyAux.presheaf_map_map, coe_resUnits, IsUnit.unit_spec,
      CohomologyAux.presheaf_map_map]
    exact h.symm

/-- A line bundle trivialized by a chart which is the whole scheme is trivial. -/
lemma class_eq_one_of_top_le {i₀ : L.ι} (h : ⊤ ≤ L.U i₀) : L.class = 1 := by
  refine (class_eq_one_iff L).2 ⟨fun j ↦ resUnits (le_inf le_rfl ((le_top).trans h) :
    L.U j ≤ L.U j ⊓ L.U i₀) (L.g j i₀), fun j k ↦ ?_⟩
  rw [resUnits_resUnits, resUnits_resUnits,
    ← L.resUnits_g_symm (i := k) (j := i₀) (le_inf inf_le_right (le_top.trans h))
      (le_inf (le_top.trans h) inf_le_right),
    L.resUnits_g_mul_resUnits_g _ _ le_rfl, resUnits_self]

/-- The inverse image of `L` along a morphism whose image lies in a chart of `L` is trivial. -/
lemma class_pullback_eq_one_of_range_subset (f : Y ⟶ X) {i₀ : L.ι}
    (h : Set.range f ⊆ L.U i₀) : (L.pullback f).class = 1 :=
  class_eq_one_of_top_le (L.pullback f) (i₀ := i₀) fun y _ ↦ h ⟨y, rfl⟩

section Pow

/-- The power `L^{⊗n}`, `n ∈ ℤ`, with the same charts as `L` and transition functions `gᵢⱼⁿ`. -/
noncomputable def pow (n : ℤ) : X.LineBundle where
  ι := L.ι
  U := L.U
  iSup_eq_top := L.iSup_eq_top
  g i j := L.g i j ^ n
  cocycle i j k := by
    have h := congrArg (fun v ↦ ((v ^ n : (Γ(X, L.U i ⊓ L.U j ⊓ L.U k))ˣ) :
      Γ(X, L.U i ⊓ L.U j ⊓ L.U k))) (L.resUnits_g_mul_resUnits_g (T := L.U i ⊓ L.U j ⊓ L.U k)
        inf_le_left (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
    simpa only [mul_zpow, ← map_zpow, Units.val_mul, coe_resUnits] using h

@[simp] lemma pow_ι (n : ℤ) : (L.pow n).ι = L.ι := rfl
@[simp] lemma pow_U (n : ℤ) : (L.pow n).U = L.U := rfl
lemma pow_g (n : ℤ) (i j : L.ι) : (L.pow n).g i j = L.g i j ^ n := rfl

lemma pow_one : L.pow 1 = L := by
  simp only [pow, zpow_one]

lemma class_pow_add (a b : ℤ) : (L.pow (a + b)).class = (L.pow a).class * (L.pow b).class := by
  rw [← class_tensor, class_eq_class_iff]
  refine ⟨fun p ↦ resUnits (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
      L.U p.1 ⊓ (L.U p.2.1 ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.1) (L.g p.1 p.2.1) ^ a *
    resUnits (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
      L.U p.1 ⊓ (L.U p.2.1 ⊓ L.U p.2.2) ≤ L.U p.1 ⊓ L.U p.2.2) (L.g p.1 p.2.2) ^ b,
    fun p q ↦ ?_⟩
  obtain ⟨p₁, p₂, p₃⟩ := p
  obtain ⟨q₁, q₂, q₃⟩ := q
  set T := L.U p₁ ⊓ (L.U p₂ ⊓ L.U p₃) ⊓ (L.U q₁ ⊓ (L.U q₂ ⊓ L.U q₃)) with hT
  have h₁ : T ≤ L.U p₁ := inf_le_left.trans inf_le_left
  have h₂ : T ≤ L.U p₂ := inf_le_left.trans (inf_le_right.trans inf_le_left)
  have h₃ : T ≤ L.U p₃ := inf_le_left.trans (inf_le_right.trans inf_le_right)
  have h₄ : T ≤ L.U q₁ := inf_le_right.trans inf_le_left
  have h₅ : T ≤ L.U q₂ := inf_le_right.trans (inf_le_right.trans inf_le_left)
  have h₆ : T ≤ L.U q₃ := inf_le_right.trans (inf_le_right.trans inf_le_right)
  have e₁ := L.resUnits_g_mul_resUnits_g (le_inf h₁ h₄) (le_inf h₄ h₅) (le_inf h₁ h₅)
  have e₂ := L.resUnits_g_mul_resUnits_g (le_inf h₁ h₂) (le_inf h₂ h₅) (le_inf h₁ h₅)
  have e₃ := L.resUnits_g_mul_resUnits_g (le_inf h₁ h₄) (le_inf h₄ h₆) (le_inf h₁ h₆)
  have e₄ := L.resUnits_g_mul_resUnits_g (le_inf h₁ h₃) (le_inf h₃ h₆) (le_inf h₁ h₆)
  change resUnits (le_inf h₁ h₄ : T ≤ L.U p₁ ⊓ L.U q₁) (L.g p₁ q₁ ^ (a + b)) *
      resUnits (le_inf (le_inf h₂ h₃) (le_inf h₅ h₆) :
        T ≤ L.U p₂ ⊓ L.U p₃ ⊓ (L.U q₂ ⊓ L.U q₃))
      ((resUnits (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          L.U p₂ ⊓ L.U p₃ ⊓ (L.U q₂ ⊓ L.U q₃) ≤ L.U p₂ ⊓ L.U q₂) (L.g p₂ q₂ ^ a) *
        resUnits (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          L.U p₂ ⊓ L.U p₃ ⊓ (L.U q₂ ⊓ L.U q₃) ≤ L.U p₃ ⊓ L.U q₃) (L.g p₃ q₃ ^ b))⁻¹) =
    resUnits (inf_le_left : T ≤ L.U p₁ ⊓ (L.U p₂ ⊓ L.U p₃))
      (resUnits (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          L.U p₁ ⊓ (L.U p₂ ⊓ L.U p₃) ≤ L.U p₁ ⊓ L.U p₂) (L.g p₁ p₂) ^ a *
        resUnits (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          L.U p₁ ⊓ (L.U p₂ ⊓ L.U p₃) ≤ L.U p₁ ⊓ L.U p₃) (L.g p₁ p₃) ^ b) *
    (resUnits (inf_le_right : T ≤ L.U q₁ ⊓ (L.U q₂ ⊓ L.U q₃))
      (resUnits (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          L.U q₁ ⊓ (L.U q₂ ⊓ L.U q₃) ≤ L.U q₁ ⊓ L.U q₂) (L.g q₁ q₂) ^ a *
        resUnits (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          L.U q₁ ⊓ (L.U q₂ ⊓ L.U q₃) ≤ L.U q₁ ⊓ L.U q₃) (L.g q₁ q₃) ^ b))⁻¹
  simp only [map_mul, map_inv, map_zpow, resUnits_resUnits]
  set x := resUnits (le_inf h₁ h₄) (L.g p₁ q₁)
  set y₁ := resUnits (le_inf h₄ h₅) (L.g q₁ q₂)
  set y₂ := resUnits (le_inf h₄ h₆) (L.g q₁ q₃)
  set z₁ := resUnits (le_inf h₁ h₂) (L.g p₁ p₂)
  set z₂ := resUnits (le_inf h₁ h₃) (L.g p₁ p₃)
  set w₁ := resUnits (le_inf h₂ h₅) (L.g p₂ q₂)
  set w₂ := resUnits (le_inf h₃ h₆) (L.g p₃ q₃)
  have hx₁ : x = z₁ * w₁ * y₁⁻¹ := by rw [e₂, ← e₁, mul_inv_cancel_right]
  have hx₂ : x = z₂ * w₂ * y₂⁻¹ := by rw [e₄, ← e₃, mul_inv_cancel_right]
  rw [zpow_add]
  nth_rewrite 1 [hx₁]
  rw [hx₂]
  simp only [mul_zpow, inv_zpow', mul_inv_rev]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
  module

lemma class_pow_zero : (L.pow 0).class = 1 :=
  (class_eq_one_iff _).2 ⟨fun _ ↦ 1, fun i j ↦ by
    change L.g i j ^ (0 : ℤ) = _
    simp only [zpow_zero, map_one, inv_one, mul_one]
    rfl⟩

lemma class_pow_natCast (n : ℕ) : (L.pow n).class = L.class ^ n := by
  induction n with
  | zero => simpa using L.class_pow_zero
  | succ n ih =>
    rw [Nat.cast_succ, class_pow_add, ih, pow_one, _root_.pow_succ]

/-- The class of `L^{⊗n}` is the `n`-th power of the class of `L`. -/
theorem class_pow (n : ℤ) : (L.pow n).class = L.class ^ n := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using L.class_pow_natCast n
  · rw [zpow_neg, zpow_natCast, ← class_pow_natCast, eq_inv_iff_mul_eq_one, ← class_pow_add,
      neg_add_cancel, class_pow_zero]

/-- If `L^{⊗n}` is trivial, then `L` has an invertible section of `L^{⊗n}`. -/
theorem exists_isSection_isUnit_of_class_zpow_eq_one {n : ℤ} (h : L.class ^ n = 1) :
    ∃ u : L.Fam ⊤, L.IsSection n ⊤ u ∧ IsUnit u := by
  rw [← class_pow, class_eq_one_iff_nonempty_trivialization] at h
  obtain ⟨τ⟩ := h
  refine ⟨τ.e, fun i j ↦ ?_, τ.isUnit⟩
  have := τ.isSection i j
  have e : ((L.pow n).g i j ^ ((1 : ℕ) : ℤ)) = L.g i j ^ n := by
    rw [Nat.cast_one, zpow_one]
    rfl
  unfold trans at this ⊢
  rw [e] at this
  exact this

end Pow

section ProperIntegral

variable {K : Type u} [Field K]

omit L in
/-- On an integral scheme universally closed over a field (e.g. proper), a global function is
zero or vanishes nowhere: `Γ(X, 𝒪_X)` is a field. -/
lemma basicOpen_eq_top_or_eq_zero (f : X ⟶ Spec (.of K)) [IsIntegral X] [UniversallyClosed f]
    (c : Γ(X, ⊤)) : X.basicOpen c = ⊤ ∨ c = 0 := by
  by_cases hc : c = 0
  · exact Or.inr hc
  · obtain ⟨d, hd⟩ := (isField_of_universallyClosed K f).mul_inv_cancel hc
    exact Or.inl (X.basicOpen_of_isUnit (IsUnit.of_mul_eq_one d hd))

/-- Let `X` be integral and universally closed over a field (e.g. proper), and `L` a line bundle
on `X` some power `L^{⊗n}`, `n > 0`, of which is trivial. A global section of `L` which does not
vanish at some point vanishes nowhere. -/
theorem famLocus_eq_top_of_class_pow_eq_one (f : X ⟶ Spec (.of K)) [IsIntegral X]
    [UniversallyClosed f] {n : ℕ} (hn : 0 < n) (h : L.class ^ n = 1) {t : L.Fam ⊤}
    (ht : L.IsSection 1 ⊤ t) {x : X} (hx : x ∈ L.famLocus ⊤ t) : L.famLocus ⊤ t = ⊤ := by
  obtain ⟨u, hu, hu'⟩ := L.exists_isSection_isUnit_of_class_zpow_eq_one (n := n)
    (by rwa [zpow_natCast])
  have htn : L.IsSection n ⊤ (t ^ n) := (ht.pow n).of_eq (by simp)
  have hy : L.IsSection 0 ⊤ (↑hu'.unit⁻¹ * t ^ n) := hu.of_isUnit_mul hu' (by
    rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]
    exact htn)
  obtain ⟨c, hc⟩ := exists_famConst_eq hy
  have hloc : L.famLocus ⊤ (↑hu'.unit⁻¹ * t ^ n) = L.famLocus ⊤ t := by
    rw [famLocus_mul _ htn, famLocus_of_isUnit (Units.isUnit _), famLocus_pow _ hn, top_inf_eq]
  rw [← hloc, ← hc, famLocus_famConst] at hx ⊢
  rcases basicOpen_eq_top_or_eq_zero f c with h | h
  · exact h
  · rw [h, Scheme.basicOpen_zero] at hx
    exact absurd hx (by simp)

end ProperIntegral

end Trivial

end LineBundle

namespace Pic

variable {X : Scheme.{u}}

/-- If every open subset containing a given point is the whole scheme (e.g. for the spectrum of
a local ring), the Picard group is trivial. -/
lemma subsingleton_of_forall_eq_top (x : X) (hx : ∀ U : X.Opens, x ∈ U → U = ⊤) :
    Subsingleton X.Pic := by
  suffices ∀ c : X.Pic, c = 1 from ⟨fun a b ↦ (this a).trans (this b).symm⟩
  intro c
  obtain ⟨L, rfl⟩ := LineBundle.class_surjective X c
  have : x ∈ ⨆ i, L.U i := by rw [L.iSup_eq_top]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact L.class_eq_one_of_top_le (hx _ hi).ge

/-- The Picard group of the spectrum of a local ring is trivial. -/
instance subsingleton_spec_of_isLocalRing (R : CommRingCat.{u}) [IsLocalRing R] :
    Subsingleton (Spec R).Pic :=
  subsingleton_of_forall_eq_top (IsLocalRing.closedPoint R) fun U hU ↦
    eq_top_iff.2 fun y _ ↦ (IsLocalRing.specializes_closedPoint y).mem_open U.2 hU

end Pic

end AlgebraicGeometry.Scheme
