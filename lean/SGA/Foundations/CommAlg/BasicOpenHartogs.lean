/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Hartogs extension across the complement of two basic opens

Let `X` be a scheme and `a, b` global sections of `X`.

* `Scheme.isWeaklyRegular_of_basicOpen_sup_eq_top`: if `X = D(a) ∪ D(b)` and `a` is a
  nonzerodivisor on `Γ(D(b))`, then `a, b` is a regular sequence on `Γ(X)`.
* `Scheme.bijective_restrict_basicOpen_sup`: conversely, if `X` is quasi-compact and
  quasi-separated and `a, b` is a regular sequence on `Γ(X)`, then every section over
  `D(a) ∪ D(b)` extends uniquely to `X`.

Both hold more generally for sections over an open `V` of `X`
(`Scheme.isWeaklyRegular_of_basicOpen_sup_eq`,
`Scheme.bijective_restrict_basicOpen_sup_of_isCompact`).

These are the two directions of the elementary case "depth `≥ 2` along `V(a, b)`" of the
Hartogs property (EGA IV 5.10.5, SGA 2 III.3.3; Stacks 0AVZ); they are used for the purity of
branch locus in dimension two. The divisibility lemma
`IsWeaklyRegular.pow_dvd_of_pow_dvd_pow_mul` (powers of a regular sequence) is also proved.

* `Module.finite_of_isLocalization_pair`: finiteness of sections over `D(x) ∪ D(y)`. If `x, y` is a
  regular sequence in a noetherian ring `A` and `C` is an `A`-algebra on which `x` is regular, with
  `C_x` finite projective over `A_x` and `C_y` finite over `A_y`, then `C` is a finite `A`-module:
  it embeds into `A^n` (the lattice argument behind the coherence of `j_* F` for a locally free
  `F` on the punctured spectrum of a two-dimensional regular local ring, SGA 2 VIII).
-/

universe u

open CategoryTheory Opposite TopologicalSpace RingTheory.Sequence Filter

namespace RingTheory.Sequence.IsWeaklyRegular

variable {B : Type*} [CommRing B] {a b : B}

/-- If `a, b` is a regular sequence, then `a ∣ b z` implies `a ∣ z`. -/
theorem dvd_of_dvd_mul_of_pair (h : IsWeaklyRegular B [a, b]) {z : B} (hz : a ∣ b * z) :
    a ∣ z := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff] at h
  obtain ⟨w, hw⟩ := hz
  have : b • (Submodule.Quotient.mk z : QuotSMulTop a B) = b • 0 := by
    rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨w, Submodule.mem_top, by rw [smul_eq_mul, smul_eq_mul, hw]⟩
  have := h.2 this
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at this
  obtain ⟨e, -, he⟩ := this
  exact ⟨e, he.symm⟩

/-- If `a, b` is a regular sequence, then `aⁿ ∣ bᵐ z` implies `aⁿ ∣ z`. -/
theorem pow_dvd_of_pow_dvd_pow_mul (h : IsWeaklyRegular B [a, b]) (n m : ℕ) {z : B}
    (hz : a ^ n ∣ b ^ m * z) : a ^ n ∣ z := by
  have ha : IsSMulRegular B a := ((isWeaklyRegular_cons_iff B a [b]).mp h).1
  -- first `m = 1`
  have key : ∀ n : ℕ, ∀ z : B, a ^ n ∣ b * z → a ^ n ∣ z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro z hz
      obtain ⟨z₁, rfl⟩ := ih z (dvd_trans (pow_dvd_pow a n.le_succ) hz)
      obtain ⟨w, hw⟩ := hz
      have hpow : IsSMulRegular B (a ^ n) := ha.pow n
      have : b * z₁ = a * w := by
        apply hpow
        simp only [smul_eq_mul]
        linear_combination hw
      obtain ⟨v, rfl⟩ := dvd_of_dvd_mul_of_pair h ⟨w, this⟩
      exact ⟨v, by ring⟩
  induction m generalizing z with
  | zero => simpa using hz
  | succ m ih =>
    apply key n z
    apply ih
    rw [← mul_assoc, ← pow_succ]
    exact hz

end RingTheory.Sequence.IsWeaklyRegular

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- If an open `V` is `D(a) ∪ D(b)` for sections `a, b` over `V` and `a` is a nonzerodivisor on
`Γ(D(b))`, then `a, b` is a regular sequence on `Γ(V)`: sections `c/a` on `D(a)` and `c'/b` on
`D(b)` with `bc = ac'` glue. -/
theorem isWeaklyRegular_of_basicOpen_sup_eq {V : X.Opens} {a b : Γ(X, V)}
    (hab : X.basicOpen a ⊔ X.basicOpen b = V)
    (ha : ∀ s : Γ(X, X.basicOpen b),
      X.presheaf.map (homOfLE (X.basicOpen_le b)).op a * s = 0 → s = 0) :
    IsWeaklyRegular Γ(X, V) [a, b] := by
  set Ua := X.basicOpen a
  set Ub := X.basicOpen b
  set ra := (X.presheaf.map (homOfLE (X.basicOpen_le a) : Ua ⟶ V).op).hom
  set rb := (X.presheaf.map (homOfLE (X.basicOpen_le b) : Ub ⟶ V).op).hom
  have hcov : V ≤ Ua ⊔ Ub := hab.ge
  have hua : IsUnit (ra a) := X.toRingedSpace.isUnit_res_basicOpen a
  have hub : IsUnit (rb b) := X.toRingedSpace.isUnit_res_basicOpen b
  -- a section vanishing on `D(a)` and `D(b)` vanishes
  have hext : ∀ s : Γ(X, V), ra s = 0 → rb s = 0 → s = 0 := by
    intro s h1 h2
    refine X.sheaf.eq_of_locally_eq₂ (homOfLE (X.basicOpen_le a)) (homOfLE (X.basicOpen_le b))
      hcov s 0 ?_ ?_
    · rw [map_zero]; exact h1
    · rw [map_zero]; exact h2
  -- `a` is regular
  have hareg : ∀ c : Γ(X, V), a * c = 0 → c = 0 := by
    intro c hc
    refine hext c ?_ (ha _ ?_)
    · have := congrArg ra hc
      rw [map_mul, map_zero] at this
      exact (hua.mul_right_eq_zero).mp this
    · have := congrArg rb hc
      rwa [map_mul, map_zero] at this
  -- `b` is regular modulo `a`: if `b c = a c'` then `c ∈ a Γ`, by gluing `c/a` and `c'/b`
  have hdiv : ∀ c c' : Γ(X, V), b * c = a * c' → ∃ e, a * e = c := by
    intro c c' hcc'
    let sa : Γ(X, Ua) := ra c * ↑hua.unit⁻¹
    let sb : Γ(X, Ub) := rb c' * ↑hub.unit⁻¹
    have hsa : ra a * sa = ra c := by
      simp only [sa, mul_comm (ra c), ← mul_assoc, IsUnit.mul_val_inv, one_mul]
    have hsb : rb b * sb = rb c' := by
      simp only [sb, mul_comm (rb c'), ← mul_assoc, IsUnit.mul_val_inv, one_mul]
    -- restrictions to `D(a) ⊓ D(b)`
    set W := Ua ⊓ Ub
    set rW := (X.presheaf.map (homOfLE (inf_le_left.trans (X.basicOpen_le a)) : W ⟶ V).op).hom
    set rWa := (X.presheaf.map (homOfLE inf_le_left : W ⟶ Ua).op).hom
    set rWb := (X.presheaf.map (homOfLE inf_le_right : W ⟶ Ub).op).hom
    have hWa : ∀ z, rWa (ra z) = rW z := fun z ↦ by
      simp only [rWa, ra, rW, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
        homOfLE_comp]
    have hWb : ∀ z, rWb (rb z) = rW z := fun z ↦ by
      simp only [rWb, rb, rW, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
        homOfLE_comp]
    have hWua : IsUnit (rW a) := hWa a ▸ hua.map rWa
    have hWub : IsUnit (rW b) := hWb b ▸ hub.map rWb
    have hagree : rWa sa = rWb sb := by
      have e1 : rW a * rWa sa = rW c := by rw [← hWa, ← map_mul, hsa, hWa]
      have e2 : rW b * rWb sb = rW c' := by rw [← hWb, ← map_mul, hsb, hWb]
      apply (hWua.mul_right_inj).mp
      apply (hWub.mul_right_inj).mp
      rw [e1, mul_left_comm, e2, ← map_mul, ← map_mul, hcc', mul_comm]
    let t : Γ(X, Ua ⊔ Ub) := (X.sheaf.objSupIsoProdEqLocus Ua Ub).inv ⟨(sa, sb), hagree⟩
    let e : Γ(X, V) := X.presheaf.map (eqToHom hab.symm).op t
    have key : ∀ (V' : X.Opens) (i : V' ⟶ Ua ⊔ Ub) (j : V' ⟶ V),
        (X.presheaf.map j.op).hom e = (X.presheaf.map i.op).hom t := by
      intro V' i j
      change (X.presheaf.map j.op).hom ((X.presheaf.map (eqToHom hab.symm).op).hom t) = _
      simp only [← CommRingCat.comp_apply, ← Functor.map_comp]
      exact congrArg (fun φ ↦ (X.presheaf.map φ).hom t) (Subsingleton.elim _ _)
    have hea : ra e = sa := (key Ua _ _).trans
      (TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf Ua Ub ⟨(sa, sb), hagree⟩)
    have heb : rb e = sb := (key Ub _ _).trans
      (TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf Ua Ub ⟨(sa, sb), hagree⟩)
    refine ⟨e, sub_eq_zero.mp (hext _ ?_ ?_)⟩
    · rw [map_sub, map_mul, hea, hsa, sub_self]
    · rw [map_sub, map_mul, heb, sub_eq_zero]
      apply (hub.mul_right_inj).mp
      rw [← mul_assoc, mul_comm (rb b), mul_assoc, hsb, ← map_mul, ← map_mul, hcc']
  refine IsWeaklyRegular.cons (fun c₁ c₂ h ↦ sub_eq_zero.mp (hareg _ ?_)) ?_
  · rw [mul_sub, sub_eq_zero]; exact h
  refine (isWeaklyRegular_singleton_iff _ b).mpr fun u v huv ↦ ?_
  rw [← sub_eq_zero, ← smul_sub] at huv
  rw [← sub_eq_zero]
  generalize u - v = w at huv ⊢
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_smul_pointwise_iff_exists] at huv
  obtain ⟨c', -, hc'⟩ := huv
  obtain ⟨e, rfl⟩ := hdiv c c' (by rw [← smul_eq_mul, ← hc', smul_eq_mul])
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨e, Submodule.mem_top, rfl⟩

/-- If `X = D(a) ∪ D(b)` and `a` is a nonzerodivisor on `Γ(D(b))`, then `a, b` is a regular
sequence on `Γ(X)`. -/
theorem isWeaklyRegular_of_basicOpen_sup_eq_top {a b : Γ(X, ⊤)}
    (hab : X.basicOpen a ⊔ X.basicOpen b = ⊤)
    (ha : ∀ s : Γ(X, X.basicOpen b),
      X.presheaf.map (homOfLE le_top : X.basicOpen b ⟶ ⊤).op a * s = 0 → s = 0) :
    IsWeaklyRegular Γ(X, ⊤) [a, b] :=
  isWeaklyRegular_of_basicOpen_sup_eq X hab ha

/-- Hartogs for two basic opens: if `a, b` is a regular sequence of sections of `𝒪_X` over a
quasi-compact and quasi-separated open `V`, then restriction `Γ(V) → Γ(D(a) ∪ D(b))` is
bijective. -/
theorem bijective_restrict_basicOpen_sup_of_isCompact {V : X.Opens} (hV : IsCompact (V : Set X))
    (hV' : IsQuasiSeparated (V : Set X)) {a b : Γ(X, V)} (hab : IsWeaklyRegular Γ(X, V) [a, b]) :
    Function.Bijective (X.presheaf.map
      (homOfLE (sup_le (X.basicOpen_le a) (X.basicOpen_le b)) :
        X.basicOpen a ⊔ X.basicOpen b ⟶ V).op) := by
  set Ua := X.basicOpen a
  set Ub := X.basicOpen b
  set V₀ := Ua ⊔ Ub
  set ra := (X.presheaf.map (homOfLE (X.basicOpen_le a) : Ua ⟶ V).op).hom
  set rb := (X.presheaf.map (homOfLE (X.basicOpen_le b) : Ub ⟶ V).op).hom
  set rV := (X.presheaf.map
    (homOfLE (sup_le (X.basicOpen_le a) (X.basicOpen_le b)) : V₀ ⟶ V).op).hom
  set rVa := (X.presheaf.map (homOfLE le_sup_left : Ua ⟶ V₀).op).hom
  set rVb := (X.presheaf.map (homOfLE le_sup_right : Ub ⟶ V₀).op).hom
  have hVa : ∀ z, rVa (rV z) = ra z := fun z ↦ by
    simp only [rVa, rV, ra, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  have hVb : ∀ z, rVb (rV z) = rb z := fun z ↦ by
    simp only [rVb, rV, rb, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  have hLa := isLocalization_basicOpen_of_qcqs (X := X) (U := V) hV hV' a
  have hLb := isLocalization_basicOpen_of_qcqs (X := X) (U := V) hV hV' b
  have hLab := isLocalization_basicOpen_of_qcqs (X := X) (U := V) hV hV' (a * b)
  have ha : IsSMulRegular Γ(X, V) a := ((isWeaklyRegular_cons_iff _ a [b]).mp hab).1
  have hua : IsUnit (ra a) := X.toRingedSpace.isUnit_res_basicOpen a
  have hub : IsUnit (rb b) := X.toRingedSpace.isUnit_res_basicOpen b
  have hext : ∀ s t : Γ(X, V₀), rVa s = rVa t → rVb s = rVb t → s = t := fun s t h₁ h₂ ↦
    X.sheaf.eq_of_locally_eq₂ (homOfLE le_sup_left) (homOfLE le_sup_right) le_rfl s t h₁ h₂
  constructor
  · -- injectivity: a section vanishing on `D(a)` is killed by a power of `a`
    intro s t hst
    rw [← sub_eq_zero]
    have h0 : ra (s - t) = 0 := by
      rw [← hVa, map_sub, map_sub, sub_eq_zero]
      exact congrArg rVa hst
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a) _ _).mp h0
    exact (ha.pow n) (by simpa using hn)
  · -- surjectivity: glue `c / aⁿ` and `d / bᵐ`
    intro t
    obtain ⟨⟨c, _, n, rfl⟩, hc⟩ := IsLocalization.surj (Submonoid.powers a) (rVa t)
    obtain ⟨⟨d, _, m, rfl⟩, hd⟩ := IsLocalization.surj (Submonoid.powers b) (rVb t)
    change rVa t * ra (a ^ n) = ra c at hc
    change rVb t * rb (b ^ m) = rb d at hd
    -- compare on `D(ab)`
    set rab := (X.presheaf.map (homOfLE (X.basicOpen_le (a * b)) : X.basicOpen (a * b) ⟶ V).op).hom
    have hle : X.basicOpen (a * b) ≤ V₀ :=
      (X.basicOpen_mul a b).trans_le (inf_le_left.trans le_sup_left)
    set rVab := (X.presheaf.map (homOfLE hle).op).hom
    set raab := (X.presheaf.map (homOfLE ((X.basicOpen_mul a b).trans_le inf_le_left)).op).hom
    set rbab := (X.presheaf.map (homOfLE ((X.basicOpen_mul a b).trans_le inf_le_right)).op).hom
    have h1 : ∀ z, raab (rVa z) = rVab z := fun z ↦ by
      simp only [raab, rVa, rVab, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
        homOfLE_comp]
    have h2 : ∀ z, rbab (rVb z) = rVab z := fun z ↦ by
      simp only [rbab, rVb, rVab, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
        homOfLE_comp]
    have h3 : ∀ z, raab (ra z) = rab z := fun z ↦ by
      simp only [raab, ra, rab, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
        homOfLE_comp]
    have h4 : ∀ z, rbab (rb z) = rab z := fun z ↦ by
      simp only [rbab, rb, rab, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
        homOfLE_comp]
    have heq : rab (c * b ^ m) = rab (d * a ^ n) := by
      have e1 := congrArg raab hc
      have e2 := congrArg rbab hd
      simp only [map_mul, h1, h3] at e1
      simp only [map_mul, h2, h4] at e2
      rw [map_mul, map_mul, ← e1, ← e2]
      ring
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (a * b)) heq
    simp only at hk
    have hk' : b ^ (k + m) * c = a ^ n * (b ^ k * d) := by
      apply ha.pow k
      simp only [smul_eq_mul]
      linear_combination hk
    obtain ⟨e, rfl⟩ := hab.pow_dvd_of_pow_dvd_pow_mul n (k + m) ⟨_, hk'⟩
    have he : b ^ (k + m) * e = b ^ k * d := by
      apply ha.pow n
      simp only [smul_eq_mul]
      linear_combination hk'
    refine ⟨e, hext _ _ ?_ ?_⟩
    · rw [hVa]
      apply (hua.pow n).mul_left_inj.mp
      rw [← map_pow, hc, ← map_mul, mul_comm]
    · rw [hVb]
      have hubk : IsUnit (rb (b ^ k)) := by rw [map_pow]; exact hub.pow k
      apply (hub.pow m).mul_left_inj.mp
      apply hubk.mul_right_inj.mp
      rw [← map_pow, hd, ← map_mul, ← map_mul, ← map_mul, ← he]
      ring_nf

/-- Hartogs for two basic opens: if `a, b` is a regular sequence of global sections of a qcqs
scheme `X`, then restriction `Γ(X) → Γ(D(a) ∪ D(b))` is bijective. -/
theorem bijective_restrict_basicOpen_sup [CompactSpace X] [QuasiSeparatedSpace X]
    {a b : Γ(X, ⊤)} (hab : IsWeaklyRegular Γ(X, ⊤) [a, b]) :
    Function.Bijective
      (X.presheaf.map (homOfLE le_top : X.basicOpen a ⊔ X.basicOpen b ⟶ ⊤).op) :=
  bijective_restrict_basicOpen_sup_of_isCompact X isCompact_univ isQuasiSeparated_univ hab

end AlgebraicGeometry.Scheme

/-- Finiteness from finiteness over `D(x)` and `D(y)`. Let `x, y` be a regular sequence in a
noetherian ring `A` and `C` an `A`-algebra on which `x` is regular. If `C_x` is a finite projective
`A_x`-module and `C_y` a finite `A_y`-module, then `C` is a finite `A`-module. -/
theorem Module.finite_of_isLocalization_pair {A C : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing C] [Algebra A C] {x y : A} (hxy : IsWeaklyRegular A [x, y])
    (hxC : IsSMulRegular C x)
    (Ax : Type*) [CommRing Ax] [Algebra A Ax] [IsLocalization.Away x Ax]
    (Cx : Type*) [CommRing Cx] [Algebra C Cx] [Algebra A Cx] [IsScalarTower A C Cx]
    [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers x)) Cx]
    [Algebra Ax Cx] [IsScalarTower A Ax Cx] [Module.Finite Ax Cx] [Module.Projective Ax Cx]
    (Ay : Type*) [CommRing Ay] [Algebra A Ay] [IsLocalization.Away y Ay]
    (Cy : Type*) [CommRing Cy] [Algebra C Cy] [Algebra A Cy] [IsScalarTower A C Cy]
    [IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers y)) Cy]
    [Algebra Ay Cy] [IsScalarTower A Ay Cy] [Module.Finite Ay Cy] :
    Module.Finite A C := by
  classical
  let f : C →ₗ[A] Cx := (IsScalarTower.toAlgHom A C Cx).toLinearMap
  let g : C →ₗ[A] Cy := (IsScalarTower.toAlgHom A C Cy).toLinearMap
  have hx : IsSMulRegular A x := ((isWeaklyRegular_cons_iff A x [y]).mp hxy).1
  -- `f` is injective since `x` is `C`-regular
  have hfinj : Function.Injective f := by
    intro c₁ c₂ h
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers x) h
    exact (hxC.pow n) hn
  -- a finitely generated submodule `N ⊆ C` generating `Cx` and `Cy`
  obtain ⟨Sx, hSx⟩ := Module.Finite.fg_top (R := Ax) (M := Cx)
  obtain ⟨Sy, hSy⟩ := Module.Finite.fg_top (R := Ay) (M := Cy)
  choose px hpx using fun s : Sx ↦ IsLocalizedModule.mk'_surjective (Submonoid.powers x) f (s : Cx)
  choose py hpy using fun s : Sy ↦ IsLocalizedModule.mk'_surjective (Submonoid.powers y) g (s : Cy)
  let G : Set C := Set.range (fun s ↦ (px s).1) ∪ Set.range (fun s ↦ (py s).1)
  have hG : G.Finite := (Set.finite_range _).union (Set.finite_range _)
  let N := Submodule.span A G
  have hNx : Submodule.localized' Ax (Submonoid.powers x) f N = ⊤ := by
    rw [eq_top_iff, ← hSx, Submodule.span_le]
    intro s hs
    exact ⟨_, Submodule.subset_span (Or.inl ⟨⟨s, hs⟩, rfl⟩), _, hpx ⟨s, hs⟩⟩
  have hNy : Submodule.localized' Ay (Submonoid.powers y) g N = ⊤ := by
    rw [eq_top_iff, ← hSy, Submodule.span_le]
    intro s hs
    exact ⟨_, Submodule.subset_span (Or.inr ⟨⟨s, hs⟩, rfl⟩), _, hpy ⟨s, hs⟩⟩
  have hxN : ∀ c : C, ∃ a : ℕ, x ^ a • c ∈ N := by
    intro c
    obtain ⟨n, hn, ⟨_, a, rfl⟩, h⟩ := (Submodule.mem_localized' _ _ _ _ (f c)).mp
      (hNx ▸ Submodule.mem_top)
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at h
    exact ⟨a, hfinj h ▸ hn⟩
  have hyN : ∀ c : C, ∃ b : ℕ, y ^ b • c ∈ N := by
    intro c
    obtain ⟨n, hn, ⟨_, a, rfl⟩, h⟩ := (Submodule.mem_localized' _ _ _ _ (g c)).mp
      (hNy ▸ Submodule.mem_top)
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at h
    obtain ⟨⟨_, b, rfl⟩, hb⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers y) h
    rw [Submonoid.smul_def, Submonoid.smul_def] at hb
    refine ⟨b + a, ?_⟩
    rw [pow_add, mul_smul, ← hb]
    exact N.smul_mem _ hn
  -- an embedding `Cx → Ax^n`
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Ax Cx
  obtain ⟨j, hj⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hjinj : Function.Injective j := fun a b h ↦ by
    have := congrArg π h
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hj, LinearMap.id_apply,
      LinearMap.id_apply] at this
  -- `A → Ax` is injective and `x` acts invertibly on `Ax`
  have hAx : Function.Injective (algebraMap A Ax) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers x) Ax a).mp ha
    exact (hx.pow k) (by simpa using hk)
  have hunit : ∀ k : ℕ, IsUnit (algebraMap A Ax (x ^ k)) := fun k ↦
    IsLocalization.map_units Ax (⟨x ^ k, k, rfl⟩ : Submonoid.powers x)
  -- the lattice `A^n ⊆ Ax^n`
  let ι : (Fin n → A) →ₗ[A] (Fin n → Ax) :=
    LinearMap.pi fun i ↦ Algebra.linearMap A Ax ∘ₗ LinearMap.proj i
  have hι : Function.Injective ι := fun v w h ↦ funext fun i ↦ hAx (congrFun h i)
  let P := LinearMap.range ι
  have hP : ∀ v, (∀ i, ∃ a, algebraMap A Ax a = v i) → v ∈ P := fun v hv ↦ by
    choose a ha using hv
    exact ⟨a, funext ha⟩
  have hP' : ∀ v ∈ P, ∀ i, ∃ a, algebraMap A Ax a = v i := by
    rintro _ ⟨a, rfl⟩ i
    exact ⟨a i, rfl⟩
  -- a uniform denominator for the generators
  have hev : ∀ z : Ax, ∀ᶠ K in atTop, ∃ a, algebraMap A Ax a = x ^ K • z := by
    intro z
    obtain ⟨⟨a, _, k, rfl⟩, hk⟩ := IsLocalization.surj (Submonoid.powers x) z
    refine eventually_atTop.mpr ⟨k, fun K hK ↦ ⟨x ^ (K - k) * a, ?_⟩⟩
    rw [map_mul, ← hk, Algebra.smul_def, ← mul_assoc, mul_comm _ z, mul_assoc, ← map_mul,
      ← pow_add, Nat.sub_add_cancel hK, mul_comm]
  have := hG.to_subtype
  obtain ⟨K, hK⟩ := (eventually_all.mpr fun p : G × Fin n ↦ hev (j (f p.1) p.2)).exists
  let Ψ : C →ₗ[A] (Fin n → Ax) := x ^ K • ((j.restrictScalars A) ∘ₗ f)
  have hΨN : ∀ γ ∈ N, Ψ γ ∈ P := by
    intro γ hγ
    refine (Submodule.span_le (p := P.comap Ψ)).mpr (fun γ hγ ↦ hP _ fun i ↦ ?_) hγ
    obtain ⟨a, ha⟩ := hK (⟨γ, hγ⟩, i)
    exact ⟨a, by simp [Ψ, ha]⟩
  have hΨP : ∀ c, Ψ c ∈ P := by
    intro c
    obtain ⟨a, ha⟩ := hxN c
    obtain ⟨b, hb⟩ := hyN c
    have h1 := hP' _ (hΨN _ ha)
    have h2 := hP' _ (hΨN _ hb)
    refine hP _ fun i ↦ ?_
    obtain ⟨w₁, hw₁⟩ := h1 i
    obtain ⟨w₂, hw₂⟩ := h2 i
    rw [map_smul, Pi.smul_apply] at hw₁ hw₂
    have hw : y ^ b * w₁ = x ^ a * w₂ := by
      apply hAx
      rw [map_mul, map_mul, hw₁, hw₂, ← Algebra.smul_def, ← Algebra.smul_def, smul_comm]
    obtain ⟨u, rfl⟩ := hxy.pow_dvd_of_pow_dvd_pow_mul a b ⟨w₂, hw⟩
    refine ⟨u, (hunit a).mul_right_injective ?_⟩
    change algebraMap A Ax (x ^ a) * algebraMap A Ax u = algebraMap A Ax (x ^ a) * Ψ c i
    rw [← map_mul, hw₁, Algebra.smul_def]
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    apply hfinj
    rw [map_zero]
    apply hjinj
    rw [map_zero]
    have : x ^ K • j (f c) = 0 := hc
    rw [← algebraMap_smul Ax] at this
    exact (hunit K).smul_eq_zero.mp this
  let e : P ≃ₗ[A] (Fin n → A) := (LinearEquiv.ofInjective ι hι).symm
  have : IsNoetherian A P := isNoetherian_of_linearEquiv e.symm
  exact Module.Finite.of_injective (Ψ.codRestrict P hΨP)
    (fun c₁ c₂ h ↦ hΨinj (congrArg Subtype.val h))
