/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import SGA.Foundations.CommAlg.BasicOpenHartogs
import SGA.Foundations.CommAlg.Purity
import SGA.Foundations.CommAlg.PurityInduction

/-!
# Purity for the punctured spectrum of a regular local ring

Let `A` be a regular local ring of dimension `≥ 2`, `X = Spec A` and `U = X \ {𝔪}` its punctured
spectrum. Base change along `U ⟶ X` is an equivalence between the finite étale schemes over `X`
and those over `U` (Zariski–Nagata purity; Stacks 0BMB, SGA 2 X.3.4, SGA 1 X.3.3 for `X = Spec A`).

* Full faithfulness is Hartogs: a finite étale `Y = Spec B` over `X` is flat, so a regular
  sequence `x, y ∈ 𝔪` of `A` stays regular on `B`, and `B = Γ(Y ×_X U)`
  (`bijective_restrict_preimage_puncturedSpectrum`: sections over `Y ×_X U` are determined on
  `D(x)`, and `Γ(Y) → Γ(D(x) ∪ D(y))` is bijective).
* Essential surjectivity: for `W` finite étale over `U`, `W ≅ Spec Γ(W) ×_X U` because `U` is
  quasi-affine; `C = Γ(W)` has depth `≥ 2` (regularity of `x, y` is local on `W`,
  `Scheme.isWeaklyRegular_of_le_iSup`), is a finite `A`-module
  (`Module.finite_of_isLocalization_pair`) and is étale over `U`, hence étale over `A` by the
  algebraic purity theorem `IsRegularLocalRing.etale_of_isWeaklyRegular_of_two_le_ringKrullDim`.

The main theorem is `isEquivalence_pullback_puncturedSpectrum`. The Hartogs results
(`bijective_restrict_preimage_puncturedSpectrum`, `bijective_appTop_ι_puncturedSpectrum`) and
`full_faithful_pullback_puncturedSpectrum` only need a noetherian local ring with a regular
sequence `x, y` in its maximal ideal.
-/

universe u

open CategoryTheory Limits IsLocalRing RingTheory.Sequence

namespace AlgebraicGeometry

/-- A ring map `Γ(Y) ⟶ Γ(Z)` into the sections of `Z` comes from a morphism `Z ⟶ Y` when `Y` is
affine. -/
theorem Scheme.exists_appTop_eq {Z Y : Scheme.{u}} [IsAffine Y] (θ : Γ(Y, ⊤) ⟶ Γ(Z, ⊤)) :
    ∃ ψ : Z ⟶ Y, ψ.appTop = θ := by
  refine ⟨Z.toSpecΓ ≫ Spec.map θ ≫ Y.isoSpec.inv, ?_⟩
  have h1 : Y.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(Y, ⊤)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.isoSpec_hom, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    rfl
  have h : Y.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Y, ⊤)).inv := by
    rw [← Category.comp_id (Y.isoSpec.inv.appTop), ← Iso.hom_inv_id (Scheme.ΓSpecIso Γ(Y, ⊤)),
      ← Category.assoc, h1, Category.id_comp]
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, h, Scheme.toSpecΓ_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

end AlgebraicGeometry

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (U : X.Opens) (P : MorphismProperty Scheme.{u})
  [P.IsStableUnderBaseChange]

omit [P.IsStableUnderBaseChange] in
set_option backward.isDefEq.respectTransparency false in
lemma MorphismProperty.Over.pullback_map_left_fst [P.IsStableUnderBaseChange] {Y₁ Y₂ : P.Over ⊤ X}
    (g : Y₁ ⟶ Y₂) :
    ((MorphismProperty.Over.pullback P ⊤ U.ι).map g).left ≫ pullback.fst Y₂.hom U.ι =
      pullback.fst Y₁.hom U.ι ≫ g.left := by
  simp [MorphismProperty.Over.pullback]

omit [P.IsStableUnderBaseChange] in
set_option backward.isDefEq.respectTransparency false in
lemma MorphismProperty.Over.pullback_map_left_snd [P.IsStableUnderBaseChange] {Y₁ Y₂ : P.Over ⊤ X}
    (g : Y₁ ⟶ Y₂) :
    ((MorphismProperty.Over.pullback P ⊤ U.ι).map g).left ≫ pullback.snd Y₂.hom U.ι =
      pullback.snd Y₁.hom U.ι := by
  simp [MorphismProperty.Over.pullback]

/-- Pullback of `P`-schemes over `X` to an open `U` is faithful if their global sections inject
into the sections over the preimage of `U`, and they are affine. -/
theorem MorphismProperty.Over.faithful_pullback_of_injective
    (h : ∀ Y : P.Over ⊤ X, IsAffine Y.left ∧ Function.Injective (pullback.fst Y.hom U.ι).appTop) :
    (MorphismProperty.Over.pullback P ⊤ U.ι).Faithful where
  map_injective {Y₁ Y₂} g₁ g₂ hg := by
    have := (h Y₂).1
    ext1
    apply ext_of_isAffine
    have e : pullback.fst Y₁.hom U.ι ≫ g₁.left = pullback.fst Y₁.hom U.ι ≫ g₂.left := by
      have := congrArg (fun φ ↦ φ.left ≫ pullback.fst Y₂.hom U.ι) hg
      exact (MorphismProperty.Over.pullback_map_left_fst U P g₁).symm.trans
        (this.trans (MorphismProperty.Over.pullback_map_left_fst U P g₂))
    have e' := congrArg Scheme.Hom.appTop e
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at e'
    ext z
    exact (h Y₁).2 congr($e' z)

/-- Pullback of `P`-schemes over an affine `X` to an open `U` is full if they are affine and their
global sections are the sections over the preimage of `U`. -/
theorem MorphismProperty.Over.full_pullback_of_bijective [IsAffine X]
    (h : ∀ Y : P.Over ⊤ X, IsAffine Y.left ∧ Function.Bijective (pullback.fst Y.hom U.ι).appTop) :
    (MorphismProperty.Over.pullback P ⊤ U.ι).Full where
  map_surjective {Y₁ Y₂} φ := by
    have := (h Y₂).1
    have := (h Y₁).1
    let F := MorphismProperty.Over.pullback P ⊤ U.ι
    let f₁ : (F.obj Y₁).left ⟶ Y₁.left := pullback.fst Y₁.hom U.ι
    let f₂ : (F.obj Y₂).left ⟶ Y₂.left := pullback.fst Y₂.hom U.ι
    let s₁ : (F.obj Y₁).left ⟶ U := pullback.snd Y₁.hom U.ι
    let s₂ : (F.obj Y₂).left ⟶ U := pullback.snd Y₂.hom U.ι
    have c₁ : f₁ ≫ Y₁.hom = s₁ ≫ U.ι := pullback.condition
    have c₂ : f₂ ≫ Y₂.hom = s₂ ≫ U.ι := pullback.condition
    have hiso : IsIso f₁.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr (h Y₁).2
    let θ : Γ(Y₂.left, ⊤) ⟶ Γ(Y₁.left, ⊤) := (φ.left ≫ f₂).appTop ≫ inv f₁.appTop
    obtain ⟨ψ, hψ⟩ := Scheme.exists_appTop_eq (Z := Y₁.left) (Y := Y₂.left) θ
    have hfst : f₁ ≫ ψ = φ.left ≫ f₂ := by
      apply ext_of_isAffine
      rw [Scheme.Hom.comp_appTop, hψ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hφ : φ.left ≫ s₂ = s₁ := MorphismProperty.Over.w φ
    have hw : ψ ≫ Y₂.hom = Y₁.hom := by
      have : IsAffine ((Functor.fromPUnit X).obj Y₂.right) := ‹IsAffine X›
      apply ext_of_isAffine
      rw [← cancel_mono f₁.appTop, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
      congr 1
      rw [← Category.assoc, hfst, Category.assoc, c₂, ← Category.assoc, hφ, ← c₁]
    refine ⟨MorphismProperty.Over.homMk ψ hw trivial, ?_⟩
    ext1
    apply pullback.hom_ext
    · exact (MorphismProperty.Over.pullback_map_left_fst U P _).trans hfst
    · exact (MorphismProperty.Over.pullback_map_left_snd U P _).trans hφ.symm

end AlgebraicGeometry

namespace AlgebraicGeometry

section PuncturedSpectrum

variable (R : CommRingCat.{u}) [IsLocalRing R]

/-- The punctured spectrum `Spec R \ {𝔪}` of a local ring `R`, as an open subscheme. -/
def puncturedSpectrum : (Spec R).Opens where
  carrier := {closedPoint R}ᶜ
  is_open' := (isClosed_singleton_closedPoint R).isOpen_compl

variable {R}

lemma mem_puncturedSpectrum {p : Spec R} : p ∈ puncturedSpectrum R ↔ p ≠ closedPoint R :=
  Iff.rfl

/-- If `x, y ∈ 𝔪` generate `𝔪` up to radical, the punctured spectrum is `D(x) ∪ D(y)`. -/
lemma puncturedSpectrum_eq_basicOpen_sup {x y : R} (hx : x ∈ maximalIdeal R)
    (hy : y ∈ maximalIdeal R) (hxy : maximalIdeal R ≤ (Ideal.span {x, y}).radical) :
    puncturedSpectrum R = PrimeSpectrum.basicOpen x ⊔ PrimeSpectrum.basicOpen y := by
  refine TopologicalSpace.Opens.ext (Set.ext fun (p : PrimeSpectrum R) ↦ ?_)
  change p ≠ closedPoint R ↔ x ∉ p.asIdeal ∨ y ∉ p.asIdeal
  constructor
  · intro hp
    by_contra! h
    apply hp
    apply PrimeSpectrum.ext
    refine ((maximalIdeal.isMaximal R).eq_of_le p.2.ne_top ?_).symm
    refine hxy.trans (p.2.radical_le_iff.mpr ?_)
    rw [Ideal.span_le]
    rintro z (rfl | rfl)
    exacts [h.1, h.2]
  · rintro (h | h) rfl
    exacts [h hx, h hy]

end PuncturedSpectrum

end AlgebraicGeometry

/-- The image of a regular pair under a ring isomorphism is a regular pair. -/
theorem isWeaklyRegular_pair_map_ringEquiv {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T)
    {a b : S} (h : IsWeaklyRegular S [a, b]) : IsWeaklyRegular T [e a, e b] := by
  rw [isWeaklyRegular_pair_iff] at h ⊢
  obtain ⟨ha, hdiv⟩ := h
  refine ⟨fun u v huv ↦ e.symm.injective (ha ?_), fun z ⟨c, hc⟩ ↦ ?_⟩
  · have := congrArg e.symm huv
    simp only [smul_eq_mul, map_mul, RingEquiv.symm_apply_apply] at this
    exact this
  · obtain ⟨d, hd⟩ := hdiv (e.symm z) ⟨e.symm c, e.injective (by simp [map_mul, hc])⟩
    exact ⟨e d, e.symm.injective (by simp [map_mul, hd])⟩

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- Regularity of a pair of sections is local: if the open `V` is covered by opens `Uᵢ` such that
`a, b ∈ Γ(V)` restrict to a regular sequence on every `Γ(Uᵢ)` and `a` to a nonzerodivisor on
every `Γ(Uᵢ ∩ Uⱼ)`, then `a, b` is a regular sequence on `Γ(V)`. -/
theorem isWeaklyRegular_of_le_iSup {ι : Type*} {V : X.Opens} (U : ι → X.Opens)
    (hU : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i) {a b : Γ(X, V)}
    (h1 : ∀ i, IsWeaklyRegular Γ(X, U i)
      [X.presheaf.map (homOfLE (hU i)).op a, X.presheaf.map (homOfLE (hU i)).op b])
    (h2 : ∀ i j, ∀ s : Γ(X, U i ⊓ U j),
      X.presheaf.map (homOfLE (inf_le_left.trans (hU i))).op a * s = 0 → s = 0) :
    IsWeaklyRegular Γ(X, V) [a, b] := by
  let r : ∀ i, Γ(X, V) ⟶ Γ(X, U i) := fun i ↦ X.presheaf.map (homOfLE (hU i)).op
  have hext : ∀ s t : Γ(X, V), (∀ i, r i s = r i t) → s = t := fun s t h ↦
    X.sheaf.eq_of_locally_eq' U V (fun i ↦ homOfLE (hU i)) hcover s t h
  -- restrictions to `Uᵢ ∩ Uⱼ` through `Uᵢ` and through `Uⱼ` agree
  have hres : ∀ i j (z : Γ(X, V)),
      X.presheaf.map (TopologicalSpace.Opens.infLELeft (U i) (U j)).op (r i z) =
        X.presheaf.map (homOfLE (inf_le_left.trans (hU i))).op z ∧
      X.presheaf.map (TopologicalSpace.Opens.infLERight (U i) (U j)).op (r j z) =
        X.presheaf.map (homOfLE (inf_le_left.trans (hU i))).op z := by
    intro i j z
    constructor <;>
    · simp only [r, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
  rw [isWeaklyRegular_pair_iff]
  refine ⟨fun c₁ c₂ hc ↦ hext _ _ fun i ↦ ?_, fun z ⟨c', hc'⟩ ↦ ?_⟩
  · refine ((isWeaklyRegular_pair_iff _ _).mp (h1 i)).1 ?_
    change r i a * r i c₁ = r i a * r i c₂
    rw [← map_mul, ← map_mul]
    exact congrArg (r i) hc
  · -- `b z = a c'`: divide `z` by `a` locally and glue
    have hdiv : ∀ i, ∃ e, r i z = r i a * e := fun i ↦
      ((isWeaklyRegular_pair_iff _ _).mp (h1 i)).2 (r i z)
        ⟨r i c', by rw [← map_mul, ← map_mul, hc']⟩
    choose e he using hdiv
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U e := by
      intro i j
      change X.presheaf.map (TopologicalSpace.Opens.infLELeft (U i) (U j)).op (e i) =
        X.presheaf.map (TopologicalSpace.Opens.infLERight (U i) (U j)).op (e j)
      apply sub_eq_zero.mp
      apply h2 i j
      rw [mul_sub]
      have ei := congrArg (X.presheaf.map (TopologicalSpace.Opens.infLELeft (U i) (U j)).op)
        (he i)
      have ej := congrArg (X.presheaf.map (TopologicalSpace.Opens.infLERight (U i) (U j)).op)
        (he j)
      rw [map_mul, (hres i j z).1, (hres i j a).1] at ei
      rw [map_mul, (hres i j z).2, (hres i j a).2] at ej
      change _ - X.presheaf.map (homOfLE (inf_le_left.trans (hU i))).op a *
        X.presheaf.map (TopologicalSpace.Opens.infLERight (U i) (U j)).op (e j) = 0
      rw [← ei, ← ej, sub_self]
    obtain ⟨s, hs, -⟩ :=
      X.sheaf.existsUnique_gluing' U V (fun i ↦ homOfLE (hU i)) hcover e hcompat
    let s' : Γ(X, V) := s
    have hs' : ∀ i, r i s' = e i := hs
    refine ⟨s', hext _ _ fun i ↦ ?_⟩
    rw [map_mul, he i, hs' i]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} [IsLocalRing R]

/-- Bijectivity of the restriction from `⊤` to an open only depends on the open. -/
lemma Scheme.bijective_presheaf_map_congr {X : Scheme.{u}} {V V' : X.Opens} (h : V = V') :
    Function.Bijective (X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op) ↔
      Function.Bijective (X.presheaf.map (homOfLE le_top : V' ⟶ ⊤).op) := by
  subst h; rfl

/-- A basic open `D(f)`, `f ∈ 𝔪`, lies in the punctured spectrum. -/
lemma basicOpen_le_puncturedSpectrum {f : R} (hf : f ∈ maximalIdeal R) :
    (PrimeSpectrum.basicOpen f : (Spec R).Opens) ≤ puncturedSpectrum R := by
  intro p hp
  change p ≠ closedPoint R
  rintro rfl
  exact hp hf

/-- Sections over the preimage of the punctured spectrum in a flat affine `Y ⟶ Spec R` are
determined by their restriction to `D(x)`, for `x ∈ 𝔪` a nonzerodivisor: the preimage is covered
by the `D(g)`, `g ∈ 𝔪`, on which `x` stays a nonzerodivisor by flatness. -/
theorem injective_restrict_basicOpen_preimage_puncturedSpectrum {x : R}
    (hx0 : x ∈ nonZeroDivisors R) {Y : Scheme.{u}} (f : Y ⟶ Spec R) [IsAffineHom f] [Flat f]
    (h : Y.basicOpen (((Scheme.ΓSpecIso R).inv ≫ f.appTop) x) ≤ f ⁻¹ᵁ puncturedSpectrum R) :
    Function.Injective (Y.presheaf.map (homOfLE h).op) := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  let φ : R ⟶ Γ(Y, ⊤) := (Scheme.ΓSpecIso R).inv ≫ f.appTop
  let _ : Algebra R Γ(Y, ⊤) := φ.hom.toAlgebra
  have : Module.Flat R Γ(Y, ⊤) := by
    change φ.hom.Flat
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv))
      (HasRingHomProperty.appTop @Flat f inferInstance)
  let V := f ⁻¹ᵁ puncturedSpectrum R
  have hbo : ∀ g : R, Y.basicOpen (φ g) = f ⁻¹ᵁ PrimeSpectrum.basicOpen g := fun g ↦ by
    rw [← basicOpen_eq_of_affine, Scheme.preimage_basicOpen_top]
    rfl
  have hle : ∀ g ∈ maximalIdeal R, Y.basicOpen (φ g) ≤ V := fun g hg ↦ by
    rw [hbo]
    exact fun y hy ↦ basicOpen_le_puncturedSpectrum hg hy
  -- `x` stays a nonzerodivisor on `Γ(D(g))`
  have hxreg : ∀ (g : R) (t : Γ(Y, Y.basicOpen (φ g))),
      algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen (φ g)) (φ x) * t = 0 → t = 0 := by
    intro g t ht
    let Yg := Γ(Y, Y.basicOpen (φ g))
    let _ : Algebra R Yg := ((algebraMap Γ(Y, ⊤) Yg).comp φ.hom).toAlgebra
    have : IsScalarTower R Γ(Y, ⊤) Yg := IsScalarTower.of_algebraMap_eq' rfl
    have : Module.Flat Γ(Y, ⊤) Yg := IsLocalization.flat Yg (Submonoid.powers (φ g))
    have : Module.Flat R Yg := Module.Flat.trans R Γ(Y, ⊤) Yg
    have hxr : IsSMulRegular Yg x := Module.Flat.isSMulRegular_of_nonZeroDivisors hx0
    exact hxr.right_eq_zero_of_smul (by rw [Algebra.smul_def]; exact ht)
  intro s t hst
  refine Y.sheaf.eq_of_locally_eq' (fun g : {g : R // g ∈ maximalIdeal R} ↦ Y.basicOpen (φ g)) V
    (fun g ↦ homOfLE (hle g g.2)) ?_ s t fun g ↦ ?_
  · -- the `D(g)`, `g ∈ 𝔪`, cover the preimage of the punctured spectrum
    intro y hy
    have hy' : f.base y ≠ closedPoint R := hy
    obtain ⟨g, hgm, hgy⟩ : ∃ g ∈ maximalIdeal R, g ∉ (f.base y).asIdeal := by
      by_contra! H
      exact hy' (PrimeSpectrum.ext ((maximalIdeal.isMaximal R).eq_of_le
        (f.base y).2.ne_top H).symm)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hgm⟩, ?_⟩
    change y ∈ Y.basicOpen (φ g)
    rw [hbo]
    exact hgy
  · -- on `D(g)`, the two sections agree after inverting `x`, hence agree
    obtain ⟨g, hg⟩ := g
    let Ug := Y.basicOpen (φ g)
    have hUg : IsAffineOpen Ug := (isAffineOpen_top Y).basicOpen (φ g)
    let ag : Γ(Y, Ug) := algebraMap Γ(Y, ⊤) Γ(Y, Ug) (φ x)
    have hL := hUg.isLocalization_basicOpen ag
    have hle' : Y.basicOpen ag ≤ Y.basicOpen (φ x) := by
      change Y.basicOpen ((Y.presheaf.map (homOfLE le_top : Ug ⟶ ⊤).op) (φ x)) ≤ _
      rw [Scheme.basicOpen_res]
      exact inf_le_right
    have e : ∀ z : Γ(Y, V), algebraMap Γ(Y, Ug) Γ(Y, Y.basicOpen ag)
        (Y.presheaf.map (homOfLE (hle g hg)).op z) =
          Y.presheaf.map (homOfLE hle').op (Y.presheaf.map (homOfLE h).op z) := by
      intro z
      change (Y.presheaf.map _) ((Y.presheaf.map _) z) = (Y.presheaf.map _) ((Y.presheaf.map _) z)
      simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    have h1 : algebraMap Γ(Y, Ug) Γ(Y, Y.basicOpen ag) (Y.presheaf.map (homOfLE (hle g hg)).op s) =
        algebraMap Γ(Y, Ug) Γ(Y, Y.basicOpen ag) (Y.presheaf.map (homOfLE (hle g hg)).op t) := by
      rw [e, e, hst]
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers ag) h1
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
    rw [← hn, ← sub_eq_zero, ← mul_sub] at hc
    have hpow : ∀ n : ℕ, ∀ u : Γ(Y, Ug), ag ^ n * u = 0 → u = 0 := by
      intro n
      induction n with
      | zero => intro u hu; simpa using hu
      | succ n ih =>
        intro u hu
        exact ih u (hxreg g _ (by rw [← mul_assoc, ← pow_succ']; exact hu))
    exact sub_eq_zero.mp (hpow n _ hc)

/-- Hartogs extension for flat affine schemes over a local ring of depth `≥ 2`: if `x, y ∈ 𝔪` is a
regular sequence and `f : Y ⟶ Spec R` is affine and flat, every section of `𝒪_Y` over the
preimage of the punctured spectrum extends uniquely to `Y`. -/
theorem bijective_restrict_preimage_puncturedSpectrum {x y : R} (hx : x ∈ maximalIdeal R)
    (hy : y ∈ maximalIdeal R) (hreg : IsWeaklyRegular R [x, y]) {Y : Scheme.{u}}
    (f : Y ⟶ Spec R) [IsAffineHom f] [Flat f] : Function.Bijective
      (Y.presheaf.map (homOfLE le_top : f ⁻¹ᵁ puncturedSpectrum R ⟶ ⊤).op) := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  let φ : R ⟶ Γ(Y, ⊤) := (Scheme.ΓSpecIso R).inv ≫ f.appTop
  let a := φ x
  let b := φ y
  let V := f ⁻¹ᵁ puncturedSpectrum R
  have hle : ∀ g ∈ maximalIdeal R, Y.basicOpen (φ g) ≤ V := fun g hg ↦ by
    have : Y.basicOpen (φ g) = f ⁻¹ᵁ PrimeSpectrum.basicOpen g := by
      rw [← basicOpen_eq_of_affine, Scheme.preimage_basicOpen_top]
      rfl
    rw [this]
    exact fun y hy ↦ basicOpen_le_puncturedSpectrum hg hy
  have hW : Y.basicOpen a ⊔ Y.basicOpen b ≤ V := sup_le (hle x hx) (hle y hy)
  have hreg' : IsWeaklyRegular Γ(Y, ⊤) [a, b] := by
    let := φ.hom.toAlgebra
    have : Module.Flat R Γ(Y, ⊤) := by
      change φ.hom.Flat
      exact RingHom.Flat.comp (RingHom.Flat.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv))
        (HasRingHomProperty.appTop @Flat f inferInstance)
    exact hreg.of_flat (S := Γ(Y, ⊤))
  have hx0 : x ∈ nonZeroDivisors R := by
    have hxr := ((isWeaklyRegular_cons_iff R x [y]).mp hreg).1
    exact mem_nonZeroDivisors_iff_right.mpr fun z hz ↦
      hxr.right_eq_zero_of_smul (by rw [smul_eq_mul, mul_comm, hz])
  have hinj := injective_restrict_basicOpen_preimage_puncturedSpectrum hx0 f (hle x hx)
  have htop := Scheme.bijective_restrict_basicOpen_sup Y hreg'
  let r1 := Y.presheaf.map (homOfLE le_top : V ⟶ ⊤).op
  let r2 := Y.presheaf.map (homOfLE hW : Y.basicOpen a ⊔ Y.basicOpen b ⟶ V).op
  let r3 := Y.presheaf.map (homOfLE le_sup_left : Y.basicOpen a ⟶ Y.basicOpen a ⊔ Y.basicOpen b).op
  have e1 : ∀ z, r2 (r1 z) =
      Y.presheaf.map (homOfLE le_top : Y.basicOpen a ⊔ Y.basicOpen b ⟶ ⊤).op z := fun z ↦ by
    simp only [r1, r2, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  have e2 : ∀ z, r3 (r2 z) = Y.presheaf.map (homOfLE (hle x hx)).op z := fun z ↦ by
    simp only [r2, r3, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  have hr2 : Function.Injective r2 := fun s t hst ↦ hinj (by rw [← e2, ← e2, hst])
  refine ⟨fun s t hst ↦ htop.1 (by rw [← e1, ← e1]; exact congrArg r2 hst), fun s ↦ ?_⟩
  obtain ⟨t, ht⟩ := htop.2 (r2 s)
  exact ⟨t, hr2 (by rw [e1, ht])⟩

/-- The form of `bijective_restrict_preimage_puncturedSpectrum` used for base change. -/
theorem bijective_appTop_pullback_fst_puncturedSpectrum {x y : R} (hx : x ∈ maximalIdeal R)
    (hy : y ∈ maximalIdeal R) (hreg : IsWeaklyRegular R [x, y]) {Y : Scheme.{u}}
    (f : Y ⟶ Spec R) [IsAffineHom f] [Flat f] :
    Function.Bijective (pullback.fst f (puncturedSpectrum R).ι).appTop := by
  have hH := bijective_restrict_preimage_puncturedSpectrum hx hy hreg f
  rw [← Scheme.bijective_presheaf_map_congr (Scheme.Opens.ι_image_top _)] at hH
  have he : Function.Bijective (pullbackRestrictIsoRestrict f (puncturedSpectrum R)).hom.appTop :=
    ConcreteCategory.bijective_of_isIso ((pullbackRestrictIsoRestrict f _).hom.app ⊤)
  rw [← pullbackRestrictIsoRestrict_hom_ι, Scheme.Hom.comp_appTop]
  exact he.comp hH

/-- `Γ(Spec R) → Γ(U)` is bijective for the punctured spectrum `U` of a local ring of depth
`≥ 2`. -/
theorem bijective_appTop_ι_puncturedSpectrum {x y : R} (hx : x ∈ maximalIdeal R)
    (hy : y ∈ maximalIdeal R) (hreg : IsWeaklyRegular R [x, y]) :
    Function.Bijective (puncturedSpectrum R).ι.appTop := by
  have hH := bijective_restrict_preimage_puncturedSpectrum hx hy hreg (𝟙 (Spec R))
  rw [Scheme.Hom.appTop, Scheme.Opens.ι_app]
  exact (Scheme.bijective_presheaf_map_congr (by simp)).mp hH

/-- Base change of affine flat schemes over `Spec R` to the punctured spectrum is fully faithful,
when `R` is local of depth `≥ 2` (witnessed by a regular sequence `x, y` in `𝔪`). -/
theorem full_faithful_pullback_puncturedSpectrum {x y : R} (hx : x ∈ maximalIdeal R)
    (hy : y ∈ maximalIdeal R) (hreg : IsWeaklyRegular R [x, y]) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    (hP : ∀ {Y : Scheme.{u}} (f : Y ⟶ Spec R), P f → IsAffineHom f ∧ Flat f) :
    (MorphismProperty.Over.pullback P ⊤ (puncturedSpectrum R).ι).Full ∧
      (MorphismProperty.Over.pullback P ⊤ (puncturedSpectrum R).ι).Faithful := by
  have h : ∀ Y : P.Over ⊤ (Spec R), IsAffine Y.left ∧
      Function.Bijective (pullback.fst Y.hom (puncturedSpectrum R).ι).appTop := by
    intro Y
    obtain ⟨_, _⟩ := hP Y.hom Y.prop
    have : IsAffine ((Functor.fromPUnit (Spec R)).obj Y.right) :=
      inferInstanceAs (IsAffine (Spec R))
    exact ⟨isAffine_of_isAffineHom Y.hom,
      bijective_appTop_pullback_fst_puncturedSpectrum hx hy hreg Y.hom⟩
  exact ⟨MorphismProperty.Over.full_pullback_of_bijective _ P h,
    MorphismProperty.Over.faithful_pullback_of_injective _ P fun Y ↦ ⟨(h Y).1, (h Y).2.1⟩⟩

end AlgebraicGeometry

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} [IsLocalRing R]

instance : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := by
  have : MorphismProperty.IsStableUnderBaseChange @IsFinite.{u} := inferInstance
  have : MorphismProperty.IsStableUnderBaseChange @Etale.{u} := inferInstance
  exact MorphismProperty.IsStableUnderBaseChange.inf

/-- The punctured spectrum of a noetherian local ring is quasi-affine. -/
instance [IsNoetherianRing R] : (puncturedSpectrum R).toScheme.IsQuasiAffine := by
  have : CompactSpace (puncturedSpectrum R) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  exact .of_isImmersion (puncturedSpectrum R).ι

/-- Let `U` be the punctured spectrum of a noetherian local ring `R` of depth `≥ 2`. An affine
scheme `w : W ⟶ U` is the base change to `U` of `Spec Γ(W) ⟶ Spec R`. -/
theorem isPullback_toSpecΓ_puncturedSpectrum [IsNoetherianRing R] {x y : R}
    (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R)
    (hreg : IsWeaklyRegular R [x, y])
    {W : Scheme.{u}} (w : W ⟶ puncturedSpectrum R) [IsAffineHom w] :
    IsPullback W.toSpecΓ w
      (Spec.map ((Scheme.ΓSpecIso R).inv ≫ (puncturedSpectrum R).ι.appTop ≫ w.appTop))
      (puncturedSpectrum R).ι := by
  let U := puncturedSpectrum R
  have hP := Scheme.isPullback_toSpecΓ_toSpecΓ w
  have : IsIso U.ι.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr
    (bijective_appTop_ι_puncturedSpectrum hx hy hreg)
  let e : Spec Γ(U, ⊤) ≅ Spec R := asIso (Spec.map U.ι.appTop) ≪≫ (Spec R).isoSpec.symm
  refine (hP.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_).flip
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.id_comp, e, Iso.trans_hom, asIso_hom, Iso.symm_hom]
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, e, Iso.trans_hom, asIso_hom, Iso.symm_hom,
      Scheme.isoSpec_Spec_inv, Spec.map_comp, Category.assoc]
    rfl

/-- If `W ⟶ V` is the base change of `Spec.map φ : Spec C ⟶ Spec R` to an open `V`, a property `Q`
of `W ⟶ V` that is local on the target passes to `Spec C_f ⟶ Spec R_f` for `D(f) ⊆ V`. -/
theorem SpecMap_awayMap_of_isPullback (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    (hres : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Y.Opens), Q g → Q (g ∣_ V))
    {R C : CommRingCat.{u}} {φ : R ⟶ C} {W : Scheme.{u}}
    {V : (Spec R).Opens} {t : W ⟶ Spec C} {w : W ⟶ V}
    (sq : IsPullback t w (Spec.map φ) V.ι) (hw : Q w) {f : R}
    (hf : PrimeSpectrum.basicOpen f ≤ V) :
    Q (Spec.map (CommRingCat.ofHom (Localization.awayMap φ.hom f))) := by
  have h1 : Q (Spec.map φ ∣_ V) := by
    have e1 : sq.isoPullback.inv ≫ w = pullback.snd _ _ := by
      rw [Iso.inv_comp_eq, sq.isoPullback_hom_snd]
    have : Spec.map φ ∣_ V = ((pullbackRestrictIsoRestrict (Spec.map φ) V).inv ≫
        sq.isoPullback.inv) ≫ w := by
      rw [Category.assoc, e1]
      rfl
    rw [this, Q.cancel_left_of_respectsIso]
    exact hw
  let D : (Spec R).Opens := PrimeSpectrum.basicOpen f
  have h2 := hres _ (V.ι ⁻¹ᵁ D) h1
  have hD : V ⊓ D = D := inf_eq_right.mpr hf
  rw [Q.arrow_mk_iso_iff (morphismRestrictRestrict _ _ _),
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, hD] at h2
  exact (Q.arrow_mk_iso_iff (SpecMapRestrictBasicOpenIso φ f)).mp h2

/-- Local finiteness and étaleness of `Spec Γ(W) ⟶ Spec R` over the punctured spectrum. -/
theorem finite_etale_awayMap_of_puncturedSpectrum [IsNoetherianRing R] {x y : R}
    (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R)
    (hreg : IsWeaklyRegular R [x, y])
    {W : Scheme.{u}} (w : W ⟶ puncturedSpectrum R) [IsFinite w] [Etale w] {f : R}
    (hf : f ∈ maximalIdeal R) :
    (Localization.awayMap ((Scheme.ΓSpecIso R).inv ≫ (puncturedSpectrum R).ι.appTop ≫
      w.appTop).hom f).Finite ∧
    (Localization.awayMap ((Scheme.ΓSpecIso R).inv ≫ (puncturedSpectrum R).ι.appTop ≫
      w.appTop).hom f).Etale := by
  have sq := isPullback_toSpecΓ_puncturedSpectrum hx hy hreg w
  have : MorphismProperty.RespectsIso @IsFinite.{u} :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f hf ↦ by
      have : IsIso f := hf
      infer_instance
  have : MorphismProperty.IsStableUnderComposition @Etale.{u} :=
    (inferInstance : MorphismProperty.IsMultiplicative @Etale.{u}).toIsStableUnderComposition
  have : MorphismProperty.RespectsIso @Etale.{u} :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f hf ↦ by
      have : IsIso f := hf
      infer_instance
  constructor
  · have := SpecMap_awayMap_of_isPullback @IsFinite (fun g V h ↦ by have := h; infer_instance)
      sq inferInstance (basicOpen_le_puncturedSpectrum hf)
    rwa [IsFinite.SpecMap_iff] at this
  · have := SpecMap_awayMap_of_isPullback @Etale (fun g V h ↦ by have := h; infer_instance)
      sq inferInstance (basicOpen_le_puncturedSpectrum hf)
    rwa [HasRingHomProperty.Spec_iff (P := @Etale)] at this

end AlgebraicGeometry

namespace AlgebraicGeometry

section AwayMap

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (f : A)

/-- With `Aₓ → Bₓ` given by `Localization.awayMap`, the tower `A → Aₓ → Bₓ` is a scalar tower. -/
lemma isScalarTower_awayMap :
    letI := φ.toAlgebra
    letI := (Localization.awayMap φ f).toAlgebra
    IsScalarTower A (Localization.Away f) (Localization.Away (φ f)) := by
  let := φ.toAlgebra
  let := (Localization.awayMap φ f).toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  rw [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
    IsLocalization.map_comp, IsScalarTower.algebraMap_eq A B, RingHom.algebraMap_toAlgebra]

/-- If `Aₓ → Bₓ` is étale, then `Bₓ` is formally étale over `A`. -/
lemma formallyEtale_away_of_awayMap (h : (Localization.awayMap φ f).Etale) :
    letI := φ.toAlgebra
    Algebra.FormallyEtale A (Localization.Away (φ f)) := by
  let := φ.toAlgebra
  let := (Localization.awayMap φ f).toAlgebra
  have := isScalarTower_awayMap φ f
  have : Algebra.Etale (Localization.Away f) (Localization.Away (φ f)) := h
  have : Algebra.FormallyEtale A (Localization.Away f) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)
  exact Algebra.FormallyEtale.comp A (Localization.Away f) _

end AwayMap


section Regular

variable {R : CommRingCat.{u}} [IsRegularLocalRing R]

/-- A regular local ring of dimension two has a regular system of parameters `x, y`. -/
lemma IsRegularLocalRing.exists_regular_pair (hdim : ringKrullDim R = 2) :
    ∃ x y : R, x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧
      maximalIdeal R ≤ (Ideal.span {x, y}).radical ∧ IsWeaklyRegular R [x, y] := by
  obtain ⟨rs, hlen, hspan, hreg⟩ :=
    IsRegularLocalRing.exists_isRegular_ofList_eq_maximalIdeal (R := R)
  rw [hdim] at hlen
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp (by exact_mod_cast hlen)
  have hsp : Ideal.span {x, y} = maximalIdeal R := by
    rw [← hspan]
    congr 1
    ext z
    simp
  refine ⟨x, y, ?_, ?_, ?_, hreg.1⟩
  · rw [← hsp]; exact Ideal.subset_span (by simp)
  · rw [← hsp]; exact Ideal.subset_span (by simp)
  · rw [hsp]; exact Ideal.le_radical

/-- A regular local ring of dimension `≥ 2` has a regular sequence `x, y` in its maximal ideal. -/
lemma IsRegularLocalRing.exists_isWeaklyRegular_pair (hdim : 2 ≤ ringKrullDim R) :
    ∃ x y : R, x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧ IsWeaklyRegular R [x, y] := by
  have hdepth : ((2 : ℕ) : ℕ∞) ≤ (maximalIdeal R).depth R := by
    have := IsRegularLocalRing.depth_eq_ringKrullDim (R := R)
    rw [← this] at hdim
    exact WithBot.coe_le_coe.mp hdim
  obtain ⟨rs, hlen, hmem, hrs⟩ := (Ideal.le_depth_iff (maximalIdeal R) R 2).mp hdepth
  obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp hlen
  exact ⟨x, y, hmem x (by simp), hmem y (by simp), hrs⟩

/-- **Zariski–Nagata purity** for the punctured spectrum `U` of a regular local ring `R` of
dimension `≥ 2`, essential surjectivity: every finite étale `U`-scheme extends to a finite étale
`Spec R`-scheme. -/
theorem essSurj_pullback_puncturedSpectrum (hdim : 2 ≤ ringKrullDim R) :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ (puncturedSpectrum R).ι).EssSurj where
  mem_essImage W := by
    obtain ⟨x, y, hx, hy, hreg⟩ := IsRegularLocalRing.exists_isWeaklyRegular_pair hdim
    have : IsFinite W.hom := W.prop.1
    have : Etale W.hom := W.prop.2
    let w : W.left ⟶ puncturedSpectrum R := W.hom
    let C : CommRingCat := Γ(W.left, ⊤)
    let φ : R ⟶ C := (Scheme.ΓSpecIso R).inv ≫ (puncturedSpectrum R).ι.appTop ≫ w.appTop
    have sq : IsPullback W.left.toSpecΓ w (Spec.map φ) (puncturedSpectrum R).ι :=
      isPullback_toSpecΓ_puncturedSpectrum hx hy hreg w
    let : Algebra R C := φ.hom.toAlgebra
    have hloc := fun f hf ↦ finite_etale_awayMap_of_puncturedSpectrum hx hy hreg w (f := f) hf
    have hW : W.left.IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom w
    -- `C_g` is flat over `R` for `g ∈ 𝔪`
    have hflat : ∀ g ∈ maximalIdeal R, Module.Flat R (Localization.Away (φ g)) := by
      intro g hg
      let := (Localization.awayMap φ.hom g).toAlgebra
      have : IsScalarTower R (Localization.Away g) (Localization.Away (φ g)) :=
        isScalarTower_awayMap φ.hom g
      have : Algebra.Etale (Localization.Away g) (Localization.Away (φ g)) := (hloc g hg).2
      have : Module.Flat R (Localization.Away g) := IsLocalization.flat _ (Submonoid.powers g)
      exact Module.Flat.trans R (Localization.Away g) _
    -- `x, y` is regular on `Γ(D(g)) = C_g` for `g ∈ 𝔪`
    have hregg : ∀ g ∈ maximalIdeal R, IsWeaklyRegular Γ(W.left, W.left.basicOpen (φ g))
        [W.left.presheaf.map (homOfLE le_top : W.left.basicOpen (φ g) ⟶ ⊤).op (φ x),
          W.left.presheaf.map (homOfLE le_top : W.left.basicOpen (φ g) ⟶ ⊤).op (φ y)] := by
      intro g hg
      have := hflat g hg
      have h1 := hreg.of_flat (S := Localization.Away (φ g))
      have hL := isLocalization_basicOpen_of_qcqs (X := W.left) (U := ⊤) isCompact_univ
        isQuasiSeparated_univ (φ g)
      let e : Localization.Away (φ g) ≃ₐ[C] Γ(W.left, W.left.basicOpen (φ g)) :=
        IsLocalization.algEquiv (Submonoid.powers (φ g)) _ _
      have h2 := isWeaklyRegular_pair_map_ringEquiv e.toRingEquiv
        (a := algebraMap R (Localization.Away (φ g)) x)
        (b := algebraMap R (Localization.Away (φ g)) y) h1
      have hex : ∀ r : R, e.toRingEquiv (algebraMap R (Localization.Away (φ g)) r) =
          W.left.presheaf.map (homOfLE le_top : W.left.basicOpen (φ g) ⟶ ⊤).op (φ r) := by
        intro r
        rw [IsScalarTower.algebraMap_apply R C (Localization.Away (φ g))]
        exact e.commutes (φ r)
      rw [hex, hex] at h2
      exact h2
    -- the `D(g)`, `g ∈ 𝔪`, cover `W`
    have hbo : ∀ g : R, W.left.basicOpen (φ g) =
        w ⁻¹ᵁ ((puncturedSpectrum R).ι ⁻¹ᵁ PrimeSpectrum.basicOpen g) := by
      intro g
      rw [← basicOpen_eq_of_affine, Scheme.preimage_basicOpen_top, Scheme.preimage_basicOpen_top]
      rfl
    have hcover : (⊤ : W.left.Opens) ≤
        ⨆ g : {g : R // g ∈ maximalIdeal R}, W.left.basicOpen (φ g) := by
      intro z _
      have hz : (puncturedSpectrum R).ι.base (w.base z) ≠ closedPoint R := (w.base z).2
      obtain ⟨g, hgm, hgz⟩ : ∃ g ∈ maximalIdeal R,
          g ∉ ((puncturedSpectrum R).ι.base (w.base z)).asIdeal := by
        by_contra! H
        exact hz (PrimeSpectrum.ext ((maximalIdeal.isMaximal R).eq_of_le
          ((puncturedSpectrum R).ι.base (w.base z)).2.ne_top H).symm)
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hgm⟩, ?_⟩
      rw [hbo]
      exact hgz
    -- `x` is regular on the intersections `D(g) ∩ D(h) = D(gh)`
    have h2 : ∀ g h : {g : R // g ∈ maximalIdeal R},
        ∀ s : Γ(W.left, W.left.basicOpen (φ g) ⊓ W.left.basicOpen (φ h)),
          W.left.presheaf.map (homOfLE (inf_le_left.trans le_top)).op (φ x) * s = 0 → s = 0 := by
      intro g h s hs
      have hE : W.left.basicOpen (φ (g * h)) = W.left.basicOpen (φ g) ⊓ W.left.basicOpen (φ h) := by
        rw [map_mul, Scheme.basicOpen_mul]
      let τ := W.left.presheaf.map (eqToHom hE).op
      have hτ : Function.Injective τ :=
        (ConcreteCategory.bijective_of_isIso (W.left.presheaf.map (eqToHom hE).op)).1
      have hx' := ((isWeaklyRegular_cons_iff _ _ _).mp
        (hregg (g * h) (Ideal.mul_mem_right _ _ g.2))).1
      have e1 : τ (W.left.presheaf.map (homOfLE (inf_le_left.trans le_top) :
          W.left.basicOpen (φ g) ⊓ W.left.basicOpen (φ h) ⟶ ⊤).op (φ x)) =
          W.left.presheaf.map (homOfLE le_top : W.left.basicOpen (φ (g * h)) ⟶ ⊤).op (φ x) := by
        change (W.left.presheaf.map _ ≫ W.left.presheaf.map (eqToHom hE).op) (φ x) = _
        rw [← Functor.map_comp]
        rfl
      apply hτ
      rw [map_zero]
      apply hx'
      change _ * τ s = _ * 0
      rw [mul_zero, ← e1, ← map_mul, hs, map_zero]
    -- the ring `C = Γ(W)` has depth `≥ 2`
    have hregC : IsWeaklyRegular C [x, y] := by
      have := Scheme.isWeaklyRegular_of_le_iSup W.left
        (fun g : {g : R // g ∈ maximalIdeal R} ↦ W.left.basicOpen (φ g)) (fun _ ↦ le_top)
        hcover (a := φ x) (b := φ y) (fun g ↦ hregg g g.2) h2
      exact (isWeaklyRegular_map_algebraMap_iff (R := R) (S := C) (M := C) [x, y]).mp this
    -- `C` is a finite `R`-module
    have hfin : Module.Finite R C := by
      have hxC : IsSMulRegular C x := ((isWeaklyRegular_cons_iff C x [y]).mp hregC).1
      have hmap : ∀ f : R, Algebra.algebraMapSubmonoid C (Submonoid.powers f) =
          Submonoid.powers (algebraMap R C f) := fun f ↦ Submonoid.map_powers _ _
      let Cx := Localization.Away (algebraMap R C x)
      let := (Localization.awayMap φ.hom x).toAlgebra
      have : IsScalarTower R (Localization.Away x) Cx := isScalarTower_awayMap φ.hom x
      have : Module.Finite (Localization.Away x) Cx := (hloc x hx).1
      have : Algebra.Etale (Localization.Away x) Cx := (hloc x hx).2
      have : Module.FinitePresentation (Localization.Away x) Cx :=
        Module.finitePresentation_of_finite _ _
      have : Module.Projective (Localization.Away x) Cx :=
        Module.Flat.projective_of_finitePresentation
      have : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers x)) Cx := by
        rw [hmap]; infer_instance
      let Cy := Localization.Away (algebraMap R C y)
      let := (Localization.awayMap φ.hom y).toAlgebra
      have : IsScalarTower R (Localization.Away y) Cy := isScalarTower_awayMap φ.hom y
      have : Module.Finite (Localization.Away y) Cy := (hloc y hy).1
      have : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers y)) Cy := by
        rw [hmap]; infer_instance
      exact Module.finite_of_isLocalization_pair hreg hxC (Localization.Away x) Cx
        (Localization.Away y) Cy
    -- `C` is étale over the punctured spectrum, hence étale over `R` by algebraic purity
    have hU : ∀ (Q : Ideal C) [Q.IsPrime], Q.comap (algebraMap R C) ≠ maximalIdeal R →
        Algebra.IsEtaleAt R Q := by
      intro Q _ hQ
      obtain ⟨g, hgm, hgQ⟩ : ∃ g ∈ maximalIdeal R, g ∉ Q.comap (algebraMap R C) := by
        by_contra! H
        exact hQ (le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
          fun g hg ↦ H g hg)
      have : Algebra.FormallyEtale R (Localization.Away (algebraMap R C g)) :=
        formallyEtale_away_of_awayMap φ.hom g (hloc g hgm).2
      exact (Algebra.basicOpen_subset_etaleLocus_iff (R := R)).mpr this
        (show (⟨Q, ‹_›⟩ : PrimeSpectrum C) ∈ PrimeSpectrum.basicOpen (algebraMap R C g) from hgQ)
    have hC : Algebra.Etale R C :=
      IsRegularLocalRing.etale_of_isWeaklyRegular_of_two_le_ringKrullDim hdim hx hy hreg hregC hU
    have hfinite : IsFinite (Spec.map φ) := by
      rw [IsFinite.SpecMap_iff]; exact hfin
    have hetale : Etale (Spec.map φ) := by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]; exact hC
    let Y : MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ (Spec R) :=
      MorphismProperty.Over.mk ⊤ (Spec.map φ) ⟨hfinite, hetale⟩
    refine ⟨Y, ⟨MorphismProperty.Over.isoMk sq.isoPullback.symm ?_⟩⟩
    change sq.isoPullback.inv ≫ w = pullback.snd (Spec.map φ) (puncturedSpectrum R).ι
    rw [Iso.inv_comp_eq, sq.isoPullback_hom_snd]

/-- **Zariski–Nagata purity** for a regular local ring `R` of dimension `≥ 2` (Stacks 0BMB; SGA 2
X.3.4; SGA 1 X.3.3 for `X = Spec R`): base change to the punctured spectrum
`U = Spec R \ {𝔪}` is an equivalence from finite étale `Spec R`-schemes to finite étale
`U`-schemes. -/
theorem isEquivalence_pullback_puncturedSpectrum (hdim : 2 ≤ ringKrullDim R) :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤
      (puncturedSpectrum R).ι).IsEquivalence := by
  obtain ⟨x, y, hx, hy, hreg⟩ := IsRegularLocalRing.exists_isWeaklyRegular_pair hdim
  obtain ⟨hfull, hfaith⟩ := full_faithful_pullback_puncturedSpectrum hx hy hreg
    (@IsFinite ⊓ @Etale) fun f hf ↦ ⟨have := hf.1; inferInstance, have := hf.2; inferInstance⟩
  have := essSurj_pullback_puncturedSpectrum hdim
  exact { }

end Regular

end AlgebraicGeometry
