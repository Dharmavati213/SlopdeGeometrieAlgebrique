/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Projective.ProjectiveSpace

/-!
# Morphisms to `Proj` defined by sections of a line bundle

Let `L` be a line bundle on a scheme `X` and `A` an `ℕ`-graded ring. A homomorphism of graded
rings `φ : A → ⊕ₙ Γ(X, L^{⊗n})` whose image of `A₊` has no common zero defines a morphism
`X ⟶ Proj A`: on the open subset `X_{φ(t)}` (`t` homogeneous of positive degree) it is
`X_{φ(t)} ⟶ Spec A_(t) = D₊(t)`, given by `a / tⁿ ↦ φ(a) / φ(t)ⁿ` (EGA II 3.7.1, 3.7.4;
Stacks 01N8). In the cocycle model of `SGA.Foundations.Ample`, `φ` is a family of ring
homomorphisms `φₐ : A → Γ(Uₐ, 𝒪_X)` on the trivializing open subsets, such that for `P` homogeneous
of degree `d` the family `(φₐ P)ₐ` is a section of `L^{⊗d}` (`Scheme.LineBundle.GradedHom`).

## Main definitions and results

- `AlgebraicGeometry.Scheme.glueOpens`: gluing morphisms defined on the members of an open
  cover.
- `AlgebraicGeometry.Proj.chartHom`: the morphism `X_{ψ(t)} ⟶ D₊(t) ⊆ Proj A` defined by a ring
  homomorphism `ψ : A → Γ(U, 𝒪_X)`, with its compatibilities with restriction, twisting by
  units and change of `t`.
- `AlgebraicGeometry.Scheme.LineBundle.GradedHom.toProj`: the morphism `X ⟶ Proj A` defined by
  a graded homomorphism `A → ⊕ₙ Γ(X, L^{⊗n})` without base points, and
  `GradedHom.toProj_preimage_basicOpen`: the inverse image of `D₊(t)` is the non-vanishing
  locus of the section `φ(t)`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite HomogeneousLocalization

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms defined on the members of an open cover of `X` that agree on the pairwise
intersections glue to a morphism on `X`. -/
noncomputable def glueOpens {J : Type*} (W : J → X.Opens) (hW : IsOpenCover W)
    (g : ∀ j, (W j).toScheme ⟶ Y)
    (hg : ∀ j k, X.homOfLE (inf_le_left : W j ⊓ W k ≤ W j) ≫ g j =
      X.homOfLE inf_le_right ≫ g k) : X ⟶ Y :=
  (X.openCoverOfIsOpenCover W hW).glueMorphisms g fun j k ↦ by
    change pullback.fst (W j).ι (W k).ι ≫ g j = pullback.snd (W j).ι (W k).ι ≫ g k
    rw [← cancel_epi (isPullback_opens_inf (W j) (W k)).isoPullback.hom]
    simpa using hg j k

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ι_glueOpens {J : Type*} (W : J → X.Opens) (hW : IsOpenCover W)
    (g : ∀ j, (W j).toScheme ⟶ Y)
    (hg : ∀ j k, X.homOfLE (inf_le_left : W j ⊓ W k ≤ W j) ≫ g j =
      X.homOfLE inf_le_right ≫ g k) (j : J) :
    (W j).ι ≫ glueOpens W hW g hg = g j :=
  (X.openCoverOfIsOpenCover W hW).ι_glueMorphisms _ _ j

/-- Two restrictions of a section to the same open subset agree. -/
lemma presheaf_map_map_apply {U V W : X.Opens} (i : U ⟶ V) (j : W ⟶ U) (k : W ⟶ V)
    (s : Γ(X, V)) : X.presheaf.map j.op (X.presheaf.map i.op s) = X.presheaf.map k.op s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end Scheme

namespace Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜] {X : Scheme.{u}}

section chart

variable {U : X.Opens} (ψ : A →+* Γ(X, U))

/-- The composite of `ψ : A → Γ(X, U)` with the restriction to `X_{ψ(t)}`. -/
noncomputable def resBasicOpen (t : A) : A →+* Γ(X, X.basicOpen (ψ t)) :=
  (X.presheaf.map (homOfLE (X.basicOpen_le (ψ t))).op).hom.comp ψ

lemma isUnit_resBasicOpen (t : A) : IsUnit (resBasicOpen ψ t t) :=
  X.toRingedSpace.isUnit_res_basicOpen (ψ t)

lemma resBasicOpen_apply (t a : A) :
    resBasicOpen ψ t a = X.presheaf.map (homOfLE (X.basicOpen_le (ψ t))).op (ψ a) :=
  rfl

/-- The ring homomorphism `A_(t) ⟶ Γ(X_{ψ(t)}, 𝒪_X)`, `a / tⁿ ↦ ψ(a) / ψ(t)ⁿ`, defined by a ring
homomorphism `ψ : A → Γ(U, 𝒪_X)`. -/
noncomputable def awayToSections (t : A) : Away 𝒜 t →+* Γ(X, X.basicOpen (ψ t)) :=
  (IsLocalization.Away.lift (S := Localization.Away t) t (isUnit_resBasicOpen ψ t)).comp
    (algebraMap (Away 𝒜 t) (Localization.Away t))

variable {𝒜}

lemma awayToSections_mk {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayToSections 𝒜 ψ t (Away.mk 𝒜 ht n a ha) * resBasicOpen ψ t t ^ n =
      resBasicOpen ψ t a := by
  change (IsLocalization.Away.lift (S := Localization.Away t) t (isUnit_resBasicOpen ψ t))
    (Away.mk 𝒜 ht n a ha).val * _ = _
  rw [Away.val_mk, Localization.mk_eq_mk', mul_comm, ← map_pow]
  exact ((IsLocalization.lift_mk'_spec (M := Submonoid.powers t) (S := Localization.Away t)
    _ a _ ⟨t ^ n, n, rfl⟩).mp rfl).symm

/-- The morphism `X_{ψ(t)} ⟶ D₊(t) ⊆ Proj A` defined by a ring homomorphism
`ψ : A → Γ(U, 𝒪_X)`, for `t` homogeneous of positive degree. -/
noncomputable def chartHom {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) (hd : 0 < d) :
    (X.basicOpen (ψ t)).toScheme ⟶ Proj 𝒜 :=
  (X.basicOpen (ψ t)).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (awayToSections 𝒜 ψ t)) ≫
    awayι 𝒜 t ht hd

/-- `chartHom` does not depend on the degree used to define it. -/
lemma chartHom_congr {t : A} {d d' : ℕ} (ht : t ∈ 𝒜 d) (hd : 0 < d) (ht' : t ∈ 𝒜 d')
    (hd' : 0 < d') : chartHom ψ ht hd = chartHom ψ ht' hd' :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The charts are compatible with restriction and with twisting by a unit: if `ψ'` agrees on
homogeneous elements of degree `m` with `uᵐ ψ` on `X_{ψ'(t)} ⊆ X_{ψ(t)}`, then the two charts agree
there. -/
lemma homOfLE_chartHom {V : X.Opens} (ψ' : A →+* Γ(X, V)) {t : A} {d : ℕ} (ht : t ∈ 𝒜 d)
    (hd : 0 < d) (h : X.basicOpen (ψ' t) ≤ X.basicOpen (ψ t))
    (u : Γ(X, X.basicOpen (ψ' t))ˣ)
    (hu : ∀ (m : ℕ) (P : A), P ∈ 𝒜 m →
      resBasicOpen ψ' t P =
        (u : Γ(X, _)) ^ m * X.presheaf.map (homOfLE h).op (resBasicOpen ψ t P)) :
    X.homOfLE h ≫ chartHom ψ ht hd = chartHom ψ' ht hd := by
  simp only [chartHom, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp_assoc]
  congr 2
  congr 1
  ext x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 ht x
  apply ((isUnit_resBasicOpen ψ' t).pow n).mul_left_injective
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  rw [awayToSections_mk, hu _ _ ha, hu _ _ ht, ← awayToSections_mk ψ ht n a ha, map_mul, map_pow,
    smul_eq_mul]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma map_resBasicOpen {t x : A} (h : X.basicOpen (ψ x) ≤ X.basicOpen (ψ t)) (a : A) :
    X.presheaf.map (homOfLE h).op (resBasicOpen ψ t a) = resBasicOpen ψ x a := by
  simp only [resBasicOpen, RingHom.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma basicOpen_mul_le {t t' : A} : X.basicOpen (ψ (t * t')) ≤ X.basicOpen (ψ t) := by
  rw [map_mul, Scheme.basicOpen_mul]
  exact inf_le_left

set_option backward.isDefEq.respectTransparency false in
/-- The chart at `t` restricted to `X_{ψ(tt')}` is the chart at `tt'`. -/
lemma homOfLE_chartHom_mul {t t' : A} {d d' : ℕ} (ht : t ∈ 𝒜 d) (ht' : t' ∈ 𝒜 d') (hd : 0 < d) :
    X.homOfLE (basicOpen_mul_le ψ) ≫ chartHom ψ ht hd =
      chartHom ψ (SetLike.mul_mem_graded ht ht') (hd.trans_le (d.le_add_right d')) := by
  simp only [chartHom, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp_assoc,
    ← SpecMap_awayMap_awayι 𝒜 ht hd ht' rfl]
  congr 2
  congr 1
  ext x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 ht x
  apply ((isUnit_resBasicOpen ψ (t * t')).pow n).mul_left_injective
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    awayMap_mk]
  have e1 : resBasicOpen ψ (t * t') (a * t' ^ n) =
      X.presheaf.map (homOfLE (basicOpen_mul_le ψ (t := t) (t' := t'))).op
        (awayToSections 𝒜 ψ t (Away.mk 𝒜 ht n a ha) * resBasicOpen ψ t t ^ n *
          resBasicOpen ψ t t' ^ n) := by
    rw [awayToSections_mk, ← map_pow, ← map_mul, map_resBasicOpen]
  rw [awayToSections_mk, e1, ← map_resBasicOpen ψ (basicOpen_mul_le ψ) (t * t'),
    map_mul (resBasicOpen ψ t) t t']
  simp only [map_mul, map_pow, mul_pow]
  ring

/-- `homOfLE_chartHom_mul` for an element `x` equal to `t * t'`. -/
lemma homOfLE_chartHom_mul' {t t' x : A} {d d' : ℕ} (ht : t ∈ 𝒜 d) (ht' : t' ∈ 𝒜 d')
    (hd : 0 < d) (hx : x = t * t') (h : X.basicOpen (ψ x) ≤ X.basicOpen (ψ t)) :
    X.homOfLE h ≫ chartHom ψ ht hd =
      chartHom ψ (hx ▸ SetLike.mul_mem_graded ht ht') (hd.trans_le (d.le_add_right d')) := by
  subst hx
  exact homOfLE_chartHom_mul ψ ht ht' hd

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of `D₊(t)` under the chart at `s` is `X_{ψ(s)} ∩ X_{ψ(t)}`. -/
lemma chartHom_preimage_basicOpen {s t : A} {d e : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d)
    (ht : t ∈ 𝒜 e) (he : 0 < e) :
    chartHom ψ hs hd ⁻¹ᵁ Proj.basicOpen 𝒜 t =
      (X.basicOpen (ψ s)).ι ⁻¹ᵁ X.basicOpen (ψ t) := by
  have key : X.basicOpen (awayToSections 𝒜 ψ s (Away.isLocalizationElem hs ht)) =
      X.basicOpen (ψ s) ⊓ X.basicOpen (ψ t) := by
    have hu := (isUnit_resBasicOpen ψ s).pow e
    have := congrArg X.basicOpen (awayToSections_mk ψ hs e (t ^ d)
      (by simpa [smul_eq_mul, mul_comm] using SetLike.pow_mem_graded d ht))
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit X hu, map_pow,
      Scheme.basicOpen_pow _ _ hd, resBasicOpen_apply, Scheme.basicOpen_res] at this
    rwa [inf_eq_left.mpr (X.basicOpen_le _)] at this
  rw [chartHom, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    awayι_preimage_basicOpen 𝒜 hs hd ht he, SpecMap_preimage_basicOpen,
    Scheme.Opens.toSpecΓ_preimage_basicOpen]
  change (X.basicOpen (ψ s)).ι ⁻¹ᵁ
    X.basicOpen (awayToSections 𝒜 ψ s (Away.isLocalizationElem hs ht)) = _
  rw [key, Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]

end chart

end Proj

namespace Scheme.LineBundle

variable {X : Scheme.{u}} (L : X.LineBundle) {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A homomorphism of graded rings from `A` to the ring `⊕ₙ Γ(X, L^{⊗n})` of sections of the
powers of `L`, in the cocycle model: ring homomorphisms `φₐ : A → Γ(Uₐ, 𝒪_X)` on the
trivializing open subsets such that, for `P` homogeneous of degree `d`, `φₐ(P) = gₐᵦᵈ φᵦ(P)` on
`Uₐ ∩ Uᵦ`, i.e. `(φₐ(P))ₐ` is a section of `L^{⊗d}`. -/
structure GradedHom where
  /-- The homomorphism on the trivializing open subset `Uₐ`. -/
  app : ∀ a : L.ι, A →+* Γ(X, L.U a)
  app_mem : ∀ (a b : L.ι) (d : ℕ) (P : A), P ∈ 𝒜 d →
    X.presheaf.map (homOfLE (inf_le_left : L.U a ⊓ L.U b ≤ L.U a)).op (app a P) =
      (L.g a b : Γ(X, L.U a ⊓ L.U b)) ^ d *
        X.presheaf.map (homOfLE (inf_le_right : L.U a ⊓ L.U b ≤ L.U b)).op (app b P)

namespace GradedHom

variable {L 𝒜} (φ : L.GradedHom 𝒜)

/-- The section of `L^{⊗d}` image of a homogeneous element of degree `d`. -/
def sec {d : ℕ} {P : A} (hP : P ∈ 𝒜 d) : L.sections d :=
  ⟨fun a ↦ φ.app a P, fun a b ↦ φ.app_mem a b d P hP⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
@[simp]
lemma sec_apply {d : ℕ} {P : A} (hP : P ∈ 𝒜 d) (a : L.ι) : (φ.sec hP).1 a = φ.app a P :=
  rfl

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
set_option backward.isDefEq.respectTransparency false in
/-- On `Uₐ ∩ Uᵦ`, `φₐ(P)` and `φᵦ(P)` differ by a unit. -/
lemma inf_basicOpen_app (a b : L.ι) {d : ℕ} {P : A} (hP : P ∈ 𝒜 d) :
    L.U a ⊓ L.U b ⊓ X.basicOpen (φ.app a P) = L.U a ⊓ L.U b ⊓ X.basicOpen (φ.app b P) := by
  have h := congrArg X.basicOpen (φ.app_mem a b d P hP)
  rwa [Scheme.basicOpen_mul, Scheme.basicOpen_res, Scheme.basicOpen_res,
    Scheme.basicOpen_of_isUnit X ((L.g a b).isUnit.pow d), ← inf_assoc, inf_idem] at h

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
lemma mem_nonvanishingLocus_sec_iff {d : ℕ} {P : A} (hP : P ∈ 𝒜 d) {a : L.ι} {x : X}
    (hx : x ∈ L.U a) : x ∈ L.nonvanishingLocus (φ.sec hP) ↔ x ∈ X.basicOpen (φ.app a P) := by
  refine ⟨fun h ↦ ?_, fun h ↦ (L.mem_nonvanishingLocus _).mpr ⟨a, h⟩⟩
  obtain ⟨b, hb⟩ := (L.mem_nonvanishingLocus _).mp h
  have hxb : x ∈ L.U b := X.basicOpen_le _ hb
  have : x ∈ L.U a ⊓ L.U b ⊓ X.basicOpen (φ.app b P) := ⟨⟨hx, hxb⟩, hb⟩
  rw [← φ.inf_basicOpen_app a b hP] at this
  exact this.2

/-- The index type of the charts of `GradedHom.toProj`: pairs of a trivializing open subset `Uₐ`
and a homogeneous element `t` of positive degree. -/
def ChartIndex : Type u :=
  Σ' (_ : L.ι) (d : ℕ) (t : A), 0 < d ∧ t ∈ 𝒜 d

/-- The open subset `X_{φₐ(t)}` of a chart. -/
def chartOpen (j : ChartIndex (L := L) (𝒜 := 𝒜)) : X.Opens :=
  X.basicOpen (φ.app j.1 j.2.2.1)

/-- The chart `X_{φₐ(t)} ⟶ D₊(t)` of `GradedHom.toProj`. -/
noncomputable def chart (j : ChartIndex (L := L) (𝒜 := 𝒜)) :
    (φ.chartOpen j).toScheme ⟶ Proj 𝒜 :=
  Proj.chartHom (φ.app j.1) j.2.2.2.2 j.2.2.2.1

set_option backward.isDefEq.respectTransparency false in
lemma chart_compat_aux (a b : L.ι) {d : ℕ} {x : A} (hx : x ∈ 𝒜 d) (hd : 0 < d)
    (Y : X.Opens) (hYa : Y ≤ X.basicOpen (φ.app a x)) (hYb : Y ≤ X.basicOpen (φ.app b x))
    (hY : Y ≤ L.U a ⊓ L.U b) :
    X.homOfLE hYa ≫ Proj.chartHom (φ.app a) hx hd =
      X.homOfLE hYb ≫ Proj.chartHom (φ.app b) hx hd := by
  let V := L.U a ⊓ L.U b
  let ψ : A →+* Γ(X, V) :=
    (X.presheaf.map (homOfLE (inf_le_right : L.U a ⊓ L.U b ≤ L.U b)).op).hom.comp (φ.app b)
  have hψ : X.basicOpen (ψ x) = V ⊓ X.basicOpen (φ.app b x) := Scheme.basicOpen_res _ _ _
  have h1 : X.basicOpen (ψ x) ≤ X.basicOpen (φ.app b x) := hψ.trans_le inf_le_right
  have h2 : X.basicOpen (ψ x) ≤ X.basicOpen (φ.app a x) := by
    rw [hψ, ← φ.inf_basicOpen_app a b hx]
    exact inf_le_right
  have hY' : Y ≤ X.basicOpen (ψ x) := hψ ▸ le_inf hY hYb
  have hVb : X.basicOpen (ψ x) ≤ V := X.basicOpen_le _
  have e1 : X.homOfLE h1 ≫ Proj.chartHom (φ.app b) hx hd = Proj.chartHom ψ hx hd := by
    refine Proj.homOfLE_chartHom _ _ hx hd h1 1 fun m P _ ↦ ?_
    rw [Units.val_one, one_pow, one_mul]
    exact (X.presheaf_map_map_apply _ _ (homOfLE (h1.trans (X.basicOpen_le _))) _).trans
      (X.presheaf_map_map_apply _ _ _ _).symm
  let u : Γ(X, X.basicOpen (ψ x))ˣ :=
    Units.map (X.presheaf.map (homOfLE hVb).op).hom (L.g a b)⁻¹
  have e2 : X.homOfLE h2 ≫ Proj.chartHom (φ.app a) hx hd = Proj.chartHom ψ hx hd := by
    refine Proj.homOfLE_chartHom _ _ hx hd h2 u fun m P hP ↦ ?_
    have := congrArg (X.presheaf.map (homOfLE hVb).op).hom (φ.app_mem a b m P hP)
    have hb' : Proj.resBasicOpen ψ x P = X.presheaf.map (homOfLE hVb).op
        (X.presheaf.map (homOfLE (inf_le_right : L.U a ⊓ L.U b ≤ L.U b)).op (φ.app b P)) :=
      rfl
    have ha' : X.presheaf.map (homOfLE h2).op (Proj.resBasicOpen (φ.app a) x P) =
        X.presheaf.map (homOfLE hVb).op
          (X.presheaf.map (homOfLE (inf_le_left : L.U a ⊓ L.U b ≤ L.U a)).op (φ.app a P)) :=
      (X.presheaf_map_map_apply _ _ (homOfLE (h2.trans (X.basicOpen_le _))) _).trans
        (X.presheaf_map_map_apply _ _ _ _).symm
    rw [hb', ha', this, map_mul, map_pow, ← mul_assoc, ← mul_pow]
    simp only [u, Units.coe_map, MonoidHom.coe_coe]
    rw [← map_mul, Units.inv_mul, map_one, one_pow, one_mul]
  rw [← X.homOfLE_homOfLE hY' h2, Category.assoc, e2, ← e1, ← Category.assoc,
    X.homOfLE_homOfLE]

set_option backward.isDefEq.respectTransparency false in
lemma chart_compat (j k : ChartIndex (L := L) (𝒜 := 𝒜)) :
    X.homOfLE (inf_le_left : φ.chartOpen j ⊓ φ.chartOpen k ≤ φ.chartOpen j) ≫ φ.chart j =
      X.homOfLE inf_le_right ≫ φ.chart k := by
  obtain ⟨a, d, t, hd, ht⟩ := j
  obtain ⟨b, e, s, he, hs⟩ := k
  change X.homOfLE (inf_le_left : X.basicOpen (φ.app a t) ⊓ X.basicOpen (φ.app b s) ≤ _) ≫
      Proj.chartHom (φ.app a) ht hd = X.homOfLE inf_le_right ≫ Proj.chartHom (φ.app b) hs he
  have hY : X.basicOpen (φ.app a t) ⊓ X.basicOpen (φ.app b s) ≤ L.U a ⊓ L.U b :=
    inf_le_inf (X.basicOpen_le _) (X.basicOpen_le _)
  have hYas : X.basicOpen (φ.app a t) ⊓ X.basicOpen (φ.app b s) ≤ X.basicOpen (φ.app a s) := by
    have := le_inf hY (inf_le_right : X.basicOpen (φ.app a t) ⊓ X.basicOpen (φ.app b s) ≤ _)
    rw [← φ.inf_basicOpen_app a b hs] at this
    exact this.trans inf_le_right
  have hYbt : X.basicOpen (φ.app a t) ⊓ X.basicOpen (φ.app b s) ≤ X.basicOpen (φ.app b t) := by
    have := le_inf hY (inf_le_left : X.basicOpen (φ.app a t) ⊓ X.basicOpen (φ.app b s) ≤ _)
    rw [φ.inf_basicOpen_app a b ht] at this
    exact this.trans inf_le_right
  have hYa : X.basicOpen (φ.app a t) ⊓ X.basicOpen (φ.app b s) ≤
      X.basicOpen (φ.app a (t * s)) := by
    rw [map_mul, Scheme.basicOpen_mul]
    exact le_inf inf_le_left hYas
  have hYb : X.basicOpen (φ.app a t) ⊓ X.basicOpen (φ.app b s) ≤
      X.basicOpen (φ.app b (t * s)) := by
    rw [map_mul, Scheme.basicOpen_mul]
    exact le_inf hYbt inf_le_right
  have hbs : X.basicOpen (φ.app b (t * s)) ≤ X.basicOpen (φ.app b s) := by
    rw [map_mul, Scheme.basicOpen_mul]
    exact inf_le_right
  rw [← X.homOfLE_homOfLE hYa (Proj.basicOpen_mul_le _), Category.assoc,
    Proj.homOfLE_chartHom_mul (φ.app a) ht hs hd, ← X.homOfLE_homOfLE hYb hbs, Category.assoc,
    Proj.homOfLE_chartHom_mul' (φ.app b) hs ht he (mul_comm t s)]
  exact φ.chart_compat_aux a b _ _ _ hYa hYb hY

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
lemma iSup_chartOpen (hφ : ∀ x : X, ∃ (d : ℕ) (t : A) (_ : 0 < d) (ht : t ∈ 𝒜 d),
      x ∈ L.nonvanishingLocus (φ.sec ht)) :
    ⨆ j, φ.chartOpen j = ⊤ := by
  refine top_le_iff.mp fun x _ ↦ ?_
  obtain ⟨d, t, hd, ht, hx⟩ := hφ x
  obtain ⟨a, ha⟩ := (L.mem_nonvanishingLocus _).mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, d, t, hd, ht⟩, ha⟩

/-- EGA II 3.7.1, Stacks 01N8: the morphism `X ⟶ Proj A` defined by a graded homomorphism
`φ : A → ⊕ₙ Γ(X, L^{⊗n})` such that the non-vanishing loci of the sections `φ(t)`, `t`
homogeneous of positive degree, cover `X`. On `X_{φ(t)}` it is `X_{φ(t)} ⟶ Spec A_(t) = D₊(t)`,
`a / tⁿ ↦ φ(a) / φ(t)ⁿ`. -/
noncomputable def toProj (hφ : ∀ x : X, ∃ (d : ℕ) (t : A) (_ : 0 < d) (ht : t ∈ 𝒜 d),
      x ∈ L.nonvanishingLocus (φ.sec ht)) : X ⟶ Proj 𝒜 :=
  Scheme.glueOpens φ.chartOpen (φ.iSup_chartOpen hφ) φ.chart φ.chart_compat

variable (hφ : ∀ x : X, ∃ (d : ℕ) (t : A) (_ : 0 < d) (ht : t ∈ 𝒜 d),
  x ∈ L.nonvanishingLocus (φ.sec ht))

@[reassoc (attr := simp)]
lemma ι_toProj (j : ChartIndex (L := L) (𝒜 := 𝒜)) :
    (φ.chartOpen j).ι ≫ φ.toProj hφ = φ.chart j :=
  Scheme.ι_glueOpens _ _ _ _ j

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of `D₊(t)` under `φ.toProj` is the non-vanishing locus of `φ(t)`
(EGA II 3.7.3). -/
lemma toProj_preimage_basicOpen {d : ℕ} {t : A} (ht : t ∈ 𝒜 d) (hd : 0 < d) :
    φ.toProj hφ ⁻¹ᵁ Proj.basicOpen 𝒜 t = L.nonvanishingLocus (φ.sec ht) := by
  ext x
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((φ.iSup_chartOpen hφ).ge (Set.mem_univ x))
  have h1 : x ∈ φ.toProj hφ ⁻¹ᵁ Proj.basicOpen 𝒜 t ↔
      (⟨x, hj⟩ : φ.chartOpen j) ∈ (φ.chartOpen j).ι ⁻¹ᵁ X.basicOpen (φ.app j.1 t) := by
    change _ ↔ _ ∈ (X.basicOpen (φ.app j.1 j.2.2.1)).ι ⁻¹ᵁ _
    rw [← Proj.chartHom_preimage_basicOpen (φ.app j.1) j.2.2.2.2 j.2.2.2.1 ht hd]
    change _ ↔ (⟨x, hj⟩ : φ.chartOpen j) ∈ φ.chart j ⁻¹ᵁ _
    rw [← φ.ι_toProj hφ, Scheme.Hom.comp_preimage]
    rfl
  refine h1.trans ?_
  exact (φ.mem_nonvanishingLocus_sec_iff ht (X.basicOpen_le _ hj)).symm

end GradedHom

end Scheme.LineBundle

end AlgebraicGeometry
