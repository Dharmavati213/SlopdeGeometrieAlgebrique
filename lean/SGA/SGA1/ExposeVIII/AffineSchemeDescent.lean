/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import SGA.SGA1.ExposeVIII.AffineDescent

/-!
# SGA 1, Exposé VIII, VIII.2.1 for affine schemes, with descent data as equivalence pairs

In §7 SGA describes a descent datum on `X' → S'` relative to `g : S' → S` as an equivalence pair
`q₁, q₂ : X'' ⇉ X'` over `p₁, p₂ : S' ×_S S' ⇉ S'` with both squares cartesian; it is effective
if there is a cartesian square `X' → X` over `g` with `h ∘ q₁ = h ∘ q₂`. This is the form used
in `SGA.SGA1.ExposeVIII.Effectiveness` (`DescentDatum`, `IsEffectiveOfIsAffineHomStatement`).

Here VIII.2.1 is proved in that form when `S` is affine:

* `exists_isPullback_of_isAffineHom`, for `S` and `S'` affine: taking global sections turns the
  descent datum into rings `A → B → C`, `R = Γ(X'')`, the cartesian squares into pushouts, and
  the reflexivity and transitivity of the equivalence pair into the counit and cocycle
  conditions of an algebra descent datum (`isPushout_eqLocus_of_descent`); the descended scheme
  is the spectrum of the equalizer of `q₁^♯, q₂^♯ : C ⇉ R`, by VIII.1.6.
* `exists_isPullback_of_isAffineHom_of_isAffine`, for `S` affine and `S'` arbitrary: reduction to
  the previous case through an affine `S₁ → S'` covering `S'`, as in the proof of VIII.1.1.

The last reduction of SGA, from an arbitrary base `S` to affine ones, glues the descended
schemes over an affine open cover of `S`; it is done in `Effectiveness`
(`DescentDatum.isEffective_of_isAffineHom`), and VIII.2.1 for arbitrary `S` in the form of this
file is `exists_isPullback_of_isAffineHom_of_flat` (`AffineHomDescent`).
-/

universe u

open CategoryTheory Limits TensorProduct

namespace SGA.SGA1.ExposeVIII

variable {A B C P R Q : CommRingCat.{u}}

section

variable (gA : A ⟶ B) (a : B ⟶ C) (p₁ p₂ : B ⟶ P) (b : P ⟶ R) (q₁ q₂ : C ⟶ R)
  (hP : IsPushout gA gA p₁ p₂) (w₁ : a ≫ q₁ = p₁ ≫ b) (h₂ : IsPushout a p₂ q₂ b)

include hP w₁ h₂ in
lemma comp_mem_eqLocus (x : A) : (gA ≫ a).hom x ∈ q₁.hom.eqLocus q₂.hom := by
  change (gA ≫ a ≫ q₁).hom x = (gA ≫ a ≫ q₂).hom x
  rw [w₁, h₂.w, ← Category.assoc, hP.w, Category.assoc]

end

/-- VIII.2.1 over an affine base, ring form. Let `A → B` be faithfully flat, `P = B ⊗_A B` (a
pushout), `C` a `B`-algebra and `R` with `q₁, q₂ : C → R` and `b : P → R` such that the square
`(a, p₂, q₂, b)` is a pushout and `(a, p₁, q₁, b)` commutes (the global sections of a descent
datum in the form of VIII.7 with affine `X'`). Given a common retraction `δ` of `q₁, q₂`
(reflexivity) and a map `τ` to the pushout of `(q₂, q₁)` as below (transitivity), the equalizer
`C₀ = {x | q₁ x = q₂ x}` satisfies `C ≅ B ⊗_A C₀`, i.e. the square `A → B → C`, `A → C₀ → C` is
a pushout. -/
theorem isPushout_eqLocus_of_descent (gA : A ⟶ B) (hg : gA.hom.FaithfullyFlat) (a : B ⟶ C)
    (p₁ p₂ : B ⟶ P) (hP : IsPushout gA gA p₁ p₂) (b : P ⟶ R) (q₁ q₂ : C ⟶ R)
    (w₁ : a ≫ q₁ = p₁ ≫ b) (h₂ : IsPushout a p₂ q₂ b) (δ : R ⟶ C) (hδ₁ : q₁ ≫ δ = 𝟙 C)
    (hδ₂ : q₂ ≫ δ = 𝟙 C) (inl inr : R ⟶ Q) (hQ : IsPushout q₂ q₁ inl inr) (τ : R ⟶ Q)
    (hτ₁ : q₁ ≫ τ = q₁ ≫ inl) (hτ₂ : q₂ ≫ τ = q₂ ≫ inr) :
    IsPushout gA (CommRingCat.ofHom ((gA ≫ a).hom.codRestrict _
        (comp_mem_eqLocus gA a p₁ p₂ b q₁ q₂ hP w₁ h₂)))
      a (CommRingCat.ofHom (q₁.hom.eqLocus q₂.hom).subtype) := by
  have hw₁ (c : B) : q₁ (a c) = b (p₁ c) := by simpa using congr($w₁ c)
  have hδ₁' (x : C) : δ (q₁ x) = x := by simpa using congr($hδ₁ x)
  have hδ₂' (x : C) : δ (q₂ x) = x := by simpa using congr($hδ₂ x)
  have hτ₁' (x : C) : τ (q₁ x) = inl (q₁ x) := by simpa using congr($hτ₁ x)
  have hτ₂' (x : C) : τ (q₂ x) = inr (q₂ x) := by simpa using congr($hτ₂ x)
  let : Algebra A B := gA.hom.toAlgebra
  let : Algebra B C := a.hom.toAlgebra
  let : Algebra A C := (gA ≫ a).hom.toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.FaithfullyFlat A B := hg
  have hpaste : IsPushout (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap A C)) (p₁ ≫ b) q₂ := (hP.flip.paste_horiz h₂).flip
  let σ := (CommRingCat.isPushout_tensorProduct A B C).isoIsPushout _ _ hpaste
  have hσl (c : B) : σ.hom (c ⊗ₜ 1) = b (p₁ c) :=
    congr($((CommRingCat.isPushout_tensorProduct A B C).inl_isoIsPushout_hom _ _ hpaste) c)
  have hσr (x : C) : σ.hom (1 ⊗ₜ x) = q₂ x :=
    congr($((CommRingCat.isPushout_tensorProduct A B C).inr_isoIsPushout_hom _ _ hpaste) x)
  have hσinvl (c : B) : σ.inv (b (p₁ c)) = c ⊗ₜ 1 :=
    congr($((CommRingCat.isPushout_tensorProduct A B C).inl_isoIsPushout_inv _ _ hpaste) c)
  have hσinvr (x : C) : σ.inv (q₂ x) = 1 ⊗ₜ x :=
    congr($((CommRingCat.isPushout_tensorProduct A B C).inr_isoIsPushout_inv _ _ hpaste) x)
  -- the coaction `θ = σ⁻¹ ∘ q₁`
  let θ : C →ₐ[B] B ⊗[A] C :=
    { (q₁ ≫ σ.inv).hom with
      commutes' := fun c ↦ by
        change σ.inv (q₁ (a c)) = c ⊗ₜ 1
        rw [hw₁, hσinvl] }
  have hθ (x : C) : θ x = σ.inv (q₁ x) := rfl
  -- the counit condition, from the diagonal `δ`
  have hact (y : B ⊗[A] C) : LinearMap.liftBaseChange B LinearMap.id y = δ (σ.hom y) := by
    induction y with
    | zero => simp
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
    | tmul c x =>
      have : c ⊗ₜ[A] x = (c ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] x) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [LinearMap.liftBaseChange_tmul, LinearMap.id_apply, this, map_mul, map_mul, hσl, hσr,
        ← hw₁, hδ₁', hδ₂', Algebra.smul_def]
      rfl
  -- the cocycle condition, from the transitivity `τ`
  let mapθ : B ⊗[A] C →ₐ[A] B ⊗[A] (B ⊗[A] C) :=
    Algebra.TensorProduct.map (AlgHom.id A B) (θ.restrictScalars A)
  let incR : B ⊗[A] C →ₐ[A] B ⊗[A] (B ⊗[A] C) := Algebra.TensorProduct.includeRight
  let L : R ⟶ CommRingCat.of (B ⊗[A] (B ⊗[A] C)) := σ.inv ≫ CommRingCat.ofHom mapθ.toRingHom
  let Rr : R ⟶ CommRingCat.of (B ⊗[A] (B ⊗[A] C)) := σ.inv ≫ CommRingCat.ofHom incR.toRingHom
  have hcompat : q₂ ≫ L = q₁ ≫ Rr := by
    ext x
    change mapθ (σ.inv (q₂ x)) = incR (σ.inv (q₁ x))
    rw [hσinvr, ← hθ]
    simp [mapθ, incR]
  let Λ := hQ.desc L Rr hcompat
  have hΛl (z : R) : Λ (inl z) = mapθ (σ.inv z) := congr($(hQ.inl_desc L Rr hcompat) z)
  have hΛr (z : R) : Λ (inr z) = incR (σ.inv z) := congr($(hQ.inr_desc L Rr hcompat) z)
  have hσσ (z : R) : σ.hom (σ.inv z) = z := σ.inv_hom_id_apply z
  have hkey (y : B ⊗[A] C) : Λ (τ (σ.hom y)) = (TensorProduct.mk A B C 1).lTensor B y := by
    induction y with
    | zero => simp
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz, map_add]
    | tmul c x =>
      have : c ⊗ₜ[A] x = (c ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] x) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this, map_mul, map_mul, map_mul, hσl, hσr, ← hw₁, hτ₁', hτ₂', hΛl, hΛr, hσinvr,
        ← hθ]
      have hθc : θ (a c) = c ⊗ₜ 1 := θ.commutes c
      rw [hθc]
      simp [mapθ, incR]
  have hlT (y : B ⊗[A] C) : (θ.toLinearMap.restrictScalars A).lTensor B y = mapθ y := by
    induction y with
    | zero => simp
    | add y z hy hz => rw [map_add, map_add, hy, hz]
    | tmul c x => simp [mapθ]
  let D : AlgebraDescentDatum A B C :=
    { coaction := θ.toLinearMap
      coaction_one := map_one θ
      coaction_mul := map_mul θ
      counit x := by
        change LinearMap.liftBaseChange B LinearMap.id (θ x) = x
        rw [hact, hθ, hσσ, hδ₁']
      coassoc x := by
        change (θ.toLinearMap.restrictScalars A).lTensor B (θ x) =
          (TensorProduct.mk A B C 1).lTensor B (θ x)
        rw [hlT, ← hkey, hθ, hσσ, hτ₁', hΛl] }
  -- the invariants are the equalizer of `q₁` and `q₂`
  have hinv (x : C) : x ∈ D.invariantsSubalgebra ↔ x ∈ q₁.hom.eqLocus q₂.hom := by
    change θ x = 1 ⊗ₜ x ↔ q₁ x = q₂ x
    rw [hθ, ← hσinvr]
    exact σ.commRingCatIsoToRingEquiv.symm.injective.eq_iff
  let e₀ : D.invariantsSubalgebra ≃+* q₁.hom.eqLocus q₂.hom :=
    { toFun x := ⟨x.1, (hinv x.1).1 x.2⟩
      invFun y := ⟨y.1, (hinv y.1).2 y.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl }
  refine (CommRingCat.isPushout_tensorProduct A B D.invariantsSubalgebra).of_iso (Iso.refl _)
    (Iso.refl _) e₀.toCommRingCatIso D.descentAlgEquiv.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
  · rfl
  · ext x
    rfl
  · ext c
    change D.descentAlgHom (c ⊗ₜ 1) = a c
    rw [AlgebraDescentDatum.descentAlgHom_tmul]
    exact (Algebra.algebraMap_eq_smul_one c).symm
  · ext x
    change D.descentAlgHom (1 ⊗ₜ x) = (x : C)
    rw [AlgebraDescentDatum.descentAlgHom_tmul, one_smul]


open AlgebraicGeometry in
/-- VIII.2.1 for `S` and `S'` affine, with descent data as equivalence pairs (VIII.7): let
`g : S' → S` be faithfully flat and `q₁, q₂ : X'' ⇉ X'` an equivalence pair over
`p₁, p₂ : S' ×_S S' ⇉ S'` with both squares cartesian, where `X' → S'` is affine. Then the descent
datum is effective: there is a cartesian square `X' → X` over `g` with `h ∘ q₁ = h ∘ q₂`. Only
reflexivity and transitivity of the equivalence pair are used. The arguments are the fields of
`SGA.SGA1.ExposeVIII.DescentDatum`, so this proves `IsEffectiveOfIsAffineHomStatement` for
affine `S` and `S'`. -/
theorem exists_isPullback_of_isAffineHom {S S' : Scheme.{u}} (g : S' ⟶ S) [IsAffine S]
    [IsAffine S'] [Flat g] [Surjective g] {X' X'' : Scheme.{u}} (a : X' ⟶ S') [IsAffineHom a]
    (b : X'' ⟶ pullback g g) (q₁ q₂ : X'' ⟶ X')
    (h₁ : IsPullback q₁ b a (pullback.fst g g)) (h₂ : IsPullback q₂ b a (pullback.snd g g))
    (refl : ∀ ⦃T : Scheme.{u}⦄ (x : T ⟶ X'), ∃ r : T ⟶ X'', r ≫ q₁ = x ∧ r ≫ q₂ = x)
    (trans : ∀ ⦃T : Scheme.{u}⦄ (r r' : T ⟶ X''), r ≫ q₂ = r' ≫ q₁ →
      ∃ r'' : T ⟶ X'', r'' ≫ q₁ = r ≫ q₁ ∧ r'' ≫ q₂ = r' ≫ q₂) :
    ∃ (X : Scheme.{u}) (f : X ⟶ S) (h : X' ⟶ X), IsPullback h a f g ∧ q₁ ≫ h = q₂ ≫ h := by
  have : IsAffine X' := isAffine_of_isAffineHom a
  have : IsAffine X'' := IsAffine.of_isPullback h₁
  have hg : g.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp ⟨‹_›, ‹_›⟩
  have hP := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback g g)
  have w₁ : a.appTop ≫ q₁.appTop = (pullback.fst g g).appTop ≫ b.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h₁.w]
  have hR₂ := isPushout_appTop_of_isPullback h₂
  obtain ⟨r, hr₁, hr₂⟩ := refl (𝟙 X')
  have hδ₁ : q₁.appTop ≫ r.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hr₁]; rfl
  have hδ₂ : q₂.appTop ≫ r.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hr₂]; rfl
  obtain ⟨r'', hr''₁, hr''₂⟩ :=
    trans (pullback.fst q₂ q₁) (pullback.snd q₂ q₁) pullback.condition
  have hQ := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback q₂ q₁)
  have hτ₁ : q₁.appTop ≫ r''.appTop = q₁.appTop ≫ (pullback.fst q₂ q₁).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hr''₁]
  have hτ₂ : q₂.appTop ≫ r''.appTop = q₂.appTop ≫ (pullback.snd q₂ q₁).appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hr''₂]
  have hpush := isPushout_eqLocus_of_descent g.appTop hg a.appTop _ _ hP b.appTop q₁.appTop
    q₂.appTop w₁ hR₂ r.appTop hδ₁ hδ₂ _ _ hQ r''.appTop hτ₁ hτ₂
  refine ⟨_, Spec.map (CommRingCat.ofHom ((g.appTop ≫ a.appTop).hom.codRestrict _
      (comp_mem_eqLocus _ _ _ _ _ _ _ hP w₁ hR₂))) ≫ S.isoSpec.inv,
    X'.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (q₁.appTop.hom.eqLocus q₂.appTop.hom).subtype),
    ?_, ?_⟩
  · refine (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).flip.of_iso X'.isoSpec.symm
      (Iso.refl _) S'.isoSpec.symm S.isoSpec.symm ?_ ?_ ?_ ?_
    · simp
    · simp [Scheme.isoSpec_inv_naturality]
    · simp
    · simp [Scheme.isoSpec_inv_naturality]
  · rw [← Scheme.isoSpec_hom_naturality_assoc, ← Scheme.isoSpec_hom_naturality_assoc,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext x
    exact x.2

set_option backward.isDefEq.respectTransparency.types false in
open AlgebraicGeometry MorphismProperty in
/-- VIII.2.1 for affine `S`, with descent data as equivalence pairs (VIII.7): for `S` affine and
`g : S' → S` faithfully flat and quasi-compact, every descent datum on an affine `X' → S'` is
effective. As in SGA, one replaces `S'` by an affine `S₁` (a finite disjoint union of affine open
subsets of `S'`), applies `exists_isPullback_of_isAffineHom` to the pulled-back descent datum,
and descends the result along the fppf covering `S₁ → S'`. This proves
`IsEffectiveOfIsAffineHomStatement` for affine `S`. -/
theorem exists_isPullback_of_isAffineHom_of_isAffine {S S' : Scheme.{u}} (g : S' ⟶ S)
    [IsAffine S] [Flat g] [Surjective g] [QuasiCompact g] {X' X'' : Scheme.{u}} (a : X' ⟶ S')
    [IsAffineHom a] (b : X'' ⟶ pullback g g) (q₁ q₂ : X'' ⟶ X')
    (h₁ : IsPullback q₁ b a (pullback.fst g g)) (h₂ : IsPullback q₂ b a (pullback.snd g g))
    (refl : ∀ ⦃T : Scheme.{u}⦄ (x : T ⟶ X'), ∃ r : T ⟶ X'', r ≫ q₁ = x ∧ r ≫ q₂ = x)
    (trans : ∀ ⦃T : Scheme.{u}⦄ (r r' : T ⟶ X''), r ≫ q₂ = r' ≫ q₁ →
      ∃ r'' : T ⟶ X'', r'' ≫ q₁ = r ≫ q₁ ∧ r'' ≫ q₂ = r' ≫ q₂) :
    ∃ (X : Scheme.{u}) (f : X ⟶ S) (h : X' ⟶ X), IsPullback h a f g ∧ q₁ ≫ h = q₂ ≫ h := by
  have : CompactSpace S' := QuasiCompact.compactSpace_of_compactSpace g
  -- an affine scheme `S₁` with a surjective local isomorphism `π : S₁ ⟶ S'`
  obtain ⟨S₁, π, hπs, hπ, hS₁⟩ := S'.exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  have : Flat π := IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ π hπ
  have : ContainsIdentities @LocallyOfFinitePresentation := ⟨fun _ ↦ inferInstance⟩
  have : LocallyOfFinitePresentation π :=
    IsLocalIso.le_of_isZariskiLocalAtSource @LocallyOfFinitePresentation _ _ π hπ
  have : Surjective π := hπs
  -- the descent datum pulled back to `S₁`, relative to `g₁ = π ≫ g`
  let g₁ := π ≫ g
  have hX₁ : IsPullback (pullback.fst a π) (pullback.snd a π) a π := IsPullback.of_hasPullback a π
  let π'' : pullback g₁ g₁ ⟶ pullback g g :=
    pullback.map g₁ g₁ g g π π (𝟙 S) (by simp [g₁]) (by simp [g₁])
  have hπ''₁ : π'' ≫ pullback.fst g g = pullback.fst g₁ g₁ ≫ π := pullback.lift_fst _ _ _
  have hπ''₂ : π'' ≫ pullback.snd g g = pullback.snd g₁ g₁ ≫ π := pullback.lift_snd _ _ _
  have he'' : pullback.fst b π'' ≫ b = pullback.snd b π'' ≫ π'' := pullback.condition
  let q₁₁ : pullback b π'' ⟶ pullback a π :=
    pullback.lift (pullback.fst b π'' ≫ q₁) (pullback.snd b π'' ≫ pullback.fst g₁ g₁)
    (by simp only [Category.assoc]; rw [h₁.w, reassoc_of% he'', hπ''₁])
  let q₂₁ : pullback b π'' ⟶ pullback a π :=
    pullback.lift (pullback.fst b π'' ≫ q₂) (pullback.snd b π'' ≫ pullback.snd g₁ g₁)
    (by simp only [Category.assoc]; rw [h₂.w, reassoc_of% he'', hπ''₂])
  have hq₁₁f : q₁₁ ≫ pullback.fst a π = pullback.fst b π'' ≫ q₁ := pullback.lift_fst _ _ _
  have hq₁₁a : q₁₁ ≫ pullback.snd a π = pullback.snd b π'' ≫ pullback.fst g₁ g₁ :=
    pullback.lift_snd _ _ _
  have hq₂₁f : q₂₁ ≫ pullback.fst a π = pullback.fst b π'' ≫ q₂ := pullback.lift_fst _ _ _
  have hq₂₁a : q₂₁ ≫ pullback.snd a π = pullback.snd b π'' ≫ pullback.snd g₁ g₁ :=
    pullback.lift_snd _ _ _
  have h₁' : IsPullback q₁₁ (pullback.snd b π'') (pullback.snd a π) (pullback.fst g₁ g₁) := by
    refine IsPullback.of_right ?_ hq₁₁a hX₁
    rw [hq₁₁f, ← hπ''₁]
    exact (IsPullback.of_hasPullback b π'').paste_horiz h₁
  have h₂' : IsPullback q₂₁ (pullback.snd b π'') (pullback.snd a π) (pullback.snd g₁ g₁) := by
    refine IsPullback.of_right ?_ hq₂₁a hX₁
    rw [hq₂₁f, ← hπ''₂]
    exact (IsPullback.of_hasPullback b π'').paste_horiz h₂
  have refl₁ : ∀ ⦃T : Scheme.{u}⦄ (x : T ⟶ pullback a π),
      ∃ r : T ⟶ pullback b π'', r ≫ q₁₁ = x ∧ r ≫ q₂₁ = x := by
    intro T x
    obtain ⟨r', hr'₁, hr'₂⟩ := refl (x ≫ pullback.fst a π)
    let σ : T ⟶ pullback g₁ g₁ := pullback.lift (x ≫ pullback.snd a π) (x ≫ pullback.snd a π) rfl
    have hσ : r' ≫ b = σ ≫ π'' := by
      apply pullback.hom_ext
      · rw [Category.assoc, ← h₁.w, reassoc_of% hr'₁, Category.assoc, hπ''₁,
          pullback.lift_fst_assoc, Category.assoc, hX₁.w]
      · rw [Category.assoc, ← h₂.w, reassoc_of% hr'₂, Category.assoc, hπ''₂,
          pullback.lift_snd_assoc, Category.assoc, hX₁.w]
    refine ⟨pullback.lift r' σ hσ, ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hq₁₁f, pullback.lift_fst_assoc, hr'₁]
      · rw [Category.assoc, hq₁₁a, pullback.lift_snd_assoc, pullback.lift_fst]
    · apply pullback.hom_ext
      · rw [Category.assoc, hq₂₁f, pullback.lift_fst_assoc, hr'₂]
      · rw [Category.assoc, hq₂₁a, pullback.lift_snd_assoc, pullback.lift_snd]
  have trans₁ : ∀ ⦃T : Scheme.{u}⦄ (r r' : T ⟶ pullback b π''), r ≫ q₂₁ = r' ≫ q₁₁ →
      ∃ r'' : T ⟶ pullback b π'', r'' ≫ q₁₁ = r ≫ q₁₁ ∧ r'' ≫ q₂₁ = r' ≫ q₂₁ := by
    intro T r r' hrr
    have hρ : (r ≫ pullback.fst b π'') ≫ q₂ = (r' ≫ pullback.fst b π'') ≫ q₁ := by
      rw [Category.assoc, ← hq₂₁f, reassoc_of% hrr, hq₁₁f, Category.assoc]
    obtain ⟨ρ'', hρ₁, hρ₂⟩ := trans _ _ hρ
    have hmid : r ≫ pullback.snd b π'' ≫ pullback.snd g₁ g₁ =
        r' ≫ pullback.snd b π'' ≫ pullback.fst g₁ g₁ := by
      rw [← hq₂₁a, ← hq₁₁a, reassoc_of% hrr]
    let σ : T ⟶ pullback g₁ g₁ := pullback.lift (r ≫ pullback.snd b π'' ≫ pullback.fst g₁ g₁)
      (r' ≫ pullback.snd b π'' ≫ pullback.snd g₁ g₁) (by
        simp only [Category.assoc]
        rw [pullback.condition, reassoc_of% hmid, pullback.condition])
    have hσ : ρ'' ≫ b = σ ≫ π'' := by
      apply pullback.hom_ext
      · calc (ρ'' ≫ b) ≫ pullback.fst g g = (r ≫ pullback.fst b π'') ≫ q₁ ≫ a := by
              rw [Category.assoc, ← h₁.w, reassoc_of% hρ₁, Category.assoc]
          _ = r ≫ pullback.snd b π'' ≫ pullback.fst g₁ g₁ ≫ π := by
              rw [h₁.w, Category.assoc, reassoc_of% he'', hπ''₁]
          _ = (σ ≫ π'') ≫ pullback.fst g g := by
              rw [Category.assoc, hπ''₁, pullback.lift_fst_assoc, Category.assoc, Category.assoc]
      · calc (ρ'' ≫ b) ≫ pullback.snd g g = (r' ≫ pullback.fst b π'') ≫ q₂ ≫ a := by
              rw [Category.assoc, ← h₂.w, reassoc_of% hρ₂, Category.assoc]
          _ = r' ≫ pullback.snd b π'' ≫ pullback.snd g₁ g₁ ≫ π := by
              rw [h₂.w, Category.assoc, reassoc_of% he'', hπ''₂]
          _ = (σ ≫ π'') ≫ pullback.snd g g := by
              rw [Category.assoc, hπ''₂, pullback.lift_snd_assoc, Category.assoc, Category.assoc]
    refine ⟨pullback.lift ρ'' σ hσ, ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hq₁₁f, pullback.lift_fst_assoc, hρ₁, Category.assoc, Category.assoc,
          hq₁₁f]
      · rw [Category.assoc, hq₁₁a, pullback.lift_snd_assoc, pullback.lift_fst, Category.assoc,
          hq₁₁a]
    · apply pullback.hom_ext
      · rw [Category.assoc, hq₂₁f, pullback.lift_fst_assoc, hρ₂, Category.assoc, Category.assoc,
          hq₂₁f]
      · rw [Category.assoc, hq₂₁a, pullback.lift_snd_assoc, pullback.lift_snd, Category.assoc,
          hq₂₁a]
  -- descent over the affine `S₁`
  obtain ⟨X, f, h₁X, hpb, hq⟩ := exists_isPullback_of_isAffineHom g₁ (pullback.snd a π)
    (pullback.snd b π'') q₁₁ q₂₁ h₁' h₂' refl₁ trans₁
  -- `h₁X` factors through the fppf covering `X' ×_{S'} S₁ ⟶ X'`
  have hdesc : ∀ {T : Scheme.{u}} (u v : T ⟶ pullback a π),
      u ≫ pullback.fst a π = v ≫ pullback.fst a π → u ≫ h₁X = v ≫ h₁X := by
    intro T u v huv
    obtain ⟨r, hr₁, hr₂⟩ := refl (u ≫ pullback.fst a π)
    let σ : T ⟶ pullback g₁ g₁ := pullback.lift (u ≫ pullback.snd a π) (v ≫ pullback.snd a π) (by
      simp only [g₁, Category.assoc]
      rw [← hX₁.w_assoc, reassoc_of% huv])
    have hσ : r ≫ b = σ ≫ π'' := by
      apply pullback.hom_ext
      · rw [Category.assoc, ← h₁.w, reassoc_of% hr₁, Category.assoc, hπ''₁,
          pullback.lift_fst_assoc, Category.assoc, hX₁.w]
      · rw [Category.assoc, ← h₂.w, reassoc_of% hr₂, Category.assoc, hπ''₂,
          pullback.lift_snd_assoc, Category.assoc, reassoc_of% huv, hX₁.w]
    have hw₁ : pullback.lift r σ hσ ≫ q₁₁ = u := by
      apply pullback.hom_ext
      · rw [Category.assoc, hq₁₁f, pullback.lift_fst_assoc, hr₁]
      · rw [Category.assoc, hq₁₁a, pullback.lift_snd_assoc, pullback.lift_fst]
    have hw₂ : pullback.lift r σ hσ ≫ q₂₁ = v := by
      apply pullback.hom_ext
      · rw [Category.assoc, hq₂₁f, pullback.lift_fst_assoc, hr₂, huv]
      · rw [Category.assoc, hq₂₁a, pullback.lift_snd_assoc, pullback.lift_snd]
    rw [← hw₁, ← hw₂, Category.assoc, Category.assoc, hq]
  let h : X' ⟶ X := EffectiveEpi.desc (pullback.fst a π) h₁X hdesc
  have hfac : pullback.fst a π ≫ h = h₁X := EffectiveEpi.fac _ _ _
  have w : h ≫ f = a ≫ g := by
    rw [← cancel_epi (pullback.fst a π), reassoc_of% hfac, hpb.w, hX₁.w_assoc]
  refine ⟨X, f, h, ?_, ?_⟩
  · -- the comparison map `X' ⟶ X ×_S S'` is an isomorphism, since it is one after the fppf
    -- base change `S₁ ⟶ S'`
    let c : X' ⟶ pullback f g := pullback.lift h a w
    have hY₁ : IsPullback (pullback.fst (pullback.snd f g) π ≫ pullback.fst f g)
        (pullback.snd (pullback.snd f g) π) f g₁ :=
      (IsPullback.of_hasPullback (pullback.snd f g) π).paste_horiz (IsPullback.of_hasPullback f g)
    let c₁ : pullback a π ⟶ pullback (pullback.snd f g) π :=
      pullback.lift (pullback.fst a π ≫ c) (pullback.snd a π) (by
        rw [Category.assoc, pullback.lift_snd, hX₁.w])
    have hc₁ : c₁ = (hpb.isoIsPullback _ _ hY₁).hom := by
      apply hY₁.hom_ext
      · rw [IsPullback.isoIsPullback_hom_fst, pullback.lift_fst_assoc, Category.assoc,
          pullback.lift_fst, hfac]
      · rw [IsPullback.isoIsPullback_hom_snd, pullback.lift_snd]
    have hsq : IsPullback c₁ (pullback.fst a π) (pullback.fst (pullback.snd f g) π) c := by
      refine IsPullback.of_right (h₁₂ := pullback.snd (pullback.snd f g) π)
        (h₂₂ := pullback.snd f g) ?_ (pullback.lift_fst _ _ _)
        (IsPullback.of_hasPullback (pullback.snd f g) π).flip
      rw [pullback.lift_snd, pullback.lift_snd]
      exact hX₁.flip
    have : IsIso c := by
      apply MorphismProperty.of_isPullback_of_descendsAlong (P := isomorphisms Scheme.{u})
        (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hsq
      · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      · rw [hc₁]
        exact (isomorphisms Scheme).of_isIso _
    exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
  · -- `h ∘ q₁ = h ∘ q₂`, checked after the fppf base change `X₁'' ⟶ X''`
    have : Surjective π'' := MorphismProperty.pullbackMap (P := @Surjective) hπs hπs rfl rfl
    have : Flat π'' := MorphismProperty.pullbackMap (P := @Flat) ‹Flat π› ‹Flat π› rfl rfl
    have : LocallyOfFinitePresentation π'' :=
      MorphismProperty.pullbackMap (P := @LocallyOfFinitePresentation)
        ‹LocallyOfFinitePresentation π› ‹LocallyOfFinitePresentation π› rfl rfl
    rw [← cancel_epi (pullback.fst b π''), ← reassoc_of% hq₁₁f, ← reassoc_of% hq₂₁f, hfac, hq]

end SGA.SGA1.ExposeVIII
