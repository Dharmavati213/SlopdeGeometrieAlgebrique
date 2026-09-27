/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.RelativeGluing
import SGA.Foundations.Projective.ProjBaseChange

/-!
# Relative `Proj`

A quasi-coherent graded algebra on a scheme `S` is described affine-locally
(`AlgebraicGeometry.Scheme.GradedAlgebraData`): a graded `Γ(S, U)`-algebra `A(U)` for every
affine open `U`, with restriction maps `A(U) → A(V)` for `V ⊆ U` such that
`A(V) = Γ(S, V) ⊗_{Γ(S, U)} A(U)`. By flat base change of `Proj`
(`AlgebraicGeometry.Proj.isPullback_map_baseChange`), the schemes `Proj A(U)` over `U` form a
relative gluing datum, and glue to the relative `Proj` over `S` (EGA II 3.1.3, Stacks 01M3).

## Main definitions and results

- `AlgebraicGeometry.Proj.map_toSpecBase`: `Proj` of a graded homomorphism over a ring
  homomorphism lies over `Spec` of the ring homomorphism.
- `AlgebraicGeometry.Proj.isIso_map_of_bijective`: `Proj` of a bijective graded homomorphism is
  an isomorphism.
- `AlgebraicGeometry.Scheme.GradedAlgebraData.relativeProj`: the relative `Proj` and
  `GradedAlgebraData.toBase`; `GradedAlgebraData.isPullback_ι_toBase`: over an affine open `U`
  it is `Proj A(U)`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite HomogeneousLocalization TensorProduct

namespace AlgebraicGeometry.Proj

section Functoriality

variable {R R' A B : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [Algebra R A]
  [Algebra R' B] {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R' B} [GradedAlgebra 𝒜]
  [GradedAlgebra ℬ]

lemma map_congr {ψ₁ ψ₂ : 𝒜 →+*ᵍ ℬ} (e : ψ₁ = ψ₂) (h₁ : HomogeneousIdeal.irrelevant ℬ ≤
    (HomogeneousIdeal.irrelevant 𝒜).map ψ₁) (h₂ : HomogeneousIdeal.irrelevant ℬ ≤
      (HomogeneousIdeal.irrelevant 𝒜).map ψ₂) : Proj.map ψ₁ h₁ = Proj.map ψ₂ h₂ := by
  subst e
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `Proj` of a graded homomorphism lying over a ring homomorphism `φ : R → R'` lies over
`Spec φ`. -/
theorem map_toSpecBase (φ : R →+* R') (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : ∀ r, ψ (algebraMap R A r) = algebraMap R' B (φ r))
    (hirr : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ) :
    Proj.map ψ hirr ≫ toSpecBase 𝒜 = toSpecBase ℬ ≫ Spec.map (CommRingCat.ofHom φ) := by
  refine (mapAffineOpenCover ψ hirr).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f, mapAffineOpenCover_f]
  rw [awayι_comp_map_assoc _ _ _ _ s.2.2, awayι_toSpecBase, awayι_toSpecBase_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  change (Away.map ψ s.2 (HomogeneousLocalization.mk
      ⟨0, algebraMap R (𝒜 0) r, 1, one_mem _⟩)).val =
    (HomogeneousLocalization.mk ⟨0, algebraMap R' (ℬ 0) (φ r), 1, one_mem _⟩ :
      Away ℬ (ψ s.2)).val
  rw [Away.map, map_mk, val_mk, val_mk]
  congr 1
  · change ψ (algebraMap R A r) = algebraMap R' B (φ r)
    exact hψ r
  · exact Subtype.ext ψ.map_one

/-- The inverse of a bijective graded homomorphism is graded. -/
lemma mem_of_bijective (ψ : 𝒜 →+*ᵍ ℬ) (hψ : Function.Bijective ψ) {n : ℕ} {b : B}
    (hb : b ∈ ℬ n) {a : A} (ha : ψ a = b) : a ∈ 𝒜 n := by
  classical
  have : ψ (DirectSum.decompose 𝒜 a n) = b := by
    rw [GradedRingHom.map_directSumDecompose, ha, DirectSum.decompose_of_mem_same _ hb]
  rw [← hψ.1 (this.trans ha.symm)]
  exact SetLike.coe_mem _

/-- The graded inverse of a bijective graded homomorphism. -/
noncomputable def invOfBijective (ψ : 𝒜 →+*ᵍ ℬ) (hψ : Function.Bijective ψ) : ℬ →+*ᵍ 𝒜 where
  toRingHom := (RingEquiv.ofBijective ψ.toRingHom hψ).symm.toRingHom
  map_mem {_ b} hb := mem_of_bijective ψ hψ hb
    ((RingEquiv.ofBijective ψ.toRingHom hψ).apply_symm_apply b)

lemma irrelevant_le_map_of_surjective (ψ : 𝒜 →+*ᵍ ℬ) (hψ : Function.Bijective ψ) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ := by
  intro b hb
  obtain ⟨a, rfl⟩ := hψ.2 b
  refine Ideal.mem_map_of_mem _ ?_
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    ← GradedRingHom.map_directSumDecompose] at hb
  exact hψ.1 (hb.trans (map_zero ψ).symm)

set_option backward.isDefEq.respectTransparency false in
/-- `Proj` of a bijective graded homomorphism is an isomorphism. -/
theorem isIso_map_of_bijective (ψ : 𝒜 →+*ᵍ ℬ) (hψ : Function.Bijective ψ)
    (hirr : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ) :
    IsIso (Proj.map ψ hirr) := by
  let ψ' := invOfBijective ψ hψ
  have hψ' : Function.Bijective ψ' := (RingEquiv.ofBijective ψ.toRingHom hψ).symm.bijective
  have e₁ : ψ'.comp ψ = GradedRingHom.id 𝒜 := GradedRingHom.ext fun a ↦
    (RingEquiv.ofBijective ψ.toRingHom hψ).symm_apply_apply a
  have e₂ : ψ.comp ψ' = GradedRingHom.id ℬ := GradedRingHom.ext fun b ↦
    (RingEquiv.ofBijective ψ.toRingHom hψ).apply_symm_apply b
  refine ⟨Proj.map ψ' (irrelevant_le_map_of_surjective ψ' hψ'), ?_, ?_⟩
  · rw [← Proj.map_comp, map_congr e₂ _ (by simp), Proj.map_id]
  · rw [← Proj.map_comp, map_congr e₁ _ (by simp), Proj.map_id]

end Functoriality

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- A quasi-coherent sheaf of `ℕ`-graded algebras on `S`, described on the affine opens: a graded
`Γ(S, U)`-algebra `A(U)` for every affine open `U`, with graded restriction homomorphisms such
that `A(V) = Γ(S, V) ⊗_{Γ(S, U)} A(U)` for `V ⊆ U` (EGA I 1.4, EGA II 3.1). -/
structure GradedAlgebraData where
  /-- The algebra of sections over an affine open. -/
  A : S.affineOpens → Type u
  [commRing : ∀ U, CommRing (A U)]
  [algebra : ∀ U, Algebra Γ(S, U.1) (A U)]
  /-- The grading. -/
  grading : ∀ U, ℕ → Submodule Γ(S, U.1) (A U)
  [gradedAlgebra : ∀ U, GradedAlgebra (grading U)]
  /-- The restriction homomorphisms. -/
  res : ∀ {U V : S.affineOpens}, V ≤ U → (grading U →+*ᵍ grading V)
  res_id : ∀ U (a : A U), res (le_refl U) a = a
  res_comp : ∀ {U V W : S.affineOpens} (h : V ≤ U) (h' : W ≤ V) (a : A U),
    res h' (res h a) = res (h'.trans h) a
  res_algebraMap : ∀ {U V : S.affineOpens} (h : V ≤ U) (r : Γ(S, U.1)),
    res h (algebraMap Γ(S, U.1) (A U) r) =
      algebraMap Γ(S, V.1) (A V) (S.presheaf.map (homOfLE (show V.1 ≤ U.1 from h)).op r)
  isPushout : ∀ {U V : S.affineOpens} (h : V ≤ U),
    IsPushout (CommRingCat.ofHom (algebraMap Γ(S, U.1) (A U)))
      (S.presheaf.map (homOfLE (show V.1 ≤ U.1 from h)).op) (CommRingCat.ofHom (res h).toRingHom)
      (CommRingCat.ofHom (algebraMap Γ(S, V.1) (A V)))

namespace GradedAlgebraData

attribute [instance] commRing algebra gradedAlgebra

variable {S} (d : S.GradedAlgebraData)

section BaseChange

variable {U V : S.affineOpens} (h : V ≤ U)

/-- The restriction `Γ(S, U) → Γ(S, V)`. -/
noncomputable abbrev resΓ : Γ(S, U.1) ⟶ Γ(S, V.1) :=
  S.presheaf.map (homOfLE (show V.1 ≤ U.1 from h)).op

set_option backward.isDefEq.respectTransparency false in
/-- The graded isomorphism `Γ(S, V) ⊗_{Γ(S, U)} A(U) ≅ A(V)`. -/
lemma exists_baseChange_gradedHom :
    letI : Algebra Γ(S, U.1) Γ(S, V.1) := (resΓ h).hom.toAlgebra
    ∃ E : (fun n ↦ (d.grading U n).baseChange Γ(S, V.1)) →+*ᵍ d.grading V,
      Function.Bijective E ∧ E.comp (Proj.baseChangeGradedHom Γ(S, V.1) (d.grading U)) = d.res h ∧
        ∀ r, E (algebraMap Γ(S, V.1) (Γ(S, V.1) ⊗[Γ(S, U.1)] d.A U) r) =
          algebraMap Γ(S, V.1) (d.A V) r := by
  let : Algebra Γ(S, U.1) Γ(S, V.1) := (resΓ h).hom.toAlgebra
  have hpo := CommRingCat.isPushout_tensorProduct Γ(S, U.1) Γ(S, V.1) (d.A U)
  let e := hpo.isoIsPushout _ _ (d.isPushout h).flip
  have he₁ (r : Γ(S, V.1)) : e.hom.hom (r ⊗ₜ 1) = algebraMap Γ(S, V.1) (d.A V) r :=
    congrArg (fun φ ↦ φ.hom r) (hpo.inl_isoIsPushout_hom _ _ (d.isPushout h).flip)
  have he₂ (a : d.A U) : e.hom.hom (1 ⊗ₜ a) = d.res h a :=
    congrArg (fun φ ↦ φ.hom a) (hpo.inr_isoIsPushout_hom _ _ (d.isPushout h).flip)
  let E : (fun n ↦ (d.grading U n).baseChange Γ(S, V.1)) →+*ᵍ d.grading V :=
    { toRingHom := e.hom.hom
      map_mem := fun {n x} hx ↦ by
        rw [Submodule.baseChange_eq_span] at hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨a, ha, rfl⟩ := hy
          change e.hom.hom (1 ⊗ₜ a) ∈ _
          rw [he₂]
          exact (d.res h).2 ha
        | zero => simp
        | add y z _ _ hy hz => simpa using add_mem hy hz
        | smul r y _ hy =>
          change e.hom.hom (r • y) ∈ _
          rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
            Algebra.algebraMap_self, RingHom.id_apply, he₁, ← Algebra.smul_def]
          exact Submodule.smul_mem _ r hy }
  refine ⟨E, ConcreteCategory.bijective_of_isIso e.hom, GradedRingHom.ext fun a ↦ he₂ a,
    fun r ↦ ?_⟩
  change e.hom.hom (algebraMap Γ(S, V.1) (Γ(S, V.1) ⊗[Γ(S, U.1)] d.A U) r) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, he₁]

lemma irrelevant_le_map_res : HomogeneousIdeal.irrelevant (d.grading V) ≤
    (HomogeneousIdeal.irrelevant (d.grading U)).map (d.res h) := by
  let : Algebra Γ(S, U.1) Γ(S, V.1) := (resΓ h).hom.toAlgebra
  obtain ⟨E, hE, hEbc, -⟩ := d.exists_baseChange_gradedHom h
  rw [← hEbc]
  exact HomogeneousIdeal.irrelevant_le_map_comp (Proj.irrelevant_baseChange_le _)
    (Proj.irrelevant_le_map_of_surjective E hE)

set_option backward.isDefEq.respectTransparency false in
/-- `Proj A(V)` is the base change of `Proj A(U)` along `Spec Γ(S, V) ⟶ Spec Γ(S, U)`. -/
theorem isPullback_map_res :
    IsPullback (Proj.map (d.res h) (d.irrelevant_le_map_res h)) (Proj.toSpecBase (d.grading V))
      (Proj.toSpecBase (d.grading U)) (Spec.map (resΓ h)) := by
  let : Algebra Γ(S, U.1) Γ(S, V.1) := (resΓ h).hom.toAlgebra
  obtain ⟨E, hE, hEbc, hEalg⟩ := d.exists_baseChange_gradedHom h
  have hirrE := Proj.irrelevant_le_map_of_surjective E hE
  have : IsIso (Proj.map E hirrE) := Proj.isIso_map_of_bijective E hE hirrE
  have hmap : Proj.map (d.res h) (d.irrelevant_le_map_res h) =
      Proj.map E hirrE ≫ Proj.map _ (Proj.irrelevant_baseChange_le (d.grading U)) := by
    rw [← Proj.map_comp]
    exact Proj.map_congr hEbc.symm _ _
  have hbase : Proj.toSpecBase (d.grading V) =
      Proj.map E hirrE ≫ Proj.toSpecBase (fun n ↦ (d.grading U n).baseChange Γ(S, V.1)) := by
    have := Proj.map_toSpecBase (RingHom.id Γ(S, V.1)) E hEalg hirrE
    rw [this]
    simp only [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  refine (Proj.isPullback_map_baseChange (R' := Γ(S, V.1)) (d.grading U)).of_iso
    (asIso (Proj.map E hirrE)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by simp) (by simp; rfl)
  · rw [hmap]
    simp
  · rw [hbase]
    simp

end BaseChange


section Gluing

lemma SpecMap_resΓ_isoSpec_inv {U V : S.affineOpens} (h : V ≤ U) :
    Spec.map (resΓ h) ≫ U.2.isoSpec.inv = V.2.isoSpec.inv ≫ S.homOfLE h := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact Scheme.Opens.toSpecΓ_SpecMap_presheaf_map _ _ _

/-- The diagram `U ↦ Proj A(U)` over the affine opens of `S`. -/
noncomputable def projFunctor : S.affineOpens ⥤ Scheme.{u} where
  obj U := Proj (d.grading U)
  map {V U} f := Proj.map (d.res (leOfHom f)) (d.irrelevant_le_map_res _)
  map_id U := (Proj.map_congr (GradedRingHom.ext (d.res_id U)) _ _).trans Proj.map_id
  map_comp {W V U} f g := by
    rw [← Proj.map_comp]
    exact Proj.map_congr (GradedRingHom.ext fun a ↦ (d.res_comp _ _ a).symm) _ _

/-- The structure morphisms `Proj A(U) ⟶ U`. -/
noncomputable def projNatTrans :
    d.projFunctor ⟶ (S.directedAffineCover.functorOfLocallyDirected : S.affineOpens ⥤ Scheme) where
  app U := Proj.toSpecBase (d.grading U) ≫ U.2.isoSpec.inv
  naturality {V U} f := by
    change Proj.map (d.res (leOfHom f)) _ ≫ Proj.toSpecBase _ ≫ U.2.isoSpec.inv =
      (Proj.toSpecBase _ ≫ V.2.isoSpec.inv) ≫ S.homOfLE (leOfHom f)
    rw [Category.assoc, ← SpecMap_resΓ_isoSpec_inv, ← Category.assoc, ← Category.assoc,
      (d.isPullback_map_res (leOfHom f)).w]

lemma projNatTrans_equifibered : d.projNatTrans.Equifibered := fun V U f ↦
  (d.isPullback_map_res (leOfHom f)).of_iso (Iso.refl _) (Iso.refl _) V.2.isoSpec.symm
    U.2.isoSpec.symm ((Category.comp_id _).trans (Category.id_comp _).symm)
    (Category.id_comp _).symm (Category.id_comp _).symm (SpecMap_resΓ_isoSpec_inv _)

/-- The relative gluing datum of the `Proj A(U)` over the affine opens `U` of `S`. -/
noncomputable def relativeGluingData : S.directedAffineCover.RelativeGluingData where
  functor := d.projFunctor
  natTrans := d.projNatTrans
  equifibered := d.projNatTrans_equifibered

/-- The relative `Proj` of a quasi-coherent graded algebra on `S` (EGA II 3.1.3). -/
noncomputable def relativeProj : Scheme.{u} :=
  d.relativeGluingData.glued

/-- The structure morphism of the relative `Proj`. -/
noncomputable def toBase : d.relativeProj ⟶ S :=
  d.relativeGluingData.toBase

/-- Over an affine open `U` of `S`, the relative `Proj` is `Proj A(U)`. -/
theorem isPullback_ι_toBase (U : S.affineOpens) :
    IsPullback (Proj.toSpecBase (d.grading U) ≫ U.2.isoSpec.inv)
      (colimit.ι d.relativeGluingData.functor U) U.1.ι d.toBase :=
  d.relativeGluingData.isPullback_natTrans_ι_toBase U

end Gluing

end GradedAlgebraData

end AlgebraicGeometry.Scheme
