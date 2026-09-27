/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Formal.EtaleLift
import SGA.SGA1.ExposeIX.FiniteEffectiveDescent


/-!
# SGA 1, Exposé IX, 1.7: étale schemes over a nilpotent thickening

IX.1.7 (I.8.3): let `i : S₀ ⟶ S` be a surjective closed immersion (a closed immersion defined by a
nil ideal). Base change along `i` is an equivalence from étale `S`-schemes to étale `S₀`-schemes
(`isEquivalence_pullback_etale_of_isClosedImmersion`).

Full faithfulness is IX.3 (`fullyFaithfulPullbackEtaleOfIsClosedImmersion`). For essential
surjectivity (`essSurj_pullback_etale_of_isClosedImmersion`): as `i` is radicial, every étale
`S₀`-scheme carries a unique descent datum relative to `i`, which is trivial since `i` is a
monomorphism (`DescentDatum.act_eq_fst_of_mono`); effectiveness is local on `S` and on the étale
scheme (IX.4.3, `DescentDatum.isEffective_of_universallyInjective_of_affine`), and the affine case
is I.8.1: étale algebras lift along `A → A ⧸ I` for any ideal `I`
(`Algebra.Etale.exists_etale_tensorQuotient_equiv`, from `SGA.Foundations.Formal.EtaleLift`;
`exists_isPullback_of_isClosedImmersion`).
-/

universe u

open CategoryTheory Limits MorphismProperty TensorProduct

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- I.8.1, affine form (from `SGA.Foundations.Formal.EtaleLift`): an affine étale
`Spec (A ⧸ I)`-scheme is the fibre over `Spec (A ⧸ I)` of an affine étale `Spec A`-scheme. -/
theorem exists_isPullback_of_etale_of_isAffine {A : Type u} [CommRing A] (I : Ideal A)
    {X₀ : Scheme.{u}} [IsAffine X₀] (b₀ : X₀ ⟶ Spec (.of (A ⧸ I))) [Etale b₀] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Algebra.Etale A B ∧
      ∃ ιX : X₀ ⟶ Spec (.of B),
        IsPullback ιX b₀ (Spec.map (CommRingCat.ofHom (algebraMap A B))) (specQuotient I) := by
  let φ : CommRingCat.of (A ⧸ I) ⟶ Γ(X₀, ⊤) := (Scheme.ΓSpecIso (.of (A ⧸ I))).inv ≫ b₀.appTop
  let : Algebra (A ⧸ I) Γ(X₀, ⊤) := φ.hom.toAlgebra
  have hφ : CommRingCat.ofHom (algebraMap (A ⧸ I) Γ(X₀, ⊤)) = φ := rfl
  have hb₀ : b₀ =
      X₀.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) Γ(X₀, ⊤))) := by
    rw [hφ, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  have : Algebra.Etale (A ⧸ I) Γ(X₀, ⊤) := by
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) Γ(X₀, ⊤)))) := by
      have : Etale (X₀.isoSpec.inv ≫ b₀) := inferInstance
      rwa [hb₀, Iso.inv_hom_id_assoc] at this
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp this
  obtain ⟨B, _, _, hBe, ⟨e⟩⟩ := Algebra.Etale.exists_etale_tensorQuotient_equiv I Γ(X₀, ⊤)
  let θ : X₀ ⟶ pullback (specQuotient I) (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    X₀.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (e : (A ⧸ I) ⊗[A] B →+* Γ(X₀, ⊤))) ≫
      (pullbackSpecIso A (A ⧸ I) B).inv
  have : IsIso (CommRingCat.ofHom (e : (A ⧸ I) ⊗[A] B →+* Γ(X₀, ⊤))) :=
    ⟨⟨CommRingCat.ofHom (e.symm : Γ(X₀, ⊤) →+* (A ⧸ I) ⊗[A] B),
      CommRingCat.hom_ext (RingHom.ext fun x ↦ e.symm_apply_apply x),
      CommRingCat.hom_ext (RingHom.ext fun x ↦ e.apply_symm_apply x)⟩⟩
  have : IsIso θ := by dsimp only [θ]; infer_instance
  have hθ : θ ≫ pullback.fst _ _ = b₀ := by
    rw [hb₀]
    simp only [θ, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
    congr 2
    ext x
    exact e.commutes (Ideal.Quotient.mk I x)
  refine ⟨B, inferInstance, inferInstance, hBe, θ ≫ pullback.snd _ _, ?_⟩
  refine (IsPullback.of_iso_pullback ⟨?_⟩ (asIso θ) hθ rfl).flip
  rw [asIso_hom, Category.assoc, ← pullback.condition, ← Category.assoc, hθ]

set_option backward.isDefEq.respectTransparency false in
/-- I.8.1, affine form: an affine étale scheme over a closed subscheme `T₀` of an affine scheme
`T` is the base change of an étale `T`-scheme. -/
theorem exists_isPullback_of_isClosedImmersion {T T₀ W : Scheme.{u}} [IsAffine T]
    (j : T₀ ⟶ T) [IsClosedImmersion j] [IsAffine W] (w : W ⟶ T₀) [Etale w] :
    ∃ (X : Scheme.{u}) (b : X ⟶ T) (v : W ⟶ X), Etale b ∧ IsPullback v w b j := by
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := j ≫ T.isoSpec.hom)).mp inferInstance
  obtain ⟨B, _, _, hB, ιX, hX⟩ := exists_isPullback_of_etale_of_isAffine I (w ≫ e.hom)
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) B))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr hB)
  refine ⟨Spec (.of B), Spec.map (CommRingCat.ofHom (algebraMap _ B)) ≫ T.isoSpec.inv, ιX,
    inferInstance, ?_⟩
  refine hX.of_iso (Iso.refl _) (Iso.refl _) e.symm T.isoSpec.symm (by simp) (by simp)
    (by simp) ?_
  rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc]
  change (e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫ _ = _
  rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Along a monomorphism `g`, a descent datum is trivial: `x'·s' = x'`. -/
lemma DescentDatum.act_eq_fst_of_mono {S' S X' : Scheme.{u}} {g : S' ⟶ S} [Mono g]
    {a : X' ⟶ S'} (D : DescentDatum g a) : D.act = pullback.fst (a ≫ g) g := by
  have h : pullback.fst (a ≫ g) g ≫ pullback.lift (𝟙 X') a (by simp) = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      rw [← cancel_mono g, Category.assoc, pullback.condition]
  rw [← Category.id_comp D.act, ← h, Category.assoc, D.unit, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.1.7 (and I.8.3), essential surjectivity: along a surjective closed immersion
`i : S₀ ⟶ S` (a closed immersion defined by a nil ideal), every étale `S₀`-scheme is the base
change of an étale `S`-scheme. Since `i` is radicial, every étale `S₀`-scheme carries a unique
descent datum, and effectiveness is local on `S` and on the étale scheme
(`DescentDatum.isEffective_of_universallyInjective_of_affine`); the affine case is I.8.1
(`exists_isPullback_of_isClosedImmersion`). -/
theorem essSurj_pullback_etale_of_isClosedImmersion {S₀ S : Scheme.{u}} (i : S₀ ⟶ S)
    [IsClosedImmersion i] [Surjective i] : (MorphismProperty.Over.pullback @Etale ⊤ i).EssSurj :=
  essSurj_pullback_etale_of_isEffective fun _ _ _ D ↦
    D.isEffective_of_universallyInjective_of_affine fun U W _ w _ E ↦ by
      have : IsAffine U.1 := U.2
      obtain ⟨X, b, v, hb, hv⟩ := exists_isPullback_of_isClosedImmersion (pullback.snd i U.1.ι) w
      exact ⟨X, b, v, hb, hv, by rw [E.act_eq_fst_of_mono]⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.1.7 (and I.8.3): base change along a surjective closed immersion `S₀ ⟶ S` is an
equivalence from étale `S`-schemes to étale `S₀`-schemes. -/
theorem isEquivalence_pullback_etale_of_isClosedImmersion {S₀ S : Scheme.{u}} (i : S₀ ⟶ S)
    [IsClosedImmersion i] [Surjective i] :
    (MorphismProperty.Over.pullback @Etale ⊤ i).IsEquivalence :=
  have := essSurj_pullback_etale_of_isClosedImmersion i
  have := (fullyFaithfulPullbackEtaleOfIsClosedImmersion i).full
  have := (fullyFaithfulPullbackEtaleOfIsClosedImmersion i).faithful
  { }

end SGA.SGA1.ExposeIX
