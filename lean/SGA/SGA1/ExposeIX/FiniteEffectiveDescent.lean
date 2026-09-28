/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CompletionDimension
import SGA.Foundations.Formal.CompletionNoetherian
import SGA.Foundations.Formal.FiniteEtale
import SGA.SGA1.ExposeIX.CompletedLocalRings
import SGA.SGA1.ExposeIX.Unramified
import SGA.SGA1.ExposeIX.EffectiveNearPoint
import SGA.SGA1.ExposeIX.QuasiAffineDescent
import SGA.SGA1.ExposeIX.SubmersiveCompleteLocal


/-!
# SGA 1, Exposé IX, 4.7 and 4.10: descent of étale schemes along finite morphisms

IX.4.7: a finite surjective morphism `g : S' ⟶ S` (of finite presentation) is an effective descent
morphism for étale separated schemes of finite type. We prove it when `S` is locally noetherian
(`DescentDatum.isEffective_of_isFinite`, `isEffectiveDescentMorphism_of_isFinite`), following SGA,
and deduce IX.4.10 (topological invariance of the étale site under finite radicial surjective
morphisms) over a locally noetherian base
(`isEquivalence_pullback_etale_of_isFinite_of_isLocallyNoetherian`; the general case, by
noetherian approximation, is in `SGA.SGA1.ExposeIX.TopologicalInvariance`).

* Étale coverings over a complete noetherian local base `Spec R`
  (`DescentDatum.isEffective_of_isFinite_of_isAdicComplete`): over the closed point the datum is
  effective by IX.4.1 (the base change of `g` is faithfully flat); the descended scheme `X₀` is
  finite étale and lifts to a finite étale `X = Spec B` (IX.1.8 for complete rings,
  `Algebra.Etale.exists_finite_etale_tensorQuotient_equiv`). The projection `X' ⟶ X₀` lifts
  uniquely to `X' ⟶ X`: morphisms from a finite `Spec R`-scheme to `X` are determined by, and
  lift from, the closed fibre (`existsUnique_hom_of_isPullback`, from
  `Algebra.FormallyEtale.bijective_map_tensorQuotient`). The square is cartesian by
  `isIso_of_isIso_closedFibre` (an étale morphism of finite `Spec R`-schemes which is an
  isomorphism on the closed fibres is an isomorphism), and compatible with the descent data by
  uniqueness of lifts. By IX.4.5, étale coverings over a locally noetherian base follow
  (`DescentDatum.isEffective_etaleCovering_of_isFinite`).
* The general case over a complete noetherian local base, by induction on the dimension
  (`effectiveFiniteDescentComplete`): the generizations of the closed fibre of `X'` form an open
  and closed subset, finite over `S'` and stable under the descent datum
  (`DescentDatum.exists_isStable_isFinite`, from IX.2.5's
  `exists_opens_forall_specializes_isFinite`);
  its complement lies over the punctured spectrum, whose local rings, and their completions,
  have smaller dimension (`IsLocalRing.ringKrullDim_adicCompletion_le`,
  `AlgebraicGeometry.ringKrullDim_stalk_lt_of_ne_closedPoint`), so that the induction hypothesis
  applies via IX.4.5 (`DescentDatum.isEffective_of_isFinite_of_forall_stalk`); the two effective
  pieces are glued (IX.4.3).

The general case (arbitrary `S`, `g` of finite presentation) is in
`SGA.SGA1.ExposeIX.HenselianFiniteDescent`, with strict henselizations in place of completions.
The two local stages are stated here for any local base with the relevant lifting properties
(`DescentDatum.isEffective_of_isFinite_of_lift`, `DescentDatum.exists_isStable_isFinite_of_forall`).
-/

universe u

open CategoryTheory Limits TensorProduct MorphismProperty

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

section General

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The closed immersion `Spec (A ⧸ I) ⟶ Spec A`. -/
noncomputable abbrev specQuotient : Spec (.of (A ⧸ I)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I)))

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms from a finite `Spec A`-scheme `Y` to `Spec B` are determined by, and lift from, their
restrictions to `Y ×_{Spec A} Spec (A ⧸ I)` (given here by any cartesian square), provided the
corresponding statement holds for `A`-algebra maps from `B` to finite `A`-algebras. -/
theorem existsUnique_hom_of_isPullback_of_bijective {Y Y₀ : Scheme.{u}} {p : Y ⟶ Spec (.of A)}
    [IsFinite p] {ι : Y₀ ⟶ Y} {q : Y₀ ⟶ Spec (.of (A ⧸ I))} (h : IsPullback ι q p (specQuotient I))
    (B : Type u) [CommRing B] [Algebra A B]
    (hB : ∀ (T : Type u) [CommRing T] [Algebra A T] [Module.Finite A T], Function.Bijective
      fun f : B →ₐ[A] T ↦ (Algebra.TensorProduct.includeRight : T →ₐ[A] (A ⧸ I) ⊗[A] T).comp f)
    (f₀ : Y₀ ⟶ Spec (.of B)) (hf₀ : f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = ι ≫ p) :
    ∃! f : Y ⟶ Spec (.of B),
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = p ∧ ι ≫ f = f₀ := by
  have : IsAffine Y := isAffine_of_isAffineHom p
  let φ : CommRingCat.of A ⟶ Γ(Y, ⊤) := (Scheme.ΓSpecIso (.of A)).inv ≫ p.appTop
  let : Algebra A Γ(Y, ⊤) := φ.hom.toAlgebra
  have hφ : CommRingCat.ofHom (algebraMap A Γ(Y, ⊤)) = φ := rfl
  have hp : p = Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A Γ(Y, ⊤))) := by
    rw [hφ, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  have : Module.Finite A Γ(Y, ⊤) := by
    change φ.hom.Finite
    exact p.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2)
  have h' : IsPullback q (ι ≫ Y.isoSpec.hom) (specQuotient I)
      (Spec.map (CommRingCat.ofHom (algebraMap A Γ(Y, ⊤)))) :=
    h.flip.of_iso (Iso.refl _) (Iso.refl _) Y.isoSpec (Iso.refl _) (by simp) (by simp)
      (by simp) (by simp [hp])
  let e : Y₀ ≅ Spec (.of ((A ⧸ I) ⊗[A] Γ(Y, ⊤))) :=
    h'.isoPullback ≪≫ pullbackSpecIso A (A ⧸ I) Γ(Y, ⊤)
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom
      (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := A) (A := A ⧸ I) (B := Γ(Y, ⊤))))) =
      ι ≫ Y.isoSpec.hom := by
    rw [Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_snd, IsPullback.isoPullback_hom_snd]
  have hincl : CommRingCat.ofHom (algebraMap A Γ(Y, ⊤)) ≫ CommRingCat.ofHom
      (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight (R := A) (A := A ⧸ I) (B := Γ(Y, ⊤)))) =
      CommRingCat.ofHom (algebraMap A ((A ⧸ I) ⊗[A] Γ(Y, ⊤))) := by
    ext x; simp [Algebra.TensorProduct.algebraMap_apply]
  let incR : CommRingCat.of Γ(Y, ⊤) ⟶ CommRingCat.of ((A ⧸ I) ⊗[A] Γ(Y, ⊤)) :=
    CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight (R := A) (A := A ⧸ I) (B := Γ(Y, ⊤))))
  -- morphisms `Y ⟶ Spec B` over `Spec A` come from `A`-algebra maps
  have key (f : Y ⟶ Spec (.of B)) (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = p) :
      ∃ ψ : B →ₐ[A] Γ(Y, ⊤),
        f = Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (ψ : B →+* Γ(Y, ⊤))) := by
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ f)
    have hc : CommRingCat.ofHom (algebraMap A B) ≫ ψ =
        CommRingCat.ofHom (algebraMap A Γ(Y, ⊤)) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hψ, Category.assoc, hf, hp, Iso.inv_hom_id_assoc]
    refine ⟨{ ψ.hom with commutes' := fun a ↦ congr($hc a) }, ?_⟩
    rw [← Iso.inv_comp_eq, ← hψ]
    rfl
  let f₀' := e.inv ≫ f₀
  obtain ⟨ψ₀, hψ₀⟩ := Spec.map_surjective f₀'
  have hc₀ : CommRingCat.ofHom (algebraMap A B) ≫ ψ₀ =
      CommRingCat.ofHom (algebraMap A ((A ⧸ I) ⊗[A] Γ(Y, ⊤))) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ₀, Category.assoc, hf₀, hp, ← Category.assoc ι, ← he, ← hincl,
      Spec.map_comp]
    simp
  let ψ₀' : B →ₐ[A] (A ⧸ I) ⊗[A] Γ(Y, ⊤) := { ψ₀.hom with commutes' := fun a ↦ congr($hc₀ a) }
  obtain ⟨ψ, hψ⟩ := (hB Γ(Y, ⊤)).2 ψ₀'
  have hψ' : CommRingCat.ofHom (ψ : B →+* Γ(Y, ⊤)) ≫ incR = ψ₀ := by
    ext x
    exact congr($hψ x)
  have hmap (χ : B →ₐ[A] Γ(Y, ⊤)) :
      e.hom ≫ Spec.map (CommRingCat.ofHom (χ : B →+* Γ(Y, ⊤)) ≫ incR) =
      ι ≫ Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (χ : B →+* Γ(Y, ⊤))) := by
    rw [Spec.map_comp, ← Category.assoc, he, Category.assoc]
  have hex : ι ≫ Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (ψ : B →+* Γ(Y, ⊤))) = f₀ := by
    rw [← hmap, hψ', hψ₀]
    simp [f₀']
  refine ⟨Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (ψ : B →+* Γ(Y, ⊤))), ⟨?_, hex⟩, ?_⟩
  · rw [Category.assoc, ← Spec.map_comp, hp]
    congr 2
    ext a
    exact ψ.commutes a
  · rintro f ⟨hf₁, hf₂⟩
    obtain ⟨ψ', rfl⟩ := key f hf₁
    congr 2
    have : (Algebra.TensorProduct.includeRight : Γ(Y, ⊤) →ₐ[A] (A ⧸ I) ⊗[A] Γ(Y, ⊤)).comp ψ' =
        (Algebra.TensorProduct.includeRight).comp ψ := by
      have h₁ : e.hom ≫ Spec.map (CommRingCat.ofHom (ψ' : B →+* Γ(Y, ⊤)) ≫ incR) =
          e.hom ≫ Spec.map (CommRingCat.ofHom (ψ : B →+* Γ(Y, ⊤)) ≫ incR) := by
        rw [hmap, hmap, hex, hf₂]
      have h₂ := Spec.map_injective (cancel_epi e.hom |>.mp h₁)
      ext x
      exact congr($h₂ x)
    rw [(hB Γ(Y, ⊤)).1 this]

set_option backward.isDefEq.respectTransparency false in
/-- A finite étale `Spec (A ⧸ I)`-scheme is the fibre of a finite étale `Spec A`-scheme, provided
finite étale `A ⧸ I`-algebras lift to finite étale `A`-algebras. -/
theorem exists_isPullback_of_finite_etale_of_lift
    (hlift : ∀ (C : Type u) [CommRing C] [Algebra (A ⧸ I) C] [Module.Finite (A ⧸ I) C]
      [Algebra.Etale (A ⧸ I) C], ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
        Module.Finite A B ∧ Algebra.Etale A B ∧ Nonempty ((A ⧸ I) ⊗[A] B ≃ₐ[A ⧸ I] C))
    {X₀ : Scheme.{u}} (b₀ : X₀ ⟶ Spec (.of (A ⧸ I))) [IsFinite b₀] [Etale b₀] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
      ∃ ιX : X₀ ⟶ Spec (.of B),
        IsPullback ιX b₀ (Spec.map (CommRingCat.ofHom (algebraMap A B))) (specQuotient I) := by
  have : IsAffine X₀ := isAffine_of_isAffineHom b₀
  let φ : CommRingCat.of (A ⧸ I) ⟶ Γ(X₀, ⊤) := (Scheme.ΓSpecIso (.of (A ⧸ I))).inv ≫ b₀.appTop
  let : Algebra (A ⧸ I) Γ(X₀, ⊤) := φ.hom.toAlgebra
  have hφ : CommRingCat.ofHom (algebraMap (A ⧸ I) Γ(X₀, ⊤)) = φ := rfl
  have hb₀ : b₀ = X₀.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) Γ(X₀, ⊤))) := by
    rw [hφ, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  have : Module.Finite (A ⧸ I) Γ(X₀, ⊤) := by
    change φ.hom.Finite
    exact b₀.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (A ⧸ I))).inv).2)
  have : Algebra.Etale (A ⧸ I) Γ(X₀, ⊤) := by
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap (A ⧸ I) Γ(X₀, ⊤)))) := by
      have : Etale (X₀.isoSpec.inv ≫ b₀) := inferInstance
      rwa [hb₀, Iso.inv_hom_id_assoc] at this
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp this
  obtain ⟨B, _, _, hBf, hBe, ⟨e⟩⟩ := hlift Γ(X₀, ⊤)
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
  refine ⟨B, inferInstance, inferInstance, hBf, hBe, θ ≫ pullback.snd _ _, ?_⟩
  refine (IsPullback.of_iso_pullback ⟨?_⟩ (asIso θ) hθ rfl).flip
  rw [asIso_hom, Category.assoc, ← pullback.condition, ← Category.assoc, hθ]

end General

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]

/-- Maps out of a formally étale algebra into a finite algebra over an adic noetherian ring are
determined by, and lift from, their reductions modulo `I`. -/
theorem bijective_comp_includeRight_of_isAdicComplete {B R : Type u} [CommRing B] [CommRing R]
    [Algebra A B] [Algebra A R] [Algebra.FormallyEtale A B] [Module.Finite A R] :
    Function.Bijective fun f : B →ₐ[A] R ↦
      ((Algebra.TensorProduct.includeRight : R →ₐ[A] (A ⧸ I) ⊗[A] R)).comp f := by
  have H := Algebra.FormallyEtale.bijective_map_tensorQuotient I (B := B) (B' := R)
  refine ⟨fun f g hfg ↦ H.1 ?_, fun ψ ↦ ?_⟩
  · apply Algebra.TensorProduct.ext (Subsingleton.elim _ _)
    ext b
    simpa using congr($hfg b)
  · let Ψ : (A ⧸ I) ⊗[A] B →ₐ[A ⧸ I] (A ⧸ I) ⊗[A] R :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) ψ fun _ _ ↦ Commute.all _ _
    obtain ⟨f, hf⟩ := H.2 Ψ
    refine ⟨f, ?_⟩
    ext b
    have := congr($hf (1 ⊗ₜ b))
    simpa [Ψ, ← Algebra.TensorProduct.one_def] using this

/-- Morphisms from a finite `Spec A`-scheme `Y` to `Spec B`, for `B` formally étale over `A`, are
determined by, and lift from, their restrictions to `Y ×_{Spec A} Spec (A ⧸ I)` (given here by any
cartesian square). -/
theorem existsUnique_hom_of_isPullback {Y Y₀ : Scheme.{u}} {p : Y ⟶ Spec (.of A)} [IsFinite p]
    {ι : Y₀ ⟶ Y} {q : Y₀ ⟶ Spec (.of (A ⧸ I))} (h : IsPullback ι q p (specQuotient I))
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.FormallyEtale A B]
    (f₀ : Y₀ ⟶ Spec (.of B)) (hf₀ : f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = ι ≫ p) :
    ∃! f : Y ⟶ Spec (.of B),
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = p ∧ ι ≫ f = f₀ :=
  existsUnique_hom_of_isPullback_of_bijective I h B
    (fun _ _ _ _ ↦ bijective_comp_includeRight_of_isAdicComplete I) f₀ hf₀

set_option backward.isDefEq.respectTransparency false in
/-- The fibre of a fibre product is the fibre product of the fibres. -/
lemma isPullback_pullbackMap_of_isPullback {X S' T S X₀ S'₀ : Scheme.{u}} {b : X ⟶ S}
    {g : S' ⟶ S} {σ : T ⟶ S} {ιX : X₀ ⟶ X} {qX : X₀ ⟶ T} {ιS : S'₀ ⟶ S'} {qS : S'₀ ⟶ T}
    (hX : IsPullback ιX qX b σ) (hS : IsPullback ιS qS g σ) :
    IsPullback (pullback.map qX qS b g ιX ιS σ hX.w.symm hS.w.symm)
      (pullback.snd qX qS ≫ qS) (pullback.snd b g ≫ g) σ := by
  refine IsPullback.of_isLimit' ⟨by simp [pullback.map, hS.w]⟩ (PullbackCone.IsLimit.mk _
    (fun s ↦ pullback.lift
      (hX.lift (s.fst ≫ pullback.fst b g) s.snd (by
        rw [Category.assoc, pullback.condition, ← Category.assoc]; exact s.condition))
      (hS.lift (s.fst ≫ pullback.snd b g) s.snd (by rw [Category.assoc]; exact s.condition))
      (by simp))
    (fun s ↦ ?_) (fun s ↦ by simp) (fun s m h₁ h₂ ↦ ?_))
  · apply pullback.hom_ext <;> simp [pullback.map]
  · have h₁' := congr_arg (· ≫ pullback.fst b g) h₁
    have h₁'' := congr_arg (· ≫ pullback.snd b g) h₁
    simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd] at h₁' h₁''
    have h₂' : m ≫ pullback.fst qX qS ≫ qX = s.snd := by
      rw [pullback.condition, ← h₂]
    apply pullback.hom_ext
    · apply hX.hom_ext
      · simpa using h₁'
      · simpa using h₂'
    · apply hS.hom_ext
      · simpa using h₁''
      · simpa using h₂

/-- A finite étale `Spec (A ⧸ I)`-scheme is the fibre of a finite étale `Spec A`-scheme. -/
theorem exists_isPullback_of_finite_etale {X₀ : Scheme.{u}} (b₀ : X₀ ⟶ Spec (.of (A ⧸ I)))
    [IsFinite b₀] [Etale b₀] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
      ∃ ιX : X₀ ⟶ Spec (.of B),
        IsPullback ιX b₀ (Spec.map (CommRingCat.ofHom (algebraMap A B))) (specQuotient I) :=
  exists_isPullback_of_finite_etale_of_lift I
    (fun C _ _ _ _ ↦ Algebra.Etale.exists_finite_etale_tensorQuotient_equiv I C) b₀

section ClosedFibre

open IsLocalRing

/-- The image of the first projection of a cartesian square of schemes. -/
lemma isPullback_range_fst_eq {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback fst snd f g) : Set.range fst = f ⁻¹' Set.range g := by
  have : Set.range h.isoPullback.hom = Set.univ :=
    Set.range_eq_univ.mpr h.isoPullback.hom.homeomorph.surjective
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, this,
    Set.image_univ, Scheme.Pullback.range_fst]

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Over a local ring, a nonempty closed subset of a scheme universally closed over `Spec R`
meets the closed fibre. -/
lemma exists_mem_closedFibre_of_isClosed {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))
    [UniversallyClosed p] {Z : Set Y} (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ y ∈ Z, p y = closedPoint R := by
  obtain ⟨y, hy⟩ := hne
  have hC : IsClosed (p '' Z) := p.isClosedMap _ hZ
  have : closedPoint R ∈ p '' Z :=
    (specializes_closedPoint (p y)).mem_closed hC ⟨y, hy, rfl⟩
  obtain ⟨y', hy', e⟩ := this
  exact ⟨y', hy', e⟩

/-- Over a local ring, a clopen subset of a scheme universally closed over `Spec R` which
contains the closed fibre is everything. -/
lemma eq_univ_of_isClopen_of_closedFibre_subset {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))
    [UniversallyClosed p] {U : Set Y} (hU : IsClopen U) (hs : p ⁻¹' {closedPoint R} ⊆ U) :
    U = Set.univ := by
  by_contra hne
  obtain ⟨y, hy, hys⟩ := exists_mem_closedFibre_of_isClosed p hU.isOpen.isClosed_compl
    (Set.nonempty_compl.mpr hne)
  exact hy (hs hys)

set_option backward.isDefEq.respectTransparency false in
/-- Over a local ring `R`, an étale morphism `c : Y ⟶ Z` of finite `Spec R`-schemes which becomes
an isomorphism over the closed point (given by cartesian squares over some `σ : T ⟶ Spec R`
whose image contains the closed point) is an isomorphism. -/
theorem isIso_of_isIso_closedFibre {T : Scheme.{u}} (σ : T ⟶ Spec (.of R))
    (hσ : closedPoint R ∈ Set.range σ) {Y Z Y₀ Z₀ : Scheme.{u}} (pY : Y ⟶ Spec (.of R))
    (pZ : Z ⟶ Spec (.of R)) [IsFinite pY] [IsFinite pZ] (c : Y ⟶ Z) (hc : c ≫ pZ = pY)
    [Etale c] {ιY : Y₀ ⟶ Y} {qY : Y₀ ⟶ T} (hY : IsPullback ιY qY pY σ)
    {ιZ : Z₀ ⟶ Z} {qZ : Z₀ ⟶ T} (hZ : IsPullback ιZ qZ pZ σ)
    (c₀ : Y₀ ⟶ Z₀) (hc₀ : c₀ ≫ ιZ = ιY ≫ c) (hq : c₀ ≫ qZ = qY) [IsIso c₀] : IsIso c := by
  have : IsFinite (c ≫ pZ) := hc ▸ inferInstance
  have : IsFinite c := IsFinite.of_comp c pZ
  -- surjectivity
  have hsurj : Surjective c := by
    refine ⟨fun z ↦ ?_⟩
    have hU : IsClopen (Set.range c) :=
      ⟨c.isClosedMap.isClosed_range, c.isOpenMap.isOpen_range⟩
    have := eq_univ_of_isClopen_of_closedFibre_subset pZ hU (fun z hz ↦ ?_)
    · exact this.ge (Set.mem_univ z)
    · have hz' : z ∈ Set.range ιZ := by
        rw [isPullback_range_fst_eq hZ]
        change pZ z ∈ Set.range σ
        rw [Set.mem_singleton_iff.mp hz]; exact hσ
      obtain ⟨z₀, rfl⟩ := hz'
      refine ⟨ιY (inv c₀ z₀), ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hc₀, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc]
  -- universal injectivity, via the diagonal
  have : IsSeparated pY := inferInstance
  have : IsSeparated (c ≫ pZ) := hc ▸ inferInstance
  have : IsSeparated c := IsSeparated.of_comp c pZ
  have hW : IsPullback (ιY ≫ pullback.diagonal c) qY (pullback.fst c c ≫ pY) σ := by
    refine IsPullback.of_isLimit' ⟨by simp [hY.w]⟩ (PullbackCone.IsLimit.mk _
      (fun s ↦ hY.lift (s.fst ≫ pullback.fst c c) s.snd (by simpa using s.condition))
      (fun s ↦ ?_) (fun s ↦ by simp) (fun s m h₁ h₂ ↦ hY.hom_ext (by
        have := congr_arg (· ≫ pullback.fst c c) h₁
        simpa using this) (by simpa using h₂)))
    have h₂ : (s.fst ≫ pullback.snd c c) ≫ pY = s.snd ≫ σ := by
      have hs : s.fst ≫ pullback.fst c c ≫ pY = s.snd ≫ σ := by
        simpa only [Category.assoc] using s.condition
      calc (s.fst ≫ pullback.snd c c) ≫ pY = s.fst ≫ pullback.snd c c ≫ c ≫ pZ := by
            rw [hc, Category.assoc]
        _ = s.fst ≫ pullback.fst c c ≫ c ≫ pZ := by rw [pullback.condition_assoc]
        _ = s.snd ≫ σ := by rw [hc, hs]
    have key : hY.lift (s.fst ≫ pullback.fst c c) s.snd (by simpa using s.condition) =
        hY.lift (s.fst ≫ pullback.snd c c) s.snd h₂ := by
      rw [← cancel_mono c₀]
      apply hZ.hom_ext
      · simp only [Category.assoc, hc₀, IsPullback.lift_fst_assoc, pullback.condition]
      · simp [hq]
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      conv_lhs => rw [key]
      simp
  have hdiag : Surjective (pullback.diagonal c) := by
    refine ⟨fun w ↦ ?_⟩
    have : IsFinite (pullback.fst c c ≫ pY) := inferInstance
    have hU : IsClopen (Set.range (pullback.diagonal c)) :=
      ⟨(pullback.diagonal c).isClosedEmbedding.isClosed_range,
        (pullback.diagonal c).isOpenEmbedding.isOpen_range⟩
    have := eq_univ_of_isClopen_of_closedFibre_subset (pullback.fst c c ≫ pY) hU
      (fun w hw ↦ ?_)
    · exact this.ge (Set.mem_univ w)
    · have hw' : w ∈ Set.range (ιY ≫ pullback.diagonal c) := by
        rw [isPullback_range_fst_eq hW]
        change (pullback.fst c c ≫ pY) w ∈ Set.range σ
        rw [Set.mem_singleton_iff.mp hw]; exact hσ
      obtain ⟨y₀, rfl⟩ := hw'
      exact ⟨ιY y₀, rfl⟩
  have : UniversallyInjective c := (UniversallyInjective.iff_diagonal c).mpr hdiag
  exact isIso_of_etale_of_universallyInjective_of_surjective c

end ClosedFibre

section Stage1

open IsLocalRing

section General

variable {R : Type u} [CommRing R] [IsLocalRing R]

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.7, finite étale case over a local base `Spec R` over which finite étale algebras lift
from the residue field (`hlift`) and maps from finite étale algebras to finite algebras lift from
the closed fibre (`hB`), e.g. a complete noetherian or a strictly henselian local ring: along a
finite surjective `g : S' ⟶ Spec R`, every descent datum on a finite étale `S'`-scheme is
effective, with a finite étale descended scheme. -/
theorem DescentDatum.isEffective_of_isFinite_of_lift
    (hlift : ∀ (C : Type u) [CommRing C] [Algebra (R ⧸ maximalIdeal R) C]
      [Module.Finite (R ⧸ maximalIdeal R) C] [Algebra.Etale (R ⧸ maximalIdeal R) C],
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B), Module.Finite R B ∧ Algebra.Etale R B ∧
        Nonempty ((R ⧸ maximalIdeal R) ⊗[R] B ≃ₐ[R ⧸ maximalIdeal R] C))
    (hB : ∀ (B : Type u) [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.Etale R B]
      (T : Type u) [CommRing T] [Algebra R T] [Module.Finite R T], Function.Bijective
        fun f : B →ₐ[R] T ↦
          (Algebra.TensorProduct.includeRight : T →ₐ[R] (R ⧸ maximalIdeal R) ⊗[R] T).comp f)
    {S' Y : Scheme.{u}} {g : S' ⟶ Spec (.of R)} [IsFinite g] [Surjective g] {a : Y ⟶ S'}
    [IsFinite a] [Etale a] (D : DescentDatum g a) : D.IsEffective (@IsFinite ⊓ @Etale) := by
  let σ := specQuotient (maximalIdeal R)
  have hF : IsField (R ⧸ maximalIdeal R) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
  have hbot (x : PrimeSpectrum (R ⧸ maximalIdeal R)) : x.asIdeal = ⊥ := by
    refine eq_bot_iff.mpr fun r hr ↦ ?_
    by_contra h
    obtain ⟨r', hr'⟩ := hF.mul_inv_cancel h
    exact x.isPrime.ne_top (x.asIdeal.eq_top_of_isUnit_mem hr (IsUnit.of_mul_eq_one _ hr'))
  have : Subsingleton (Spec (.of (R ⧸ maximalIdeal R))) :=
    ⟨fun x y ↦ PrimeSpectrum.ext ((hbot x).trans (hbot y).symm)⟩
  have hσ : closedPoint R ∈ Set.range σ := by
    obtain ⟨x⟩ : Nonempty (PrimeSpectrum (R ⧸ maximalIdeal R)) := inferInstance
    refine ⟨x, PrimeSpectrum.ext ?_⟩
    change x.asIdeal.comap (Ideal.Quotient.mk _) = maximalIdeal R
    refine ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ x.isPrime.ne_top)
      fun r hr ↦ ?_).symm
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  -- effective descent on the closed fibre (IX.4.1)
  have ha₀ : etaleSeparatedFiniteType (pullback.snd a (pullback.fst g σ)) :=
    MorphismProperty.pullback_snd _ _ ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  obtain ⟨X₀, b₀, v₀, hb₀, hv₀, hact₀⟩ := (D.baseChange σ).isEffective_of_flat' ha₀
  have : Etale b₀ := hb₀.1.1
  have : IsFinite b₀ :=
    of_isPullback_of_descendsAlong (P := @IsFinite) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      hv₀.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  -- lift the descended scheme to a finite étale `Spec R`-scheme
  obtain ⟨B, _, _, hBf, hBe, ιX, hX⟩ :=
    exists_isPullback_of_finite_etale_of_lift (maximalIdeal R) hlift b₀
  let b : Spec (.of B) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have : Etale b := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr hBe)
  have : IsFinite b := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hBf)
  have hY := isPullback_baseChange_obj σ (g := g) (a := a)
  -- the projection `Y ⟶ Spec B`, lifting the closed fibre
  obtain ⟨v, ⟨hvb, hvι⟩, -⟩ :=
    existsUnique_hom_of_isPullback_of_bijective (maximalIdeal R) hY B (hB B) (v₀ ≫ ιX) (by
      rw [Category.assoc, hX.w, ← Category.assoc, hv₀.w, hY.w, Category.assoc])
  -- the square is cartesian: the comparison map is an isomorphism on the closed fibres
  let c : Y ⟶ pullback b g := pullback.lift v a hvb
  have : Etale (c ≫ pullback.snd b g) := by rw [pullback.lift_snd]; infer_instance
  have : Etale c := Etale.of_comp c (pullback.snd b g)
  have hZ := isPullback_pullbackMap_of_isPullback hX (IsPullback.of_hasPullback g σ)
  have : IsIso c := isIso_of_isIso_closedFibre σ hσ (a ≫ g) (pullback.snd b g ≫ g) c
    (by simp [c]) hY hZ hv₀.isoPullback.hom (by
      apply pullback.hom_ext
      · simp [c, b, σ, pullback.map, hvι]
      · simp [c, b, σ, pullback.map, pullback.condition]) (by simp)
  have hv : IsPullback v a b g :=
    IsPullback.of_iso_pullback ⟨hvb⟩ (asIso c) (by simp [c]) (by simp [c])
  -- compatibility with the descent datum, checked on the closed fibre of `Y ×_{Spec R} S'`
  have hact : D.act ≫ v = pullback.fst (a ≫ g) g ≫ v := by
    have hX'' := isPullback_baseChangeAux g a σ
    obtain ⟨f, -, huniq⟩ := existsUnique_hom_of_isPullback_of_bijective (maximalIdeal R) hX'' B
      (hB B)
      (DescentDatum.baseChangeAux g a σ ≫ D.act ≫ v) (by
        rw [Category.assoc, Category.assoc, hvb, reassoc_of% D.act_comp])
    have h₁ := huniq (D.act ≫ v) ⟨by rw [Category.assoc, hvb, reassoc_of% D.act_comp], rfl⟩
    have h₂ := huniq (pullback.fst (a ≫ g) g ≫ v) ⟨by
        rw [Category.assoc, hvb, pullback.condition], by
        have e₁ : DescentDatum.baseChangeAux g a σ ≫ D.act =
            (D.baseChange σ).act ≫ pullback.fst a (pullback.fst g σ) :=
          (pullback.lift_fst _ _ _).symm
        rw [reassoc_of% e₁, DescentDatum.baseChangeAux_fst_assoc, hvι, reassoc_of% hact₀]⟩
    rw [h₁, h₂]
  exact ⟨Spec (.of B), b, v, ⟨inferInstance, inferInstance⟩, hv, hact⟩

end General

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R]

/-- IX.4.7, finite étale case over a complete noetherian local base: along a finite surjective
`g : S' ⟶ Spec R`, every descent datum on a finite étale `S'`-scheme is effective, with a
finite étale descended scheme. -/
theorem DescentDatum.isEffective_of_isFinite_of_isAdicComplete {S' Y : Scheme.{u}}
    {g : S' ⟶ Spec (.of R)} [IsFinite g] [Surjective g] {a : Y ⟶ S'} [IsFinite a] [Etale a]
    (D : DescentDatum g a) : D.IsEffective (@IsFinite ⊓ @Etale) :=
  D.isEffective_of_isFinite_of_lift
    (fun C _ _ _ _ ↦ Algebra.Etale.exists_finite_etale_tensorQuotient_equiv (maximalIdeal R) C)
    (fun _ _ _ _ _ _ _ _ _ ↦ bijective_comp_includeRight_of_isAdicComplete (maximalIdeal R))

end Stage1

section Stage2

variable {S' S X' : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'}

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.7 for étale coverings over a locally noetherian base: along a finite surjective
`g : S' ⟶ S` with `S` locally noetherian, every descent datum on a finite étale `S'`-scheme is
effective, with a finite étale descended scheme. -/
theorem DescentDatum.isEffective_etaleCovering_of_isFinite [IsLocallyNoetherian S] [IsFinite g]
    [Surjective g] [IsFinite a] [Etale a] (D : DescentDatum g a) :
    D.IsEffective etaleCovering := by
  have ha : etaleFinitePresentation a := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hfp : D.IsEffective etaleFinitePresentation := by
    rw [D.isEffective_iff_forall_fromSpecCompletedStalk ha]
    intro x
    exact ((D.baseChange (fromSpecCompletedStalk S x)).isEffective_of_isFinite_of_isAdicComplete
      ).of_le fun _ _ f h ↦ have : IsFinite f := h.1; ⟨⟨h.2, inferInstance⟩, inferInstance⟩
  obtain ⟨X, b, v, hb, hv, hact⟩ := hfp
  have : Etale b := hb.1.1
  -- `X` is finite over `S`: it is proper, since `X' = X ×_S S'` is, and quasi-finite
  have : IsProper b := (isProper_iff_of_isPullback hv.flip).mp inferInstance
  have : LocallyQuasiFinite b := locallyQuasiFinite_of_formallyUnramified b
  exact ⟨X, b, v, ⟨.of_isProper_of_locallyQuasiFinite b, inferInstance⟩, hv, hact⟩

end Stage2


section Noetherian

open IsLocalRing

/-- A morphism which is universally closed on each member of a finite open cover of its source
is universally closed. -/
lemma universallyClosed_of_iSup_eq_top {ι : Type*} [Finite ι] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) [∀ i, UniversallyClosed ((U i).ι ≫ f)] :
    UniversallyClosed f := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have hsq (i : ι) : IsPullback ((i₁ ⁻¹ᵁ U i).ι ≫ f') (i₁ ∣_ U i) i₂ ((U i).ι ≫ f) :=
    ((isPullback_morphismRestrict i₁ (U i)).paste_vert H.flip).flip
  have hcl (i : ι) : IsClosedMap ((i₁ ⁻¹ᵁ U i).ι ≫ f') :=
    UniversallyClosed.universally_isClosedMap _ _ _ (hsq i)
  intro Z hZ
  have : f' '' Z = ⋃ i, ((i₁ ⁻¹ᵁ U i).ι ≫ f') '' ((i₁ ⁻¹ᵁ U i).ι ⁻¹' Z) := by
    ext y
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : i₁ x ∈ (⊤ : X.Opens) := trivial
      rw [← hU] at this
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
      exact ⟨i, ⟨x, hi⟩, hx, rfl⟩
    · rintro ⟨i, x, hx, rfl⟩
      exact ⟨_, hx, rfl⟩
  rw [this]
  exact isClosed_iUnion_of_finite fun i ↦ hcl i _ (hZ.preimage (i₁ ⁻¹ᵁ U i).ι.continuous)

/-- For a closed map `φ : Z ⟶ X` over `Spec R` and `O` the set of generizations of points of the
closed fibre of `X`, the preimage of `O` is the set of generizations of points of the closed fibre
of `Z`. -/
lemma preimage_generizations_closedFibre {R : Type u} [CommRing R] [IsLocalRing R]
    {X Z : Scheme.{u}} (p : X ⟶ Spec (.of R)) (φ : Z ⟶ X) (hφ : IsClosedMap φ) (z : Z) :
    (∃ y, φ z ⤳ y ∧ p y = closedPoint R) ↔ ∃ w, z ⤳ w ∧ (φ ≫ p) w = closedPoint R := by
  constructor
  · rintro ⟨y, hzy, hy⟩
    have hcl : IsClosed (φ '' closure {z}) := hφ _ isClosed_closure
    have : y ∈ φ '' closure {z} :=
      hzy.mem_closed hcl ⟨z, subset_closure rfl, rfl⟩
    obtain ⟨w, hw, rfl⟩ := this
    exact ⟨w, specializes_iff_mem_closure.mpr hw, hy⟩
  · rintro ⟨w, hzw, hw⟩
    exact ⟨φ w, hzw.map φ.continuous, hw⟩

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.7, proof: over a local base `Spec R`, let `g : S' ⟶ Spec R` be finite and `X'` étale,
separated and of finite type over `S'` with a descent datum. Suppose that every point `y` of the
closed fibre of `X'` has an open neighbourhood of generizations of `y` which is finite over
`Spec R` (`hW`; true if `R` is henselian, e.g. complete noetherian). Then the generizations of the
points of the closed fibre of `X'` form an open and closed subset, finite over `S'` and stable
under the descent datum. -/
theorem DescentDatum.exists_isStable_isFinite_of_forall {R : Type u} [CommRing R] [IsLocalRing R]
    {S' X' : Scheme.{u}} {g : S' ⟶ Spec (.of R)} [IsFinite g] {a : X' ⟶ S'} [Etale a]
    [IsSeparated a] [QuasiCompact a] (D : DescentDatum g a)
    (hW : ∀ y : X', (a ≫ g) y = closedPoint R →
      ∃ W : X'.Opens, y ∈ W ∧ (∀ z ∈ W, z ⤳ y) ∧ IsFinite (W.ι ≫ a ≫ g)) :
    ∃ O : X'.Opens, IsClosed (O : Set X') ∧ D.IsStable O ∧ IsFinite (O.ι ≫ a) ∧
      ∀ x : X', (a ≫ g) x = closedPoint R → x ∈ O := by
  classical
  have : LocallyQuasiFinite a := locallyQuasiFinite_of_formallyUnramified a
  have hfin : ((a ≫ g) ⁻¹' {closedPoint R}).Finite := (a ≫ g).finite_preimage_singleton _
  let ι := ↥((a ≫ g) ⁻¹' {closedPoint R})
  have : Finite ι := hfin.to_subtype
  choose W hyW hWsp hWfin using fun y : ι ↦ hW y.1 y.2
  let O : X'.Opens := ⨆ y, W y
  have hO (x : X') : x ∈ O ↔ ∃ y, x ⤳ y ∧ (a ≫ g) y = closedPoint R := by
    refine ⟨fun hx ↦ ?_, fun ⟨y, hxy, hy⟩ ↦ ?_⟩
    · obtain ⟨y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨y.1, hWsp y x hy, y.2⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy.mem_open (W _).isOpen (hyW _)⟩
  have hWcl (y : ι) : IsClosed (W y : Set X') := by
    have := hWfin y
    have : IsFinite (W y).ι := IsFinite.of_comp (W y).ι (a ≫ g)
    rw [← Scheme.Opens.range_ι]
    exact (W y).ι.isClosedMap.isClosed_range
  refine ⟨O, ?_, ?_, ?_, fun x hx ↦ (hO x).mpr ⟨x, specializes_rfl, hx⟩⟩
  · simp only [O, TopologicalSpace.Opens.coe_iSup]
    exact isClosed_iUnion_of_finite hWcl
  · -- stability: both preimages are the generizations of the closed fibre of `X' ×_S S'`
    have hfst : IsClosedMap (pullback.fst (a ≫ g) g) := (pullback.fst (a ≫ g) g).isClosedMap
    have hact : IsClosedMap D.act := by
      rw [← D.swapAct_fst]
      exact hfst.comp (asIso D.swapAct).hom.homeomorph.isClosedMap
    have hq : pullback.fst (a ≫ g) g ≫ a ≫ g = D.act ≫ a ≫ g := by
      rw [reassoc_of% D.act_comp, pullback.condition]
    ext z
    change D.act z ∈ O ↔ pullback.fst (a ≫ g) g z ∈ O
    rw [hO, hO, preimage_generizations_closedFibre _ _ hact,
      preimage_generizations_closedFibre _ _ hfst, hq]
  · have hle (y : ι) : W y ≤ O := le_iSup W y
    let U (y : ι) : O.toScheme.Opens := (X'.homOfLE (hle y)).opensRange
    have hU : ⨆ y, U y = ⊤ := by
      refine eq_top_iff.mpr fun x _ ↦ ?_
      obtain ⟨y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨y, ⟨⟨x.1, hy⟩, ?_⟩⟩
      apply O.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      rfl
    have (y : ι) : UniversallyClosed ((U y).ι ≫ O.ι ≫ a ≫ g) := by
      have := hWfin y
      have e : (U y).ι ≫ O.ι ≫ a ≫ g =
          (X'.homOfLE (hle y)).isoOpensRange.inv ≫ (W y).ι ≫ a ≫ g := by
        rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι,
          Scheme.homOfLE_ι_assoc]
      rw [e]
      infer_instance
    have : UniversallyClosed (O.ι ≫ a ≫ g) := universallyClosed_of_iSup_eq_top _ U hU
    have : IsProper (O.ι ≫ a ≫ g) := ⟨⟩
    have : IsFinite ((O.ι ≫ a) ≫ g) := by
      rw [Category.assoc]; exact .of_isProper_of_locallyQuasiFinite _
    exact IsFinite.of_comp (O.ι ≫ a) g

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R]

/-- IX.4.7, proof: over a complete noetherian local base `Spec R`, let `g : S' ⟶ Spec R` be
finite and `X'` étale, separated and of finite type over `S'` with a descent datum. The
generizations of the points of the closed fibre of `X'` form an open and closed subset, finite
over `S'` and stable under the descent datum. -/
theorem DescentDatum.exists_isStable_isFinite {S' X' : Scheme.{u}} {g : S' ⟶ Spec (.of R)}
    [IsFinite g] {a : X' ⟶ S'} [Etale a] [IsSeparated a] [QuasiCompact a]
    (D : DescentDatum g a) :
    ∃ O : X'.Opens, IsClosed (O : Set X') ∧ D.IsStable O ∧ IsFinite (O.ι ≫ a) ∧
      ∀ x : X', (a ≫ g) x = closedPoint R → x ∈ O := by
  have : LocallyQuasiFinite a := locallyQuasiFinite_of_formallyUnramified a
  exact D.exists_isStable_isFinite_of_forall fun y hy ↦
    exists_opens_forall_specializes_isFinite (a ≫ g) hy ((a ≫ g).finite_preimage_singleton _)

lemma withBot_enat_le_of_lt_succ {a : WithBot ℕ∞} {m : ℕ} (h : a < ((m + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ (m : WithBot ℕ∞) := by
  induction a with
  | bot => exact bot_le
  | coe a =>
    have h' : a < ((m : ℕ∞) + 1) := by exact_mod_cast h
    exact_mod_cast (ENat.lt_add_one_iff (ENat.natCast_ne_top m)).mp h'

/-- (Implementation) IX.4.7 over the complete noetherian local rings of dimension at most `n`. -/
def EffectiveFiniteDescentComplete (n : ℕ) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R], ringKrullDim R ≤ n →
    ∀ {S' X' : Scheme.{u}} (g : S' ⟶ Spec (.of R)) [IsFinite g] [Surjective g] (a : X' ⟶ S')
      [Etale a] [IsSeparated a] [QuasiCompact a] (D : DescentDatum g a), D.IsEffective @Etale

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.7, reduction to complete local rings (via IX.4.5): over a locally noetherian `S` whose
local rings have dimension at most `n`. -/
theorem DescentDatum.isEffective_of_isFinite_of_forall_stalk {n : ℕ}
    (H : EffectiveFiniteDescentComplete.{u} n) {S S' X' : Scheme.{u}} [IsLocallyNoetherian S]
    {g : S' ⟶ S} [IsFinite g] [Surjective g] {a : X' ⟶ S'} [Etale a] [IsSeparated a]
    [QuasiCompact a] (D : DescentDatum g a)
    (hdim : ∀ x : S, ringKrullDim (S.presheaf.stalk x) ≤ n) :
    D.IsEffective etaleFinitePresentation := by
  have ha : etaleFinitePresentation a := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  rw [D.isEffective_iff_forall_fromSpecCompletedStalk ha]
  intro x
  have hR := (IsLocalRing.ringKrullDim_adicCompletion_le (A := S.presheaf.stalk x)).trans
    (hdim x)
  exact (D.baseChange (fromSpecCompletedStalk S x)).isEffective_etaleFinitePresentation_of_etale
    (MorphismProperty.pullback_snd _ _ ha) (H _ hR _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.7 over complete noetherian local rings, by induction on the dimension. -/
theorem effectiveFiniteDescentComplete (n : ℕ) : EffectiveFiniteDescentComplete.{u} n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro R _ _ _ _ hR S' X' g _ _ a _ _ _ D
  obtain ⟨O, hOcl, hOst, hOfin, hOs⟩ := D.exists_isStable_isFinite
  let O₂ : X'.Opens := ⟨(O : Set X')ᶜ, hOcl.isOpen_compl⟩
  have hO₂st : D.IsStable O₂ := by
    ext z
    have := SetLike.ext_iff.mp hOst z
    change z ∈ D.act ⁻¹ᵁ O ↔ z ∈ pullback.fst (a ≫ g) g ⁻¹ᵁ O at this
    change D.act z ∉ O ↔ pullback.fst (a ≫ g) g z ∉ O
    exact not_congr this
  -- the finite part (IX.1.8 and IX.4.1 on the closed fibre)
  have hE₁ : (D.restrict O hOst).IsEffective @Etale :=
    (D.restrict O hOst).isEffective_of_isFinite_of_isAdicComplete.of_le fun _ _ _ h ↦ h.2
  obtain ⟨E₁⟩ := (DescentDatum.isEffective_iff_nonempty_descent etale).mp hE₁
  -- the part without points over the closed point (induction hypothesis)
  have hE₂ : (D.restrict O₂ hO₂st).IsEffective @Etale := by
    -- the points outside `O` lie over the punctured spectrum `U`
    let U : (Spec (.of R)).Opens :=
      ⟨{closedPoint R}ᶜ, (isClosed_singleton_closedPoint R).isOpen_compl⟩
    have hO₂U : O₂ ≤ (a ≫ g) ⁻¹ᵁ U := fun x hx hxs ↦ hx (hOs x hxs)
    have hst : D.IsStable ((a ≫ g) ⁻¹ᵁ U) := D.isStable_preimage U
    have hEU : (D.restrict ((a ≫ g) ⁻¹ᵁ U) hst).IsEffective @Etale := by
      rcases n with _ | m
      · -- dimension zero: `U` is empty
        have hUO : (a ≫ g) ⁻¹ᵁ U ≤ O := by
          intro x hx
          exfalso
          have hne : (a ≫ g) x ≠ closedPoint R := hx
          have hlt := ringKrullDim_stalk_lt_of_ne_closedPoint _ hne
          have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim ((Spec (.of R)).presheaf.stalk ((a ≫ g) x)) :=
            ringKrullDim_nonneg_of_nontrivial
          exact absurd (h0.trans_lt (hlt.trans_le hR)) (by simp)
        exact (DescentDatum.isEffective_iff_nonempty_descent etale).mpr
          ⟨E₁.restrictLE hst hOst hUO⟩
      · have hdimU (y : U) : ringKrullDim (U.toScheme.presheaf.stalk y) ≤ m := by
          rw [ringKrullDim_stalk_opens]
          exact withBot_enat_le_of_lt_succ
            ((ringKrullDim_stalk_lt_of_ne_closedPoint y.1 y.2).trans_le hR)
        have := (D.baseChange U.ι).isEffective_of_isFinite_of_forall_stalk
          (IH m (Nat.lt_succ_self m)) hdimU
        exact DescentDatum.isEffective_restrict_of_isEffective_baseChange rfl
          (this.of_le fun _ _ _ h ↦ h.1.1)
    obtain ⟨EU⟩ := (DescentDatum.isEffective_iff_nonempty_descent etale).mp hEU
    exact (DescentDatum.isEffective_iff_nonempty_descent etale).mpr
      ⟨EU.restrictLE hO₂st hst hO₂U⟩
  refine D.isEffective_of_iSup_eq_top (fun b : Bool ↦ if b then O else O₂) ?_
    (fun b ↦ by cases b <;> simpa) (fun b ↦ by cases b <;> simpa)
  refine eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
  by_cases hx : x ∈ O
  · exact ⟨true, by simpa using hx⟩
  · exact ⟨false, by simp only [Bool.false_eq_true, ite_false]; exact hx⟩

lemma exists_ringKrullDim_le_nat (A : Type*) [CommRing A] [FiniteRingKrullDim A] :
    ∃ n : ℕ, ringKrullDim A ≤ n := by
  have h := ringKrullDim_ne_top (R := A)
  induction h' : ringKrullDim A with
  | bot => exact ⟨0, bot_le⟩
  | coe e =>
    rw [h'] at h
    have he : e ≠ ⊤ := fun he ↦ h (by rw [he]; rfl)
    exact ⟨e.toNat, by exact_mod_cast (ENat.natCast_toNat he).symm.le⟩

variable {S' S X' : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'}

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.7 (locally noetherian base): let `g : S' ⟶ S` be finite and surjective, with `S` locally
noetherian (so that `g` is of finite presentation). Every descent datum relative to `g` on an
étale, separated `S'`-scheme of finite type is effective. -/
theorem DescentDatum.isEffective_of_isFinite [IsLocallyNoetherian S] [IsFinite g]
    [Surjective g] (D : DescentDatum g a) (ha : etaleSeparatedFiniteType a) :
    D.IsEffective etaleSeparatedFiniteType := by
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := ha
  have : Etale a := h₁
  have : IsSeparated a := h₂
  have : QuasiCompact a := h₃
  have ha' : etaleFinitePresentation a := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hfp : D.IsEffective etaleFinitePresentation := by
    rw [D.isEffective_iff_forall_fromSpecCompletedStalk ha']
    intro x
    obtain ⟨n, hn⟩ := exists_ringKrullDim_le_nat
      (AdicCompletion (maximalIdeal (S.presheaf.stalk x)) (S.presheaf.stalk x))
    exact (D.baseChange (fromSpecCompletedStalk S x)).isEffective_etaleFinitePresentation_of_etale
      (MorphismProperty.pullback_snd _ _ ha') (effectiveFiniteDescentComplete n _ hn _ _ _)
  exact D.isEffective_etaleSeparatedFiniteType_of_etale ⟨⟨h₁, h₂⟩, h₃⟩
    (hfp.of_le fun _ _ _ h ↦ h.1.1)

/-- IX.4.7 (locally noetherian base): a finite surjective morphism to a locally noetherian scheme
is an effective descent morphism for étale separated schemes of finite type. -/
theorem isEffectiveDescentMorphism_of_isFinite [IsLocallyNoetherian S] [IsFinite g]
    [Surjective g] : IsEffectiveDescentMorphism g etaleSeparatedFiniteType :=
  ⟨isDescentMorphism_of_isFinite, fun _ _ D ha ↦ D.isEffective_of_isFinite ha⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.4.10 (locally noetherian base): for `g : S' ⟶ S` finite, radicial and surjective with `S`
locally noetherian, base change is an equivalence from étale `S`-schemes to étale
`S'`-schemes. -/
theorem isEquivalence_pullback_etale_of_isFinite_of_isLocallyNoetherian [IsLocallyNoetherian S]
    [IsFinite g] [UniversallyInjective g] [Surjective g] :
    (MorphismProperty.Over.pullback @Etale ⊤ g).IsEquivalence :=
  isEquivalence_pullback_etale_of_isEffective fun _ _ _ D ↦
    D.isEffective_of_universallyInjective_of_affine fun U _ _ _ _ E ↦
      have : IsAffine U.1 := U.2
      have : IsAffine (pullback g U.1.ι) := isAffine_of_isAffineHom (pullback.snd g U.1.ι)
      (E.isEffective_of_isFinite ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩).of_le
        etaleSeparatedFiniteType_le_etale

end Noetherian

end SGA.SGA1.ExposeIX
