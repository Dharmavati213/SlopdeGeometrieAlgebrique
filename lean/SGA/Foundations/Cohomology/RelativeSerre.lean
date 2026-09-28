/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Coherent
import SGA.Foundations.Cohomology.TwistBaseChange
import SGA.Foundations.Cohomology.CechTransport
import SGA.Foundations.Projective.ProjectiveSpaceSpec
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Relative Serre vanishing on `ℙ(σ; S)`

Let `S` be a locally noetherian scheme, `σ` a finite type numbered by `e : Fin (r + 1) ≃ σ`, and
`F` a coherent module on `ℙ(σ; S) ≅ ℙʳ_S` (the projective space of `SGA.Foundations.Projective`,
with its twisting sheaf `𝒪(1)`).

* `ProjectiveSpace.affineChart e hW : Proj Γ(W)[x₀, …, x_r] ⟶ ℙ(σ; S)`: the chart over an affine
  open `W ⊆ S`, an open immersion with image `ℙ(σ; W)` (`opensRange_affineChart`) under which the
  standard opens and the twisting sheaves correspond (`affineChart_preimage_basicOpen`,
  `affineChart_cocycle`, using `CohomologyAux.proj_map_appLE_fracSection`).
* `ProjectiveSpace.exists_twist_H'_preimage_subsingleton`: `Hᵖ(ℙ(σ; W), F(n)) = 0` for `p > 0` and
  `n ≫ 0` (Serre's vanishing theorem on `Proj Γ(W)[xᵢ]`, transported along the chart by Čech
  complexes).
* `ProjectiveSpace.exists_twist_H'_preimage_cechOpen_subsingleton`: the same, uniformly over the
  finite intersections of a finite affine family of opens of `S`; this is the vanishing of
  `Rᵖ π_* F(n)` for `n ≫ 0` (EGA III 2.2.1 (ii), relative form).
-/

universe u
open CategoryTheory TopologicalSpace Opposite HomogeneousLocalization MvPolynomial Limits

namespace AlgebraicGeometry

namespace CohomologyAux

open Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

set_option backward.isDefEq.respectTransparency false in
lemma proj_map_appLE_fracSection {d : ℕ} {a b : A} (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : U ≤ basicOpen 𝒜 b) (V : (Proj ℬ).Opens)
    (hV : V ≤ map f hf ⁻¹ᵁ U) :
    (map f hf).appLE U V hV (fracSection 𝒜 ha hb U hU) =
      fracSection ℬ (GradedRingHom.map_mem f ha) (GradedRingHom.map_mem f hb) V
        (show V ≤ basicOpen ℬ (f b) from hV.trans ((map f hf).preimage_mono hU)) := by
  refine section_ext (𝒜 := ℬ) fun x ↦ ?_
  rw [val_fracSection_apply]
  change (HomogeneousLocalization.localRingHom f _ _ rfl
    ((fracSection 𝒜 ha hb U hU).1 ⟨ProjectiveSpectrum.comap f hf x.1, hV x.2⟩)).val = _
  rw [HomogeneousLocalization.val_localRingHom, val_fracSection_apply, Localization.mk_eq_mk']
  erw [Localization.localRingHom_mk']
  rw [Localization.mk_eq_mk']
  rfl


lemma fracSection_congr {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} {a a' b b' : A} (ha : a ∈ 𝒜 d) (ha' : a' ∈ 𝒜 d)
    (hb : b ∈ 𝒜 d) (hb' : b' ∈ 𝒜 d) (haa : a = a') (hbb : b = b') (U : (Proj 𝒜).Opens)
    (hU : U ≤ basicOpen 𝒜 b) (hU' : U ≤ basicOpen 𝒜 b') :
    fracSection 𝒜 ha hb U hU = fracSection 𝒜 ha' hb' U hU' := by
  subst haa; subst hbb; rfl

lemma presheaf_map_appLE_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) {V V' : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V) (x : Γ(Y, U)) :
    X.presheaf.map (homOfLE h).op (f.appLE U V e x) = f.appLE U V' (h.trans e) x := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

lemma appLE_of_eq {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) : f.appLE U V e x = f'.appLE U V (h ▸ e) x := by
  subst h; rfl

end CohomologyAux

open ProjectiveSpace

variable {S : Scheme.{u}} {r : ℕ} {σ : Type u} (e : Fin (r + 1) ≃ σ) {W : S.Opens}
  (hW : IsAffineOpen W)

/-- The chart `Proj Γ(W)[x₀, …, x_r] ≅ ℙ(σ; W) ⊆ ℙ(σ; S)` over an affine open `W` of `S`, for a
numbering `e : Fin (r + 1) ≃ σ` of the variables. -/
noncomputable def ProjectiveSpace.affineChart :
    Proj (grading (Fin (r + 1)) Γ(S, W)) ⟶ ℙ(σ; S) :=
  (projRenameIso (R := Γ(S, W)) e).hom ≫ (isoProj σ Γ(S, W)).hom ≫ map S hW.fromSpec

instance : IsOpenImmersion (ProjectiveSpace.affineChart e hW) := by
  have : IsOpenImmersion (map (σ := σ) S hW.fromSpec) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_map hW.fromSpec).flip
      inferInstance
  unfold ProjectiveSpace.affineChart
  infer_instance

lemma ProjectiveSpace.affineChart_preimage_basicOpen (k : Fin (r + 1)) :
    ProjectiveSpace.affineChart e hW ⁻¹ᵁ basicOpen S (e k) =
      Proj.basicOpen (grading (Fin (r + 1)) Γ(S, W)) (X k) := by
  rw [ProjectiveSpace.affineChart, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    map_preimage_basicOpen, isoProj_hom_preimage_basicOpen]
  change Proj.map _ _ ⁻¹ᵁ _ = _
  rw [Proj.map_preimage_basicOpen]
  congr 1
  simp

lemma ProjectiveSpace.affineChart_toProj :
    ProjectiveSpace.affineChart e hW ≫ toProj σ S =
      (projRenameIso (R := Γ(S, W)) e).hom ≫ projToProjInt σ Γ(S, W) := by
  simp [ProjectiveSpace.affineChart]

lemma ProjectiveSpace.opensRange_affineChart :
    (ProjectiveSpace.affineChart e hW).opensRange = (ℙ(σ; S) ↘ S) ⁻¹ᵁ W := by
  have : IsOpenImmersion (map (σ := σ) S hW.fromSpec) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_map hW.fromSpec).flip
      inferInstance
  have e1 := Scheme.Hom.opensRange_comp_of_isIso (projRenameIso (R := Γ(S, W)) e).hom
    ((isoProj σ Γ(S, W)).hom ≫ map S hW.fromSpec)
  have e2 := Scheme.Hom.opensRange_comp_of_isIso (isoProj σ Γ(S, W)).hom (map S hW.fromSpec)
  have h := (isPullback_map (σ := σ) hW.fromSpec)
  have e3 : (map (σ := σ) S hW.fromSpec).opensRange = (ℙ(σ; S) ↘ S) ⁻¹ᵁ W := by
    apply TopologicalSpace.Opens.ext
    rw [Scheme.Hom.coe_opensRange, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr (inferInstance : Surjective h.isoPullback.hom).surj, Set.image_univ,
      IsOpenImmersion.range_pullbackFst, hW.opensRange_fromSpec]
  exact e1.trans (e2.trans e3)

end AlgebraicGeometry

namespace AlgebraicGeometry

open ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} {r : ℕ} {σ : Type u} (e : Fin (r + 1) ≃ σ) {W : S.Opens}
  (hW : IsAffineOpen W)

lemma ProjectiveSpace.affineChart_cocycle (i j : Fin (r + 1))
    (h : Proj.basicOpen (homogeneousSubmodule (Fin (r + 1)) Γ(S, W)) (X i) ⊓
        Proj.basicOpen (homogeneousSubmodule (Fin (r + 1)) Γ(S, W)) (X j) ≤
      ((twistingSheaf σ S).pullback (affineChart e hW)).U (e i) ⊓
        ((twistingSheaf σ S).pullback (affineChart e hW)).U (e j)) :
    (Proj (grading (Fin (r + 1)) Γ(S, W))).presheaf.map (homOfLE h).op
      (((twistingSheaf σ S).pullback (affineChart e hW)).g (e i) (e j)).val =
      ((projectiveSpace.twistingBundle (Fin (r + 1)) Γ(S, W)).g (ULift.up i) (ULift.up j)).val := by
  change (Proj (grading (Fin (r + 1)) Γ(S, W))).presheaf.map (homOfLE h).op
      ((affineChart e hW).appLE _ _ _ ((toProj _ S).appLE _ _ _
        (Proj.fracSection _ (X_mem_grading (e j)) (X_mem_grading (e i)) _ inf_le_left))) =
    Proj.fracSection _ (projectiveSpace.X_mem j) (projectiveSpace.X_mem i) _ inf_le_left
  simp only [← ConcreteCategory.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE]
  erw [CohomologyAux.presheaf_map_appLE_apply]
  refine (CohomologyAux.appLE_of_eq (affineChart_toProj e hW) _ _ _ _).trans ?_
  have hcomp : (projRenameIso (R := Γ(S, W)) e).hom ≫ projToProjInt σ Γ(S, W) =
      Proj.map ((gradingRename (R := Γ(S, W)) e.symm).comp (gradingMap _ (intCast Γ(S, W))))
        (HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_map _)
          (irrelevant_le_map_rename _)) :=
    (Proj.map_comp _ _ _ _).symm
  refine (CohomologyAux.appLE_of_eq hcomp _ _ _ _).trans ?_
  refine (CohomologyAux.proj_map_appLE_fracSection _ _ _ _ _ _ _ _).trans ?_
  exact CohomologyAux.fracSection_congr _ _ _ _ (by simp) (by simp) _ _ _

end AlgebraicGeometry

namespace AlgebraicGeometry

open ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} {σ : Type u}

/-- A non-empty finite type has a numbering by some `Fin (r + 1)`. -/
lemma CohomologyAux.exists_equiv_fin_succ (σ : Type*) [Finite σ] [Nonempty σ] :
    ∃ r : ℕ, Nonempty (Fin (r + 1) ≃ σ) :=
  ⟨Nat.card σ - 1, ⟨(finCongr (Nat.sub_add_cancel Nat.card_pos)).trans (Finite.equivFin σ).symm⟩⟩

/-- **Relative Serre vanishing over an affine open** (EGA III 2.2.1 (ii) over `W`): for `F`
coherent on `ℙ(σ; S)` (`S` locally noetherian, `σ` numbered by `e : Fin (r + 1) ≃ σ`) and
`W ⊆ S` affine, `Hᵖ(ℙ(σ; W), F(n)) = 0` for `p > 0` and `n ≫ 0`. -/
theorem ProjectiveSpace.exists_twist_H'_preimage_subsingleton [IsLocallyNoetherian S]
    [Finite σ] [Nonempty σ] (F : ℙ(σ; S).Modules) [hF : F.IsCoherent] {W : S.Opens}
    (hW : IsAffineOpen W) :
    ∃ n₀ : ℤ, ∀ n ≥ n₀, ∀ q : ℕ, Subsingleton
      (((twistingSheaf σ S).twist F n).H' (q + 1) ((ℙ(σ; S) ↘ S) ⁻¹ᵁ W)) := by
  obtain ⟨r, ⟨e⟩⟩ := CohomologyAux.exists_equiv_fin_succ σ
  have hR : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let L := twistingSheaf σ S
  let g := affineChart e hW
  have hgo : IsOpenImmersion g := inferInstanceAs (IsOpenImmersion (affineChart e hW))
  have hFq : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have hFt : F.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  let F' := F.restrict g
  have hF'q : F'.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor g F
  have hF't : F'.IsFiniteType := Scheme.Modules.isFiniteType_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback g).app F).symm
  have hF' : F'.IsCoherent := ⟨hF'q, hF't⟩
  obtain ⟨n₀, hn₀⟩ := projectiveSpace.exists_H_twist_subsingleton
    (@projectiveSpace.IsStdFinite.of_isCoherent (Fin (r + 1)) Γ(S, W) _ F' hF')
  refine ⟨n₀, fun n hn q ↦ ?_⟩
  let τ := projectiveSpace.twistingBundle (Fin (r + 1)) Γ(S, W)
  let e' : τ.ι ≃ (L.pullback g).ι := Equiv.ulift.trans e
  have hU : ∀ i, (L.pullback g).U (e' i) = τ.U i := fun i ↦
    affineChart_preimage_basicOpen e hW i.down
  let e1 : (L.twist F n).restrict g ≅ τ.twist F' n :=
    L.twistRestrictPullbackIso F n g ≪≫
      Scheme.LineBundle.twistTransferIso F' n τ (L.pullback g) e' hU
        (fun i j ↦ affineChart_cocycle e hW i.down j.down _)
  have h0 := hn₀ n hn q
  have h1 : Subsingleton (((L.twist F n).restrict g).H' (q + 1) ⊤) :=
    @Scheme.Modules.subsingleton_H'_of_iso _ _ _ _ _ e1.symm h0
  -- Leray on `Proj Γ(W)[x]` for the standard cover
  let M := (L.twist F n).restrict g
  have hMq : M.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor g _
  have hacyc : ∀ {m : ℕ} (x : Fin (m + 1) → Fin (r + 1)) (q' : ℕ),
      Subsingleton (M.toAbSheaf.H' (q' + 1)
        (TopCat.Presheaf.cechOpen (projectiveSpace.stdCover (Fin (r + 1)) Γ(S, W)) x)) :=
    fun x q' ↦ M.H'_subsingleton_of_isAffineOpen (by
      have := Proj.isAffineOpen_basicOpen _ _
        (projectiveSpace.prodX_mem (A := Γ(S, W)) (Finset.univ.image x))
        (projectiveSpace.image_nonempty x).card_pos
      rw [← projectiveSpace.cechOpen_stdCover] at this
      exact this) q'
  have hex := (TopCat.Sheaf.cechComplex_exactAt_iff_subsingleton_H'
    (X := (Proj (grading (Fin (r + 1)) Γ(S, W))).carrier)
    (projectiveSpace.stdCover (Fin (r + 1)) Γ(S, W)) q M.toAbSheaf hacyc).mpr (by
      convert h1 using 3
      exact projectiveSpace.iSup_stdCover _ _)
  -- transport to `ℙ(σ; S)` along the chart
  have hex' := (CohomologyAux.restrictCechTransport g (L.twist F n)
    (projectiveSpace.stdCover (Fin (r + 1)) Γ(S, W))).exactAt q hex
  have hacyc' : ∀ {m : ℕ} (x : Fin (m + 1) → Fin (r + 1)) (q' : ℕ),
      Subsingleton ((L.twist F n).toAbSheaf.H' (q' + 1)
        (TopCat.Presheaf.cechOpen
          (fun k ↦ g ''ᵁ projectiveSpace.stdCover (Fin (r + 1)) Γ(S, W) k) x)) := fun x q' ↦ by
    have e := CohomologyAux.image_cechOpen g (projectiveSpace.stdCover (Fin (r + 1)) Γ(S, W)) x
    have ha0 := Proj.isAffineOpen_basicOpen _ _
      (projectiveSpace.prodX_mem (A := Γ(S, W)) (Finset.univ.image x))
      (projectiveSpace.image_nonempty x).card_pos
    rw [← projectiveSpace.cechOpen_stdCover] at ha0
    have ha : IsAffineOpen (g ''ᵁ TopCat.Presheaf.cechOpen
        (projectiveSpace.stdCover (Fin (r + 1)) Γ(S, W)) x) :=
      @IsAffineOpen.image_of_isOpenImmersion _ _ _ ha0 g hgo
    rw [e] at ha
    exact (L.twist F n).H'_subsingleton_of_isAffineOpen ha q'
  have h2 := (TopCat.Sheaf.cechComplex_exactAt_iff_subsingleton_H'
    (fun k ↦ g ''ᵁ projectiveSpace.stdCover (Fin (r + 1)) Γ(S, W) k) q (L.twist F n).toAbSheaf
    hacyc').mp hex'
  have e : (⨆ k, g ''ᵁ projectiveSpace.stdCover (Fin (r + 1)) Γ(S, W) k) =
      (ℙ(σ; S) ↘ S) ⁻¹ᵁ W := by
    refine (Scheme.Hom.image_iSup g
      (projectiveSpace.stdCover (Fin (r + 1)) Γ(S, W))).symm.trans ?_
    convert (Scheme.Hom.image_top_eq_opensRange g).trans (opensRange_affineChart e hW) using 2
    exact projectiveSpace.iSup_stdCover _ _
  rw [e] at h2
  exact h2

lemma CohomologyAux.cechOpen_eq_iInf_image {T : Type*} [TopologicalSpace T] {ι : Type*}
    [DecidableEq ι] (V : ι → TopologicalSpace.Opens T) {m : ℕ} (x : Fin m → ι) :
    TopCat.Presheaf.cechOpen (X := TopCat.of T) V x = ⨅ i ∈ Finset.univ.image x, V i := by
  refine le_antisymm (le_iInf₂ fun i hi ↦ ?_) (le_iInf fun a ↦ ?_)
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
    exact TopCat.Presheaf.cechOpen_le _ x a
  · exact iInf₂_le (x a) (Finset.mem_image_of_mem x (Finset.mem_univ a))

/-- **Relative Serre vanishing** (EGA III 2.2.1 (ii), relative form): let `S` be locally
noetherian, `V₁, …, V_N` affine opens of `S` all of whose finite intersections are affine, and `F`
coherent on `ℙʳ_S`. Then there is `n₀` with `Hᵖ(ℙʳ_{V_x}, F(n)) = 0` for all `p > 0`, `n ≥ n₀` and
all finite intersections `V_x` of the `Vᵢ`; i.e. `Rᵖ π_* F(n) = 0` over `⋃ Vᵢ`. -/
theorem ProjectiveSpace.exists_twist_H'_preimage_cechOpen_subsingleton [IsLocallyNoetherian S]
    [Finite σ] [Nonempty σ] (F : ℙ(σ; S).Modules) [F.IsCoherent] {N : ℕ} (V : Fin N → S.Opens)
    (hV : ∀ {m : ℕ} (x : Fin (m + 1) → Fin N), IsAffineOpen (TopCat.Presheaf.cechOpen V x)) :
    ∃ n₀ : ℤ, ∀ n ≥ n₀, ∀ {m : ℕ} (x : Fin (m + 1) → Fin N) (q : ℕ), Subsingleton
      (((twistingSheaf σ S).twist F n).H' (q + 1)
        ((ℙ(σ; S) ↘ S) ⁻¹ᵁ TopCat.Presheaf.cechOpen V x)) := by
  classical
  have key (T : Finset (Fin N)) : ∃ n₀ : ℕ, ∀ {m : ℕ} (x : Fin (m + 1) → Fin N),
      Finset.univ.image x = T → ∀ n ≥ (n₀ : ℤ), ∀ q : ℕ, Subsingleton
        (((twistingSheaf σ S).twist F n).H' (q + 1)
          ((ℙ(σ; S) ↘ S) ⁻¹ᵁ TopCat.Presheaf.cechOpen V x)) := by
    by_cases hT : ∃ (m : ℕ) (x : Fin (m + 1) → Fin N), Finset.univ.image x = T
    · obtain ⟨m, x, hx⟩ := hT
      obtain ⟨n₀, hn₀⟩ := ProjectiveSpace.exists_twist_H'_preimage_subsingleton F (hV x)
      refine ⟨n₀.toNat, fun y hy n hn q ↦ ?_⟩
      have e : TopCat.Presheaf.cechOpen V y = TopCat.Presheaf.cechOpen V x := by
        rw [CohomologyAux.cechOpen_eq_iInf_image, CohomologyAux.cechOpen_eq_iInf_image, hx, hy]
      rw [e]
      exact hn₀ n (le_trans (Int.self_le_toNat n₀) hn) q
    · exact ⟨0, fun x hx ↦ absurd ⟨_, x, hx⟩ hT⟩
  choose n₀ hn₀ using key
  refine ⟨(Finset.univ.sup n₀ : ℕ), fun n hn m x q ↦ ?_⟩
  refine hn₀ (Finset.univ.image x) x rfl n (le_trans ?_ hn) q
  exact_mod_cast Finset.le_sup (f := n₀) (Finset.mem_univ _)

end AlgebraicGeometry
