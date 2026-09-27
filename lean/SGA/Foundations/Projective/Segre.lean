/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Projective.Morphisms
import SGA.Foundations.Projective.ProjectiveSpaceSpec

/-!
# The Segre embedding

The Segre morphism `ℙ(σ; S) ×_S ℙ(τ; S) ⟶ ℙ(σ × τ; S)`, `(x, y) ↦ (xᵢ yⱼ)`, is a closed
immersion (EGA II 4.3.1, Hartshorne Ex. II.3.16). We construct it over `ℤ` as the morphism
`Proj ℤ[σ] × Proj ℤ[τ] ⟶ Proj ℤ[σ × τ]` defined by the sections `xᵢ ⊗ yⱼ` of
`𝒪(1, 1) = p₁^* 𝒪(1) ⊗ p₂^* 𝒪(1)` (`ToProj`), check that it is a closed immersion on the charts
`zᵢⱼ ≠ 0`, where it has the retraction `(zₗₘ / zᵢⱼ) ↦ (xₗ / xᵢ, yₘ / yⱼ)`, and base change to `S`.
As a consequence, H-projective and H-quasi-projective morphisms are stable under composition
(EGA II 5.5.5 (ii), Hartshorne Ex. II.4.9).

## Main definitions and results

- `Scheme.LineBundle.sections.tmul`: tensor products of sections of line bundles (for
  `Scheme.LineBundle.tensor` from `SGA.Foundations.Ample`), with `nonvanishingLocus_tmul`.
- `AlgebraicGeometry.Proj.ι_comp_eq`: a morphism to `Proj A`, restricted to an open subset mapping
  to `D₊(t)`, is given by the ring homomorphism `A_(t) → Γ(D₊(t)) → Γ(V)`.
- `AlgebraicGeometry.ProjectiveSpace.segreInt`, `ProjectiveSpace.isClosedImmersion_segreInt`:
  the Segre embedding over `ℤ`.
- `AlgebraicGeometry.ProjectiveSpace.segre`: the Segre embedding
  `ℙ(σ; ℙ(τ; S)) = ℙ(σ; S) ×_S ℙ(τ; S) ⟶ ℙ(σ × τ; S)` over `S`, a closed immersion over `S`.
- `AlgebraicGeometry.IsHProjective.comp`, `IsHQuasiProjective.comp`: stability under composition.
-/

universe u

open CategoryTheory Limits MvPolynomial HomogeneousLocalization Opposite

namespace AlgebraicGeometry

namespace Scheme.LineBundle

variable {X : Scheme.{u}} (L M : X.LineBundle)

set_option backward.isDefEq.respectTransparency false in
lemma tmul_compat {n : ℕ} (s : L.sections n) (t : M.sections n) (p q : L.ι × M.ι) :
    X.presheaf.map (homOfLE (inf_le_left : L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤
        L.U p.1 ⊓ M.U p.2)).op
      (X.presheaf.map (homOfLE (inf_le_left : L.U p.1 ⊓ M.U p.2 ≤ L.U p.1)).op (s.1 p.1) *
        X.presheaf.map (homOfLE (inf_le_right : L.U p.1 ⊓ M.U p.2 ≤ M.U p.2)).op (t.1 p.2)) =
      (L.tensorG M p q : Γ(X, _)) ^ n *
        X.presheaf.map (homOfLE (inf_le_right : L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤
          L.U q.1 ⊓ M.U q.2)).op
          (X.presheaf.map (homOfLE (inf_le_left : L.U q.1 ⊓ M.U q.2 ≤ L.U q.1)).op (s.1 q.1) *
            X.presheaf.map (homOfLE (inf_le_right : L.U q.1 ⊓ M.U q.2 ≤ M.U q.2)).op
              (t.1 q.2)) := by
  have hs := congrArg (X.presheaf.map (homOfLE (inf_inf_le_left :
    L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ L.U p.1 ⊓ L.U q.1)).op).hom (s.2 p.1 q.1)
  have ht := congrArg (X.presheaf.map (homOfLE (inf_inf_le_right :
    L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ M.U p.2 ⊓ M.U q.2)).op).hom (t.2 p.2 q.2)
  simp only [map_mul, map_pow, ← CommRingCat.comp_apply, ← Functor.map_comp] at hs ht
  simp only [tensorG, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul, mul_pow,
    ← CommRingCat.comp_apply, ← Functor.map_comp]
  rw [mul_mul_mul_comm]
  exact congrArg₂ (· * ·) hs ht

/-- The product `s ⊗ t` of sections of `L^{⊗n}` and `M^{⊗n}`, a section of `(L ⊗ M)^{⊗n}`. -/
noncomputable def sections.tmul {n : ℕ} (s : L.sections n) (t : M.sections n) :
    (L.tensor M).sections n :=
  ⟨fun (p : L.ι × M.ι) ↦
      X.presheaf.map (homOfLE (inf_le_left : L.U p.1 ⊓ M.U p.2 ≤ L.U p.1)).op (s.1 p.1) *
      X.presheaf.map (homOfLE (inf_le_right : L.U p.1 ⊓ M.U p.2 ≤ M.U p.2)).op (t.1 p.2),
    fun p q ↦ L.tmul_compat M s t p q⟩

lemma nonvanishingLocus_tmul {n : ℕ} (s : L.sections n) (t : M.sections n) :
    (L.tensor M).nonvanishingLocus (sections.tmul L M s t) =
      L.nonvanishingLocus s ⊓ M.nonvanishingLocus t := by
  simp only [nonvanishingLocus, iSup_inf_iSup]
  change ⨆ p : L.ι × M.ι, X.basicOpen (_ * _) = _
  refine iSup_congr fun p ↦ ?_
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_res, Scheme.basicOpen_res]
  apply le_antisymm
  · exact inf_le_inf inf_le_right inf_le_right
  · exact le_inf (le_inf (le_inf (inf_le_left.trans (X.basicOpen_le _))
      (inf_le_right.trans (X.basicOpen_le _))) inf_le_left)
      (le_inf (le_inf (inf_le_left.trans (X.basicOpen_le _))
      (inf_le_right.trans (X.basicOpen_le _))) inf_le_right)

end Scheme.LineBundle

lemma Scheme.Hom.appLE_map_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V₁ V₂ V₃ : X.Opens} (e : V₁ ≤ f ⁻¹ᵁ U) (i : V₂ ≤ V₁) (j : V₃ ≤ V₂) (e' : V₃ ≤ f ⁻¹ᵁ U)
    (x : Γ(Y, U)) :
    X.presheaf.map (homOfLE j).op (X.presheaf.map (homOfLE i).op (f.appLE U V₁ e x)) =
      f.appLE U V₃ e' x := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
    Scheme.Hom.appLE_map]

namespace Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- The inclusion of `D₊(t)` into `Proj A` is `D₊(t) ≅ Spec A_(t) ⟶ Proj A`. -/
lemma basicOpen_ι_eq {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) (hd : 0 < d) :
    (basicOpen 𝒜 t).ι = (basicOpen 𝒜 t).toSpecΓ ≫
      Spec.map (awayToSection 𝒜 t) ≫ awayι 𝒜 t ht hd := by
  rw [← basicOpenIsoSpec_inv_ι 𝒜 t ht hd, ← Category.assoc,
    show (basicOpen 𝒜 t).toSpecΓ ≫ Spec.map (awayToSection 𝒜 t) =
      (basicOpenIsoSpec 𝒜 t ht hd).hom from (basicOpenIsoSpec_hom 𝒜 t ht hd).symm,
    Iso.hom_inv_id_assoc]

/-- A morphism `g : Y ⟶ Proj A`, restricted to an open subset `V` mapping to `D₊(t)`, is
`V ⟶ Spec Γ(V) ⟶ Spec A_(t) = D₊(t)`, given by the ring homomorphism
`A_(t) → Γ(D₊(t)) → Γ(V)`. -/
lemma ι_comp_eq {Y : Scheme.{u}} (g : Y ⟶ Proj 𝒜) {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) (hd : 0 < d)
    (V : Y.Opens) (h : V ≤ g ⁻¹ᵁ basicOpen 𝒜 t) :
    V.ι ≫ g = V.toSpecΓ ≫ Spec.map (awayToSection 𝒜 t ≫ g.appLE (basicOpen 𝒜 t) V h) ≫
      awayι 𝒜 t ht hd := by
  rw [← Y.homOfLE_ι h, Category.assoc, ← morphismRestrict_ι, basicOpen_ι_eq 𝒜 ht hd,
    ← Scheme.Opens.toSpecΓ_naturality_assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  rfl

variable {𝒜}

set_option backward.isDefEq.respectTransparency false in
/-- The section of `D₊(t)` defined by `a / tⁿ ∈ A_(t)` is `fracSection`. -/
lemma awayToSection_mk {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayToSection 𝒜 t (Away.mk 𝒜 ht n a ha) =
      fracSection 𝒜 ha (SetLike.pow_mem_graded n ht) (basicOpen 𝒜 t)
        (basicOpen_le_basicOpen_pow 𝒜 t n) := by
  refine section_ext 𝒜 fun x ↦ ?_
  rw [val_fracSection_apply]
  refine (ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 t _ x).trans ?_
  rw [Away.val_mk, Localization.mk_eq_mk', Localization.mk_eq_mk', IsLocalization.map_mk']
  rfl

end Proj

namespace ProjectiveSpace

open Scheme.LineBundle

set_option hygiene false in
local notation3 "ℤ'" => ULift.{u} ℤ

lemma ringHom_ext_uliftInt {R : Type*} [Ring R] (f g : ULift.{u} ℤ →+* R) : f = g := by
  have : f.comp ULift.ringEquiv.symm.toRingHom = g.comp ULift.ringEquiv.symm.toRingHom :=
    RingHom.ext_int _ _
  ext ⟨n⟩
  exact DFunLike.congr_fun this n

variable (σ τ : Type u)

/-- Serre's twisting sheaf `𝒪(1)` on `Proj ℤ[σ]`. -/
noncomputable abbrev twistingSheafInt : (Proj (grading σ ℤ')).LineBundle :=
  Proj.twistingSheaf (grading σ ℤ') X X_mem_grading (iSup_basicOpen_X σ ℤ')

/-- The homogeneous coordinate `xᵢ` as a section of `𝒪(1)` on `Proj ℤ[σ]`. -/
noncomputable abbrev coordInt (i : σ) : (twistingSheafInt σ).sections 1 :=
  Proj.twistingSheaf.homogeneousSection X X_mem_grading (iSup_basicOpen_X σ ℤ') (X_mem_grading i)

/-- `Proj ℤ[σ] × Proj ℤ[τ]`. -/
noncomputable abbrev segreSource : Scheme.{u} :=
  pullback (terminal.from (Proj (grading σ ℤ'))) (terminal.from (Proj (grading τ ℤ')))

/-- The first projection of `Proj ℤ[σ] × Proj ℤ[τ]`. -/
noncomputable abbrev segreFst : segreSource σ τ ⟶ Proj (grading σ ℤ') :=
  pullback.fst _ _

/-- The second projection of `Proj ℤ[σ] × Proj ℤ[τ]`. -/
noncomputable abbrev segreSnd : segreSource σ τ ⟶ Proj (grading τ ℤ') :=
  pullback.snd _ _

/-- The line bundle `𝒪(1, 1) = p₁^* 𝒪(1) ⊗ p₂^* 𝒪(1)` on `Proj ℤ[σ] × Proj ℤ[τ]`. -/
noncomputable def segreBundle : (segreSource σ τ).LineBundle :=
  ((twistingSheafInt σ).pullback (segreFst σ τ)).tensor
    ((twistingSheafInt τ).pullback (segreSnd σ τ))

/-- The sections `xᵢ ⊗ yⱼ` of `𝒪(1, 1)`. -/
noncomputable def segreSection (a : σ × τ) : (segreBundle σ τ).sections 1 :=
  sections.tmul _ _ ((coordInt σ a.1).pullback _ (segreFst σ τ))
    ((coordInt τ a.2).pullback _ (segreSnd σ τ))

variable {σ τ}

lemma nonvanishingLocus_segreSection (a : σ × τ) :
    (segreBundle σ τ).nonvanishingLocus (segreSection σ τ a) =
      segreFst σ τ ⁻¹ᵁ Proj.basicOpen _ (X a.1) ⊓
        segreSnd σ τ ⁻¹ᵁ Proj.basicOpen _ (X a.2) := by
  refine (nonvanishingLocus_tmul _ _ _ _).trans ?_
  rw [nonvanishingLocus_pullback, nonvanishingLocus_pullback,
    Proj.twistingSheaf.nonvanishingLocus_homogeneousSection,
    Proj.twistingSheaf.nonvanishingLocus_homogeneousSection]

lemma exists_mem_nonvanishingLocus_segreSection (x : segreSource σ τ) :
    ∃ a, x ∈ (segreBundle σ τ).nonvanishingLocus (segreSection σ τ a) := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_basicOpen_X σ ℤ').ge (Set.mem_univ (segreFst σ τ x)))
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_basicOpen_X τ ℤ').ge (Set.mem_univ (segreSnd σ τ x)))
  exact ⟨(i, j), by rw [nonvanishingLocus_segreSection]; exact ⟨hi, hj⟩⟩

variable (σ τ)

/-- The graded homomorphism `ℤ[zᵢⱼ] → ⊕ₙ Γ(𝒪(n, n))`, `zᵢⱼ ↦ xᵢ ⊗ yⱼ`. -/
noncomputable abbrev segreGradedHom : (segreBundle σ τ).GradedHom (grading (σ × τ) ℤ') :=
  (segreBundle σ τ).gradedHomOfSections (segreSection σ τ)

/-- The Segre morphism `Proj ℤ[σ] × Proj ℤ[τ] ⟶ Proj ℤ[σ × τ]`, `(x, y) ↦ (xᵢ yⱼ)`. -/
noncomputable def segreInt : segreSource σ τ ⟶ Proj (grading (σ × τ) ℤ') :=
  (segreGradedHom σ τ).toProj (exists_nonvanishingLocus_gradedHomOfSections _ _
    exists_mem_nonvanishingLocus_segreSection)

variable {σ τ}

set_option backward.isDefEq.respectTransparency false in
lemma coordInt_self (i : σ) :
    ((coordInt σ i).1 i : Γ(Proj (grading σ ℤ'), Proj.basicOpen _ (X i))) = 1 := by
  change Proj.fracSection _ (X_mem_grading i)
    (Proj.pow_mem_of_mem_one _ (X_mem_grading i) 1) (Proj.basicOpen _ (X i))
    (Proj.basicOpen_le_basicOpen_pow _ _ _) = 1
  rw [Proj.fracSection_eq _ _ (X_mem_grading i) (X_mem_grading i) _ _ le_rfl (by ring),
    Proj.fracSection_self]

set_option backward.isDefEq.respectTransparency false in
lemma segreSection_self (a : σ × τ) :
    ((segreSection σ τ a).1 a : Γ(segreSource σ τ, _)) = 1 := by
  change _ * _ = 1
  simp only [sections.pullback_apply]
  erw [coordInt_self, coordInt_self]
  simp

lemma segreSection_apply (b a : σ × τ) :
    ((segreSection σ τ b).1 a : Γ(segreSource σ τ, (segreBundle σ τ).U a)) =
      (segreSource σ τ).presheaf.map (homOfLE (inf_le_left :
          segreFst σ τ ⁻¹ᵁ Proj.basicOpen _ (X a.1) ⊓ segreSnd σ τ ⁻¹ᵁ Proj.basicOpen _ (X a.2) ≤
            segreFst σ τ ⁻¹ᵁ Proj.basicOpen _ (X a.1))).op
        ((segreFst σ τ).appLE _ _ le_rfl ((coordInt σ b.1).1 a.1)) *
      (segreSource σ τ).presheaf.map (homOfLE (inf_le_right :
          segreFst σ τ ⁻¹ᵁ Proj.basicOpen _ (X a.1) ⊓ segreSnd σ τ ⁻¹ᵁ Proj.basicOpen _ (X a.2) ≤
            segreSnd σ τ ⁻¹ᵁ Proj.basicOpen _ (X a.2))).op
        ((segreSnd σ τ).appLE _ _ le_rfl ((coordInt τ b.2).1 a.2)) :=
  rfl

variable (σ τ) in
/-- The chart of the Segre morphism at `zₐ`. -/
noncomputable abbrev segreChartIndex (a : σ × τ) :
    GradedHom.ChartIndex (L := segreBundle σ τ) (𝒜 := grading (σ × τ) ℤ') :=
  ⟨a, 1, X a, one_pos, X_mem_grading a⟩

lemma segreGradedHom_app_X (a b : σ × τ) :
    (segreGradedHom σ τ).app a (X b) = (segreSection σ τ b).1 a :=
  (segreBundle σ τ).evalSections_X _ a b

set_option backward.isDefEq.respectTransparency false in
lemma segreChartOpen_eq (a : σ × τ) :
    (segreGradedHom σ τ).chartOpen (segreChartIndex σ τ a) =
      segreFst σ τ ⁻¹ᵁ Proj.basicOpen _ (X a.1) ⊓ segreSnd σ τ ⁻¹ᵁ Proj.basicOpen _ (X a.2) := by
  change (segreSource σ τ).basicOpen ((segreGradedHom σ τ).app a (X a)) = _
  rw [segreGradedHom_app_X, segreSection_self, Scheme.basicOpen_one]
  rfl

/-- `ℤ[σ]_(xᵢ) → ℤ[σ × τ]_(zᵢⱼ)`, `xₗ / xᵢ ↦ zₗⱼ / zᵢⱼ`. -/
noncomputable def segreAwayFst (a : σ × τ) :
    Away (grading σ ℤ') (X a.1) →+* Away (grading (σ × τ) ℤ') (X a) :=
  (eval₂Hom (awayC (X a)) fun l ↦ awayX a rfl (l.1, a.2)).comp (awayEquiv a.1 rfl).toRingHom

/-- `ℤ[τ]_(yⱼ) → ℤ[σ × τ]_(zᵢⱼ)`, `yₗ / yⱼ ↦ zᵢₗ / zᵢⱼ`. -/
noncomputable def segreAwaySnd (a : σ × τ) :
    Away (grading τ ℤ') (X a.2) →+* Away (grading (σ × τ) ℤ') (X a) :=
  (eval₂Hom (awayC (X a)) fun l ↦ awayX a rfl (a.1, l.1)).comp (awayEquiv a.2 rfl).toRingHom

lemma segreAwayFst_awayHomogenize (a : σ × τ) (l : {l // l ≠ a.1}) :
    segreAwayFst a (awayHomogenize a.1 rfl (X l)) = awayX a rfl (l.1, a.2) := by
  simp only [segreAwayFst, RingHom.coe_comp, Function.comp_apply]
  rw [show (awayEquiv a.1 rfl).toRingHom (awayHomogenize a.1 rfl (X l)) = X l from
    congr($(awayDehomogenize_comp_awayHomogenize a.1 (rfl : (X a.1 : MvPolynomial σ ℤ') = X a.1))
      (X l)), eval₂Hom_X']

lemma segreAwaySnd_awayHomogenize (a : σ × τ) (l : {l // l ≠ a.2}) :
    segreAwaySnd a (awayHomogenize a.2 rfl (X l)) = awayX a rfl (a.1, l.1) := by
  simp only [segreAwaySnd, RingHom.coe_comp, Function.comp_apply]
  rw [show (awayEquiv a.2 rfl).toRingHom (awayHomogenize a.2 rfl (X l)) = X l from
    congr($(awayDehomogenize_comp_awayHomogenize a.2 (rfl : (X a.2 : MvPolynomial τ ℤ') = X a.2))
      (X l)), eval₂Hom_X']

set_option backward.isDefEq.respectTransparency false in
lemma segre_awayToSections_awayX (a b : σ × τ) :
    Proj.awayToSections _ ((segreGradedHom σ τ).app a) (X a) (awayX a rfl b) =
      Proj.resBasicOpen ((segreGradedHom σ τ).app a) (X a) (X b) := by
  have h := Proj.awayToSections_mk ((segreGradedHom σ τ).app a) (X_mem_grading a) 1 (X b)
    (by simpa using X_mem_grading b)
  have e : (segreGradedHom σ τ).app a (X a) = 1 :=
    (segreGradedHom_app_X a a).trans (segreSection_self a)
  have h1 : Proj.resBasicOpen ((segreGradedHom σ τ).app a) (X a) (X a) = 1 := by
    rw [Proj.resBasicOpen_apply]
    simp only [e, map_one]
  rwa [h1, one_pow, mul_one] at h

set_option backward.isDefEq.respectTransparency false in
lemma segreAwayFst_comp (a : σ × τ) :
    CommRingCat.ofHom (segreAwayFst a) ≫
        CommRingCat.ofHom (Proj.awayToSections _ ((segreGradedHom σ τ).app a) (X a)) =
      Proj.awayToSection _ (X a.1) ≫ (segreFst σ τ).appLE (Proj.basicOpen _ (X a.1))
        ((segreGradedHom σ τ).chartOpen (segreChartIndex σ τ a))
        ((segreChartOpen_eq a).trans_le inf_le_left) := by
  rw [← cancel_epi
    (awayEquiv a.1 (rfl : (X a.1 : MvPolynomial σ ℤ') = X a.1)).symm.toCommRingCatIso.hom]
  refine AffineSpace.of_mvPolynomial_int_ext fun l ↦ ?_
  change Proj.awayToSections _ _ _ (segreAwayFst a (awayHomogenize a.1 rfl (X l))) =
    (segreFst σ τ).appLE _ _ _ (Proj.awayToSection _ (X a.1) (awayHomogenize a.1 rfl (X l)))
  rw [segreAwayFst_awayHomogenize, segre_awayToSections_awayX, Proj.resBasicOpen_apply,
    segreGradedHom_app_X a (l.1, a.2)]
  rw [awayHomogenize, eval₂Hom_X', awayX, Proj.awayToSection_mk, segreSection_apply,
    coordInt_self, map_one, map_one, mul_one]
  exact Scheme.Hom.appLE_map_map_apply _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma segreAwaySnd_comp (a : σ × τ) :
    CommRingCat.ofHom (segreAwaySnd a) ≫
        CommRingCat.ofHom (Proj.awayToSections _ ((segreGradedHom σ τ).app a) (X a)) =
      Proj.awayToSection _ (X a.2) ≫ (segreSnd σ τ).appLE (Proj.basicOpen _ (X a.2))
        ((segreGradedHom σ τ).chartOpen (segreChartIndex σ τ a))
        ((segreChartOpen_eq a).trans_le inf_le_right) := by
  rw [← cancel_epi
    (awayEquiv a.2 (rfl : (X a.2 : MvPolynomial τ ℤ') = X a.2)).symm.toCommRingCatIso.hom]
  refine AffineSpace.of_mvPolynomial_int_ext fun l ↦ ?_
  change Proj.awayToSections _ _ _ (segreAwaySnd a (awayHomogenize a.2 rfl (X l))) =
    (segreSnd σ τ).appLE _ _ _ (Proj.awayToSection _ (X a.2) (awayHomogenize a.2 rfl (X l)))
  rw [segreAwaySnd_awayHomogenize, segre_awayToSections_awayX, Proj.resBasicOpen_apply,
    segreGradedHom_app_X a (a.1, l.1)]
  rw [awayHomogenize, eval₂Hom_X', awayX, Proj.awayToSection_mk, segreSection_apply,
    coordInt_self, map_one, map_one, one_mul]
  exact Scheme.Hom.appLE_map_map_apply _ _ _ _ _ _

/-- The map `Spec ℤ[σ × τ]_(zₐ) ⟶ Proj ℤ[σ] × Proj ℤ[τ]`, `(zₗₘ / zₐ) ↦ (xₗ / x_{a₁}, yₘ / y_{a₂})`,
a retraction of the Segre morphism on the chart `zₐ ≠ 0`. -/
noncomputable def segreRetraction (a : σ × τ) :
    Spec (.of (Away (grading (σ × τ) ℤ') (X a))) ⟶ segreSource σ τ :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (segreAwayFst a)) ≫
      Proj.awayι _ (X a.1) (X_mem_grading a.1) one_pos)
    (Spec.map (CommRingCat.ofHom (segreAwaySnd a)) ≫
      Proj.awayι _ (X a.2) (X_mem_grading a.2) one_pos)
    (terminal.hom_ext _ _)

/-- The Segre morphism on the chart `zₐ ≠ 0`. -/
noncomputable def segreChart (a : σ × τ) :
    ((segreGradedHom σ τ).chartOpen (segreChartIndex σ τ a)).toScheme ⟶
      Spec (.of (Away (grading (σ × τ) ℤ') (X a))) :=
  ((segreGradedHom σ τ).chartOpen (segreChartIndex σ τ a)).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (Proj.awayToSections _ ((segreGradedHom σ τ).app a) (X a)))

lemma segreChart_awayι (a : σ × τ) :
    segreChart a ≫ Proj.awayι _ (X a) (X_mem_grading a) one_pos =
      ((segreGradedHom σ τ).chartOpen (segreChartIndex σ τ a)).ι ≫ segreInt σ τ := by
  rw [segreInt, GradedHom.ι_toProj]
  simp only [segreChart, Category.assoc]
  rfl

lemma segreChart_segreRetraction (a : σ × τ) :
    segreChart a ≫ segreRetraction a =
      ((segreGradedHom σ τ).chartOpen (segreChartIndex σ τ a)).ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, segreRetraction, pullback.lift_fst, segreChart, Category.assoc,
      ← Spec.map_comp_assoc]
    erw [segreAwayFst_comp]
    exact (Proj.ι_comp_eq _ (segreFst σ τ) (X_mem_grading a.1) one_pos _ _).symm
  · rw [Category.assoc, segreRetraction, pullback.lift_snd, segreChart, Category.assoc,
      ← Spec.map_comp_assoc]
    erw [segreAwaySnd_comp]
    exact (Proj.ι_comp_eq _ (segreSnd σ τ) (X_mem_grading a.2) one_pos _ _).symm

lemma range_segreRetraction (a : σ × τ) :
    Set.range (segreRetraction a) ⊆
      Set.range ((segreGradedHom σ τ).chartOpen (segreChartIndex σ τ a)).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι, SetLike.mem_coe, segreChartOpen_eq]
  constructor
  · change (segreRetraction a ≫ segreFst σ τ) x ∈ Proj.basicOpen _ (X a.1)
    rw [segreRetraction, pullback.lift_fst,
      ← Proj.opensRange_awayι _ _ (X_mem_grading a.1) one_pos]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  · change (segreRetraction a ≫ segreSnd σ τ) x ∈ Proj.basicOpen _ (X a.2)
    rw [segreRetraction, pullback.lift_snd,
      ← Proj.opensRange_awayι _ _ (X_mem_grading a.2) one_pos]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

instance isClosedImmersion_segreChart (a : σ × τ) : IsClosedImmersion (segreChart a) := by
  let r' := IsOpenImmersion.lift _ _ (range_segreRetraction a)
  have h1 : segreChart a ≫ r' = 𝟙 _ := by
    rw [← cancel_mono ((segreGradedHom σ τ).chartOpen (segreChartIndex σ τ a)).ι, Category.assoc,
      IsOpenImmersion.lift_fac, segreChart_segreRetraction, Category.id_comp]
  have : IsClosedImmersion (segreChart a ≫ r') := by rw [h1]; infer_instance
  have : IsSeparated (r' ≫ terminal.from _) := by rw [terminal.comp_from]; infer_instance
  have : IsSeparated r' := IsSeparated.of_comp r' (terminal.from _)
  exact IsClosedImmersion.of_comp _ r'

lemma segreInt_preimage_basicOpen (a : σ × τ) :
    segreInt σ τ ⁻¹ᵁ Proj.basicOpen _ (X a) =
      (segreGradedHom σ τ).chartOpen (segreChartIndex σ τ a) := by
  rw [segreInt, GradedHom.toProj_preimage_basicOpen _ _ (X_mem_grading a) one_pos,
    gradedHomOfSections_sec_X, nonvanishingLocus_segreSection, segreChartOpen_eq]

variable (σ τ) in
/-- The Segre morphism `Proj ℤ[σ] × Proj ℤ[τ] ⟶ Proj ℤ[σ × τ]` is a closed immersion. -/
theorem isClosedImmersion_segreInt : IsClosedImmersion (segreInt σ τ) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _
    (iSup_basicOpen_X (σ × τ) ℤ')]
  intro a
  have e : segreInt σ τ ∣_ Proj.basicOpen _ (X a) =
      (Scheme.isoOfEq _ (segreInt_preimage_basicOpen a)).hom ≫ segreChart a ≫
        (Proj.basicOpenIsoSpec _ (X a) (X_mem_grading a) one_pos).inv := by
    rw [← cancel_mono (Proj.basicOpen _ (X a)).ι, morphismRestrict_ι, Category.assoc,
      Category.assoc, Proj.basicOpenIsoSpec_inv_ι, segreChart_awayι, Scheme.isoOfEq_hom_ι_assoc]
  rw [e]
  infer_instance

section relative

variable (S : Scheme.{u})

/-- The projection `ℙ(σ; ℙ(τ; S)) ⟶ Proj ℤ[σ] × Proj ℤ[τ]`. -/
noncomputable def toSegreSource : ℙ(σ; ℙ(τ; S)) ⟶ segreSource σ τ :=
  pullback.lift (toProj σ _) (ℙ(σ; ℙ(τ; S)) ↘ ℙ(τ; S) ≫ toProj τ S) (terminal.hom_ext _ _)

/-- The Segre embedding `ℙ(σ; S) ×_S ℙ(τ; S) = ℙ(σ; ℙ(τ; S)) ⟶ ℙ(σ × τ; S)`,
`(x, y) ↦ (xᵢ yⱼ)` (EGA II 4.3.1). -/
noncomputable def segre : ℙ(σ; ℙ(τ; S)) ⟶ ℙ(σ × τ; S) :=
  pullback.lift (ℙ(σ; ℙ(τ; S)) ↘ ℙ(τ; S) ≫ ℙ(τ; S) ↘ S) (toSegreSource S ≫ segreInt σ τ)
    (terminal.hom_ext _ _)

@[reassoc (attr := simp)]
lemma segre_over :
    segre S ≫ ℙ(σ × τ; S) ↘ S = ℙ(σ; ℙ(τ; S)) ↘ ℙ(τ; S) ≫ ℙ(τ; S) ↘ S :=
  pullback.lift_fst _ _ _

lemma isPullback_toSegreSource :
    IsPullback (toSegreSource (σ := σ) (τ := τ) S) (ℙ(σ; ℙ(τ; S)) ↘ ℙ(τ; S) ≫ ℙ(τ; S) ↘ S)
      (terminal.from _) (terminal.from S) := by
  have h₁ : IsPullback (toSegreSource (σ := σ) (τ := τ) S) (ℙ(σ; ℙ(τ; S)) ↘ ℙ(τ; S))
      (segreSnd σ τ) (toProj τ S) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [toSegreSource, pullback.lift_fst, terminal.comp_from]
    exact isPullback_toProj σ _
  have := h₁.paste_vert (isPullback_toProj τ S)
  rwa [terminal.comp_from] at this

/-- EGA II 4.3.1: the Segre morphism is a closed immersion. -/
instance isClosedImmersion_segre : IsClosedImmersion (segre (σ := σ) (τ := τ) S) := by
  have H : IsPullback (toSegreSource (σ := σ) (τ := τ) S) (segre S) (segreInt σ τ)
      (toProj (σ × τ) S) := by
    refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm (isPullback_toProj (σ × τ) S)
    rw [segre_over, terminal.comp_from]
    exact isPullback_toSegreSource S
  have := isClosedImmersion_segreInt σ τ
  exact MorphismProperty.of_isPullback H this

end relative

end ProjectiveSpace

namespace ProjectiveSpace

variable (S : Scheme.{u})

lemma basicOpen_eq_top_of_subsingleton {σ : Type u} [Subsingleton σ] (i : σ) :
    basicOpen S i = ⊤ := by
  rw [← iSup_basicOpen S]
  exact le_antisymm (le_iSup _ i) (iSup_le fun j ↦ (Subsingleton.elim i j) ▸ le_rfl)

/-- `ℙ(σ; S) = S` for `σ` with one element. -/
instance {σ : Type u} [Unique σ] : IsIso (ℙ(σ; S) ↘ S) := by
  have e := basicOpen_eq_top_of_subsingleton S (default : σ)
  have : IsEmpty {j : σ // j ≠ default} := ⟨fun j ↦ j.2 (Subsingleton.elim _ _)⟩
  have : IsIso (basicOpen S (default : σ)).ι := by
    rw [e]
    exact inferInstanceAs (IsIso ℙ(σ; S).topIso.hom)
  have : IsIso ((basicOpen S (default : σ)).ι ≫ ℙ(σ; S) ↘ S) := by
    rw [← basicOpenIsoAffineSpace_hom_over]
    infer_instance
  exact IsIso.of_isIso_comp_left (basicOpen S (default : σ)).ι (ℙ(σ; S) ↘ S)

end ProjectiveSpace

namespace IsHProjective

variable {X Y S : Scheme.{u}}

/-- Closed immersions are H-projective. -/
instance (priority := 900) of_isClosedImmersion (f : X ⟶ S) [IsClosedImmersion f] :
    IsHProjective f :=
  ⟨PUnit, inferInstance, f ≫ inv (ℙ(PUnit; S) ↘ S), inferInstance, by simp⟩

/-- EGA II 5.5.5 (ii), Hartshorne Ex. II.4.9: a composition of H-projective morphisms is
H-projective (using the Segre embedding). -/
instance comp (f : X ⟶ Y) (g : Y ⟶ S) [hf : IsHProjective f] [hg : IsHProjective g] :
    IsHProjective (f ≫ g) := by
  obtain ⟨σ, _, i, _, rfl⟩ := hf
  obtain ⟨τ, _, j, _, rfl⟩ := hg
  have : IsClosedImmersion (ProjectiveSpace.map (σ := σ) (ℙ(τ; S)) j) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map j).flip ‹_›
  refine ⟨σ × τ, inferInstance, i ≫ ProjectiveSpace.map _ j ≫ ProjectiveSpace.segre S,
    inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, ProjectiveSpace.segre_over, ProjectiveSpace.map_over_assoc,
    Category.assoc]

instance : MorphismProperty.IsStableUnderComposition @IsHProjective where
  comp_mem f g hf hg := @comp _ _ _ f g hf hg

/-- A fibre product of H-projective morphisms is H-projective. -/
instance pullback_fst_comp (f : X ⟶ S) (g : Y ⟶ S) [IsHProjective f] [IsHProjective g] :
    IsHProjective (pullback.fst f g ≫ f) := by
  have : IsHProjective (pullback.fst f g) :=
    of_isPullback (IsPullback.of_hasPullback f g).flip
  infer_instance

end IsHProjective

namespace IsHQuasiProjective

variable {X Y S : Scheme.{u}}

/-- A composition of H-quasi-projective morphisms is H-quasi-projective. -/
instance comp (f : X ⟶ Y) (g : Y ⟶ S) [hf : IsHQuasiProjective f] [hg : IsHQuasiProjective g] :
    IsHQuasiProjective (f ≫ g) := by
  obtain ⟨σ, _, i, _, _, rfl⟩ := hf
  obtain ⟨τ, _, j, _, _, rfl⟩ := hg
  have : IsImmersion (ProjectiveSpace.map (σ := σ) (ℙ(τ; S)) j) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map j).flip ‹_›
  have : QuasiCompact (ProjectiveSpace.map (σ := σ) (ℙ(τ; S)) j) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map j).flip ‹_›
  refine ⟨σ × τ, inferInstance, i ≫ ProjectiveSpace.map _ j ≫ ProjectiveSpace.segre S,
    inferInstance, inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, ProjectiveSpace.segre_over, ProjectiveSpace.map_over_assoc,
    Category.assoc]

end IsHQuasiProjective

end AlgebraicGeometry
