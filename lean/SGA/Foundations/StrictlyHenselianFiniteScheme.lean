/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Limits
import SGA.Foundations.HenselianFinite
import SGA.Foundations.Limits.GeometricFiberCard
import SGA.Foundations.StrictlyHenselianLift

/-!
# Finite schemes over a strictly henselian local ring

Let `O` be a strictly henselian local ring and `g : X' ⟶ Spec O` finite.

* `AlgebraicGeometry.isStrictlyHenselian_of_isFinite`: a clopen subscheme `Q` of `X'` meeting the
  closed fibre in a single point `p₀` is the spectrum of a strictly henselian local ring, with
  closed point `p₀` (Stacks 04GH, 04GG (10)).
* `AlgebraicGeometry.exists_section_of_isFinite`: every étale `X'`-scheme with a geometric point
  over a geometric point of such a `Q` has a section over `Q` through it.
* `AlgebraicGeometry.eq_of_apply_eq_of_isFinite`: two geometric points of `X'` over the same
  geometric point of `Spec O` at the closed point, with the same image point, are equal (the
  residue fields of the closed fibre are purely inseparable over the separably closed residue
  field of `O`).
* `AlgebraicGeometry.exists_hom_sigma_of_isFinite`: `X'` is the disjoint union of such pieces `Q`,
  one for each geometric point over a geometric point of `Spec O` at the closed point; hence,
  given for each of these geometric points `a` an étale `B`-scheme `U_a` with a point over
  `a ≫ ρ` (for `ρ : X' ⟶ B`), there is a `B`-morphism `X' ⟶ ∐ U_a` sending `a` to the given
  point in `U_a`.

This is the local structure of finite morphisms over a strictly henselian base
(EGA IV 18.8.10, SGA 4 VIII 4.8, Stacks 04GH): `X' = ∐ Spec 𝒪^{sh}_{X', a}`.
-/

universe u

open CategoryTheory Limits IsLocalRing

noncomputable section

-- As in `SGA.Foundations.StrictLocalizationLift`.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry

/-- The residue field of the spectrum of a strictly henselian local ring at its closed point is
separably closed. -/
lemma isSepClosed_residueField_Spec_closedPoint (A : CommRingCat.{u}) [IsStrictlyHenselian A] :
    IsSepClosed ((Spec A).residueField (closedPoint A)) := by
  have e₁ : ResidueField A ≃+* (maximalIdeal A).ResidueField :=
    RingEquiv.ofBijective (algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField _)
  have : IsSepClosed (maximalIdeal A).ResidueField := IsSepClosed.of_ringEquiv e₁
  let e₂ : (maximalIdeal A).ResidueField ≃+* (Spec A).residueField (closedPoint A) :=
    (Scheme.Spec.residueFieldIso A (closedPoint A)).commRingCatIsoToRingEquiv.symm
  exact IsSepClosed.of_ringEquiv e₂

variable {O : CommRingCat.{u}} [IsStrictlyHenselian O] {X' : Scheme.{u}} (g : X' ⟶ Spec O)
  [IsFinite g]

section Piece

variable (Q : X'.Opens) (hQ : IsClosed (Q : Set X')) (p₀ : X') (hp₀ : p₀ ∈ Q)
  (hQ' : ∀ z ∈ Q, g z = closedPoint O → z = p₀)

include hQ in
/-- A clopen subscheme of an affine scheme is affine. -/
lemma isAffine_of_isClosed [IsAffine X'] : IsAffine Q := by
  have : IsClosedImmersion Q.ι :=
    .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hQ)
  exact isAffine_of_isAffineHom Q.ι

include hQ hQ' in
/-- A clopen subscheme `Q` of a finite scheme over a strictly henselian local ring `O` meeting the
closed fibre in the single point `p₀` is the spectrum of a strictly henselian local ring, whose
closed point is `p₀`. -/
lemma isStrictlyHenselian_of_isFinite :
    ∃ _ : IsAffine Q, ∃ _ : IsLocalRing Γ(Q, ⊤), IsStrictlyHenselian Γ(Q, ⊤) ∧
      Q.toScheme.isoSpec.hom ⟨p₀, hp₀⟩ = closedPoint Γ(Q, ⊤) := by
  have : IsAffine X' := isAffine_of_isAffineHom g
  have : IsAffine Q := isAffine_of_isClosed Q hQ
  refine ⟨this, ?_⟩
  let A := Γ(Q, ⊤)
  let φ : O ⟶ A := (Scheme.ΓSpecIso O).inv ≫ (Q.ι ≫ g).appTop
  have hQg : Q.ι ≫ g = Q.toScheme.isoSpec.hom ≫ Spec.map φ := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  let _ : Algebra O A := φ.hom.toAlgebra
  have : IsClosedImmersion Q.ι :=
    .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hQ)
  have : Module.Finite O A := by
    have : IsFinite (Spec.map φ) := by
      have : Spec.map φ = Q.toScheme.isoSpec.inv ≫ Q.ι ≫ g := by rw [hQg, Iso.inv_hom_id_assoc]
      rw [this]
      infer_instance
    exact (IsFinite.SpecMap_iff _).mp this
  have hpt (z : Q) : g (Q.ι z) = PrimeSpectrum.comap φ.hom (Q.toScheme.isoSpec.hom z) := by
    rw [← Scheme.Hom.comp_apply, hQg]
    rfl
  -- every maximal ideal of `A` is the ideal of `p₀`
  let M₀ := (Q.toScheme.isoSpec.hom ⟨p₀, hp₀⟩).asIdeal
  have hmax (M : Ideal A) (hM : M.IsMaximal) : M = M₀ := by
    let m : Q := Q.toScheme.isoSpec.inv ⟨M, hM.isPrime⟩
    have hm : Q.toScheme.isoSpec.hom m = ⟨M, hM.isPrime⟩ := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    have hgm : g (Q.ι m) = closedPoint O := by
      rw [hpt, hm]
      exact PrimeSpectrum.ext (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M))
    have hm₀ : m = ⟨p₀, hp₀⟩ := Subtype.ext (hQ' _ m.2 hgm)
    have := congrArg PrimeSpectrum.asIdeal (hm.symm.trans (congrArg Q.toScheme.isoSpec.hom hm₀))
    exact this
  have hM₀ : M₀.IsMaximal := by
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal M₀ (Q.toScheme.isoSpec.hom ⟨p₀, hp₀⟩).2.ne_top
    rw [← hmax M hM]
    exact hM
  have : IsLocalRing A := .of_unique_max_ideal ⟨M₀, hM₀, fun M hM ↦ hmax M hM⟩
  refine ⟨this, IsStrictlyHenselian.of_finite (A := O) A, ?_⟩
  exact PrimeSpectrum.ext (eq_maximalIdeal hM₀)

include hQ hQ' in
/-- **Sections of étale morphisms over a local piece** (Stacks 04GG (10)): let `Q ⊆ X'` be clopen,
meeting the closed fibre only in `p₀`, and `p : Spec Ω ⟶ Q` a geometric point at `p₀`. Every lift
`z` of `p` to an étale `X'`-scheme `Z` extends to a section `Q ⟶ Z` over `Q`. -/
theorem exists_section_of_isFinite {Ω : Type u} [Field Ω] {Z : Scheme.{u}} (q : Z ⟶ X') [Etale q]
    (p : Spec (.of Ω) ⟶ Q) (hp : p (closedPoint Ω) = ⟨p₀, hp₀⟩) (z : Spec (.of Ω) ⟶ Z)
    (hz : z ≫ q = p ≫ Q.ι) :
    ∃ s : (Q : Scheme.{u}) ⟶ Z, s ≫ q = Q.ι ∧ p ≫ s = z := by
  obtain ⟨_, _, _, hcl⟩ := isStrictlyHenselian_of_isFinite g Q hQ p₀ hp₀ hQ'
  let A := Γ(Q, ⊤)
  let α : A ⟶ CommRingCat.of Ω := p.appTop ≫ (Scheme.ΓSpecIso (.of Ω)).hom
  have hα : Spec.map α = p ≫ Q.toScheme.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Scheme.isoSpec_Spec_hom, ← Spec.map_comp]
  have : IsLocalHom α.hom := by
    refine ⟨fun a ha ↦ ?_⟩
    by_contra hna
    have hker : (Spec.map α (closedPoint Ω)).asIdeal = maximalIdeal A := by
      rw [hα, Scheme.Hom.comp_apply, hp, hcl]
      rfl
    have ha' : a ∈ (Spec.map α (closedPoint Ω)).asIdeal := by
      rw [hker]
      exact (mem_maximalIdeal a).mpr hna
    change α.hom a ∈ maximalIdeal Ω at ha'
    rw [maximalIdeal_eq_bot, Ideal.mem_bot] at ha'
    rw [ha'] at ha
    exact not_isUnit_zero ha
  obtain ⟨g', hg'q, hg'z⟩ := Scheme.exists_lift_of_isStrictlyHenselian α
    (Q.toScheme.isoSpec.inv ≫ Q.ι) q z (by rw [hz, hα, Category.assoc, Iso.hom_inv_id_assoc])
  refine ⟨Q.toScheme.isoSpec.hom ≫ g', ?_, ?_⟩
  · rw [Category.assoc, hg'q, Iso.hom_inv_id_assoc]
  · rw [← Category.assoc, ← hα, hg'z]

end Piece

omit [IsFinite g] in
/-- Two geometric points of `X'` over the same geometric point of `Spec O` at the closed point, with
the same image point, are equal: the residue fields of the closed fibre are purely inseparable
over the separably closed residue field of `O`. -/
lemma eq_of_apply_eq_of_isFinite [LocallyQuasiFinite g] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec O) (hs : s (closedPoint Ω) = closedPoint O)
    {a b : Spec (.of Ω) ⟶ X'} (ha : a ≫ g = s) (hb : b ≫ g = s)
    (hab : a (closedPoint Ω) = b (closedPoint Ω)) : a = b := by
  obtain ⟨y, φ, rfl⟩ := Scheme.eq_specMap_comp_fromSpecResidueField s
  have hy : y = closedPoint O := by
    rw [← hs, Scheme.specMap_comp_fromSpecResidueField_apply]
  have hx : g (a (closedPoint Ω)) = y := by
    rw [← Scheme.Hom.comp_apply, ha, Scheme.specMap_comp_fromSpecResidueField_apply]
  have hcard := g.natCard_pointsOver_at_eq y φ (a (closedPoint Ω)) hx
  let := (g.residueFieldMap (a (closedPoint Ω))).hom.toAlgebra
  have : IsSepClosed ((Spec O).residueField (g (a (closedPoint Ω)))) := by
    rw [hx, hy]
    exact isSepClosed_residueField_Spec_closedPoint O
  have := g.finiteDimensional_residueField (a (closedPoint Ω))
  have : IsPurelyInseparable ((Spec O).residueField (g (a (closedPoint Ω))))
      (X'.residueField (a (closedPoint Ω))) := inferInstance
  rw [IsPurelyInseparable.finSepDegree_eq_one] at hcard
  have hsub := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact congrArg Subtype.val (hsub.elim ⟨a, rfl, ha⟩ ⟨b, hab.symm, hb⟩)

set_option backward.isDefEq.respectTransparency false in
/-- **Local structure of finite schemes over a strictly henselian local ring** (EGA IV 18.8.10,
Stacks 04GH). Let `g : X' ⟶ Spec O` be finite, `O` strictly henselian, `s` a geometric point of
`Spec O` at the closed point, and `ι i` (`i ∈ I`) the geometric points of `X'` over `s`, listed
injectively and covering the closed fibre. Given `ρ : X' ⟶ B` and, for each `i`, an étale
`B`-scheme `U i` with a geometric point `u i` over `ι i ≫ ρ`, there is a `B`-morphism
`σ : X' ⟶ ∐ U i` with `ι i ≫ σ = u i` in the summand `U i`: `X'` is the disjoint union of clopen
pieces, one around each geometric point of the closed fibre, over which the étale `B`-schemes
have sections. -/
theorem exists_hom_sigma_of_isFinite {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec O) (hs : s (closedPoint Ω) = closedPoint O)
    {I : Type u} (ι : I → (Spec (.of Ω) ⟶ X')) (hι : ∀ i, ι i ≫ g = s)
    (hinj : Function.Injective ι)
    (hsurj : ∀ z, g z = closedPoint O → ∃ i, ι i (closedPoint Ω) = z)
    {B : Scheme.{u}} (ρ : X' ⟶ B) {U : I → Scheme.{u}} (q : ∀ i, U i ⟶ B) [∀ i, Etale (q i)]
    (u : ∀ i, Spec (.of Ω) ⟶ U i) (hu : ∀ i, u i ≫ q i = ι i ≫ ρ) :
    ∃ σ : X' ⟶ ∐ U, σ ≫ Sigma.desc q = ρ ∧ ∀ i, ι i ≫ σ = u i ≫ Sigma.ι U i := by
  classical
  let x₀ (i : I) : X' := ι i (closedPoint Ω)
  have hx₀ (i : I) : g (x₀ i) = closedPoint O := by
    rw [← Scheme.Hom.comp_apply, hι, hs]
  choose Q hQc hxQ hQ' using fun i ↦ exists_isClopen_of_isFinite g (x₀ i) (hx₀ i)
  let Q' (i : I) : X'.Opens := ⟨Q i, (hQc i).2⟩
  -- the pieces are pairwise disjoint and cover `X'`
  have hclosed (C : Set X') (hC : IsClosed C) (z : X') (hz : z ∈ C) :
      ∃ z' ∈ C, g z' = closedPoint O := by
    obtain ⟨z', hz'C, hz'⟩ := (specializes_closedPoint (g z)).mem_closed
      (g.isClosedMap _ hC) ⟨z, hz, rfl⟩
    exact ⟨z', hz'C, hz'⟩
  have hdisj (i j : I) (hij : i ≠ j) (z : X') (hzi : z ∈ Q i) (hzj : z ∈ Q j) : False := by
    obtain ⟨z', ⟨hz'i, hz'j⟩, hz'⟩ := hclosed _ ((hQc i).1.inter (hQc j).1) z ⟨hzi, hzj⟩
    have h := (hQ' i z' hz'i hz').symm.trans (hQ' j z' hz'j hz')
    exact hij (hinj (eq_of_apply_eq_of_isFinite g s hs (hι i) (hι j) h))
  have hcov (z : X') : ∃ i, z ∈ Q i := by
    obtain ⟨z', hz'C, hz'⟩ := hclosed (closure {z}) isClosed_closure z (subset_closure rfl)
    obtain ⟨i, hi⟩ := hsurj z' hz'
    refine ⟨i, ?_⟩
    have hsp : z ⤳ z' := specializes_iff_mem_closure.mpr hz'C
    exact hsp.mem_open (hQc i).2 (hi ▸ hxQ i)
  -- the sections over the pieces
  have hrange (i : I) : Set.range (ι i) ⊆ Set.range (Q' i).ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim t (closedPoint Ω)]
    exact hxQ i
  let p (i : I) : Spec (.of Ω) ⟶ Q' i := IsOpenImmersion.lift (Q' i).ι (ι i) (hrange i)
  have hp (i : I) : p i ≫ (Q' i).ι = ι i := IsOpenImmersion.lift_fac _ _ _
  have hp₀ (i : I) : p i (closedPoint Ω) = ⟨x₀ i, hxQ i⟩ := by
    apply Subtype.ext
    change ((Q' i).ι) (p i (closedPoint Ω)) = x₀ i
    rw [← Scheme.Hom.comp_apply, hp]
  have hsec (i : I) := exists_section_of_isFinite g (Q' i) (hQc i).1 (x₀ i) (hxQ i) (hQ' i)
    (pullback.snd (q i) ρ) (p i) (hp₀ i) (pullback.lift (u i) (ι i) (hu i))
    (by rw [pullback.lift_snd, hp])
  choose s hs₁ hs₂ using hsec
  let F (i : I) : (Q' i : Scheme.{u}) ⟶ ∐ U := s i ≫ pullback.fst _ _ ≫ Sigma.ι U i
  let 𝒰 : X'.OpenCover :=
    { I₀ := I
      X i := Q' i
      f i := (Q' i).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun z ↦ ?_, inferInstance⟩
        obtain ⟨i, hi⟩ := hcov z
        exact ⟨i, ⟨z, hi⟩, rfl⟩ }
  have hF (i j : I) : pullback.fst ((Q' i).ι) ((Q' j).ι) ≫ F i =
      pullback.snd ((Q' i).ι) ((Q' j).ι) ≫ F j := by
    by_cases hij : i = j
    · subst hij
      have : pullback.fst ((Q' i).ι) ((Q' i).ι) = pullback.snd _ _ :=
        (cancel_mono (Q' i).ι).mp pullback.condition
      rw [this]
    · let P : Scheme.{u} := pullback ((Q' i).ι) ((Q' j).ι)
      have : IsEmpty P := ⟨fun w ↦ by
        have h : ((Q' i).ι) ((pullback.fst (Q' i).ι (Q' j).ι) w) =
            ((Q' j).ι) ((pullback.snd (Q' i).ι (Q' j).ι) w) := by
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
        have h' : ((pullback.fst (Q' i).ι (Q' j).ι) w).1 =
            ((pullback.snd (Q' i).ι (Q' j).ι) w).1 := h
        exact hdisj i j hij _ ((pullback.fst ((Q' i).ι) ((Q' j).ι)) w).2
          (h' ▸ ((pullback.snd ((Q' i).ι) ((Q' j).ι)) w).2)⟩
      exact isInitialOfIsEmpty.hom_ext _ _
  refine ⟨𝒰.glueMorphisms F hF, ?_, fun i ↦ ?_⟩
  · refine 𝒰.hom_ext _ _ fun i ↦ ?_
    rw [Scheme.Cover.ι_glueMorphisms_assoc]
    change (s i ≫ pullback.fst _ _ ≫ Sigma.ι U i) ≫ Sigma.desc q = (Q' i).ι ≫ ρ
    rw [Category.assoc, Category.assoc, Sigma.ι_desc, pullback.condition, ← Category.assoc,
      hs₁ i]
  · rw [← hp i, Category.assoc]
    change p i ≫ (𝒰.f i ≫ 𝒰.glueMorphisms F hF) = _
    rw [Scheme.Cover.ι_glueMorphisms]
    change p i ≫ s i ≫ pullback.fst _ _ ≫ Sigma.ι U i = _
    rw [reassoc_of% (hs₂ i), pullback.lift_fst_assoc]

end AlgebraicGeometry
