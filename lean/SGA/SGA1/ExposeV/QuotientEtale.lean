/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeV.QuotientFiniteEtale
import SGA.SGA1.ExposeV.QuotientGluing
import SGA.SGA1.ExposeV.EtaleCoveringAutomorphisms
import SGA.SGA1.ExposeVIII.FiniteDescent

/-!
# SGA 1, Exposé V, §3: quotients of étale schemes by finite groups (V.3.1–V.3.4)

* V.3.4 for any base (`finite_etale_fromQuotient`, `finiteEtaleQuotientStatement`): if `X` is
  finite étale over `S` and `G` acts by `S`-automorphisms, then `X/G = Spec_S (f_* 𝒪_X)^G` is
  finite étale over `S`. Over an affine open `Spec R`, this is
  `finite_etale_fixedPoints_of_finite_etale`. No noetherian hypothesis is needed.
* V.3.2 when `X` is finite étale over `S`: `X ⟶ X/G` is étale (`etale_toQuotient`).
* V.3.1, admissibility (`isAdmissible_of_etale`): an étale separated quasi-compact `X` is
  quasi-affine over `S` (VIII.6.2), so `G` acts admissibly (V.1.8).
* Points with values in a field: for the quotient `p : X ⟶ Y` of V.1.3, two points
  `Spec Ω ⟶ X` with the same image in `Y` differ by an element of `G`
  (`exists_comp_eq_of_comp_eq`), and points of `Y` lift to `X` when the residue extensions are
  separable and `Ω` is separably closed (`exists_geometricPoint_lift_of_isSeparable`).

V.3.1 and V.3.2 for `X` étale but not finite over `S` are in `QuotientComponents.lean`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace SGA.SGA1.ExposeV

section FiniteEtale

variable {G : Type*} [Group G] [Finite G] {X S : Scheme.{u}} {T : G → (X ⟶ X)}
  (hT : IsRightAction T) {f : X ⟶ S} (hTf : ∀ g, T g ≫ f = f)

include hT in
/-- V.3.4 over an affine open `U`: the ring map `Γ(S, U) → Γ(X, f⁻¹ U)^G` is finite étale. -/
lemma finite_etale_invariantDiagramMap_app [IsFinite f] [Etale f] (U : S.Opens)
    (hU : IsAffineOpen U) :
    ((invariantDiagramMap hTf).app (op ⟨U, hU⟩)).hom.Finite ∧
      ((invariantDiagramMap hTf).app (op ⟨U, hU⟩)).hom.Etale := by
  let R := Γ(S, U)
  let A := Γ(X, f ⁻¹ᵁ U)
  let _ : Algebra R A := (f.app U).hom.toAlgebra
  let _ : MulSemiringAction G A :=
    sectionsAction hT (f ⁻¹ᵁ U) fun g ↦ preimage_le_preimage_of_comp_eq (hTf g) U
  have : SMulCommClass G R A := ⟨fun g r s ↦ by
    change (T g).appLE _ _ _ (f.app U r * s) = f.app U r * (T g).appLE _ _ _ s
    rw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (hTf g) _ _ _ le_rfl]⟩
  have : Module.Finite R A := RingHom.finite_algebraMap.mp (f.finite_app U hU)
  have : Algebra.Etale R A := by
    rw [← RingHom.etale_algebraMap]
    have := HasRingHomProperty.appLE @Etale f ‹_› ⟨U, hU⟩ ⟨f ⁻¹ᵁ U, hU.preimage f⟩ le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  obtain ⟨h₁, h₂⟩ := finite_etale_fixedPoints_of_finite_etale G (R := R) (A := A)
  let e : FixedPoints.subalgebra R A G ≃+* invariantSubring hTf U :=
    { toFun x := ⟨x.1, x.2⟩
      invFun x := ⟨x.1, x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl }
  have hφ : ((invariantDiagramMap hTf).app (op ⟨U, hU⟩)).hom =
      e.toRingHom.comp (algebraMap R (FixedPoints.subalgebra R A G)) := by
    ext r
    rfl
  have H₁ : (e.toRingHom.comp (algebraMap R (FixedPoints.subalgebra R A G))).Finite :=
    RingHom.finite_respectsIso.1 _ _ (RingHom.finite_algebraMap.mpr h₁)
  have H₂ : (e.toRingHom.comp (algebraMap R (FixedPoints.subalgebra R A G))).Etale :=
    RingHom.Etale.respectsIso.1 _ _ (RingHom.etale_algebraMap.mpr h₂)
  rw [hφ]
  exact ⟨H₁, H₂⟩

set_option backward.isDefEq.respectTransparency false in
include hT in
/-- V.3.4 (for any base `S`): if `X` is finite étale over `S`, so is `X/G = Spec_S (f_* 𝒪_X)^G`.
Over an affine open `U` of `S`, `X/G` is `Spec Γ(X, f⁻¹ U)^G`
(`finite_etale_invariantDiagramMap_app`). -/
theorem finite_etale_fromQuotient [IsFinite f] [Etale f] :
    IsFinite (fromQuotient hTf) ∧ Etale (fromQuotient hTf) := by
  let q := fromQuotient hTf
  have key : ∀ U : S.affineOpens, IsFinite (q ∣_ U.1) ∧ Etale (q ∣_ U.1) := by
    rintro ⟨U, hU⟩
    let c := (quotientOpenCover hTf).f ⟨U, hU⟩
    let φ := (invariantDiagramMap hTf).app (op ⟨U, hU⟩)
    have hrange : Set.range (q ⁻¹ᵁ U).ι = Set.range c := by
      rw [Scheme.Opens.range_ι]
      exact congr_arg SetLike.coe (fromQuotient_preimage hTf ⟨U, hU⟩)
    let e₁ := IsOpenImmersion.isoOfRangeEq (q ⁻¹ᵁ U).ι c hrange
    have hcomm : e₁.hom ≫ Spec.map φ = (q ∣_ U) ≫ hU.isoSpec.hom := by
      rw [← cancel_mono hU.fromSpec, Category.assoc, Category.assoc, IsAffineOpen.fromSpec,
        Iso.hom_inv_id_assoc, morphismRestrict_ι]
      have := ι_fromQuotient hTf ⟨U, hU⟩
      change c ≫ q = Spec.map φ ≫ hU.fromSpec at this
      rw [IsAffineOpen.fromSpec] at this
      rw [← this, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
    let E : Arrow.mk (q ∣_ U) ≅ Arrow.mk (Spec.map φ) := Arrow.isoMk e₁ hU.isoSpec hcomm
    obtain ⟨h₁, h₂⟩ := finite_etale_invariantDiagramMap_app hT hTf U hU
    exact ⟨(MorphismProperty.arrow_mk_iso_iff @IsFinite E).mpr ((IsFinite.SpecMap_iff _).mpr h₁),
      (MorphismProperty.arrow_mk_iso_iff @Etale E).mpr (HasRingHomProperty.Spec_iff.mpr h₂)⟩
  have hU : ⨆ U : S.affineOpens, (U : S.Opens) = ⊤ := iSup_affineOpens_eq_top S
  exact ⟨IsZariskiLocalAtTarget.of_iSup_eq_top _ hU fun U ↦ (key U).1,
    IsZariskiLocalAtTarget.of_iSup_eq_top _ hU fun U ↦ (key U).2⟩

end FiniteEtale

end SGA.SGA1.ExposeV

namespace SGA.SGA1.ExposeV

section Points

variable {P Y : Scheme.{u}}

/-- A point `w` of `P` over the image of a geometric point `y : Spec Ω ⟶ Y`, with `Ω` separably
closed and `κ(w)` separable over `κ(π w)`, is the image of a geometric point of `P` over `y`. -/
lemma exists_geometricPoint_lift_of_isSeparable (π : P ⟶ Y) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y) (w : P) (hw : π w = y (IsLocalRing.closedPoint Ω))
    (hsep : letI := (π.residueFieldMap w).hom.toAlgebra
      Algebra.IsSeparable (Y.residueField (π w)) (P.residueField w)) :
    ∃ w' : Spec (.of Ω) ⟶ P, w' ≫ π = y ∧ w' (IsLocalRing.closedPoint Ω) = w := by
  let φ := Y.descResidueField (Scheme.stalkClosedPointTo y)
  have hy : Spec.map φ ≫ Y.fromSpecResidueField _ = y :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω Y y
  let φ' := (Y.residueFieldCongr hw).hom ≫ φ
  let _ : Algebra (Y.residueField (π w)) (P.residueField w) := (π.residueFieldMap w).hom.toAlgebra
  let _ : Algebra (Y.residueField (π w)) Ω := φ'.hom.toAlgebra
  let l := IsSepClosed.lift (K := Y.residueField (π w)) (L := P.residueField w) (M := Ω)
  let ψ : P.residueField w ⟶ .of Ω := CommRingCat.ofHom l.toRingHom
  have hψ : π.residueFieldMap w ≫ ψ = φ' := by
    ext a
    exact l.commutes a
  refine ⟨Spec.map ψ ≫ P.fromSpecResidueField w, ?_, Scheme.fromSpecResidueField_apply w _⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc, hψ, Spec.map_comp_assoc, Scheme.residueFieldCongr_fromSpecResidueField,
    hy]

/-- If `p ≫ q` is étale, the residue extensions of `p` are separable. -/
lemma isSeparable_residueFieldMap_of_etale_comp {X Q S : Scheme.{u}} (p : X ⟶ Q) (q : Q ⟶ S)
    [Etale (p ≫ q)] (x : X) :
    letI := (p.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Q.residueField (p x)) (X.residueField x) := by
  let K := S.residueField ((p ≫ q) x)
  let _ : Algebra K (Q.residueField (p x)) :=
    RingHom.toAlgebra (show K →+* Q.residueField (p x) from (q.residueFieldMap (p x)).hom)
  let _ : Algebra (Q.residueField (p x)) (X.residueField x) := (p.residueFieldMap x).hom.toAlgebra
  let _ : Algebra K (X.residueField x) := ((p ≫ q).residueFieldMap x).hom.toAlgebra
  have : Algebra.IsSeparable K (X.residueField x) := inferInstance
  have : IsScalarTower K (Q.residueField (p x)) (X.residueField x) :=
    .of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        Scheme.residueFieldMap_comp]
      rfl)
  exact Algebra.isSeparable_tower_top_of_isSeparable K (Q.residueField (p x)) (X.residueField x)

end Points

end SGA.SGA1.ExposeV

namespace SGA.SGA1.ExposeV

section Conjugate

variable {G : Type*} [Group G] [Finite G] {X Q : Scheme.{u}} {T : G → (X ⟶ X)}
  (hT : IsRightAction T) {p : X ⟶ Q} (hTp : ∀ g, T g ≫ p = p)

include hT in
/-- Two points `x₁ x₂ : Spec Ω ⟶ W` of an affine scheme `W` with a right action of `G` which have
the same image in `Spec Γ(W)^G` differ by an element of `G`. -/
lemma exists_comp_eq_of_isAffine [IsAffine X] {Ω : Type u} [Field Ω]
    (x₁ x₂ : Spec (.of Ω) ⟶ X)
    (h : letI := sectionsAction hT ⊤ fun _ ↦ le_top
      x₁ ≫ X.isoSpec.hom ≫ specMap Γ(X, ⊤) (.of (FixedPoints.subring Γ(X, ⊤) G)) =
        x₂ ≫ X.isoSpec.hom ≫ specMap Γ(X, ⊤) (.of (FixedPoints.subring Γ(X, ⊤) G))) :
    ∃ g, x₁ ≫ T g = x₂ := by
  let A : CommRingCat.{u} := Γ(X, ⊤)
  let _ : MulSemiringAction G A := sectionsAction hT ⊤ fun _ ↦ le_top
  let B : CommRingCat.{u} := .of (FixedPoints.subring A G)
  obtain ⟨a₁, ha₁⟩ := Spec.map_surjective (x₁ ≫ X.isoSpec.hom)
  obtain ⟨a₂, ha₂⟩ := Spec.map_surjective (x₂ ≫ X.isoSpec.hom)
  have hB : CommRingCat.ofHom (algebraMap B A) ≫ a₁ = CommRingCat.ofHom (algebraMap B A) ≫ a₂ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, ha₁, ha₂]
    simpa only [Category.assoc] using h
  obtain ⟨g, hg⟩ := exists_eq_comp_smul_of_comp_eq (B := B) G a₁.hom a₂.hom
    (congr_arg CommRingCat.Hom.hom hB)
  refine ⟨g, ?_⟩
  rw [← cancel_mono X.isoSpec.hom, Category.assoc, isoSpec_hom_comp_specAction hT, ← ha₂,
    ← Category.assoc, ← ha₁, specAction, ← Spec.map_comp]
  congr 1
  ext t
  exact (hg t).symm

include hT in
/-- V.1.1 (iii), V.2, on points with values in a field: under the hypotheses of V.1.3, two
points `x₁ x₂ : Spec Ω ⟶ X` with the same image in `Y = X/G` differ by an element of `G`. -/
lemma exists_comp_eq_of_comp_eq [IsAffineHom p]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U) {Ω : Type u} [Field Ω]
    (x₁ x₂ : Spec (.of Ω) ⟶ X) (h : x₁ ≫ p = x₂ ≫ p) : ∃ g, x₁ ≫ T g = x₂ := by
  obtain ⟨V, hV, hz⟩ := exists_isAffineOpen_mem ((x₁ ≫ p) (IsLocalRing.closedPoint Ω))
  let W := p ⁻¹ᵁ V
  have : IsAffine W.toScheme := hV.preimage p
  have hmem : ∀ x : Spec (.of Ω) ⟶ X, x ≫ p = x₁ ≫ p → Set.range x ⊆ Set.range W.ι := by
    rintro x hx _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain rfl : t = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    change (x ≫ p) _ ∈ V
    rwa [hx]
  let x₁' := IsOpenImmersion.lift W.ι x₁ (hmem x₁ rfl)
  let x₂' := IsOpenImmersion.lift W.ι x₂ (hmem x₂ h.symm)
  have hR := isRightAction_restrictAction hTp hT V
  have hq := isQuotient_restrict hTp hT (fun U _ ↦ hsec U) V
  let A : CommRingCat.{u} := Γ(W.toScheme, ⊤)
  let _ : MulSemiringAction G A := sectionsAction hR ⊤ fun _ ↦ le_top
  let B : CommRingCat.{u} := .of (FixedPoints.subring A G)
  have hq' : IsQuotient (restrictAction hTp V) (W.toScheme.isoSpec.hom ≫ specMap A B) :=
    (isQuotient_specMap (G := G) (B := B) Subtype.val_injective).iso_comp _
      (isoSpec_hom_comp_specAction hR)
  have e := hq.comp_uniqueIso_hom hq'
  have h' : x₁' ≫ p ∣_ V = x₂' ≫ p ∣_ V := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc, h]
  obtain ⟨g, hg⟩ := exists_comp_eq_of_isAffine hR x₁' x₂' (by rw [← e, reassoc_of% h'])
  refine ⟨g, ?_⟩
  have h₁ : x₁' ≫ W.ι = x₁ := IsOpenImmersion.lift_fac _ _ _
  have h₂ : x₂' ≫ W.ι = x₂ := IsOpenImmersion.lift_fac _ _ _
  rw [← h₁, ← h₂, ← hg, Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι]

end Conjugate

end SGA.SGA1.ExposeV

namespace SGA.SGA1.ExposeV

section Statements

variable {G : Type*} [Group G] [Finite G] {X S : Scheme.{u}} {T : G → (X ⟶ X)}
  (hT : IsRightAction T) {f : X ⟶ S} (hTf : ∀ g, T g ≫ f = f)

include hT in
/-- V.3.2 when `X` is finite étale over `S`: the quotient morphism `X ⟶ X/G` is étale. -/
theorem etale_toQuotient [IsFinite f] [Etale f] : Etale (toQuotient hTf) := by
  have := (finite_etale_fromQuotient hT hTf).2
  have : Etale (toQuotient hTf ≫ fromQuotient hTf) := by
    rw [toQuotient_fromQuotient]
    infer_instance
  exact Etale.of_comp _ (fromQuotient hTf)

include hT in
/-- V.3.4 for an arbitrary quotient `p : X ⟶ Z`: `Z` is finite étale over `S`. -/
theorem finite_etale_desc_of_isQuotient [IsFinite f] [Etale f] {Z : Scheme.{u}} {p : X ⟶ Z}
    (hp : IsQuotient T p) : IsFinite (hp.desc f hTf) ∧ Etale (hp.desc f hTf) := by
  have hq := isQuotient_toQuotient hTf hT
  obtain ⟨h₁, h₂⟩ := finite_etale_fromQuotient hT hTf
  have : hp.desc f hTf = (hp.uniqueIso hq).hom ≫ fromQuotient hTf :=
    hp.hom_ext (by rw [hp.fac, IsQuotient.comp_uniqueIso_hom_assoc, toQuotient_fromQuotient])
  rw [this]
  exact ⟨inferInstance, inferInstance⟩

include hT hTf in
/-- V.3.2 when `X` is finite étale over `S`, for an arbitrary quotient `p : X ⟶ Z`. -/
theorem etale_of_isQuotient [IsFinite f] [Etale f] {Z : Scheme.{u}} {p : X ⟶ Z}
    (hp : IsQuotient T p) : Etale p := by
  have := (finite_etale_desc_of_isQuotient hT hTf hp).2
  have : Etale (p ≫ hp.desc f hTf) := by
    rw [hp.fac]
    infer_instance
  exact Etale.of_comp _ (hp.desc f hTf)

include hT hTf in
/-- V.3.1, admissibility: if `X` is étale, separated and quasi-compact over `S` (no noetherian
hypothesis), then `G` acts admissibly. As in SGA, `X` is quasi-affine (hence quasi-projective)
over `S` by VIII.6.2, and V.1.8 applies. -/
theorem isAdmissible_of_etale [Etale f] [IsSeparated f] [QuasiCompact f] : IsAdmissible T := by
  have := SGA.SGA1.ExposeVIII.isQuasiAffineHom_of_quasiFinite f
  exact isAdmissible_of_isQuasiAffineHom hT f hTf

end Statements

/-- V.3.4 holds, for any base (the noetherian hypothesis is not used). -/
theorem finiteEtaleQuotientStatement : FiniteEtaleQuotientStatement.{u} := by
  intro X Y f _ _ _ G _ _ T hT hf Z p hp
  exact finite_etale_desc_of_isQuotient hT hf hp

end SGA.SGA1.ExposeV
