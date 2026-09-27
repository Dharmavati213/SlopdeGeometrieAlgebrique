/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import SGA.Foundations.Projective.LineBundleIso
import SGA.Foundations.Projective.SectionsBaseChange

/-!
# Homomorphisms of section rings

Ring homomorphisms between the graded rings `Γ_*(L) = ⊕ₙ Γ(X, L^{⊗n})` induced by inverse images
of line bundles along morphisms (`Scheme.LineBundle.sectionRingMapOf`) and by isomorphisms of
line bundles (`Scheme.LineBundle.Iso.sectionRingHom`), and flat base change for section rings:
for `X' = X ×_Y Y'` with `Y' ⟶ Y` a flat morphism of affine schemes and `X` quasi-compact and
quasi-separated, `Γ_*(L') = Γ(Y') ⊗_{Γ(Y)} Γ_*(L)` (`isPushout_sectionRingMapOf`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct DirectSum

namespace AlgebraicGeometry.Scheme.LineBundle

section SectionRingHom

variable {X₁ X₂ : Scheme.{u}} (L₁ : X₁.LineBundle) (L₂ : X₂.LineBundle) (R₁ R₂ : Type u)
  [CommRing R₁] [Algebra R₁ Γ(X₁, ⊤)] [CommRing R₂] [Algebra R₂ Γ(X₂, ⊤)]

/-- The ring homomorphism `Γ_*(L₁) → Γ_*(L₂)` defined by additive maps between the sections of
`L₁^{⊗n}` and of `L₂^{⊗n}` for all `n`, compatible with the unit and the products. -/
noncomputable def sectionRingHom
    (F : ∀ n, L₁.sectionSubmodule R₁ n →+ L₂.sectionSubmodule R₂ n)
    (hone : ∀ h, (F 0 ⟨1, h⟩ : L₂.Fam ⊤) = 1)
    (hmul : ∀ {m n : ℕ} (s : L₁.sectionSubmodule R₁ m) (t : L₁.sectionSubmodule R₁ n) h,
      (F (m + n) ⟨s.1 * t.1, h⟩ : L₂.Fam ⊤) = (F m s : L₂.Fam ⊤) * F n t) :
    L₁.sectionRing R₁ →+* L₂.sectionRing R₂ :=
  DirectSum.toSemiring (fun n ↦ (DirectSum.of _ n).comp (F n))
    (by
      change DirectSum.of _ 0 _ = DirectSum.of _ 0 _
      congr 1
      exact Subtype.ext (hone _))
    (fun {i j} a b ↦ by
      change DirectSum.of _ (i + j) _ = DirectSum.of _ i _ * DirectSum.of _ j _
      rw [DirectSum.of_mul_of]
      congr 1
      exact Subtype.ext (hmul a b _))

variable {L₁ L₂ R₁ R₂}

lemma sectionRingHom_of (F : ∀ n, L₁.sectionSubmodule R₁ n →+ L₂.sectionSubmodule R₂ n) (hone)
    (hmul) (n : ℕ) (s : L₁.sectionSubmodule R₁ n) :
    sectionRingHom L₁ L₂ R₁ R₂ F hone hmul (DirectSum.of _ n s) = DirectSum.of _ n (F n s) :=
  DirectSum.toSemiring_of _ _ _ _ _

lemma sectionRingHom_mem (F : ∀ n, L₁.sectionSubmodule R₁ n →+ L₂.sectionSubmodule R₂ n) (hone)
    (hmul) {n : ℕ} {x : L₁.sectionRing R₁} (hx : x ∈ L₁.sectionGrading R₁ n) :
    sectionRingHom L₁ L₂ R₁ R₂ F hone hmul x ∈ L₂.sectionGrading R₂ n := by
  obtain ⟨s, rfl⟩ := hx
  change sectionRingHom L₁ L₂ R₁ R₂ F hone hmul (DirectSum.of _ n s) ∈ _
  rw [sectionRingHom_of]
  exact DirectSum.of_mem_lofGrading _ n _

lemma sectionRingHom_ofIsSection (F : ∀ n, L₁.sectionSubmodule R₁ n →+ L₂.sectionSubmodule R₂ n)
    (hone) (hmul) {n : ℕ} (s : L₁.Fam ⊤) (hs : L₁.IsSection n ⊤ s) :
    sectionRingHom L₁ L₂ R₁ R₂ F hone hmul (L₁.ofIsSection s hs) =
      L₂.ofIsSection (F n ⟨s, hs⟩).1 (F n ⟨s, hs⟩).2 :=
  sectionRingHom_of F hone hmul n ⟨s, hs⟩

end SectionRingHom

section SectionRingMapOf

variable {X T T' : Scheme.{u}} (L : X.LineBundle) {b : T ⟶ X} {c : T' ⟶ X} (t : T' ⟶ T)
  (hc : t ≫ b = c) (R : Type u) [CommRing R] [Algebra R Γ(T, ⊤)] (R' : Type u) [CommRing R']
  [Algebra R' Γ(T', ⊤)]

/-- The inverse image `Γ(T, (b*L)^{⊗n}) → Γ(T', (c*L)^{⊗n})` along `t`, for `c = t ≫ b`. -/
noncomputable def pullAddOf (n : ℕ) :
    (L.pullback b).sectionSubmodule R n →+ (L.pullback c).sectionSubmodule R' n where
  toFun s := ⟨L.famPullbackOf t hc t.preimage_top.ge s.1, s.2.famPullbackOf t hc _⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The ring homomorphism `Γ_*(b*L) → Γ_*(c*L)` given by the inverse image along `t`, for
`c = t ≫ b`. -/
noncomputable def sectionRingMapOf :
    (L.pullback b).sectionRing R →+* (L.pullback c).sectionRing R' :=
  sectionRingHom _ _ R R' (L.pullAddOf t hc R R') (fun _ ↦ map_one _) fun _ _ _ ↦ map_mul _ _ _

variable {L t hc R R'}

lemma sectionRingMapOf_of (n : ℕ) (s : (L.pullback b).sectionSubmodule R n) :
    L.sectionRingMapOf t hc R R' (DirectSum.of _ n s) =
      DirectSum.of _ n ⟨L.famPullbackOf t hc t.preimage_top.ge s.1, s.2.famPullbackOf t hc _⟩ :=
  sectionRingHom_of _ _ _ n s

lemma coeFam_sectionRingMapOf (x : (L.pullback b).sectionRing R) :
    (L.pullback c).coeFam R' (L.sectionRingMapOf t hc R R' x) =
      L.famPullbackOf t hc t.preimage_top.ge ((L.pullback b).coeFam R x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n s =>
    rw [sectionRingMapOf_of]
    simp only [coeFam_of]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma sectionRingMapOf_mem {n : ℕ} {x : (L.pullback b).sectionRing R}
    (hx : x ∈ (L.pullback b).sectionGrading R n) :
    L.sectionRingMapOf t hc R R' x ∈ (L.pullback c).sectionGrading R' n :=
  sectionRingHom_mem _ _ _ hx

lemma sectionRingMapOf_ofIsSection {n : ℕ} (s : (L.pullback b).Fam ⊤)
    (hs : (L.pullback b).IsSection n ⊤ s) :
    L.sectionRingMapOf t hc R R' ((L.pullback b).ofIsSection s hs) =
      (L.pullback c).ofIsSection (L.famPullbackOf t hc t.preimage_top.ge s)
        (hs.famPullbackOf t hc _) :=
  sectionRingHom_ofIsSection _ _ _ s hs

lemma sectionRingMapOf_comp {T'' : Scheme.{u}} {d : T'' ⟶ X} (t' : T'' ⟶ T') (hd : t' ≫ c = d)
    (R'' : Type u) [CommRing R''] [Algebra R'' Γ(T'', ⊤)] (x : (L.pullback b).sectionRing R) :
    L.sectionRingMapOf t' hd R' R'' (L.sectionRingMapOf t hc R R' x) =
      L.sectionRingMapOf (t' ≫ t) (by rw [Category.assoc, hc, hd]) R R'' x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n s =>
    rw [sectionRingMapOf_of, sectionRingMapOf_of, sectionRingMapOf_of]
    congr 2
    exact famPullbackOf_famPullbackOf t hc t' hd _ _ s.1
  | add x y hx hy => simp only [map_add, hx, hy]

lemma sectionRingMapOf_congr {t₁ t₂ : T' ⟶ T} (ht : t₁ = t₂) (hc₁ : t₁ ≫ b = c)
    (hc₂ : t₂ ≫ b = c) (x : (L.pullback b).sectionRing R) :
    L.sectionRingMapOf t₁ hc₁ R R' x = L.sectionRingMapOf t₂ hc₂ R R' x := by
  subst ht
  rfl

lemma sectionRingMapOf_id (hc : 𝟙 T ≫ b = b) (x : (L.pullback b).sectionRing R) :
    L.sectionRingMapOf (𝟙 T) hc R R x = x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n s =>
    rw [sectionRingMapOf_of]
    congr 1
    exact Subtype.ext ((famPullbackOf_id hc _ s.1).trans (famRes_self _ _))
  | add x y hx hy => simp only [map_add, hx, hy]

end SectionRingMapOf

namespace Iso

variable {X : Scheme.{u}} {L M : X.LineBundle} (e : L.Iso M) (R : Type u) [CommRing R]
  [Algebra R Γ(X, ⊤)]

/-- The image under `e` of sections of `L^{⊗n}` over `X`. -/
noncomputable def mapAdd (n : ℕ) : L.sectionSubmodule R n →+ M.sectionSubmodule R n where
  toFun s := ⟨e.mapFam s.2, e.isSection_mapFam s.2⟩
  map_zero' := Subtype.ext (e.mapFam_zero (isSection_zero _))
  map_add' s t := Subtype.ext (e.mapFam_add s.2 t.2)

/-- The ring homomorphism `Γ_*(L) → Γ_*(M)` induced by an isomorphism `e : L ≅ M`. -/
noncomputable def sectionRingHom : L.sectionRing R →+* M.sectionRing R :=
  LineBundle.sectionRingHom L M R R (e.mapAdd R)
    (fun h ↦ by
      change e.mapFam (s := (1 : L.Fam ⊤)) h = 1
      rw [e.mapFam_congr h ((isSection_famConst (L := L) 1).of_eq Nat.cast_zero.symm)
        (map_one (L.famConst ⊤)).symm, e.mapFam_famConst, map_one])
    (fun s t h ↦ by
      change e.mapFam (s := s.1 * t.1) h = e.mapFam (s := s.1) s.2 * e.mapFam (s := t.1) t.2
      exact e.mapFam_mul s.2 t.2)

variable {e R}

lemma sectionRingHom_of (n : ℕ) (s : L.sectionSubmodule R n) :
    e.sectionRingHom R (DirectSum.of _ n s) =
      DirectSum.of _ n ⟨e.mapFam s.2, e.isSection_mapFam s.2⟩ :=
  LineBundle.sectionRingHom_of (e.mapAdd R) _ _ n s

lemma sectionRingHom_mem {n : ℕ} {x : L.sectionRing R} (hx : x ∈ L.sectionGrading R n) :
    e.sectionRingHom R x ∈ M.sectionGrading R n :=
  LineBundle.sectionRingHom_mem (e.mapAdd R) _ _ hx

lemma sectionRingHom_ofIsSection {n : ℕ} (s : L.Fam ⊤) (hs : L.IsSection n ⊤ s) :
    e.sectionRingHom R (L.ofIsSection s hs) =
      M.ofIsSection (e.mapFam hs) (e.isSection_mapFam hs) :=
  LineBundle.sectionRingHom_ofIsSection (e.mapAdd R) _ _ s hs

lemma symm_sectionRingHom_sectionRingHom (x : L.sectionRing R) :
    e.symm.sectionRingHom R (e.sectionRingHom R x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n s =>
    rw [sectionRingHom_of, sectionRingHom_of]
    congr 1
    exact Subtype.ext (e.mapFam_symm_mapFam s.2)
  | add x y hx hy => simp only [map_add, hx, hy]

lemma sectionRingHom_symm_sectionRingHom (x : M.sectionRing R) :
    e.sectionRingHom R (e.symm.sectionRingHom R x) = x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n s =>
    rw [sectionRingHom_of, sectionRingHom_of]
    congr 1
    exact Subtype.ext (e.mapFam_mapFam_symm s.2)
  | add x y hx hy => simp only [map_add, hx, hy]

variable (e R) in
/-- The isomorphism `Γ_*(L) ≅ Γ_*(M)` induced by an isomorphism `e : L ≅ M`. -/
noncomputable def sectionRingEquiv : L.sectionRing R ≃+* M.sectionRing R :=
  RingEquiv.ofRingHom (e.sectionRingHom R) (e.symm.sectionRingHom R)
    (RingHom.ext e.sectionRingHom_symm_sectionRingHom)
    (RingHom.ext e.symm_sectionRingHom_sectionRingHom)

lemma mapFam_algebraMap (r : R)
    (h : L.IsSection ((0 : ℕ) : ℤ) ⊤ (algebraMap R (L.Fam ⊤) r)) :
    e.mapFam h = algebraMap R (M.Fam ⊤) r := by
  have h' : L.IsSection ((0 : ℕ) : ℤ) ⊤
      (L.famConst ⊤ (X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op
        (algebraMap R Γ(X, ⊤) r))) := h
  rw [e.mapFam_congr h h' (algebraMap_fam L R ⊤ r), e.mapFam_famConst, algebraMap_fam]

lemma sectionRingHom_algebraMap (r : R) :
    e.sectionRingHom R (algebraMap R (L.sectionRing R) r) = algebraMap R (M.sectionRing R) r := by
  rw [DirectSum.algebraMap_apply, DirectSum.algebraMap_apply]
  refine (sectionRingHom_of 0 _).trans ?_
  congr 1
  exact Subtype.ext (e.mapFam_algebraMap r
    (DirectSum.GAlgebra.toFun (A := fun i ↦ L.sectionSubmodule R i) r).2)

end Iso

section SectionRingMapOfAlgebraMap

variable {X T T' : Scheme.{u}} {L : X.LineBundle} {b : T ⟶ X} {c : T' ⟶ X} {t : T' ⟶ T}
  {hc : t ≫ b = c} {R : Type u} [CommRing R] [Algebra R Γ(T, ⊤)] {R' : Type u} [CommRing R']
  [Algebra R' Γ(T', ⊤)]

set_option backward.isDefEq.respectTransparency false in
lemma sectionRingMapOf_algebraMap (r : R) (r' : R')
    (h : t.appTop (algebraMap R Γ(T, ⊤) r) = algebraMap R' Γ(T', ⊤) r') :
    L.sectionRingMapOf t hc R R' (algebraMap R ((L.pullback b).sectionRing R) r) =
      algebraMap R' ((L.pullback c).sectionRing R') r' := by
  rw [DirectSum.algebraMap_apply, DirectSum.algebraMap_apply, sectionRingMapOf_of]
  congr 1
  refine Subtype.ext ?_
  change L.famPullbackOf t hc _ (algebraMap R ((L.pullback b).Fam ⊤) r) =
    algebraMap R' ((L.pullback c).Fam ⊤) r'
  subst hc
  rw [famPullbackOf_eq_famPullback, algebraMap_fam, famPullback_famConst, algebraMap_fam, ← h]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE]

end SectionRingMapOfAlgebraMap

section BaseChange

variable {X X' Y Y' Z : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {fst : X' ⟶ X} {snd : X' ⟶ Y'}
  (L : Z.LineBundle) (b : X ⟶ Z)
  [Algebra Γ(Y, ⊤) Γ(X, ⊤)] [Algebra Γ(Y', ⊤) Γ(X', ⊤)] [Algebra Γ(Y, ⊤) Γ(Y', ⊤)]
  [Algebra Γ(Y, ⊤) Γ(X', ⊤)] [IsScalarTower Γ(Y, ⊤) Γ(Y', ⊤) Γ(X', ⊤)]
  (hf : algebraMap Γ(Y, ⊤) Γ(X, ⊤) = f.appTop.hom)
  (hsnd : algebraMap Γ(Y', ⊤) Γ(X', ⊤) = snd.appTop.hom)
  (hg : algebraMap Γ(Y, ⊤) Γ(Y', ⊤) = g.appTop.hom)

include hf hsnd hg in
/-- The inverse image `Γ(X, (b*L)^{⊗n}) → Γ(X', ((fst ≫ b)*L)^{⊗n})` along the first projection of
a cartesian square, as a `Γ(Y)`-linear map. -/
noncomputable def pullLinOf (H : IsPullback fst snd f g) (n : ℕ) :
    (L.pullback b).sectionSubmodule Γ(Y, ⊤) n →ₗ[Γ(Y, ⊤)]
      (L.pullback (fst ≫ b)).sectionSubmodule Γ(Y', ⊤) n where
  toFun s := ⟨L.famPullbackOf fst rfl fst.preimage_top.ge s.1, s.2.famPullbackOf fst rfl _⟩
  map_add' s t := Subtype.ext (map_add _ _ _)
  map_smul' r s := Subtype.ext <| by
    change (L.pullback b).famPullback fst fst.preimage_top.ge (r • s.1) =
      r • (L.pullback b).famPullback fst fst.preimage_top.ge s.1
    rw [Algebra.smul_def, Algebra.smul_def, map_mul,
      famPullback_algebraMap fst (hR := appTop_algebraMap_of_isPullback hf hsnd hg H)]



set_option backward.isDefEq.respectTransparency false in
include hf hsnd hg in
lemma isBaseChange_pullLinOf (H : IsPullback fst snd f g) [IsAffine Y] [IsAffine Y'] [Flat g]
    [CompactSpace X] [QuasiSeparatedSpace X] (n : ℕ) :
    IsBaseChange Γ(Y', ⊤) (L.pullLinOf b hf hsnd hg H n) := by
  have hbc := (L.pullback b).isBaseChange_pullLin hf hsnd hg H (n : ℤ)
  let e : ((L.pullback b).pullback fst).sectionSubmoduleOn Γ(Y', ⊤) n ⊤ ≃ₗ[Γ(Y', ⊤)]
      (L.pullback (fst ≫ b)).sectionSubmodule Γ(Y', ⊤) n :=
    { toFun x := ⟨x.1, isSection_pullback_comp_iff.mpr x.2⟩
      invFun x := ⟨x.1, isSection_pullback_comp_iff.mp x.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      left_inv _ := rfl
      right_inv _ := rfl }
  have : L.pullLinOf b hf hsnd hg H n = (e.toLinearMap.restrictScalars Γ(Y, ⊤)).comp
      ((L.pullback b).pullLin Γ(Y, ⊤) fst Γ(Y', ⊤)
        (appTop_algebraMap_of_isPullback hf hsnd hg H) n fst.preimage_top.ge) :=
    LinearMap.ext fun _ ↦ rfl
  rw [this]
  exact hbc.comp (IsBaseChange.ofEquiv e)

set_option backward.isDefEq.respectTransparency false in
include hf hsnd hg in
/-- Flat base change for section rings: for a cartesian square `X' = X ×_Y Y'` with `Y' ⟶ Y` a
flat morphism of affine schemes and `X` quasi-compact and quasi-separated,
`Γ_*((fst ≫ b)*L) = Γ(Y') ⊗_{Γ(Y)} Γ_*(b*L)`. -/
theorem isPushout_sectionRingMapOf (H : IsPullback fst snd f g) [IsAffine Y] [IsAffine Y']
    [Flat g] [CompactSpace X] [QuasiSeparatedSpace X] {c : X' ⟶ Z} (hc : fst ≫ b = c) :
    IsPushout (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) ((L.pullback b).sectionRing Γ(Y, ⊤))))
      g.appTop (CommRingCat.ofHom (L.sectionRingMapOf fst hc
        (R := ((Γ(Y, ⊤) : CommRingCat) : Type u)) (R' := ((Γ(Y', ⊤) : CommRingCat) : Type u))))
      (CommRingCat.ofHom (algebraMap Γ(Y', ⊤) ((L.pullback c).sectionRing Γ(Y', ⊤)))) := by
  subst hc
  classical
  have hbc : IsBaseChange Γ(Y', ⊤) (DirectSum.lmap (L.pullLinOf b hf hsnd hg H)) :=
    IsBaseChange.directSum fun n ↦ L.isBaseChange_pullLinOf b hf hsnd hg H n
  have hmap (x : (L.pullback b).sectionRing Γ(Y, ⊤)) :
      DirectSum.lmap (L.pullLinOf b hf hsnd hg H) x =
        L.sectionRingMapOf fst rfl Γ(Y, ⊤) Γ(Y', ⊤) x := by
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of n s =>
      rw [DirectSum.lmap_of, sectionRingMapOf_of]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  let : Algebra ((L.pullback b).sectionRing Γ(Y, ⊤))
      ((L.pullback (fst ≫ b)).sectionRing Γ(Y', ⊤)) :=
    (L.sectionRingMapOf fst rfl Γ(Y, ⊤) Γ(Y', ⊤)).toAlgebra
  have hsmul (r : Γ(Y, ⊤)) (x : (L.pullback (fst ≫ b)).sectionRing Γ(Y', ⊤)) :
      r • x = algebraMap Γ(Y, ⊤) Γ(Y', ⊤) r • x := by
    rw [algebraMap_smul]
  let : Algebra Γ(Y, ⊤) ((L.pullback (fst ≫ b)).sectionRing Γ(Y', ⊤)) :=
    Algebra.ofModule (fun r x y ↦ by rw [hsmul, hsmul, smul_mul_assoc])
      (fun r x y ↦ by rw [hsmul, hsmul, mul_smul_comm])
  have : IsScalarTower Γ(Y, ⊤) ((L.pullback b).sectionRing Γ(Y, ⊤))
      ((L.pullback (fst ≫ b)).sectionRing Γ(Y', ⊤)) := by
    refine ⟨fun r c d ↦ ?_⟩
    change L.sectionRingMapOf fst rfl Γ(Y, ⊤) Γ(Y', ⊤) (r • c) * d =
      r • (L.sectionRingMapOf fst rfl Γ(Y, ⊤) Γ(Y', ⊤) c * d)
    rw [← hmap, map_smul, hmap, hsmul, hsmul, smul_mul_assoc]
  have hpush : Algebra.IsPushout Γ(Y, ⊤) Γ(Y', ⊤) ((L.pullback b).sectionRing Γ(Y, ⊤))
      ((L.pullback (fst ≫ b)).sectionRing Γ(Y', ⊤)) := by
    refine ⟨?_⟩
    convert hbc using 1
    all_goals try rfl
    refine LinearMap.ext fun x ↦ ?_
    exact (hmap x).symm
  have := CommRingCat.isPushout_of_isPushout Γ(Y, ⊤) Γ(Y', ⊤)
    ((L.pullback b).sectionRing Γ(Y, ⊤)) ((L.pullback (fst ≫ b)).sectionRing Γ(Y', ⊤))
  have e : g.appTop = CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(Y', ⊤)) := by
    rw [hg]
    rfl
  rw [e]
  exact this.flip

end BaseChange

section BaseRing

variable {Z T : Scheme.{u}} (L : Z.LineBundle) (c : T ⟶ Z) (R₁ R₂ : Type u) [CommRing R₁]
  [Algebra R₁ Γ(T, ⊤)] [CommRing R₂] [Algebra R₂ Γ(T, ⊤)]

lemma sectionRingMapOf_id_comp (x : (L.pullback c).sectionRing R₁) :
    L.sectionRingMapOf (𝟙 T) (Category.id_comp c) R₂ R₁
      (L.sectionRingMapOf (𝟙 T) (Category.id_comp c) R₁ R₂ x) = x := by
  rw [sectionRingMapOf_comp]
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n s =>
    rw [sectionRingMapOf_of]
    congr 1
    exact Subtype.ext ((famPullbackOf_id _ _ s.1).trans (famRes_self _ _))
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The identification of `Γ_*(c*L)` over two base rings. -/
noncomputable def sectionRingBaseIso :
    CommRingCat.of ((L.pullback c).sectionRing R₁) ≅ CommRingCat.of ((L.pullback c).sectionRing R₂)
    where
  hom := CommRingCat.ofHom (L.sectionRingMapOf (𝟙 T) (Category.id_comp c) R₁ R₂)
  inv := CommRingCat.ofHom (L.sectionRingMapOf (𝟙 T) (Category.id_comp c) R₂ R₁)
  hom_inv_id := CommRingCat.hom_ext (RingHom.ext fun x ↦ sectionRingMapOf_id_comp L c R₁ R₂ x)
  inv_hom_id := CommRingCat.hom_ext (RingHom.ext fun x ↦ sectionRingMapOf_id_comp L c R₂ R₁ x)

end BaseRing

section BaseChangeOwn

/-- A commutative ring `R` is isomorphic to `CommRingCat.of R`. -/
def _root_.CommRingCat.ofSelfIso (R : CommRingCat.{u}) : CommRingCat.of R ≅ R :=
  CategoryTheory.Iso.refl R

variable {X X' Y Y' Z : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {fst : X' ⟶ X} {snd : X' ⟶ Y'}
  (L : Z.LineBundle) (b : X ⟶ Z)

set_option backward.isDefEq.respectTransparency false in
/-- Flat base change for section rings, with each section ring over the ring of global functions
of its scheme: for `X' = X ×_Y Y'` with `Y' ⟶ Y` a flat morphism of affine schemes and `X`
quasi-compact and quasi-separated, `Γ_*(c*L) = Γ(Y') ⊗_{Γ(Y)} Γ_*(b*L)` for `c = fst ≫ b`. -/
theorem isPushout_sectionRingMapOf' (H : IsPullback fst snd f g) [IsAffine Y] [IsAffine Y']
    [Flat g] [CompactSpace X] [QuasiSeparatedSpace X] {c : X' ⟶ Z} (hc : fst ≫ b = c) :
    IsPushout (f.appTop ≫ CommRingCat.ofHom
        (algebraMap Γ(X, ⊤) ((L.pullback b).sectionRing Γ(X, ⊤)))) g.appTop
      (CommRingCat.ofHom (L.sectionRingMapOf fst hc (R := ((Γ(X, ⊤) : CommRingCat) : Type u))
        (R' := ((Γ(X', ⊤) : CommRingCat) : Type u))))
      (snd.appTop ≫ CommRingCat.ofHom
        (algebraMap Γ(X', ⊤) ((L.pullback c).sectionRing Γ(X', ⊤)))) := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(Y', ⊤) Γ(X', ⊤) := snd.appTop.hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(Y', ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(X', ⊤) := (snd.appTop.hom.comp g.appTop.hom).toAlgebra
  have : IsScalarTower Γ(Y, ⊤) Γ(Y', ⊤) Γ(X', ⊤) := .of_algebraMap_eq' rfl
  have h := L.isPushout_sectionRingMapOf b rfl rfl rfl H hc
  refine h.of_iso (CommRingCat.ofSelfIso _) (sectionRingBaseIso L b _ _)
    (CommRingCat.ofSelfIso _) (sectionRingBaseIso L c _ _) ?_ ?_ ?_ ?_
  · refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    exact sectionRingMapOf_algebraMap (L := L) (t := 𝟙 X) (hc := Category.id_comp b) r
      (f.appTop r) rfl
  · rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
    change L.sectionRingMapOf (𝟙 X') _ _ _ (L.sectionRingMapOf fst hc _ _ x) =
      L.sectionRingMapOf fst hc _ _ (L.sectionRingMapOf (𝟙 X) _ _ _ x)
    rw [sectionRingMapOf_comp, sectionRingMapOf_comp]
    exact sectionRingMapOf_congr (by simp) _ _ x
  · refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    exact sectionRingMapOf_algebraMap (L := L) (t := 𝟙 X') (hc := Category.id_comp c) r
      (snd.appTop r) rfl

end BaseChangeOwn

section Ext

variable {T : Scheme.{u}} {M : T.LineBundle} {R : Type u} [CommRing R] [Algebra R Γ(T, ⊤)]
  {A : Type*} [Semiring A]

/-- Ring homomorphisms out of `Γ_*(M)` agreeing on the homogeneous elements are equal. -/
lemma sectionRing_ringHom_ext {φ ψ : M.sectionRing R →+* A}
    (h : ∀ n (s : M.sectionSubmodule R n), φ (DirectSum.of _ n s) = ψ (DirectSum.of _ n s)) :
    φ = ψ := by
  refine RingHom.ext fun x ↦ ?_
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n s => exact h n s
  | add x y hx hy => simp only [map_add, hx, hy]

end Ext

section Components

variable {X₁ X₂ : Scheme.{u}} {L₁ : X₁.LineBundle} {L₂ : X₂.LineBundle} {R₁ R₂ : Type u}
  [CommRing R₁] [Algebra R₁ Γ(X₁, ⊤)] [CommRing R₂] [Algebra R₂ Γ(X₂, ⊤)]

/-- The homogeneous components of the image under `sectionRingHom F` are the images of the
homogeneous components. -/
lemma sectionRingHom_apply (F : ∀ n, L₁.sectionSubmodule R₁ n →+ L₂.sectionSubmodule R₂ n)
    (hone) (hmul) (y : L₁.sectionRing R₁) (k : ℕ) :
    sectionRingHom L₁ L₂ R₁ R₂ F hone hmul y k = F k (y k) := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp only [map_zero, DirectSum.zero_apply]
  | of n s =>
    rw [sectionRingHom_of, DirectSum.of_apply, DirectSum.of_apply]
    split_ifs with h
    · subst h
      rfl
    · exact (map_zero (F k)).symm
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy]

end Components

section Loci

variable {X : Scheme.{u}} {L : X.LineBundle} {V : X.Opens}

lemma _root_.AlgebraicGeometry.Scheme.basicOpen_neg {U : X.Opens} (f : Γ(X, U)) :
    X.basicOpen (-f) = X.basicOpen f := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨m, h⟩ := (X.mem_basicOpen'' _ x).mp hx
    refine (X.mem_basicOpen'' _ x).mpr ⟨m, ?_⟩
    rwa [map_neg, IsUnit.neg_iff] at h
  · obtain ⟨m, h⟩ := (X.mem_basicOpen'' _ x).mp hx
    refine (X.mem_basicOpen'' _ x).mpr ⟨m, ?_⟩
    rwa [map_neg, IsUnit.neg_iff]

lemma famLocus_neg (s : L.Fam V) : L.famLocus V (-s) = L.famLocus V s := by
  simp only [famLocus, Pi.neg_apply, Scheme.basicOpen_neg]

lemma famLocus_sum_le {ι : Type*} (t : Finset ι) (f : ι → L.Fam V) :
    L.famLocus V (∑ i ∈ t, f i) ≤ ⨆ i ∈ t, L.famLocus V (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, famLocus_zero, bot_le]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    refine (famLocus_add_le _ _).trans (sup_le ?_ (ih.trans ?_))
    · exact le_iSup₂_of_le a (Finset.mem_insert_self a t) le_rfl
    · exact iSup₂_mono' fun i hi ↦ ⟨i, Finset.mem_insert_of_mem hi, le_rfl⟩

end Loci

section IsoAmple

variable {X Y : Scheme.{u}} {L M : X.LineBundle}

/-- Ampleness is invariant under isomorphisms of line bundles. -/
theorem IsAmple.of_iso (e : L.Iso M) (hL : L.IsAmple) : M.IsAmple := by
  refine ⟨hL.1, fun x ↦ ?_⟩
  obtain ⟨n, hn, s, hx, ha⟩ := hL.2 x
  have hs := e.isSection_mapFam s.isSection_toFam
  have ht : M.nonvanishingLocus (M.sectionsOfFam _ hs) = L.nonvanishingLocus s := by
    rw [nonvanishingLocus_sectionsOfFam, e.famLocus_mapFam, s.famLocus_toFam]
  exact ⟨n, hn, M.sectionsOfFam _ hs, ht ▸ hx, ht ▸ ha⟩

/-- Relative ampleness is invariant under isomorphisms of line bundles. -/
theorem IsRelativelyAmple.of_iso {f : X ⟶ Y} (e : L.Iso M) (hL : L.IsRelativelyAmple f) :
    M.IsRelativelyAmple f :=
  ⟨hL.1, fun V hV ↦ (hL.2 V hV).of_iso (e.pullback _)⟩

end IsoAmple

end AlgebraicGeometry.Scheme.LineBundle
