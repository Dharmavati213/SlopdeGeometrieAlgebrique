/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import SGA.Foundations.Projective.SectionRing

/-!
# Flat base change for the sections of the powers of a line bundle

Let `X ⟶ Y` be a morphism with `X` quasi-compact and quasi-separated, and `Y' ⟶ Y` a flat morphism
of affine schemes, with `X' = X ×_Y Y'`. For a line bundle `L` on `X` with inverse image `L'` on
`X'`, the sections of `L'^{⊗n}` over `X'` are the base change of those of `L^{⊗n}`:
`Γ(X', L'^{⊗n}) = Γ(Y', 𝒪) ⊗_{Γ(Y, 𝒪)} Γ(X, L^{⊗n})` (EGA III 1.4.15 for `H⁰`, EGA IV 2.3.1).

We reduce to the case of `𝒪_X` over the affine opens and their pairwise intersections of a
finite trivializing affine cover of `X` (mathlib's
`AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`), and use that flat
base change preserves kernels (`IsBaseChange.of_left_exact`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.LineBundle

variable {X : Scheme.{u}} (L : X.LineBundle) (R : Type u) [CommRing R] [Algebra R Γ(X, ⊤)]

section Modules

variable {L R}

lemma famRes_algebraMap {V V' : X.Opens} (h : V' ≤ V) (r : R) :
    L.famRes h (algebraMap R (L.Fam V) r) = algebraMap R (L.Fam V') r := by
  rw [algebraMap_fam, algebraMap_fam, famRes_famConst, CohomologyAux.presheaf_map_map]

variable (L R) in
/-- Restriction of sections of `L^{⊗n}`, as an `R`-linear map. -/
noncomputable def resLin (n : ℤ) {V V' : X.Opens} (h : V' ≤ V) :
    L.sectionSubmoduleOn R n V →ₗ[R] L.sectionSubmoduleOn R n V' where
  toFun s := ⟨L.famRes h s, s.2.famRes h⟩
  map_add' s t := Subtype.ext (map_add _ _ _)
  map_smul' r s := Subtype.ext <| by
    change L.famRes h (r • s.1) = r • L.famRes h s.1
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, famRes_algebraMap]

@[simp]
lemma coe_resLin (n : ℤ) {V V' : X.Opens} (h : V' ≤ V) (s : L.sectionSubmoduleOn R n V) :
    (L.resLin R n h s : L.Fam V') = L.famRes h s :=
  rfl

end Modules

section Exact

variable {ι' : Type*} (W : ι' → X.Opens) (hcov : ⨆ a, W a = ⊤)

/-- Restriction of sections over `X` to the members of a cover. -/
noncomputable def coverEval (n : ℤ) :
    L.sectionSubmoduleOn R n ⊤ →ₗ[R] ∀ a, L.sectionSubmoduleOn R n (W a) :=
  LinearMap.pi fun _ ↦ L.resLin R n le_top

/-- The difference of the two restrictions to the pairwise intersections of a cover. -/
noncomputable def coverDiff (n : ℤ) :
    (∀ a, L.sectionSubmoduleOn R n (W a)) →ₗ[R]
      ∀ p : ι' × ι', L.sectionSubmoduleOn R n (W p.1 ⊓ W p.2) :=
  LinearMap.pi fun p ↦ L.resLin R n inf_le_left ∘ₗ LinearMap.proj p.1 -
    L.resLin R n inf_le_right ∘ₗ LinearMap.proj p.2

include hcov

lemma coverEval_injective (n : ℤ) : Function.Injective (L.coverEval R W n) := by
  intro s t h
  refine Subtype.ext (famRes_injective W (fun _ ↦ le_top) hcov.ge fun a ↦ ?_)
  exact congrArg Subtype.val (congrFun h a)

lemma exact_coverEval_coverDiff (n : ℤ) :
    Function.Exact (L.coverEval R W n) (L.coverDiff R W n) := by
  intro u
  constructor
  · intro hu
    have hcomp (a b : ι') : L.famRes (inf_le_left : W a ⊓ W b ≤ W a) (u a) =
        L.famRes (inf_le_right : W a ⊓ W b ≤ W b) (u b) := by
      have := congrArg Subtype.val (congrFun hu (a, b))
      simpa [coverDiff, sub_eq_zero] using this
    obtain ⟨s, hs, hsu⟩ := exists_isSection_glue W (fun _ ↦ le_top) hcov.ge (fun a ↦ (u a).1)
      (fun a ↦ (u a).2) hcomp
    exact ⟨⟨s, hs⟩, funext fun a ↦ Subtype.ext (hsu a)⟩
  · rintro ⟨s, rfl⟩
    funext p
    apply Subtype.ext
    simp [coverDiff, coverEval, famRes_famRes]

end Exact

instance isScalarTower_fam {Z : Scheme.{u}} {M : Z.LineBundle} {R₁ R₂ : Type u} [CommRing R₁]
    [CommRing R₂] [Algebra R₁ R₂] [Algebra R₁ Γ(Z, ⊤)] [Algebra R₂ Γ(Z, ⊤)]
    [IsScalarTower R₁ R₂ Γ(Z, ⊤)] {V : Z.Opens} : IsScalarTower R₁ R₂ (M.Fam V) :=
  .of_algebraMap_eq fun r ↦ by
    rw [algebraMap_fam, algebraMap_fam, IsScalarTower.algebraMap_apply R₁ R₂ Γ(Z, ⊤)]

section Pullback

variable {L R} {X' : Scheme.{u}} (fst : X' ⟶ X) (S : Type u) [CommRing S] [Algebra S Γ(X', ⊤)]

lemma famPullback_famConst {V : X.Opens} {V' : X'.Opens} (h : V' ≤ fst ⁻¹ᵁ V) (r : Γ(X, V)) :
    L.famPullback fst h (L.famConst V r) = (L.pullback fst).famConst V' (fst.appLE V V' h r) := by
  funext (i : L.ι)
  change fst.appLE (V ⊓ L.U i) (V' ⊓ fst ⁻¹ᵁ L.U i) _ (X.presheaf.map _ r) =
    X'.presheaf.map (homOfLE (inf_le_left : V' ⊓ fst ⁻¹ᵁ L.U i ≤ V')).op (fst.appLE V V' h r)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_map]

variable [Algebra R S] [Algebra R Γ(X', ⊤)] [IsScalarTower R S Γ(X', ⊤)]
  (hR : ∀ r : R, fst.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(X', ⊤) r)

include hR in
lemma famPullback_algebraMap {V : X.Opens} {V' : X'.Opens} (h : V' ≤ fst ⁻¹ᵁ V) (r : R) :
    L.famPullback fst h (algebraMap R (L.Fam V) r) = algebraMap R ((L.pullback fst).Fam V') r := by
  rw [algebraMap_fam, famPullback_famConst, algebraMap_fam]
  congr 1
  rw [← hR, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE]
  rfl

variable (L R) in
include hR in
/-- The inverse image of sections of `L^{⊗n}` along `fst`, as an `R`-linear map. -/
noncomputable def pullLin (n : ℤ) {V : X.Opens} {V' : X'.Opens} (h : V' ≤ fst ⁻¹ᵁ V) :
    L.sectionSubmoduleOn R n V →ₗ[R] (L.pullback fst).sectionSubmoduleOn S n V' where
  toFun s := ⟨L.famPullback fst h s, s.2.famPullback fst h⟩
  map_add' s t := Subtype.ext (map_add _ _ _)
  map_smul' r s := Subtype.ext <| by
    change L.famPullback fst h (r • s.1) = r • L.famPullback fst h s.1
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, famPullback_algebraMap fst hR]

@[simp]
lemma coe_pullLin (n : ℤ) {V : X.Opens} {V' : X'.Opens} (h : V' ≤ fst ⁻¹ᵁ V)
    (s : L.sectionSubmoduleOn R n V) :
    (L.pullLin R fst S hR n h s : (L.pullback fst).Fam V') = L.famPullback fst h s :=
  rfl

end Pullback

section LocalBaseChange

variable {L} {X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {fst : X' ⟶ X} {snd : X' ⟶ Y'}

/-- Flat base change for the sections of `𝒪_X` over a quasi-compact quasi-separated open. -/
lemma isPushout_appLE_of_flat (H : IsPullback fst snd f g) [IsAffine Y] [IsAffine Y'] [Flat g]
    {W : X.Opens} (hW : IsCompact (W : Set X)) (hW' : IsQuasiSeparated (W : Set X)) :
    IsPushout (f.appLE ⊤ W le_top) (g.appLE ⊤ ⊤ le_top) (fst.appLE W (fst ⁻¹ᵁ W) le_rfl)
      (snd.appLE ⊤ (fst ⁻¹ᵁ W) le_top) := by
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H (US := ⊤) (UT := ⊤) (UX := W)
    (UY := fst ⁻¹ᵁ W) le_top le_top (by simp) (isAffineOpen_top Y) (isAffineOpen_top Y') hW hW'
  exact (isIso_pushoutSection_iff H _ _ _).mp this

variable (L)
  [Algebra Γ(Y, ⊤) Γ(X, ⊤)] [Algebra Γ(Y', ⊤) Γ(X', ⊤)] [Algebra Γ(Y, ⊤) Γ(Y', ⊤)]
  [Algebra Γ(Y, ⊤) Γ(X', ⊤)] [IsScalarTower Γ(Y, ⊤) Γ(Y', ⊤) Γ(X', ⊤)]
  (hf : algebraMap Γ(Y, ⊤) Γ(X, ⊤) = f.appTop.hom)
  (hsnd : algebraMap Γ(Y', ⊤) Γ(X', ⊤) = snd.appTop.hom)
  (hg : algebraMap Γ(Y, ⊤) Γ(Y', ⊤) = g.appTop.hom)

include hf hsnd hg in
lemma appTop_algebraMap_of_isPullback (H : IsPullback fst snd f g) (r : Γ(Y, ⊤)) :
    fst.appTop (algebraMap Γ(Y, ⊤) Γ(X, ⊤) r) = algebraMap Γ(Y, ⊤) Γ(X', ⊤) r := by
  rw [IsScalarTower.algebraMap_apply Γ(Y, ⊤) Γ(Y', ⊤) Γ(X', ⊤), hf, hsnd, hg,
    ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, H.w]

lemma famUnit_famConst {Z : Scheme.{u}} {M : Z.LineBundle} (k : M.ι) {V : Z.Opens}
    (hV : V ≤ M.U k) (c : Γ(Z, V)) : M.famUnit k hV (M.famConst V c) = c := by
  rw [famUnit_apply, famConst_apply, CohomologyAux.presheaf_map_map,
    CohomologyAux.presheaf_map_self]

set_option backward.isDefEq.respectTransparency false in
include hf hsnd hg in
/-- Flat base change for the sections of `L^{⊗n}` over a quasi-compact quasi-separated open on
which `L` is trivial. -/
theorem isBaseChange_pullLin_of_le (H : IsPullback fst snd f g) [IsAffine Y] [IsAffine Y']
    [Flat g] (n : ℤ) {W : X.Opens} (hW : IsCompact (W : Set X))
    (hW' : IsQuasiSeparated (W : Set X)) {k : L.ι} (hk : W ≤ L.U k) {W₁ : X'.Opens}
    (hW₁ : W₁ = fst ⁻¹ᵁ W) :
    IsBaseChange Γ(Y', ⊤) (L.pullLin Γ(Y, ⊤) fst Γ(Y', ⊤)
      (appTop_algebraMap_of_isPullback hf hsnd hg H) n hW₁.le) := by
  subst hW₁
  let : Algebra Γ(Y, ⊤) Γ(X, W) := (f.appLE ⊤ W le_top).hom.toAlgebra
  let : Algebra Γ(Y', ⊤) Γ(X', fst ⁻¹ᵁ W) := (snd.appLE ⊤ (fst ⁻¹ᵁ W) le_top).hom.toAlgebra
  let : Algebra Γ(X, W) Γ(X', fst ⁻¹ᵁ W) := (fst.appLE W (fst ⁻¹ᵁ W) le_rfl).hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(X', fst ⁻¹ᵁ W) :=
    ((snd.appLE ⊤ (fst ⁻¹ᵁ W) le_top).hom.comp (algebraMap Γ(Y, ⊤) Γ(Y', ⊤))).toAlgebra
  have : IsScalarTower Γ(Y, ⊤) Γ(Y', ⊤) Γ(X', fst ⁻¹ᵁ W) := .of_algebraMap_eq' rfl
  have hgle : g.appLE ⊤ ⊤ le_top = g.appTop := g.appLE_eq_app
  have : IsScalarTower Γ(Y, ⊤) Γ(X, W) Γ(X', fst ⁻¹ᵁ W) := .of_algebraMap_eq fun r ↦ by
    change (snd.appLE ⊤ (fst ⁻¹ᵁ W) le_top) (algebraMap Γ(Y, ⊤) Γ(Y', ⊤) r) =
      fst.appLE W (fst ⁻¹ᵁ W) le_rfl (f.appLE ⊤ W le_top r)
    rw [hg, ← hgle, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    have key : ∀ (φ ψ : X' ⟶ Y), φ = ψ → ∀ e e',
        φ.appLE ⊤ (fst ⁻¹ᵁ W) e = ψ.appLE ⊤ (fst ⁻¹ᵁ W) e' := by
      rintro φ _ rfl e e'
      rfl
    exact congrArg (fun φ : Γ(Y, ⊤) ⟶ Γ(X', fst ⁻¹ᵁ W) ↦ φ r) (key _ _ H.w.symm _ _)
  have hpo : Algebra.IsPushout Γ(Y, ⊤) Γ(Y', ⊤) Γ(X, W) Γ(X', fst ⁻¹ᵁ W) := by
    rw [← CommRingCat.isPushout_iff_isPushout, hg]
    have := (isPushout_appLE_of_flat H hW hW').flip
    rw [hgle] at this
    exact this
  -- the trivializations of `L^{⊗n}` on `W` and of `L'^{⊗n}` on `fst⁻¹ W`
  have hk' : fst ⁻¹ᵁ W ≤ (L.pullback fst).U k := fst.preimage_mono hk
  let eM : L.sectionSubmoduleOn Γ(Y, ⊤) n W ≃ₗ[Γ(Y, ⊤)] Γ(X, W) := LinearEquiv.ofBijective
    { toFun u := L.famUnit k hk u.1
      map_add' u v := map_add _ _ _
      map_smul' r u := by
        change L.famUnit k hk (r • u.1) = algebraMap Γ(Y, ⊤) Γ(X, W) r * L.famUnit k hk u.1
        rw [Algebra.smul_def, map_mul, algebraMap_fam, famUnit_famConst, hf]
        rfl }
    ⟨fun u v h ↦ Subtype.ext (u.2.ext_famUnit k v.2 hk h), fun c ↦ by
      obtain ⟨s, hs, hsc⟩ := L.exists_isSection_famUnit_eq k n hk c
      exact ⟨⟨s, hs⟩, hsc⟩⟩
  let eN : (L.pullback fst).sectionSubmoduleOn Γ(Y', ⊤) n (fst ⁻¹ᵁ W) ≃ₗ[Γ(Y', ⊤)]
      Γ(X', fst ⁻¹ᵁ W) := LinearEquiv.ofBijective
    { toFun u := (L.pullback fst).famUnit k hk' u.1
      map_add' u v := map_add _ _ _
      map_smul' r u := by
        change (L.pullback fst).famUnit k hk' (r • u.1) =
          algebraMap Γ(Y', ⊤) Γ(X', fst ⁻¹ᵁ W) r * (L.pullback fst).famUnit k hk' u.1
        rw [Algebra.smul_def, map_mul, algebraMap_fam, famUnit_famConst, hsnd]
        rfl }
    ⟨fun u v h ↦ Subtype.ext (IsSection.ext_famUnit (L := L.pullback fst) k u.2 v.2 hk' h),
      fun c ↦ by
      obtain ⟨s, hs, hsc⟩ := (L.pullback fst).exists_isSection_famUnit_eq k n hk' c
      exact ⟨⟨s, hs⟩, hsc⟩⟩
  refine (IsBaseChange.iff_of_equiv_comm eM eN ?_).mpr hpo.out
  ext u
  change fst.appLE W (fst ⁻¹ᵁ W) le_rfl (L.famUnit k hk u.1) =
    (L.pullback fst).famUnit k hk' (L.famPullback fst le_rfl u.1)
  rw [famUnit_apply, famUnit_apply, famPullback_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.map_appLE]
  change _ = X'.presheaf.map (homOfLE (le_inf le_rfl hk' :
    fst ⁻¹ᵁ W ≤ fst ⁻¹ᵁ W ⊓ fst ⁻¹ᵁ L.U k)).op
      (fst.appLE (W ⊓ L.U k) (fst ⁻¹ᵁ W ⊓ fst ⁻¹ᵁ L.U k) (fst.preimage_inf.ge) (u.1 k))
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

set_option backward.isDefEq.respectTransparency false in
include hf hsnd hg in
/-- Flat base change for the sections of `L^{⊗n}`: if `X` is quasi-compact and quasi-separated
and `Y' ⟶ Y` is a flat morphism of affine schemes, then
`Γ(X ×_Y Y', L'^{⊗n}) = Γ(Y', 𝒪) ⊗_{Γ(Y, 𝒪)} Γ(X, L^{⊗n})`. -/
theorem isBaseChange_pullLin (H : IsPullback fst snd f g) [IsAffine Y] [IsAffine Y'] [Flat g]
    [CompactSpace X] [QuasiSeparatedSpace X] (n : ℤ) :
    IsBaseChange Γ(Y', ⊤) (L.pullLin Γ(Y, ⊤) fst Γ(Y', ⊤)
      (appTop_algebraMap_of_isPullback hf hsnd hg H) n fst.preimage_top.ge) := by
  obtain ⟨ι', _, V, k, hVa, hVk, -, hcov⟩ := L.exists_finite_cover (U := ⊤) isCompact_univ
  have hcov' : ⨆ a, V a = ⊤ := top_le_iff.mp hcov
  have hcov'' : ⨆ a, fst ⁻¹ᵁ V a = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcov', Scheme.Hom.preimage_top]
  have hR := appTop_algebraMap_of_isPullback hf hsnd hg H
  have : Module.Flat Γ(Y, ⊤) Γ(Y', ⊤) := by
    rw [← RingHom.flat_algebraMap_iff, hg]
    exact g.flat_appTop
  refine IsBaseChange.of_left_exact Γ(Y', ⊤)
    (L.pullLin Γ(Y, ⊤) fst Γ(Y', ⊤) hR n fst.preimage_top.ge)
    (LinearMap.pi fun a ↦ L.pullLin Γ(Y, ⊤) fst Γ(Y', ⊤) hR n (le_refl (fst ⁻¹ᵁ V a)) ∘ₗ
      LinearMap.proj a)
    (LinearMap.pi fun p : ι' × ι' ↦ L.pullLin Γ(Y, ⊤) fst Γ(Y', ⊤) hR n
      (fst.preimage_inf.symm.le : fst ⁻¹ᵁ V p.1 ⊓ fst ⁻¹ᵁ V p.2 ≤ fst ⁻¹ᵁ (V p.1 ⊓ V p.2)) ∘ₗ
        LinearMap.proj p)
    (f := L.coverEval _ V n) (g := L.coverDiff _ V n)
    (f' := (L.pullback fst).coverEval Γ(Y', ⊤) (fun a ↦ fst ⁻¹ᵁ V a) n)
    (g' := (L.pullback fst).coverDiff Γ(Y', ⊤) (fun a ↦ fst ⁻¹ᵁ V a) n) ?_ ?_ ?_ ?_
    (L.exact_coverEval_coverDiff _ V hcov' n) (L.coverEval_injective _ V hcov' n)
    ((L.pullback fst).exact_coverEval_coverDiff _ _ hcov'' n)
    ((L.pullback fst).coverEval_injective _ _ hcov'' n)
  · ext s a : 2
    apply Subtype.ext
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply, coverEval,
      LinearMap.coe_proj, Function.eval, LinearMap.coe_restrictScalars, coe_pullLin, coe_resLin,
      famPullback_famRes, famRes_famPullback]
  · ext u p : 2
    apply Subtype.ext
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply, coverDiff,
      LinearMap.coe_proj, Function.eval, LinearMap.coe_restrictScalars, coe_pullLin, coe_resLin,
      LinearMap.sub_apply, Submodule.coe_sub, map_sub, famPullback_famRes, famRes_famPullback]
  · exact IsBaseChange.pi _ fun a ↦ L.isBaseChange_pullLin_of_le hf hsnd hg H n
      (hVa a).isCompact (hVa a).isQuasiSeparated (hVk a) rfl
  · exact IsBaseChange.pi _ fun p ↦ L.isBaseChange_pullLin_of_le hf hsnd hg H n
      (QuasiSeparatedSpace.inter_isCompact _ _ (V p.1).2 (hVa p.1).isCompact (V p.2).2
        (hVa p.2).isCompact)
      (isQuasiSeparated_univ.of_subset (Set.subset_univ _))
      (inf_le_left.trans (hVk p.1)) fst.preimage_inf

end LocalBaseChange

end AlgebraicGeometry.Scheme.LineBundle
