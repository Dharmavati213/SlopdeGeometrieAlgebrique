/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.FiniteHomAlgebraization
import SGA.Foundations.Cohomology.LocallyFreeAlgebraization
import SGA.Foundations.Cohomology.AlgebraAlgebraization
import SGA.Foundations.Cohomology.RelativeSpecEtale

/-!
# Algebraization of étale coverings of the formal completion (projective case)

Let `A` be a noetherian `I`-adically complete ring, `X` a closed subscheme of `ℙ(τ; Spec A)` and
`(Yₙ ⟶ Xₙ)` an étale covering of the formal completion of `X` along `f⁻¹ V(I)`
(`Scheme.FormalFiniteEtale (thickeningDiagram I f)`). Then
`exists_finiteEtale_of_formalFiniteEtale`: there is a finite étale `Y ⟶ X` with
`Y ×_X X₀ ≅ Y₀` over `X₀` (EGA III 5.4.5; SGA 1 IX.1.10, essential surjectivity).

* `formalAdicSystem`: the algebras `(Yₙ ⟶ X)_* 𝒪` form an adic system (affine base change along
  `Xₙ ⟶ Xₙ₊₁`, `formalTransition_app_surjective`, `formalTransition_app_eq_zero_iff`), locally
  free (`formalAdicSystem_isLocallyFree`: finite étale algebras over `Γ(X, U) / I^{n+1}` are
  projective, `liftingProperty_of_projective`);
* the existence theorem for locally free adic systems
  (`AdicSystem.exists_iso_quotientIdealPow_projective`) and the algebraization of the algebra
  structures (`exists_moduleAlgebra_algebraization`) give a coherent locally projective algebra
  `B`; `Spec_X B ⟶ X` is étale since `B / I B` is unramified
  (`etale_relativeSpecHom_of_reduction`, `formallyUnramified_formal`);
* `isIso_closedFibreLift`: `Y₀ ≅ Spec_X B ×_X X₀`, computed on affine opens with
  `toRelativeSpec_appLE` and affine base change.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

open Scheme.Modules

section LiftingQuotient

/-- A projective module over a quotient `S = R / K` has the lifting property for `R`-modules
killed by `K`. -/
theorem liftingProperty_of_projective {R S P : Type u} [CommRing R] [CommRing S] [AddCommGroup P]
    [Module R P] [Module S P] (π : R →+* S) (hπ : Function.Surjective π)
    (hP : ∀ (c : R) (x : P), c • x = π c • x) [Module.Projective S P] :
    LiftingProperty (RingHom.ker π) P := by
  intro N _ _ hN φ hφ
  let _ : SMul S N := ⟨fun s n ↦ (hπ s).choose • n⟩
  have hs : ∀ (c : R) (n : N), π c • n = c • n := by
    intro c n
    change (hπ (π c)).choose • n = c • n
    rw [← sub_eq_zero, ← sub_smul]
    refine hN _ ?_ n
    rw [RingHom.mem_ker, map_sub, (hπ (π c)).choose_spec, sub_self]
  let _ : Module S N := hπ.moduleLeft π hs
  let φS : N →ₗ[S] P :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun s n ↦ by
        obtain ⟨c, rfl⟩ := hπ s
        rw [RingHom.id_apply, hs, φ.map_smul, hP] }
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property φS LinearMap.id hφ
  refine ⟨{ toFun := ψ
            map_add' := ψ.map_add
            map_smul' := fun c x ↦ by rw [RingHom.id_apply, hP, ψ.map_smul, hs] }, ?_⟩
  ext x
  exact LinearMap.congr_fun hψ x

/-- For `q : Z ⟶ X'` finite étale and `i : X' ⟶ X` surjective on sections over the affine `U`,
the sections of `(q ≫ i)_* 𝒪_Z` over `U` have the lifting property for modules killed by the
ideal of `i`. -/
lemma liftingProperty_pushforwardUnit_comp {Z X' X : Scheme.{u}} (q : Z ⟶ X') (i : X' ⟶ X)
    [IsFinite q] [Etale q] [IsAffineHom i] {U : X.Opens} (hU : IsAffineOpen U)
    (hi : Function.Surjective (i.app U)) {K : Ideal Γ(X, U)} (hK : RingHom.ker (i.app U).hom = K) :
    LiftingProperty K Γ(pushforwardUnit (q ≫ i), U) :=
  letI : Module Γ(X', i ⁻¹ᵁ U) Γ(pushforwardUnit (q ≫ i), U) :=
    inferInstanceAs (Module Γ(X', i ⁻¹ᵁ U) Γ(pushforwardUnit q, i ⁻¹ᵁ U))
  haveI : Module.Projective Γ(X', i ⁻¹ᵁ U) Γ(pushforwardUnit (q ≫ i), U) :=
    projective_pushforwardUnit_sections q (hU.preimage i)
  hK ▸ liftingProperty_of_projective (i.app U).hom hi (fun _ _ ↦ rfl)

end LiftingQuotient

section AppLE

lemma appLE_surjective_ker_of_eq {X Y : Scheme.{u}} (h : X ⟶ Y) (V : Y.Opens) {W : X.Opens}
    (hW : W = h ⁻¹ᵁ V) (e : W ≤ h ⁻¹ᵁ V) :
    (Function.Surjective (h.appLE V W e) ↔ Function.Surjective (h.app V)) ∧
      RingHom.ker (h.appLE V W e).hom = RingHom.ker (h.app V).hom := by
  subst hW
  rw [Scheme.Hom.app_eq_appLE]
  exact ⟨Iff.rfl, rfl⟩

end AppLE

section Transition

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- The ideal of `X_n` in `X_{n+1}` over an affine open `U` of `X` is `I^{n+1}`. -/
lemma ker_thickening_transition_app (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) :
    RingHom.ker ((thickening.transition f I n).app (thickening.ι f I (n + 1) ⁻¹ᵁ U)).hom =
      (idealV f I U (n + 1)).map ((thickening.ι f I (n + 1)).app U).hom := by
  have h₁ := congrArg (fun φ : thickening f I n ⟶ X ↦ RingHom.ker (φ.app U).hom)
    (thickening.transition_ι f I n)
  rw [ker_thickening_app I f n hU] at h₁
  have h₂ : (RingHom.ker ((thickening.transition f I n).app
      (thickening.ι f I (n + 1) ⁻¹ᵁ U)).hom).comap ((thickening.ι f I (n + 1)).app U).hom =
        idealV f I U (n + 1) := by
    rw [RingHom.comap_ker]
    exact h₁
  rw [← h₂, Ideal.map_comap_of_surjective _
    ((thickening.ι f I (n + 1)).app_surjective U hU)]

end Transition

section FormalAdicSystem

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A)
  (𝒴 : Scheme.FormalFiniteEtale (thickeningDiagram I f))

/-- The structure morphism `Yₙ ⟶ Xₙ` of an étale covering of the formal completion. -/
def formalQ (n : ℕ) : (𝒴.obj n).left ⟶ thickening f I n := (𝒴.obj n).hom

instance formalQ_isFinite (n : ℕ) : IsFinite (formalQ I f 𝒴 n) :=
  ((Scheme.finiteEtaleHom_iff _).mp (𝒴.obj n).prop).1

instance formalQ_etale (n : ℕ) : Etale (formalQ I f 𝒴 n) :=
  ((Scheme.finiteEtaleHom_iff _).mp (𝒴.obj n).prop).2

/-- The composite `Yₙ ⟶ Xₙ ⟶ X`. -/
abbrev formalStructure (n : ℕ) : (𝒴.obj n).left ⟶ X :=
  formalQ I f 𝒴 n ≫ thickening.ι f I n

lemma transition_formalQ (n : ℕ) :
    𝒴.transition n ≫ formalQ I f 𝒴 (n + 1) = formalQ I f 𝒴 n ≫ thickening.transition f I n := by
  have h := 𝒴.transition_hom n
  rw [thickeningDiagram_map] at h
  exact h

lemma transition_formalStructure (n : ℕ) :
    𝒴.transition n ≫ formalStructure I f 𝒴 (n + 1) = formalStructure I f 𝒴 n := by
  rw [formalStructure, formalStructure, ← Category.assoc, transition_formalQ, Category.assoc,
    thickening.transition_ι]

lemma isPullback_formalTransition (n : ℕ) :
    IsPullback (𝒴.transition n) (formalQ I f 𝒴 n) (formalQ I f 𝒴 (n + 1))
      (thickening.transition f I n) := by
  let i : (𝒴.obj n).left ≅
      pullback (𝒴.obj (n + 1)).hom ((thickeningDiagram I f).map (homOfLE n.le_succ)) :=
    { hom := (𝒴.iso n).inv.left
      inv := (𝒴.iso n).hom.left
      hom_inv_id := congrArg (fun f ↦ f.left) (𝒴.iso n).inv_hom_id
      inv_hom_id := congrArg (fun f ↦ f.left) (𝒴.iso n).hom_inv_id }
  have h : IsPullback (𝒴.transition n) (𝒴.obj n).hom (𝒴.obj (n + 1)).hom
      ((thickeningDiagram I f).map (homOfLE n.le_succ)) := by
    refine IsPullback.of_iso_pullback ⟨𝒴.transition_hom n⟩ i rfl ?_
    change (𝒴.iso n).inv.left ≫ _ = _
    simpa using (𝒴.iso n).inv.w
  rw [thickeningDiagram_map] at h
  exact h

lemma map_map_app_comp {Z X' X : Scheme.{u}} (q : Z ⟶ X') (i : X' ⟶ X) (U : X.Opens)
    (J : Ideal Γ(X, U)) :
    (J.map (i.app U).hom).map (q.app (i ⁻¹ᵁ U)).hom = J.map ((q ≫ i).app U).hom := by
  rw [Ideal.map_map]
  rfl

lemma formalStructure_preimage (n : ℕ) (U : X.Opens) :
    formalStructure I f 𝒴 n ⁻¹ᵁ U =
      𝒴.transition n ⁻¹ᵁ (formalQ I f 𝒴 (n + 1) ⁻¹ᵁ (thickening.ι f I (n + 1) ⁻¹ᵁ U)) := by
  rw [← transition_formalStructure I f 𝒴 n, formalStructure, Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage]

lemma formalTransition_app_surjective (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective ((pushforwardUnitMap (𝒴.transition n)
        (transition_formalStructure I f 𝒴 n)).app U) := by
  let U' := thickening.ι f I (n + 1) ⁻¹ᵁ U
  have hU' : IsAffineOpen U' := hU.preimage _
  obtain ⟨hs, -⟩ := app_surjective_ker_of_isPullback (isPullback_formalTransition I f 𝒴 n) hU'
    (hU'.preimage _) (hU'.preimage _) ((thickening.transition f I n).app_surjective U' hU')
  obtain ⟨hsurj, -⟩ := appLE_surjective_ker_of_eq (𝒴.transition n)
    (formalQ I f 𝒴 (n + 1) ⁻¹ᵁ U') (formalStructure_preimage I f 𝒴 n U)
    (preimage_le_preimage_of_comp_eq _ (transition_formalStructure I f 𝒴 n) U)
  intro y
  obtain ⟨x, hx⟩ := hsurj.mpr hs (pushforwardUnitEquiv _ y)
  exact ⟨(pushforwardUnitEquiv _).symm x, (pushforwardUnitMap_app (𝒴.transition n)
    (transition_formalStructure I f 𝒴 n) U _).trans hx⟩

lemma formalTransition_ker (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) :
    RingHom.ker ((𝒴.transition n).appLE (formalStructure I f 𝒴 (n + 1) ⁻¹ᵁ U)
        (formalStructure I f 𝒴 n ⁻¹ᵁ U)
        (preimage_le_preimage_of_comp_eq _ (transition_formalStructure I f 𝒴 n) U)).hom =
      (idealV f I U (n + 1)).map ((formalStructure I f 𝒴 (n + 1)).app U).hom := by
  let U' := thickening.ι f I (n + 1) ⁻¹ᵁ U
  have hU' : IsAffineOpen U' := hU.preimage _
  obtain ⟨-, hk⟩ := app_surjective_ker_of_isPullback (isPullback_formalTransition I f 𝒴 n) hU'
    (hU'.preimage _) (hU'.preimage _) ((thickening.transition f I n).app_surjective U' hU')
  obtain ⟨-, hker⟩ := appLE_surjective_ker_of_eq (𝒴.transition n)
    (formalQ I f 𝒴 (n + 1) ⁻¹ᵁ U') (formalStructure_preimage I f 𝒴 n U)
    (preimage_le_preimage_of_comp_eq _ (transition_formalStructure I f 𝒴 n) U)
  rw [ker_thickening_transition_app I f n hU, map_map_app_comp] at hk
  exact hker.trans hk

lemma formalTransition_app_eq_zero_iff (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (s : Γ(pushforwardUnit (formalStructure I f 𝒴 (n + 1)), U)) :
    (pushforwardUnitMap (𝒴.transition n) (transition_formalStructure I f 𝒴 n)).app U s = 0 ↔
      s ∈ (idealV f I U 1 ^ (n + 1) • ⊤ :
        Submodule Γ(X, U) Γ(pushforwardUnit (formalStructure I f 𝒴 (n + 1)), U)) := by
  rw [mem_smul_top_pushforwardUnit_iff, ← AdicSystem.idealV_eq_pow,
    ← formalTransition_ker I f 𝒴 n hU, RingHom.mem_ker,
    ← pushforwardUnitMap_app (𝒴.transition n) (transition_formalStructure I f 𝒴 n)]
  rfl

/-- The adic system `(Yₙ ⟶ X)_* 𝒪_{Yₙ}` of an étale covering of the formal completion of `X`
along `f⁻¹ V(I)`. -/
def formalAdicSystem : AdicSystem I f where
  obj n := pushforwardUnit (formalStructure I f 𝒴 n)
  map n := pushforwardUnitMap (𝒴.transition n) (transition_formalStructure I f 𝒴 n)
  isQuasicoherent _ := inferInstance
  surjective n _ hU := formalTransition_app_surjective I f 𝒴 n hU
  map_app_eq_zero_iff n _ hU s := formalTransition_app_eq_zero_iff I f 𝒴 n hU s

lemma formalAdicSystem_isLocallyFree : (formalAdicSystem I f 𝒴).IsLocallyFree := by
  intro n U hU
  have hker : RingHom.ker ((thickening.ι f I n).app U).hom = idealV f I U 1 ^ (n + 1) := by
    rw [ker_thickening_app I f n hU, AdicSystem.idealV_eq_pow]
  have hs : Function.Surjective ((thickening.ι f I n).app U) :=
    (thickening.ι f I n).app_surjective U hU
  change LiftingProperty _ Γ(pushforwardUnit (formalQ I f 𝒴 n ≫ thickening.ι f I n), U)
  exact liftingProperty_pushforwardUnit_comp (formalQ I f 𝒴 n) (thickening.ι f I n) hU hs hker

end FormalAdicSystem

section ClosedFibreIso

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A)
  {B : X.Modules} [B.IsQuasicoherent] (algB : ModuleAlgebra B) {Z : Scheme.{u}}
  (q : Z ⟶ thickening f I 0) (φ : B ⟶ pushforwardUnit (q ≫ thickening.ι f I 0))
  (hmul : ∀ (U : X.Opens) (x y : Γ(B, U)),
    φ.app U (mulApp algB.mul U x y) = pfMul _ (φ.app U x) (φ.app U y))
  (hone : φ.app ⊤ algB.one = (pushforwardUnitEquiv _).symm 1)

/-- The comparison morphism `Z ⟶ Spec_X B ×_X X₀` of an algebra morphism `B ⟶ (Z ⟶ X)_* 𝒪_Z`,
`Z` over `X₀`. -/
def closedFibreLift : Z ⟶ pullback algB.relativeSpecHom (thickening.ι f I 0) :=
  pullback.lift (toRelativeSpec algB φ hmul hone) q (by rw [toRelativeSpec_relativeSpecHom])

@[reassoc (attr := simp)]
lemma closedFibreLift_fst :
    closedFibreLift I f algB q φ hmul hone ≫ pullback.fst _ _ = toRelativeSpec algB φ hmul hone :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma closedFibreLift_snd : closedFibreLift I f algB q φ hmul hone ≫ pullback.snd _ _ = q :=
  pullback.lift_snd _ _ _

/-- Elements of `J Γ(B, U)` go to the ideal generated by `J` in `Γ(Spec_X B, p⁻¹ U)`. -/
lemma sectionsIso_inv_mem_map (U : X.AffineZariskiSite) (J : Ideal Γ(X, U.toOpens))
    (b : Γ(B, U.toOpens)) (hb : b ∈ (J • ⊤ : Submodule Γ(X, U.toOpens) Γ(B, U.toOpens))) :
    (algB.sectionsIso U).inv b ∈ J.map (algB.relativeSpecHom.app U.toOpens).hom := by
  have halg : ∀ r : Γ(X, U.toOpens), (algB.sectionsIso U).inv
      (algebraMap Γ(X, U.toOpens) (algB.Sections U.toOpens) r) =
        algB.relativeSpecHom.app U.toOpens r := by
    intro r
    rw [← algB.sectionsIso_hom_appLE U r, Iso.hom_inv_id_apply, ModuleAlgebra.relSpecAppLE,
      ← Scheme.Hom.app_eq_appLE]
  refine Submodule.smul_induction_on (p := fun z : Γ(B, U.toOpens) ↦ (algB.sectionsIso U).inv z ∈
    J.map (algB.relativeSpecHom.app U.toOpens).hom) hb ?_ ?_
  · intro r hr m _
    let m' : algB.Sections U.toOpens := m
    have e' : r • m' = algebraMap Γ(X, U.toOpens) (algB.Sections U.toOpens) r * m' :=
      Algebra.smul_def r m'
    have e : (algB.sectionsIso U).inv (r • m') =
        algB.relativeSpecHom.app U.toOpens r * (algB.sectionsIso U).inv m' := by
      rw [e', map_mul, halg]
    exact (congrArg (fun z ↦ z ∈ J.map (algB.relativeSpecHom.app U.toOpens).hom) e).mpr
      (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr))
  · intro x y hx hy
    let x' : algB.Sections U.toOpens := x
    let y' : algB.Sections U.toOpens := y
    have e : (algB.sectionsIso U).inv (x' + y') =
        (algB.sectionsIso U).inv x' + (algB.sectionsIso U).inv y' := map_add _ _ _
    exact (congrArg (fun z ↦ z ∈ J.map (algB.relativeSpecHom.app U.toOpens).hom) e).mpr
      (add_mem hx hy)

variable [IsAffineHom (q ≫ thickening.ι f I 0)]
  (hsurj : ∀ {U : X.Opens}, IsAffineOpen U → Function.Surjective (φ.app U))
  (hker : ∀ {U : X.Opens}, IsAffineOpen U → ∀ x : Γ(B, U),
    φ.app U x = 0 ↔ x ∈ (idealV f I U 1 • ⊤ : Submodule Γ(X, U) Γ(B, U)))

include hsurj hker in
/-- **The algebraization restricts to the closed fibre**: if `φ : B ⟶ (Z ⟶ X)_* 𝒪_Z` is surjective
on affine opens with kernel `I B`, then `Z ≅ Spec_X B ×_X X₀`. -/
theorem isIso_closedFibreLift : IsIso (closedFibreLift I f algB q φ hmul hone) := by
  have hg : closedFibreLift I f algB q φ hmul hone ≫
      (pullback.fst algB.relativeSpecHom (thickening.ι f I 0) ≫ algB.relativeSpecHom) =
        q ≫ thickening.ι f I 0 := by
    rw [closedFibreLift_fst_assoc, toRelativeSpec_relativeSpecHom]
  refine isIso_of_bijective_appLE _ hg fun U ↦ ?_
  have hU := U.2
  obtain ⟨hρs, hρk⟩ := app_surjective_ker_of_isPullback
    (IsPullback.of_hasPullback algB.relativeSpecHom (thickening.ι f I 0)) hU
    (hU.preimage algB.relativeSpecHom) (hU.preimage _)
    ((thickening.ι f I 0).app_surjective U.toOpens hU)
  rw [ker_thickening_app I f 0 hU, zero_add] at hρk
  have hcomp : ∀ b : algB.Sections U.toOpens,
      (closedFibreLift I f algB q φ hmul hone).appLE
        ((pullback.fst algB.relativeSpecHom (thickening.ι f I 0) ≫ algB.relativeSpecHom) ⁻¹ᵁ
          U.toOpens) ((q ≫ thickening.ι f I 0) ⁻¹ᵁ U.toOpens)
        (preimage_le_preimage_of_comp_eq _ hg U.toOpens)
        ((pullback.fst algB.relativeSpecHom (thickening.ι f I 0)).app
          (algB.relativeSpecHom ⁻¹ᵁ U.toOpens) ((algB.sectionsIso U).inv b)) =
        pushforwardUnitEquiv _ (φ.app U.toOpens b) := by
    intro b
    have h1 : (pullback.fst algB.relativeSpecHom (thickening.ι f I 0)).app
        (algB.relativeSpecHom ⁻¹ᵁ U.toOpens) ≫ (closedFibreLift I f algB q φ hmul hone).appLE
        ((pullback.fst algB.relativeSpecHom (thickening.ι f I 0) ≫ algB.relativeSpecHom) ⁻¹ᵁ
          U.toOpens) ((q ≫ thickening.ι f I 0) ⁻¹ᵁ U.toOpens)
        (preimage_le_preimage_of_comp_eq _ hg U.toOpens) =
        (toRelativeSpec algB φ hmul hone).appLE (algB.relativeSpecHom ⁻¹ᵁ U.toOpens)
          ((q ≫ thickening.ι f I 0) ⁻¹ᵁ U.toOpens)
          (by rw [← Scheme.Hom.comp_preimage, toRelativeSpec_relativeSpecHom]) := by
      rw [Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
        (appLE_eq_of_eq (closedFibreLift_fst I f algB q φ hmul hone) _ _ _ _)
    have h3 : ((algB.sectionsIso U).inv ≫
        (pullback.fst algB.relativeSpecHom (thickening.ι f I 0)).app
          (algB.relativeSpecHom ⁻¹ᵁ U.toOpens) ≫ (closedFibreLift I f algB q φ hmul hone).appLE
        ((pullback.fst algB.relativeSpecHom (thickening.ι f I 0) ≫ algB.relativeSpecHom) ⁻¹ᵁ
          U.toOpens) ((q ≫ thickening.ι f I 0) ⁻¹ᵁ U.toOpens)
        (preimage_le_preimage_of_comp_eq _ hg U.toOpens)) b =
        pushforwardUnitEquiv _ (φ.app U.toOpens b) := by
      rw [h1, toRelativeSpec_appLE]
      rfl
    exact h3
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨y, rfl⟩ := hρs w
    obtain ⟨b, rfl⟩ : ∃ b, (algB.sectionsIso U).inv b = y :=
      ⟨(algB.sectionsIso U).hom y, Iso.hom_inv_id_apply _ _⟩
    rw [hcomp] at hw
    have hb := (hker hU b).mp hw
    have hmem : (algB.sectionsIso U).inv b ∈ RingHom.ker
        ((pullback.fst algB.relativeSpecHom (thickening.ι f I 0)).app
          (algB.relativeSpecHom ⁻¹ᵁ U.toOpens)).hom := by
      rw [hρk]
      exact sectionsIso_inv_mem_map algB U _ b hb
    exact RingHom.mem_ker.mp hmem
  · intro z
    obtain ⟨b, hb⟩ := hsurj hU z
    exact ⟨_, (hcomp b).trans hb⟩

end ClosedFibreIso

section Existence

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} {τ : Type u} [Finite τ] (κ : X ⟶ ℙ(τ; Spec A)) [IsClosedImmersion κ]

omit [IsNoetherianRing A] [IsAdicComplete I A] in
set_option backward.isDefEq.respectTransparency.types false in
/-- The reduction `(Y₀ ⟶ X)_* 𝒪` of an étale covering of the formal completion is formally
unramified over `X` on affine opens. -/
lemma formallyUnramified_formal (f : X ⟶ Spec A)
    (𝒴 : Scheme.FormalFiniteEtale (thickeningDiagram I f)) (U : X.AffineZariskiSite) :
    Algebra.FormallyUnramified Γ(X, U.toOpens)
      ((pushforwardAlgebra (formalStructure I f 𝒴 0)).Sections U.toOpens) := by
  let U₀ := thickening.ι f I 0 ⁻¹ᵁ U.toOpens
  have hU₀ : IsAffineOpen U₀ := U.2.preimage _
  let q := formalQ I f 𝒴 0
  let _ : Algebra Γ(X, U.toOpens) Γ(thickening f I 0, U₀) :=
    ((thickening.ι f I 0).app U.toOpens).hom.toAlgebra
  let _ : Algebra Γ(thickening f I 0, U₀) Γ((𝒴.obj 0).left, q ⁻¹ᵁ U₀) := (q.app U₀).hom.toAlgebra
  let _ : Algebra Γ(X, U.toOpens) Γ((𝒴.obj 0).left, q ⁻¹ᵁ U₀) :=
    ((formalStructure I f 𝒴 0).app U.toOpens).hom.toAlgebra
  have : IsScalarTower Γ(X, U.toOpens) Γ(thickening f I 0, U₀) Γ((𝒴.obj 0).left, q ⁻¹ᵁ U₀) :=
    .of_algebraMap_eq fun _ ↦ rfl
  have h₁ : Algebra.FormallyUnramified Γ(X, U.toOpens) Γ(thickening f I 0, U₀) :=
    .of_surjective (Algebra.ofId _ _) ((thickening.ι f I 0).app_surjective U.toOpens U.2)
  have he : (q.app U₀).hom.Etale := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE (P := @Etale) q (formalQ_etale I f 𝒴 0) ⟨U₀, hU₀⟩
      ⟨_, hU₀.preimage q⟩ le_rfl
  have : Algebra.Etale Γ(thickening f I 0, U₀) Γ((𝒴.obj 0).left, q ⁻¹ᵁ U₀) := he
  have h₂ : Algebra.FormallyUnramified Γ(X, U.toOpens) Γ((𝒴.obj 0).left, q ⁻¹ᵁ U₀) :=
    .comp Γ(X, U.toOpens) Γ(thickening f I 0, U₀) _
  let e : Γ((𝒴.obj 0).left, q ⁻¹ᵁ U₀) ≃ₐ[Γ(X, U.toOpens)]
      (pushforwardAlgebra (formalStructure I f 𝒴 0)).Sections U.toOpens :=
    AlgEquiv.ofRingEquiv
      (f := (pushforwardAlgebraSectionsEquiv (formalStructure I f 𝒴 0) U.toOpens).symm) fun r ↦
      (pushforwardAlgebraSectionsEquiv (formalStructure I f 𝒴 0) U.toOpens).injective (by
        change (formalStructure I f 𝒴 0).app U.toOpens r =
          (formalStructure I f 𝒴 0).app U.toOpens r * pushforwardUnitEquiv _
            (1 : (pushforwardAlgebra (formalStructure I f 𝒴 0)).Sections U.toOpens)
        rw [show pushforwardUnitEquiv _
            (1 : (pushforwardAlgebra (formalStructure I f 𝒴 0)).Sections U.toOpens) = 1 from
          (pushforwardAlgebraSectionsEquiv _ U.toOpens).map_one, mul_one])
  exact .of_equiv e

/-- **Grothendieck's existence theorem for étale coverings, projective case** (EGA III 5.4.5;
SGA 1 IX.1.10 essential surjectivity; SGA 1 I.8.4 for the formal side): let `A` be noetherian and
`I`-adically complete, `X` a closed subscheme of `ℙ(τ; Spec A)` and `(Yₙ ⟶ Xₙ)` an étale
covering of the formal completion of `X` along `f⁻¹ V(I)`. Then there is a finite étale
`p : Y ⟶ X` with `Y ×_X X₀ ≅ Y₀` over `X₀`. -/
theorem exists_finiteEtale_of_formalFiniteEtale (f : X ⟶ Spec A)
    (hf : f = κ ≫ ℙ(τ; Spec A) ↘ Spec A) (𝒴 : Scheme.FormalFiniteEtale (thickeningDiagram I f)) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p) (_ : Etale p)
      (e : pullback p (thickening.ι f I 0) ≅ (𝒴.obj 0).left),
      e.hom ≫ formalQ I f 𝒴 0 = pullback.snd _ _ := by
  subst hf
  let G := formalAdicSystem I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) 𝒴
  have hG := formalAdicSystem_isLocallyFree I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) 𝒴
  have : (G.obj 0).IsCoherent :=
    isCoherent_pushforwardUnit (formalStructure I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) 𝒴 0)
  obtain ⟨F, hF, e, he, hproj⟩ := G.exists_iso_quotientIdealPow_projective I κ hG
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : F.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  let alg : ∀ n, ModuleAlgebra (G.obj n) := fun n ↦
    pushforwardAlgebra (formalStructure I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) 𝒴 n)
  have hmul : ∀ (n : ℕ) (U : X.Opens) (x y : Γ(G.obj (n + 1), U)),
      (G.map n).app U (mulApp (alg (n + 1)).mul U x y) =
        mulApp (alg n).mul U ((G.map n).app U x) ((G.map n).app U y) := fun n U x y ↦ by
    have h1 := mulApp_pushforwardAlgebra (formalStructure I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) 𝒴 (n + 1))
      U x y
    have h2 := mulApp_pushforwardAlgebra (formalStructure I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) 𝒴 n) U
      ((G.map n).app U x) ((G.map n).app U y)
    have h3 := pushforwardUnitMap_pfMul (𝒴.transition n)
      (transition_formalStructure I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) 𝒴 n) U x y
    exact (congrArg ((G.map n).app U) h1).trans (h3.trans h2.symm)
  have hone : ∀ n, (G.map n).app ⊤ (alg (n + 1)).one = (alg n).one := fun n ↦
    pushforwardUnitMap_one (𝒴.transition n)
      (transition_formalStructure I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) 𝒴 n)
  obtain ⟨μ, hμ⟩ := exists_mul_algebraization I _ e he alg hmul hproj
  obtain ⟨one, hone'⟩ := exists_one_algebraization I _ e he alg hone
  obtain ⟨algB, hmulB, honeB⟩ := exists_moduleAlgebra_algebraization I _ e alg hμ hproj hone'
  have hmul0 : ∀ (U : X.Opens) (x y : Γ(F, U)),
      (algRed I _ e 0).app U (mulApp algB.mul U x y) =
        mulApp (alg 0).mul U ((algRed I _ e 0).app U x) ((algRed I _ e 0).app U y) := by
    rw [hmulB]
    exact algRed_mulApp I _ e alg hμ 0
  have hone0 : (algRed I _ e 0).app ⊤ algB.one = (alg 0).one := by
    rw [honeB]
    exact hone' 0
  have hsurj : ∀ {U : X.Opens}, IsAffineOpen U → Function.Surjective ((algRed I _ e 0).app U) :=
    fun hU ↦ algRed_app_surjective I _ e 0 hU
  have hker : ∀ {U : X.Opens}, IsAffineOpen U → ∀ x : Γ(F, U), (algRed I _ e 0).app U x = 0 ↔
      x ∈ (idealV (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I U 1 • ⊤ : Submodule Γ(X, U) Γ(F, U)) := by
    intro U hU x
    constructor
    · intro h
      simpa only [zero_add, pow_one] using algRed_app_eq_zero I _ e 0 hU x h
    · intro h
      rw [algRed, Scheme.Modules.Hom.comp_app_apply,
        (toQuotientIdealPow_app_eq_zero_iff' I _ F hU 0 x).mpr (by rwa [zero_add, pow_one]),
        map_zero]
  have hunr := formallyUnramified_formal I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) 𝒴
  have hetale : Etale algB.relativeSpecHom :=
    etale_relativeSpecHom_of_reduction I _ algB (alg 0) (algRed I _ e 0) hmul0 hone0 hsurj hker
      hunr hproj
  have hmul0' : ∀ (U : X.Opens) (x y : Γ(F, U)),
      (algRed I _ e 0).app U (mulApp algB.mul U x y) =
        pfMul _ ((algRed I _ e 0).app U x) ((algRed I _ e 0).app U y) := fun U x y ↦ by
    rw [hmul0]
    exact mulApp_pushforwardAlgebra _ U _ _
  have hiso := isIso_closedFibreLift I _ algB (formalQ I _ 𝒴 0) (algRed I _ e 0) hmul0' hone0
    hsurj hker
  refine ⟨_, algB.relativeSpecHom, inferInstance, hetale,
    (asIso (closedFibreLift I _ algB (formalQ I _ 𝒴 0) (algRed I _ e 0) hmul0' hone0)).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  exact (closedFibreLift_snd I _ algB (formalQ I _ 𝒴 0) (algRed I _ e 0) hmul0' hone0).symm

end Existence

end AlgebraicGeometry.CohomologyAux
