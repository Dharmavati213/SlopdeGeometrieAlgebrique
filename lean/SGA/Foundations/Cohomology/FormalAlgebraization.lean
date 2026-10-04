/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.FiniteEtaleExistence

/-!
# Algebraization of finite flat covers of the formal completion (projective case)

Let `A` be a noetherian `I`-adically complete ring, `X` a closed subscheme of `ℙ(τ; Spec A)`,
`f : X ⟶ Spec A` and `Xₙ = X ×_A A / I^{n+1}` (`thickening f I n`). A *finite flat covering of
the formal completion* of `X` along `f⁻¹ V(I)` (`FormalFiniteFlat I f`) is a sequence of finite
flat morphisms `qₙ : Yₙ ⟶ Xₙ` with `Yₙ = Yₙ₊₁ ×_{Xₙ₊₁} Xₙ`. We prove
(`exists_finite_flat_of_formalFiniteFlat`) that such a system is algebraizable: there is a finite
flat `p : Y ⟶ X` with `Y ×_X X₀ ≅ Y₀` over `X₀`. This is the existence part of EGA III 5.4.5
for finite flat formal `X̂`-schemes, in the projective case, with only the level-`0`
identification (EGA III 5.4.5 is an equivalence of categories and identifies the whole formal
completion of `Y` with `(Yₙ)`); Stacks 0A42 is the existence theorem used.

This is the finite flat analogue of `exists_finiteEtale_of_formalFiniteEtale`, and the proof is
the same: the algebras `(Yₙ ⟶ X)_* 𝒪` form a locally free adic system (finite flat algebras over
the noetherian rings `Γ(X, U) / I^{n+1}` are projective), the existence theorem for locally free
adic systems (`AdicSystem.exists_iso_quotientIdealPow_projective`) gives a coherent `𝒪_X`-module
`B` with projective sections, the algebra structures algebraize
(`exists_moduleAlgebra_algebraization`), and `Y = Spec_X B`. Flatness of `Y ⟶ X` comes from the
projectivity of the sections of `B`.

## Main definitions and results

* `AlgebraicGeometry.CohomologyAux.projective_pushforwardUnit_sections_of_flat`: for `p` finite
  and flat over a locally noetherian scheme, the sections of `p_* 𝒪` over affine opens are
  projective.
* `AlgebraicGeometry.CohomologyAux.FormalFiniteFlat`: finite flat coverings of the formal
  completion.
* `AlgebraicGeometry.CohomologyAux.exists_finite_flat_of_formalFiniteFlat`: their
  algebraization.

## References

* [EGA III, 5.4.5][EGA3], [EGA III, 5.1.4][EGA3]; Stacks Tag 088C, 0A42.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

open Scheme.Modules

section FlatSections

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

set_option backward.isDefEq.respectTransparency.types false in
/-- For `p` finite and flat over a locally noetherian scheme, the sections of `p_* 𝒪_Y` over
affine opens are projective. -/
lemma projective_pushforwardUnit_sections_of_flat [IsLocallyNoetherian X] [IsFinite p] [Flat p]
    {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Projective Γ(X, U) Γ(pushforwardUnit p, U) := by
  have hfl : (p.app U).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE (P := @Flat) p ‹_› ⟨U, hU⟩ ⟨_, hU.preimage p⟩ le_rfl
  have hf : (p.app U).hom.Finite := p.finite_app U hU
  let _ := (p.app U).hom.toAlgebra
  have : Module.Flat Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := hfl
  have : Module.Finite Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := hf
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.FinitePresentation Γ(X, U) Γ(Y, p ⁻¹ᵁ U) :=
    Module.finitePresentation_of_finite _ _
  have : Module.Projective Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := Module.Flat.projective_of_finitePresentation
  exact this

/-- For `q : Z ⟶ X'` finite and flat and `i : X' ⟶ X` affine, surjective on sections over the
affine `U`, with `X'` locally noetherian, the sections of `(q ≫ i)_* 𝒪_Z` over `U` have the
lifting property for modules killed by the ideal of `i`. -/
lemma liftingProperty_pushforwardUnit_comp_of_flat {Z X' : Scheme.{u}} (q : Z ⟶ X')
    (i : X' ⟶ X) [IsLocallyNoetherian X'] [IsFinite q] [Flat q] [IsAffineHom i] {U : X.Opens}
    (hU : IsAffineOpen U) (hi : Function.Surjective (i.app U)) {K : Ideal Γ(X, U)}
    (hK : RingHom.ker (i.app U).hom = K) :
    LiftingProperty K Γ(pushforwardUnit (q ≫ i), U) :=
  letI : Module Γ(X', i ⁻¹ᵁ U) Γ(pushforwardUnit (q ≫ i), U) :=
    inferInstanceAs (Module Γ(X', i ⁻¹ᵁ U) Γ(pushforwardUnit q, i ⁻¹ᵁ U))
  haveI : Module.Projective Γ(X', i ⁻¹ᵁ U) Γ(pushforwardUnit (q ≫ i), U) :=
    projective_pushforwardUnit_sections_of_flat q (hU.preimage i)
  hK ▸ liftingProperty_of_projective (i.app U).hom hi (fun _ _ ↦ rfl)

end FlatSections

section Structure

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- A **finite flat covering of the formal completion** of `X` along `f⁻¹ V(I)`: finite flat
morphisms `qₙ : Yₙ ⟶ Xₙ` to the thickenings `Xₙ = X ×_A A / I^{n+1}`, with transition morphisms
`Yₙ ⟶ Yₙ₊₁` making `Yₙ = Yₙ₊₁ ×_{Xₙ₊₁} Xₙ` (EGA III 5.4.5, for finite flat formal schemes over
`X̂`). -/
structure FormalFiniteFlat where
  /-- The schemes `Yₙ`. -/
  obj : ℕ → Scheme.{u}
  /-- The structure morphisms `Yₙ ⟶ Xₙ`. -/
  hom (n : ℕ) : obj n ⟶ thickening f I n
  isFinite_hom (n : ℕ) : IsFinite (hom n)
  flat_hom (n : ℕ) : Flat (hom n)
  /-- The transition morphisms `Yₙ ⟶ Yₙ₊₁`. -/
  transition (n : ℕ) : obj n ⟶ obj (n + 1)
  isPullback (n : ℕ) : IsPullback (transition n) (hom n) (hom (n + 1)) (thickening.transition f I n)

namespace FormalFiniteFlat

variable {I f} (𝒴 : FormalFiniteFlat I f)

attribute [instance] isFinite_hom flat_hom

/-- The composite `Yₙ ⟶ Xₙ ⟶ X`. -/
abbrev structureHom (n : ℕ) : 𝒴.obj n ⟶ X :=
  𝒴.hom n ≫ thickening.ι f I n

lemma transition_hom (n : ℕ) :
    𝒴.transition n ≫ 𝒴.hom (n + 1) = 𝒴.hom n ≫ thickening.transition f I n :=
  (𝒴.isPullback n).w

lemma transition_structureHom (n : ℕ) :
    𝒴.transition n ≫ 𝒴.structureHom (n + 1) = 𝒴.structureHom n := by
  rw [structureHom, structureHom, ← Category.assoc, transition_hom, Category.assoc,
    thickening.transition_ι]

lemma structureHom_preimage (n : ℕ) (U : X.Opens) :
    𝒴.structureHom n ⁻¹ᵁ U =
      𝒴.transition n ⁻¹ᵁ (𝒴.hom (n + 1) ⁻¹ᵁ (thickening.ι f I (n + 1) ⁻¹ᵁ U)) := by
  rw [← transition_structureHom 𝒴 n, structureHom, Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage]

lemma transition_app_surjective (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective ((pushforwardUnitMap (𝒴.transition n)
        (𝒴.transition_structureHom n)).app U) := by
  let U' := thickening.ι f I (n + 1) ⁻¹ᵁ U
  have hU' : IsAffineOpen U' := hU.preimage _
  obtain ⟨hs, -⟩ := app_surjective_ker_of_isPullback (𝒴.isPullback n) hU'
    (hU'.preimage _) (hU'.preimage _) ((thickening.transition f I n).app_surjective U' hU')
  obtain ⟨hsurj, -⟩ := appLE_surjective_ker_of_eq (𝒴.transition n)
    (𝒴.hom (n + 1) ⁻¹ᵁ U') (𝒴.structureHom_preimage n U)
    (preimage_le_preimage_of_comp_eq _ (𝒴.transition_structureHom n) U)
  intro y
  obtain ⟨x, hx⟩ := hsurj.mpr hs (pushforwardUnitEquiv _ y)
  exact ⟨(pushforwardUnitEquiv _).symm x, (pushforwardUnitMap_app (𝒴.transition n)
    (𝒴.transition_structureHom n) U _).trans hx⟩

lemma transition_ker (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) :
    RingHom.ker ((𝒴.transition n).appLE (𝒴.structureHom (n + 1) ⁻¹ᵁ U)
        (𝒴.structureHom n ⁻¹ᵁ U)
        (preimage_le_preimage_of_comp_eq _ (𝒴.transition_structureHom n) U)).hom =
      (idealV f I U (n + 1)).map ((𝒴.structureHom (n + 1)).app U).hom := by
  let U' := thickening.ι f I (n + 1) ⁻¹ᵁ U
  have hU' : IsAffineOpen U' := hU.preimage _
  obtain ⟨-, hk⟩ := app_surjective_ker_of_isPullback (𝒴.isPullback n) hU'
    (hU'.preimage _) (hU'.preimage _) ((thickening.transition f I n).app_surjective U' hU')
  obtain ⟨-, hker⟩ := appLE_surjective_ker_of_eq (𝒴.transition n)
    (𝒴.hom (n + 1) ⁻¹ᵁ U') (𝒴.structureHom_preimage n U)
    (preimage_le_preimage_of_comp_eq _ (𝒴.transition_structureHom n) U)
  rw [ker_thickening_transition_app I f n hU, map_map_app_comp] at hk
  exact hker.trans hk

lemma transition_app_eq_zero_iff (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (s : Γ(pushforwardUnit (𝒴.structureHom (n + 1)), U)) :
    (pushforwardUnitMap (𝒴.transition n) (𝒴.transition_structureHom n)).app U s = 0 ↔
      s ∈ (idealV f I U 1 ^ (n + 1) • ⊤ :
        Submodule Γ(X, U) Γ(pushforwardUnit (𝒴.structureHom (n + 1)), U)) := by
  rw [mem_smul_top_pushforwardUnit_iff, ← AdicSystem.idealV_eq_pow,
    ← 𝒴.transition_ker n hU, RingHom.mem_ker,
    ← pushforwardUnitMap_app (𝒴.transition n) (𝒴.transition_structureHom n)]
  rfl

/-- The adic system `(Yₙ ⟶ X)_* 𝒪_{Yₙ}` of a finite flat covering of the formal completion. -/
def adicSystem : AdicSystem I f where
  obj n := pushforwardUnit (𝒴.structureHom n)
  map n := pushforwardUnitMap (𝒴.transition n) (𝒴.transition_structureHom n)
  isQuasicoherent _ := inferInstance
  surjective n _ hU := 𝒴.transition_app_surjective n hU
  map_app_eq_zero_iff n _ hU s := 𝒴.transition_app_eq_zero_iff n hU s

lemma adicSystem_isLocallyFree (h : ∀ n, IsLocallyNoetherian (thickening f I n)) :
    𝒴.adicSystem.IsLocallyFree := by
  intro n U hU
  have hker : RingHom.ker ((thickening.ι f I n).app U).hom = idealV f I U 1 ^ (n + 1) := by
    rw [ker_thickening_app I f n hU, AdicSystem.idealV_eq_pow]
  have hs : Function.Surjective ((thickening.ι f I n).app U) :=
    (thickening.ι f I n).app_surjective U hU
  have := h n
  change LiftingProperty _ Γ(pushforwardUnit (𝒴.hom n ≫ thickening.ι f I n), U)
  exact liftingProperty_pushforwardUnit_comp_of_flat (𝒴.hom n) (thickening.ι f I n) hU hs hker

end FormalFiniteFlat

end Structure

section Flatness

variable {X : Scheme.{u}} {B : X.Modules} [B.IsQuasicoherent] (algB : ModuleAlgebra B)

set_option backward.isDefEq.respectTransparency.types false in
/-- `Spec_X B ⟶ X` is flat if the sections of `B` over affine opens are flat modules. -/
theorem flat_relativeSpecHom
    (h : ∀ {U : X.Opens}, IsAffineOpen U → Module.Flat Γ(X, U) Γ(B, U)) :
    Flat algB.relativeSpecHom :=
  algB.relativeSpecHom_of (P := @Flat) fun U ↦ by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    have : Module.Flat Γ(X, U.toOpens) (algB.Sections U.toOpens) := h U.2
    exact RingHom.flat_algebraMap_iff.mpr this

end Flatness

section Existence

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} {τ : Type u} [Finite τ] (κ : X ⟶ ℙ(τ; Spec A)) [IsClosedImmersion κ]

/-- **Grothendieck's existence theorem for finite flat coverings, projective case** (the
existence part of EGA III 5.4.5 for finite flat formal `X̂`-schemes, with only the level-`0`
identification): let `A` be noetherian and `I`-adically complete, `X` a
closed subscheme of `ℙ(τ; Spec A)` and `(Yₙ ⟶ Xₙ)` a finite flat covering of the formal
completion of `X` along `f⁻¹ V(I)`. Then there is a finite flat `p : Y ⟶ X` with
`Y ×_X X₀ ≅ Y₀` over `X₀`. -/
theorem exists_finite_flat_of_formalFiniteFlat (f : X ⟶ Spec A)
    (hf : f = κ ≫ ℙ(τ; Spec A) ↘ Spec A) (𝒴 : FormalFiniteFlat I f) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p) (_ : Flat p)
      (e : pullback p (thickening.ι f I 0) ≅ 𝒴.obj 0),
      e.hom ≫ 𝒴.hom 0 = pullback.snd _ _ := by
  subst hf
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (κ ≫ ℙ(τ; Spec A) ↘ Spec A)
  have hnoeth : ∀ n, IsLocallyNoetherian (thickening (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n) :=
    fun n ↦ LocallyOfFiniteType.isLocallyNoetherian
      (thickening.ι (κ ≫ ℙ(τ; Spec A) ↘ Spec A) I n)
  let G := 𝒴.adicSystem
  have hG := 𝒴.adicSystem_isLocallyFree hnoeth
  have : (G.obj 0).IsCoherent := isCoherent_pushforwardUnit (𝒴.structureHom 0)
  obtain ⟨F, hF, e, he, hproj⟩ := G.exists_iso_quotientIdealPow_projective I κ hG
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : F.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  let alg : ∀ n, ModuleAlgebra (G.obj n) := fun n ↦ pushforwardAlgebra (𝒴.structureHom n)
  have hmul : ∀ (n : ℕ) (U : X.Opens) (x y : Γ(G.obj (n + 1), U)),
      (G.map n).app U (mulApp (alg (n + 1)).mul U x y) =
        mulApp (alg n).mul U ((G.map n).app U x) ((G.map n).app U y) := fun n U x y ↦ by
    have h1 := mulApp_pushforwardAlgebra (𝒴.structureHom (n + 1)) U x y
    have h2 := mulApp_pushforwardAlgebra (𝒴.structureHom n) U
      ((G.map n).app U x) ((G.map n).app U y)
    have h3 := pushforwardUnitMap_pfMul (𝒴.transition n) (𝒴.transition_structureHom n) U x y
    exact (congrArg ((G.map n).app U) h1).trans (h3.trans h2.symm)
  have hone : ∀ n, (G.map n).app ⊤ (alg (n + 1)).one = (alg n).one := fun n ↦
    pushforwardUnitMap_one (𝒴.transition n) (𝒴.transition_structureHom n)
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
  have hflat : Flat algB.relativeSpecHom := flat_relativeSpecHom algB fun hU ↦
    have := hproj hU
    inferInstance
  have hmul0' : ∀ (U : X.Opens) (x y : Γ(F, U)),
      (algRed I _ e 0).app U (mulApp algB.mul U x y) =
        pfMul _ ((algRed I _ e 0).app U x) ((algRed I _ e 0).app U y) := fun U x y ↦ by
    rw [hmul0]
    exact mulApp_pushforwardAlgebra _ U _ _
  have hiso := isIso_closedFibreLift I _ algB (𝒴.hom 0) (algRed I _ e 0) hmul0' hone0
    hsurj hker
  refine ⟨_, algB.relativeSpecHom, inferInstance, hflat,
    (asIso (closedFibreLift I _ algB (𝒴.hom 0) (algRed I _ e 0) hmul0' hone0)).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  exact (closedFibreLift_snd I _ algB (𝒴.hom 0) (algRed I _ e 0) hmul0' hone0).symm

end Existence

end AlgebraicGeometry.CohomologyAux
