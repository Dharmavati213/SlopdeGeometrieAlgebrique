/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.ThickeningReduction
import SGA.Foundations.Cohomology.AlgebraAlgebraization

/-!
# Morphisms of finite schemes over a complete base

Let `A` be a noetherian `I`-adically complete ring, `f : X ⟶ Spec A` proper and
`X_n = X ×_A A / I^{n+1}`. For finite `p : Y ⟶ X`, `p' : Y' ⟶ X`:

* `eq_of_forall_pullback_thickening_comp_eq`: two `X`-morphisms `Y ⟶ Y'` agreeing on all the
  `Y ×_X X_n` are equal;
* `exists_hom_of_forall_pullback_thickening`: for `p'` moreover étale, a compatible family of
  `X`-morphisms `Y ×_X X_n ⟶ Y'` comes from an `X`-morphism `Y ⟶ Y'`.

This is the full faithfulness of `Y ↦ (Y ×_X X_n)_n` on finite étale `X`-schemes (EGA III 5.1.4,
5.4.1; SGA 1 IX.1.10). The proof passes to the algebras `p_* 𝒪_Y`: a morphism `Y ⟶ Y'` over `X`
is an algebra morphism `p'_* 𝒪_{Y'} ⟶ p_* 𝒪_Y` (`toRelativeSpecSelf`, `comp_toRelativeSpecSelf`),
and these algebraize by the full faithfulness of the existence theorem for coherent modules
(`existsUnique_comp_toQuotientIdealPow_eq`), multiplicativity being checked modulo `I^{n+1}`
(`map_mulApp_of_reductions`, `eq_of_forall_app_top_eq`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

open Scheme.Modules

section Separation

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} (f : X ⟶ Spec A) [IsProper f]

/-- **Separation of global sections**: over a complete base, global sections of a coherent `K`
with the same images under a family `ρₙ : K ⟶ K'ₙ` with kernels in `I^{n+1} K` are equal. -/
theorem eq_of_forall_app_top_eq {K : X.Modules} [K.IsCoherent] {K' : ℕ → X.Modules}
    (ρ : ∀ n, K ⟶ K' n)
    (hρ : ∀ (n : ℕ) {V : X.Opens} (_ : IsAffineOpen V) (x : Γ(K, V)), (ρ n).app V x = 0 →
      x ∈ (idealV f I V 1 ^ (n + 1) • ⊤ : Submodule Γ(X, V) Γ(K, V)))
    {s t : Γ(K, ⊤)} (h : ∀ n, (ρ n).app ⊤ s = (ρ n).app ⊤ t) : s = t := by
  have : K.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have key : homOfSection K s = homOfSection K t := by
    refine eq_of_comp_toQuotientIdealPow_eq I f fun n ↦ ?_
    rw [← sub_eq_zero, ← Preadditive.sub_comp]
    refine hom_ext_of_affine fun V hV (r : Γ(X, V)) ↦ ?_
    change (K.toQuotientIdealPow f I n).app V
      (r • K.presheaf.map (homOfLE le_top : V ⟶ ⊤).op s -
        r • K.presheaf.map (homOfLE le_top : V ⟶ ⊤).op t) = 0
    rw [← smul_sub, ← map_sub, toQuotientIdealPow_app_eq_zero_iff' I f K hV]
    refine Submodule.smul_mem _ _ (hρ n hV _ ?_)
    rw [hom_app_presheaf_map, map_sub, h n, sub_self, map_zero]
  have h₁ := congrArg (fun φ : unitModule X ⟶ K ↦ φ.app ⊤ (1 : Γ(X, ⊤))) key
  change (1 : Γ(X, ⊤)) • K.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op s =
    (1 : Γ(X, ⊤)) • K.presheaf.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op t at h₁
  rwa [one_smul, one_smul, modules_map_self, modules_map_self] at h₁

/-- The multiplicativity of `d : B' ⟶ B` can be checked after the reductions `ρₙ`, when these are
multiplicative with kernels in `I^{n+1} B` (over a complete base, `X` proper). -/
theorem map_mulApp_of_reductions {B' B : X.Modules}
    [B'.IsCoherent] [B.IsCoherent]
    (hB' : ∀ {V : X.Opens}, IsAffineOpen V → Module.Projective Γ(X, V) Γ(B', V))
    (μ' : B' ⟶ sheafHom B' B') (μ : B ⟶ sheafHom B B)
    {K : ℕ → X.Modules} (μK : ∀ n, K n ⟶ sheafHom (K n) (K n)) (ρ : ∀ n, B ⟶ K n)
    (hρ : ∀ (n : ℕ) {V : X.Opens} (_ : IsAffineOpen V) (x : Γ(B, V)), (ρ n).app V x = 0 →
      x ∈ (idealV f I V 1 ^ (n + 1) • ⊤ : Submodule Γ(X, V) Γ(B, V)))
    (hρmul : ∀ n (U : X.Opens) (x y : Γ(B, U)),
      (ρ n).app U (mulApp μ U x y) = mulApp (μK n) U ((ρ n).app U x) ((ρ n).app U y))
    (d : B' ⟶ B)
    (hdmul : ∀ n (U : X.Opens) (x y : Γ(B', U)),
      (ρ n).app U (d.app U (mulApp μ' U x y)) =
        mulApp (μK n) U ((ρ n).app U (d.app U x)) ((ρ n).app U (d.app U y)))
    (U : X.Opens) (x y : Γ(B', U)) :
    d.app U (mulApp μ' U x y) = mulApp μ U (d.app U x) (d.app U y) := by
  have key : μ' ≫ sheafHomPostcomp d = d ≫ μ ≫ sheafHomPrecomp d := by
    refine eq_of_comp_sheafHomPostcomp_eq I f hB' ρ hρ fun n ↦ ?_
    refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
    ext a
    refine HomOn.ext (funext fun V ↦ funext fun hV ↦ LinearMap.ext fun c ↦ ?_)
    change (ρ n).app V (d.app V (((μ'.app U a : Γ(sheafHom B' B', U)) :
        HomOn B' B' U).app V hV c)) =
      (ρ n).app V (((μ.app U (d.app U a) : Γ(sheafHom B B, U)) : HomOn B B U).app V hV
        (d.app V c))
    rw [mulApp_eq μ' hV, mulApp_eq μ hV, hdmul, hρmul, hom_app_presheaf_map d]
  have h := congrArg (fun φ : B' ⟶ sheafHom B' B ↦
    ((φ.app U x : Γ(sheafHom B' B, U)) : HomOn B' B U).app U le_rfl y) key
  exact h

end Separation

section RelativeSpecSelf

variable {X Y Y' : Scheme.{u}} (p : Y ⟶ X) {p' : Y' ⟶ X} [IsAffineHom p] [IsAffineHom p']

lemma mulApp_pushforwardAlgebra {Z : Scheme.{u}} (g : Z ⟶ X) (U : X.Opens)
    (x y : Γ(pushforwardUnit g, U)) :
    mulApp (pushforwardAlgebra g).mul U x y = pfMul g x y :=
  mulApp_pfMulHom g U x y

lemma toRelativeSpec_congr {Z : Scheme.{u}} {g : Z ⟶ X} {B : X.Modules} [B.IsQuasicoherent]
    (algB : ModuleAlgebra B) {φ φ' : B ⟶ pushforwardUnit g} (e : φ = φ') (hmul hone hmul' hone') :
    toRelativeSpec algB φ hmul hone = toRelativeSpec algB φ' hmul' hone' := by
  subst e
  rfl

omit [IsAffineHom p] [IsAffineHom p'] in
lemma pushforwardAlgebra_hone :
    (𝟙 (pushforwardUnit p) : pushforwardUnit p ⟶ _).app ⊤ (pushforwardAlgebra p).one =
      (pushforwardUnitEquiv p).symm 1 :=
  rfl

/-- The comparison morphism `Y ⟶ Spec_X p_* 𝒪_Y`, an isomorphism for `p` affine. -/
def toRelativeSpecSelf : Y ⟶ (pushforwardAlgebra p).relativeSpec :=
  toRelativeSpec (pushforwardAlgebra p) (𝟙 _) (pushforwardAlgebra_hmul p)
    (pushforwardAlgebra_hone p)

instance : IsIso (toRelativeSpecSelf p) :=
  isIso_toRelativeSpec_pushforwardAlgebra p

@[reassoc (attr := simp)]
lemma toRelativeSpecSelf_relativeSpecHom :
    toRelativeSpecSelf p ≫ (pushforwardAlgebra p).relativeSpecHom = p :=
  toRelativeSpec_relativeSpecHom _ _ _ _

variable {p} in
omit [IsAffineHom p] in
lemma comp_toRelativeSpecSelf (u : Y ⟶ Y') (hu : u ≫ p' = p) :
    u ≫ toRelativeSpecSelf p' = toRelativeSpec (pushforwardAlgebra p') (pushforwardUnitMap u hu)
      (by
        have := comp_pushforwardUnitMap_hmul u hu _ _ (pushforwardAlgebra_hmul p')
        simpa only [Category.id_comp] using this)
      (by
        have := comp_pushforwardUnitMap_hone u hu _ (𝟙 _) (pushforwardAlgebra_hone p')
        simpa only [Category.id_comp] using this) := by
  rw [toRelativeSpecSelf, comp_toRelativeSpec u hu]
  exact toRelativeSpec_congr _ (Category.id_comp _) _ _ _ _

end RelativeSpecSelf

section FullyFaithful

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} (f : X ⟶ Spec A) [IsProper f] {Y Y' : Scheme.{u}} {p : Y ⟶ X} {p' : Y' ⟶ X}
  [IsFinite p] [IsFinite p']

include I in
/-- **Uniqueness for morphisms of finite `X`-schemes** (EGA III 5.1.4, SGA 1 IX.1.10): over a
complete noetherian base and `X` proper, two `X`-morphisms `Y ⟶ Y'` of finite `X`-schemes which
agree on all the `Y ×_X X_n` are equal. -/
theorem eq_of_forall_pullback_thickening_comp_eq {u u' : Y ⟶ Y'} (hu : u ≫ p' = p)
    (hu' : u' ≫ p' = p)
    (h : ∀ n, pullback.fst p (thickening.ι f I n) ≫ u = pullback.fst p (thickening.ι f I n) ≫ u') :
    u = u' := by
  have := isCoherent_pushforwardUnit p
  have := isCoherent_pushforwardUnit p'
  have key : pushforwardUnitMap u hu = pushforwardUnitMap u' hu' := by
    refine eq_of_comp_toQuotientIdealPow_eq I f fun n ↦ ?_
    rw [← cancel_mono (reductionIso I f p n).hom, Category.assoc, Category.assoc,
      toQuotientIdealPow_reductionIso_hom, reductionMap, ← pushforwardUnitMap_comp,
      ← pushforwardUnitMap_comp]
    exact pushforwardUnitMap_congr (h n) _ _
  rw [← cancel_mono (toRelativeSpecSelf p'), comp_toRelativeSpecSelf u hu,
    comp_toRelativeSpecSelf u' hu']
  exact toRelativeSpec_congr _ key _ _ _ _

/-- **Existence for morphisms of finite étale `X`-schemes** (EGA III 5.1.4, 5.4.1; SGA 1
IX.1.10): over a complete noetherian base and `X` proper, a compatible family of `X`-morphisms
`Y ×_X X_n ⟶ Y'` comes from an `X`-morphism `Y ⟶ Y'`. -/
theorem exists_hom_of_forall_pullback_thickening [Etale p']
    (ψ : ∀ n, pullback p (thickening.ι f I n) ⟶ Y')
    (hψ : ∀ n, ψ n ≫ p' = pullback.fst p (thickening.ι f I n) ≫ p)
    (τ : ∀ n, pullback p (thickening.ι f I n) ⟶ pullback p (thickening.ι f I (n + 1)))
    (hτ : ∀ n, τ n ≫ pullback.fst _ _ = pullback.fst _ _)
    (hc : ∀ n, τ n ≫ ψ (n + 1) = ψ n) :
    ∃ u : Y ⟶ Y', u ≫ p' = p ∧ ∀ n, pullback.fst p (thickening.ι f I n) ≫ u = ψ n := by
  have := isCoherent_pushforwardUnit p
  have := isCoherent_pushforwardUnit p'
  let d : ∀ n, pushforwardUnit p' ⟶ pushforwardUnit (pullback.fst p (thickening.ι f I n) ≫ p) :=
    fun n ↦ pushforwardUnitMap (ψ n) (hψ n)
  have hd : ∀ n, d (n + 1) ≫ pushforwardUnitMap (τ n)
      (comp_fst_comp_eq_of_comp_fst I f p (hτ n)) = d n := by
    intro n
    rw [← pushforwardUnitMap_comp]
    exact pushforwardUnitMap_congr (hc n) _ _
  let v : ∀ n, pushforwardUnit p' ⟶ (pushforwardUnit p).quotientIdealPow f I n :=
    fun n ↦ d n ≫ (reductionIso I f p n).inv
  have hv : ∀ n, v (n + 1) ≫ (pushforwardUnit p).quotientIdealPowMap f I n = v n := by
    intro n
    have e : (reductionIso I f p (n + 1)).inv ≫ (pushforwardUnit p).quotientIdealPowMap f I n =
        pushforwardUnitMap (τ n) (comp_fst_comp_eq_of_comp_fst I f p (hτ n)) ≫
          (reductionIso I f p n).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, ← quotientIdealPowMap_reductionIso' I f p (τ n) (hτ n),
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simp only [v, Category.assoc, e]
    rw [← Category.assoc, hd]
  obtain ⟨d₀, hd₀, -⟩ := existsUnique_comp_toQuotientIdealPow_eq I f v hv
  have hred : ∀ n, d₀ ≫ reductionMap I f p n = d n := by
    intro n
    rw [← toQuotientIdealPow_reductionIso_hom, ← Category.assoc, hd₀, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hred' : ∀ n (U : X.Opens) (z : Γ(pushforwardUnit p', U)),
      (reductionMap I f p n).app U (d₀.app U z) = (d n).app U z := fun n U z ↦ by
    rw [← Scheme.Modules.Hom.comp_app_apply, hred]
  have hρ : ∀ (n : ℕ) {V : X.Opens} (_ : IsAffineOpen V) (x : Γ(pushforwardUnit p, V)),
      (reductionMap I f p n).app V x = 0 →
        x ∈ (idealV f I V 1 ^ (n + 1) • ⊤ : Submodule Γ(X, V) Γ(pushforwardUnit p, V)) :=
    fun n V hV x hx ↦ ((reductionMap_app_surjective_and I f p n hV).2 x).mp hx
  have hmul : ∀ (U : X.Opens) (x y : Γ(pushforwardUnit p', U)),
      d₀.app U (mulApp (pushforwardAlgebra p').mul U x y) =
        pfMul p (d₀.app U x) (d₀.app U y) := by
    intro U x y
    rw [← mulApp_pushforwardAlgebra p]
    refine map_mulApp_of_reductions I f (projective_pushforwardUnit_sections p')
      (pushforwardAlgebra p').mul (pushforwardAlgebra p).mul
      (fun n ↦ (pushforwardAlgebra (pullback.fst p (thickening.ι f I n) ≫ p)).mul)
      (reductionMap I f p) hρ (fun n U x y ↦ ?_) d₀ (fun n U x y ↦ ?_) U x y
    · rw [mulApp_pushforwardAlgebra, mulApp_pushforwardAlgebra]
      exact pushforwardUnitMap_pfMul _ _ U x y
    · rw [hred', hred', hred', mulApp_pushforwardAlgebra, mulApp_pushforwardAlgebra]
      exact pushforwardUnitMap_pfMul _ _ U x y
  have hone : d₀.app ⊤ (pushforwardAlgebra p').one = (pushforwardUnitEquiv p).symm 1 := by
    refine eq_of_forall_app_top_eq I f (reductionMap I f p) hρ fun n ↦ ?_
    rw [hred']
    exact (pushforwardUnitMap_one _ _).trans (pushforwardUnitMap_one _ _).symm
  refine ⟨toRelativeSpec (pushforwardAlgebra p') d₀ hmul hone ≫ inv (toRelativeSpecSelf p'), ?_,
    fun n ↦ ?_⟩
  · have e : inv (toRelativeSpecSelf p') ≫ p' = (pushforwardAlgebra p').relativeSpecHom := by
      rw [IsIso.inv_comp_eq, toRelativeSpecSelf_relativeSpecHom]
    rw [Category.assoc, e, toRelativeSpec_relativeSpecHom]
  · rw [← Category.assoc, comp_toRelativeSpec (pullback.fst p (thickening.ι f I n)) rfl,
      IsIso.comp_inv_eq, comp_toRelativeSpecSelf (ψ n) (hψ n)]
    exact toRelativeSpec_congr _ (hred n) _ _ _ _

end FullyFaithful

end AlgebraicGeometry.CohomologyAux
