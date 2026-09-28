/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.RelativeDerivation
import SGA.SGA1.ExposeIII.GlobalExtension

/-!
# SGA 1, Exposé III, 5.3–5.4: extension of morphisms over a non-affine thickening

Let `f : X → S` be smooth with `S` affine, `p : T → S`, `i : T₀ → T` a surjective closed immersion
whose ideal has square zero, and `g₀ : T₀ → X` an `S`-morphism. SGA 1 III.5.3–5.4: locally `g₀`
extends (III.3.1), two local extensions differ by a section of `𝒢 = ℋom(g₀^* Ω_{X/S}, 𝒥)`
(III.5.2), and the obstruction to a global extension is the class in `H¹(T₀, 𝒢)` of the torsor
of local extensions.

We prove the Čech form (`exists_extension_of_cech`): if `T` is covered by finitely many affine
opens `Uₖ` with `g₀(i⁻¹ Uₖ)` contained in affine opens of `X`, and the Čech complex of `𝒢`
(`relDerivationPresheaf`) for this cover is exact in degree `1`, then `g₀` extends to `T`. The
differences `eₗ - eₖ` of local extensions form a Čech `1`-cocycle; a primitive corrects the `eₖ`,
which then glue.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TopCat.Presheaf (cechOpen cechOpen_le CechCochain cechD cechD_apply)

noncomputable section

namespace SGA.SGA1.ExposeIII

variable {X T T₀ S : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) {i : T₀ ⟶ T} {g₀ : T₀ ⟶ X}

set_option backward.isDefEq.respectTransparency false in
/-- III.5.3–5.4, Čech form: let `f : X → S` be smooth with `S` affine, `i : T₀ → T` a surjective
closed immersion whose ideal has square zero on affine opens, and `g₀ : T₀ → X` an `S`-morphism.
Let `Uₖ` be finitely many affine opens covering `T` with `g₀(i⁻¹ Uₖ) ⊆ Vₖ` for affine opens
`Vₖ ⊆ X`. If the Čech complex of `𝒢 = ℋom(g₀^* Ω_{X/S}, 𝒥)` for the cover `(Uₖ)` is exact in
degree `1`, then `g₀` extends to an `S`-morphism `T → X`. -/
theorem exists_extension_of_cech [IsAffine S] [Smooth f] [Surjective i] [IsClosedImmersion i]
    (hsq : IsSqZeroOn i) (hg₀ : g₀ ≫ f = i ≫ p) {n : ℕ} (U : Fin n → T.Opens)
    (V : Fin n → X.Opens) (hU : ∀ k, IsAffineOpen (U k)) (hV : ∀ k, IsAffineOpen (V k))
    (hle : ∀ k, i ⁻¹ᵁ U k ≤ g₀ ⁻¹ᵁ V k) (hcov : ⨆ k, U k = ⊤)
    (hexact : (TopCat.Presheaf.cechComplex U (relDerivationPresheaf f i g₀)).ExactAt 1) :
    ∃ g : T ⟶ X, g ≫ f = p ∧ i ≫ g = g₀ := by
  classical
  let c (k : Fin n) : ExtensionChart i g₀ := ⟨V k, U k, hV k, hU k, hle k⟩
  have hext (k : Fin n) := exists_extension_of_affineOpens f p i i.surjective g₀ hg₀
    (isAffineOpen_top S) (hV k) (hU k) (by simp) (by simp) (hle k)
  choose eh he₁ he₂ using hext
  let e (k : Fin n) : Extension f p i g₀ (U k) := ⟨eh k, he₁ k, he₂ k⟩
  let P := relDerivationPresheaf f i g₀
  rw [TopCat.Presheaf.cechComplex_exactAt_succ_iff] at hexact
  -- the cocycle of differences of the local extensions
  let c₁ : CechCochain U P 1 := fun x ↦ RelChartDerivation.diff hsq
    ((e (x 0)).restrict (cechOpen_le U x 0)) ((e (x 1)).restrict (cechOpen_le U x 1))
  have hc₁ : cechD U P 1 c₁ = 0 := by
    funext x
    refine RelChartDerivation.ext fun c' hc' a ↦ ?_
    let E (j : Fin (1 + 1 + 1)) : Γ(T, c'.W) :=
      (e (x j)).chartMap c' (hc'.trans (cechOpen_le U x j)) a
    have hA (l : Fin (1 + 1 + 1)) (h : cechOpen U x ≤ cechOpen U (x ∘ Fin.succAbove l)) :
        relDerivationPresheafEval c' hc' a (P.map (homOfLE h).op (c₁ (x ∘ Fin.succAbove l))) =
          E (Fin.succAbove l 1) - E (Fin.succAbove l 0) := by
      change ((e _).restrict _).chartMap c' _ a - ((e _).restrict _).chartMap c' _ a = _
      rw [Extension.chartMap_restrict, Extension.chartMap_restrict]
      rfl
    change relDerivationPresheafEval c' hc' a (cechD U P 1 c₁ x) = 0
    rw [cechD_apply, map_sum, Fin.sum_univ_three]
    simp only [map_zsmul, hA]
    have h₀ : (Fin.succAbove (0 : Fin (1 + 1 + 1)) 0) = 1 := rfl
    have h₁ : (Fin.succAbove (0 : Fin (1 + 1 + 1)) 1) = 2 := rfl
    have h₂ : (Fin.succAbove (1 : Fin (1 + 1 + 1)) 0) = 0 := rfl
    have h₃ : (Fin.succAbove (1 : Fin (1 + 1 + 1)) 1) = 2 := rfl
    have h₄ : (Fin.succAbove (2 : Fin (1 + 1 + 1)) 0) = 0 := rfl
    have h₅ : (Fin.succAbove (2 : Fin (1 + 1 + 1)) 1) = 1 := rfl
    simp only [h₀, h₁, h₂, h₃, h₄, h₅, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      neg_one_sq, one_smul, neg_smul]
    abel
  obtain ⟨b, hb⟩ := hexact c₁ hc₁
  -- correct the local extensions by the `0`-cochain `b`
  have hbk (k : Fin n) : U k ≤ cechOpen U (fun _ : Fin 1 ↦ k) := le_iInf fun _ ↦ le_rfl
  let bk (k : Fin n) : RelChartDerivation f i g₀ (U k) :=
    RelChartDerivation.res (hbk k) (b fun _ ↦ k)
  let e' (k : Fin n) : Extension f p i g₀ (U k) :=
    (e k).ofRelChartDer hsq ((-bk k).app (c k) le_rfl) ((-bk k).isChartDer (c k) le_rfl)
  have hdiff (k : Fin n) : RelChartDerivation.diff hsq (e k) (e' k) = -bk k :=
    RelChartDerivation.diff_ofRelChartDer hsq (c := c k) (e k) (-bk k)
  have hE {k k' : Fin n} (hk : k = k') (c' : ExtensionChart i g₀) (h : c'.W ≤ U k)
      (h' : c'.W ≤ U k') (a : Γ(X, c'.V)) : (e k).chartMap c' h a = (e k').chartMap c' h' a := by
    subst hk; rfl
  have hcompat (k l : Fin n) :
      (e' k).restrict (inf_le_left : U k ⊓ U l ≤ U k) = (e' l).restrict inf_le_right := by
    rw [← RelChartDerivation.diff_eq_zero_iff hsq]
    refine RelChartDerivation.ext fun c' hc' a ↦ ?_
    have hkl : c'.W ≤ cechOpen U ![k, l] :=
      hc'.trans (le_iInf fun j ↦ Fin.cases inf_le_left (fun j ↦ Fin.cases inf_le_right
        (fun j ↦ j.elim0) j) j)
    have hB (z : Fin 1 → Fin n) (k' : Fin n) (hz : z = fun _ ↦ k') (hk' : c'.W ≤ U k')
        (h : cechOpen U ![k, l] ≤ cechOpen U z) :
        relDerivationPresheafEval c' hkl a (P.map (homOfLE h).op (b z)) =
          (bk k').app c' hk' a := by
      subst hz; rfl
    have hcoc := congrArg (relDerivationPresheafEval c' hkl a) (congrFun hb ![k, l])
    rw [cechD_apply, map_sum, Fin.sum_univ_two] at hcoc
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, map_neg] at hcoc
    rw [hB (![k, l] ∘ Fin.succAbove 0) l (by funext j; fin_cases j; rfl) (hc'.trans inf_le_right),
      hB (![k, l] ∘ Fin.succAbove 1) k (by funext j; fin_cases j; rfl)
        (hc'.trans inf_le_left)] at hcoc
    have hc1 : relDerivationPresheafEval c' hkl a (c₁ ![k, l]) =
        (e l).chartMap c' (hc'.trans inf_le_right) a -
          (e k).chartMap c' (hc'.trans inf_le_left) a := by
      change ((e _).restrict _).chartMap c' _ a - ((e _).restrict _).chartMap c' _ a = _
      rw [Extension.chartMap_restrict, Extension.chartMap_restrict,
        hE (show ![k, l] 1 = l by simp), hE (show ![k, l] 0 = k by simp)]
    rw [hc1] at hcoc
    have hk := congrArg (RelChartDerivation.appAddHom c' (hc'.trans inf_le_left) a) (hdiff k)
    have hl := congrArg (RelChartDerivation.appAddHom c' (hc'.trans inf_le_right) a) (hdiff l)
    simp only [RelChartDerivation.appAddHom_apply, RelChartDerivation.diff_app,
      RelChartDerivation.neg_app] at hk hl
    simp only [RelChartDerivation.diff_app, RelChartDerivation.zero_app,
      Extension.chartMap_restrict]
    linear_combination hl - hk - hcoc
  -- glue
  obtain ⟨s, -, -⟩ := (isSheaf_extensionPresheaf f p i g₀).isSheafUniqueGluing_types
    (U := U) (fun k ↦ e' k) fun k l ↦ hcompat k l
  let s' : Extension f p i g₀ ⊤ := Extension.restrict hcov.ge s
  exact ⟨s'.toHom, s'.toHom_comp, s'.comp_toHom⟩

end SGA.SGA1.ExposeIII
