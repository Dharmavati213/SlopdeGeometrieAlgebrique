/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.DerivationSheaf
import SGA.Foundations.Cohomology.CechLocalization
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# SGA 1, Exposé III, 5.5: global extensions over affine schemes

Let `f : X → Y` be smooth, `Y'` affine over `Y` and `Y'₀ ⊆ Y'` a closed subscheme defined by a
nilpotent ideal. SGA 1 III.5.5 shows that every `Y`-morphism `g₀ : Y'₀ → X` extends to a
`Y`-morphism `Y' → X`: the extensions form a torsor under the quasi-coherent sheaf
`𝒢 = ℋom(g₀^* Ω_{X/Y}, 𝒥)` (III.5.1–5.2), which is locally trivial by III.3.1, and
`H¹(Y', 𝒢) = 0` since `Y'` is affine.

We follow this argument with Čech cohomology for a finite cover of `Y'` by basic opens `D(fₖ)`:

* `exists_section_of_isSqZeroOn`: the square-zero case, for sections of a smooth morphism
  `f : X → T` over an affine `T`. Local extensions `eₖ` exist on basic opens `D(fₖ)` covering `T`
  (III.3.1, `exists_extension_of_affineOpens`); their differences form a Čech `1`-cocycle of the
  presheaf `𝒢` (`derivationPresheaf`), which is exact in positive degrees for standard covers
  because `𝒢` is quasi-coherent (`ChartDerivation.isLocalizedModule_res`,
  `TopCat.Presheaf.cechComplex_exactAt_of_isLocalizedModule`); correcting the `eₖ` by a `0`-cochain
  makes them agree on overlaps, and they glue (III.5.1, `isSheaf_extensionPresheaf`).
* `exists_extension_of_isSqZeroOn`: the general square-zero case, by base change to `Y'`.
* `exists_extension_of_isNilpotent` and `globalExtensionStatement`: III.5.5, by induction on the
  nilpotency index, through the thickenings `Spec(R/Iᵏ)`.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TopCat.Presheaf (cechOpen cechOpen_le cechOpen_cons_le CechCochain cechD cechD_apply resₗ)

namespace SGA.SGA1.ExposeIII

lemma iInf_basicOpen_eq_basicOpen_prod {Y : Scheme.{u}} {V : Y.Opens} {m : ℕ}
    (g : Fin (m + 1) → Γ(Y, V)) : ⨅ a, Y.basicOpen (g a) = Y.basicOpen (∏ a, g a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : ⨅ a, Y.basicOpen (g a) =
        Y.basicOpen (g 0) ⊓ ⨅ a : Fin (m + 1), Y.basicOpen (g a.succ) :=
      le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun a ↦ iInf_le _ a.succ))
        (le_iInf fun a ↦ Fin.cases inf_le_left (fun b ↦ inf_le_right.trans (iInf_le _ b)) a)
    rw [h, ih, ← Scheme.basicOpen_mul, ← Fin.prod_univ_succ]

variable {X T T₀ : Scheme.{u}} (f : X ⟶ T) (i : T₀ ⟶ T) (g₀ : T₀ ⟶ X)

/-- III.5.5, square-zero case, for sections: let `f : X → T` be smooth with `T` affine, and
`i : T₀ → T` a surjective closed immersion whose ideal has square zero. Every section `g₀` of `f`
over `T₀` extends to a section of `f` over `T`. -/
theorem exists_section_of_isSqZeroOn [IsAffine T] [Smooth f] [Surjective i] [IsClosedImmersion i]
    (hsq : IsSqZeroOn i) (hg₀ : g₀ ≫ f = i) : ∃ s : T ⟶ X, s ≫ f = 𝟙 T ∧ i ≫ s = g₀ := by
  classical
  have hg₀' : g₀ ≫ f = i ≫ 𝟙 T := by rw [Category.comp_id, hg₀]
  -- basic opens carrying a chart
  let S : Set Γ(T, ⊤) := {r | ∃ V : X.Opens, IsAffineOpen V ∧ i ⁻¹ᵁ T.basicOpen r ≤ g₀ ⁻¹ᵁ V}
  have hS : ⨆ r : S, T.basicOpen (r : Γ(T, ⊤)) = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨w, hw⟩ := i.surjective x
    obtain ⟨_, ⟨V, hV, rfl⟩, hwV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (g₀ w)) isOpen_univ
    obtain ⟨r, hxr, -, hrV⟩ := exists_basicOpen_preimage_le (i := i) (g₀ := g₀) (U := ⊤)
      (V := V) trivial fun w' hw' ↦ by rwa [i.isClosedEmbedding.injective (hw'.trans hw.symm)]
    exact Opens.mem_iSup.mpr ⟨⟨r, V, hV, hrV⟩, hxr⟩
  have hspan : Ideal.span S = ⊤ := (isAffineOpen_top T).iSup_basicOpen_eq_self_iff.mp hS
  obtain ⟨t, htS, ht⟩ := Submodule.mem_span_finite_of_mem_span
    (show (1 : Γ(T, ⊤)) ∈ Submodule.span Γ(T, ⊤) S by
      change (1 : Γ(T, ⊤)) ∈ Ideal.span S
      rw [hspan]
      exact Submodule.mem_top)
  -- a finite standard cover with charts and local extensions
  let n := t.card
  let fk : Fin n → Γ(T, ⊤) := fun k ↦ (t.equivFin.symm k).1
  have hfk (k : Fin n) : fk k ∈ S := htS (t.equivFin.symm k).2
  have hrange : Set.range fk = t := by
    ext x
    refine ⟨?_, fun hx ↦ ⟨t.equivFin ⟨x, hx⟩, by simp [fk]⟩⟩
    rintro ⟨k, rfl⟩
    exact (t.equivFin.symm k).2
  have hspan' : Ideal.span (Set.range fk) = ⊤ := by
    rw [hrange, Ideal.eq_top_iff_one]
    exact ht
  choose V hV hle using hfk
  let U : Fin n → T.Opens := fun k ↦ T.basicOpen (fk k)
  let c (k : Fin n) : ExtensionChart i g₀ :=
    ⟨V k, U k, hV k, (isAffineOpen_top T).basicOpen (fk k), hle k⟩
  have hext (k : Fin n) := exists_extension_of_affineOpens f (𝟙 T) i i.surjective g₀ hg₀'
    (isAffineOpen_top T) (hV k) ((isAffineOpen_top T).basicOpen (fk k)) (by simp) (by simp)
    (hle k)
  choose eh he₁ he₂ using hext
  let e (k : Fin n) : Extension f (𝟙 T) i g₀ (U k) := ⟨eh k, he₁ k, he₂ k⟩
  -- the Čech opens are basic opens, hence affine
  have hcech {m : ℕ} (y : Fin (m + 1) → Fin n) : cechOpen U y = T.basicOpen (∏ a, fk (y a)) :=
    iInf_basicOpen_eq_basicOpen_prod (fun a ↦ fk (y a))
  have hWy {m : ℕ} (y : Fin (m + 1) → Fin n) : IsAffineOpen (cechOpen U y) := by
    rw [hcech]; exact (isAffineOpen_top T).basicOpen _
  let cy {m : ℕ} (y : Fin (m + 1) → Fin n) : ExtensionChart i g₀ :=
    ⟨V (y 0), cechOpen U y, hV (y 0), hWy y,
      (i.preimage_mono (cechOpen_le U y 0)).trans (hle (y 0))⟩
  -- the Čech complex of `𝒢` for the cover is exact in positive degrees
  let P := derivationPresheaf f i g₀
  have hlin := derivationPresheaf_map_smul f i g₀
  have hloc {m : ℕ} (k : Fin n) (y : Fin (m + 1) → Fin n) :
      IsLocalizedModule.Away (fk k) (resₗ P hlin (cechOpen_cons_le U k y)) := by
    have hcons : cechOpen U (Fin.cons k y : Fin (m + 2) → Fin n) =
        T.basicOpen (resTop (cechOpen U y) (fk k)) := by
      rw [resTop, Scheme.basicOpen_res, hcech, hcech, Fin.prod_univ_succ, Fin.cons_zero,
        Scheme.basicOpen_mul, inf_comm]
      simp only [Fin.cons_succ]
    refine ChartDerivation.isLocalizedModule_res hsq (cy y)
      ((e (y 0)).restrict (cechOpen_le U y 0)) (hWy (Fin.cons k y)) (cechOpen_cons_le U k y)
      (fk k) ((hWy y).isLocalization_of_eq_basicOpen _ _ hcons)
      (((hWy y).preimage i).isLocalization_of_eq_basicOpen _ _ ?_) _ fun _ ↦ rfl
    rw [hcons, Scheme.preimage_basicOpen, Scheme.Hom.app_eq_appLE]
    rfl
  have hexact := TopCat.Presheaf.cechComplex_exactAt_of_isLocalizedModule hlin U fk 1
    (by rw [hspan']; exact Ideal.le_radical Submodule.mem_top)
    (fun x ↦ by rw [map_one]; exact isUnit_one) hloc 0
  rw [TopCat.Presheaf.cechComplex_exactAt_succ_iff] at hexact
  -- the cocycle of differences of the local extensions
  let c₁ : CechCochain U P 1 := fun x ↦ ChartDerivation.diff hsq
    ((e (x 0)).restrict (cechOpen_le U x 0)) ((e (x 1)).restrict (cechOpen_le U x 1))
  have hc₁ : cechD U P 1 c₁ = 0 := by
    funext x
    refine ChartDerivation.ext fun c' hc' a ↦ ?_
    let E (j : Fin (1 + 1 + 1)) : Γ(T, c'.W) :=
      (e (x j)).chartMap c' (hc'.trans (cechOpen_le U x j)) a
    have hA (l : Fin (1 + 1 + 1)) (h : cechOpen U x ≤ cechOpen U (x ∘ Fin.succAbove l)) :
        derivationPresheafEval c' hc' a (P.map (homOfLE h).op (c₁ (x ∘ Fin.succAbove l))) =
          E (Fin.succAbove l 1) - E (Fin.succAbove l 0) := by
      change ((e _).restrict _).chartMap c' _ a - ((e _).restrict _).chartMap c' _ a = _
      rw [Extension.chartMap_restrict, Extension.chartMap_restrict]
      rfl
    change derivationPresheafEval c' hc' a (cechD U P 1 c₁ x) = 0
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
  let bk (k : Fin n) : ChartDerivation f i g₀ (U k) := ChartDerivation.res (hbk k) (b fun _ ↦ k)
  let e' (k : Fin n) : Extension f (𝟙 T) i g₀ (U k) :=
    (e k).ofChartDer hsq ((-bk k).app (c k) le_rfl) ((-bk k).isChartDer (c k) le_rfl)
  have hdiff (k : Fin n) : ChartDerivation.diff hsq (e k) (e' k) = -bk k :=
    ChartDerivation.diff_ofChartDer hsq (c := c k) (e k) (-bk k)
  have hE {k k' : Fin n} (hk : k = k') (c' : ExtensionChart i g₀) (h : c'.W ≤ U k)
      (h' : c'.W ≤ U k') (a : Γ(X, c'.V)) : (e k).chartMap c' h a = (e k').chartMap c' h' a := by
    subst hk; rfl
  have hcompat (k l : Fin n) :
      (e' k).restrict (inf_le_left : U k ⊓ U l ≤ U k) = (e' l).restrict inf_le_right := by
    rw [← ChartDerivation.diff_eq_zero_iff hsq]
    refine ChartDerivation.ext fun c' hc' a ↦ ?_
    have hkl : c'.W ≤ cechOpen U ![k, l] :=
      hc'.trans (le_iInf fun j ↦ Fin.cases inf_le_left (fun j ↦ Fin.cases inf_le_right
        (fun j ↦ j.elim0) j) j)
    have hB (z : Fin 1 → Fin n) (k' : Fin n) (hz : z = fun _ ↦ k') (hk' : c'.W ≤ U k')
        (h : cechOpen U ![k, l] ≤ cechOpen U z) :
        derivationPresheafEval c' hkl a (P.map (homOfLE h).op (b z)) =
          (bk k').app c' hk' a := by
      subst hz; rfl
    have hcoc := congrArg (derivationPresheafEval c' hkl a) (congrFun hb ![k, l])
    rw [cechD_apply, map_sum, Fin.sum_univ_two] at hcoc
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, map_neg] at hcoc
    rw [hB (![k, l] ∘ Fin.succAbove 0) l (by funext j; fin_cases j; rfl) (hc'.trans inf_le_right),
      hB (![k, l] ∘ Fin.succAbove 1) k (by funext j; fin_cases j; rfl)
        (hc'.trans inf_le_left)] at hcoc
    have hc1 : derivationPresheafEval c' hkl a (c₁ ![k, l]) =
        (e l).chartMap c' (hc'.trans inf_le_right) a -
          (e k).chartMap c' (hc'.trans inf_le_left) a := by
      change ((e _).restrict _).chartMap c' _ a - ((e _).restrict _).chartMap c' _ a = _
      rw [Extension.chartMap_restrict, Extension.chartMap_restrict,
        hE (show ![k, l] 1 = l by simp), hE (show ![k, l] 0 = k by simp)]
    rw [hc1] at hcoc
    have hk := congrArg (ChartDerivation.appAddHom c' (hc'.trans inf_le_left) a) (hdiff k)
    have hl := congrArg (ChartDerivation.appAddHom c' (hc'.trans inf_le_right) a) (hdiff l)
    simp only [ChartDerivation.appAddHom_apply, ChartDerivation.diff_app,
      ChartDerivation.neg_app] at hk hl
    simp only [ChartDerivation.diff_app, ChartDerivation.zero_app, Extension.chartMap_restrict]
    linear_combination hl - hk - hcoc
  -- glue
  obtain ⟨s, -, -⟩ := (isSheaf_extensionPresheaf f (𝟙 T) i g₀).isSheafUniqueGluing_types
    (U := U) (fun k ↦ e' k) fun k l ↦ hcompat k l
  have hsup : (⊤ : T.Opens) ≤ ⨆ k, U k := by
    intro x _
    have := (isAffineOpen_top T).iSup_basicOpen_eq_self_iff.mpr hspan'
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      Opens.mem_iSup.mp (this.symm ▸ (show x ∈ (⊤ : T.Opens) from trivial))
    exact Opens.mem_iSup.mpr ⟨k, hk⟩
  let s' : Extension f (𝟙 T) i g₀ ⊤ := Extension.restrict hsup s
  exact ⟨s'.toHom, s'.toHom_comp, s'.comp_toHom⟩

/-- III.5.5, square-zero case: let `f : X → Y` be smooth, `Y'` an affine `Y`-scheme and
`i : Y'₀ → Y'` a surjective closed immersion whose ideal has square zero. Every `Y`-morphism
`g₀ : Y'₀ → X` extends to a `Y`-morphism `Y' → X`. -/
theorem exists_extension_of_isSqZeroOn {Y Y' Y'₀ : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (p : Y' ⟶ Y) [IsAffine Y'] (i : Y'₀ ⟶ Y') [Surjective i] [IsClosedImmersion i]
    (hsq : IsSqZeroOn i) (g₀ : Y'₀ ⟶ X) (hg₀ : g₀ ≫ f = i ≫ p) :
    ∃ g : Y' ⟶ X, g ≫ f = p ∧ i ≫ g = g₀ := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_section_of_isSqZeroOn (pullback.snd f p) i
    (pullback.lift g₀ i hg₀) hsq (pullback.lift_snd _ _ _)
  refine ⟨s ≫ pullback.fst f p, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs₁, Category.id_comp]
  · rw [← Category.assoc, hs₂, pullback.lift_fst]

/-- The ideal of a closed immersion into an affine scheme has square zero on all affine opens as
soon as its ideal of global sections has square zero. -/
lemma isSqZeroOn_of_ker_appTop_sq [IsAffine T] [IsClosedImmersion i]
    (h : RingHom.ker i.appTop.hom ^ 2 = ⊥) : IsSqZeroOn i := by
  have hk : i.ker ^ 2 = ⊥ := Scheme.IdealSheafData.ext_of_isAffine (by
    rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply]
    exact h)
  intro W hW x hx y hy
  have hmem : x * y ∈ (i.ker ^ 2).ideal ⟨W, hW⟩ := by
    rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply, pow_two]
    refine Ideal.mul_mem_mul ?_ ?_
    · rwa [Scheme.Hom.app_eq_appLE]
    · rwa [Scheme.Hom.app_eq_appLE]
  rw [hk] at hmem
  exact hmem

lemma ker_appTop_SpecMap_sq {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (h : RingHom.ker φ.hom ^ 2 = ⊥) : RingHom.ker (Spec.map φ).appTop.hom ^ 2 = ⊥ := by
  have key (x : Γ(Spec R, ⊤)) : x ∈ RingHom.ker (Spec.map φ).appTop.hom ↔
      (Scheme.ΓSpecIso R).hom x ∈ RingHom.ker φ.hom := by
    rw [RingHom.mem_ker, RingHom.mem_ker,
      ← map_eq_zero_iff _ (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv.injective]
    change (Scheme.ΓSpecIso S).hom ((Spec.map φ).appTop x) = 0 ↔ _
    rw [← ConcreteCategory.comp_apply, Scheme.ΓSpecIso_naturality, ConcreteCategory.comp_apply]
  rw [eq_bot_iff, pow_two, Ideal.mul_le]
  intro x hx y hy
  rw [Ideal.mem_bot]
  have : (Scheme.ΓSpecIso R).hom (x * y) ∈ RingHom.ker φ.hom ^ 2 := by
    rw [map_mul, pow_two]
    exact Ideal.mul_mem_mul ((key x).mp hx) ((key y).mp hy)
  rw [h, Ideal.mem_bot] at this
  exact (map_eq_zero_iff _ (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective).mp this

lemma surjective_SpecMap_quotient {R : CommRingCat.{u}} (J : Ideal R) (hJ : J ^ 2 = ⊥) :
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
  refine ⟨fun x ↦ ?_⟩
  have hx : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    let y : PrimeSpectrum R := x
    have := y.isPrime
    change (J : Set R) ⊆ y.asIdeal
    exact Ideal.IsPrime.le_of_pow_le (P := y.asIdeal) (n := 2) (hJ.trans_le bot_le)
  exact hx

/-- III.5.5 for `Spec R ⊇ Spec (R/I)` with `I` nilpotent, by induction on the nilpotency index
using the thickenings `Spec (R/Iᵏ)`. -/
theorem exists_extension_SpecMap_quotient (n : ℕ) : ∀ {R : CommRingCat.{u}} (I : Ideal R),
    I ^ (n + 1) = ⊥ → ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (p : Spec R ⟶ Y)
      (g₀ : Spec (.of (R ⧸ I)) ⟶ X),
      g₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ p →
        ∃ g : Spec R ⟶ X, g ≫ f = p ∧
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g = g₀ := by
  induction n with
  | zero =>
    intro R I hI X Y f _ p g₀ hg₀
    have hI2 : I ^ 2 = ⊥ := eq_bot_iff.mpr ((Ideal.pow_le_pow_right (by norm_num)).trans hI.le)
    have := surjective_SpecMap_quotient I hI2
    refine exists_extension_of_isSqZeroOn f p _ ?_ g₀ hg₀
    refine isSqZeroOn_of_ker_appTop_sq _ (ker_appTop_SpecMap_sq _ ?_)
    rwa [CommRingCat.hom_ofHom, Ideal.mk_ker]
  | succ n ih =>
    intro R I hI X Y f _ p g₀ hg₀
    set J := I ^ (n + 1) with hJ
    have hJI : J ≤ I := Ideal.pow_le_self (Nat.succ_ne_zero n)
    have hJ2 : J ^ 2 = ⊥ := by
      rw [hJ, ← pow_mul, eq_bot_iff, ← hI]
      exact Ideal.pow_le_pow_right (by omega)
    let R' : CommRingCat.{u} := .of (R ⧸ J)
    let I' : Ideal R' := I.map (Ideal.Quotient.mk J)
    have hI' : I' ^ (n + 1) = ⊥ := by
      rw [← Ideal.map_pow, ← hJ, Ideal.map_quotient_self]
    let e : R ⧸ I ≃+* R' ⧸ I' := (DoubleQuot.quotQuotEquivQuotOfLE hJI).symm
    have he : CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom (Ideal.Quotient.mk I') =
        CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ CommRingCat.ofHom e.toRingHom := by
      ext x
      rfl
    have hSpec : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I')) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, he]
    obtain ⟨h, hh₁, hh₂⟩ := ih (R := R') I' hI' f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ p)
      (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ g₀) (by
        rw [Category.assoc, hg₀, ← Category.assoc, ← hSpec, Category.assoc])
    have := surjective_SpecMap_quotient J hJ2
    obtain ⟨g, hg₁, hg₂⟩ := exists_extension_of_isSqZeroOn f p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      (isSqZeroOn_of_ker_appTop_sq _ (ker_appTop_SpecMap_sq _ (by
        rwa [CommRingCat.hom_ofHom, Ideal.mk_ker]))) h hh₁
    refine ⟨g, hg₁, ?_⟩
    have : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
      inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom e.toRingHom)), ← Category.assoc, ← hSpec,
      Category.assoc, hg₂, hh₂]

/-- III.5.5: let `f : X → Y` be smooth, `Y'` an affine `Y`-scheme and `Y'₀ ⊆ Y'` a closed
subscheme defined by a nilpotent ideal. Every `Y`-morphism `g₀ : Y'₀ → X` extends to a
`Y`-morphism `Y' → X`. -/
theorem exists_extension_of_isNilpotent {Y Y' Y'₀ : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (p : Y' ⟶ Y) [IsAffine Y'] (i : Y'₀ ⟶ Y') [IsClosedImmersion i] (hi : IsNilpotent i.ker)
    (g₀ : Y'₀ ⟶ X) (hg₀ : g₀ ≫ f = i ≫ p) : ∃ g : Y' ⟶ X, g ≫ f = p ∧ i ≫ g = g₀ := by
  obtain ⟨hY'₀, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine i
  set I := RingHom.ker i.appTop.hom
  obtain ⟨m, hm⟩ := hi
  have hI : I ^ (m + 1) = ⊥ := by
    have h := congrArg (fun K : Y'.IdealSheafData ↦ K.ideal ⟨⊤, isAffineOpen_top Y'⟩) hm
    simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply] at h
    have h' : I ^ m = ⊥ := h
    rw [eq_bot_iff]
    exact (Ideal.pow_le_pow_right (Nat.le_succ m)).trans h'.le
  let e : Γ(Y', ⊤) ⧸ I ≃+* Γ(Y'₀, ⊤) := RingHom.quotientKerEquivOfSurjective hsurj
  let a : Y'₀ ⟶ Spec (.of (Γ(Y', ⊤) ⧸ I)) :=
    Y'₀.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom e.toRingHom)
  have : IsIso a := by
    have : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
      inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
    infer_instance
  have hia : i = a ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ Y'.isoSpec.inv := by
    have : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ CommRingCat.ofHom e.toRingHom =
        i.appTop := by
      ext x
      exact RingHom.quotientKerEquivOfSurjective_apply_mk hsurj x
    rw [Category.assoc, ← Spec.map_comp_assoc, this, Scheme.isoSpec_inv_naturality,
      Iso.hom_inv_id_assoc]
  obtain ⟨G, hG₁, hG₂⟩ := exists_extension_SpecMap_quotient m I hI f (Y'.isoSpec.inv ≫ p)
    (inv a ≫ g₀) (by
      rw [Category.assoc, hg₀, hia]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc])
  refine ⟨Y'.isoSpec.hom ≫ G, by rw [Category.assoc, hG₁, Iso.hom_inv_id_assoc], ?_⟩
  rw [hia]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hG₂, IsIso.hom_inv_id_assoc]

/-- III.5.5: `GlobalExtensionStatement` holds. -/
theorem globalExtensionStatement : GlobalExtensionStatement.{u} :=
  fun _ _ _ _ f _ p _ i _ hi g₀ hg₀ ↦ exists_extension_of_isNilpotent f p i hi g₀ hg₀

end SGA.SGA1.ExposeIII
