/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Cartan
import SGA.Foundations.Cohomology.CechLocalization
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# Serre's vanishing theorem on affine schemes

For any commutative ring `R` and any quasi-coherent `𝒪_{Spec R}`-module `M` (equivalently
`M = Ñ` for an `R`-module `N`), `Hⁿ(D(g), M) = 0` for all `n > 0` and `g ∈ R`; in particular
`Hⁿ(Spec R, M) = 0` for `n > 0` (Serre; EGA III 1.3.1; Stacks Project, Tag 01XB; Hartshorne
III.3.5 for noetherian `R`). No noetherian hypothesis is needed. The version for affine opens of
arbitrary schemes is in `SGA.Foundations.Cohomology.AffineOpenVanishing`.

The proof is Cartan's criterion (`TopCat.Sheaf.H'_subsingleton_of_cech`) applied to the basis of
standard opens `D(g)` and the finite covers of a standard open by standard opens, whose Čech
complexes are exact by `TopCat.Presheaf.cechComplex_exactAt_of_isLocalizedModule`, since the
sections of a quasi-coherent module over `D(a)` form the localization `M_a`.

## Main results

* `IsLocalizedModule.Away.of_comp`: if `M → M₁` is a localization at `a` and `M → M₂` one at
  `a b`, then a compatible `M₁ → M₂` is a localization at `b`.
* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_res_basicOpen`: for a quasi-coherent `M`
  on `Spec R`, the restriction `Γ(M, D(a)) → Γ(M, D(a b))` is a localization at `b`.
* `AlgebraicGeometry.Scheme.Modules.H'_basicOpen_subsingleton`,
  `AlgebraicGeometry.Scheme.Modules.H_subsingleton_of_isQuasicoherent`: Serre's vanishing.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite Abelian TopCat.Presheaf

section Algebra

variable {R : Type*} [CommRing R] {M M₁ M₂ : Type*} [AddCommGroup M] [AddCommGroup M₁]
  [AddCommGroup M₂] [Module R M] [Module R M₁] [Module R M₂]

/-- If `f₁ : M → M₁` is a localization at `a` and `f₂ : M → M₂` is a localization at `a * b`,
then any `β : M₁ → M₂` with `β ∘ f₁ = f₂` is a localization at `b`: `(M_a)_b = M_{ab}`. -/
lemma IsLocalizedModule.Away.of_comp (a b : R) (f₁ : M →ₗ[R] M₁) (f₂ : M →ₗ[R] M₂)
    (β : M₁ →ₗ[R] M₂) (hβ : ∀ m, β (f₁ m) = f₂ m) [IsLocalizedModule.Away a f₁]
    [IsLocalizedModule.Away (a * b) f₂] : IsLocalizedModule.Away b β := by
  have hab := IsLocalizedModule.Away.isUnit_algebraMap f₂ (a * b)
  rw [map_mul, ((Commute.all a b).map (algebraMap R (Module.End R M₂))).isUnit_mul_iff] at hab
  have ha₁ := IsLocalizedModule.Away.isUnit_algebraMap f₁ a
  -- powers of `a` act bijectively on `M₁` and on `M₂`
  have hbij₁ (n : ℕ) : Function.Bijective fun x : M₁ ↦ a ^ n • x := by
    have := ha₁.pow n
    rwa [← map_pow, Module.End.isUnit_iff] at this
  have hinj₂ (n : ℕ) : Function.Injective fun x : M₂ ↦ a ^ n • x := by
    have := hab.1.pow n
    rw [← map_pow, Module.End.isUnit_iff] at this
    exact this.1
  refine IsLocalizedModule.Away.mk_of_addCommGroup hab.2 (fun z ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨n, m, hm⟩ := IsLocalizedModule.Away.surj f₂ (a * b) z
    obtain ⟨y, hy⟩ := (hbij₁ n).2 (f₁ m)
    have hy' : a ^ n • y = f₁ m := hy
    refine ⟨n, y, hinj₂ n ?_⟩
    simp only
    rw [← LinearMap.map_smul, hy', hβ, ← hm, mul_pow, mul_smul]
  · obtain ⟨k, m, hm⟩ := IsLocalizedModule.Away.surj f₁ a x
    have h0 : f₂ m = f₂ 0 := by rw [← hβ, ← hm, LinearMap.map_smul, hx, smul_zero, map_zero]
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (a * b) h0
    rw [smul_zero] at hn
    refine ⟨n, (hbij₁ (n + k)).1 ?_⟩
    simp only [smul_zero]
    rw [pow_add, mul_smul, smul_comm (a ^ k), ← smul_assoc, smul_eq_mul, ← mul_pow, hm,
      ← LinearMap.map_smul, hn, map_zero]

end Algebra

namespace PrimeSpectrum

variable {R : Type*} [CommRing R]

lemma mem_radical_span_of_basicOpen_le_iSup {ι : Type*} (f : ι → R) (g : R)
    (h : basicOpen g ≤ ⨆ i, basicOpen (f i)) : g ∈ (Ideal.span (Set.range f)).radical := by
  have hsub : zeroLocus (Ideal.span (Set.range f) : Set R) ⊆
      zeroLocus ((Ideal.span {g} : Ideal R) : Set R) := by
    intro p hp
    rw [zeroLocus_span] at hp ⊢
    by_contra hg
    have hpg : p ∈ basicOpen g := by
      rw [mem_basicOpen]
      exact fun hmem ↦ hg (Set.singleton_subset_iff.mpr hmem)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (h hpg)
    exact (mem_basicOpen _ _).mp hi (hp ⟨i, rfl⟩)
  exact (zeroLocus_subset_zeroLocus_iff _ _).mp hsub (Ideal.mem_span_singleton_self g)

lemma iInf_basicOpen {n : ℕ} (f : Fin n → R) :
    ⨅ a, basicOpen (f a) = basicOpen (∏ a, f a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : ⨅ a, basicOpen (f a) = basicOpen (f 0) ⊓ ⨅ a : Fin n, basicOpen (f a.succ) :=
      le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun a ↦ iInf_le _ a.succ))
        (le_iInf fun a ↦ Fin.cases inf_le_left (fun b ↦ inf_le_right.trans (iInf_le _ b)) a)
    rw [h, ih, Fin.prod_univ_succ, basicOpen_mul]

end PrimeSpectrum

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

/-- The standard open `D(a)`, as an open of the scheme `Spec R`. -/
abbrev basicOpen' (a : R) : (Spec R).Opens := PrimeSpectrum.basicOpen a

lemma map_smul_Spec' ⦃V W : (Spec R).Opens⦄ (h : W ≤ V) (r : R) (s : Γ(M, V)) :
    M.presheaf.map (homOfLE h).op (r • s) = r • M.presheaf.map (homOfLE h).op s :=
  map_smul_Spec _ r s

/-- For a quasi-coherent module on `Spec R`, the restriction `Γ(M, D(a)) → Γ(M, D(ab))` is a
localization at `b` (EGA I 1.3.7: `Γ(D(a), Ñ) = N_a`). -/
lemma isLocalizedModule_res_basicOpen [M.IsQuasicoherent] (a b : R)
    (h : basicOpen' (a * b) ≤ basicOpen' a) :
    IsLocalizedModule.Away b (resₗ M.presheaf (map_smul_Spec' M) h) := by
  have hM : IsLocalizing (modulesSpecToSheaf.obj M) :=
    (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  have h₁ : IsLocalizedModule.Away a
      (resₗ M.presheaf (map_smul_Spec' M) (le_top : basicOpen' a ≤ ⊤)) := hM a
  have h₂ : IsLocalizedModule.Away (a * b)
      (resₗ M.presheaf (map_smul_Spec' M) (le_top : basicOpen' (a * b) ≤ ⊤)) := hM (a * b)
  exact IsLocalizedModule.Away.of_comp a b
    (resₗ M.presheaf (map_smul_Spec' M) (le_top : basicOpen' a ≤ ⊤))
    (resₗ M.presheaf (map_smul_Spec' M) (le_top : basicOpen' (a * b) ≤ ⊤)) _
    fun m ↦ map_map_apply M.presheaf _ _ m

lemma isLocalizedModule_res_of_eq [M.IsQuasicoherent] {W W' : (Spec R).Opens} (a b : R)
    (hW : W = basicOpen' a) (hW' : W' = basicOpen' (a * b)) (h : W' ≤ W) :
    IsLocalizedModule.Away b (resₗ M.presheaf (map_smul_Spec' M) h) := by
  subst hW hW'
  exact isLocalizedModule_res_basicOpen M a b h

lemma cechOpen_basicOpen' {n m : ℕ} (f : Fin n → R) (y : Fin m → Fin n) :
    cechOpen (fun i ↦ basicOpen' (f i)) y = basicOpen' (∏ a, f (y a)) :=
  PrimeSpectrum.iInf_basicOpen (fun a ↦ f (y a))

lemma cechOpen_cons_basicOpen' {n m : ℕ} (f : Fin n → R) (k : Fin n) (y : Fin m → Fin n) :
    cechOpen (fun i ↦ basicOpen' (f i)) (Fin.cons k y : Fin (m + 1) → Fin n) =
      basicOpen' ((∏ a, f (y a)) * f k) := by
  rw [cechOpen_basicOpen', Fin.prod_univ_succ, mul_comm]
  rfl

variable (R) in
/-- Finite families of standard opens of `Spec R` whose union is a standard open. -/
def IsStandardCover ⦃n : ℕ⦄ (U : Fin n → (Spec R).Opens) : Prop :=
  ∃ (f : Fin n → R) (g : R), (∀ i, U i = basicOpen' (f i)) ∧ ⨆ i, U i = basicOpen' g

/-- The Čech complex of a quasi-coherent module on `Spec R` for a finite cover of a standard open
by standard opens is exact in positive degrees (Stacks Tag 01X9). -/
theorem cechComplex_exactAt_of_isStandardCover [M.IsQuasicoherent] {n : ℕ}
    {U : Fin n → (Spec R).Opens} (hU : IsStandardCover R U) (p : ℕ) :
    (cechComplex U M.presheaf).ExactAt (p + 1) := by
  obtain ⟨f, g, hUf, hsup⟩ := hU
  obtain rfl : U = fun i ↦ basicOpen' (f i) := funext hUf
  refine cechComplex_exactAt_of_isLocalizedModule (map_smul_Spec' M) _ f g
    (PrimeSpectrum.mem_radical_span_of_basicOpen_le_iSup f g hsup.ge) (fun x ↦ ?_)
    (fun k y ↦ ?_) p
  · exact isUnit_algebraMap_end_of_le_basicOpen g
      (((cechOpen_le _ x 0).trans (le_iSup (fun i ↦ basicOpen' (f i)) _)).trans hsup.le)
  · exact isLocalizedModule_res_of_eq M _ (f k) (cechOpen_basicOpen' f y)
      (cechOpen_cons_basicOpen' f k y) _

variable (R) in
/-- Every open cover of a standard open `D(g)` is refined by a finite cover of `D(g)` by standard
opens. -/
lemma exists_isStandardCover_refinement (V : (Spec R).Opens)
    (hV : V ∈ Set.range (basicOpen' (R := R)))
    (W : V → (Spec R).Opens) (hW : ∀ x, x.1 ∈ W x) :
    ∃ (n : ℕ) (U : Fin n → (Spec R).Opens), IsStandardCover R U ∧ ⨆ i, U i = V ∧
      ∀ i, ∃ x, U i ≤ W x := by
  obtain ⟨g, rfl⟩ := hV
  have hb (x : basicOpen' g) : ∃ h : R, x.1 ∈ basicOpen' h ∧ basicOpen' h ≤ W x ⊓ basicOpen' g := by
    obtain ⟨_, ⟨h, rfl⟩, hxh, hle⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (a := x.1) (⟨hW x, x.2⟩ : x.1 ∈ W x ⊓ basicOpen' g) (W x ⊓ basicOpen' g).2
    exact ⟨h, hxh, fun y hy ↦ hle hy⟩
  choose h hxh hle using hb
  obtain ⟨t, ht⟩ := (PrimeSpectrum.isCompact_basicOpen g).elim_finite_subcover
    (fun x : basicOpen' g ↦ (PrimeSpectrum.basicOpen (h x) : Set (PrimeSpectrum R)))
    (fun x ↦ (PrimeSpectrum.basicOpen (h x)).2)
    fun y hy ↦ Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxh ⟨y, hy⟩⟩
  let e := t.equivFin.symm
  have hsup : ⨆ i, basicOpen' (h (e i)) = basicOpen' g := by
    refine le_antisymm (iSup_le fun i ↦ (hle _).trans inf_le_right) fun y hy ↦ ?_
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht hy)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨e.symm ⟨x, hx⟩, ?_⟩
    simp only [Equiv.apply_symm_apply]
    exact hyx
  exact ⟨t.card, fun i ↦ basicOpen' (h (e i)), ⟨fun i ↦ h (e i), g, fun _ ↦ rfl, hsup⟩, hsup,
    fun i ↦ ⟨e i, (hle _).trans inf_le_left⟩⟩

/-- **Serre's vanishing theorem** (EGA III 1.3.1; Stacks Tag 01XB): for a quasi-coherent module
`M` on `Spec R` (any commutative ring `R`) and a standard open `D(g)`,
`Hⁿ(D(g), M) = 0` for all `n > 0`. -/
theorem H'_basicOpen_subsingleton [M.IsQuasicoherent] (g : R) (p : ℕ) :
    Subsingleton (((SheafOfModules.toSheaf _).obj M).H' (p + 1) (basicOpen' g)) := by
  have hCov : ∀ ⦃n⦄ (U : Fin n → (Spec R).Opens), IsStandardCover R U →
      ∀ ⦃p⦄ (x : Fin (p + 1) → Fin n), cechOpen U x ∈ Set.range (basicOpen' (R := R)) :=
    fun _ U ⟨f, _, hUf, _⟩ _ x ↦ ⟨∏ a, f (x a), by
      obtain rfl : U = fun i ↦ basicOpen' (f i) := funext hUf
      exact (cechOpen_basicOpen' f x).symm⟩
  have hF : TopCat.Sheaf.CechAcyclic (X := (Spec R).carrier) (IsStandardCover R)
      ((SheafOfModules.toSheaf _).obj M) :=
    fun _ _ hU p ↦ cechComplex_exactAt_of_isStandardCover M hU p
  exact TopCat.Sheaf.H'_subsingleton_of_cech (X := (Spec R).carrier) hCov
    (exists_isStandardCover_refinement R) p _ hF ⟨g, rfl⟩

/-- **Serre's vanishing theorem** (EGA III 1.3.1; Stacks Tag 01XB): the higher cohomology of a
quasi-coherent module on an affine scheme `Spec R` vanishes, for any commutative ring `R`. -/
theorem H_subsingleton_of_isQuasicoherent [M.IsQuasicoherent] (p : ℕ) :
    Subsingleton (Sheaf.H ((SheafOfModules.toSheaf _).obj M) (p + 1)) := by
  have := H'_basicOpen_subsingleton M 1 p
  rw [show basicOpen' (1 : R) = ⊤ from PrimeSpectrum.basicOpen_one] at this
  exact (Sheaf.H'.addEquivH isTerminalTop _ (p + 1)).symm.subsingleton

end AlgebraicGeometry.Scheme.Modules
