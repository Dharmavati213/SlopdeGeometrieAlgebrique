/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import SGA.Foundations.Cohomology.Helpers

/-!
# The norm of a finite locally free morphism

Let `f : X ⟶ Y` be finite, flat and locally of finite presentation (finite locally free). Over the
affine opens `V` of a basis of `Y`, `Γ(X, f⁻¹ V)` is a finite free `Γ(Y, V)`-algebra, and the norms
of these algebras glue to multiplicative maps `N_f : Γ(X, f⁻¹ W) → Γ(Y, W)` for all opens `W` of
`Y`, compatible with restrictions (EGA II 6.5). A point `y ∈ W` lies in the
non-vanishing locus of `N_f(u)` iff every point of `X` over `y` lies in that of `u`.

## Main definitions and results

- `Algebra.dvd_algebraMap_norm`: an element of a finite free algebra divides its norm.
- `Module.free_localizedModule_iff_free`: freeness of a localization of a module does not depend
  on the chosen localizations.
- `AlgebraicGeometry.Scheme.Hom.IsFreeOver`: the affine opens of `Y` over which `f` is finite and
  free; `Scheme.Hom.exists_isFreeOver`: they form a basis of `Y` if `f` is finite locally free.
- `AlgebraicGeometry.Scheme.Hom.norm`: the norm `N_f`, with `norm_mul`, `norm_one`, `norm_res`.
- `AlgebraicGeometry.Scheme.Hom.mem_basicOpen_norm_iff`: `N_f(u)(y) ≠ 0` iff `u(x) ≠ 0` for all
  `x` over `y`.
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
  [Module.Finite R S]

/-- An element `x` of a finite free `R`-algebra divides (the image of) its norm: by
Cayley–Hamilton, the constant term of the characteristic polynomial of `x`, which is `± N(x)`, is
a multiple of `x`. -/
theorem dvd_algebraMap_norm (x : S) : x ∣ algebraMap R S (Algebra.norm R x) := by
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := (Algebra.lmul R S x).charpoly)
  have h := congrArg (Polynomial.aeval x) hq
  rw [map_sub, Algebra.aeval_self_charpoly_lmul, Polynomial.aeval_C, map_mul,
    Polynomial.aeval_X, zero_sub] at h
  have hc : x ∣ algebraMap R S ((Algebra.lmul R S x).charpoly.coeff 0) :=
    ⟨-(Polynomial.aeval x q), by rw [mul_neg, ← h, neg_neg]⟩
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul]
  exact hc.mul_left _

end Algebra

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Freeness of a localization of a module does not depend on the chosen localizations: for any
localization `Mₜ` of `M` at a submonoid `T`, over a localization `Rₜ` of `R` at `T`, `Mₜ` is free
over `Rₜ` iff `T⁻¹ M` is free over `T⁻¹ R`. -/
theorem free_localizedModule_iff_free (T : Submonoid R) (Rₜ : Type*) {Mₜ : Type*} [CommRing Rₜ]
    [Algebra R Rₜ] [IsLocalization T Rₜ] [AddCommGroup Mₜ] [Module R Mₜ] (g : M →ₗ[R] Mₜ)
    [IsLocalizedModule T g] [Module Rₜ Mₜ] [IsScalarTower R Rₜ Mₜ] :
    Module.Free (Localization T) (LocalizedModule T M) ↔ Module.Free Rₜ Mₜ := by
  set e := (IsLocalization.algEquiv T (Localization T) Rₜ).toRingEquiv
  apply Module.Free.iff_of_equiv (σ := e)
  refine { __ := IsLocalizedModule.iso T g, map_smul' := ?_ }
  intro r x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq T r
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g s)).1
  simp [e, ← map_smul, ← smul_assoc]

end Module

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- An open subset `V` of `Y` over which `f` is finite and free: `V` is affine and `Γ(X, f⁻¹ V)`
is a finite free `Γ(Y, V)`-module, via `f`. -/
def IsFreeOver (V : Y.Opens) : Prop :=
  IsAffineOpen V ∧ (f.app V).hom.Finite ∧
    letI := (f.app V).hom.toAlgebra; Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V)

/-- The norm `Γ(X, f⁻¹ V) → Γ(Y, V)` of the `Γ(Y, V)`-algebra `Γ(X, f⁻¹ V)`; it is meaningful
when `f` is finite and free over `V`. -/
noncomputable def normApp (V : Y.Opens) : Γ(X, f ⁻¹ᵁ V) →* Γ(Y, V) :=
  letI := (f.app V).hom.toAlgebra; Algebra.norm Γ(Y, V)

variable {f}

/-- The non-vanishing locus of `N(u)` over a free open lies under that of `u`: `u` divides
`N(u)`. -/
lemma IsFreeOver.preimage_basicOpen_normApp_le {V : Y.Opens} (hV : f.IsFreeOver V)
    (u : Γ(X, f ⁻¹ᵁ V)) : f ⁻¹ᵁ Y.basicOpen (f.normApp V u) ≤ X.basicOpen u := by
  obtain ⟨-, hfin, hfree⟩ := hV
  let := (f.app V).hom.toAlgebra
  have : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hfin
  obtain ⟨c, hc⟩ := Algebra.dvd_algebraMap_norm (R := Γ(Y, V)) u
  rw [Scheme.preimage_basicOpen]
  change X.basicOpen (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V) (Algebra.norm Γ(Y, V) u)) ≤ _
  rw [hc, Scheme.basicOpen_mul]
  exact inf_le_left

set_option backward.isDefEq.respectTransparency false in
/-- Let `A = Γ(Y, W₀)` for an affine open `W₀`, `B = Γ(X, f⁻¹ W₀)` and `E = D(r) ⊆ W₀`. Then
`Γ(Y, E)` and `Γ(X, f⁻¹ E)` are the localizations of `A` and `B` away from `r`, with compatible
algebra structures. This packages the instances needed to compare norms and freeness. -/
lemma isLocalization_basicOpen [IsAffineHom f] {W₀ E : Y.Opens} (hW₀ : IsAffineOpen W₀)
    (r : Γ(Y, W₀)) (hEW : E ≤ W₀) (e : Y.basicOpen r = E) :
    letI := (f.app W₀).hom.toAlgebra
    letI : Algebra Γ(Y, W₀) Γ(Y, E) := (Y.presheaf.map (homOfLE hEW).op).hom.toAlgebra
    letI : Algebra Γ(X, f ⁻¹ᵁ W₀) Γ(X, f ⁻¹ᵁ E) :=
      (X.presheaf.map (homOfLE (f.preimage_mono hEW)).op).hom.toAlgebra
    letI : Algebra Γ(Y, E) Γ(X, f ⁻¹ᵁ E) := (f.app E).hom.toAlgebra
    letI : Algebra Γ(Y, W₀) Γ(X, f ⁻¹ᵁ E) :=
      (f.appLE W₀ (f ⁻¹ᵁ E) (f.preimage_mono hEW)).hom.toAlgebra
    IsLocalization (Submonoid.powers r) Γ(Y, E) ∧
      IsLocalization (Algebra.algebraMapSubmonoid Γ(X, f ⁻¹ᵁ W₀) (.powers r)) Γ(X, f ⁻¹ᵁ E) ∧
      IsScalarTower Γ(Y, W₀) Γ(Y, E) Γ(X, f ⁻¹ᵁ E) ∧
      IsScalarTower Γ(Y, W₀) Γ(X, f ⁻¹ᵁ W₀) Γ(X, f ⁻¹ᵁ E) := by
  let := (f.app W₀).hom.toAlgebra
  let : Algebra Γ(Y, W₀) Γ(Y, E) := (Y.presheaf.map (homOfLE hEW).op).hom.toAlgebra
  let : Algebra Γ(X, f ⁻¹ᵁ W₀) Γ(X, f ⁻¹ᵁ E) :=
    (X.presheaf.map (homOfLE (f.preimage_mono hEW)).op).hom.toAlgebra
  let : Algebra Γ(Y, E) Γ(X, f ⁻¹ᵁ E) := (f.app E).hom.toAlgebra
  let : Algebra Γ(Y, W₀) Γ(X, f ⁻¹ᵁ E) :=
    (f.appLE W₀ (f ⁻¹ᵁ E) (f.preimage_mono hEW)).hom.toAlgebra
  refine ⟨hW₀.isLocalization_of_eq_basicOpen r (homOfLE hEW) e.symm, ?_, ?_, ?_⟩
  · have h := (hW₀.preimage f).isLocalization_of_eq_basicOpen (f.app W₀ r)
      (homOfLE (f.preimage_mono hEW)) (by rw [← e, Scheme.preimage_basicOpen])
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact h
  · refine IsScalarTower.of_algebraMap_eq' ?_
    change (f.appLE W₀ (f ⁻¹ᵁ E) _).hom = (f.app E).hom.comp (Y.presheaf.map (homOfLE hEW).op).hom
    rw [← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
  · refine IsScalarTower.of_algebraMap_eq' ?_
    change (f.appLE W₀ (f ⁻¹ᵁ E) _).hom =
      (X.presheaf.map (homOfLE (f.preimage_mono hEW)).op).hom.comp (f.app W₀).hom
    rw [← CommRingCat.hom_comp, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

set_option backward.isDefEq.respectTransparency false in
/-- If `f` is finite and free over `V`, it is finite and free over every basic open `E = D(a)`
of `V`, and the norm over `E` is the restriction of the norm over `V`: the norm commutes with
localization. -/
lemma IsFreeOver.basicOpen [IsAffineHom f] {V E : Y.Opens} (hV : f.IsFreeOver V) (a : Γ(Y, V))
    (hEV : E ≤ V) (e : Y.basicOpen a = E) :
    f.IsFreeOver E ∧ ∀ u : Γ(X, f ⁻¹ᵁ V),
      f.normApp E (X.presheaf.map (homOfLE (f.preimage_mono hEV)).op u) =
        Y.presheaf.map (homOfLE hEV).op (f.normApp V u) := by
  obtain ⟨hVa, hfin, hfree⟩ := hV
  let := (f.app V).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(Y, E) := (Y.presheaf.map (homOfLE hEV).op).hom.toAlgebra
  let : Algebra Γ(X, f ⁻¹ᵁ V) Γ(X, f ⁻¹ᵁ E) :=
    (X.presheaf.map (homOfLE (f.preimage_mono hEV)).op).hom.toAlgebra
  let : Algebra Γ(Y, E) Γ(X, f ⁻¹ᵁ E) := (f.app E).hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ E) :=
    (f.appLE V (f ⁻¹ᵁ E) (f.preimage_mono hEV)).hom.toAlgebra
  obtain ⟨h₁, h₂, h₃, h₄⟩ := isLocalization_basicOpen (f := f) hVa a hEV e
  have : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hfin
  let b := (Module.Free.chooseBasis Γ(Y, V) Γ(X, f ⁻¹ᵁ V)).localizationLocalization Γ(Y, E)
    (.powers a) Γ(X, f ⁻¹ᵁ E)
  refine ⟨⟨e ▸ hVa.basicOpen a, Module.Finite.of_basis b, Module.Free.of_basis b⟩, fun u ↦ ?_⟩
  exact Algebra.norm_localization Γ(Y, V) (.powers a) u

/-- The norms over two opens over which `f` is finite and free agree on their intersection. -/
lemma IsFreeOver.normApp_compatible [IsAffineHom f] {V₁ V₂ : Y.Opens} (h₁ : f.IsFreeOver V₁)
    (h₂ : f.IsFreeOver V₂) (u₁ : Γ(X, f ⁻¹ᵁ V₁)) (u₂ : Γ(X, f ⁻¹ᵁ V₂))
    (hu : X.presheaf.map (homOfLE (f.preimage_mono (inf_le_left : V₁ ⊓ V₂ ≤ V₁))).op u₁ =
      X.presheaf.map (homOfLE (f.preimage_mono (inf_le_right : V₁ ⊓ V₂ ≤ V₂))).op u₂) :
    Y.presheaf.map (homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).op (f.normApp V₁ u₁) =
      Y.presheaf.map (homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).op (f.normApp V₂ u₂) := by
  choose a b hab hx using fun x : (V₁ ⊓ V₂ : Y.Opens) ↦
    exists_basicOpen_le_affine_inter h₁.1 h₂.1 x.1 x.2
  have hE₁ (x) : Y.basicOpen (a x) ≤ V₁ := Y.basicOpen_le _
  have hE₂ (x) : Y.basicOpen (a x) ≤ V₂ := (hab x).le.trans (Y.basicOpen_le _)
  refine TopCat.Sheaf.eq_of_locally_eq' Y.sheaf (fun x ↦ Y.basicOpen (a x)) (V₁ ⊓ V₂)
    (fun x ↦ homOfLE (le_inf (hE₁ x) (hE₂ x)))
    (fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hx ⟨y, hy⟩⟩) _ _ fun x ↦ ?_
  change Y.presheaf.map _ (Y.presheaf.map _ _) = Y.presheaf.map _ (Y.presheaf.map _ _)
  rw [CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_map,
    ← (h₁.basicOpen (a x) (hE₁ x) rfl).2, ← (h₂.basicOpen (b x) (hE₂ x) (hab x).symm).2]
  congr 1
  have := congrArg (X.presheaf.map (homOfLE (f.preimage_mono (le_inf (hE₁ x) (hE₂ x)))).op) hu
  rwa [CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_map] at this

set_option backward.isDefEq.respectTransparency false in
/-- If `f` is finite locally free, the opens of `Y` over which `f` is finite and free form a
basis of `Y`: for `W₀` affine, `Γ(X, f⁻¹ W₀)` is a finite, flat and finitely presented
`Γ(Y, W₀)`-module, hence free over the basic opens of a cover of `W₀`. -/
lemma exists_isFreeOver [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] {W : Y.Opens}
    {y : Y} (hy : y ∈ W) : ∃ V, f.IsFreeOver V ∧ y ∈ V ∧ V ≤ W := by
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hyW₀, hW₀W⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy W.isOpen
  let := (f.app W₀).hom.toAlgebra
  have : Module.Finite Γ(Y, W₀) Γ(X, f ⁻¹ᵁ W₀) := f.finite_app W₀ hW₀
  have : Module.Flat Γ(Y, W₀) Γ(X, f ⁻¹ᵁ W₀) := by
    have := HasRingHomProperty.appLE @Flat f ‹_› ⟨W₀, hW₀⟩ ⟨f ⁻¹ᵁ W₀, hW₀.preimage f⟩ le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at this
    exact this
  have : Algebra.FinitePresentation Γ(Y, W₀) Γ(X, f ⁻¹ᵁ W₀) := by
    have := HasRingHomProperty.appLE @LocallyOfFinitePresentation f ‹_› ⟨W₀, hW₀⟩
      ⟨f ⁻¹ᵁ W₀, hW₀.preimage f⟩ le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at this
    exact this
  have : Module.FinitePresentation Γ(Y, W₀) Γ(X, f ⁻¹ᵁ W₀) :=
    .of_finite_of_finitePresentation _ _
  let p := hW₀.primeIdealOf ⟨y, hyW₀⟩
  have : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl Γ(X, f ⁻¹ᵁ W₀)) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Γ(X, f ⁻¹ᵁ W₀))
    (Localization.AtPrime p.asIdeal)
  have hrW : Y.basicOpen r ≤ W₀ := Y.basicOpen_le r
  let : Algebra Γ(Y, W₀) Γ(Y, Y.basicOpen r) := (Y.presheaf.map (homOfLE hrW).op).hom.toAlgebra
  let : Algebra Γ(X, f ⁻¹ᵁ W₀) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (X.presheaf.map (homOfLE (f.preimage_mono hrW)).op).hom.toAlgebra
  let : Algebra Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r) := (f.app _).hom.toAlgebra
  let : Algebra Γ(Y, W₀) Γ(X, f ⁻¹ᵁ Y.basicOpen r) :=
    (f.appLE W₀ (f ⁻¹ᵁ Y.basicOpen r) (f.preimage_mono hrW)).hom.toAlgebra
  obtain ⟨h₁, h₂, h₃, h₄⟩ := isLocalization_basicOpen (f := f) hW₀ r hrW rfl
  have : IsLocalizedModule (.powers r) (IsScalarTower.toAlgHom Γ(Y, W₀) Γ(X, f ⁻¹ᵁ W₀)
      Γ(X, f ⁻¹ᵁ Y.basicOpen r)).toLinearMap := isLocalizedModule_iff_isLocalization.mpr h₂
  refine ⟨Y.basicOpen r, ⟨hW₀.basicOpen r, ?_, ?_⟩, ?_, hrW.trans hW₀W⟩
  · exact Module.Finite.of_isLocalizedModule (.powers r) (Rₚ := Γ(Y, Y.basicOpen r))
      (IsScalarTower.toAlgHom Γ(Y, W₀) Γ(X, f ⁻¹ᵁ W₀) Γ(X, f ⁻¹ᵁ Y.basicOpen r)).toLinearMap
  · exact (Module.free_localizedModule_iff_free (.powers r) Γ(Y, Y.basicOpen r)
      (IsScalarTower.toAlgHom Γ(Y, W₀) Γ(X, f ⁻¹ᵁ W₀) Γ(X, f ⁻¹ᵁ Y.basicOpen r)).toLinearMap).mp
      hfree
  · have : hW₀.fromSpec p ∈ Y.basicOpen r := by
      change p ∈ hW₀.fromSpec ⁻¹ᵁ Y.basicOpen r
      rw [hW₀.fromSpec_preimage_basicOpen]
      exact hr
    rwa [hW₀.fromSpec_primeIdealOf] at this

section Norm

variable (f) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

lemma existsUnique_norm (W : Y.Opens) (u : Γ(X, f ⁻¹ᵁ W)) :
    ∃! s : Γ(Y, W), ∀ (V : Y.Opens) (_ : f.IsFreeOver V) (hVW : V ≤ W),
      Y.presheaf.map (homOfLE hVW).op s =
        f.normApp V (X.presheaf.map (homOfLE (f.preimage_mono hVW)).op u) := by
  let ι := {V : Y.Opens // f.IsFreeOver V ∧ V ≤ W}
  have hcover : W ≤ ⨆ V : ι, V.1 := fun y hy ↦ by
    obtain ⟨V, hV, hyV, hVW⟩ := exists_isFreeOver (f := f) hy
    exact Opens.mem_iSup.mpr ⟨⟨V, hV, hVW⟩, hyV⟩
  obtain ⟨s, hs, hs'⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf (fun V : ι ↦ V.1) W
    (fun V ↦ homOfLE V.2.2) hcover
    (fun V ↦ f.normApp V.1 (X.presheaf.map (homOfLE (f.preimage_mono V.2.2)).op u))
    (fun V₁ V₂ ↦ V₁.2.1.normApp_compatible V₂.2.1 _ _
      (by rw [CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_map]))
  exact ⟨s, fun V hV hVW ↦ hs ⟨V, hV, hVW⟩, fun t ht ↦ hs' t fun V ↦ ht V.1 V.2.1 V.2.2⟩

/-- The function underlying the norm `N_f : Γ(X, f⁻¹ W) → Γ(Y, W)`. -/
noncomputable def normFun (W : Y.Opens) (u : Γ(X, f ⁻¹ᵁ W)) : Γ(Y, W) :=
  (f.existsUnique_norm W u).exists.choose

lemma normFun_spec (W : Y.Opens) (u : Γ(X, f ⁻¹ᵁ W)) {V : Y.Opens} (hV : f.IsFreeOver V)
    (hVW : V ≤ W) : Y.presheaf.map (homOfLE hVW).op (f.normFun W u) =
      f.normApp V (X.presheaf.map (homOfLE (f.preimage_mono hVW)).op u) :=
  (f.existsUnique_norm W u).exists.choose_spec V hV hVW

lemma eq_normFun {W : Y.Opens} {u : Γ(X, f ⁻¹ᵁ W)} {s : Γ(Y, W)}
    (hs : ∀ (V : Y.Opens) (_ : f.IsFreeOver V) (hVW : V ≤ W), Y.presheaf.map (homOfLE hVW).op s =
      f.normApp V (X.presheaf.map (homOfLE (f.preimage_mono hVW)).op u)) :
    s = f.normFun W u :=
  (f.existsUnique_norm W u).unique hs fun _ hV hVW ↦ f.normFun_spec W u hV hVW

/-- The norm `N_f : Γ(X, f⁻¹ W) → Γ(Y, W)` of a finite locally free morphism `f` (EGA II 6.5):
the unique section of `𝒪_Y` over `W` whose restriction to every open `V ⊆ W` over which `f` is
finite and free is the norm of the finite free `Γ(Y, V)`-algebra `Γ(X, f⁻¹ V)`. -/
noncomputable def norm (W : Y.Opens) : Γ(X, f ⁻¹ᵁ W) →* Γ(Y, W) where
  toFun := f.normFun W
  map_one' := (f.eq_normFun fun V _ hVW ↦ by simp only [map_one]).symm
  map_mul' u v := (f.eq_normFun fun V hV hVW ↦ by
    simp only [map_mul, f.normFun_spec W u hV hVW, f.normFun_spec W v hV hVW]).symm

lemma norm_spec (W : Y.Opens) (u : Γ(X, f ⁻¹ᵁ W)) {V : Y.Opens} (hV : f.IsFreeOver V)
    (hVW : V ≤ W) : Y.presheaf.map (homOfLE hVW).op (f.norm W u) =
      f.normApp V (X.presheaf.map (homOfLE (f.preimage_mono hVW)).op u) :=
  f.normFun_spec W u hV hVW

/-- The norm commutes with restrictions. -/
lemma norm_res {W W' : Y.Opens} (hW : W' ≤ W) (u : Γ(X, f ⁻¹ᵁ W)) :
    f.norm W' (X.presheaf.map (homOfLE (f.preimage_mono hW)).op u) =
      Y.presheaf.map (homOfLE hW).op (f.norm W u) := by
  refine (f.eq_normFun fun V hV hVW ↦ ?_).symm
  rw [CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_map]
  exact f.norm_spec W u hV (hVW.trans hW)

/-- If `N_f(u)` does not vanish at `f(x)`, then `u` does not vanish at `x`. -/
lemma preimage_basicOpen_norm_le {W : Y.Opens} (u : Γ(X, f ⁻¹ᵁ W)) :
    f ⁻¹ᵁ Y.basicOpen (f.norm W u) ≤ X.basicOpen u := by
  intro x hx
  have hxW : f x ∈ W := Y.basicOpen_le _ hx
  obtain ⟨V, hV, hxV, hVW⟩ := exists_isFreeOver (f := f) hxW
  have h : f x ∈ Y.basicOpen (Y.presheaf.map (homOfLE hVW).op (f.norm W u)) := by
    rw [Scheme.basicOpen_res]
    exact ⟨hxV, hx⟩
  rw [f.norm_spec W u hV hVW] at h
  have := hV.preimage_basicOpen_normApp_le _ h
  rw [Scheme.basicOpen_res] at this
  exact this.2

/-- If `u` does not vanish at any point over `y ∈ W`, then `N_f(u)` does not vanish at `y`: `u` is
a unit over the inverse image of a neighbourhood of `y`, `f` being closed. -/
lemma mem_basicOpen_norm {W : Y.Opens} (u : Γ(X, f ⁻¹ᵁ W)) {y : Y} (hy : y ∈ W)
    (h : ∀ x, f x = y → x ∈ X.basicOpen u) : y ∈ Y.basicOpen (f.norm W u) := by
  let C : Set X := (X.basicOpen u : Set X)ᶜ
  have hC : IsClosed (f '' C) := f.isClosedMap _ (X.basicOpen u).isOpen.isClosed_compl
  have hyC : y ∉ f '' C := by
    rintro ⟨x, hxC, rfl⟩
    exact hxC (h x rfl)
  let W₁ : Y.Opens := W ⊓ ⟨(f '' C)ᶜ, hC.isOpen_compl⟩
  have hW₁ : W₁ ≤ W := inf_le_left
  have hle : f ⁻¹ᵁ W₁ ≤ X.basicOpen u := fun x hx ↦ by
    by_contra hxu
    exact hx.2 ⟨x, hxu, rfl⟩
  have hunit : IsUnit (X.presheaf.map (homOfLE (f.preimage_mono hW₁)).op u) := by
    have := (X.toRingedSpace.isUnit_res_basicOpen u).map
      (X.presheaf.map (homOfLE hle).op).hom
    change IsUnit (X.presheaf.map (homOfLE hle).op
      (X.presheaf.map (homOfLE (X.basicOpen_le u)).op u)) at this
    rwa [CohomologyAux.presheaf_map_map] at this
  have h₁ := (hunit.map (f.norm W₁)).map (Y.presheaf.map (homOfLE (le_refl W₁)).op).hom
  rw [f.norm_res hW₁, CohomologyAux.presheaf_map_map] at h₁
  have h₂ := Y.basicOpen_of_isUnit h₁
  rw [Scheme.basicOpen_res] at h₂
  have hyW₁ : y ∈ W₁ := ⟨hy, hyC⟩
  rw [← h₂] at hyW₁
  exact hyW₁.2

/-- `N_f(u)` does not vanish at `y ∈ W` iff `u` does not vanish at any point over `y`. -/
lemma mem_basicOpen_norm_iff {W : Y.Opens} (u : Γ(X, f ⁻¹ᵁ W)) {y : Y} (hy : y ∈ W) :
    y ∈ Y.basicOpen (f.norm W u) ↔ ∀ x, f x = y → x ∈ X.basicOpen u :=
  ⟨fun h x hx ↦ f.preimage_basicOpen_norm_le u (show f x ∈ _ from hx ▸ h),
    f.mem_basicOpen_norm u hy⟩

end Norm

end Scheme.Hom

end AlgebraicGeometry
