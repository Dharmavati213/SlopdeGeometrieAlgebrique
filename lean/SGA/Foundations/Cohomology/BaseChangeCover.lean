/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.BaseChangeLocal
import SGA.Foundations.Cohomology.SeparatingSections
import SGA.Foundations.Cohomology.SteinFactorization
import SGA.Foundations.Cohomology.BaseChangeSections
import SGA.Foundations.Cohomology.QuasiCoherentAbelian
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Čech data of a finite affine cover and the sheaves `𝒪_X / Iⁿ⁺¹`

Let `f : X ⟶ Spec A` and let `U₁, …, U_r` be a finite affine open cover of `X`, with affine
intersections. This file provides the geometric input of the local base change theorem
(`CohomologyAux.BaseChangeData`, EGA III 7.8):

* `CohomologyAux.exists_glue_of_iSup_eq_top`, `CohomologyAux.eq_zero_of_forall_map_eq_zero`: the
  sheaf axioms for a finite cover;
* `CohomologyAux.quotApp`: the reduction `Γ(X, V) → Γ(𝒪_X / Iⁿ⁺¹ 𝒪_X, V)`, whose kernel is
  `Iⁿ⁺¹ Γ(X, V)` for `V` affine (`quotApp_eq_zero_iff`);
* `CohomologyAux.cechSigma`, `cechAlpha`, `cechBeta`: the restrictions
  `Γ(X, 𝒪_X) → ∏ Γ(Uᵢ) ⇉ ∏ Γ(Uᵢ ∩ Uⱼ)` as `A`-algebra maps;
* `CohomologyAux.exists_glue_quot`: a family of sections of the `Uᵢ` agreeing modulo `Iⁿ⁺¹` on the
  `Uᵢ ∩ Uⱼ` glues to a section of `𝒪_X / Iⁿ⁺¹ 𝒪_X`;
* for `f` proper: `CohomologyAux.exists_lift` (compatible families of sections of the thickenings
  lift to `Γ(X, 𝒪_X)`, the theorem on formal functions EGA III 4.1.5), `CohomologyAux.artinRees`
  (EGA III 4.1.7) and `CohomologyAux.exists_monic` (sections of the closed fibre are integral);
* `CohomologyAux.isReduced_tensor_sections`: geometrically reduced fibres give reduced
  `K ⊗_A Γ(X, V)`;
* `CohomologyAux.baseChangeData`: all of this assembled into `BaseChangeData` over a noetherian
  local ring.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct Polynomial

namespace AlgebraicGeometry.CohomologyAux

attribute [local instance] Ideal.Quotient.field

section Glue

variable {X : Scheme.{u}} (N : X.Modules) {ι : Type*} (U : ι → X.Opens)

/-- Gluing sections of an `𝒪_X`-module over an open cover of `X`. -/
lemma exists_glue_of_iSup_eq_top (hU : ⨆ i, U i = ⊤) (s : ∀ i, Γ(N, U i))
    (h : ∀ i j, N.presheaf.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op (s i) =
      N.presheaf.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op (s j)) :
    ∃ z : Γ(N, ⊤), ∀ i, N.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op z = s i := by
  obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' N.toAbSheaf U ⊤
    (fun _ ↦ homOfLE le_top) hU.ge s h
  exact ⟨t, ht⟩

/-- A section of an `𝒪_X`-module vanishing on the members of an open cover vanishes. -/
lemma eq_zero_of_forall_map_eq_zero (hU : ⨆ i, U i = ⊤) (z : Γ(N, ⊤))
    (h : ∀ i, N.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op z = 0) : z = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' N.toAbSheaf U ⊤ (fun _ ↦ homOfLE le_top) hU.ge z 0
    fun i ↦ ?_
  change N.presheaf.map _ z = N.presheaf.map _ 0
  rw [h i, map_zero]

end Glue

section Quot

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- The reduction map `Γ(X, V) → Γ(𝒪_X / Iⁿ⁺¹ 𝒪_X, V)`. -/
noncomputable def quotApp (n : ℕ) (V : X.Opens) :
    Γ(X, V) →+ Γ((unitModule X).quotientIdealPow f I n, V) :=
  (((unitModule X).toQuotientIdealPow f I n).app V).hom

lemma quotApp_map (n : ℕ) {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) :
    quotApp I f n W (X.presheaf.map (homOfLE h).op x) =
      ((unitModule X).quotientIdealPow f I n).presheaf.map (homOfLE h).op (quotApp I f n V x) :=
  hom_app_presheaf_map _ (homOfLE h) (show Γ(unitModule X, V) from x)

lemma quotApp_succ (n : ℕ) (V : X.Opens) (x : Γ(X, V)) :
    ((unitModule X).quotientIdealPowMap f I n).app V (quotApp I f (n + 1) V x) =
      quotApp I f n V x := by
  change (((unitModule X).toQuotientIdealPow f I (n + 1) ≫
    (unitModule X).quotientIdealPowMap f I n).app V) x = _
  rw [Scheme.Modules.toQuotientIdealPow_comp_map]
  rfl

variable [IsNoetherianRing A]

/-- **Sections of `𝒪_X / Iⁿ⁺¹` over an affine open**: the kernel of `quotApp` is `Iⁿ⁺¹ Γ(X, V)`. -/
lemma quotApp_eq_zero_iff (n : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (x : Γ(X, V)) :
    quotApp I f n V x = 0 ↔ x ∈ idealV f I V (n + 1) := by
  have h1 := toQuotientIdealPow_app_eq_zero_iff I f (unitModule X) n V
    (show Γ(unitModule X, V) from x)
  have h2 := mem_range_ιPow_app f I (unitModule X) hV (n + 1) (show Γ(unitModule X, V) from x)
  refine h1.trans (h2.trans ?_)
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun r hr y _ ↦ ?_) fun y z hy hz ↦ ?_
    · exact Ideal.mul_mem_right _ _ hr
    · exact Ideal.add_mem _ hy hz
  · intro hx
    have := Submodule.smul_mem_smul (M := Γ(unitModule X, V)) hx
      (Submodule.mem_top (x := show Γ(unitModule X, V) from (1 : Γ(X, V))))
    convert this using 1
    change x = x * 1
    rw [mul_one]

end Quot

section Pi

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {S : ι → Type*} [∀ i, CommRing (S i)]
  [∀ i, Algebra R (S i)]

/-- Membership in the extension of an ideal to a finite product is componentwise. -/
lemma mem_map_pi_iff (J : Ideal R) (x : ∀ i, S i) :
    x ∈ J.map (algebraMap R (∀ i, S i)) ↔ ∀ i, x i ∈ J.map (algebraMap R (S i)) := by
  classical
  have := Fintype.ofFinite ι
  constructor
  · intro hx i
    have := Ideal.mem_map_of_mem (Pi.evalRingHom S i) hx
    rwa [Ideal.map_map] at this
  · intro hx
    have hx' : ∀ i, x i ∈ J • (⊤ : Submodule R (S i)) := fun i ↦ mem_smul_top_iff.mpr (hx i)
    rw [← mem_smul_top_iff, ← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have : Pi.single i (x i) ∈ (J • (⊤ : Submodule R (S i))).map (LinearMap.single R S i) :=
      Submodule.mem_map_of_mem (hx' i)
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this

end Pi

section Cover

variable {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)

lemma structMapV_map {V W : X.Opens} (h : W ≤ V) (a : A) :
    X.presheaf.map (homOfLE h).op (structMapV f V a) = structMapV f W a := by
  rw [structMapV_eq_map, structMapV_eq_map, presheaf_map_map]

variable [∀ V : X.Opens, Algebra A Γ(X, V)]
  (hA : ∀ V : X.Opens, algebraMap A Γ(X, V) = structMapV f V)

include hA in
/-- For `f` flat, the sections over affine opens are flat `A`-modules. -/
lemma flat_sections [Flat f] {V : X.Opens} (hV : IsAffineOpen V) : Module.Flat A Γ(X, V) := by
  rw [← RingHom.flat_algebraMap_iff, hA, structMapV, CommRingCat.hom_comp]
  exact RingHom.Flat.comp (.of_bijective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso A).inv))
    (HasRingHomProperty.appLE (P := @Flat) f ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top)

include hA in
/-- For `f` proper over a noetherian `A`, `Γ(X, 𝒪_X)` is a finite `A`-module. -/
lemma finite_sections_top [IsNoetherianRing A] [IsProper f] : Module.Finite A Γ(X, ⊤) := by
  have e : structMapV f ⊤ = f.specStructureRingHom := by
    ext a
    rw [structMapV_eq_map, presheaf_map_self]
  rw [← RingHom.finite_algebraMap, hA, e, Scheme.Hom.specStructureRingHom, CommRingCat.hom_comp]
  exact RingHom.Finite.comp (finite_app_of_isProper f (isAffineOpen_top (Spec A)))
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)

include hA in
/-- The restriction `Γ(X, V) → Γ(X, W)` as an `A`-algebra map. -/
noncomputable def resAlgHom {V W : X.Opens} (h : W ≤ V) : Γ(X, V) →ₐ[A] Γ(X, W) where
  toRingHom := (X.presheaf.map (homOfLE h).op).hom
  commutes' a := by
    change X.presheaf.map (homOfLE h).op (algebraMap A Γ(X, V) a) = algebraMap A Γ(X, W) a
    rw [hA, hA, structMapV_map]

lemma resAlgHom_apply {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) :
    resAlgHom f hA h x = X.presheaf.map (homOfLE h).op x := rfl

variable {n : ℕ} (U : Fin n → X.Opens)

/-- The restriction `σ : Γ(X, 𝒪_X) → ∏ᵢ Γ(Uᵢ, 𝒪_X)`. -/
noncomputable def cechSigma : Γ(X, ⊤) →ₐ[A] ∀ i, Γ(X, U i) :=
  AlgHom.pi fun _ ↦ resAlgHom f hA le_top

/-- The first restriction `α : ∏ᵢ Γ(Uᵢ, 𝒪_X) → ∏ᵢⱼ Γ(Uᵢ ∩ Uⱼ, 𝒪_X)`, `(cᵢ) ↦ (cᵢ|Uᵢ ∩ Uⱼ)`. -/
noncomputable def cechAlpha :
    (∀ i, Γ(X, U i)) →ₐ[A] ∀ p : Fin n × Fin n, Γ(X, U p.1 ⊓ U p.2) :=
  AlgHom.pi fun p ↦ (resAlgHom f hA inf_le_left).comp (Pi.evalAlgHom _ _ p.1)

/-- The second restriction `β : ∏ᵢ Γ(Uᵢ, 𝒪_X) → ∏ᵢⱼ Γ(Uᵢ ∩ Uⱼ, 𝒪_X)`, `(cᵢ) ↦ (cⱼ|Uᵢ ∩ Uⱼ)`. -/
noncomputable def cechBeta :
    (∀ i, Γ(X, U i)) →ₐ[A] ∀ p : Fin n × Fin n, Γ(X, U p.1 ⊓ U p.2) :=
  AlgHom.pi fun p ↦ (resAlgHom f hA inf_le_right).comp (Pi.evalAlgHom _ _ p.2)

lemma cechSigma_apply (y : Γ(X, ⊤)) (i : Fin n) :
    cechSigma f hA U y i = X.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op y := rfl

lemma cechAlpha_apply (c : ∀ i, Γ(X, U i)) (p : Fin n × Fin n) :
    cechAlpha f hA U c p =
      X.presheaf.map (homOfLE inf_le_left : U p.1 ⊓ U p.2 ⟶ U p.1).op (c p.1) :=
  rfl

lemma cechBeta_apply (c : ∀ i, Γ(X, U i)) (p : Fin n × Fin n) :
    cechBeta f hA U c p =
      X.presheaf.map (homOfLE inf_le_right : U p.1 ⊓ U p.2 ⟶ U p.2).op (c p.2) :=
  rfl

lemma cechAlpha_cechSigma (y : Γ(X, ⊤)) :
    cechAlpha f hA U (cechSigma f hA U y) = cechBeta f hA U (cechSigma f hA U y) := by
  funext p
  rw [cechAlpha_apply, cechBeta_apply, cechSigma_apply, cechSigma_apply]
  exact presheaf_map_map' _ _ _ _ y

end Cover

section Data

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A) [∀ V : X.Opens, Algebra A Γ(X, V)]
  (hA : ∀ V : X.Opens, algebraMap A Γ(X, V) = structMapV f V)
  {n : ℕ} (U : Fin n → X.Opens) (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
  (hUa₂ : ∀ i j, IsAffineOpen (U i ⊓ U j))

include hA in
omit [IsNoetherianRing A] in
lemma mem_idealV_iff (V : X.Opens) (k : ℕ) (x : Γ(X, V)) :
    x ∈ idealV f I V k ↔ x ∈ (I ^ k).map (algebraMap A Γ(X, V)) := by
  rw [idealV, hA]

include hA hUa₂ in
/-- **Gluing modulo `Iᵏ⁺¹`**: sections of the `Uᵢ` whose restrictions to the `Uᵢ ∩ Uⱼ` agree
modulo `Iᵏ⁺¹` define a section of `𝒪_X / Iᵏ⁺¹ 𝒪_X`. -/
lemma exists_glue_quot (hU : ⨆ i, U i = ⊤) (k : ℕ) (c : ∀ i, Γ(X, U i))
    (hc : cechAlpha f hA U c - cechBeta f hA U c ∈
      (I ^ (k + 1)).map (algebraMap A (∀ p : Fin n × Fin n, Γ(X, U p.1 ⊓ U p.2)))) :
    ∃ z : Γ((unitModule X).quotientIdealPow f I k, ⊤), ∀ i,
      ((unitModule X).quotientIdealPow f I k).presheaf.map (homOfLE le_top : U i ⟶ ⊤).op z =
        quotApp I f k (U i) (c i) := by
  refine exists_glue_of_iSup_eq_top ((unitModule X).quotientIdealPow f I k) U hU _ fun i j ↦ ?_
  rw [← quotApp_map, ← quotApp_map, ← sub_eq_zero, ← map_sub,
    quotApp_eq_zero_iff I f k (hUa₂ i j), mem_idealV_iff I f hA]
  exact (mem_map_pi_iff _ _).mp hc (i, j)

include hA hU hUa hUa₂ in
/-- Compatible families of sections over the thickenings come from global sections: the theorem
on formal functions (EGA III 4.1.5, 4.1.7) in the form `exists_H'_map_toQuotientIdealPow_eq`. -/
lemma exists_lift [IsProper f] (c : ℕ → ∀ i, Γ(X, U i))
    (h₁ : ∀ k, cechAlpha f hA U (c k) - cechBeta f hA U (c k) ∈
      (I.map (algebraMap A (∀ p : Fin n × Fin n, Γ(X, U p.1 ⊓ U p.2)))) ^ (k + 1))
    (h₂ : ∀ k, c (k + 1) - c k ∈ (I.map (algebraMap A (∀ i, Γ(X, U i)))) ^ (k + 1)) :
    ∃ y, cechSigma f hA U y - c 0 ∈ I.map (algebraMap A (∀ i, Γ(X, U i))) := by
  choose z hz using fun k ↦ exists_glue_quot I f hA U hUa₂ hU k (c k)
    (by rw [Ideal.map_pow]; exact h₁ k)
  have hcompat : ∀ k, ((unitModule X).quotientIdealPowMap f I k).app ⊤ (z (k + 1)) = z k := by
    intro k
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_map_eq_zero _ U hU _ fun i ↦ ?_
    rw [map_sub, ← hom_app_presheaf_map, hz, hz, quotApp_succ, ← map_sub,
      quotApp_eq_zero_iff I f k (hUa i), mem_idealV_iff I f hA]
    have h₂' := h₂ k
    rw [← Ideal.map_pow] at h₂'
    exact (mem_map_pi_iff _ _).mp h₂' i
  have : (unitModule X).IsCoherent := isCoherent_unitModule X
  obtain ⟨y, hy⟩ := exists_H'_map_toQuotientIdealPow_eq I f (unitModule X) 0
    ⟨_, mem_formalLimit_of_compat (I := I) (f := f) z hcompat⟩ 0
  let a : Γ(X, ⊤) := Scheme.Modules.H.equiv₀ _ y
  have ha : quotApp I f 0 ⊤ a = z 0 := by
    change ((unitModule X).toQuotientIdealPow f I 0).app ⊤ (Scheme.Modules.H.equiv₀ _ y) = _
    rw [← equiv₀_H'_map_toQuotientIdealPow, hy]
    exact (Scheme.Modules.H.equiv₀ _).apply_symm_apply _
  refine ⟨a, (mem_map_pi_iff _ _).mpr fun i ↦ ?_⟩
  have h := (quotApp_eq_zero_iff I f 0 (hUa i) (cechSigma f hA U a i - c 0 i)).mp (by
    rw [map_sub, cechSigma_apply, quotApp_map, ha, hz, sub_self])
  rw [mem_idealV_iff I f hA, zero_add, pow_one] at h
  exact h

include hA hU hUa in
/-- **Artin–Rees for global sections** (EGA III 4.1.7, proof of 4.1.5): a global function whose
restrictions to the `Uᵢ` lie in `I^N` for `N ≫ 0` lies in `I Γ(X, 𝒪_X)`
(`exists_range_ιPow_le`). -/
lemma artinRees [IsProper f] : ∃ N, ∀ y : Γ(X, ⊤),
    cechSigma f hA U y ∈ (I.map (algebraMap A (∀ i, Γ(X, U i)))) ^ N →
      y ∈ I.map (algebraMap A Γ(X, ⊤)) := by
  have : (unitModule X).IsCoherent := isCoherent_unitModule X
  let _ := (unitModule X).moduleOver f 0 ⊤
  obtain ⟨c, hc⟩ := exists_range_ιPow_le I f (unitModule X) 0
  refine ⟨c + 1, fun y hy ↦ ?_⟩
  rw [← Ideal.map_pow] at hy
  have h0 : quotApp I f c ⊤ y = 0 := by
    refine eq_zero_of_forall_map_eq_zero _ U hU _ fun i ↦ ?_
    rw [← quotApp_map, quotApp_eq_zero_iff I f c (hUa i), mem_idealV_iff I f hA]
    exact (mem_map_pi_iff _ _).mp hy i
  obtain ⟨t, ht⟩ := (toQuotientIdealPow_app_eq_zero_iff I f (unitModule X) c ⊤
    (show Γ(unitModule X, ⊤) from y)).mp h0
  let t' := (Scheme.Modules.H.equiv₀ (IPow f I (unitModule X) (c + 1))).symm t
  have hmem := hc (c + 1) 1 (by omega) t'
  have e : Scheme.Modules.H.equiv₀ _
      (Scheme.Modules.H'.map (ιPow f I (unitModule X) (c + 1)) 0 ⊤ t') = y := by
    have := CategoryTheory.Sheaf.H'.equiv₀_naturality
      (Scheme.Modules.Hom.toAbSheaf (ιPow f I (unitModule X) (c + 1))) (U := ⊤) t'
    refine this.trans ?_
    change ((ιPow f I (unitModule X) (c + 1)).app ⊤)
      ((Scheme.Modules.H.equiv₀ _) ((Scheme.Modules.H.equiv₀ _).symm t)) = y
    rw [LinearEquiv.apply_symm_apply]
    exact ht
  have hs : f.specStructureRingHom = algebraMap A Γ(X, ⊤) := by
    ext a; rw [hA, structMapV_eq_map, presheaf_map_self]
  rw [← e]
  rw [pow_one] at hmem
  refine Submodule.smul_induction_on hmem (fun a ha w _ ↦ ?_) fun w w' hw hw' ↦ ?_
  · change Scheme.Modules.H.equiv₀ _ (f.specStructureRingHom a • w) ∈ _
    rw [LinearEquiv.map_smul, hs]
    change algebraMap A Γ(X, ⊤) a * (show Γ(X, ⊤) from Scheme.Modules.H.equiv₀ _ w) ∈ _
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
  · rw [map_add]
    exact Ideal.add_mem _ hw hw'

include hA in
/-- `Γ(X, 𝒪_X / Iᵏ⁺¹)` is a finite `A`-module (EGA III 3.2.1), for `f` proper. -/
lemma finite_sections_quot [IsProper f] (k : ℕ) :
    letI : Module A Γ((unitModule X).quotientIdealPow f I k, ⊤) :=
      Module.compHom _ (algebraMap A Γ(X, ⊤))
    Module.Finite A Γ((unitModule X).quotientIdealPow f I k, ⊤) := by
  let _ : Module A Γ((unitModule X).quotientIdealPow f I k, ⊤) :=
    Module.compHom _ (algebraMap A Γ(X, ⊤))
  have : (unitModule X).IsCoherent := isCoherent_unitModule X
  have : (unitModule X).IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have := isQuasicoherent_IPow I f (unitModule X) (k + 1)
  have : ((unitModule X).quotientIdealPow f I k).IsCoherent :=
    isCoherent_X₃_of_shortExact (shortExact_quotientIdealPow f I (unitModule X) k)
  have h := properFinitenessStatement A X f ((unitModule X).quotientIdealPow f I k) 0
  let _ := ((unitModule X).quotientIdealPow f I k).moduleOver f 0 ⊤
  let e0 := Scheme.Modules.H.equiv₀ ((unitModule X).quotientIdealPow f I k)
  have hs : f.specStructureRingHom = algebraMap A Γ(X, ⊤) := by
    ext a; rw [hA, structMapV_eq_map, presheaf_map_self]
  let e : ((unitModule X).quotientIdealPow f I k).H 0 ≃ₗ[A]
      Γ((unitModule X).quotientIdealPow f I k, ⊤) :=
    { toAddEquiv := e0.toAddEquiv
      map_smul' := fun a x ↦ by
        change e0 (f.specStructureRingHom a • x) = algebraMap A Γ(X, ⊤) a • e0 x
        rw [LinearEquiv.map_smul, hs] }
  exact Module.Finite.equiv e

include hA hU hUa hUa₂ in
/-- **Sections of the closed fibre are integral** (properness): if `c ∈ ∏ Γ(Uᵢ)` is a section
modulo `I`, it satisfies a monic equation over `A` modulo `I`. (The images of the `cʲ` in the
finite `A`-module `Γ(X, 𝒪_X / I)` span a noetherian submodule.) -/
lemma exists_monic [IsProper f] (c : ∀ i, Γ(X, U i))
    (hc : cechAlpha f hA U c - cechBeta f hA U c ∈
      I.map (algebraMap A (∀ p : Fin n × Fin n, Γ(X, U p.1 ⊓ U p.2)))) :
    ∃ P : A[X], P.Monic ∧ aeval c P ∈ I.map (algebraMap A (∀ i, Γ(X, U i))) := by
  have hpow : ∀ j : ℕ, cechAlpha f hA U (c ^ j) - cechBeta f hA U (c ^ j) ∈
      (I ^ (0 + 1)).map (algebraMap A (∀ p : Fin n × Fin n, Γ(X, U p.1 ⊓ U p.2))) := by
    intro j
    rw [map_pow, map_pow, zero_add, pow_one]
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (cechAlpha f hA U c) (cechBeta f hA U c) j
    rw [hd]
    exact Ideal.mul_mem_right _ _ hc
  choose z hz using fun j ↦ exists_glue_quot I f hA U hUa₂ hU 0 (c ^ j) (hpow j)
  let _ : Module A Γ((unitModule X).quotientIdealPow f I 0, ⊤) :=
    Module.compHom _ (algebraMap A Γ(X, ⊤))
  have : Module.Finite A Γ((unitModule X).quotientIdealPow f I 0, ⊤) :=
    finite_sections_quot I f hA 0
  have : _root_.IsNoetherian A Γ((unitModule X).quotientIdealPow f I 0, ⊤) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  let F : ℕ →o Submodule A Γ((unitModule X).quotientIdealPow f I 0, ⊤) :=
    ⟨fun k ↦ Submodule.span A (Set.range fun j : Fin k ↦ z j), fun k l hkl ↦
      Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨⟨j, by omega⟩, rfl⟩)⟩
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) F
  have hzN : z N ∈ F N := by
    rw [hN (N + 1) (Nat.le_succ N)]
    exact Submodule.subset_span ⟨⟨N, Nat.lt_succ_self N⟩, rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hzN
  refine ⟨Polynomial.X ^ N - ∑ j : Fin N, C (a j) * Polynomial.X ^ (j : ℕ),
    monic_X_pow_sub (degree_sum_fin_lt a), ?_⟩
  refine (mem_map_pi_iff _ _).mpr fun i ↦ ?_
  have hev : (aeval c (Polynomial.X ^ N - ∑ j : Fin N, C (a j) * Polynomial.X ^ (j : ℕ))) i =
      (c ^ N) i - ∑ j : Fin N, algebraMap A Γ(X, U i) (a j) * (c ^ (j : ℕ)) i := by
    simp only [map_sub, map_pow, aeval_X, map_sum, map_mul, aeval_C, Pi.sub_apply,
      Finset.sum_apply, Pi.mul_apply, Pi.algebraMap_apply]
  rw [hev]
  have h := (quotApp_eq_zero_iff I f 0 (hUa i) _).mp (show quotApp I f 0 (U i)
    ((c ^ N) i - ∑ j : Fin N, algebraMap A Γ(X, U i) (a j) * (c ^ (j : ℕ)) i) = 0 from ?_)
  · rwa [mem_idealV_iff I f hA, zero_add, pow_one] at h
  have hsm : ∀ (j : Fin N), quotApp I f 0 (U i) (algebraMap A Γ(X, U i) (a j) * (c ^ (j : ℕ)) i) =
      ((unitModule X).quotientIdealPow f I 0).presheaf.map (homOfLE le_top : U i ⟶ ⊤).op
        (a j • z j) := by
    intro j
    change quotApp I f 0 (U i) (algebraMap A Γ(X, U i) (a j) • (c ^ (j : ℕ)) i) =
      ((unitModule X).quotientIdealPow f I 0).presheaf.map (homOfLE le_top : U i ⟶ ⊤).op
        (algebraMap A Γ(X, ⊤) (a j) • z j)
    rw [Scheme.Modules.map_smul, hz, hA, hA, structMapV_map]
    exact Scheme.Modules.Hom.app_smul _ _ _
  rw [map_sub, map_sum, Finset.sum_congr rfl fun j _ ↦ hsm j, ← map_sum, ha, ← hz, sub_self]

end Data

section Reduced

variable {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
  [∀ V : X.Opens, Algebra A Γ(X, V)] (hA : ∀ V : X.Opens, algebraMap A Γ(X, V) = structMapV f V)

include hA in
/-- **Geometrically reduced fibres, on sections** (EGA IV 4.6.1): for `f` geometrically reduced,
`K` a field over `A` and `V ⊆ X` affine, `K ⊗_A Γ(X, V) = Γ(X_K, V_K)` is reduced. -/
lemma isReduced_tensor_sections [GeometricallyReduced f] (K : Type u) [Field K] [Algebra A K]
    {V : X.Opens} (hV : IsAffineOpen V) : _root_.IsReduced (K ⊗[A] Γ(X, V)) := by
  let β : A ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap A K)
  have H := IsPullback.of_hasPullback f (Spec.map β)
  have hP : IsReduced (pullback f (Spec.map β)) :=
    GeometricallyReduced.geometrically_isReduced (f := f) (Spec.map β) _ _ H
  have h := isPushout_baseChange H hV
  have e₁ : (Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ V le_top =
      CommRingCat.ofHom (algebraMap A Γ(X, V)) := by
    rw [hA]; rfl
  rw [e₁] at h
  let e := h.isoIsPushout _ _ (CommRingCat.isPushout_tensorProduct A Γ(X, V) K)
  have : _root_.IsReduced (Γ(X, V) ⊗[A] K) :=
    isReduced_of_injective e.inv.hom (ConcreteCategory.bijective_of_isIso e.inv).1
  exact isReduced_of_injective (Algebra.TensorProduct.comm A K Γ(X, V)).toRingHom
    (AlgEquiv.injective _)

include hA in
lemma flat_pi_sections [Flat f] {ι : Type*} [Finite ι] (W : ι → X.Opens)
    (hW : ∀ i, IsAffineOpen (W i)) : Module.Flat A (∀ i, Γ(X, W i)) := by
  classical
  have := Fintype.ofFinite ι
  have : ∀ i, Module.Flat A Γ(X, W i) := fun i ↦ flat_sections f hA (hW i)
  exact Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := A)).symm

end Reduced

section Assemble

variable {A : CommRingCat.{u}} [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec A) [∀ V : X.Opens, Algebra A Γ(X, V)]
  (hA : ∀ V : X.Opens, algebraMap A Γ(X, V) = structMapV f V)
  {n : ℕ} (U : Fin n → X.Opens) (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
  (hUa₂ : ∀ i j, IsAffineOpen (U i ⊓ U j))

include hA hU hUa hUa₂ in
/-- **The geometric input of the local base change theorem**: for `f` proper, flat with
geometrically reduced fibres over a noetherian local ring, the Čech data of a finite affine
cover with affine intersections satisfy `BaseChangeData`. -/
theorem baseChangeData [IsProper f] [GeometricallyReduced f] :
    BaseChangeData (cechSigma f hA U) (cechAlpha f hA U) (cechBeta f hA U) where
  comp_eq := cechAlpha_cechSigma f hA U
  exists_monic c hc := exists_monic _ f hA U hU hUa hUa₂ c hc
  isReduced := by
    classical
    have : ∀ i, _root_.IsReduced
        (AlgebraicClosure (A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] Γ(X, U i)) :=
      fun i ↦ isReduced_tensor_sections f hA _ (hUa i)
    exact isReduced_of_injective
      (Algebra.TensorProduct.piRight A A (AlgebraicClosure (A ⧸ IsLocalRing.maximalIdeal A))
        fun i ↦ Γ(X, U i)).toRingHom (AlgEquiv.injective _)
  exists_lift c h₁ h₂ := exists_lift _ f hA U hU hUa hUa₂ c h₁ h₂
  artinRees := artinRees _ f hA U hU hUa

end Assemble

end AlgebraicGeometry.CohomologyAux
