/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.LocallyFreeAlgebraization
import SGA.Foundations.Cohomology.ClosedFibre

/-!
# Algebraizations of locally free adic systems on proper schemes are locally free

Let `A` be noetherian and `I`-adically complete, `f : X ⟶ Spec A` proper and `B` a coherent
`𝒪_X`-module whose reductions `B / I^{n+1} B` are locally free on the thickenings `X_n` (their
sections over affine opens have the lifting property of projective modules over
`Γ(X, V) / I^{n+1}`). Then `B` has projective sections over every affine open (EGA III 5.1.4,
Stacks 0DEM). This removes the projectivity hypothesis on `X` from
`projective_sections_of_liftingProperty`.

* `splittingIdeal R M`: the ideal of `a ∈ R` such that `a • id_M` factors through a projective
  module; `M` is projective iff it contains `1`, and it behaves well under localization
  (`projective_of_mem_splittingIdeal`, `exists_pow_mem_splittingIdeal_of_projective`);
* `exists_mem_splittingIdeal_sub_one_mem`: the local step, via Nakayama;
* `isLocalizedModule_resLinear`: `Γ(B, V) → Γ(B, D(f))` is a localization for `B`
  quasi-coherent and `V` affine;
* `projective_sections_of_liftingProperty_of_isProper`: the main theorem.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

section SplittingIdeal

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

/-- The **splitting ideal** of an `R`-module `M`: the `a ∈ R` such that `a • id_M` factors through
a projective module. `M` is projective iff `1` lies in it (`projective_of_one_mem_splittingIdeal`),
and it localizes well (`projective_of_mem_splittingIdeal`,
`exists_pow_mem_splittingIdeal_of_projective`). -/
def splittingIdeal : Ideal R where
  carrier := {a | ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module R N) (_ : Module.Projective R N)
    (π : N →ₗ[R] M) (ψ : M →ₗ[R] N), π ∘ₗ ψ = a • LinearMap.id}
  add_mem' := by
    rintro a b ⟨N, _, _, _, π, ψ, h⟩ ⟨N', _, _, _, π', ψ', h'⟩
    refine ⟨N × N', inferInstance, inferInstance, inferInstance, π.coprod π', ψ.prod ψ', ?_⟩
    rw [LinearMap.coprod_comp_prod, h, h', add_smul]
  zero_mem' := ⟨R, inferInstance, inferInstance, inferInstance, 0, 0, by simp⟩
  smul_mem' := by
    rintro c a ⟨N, _, _, _, π, ψ, h⟩
    refine ⟨N, inferInstance, inferInstance, inferInstance, π, c • ψ, ?_⟩
    rw [LinearMap.comp_smul, h, smul_smul, smul_eq_mul]

variable {R M}

lemma mem_splittingIdeal_of_comp {N : Type u} [AddCommGroup N] [Module R N]
    [Module.Projective R N] (π : N →ₗ[R] M) (ψ : M →ₗ[R] N) {a : R}
    (h : π ∘ₗ ψ = a • LinearMap.id) : a ∈ splittingIdeal R M :=
  ⟨N, inferInstance, inferInstance, inferInstance, π, ψ, h⟩

/-- `M` is projective as soon as `1` lies in its splitting ideal. -/
theorem projective_of_one_mem_splittingIdeal (h : (1 : R) ∈ splittingIdeal R M) :
    Module.Projective R M := by
  obtain ⟨N, _, _, _, π, ψ, h⟩ := h
  exact Module.Projective.of_split ψ π (by rw [h, one_smul])

/-- Over the localization `Rₐ` of `R` at `a` in the splitting ideal, the localization `Mₐ` of `M`
is projective. -/
theorem projective_of_mem_splittingIdeal {a : R} (ha : a ∈ splittingIdeal R M)
    (Rₛ : Type u) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization.Away a Rₛ]
    {Mₛ : Type u} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (g : M →ₗ[R] Mₛ) [IsLocalizedModule (Submonoid.powers a) g] :
    Module.Projective Rₛ Mₛ := by
  obtain ⟨N, _, _, _, π, ψ, h⟩ := ha
  have hbc := IsLocalizedModule.isBaseChange (Submonoid.powers a) Rₛ g
  have hu : IsUnit (algebraMap R Rₛ a) :=
    IsLocalization.map_units Rₛ (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)
  let πs := π.baseChange Rₛ
  let ψs := ψ.baseChange Rₛ
  have hcomp : πs ∘ₗ ((hu.unit⁻¹ : Rₛˣ) • ψs) = LinearMap.id := by
    rw [LinearMap.comp_smul, ← LinearMap.baseChange_comp, h, LinearMap.baseChange_smul,
      LinearMap.baseChange_id]
    refine LinearMap.ext fun x ↦ ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, ← algebraMap_smul Rₛ a x,
      Units.smul_def, smul_smul, hu.val_inv_mul, one_smul]
  have : Module.Projective Rₛ (Rₛ ⊗[R] M) :=
    Module.Projective.of_split ((hu.unit⁻¹ : Rₛˣ) • ψs) πs hcomp
  exact Module.Projective.of_equiv hbc.equiv

/-- If the localization `M_f` is projective over `R_f` and `M` is finitely presented, some power
of `f` lies in the splitting ideal of `M`. -/
theorem exists_pow_mem_splittingIdeal_of_projective [Module.FinitePresentation R M] (f : R)
    (Rₛ : Type u) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization.Away f Rₛ]
    {Mₛ : Type u} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (g : M →ₗ[R] Mₛ) [IsLocalizedModule (Submonoid.powers f) g] [Module.Projective Rₛ Mₛ] :
    ∃ k : ℕ, f ^ k ∈ splittingIdeal R M := by
  classical
  have hbc := IsLocalizedModule.isBaseChange (Submonoid.powers f) Rₛ g
  have : Module.Projective Rₛ (Rₛ ⊗[R] M) := Module.Projective.of_equiv hbc.equiv.symm
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  let πs := π.baseChange Rₛ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property πs LinearMap.id
    (LinearMap.lTensor_surjective Rₛ hπ)
  let h := TensorProduct.mk R Rₛ (Fin n → R) 1
  let g' := TensorProduct.mk R Rₛ M 1
  have : IsLocalizedModule (Submonoid.powers f) h :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) Rₛ h).mpr
      (TensorProduct.isBaseChange R (Fin n → R) Rₛ)
  have : IsLocalizedModule (Submonoid.powers f) g' :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) Rₛ g').mpr
      (TensorProduct.isBaseChange R M Rₛ)
  obtain ⟨ψ, s, hψ⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers f) h ((σ.restrictScalars R) ∘ₗ g')
  have key : g' ∘ₗ (π ∘ₗ ψ) = g' ∘ₗ (s • LinearMap.id) := by
    have e1 : g' ∘ₗ π = (πs.restrictScalars R) ∘ₗ h := by
      ext x
      simp [g', h, πs]
    rw [← LinearMap.comp_assoc, e1, LinearMap.comp_assoc, hψ, LinearMap.comp_smul,
      LinearMap.comp_smul, LinearMap.comp_id, ← LinearMap.comp_assoc,
      ← LinearMap.restrictScalars_comp, hσ]
    rfl
  obtain ⟨t, ht⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    (Submonoid.powers f) g' _ _ key
  obtain ⟨k, hk⟩ := (t * s).2
  refine ⟨k, mem_splittingIdeal_of_comp π ((t : R) • ψ) ?_⟩
  have hk' : f ^ k = (t : R) * s := hk
  rw [LinearMap.comp_smul, show (t : R) • (π ∘ₗ ψ) = t • (π ∘ₗ ψ) from rfl, ht, hk', mul_smul]
  rfl

/-- Endomorphisms of a finite module over a noetherian ring form a finite module. -/
lemma finite_end_of_isNoetherianRing [IsNoetherianRing R] [Module.Finite R M] :
    Module.Finite R (M →ₗ[R] M) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  refine Module.Finite.of_injective (LinearMap.lcomp R M π) fun φ φ' h ↦ ?_
  refine LinearMap.ext fun m ↦ ?_
  obtain ⟨e, rfl⟩ := hπ m
  exact LinearMap.congr_fun h e

/-- **The local step of the projectivity of algebraizations**: let `R` be noetherian and `M` a
finite `R`-module all of whose reductions `M / J^{k+1} M` have the lifting property over
`R / J^{k+1}`. Then the splitting ideal of `M` contains an element of `1 + J`. -/
theorem exists_mem_splittingIdeal_sub_one_mem [IsNoetherianRing R] [Module.Finite R M]
    (J : Ideal R)
    (hM : ∀ k : ℕ, LiftingProperty (J ^ (k + 1)) (M ⧸ (J ^ (k + 1) • ⊤ : Submodule R M))) :
    ∃ a ∈ splittingIdeal R M, a - 1 ∈ J := by
  have := finite_end_of_isNoetherianRing (R := R) (M := M)
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  let Φ : (M →ₗ[R] (Fin n → R)) →ₗ[R] (M →ₗ[R] M) := LinearMap.llcomp R M (Fin n → R) M π
  have hle : (⊤ : Submodule R (M →ₗ[R] M)) ≤ LinearMap.range Φ ⊔ J • ⊤ := by
    intro φ _
    obtain ⟨ψ, hψ⟩ := exists_sub_comp_mem_pow_smul π hπ hM 1 φ
    rw [pow_one] at hψ
    have : φ = π ∘ₗ ψ + (φ - π ∘ₗ ψ) := by abel
    rw [this]
    exact Submodule.add_mem_sup ⟨ψ, rfl⟩ hψ
  obtain ⟨r, hr, hrN⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (Module.Finite.fg_top) le_rfl hle
  obtain ⟨ψ, hψ⟩ : r • LinearMap.id ∈ LinearMap.range Φ :=
    hrN (Submodule.smul_mem_pointwise_smul _ r ⊤ Submodule.mem_top)
  exact ⟨r, mem_splittingIdeal_of_comp π ψ hψ, hr⟩

end SplittingIdeal

section SchemeLocalization

variable {X : Scheme.{u}} (B : X.Modules)

/-- `Γ(B, W)` as a `Γ(X, V)`-module through restriction, for `W ≤ V`. -/
abbrev resModule {V W : X.Opens} (h : W ≤ V) : Module Γ(X, V) Γ(B, W) :=
  Module.compHom _ (X.presheaf.map (homOfLE h).op).hom

/-- Restriction of sections `Γ(B, V) → Γ(B, W)` as a `Γ(X, V)`-linear map. -/
def resLinear {V W : X.Opens} (h : W ≤ V) :
    letI := resModule B h
    Γ(B, V) →ₗ[Γ(X, V)] Γ(B, W) :=
  letI := resModule B h
  { toFun := B.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun r s ↦ Scheme.Modules.map_smul B (homOfLE h) r s }

lemma resLinear_apply {V W : X.Opens} (h : W ≤ V) (s : Γ(B, V)) :
    resLinear B h s = B.presheaf.map (homOfLE h).op s := by
  unfold resLinear
  rfl

instance isScalarTower_basicOpen {V : X.Opens} (f : Γ(X, V)) :
    letI := resModule B (X.basicOpen_le f)
    IsScalarTower Γ(X, V) Γ(X, X.basicOpen f) Γ(B, X.basicOpen f) :=
  letI := resModule B (X.basicOpen_le f)
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- For `B` quasi-coherent and `V` affine, `Γ(B, V) → Γ(B, D(f))` is the localization at `f`. -/
lemma isLocalizedModule_resLinear [B.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)
    (f : Γ(X, V)) :
    letI := resModule B (X.basicOpen_le f)
    IsLocalizedModule (Submonoid.powers f) (resLinear B (X.basicOpen_le f)) := by
  let _ := resModule B (X.basicOpen_le f)
  have hW : X.basicOpen f ⊓ V = X.basicOpen f := inf_eq_left.mpr (X.basicOpen_le f)
  have h := B.isLocalizedModule_presheafInf_top hV f hW
  have h₁ : (⊤ : X.Opens) ⊓ V ≤ V := inf_le_right
  have h₂ : X.basicOpen f ≤ X.basicOpen f ⊓ V := le_inf le_rfl (X.basicOpen_le f)
  let e₁ : Γ(B, V) →ₗ[Γ(X, V)] (B.presheafInf V).obj (op ⊤) :=
    { toFun := fun s ↦ B.presheaf.map (homOfLE h₁).op s
      map_add' := fun _ _ ↦ map_add _ _ _
      map_smul' := fun r s ↦ by
        rw [Scheme.Modules.map_smul]
        rfl }
  let e₂ : (B.presheafInf V).obj (op (X.basicOpen f)) →ₗ[Γ(X, V)] Γ(B, X.basicOpen f) :=
    { toFun := fun s ↦ B.presheaf.map (homOfLE h₂).op s
      map_add' := fun _ _ ↦ map_add _ _ _
      map_smul' := fun r s ↦ by
        let s' : Γ(B, X.basicOpen f ⊓ V) := s
        change B.presheaf.map (homOfLE h₂).op
            (X.presheaf.map (homOfLE (inf_le_right : X.basicOpen f ⊓ V ≤ V)).op r • s') =
          X.presheaf.map (homOfLE (X.basicOpen_le f)).op r • B.presheaf.map (homOfLE h₂).op s'
        rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
        rfl }
  have he₁ : Function.Bijective e₁ := by
    have : IsIso (homOfLE h₁).op :=
      ⟨(homOfLE (le_inf le_top le_rfl : V ≤ ⊤ ⊓ V)).op, Subsingleton.elim _ _,
        Subsingleton.elim _ _⟩
    exact ConcreteCategory.bijective_of_isIso (B.presheaf.map (homOfLE h₁).op)
  have he₂ : Function.Bijective e₂ := by
    have : IsIso (homOfLE h₂).op :=
      ⟨(homOfLE hW.le).op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    exact ConcreteCategory.bijective_of_isIso (B.presheaf.map (homOfLE h₂).op)
  have heq : resLinear B (X.basicOpen_le f) =
      e₂ ∘ₗ TopCat.Presheaf.resₗ (B.presheafInf V) (B.presheafInf_map_smul V)
        (le_top : X.basicOpen f ≤ ⊤) ∘ₗ e₁ := by
    refine LinearMap.ext fun s ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, TopCat.Presheaf.resₗ_apply, resLinear_apply]
    change B.presheaf.map (homOfLE (X.basicOpen_le f)).op s = B.presheaf.map (homOfLE h₂).op
      (B.presheaf.map (homOfLE (inf_le_inf_right V (le_top : X.basicOpen f ≤ ⊤))).op
        (B.presheaf.map (homOfLE h₁).op s))
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← B.presheaf.map_comp,
      ← B.presheaf.map_comp]
    rfl
  rw [heq]
  refine (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers f) e₂ he₂).mpr ?_
  exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers f) e₁ he₁).mpr h

end SchemeLocalization

section Main

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A)

omit [IsNoetherianRing A] in
/-- A point of `f⁻¹ V(I)` lying in `V` lies in `D(a)` for every `a ∈ 1 + I Γ(X, V)`. -/
lemma mem_basicOpen_of_sub_one_mem {V : X.Opens} {x : X} (hxV : x ∈ V)
    (hx : x ∈ zeroLocusPreimage I f) {a : Γ(X, V)} (ha : a - 1 ∈ idealV f I V 1) :
    x ∈ X.basicOpen a := by
  rw [Scheme.mem_basicOpen X a x hxV]
  let φ := (X.presheaf.germ V x hxV).hom
  have hle : idealV f I V 1 ≤ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap φ := by
    rw [idealV, pow_one, Ideal.map_le_iff_le_comap]
    intro c hc
    change φ (structMapV f V c) ∈ IsLocalRing.maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := (Scheme.mem_basicOpen X _ x hxV).mpr hu
    rw [structMapV_eq_map, Scheme.basicOpen_res] at this
    exact hx c hc this.2
  have h1 : φ a - 1 ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    simpa only [Ideal.mem_comap, map_sub, map_one] using hle ha
  by_contra hna
  have h2 : φ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := hna
  have h3 := (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).sub_mem h2 h1
  rw [sub_sub_cancel] at h3
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h3)

variable [IsAdicComplete I A] [IsProper f]

/-- **Algebraizations of locally free adic systems are locally free** (EGA III 5.1.4 / Stacks 0DEM
for the flatness of algebraizations; proper case): let `A` be noetherian and `I`-adically complete,
`f : X ⟶ Spec A` proper and `B` coherent on `X` such that every `Γ(B / I^{n+1} B, V)` (`V` affine)
is projective over `Γ(X, V) / I^{n+1}`. Then `Γ(B, V)` is projective for every affine open `V`.

Proof: the set of points with an affine neighbourhood over which `B` has projective sections is
open, and contains `f⁻¹ V(I)` (Nakayama, `exists_mem_splittingIdeal_sub_one_mem`); its closed
complement misses `f⁻¹ V(I)`, hence is empty since `f` is closed and `I` lies in the Jacobson
radical of `A`. Projectivity over an arbitrary affine open then follows by covering it with basic
opens (`exists_pow_mem_splittingIdeal_of_projective`). -/
theorem projective_sections_of_liftingProperty_of_isProper (B : X.Modules) [B.IsCoherent]
    (hB : ∀ (n : ℕ) {V : X.Opens} (_ : IsAffineOpen V),
      LiftingProperty (idealV f I V 1 ^ (n + 1)) Γ(B.quotientIdealPow f I n, V))
    {V : X.Opens} (hV : IsAffineOpen V) : Module.Projective Γ(X, V) Γ(B, V) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : B.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : B.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  let G : Set X :=
    {x | ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ Module.Projective Γ(X, W) Γ(B, W)}
  have hGopen : IsOpen G := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hP⟩ ↦
    ⟨W, fun y hy ↦ ⟨W, hW, hy, hP⟩, W.isOpen, hxW⟩
  have hsplit : ∀ {W : X.Opens} (hW : IsAffineOpen W),
      ∃ a ∈ splittingIdeal Γ(X, W) Γ(B, W), a - 1 ∈ idealV f I W 1 := by
    intro W hW
    have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    have : Module.Finite Γ(X, W) Γ(B, W) := finite_sections_of_isFiniteType B hW
    exact exists_mem_splittingIdeal_sub_one_mem _ fun k ↦
      LiftingProperty.of_equiv (quotientIdealPowSectionsEquiv I f B k hW).symm (hB k hW)
  have hzero : zeroLocusPreimage I f ⊆ G := by
    intro x hx
    obtain ⟨W, hW, hxW, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨a, ha, ha1⟩ := hsplit hW
    refine ⟨X.basicOpen a, hW.basicOpen a, mem_basicOpen_of_sub_one_mem I f hxW hx ha1, ?_⟩
    let _ := resModule B (X.basicOpen_le a)
    have := isScalarTower_basicOpen B a
    have := isLocalizedModule_resLinear B hW a
    have := hW.isLocalization_basicOpen a
    exact projective_of_mem_splittingIdeal ha Γ(X, X.basicOpen a) (resLinear B (X.basicOpen_le a))
  have hG : G = Set.univ := by
    by_contra hne
    obtain ⟨x, hx, hx0⟩ := exists_mem_zeroLocusPreimage_of_isClosed I f
      (isClosed_compl_iff.mpr hGopen) (Set.nonempty_compl.mpr hne)
    exact hx (hzero hx0)
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : Module.Finite Γ(X, V) Γ(B, V) := finite_sections_of_isFiniteType B hV
  have : Module.FinitePresentation Γ(X, V) Γ(B, V) := Module.finitePresentation_of_finite _ _
  have hspan : Ideal.span (splittingIdeal Γ(X, V) Γ(B, V) : Set Γ(X, V)) = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro x hxV
    obtain ⟨W, hW, hxW, hP⟩ : x ∈ G := hG ▸ Set.mem_univ x
    obtain ⟨g, h, hgh, hx⟩ := exists_basicOpen_le_affine_inter hV hW x ⟨hxV, hxW⟩
    have hPh : Module.Projective Γ(X, X.basicOpen h) Γ(B, X.basicOpen h) := by
      let _ := resModule B (X.basicOpen_le h)
      have := isScalarTower_basicOpen B h
      have := isLocalizedModule_resLinear B hW h
      have := hW.isLocalization_basicOpen h
      exact Module.projective_of_isLocalizedModule (Submonoid.powers h)
        (resLinear B (X.basicOpen_le h))
    have hPg : Module.Projective Γ(X, X.basicOpen g) Γ(B, X.basicOpen g) := by
      rw [hgh]
      exact hPh
    let _ := resModule B (X.basicOpen_le g)
    have := isScalarTower_basicOpen B g
    have := isLocalizedModule_resLinear B hV g
    have := hV.isLocalization_basicOpen g
    obtain ⟨k, hk⟩ := exists_pow_mem_splittingIdeal_of_projective g Γ(X, X.basicOpen g)
      (resLinear B (X.basicOpen_le g))
    refine Opens.mem_iSup.mpr ⟨⟨g ^ k, hk⟩, ?_⟩
    change x ∈ X.basicOpen (g ^ k)
    rw [Scheme.mem_basicOpen X _ x hxV, map_pow]
    exact ((Scheme.mem_basicOpen X g x hxV).mp hx).pow k
  rw [Ideal.span_eq] at hspan
  exact projective_of_one_mem_splittingIdeal (hspan ▸ Submodule.mem_top)

end Main

end AlgebraicGeometry.CohomologyAux
