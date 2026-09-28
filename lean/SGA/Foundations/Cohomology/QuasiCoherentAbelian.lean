/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.QuasiCoherentKernel
import SGA.Foundations.Cohomology.Coherent
import SGA.Foundations.QuasiCoherent.Cokernel

/-!
# Kernels, cokernels and images of quasi-coherent and coherent modules

* `CohomologyAux.isQuasicoherent_cokernel`, `isQuasicoherent_image`, `isQuasicoherent_kernel`:
  the quasi-coherent modules form an abelian subcategory (EGA I 2.2.2 (iii); Stacks Tag 01LA).
* `CohomologyAux.isCoherent_kernel`, `isCoherent_cokernel`, `isCoherent_image`: on a locally
  noetherian scheme, so do the coherent (= quasi-coherent of finite type) modules (EGA I 1.5.1).
* `CohomologyAux.FiniteCohomology`: all cohomology modules are finitely generated over a
  noetherian ring `R` acting through a ring map `R → Γ(X, 𝒪_X)`; this property satisfies
  "two out of three" in short exact sequences (`FiniteCohomology.of_shortExact₂` etc.), by the
  long exact cohomology sequence.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

/-- Cokernels of quasi-coherent modules on an affine scheme are quasi-coherent (alias of the
canonical `Scheme.Modules.isQuasicoherent_cokernel_Spec`). -/
alias isQuasicoherent_cokernel_spec := Scheme.Modules.isQuasicoherent_cokernel_Spec

variable {X : Scheme.{u}}

/-- Quasi-coherence can be checked on the restrictions to `Spec Γ(X, V)` for the affine opens
`V`. -/
lemma isQuasicoherent_of_restrict_fromSpec (M : X.Modules)
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U), (M.restrict hU.fromSpec).IsQuasicoherent) :
    M.IsQuasicoherent := by
  refine isQuasicoherent_of_restrict_cover M (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X) fun U ↦ ?_
  have hU : IsAffineOpen U.1 := U.2
  have := h U.1 hU
  let iso : (M.restrict hU.fromSpec).restrict hU.isoSpec.hom ≅ M.restrict U.1.ι :=
    ((Scheme.Modules.restrictFunctorComp _ _).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec).app M
  have : ((M.restrict hU.fromSpec).restrict hU.isoSpec.hom).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor hU.isoSpec.hom _
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso iso this

/-- **Cokernels of morphisms of quasi-coherent modules are quasi-coherent** (EGA I 2.2.2 (iii);
Stacks Tag 01LA). Alias of the canonical `Scheme.Modules.isQuasicoherent_cokernel`
(`SGA.Foundations.QuasiCoherent.Cokernel`). -/
alias isQuasicoherent_cokernel := Scheme.Modules.isQuasicoherent_cokernel

/-- **Images of morphisms of quasi-coherent modules are quasi-coherent.** -/
theorem isQuasicoherent_image {E F : X.Modules} [E.IsQuasicoherent] [F.IsQuasicoherent]
    (φ : E ⟶ F) : (Abelian.image φ).IsQuasicoherent := by
  have : (ShortComplex.kernelSequence (cokernel.π φ)).X₂.IsQuasicoherent := ‹F.IsQuasicoherent›
  have : (ShortComplex.kernelSequence (cokernel.π φ)).X₃.IsQuasicoherent :=
    isQuasicoherent_cokernel φ
  exact isQuasicoherent_X₁_of_shortExact (shortExact_kernelSequence (cokernel.π φ))

/-- The kernel of `φ` is the kernel of the epimorphism onto its image. -/
noncomputable def kernelIsoKernelFactorThruImage {E F : X.Modules} (φ : E ⟶ F) :
    kernel φ ≅ kernel (Abelian.factorThruImage φ) :=
  kernelIsoOfEq (Abelian.image.fac φ).symm ≪≫ kernelCompMono _ _

/-- **Kernels of morphisms of quasi-coherent modules are quasi-coherent** (EGA I 2.2.2 (iii);
Stacks Tag 01LA). -/
theorem isQuasicoherent_kernel {E F : X.Modules} [E.IsQuasicoherent] [F.IsQuasicoherent]
    (φ : E ⟶ F) : (kernel φ).IsQuasicoherent := by
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₂.IsQuasicoherent :=
    ‹E.IsQuasicoherent›
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₃.IsQuasicoherent :=
    isQuasicoherent_image φ
  have := isQuasicoherent_X₁_of_shortExact
    (shortExact_kernelSequence (Abelian.factorThruImage φ))
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (kernelIsoKernelFactorThruImage φ).symm this

section Coherent

variable [IsLocallyNoetherian X]

/-- Sections of a quasi-coherent submodule of a coherent module over affines are finitely
generated (on a locally noetherian scheme). -/
lemma isCoherent_X₁_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsCoherent] : S.X₁.IsCoherent where
  isQuasicoherent := inferInstance
  isFiniteType := by
    have := (Scheme.Modules.IsCoherent.isQuasicoherent : S.X₂.IsQuasicoherent)
    have := (Scheme.Modules.IsCoherent.isFiniteType : S.X₂.IsFiniteType)
    refine isFiniteType_of_finite_sections S.X₁ (fun U : X.affineOpens ↦ U.1)
      (iSup_affineOpens_eq_top X) (fun U ↦ U.2) fun U ↦ ?_
    have := finite_sections_of_isFiniteType S.X₂ U.2
    have := IsLocallyNoetherian.component_noetherian U
    have : _root_.IsNoetherian Γ(X, U.1) Γ(S.X₂, U.1) :=
      isNoetherian_of_isNoetherianRing_of_finite _ _
    exact Module.Finite.of_injective (appLinearMap S.f U.1) (app_injective_of_shortExact hS _)

omit [IsLocallyNoetherian X] in
/-- Quotients of coherent modules by quasi-coherent submodules are coherent. -/
lemma isCoherent_X₃_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsCoherent] : S.X₃.IsCoherent where
  isQuasicoherent := by
    have := (Scheme.Modules.IsCoherent.isQuasicoherent : S.X₂.IsQuasicoherent)
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((hS.gIsCokernel).coconePointUniqueUpToIso (colimit.isColimit _)).symm
      (isQuasicoherent_cokernel S.f)
  isFiniteType := by
    have := (Scheme.Modules.IsCoherent.isQuasicoherent : S.X₂.IsQuasicoherent)
    have := (Scheme.Modules.IsCoherent.isFiniteType : S.X₂.IsFiniteType)
    have hq : S.X₃.IsQuasicoherent := (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((hS.gIsCokernel).coconePointUniqueUpToIso (colimit.isColimit _)).symm
      (isQuasicoherent_cokernel S.f)
    refine isFiniteType_of_finite_sections S.X₃ (fun U : X.affineOpens ↦ U.1)
      (iSup_affineOpens_eq_top X) (fun U ↦ U.2) fun U ↦ ?_
    have := finite_sections_of_isFiniteType S.X₂ U.2
    have hsurj := TopCat.Sheaf.surjective_app_of_subsingleton_H'_one
      (Scheme.Modules.shortExact_abShortComplex hS) U.1
      (S.X₁.H'_subsingleton_of_isAffineOpen U.2 0)
    exact Module.Finite.of_surjective (appLinearMap S.g U.1) hsurj

end Coherent

section FiniteCohomology

variable {R : Type*} [CommRing R] (ρ : R →+* Γ(X, ⊤))

/-- All the cohomology modules of `M` are finitely generated `R`-modules, for the action of `R`
through `ρ : R → Γ(X, 𝒪_X)`. -/
def FiniteCohomology (M : X.Modules) : Prop :=
  ∀ p : ℕ, letI := Module.compHom (M.H p) ρ
    Module.Finite R (M.H p)

variable {ρ}

/-- `H'.map` as an `R`-linear map. -/
noncomputable def H'.mapₗ {M N : X.Modules} (φ : M ⟶ N) (p : ℕ) :
    letI := Module.compHom (M.H p) ρ
    letI := Module.compHom (N.H p) ρ
    M.H p →ₗ[R] N.H p :=
  letI := Module.compHom (M.H p) ρ
  letI := Module.compHom (N.H p) ρ
  { toFun := Scheme.Modules.H'.map φ p ⊤
    map_add' := map_add _
    map_smul' := fun r x ↦ (Scheme.Modules.H'.map φ p ⊤).map_smul (ρ r) x }

/-- The connecting map as an `R`-linear map. -/
noncomputable def H'.δₗ {S : ShortComplex X.Modules} (hS : S.ShortExact) (p : ℕ) :
    letI := Module.compHom (S.X₃.H p) ρ
    letI := Module.compHom (S.X₁.H (p + 1)) ρ
    S.X₃.H p →ₗ[R] S.X₁.H (p + 1) :=
  letI := Module.compHom (S.X₃.H p) ρ
  letI := Module.compHom (S.X₁.H (p + 1)) ρ
  { toFun := Scheme.Modules.H'.δ hS p ⊤
    map_add' := map_add _
    map_smul' := fun r x ↦ (Scheme.Modules.H'.δ hS p ⊤).map_smul (ρ r) x }

variable [IsNoetherianRing R] {S : ShortComplex X.Modules} (hS : S.ShortExact)
include hS

lemma FiniteCohomology.of_shortExact₂ (h₁ : FiniteCohomology ρ S.X₁)
    (h₃ : FiniteCohomology ρ S.X₃) : FiniteCohomology ρ S.X₂ := fun p ↦ by
  let _ := Module.compHom (S.X₁.H p) ρ
  let _ := Module.compHom (S.X₂.H p) ρ
  let _ := Module.compHom (S.X₃.H p) ρ
  have := h₁ p
  have := h₃ p
  exact finite_of_exact (H'.mapₗ (ρ := ρ) S.f p) (H'.mapₗ (ρ := ρ) S.g p)
    (Scheme.Modules.H'.exact_map_map hS p ⊤)

lemma FiniteCohomology.of_shortExact₃ (h₁ : FiniteCohomology ρ S.X₁)
    (h₂ : FiniteCohomology ρ S.X₂) : FiniteCohomology ρ S.X₃ := fun p ↦ by
  let _ := Module.compHom (S.X₁.H (p + 1)) ρ
  let _ := Module.compHom (S.X₂.H p) ρ
  let _ := Module.compHom (S.X₃.H p) ρ
  have := h₁ (p + 1)
  have := h₂ p
  exact finite_of_exact (H'.mapₗ (ρ := ρ) S.g p) (H'.δₗ (ρ := ρ) hS p)
    (Scheme.Modules.H'.exact_map_δ hS p ⊤)

lemma FiniteCohomology.of_shortExact₁ (h₂ : FiniteCohomology ρ S.X₂)
    (h₃ : FiniteCohomology ρ S.X₃) : FiniteCohomology ρ S.X₁ := fun p ↦ by
  cases p with
  | zero =>
    let _ := Module.compHom (S.X₁.H 0) ρ
    let _ := Module.compHom (S.X₂.H 0) ρ
    have := h₂ 0
    have hinj : Function.Injective (H'.mapₗ (ρ := ρ) S.f 0) := by
      intro x y hxy
      have e (z : S.X₁.H 0) : Scheme.Modules.H.equiv₀ S.X₂ (Scheme.Modules.H'.map S.f 0 ⊤ z) =
          S.f.app ⊤ (Scheme.Modules.H.equiv₀ S.X₁ z) :=
        CategoryTheory.Sheaf.H'.equiv₀_naturality (Scheme.Modules.Hom.toAbSheaf S.f) z
      have h := congrArg (Scheme.Modules.H.equiv₀ S.X₂) hxy
      change Scheme.Modules.H.equiv₀ S.X₂ (Scheme.Modules.H'.map S.f 0 ⊤ x) =
        Scheme.Modules.H.equiv₀ S.X₂ (Scheme.Modules.H'.map S.f 0 ⊤ y) at h
      rw [e, e] at h
      exact (Scheme.Modules.H.equiv₀ S.X₁).injective (app_injective_of_shortExact hS ⊤ h)
    exact Module.Finite.of_injective (H'.mapₗ (ρ := ρ) S.f 0) hinj
  | succ p =>
    let _ := Module.compHom (S.X₁.H (p + 1)) ρ
    let _ := Module.compHom (S.X₂.H (p + 1)) ρ
    let _ := Module.compHom (S.X₃.H p) ρ
    have := h₂ (p + 1)
    have := h₃ p
    exact finite_of_exact (H'.δₗ (ρ := ρ) hS p) (H'.mapₗ (ρ := ρ) S.f (p + 1))
      (Scheme.Modules.H'.exact_δ_map hS p ⊤)

end FiniteCohomology

end AlgebraicGeometry.CohomologyAux
