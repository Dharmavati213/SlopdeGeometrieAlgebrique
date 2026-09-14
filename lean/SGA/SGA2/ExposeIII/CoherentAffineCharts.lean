/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.AffineQuasicoherentHartogs

/-!
# Finite affine coefficients from genuine sheaf presentations

These bridges derive finite coefficient modules from finite generating
sections and local finite presentations of actual scheme modules.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

/-- A finite family of genuine generating sections of a quasi-coherent
affine module gives a finite coefficient module. -/
theorem affineModuleCoefficients_finite_of_generators
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (s : M.GeneratingSections) [s.IsFiniteType] :
    Module.Finite R (affineModuleCoefficients M) := by
  let φ : tilde (ModuleCat.of R (s.I →₀ R)) ⟶ tilde (affineModuleCoefficients M) :=
    (tildeFinsupp s.I).hom ≫ s.π ≫ (affineQuasicoherentPresentationIso M).inv
  let g : ModuleCat.of R (s.I →₀ R) ⟶ affineModuleCoefficients M :=
    (tilde.functor R).preimage φ
  have hφ : (tilde.functor R).map g = φ := (tilde.functor R).map_preimage φ
  have h_epi : Epi ((tilde.functor R).map g) := by
    rw [hφ]
    have : Epi (s.π : (SheafOfModules.free s.I : (Spec R).Modules) ⟶ M) := s.epi
    have : Epi ((tildeFinsupp (R := R) s.I).hom) := inferInstance
    have : Epi (affineQuasicoherentPresentationIso M).inv := inferInstance
    dsimp [φ]
    infer_instance
  have : Epi g := (tilde.functor R).epi_of_epi_map h_epi
  exact Module.Finite.of_surjective g.hom ((ModuleCat.epi_iff_surjective g).mp inferInstance)

/-- A finite presentation of an actual quasi-coherent affine sheaf yields
a finite coefficient module, without assuming any coefficient presentation. -/
theorem affineModuleCoefficients_finite_of_presentation
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (P : M.Presentation) [P.IsFinite] : Module.Finite R (affineModuleCoefficients M) :=
  affineModuleCoefficients_finite_of_generators M P.generators

/-- Transport of an actual finite presentation preserves the finite
generator and relation indexing types. -/
theorem presentation_map_isFinite {D E : Type u} [Category.{u} D] [Category.{u} E]
    {J : GrothendieckTopology D} {K : GrothendieckTopology E}
    {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} A} (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} A ⥤ SheafOfModules.{u} B)
    [PreservesColimitsOfSize.{u, u} F]
    (η : SheafOfModules.unit B ≅ F.obj (SheafOfModules.unit A)) :
    (P.map F η).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite P.generators.I)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite P.relations.I)⟩

/-- A finitely presented actual scheme module has a covering by affine
opens with actual finite presentations on each restricted module. -/
theorem exists_affineOpenCover_finitePresentation {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] :
    ∃ (ι : Type u) (U : ι → X.Opens)
      (P : ∀ i, (M.restrict (U i).ι).Presentation),
      IsOpenCover U ∧ ∀ i, IsAffineOpen (U i) ∧ (P i).IsFinite := by
  obtain ⟨Q, hQ⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  let := hQ
  choose κ hsub heq using fun i ↦ Opens.isBasis_iff_cover.mp X.isBasis_affineOpens (Q.X i)
  let ι := Σ i, κ i
  let U : ι → X.Opens := fun i => i.2
  have hpres (i : ι) : ∃ P : (M.restrict (U i).ι).Presentation, P.IsFinite := by
    let u := X.homOfLE (U := i.2) (V := Q.X i.1) (by simp [heq, le_sSup])
    have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor u) := inferInstance
    let F := (Scheme.Modules.overEquiv (Q.X i.1)).functor ⋙ Scheme.Modules.restrictFunctor u
    let iso : SheafOfModules.overFunctor X.ringCatSheaf _ ⋙ F ≅
        Scheme.Modules.restrictFunctor (Scheme.Opens.ι i.2.1) :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv _) _ ≪≫
        (Scheme.Modules.restrictFunctorComp _ _).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (by simp [u]))
    let P := (Q.presentation i.1).map F (Scheme.Modules.restrictUnitIso _).symm
    have : P.IsFinite := presentation_map_isFinite _ _ _
    exact ⟨SheafOfModules.Presentation.ofIsIso (iso.app M).hom P, inferInstance⟩
  choose P hP using hpres
  refine ⟨ι, U, P, ?_, fun i => ⟨hsub _ i.2.2, hP i⟩⟩
  have hc := Q.coversTop
  rw [Opens.coversTop_iff, IsOpenCover] at hc
  rw [IsOpenCover]
  change ⨆ i : Σ i, κ i, (i.2 : X.Opens) = ⊤
  rw [iSup_sigma, ← hc]
  refine iSup_congr fun i => ?_
  rw [heq i, sSup_eq_iSup']

/-- Restricting an actual finite presentation preserves its finiteness. -/
theorem presentationRestrict_isFinite {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {M : X.Modules} (P : M.Presentation) [P.IsFinite] :
    (Scheme.Modules.presentationRestrict f P).IsFinite := by
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor f) := inferInstance
  exact presentation_map_isFinite P (Scheme.Modules.restrictFunctor f)
    (Scheme.Modules.restrictUnitIso f).symm

/-- A finite presentation on an affine open supplies finite coefficients
for the canonical chart from its spectrum of sections. -/
theorem affineChart_coefficients_finite {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (P : (M.restrict U.ι).Presentation) [P.IsFinite] :
    Module.Finite Γ(X, U) (affineModuleCoefficients (M.restrict hU.fromSpec)) := by
  let Q := Scheme.Modules.presentationRestrict hU.isoSpec.inv P
  have : Q.IsFinite := presentationRestrict_isFinite _ _
  let e := ((Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app M).symm
  let Q' := SheafOfModules.Presentation.ofIsIso e.hom Q
  have : Q'.IsFinite := inferInstance
  exact affineModuleCoefficients_finite_of_presentation (M.restrict hU.fromSpec) Q'

/-- Finite affine coefficient charts exist inside every prescribed open
neighborhood of a finitely presented scheme module. -/
theorem exists_affine_mem_subset_finiteCoefficients {X : Scheme.{u}}
    (M : X.Modules) [M.IsFinitePresentation] {V : X.Opens} {x : X} (hx : x ∈ V) :
    ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧ U ≤ V ∧
      Module.Finite Γ(X, U) (affineModuleCoefficients (M.restrict hU.fromSpec)) := by
  obtain ⟨ι, W, P, hcov, hP⟩ := exists_affineOpenCover_finitePresentation M
  obtain ⟨i, hxi⟩ := hcov.exists_mem x
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (U := V ⊓ W i) ⟨hx, hxi⟩
  let g := X.homOfLE (U := U) (V := W i) (fun y hy => (hUV hy).2)
  have := (hP i).2
  let Q := Scheme.Modules.presentationRestrict g (P i)
  have : Q.IsFinite := presentationRestrict_isFinite _ _
  let e : (M.restrict (W i).ι).restrict g ≅ M.restrict U.ι :=
    ((Scheme.Modules.restrictFunctorComp g (W i).ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (by simp [g])).app M
  let Q' := SheafOfModules.Presentation.ofIsIso e.hom Q
  have : Q'.IsFinite := inferInstance
  exact ⟨U, hU, hxU, fun y hy => (hUV hy).1, affineChart_coefficients_finite M U hU Q'⟩

/-- Opens carrying finite actual affine coefficient modules form a basis;
this is derived from finite presentation, not assumed as a presentation of `M`. -/
theorem finiteAffineModuleOpens_isBasis {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] :
    Opens.IsBasis {U : X.Opens | ∃ hU : IsAffineOpen U,
      Module.Finite Γ(X, U) (affineModuleCoefficients (M.restrict hU.fromSpec))} := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro V x hx
  obtain ⟨U, hU, hxU, hUV, hfin⟩ := exists_affine_mem_subset_finiteCoefficients M hx
  exact ⟨U, ⟨hU, hfin⟩, hxU, hUV⟩

/-- An actual finitely presented scheme module admits a genuine affine
open cover with finite coefficient modules. -/
theorem exists_affineCover_finiteCoefficients {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] :
    ∃ 𝒰 : X.AffineOpenCover.{u}, ∀ i,
      Module.Finite (𝒰.X i) (affineModuleCoefficients (M.restrict (𝒰.f i))) := by
  obtain ⟨ι, U, P, hcov, hP⟩ := exists_affineOpenCover_finitePresentation M
  let 𝒰 := Scheme.AffineOpenCover.ofIsOpenCover U hcov (fun i => (hP i).1)
  refine ⟨𝒰, fun i => ?_⟩
  have := (hP i).2
  exact affineChart_coefficients_finite M (U i) (hP i).1 (P i)

/-- Finite presentation gives finite actual stalk modules, through a genuine
affine chart and the semilinear restriction comparison. -/
instance schemeModuleStalk_finite_of_finitePresentation {X : Scheme.{u}}
    (M : X.Modules) [M.IsFinitePresentation] (x : X) :
    Module.Finite (X.presheaf.stalk x) (schemeModuleStalk M x) := by
  obtain ⟨𝒰, h𝒰⟩ := exists_affineCover_finiteCoefficients M
  obtain ⟨p, hp⟩ := 𝒰.covers x
  let i := 𝒰.idx x
  have : Module.Finite (𝒰.X i) (affineModuleCoefficients (M.restrict (𝒰.f i))) := h𝒰 i
  have : Module.Finite ((Spec (𝒰.X i)).presheaf.stalk p)
      ((M.restrict (𝒰.f i)).presheaf.stalk p) :=
    affineQuasicoherentStalkFinite _ p
  have hf : Module.Finite (X.presheaf.stalk (𝒰.f i p)) (schemeModuleStalk M (𝒰.f i p)) :=
    Module.Finite.of_surjective (schemeModuleRestrictStalkSemilinearEquiv (𝒰.f i) M p).toLinearMap
      (schemeModuleRestrictStalkSemilinearEquiv (𝒰.f i) M p).surjective
  have hp' : 𝒰.f i p = x := hp
  exact hp' ▸ hf

end SGA.SGA2.ExposeIII
