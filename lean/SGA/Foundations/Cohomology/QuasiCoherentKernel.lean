/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.QuasiCoherentLocal
import SGA.Foundations.Cohomology.Cartan
import Mathlib.Topology.Sheaves.Module

/-!
# Quasi-coherence from localizations, and kernels of quasi-coherent modules

An `𝒪_X`-module whose sections over the basic opens `D(c)` of the members `V` of an affine open
cover are the localizations `Γ(V, M)_c` is quasi-coherent (EGA I 1.4.1, the converse of Stage I's
`Scheme.Modules.isLocalizedModule_presheafInf_top`). Consequently the kernel of an epimorphism of
quasi-coherent modules is quasi-coherent (EGA I 1.3.8, 1.4.2; the category of quasi-coherent
modules is abelian).
-/

universe u

open CategoryTheory TopologicalSpace Opposite Limits

namespace AlgebraicGeometry.CohomologyAux

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Transport back from an open subscheme preserves quasi-coherence (after SGA 2, VI). -/
lemma overEquivInverse_isQuasicoherent (U : X.Opens) (M : U.toScheme.Modules)
    [M.IsQuasicoherent] : ((Scheme.Modules.overEquiv U).inverse.obj M).IsQuasicoherent := by
  let := U.instIsDenseSubsiteOverSubtypeMemOverGrothendieckTopologyFunctorOverEquivalence
  let : U.overEquivalence.functor.IsContinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) :=
    inferInstanceAs (U.overEquivalence.functor.IsContinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U.carrier))
  let (V : Over U) :
      (Over.post (X := V) U.overEquivalence.functor).IsContinuous
        (((Opens.grothendieckTopology X).over U).over V)
        ((Opens.grothendieckTopology ↥U).over (U.overEquivalence.functor.obj V)) :=
    Functor.isContinuous_iff_coverPreserving.mpr
      ((CoverPreserving.of_isContinuous U.overEquivalence.functor
        ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U)).overPost V)
  exact SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    U.overEquivalence.functor (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Quasi-coherence can be checked on the restrictions to the members of an open cover. -/
lemma isQuasicoherent_of_restrict_cover (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (hM : ∀ i, (M.restrict (U i).ι).IsQuasicoherent) :
    M.IsQuasicoherent := by
  let (i : ι) : (M.over (U i)).IsQuasicoherent := by
    let := hM i
    let e := (Scheme.Modules.overEquiv (U i)).inverse.mapIso
      ((Scheme.Modules.overFunctorEquiv (U i)).app M).symm ≪≫
        ((Scheme.Modules.overEquiv (U i)).unitIso.app (M.over (U i))).symm
    exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over (U i))).prop_of_iso e
      (overEquivInverse_isQuasicoherent (U i) (M.restrict (U i).ι))
  apply SheafOfModules.IsQuasicoherent.of_coversTop M U
  rw [Opens.coversTop_iff]
  exact hU

/-- **Quasi-coherence from localizations** (EGA I 1.4.1): a module whose sections over the basic
opens of each member `V` of an affine open cover are the localizations of its sections over `V`
is quasi-coherent. -/
theorem isQuasicoherent_of_isLocalizedModule (M : X.Modules) {ι : Type u} (V : ι → X.Opens)
    (hV : ⨆ i, V i = ⊤) (hVa : ∀ i, IsAffineOpen (V i))
    (hloc : ∀ i (c : Γ(X, V i)), IsLocalizedModule.Away c
      (TopCat.Presheaf.resₗ (M.presheafInf (V i)) (M.presheafInf_map_smul (V i))
        (le_top : X.basicOpen c ≤ ⊤))) : M.IsQuasicoherent := by
  refine isQuasicoherent_of_restrict_cover M V hV fun i ↦ ?_
  have := M.isQuasicoherent_restrict_fromSpec_of_isLocalizedModule (hVa i) (hloc i)
  let iso : (M.restrict (hVa i).fromSpec).restrict (hVa i).isoSpec.hom ≅ M.restrict (V i).ι :=
    ((Scheme.Modules.restrictFunctorComp _ _).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (hVa i).isoSpec_hom_fromSpec).app M
  have : ((M.restrict (hVa i).fromSpec).restrict (hVa i).isoSpec.hom).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor (hVa i).isoSpec.hom _
  exact (SheafOfModules.isQuasicoherent (V i).toScheme.ringCatSheaf).prop_of_iso iso this

section ShortExact

variable {S : ShortComplex X.Modules} (hS : S.ShortExact)
include hS

/-- In a short exact sequence of `𝒪_X`-modules, the first map is injective on sections. -/
lemma app_injective_of_shortExact (U : X.Opens) : Function.Injective (S.f.app U) := by
  have := (Scheme.Modules.shortExact_abShortComplex hS).mono_f
  exact CategoryTheory.Sheaf.app_injective_of_mono (Scheme.Modules.Hom.toAbSheaf S.f) U

/-- In a short exact sequence of `𝒪_X`-modules, sections are left exact. -/
lemma exists_app_eq_of_shortExact (U : X.Opens) (t : Γ(S.X₂, U)) (ht : S.g.app U t = 0) :
    ∃ s, S.f.app U s = t := by
  have h := Scheme.Modules.shortExact_abShortComplex hS
  have := h.mono_f
  exact CategoryTheory.Sheaf.exists_app_eq_of_exact h.exact t ht

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0` with `M₂`, `M₃` quasi-coherent, the sections
of `M₁` over a basic open of an affine are localizations. -/
lemma isLocalizedModule_X₁_of_shortExact [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) (c : Γ(X, V)) :
    IsLocalizedModule.Away c (TopCat.Presheaf.resₗ (S.X₁.presheafInf V)
      (S.X₁.presheafInf_map_smul V) (le_top : X.basicOpen c ≤ ⊤)) := by
  have hW : X.basicOpen c ⊓ V = X.basicOpen c := inf_eq_left.mpr (X.basicOpen_le c)
  have hE := S.X₂.isLocalizedModule_presheafInf_top hV c hW
  have hF := S.X₃.isLocalizedModule_presheafInf_top hV c hW
  have hinj := app_injective_of_shortExact hS
  have hunit : IsUnit (X.presheaf.map
      (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op c) := by
    rw [← CohomologyAux.presheaf_map_map (X.basicOpen_le c)
      (inf_le_left : X.basicOpen c ⊓ V ≤ X.basicOpen c)]
    exact (X.toRingedSpace.isUnit_res_basicOpen c).map (X.presheaf.map _).hom
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ (fun y ↦ ?_) (fun x hx ↦ ?_)
  · rw [Module.End.isUnit_iff]
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
    · change X.presheaf.map (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op c •
          (@id Γ(S.X₁, X.basicOpen c ⊓ V) x) =
        X.presheaf.map (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op c •
          (@id Γ(S.X₁, X.basicOpen c ⊓ V) y) at hxy
      have := congrArg (hunit.unit⁻¹.1 • ·) hxy
      simp only [smul_smul, IsUnit.val_inv_mul, one_smul] at this
      exact this
    · refine ⟨hunit.unit⁻¹.1 • (@id Γ(S.X₁, X.basicOpen c ⊓ V) y), ?_⟩
      change X.presheaf.map (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op c •
        (hunit.unit⁻¹.1 • (@id Γ(S.X₁, X.basicOpen c ⊓ V) y)) = y
      rw [smul_smul, IsUnit.mul_val_inv, one_smul]
      rfl
  · -- surjectivity: lift `y` to `M₂`, correct by a power of `c`, and descend again
    obtain ⟨n, e, he⟩ := IsLocalizedModule.Away.surj
      (TopCat.Presheaf.resₗ (S.X₂.presheafInf V) (S.X₂.presheafInf_map_smul V)
        (le_top : X.basicOpen c ≤ ⊤)) c
      (S.f.app (X.basicOpen c ⊓ V) y : (S.X₂.presheafInf V).obj (op (X.basicOpen c)))
    change X.presheaf.map (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op (c ^ n) •
        S.f.app (X.basicOpen c ⊓ V) y =
      S.X₂.presheaf.map (homOfLE (inf_le_inf_right V le_top :
        X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op (@id Γ(S.X₂, ⊤ ⊓ V) e) at he
    have hge : TopCat.Presheaf.resₗ (S.X₃.presheafInf V) (S.X₃.presheafInf_map_smul V)
        (le_top : X.basicOpen c ≤ ⊤) (S.g.app (⊤ ⊓ V) e) =
        TopCat.Presheaf.resₗ (S.X₃.presheafInf V) (S.X₃.presheafInf_map_smul V)
        (le_top : X.basicOpen c ≤ ⊤) 0 := by
      change S.X₃.presheaf.map (homOfLE (inf_le_inf_right V le_top :
          X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op (S.g.app (⊤ ⊓ V) (@id Γ(S.X₂, ⊤ ⊓ V) e)) =
        S.X₃.presheaf.map (homOfLE (inf_le_inf_right V le_top :
          X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op 0
      have hfg (z : Γ(S.X₁, X.basicOpen c ⊓ V)) :
          S.g.app (X.basicOpen c ⊓ V) (S.f.app (X.basicOpen c ⊓ V) z) = 0 := by
        change (S.f ≫ S.g).app _ z = 0
        rw [S.zero]
        rfl
      rw [map_zero, ← CohomologyAux.hom_app_presheaf_map, ← he, Scheme.Modules.Hom.app_smul]
      exact (congrArg (fun z ↦ X.presheaf.map (homOfLE (inf_le_right :
        X.basicOpen c ⊓ V ≤ V)).op (c ^ n) • z) (hfg y)).trans (smul_zero _)
    obtain ⟨j, hj⟩ := IsLocalizedModule.Away.exists_of_eq c hge
    rw [smul_zero] at hj
    change X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op (c ^ j) •
      S.g.app (⊤ ⊓ V) (@id Γ(S.X₂, ⊤ ⊓ V) e) = 0 at hj
    obtain ⟨x, hx⟩ := exists_app_eq_of_shortExact hS (⊤ ⊓ V)
      (X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op (c ^ j) •
        (@id Γ(S.X₂, ⊤ ⊓ V) e)) (by rw [Scheme.Modules.Hom.app_smul]; exact hj)
    refine ⟨n + j, x, hinj (X.basicOpen c ⊓ V) ?_⟩
    change S.f.app _ (X.presheaf.map (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op
        (c ^ (n + j)) • (@id Γ(S.X₁, X.basicOpen c ⊓ V) y)) =
      S.f.app _ (S.X₁.presheaf.map (homOfLE (inf_le_inf_right V le_top :
        X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op x)
    rw [Scheme.Modules.Hom.app_smul, CohomologyAux.hom_app_presheaf_map, hx,
      Scheme.Modules.map_smul, ← he, smul_smul, CohomologyAux.presheaf_map_map, ← map_mul,
      pow_add, mul_comm]
    rfl
  · -- injectivity: a section of `M₁` vanishing on `D(c)` is killed by a power of `c`
    have h0 : TopCat.Presheaf.resₗ (S.X₂.presheafInf V) (S.X₂.presheafInf_map_smul V)
        (le_top : X.basicOpen c ≤ ⊤) (S.f.app (⊤ ⊓ V) x) =
        TopCat.Presheaf.resₗ (S.X₂.presheafInf V) (S.X₂.presheafInf_map_smul V)
        (le_top : X.basicOpen c ≤ ⊤) 0 := by
      change S.X₂.presheaf.map (homOfLE (inf_le_inf_right V le_top :
          X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op (S.f.app (⊤ ⊓ V) (@id Γ(S.X₁, ⊤ ⊓ V) x)) =
        S.X₂.presheaf.map (homOfLE (inf_le_inf_right V le_top :
          X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op 0
      rw [map_zero, ← CohomologyAux.hom_app_presheaf_map]
      change S.f.app _ (TopCat.Presheaf.resₗ (S.X₁.presheafInf V)
        (S.X₁.presheafInf_map_smul V) (le_top : X.basicOpen c ≤ ⊤) x) = 0
      rw [hx]
      exact map_zero (ConcreteCategory.hom (S.f.app (X.basicOpen c ⊓ V)))
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq c h0
    rw [smul_zero] at hn
    refine ⟨n, hinj (⊤ ⊓ V) ?_⟩
    change S.f.app _ (X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op (c ^ n) •
      (@id Γ(S.X₁, ⊤ ⊓ V) x)) = S.f.app _ 0
    rw [Scheme.Modules.Hom.app_smul, map_zero]
    exact hn

/-- **The kernel of an epimorphism of quasi-coherent modules is quasi-coherent** (EGA I 1.3.8,
1.4.2): in a short exact sequence `0 → M₁ → M₂ → M₃ → 0` with `M₂`, `M₃` quasi-coherent, `M₁` is
quasi-coherent. -/
theorem isQuasicoherent_X₁_of_shortExact [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₁.IsQuasicoherent :=
  isQuasicoherent_of_isLocalizedModule S.X₁ (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X) (fun U ↦ U.2) fun U c ↦
      isLocalizedModule_X₁_of_shortExact hS U.2 c

end ShortExact

end AlgebraicGeometry.CohomologyAux
