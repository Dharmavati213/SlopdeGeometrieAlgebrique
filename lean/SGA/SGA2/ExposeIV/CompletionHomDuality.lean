/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.CompletionSubmodules
import SGA.SGA2.ExposeIV.ModuleBidualConverse

/-! # Actual Hom and canonical biduality under completion

Restriction of scalars on supported completed-ring modules is fully faithful
by the proved tensor/restriction equivalence. Consequently the original
linear Hom modules agree, by the actual restriction map. For finite source
modules this compares the actual double Hom and its canonical evaluation.
There is no noetherianity assumption on the completed ring.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite ModuleCat
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R)

/-- Actual restriction of a completed-ring linear morphism, as a linear
map between the original Hom modules. -/
def completionHomRestriction (H M : ModuleCat.{u} (AdicCompletion J R)) :
    (restrictScalars (algebraMap R (AdicCompletion J R))).obj
        ((moduleHomDual H).obj (op M)) ⟶
      (moduleHomDual ((restrictScalars (algebraMap R (AdicCompletion J R))).obj H)).obj
        (op ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M)) :=
  ModuleCat.ofHom
    (X := (restrictScalars (algebraMap R (AdicCompletion J R))).obj
      ((moduleHomDual H).obj (op M)))
    (Y := (moduleHomDual ((restrictScalars (algebraMap R (AdicCompletion J R))).obj H)).obj
      (op ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M)))
    { toFun := (restrictScalars (algebraMap R (AdicCompletion J R))).map
      map_add' g h := by apply ModuleCat.hom_ext; ext x; rfl
      map_smul' a g := by apply ModuleCat.hom_ext; ext x; rfl }

omit [IsNoetherianRing R] in
/-- The comparison is literally the same underlying function on morphisms. -/
@[simp]
theorem completionHomRestriction_apply (H M : ModuleCat.{u} (AdicCompletion J R))
    (g : M ⟶ H) (x : M) : ModuleCat.Hom.hom (completionHomRestriction J H M g) x = g x := rfl

/-- Every original-ring linear morphism between supported completed-ring
modules is linear for the existing completed-ring actions. -/
theorem completionHomRestriction_bijective (H M : ModuleCat.{u} (AdicCompletion J R))
    (hH : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) H)
    (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M) :
    Function.Bijective (completionHomRestriction J H M) := by
  constructor
  · intro g h he
    apply ModuleCat.hom_ext
    ext x
    exact congrArg
      (fun f : (restrictScalars (algebraMap R (AdicCompletion J R))).obj M ⟶
        (restrictScalars (algebraMap R (AdicCompletion J R))).obj H => ModuleCat.Hom.hom f x) he
  · intro g
    let F := (supportedCompletionEquivalence J).inverse
    let M' : SupportedModuleCat (J.map (algebraMap R (AdicCompletion J R))) := ⟨M, hM⟩
    let H' : SupportedModuleCat (J.map (algebraMap R (AdicCompletion J R))) := ⟨H, hH⟩
    let g' : F.obj M' ⟶ F.obj H' := ObjectProperty.homMk g
    obtain ⟨k, hk⟩ := F.map_surjective g'
    exact ⟨k.hom, congrArg (fun t : F.obj M' ⟶ F.obj H' => t.hom) hk⟩

/-- The actual restriction map gives the natural comparison of linear Hom modules. -/
def completionHomDualIso (H M : ModuleCat.{u} (AdicCompletion J R))
    (hH : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) H)
    (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M) :
    (restrictScalars (algebraMap R (AdicCompletion J R))).obj
        ((moduleHomDual H).obj (op M)) ≅
      (moduleHomDual ((restrictScalars (algebraMap R (AdicCompletion J R))).obj H)).obj
        (op ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M)) := by
  letI := (ConcreteCategory.isIso_iff_bijective (completionHomRestriction J H M)).mpr
    (completionHomRestriction_bijective J H M hH hM)
  exact asIso (completionHomRestriction J H M)

@[simp]
theorem completionHomDualIso_hom_apply (H M : ModuleCat.{u} (AdicCompletion J R))
    (hH : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) H)
    (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M)
    (g : M ⟶ H) (x : M) :
    ModuleCat.Hom.hom ((completionHomDualIso J H M hH hM).hom g) x = g x := rfl

/-- Extending a restricted morphism changes none of its actual values. -/
@[simp]
theorem completionHomDualIso_inv_apply (H M : ModuleCat.{u} (AdicCompletion J R))
    (hH : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) H)
    (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M)
    (g : (restrictScalars (algebraMap R (AdicCompletion J R))).obj M ⟶
      (restrictScalars (algebraMap R (AdicCompletion J R))).obj H) (x : M) :
    ModuleCat.Hom.hom ((completionHomDualIso J H M hH hM).inv g) x = g x := by
  exact congrArg
    (fun k : (restrictScalars (algebraMap R (AdicCompletion J R))).obj M ⟶
      (restrictScalars (algebraMap R (AdicCompletion J R))).obj H => ModuleCat.Hom.hom k x)
    (ConcreteCategory.congr_hom (completionHomDualIso J H M hH hM).inv_hom_id g)

/-- Naturality is literal precomposition on both original Hom modules. -/
@[reassoc]
theorem completionHomDualIso_naturality
    (H M N : ModuleCat.{u} (AdicCompletion J R))
    (hH : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) H)
    (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M)
    (hN : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) N)
    (f : M ⟶ N) :
    (restrictScalars (algebraMap R (AdicCompletion J R))).map ((moduleHomDual H).map f.op) ≫
        (completionHomDualIso J H M hH hM).hom =
      (completionHomDualIso J H N hH hN).hom ≫
        (moduleHomDual ((restrictScalars (algebraMap R (AdicCompletion J R))).obj H)).map
          ((restrictScalars (algebraMap R (AdicCompletion J R))).map f).op := by
  apply ModuleCat.hom_ext
  ext g
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- Naturality in the coefficient is literal postcomposition. Together with
precomposition naturality this compares the actual Hom bifunctors. -/
@[reassoc]
theorem completionHomDualIso_coefficient_naturality
    (H K M : ModuleCat.{u} (AdicCompletion J R))
    (hH : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) H)
    (hK : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) K)
    (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M)
    (f : H ⟶ K) :
    (restrictScalars (algebraMap R (AdicCompletion J R))).map
        (((linearYoneda (AdicCompletion J R) (ModuleCat (AdicCompletion J R))).map f).app (op M)) ≫
        (completionHomDualIso J K M hK hM).hom =
      (completionHomDualIso J H M hH hM).hom ≫
        (((linearYoneda R (ModuleCat R)).map
          ((restrictScalars (algebraMap R (AdicCompletion J R))).map f)).app
            (op ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M))) := by
  apply ModuleCat.hom_ext
  ext g
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- For a finite supported source, even an infinite original Hom dual remains
supported. A power of the finite support ideal annihilates the source and hence
the dual; no finiteness of that dual is assumed. -/
theorem completionHomDual_supported (H M : ModuleCat.{u} (AdicCompletion J R))
    [Module.Finite (AdicCompletion J R) M]
    (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M) :
    supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R)))
      ((moduleHomDual H).obj (op M)) := by
  let K := J.map (algebraMap R (AdicCompletion J R))
  obtain ⟨n, hn⟩ := finite_support_pow_annihilator_of_fg K
    (J.fg_of_isNoetherianRing.map _) M hM
  apply support_subset_zeroLocus_of_powerTorsion_eq_top
  apply top_unique
  intro x _
  refine (mem_powerTorsion_iff K ((moduleHomDual H).obj (op M)) x).mpr ⟨n, ?_⟩
  intro a ha
  exact Module.mem_annihilator.mp ((moduleHomDual_annihilator_le H M) (hn ha)) x

/-- Restriction compares the original completed-ring bidual with the original
base-ring bidual, for a finite supported source and supported coefficients. -/
def completionHomBidualIso (H M : ModuleCat.{u} (AdicCompletion J R))
    [Module.Finite (AdicCompletion J R) M]
    (hH : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) H)
    (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M) :
    (restrictScalars (algebraMap R (AdicCompletion J R))).obj ((moduleHomBidual H).obj M) ≅
      (moduleHomBidual ((restrictScalars (algebraMap R (AdicCompletion J R))).obj H)).obj
        ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M) :=
  completionHomDualIso J H ((moduleHomDual H).obj (op M)) hH
      (completionHomDual_supported J H M hM) ≪≫
    (moduleHomDual ((restrictScalars (algebraMap R (AdicCompletion J R))).obj H)).mapIso
      (completionHomDualIso J H M hH hM).symm.op

/-- The comparison intertwines canonical evaluation itself, not a chosen
isomorphism from a module to its bidual. -/
@[reassoc]
theorem completionHomBidualIso_evaluation (H M : ModuleCat.{u} (AdicCompletion J R))
    [Module.Finite (AdicCompletion J R) M]
    (hH : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) H)
    (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M) :
    (restrictScalars (algebraMap R (AdicCompletion J R))).map (moduleBidualEvaluation H M) ≫
        (completionHomBidualIso J H M hH hM).hom =
      moduleBidualEvaluation ((restrictScalars (algebraMap R (AdicCompletion J R))).obj H)
        ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M) := by
  apply ModuleCat.hom_ext
  ext x
  apply ModuleCat.hom_ext
  ext g
  exact completionHomDualIso_inv_apply J H M hH hM g x

/-- Canonical reflexivity of a finite supported module is unchanged by
actual restriction of scalars. -/
theorem completion_moduleBidualEvaluation_isIso_iff
    (H M : ModuleCat.{u} (AdicCompletion J R)) [Module.Finite (AdicCompletion J R) M]
    (hH : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) H)
    (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M) :
    IsIso (moduleBidualEvaluation H M) ↔
      IsIso (moduleBidualEvaluation
        ((restrictScalars (algebraMap R (AdicCompletion J R))).obj H)
        ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M)) := by
  constructor
  · intro h
    let := h
    rw [← completionHomBidualIso_evaluation J H M hH hM]
    infer_instance
  · intro h
    let := h
    have he : IsIso
        ((restrictScalars (algebraMap R (AdicCompletion J R))).map (moduleBidualEvaluation H M) ≫
          (completionHomBidualIso J H M hH hM).hom) := by
      rw [completionHomBidualIso_evaluation]
      infer_instance
    have : IsIso
        ((restrictScalars (algebraMap R (AdicCompletion J R))).map (moduleBidualEvaluation H M)) :=
      IsIso.of_isIso_comp_right _ (completionHomBidualIso J H M hH hM).hom
    exact isIso_of_reflects_iso _ (restrictScalars (algebraMap R (AdicCompletion J R)))

/-- Finiteness of the original Hom value is unchanged by completion, on
a finite supported test module. The coefficient need not be finite. -/
theorem completion_moduleHomDual_finite_iff
    (H M : ModuleCat.{u} (AdicCompletion J R)) [Module.Finite (AdicCompletion J R) M]
    (hH : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) H)
    (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M) :
    Module.Finite (AdicCompletion J R) ((moduleHomDual H).obj (op M)) ↔
      Module.Finite R
        ((moduleHomDual ((restrictScalars (algebraMap R (AdicCompletion J R))).obj H)).obj
          (op ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M))) := by
  constructor
  · intro h
    let := h
    have := completion_restrictScalars_finite J ((moduleHomDual H).obj (op M))
      (completionHomDual_supported J H M hM)
    exact Module.Finite.of_surjective (completionHomDualIso J H M hH hM).hom.hom
      (completionHomDualIso J H M hH hM).toLinearEquiv.surjective
  · intro h
    let := h
    exact Module.Finite.of_surjective
      ((semilinearMapAddEquiv (algebraMap R (AdicCompletion J R)) _ _).symm
        (completionHomDualIso J H M hH hM).inv)
      ((ModuleCat.epi_iff_surjective (completionHomDualIso J H M hH hM).inv).mp inferInstance)

end SGA.SGA2.ExposeIV
