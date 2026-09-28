/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.QuasiCoherentKernel

/-!
# Direct images along affine morphisms

Let `j : X ⟶ Y` be an affine morphism of schemes and `M` a quasi-coherent `𝒪_X`-module.

* `CohomologyAux.isQuasicoherent_pushforward`: `j_* M` is quasi-coherent (EGA I 9.2.2 (a); Stacks
  Tag 01XJ).
* `CohomologyAux.cechComplexPushforwardIso`: the Čech complex of `j_* M` for a family of opens `U`
  of `Y` is the Čech complex of `M` for `j⁻¹ U`, compatibly with the actions of `Γ(Y, 𝒪_Y)` and
  `Γ(X, 𝒪_X)` (`cechComplexPushforwardIso_smul`).
* `CohomologyAux.finite_H'_of_pushforward`: if `U` is an affine cover of `Y` with affine finite
  intersections, `Hᵖ(X, M) ≅ Hᵖ(Y, j_* M)` (EGA III 1.3.3; Stacks Tag 01XC; Hartshorne III.4.1 and
  Exercise III.4.1), semilinearly along `Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`. We record the consequence we need:
  if `Hᵖ(Y, j_* M)` is a finitely generated `Γ(Y, 𝒪_Y)`-module, so is `Hᵖ(X, M)`.
-/

universe u

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf

namespace AlgebraicGeometry.CohomologyAux

/-- Transfer of `IsLocalizedModule.Away` along a ring homomorphism `φ : R → S`: if the `R`-module
structures are obtained from `S`-module structures through `φ`, a map which is the localization at
`φ r` over `S` is the localization at `r` over `R`. -/
lemma isLocalizedModule_away_of_ringHom {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S M] [Module S N]
    (φ : R →+* S) (hM : ∀ (r : R) (m : M), r • m = φ r • m)
    (hN : ∀ (r : R) (n : N), r • n = φ r • n) (f : M →ₗ[R] N) (g : M →ₗ[S] N)
    (hfg : ∀ m, f m = g m) (r : R) [IsLocalizedModule.Away (φ r) g] :
    IsLocalizedModule.Away r f := by
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ (fun y ↦ ?_) (fun x hx ↦ ?_)
  · have h := IsLocalizedModule.Away.isUnit_algebraMap g (φ r)
    rw [Module.End.isUnit_iff] at h ⊢
    convert h using 1
    funext n
    exact hN r n
  · obtain ⟨k, x, hx⟩ := IsLocalizedModule.Away.surj g (φ r) y
    exact ⟨k, x, by rw [hN, map_pow, hx, hfg]⟩
  · have h0 : g x = g 0 := by rw [← hfg, hx, map_zero]
    obtain ⟨k, hk⟩ := IsLocalizedModule.Away.exists_of_eq (φ r) h0
    exact ⟨k, by rw [hM, map_pow, hk, smul_zero]⟩


variable {X Y : Scheme.{u}}

/-- **Direct images of quasi-coherent modules along affine morphisms are quasi-coherent**
(EGA I 9.2.2 (a); Stacks Tag 01XJ). -/
theorem isQuasicoherent_pushforward (j : X ⟶ Y) [IsAffineHom j] (M : X.Modules)
    [M.IsQuasicoherent] : ((Scheme.Modules.pushforward j).obj M).IsQuasicoherent := by
  refine isQuasicoherent_of_isLocalizedModule _ (fun U : Y.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top Y) (fun U ↦ U.2) fun U c ↦ ?_
  have hU' : IsAffineOpen (j ⁻¹ᵁ U.1) := U.2.preimage j
  have hW : j ⁻¹ᵁ Y.basicOpen c ⊓ j ⁻¹ᵁ U.1 = X.basicOpen (j.app U.1 c) := by
    rw [Scheme.preimage_basicOpen]
    exact inf_eq_left.mpr (X.basicOpen_le _)
  have hloc := M.isLocalizedModule_presheafInf_top hU' (j.app U.1 c) hW
  let _ (W : Y.Opens) : Module Γ(X, j ⁻¹ᵁ U.1)
      ((((Scheme.Modules.pushforward j).obj M).presheafInf U.1).obj (op W)) :=
    (inferInstance : Module Γ(X, j ⁻¹ᵁ U.1) ((M.presheafInf (j ⁻¹ᵁ U.1)).obj (op (j ⁻¹ᵁ W))))
  have hsmul (W : Y.Opens) (r : Γ(Y, U.1))
      (s : (((Scheme.Modules.pushforward j).obj M).presheafInf U.1).obj (op W)) :
      r • s = j.app U.1 r • s := by
    change j.app (W ⊓ U.1) (Y.presheaf.map (homOfLE (inf_le_right : W ⊓ U.1 ≤ U.1)).op r) •
        @id Γ(M, j ⁻¹ᵁ (W ⊓ U.1)) s =
      X.presheaf.map (homOfLE (inf_le_right : j ⁻¹ᵁ W ⊓ j ⁻¹ᵁ U.1 ≤ j ⁻¹ᵁ U.1)).op
        (j.app U.1 r) • @id Γ(M, j ⁻¹ᵁ W ⊓ j ⁻¹ᵁ U.1) s
    rw [← ConcreteCategory.comp_apply, j.naturality, ConcreteCategory.comp_apply]
    rfl
  let g : (((Scheme.Modules.pushforward j).obj M).presheafInf U.1).obj (op ⊤) →ₗ[Γ(X, j ⁻¹ᵁ U.1)]
      (((Scheme.Modules.pushforward j).obj M).presheafInf U.1).obj (op (Y.basicOpen c)) :=
    TopCat.Presheaf.resₗ (M.presheafInf (j ⁻¹ᵁ U.1)) (M.presheafInf_map_smul _)
      (le_top : j ⁻¹ᵁ Y.basicOpen c ≤ ⊤)
  have : IsLocalizedModule.Away (j.app U.1 c) g := hloc
  exact isLocalizedModule_away_of_ringHom (j.app U.1).hom (hsmul ⊤) (hsmul (Y.basicOpen c)) _ g
    (fun _ ↦ rfl) c


section Cech

variable {X Y : Scheme.{u}} (j : X ⟶ Y)

lemma cechOpen_preimage {ι : Type*} (U : ι → Y.Opens) {m : ℕ} (x : Fin m → ι) :
    cechOpen (fun i ↦ j ⁻¹ᵁ U i) x = j ⁻¹ᵁ cechOpen U x := by
  induction m with
  | zero =>
    simp only [cechOpen, iInf_of_empty]
    rfl
  | succ m ih =>
    rw [← Fin.cons_self_tail x, cechOpen_cons_eq, cechOpen_cons_eq, ih]
    rfl

variable (M : X.Modules) {ι : Type*} (U : ι → Y.Opens)

/-- The Čech cochains of `j_* M` for `U` are those of `M` for `j⁻¹ U`. -/
noncomputable def cechCochainPushforward (m : ℕ) :
    CechCochain U ((Scheme.Modules.pushforward j).obj M).presheaf m ≃+
      CechCochain (fun i ↦ j ⁻¹ᵁ U i) M.presheaf m where
  toFun c x := M.presheaf.map (homOfLE (cechOpen_preimage j U x).le).op
    (@id Γ(M, j ⁻¹ᵁ cechOpen U x) (c x))
  invFun c x := M.presheaf.map (homOfLE (cechOpen_preimage j U x).ge).op (c x)
  left_inv c := funext fun x ↦ by
    change M.presheaf.map _ (M.presheaf.map _ (@id Γ(M, j ⁻¹ᵁ cechOpen U x) (c x))) =
      @id Γ(M, j ⁻¹ᵁ cechOpen U x) (c x)
    rw [TopCat.Presheaf.map_map_apply, modules_map_self]
  right_inv c := funext fun x ↦ by
    change M.presheaf.map _ (M.presheaf.map _ (c x)) = c x
    rw [TopCat.Presheaf.map_map_apply, modules_map_self]
  map_add' c c' := funext fun x ↦ map_add _ _ _

lemma cechCochainPushforward_apply (m : ℕ)
    (c : CechCochain U ((Scheme.Modules.pushforward j).obj M).presheaf m)
    (x : Fin (m + 1) → ι) :
    cechCochainPushforward j M U m c x =
      M.presheaf.map (homOfLE (cechOpen_preimage j U x).le).op
        (@id Γ(M, j ⁻¹ᵁ cechOpen U x) (c x)) :=
  rfl

lemma cechD_cechCochainPushforward (m : ℕ)
    (c : CechCochain U ((Scheme.Modules.pushforward j).obj M).presheaf m) :
    cechD _ _ m (cechCochainPushforward j M U m c) =
      cechCochainPushforward j M U (m + 1) (cechD _ _ m c) := by
  funext x
  rw [cechD_apply, cechCochainPushforward_apply, cechD_apply]
  erw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  erw [map_zsmul]
  rw [cechCochainPushforward_apply]
  congr 1
  exact map_map_eq_map_map M.presheaf _ _ _ _ _

/-- The Čech complex of `j_* M` for `U` is the Čech complex of `M` for `j⁻¹ U`. -/
noncomputable def cechComplexPushforwardIso :
    cechComplex U ((Scheme.Modules.pushforward j).obj M).presheaf ≅
      cechComplex (fun i ↦ j ⁻¹ᵁ U i) M.presheaf :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m ↦ (cechCochainPushforward j M U m).toAddCommGrpIso) fun m m' hm ↦ by
      obtain rfl : m + 1 = m' := hm
      ext c
      change (cechComplex (fun i ↦ j ⁻¹ᵁ U i) M.presheaf).d m (m + 1)
          (cechCochainPushforward j M U m c) =
        cechCochainPushforward j M U (m + 1)
          ((cechComplex U ((Scheme.Modules.pushforward j).obj M).presheaf).d m (m + 1) c)
      have e := cechComplex_d_apply U ((Scheme.Modules.pushforward j).obj M).presheaf m c
      rw [cechComplex_d_apply, e]
      exact cechD_cechCochainPushforward j M U m c


lemma cechComplexPushforwardIso_smul {n : ℕ} (U : Fin n → Y.Opens) (r : Γ(Y, ⊤)) :
    cechComplexMap U (((Scheme.Modules.pushforward j).obj M).smulHom r).hom ≫
        (cechComplexPushforwardIso j M U).hom =
      (cechComplexPushforwardIso j M U).hom ≫
        cechComplexMap (fun i ↦ j ⁻¹ᵁ U i) (M.smulHom (j.appTop r)).hom := by
  ext m : 1
  refine AddCommGrpCat.ext fun c ↦ funext fun x ↦ ?_
  change M.presheaf.map (homOfLE (cechOpen_preimage j U x).le).op
      (j.app (cechOpen U x) (Y.presheaf.map (homOfLE (le_top : cechOpen U x ≤ ⊤)).op r) •
        @id Γ(M, j ⁻¹ᵁ cechOpen U x) (c x)) =
    X.presheaf.map (homOfLE (le_top : cechOpen (fun i ↦ j ⁻¹ᵁ U i) x ≤ ⊤)).op (j.appTop r) •
      M.presheaf.map (homOfLE (cechOpen_preimage j U x).le).op
        (@id Γ(M, j ⁻¹ᵁ cechOpen U x) (c x))
  rw [Scheme.Modules.map_smul]
  congr 1
  have hn := congrArg (fun φ ↦ (ConcreteCategory.hom φ) r)
    (j.naturality (homOfLE (le_top : cechOpen U x ≤ ⊤)).op)
  simp only [ConcreteCategory.comp_apply] at hn
  rw [hn, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The Čech cohomology of `j_* M` for `U` is the Čech cohomology of `M` for `j⁻¹ U`. -/
noncomputable def cechHomologyPushforwardAddEquiv (p : ℕ) :
    (cechComplex U ((Scheme.Modules.pushforward j).obj M).presheaf).homology p ≃+
      (cechComplex (fun i ↦ j ⁻¹ᵁ U i) M.presheaf).homology p :=
  (HomologicalComplex.homologyMapIso (cechComplexPushforwardIso j M U) p).addCommGroupIsoToAddEquiv

lemma cechHomologyPushforwardAddEquiv_smul {n : ℕ} (U : Fin n → Y.Opens) (p : ℕ)
    (r : Γ(Y, ⊤)) (x : (cechComplex U ((Scheme.Modules.pushforward j).obj M).presheaf).homology p) :
    cechHomologyPushforwardAddEquiv j M U p (r • x) =
      j.appTop r • cechHomologyPushforwardAddEquiv j M U p x := by
  change (HomologicalComplex.homologyMap (cechComplexPushforwardIso j M U).hom p)
      ((HomologicalComplex.homologyMap
        (cechComplexMap U (((Scheme.Modules.pushforward j).obj M).smulHom r).hom) p) x) =
    (HomologicalComplex.homologyMap
      (cechComplexMap (fun i ↦ j ⁻¹ᵁ U i) (M.smulHom (j.appTop r)).hom) p)
      ((HomologicalComplex.homologyMap (cechComplexPushforwardIso j M U).hom p) x)
  have h' := congrArg (fun φ ↦ (ConcreteCategory.hom (HomologicalComplex.homologyMap φ p)) x)
    (cechComplexPushforwardIso_smul j M U r)
  have e1 := HomologicalComplex.homologyMap_comp
    (cechComplexMap U (((Scheme.Modules.pushforward j).obj M).smulHom r).hom)
    (cechComplexPushforwardIso j M U).hom p
  have e2 := HomologicalComplex.homologyMap_comp (cechComplexPushforwardIso j M U).hom
    (cechComplexMap (fun i ↦ j ⁻¹ᵁ U i) (M.smulHom (j.appTop r)).hom) p
  rw [e1] at h'
  exact h'.trans (congrArg (fun φ ↦ (ConcreteCategory.hom φ) x) e2)

end Cech

section Cohomology

variable {X Y : Scheme.{u}} (j : X ⟶ Y) (M : X.Modules)

/-- **Cohomology of a direct image along an affine morphism** (EGA III 1.3.3; Stacks Tag 01XC),
finiteness form: let `U` be a finite family of opens of `Y` all of whose finite intersections are
affine. Then `Hᵖ(⋃ j⁻¹ Uᵢ, M) ≅ Hᵖ(⋃ Uᵢ, j_* M)` semilinearly along `Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`; in
particular, if `Hᵖ(⋃ Uᵢ, j_* M)` is a finitely generated `Γ(Y, 𝒪_Y)`-module, so is
`Hᵖ(⋃ j⁻¹ Uᵢ, M)`. -/
theorem finite_H'_of_pushforward [IsAffineHom j] [M.IsQuasicoherent] {n : ℕ}
    (U : Fin n → Y.Opens)
    (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (cechOpen U x)) (p : ℕ)
    [Module.Finite Γ(Y, ⊤) (((Scheme.Modules.pushforward j).obj M).H' p (⨆ i, U i))] :
    letI := Module.compHom (M.H' p (⨆ i, j ⁻¹ᵁ U i)) j.appTop.hom
    Module.Finite Γ(Y, ⊤) (M.H' p (⨆ i, j ⁻¹ᵁ U i)) := by
  have : ((Scheme.Modules.pushforward j).obj M).IsQuasicoherent := isQuasicoherent_pushforward j M
  have hV : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
      IsAffineOpen (cechOpen (fun i ↦ j ⁻¹ᵁ U i) x) := fun x ↦ by
    rw [cechOpen_preimage]
    exact (hU x).preimage j
  let eX := M.cechHomologyLinearEquiv (fun i ↦ j ⁻¹ᵁ U i) p hV
  let eY := ((Scheme.Modules.pushforward j).obj M).cechHomologyLinearEquiv U p hU
  let ec := cechHomologyPushforwardAddEquiv j M U p
  let _ := Module.compHom (M.H' p (⨆ i, j ⁻¹ᵁ U i)) j.appTop.hom
  let E : M.H' p (⨆ i, j ⁻¹ᵁ U i) ≃ₗ[Γ(Y, ⊤)]
      ((Scheme.Modules.pushforward j).obj M).H' p (⨆ i, U i) :=
    { toAddEquiv := eX.symm.toAddEquiv.trans (ec.symm.trans eY.toAddEquiv)
      map_smul' := fun r x ↦ by
        change eY (ec.symm (eX.symm (j.appTop r • x))) = r • eY (ec.symm (eX.symm x))
        rw [LinearEquiv.map_smul eX.symm, ← LinearEquiv.map_smul eY]
        congr 1
        apply ec.injective
        rw [AddEquiv.apply_symm_apply, cechHomologyPushforwardAddEquiv_smul,
          AddEquiv.apply_symm_apply] }
  exact Module.Finite.equiv E.symm

end Cohomology

end AlgebraicGeometry.CohomologyAux
