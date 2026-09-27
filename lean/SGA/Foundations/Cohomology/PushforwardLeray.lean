/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.QuasiCoherentAbelian
import SGA.Foundations.Cohomology.Pushforward

/-!
# Direct images and Leray's theorem for acyclic inverse images

Let `j : X ⟶ Y` be a morphism of schemes and `M` a quasi-coherent `𝒪_X`-module.

* `CohomologyAux.isLocalizedModule_presheafInf_top_of_cover`: sections of `M` over a finite union
  of affine opens with affine pairwise intersections localize (EGA I 9.3.1 (i); Stacks Tag 01P7).
* `CohomologyAux.isQuasicoherent_pushforward_of_cover`: if the inverse image of every affine open
  of `Y` is such a finite union, then `j_* M` is quasi-coherent (EGA I 9.2.2 (a); Stacks
  Tag 01LC).
* `CohomologyAux.pushforwardH'AddEquiv`: if `U` is a finite affine cover of an open of `Y` with
  affine finite intersections, `j_* M` is quasi-coherent and `M` has no higher cohomology on the
  inverse images of the finite intersections of the `Uᵢ` (i.e. `Rᵍ j_* M = 0` for `q > 0` over
  these opens), then `Hᵖ(j⁻¹ U, M) ≅ Hᵖ(U, j_* M)`, semilinearly along `Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`
  (the degenerate case of the Leray spectral sequence; EGA III 1.4.14, 0_III 12.1.7).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TopCat.Presheaf

namespace AlgebraicGeometry.CohomologyAux

variable {X Y : Scheme.{u}}

section Localization

variable (F : X.Modules)

/-- **Sections over a finite union of affines localize** (EGA I 9.3.1 (i); Stacks Tag 01P7): if
`V` is covered by finitely many affine opens `Wᵢ` with affine pairwise intersections and `F` is
quasi-coherent, then for `c ∈ Γ(X, V)` the restriction `Γ(V, F) → Γ(D(c), F)` is the localization
at `c`. -/
theorem isLocalizedModule_presheafInf_top_of_cover [F.IsQuasicoherent] {V : X.Opens}
    {ι : Type*} [Finite ι] (W : ι → X.Opens) (hW : ∀ i, IsAffineOpen (W i))
    (hWij : ∀ i j, IsAffineOpen (W i ⊓ W j)) (hWV : ⨆ i, W i = V) (c : Γ(X, V))
    {W' : X.Opens} (hW' : W' ⊓ V = X.basicOpen c) :
    IsLocalizedModule.Away c (TopCat.Presheaf.resₗ (F.presheafInf V) (F.presheafInf_map_smul V)
      (le_top : W' ≤ ⊤)) := by
  have := Fintype.ofFinite ι
  have hWle (i : ι) : W i ≤ V := hWV ▸ le_iSup W i
  -- the restrictions of `c`
  let ci (i : ι) : Γ(X, W i) := X.presheaf.map (homOfLE (hWle i)).op c
  have hci (i : ι) : X.basicOpen (ci i) = W i ⊓ X.basicOpen c := Scheme.basicOpen_res _ _ _
  have hciW' (i : ι) : X.basicOpen (ci i) ≤ W' ⊓ V := by
    rw [hci, hW']; exact inf_le_right
  have hunit : IsUnit (X.presheaf.map (homOfLE (inf_le_right : W' ⊓ V ≤ V)).op c) := by
    rw [← CohomologyAux.presheaf_map_map (X.basicOpen_le c) hW'.le]
    exact (X.toRingedSpace.isUnit_res_basicOpen c).map (X.presheaf.map _).hom
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ (fun y ↦ ?_) (fun x hx ↦ ?_)
  · rw [Module.End.isUnit_iff]
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
    · change X.presheaf.map (homOfLE (inf_le_right : W' ⊓ V ≤ V)).op c •
          (@id Γ(F, W' ⊓ V) x) =
        X.presheaf.map (homOfLE (inf_le_right : W' ⊓ V ≤ V)).op c • (@id Γ(F, W' ⊓ V) y) at hxy
      have := congrArg (hunit.unit⁻¹.1 • ·) hxy
      simp only [smul_smul, IsUnit.val_inv_mul, one_smul] at this
      exact this
    · refine ⟨hunit.unit⁻¹.1 • (@id Γ(F, W' ⊓ V) y), ?_⟩
      change X.presheaf.map (homOfLE (inf_le_right : W' ⊓ V ≤ V)).op c •
        (hunit.unit⁻¹.1 • (@id Γ(F, W' ⊓ V) y)) = y
      rw [smul_smul, IsUnit.mul_val_inv, one_smul]
      rfl
  · -- surjectivity: lift on each `Wᵢ`, correct by powers of `c`, and glue
    let yi (i : ι) : Γ(F, X.basicOpen (ci i)) :=
      F.presheaf.map (homOfLE (hciW' i)).op (@id Γ(F, W' ⊓ V) y)
    choose m k hmk using fun i ↦ exists_pow_smul_eq_map F (hW i) (ci i) (yi i)
    let K := Finset.univ.sup k
    obtain ⟨m', hm'def⟩ : ∃ m' : ∀ i, Γ(F, W i), ∀ i, m' i = ci i ^ (K - k i) • m i :=
      ⟨_, fun _ ↦ rfl⟩
    have hm' (i : ι) : F.presheaf.map (homOfLE (X.basicOpen_le (ci i))).op (m' i) =
        X.presheaf.map (homOfLE (X.basicOpen_le (ci i))).op (ci i ^ K) • yi i := by
      rw [hm'def, Scheme.Modules.map_smul, ← hmk, smul_smul, ← map_mul, ← pow_add,
        Nat.sub_add_cancel (Finset.le_sup (f := k) (Finset.mem_univ i))]
    -- restriction of `c` to `Wᵢ ∩ Wⱼ`
    let cij (i j : ι) : Γ(X, W i ⊓ W j) :=
      X.presheaf.map (homOfLE (inf_le_left.trans (hWle i))).op c
    have hcij (i j : ι) : X.basicOpen (cij i j) = (W i ⊓ W j) ⊓ X.basicOpen c :=
      Scheme.basicOpen_res _ _ _
    have hcij_le (i j l : ι) (h : W i ⊓ W j ≤ W l) :
        X.basicOpen (cij i j) ≤ X.basicOpen (ci l) := by
      rw [hcij, hci]; exact inf_le_inf_right _ h
    -- the differences on `Wᵢ ∩ Wⱼ` vanish on `D(c)`
    have hd (i j : ι) : F.presheaf.map (homOfLE (X.basicOpen_le (cij i j))).op
        (F.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (m' i) -
          F.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (m' j)) = 0 := by
      have key (l : ι) (hl : W i ⊓ W j ≤ W l) :
          F.presheaf.map (homOfLE (X.basicOpen_le (cij i j))).op
            (F.presheaf.map (homOfLE hl).op (m' l)) =
          X.presheaf.map (homOfLE ((X.basicOpen_le (cij i j)).trans
              (inf_le_left.trans (hWle i)))).op (c ^ K) •
            F.presheaf.map (homOfLE ((hcij_le i j l hl).trans (hciW' l) :
              X.basicOpen (cij i j) ≤ W' ⊓ V)).op (@id Γ(F, W' ⊓ V) y) := by
        have h1 : X.basicOpen (cij i j) ≤ X.basicOpen (ci l) := hcij_le i j l hl
        rw [TopCat.Presheaf.map_map_apply,
          ← TopCat.Presheaf.map_map_apply F.presheaf (X.basicOpen_le (ci l)) h1, hm',
          Scheme.Modules.map_smul, TopCat.Presheaf.map_map_apply]
        change X.presheaf.map _ (X.presheaf.map _ (X.presheaf.map _ c ^ K)) • _ = _
        rw [map_pow, map_pow, CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_map,
          map_pow]
      rw [map_sub, key i inf_le_left, key j inf_le_right, sub_self]
    choose e he using fun ij : ι × ι ↦
      exists_pow_smul_eq_zero F (hWij ij.1 ij.2) (cij ij.1 ij.2) _ (hd ij.1 ij.2)
    let E := Finset.univ.sup e
    obtain ⟨t, htdef⟩ : ∃ t : ∀ i, Γ(F, W i), ∀ i, t i = ci i ^ E • m' i := ⟨_, fun _ ↦ rfl⟩
    have hcompat : TopCat.Presheaf.IsCompatible F.presheaf W t := by
      intro i j
      rw [← sub_eq_zero]
      change F.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (t i) -
        F.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (t j) = 0
      have e1 (l : ι) (hl : W i ⊓ W j ≤ W l) : F.presheaf.map (homOfLE hl).op (t l) =
          cij i j ^ E • F.presheaf.map (homOfLE hl).op (m' l) := by
        rw [htdef, Scheme.Modules.map_smul, map_pow, CohomologyAux.presheaf_map_map]
      rw [e1 i inf_le_left, e1 j inf_le_right, ← smul_sub,
        show E = E - e (i, j) + e (i, j) from
          (Nat.sub_add_cancel (Finset.le_sup (f := e) (Finset.mem_univ (i, j)))).symm,
        pow_add, mul_smul, he (i, j), smul_zero]
    obtain ⟨s', hs', -⟩ := TopCat.Sheaf.existsUnique_gluing' F.toAbSheaf W (⊤ ⊓ V)
      (fun i ↦ homOfLE (le_inf le_top (hWle i))) (by rw [hWV]; exact inf_le_right) t hcompat
    refine ⟨E + K, s', ?_⟩
    change X.presheaf.map (homOfLE (inf_le_right : W' ⊓ V ≤ V)).op (c ^ (E + K)) •
        (@id Γ(F, W' ⊓ V) y) =
      F.presheaf.map (homOfLE (inf_le_inf_right V le_top : W' ⊓ V ≤ ⊤ ⊓ V)).op s'
    refine TopCat.Sheaf.eq_of_locally_eq' F.toAbSheaf (fun i ↦ X.basicOpen (ci i)) (W' ⊓ V)
      (fun i ↦ homOfLE (hciW' i)) (fun x hx ↦ ?_) _ _ fun i ↦ ?_
    · have hxV : x ∈ (V : Set X) := hx.2
      rw [← hWV] at hxV
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxV
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
      rw [hci]
      exact ⟨hi, (hW'.le hx)⟩
    · change F.presheaf.map (homOfLE (hciW' i)).op
          (X.presheaf.map (homOfLE (inf_le_right : W' ⊓ V ≤ V)).op (c ^ (E + K)) •
            (@id Γ(F, W' ⊓ V) y)) =
        F.presheaf.map (homOfLE (hciW' i)).op
          (F.presheaf.map (homOfLE (inf_le_inf_right V le_top : W' ⊓ V ≤ ⊤ ⊓ V)).op s')
      have hR : F.presheaf.map (homOfLE (hciW' i)).op
          (F.presheaf.map (homOfLE (inf_le_inf_right V le_top : W' ⊓ V ≤ ⊤ ⊓ V)).op s') =
          F.presheaf.map (homOfLE (X.basicOpen_le (ci i))).op (t i) := by
        rw [← hs' i]
        exact CohomologyAux.map_map_eq_map_map F.presheaf _ _ _ _ s'
      rw [hR, htdef, Scheme.Modules.map_smul, Scheme.Modules.map_smul, hm', smul_smul,
        ← map_mul, ← pow_add]
      congr 1
      change X.presheaf.map _ (X.presheaf.map _ (c ^ (E + K))) =
        X.presheaf.map _ (X.presheaf.map _ c ^ (E + K))
      simp only [map_pow, CohomologyAux.presheaf_map_map]
  · -- injectivity part: `x` vanishing on `D(c)` is killed by a power of `c`
    change F.presheaf.map (homOfLE (inf_le_inf_right V le_top : W' ⊓ V ≤ ⊤ ⊓ V)).op
      (@id Γ(F, ⊤ ⊓ V) x) = 0 at hx
    have hx0 (i : ι) : F.presheaf.map (homOfLE (X.basicOpen_le (ci i))).op
        (F.presheaf.map (homOfLE (le_inf le_top (hWle i) : W i ≤ ⊤ ⊓ V)).op
          (@id Γ(F, ⊤ ⊓ V) x)) = 0 := by
      rw [TopCat.Presheaf.map_map_apply]
      have := congrArg (F.presheaf.map (homOfLE (hciW' i)).op) hx
      rwa [TopCat.Presheaf.map_map_apply, map_zero] at this
    choose e he using fun i ↦ exists_pow_smul_eq_zero F (hW i) (ci i) _ (hx0 i)
    refine ⟨Finset.univ.sup e, ?_⟩
    change X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op (c ^ Finset.univ.sup e) •
      (@id Γ(F, ⊤ ⊓ V) x) = 0
    refine TopCat.Sheaf.eq_of_locally_eq' F.toAbSheaf W (⊤ ⊓ V)
      (fun i ↦ homOfLE (le_inf le_top (hWle i))) (by rw [hWV]; exact inf_le_right) _ _
      fun i ↦ ?_
    change F.presheaf.map (homOfLE (le_inf le_top (hWle i) : W i ≤ ⊤ ⊓ V)).op
      (X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op (c ^ Finset.univ.sup e) •
        (@id Γ(F, ⊤ ⊓ V) x)) = F.presheaf.map _ 0
    rw [map_zero, Scheme.Modules.map_smul, CohomologyAux.presheaf_map_map, map_pow,
      ← Nat.sub_add_cancel (Finset.le_sup (f := e) (Finset.mem_univ i)), pow_add, mul_smul]
    change X.presheaf.map _ c ^ _ • (ci i ^ e i • _) = 0
    rw [he i, smul_zero]

end Localization

/-- **Direct images of quasi-coherent modules are quasi-coherent** (EGA I 9.2.2 (a); Stacks
Tag 01LC), under the hypothesis that the inverse image of every affine open is a finite union of
affine opens with affine pairwise intersections (e.g. `j` quasi-compact and `X` with affine
diagonal). -/
theorem isQuasicoherent_pushforward_of_cover (j : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent]
    (hcov : ∀ U : Y.Opens, IsAffineOpen U → ∃ (n : ℕ) (W : Fin n → X.Opens),
      (∀ i, IsAffineOpen (W i)) ∧ (∀ i k, IsAffineOpen (W i ⊓ W k)) ∧ ⨆ i, W i = j ⁻¹ᵁ U) :
    ((Scheme.Modules.pushforward j).obj M).IsQuasicoherent := by
  refine isQuasicoherent_of_isLocalizedModule _ (fun U : Y.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top Y) (fun U ↦ U.2) fun U c ↦ ?_
  obtain ⟨n, W, hW, hWij, hWU⟩ := hcov U.1 U.2
  have hW' : j ⁻¹ᵁ Y.basicOpen c ⊓ j ⁻¹ᵁ U.1 = X.basicOpen (j.app U.1 c) := by
    rw [Scheme.preimage_basicOpen]
    exact inf_eq_left.mpr (X.basicOpen_le _)
  have hloc := isLocalizedModule_presheafInf_top_of_cover M W hW hWij hWU (j.app U.1 c) hW'
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

section Leray

variable (M : X.Modules) {n : ℕ} (U : Fin n → Y.Opens) (p : ℕ)

/-- Leray's comparison `Ȟᵖ(U, F) ≅ Hᵖ(⋃ Uᵢ, F)`, `Γ(X, 𝒪_X)`-linearly, for any `F` without
higher cohomology on the finite intersections of the `Uᵢ` (variant of
`Scheme.Modules.cechHomologyLinearEquiv`). -/
noncomputable def cechHomologyLinearEquivOfLeray (F : X.Modules) {n : ℕ} (V : Fin n → X.Opens)
    (hL : TopCat.Sheaf.IsLerayAcyclic (X := X.carrier) V F.toAbSheaf) :
    (TopCat.Presheaf.cechComplex V F.presheaf).homology p ≃ₗ[Γ(X, ⊤)] F.H' p (⨆ i, V i) :=
  let e := TopCat.Sheaf.cechHomologyIso p F.toAbSheaf hL
  { e.addCommGroupIsoToAddEquiv with
    map_smul' := fun r x ↦ by
      have h := congrArg
        (fun (f : (TopCat.Presheaf.cechComplex V F.toAbSheaf.obj).homology p ⟶
          F.toAbSheaf.H' p (⨆ i, V i)) ↦ f x)
        (TopCat.Sheaf.cechHomologyIso_naturality p hL hL (F.smulHom r))
      exact h }

variable (j : X ⟶ Y)

/-- **Leray's theorem for direct images with acyclic inverse images**: let `U` be a finite family
of opens of `Y` with affine finite intersections, `M` an `𝒪_X`-module with `j_* M` quasi-coherent
and `H^q(j⁻¹ U_x, M) = 0` for all `q > 0` and all finite intersections `U_x`. Then
`Hᵖ(⋃ j⁻¹ Uᵢ, M) ≅ Hᵖ(⋃ Uᵢ, j_* M)`, semilinearly along `Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`. -/
noncomputable def pushforwardH'AddEquiv
    [((Scheme.Modules.pushforward j).obj M).IsQuasicoherent]
    (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (cechOpen U x))
    (hacyc : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ),
      Subsingleton (M.H' (q + 1) (j ⁻¹ᵁ cechOpen U x))) :
    M.H' p (⨆ i, j ⁻¹ᵁ U i) ≃+ ((Scheme.Modules.pushforward j).obj M).H' p (⨆ i, U i) :=
  let hL : TopCat.Sheaf.IsLerayAcyclic (X := X.carrier) (fun i ↦ j ⁻¹ᵁ U i) M.toAbSheaf :=
    ⟨fun x q ↦ by rw [cechOpen_preimage]; exact hacyc x q⟩
  (cechHomologyLinearEquivOfLeray p M (fun i ↦ j ⁻¹ᵁ U i) hL).symm.toAddEquiv.trans
    ((cechHomologyPushforwardAddEquiv j M U p).symm.trans
      (((Scheme.Modules.pushforward j).obj M).cechHomologyLinearEquiv U p hU).toAddEquiv)

lemma pushforwardH'AddEquiv_smul [((Scheme.Modules.pushforward j).obj M).IsQuasicoherent]
    (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (cechOpen U x))
    (hacyc : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ),
      Subsingleton (M.H' (q + 1) (j ⁻¹ᵁ cechOpen U x)))
    (r : Γ(Y, ⊤)) (x : M.H' p (⨆ i, j ⁻¹ᵁ U i)) :
    pushforwardH'AddEquiv M U p j hU hacyc (j.appTop r • x) =
      r • pushforwardH'AddEquiv M U p j hU hacyc x := by
  let hL : TopCat.Sheaf.IsLerayAcyclic (X := X.carrier) (fun i ↦ j ⁻¹ᵁ U i) M.toAbSheaf :=
    ⟨fun x q ↦ by rw [cechOpen_preimage]; exact hacyc x q⟩
  let eX := cechHomologyLinearEquivOfLeray p M (fun i ↦ j ⁻¹ᵁ U i) hL
  let eY := ((Scheme.Modules.pushforward j).obj M).cechHomologyLinearEquiv U p hU
  let ec := cechHomologyPushforwardAddEquiv j M U p
  change eY (ec.symm (eX.symm (j.appTop r • x))) = r • eY (ec.symm (eX.symm x))
  rw [LinearEquiv.map_smul eX.symm, ← LinearEquiv.map_smul eY]
  congr 1
  apply ec.injective
  rw [AddEquiv.apply_symm_apply, cechHomologyPushforwardAddEquiv_smul, AddEquiv.apply_symm_apply]

/-- Finiteness transfer along `pushforwardH'AddEquiv`. -/
theorem finite_H'_of_pushforward_of_acyclic
    [((Scheme.Modules.pushforward j).obj M).IsQuasicoherent]
    (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (cechOpen U x))
    (hacyc : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ),
      Subsingleton (M.H' (q + 1) (j ⁻¹ᵁ cechOpen U x)))
    [Module.Finite Γ(Y, ⊤) (((Scheme.Modules.pushforward j).obj M).H' p (⨆ i, U i))] :
    letI := Module.compHom (M.H' p (⨆ i, j ⁻¹ᵁ U i)) j.appTop.hom
    Module.Finite Γ(Y, ⊤) (M.H' p (⨆ i, j ⁻¹ᵁ U i)) := by
  let _ := Module.compHom (M.H' p (⨆ i, j ⁻¹ᵁ U i)) j.appTop.hom
  let E : M.H' p (⨆ i, j ⁻¹ᵁ U i) ≃ₗ[Γ(Y, ⊤)]
      ((Scheme.Modules.pushforward j).obj M).H' p (⨆ i, U i) :=
    { toAddEquiv := pushforwardH'AddEquiv M U p j hU hacyc
      map_smul' := fun r x ↦ pushforwardH'AddEquiv_smul M U p j hU hacyc r x }
  exact Module.Finite.equiv E.symm

end Leray

end AlgebraicGeometry.CohomologyAux
