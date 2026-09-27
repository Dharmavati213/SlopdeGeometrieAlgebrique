/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.QuasiCoherentAbelian
import SGA.Foundations.Cohomology.PushforwardLeray
import SGA.Foundations.Cohomology.AffineOpenVanishing

/-!
# Transfer of finiteness of cohomology along direct images

* `CohomologyAux.finiteCohomology_iff_of_addEquiv`: `FiniteCohomology` is transported along
  cohomology isomorphisms which are semilinear along `Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`.
* `CohomologyAux.exists_cechCover`: a quasi-compact scheme with affine diagonal has a finite
  affine cover with affine finite intersections.
* `CohomologyAux.pushforwardHAddEquiv`: `Hᵖ(X, M) ≅ Hᵖ(Y, j_* M)` when `M` is acyclic on the
  inverse images of such a cover (Leray; EGA III 1.3.3, 0_III 12.4.7).
* `CohomologyAux.finiteCohomology_iff_pushforward_of_isAffineHom`: for `j` affine, the cohomology
  of `M` is finite over `A` iff that of `j_* M` is.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TopCat.Presheaf

namespace AlgebraicGeometry.CohomologyAux

section Transfer

variable {X Y : Scheme.{u}}

/-- `Hᵖ(V, M) = Hᵖ(V', M)` for `V = V'`, as `Γ(X, 𝒪_X)`-modules. -/
noncomputable def H'CongrOpens (M : X.Modules) (p : ℕ) {V V' : X.Opens} (h : V = V') :
    M.H' p V ≃ₗ[Γ(X, ⊤)] M.H' p V' := by
  subst h
  exact LinearEquiv.refl _ _

/-- Finiteness of cohomology transfers along a family of isomorphisms `Hᵖ(X, M) ≅ Hᵖ(Y, N)` which
are semilinear along `j^♯ : Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`. -/
lemma finiteCohomology_iff_of_addEquiv {A : CommRingCat.{u}} (j : X ⟶ Y) (g : Y ⟶ Spec A)
    (M : X.Modules) (N : Y.Modules) (e : ∀ p, M.H p ≃+ N.H p)
    (he : ∀ p (r : Γ(Y, ⊤)) (x : M.H p), e p (j.appTop r • x) = r • e p x) :
    FiniteCohomology (j ≫ g).specStructureRingHom M ↔
      FiniteCohomology g.specStructureRingHom N := by
  have hc : (j ≫ g).specStructureRingHom = j.appTop.hom.comp g.specStructureRingHom := by
    rw [Scheme.Hom.specStructureRingHom, Scheme.Hom.specStructureRingHom, Scheme.Hom.comp_appTop]
    rfl
  have key : ∀ p, letI := Module.compHom (M.H p) (j ≫ g).specStructureRingHom
      letI := Module.compHom (N.H p) g.specStructureRingHom
      ∃ E : M.H p ≃ₗ[A] N.H p, ⇑E = ⇑(e p) := fun p ↦ by
    let _ := Module.compHom (M.H p) (j ≫ g).specStructureRingHom
    let _ := Module.compHom (N.H p) g.specStructureRingHom
    refine ⟨{ toAddEquiv := e p, map_smul' := fun a x ↦ ?_ }, rfl⟩
    change e p ((j ≫ g).specStructureRingHom a • x) = g.specStructureRingHom a • e p x
    rw [hc]
    exact he p _ x
  constructor
  · intro h p
    let _ := Module.compHom (M.H p) (j ≫ g).specStructureRingHom
    let _ := Module.compHom (N.H p) g.specStructureRingHom
    obtain ⟨E, -⟩ := key p
    have := h p
    exact Module.Finite.equiv E
  · intro h p
    let _ := Module.compHom (M.H p) (j ≫ g).specStructureRingHom
    let _ := Module.compHom (N.H p) g.specStructureRingHom
    obtain ⟨E, -⟩ := key p
    have := h p
    exact Module.Finite.equiv E.symm

/-- In a scheme with affine diagonal, finite intersections of affine opens are affine. -/
lemma isAffineOpen_cechOpen [IsAffineHom (pullback.diagonal (terminal.from X))] {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    ∀ {m : ℕ} (x : Fin (m + 1) → ι), IsAffineOpen (cechOpen U x)
  | 0, x => by
    have e : cechOpen U x = U (x 0) :=
      le_antisymm (cechOpen_le U x 0)
        (le_iInf fun a ↦ (show a = 0 from Fin.fin_one_eq_zero a) ▸ le_rfl)
    rw [e]
    exact hU _
  | m + 1, x => by
    have e : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
    rw [e, cechOpen_cons_eq]
    exact (hU _).inf (isAffineOpen_cechOpen U hU (Fin.tail x))

/-- A quasi-compact scheme with affine diagonal has a finite affine open cover all of whose finite
intersections are affine. -/
lemma exists_cechCover (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] :
    ∃ (n : ℕ) (U : Fin n → X.Opens), ⨆ i, U i = ⊤ ∧
      ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (cechOpen U x) := by
  choose V hV hxV using fun x : X ↦
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ (⊤ : X.Opens) from trivial))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ (V x : Set X))
    (fun x ↦ (V x).2) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, (hxV x).1⟩)
  refine ⟨t.card, fun k ↦ V (t.equivFin.symm k), ?_,
    isAffineOpen_cechOpen _ (fun k ↦ hV _)⟩
  refine top_le_iff.mp fun x _ ↦ ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

end Transfer

section Leray

variable {X Y : Scheme.{u}} (j : X ⟶ Y) (M : X.Modules) {n : ℕ} (U : Fin n → Y.Opens)

/-- **Leray's theorem for direct images, global form**: if `U` is a finite open cover of `Y` with
affine finite intersections, `j_* M` is quasi-coherent and `M` has no higher cohomology on the
inverse images of the finite intersections, then `Hᵖ(X, M) ≅ Hᵖ(Y, j_* M)`, semilinearly along
`Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`. -/
noncomputable def pushforwardHAddEquiv [((Scheme.Modules.pushforward j).obj M).IsQuasicoherent]
    (hcov : ⨆ i, U i = ⊤)
    (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (cechOpen U x))
    (hacyc : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ),
      Subsingleton (M.H' (q + 1) (j ⁻¹ᵁ cechOpen U x))) (p : ℕ) :
    M.H p ≃+ ((Scheme.Modules.pushforward j).obj M).H p :=
  (H'CongrOpens M p (show (⊤ : X.Opens) = ⨆ i, j ⁻¹ᵁ U i by
      rw [← Scheme.Hom.preimage_iSup, hcov]; rfl)).toAddEquiv.trans
    ((pushforwardH'AddEquiv M U p j hU hacyc).trans
      (H'CongrOpens _ p hcov).toAddEquiv)

lemma pushforwardHAddEquiv_smul [((Scheme.Modules.pushforward j).obj M).IsQuasicoherent]
    (hcov : ⨆ i, U i = ⊤)
    (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (cechOpen U x))
    (hacyc : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ),
      Subsingleton (M.H' (q + 1) (j ⁻¹ᵁ cechOpen U x))) (p : ℕ) (r : Γ(Y, ⊤)) (x : M.H p) :
    pushforwardHAddEquiv j M U hcov hU hacyc p (j.appTop r • x) =
      r • pushforwardHAddEquiv j M U hcov hU hacyc p x := by
  have e₁ : (⊤ : X.Opens) = ⨆ i, j ⁻¹ᵁ U i := by rw [← Scheme.Hom.preimage_iSup, hcov]; rfl
  change (H'CongrOpens _ p hcov) (pushforwardH'AddEquiv M U p j hU hacyc
      ((H'CongrOpens M p e₁) (j.appTop r • x))) =
    r • (H'CongrOpens _ p hcov) (pushforwardH'AddEquiv M U p j hU hacyc
      ((H'CongrOpens M p e₁) x))
  rw [LinearEquiv.map_smul, pushforwardH'AddEquiv_smul, LinearEquiv.map_smul]

/-- **Finiteness of cohomology along direct images with acyclic inverse images.** -/
theorem finiteCohomology_iff_pushforward {A : CommRingCat.{u}} (g : Y ⟶ Spec A)
    [((Scheme.Modules.pushforward j).obj M).IsQuasicoherent] (hcov : ⨆ i, U i = ⊤)
    (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (cechOpen U x))
    (hacyc : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n) (q : ℕ),
      Subsingleton (M.H' (q + 1) (j ⁻¹ᵁ cechOpen U x))) :
    FiniteCohomology (j ≫ g).specStructureRingHom M ↔
      FiniteCohomology g.specStructureRingHom ((Scheme.Modules.pushforward j).obj M) :=
  finiteCohomology_iff_of_addEquiv j g M _ (pushforwardHAddEquiv j M U hcov hU hacyc)
    (pushforwardHAddEquiv_smul j M U hcov hU hacyc)

/-- **Finiteness of cohomology along affine morphisms** (EGA III 1.3.3): for `j` affine, `M`
quasi-coherent and `Y` quasi-compact with affine diagonal, `M` has finitely generated cohomology
over `A` iff `j_* M` does. -/
theorem finiteCohomology_iff_pushforward_of_isAffineHom {A : CommRingCat.{u}} [IsAffineHom j]
    (g : Y ⟶ Spec A) [M.IsQuasicoherent] [CompactSpace Y]
    [IsAffineHom (pullback.diagonal (terminal.from Y))] :
    FiniteCohomology (j ≫ g).specStructureRingHom M ↔
      FiniteCohomology g.specStructureRingHom ((Scheme.Modules.pushforward j).obj M) := by
  have : ((Scheme.Modules.pushforward j).obj M).IsQuasicoherent := isQuasicoherent_pushforward j M
  obtain ⟨n, U, hcov, hU⟩ := exists_cechCover Y
  exact finiteCohomology_iff_pushforward j M U g hcov hU
    (fun x q ↦ M.H'_subsingleton_of_isAffineOpen ((hU x).preimage j) q)

end Leray

end AlgebraicGeometry.CohomologyAux
