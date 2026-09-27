/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.SheafHomCoherent

/-!
# Morphisms of quasi-coherent modules from their sections over affine opens

A family of `Γ(X, V)`-linear maps `Γ(M, V) → Γ(N, V)`, one for each affine open `V`, compatible
with restrictions between affine opens (`CohomologyAux.AffineHomData`), defines a unique morphism
`M ⟶ N` when `M` is quasi-coherent (`CohomologyAux.AffineHomData.toHom`, with
`AffineHomData.toHom_app`; EGA I 1.3.8 and 1.4.1). The local pieces come from
`exists_homOn_app_eq` and are glued with `Scheme.Modules.HomOn.glue`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

open Scheme.Modules

variable {X : Scheme.{u}}

/-- Compatible `Γ(X, V)`-linear maps `Γ(M, V) → Γ(N, V)` on the affine opens `V`. -/
structure AffineHomData (M N : X.Modules) where
  /-- The linear map over an affine open. -/
  toFun (V : X.Opens) (hV : IsAffineOpen V) : Γ(M, V) →ₗ[Γ(X, V)] Γ(N, V)
  naturality {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V)
    (m : Γ(M, V)) :
    toFun W hW (M.presheaf.map (homOfLE h).op m) = N.presheaf.map (homOfLE h).op (toFun V hV m)

namespace AffineHomData

variable {M N : X.Modules} [M.IsQuasicoherent] (D : AffineHomData M N)

/-- A `HomOn` on an affine open agreeing with `D` there agrees with `D` on its basic opens. -/
lemma homOn_app_basicOpen {V : X.Opens} (hV : IsAffineOpen V) (ψ : HomOn M N V)
    (hψ : ∀ m, ψ.app V le_rfl m = D.toFun V hV m) (c : Γ(X, V)) (m' : Γ(M, X.basicOpen c)) :
    ψ.app (X.basicOpen c) (X.basicOpen_le c) m' = D.toFun _ (hV.basicOpen c) m' := by
  obtain ⟨m₀, k, hk⟩ := exists_pow_smul_eq_map M hV c m'
  have hU : X.basicOpen c ≤ X.basicOpen (c ^ k) := by
    cases k with
    | zero => rw [pow_zero, Scheme.basicOpen_one]; exact X.basicOpen_le c
    | succ k => rw [Scheme.basicOpen_pow _ _ k.succ_pos]
  refine eq_of_res_smul_eq (c ^ k) hU ?_
  have e1 := LinearMap.map_smul (ψ.app (X.basicOpen c) (X.basicOpen_le c))
    (X.presheaf.map (homOfLE (X.basicOpen_le c)).op (c ^ k)) m'
  have e2 := LinearMap.map_smul (D.toFun _ (hV.basicOpen c))
    (X.presheaf.map (homOfLE (X.basicOpen_le c)).op (c ^ k)) m'
  refine e1.symm.trans (Eq.trans ?_ e2)
  rw [hk, ψ.naturality (X.basicOpen_le c) le_rfl m₀, hψ, D.naturality hV (hV.basicOpen c)]

/-- A `HomOn` on an affine open agreeing with `D` there agrees with `D` on all affine opens
contained in it. -/
lemma homOn_app_of_affine {V : X.Opens} (hV : IsAffineOpen V) (ψ : HomOn M N V)
    (hψ : ∀ m, ψ.app V le_rfl m = D.toFun V hV m) {W : X.Opens} (hW : IsAffineOpen W)
    (hWV : W ≤ V) (m : Γ(M, W)) : ψ.app W hWV m = D.toFun W hW m := by
  apply N.isSheaf.section_ext (U := op W)
  intro x hx
  obtain ⟨c, hcW, hxc⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ (hWV hx)
  refine ⟨X.basicOpen c, hcW, hxc, ?_⟩
  rw [← ψ.naturality hcW hWV m, ← D.naturality hW (hV.basicOpen c) hcW]
  exact homOn_app_basicOpen D hV ψ hψ c _

/-- The local `HomOn` on an affine open defined by `D`. -/
def localHomOn {V : X.Opens} (hV : IsAffineOpen V) : HomOn M N V :=
  (exists_homOn_app_eq hV (D.toFun V hV)).choose

lemma localHomOn_app {V : X.Opens} (hV : IsAffineOpen V) {W : X.Opens} (hW : IsAffineOpen W)
    (hWV : W ≤ V) (m : Γ(M, W)) : (D.localHomOn hV).app W hWV m = D.toFun W hW m :=
  homOn_app_of_affine D hV _ (fun m ↦ congr($((exists_homOn_app_eq hV (D.toFun V hV)).choose_spec)
    m)) hW hWV m

lemma localHomOn_compat (V W : X.affineOpens) :
    (D.localHomOn V.2).restrict (inf_le_left : V.1 ⊓ W.1 ≤ V.1) =
      (D.localHomOn W.2).restrict (inf_le_right : V.1 ⊓ W.1 ≤ W.1) := by
  refine HomOn.ext (funext fun W' ↦ funext fun hW' ↦ LinearMap.ext fun m ↦ ?_)
  change (D.localHomOn V.2).app W' _ m = (D.localHomOn W.2).app W' _ m
  apply N.isSheaf.section_ext (U := op W')
  intro x hx
  obtain ⟨W'', hW'', hxW'', hW''W'⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  refine ⟨W'', hW''W', hxW'', ?_⟩
  rw [← HomOn.naturality, ← HomOn.naturality, localHomOn_app D V.2 hW'', localHomOn_app D W.2 hW'']

/-- The morphism of modules defined by compatible linear maps on the affine opens, for `M`
quasi-coherent. -/
def toHom : M ⟶ N :=
  homOnTopEquiv ((HomOn.glue (U := fun V : X.affineOpens ↦ V.1) (fun V ↦ D.localHomOn V.2)
    (fun V W ↦ D.localHomOn_compat V W)).restrict (iSup_affineOpens_eq_top X).ge)

lemma toHom_app {V : X.Opens} (hV : IsAffineOpen V) (m : Γ(M, V)) :
    D.toHom.app V m = D.toFun V hV m := by
  have h := HomOn.glue_restrict (U := fun V : X.affineOpens ↦ V.1) (fun V ↦ D.localHomOn V.2)
    (fun V W ↦ D.localHomOn_compat V W) ⟨V, hV⟩
  have h' := congr($(h).app V le_rfl m)
  rw [localHomOn_app D hV hV le_rfl] at h'
  exact h'

end AffineHomData

end AlgebraicGeometry.CohomologyAux
