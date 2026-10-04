/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ModulesHomRestriction

/-!
# Locality of the Hom-stalk comparison

Restriction to an open subspace commutes with the Hom sheaf. This allows the
finite-presentation comparison on stalks to be deduced from local presentations.

Adopted from the unmerged branch `codex/foundations-missing-inputs` (commit `c65c9a0`, file
`ModuleHomLocal.lean`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}} (U : Opens X) {M N : X.Modules}

private lemma image_preimage_eq_of_le {V : Opens U} {W : Opens X}
    (hW : W ≤ U.isOpenEmbedding.functor.obj V) :
    U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj W) = W := by
  rw [Opens.functor_map_eq_inf, inf_eq_left]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hW hx
  exact y.2

private lemma preimage_le_of_le_image {V : Opens U} {W : Opens X}
    (hW : W ≤ U.isOpenEmbedding.functor.obj V) : (Opens.map U.inclusion').obj W ≤ V := by
  have h := (Opens.map U.inclusion').map (homOfLE hW)
  simpa only [Opens.map_functor_eq] using h.le

/-- A local morphism on the ambient space restricts to a local morphism on an open subspace. -/
def HomOn.restrictOpen {V : Opens U} (φ : HomOn M N (U.isOpenEmbedding.functor.obj V)) :
    HomOn ((restrictOpenFunctor U).obj M) ((restrictOpenFunctor U).obj N) V where
  app W hW := φ.app (U.isOpenEmbedding.functor.obj W)
    (U.isOpenEmbedding.functor.map (homOfLE hW)).le
  naturality hWV _hV m := φ.naturality (U.isOpenEmbedding.functor.map (homOfLE hWV)).le _ m

private def homSectionsTransport {V W : Opens X} (h : V = W)
    (f : M.presheaf.obj (op V) →ₗ[X.presheaf.obj (op V)] N.presheaf.obj (op V)) :
    M.presheaf.obj (op W) →ₗ[X.presheaf.obj (op W)] N.presheaf.obj (op W) := h ▸ f

private lemma homSectionsTransport_naturality {V : Opens U}
    (φ : HomOn ((restrictOpenFunctor U).obj M) ((restrictOpenFunctor U).obj N) V)
    {A B : Opens X} {A' B' : Opens U}
    (eA : U.isOpenEmbedding.functor.obj A' = A)
    (eB : U.isOpenEmbedding.functor.obj B' = B)
    (hBA : B ≤ A) (hB'A' : B' ≤ A') (hA' : A' ≤ V) (m : M.presheaf.obj (op A)) :
    homSectionsTransport eB (φ.app B' (hB'A'.trans hA')) (M.presheaf.map (homOfLE hBA).op m) =
      N.presheaf.map (homOfLE hBA).op (homSectionsTransport eA (φ.app A' hA') m) := by
  cases eA
  cases eB
  exact φ.naturality hB'A' hA' m

/-- A local morphism on an open subspace is a local morphism on the corresponding
ambient open set. -/
def HomOn.ofRestrictOpen {V : Opens U}
    (φ : HomOn ((restrictOpenFunctor U).obj M) ((restrictOpenFunctor U).obj N) V) :
    HomOn M N (U.isOpenEmbedding.functor.obj V) where
  app W hW := homSectionsTransport (image_preimage_eq_of_le U hW)
    (φ.app ((Opens.map U.inclusion').obj W) (preimage_le_of_le_image U hW))
  naturality hBA hA m := homSectionsTransport_naturality U φ _ _ hBA
    ((Opens.map U.inclusion').map (homOfLE hBA)).le (preimage_le_of_le_image U hA) m

private lemma homSectionsTransport_app {V W W' : Opens X} (φ : HomOn M N V)
    (hW : W ≤ V) (hW' : W' ≤ V) (e : W = W') :
    homSectionsTransport e (φ.app W hW) = φ.app W' hW' := by
  cases e
  rfl

private lemma homSectionsTransport_restrict_app {V A B : Opens U}
    (φ : HomOn ((restrictOpenFunctor U).obj M) ((restrictOpenFunctor U).obj N) V)
    (hA : A ≤ V) (hB : B ≤ V) (e : A = B)
    (e' : U.isOpenEmbedding.functor.obj A = U.isOpenEmbedding.functor.obj B) :
    homSectionsTransport e' (φ.app A hA) = φ.app B hB := by
  cases e
  rfl

/-- The local Hom modules on an open subspace agree with those on the corresponding
ambient open set. -/
def homOnRestrictOpenEquiv (V : Opens U) :
    HomOn M N (U.isOpenEmbedding.functor.obj V) ≃
      HomOn ((restrictOpenFunctor U).obj M) ((restrictOpenFunctor U).obj N) V where
  toFun := HomOn.restrictOpen U
  invFun := HomOn.ofRestrictOpen U
  left_inv φ := by
    apply HomOn.ext
    funext W hW
    exact homSectionsTransport_app φ _ _ (image_preimage_eq_of_le U hW)
  right_inv φ := by
    apply HomOn.ext
    funext W hW
    exact homSectionsTransport_restrict_app U φ _ _ (Opens.map_functor_eq (U := U) W) _

instance moduleHomOnRestrictOpen (V : Opens U) :
    Module ((X.restrict U.isOpenEmbedding).presheaf.obj (op V))
      (HomOn M N (U.isOpenEmbedding.functor.obj V)) :=
  inferInstanceAs (Module (X.presheaf.obj (op (U.isOpenEmbedding.functor.obj V))) _)

/-- The open-restriction comparison for local Hom modules is linear. -/
def homOnRestrictOpenLinearEquiv (V : Opens U) :
    HomOn M N (U.isOpenEmbedding.functor.obj V) ≃ₗ[
      (X.restrict U.isOpenEmbedding).presheaf.obj (op V)]
        HomOn ((restrictOpenFunctor U).obj M) ((restrictOpenFunctor U).obj N) V where
  __ := homOnRestrictOpenEquiv (M := M) (N := N) U V
  map_add' _ _ := rfl
  map_smul' r φ := by ext W hW m; rfl

/-- Restriction to an open `U` commutes with the sheaf `ℋom(M, N)`:
`ℋom(M, N)|_U ≅ ℋom(M|_U, N|_U)`. -/
def sheafHomRestrictOpenIso :
    (restrictOpenFunctor U).obj (sheafHom M N) ≅
      sheafHom ((restrictOpenFunctor U).obj M) ((restrictOpenFunctor U).obj N) :=
  (SheafOfModules.fullyFaithfulForget (X.restrict U.isOpenEmbedding).ringCatSheaf).preimageIso
    (PresheafOfModules.isoMk (fun V ↦ (homOnRestrictOpenLinearEquiv U V.unop).toModuleIso)
      (fun {_ _} i ↦ by ext φ; rfl))

@[simp] lemma sheafHomRestrictOpenIso_hom_app (V : Opens U)
    (φ : HomOn M N (U.isOpenEmbedding.functor.obj V)) :
    (sheafHomRestrictOpenIso (M := M) (N := N) U).hom.val.app (op V) φ = φ.restrictOpen U := rfl

lemma HomOn.stalkMap_restrictOpen {V : Opens U}
    (φ : HomOn M N (U.isOpenEmbedding.functor.obj V)) (x : U) (hxV : x ∈ V) :
    LinearEquiv.arrowCongr (restrictOpenStalkEquiv U M x) (restrictOpenStalkEquiv U N x)
      ((φ.restrictOpen U).stalkMap x hxV) = φ.stalkMap x.1 ⟨x, hxV, rfl⟩ := by
  apply LinearMap.ext
  intro m
  obtain ⟨m, rfl⟩ := (restrictOpenStalkEquiv U M x).surjective m
  rw [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply]
  obtain ⟨W, hWV, hxW, m, rfl⟩ := ((restrictOpenFunctor U).obj M).presheaf.exists_le_germ_eq m hxV
  rw [HomOn.stalkMap_germ _ _ _ hWV, restrictOpenStalkEquiv_germ,
    restrictOpenStalkEquiv_germ,
    HomOn.stalkMap_germ _ _ _ (U.isOpenEmbedding.functor.map (homOfLE hWV)).le]
  rfl

/-- The canonical Hom-stalk map commutes with restriction to an open subspace. -/
lemma homStalkMap_restrictOpen (x : U)
    (s : ((restrictOpenFunctor U).obj (sheafHom M N)).presheaf.stalk x) :
    LinearEquiv.arrowCongr (restrictOpenStalkEquiv U M x) (restrictOpenStalkEquiv U N x)
      (homStalkMap ((restrictOpenFunctor U).obj M) ((restrictOpenFunctor U).obj N) x
        (stalkMap (sheafHomRestrictOpenIso U).hom x s)) =
      homStalkMap M N x.1 (restrictOpenStalkEquiv U (sheafHom M N) x s) := by
  obtain ⟨V, hxV, φ, rfl⟩ := ((restrictOpenFunctor U).obj (sheafHom M N)).presheaf.exists_germ_eq s
  rw [stalkMap_germ, sheafHomRestrictOpenIso_hom_app, homStalkMap_germ,
    restrictOpenStalkEquiv_germ, homStalkMap_germ, HomOn.stalkMap_restrictOpen]

/-- Bijectivity of the canonical Hom-stalk map is unchanged on an open neighbourhood. -/
theorem bijective_homStalkMap_of_restrictOpen (x : U)
    (h : Function.Bijective
      (homStalkMap ((restrictOpenFunctor U).obj M) ((restrictOpenFunctor U).obj N) x)) :
    Function.Bijective (homStalkMap M N x.1) := by
  let e := (stalkFunctor x).mapIso (sheafHomRestrictOpenIso (M := M) (N := N) U)
  let a :
      (((restrictOpenFunctor U).obj M).presheaf.stalk x →ₗ[
        (X.restrict U.isOpenEmbedding).presheaf.stalk x]
          ((restrictOpenFunctor U).obj N).presheaf.stalk x) ≃ₛₗ[
            (restrictOpenRingIso U x).commRingCatIsoToRingEquiv.toRingHom]
          (M.presheaf.stalk x.1 →ₗ[X.presheaf.stalk x.1] N.presheaf.stalk x.1) :=
    LinearEquiv.arrowCongr (restrictOpenStalkEquiv U M x) (restrictOpenStalkEquiv U N x)
  have hc := a.bijective.comp (h.comp e.toLinearEquiv.bijective)
  have he : (a ∘ homStalkMap ((restrictOpenFunctor U).obj M)
      ((restrictOpenFunctor U).obj N) x ∘ e.toLinearEquiv) =
      homStalkMap M N x.1 ∘ restrictOpenStalkEquiv U (sheafHom M N) x :=
    funext (homStalkMap_restrictOpen U x)
  rw [he] at hc
  exact (Function.Bijective.of_comp_iff _
    (restrictOpenStalkEquiv U (sheafHom M N) x).bijective).mp hc

variable (M N)

/-- The canonical Hom-stalk map is bijective whenever the source module sheaf is
locally finitely presented. -/
theorem bijective_homStalkMap [M.IsFinitePresentation] (x : X) :
    Function.Bijective (homStalkMap M N x) := by
  obtain ⟨U, hxU, P, hP⟩ := exists_finitePresentation_restrictOpen M x
  exact bijective_homStalkMap_of_restrictOpen (M := M) (N := N) U ⟨x, hxU⟩
    (bijective_homStalkMap_of_finitePresentation ((restrictOpenFunctor U).obj N) ⟨x, hxU⟩ P)

/-- For a locally finitely presented source, the stalk of the Hom sheaf is the module
of homomorphisms between the corresponding stalks. -/
def homStalkEquiv [M.IsFinitePresentation] (x : X) :
    (sheafHom M N).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x) :=
  LinearEquiv.ofBijective (homStalkMap M N x) (bijective_homStalkMap M N x)

end AlgebraicGeometry.LocallyRingedSpace.Modules
