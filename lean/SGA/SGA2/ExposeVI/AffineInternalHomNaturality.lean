/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.AffineInternalHom

/-! # Naturality of the actual affine internal-Hom comparison -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) [Module.FinitePresentation R M]

/-- The original module-valued Hom coefficient functor. -/
def affineModuleHomFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj N := ModuleCat.of R (M →ₗ[R] N)
  map {N P} a := ModuleCat.ofHom (LinearMap.llcomp R M N P a.hom)
  map_id _ := by ext h m; rfl
  map_comp _ _ := by ext h m; rfl

instance : (affineModuleHomFunctor M).Additive where
  map_add := by intros; ext h; rfl

/-- The actual tilde-Hom comparison is natural for the original coefficient maps. -/
theorem affineInternalHomIso_naturality {N P : ModuleCat.{u} R} (a : N ⟶ P) :
    tilde.map (ModuleCat.ofHom (LinearMap.llcomp R M N P a.hom)) ≫
        (affineInternalHomIso M P).hom =
      (affineInternalHomIso M N).hom ≫
        moduleSheafHomMap (Opens.grothendieckTopology (Spec R)) (tilde M) (tilde.map a) := by
  apply affineTildeMorphism_ext (ModuleCat.of R (M →ₗ[R] N)) _
  intro h
  have ha := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (ModuleCat.ofHom (LinearMap.llcomp R M N P a.hom)) ⊤) h
  change (affineInternalHomIso M P).hom.val.app (op ⊤)
      ((tilde.map (ModuleCat.ofHom (LinearMap.llcomp R M N P a.hom))).val.app (op ⊤)
        ((tilde.toOpen (ModuleCat.of R (M →ₗ[R] N)) ⊤) h)) = _
  change (tilde.map (ModuleCat.ofHom (LinearMap.llcomp R M N P a.hom))).val.app (op ⊤)
      ((tilde.toOpen (ModuleCat.of R (M →ₗ[R] N)) ⊤) h) =
    (tilde.toOpen (ModuleCat.of R (M →ₗ[R] P)) ⊤) (a.hom.comp h) at ha
  rw [ha, affineInternalHomIso_hom_toOpen]
  change affineHomSection M P ⊤ (a.hom.comp h) =
    moduleLocalHomPostcomp (tilde M).val (tilde.map a).val ⊤
      ((affineInternalHomIso M N).hom.val.app (op ⊤)
        ((tilde.toOpen (ModuleCat.of R (M →ₗ[R] N)) ⊤) h))
  rw [affineInternalHomIso_hom_toOpen, affineHomSection_postcomp]

/-- The actual affine Hom comparison, bundled naturally in the coefficient module. -/
def affineInternalHomFunctorIso :
    affineModuleHomFunctor M ⋙ tilde.functor R ≅
      tilde.functor R ⋙
        moduleSheafHomFunctor (Opens.grothendieckTopology (Spec R))
          (S := (Spec R).sheaf) (tilde M) :=
  NatIso.ofComponents (fun N ↦ affineInternalHomIso M N)
    (fun a ↦ affineInternalHomIso_naturality M a)

/-- The actual tilde-Hom comparison is natural contravariantly in its source module. -/
theorem affineInternalHomIso_precomp {P : ModuleCat.{u} R} [Module.FinitePresentation R P]
    (a : P ⟶ M) (N : ModuleCat.{u} R) :
    tilde.map (ModuleCat.ofHom (LinearMap.lcomp R N a.hom)) ≫
        (affineInternalHomIso P N).hom =
      (affineInternalHomIso M N).hom ≫
        moduleSheafHomPrecomp (Opens.grothendieckTopology (Spec R)) (tilde.map a) (tilde N) := by
  apply affineTildeMorphism_ext (ModuleCat.of R (M →ₗ[R] N)) _
  intro h
  have ha := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (ModuleCat.ofHom (LinearMap.lcomp R N a.hom)) ⊤) h
  change (affineInternalHomIso P N).hom.val.app (op ⊤)
      ((tilde.map (ModuleCat.ofHom (LinearMap.lcomp R N a.hom))).val.app (op ⊤)
        ((tilde.toOpen (ModuleCat.of R (M →ₗ[R] N)) ⊤) h)) = _
  change (tilde.map (ModuleCat.ofHom (LinearMap.lcomp R N a.hom))).val.app (op ⊤)
      ((tilde.toOpen (ModuleCat.of R (M →ₗ[R] N)) ⊤) h) =
    (tilde.toOpen (ModuleCat.of R (P →ₗ[R] N)) ⊤) (h.comp a.hom) at ha
  rw [ha, affineInternalHomIso_hom_toOpen]
  change affineHomSection P N ⊤ (h.comp a.hom) =
    moduleLocalHomPrecomp (tilde.map a).val (tilde N).val ⊤
      ((affineInternalHomIso M N).hom.val.app (op ⊤)
        ((tilde.toOpen (ModuleCat.of R (M →ₗ[R] N)) ⊤) h))
  rw [affineInternalHomIso_hom_toOpen, affineHomSection_precomp]

end SGA.SGA2.ExposeVI
