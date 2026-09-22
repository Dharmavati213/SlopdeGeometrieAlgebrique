/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.SheafTensorHom

/-!
# Functoriality and symmetry of the actual module-sheaf tensor

These are the original sectionwise tensor maps followed by sheafification.
Their adjunction with the actual internal Hom and their symmetry retain
the original morphisms, as needed for VI.1.7's tensor sequence.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite MonoidalCategory BraidedCategory

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (S : Sheaf J CommRingCat.{u})

@[simp]
theorem moduleSheafTensorMap_id
    (M F : SheafOfModules.{u} (commRingSheafToRing J S)) :
    moduleSheafTensorMap J S (𝟙 M) (𝟙 F) = 𝟙 (moduleSheafTensor J S M F) := by
  change (PresheafOfModules.sheafification (𝟙 (commRingSheafToRing J S).obj)).map
    (𝟙 M.val ⊗ₘ 𝟙 F.val) = _
  rw [id_tensorHom_id, Functor.map_id]

/-- Tensoring actual maps retains their composition. -/
@[reassoc]
theorem moduleSheafTensorMap_comp
    {M N P E F G : SheafOfModules.{u} (commRingSheafToRing J S)}
    (a : M ⟶ N) (b : N ⟶ P) (f : E ⟶ F) (g : F ⟶ G) :
    moduleSheafTensorMap J S a f ≫ moduleSheafTensorMap J S b g =
      moduleSheafTensorMap J S (a ≫ b) (f ≫ g) := by
  change (PresheafOfModules.sheafification (𝟙 (commRingSheafToRing J S).obj)).map
      (a.val ⊗ₘ f.val) ≫
    (PresheafOfModules.sheafification (𝟙 (commRingSheafToRing J S).obj)).map
      (b.val ⊗ₘ g.val) = _
  rw [← Functor.map_comp, tensorHom_comp_tensorHom]
  rfl

/-- The actual tensor functor with a fixed second module sheaf. -/
def moduleSheafTensorRightFunctor (F : SheafOfModules.{u} (commRingSheafToRing J S)) :
    SheafOfModules.{u} (commRingSheafToRing J S) ⥤
      SheafOfModules.{u} (commRingSheafToRing J S) where
  obj M := moduleSheafTensor J S M F
  map a := moduleSheafTensorMap J S a (𝟙 F)
  map_id M := moduleSheafTensorMap_id J S M F
  map_comp a b := by rw [moduleSheafTensorMap_comp, Category.id_comp]

/-- Tensor-Hom currying retains precomposition in the first tensor factor. -/
theorem moduleSheafTensorHomEquiv_precomp_left
    {M N : SheafOfModules.{u} (commRingSheafToRing J S)} (a : M ⟶ N)
    (F G : SheafOfModules.{u} (commRingSheafToRing J S))
    (φ : moduleSheafTensor J S N F ⟶ G) :
    moduleSheafTensorHomEquiv J S M F G (moduleSheafTensorMap J S a (𝟙 F) ≫ φ) =
      a ≫ moduleSheafTensorHomEquiv J S N F G φ := by
  apply SheafOfModules.hom_ext
  change presheafTensorCurry (R := S.obj) (M := M.val) (F := F.val) (G := G.val)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (commRingSheafToRing J S).obj)).homEquiv
        _ G ((PresheafOfModules.sheafification (𝟙 (commRingSheafToRing J S).obj)).map
          (PresheafOfModules.Monoidal.tensorHom (R := S.obj) a.val (𝟙 F.val)) ≫ φ)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext U m
  apply moduleLocalHom_ext
  intro V x
  dsimp [presheafTensorCurry, presheafTensorCurryLocal]
  rw [PresheafOfModules.naturality_apply]

/-- The genuine sheaf tensor is left adjoint to the actual module internal Hom. -/
def moduleSheafTensorRightAdjunction (F : SheafOfModules.{u} (commRingSheafToRing J S)) :
    moduleSheafTensorRightFunctor J S F ⊣ moduleSheafHomFunctor J F :=
  Adjunction.mkOfHomEquiv
    { homEquiv M G := (moduleSheafTensorHomEquiv J S M F G).toEquiv
      homEquiv_naturality_left_symm := by
        intro M N G a φ
        apply (moduleSheafTensorHomEquiv J S M F G).injective
        rw [AddEquiv.apply_symm_apply, moduleSheafTensorHomEquiv_precomp_left,
          AddEquiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro M G H a φ
        exact moduleSheafTensorHomEquiv_naturality J S M F a φ }

instance (F : SheafOfModules.{u} (commRingSheafToRing J S)) :
    (moduleSheafTensorRightFunctor J S F).Additive :=
  (moduleSheafTensorRightAdjunction J S F).left_adjoint_additive

/-- The actual symmetry is obtained by sheafifying the pointwise module tensor symmetry. -/
def moduleSheafTensorSwapIso
    (M F : SheafOfModules.{u} (commRingSheafToRing J S)) :
    moduleSheafTensor J S M F ≅ moduleSheafTensor J S F M :=
  (PresheafOfModules.sheafification (𝟙 (commRingSheafToRing J S).obj)).mapIso (β_ M.val F.val)

/-- The actual symmetry respects both original tensor factors. -/
@[reassoc]
theorem moduleSheafTensorSwapIso_naturality
    {M N E F : SheafOfModules.{u} (commRingSheafToRing J S)} (a : M ⟶ N) (b : E ⟶ F) :
    moduleSheafTensorMap J S a b ≫ (moduleSheafTensorSwapIso J S N F).hom =
      (moduleSheafTensorSwapIso J S M E).hom ≫ moduleSheafTensorMap J S b a := by
  change (PresheafOfModules.sheafification (𝟙 (commRingSheafToRing J S).obj)).map _ ≫
      (PresheafOfModules.sheafification (𝟙 (commRingSheafToRing J S).obj)).map _ =
    (PresheafOfModules.sheafification (𝟙 (commRingSheafToRing J S).obj)).map _ ≫
      (PresheafOfModules.sheafification (𝟙 (commRingSheafToRing J S).obj)).map _
  rw [← Functor.map_comp, ← Functor.map_comp, braiding_naturality]

end SGA.SGA2.ExposeVI
