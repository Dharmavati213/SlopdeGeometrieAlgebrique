/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Gluing unique section extension from a topological basis -/

noncomputable section

universe u v

open CategoryTheory Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} {C : Type v} [Category.{u} C]

/-- The actual sheaf `V ↦ F(V ∩ W)`, expressed as restriction followed by
pushforward along the open inclusion. -/
def openRestrictionPushforward (F : Sheaf C X) (W : Opens X) : Sheaf C X :=
  (Sheaf.pushforward C W.inclusion').obj ((W.isOpenEmbedding.sheafPullback C).obj F)

/-- The canonical restriction morphism to the open-complement pushforward. -/
def openRestrictionHom (F : Sheaf C X) (W : Opens X) : F ⟶ openRestrictionPushforward F W :=
  ⟨{ app U := F.presheaf.map (W.isOpenEmbedding.isOpenMap.adjunction.counit.app U.unop).op
     naturality _ _ _ := by
       change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
       rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
       congr 1 }⟩

/-- On every open the target is actual sections on its intersection with `W`. -/
def openRestrictionSectionsIso (F : Sheaf C X) (W V : Opens X) :
    (openRestrictionPushforward F W).presheaf.obj (op V) ≅ F.presheaf.obj (op (V ⊓ W)) :=
  F.presheaf.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf W V)))

theorem openRestrictionHom_comp_sectionsIso (F : Sheaf C X) (W V : Opens X) :
    (openRestrictionHom F W).hom.app (op V) ≫ (openRestrictionSectionsIso F W V).hom =
      F.presheaf.map (homOfLE inf_le_left : V ⊓ W ⟶ V).op := by
  change F.presheaf.map _ ≫ F.presheaf.map _ = _
  rw [← F.presheaf.map_comp]
  congr 1

/-- Unique extension of sections is local on a basis. This uses the
genuine sheaf isomorphism criterion, hence includes existence by gluing. -/
theorem isIso_restriction_of_basis (F : Sheaf C X) (W : Opens X)
    {ι : Type u} (B : ι → Opens X) (hB : Opens.IsBasis (Set.range B))
    (h : ∀ i, IsIso (F.presheaf.map (homOfLE inf_le_left : B i ⊓ W ⟶ B i).op))
    (V : Opens X) : IsIso (F.presheaf.map (homOfLE inf_le_left : V ⊓ W ⟶ V).op) := by
  have hφ : IsIso (openRestrictionHom F W) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis hB
    intro i
    have : IsIso ((openRestrictionHom F W).hom.app (op (B i)) ≫
        (openRestrictionSectionsIso F W (B i)).hom) := by
      rw [openRestrictionHom_comp_sectionsIso]
      exact h i
    exact IsIso.of_isIso_comp_right _ (openRestrictionSectionsIso F W (B i)).hom
  rw [← openRestrictionHom_comp_sectionsIso F W V]
  infer_instance

/-- Transporting the names of source and target opens does not change
whether their actual restriction is an isomorphism. -/
theorem isIso_presheaf_map_of_eq (F : X.Presheaf C)
    {U V U' V' : Opens X} (i : U ⟶ V) (j : U' ⟶ V') (hU : U = U') (hV : V = V')
    [IsIso (F.map j.op)] : IsIso (F.map i.op) := by
  subst U' V'
  have : i = j := Subsingleton.elim _ _
  simpa only [this] using (inferInstance : IsIso (F.map j.op))

end SGA.SGA2.ExposeIII
