/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.Flasque
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# SGA 2, Exposé I: injective abelian sheaves are flasque

Sheafification and the free abelian presheaf functor preserve monomorphisms.
Their right adjoints therefore carry an injective abelian sheaf to an
injective presheaf of sets. Yoneda then extends each section along the
monomorphism of representables attached to an inclusion of open subsets.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- The presheaf underlying an injective abelian sheaf is injective:
its left adjoint, sheafification, preserves monomorphisms. -/
theorem injective_presheaf_of_injective
    (F : Sheaf AddCommGrpCat.{u} X) [hF : Injective F] : Injective F.presheaf :=
  (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).map_injective
    F hF

/-- Forgetting the abelian group operations of an injective abelian
presheaf preserves injectivity, because free abelian groups preserve monos. -/
theorem injective_typePresheaf_of_injective
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] :
    Injective (F.presheaf ⋙ forget AddCommGrpCat) :=
  (AddCommGrpCat.adj.whiskerRight (Opens X)ᵒᵖ).map_injective F.presheaf
    (injective_presheaf_of_injective F)

/-- Every section of an injective abelian sheaf extends across an
inclusion of open subsets. -/
theorem surjective_restriction_of_injective
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F]
    {U V : Opens X} (i : V ⟶ U) : Function.Surjective (F.presheaf.map i.op) := by
  let G := F.presheaf ⋙ forget AddCommGrpCat
  let : Injective G := injective_typePresheaf_of_injective F
  intro s
  let g : yoneda.obj V ⟶ G := yonedaEquiv.symm s
  let e : yoneda.obj U ⟶ G := Injective.factorThru g (yoneda.map i)
  refine ⟨yonedaEquiv e, ?_⟩
  have he := congrArg (fun a : yoneda.obj V ⟶ G ↦ yonedaEquiv a)
    (Injective.comp_factorThru g (yoneda.map i))
  change G.map i.op (yonedaEquiv e) = s
  rw [yonedaEquiv_naturality e i]
  simpa only [g, Equiv.apply_symm_apply] using he

/-- Injective abelian sheaves are flasque on every topological space. -/
theorem isFlasque_of_injective (F : Sheaf AddCommGrpCat.{u} X) [Injective F] :
    TopCat.Sheaf.IsFlasque F where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (surjective_restriction_of_injective F i.unop)

end SGA.SGA2.ExposeI
