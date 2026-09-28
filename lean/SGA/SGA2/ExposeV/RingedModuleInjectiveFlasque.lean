/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.InjectiveFlasque
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# SGA 2, V.3.2: injective modules on a ringed space are flasque

Free presheaves of modules preserve monomorphisms, as does sheafification.
Their right adjoints therefore send an injective module sheaf to an injective
presheaf of sets. Yoneda extends sections across inclusions of open subsets.

The sheaf of rings is arbitrary. In particular, this argument does not require
its additive sheaf to be flat over the integers, and does not assert that the
additive sheaf underlying an injective module sheaf is injective.
-/

noncomputable section

universe u v₁ u₁

open CategoryTheory Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

/-- Free presheaves of modules preserve monomorphisms, pointwise by injectivity
of the map between finitely supported functions induced by an injection. -/
instance freePresheafOfModules_preservesMonomorphisms
    {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u}) :
    (PresheafOfModules.free R).PreservesMonomorphisms where
  preserves {F G} φ hφ := by
    apply PresheafOfModules.mono_of_injective
    intro U
    exact Finsupp.mapDomain_injective ((CategoryTheory.mono_iff_injective (φ.app U)).mp
      (inferInstance : Mono (φ.app U)))

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- The module presheaf underlying an injective module sheaf is injective. -/
theorem injective_modulePresheaf_of_injective
    (M : SheafOfModules.{u} R) [hM : Injective M] : Injective M.val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).map_injective M hM

/-- An injective module sheaf has an injective underlying presheaf of sets. -/
theorem injective_moduleTypePresheaf_of_injective
    (M : SheafOfModules.{u} R) [Injective M] :
    Injective (M.val.presheaf ⋙ forget AddCommGrpCat) :=
  (PresheafOfModules.freeAdjunction R.obj).map_injective M.val
    (injective_modulePresheaf_of_injective R M)

/-- Every section of an injective module sheaf extends to any larger open. -/
theorem surjective_moduleRestriction_of_injective
    (M : SheafOfModules.{u} R) [Injective M]
    {U V : Opens X} (i : V ⟶ U) : Function.Surjective (M.val.map i.op) := by
  let G := M.val.presheaf ⋙ forget AddCommGrpCat
  let : Injective G := injective_moduleTypePresheaf_of_injective R M
  intro s
  let g : yoneda.obj V ⟶ G := yonedaEquiv.symm s
  let e : yoneda.obj U ⟶ G := Injective.factorThru g (yoneda.map i)
  refine ⟨yonedaEquiv e, ?_⟩
  have he := congrArg (fun a : yoneda.obj V ⟶ G ↦ yonedaEquiv a)
    (Injective.comp_factorThru g (yoneda.map i))
  change G.map i.op (yonedaEquiv e) = s
  rw [yonedaEquiv_naturality e i]
  simpa only [g, Equiv.apply_symm_apply] using he

/-- Injective module sheaves are flasque on every ringed space. -/
theorem moduleIsFlasque_of_injective
    (M : SheafOfModules.{u} R) [Injective M] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M) where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (surjective_moduleRestriction_of_injective R M i.unop)

end SGA.SGA2.ExposeV
