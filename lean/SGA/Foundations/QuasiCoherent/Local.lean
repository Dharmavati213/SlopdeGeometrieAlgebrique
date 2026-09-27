/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Local properties of `𝒪_X`-modules on open covers

Mathlib defines quasi-coherence, finite type, finite presentation and local freeness of a
sheaf of modules `M` on a site through data over a covering family of objects of the site,
i.e. for a scheme `X`, over a family of opens `U i` covering `X`, on the sheaves `M.over (U i)`
over the site `Over (U i)`. We translate these into statements about the restrictions
`M.restrict (U i).ι`, which are `𝒪_{U i}`-modules on the schemes `U i`:

* `Scheme.Modules.isQuasicoherent_of_isOpenCover`, `isFiniteType_of_isOpenCover`,
  `isFinitePresentation_of_isOpenCover`, `isLocallyFree_of_isOpenCover`: a module having a
  presentation (resp. finite generating sections, a finite presentation, a basis) on each member of
  an open cover has the corresponding property ([Stacks, Tag 01BE], [Stacks, Tag 01C6]);
* `Scheme.Modules.exists_isOpenCover_generatingSections`,
  `exists_isOpenCover_finitePresentation`, `exists_isOpenCover_basis`: the converses
  (for quasi-coherence this is mathlib's `Scheme.Modules.exists_isOpenCover_presentation`).

We also record that these properties are invariant under isomorphism.
-/

universe u v₁ v₂ u₁ u₂

open CategoryTheory Limits TopologicalSpace

namespace SheafOfModules

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The image of a presentation under a left adjoint `F` with `F.obj (unit R) ≅ unit S`
(a variant of `Presentation.map` taking the adjunction as an explicit argument, which is
convenient when the categories of modules are type synonyms such as `Scheme.Modules`). -/
noncomputable def Presentation.mapOfAdjunction {M : SheafOfModules.{u} R} (P : M.Presentation)
    {F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S} {G : SheafOfModules.{u} S ⥤ _}
    (adj : F ⊣ G) (η : unit S ≅ F.obj (unit R)) : (F.obj M).Presentation :=
  have := adj.isLeftAdjoint
  P.map F η

instance Presentation.isFinite_mapOfAdjunction {M : SheafOfModules.{u} R}
    (P : M.Presentation) [P.IsFinite] {F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S}
    {G : SheafOfModules.{u} S ⥤ _} (adj : F ⊣ G) (η : unit S ≅ F.obj (unit R)) :
    (P.mapOfAdjunction adj η).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite P.generators.I)⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite P.relations.I)⟩

/-- The image of generating sections under a left adjoint `F` with
`F.obj (unit R) ≅ unit S`. -/
noncomputable def GeneratingSections.mapOfAdjunction {M : SheafOfModules.{u} R}
    (σ : M.GeneratingSections) {F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S}
    {G : SheafOfModules.{u} S ⥤ _} (adj : F ⊣ G) (η : unit S ≅ F.obj (unit R)) :
    (F.obj M).GeneratingSections :=
  have := adj.isLeftAdjoint
  σ.map F η

instance GeneratingSections.isFiniteType_mapOfAdjunction {M : SheafOfModules.{u} R}
    (σ : M.GeneratingSections) [σ.IsFiniteType] {F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S}
    {G : SheafOfModules.{u} S ⥤ _} (adj : F ⊣ G) (η : unit S ≅ F.obj (unit R)) :
    (σ.mapOfAdjunction adj η).IsFiniteType where
  finite := inferInstanceAs (Finite σ.I)

instance GeneratingSections.isIso_mapOfAdjunction_π {M : SheafOfModules.{u} R}
    (σ : M.GeneratingSections) [hσ : IsIso σ.π] {F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S}
    {G : SheafOfModules.{u} S ⥤ _} (adj : F ⊣ G) (η : unit S ≅ F.obj (unit R)) :
    IsIso (σ.mapOfAdjunction adj η).π := by
  have := adj.isLeftAdjoint
  exact inferInstanceAs (IsIso (σ.map F η).π)

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Generating sections transported along an isomorphism. -/
noncomputable def GeneratingSections.ofIso {M N : SheafOfModules.{u} R}
    (σ : M.GeneratingSections) (e : M ≅ N) : N.GeneratingSections :=
  σ.ofEpi e.hom

instance GeneratingSections.isFiniteType_ofIso {M N : SheafOfModules.{u} R}
    (σ : M.GeneratingSections) [σ.IsFiniteType] (e : M ≅ N) : (σ.ofIso e).IsFiniteType :=
  inferInstanceAs (σ.ofEpi e.hom).IsFiniteType

instance GeneratingSections.isIso_ofIso_π {M N : SheafOfModules.{u} R}
    (σ : M.GeneratingSections) [hσ : IsIso σ.π] (e : M ≅ N) : IsIso (σ.ofIso e).π := by
  rw [ofIso, ofEpi_π]
  exact IsIso.comp_isIso' hσ inferInstance

end

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A presentation transported along an isomorphism. -/
noncomputable def Presentation.ofIso {M N : SheafOfModules.{u} R} (P : M.Presentation)
    (e : M ≅ N) : N.Presentation :=
  P.ofIsIso e.hom

instance Presentation.isFinite_ofIso {M N : SheafOfModules.{u} R} (P : M.Presentation)
    [P.IsFinite] (e : M ≅ N) : (P.ofIso e).IsFinite :=
  inferInstanceAs (P.ofIsIso e.hom).IsFinite

end

end SheafOfModules

namespace TopologicalSpace.Opens

/-- The inverse image functor on open sets along a continuous map is final: every open set of
the source is contained in the inverse image of the whole target. -/
instance final_map {X Y : TopCat.{u}} (f : X ⟶ Y) : (Opens.map f).Final := by
  constructor
  intro U
  refine isConnected_of_isTerminal _
    (x := StructuredArrow.mk (Y := ⊤) (homOfLE le_top : U ⟶ (Opens.map f).obj ⊤)) ?_
  refine IsTerminal.ofUniqueHom (fun V ↦ StructuredArrow.homMk (homOfLE le_top)) ?_
  intro V m
  ext
  exact Subsingleton.elim _ _

end TopologicalSpace.Opens

namespace AlgebraicGeometry.Scheme.Modules

open SheafOfModules

variable {X : Scheme.{u}}

section Over

variable (U : X.Opens)

/-- `overEquiv U` sends the structure sheaf of `Over U` to `𝒪_U`. -/
noncomputable def overEquivFunctorObjUnitIso :
    (overEquiv U).functor.obj (unit (X.ringCatSheaf.over U)) ≅ unit U.toScheme.ringCatSheaf :=
  (overFunctorEquiv U).app (unit X.ringCatSheaf) ≪≫ restrictUnitIso U.ι

/-- The inverse of `overEquiv U` sends `𝒪_U` to the structure sheaf of `Over U`. -/
noncomputable def overInverseObjUnitIso :
    unit (X.ringCatSheaf.over U) ≅ (overEquiv U).inverse.obj (unit U.toScheme.ringCatSheaf) :=
  (overEquiv U).unitIso.app _ ≪≫ (overEquiv U).inverse.mapIso (overEquivFunctorObjUnitIso U)

/-- The inverse of `overEquiv U` sends `M.restrict U.ι` to `M.over U`. -/
noncomputable def overInverseObjRestrictIso (M : X.Modules) :
    (overEquiv U).inverse.obj (M.restrict U.ι) ≅ M.over U :=
  (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
    (overEquiv U).unitIso.symm.app _

variable {U}

/-- A presentation of `M.restrict U.ι` gives one of `M.over U`. -/
noncomputable def presentationOverOfRestrict {M : X.Modules} (P : (M.restrict U.ι).Presentation) :
    (M.over U).Presentation :=
  (P.mapOfAdjunction (overEquiv U).symm.toAdjunction (overInverseObjUnitIso U)).ofIso
    (overInverseObjRestrictIso U M)

instance {M : X.Modules} (P : (M.restrict U.ι).Presentation) [hP : P.IsFinite] :
    (presentationOverOfRestrict P).IsFinite :=
  ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩

/-- Generating sections of `M.restrict U.ι` give generating sections of `M.over U`. -/
noncomputable def generatingSectionsOverOfRestrict {M : X.Modules}
    (σ : (M.restrict U.ι).GeneratingSections) : (M.over U).GeneratingSections :=
  (σ.mapOfAdjunction (overEquiv U).symm.toAdjunction (overInverseObjUnitIso U)).ofIso
    (overInverseObjRestrictIso U M)

instance {M : X.Modules} (σ : (M.restrict U.ι).GeneratingSections) [hσ : σ.IsFiniteType] :
    (generatingSectionsOverOfRestrict σ).IsFiniteType :=
  ⟨hσ.finite⟩

instance {M : X.Modules} (σ : (M.restrict U.ι).GeneratingSections) [IsIso σ.π] :
    IsIso (generatingSectionsOverOfRestrict σ).π :=
  GeneratingSections.isIso_ofIso_π _ _
    (hσ := GeneratingSections.isIso_mapOfAdjunction_π σ (overEquiv U).symm.toAdjunction _)

/-- Generating sections of `M.over U` give generating sections of `M.restrict U.ι`. -/
noncomputable def generatingSectionsRestrictOfOver {M : X.Modules}
    (σ : (M.over U).GeneratingSections) : (M.restrict U.ι).GeneratingSections :=
  (σ.mapOfAdjunction (overEquiv U).toAdjunction (overEquivFunctorObjUnitIso U).symm).ofIso
    ((overFunctorEquiv U).app M)

instance {M : X.Modules} (σ : (M.over U).GeneratingSections) [hσ : σ.IsFiniteType] :
    (generatingSectionsRestrictOfOver σ).IsFiniteType :=
  ⟨hσ.finite⟩

instance {M : X.Modules} (σ : (M.over U).GeneratingSections) [IsIso σ.π] :
    IsIso (generatingSectionsRestrictOfOver σ).π :=
  GeneratingSections.isIso_ofIso_π _ _
    (hσ := GeneratingSections.isIso_mapOfAdjunction_π σ (overEquiv U).toAdjunction _)

/-- A presentation of `M.over U` gives one of `M.restrict U.ι`. -/
noncomputable def presentationRestrictOfOver {M : X.Modules} (P : (M.over U).Presentation) :
    (M.restrict U.ι).Presentation :=
  (P.mapOfAdjunction (overEquiv U).toAdjunction (overEquivFunctorObjUnitIso U).symm).ofIso
    ((overFunctorEquiv U).app M)

instance {M : X.Modules} (P : (M.over U).Presentation) [hP : P.IsFinite] :
    (presentationRestrictOfOver P).IsFinite :=
  ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩

end Over

section Local

variable {M : X.Modules} {ι : Type u} {U : ι → X.Opens}

/-- The quasi-coherent data of a module given by presentations on an open cover. -/
noncomputable def quasicoherentDataOfIsOpenCover (hU : IsOpenCover U)
    (P : ∀ i, (M.restrict (U i).ι).Presentation) : M.QuasicoherentData where
  I := ι
  X := U
  coversTop := (Opens.coversTop_iff _ U).mpr hU
  presentation i := presentationOverOfRestrict (P i)

/-- A module which has a presentation on each member of an open cover is quasi-coherent. -/
@[stacks 01BE]
lemma isQuasicoherent_of_isOpenCover (hU : IsOpenCover U)
    (P : ∀ i, (M.restrict (U i).ι).Presentation) : M.IsQuasicoherent :=
  (quasicoherentDataOfIsOpenCover hU P).isQuasicoherent

/-- A module which has a finite presentation on each member of an open cover is of finite
presentation. -/
lemma isFinitePresentation_of_isOpenCover (hU : IsOpenCover U)
    (P : ∀ i, (M.restrict (U i).ι).Presentation) [hP : ∀ i, (P i).IsFinite] :
    M.IsFinitePresentation where
  exists_quasicoherentData := by
    refine ⟨quasicoherentDataOfIsOpenCover hU P, ?_⟩
    constructor
    intro i
    have := hP i
    exact (inferInstance : (presentationOverOfRestrict (P i)).IsFinite)

/-- The local generators of a module given by generating sections on an open cover. -/
noncomputable def localGeneratorsDataOfIsOpenCover (hU : IsOpenCover U)
    (σ : ∀ i, (M.restrict (U i).ι).GeneratingSections) : M.LocalGeneratorsData where
  I := ι
  X := U
  coversTop := (Opens.coversTop_iff _ U).mpr hU
  generators i := generatingSectionsOverOfRestrict (σ i)

/-- A module which is generated by finitely many sections on each member of an open cover is of
finite type. -/
lemma isFiniteType_of_isOpenCover (hU : IsOpenCover U)
    (σ : ∀ i, (M.restrict (U i).ι).GeneratingSections) [hσ : ∀ i, (σ i).IsFiniteType] :
    M.IsFiniteType where
  exists_localGeneratorsData := by
    refine ⟨localGeneratorsDataOfIsOpenCover hU σ, ?_⟩
    constructor
    intro i
    have := hσ i
    exact (inferInstance : (generatingSectionsOverOfRestrict (σ i)).IsFiniteType)

/-- A module which is free on each member of an open cover is locally free. -/
lemma isLocallyFree_of_isOpenCover (hU : IsOpenCover U)
    (σ : ∀ i, (M.restrict (U i).ι).GeneratingSections) [hσ : ∀ i, IsIso (σ i).π] :
    M.IsLocallyFree where
  exists_isLocallyFreeData := by
    refine ⟨localGeneratorsDataOfIsOpenCover hU σ, ?_⟩
    constructor
    intro i
    have := hσ i
    exact (inferInstance : IsIso (generatingSectionsOverOfRestrict (σ i)).π)

variable (M) in
/-- A module of finite type is generated by finitely many sections on the members of an open
cover. -/
lemma exists_isOpenCover_generatingSections [M.IsFiniteType] :
    ∃ (ι : Type u) (U : ι → X.Opens) (σ : ∀ i, (M.restrict (U i).ι).GeneratingSections),
      IsOpenCover U ∧ ∀ i, (σ i).IsFiniteType := by
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  exact ⟨q.I, q.X, fun i ↦ generatingSectionsRestrictOfOver (q.generators i),
    (Opens.coversTop_iff _ _).mp q.coversTop, fun i ↦ by have := hq.isFiniteType i; infer_instance⟩

variable (M) in
/-- A module of finite presentation has a finite presentation on the members of an open
cover. -/
lemma exists_isOpenCover_finitePresentation [M.IsFinitePresentation] :
    ∃ (ι : Type u) (U : ι → X.Opens) (P : ∀ i, (M.restrict (U i).ι).Presentation),
      IsOpenCover U ∧ ∀ i, (P i).IsFinite := by
  obtain ⟨q, hq⟩ := IsFinitePresentation.exists_quasicoherentData M
  exact ⟨q.I, q.X, fun i ↦ presentationRestrictOfOver (q.presentation i),
    (Opens.coversTop_iff _ _).mp q.coversTop,
    fun i ↦ by have := hq.isFinite_presentation i; infer_instance⟩

variable (M) in
/-- A locally free module is free on the members of an open cover. -/
lemma exists_isOpenCover_basis [M.IsLocallyFree] :
    ∃ (ι : Type u) (U : ι → X.Opens) (σ : ∀ i, (M.restrict (U i).ι).GeneratingSections),
      IsOpenCover U ∧ ∀ i, IsIso (σ i).π := by
  obtain ⟨q, hq⟩ := IsLocallyFree.exists_isLocallyFreeData (M := M)
  exact ⟨q.I, q.X, fun i ↦ generatingSectionsRestrictOfOver (q.generators i),
    (Opens.coversTop_iff _ _).mp q.coversTop, fun i ↦ by have := hq.isIso i; infer_instance⟩

end Local

section Iso

variable {M N : X.Modules}

lemma isQuasicoherent_of_iso (e : M ≅ N) [M.IsQuasicoherent] : N.IsQuasicoherent :=
  (isQuasicoherent X.ringCatSheaf).prop_of_iso e ‹_›

lemma isFinitePresentation_of_iso (e : M ≅ N) [M.IsFinitePresentation] :
    N.IsFinitePresentation :=
  (isFinitePresentation X.ringCatSheaf).prop_of_iso e ‹_›

lemma isFiniteType_of_iso (e : M ≅ N) [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨ι, U, σ, hU, hσ⟩ := exists_isOpenCover_generatingSections M
  exact isFiniteType_of_isOpenCover hU (fun i ↦ (σ i).ofIso ((restrictFunctor (U i).ι).mapIso e))
    (hσ := fun i ↦ ⟨(hσ i).finite⟩)

lemma isLocallyFree_of_iso (e : M ≅ N) [M.IsLocallyFree] : N.IsLocallyFree := by
  obtain ⟨ι, U, σ, hU, hσ⟩ := exists_isOpenCover_basis M
  exact isLocallyFree_of_isOpenCover hU (fun i ↦ (σ i).ofIso ((restrictFunctor (U i).ι).mapIso e))
    (hσ := fun i ↦ GeneratingSections.isIso_ofIso_π _ _ (hσ := hσ i))

end Iso

end AlgebraicGeometry.Scheme.Modules
