/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
import SGA.Foundations.QuasiCoherent.DescentEffective
import SGA.Foundations.QuasiCoherent.DescentSections
import SGA.Foundations.QuasiCoherent.DescentQuotient
import SGA.Foundations.QuasiCoherent.Cokernel
import SGA.Foundations.QuasiCoherent.SchemeTheoreticImage
import SGA.Foundations.QuasiCoherent.SpecSections
import SGA.SGA1.ExposeVIII.ModuleDescent
import SGA.SGA1.ExposeVIII.ModuleProperties

/-!
# SGA 1, Exposé VIII, §1: descent of quasi-coherent Modules over preschemes

The global statements of §1, for a faithfully flat quasi-compact morphism `g : S' → S` of
arbitrary schemes, with the category `X.Modules` of `𝒪_X`-modules, the inverse images
`Scheme.Modules.pseudofunctor` and descent data for pseudofunctors (`Pseudofunctor.DescentData`).
As in SGA, each statement is reduced to the affine case (`ModuleDescent`, `ModuleProperties`,
`SubmoduleDescent`) by restricting to an affine open `Spec A` of `S` and choosing an affine
`Spec B` mapping onto its inverse image by a surjective local isomorphism.

* VIII.1.2 (full faithfulness of `g^*` with descent data on quasi-coherent Modules):
  `toDescentData_map_bijective_of_flat`, from `toDescentData_map_injective_of_flat` and
  `toDescentData_map_surjective_of_flat`.
* VIII.1.3 (effectiveness): `descentModule_isQuasicoherent_and_iso`. The descended module
  `Scheme.Modules.descentModule D` (sections of `E` over `g⁻¹ U` compatible with the descent
  datum) is quasi-coherent and `D ≅ g^* M` as descent data (`Scheme.Modules.descentIso`); the
  proofs are in `SGA.Foundations.QuasiCoherent.DescentLocalizing` and `…DescentEffective`.
* VIII.1.1 = VIII.1.2 + VIII.1.3: `quasiCoherentDescentStatement` proves
  `QuasiCoherentDescentStatement`.
* VIII.1.7: exactness of `G → g_* G' ⇉ h_* G''` on sections over every open, for `G`
  quasi-coherent: injectivity (`pullbackApp_injective_of_flat`) and exactness in the middle
  (`exists_unique_pullbackApp_eq`, also in the form
  `exists_unique_pullbackApp_eq_of_isDescentSection` for the canonical descent datum); sections
  of `g^* G` compatible with a homomorphism of descent data descend
  (`exists_pullbackApp_eq_of_descentData'`); for `G = 𝒪_S`, exactness on global sections
  (`exists_unique_appTop_eq`) and the stronger form that `X ↦ Γ(X, 𝒪_X)` is an fpqc sheaf
  (`isSheaf_fpqcTopology_Γ`).
* VIII.1.8 (descent of quasi-coherent quotient Modules): injectivity
  (`exists_iso_of_pullback_quotient`) and exactness in the middle (`exists_quotient_of_pullback`),
  from the descent datum induced on a quotient (`Scheme.Modules.quotientDescentData`) and VIII.1.1;
  an epimorphism is detected after inverse image (`epi_of_epi_pullback_map`).
* VIII.1.9: `comap_injective_of_flat`, `comap_map_eq_of_flat`, `exists_comap_eq_iff_of_flat`.
* VIII.1.10: `isFiniteType_pullback_iff_of_flat`, `isFinitePresentation_pullback_iff_of_flat`,
  `isLocallyFree_and_isFiniteType_pullback_iff_of_flat`, through the general reduction
  `prop_of_prop_pullback_of_flat`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace SGA.SGA1.ExposeVIII

/-- VIII.1: the fibered category of Modules on preschemes, as the pseudofunctor `X ↦ X.Modules`
with the inverse image functors. The fibered category `𝓕` of quasi-coherent Modules is its
full subcategory of quasi-coherent Modules. -/
noncomputable abbrev modulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp Bicategory.Adj.forget₁

/-- VIII.1.1, with its two parts VIII.1.2 and VIII.1.3 (proved in
`quasiCoherentDescentStatement`): a faithfully flat
quasi-compact morphism `g : S' → S` is an effective descent morphism for the fibered category of
quasi-coherent Modules. That is, the functor from Modules on `S` to Modules on `S'` with a
descent datum relative to `g` is fully faithful on quasi-coherent Modules (VIII.1.2), and every
descent datum on a quasi-coherent Module is isomorphic to the one of the inverse image of a
quasi-coherent Module on `S` (VIII.1.3). The affine case is
`SGA.SGA1.ExposeVIII.toDescentModule` with its `IsEquivalence` instance. -/
def QuasiCoherentDescentStatement : Prop :=
  ∀ ⦃S S' : Scheme.{u}⦄ (g : S' ⟶ S) [Flat g] [Surjective g] [QuasiCompact g],
    (∀ M N : S.Modules, M.IsQuasicoherent → N.IsQuasicoherent →
      Function.Bijective ((modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).map :
        (M ⟶ N) → _)) ∧
    ∀ D : modulesPseudofunctor.DescentData (fun _ : Unit ↦ g),
      (D.obj ()).IsQuasicoherent →
      ∃ M : S.Modules, M.IsQuasicoherent ∧
        Nonempty ((modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).obj M ≅ D)

set_option backward.isDefEq.respectTransparency.types false in
/-- The reduction of VIII.1.10 to the affine case VIII.1.11. Let `P` be a property of Modules
which is invariant under isomorphism, stable under inverse images, local for open covers, and
which on `Spec A` holds for `M^~` exactly when the `A`-module `M` has a property `Q`. If `Q`
descends along faithfully flat ring maps, then `P` descends along faithfully flat quasi-compact
morphisms, for quasi-coherent Modules. As in SGA, one restricts to an affine open `Spec A` of
`S`, replaces `S'` by an affine scheme `S₁ = Spec B` mapping onto it by a surjective local
isomorphism, and applies VIII.1.11 to `A → B`. -/
theorem prop_of_prop_pullback_of_flat
    (P : ∀ {X : Scheme.{u}}, X.Modules → Prop)
    (Q : ∀ {A : CommRingCat.{u}}, ModuleCat.{u} A → Prop)
    (hP_iso : ∀ {X : Scheme.{u}} {M N : X.Modules}, (M ≅ N) → P M → P N)
    (hP_pullback : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules), P M →
      P ((Scheme.Modules.pullback f).obj M))
    (hP_local : ∀ {X : Scheme.{u}} (M : X.Modules) {ι : Type u} {V : ι → Scheme.{u}}
      (g : ∀ i, V i ⟶ X), (∀ i, IsOpenImmersion (g i)) → (∀ x, ∃ i, x ∈ Set.range (g i)) →
      (∀ i, P ((Scheme.Modules.pullback (g i)).obj M)) → P M)
    (hPQ : ∀ {A : CommRingCat.{u}} (M : ModuleCat.{u} A), P (tilde M) ↔ Q M)
    (hQ : ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B), φ.hom.FaithfullyFlat → ∀ M : ModuleCat.{u} A,
      Q ((ModuleCat.extendScalars φ.hom).obj M) → Q M)
    {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g] [Surjective g] [QuasiCompact g]
    (F : S.Modules) [F.IsQuasicoherent] (h : P ((Scheme.Modules.pullback g).obj F)) : P F := by
  refine hP_local F (fun V : S.affineOpens ↦ V.2.fromSpec)
    (fun V ↦ IsAffineOpen.isOpenImmersion_fromSpec V.2) (fun x ↦ ?_) fun V ↦ ?_
  · obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top S).ge (Set.mem_univ x))
    exact ⟨V, by rwa [V.2.range_fromSpec]⟩
  -- the affine base `Spec A`, `A = Γ(S, V)`
  set j := V.2.fromSpec
  let FA := (Scheme.Modules.pullback j).obj F
  let gA := pullback.snd g j
  have hA : P ((Scheme.Modules.pullback gA).obj FA) :=
    hP_iso ((Scheme.Modules.pullbackComp (pullback.fst g j) g).app F ≪≫
      (Scheme.Modules.pullbackCongr pullback.condition).app F ≪≫
      ((Scheme.Modules.pullbackComp gA j).app F).symm) (hP_pullback _ _ h)
  -- an affine `S₁` with a surjective local isomorphism `S₁ ⟶ S' ×_S Spec A`
  have : CompactSpace ↥(Limits.pullback g j) := QuasiCompact.compactSpace_of_compactSpace gA
  obtain ⟨S₁, π, hπs, hπ, hS₁⟩ :=
    (Limits.pullback g j).exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  have : Flat π := IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ π hπ
  have : Surjective π := hπs
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (S₁.isoSpec.inv ≫ π ≫ gA)
  have hff : φ.hom.FaithfullyFlat := by
    rw [← flat_and_surjective_SpecMap_iff, hφ]
    exact ⟨inferInstance, inferInstance⟩
  -- `F_A = M^~`
  have : FA.IsQuasicoherent := inferInstance
  have : IsIso FA.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent FA
  let M := (modulesSpecToSheaf.obj FA).presheaf.obj (op ⊤)
  let e : tilde M ≅ FA := asIso (Scheme.Modules.fromTildeΓ FA)
  have h₁ : P ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde M)) := by
    refine hP_iso ((Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullbackComp π gA).app FA) ≪≫
      (Scheme.Modules.pullbackComp _ _).app FA ≪≫ (Scheme.Modules.pullbackCongr hφ.symm).app FA ≪≫
      (Scheme.Modules.pullback (Spec.map φ)).mapIso e.symm)
      (hP_pullback S₁.isoSpec.inv _ (hP_pullback π _ hA))
  have h₂ := (hPQ _).mp (hP_iso (pullbackSpecMapTildeIso φ _) h₁)
  exact hP_iso e ((hPQ _).mpr (hQ φ hff _ h₂))

open Scheme.Modules in
/-- VIII.1.10, finite type: for `g : S' → S` faithfully flat and quasi-compact, a quasi-coherent
Module `F` on `S` is of finite type if and only if `g^* F` is. -/
theorem isFiniteType_pullback_iff_of_flat {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g]
    [Surjective g] [QuasiCompact g] (F : S.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback g).obj F).IsFiniteType ↔ F.IsFiniteType := by
  refine ⟨fun h ↦ prop_of_prop_pullback_of_flat (fun M ↦ SheafOfModules.IsFiniteType.{u, u, u} M)
    (fun M ↦ Module.Finite _ M)
    (fun e _ ↦ isFiniteType_of_iso e) (fun _ _ _ ↦ inferInstance)
    (fun {_} _ {_} {_} g _ hcov h ↦ isFiniteType_of_forall_pullback g hcov h)
    (fun M ↦ isFiniteType_tilde_iff M) (fun {A B} φ hφ M h ↦ ?_) g F h, fun _ ↦ inferInstance⟩
  algebraize [φ.hom]
  have : Module.FaithfullyFlat A B := hφ
  exact (moduleFinite_baseChange_iff A B M).mp h

open Scheme.Modules in
/-- VIII.1.10, finite presentation: for `g : S' → S` faithfully flat and quasi-compact, a
quasi-coherent Module `F` on `S` is of finite presentation if and only if `g^* F` is. -/
theorem isFinitePresentation_pullback_iff_of_flat {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g]
    [Surjective g] [QuasiCompact g] (F : S.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback g).obj F).IsFinitePresentation ↔ F.IsFinitePresentation := by
  refine ⟨fun h ↦ prop_of_prop_pullback_of_flat
    (fun M ↦ SheafOfModules.IsFinitePresentation.{u, u, u} M)
    (fun M ↦ Module.FinitePresentation _ M)
    (fun e _ ↦ isFinitePresentation_of_iso e) (fun _ _ _ ↦ inferInstance)
    (fun {_} _ {_} {_} g _ hcov h ↦ isFinitePresentation_of_forall_pullback g hcov h)
    (fun M ↦ isFinitePresentation_tilde_iff M) (fun {A B} φ hφ M h ↦ ?_) g F h,
    fun _ ↦ inferInstance⟩
  algebraize [φ.hom]
  have : Module.FaithfullyFlat A B := hφ
  exact (moduleFinitePresentation_baseChange_iff A B M).mp h

open Scheme.Modules in
/-- VIII.1.10, locally free of finite type: for `g : S' → S` faithfully flat and quasi-compact, a
quasi-coherent Module `F` on `S` is locally free of finite type if and only if `g^* F` is. -/
theorem isLocallyFree_and_isFiniteType_pullback_iff_of_flat {S S' : Scheme.{u}} (g : S' ⟶ S)
    [Flat g] [Surjective g] [QuasiCompact g] (F : S.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback g).obj F).IsLocallyFree ∧
      ((Scheme.Modules.pullback g).obj F).IsFiniteType ↔ F.IsLocallyFree ∧ F.IsFiniteType := by
  refine ⟨fun h ↦ prop_of_prop_pullback_of_flat
    (fun M ↦ SheafOfModules.IsLocallyFree.{u, u, u} M ∧ SheafOfModules.IsFiniteType.{u, u, u} M)
    (fun M ↦ Module.Projective _ M ∧ Module.Finite _ M)
    (fun e h ↦ ⟨@isLocallyFree_of_iso _ _ _ e h.1, @isFiniteType_of_iso _ _ _ e h.2⟩)
    (fun _ _ h ↦ ⟨@isLocallyFree_pullback _ _ _ _ h.1, @isFiniteType_pullback _ _ _ _ h.2⟩)
    (fun {_} _ {_} {_} g _ hcov h ↦ ⟨isLocallyFree_of_forall_pullback g hcov fun i ↦ (h i).1,
      isFiniteType_of_forall_pullback g hcov fun i ↦ (h i).2⟩)
    (fun M ↦ isLocallyFree_and_isFiniteType_tilde_iff M) (fun {A B} φ hφ M h ↦ ?_) g F h,
    fun h ↦ ⟨@isLocallyFree_pullback _ _ _ _ h.1, @isFiniteType_pullback _ _ _ _ h.2⟩⟩
  algebraize [φ.hom]
  have : Module.FaithfullyFlat A B := hφ
  exact (moduleProjective_and_finite_baseChange_iff A B M).mp h

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.1.2, injectivity: for `g : S' → S` faithfully flat and quasi-compact, the inverse image
functor `g^*` is faithful on quasi-coherent Modules: two homomorphisms `u, v : M → N` with
`g^* u = g^* v` are equal. As in SGA, one reduces to an affine open `Spec A` of `S` and to an
affine `S₁ = Spec B` mapping onto its inverse image, where this is the injectivity of
`u ↦ B ⊗_A u` (VIII.1.4). -/
theorem pullback_map_injective_of_flat {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g] [Surjective g]
    [QuasiCompact g] {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] {u v : M ⟶ N}
    (h : (Scheme.Modules.pullback g).map u = (Scheme.Modules.pullback g).map v) : u = v := by
  refine Scheme.Modules.hom_ext_of_pullback (fun V : S.affineOpens ↦ V.2.fromSpec) (fun x ↦ ?_)
    fun V ↦ ?_
  · obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top S).ge (Set.mem_univ x))
    exact ⟨V, by rwa [V.2.range_fromSpec]⟩
  set j := V.2.fromSpec
  let gA := pullback.snd g j
  have hA : (Scheme.Modules.pullback gA).map ((Scheme.Modules.pullback j).map u) =
      (Scheme.Modules.pullback gA).map ((Scheme.Modules.pullback j).map v) :=
    (Scheme.Modules.pullback j ⋙ Scheme.Modules.pullback gA).map_eq_map_of_iso
      (Scheme.Modules.pullbackComp gA j ≪≫ Scheme.Modules.pullbackCongr pullback.condition.symm ≪≫
        (Scheme.Modules.pullbackComp _ g).symm)
      (h := congr((Scheme.Modules.pullback (pullback.fst g j)).map $h))
  -- an affine `S₁ = Spec B` mapping onto `S' ×_S Spec A`
  have : CompactSpace ↥(Limits.pullback g j) := QuasiCompact.compactSpace_of_compactSpace gA
  obtain ⟨S₁, π, hπs, hπ, hS₁⟩ :=
    (Limits.pullback g j).exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  have : Flat π := IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ π hπ
  have : Surjective π := hπs
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (S₁.isoSpec.inv ≫ π ≫ gA)
  have hff : φ.hom.FaithfullyFlat := by
    rw [← flat_and_surjective_SpecMap_iff, hφ]
    exact ⟨inferInstance, inferInstance⟩
  have h₁ : (Scheme.Modules.pullback (Spec.map φ)).map ((Scheme.Modules.pullback j).map u) =
      (Scheme.Modules.pullback (Spec.map φ)).map ((Scheme.Modules.pullback j).map v) :=
    (Scheme.Modules.pullback (Spec.map φ)).map_eq_map_of_iso
      (Scheme.Modules.pullbackCongr hφ ≪≫ (Scheme.Modules.pullbackComp _ _).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.pullbackComp _ _).symm _)
      (h := congr((Scheme.Modules.pullback S₁.isoSpec.inv).map
        ((Scheme.Modules.pullback π).map $hA)))
  -- the quasi-coherent modules `j^* M` and `j^* N` on `Spec A`
  let MA := (Scheme.Modules.pullback j).obj M
  let NA := (Scheme.Modules.pullback j).obj N
  let eM : tilde _ ≅ MA :=
    @asIso _ _ _ _ MA.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent MA)
  let eN : tilde _ ≅ NA :=
    @asIso _ _ _ _ NA.fromTildeΓ (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent NA)
  have hu := (Iso.eq_inv_comp eM).mpr
    (Scheme.Modules.fromTildeΓNatTrans.naturality ((Scheme.Modules.pullback j).map u)).symm
  have hv := (Iso.eq_inv_comp eM).mpr
    (Scheme.Modules.fromTildeΓNatTrans.naturality ((Scheme.Modules.pullback j).map v)).symm
  simp only [Functor.id_map, Functor.comp_map] at hu hv
  suffices H : moduleSpecΓFunctor.map ((Scheme.Modules.pullback j).map u) =
      moduleSpecΓFunctor.map ((Scheme.Modules.pullback j).map v) by
    rw [hu, hv]
    exact congrArg (fun w ↦ eM.inv ≫ (tilde.functor _).map w ≫ eN.hom) H
  have key : (tilde.functor _ ⋙ Scheme.Modules.pullback (Spec.map φ)).map
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullback j).map u)) =
      (tilde.functor _ ⋙ Scheme.Modules.pullback (Spec.map φ)).map
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullback j).map v)) :=
    (Scheme.Modules.pullback (Spec.map φ)).map_eq_map_of_conj eM eN hu hv h₁
  have key₂ := (tilde.functor _).map_injective
    ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor _).map_eq_map_of_iso
      (tildeCompPullbackSpecMapIso φ).symm key)
  algebraize [φ.hom]
  have : Module.FaithfullyFlat Γ(S, V) Γ(S₁, ⊤) := hff
  ext1
  exact baseChange_injective_of_faithfullyFlat (A := Γ(S, V)) (B := Γ(S₁, ⊤))
    congr(ModuleCat.Hom.hom $key₂)

set_option backward.isDefEq.respectTransparency.types false in
open Scheme.Modules in
/-- The affine case of the injectivity of `G → g_* g^* G`. -/
theorem pullbackApp_injective_of_flat_of_isAffineOpen {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g]
    [Surjective g] [QuasiCompact g] (N : S.Modules) [N.IsQuasicoherent] (V : S.affineOpens) :
    Function.Injective (pullbackApp g N V) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  set j := V.2.fromSpec
  have hj : j ⁻¹ᵁ V = ⊤ := V.2.fromSpec_preimage_self
  let gA := pullback.snd g j
  have : CompactSpace ↥(Limits.pullback g j) := QuasiCompact.compactSpace_of_compactSpace gA
  obtain ⟨S₁, π, hπs, hπ, hS₁⟩ :=
    (Limits.pullback g j).exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  have : Flat π := IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ π hπ
  have : Surjective π := hπs
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (S₁.isoSpec.inv ≫ π ≫ gA)
  have hff : φ.hom.FaithfullyFlat := by
    rw [← flat_and_surjective_SpecMap_iff, hφ]
    exact ⟨inferInstance, inferInstance⟩
  -- the section `s` vanishes after pullback to `Spec B`
  have h₁ : pullbackApp (Spec.map φ ≫ j) N V s = 0 := by
    have e : (S₁.isoSpec.inv ≫ π ≫ pullback.fst g j) ≫ g = Spec.map φ ≫ j := by
      rw [hφ, Category.assoc, Category.assoc, Category.assoc, Category.assoc, pullback.condition]
    exact (pullbackApp_eq_zero_congr e N V s).mp (pullbackApp_comp_eq_zero _ g N V s hs)
  have h₂ := pullbackApp_eq_zero_of_comp _ _ _ _ _ h₁
  -- the corresponding global section `x` of `j^* N`
  let NA := (Scheme.Modules.pullback j).obj N
  have hle : (⊤ : (Spec Γ(S, V)).Opens) ≤ j ⁻¹ᵁ V := hj.ge
  let x : Γ(NA, ⊤) := NA.presheaf.map (homOfLE hle).op (pullbackApp j N V s)
  have hx : pullbackApp (Spec.map φ) NA ⊤ x = 0 := by
    simp only [x]
    rw [pullbackApp_map, h₂, map_zero]
  suffices x = 0 by
    have h₃ : pullbackApp j N V s = 0 :=
      (injective_iff_map_eq_zero' _).mp (NA.presheaf.map_injective_of_eq _ hj.symm) _ |>.mp this
    rw [pullbackApp_eq_zero_iff_of_isOpenImmersion] at h₃
    refine (injective_iff_map_eq_zero' _).mp (N.presheaf.map_injective_of_eq _ ?_) _ |>.mp h₃
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, V.2.opensRange_fromSpec, inf_idem]
  -- `j^* N = N₀^~`
  let N₀ := (modulesSpecToSheaf.obj NA).presheaf.obj (op ⊤)
  have : IsIso NA.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent NA
  have hfrom : NA.fromTildeΓ.app ⊤ (tilde.toOpen N₀ ⊤ x) = x := by
    have := congr($(Scheme.Modules.toOpen_fromTildeΓ_app NA ⊤).hom x)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, homOfLE_refl, op_id,
      CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.id_apply] at this
    exact this
  have hy : pullbackApp (Spec.map φ) (tilde N₀) ⊤ (tilde.toOpen N₀ ⊤ x) = 0 := by
    have := pullbackApp_naturality (Spec.map φ) NA.fromTildeΓ ⊤ (tilde.toOpen N₀ ⊤ x)
    rw [hfrom, hx] at this
    exact (injective_iff_map_eq_zero' _).mp (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pullback (Spec.map φ)).map NA.fromTildeΓ).app _)).1 _ |>.mp this.symm
  have hz := pullbackApp_SpecMap_tilde φ N₀ x
  rw [hy, map_zero] at hz
  have h1x : (toExtendScalars N₀ φ x : (ModuleCat.extendScalars φ.hom).obj N₀) = 0 :=
    (injective_iff_map_eq_zero' _).mp (ConcreteCategory.bijective_of_isIso
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj N₀) ⊤)).1 _ |>.mp hz.symm
  algebraize [φ.hom]
  have : Module.FaithfullyFlat Γ(S, V) Γ(S₁, ⊤) := hff
  exact (injective_iff_map_eq_zero' _).mp
    (Module.FaithfullyFlat.tensorProduct_mk_injective (A := Γ(S, V)) (B := Γ(S₁, ⊤)) N₀) x |>.mp
    h1x

open Scheme.Modules in
/-- VIII.1.7, injectivity: for `g : S' → S` faithfully flat and quasi-compact and `G`
quasi-coherent, `G → g_* g^* G` is injective on sections over every open `U`. -/
theorem pullbackApp_injective_of_flat {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g] [Surjective g]
    [QuasiCompact g] (N : S.Modules) [N.IsQuasicoherent] (U : S.Opens) :
    Function.Injective (pullbackApp g N U) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun V : {V : S.affineOpens // V.1 ≤ U} ↦ V.1.1) U (fun V ↦ homOfLE V.2) (fun x hx ↦ ?_) _ _
    fun V ↦ ?_
  · obtain ⟨V, hV, hxV, hVU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩
  · rw [map_zero]
    refine (injective_iff_map_eq_zero' _).mp
      (pullbackApp_injective_of_flat_of_isAffineOpen g N V.1) _ |>.mp ?_
    rw [pullbackApp_map, hs, map_zero]

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.1.7 for `G = 𝒪_S`, injectivity: for a faithfully flat `g`, the map `𝒪_S → g_* 𝒪_{S'}` is
injective, i.e. every `Γ(S, U) → Γ(S', g⁻¹ U)` is injective. The stalk maps are faithfully flat
local homomorphisms; quasi-compactness is not needed. -/
lemma app_injective_of_flat_of_surjective {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g]
    [Surjective g] (U : S.Opens) : Function.Injective (g.app U) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Presheaf.section_ext S.sheaf U s 0 fun y hy ↦ ?_
  obtain ⟨x, rfl⟩ := g.surjective y
  have hinj : Function.Injective (g.stalkMap x) := by
    algebraize [(g.stalkMap x).hom]
    have : Module.FaithfullyFlat (S.presheaf.stalk (g x)) (S'.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap g x) (g.toLRSHom.prop x)
    exact ‹RingHom.FaithfullyFlat _›.injective
  apply hinj
  change g.stalkMap x (S.presheaf.germ U (g x) hy s) = g.stalkMap x (S.presheaf.germ U (g x) hy 0)
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, hs]
  simp

/-- A faithfully flat morphism is scheme-theoretically dominant (its kernel is zero). -/
lemma isSchemeTheoreticallyDominant_of_flat_of_surjective {S S' : Scheme.{u}} (g : S' ⟶ S)
    [Flat g] [Surjective g] : IsSchemeTheoreticallyDominant g := by
  refine ⟨eq_bot_iff.mpr fun U ↦ ?_⟩
  refine (g.ideal_ker_le U).trans ?_
  rw [(RingHom.injective_iff_ker_eq_bot _).mp (app_injective_of_flat_of_surjective g U)]
  exact bot_le

/-- For `g` faithfully flat and quasi-compact, every closed subscheme `I` of `S` is the
scheme-theoretic image of its inverse image in `S'`. -/
lemma map_comap_of_flat {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g] [Surjective g]
    [QuasiCompact g] (I : S.IdealSheafData) : (I.comap g).map g = I := by
  have := isSchemeTheoreticallyDominant_of_flat_of_surjective (pullback.snd g I.subschemeι)
  rw [Scheme.IdealSheafData.comap, Scheme.IdealSheafData.map_ker, pullback.condition,
    ← Scheme.IdealSheafData.map_ker, (pullback.snd g I.subschemeι).ker_eq_bot,
    Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]

/-- VIII.1.9, injectivity: for `g` faithfully flat and quasi-compact, a closed subscheme of `S` is
determined by its inverse image in `S'`. -/
theorem comap_injective_of_flat {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g] [Surjective g]
    [QuasiCompact g] : Function.Injective (fun I : S.IdealSheafData ↦ I.comap g) := by
  intro I J h
  rw [← map_comap_of_flat g I, ← map_comap_of_flat g J]
  exact congrArg (·.map g) h

/-- VIII.1.9, exactness in the middle: for `g : S' → S` faithfully flat and quasi-compact, a
closed subscheme `I'` of `S'` whose two inverse images in `S'' = S' ×_S S'` coincide is the
inverse image of a closed subscheme of `S`, namely of its scheme-theoretic image `I'.map g`.
Closed subschemes are recorded by their ideal sheaves; the inverse image of a closed subscheme
is the fibered product, `IdealSheafData.comap`. The proof uses that scheme-theoretic images
commute with flat base change (`Scheme.Hom.ker_comap_of_flat`) instead of VIII.1.8. -/
theorem comap_map_eq_of_flat {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g] [Surjective g]
    [QuasiCompact g] (I' : S'.IdealSheafData)
    (h : I'.comap (pullback.fst g g) = I'.comap (pullback.snd g g)) :
    (I'.map g).comap g = I' := by
  rw [Scheme.IdealSheafData.map, Scheme.Hom.ker_comap_of_flat,
    ← Scheme.Hom.ker_comp_of_isIso (pullbackLeftPullbackSndIso g g I'.subschemeι).hom,
    pullbackLeftPullbackSndIso_hom_fst, Scheme.Hom.ker_comp]
  change (I'.comap (pullback.snd g g)).map (pullback.fst g g) = I'
  rw [← h, map_comap_of_flat]

/-- VIII.1.9: for `g : S' → S` faithfully flat and quasi-compact, the diagram
`H(S) → H(S') ⇉ H(S'')` of sets of closed subschemes is exact: a closed subscheme of `S'` is the
inverse image of a closed subscheme of `S` if and only if its two inverse images in
`S'' = S' ×_S S'` coincide, and the latter is then unique (`comap_injective_of_flat`). -/
theorem exists_comap_eq_iff_of_flat {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g] [Surjective g]
    [QuasiCompact g] (I' : S'.IdealSheafData) :
    (∃ I : S.IdealSheafData, I.comap g = I') ↔
      I'.comap (pullback.fst g g) = I'.comap (pullback.snd g g) := by
  refine ⟨?_, fun h ↦ ⟨_, comap_map_eq_of_flat g I' h⟩⟩
  rintro ⟨I, rfl⟩
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, pullback.condition]

/-- Global sections of `𝒪_X` are morphisms to the affine line `Spec ℤ[t]`. -/
noncomputable abbrev homAffineLineEquivSections (X : Scheme.{u}) :
    (X ⟶ Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))) ≃ Γ(X, ⊤) :=
  (AffineSpace.toSpecMvPolyIntEquiv (X := X) PUnit.{u + 1}).trans (Equiv.funUnique _ _)

lemma homAffineLineEquivSections_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : Y ⟶ Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))) :
    homAffineLineEquivSections X (f ≫ e) = f.appTop (homAffineLineEquivSections Y e) :=
  AffineSpace.toSpecMvPolyIntEquiv_comp _ f e _

/-- VIII.1.7 for `G = 𝒪_S`, on global sections: for a faithfully flat quasi-compact
`g : S' → S`, the diagram `Γ(S, 𝒪_S) → Γ(S', 𝒪_{S'}) ⇉ Γ(S'', 𝒪_{S''})` is exact. SGA states
exactness of the diagram of sheaves `G → g_* G' ⇉ h_* G''` for every quasi-coherent `G`; the
affine case of that is `range_mk_eq_eqLocus`. -/
theorem exists_unique_appTop_eq {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g] [Surjective g]
    [QuasiCompact g] (s' : Γ(S', ⊤))
    (h : (pullback.fst g g).appTop s' = (pullback.snd g g).appTop s') :
    ∃! s : Γ(S, ⊤), g.appTop s = s' := by
  let f' := (homAffineLineEquivSections S').symm s'
  have hf' : pullback.fst g g ≫ f' = pullback.snd g g ≫ f' := by
    apply (homAffineLineEquivSections _).injective
    rw [homAffineLineEquivSections_comp, homAffineLineEquivSections_comp, Equiv.apply_symm_apply, h]
  let f := EffectiveEpi.desc g f' fun g₁ g₂ hg ↦ by
    calc g₁ ≫ f' = pullback.lift g₁ g₂ hg ≫ pullback.fst g g ≫ f' := by
          rw [pullback.lift_fst_assoc]
      _ = pullback.lift g₁ g₂ hg ≫ pullback.snd g g ≫ f' := by rw [hf']
      _ = g₂ ≫ f' := by rw [pullback.lift_snd_assoc]
  refine ⟨homAffineLineEquivSections S f, ?_, fun s hs ↦ ?_⟩
  · change g.appTop (homAffineLineEquivSections S f) = s'
    rw [← homAffineLineEquivSections_comp, EffectiveEpi.fac, Equiv.apply_symm_apply]
  · rw [← Equiv.apply_symm_apply (homAffineLineEquivSections S) s]
    congr 1
    apply EffectiveEpi.uniq
    apply (homAffineLineEquivSections _).injective
    rw [homAffineLineEquivSections_comp, Equiv.apply_symm_apply, hs, Equiv.apply_symm_apply]

/-- `X ↦ Hom(E, Γ(X, 𝒪_X))` is represented by `Spec E`. -/
noncomputable def ΓCompCoyonedaIso (E : CommRingCat.{u}) :
    Scheme.Γ ⋙ coyoneda.obj (op E) ≅ yoneda.obj (Spec E) :=
  NatIso.ofComponents
    (fun X ↦ Equiv.toIso ((opEquiv (Scheme.Γ.rightOp.obj X.unop) (op E)).symm.trans
      (ΓSpec.adjunction.homEquiv X.unop (op E))))
    (fun {X Y} f ↦ by
      ext φ
      change ΓSpec.adjunction.homEquiv Y.unop (op E) (Scheme.Γ.rightOp.map f.unop ≫ φ.op) =
        f.unop ≫ ΓSpec.adjunction.homEquiv X.unop (op E) φ.op
      rw [Adjunction.homEquiv_naturality_left])

/-- VIII.1.7 for `G = 𝒪_S`, in sheaf form: the functor `X ↦ Γ(X, 𝒪_X)` on all schemes is a sheaf
for the fpqc topology. Applied to the covering `g⁻¹(U) → U` for an open `U` of `S`, this is the
exactness of `Γ(U, 𝒪_S) → Γ(g⁻¹ U, 𝒪_{S'}) ⇉ Γ(h⁻¹ U, 𝒪_{S''})`. -/
theorem isSheaf_fpqcTopology_Γ : Presheaf.IsSheaf Scheme.fpqcTopology Scheme.Γ.{u} := by
  intro E
  exact Presieve.isSheaf_iso _ (ΓCompCoyonedaIso E).symm
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

/-- VIII.1.2, injectivity, for the descent data functor: for `g : S' → S` faithfully flat and
quasi-compact, `Hom_S(F, G) → Hom_{S'}(F', G')` is injective for quasi-coherent `F` and `G`. -/
theorem toDescentData_map_injective_of_flat {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g]
    [Surjective g] [QuasiCompact g] (M N : S.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Injective ((modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).map :
      (M ⟶ N) → _) :=
  fun _ _ h ↦ pullback_map_injective_of_flat g (congrArg (fun φ ↦ φ.hom ()) h)

section FullFaithfulness

/-! ### VIII.1.2: full faithfulness

The proof follows SGA: a homomorphism of descent data `g^* M ⟶ g^* N` is determined on sections
over an affine open `V = Spec A` of `S` by the affine case VIII.1.4 (for a faithfully flat
`A → B`, with `Spec B` a surjective local isomorphism onto `g⁻¹ V`), and the sections so obtained
glue since `N` is a sheaf. -/

open Scheme.Modules TensorProduct

set_option backward.isDefEq.respectTransparency false in
lemma mapComp'_hom_toNatTrans_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z)
    (h : f ≫ g = q) (N : Z.Modules) :
    (modulesPseudofunctor.mapComp' g.op.toLoc f.op.toLoc q.op.toLoc
      (by rw [← h]; rfl)).hom.toNatTrans.app N = (pullbackCompIso' f g q h N).hom := by
  subst h
  simp [Pseudofunctor.mapComp', pullbackCompIso']
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma mapComp'_inv_toNatTrans_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z)
    (h : f ≫ g = q) (N : Z.Modules) :
    (modulesPseudofunctor.mapComp' g.op.toLoc f.op.toLoc q.op.toLoc
      (by rw [← h]; rfl)).inv.toNatTrans.app N = (pullbackCompIso' f g q h N).inv := by
  subst h
  simp [Pseudofunctor.mapComp', pullbackCompIso']
  rfl

section ExtendScalars

variable {A B : CommRingCat.{u}} (N₀ : ModuleCat.{u} A) (φ : A ⟶ B)

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.1.5, in terms of extension of scalars: for `φ : A → B` faithfully flat, an element of
`B ⊗_A N₀` whose images in `(B ⊗_A B) ⊗_A N₀` under the two inclusions agree is of the
form `1 ⊗ n`. -/
lemma exists_eq_toExtendScalars_of_extendScalarsMap_eq (hφ : φ.hom.FaithfullyFlat)
    (y : (ModuleCat.extendScalars φ.hom).obj N₀)
    (h : extendScalarsMap N₀ φ (φ ≫ tensorSelfInl φ) (tensorSelfInl φ) rfl y =
      extendScalarsMap N₀ φ (φ ≫ tensorSelfInl φ) (tensorSelfInr φ) (tensorSelf_comm φ).symm y) :
    ∃ n : N₀, oneTmul N₀ φ n = y := by
  algebraize [φ.hom]
  have : Module.FaithfullyFlat A B := hφ
  let e : (ModuleCat.restrictScalars (φ ≫ tensorSelfInl φ).hom).obj
      (ModuleCat.of (tensorSelf φ) (tensorSelf φ)) ≃ₗ[A] B ⊗[A] B :=
    { toFun := id
      invFun := id
      map_add' _ _ := rfl
      map_smul' a c := by
        change (φ.hom a ⊗ₜ[A] (1 : B)) * (show B ⊗[A] B from c) = a • (show B ⊗[A] B from c)
        rw [Algebra.smul_def]; rfl
      left_inv _ := rfl
      right_inv _ := rfl }
  let E := TensorProduct.congr e (LinearEquiv.refl A N₀)
  have hl (z : (ModuleCat.extendScalars φ.hom).obj N₀) :
      E (extendScalarsMap N₀ φ (φ ≫ tensorSelfInl φ) (tensorSelfInl φ) rfl z) =
        rTensorIncludeLeft A B N₀ z := by
    induction z using TensorProduct.induction_on with
    | zero => erw [map_zero]
    | add x y hx hy => erw [map_add, map_add, map_add, hx, hy]
    | tmul b n => rfl
  have hr (z : (ModuleCat.extendScalars φ.hom).obj N₀) :
      E (extendScalarsMap N₀ φ (φ ≫ tensorSelfInl φ) (tensorSelfInr φ) (tensorSelf_comm φ).symm z) =
        rTensorIncludeRight A B N₀ z := by
    induction z using TensorProduct.induction_on with
    | zero => erw [map_zero]
    | add x y hx hy => erw [map_add, map_add, map_add, hx, hy]
    | tmul b n => rfl
  have hy : y ∈ LinearMap.eqLocus (rTensorIncludeLeft A B N₀) (rTensorIncludeRight A B N₀) := by
    change rTensorIncludeLeft A B N₀ y = rTensorIncludeRight A B N₀ y
    rw [← hl, ← hr, h]
  rw [← range_mk_eq_eqLocus] at hy
  obtain ⟨n, hn⟩ := hy
  exact ⟨n, hn⟩

end ExtendScalars

section Chart

variable {S : Scheme.{u}} (V : S.affineOpens) (N : S.Modules)

/-- The module `N₀ = Γ(Spec A, j^* N)` over `A = Γ(S, V)`, for `j : Spec A ⟶ S` the inclusion of
the affine open `V`. -/
noncomputable abbrev chartModule : ModuleCat Γ(S, V) :=
  (modulesSpecToSheaf.obj ((Scheme.Modules.pullback V.2.fromSpec).obj N)).presheaf.obj (op ⊤)

/-- For `N` quasi-coherent, `j^* N ≅ N₀^~`. -/
noncomputable def chartIso [N.IsQuasicoherent] :
    tilde (chartModule V N) ≅ (Scheme.Modules.pullback V.2.fromSpec).obj N :=
  @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ _)
    (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent _)

lemma chartIso_hom_app_toOpen [N.IsQuasicoherent] (x : chartModule V N) :
    (chartIso V N).hom.app ⊤ (tilde.toOpen (chartModule V N) ⊤ x) = x := by
  have := congr($(Scheme.Modules.toOpen_fromTildeΓ_app
    ((Scheme.Modules.pullback V.2.fromSpec).obj N) ⊤).hom x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.id_apply] at this
  exact this

lemma chartIso_inv_app (x : chartModule V N) [N.IsQuasicoherent] :
    (chartIso V N).inv.app ⊤ x = tilde.toOpen (chartModule V N) ⊤ x := by
  conv_lhs => rw [← chartIso_hom_app_toOpen V N x]
  exact iso_inv_app_hom_app (chartIso V N) ⊤ _

lemma top_le_preimage_fromSpec : ⊤ ≤ V.2.fromSpec ⁻¹ᵁ (V : S.Opens) :=
  V.2.fromSpec_preimage_self.ge

/-- The section of `N₀` corresponding to a section of `N` over `V`. -/
noncomputable def chartSection : Γ(N, V) →+ chartModule V N :=
  (pullbackAppTop V.2.fromSpec N V (top_le_preimage_fromSpec V)).hom

lemma chartSection_bijective : Function.Bijective (chartSection V N) := by
  have := IsAffineOpen.isOpenImmersion_fromSpec V.2
  have e : ⇑(chartSection V N) =
      ⇑(((Scheme.Modules.pullback V.2.fromSpec).obj N).presheaf.map
        (homOfLE (top_le_preimage_fromSpec V)).op) ∘ ⇑(pullbackApp V.2.fromSpec N V) := by
    ext x
    exact ConcreteCategory.comp_apply _ _ x
  rw [e]
  have h₁ := pullbackApp_bijective_of_isOpenImmersion V.2.fromSpec N V V.2.opensRange_fromSpec.ge
  have h₂ := ((Scheme.Modules.pullback V.2.fromSpec).obj N).presheaf.map_bijective_of_eq
    (homOfLE (top_le_preimage_fromSpec V)) V.2.fromSpec_preimage_self.symm
  exact h₂.comp h₁

variable {S' : Scheme.{u}} (g : S' ⟶ S) [N.IsQuasicoherent]

/-- For `w : Spec C ⟶ S'` over `Spec C ⟶ Spec A` (via `α : A ⟶ C`), the identification of the
global sections of `w^* g^* N` with `C ⊗_A N₀`. -/
noncomputable def chartΘ {C : CommRingCat.{u}} (α : Γ(S, V) ⟶ C) (w : Spec C ⟶ S')
    (q : Spec C ⟶ S) (hw : w ≫ g = q) (hα : Spec.map α ≫ V.2.fromSpec = q) :
    Γ((Scheme.Modules.pullback w).obj ((Scheme.Modules.pullback g).obj N), ⊤) ≃+
      (ModuleCat.extendScalars α.hom).obj (chartModule V N) :=
  (isoAppAddEquiv (pullbackCompIso' w g q hw N).symm ⊤).trans <|
    (isoAppAddEquiv (pullbackCompIso' (Spec.map α) V.2.fromSpec q hα N) ⊤).trans <|
    (isoAppAddEquiv ((Scheme.Modules.pullback (Spec.map α)).mapIso (chartIso V N).symm) ⊤).trans <|
    (isoAppAddEquiv (pullbackSpecMapTildeIso α (chartModule V N)) ⊤).trans
    (tilde.isoTop _).toLinearEquiv.symm.toAddEquiv

lemma chartΘ_apply {C : CommRingCat.{u}} (α : Γ(S, V) ⟶ C) (w : Spec C ⟶ S')
    (q : Spec C ⟶ S) (hw : w ≫ g = q) (hα : Spec.map α ≫ V.2.fromSpec = q)
    (z : Γ((Scheme.Modules.pullback w).obj ((Scheme.Modules.pullback g).obj N), ⊤)) :
    chartΘ V N g α w q hw hα z = (tilde.isoTop _).inv (((pullbackSpecMapTildeIso α _).hom.app ⊤)
      (((Scheme.Modules.pullback (Spec.map α)).map (chartIso V N).inv).app ⊤
      (((pullbackCompIso' (Spec.map α) V.2.fromSpec q hα N).hom.app ⊤)
      (((pullbackCompIso' w g q hw N).inv.app ⊤) z)))) := rfl

lemma chartΘ_pullbackAppTop {C : CommRingCat.{u}} (α : Γ(S, V) ⟶ C) (w : Spec C ⟶ S')
    (q : Spec C ⟶ S) (hw : w ≫ g = q) (hα : Spec.map α ≫ V.2.fromSpec = q)
    (hwV : ⊤ ≤ w ⁻¹ᵁ (g ⁻¹ᵁ (V : S.Opens))) (x : Γ(N, V)) :
    chartΘ V N g α w q hw hα (pullbackAppTop w ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ V) hwV
      (pullbackApp g N V x)) = oneTmul (chartModule V N) α (chartSection V N x) := by
  have hqV : ⊤ ≤ q ⁻¹ᵁ (V : S.Opens) := by rw [← hw]; exact hwV
  have hαV : ⊤ ≤ Spec.map α ⁻¹ᵁ (V.2.fromSpec ⁻¹ᵁ (V : S.Opens)) := by
    rw [V.2.fromSpec_preimage_self]; exact le_rfl
  rw [chartΘ_apply, pullbackCompIso'_inv_app_pullbackAppTop w g q hw N V hqV hwV x,
    pullbackCompIso'_hom_app_pullbackAppTop (Spec.map α) V.2.fromSpec q hα N V hqV hαV x,
    pullbackAppTop_eq_pullbackApp_map (Spec.map α) _ _ (top_le_preimage_fromSpec V) hαV]
  have e₅ : ((Scheme.Modules.pullback (Spec.map α)).map (chartIso V N).inv).app ⊤
      (pullbackApp (Spec.map α) ((Scheme.Modules.pullback V.2.fromSpec).obj N) ⊤
        (((Scheme.Modules.pullback V.2.fromSpec).obj N).presheaf.map
          (homOfLE (top_le_preimage_fromSpec V)).op (pullbackApp V.2.fromSpec N V x))) =
      pullbackApp (Spec.map α) (tilde (chartModule V N)) ⊤
        ((chartIso V N).inv.app ⊤ (chartSection V N x)) :=
    (pullbackApp_naturality (Spec.map α) (chartIso V N).inv ⊤ _).symm
  rw [e₅]
  have e₆ : (chartIso V N).inv.app ⊤ (chartSection V N x) =
      tilde.toOpen (chartModule V N) ⊤ (chartSection V N x) := chartIso_inv_app V N _
  rw [e₆]
  have e₇ := pullbackApp_SpecMap_tilde α (chartModule V N) (chartSection V N x)
  exact (congrArg (tilde.isoTop _).inv e₇).trans ((tilde.isoTop _).hom_inv_id_apply _)

lemma chartΘ_smul {C : CommRingCat.{u}} (α : Γ(S, V) ⟶ C) (w : Spec C ⟶ S')
    (q : Spec C ⟶ S) (hw : w ≫ g = q) (hα : Spec.map α ≫ V.2.fromSpec = q) (c : C)
    (z : Γ((Scheme.Modules.pullback w).obj ((Scheme.Modules.pullback g).obj N), ⊤)) :
    chartΘ V N g α w q hw hα (c • z) = c • chartΘ V N g α w q hw hα z := by
  rw [chartΘ_apply, chartΘ_apply, Hom.app_smul_Spec, Hom.app_smul_Spec, Hom.app_smul_Spec,
    Hom.app_smul_Spec]
  exact map_smul (tilde.isoTop _).inv.hom c _

lemma chartΘ_symm_smul {C : CommRingCat.{u}} (α : Γ(S, V) ⟶ C) (w : Spec C ⟶ S')
    (q : Spec C ⟶ S) (hw : w ≫ g = q) (hα : Spec.map α ≫ V.2.fromSpec = q) (c : C)
    (y : (ModuleCat.extendScalars α.hom).obj (chartModule V N)) :
    (chartΘ V N g α w q hw hα).symm (c • y) = c • (chartΘ V N g α w q hw hα).symm y := by
  apply (chartΘ V N g α w q hw hα).injective
  rw [chartΘ_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

set_option maxRecDepth 10000 in
open ModuleCat ChangeOfRings in
/-- Compatibility of `chartΘ` with inverse images along `Spec C' ⟶ Spec C`. -/
lemma chartΘ_pullbackApp {C C' : CommRingCat.{u}} (α : Γ(S, V) ⟶ C) (α' : Γ(S, V) ⟶ C')
    (β : C ⟶ C') (hβ : α ≫ β = α') (w : Spec C ⟶ S') (q : Spec C ⟶ S) (hw : w ≫ g = q)
    (hα : Spec.map α ≫ V.2.fromSpec = q) (w' : Spec C' ⟶ S') (hw' : Spec.map β ≫ w = w')
    (q' : Spec C' ⟶ S) (hq' : w' ≫ g = q') (hα' : Spec.map α' ≫ V.2.fromSpec = q')
    (hwV : ⊤ ≤ w ⁻¹ᵁ (g ⁻¹ᵁ (V : S.Opens)))
    (z : Γ((Scheme.Modules.pullback w).obj ((Scheme.Modules.pullback g).obj N), ⊤)) :
    chartΘ V N g α' w' q' hq' hα' (((pullbackCompIso' (Spec.map β) w w' hw' _).inv.app ⊤)
      (pullbackApp (Spec.map β) _ ⊤ z)) =
      extendScalarsMap (chartModule V N) α α' β hβ (chartΘ V N g α w q hw hα z) := by
  have hw'V : ⊤ ≤ w' ⁻¹ᵁ (g ⁻¹ᵁ (V : S.Opens)) := by
    rw [← hw']; exact fun x _ ↦ hwV (Set.mem_univ _)
  let : Module C ((ModuleCat.extendScalars α'.hom).obj (chartModule V N)) :=
    Module.compHom _ β.hom
  let L : (ModuleCat.extendScalars α.hom).obj (chartModule V N) →+
      (ModuleCat.extendScalars α'.hom).obj (chartModule V N) :=
    (chartΘ V N g α' w' q' hq' hα').toAddMonoidHom.comp <|
      ((pullbackCompIso' (Spec.map β) w w' hw' _).inv.app ⊤).hom.comp <|
      (pullbackApp (Spec.map β) _ ⊤).hom.comp (chartΘ V N g α w q hw hα).symm.toAddMonoidHom
  have hL (y) : L y = chartΘ V N g α' w' q' hq' hα' (((pullbackCompIso' (Spec.map β) w w' hw'
      _).inv.app ⊤) (pullbackApp (Spec.map β) _ ⊤ ((chartΘ V N g α w q hw hα).symm y))) := rfl
  have key : L = extendScalarsMap (chartModule V N) α α' β hβ := by
    refine extendScalars_addHom_ext _ _ (fun c y ↦ ?_) (fun c y ↦ ?_) fun m ↦ ?_
    · rw [hL, hL, chartΘ_symm_smul, pullbackApp_SpecMap_smul]
      erw [Hom.app_smul_Spec]
      rw [chartΘ_smul]
      rfl
    · exact extendScalarsMap_smul _ α α' β hβ c y
    · obtain ⟨x, rfl⟩ := (chartSection_bijective V N).2 m
      have h0 : (chartΘ V N g α w q hw hα).symm (oneTmul (chartModule V N) α
          (chartSection V N x)) = pullbackAppTop w ((Scheme.Modules.pullback g).obj N)
            (g ⁻¹ᵁ V) hwV (pullbackApp g N V x) := by
        rw [AddEquiv.symm_apply_eq]
        exact (chartΘ_pullbackAppTop V N g α w q hw hα hwV x).symm
      rw [hL, h0, pullbackCompIso'_inv_app_pullbackApp (Spec.map β) w w' hw' _ _ hwV hw'V,
        chartΘ_pullbackAppTop, extendScalarsMap_oneTmul]
  have := congr($key (chartΘ V N g α w q hw hα z))
  rw [hL, AddEquiv.symm_apply_apply] at this
  exact this

end Chart

section Fullness

variable {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g] [Surjective g] [QuasiCompact g]

omit [Flat g] [Surjective g] [QuasiCompact g] in
/-- The descent condition on a homomorphism `ψ₀ : g^* M ⟶ g^* N`, evaluated on inverse images
of sections. -/
lemma pullbackAppTop_of_comm {M N : S.Modules}
    (ψ₀ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N)
    {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ S') (h : f₂ ≫ g = f₁ ≫ g)
    (hc : (Scheme.Modules.pullback f₁).map ψ₀ ≫
      (pullbackCompIso' f₁ g _ rfl N).inv ≫ (pullbackCompIso' f₂ g _ h N).hom =
      ((pullbackCompIso' f₁ g _ rfl M).inv ≫ (pullbackCompIso' f₂ g _ h M).hom) ≫
      (Scheme.Modules.pullback f₂).map ψ₀) (W : S.Opens)
    (hf₁ : ⊤ ≤ f₁ ⁻¹ᵁ (g ⁻¹ᵁ W)) (hf₂ : ⊤ ≤ f₂ ⁻¹ᵁ (g ⁻¹ᵁ W)) (s : Γ(M, W)) :
    (pullbackCompIso' f₂ g _ h N).hom.app ⊤ ((pullbackCompIso' f₁ g _ rfl N).inv.app ⊤
      (pullbackAppTop f₁ ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ W) hf₁
        (ψ₀.app (g ⁻¹ᵁ W) (pullbackApp g M W s)))) =
      pullbackAppTop f₂ ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ W) hf₂
        (ψ₀.app (g ⁻¹ᵁ W) (pullbackApp g M W s)) := by
  have hq : ⊤ ≤ (f₁ ≫ g) ⁻¹ᵁ W := hf₁
  have h5 := congr(Hom.app $hc ⊤ (pullbackAppTop f₁ ((Scheme.Modules.pullback g).obj M)
    (g ⁻¹ᵁ W) hf₁ (pullbackApp g M W s)))
  rw [Hom.comp_app_apply, Hom.comp_app_apply, Hom.comp_app_apply, Hom.comp_app_apply,
    pullbackAppTop_naturality, pullbackCompIso'_inv_app_pullbackAppTop f₁ g _ rfl M W hq hf₁ s,
    pullbackCompIso'_hom_app_pullbackAppTop f₂ g _ h M W hq hf₂ s,
    pullbackAppTop_naturality] at h5
  exact h5

omit [Flat g] [Surjective g] [QuasiCompact g] in
set_option backward.isDefEq.respectTransparency false in
/-- The descent condition of a homomorphism of descent data, for two maps `f₁, f₂ : Y ⟶ S'`
with `f₁ ≫ g = f₂ ≫ g`. -/
lemma comm_of_descentData {M N : S.Modules}
    (ψ : (modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).obj M ⟶
      (modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).obj N)
    {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ S') (h : f₂ ≫ g = f₁ ≫ g) :
    (Scheme.Modules.pullback f₁).map (ψ.hom ()) ≫
      (pullbackCompIso' f₁ g _ rfl N).inv ≫ (pullbackCompIso' f₂ g _ h N).hom =
      ((pullbackCompIso' f₁ g _ rfl M).inv ≫ (pullbackCompIso' f₂ g _ h M).hom) ≫
      (Scheme.Modules.pullback f₂).map (ψ.hom ()) := by
  have hc : (Scheme.Modules.pullback f₁).map (ψ.hom ()) ≫
      (modulesPseudofunctor.mapComp' g.op.toLoc f₁.op.toLoc (f₁ ≫ g).op.toLoc
        rfl).inv.toNatTrans.app N ≫
      (modulesPseudofunctor.mapComp' g.op.toLoc f₂.op.toLoc (f₁ ≫ g).op.toLoc
        (by rw [← h]; rfl)).hom.toNatTrans.app N =
      ((modulesPseudofunctor.mapComp' g.op.toLoc f₁.op.toLoc (f₁ ≫ g).op.toLoc
        rfl).inv.toNatTrans.app M ≫
      (modulesPseudofunctor.mapComp' g.op.toLoc f₂.op.toLoc (f₁ ≫ g).op.toLoc
        (by rw [← h]; rfl)).hom.toNatTrans.app M) ≫
      (Scheme.Modules.pullback f₂).map (ψ.hom ()) :=
    ψ.comm (f₁ ≫ g) (i₁ := ()) (i₂ := ()) f₁ f₂ rfl h
  rwa [mapComp'_inv_toNatTrans_app f₁ g _ rfl N, mapComp'_hom_toNatTrans_app f₂ g _ h N,
    mapComp'_inv_toNatTrans_app f₁ g _ rfl M, mapComp'_hom_toNatTrans_app f₂ g _ h M] at hc

omit [Flat g] [Surjective g] [QuasiCompact g] in
/-- The descent condition of a homomorphism of descent data, evaluated on the image of the
inverse image of a section. -/
lemma pullbackAppTop_descentData {M N : S.Modules}
    (ψ : (modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).obj M ⟶
      (modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).obj N)
    {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ S') (h : f₂ ≫ g = f₁ ≫ g) (W : S.Opens)
    (hf₁ : ⊤ ≤ f₁ ⁻¹ᵁ (g ⁻¹ᵁ W)) (hf₂ : ⊤ ≤ f₂ ⁻¹ᵁ (g ⁻¹ᵁ W)) (s : Γ(M, W))
    (t : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ W))
    (ht : t = (ψ.hom ()).app (g ⁻¹ᵁ W) (pullbackApp g M W s)) :
    (pullbackCompIso' f₂ g _ h N).hom.app ⊤ ((pullbackCompIso' f₁ g _ rfl N).inv.app ⊤
      (pullbackAppTop f₁ ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ W) hf₁ t)) =
      pullbackAppTop f₂ ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ W) hf₂ t := by
  subst ht
  exact pullbackAppTop_of_comm g (ψ.hom ()) f₁ f₂ h (comm_of_descentData g ψ f₁ f₂ h) W hf₁ hf₂ s

set_option backward.isDefEq.respectTransparency.types false in
/-- The key step of VIII.1.2: for a homomorphism `ψ` of descent data between `g^* M` and
`g^* N` with `N` quasi-coherent, and an affine open `V` of `S`, the image under `ψ` of the
inverse image of a section of `M` over `V` is the inverse image of a section of `N`. -/
theorem exists_pullbackApp_eq_of_descentData {M N : S.Modules} [N.IsQuasicoherent]
    (ψ : (modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).obj M ⟶
      (modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).obj N)
    (V : S.affineOpens) (s : Γ(M, V)) :
    ∃ x : Γ(N, V), pullbackApp g N V x = (ψ.hom ()).app (g ⁻¹ᵁ V) (pullbackApp g M V s) := by
  set j := V.2.fromSpec
  have : IsOpenImmersion j := IsAffineOpen.isOpenImmersion_fromSpec V.2
  let gA := pullback.snd g j
  have : CompactSpace ↥(Limits.pullback g j) := QuasiCompact.compactSpace_of_compactSpace gA
  obtain ⟨S₁, π, hπs, hπ, hS₁⟩ :=
    (Limits.pullback g j).exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  have : Flat π := IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ π hπ
  have : Surjective π := hπs
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (S₁.isoSpec.inv ≫ π ≫ gA)
  have hff : φ.hom.FaithfullyFlat := by
    rw [← flat_and_surjective_SpecMap_iff, hφ]
    exact ⟨inferInstance, inferInstance⟩
  set k := S₁.isoSpec.inv ≫ π ≫ pullback.fst g j
  have hk : k ≫ g = Spec.map φ ≫ j := by
    simp only [k, Category.assoc, pullback.condition, hφ, gA]
  have hkV : ⊤ ≤ k ⁻¹ᵁ (g ⁻¹ᵁ (V : S.Opens)) := by
    change ⊤ ≤ (k ≫ g) ⁻¹ᵁ (V : S.Opens)
    rw [hk, Scheme.Hom.comp_preimage, V.2.fromSpec_preimage_self]
    exact le_rfl
  -- the two maps `Spec (B ⊗_A B) ⇉ S'`
  set ι₁ := tensorSelfInl φ
  set ι₂ := tensorSelfInr φ
  set f₁ := Spec.map ι₁ ≫ k
  set f₂ := Spec.map ι₂ ≫ k
  set α := φ ≫ ι₁
  have hι : Spec.map ι₁ ≫ Spec.map φ = Spec.map ι₂ ≫ Spec.map φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, tensorSelf_comm]
  have hα : Spec.map α ≫ j = f₁ ≫ g := by
    simp only [α, f₁, Spec.map_comp, Category.assoc, hk]
  have hq₂ : f₂ ≫ g = f₁ ≫ g := by
    simp only [f₁, f₂, Category.assoc, hk]
    rw [← Category.assoc, ← hι, Category.assoc]
  have hf₁V : ⊤ ≤ f₁ ⁻¹ᵁ (g ⁻¹ᵁ (V : S.Opens)) := by
    change ⊤ ≤ (f₁ ≫ g) ⁻¹ᵁ (V : S.Opens)
    rw [← hα, Scheme.Hom.comp_preimage, V.2.fromSpec_preimage_self]
    exact le_rfl
  have hf₂V : ⊤ ≤ f₂ ⁻¹ᵁ (g ⁻¹ᵁ (V : S.Opens)) := by
    change ⊤ ≤ (f₂ ≫ g) ⁻¹ᵁ (V : S.Opens)
    rw [hq₂]; exact hf₁V
  -- the descent condition at `Spec (B ⊗_A B)`
  obtain ⟨t, ht⟩ : ∃ t : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ V),
      t = (ψ.hom ()).app (g ⁻¹ᵁ V) (pullbackApp g M V s) := ⟨_, rfl⟩
  rw [← ht]
  have key : (pullbackCompIso' f₂ g _ hq₂ N).hom.app ⊤ ((pullbackCompIso' f₁ g _ rfl N).inv.app ⊤
      (pullbackAppTop f₁ ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ V) hf₁V t)) =
      pullbackAppTop f₂ ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ V) hf₂V t := by
    exact pullbackAppTop_descentData g ψ f₁ f₂ hq₂ V hf₁V hf₂V s t ht
  -- translate to `B ⊗_A N₀`
  set y := chartΘ V N g φ k (Spec.map φ ≫ j) hk rfl
    (pullbackAppTop k ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ V) hkV t)
  have h₁ : chartΘ V N g α f₁ (f₁ ≫ g) rfl hα
      (pullbackAppTop f₁ ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ V) hf₁V t) =
      extendScalarsMap (chartModule V N) φ α ι₁ rfl y := by
    rw [← pullbackCompIso'_inv_app_pullbackApp (Spec.map ι₁) k f₁ rfl _ _ hkV hf₁V t]
    exact chartΘ_pullbackApp V N g φ α ι₁ rfl k _ hk rfl f₁ rfl (f₁ ≫ g) rfl hα hkV _
  have h₂ : chartΘ V N g α f₂ (f₁ ≫ g) hq₂ hα
      (pullbackAppTop f₂ ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ V) hf₂V t) =
      extendScalarsMap (chartModule V N) φ α ι₂ (tensorSelf_comm φ).symm y := by
    rw [← pullbackCompIso'_inv_app_pullbackApp (Spec.map ι₂) k f₂ rfl _ _ hkV hf₂V t]
    exact chartΘ_pullbackApp V N g φ α ι₂ (tensorSelf_comm φ).symm k _ hk rfl f₂ rfl (f₁ ≫ g)
      hq₂ hα hkV _
  have h₃ : chartΘ V N g α f₂ (f₁ ≫ g) hq₂ hα
      (pullbackAppTop f₂ ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ V) hf₂V t) =
      chartΘ V N g α f₁ (f₁ ≫ g) rfl hα
        (pullbackAppTop f₁ ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ V) hf₁V t) := by
    rw [← key, chartΘ_apply, chartΘ_apply, iso_inv_app_hom_app]
  obtain ⟨n, hn⟩ := exists_eq_toExtendScalars_of_extendScalarsMap_eq (chartModule V N) φ hff y
    (h₁.symm.trans (h₃.symm.trans h₂))
  obtain ⟨x, rfl⟩ := (chartSection_bijective V N).2 n
  refine ⟨x, pullbackAppTop_injective S₁.isoSpec.inv π (pullback.fst g j)
    ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ V) ?_ hkV ?_⟩
  · rw [Scheme.Hom.opensRange_pullbackFst, V.2.opensRange_fromSpec]
  · apply (chartΘ V N g φ k (Spec.map φ ≫ j) hk rfl).injective
    rw [chartΘ_pullbackAppTop, hn]

/-- The key step of VIII.1.2, over an arbitrary open `U` of `S`: the affine case and gluing. -/
theorem exists_pullbackApp_eq_of_descentData' {M N : S.Modules} [N.IsQuasicoherent]
    (ψ : (modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).obj M ⟶
      (modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).obj N)
    (U : S.Opens) (s : Γ(M, U)) :
    ∃ x : Γ(N, U), pullbackApp g N U x = (ψ.hom ()).app (g ⁻¹ᵁ U) (pullbackApp g M U s) := by
  obtain ⟨t, ht⟩ : ∃ t : Γ((Scheme.Modules.pullback g).obj N, g ⁻¹ᵁ U),
      t = (ψ.hom ()).app (g ⁻¹ᵁ U) (pullbackApp g M U s) := ⟨_, rfl⟩
  rw [← ht]
  -- restrictions of `t` along `g⁻¹ V ⊆ g⁻¹ U`
  have hres (V : S.Opens) (hV : V ≤ U) : ((Scheme.Modules.pullback g).obj N).presheaf.map
      (homOfLE (g.preimage_mono hV)).op t =
      (ψ.hom ()).app (g ⁻¹ᵁ V) (pullbackApp g M V (M.presheaf.map (homOfLE hV).op s)) := by
    rw [ht, pullbackApp_map]
    exact (Hom.app_map (ψ.hom ()) (homOfLE (g.preimage_mono hV)) _).symm
  let ι := {V : S.affineOpens // V.1 ≤ U}
  choose x hx using fun V : ι ↦
    exists_pullbackApp_eq_of_descentData g ψ V.1 (M.presheaf.map (homOfLE V.2).op s)
  have hx' (V : ι) : pullbackApp g N V.1 (x V) = ((Scheme.Modules.pullback g).obj N).presheaf.map
      (homOfLE (g.preimage_mono V.2)).op t := (hx V).trans (hres V.1 V.2).symm
  have hcov : U ≤ ⨆ V : ι, (V.1 : S.Opens) := fun p hp ↦ by
    obtain ⟨V, hV, hpV, hVU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hpV⟩
  have hcompat : TopCat.Presheaf.IsCompatible N.presheaf (fun V : ι ↦ (V.1 : S.Opens)) x := by
    intro V W
    apply pullbackApp_injective_of_flat g N
    rw [pullbackApp_map, pullbackApp_map, hx', hx']
    change ((Scheme.Modules.pullback g).obj N).presheaf.map _ _ =
      ((Scheme.Modules.pullback g).obj N).presheaf.map _ _
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  obtain ⟨y, hy, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨N.presheaf, N.isSheaf⟩
    (fun V : ι ↦ (V.1 : S.Opens)) U (fun V ↦ homOfLE V.2) hcov x hcompat
  · refine ⟨y, TopCat.Sheaf.eq_of_locally_eq' ⟨((Scheme.Modules.pullback g).obj N).presheaf,
      ((Scheme.Modules.pullback g).obj N).isSheaf⟩ (fun V : ι ↦ g ⁻¹ᵁ (V.1 : S.Opens)) (g ⁻¹ᵁ U)
      (fun V ↦ homOfLE (g.preimage_mono V.2)) (fun p hp ↦ ?_) _ _ fun V ↦ ?_⟩
    · obtain ⟨V, hpV⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hp)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨V, hpV⟩
    · rw [← hx', ← hy V]
      exact (pullbackApp_map g N (homOfLE V.2) y).symm

/-- VIII.1.2, surjectivity: for `g` faithfully flat and quasi-compact and `N` quasi-coherent,
every homomorphism of descent data `g^* M ⟶ g^* N` comes from a homomorphism `M ⟶ N`. -/
theorem toDescentData_map_surjective_of_flat (M N : S.Modules) [N.IsQuasicoherent] :
    Function.Surjective ((modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).map :
      (M ⟶ N) → _) := by
  intro ψ
  choose x hx using fun (U : S.Opens) (s : Γ(M, U)) ↦
    exists_pullbackApp_eq_of_descentData' g ψ U s
  have hinj := pullbackApp_injective_of_flat g N
  -- the sections of the descended homomorphism
  let φapp (U : S.Opens) : Γ(M, U) →+ Γ(N, U) :=
    { toFun := x U
      map_zero' := hinj U (by rw [hx, map_zero, map_zero]; erw [map_zero]; rfl)
      map_add' s₁ s₂ := hinj U (by rw [hx, map_add, map_add, hx, hx]; erw [map_add]; rfl) }
  have hφapp (U : S.Opens) (s : Γ(M, U)) :
      pullbackApp g N U (φapp U s) = (ψ.hom ()).app (g ⁻¹ᵁ U) (pullbackApp g M U s) := hx U s
  let φ₀ : M.presheaf ⟶ N.presheaf :=
    { app U := AddCommGrpCat.ofHom (φapp U.unop)
      naturality {U V} i := by
        ext s
        apply hinj V.unop
        change pullbackApp g N V.unop (φapp V.unop (M.presheaf.map i.unop.op s)) =
          pullbackApp g N V.unop (N.presheaf.map i.unop.op (φapp U.unop s))
        rw [hφapp, pullbackApp_map, pullbackApp_map, hφapp]
        exact Hom.app_map (ψ.hom ()) _ _ }
  have hsmul (U : S.Opens) (r : Γ(S, U)) (s : Γ(M, U)) : φapp U (r • s) = r • φapp U s :=
    hinj U (by
      rw [hφapp, pullbackApp_smul, pullbackApp_smul, hφapp]
      exact Hom.app_smul (ψ.hom ()) _ _)
  let φ : M ⟶ N := ⟨PresheafOfModules.homMk φ₀ fun U r s ↦ hsmul U.unop r s⟩
  have hφ (U : S.Opens) (s : Γ(M, U)) : φ.app U s = φapp U s := rfl
  refine ⟨φ, ?_⟩
  ext1 ⟨⟩
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N,
      ψ₀ = ψ.hom () := ⟨_, rfl⟩
  change (Scheme.Modules.pullback g).map φ = _
  rw [← hψ₀]
  apply ((pullbackPushforwardAdjunction g).homEquiv M ((Scheme.Modules.pullback g).obj N)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.unit_naturality]
  ext U s
  rw [Hom.comp_app_apply, Hom.comp_app_apply, pushforward_map_app, hφ, hψ₀]
  exact hφapp U s

/-- VIII.1.2: for `g : S' → S` faithfully flat and quasi-compact, the functor from Modules on
`S` to Modules on `S'` with a descent datum relative to `g` is fully faithful on quasi-coherent
Modules. This is the first half of `QuasiCoherentDescentStatement`. -/
theorem toDescentData_map_bijective_of_flat (M N : S.Modules) [M.IsQuasicoherent]
    [N.IsQuasicoherent] :
    Function.Bijective ((modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).map :
      (M ⟶ N) → _) :=
  ⟨toDescentData_map_injective_of_flat g M N, toDescentData_map_surjective_of_flat g M N⟩

end Fullness

end FullFaithfulness

section Effectiveness

open Scheme.Modules

variable {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g] [Surjective g] [QuasiCompact g]

/-- VIII.1.3: for `g : S' → S` faithfully flat and quasi-compact, every descent datum `D` on a
quasi-coherent Module on `S'` relative to `g` is isomorphic to the descent datum of `g^* M` for
the quasi-coherent Module `M = Scheme.Modules.descentModule D` on `S`. -/
theorem descentModule_isQuasicoherent_and_iso
    (D : modulesPseudofunctor.DescentData (fun _ : Unit ↦ g)) (hD : (D.obj ()).IsQuasicoherent) :
    (Scheme.Modules.descentModule D).IsQuasicoherent ∧
      Nonempty ((modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).obj
        (Scheme.Modules.descentModule D) ≅ D) := by
  have : (Scheme.Modules.descentObj D).IsQuasicoherent := hD
  exact ⟨Scheme.Modules.isQuasicoherent_descentModule D, ⟨Scheme.Modules.descentIso D⟩⟩

/-- VIII.1.7, descent-datum form: for `G` quasi-coherent on `S`, a section of `g^* G` over
`g⁻¹ U` compatible with the canonical descent datum of `g^* G` is the inverse image of a unique
section of `G` over `U`. -/
theorem exists_unique_pullbackApp_eq_of_isDescentSection (G : S.Modules) [G.IsQuasicoherent]
    (U : S.Opens) (s' : Γ((Scheme.Modules.pullback g).obj G, g ⁻¹ᵁ U))
    (hs' : Scheme.Modules.IsDescentSection
      ((modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).obj G) U s') :
    ∃! s : Γ(G, U), pullbackApp g G U s = s' := by
  let D := (modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).obj G
  have : (Scheme.Modules.descentObj D).IsQuasicoherent :=
    inferInstanceAs ((Scheme.Modules.pullback g).obj G).IsQuasicoherent
  have := Scheme.Modules.isQuasicoherent_descentModule D
  obtain ⟨φ, hφ'⟩ : ∃ φ : Scheme.Modules.descentModule D ⟶ G,
      (Scheme.Modules.pullback g).map φ = Scheme.Modules.descentCounit D := by
    obtain ⟨φ, hφ⟩ := toDescentData_map_surjective_of_flat g (Scheme.Modules.descentModule D) G
      (Scheme.Modules.descentIso D).hom
    exact ⟨φ, congrArg (fun ψ ↦ ψ.hom ()) hφ⟩
  let m : Γ(Scheme.Modules.descentModule D, U) := ⟨s', hs'⟩
  have key : pullbackApp g G U (φ.app U m) = s' := by
    rw [pullbackApp_naturality, hφ']
    exact descentCounit_app_pullbackApp D U m
  exact ⟨_, key, fun t ht ↦ pullbackApp_injective_of_flat g G U (ht.trans key.symm)⟩

/-- VIII.1.7: for `G` quasi-coherent on `S`, with inverse images `G'` on `S'` and `G''` on
`S'' = S' ×_S S'`, the diagram `G → g_* G' ⇉ h_* G''` is exact on sections over every open
`U`: `G(U) → G'(g⁻¹ U)` is injective (`pullbackApp_injective_of_flat`), and a section `s'` of
`G'` whose two inverse images to `S''` agree in `G''` comes from a unique section of `G`. -/
theorem exists_unique_pullbackApp_eq (G : S.Modules) [G.IsQuasicoherent]
    (U : S.Opens) (s' : Γ((Scheme.Modules.pullback g).obj G, g ⁻¹ᵁ U))
    (hs' : (pullbackCompIso' (Limits.pullback.fst g g) g (Limits.pullback.fst g g ≫ g) rfl
        G).inv.app _ (pullbackApp (Limits.pullback.fst g g) _ (g ⁻¹ᵁ U) s') =
      ((Scheme.Modules.pullback (Limits.pullback.fst g g ≫ g)).obj G).presheaf.map
        (homOfLE (Scheme.Modules.preimage_le_of_comp_eq Limits.pullback.condition U)).op
        ((pullbackCompIso' (Limits.pullback.snd g g) g (Limits.pullback.fst g g ≫ g)
          Limits.pullback.condition.symm G).inv.app _
          (pullbackApp (Limits.pullback.snd g g) _ (g ⁻¹ᵁ U) s'))) :
    ∃! s : Γ(G, U), pullbackApp g G U s = s' :=
  exists_unique_pullbackApp_eq_of_isDescentSection g G U s'
    (Scheme.Modules.isDescentSection_toDescentData G U s' hs')

end Effectiveness

/-- VIII.1.1: a faithfully flat quasi-compact morphism is an effective descent morphism for the
fibered category of quasi-coherent Modules: VIII.1.2 (`toDescentData_map_bijective_of_flat`)
and VIII.1.3 (`descentModule_isQuasicoherent_and_iso`). -/
theorem quasiCoherentDescentStatement : QuasiCoherentDescentStatement.{u} := by
  intro S S' g _ _ _
  refine ⟨fun M N hM hN ↦ toDescentData_map_bijective_of_flat g M N, fun D hD ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := descentModule_isQuasicoherent_and_iso g D hD
  exact ⟨_, h₁, h₂⟩

section QuotientDescent

open Scheme.Modules

variable {S S' : Scheme.{u}} (g : S' ⟶ S) [Flat g] [Surjective g] [QuasiCompact g]

/-- For `g` faithfully flat and quasi-compact, a morphism of quasi-coherent Modules whose inverse
image is an epimorphism is an epimorphism. -/
theorem epi_of_epi_pullback_map {G M : S.Modules} [G.IsQuasicoherent] [M.IsQuasicoherent]
    (q : G ⟶ M) [Epi ((Scheme.Modules.pullback g).map q)] : Epi q := by
  have : (cokernel q).IsQuasicoherent := isQuasicoherent_cokernel q
  apply Abelian.epi_of_cokernel_π_eq_zero
  have h0 : (Scheme.Modules.pullback g).map (cokernel.π q) = 0 := by
    apply (cancel_epi ((Scheme.Modules.pullback g).map q)).1
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero]
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  apply pullbackApp_injective_of_flat g (cokernel q) U
  rw [pullbackApp_naturality, h0, Scheme.Modules.Hom.zero_app, Scheme.Modules.Hom.zero_app]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- A morphism `g^* Q₁ ⟶ g^* Q₂` compatible with epimorphisms `g^* q₁`, `g^* q₂` from `g^* G`
comes from a morphism `Q₁ ⟶ Q₂`. -/
lemma exists_pullback_map_eq_of_comp_eq {G Q₁ Q₂ : S.Modules} [Q₂.IsQuasicoherent]
    (q₁ : G ⟶ Q₁) (q₂ : G ⟶ Q₂) [Epi q₁]
    (a : (Scheme.Modules.pullback g).obj Q₁ ⟶ (Scheme.Modules.pullback g).obj Q₂)
    (ha : (Scheme.Modules.pullback g).map q₁ ≫ a = (Scheme.Modules.pullback g).map q₂) :
    ∃ b : Q₁ ⟶ Q₂, (Scheme.Modules.pullback g).map b = a := by
  let F := modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)
  let φ : F.obj Q₁ ⟶ F.obj Q₂ :=
    { hom := fun _ ↦ a
      comm := fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
        cases i₁; cases i₂
        have e₁ := (F.map q₁).comm q (i₁ := ()) (i₂ := ()) f₁ f₂ hf₁ hf₂
        have e₂ := (F.map q₂).comm q (i₁ := ()) (i₂ := ()) f₁ f₂ hf₁ hf₂
        have ha' : (F.map q₁).hom () ≫ a = (F.map q₂).hom () := ha
        have : Epi ((modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map ((F.map q₁).hom ())) :=
          (inferInstance : Epi ((Scheme.Modules.pullback f₁).map
            ((Scheme.Modules.pullback g).map q₁)))
        apply (cancel_epi ((modulesPseudofunctor.map f₁.op.toLoc).toFunctor.map
          ((F.map q₁).hom ()))).1
        rw [← Category.assoc, ← Functor.map_comp, ha', e₂, reassoc_of% e₁, ← Functor.map_comp,
          ha'] }
  obtain ⟨b, hb⟩ := toDescentData_map_surjective_of_flat g Q₁ Q₂ φ
  exact ⟨b, congrArg (fun ψ ↦ ψ.hom ()) hb⟩

/-- VIII.1.8, injectivity: two quasi-coherent quotients of a quasi-coherent `G` whose inverse
images are the same quotient of `g^* G` are the same quotient of `G`. -/
theorem exists_iso_of_pullback_quotient (G : S.Modules) [G.IsQuasicoherent]
    {Q₁ Q₂ : S.Modules} [Q₁.IsQuasicoherent] [Q₂.IsQuasicoherent] (q₁ : G ⟶ Q₁) (q₂ : G ⟶ Q₂)
    [Epi q₁] [Epi q₂]
    (e' : (Scheme.Modules.pullback g).obj Q₁ ≅ (Scheme.Modules.pullback g).obj Q₂)
    (he' : (Scheme.Modules.pullback g).map q₁ ≫ e'.hom = (Scheme.Modules.pullback g).map q₂) :
    ∃ e : Q₁ ≅ Q₂, q₁ ≫ e.hom = q₂ := by
  obtain ⟨b₁, hb₁⟩ := exists_pullback_map_eq_of_comp_eq g q₁ q₂ e'.hom he'
  obtain ⟨b₂, hb₂⟩ := exists_pullback_map_eq_of_comp_eq g q₂ q₁ e'.inv
    (by rw [← he', Category.assoc, Iso.hom_inv_id, Category.comp_id])
  refine ⟨⟨b₁, b₂, ?_, ?_⟩, ?_⟩
  · apply pullback_map_injective_of_flat g
    rw [Functor.map_comp, hb₁, hb₂, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  · apply pullback_map_injective_of_flat g
    rw [Functor.map_comp, hb₁, hb₂, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  · apply pullback_map_injective_of_flat g
    rw [Functor.map_comp]
    exact (congrArg _ hb₁).trans he'

/-- VIII.1.8, exactness in the middle: let `G` be quasi-coherent on `S` and `q' : g^* G ⟶ Q'` a
quasi-coherent quotient of `G' = g^* G` whose two inverse images to `S'' = S' ×_S S'` are the same
quotient of `G''` (there is `ψ : pr₁^* Q' ⟶ pr₂^* Q'` compatible with the maps from `G''`). Then
`Q'` is the inverse image of a quasi-coherent quotient of `G`. -/
theorem exists_quotient_of_pullback (G : S.Modules) [G.IsQuasicoherent] {Q' : S'.Modules}
    [Q'.IsQuasicoherent] (q' : (Scheme.Modules.pullback g).obj G ⟶ Q') [Epi q']
    (ψ : (Scheme.Modules.pullback (Limits.pullback.fst g g)).obj Q' ⟶
      (Scheme.Modules.pullback (Limits.pullback.snd g g)).obj Q')
    (hψ : (pullbackCompIso' (Limits.pullback.fst g g) g (Limits.pullback.fst g g ≫ g) rfl
        G).hom ≫ (Scheme.Modules.pullback (Limits.pullback.fst g g)).map q' ≫ ψ =
      (pullbackCompIso' (Limits.pullback.snd g g) g (Limits.pullback.fst g g ≫ g)
        Limits.pullback.condition.symm G).hom ≫
        (Scheme.Modules.pullback (Limits.pullback.snd g g)).map q') :
    ∃ (Q : S.Modules) (q : G ⟶ Q) (e : (Scheme.Modules.pullback g).obj Q ≅ Q'),
      Q.IsQuasicoherent ∧ Epi q ∧ (Scheme.Modules.pullback g).map q ≫ e.hom = q' := by
  let DG := (modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).obj G
  have e := descentHom_toDescentData G (Limits.pullback.fst g g) (Limits.pullback.snd g g)
    Limits.pullback.condition
  have h3 : (Scheme.Modules.pullback (Limits.pullback.fst g g)).map q' ≫ ψ =
      (pullbackCompIso' (Limits.pullback.fst g g) g (Limits.pullback.fst g g ≫ g) rfl G).inv ≫
      (pullbackCompIso' (Limits.pullback.snd g g) g (Limits.pullback.fst g g ≫ g)
        Limits.pullback.condition.symm G).hom ≫
        (Scheme.Modules.pullback (Limits.pullback.snd g g)).map q' := by
    rw [← hψ, Iso.inv_hom_id_assoc]
  have hψ' : (Scheme.Modules.pullback (Limits.pullback.fst g g)).map q' ≫ ψ =
      descentHom DG (Limits.pullback.fst g g) (Limits.pullback.snd g g)
        Limits.pullback.condition ≫ (Scheme.Modules.pullback (Limits.pullback.snd g g)).map q' :=
    h3.trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (Scheme.Modules.pullback (Limits.pullback.snd g g)).map q') e.symm))
  have : Epi (X := descentObj DG) (Y := Q') q' := ‹Epi q'›
  let DQ := quotientDescentData DG q' ψ hψ'
  have : (descentObj DQ).IsQuasicoherent := inferInstanceAs Q'.IsQuasicoherent
  have hM := isQuasicoherent_descentModule DQ
  have hε := isIso_descentCounit DQ
  let ε : (Scheme.Modules.pullback g).obj (descentModule DQ) ⟶ Q' := descentCounit DQ
  have : IsIso ε := hε
  obtain ⟨q, hq⟩ := toDescentData_map_surjective_of_flat g G (descentModule DQ)
    (toQuotientDescentData DG q' ψ hψ' ≫ (descentIso DQ).inv)
  have hq' : (Scheme.Modules.pullback g).map q ≫ ε = q' := by
    have h2 : (modulesPseudofunctor.toDescentData (fun _ : Unit ↦ g)).map q ≫
        (descentIso DQ).hom = toQuotientDescentData DG q' ψ hψ' := by
      rw [hq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact congrArg (fun φ ↦ φ.hom ()) h2
  refine ⟨descentModule DQ, q, asIso ε, hM, ?_, hq'⟩
  have : Epi ((Scheme.Modules.pullback g).map q) := by
    have e : (Scheme.Modules.pullback g).map q = q' ≫ inv ε := by
      rw [← hq', Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  exact epi_of_epi_pullback_map g q

end QuotientDescent

end SGA.SGA1.ExposeVIII
