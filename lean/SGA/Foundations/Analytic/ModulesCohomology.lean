/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ModulesExactness
import SGA.Foundations.Cohomology.CechPullback

/-!
# Pulling back cohomology classes of `𝒪`-modules: naturality and Čech computation

For a morphism of locally ringed spaces `f : X ⟶ Y` and an `𝒪_Y`-module `M`, the canonical map
`Hⁿ(Y, M) → Hⁿ(X, f^* M)` (`LocallyRingedSpace.Modules.pullbackCohomologyMap`, EGA 0_III 12.1.3.1)
is the map `TopCat.Sheaf.globalCohomologyPullbackMap` of the underlying abelian sheaves attached to
`f⁻¹ M → f^* M` (`pullbackCohomologyMap_eq`). Hence:

* it is natural in `M` (`pullbackCohomologyMap_naturality`);
* it commutes with the connecting maps of a short exact sequence of `𝒪_Y`-modules whose pullback
  is short exact, e.g. when `f` is flat (`pullbackCohomologyMap_comp_extClass`; the underlying
  abelian sheaves of a short exact sequence of modules are short exact,
  `shortExact_map_toAbFunctor`);
* it is computed by Čech cochains (`bijective_pullbackCohomologyMap_iff_cech`): for a finite open
  cover `U` of `Y` such that `M` is acyclic on the finite intersections of `U` and `f^* M` on those
  of `f⁻¹ U`, `Hⁿ(Y, M) → Hⁿ(X, f^* M)` is bijective iff the map of Čech cohomology
  `Ȟⁿ(U, M) → Ȟⁿ(f⁻¹ U, f^* M)`, induced on sections by the unit `M → f_* f^* M`
  (`pullbackAdjoint_abPullbackToPullback`), is.

This is how SGA 1 XII.4.3 (GAGA) is reduced to Čech cohomology (Serre, GAGA, no. 12).
References: EGA 0_III 12.1; Stacks Project, Tag 01ET (Leray), Tag 01BQ.
-/

universe u

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- The underlying abelian sheaf functor `X.Modules ⥤ Ab(X)` preserves epimorphisms (cokernels of
sheaves of modules are sheafifications of presheaf cokernels, computed on the underlying abelian
presheaves). The same proof as `Scheme.Modules.epi_toAbSheaf`. -/
lemma epi_toSheaf {Z : LocallyRingedSpace.{u}} {M N : Z.Modules} (g : M ⟶ N) [Epi g] :
    Epi ((SheafOfModules.toSheaf Z.ringCatSheaf).map g) := by
  let P := PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)
  let Φ := SheafOfModules.forget Z.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)
  let ε := asIso (PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).counit
  have h1 : IsZero (cokernel g) := isZero_cokernel_of_epi g
  have e1 : cokernel (P.map (Φ.map g)) ≅ cokernel g :=
    cokernel.mapIso _ _ (ε.app M) (ε.app N) (ε.hom.naturality g)
  have e2 : P.obj (cokernel (Φ.map g)) ≅ cokernel (P.map (Φ.map g)) := PreservesCokernel.iso P _
  have h2 : IsZero ((SheafOfModules.toSheaf _).obj (P.obj (cokernel (Φ.map g)))) :=
    Functor.map_isZero _ (h1.of_iso (e2 ≪≫ e1))
  let K := cokernel (Φ.map g)
  let η := asIso (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology Z.carrier)
    AddCommGrpCat.{u}).counit
  have e3 : (SheafOfModules.toSheaf _).obj (P.obj K) ≅
      (presheafToSheaf (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}).obj
        ((PresheafOfModules.toPresheaf _).obj K) :=
    (PresheafOfModules.sheafificationCompToSheaf (𝟙 Z.ringCatSheaf.obj)).app K
  have e4 : (presheafToSheaf (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}).obj
      ((PresheafOfModules.toPresheaf _).obj K) ≅
      (presheafToSheaf (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}).obj
        (cokernel ((PresheafOfModules.toPresheaf _).map (Φ.map g))) :=
    (presheafToSheaf (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}).mapIso
      (PreservesCokernel.iso _ _)
  have e5 : (presheafToSheaf (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}).obj
      (cokernel ((PresheafOfModules.toPresheaf _).map (Φ.map g))) ≅
      cokernel ((presheafToSheaf (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}).map
        ((PresheafOfModules.toPresheaf _).map (Φ.map g))) :=
    PreservesCokernel.iso _ _
  have e6 : cokernel ((presheafToSheaf (Opens.grothendieckTopology Z.carrier)
      AddCommGrpCat.{u}).map ((PresheafOfModules.toPresheaf _).map (Φ.map g))) ≅
        cokernel ((SheafOfModules.toSheaf Z.ringCatSheaf).map g) :=
    cokernel.mapIso _ _ (η.app M.toAbSheaf) (η.app N.toAbSheaf)
      (η.hom.naturality ((SheafOfModules.toSheaf Z.ringCatSheaf).map g))
  exact Preadditive.epi_of_isZero_cokernel _ (h2.of_iso (e3 ≪≫ e4 ≪≫ e5 ≪≫ e6).symm)

variable (Z : LocallyRingedSpace.{u}) in
/-- The underlying abelian sheaf functor `Z.Modules ⥤ Ab(Z)`. -/
abbrev toAbFunctor : Z.Modules ⥤ Sheaf (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf Z.ringCatSheaf

instance (Z : LocallyRingedSpace.{u}) : (toAbFunctor Z).PreservesZeroMorphisms :=
  ⟨fun _ _ ↦ CategoryTheory.Sheaf.hom_ext rfl⟩

instance (Z : LocallyRingedSpace.{u}) : (toAbFunctor Z).Additive :=
  ⟨fun {_ _ _ _} ↦ CategoryTheory.Sheaf.hom_ext rfl⟩

instance (Z : LocallyRingedSpace.{u}) : PreservesFiniteLimits (toAbFunctor Z) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf Z.ringCatSheaf))

/-- The underlying abelian sheaves of a short exact sequence of `𝒪_Z`-modules form a short exact
sequence. -/
lemma shortExact_map_toAbFunctor {Z : LocallyRingedSpace.{u}} {S : ShortComplex Z.Modules}
    (hS : S.ShortExact) : (S.map (toAbFunctor Z)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hmono : Mono ((toAbFunctor Z).map S.f) := inferInstance
  exact
    { exact := hS.exact.map_of_mono_of_preservesKernel _ hS.mono_f inferInstance
      mono_f := hmono
      epi_g := epi_toSheaf S.g }

/-- `pullbackCohomologyMap` is `TopCat.Sheaf.globalCohomologyPullbackMap` for the canonical
morphism `f⁻¹ M → f^* M`. -/
lemma pullbackCohomologyMap_eq (M : Y.Modules) (n : ℕ) :
    pullbackCohomologyMap f M n =
      TopCat.Sheaf.globalCohomologyPullbackMap (f := f.base) (abPullbackToPullback f M) n :=
  rfl

/-- The adjoint `M → f_* f^* M` of `f⁻¹ M → f^* M` is the underlying morphism of abelian sheaves
of the unit of `f^* ⊣ f_*`. -/
lemma pullbackAdjoint_abPullbackToPullback (M : Y.Modules) :
    TopCat.Sheaf.pullbackAdjoint (f := f.base) (abPullbackToPullback f M) =
      (show M.toAbSheaf ⟶ (TopCat.Sheaf.abPushforward f.base).obj ((pullback f).obj M).toAbSheaf
        from (SheafOfModules.toSheaf Y.ringCatSheaf).map
          ((pullbackPushforwardAdjunction f).unit.app M)).hom := by
  rw [TopCat.Sheaf.pullbackAdjoint, abPullbackToPullback]
  exact congrArg (fun φ ↦ φ.hom) (((abAdjunction f).homEquiv _ _).apply_symm_apply _)

/-- The morphism `f⁻¹ M → f^* M` is natural in `M`. -/
lemma abPullbackToPullback_naturality {M M' : Y.Modules} (φ : M ⟶ M') :
    (abPullback f).map ((SheafOfModules.toSheaf Y.ringCatSheaf).map φ) ≫
        abPullbackToPullback f M' =
      abPullbackToPullback f M ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map ((pullback f).map φ) := by
  have key : (SheafOfModules.toSheaf Y.ringCatSheaf).map φ ≫
        (SheafOfModules.toSheaf Y.ringCatSheaf).map
          ((pullbackPushforwardAdjunction f).unit.app M') =
      (SheafOfModules.toSheaf Y.ringCatSheaf).map ((pullbackPushforwardAdjunction f).unit.app M) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map ((pullback f).map φ)) :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg (SheafOfModules.toSheaf Y.ringCatSheaf).map
      ((pullbackPushforwardAdjunction f).unit_naturality φ).symm).trans (Functor.map_comp _ _ _))
  change (abPullback f).map ((SheafOfModules.toSheaf Y.ringCatSheaf).map φ) ≫
      ((abAdjunction f).homEquiv M'.toAbSheaf ((pullback f).obj M').toAbSheaf).symm
        ((SheafOfModules.toSheaf Y.ringCatSheaf).map
          ((pullbackPushforwardAdjunction f).unit.app M')) =
    ((abAdjunction f).homEquiv M.toAbSheaf ((pullback f).obj M).toAbSheaf).symm
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map
        ((pullbackPushforwardAdjunction f).unit.app M)) ≫
      (SheafOfModules.toSheaf X.ringCatSheaf).map ((pullback f).map φ)
  exact ((abAdjunction f).homEquiv_naturality_left_symm _ _).symm.trans
    ((congrArg ((abAdjunction f).homEquiv _ _).symm key).trans
      ((abAdjunction f).homEquiv_naturality_right_symm _ _))

/-- `Hⁿ(Y, M) → Hⁿ(X, f^* M)` is natural in `M`. -/
lemma pullbackCohomologyMap_naturality {M M' : Y.Modules} (φ : M ⟶ M') {n : ℕ} (x : M.H n) :
    pullbackCohomologyMap f M' n
        (CategoryTheory.Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map φ) n x) =
      CategoryTheory.Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map ((pullback f).map φ))
        n (pullbackCohomologyMap f M n x) :=
  TopCat.Sheaf.globalCohomologyPullbackMap_naturality (f := f.base) _ _ _ _
    (abPullbackToPullback_naturality f φ) x

/-- Bijectivity of `Hⁿ(Y, M) → Hⁿ(X, f^* M)` is invariant under isomorphisms of `M`. -/
lemma bijective_pullbackCohomologyMap_iff_of_iso {M N : Y.Modules} (e : M ≅ N) (n : ℕ) :
    Function.Bijective (pullbackCohomologyMap f M n) ↔
      Function.Bijective (pullbackCohomologyMap f N n) := by
  let eY := (toAbFunctor Y).mapIso e
  let eX := (toAbFunctor X).mapIso ((pullback f).mapIso e)
  have hab : Function.Bijective (CategoryTheory.Sheaf.H.map eY.hom n) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨CategoryTheory.Sheaf.H.map eY.inv n,
      fun x ↦ ?_, fun y ↦ ?_⟩
    · rw [← CategoryTheory.Sheaf.H.map_comp_apply, eY.hom_inv_id,
        CategoryTheory.Sheaf.H.map_id_apply]
    · rw [← CategoryTheory.Sheaf.H.map_comp_apply, eY.inv_hom_id,
        CategoryTheory.Sheaf.H.map_id_apply]
  have hab' : Function.Bijective (CategoryTheory.Sheaf.H.map eX.hom n) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨CategoryTheory.Sheaf.H.map eX.inv n,
      fun x ↦ ?_, fun y ↦ ?_⟩
    · rw [← CategoryTheory.Sheaf.H.map_comp_apply, eX.hom_inv_id,
        CategoryTheory.Sheaf.H.map_id_apply]
    · rw [← CategoryTheory.Sheaf.H.map_comp_apply, eX.inv_hom_id,
        CategoryTheory.Sheaf.H.map_id_apply]
  have hcomm : ⇑(pullbackCohomologyMap f N n) ∘ CategoryTheory.Sheaf.H.map eY.hom n =
      CategoryTheory.Sheaf.H.map eX.hom n ∘ pullbackCohomologyMap f M n :=
    funext fun x ↦ pullbackCohomologyMap_naturality f e.hom x
  rw [← Function.Bijective.of_comp_iff _ hab, hcomm, Function.Bijective.of_comp_iff' hab']

/-- Bijectivity of `Hⁿ(Y, M) → Hⁿ(X, f^* M)` passes to retracts of finite sums: if
`∑ᵢ πᵢ ≫ ιᵢ = 𝟙` for morphisms `ιᵢ : Nᵢ ⟶ M`, `πᵢ : M ⟶ Nᵢ` and the maps for the `Nᵢ` are
bijective, so is the map for `M` (e.g. `M` a finite biproduct of the `Nᵢ`). -/
lemma bijective_pullbackCohomologyMap_of_retract {M : Y.Modules} {J : Type*} [Fintype J]
    (N : J → Y.Modules) (ι : ∀ j, N j ⟶ M) (π : ∀ j, M ⟶ N j) (htot : ∑ j, π j ≫ ι j = 𝟙 M)
    (n : ℕ) (h : ∀ j, Function.Bijective (pullbackCohomologyMap f (N j) n)) :
    Function.Bijective (pullbackCohomologyMap f M n) := by
  have hT : ∑ j, (toAbFunctor Y).map (π j) ≫ (toAbFunctor Y).map (ι j) = 𝟙 _ := by
    simp only [← Functor.map_comp, ← Functor.map_sum, htot]
    exact (toAbFunctor Y).map_id M
  have hT' : ∑ j, (pullback f ⋙ toAbFunctor X).map (π j) ≫
      (pullback f ⋙ toAbFunctor X).map (ι j) = 𝟙 _ := by
    simp only [← Functor.map_comp, ← Functor.map_sum, htot]
    exact (pullback f ⋙ toAbFunctor X).map_id M
  have hY (x : M.H n) : x = ∑ j, CategoryTheory.Sheaf.H.map ((toAbFunctor Y).map (ι j)) n
      (CategoryTheory.Sheaf.H.map ((toAbFunctor Y).map (π j)) n x) := by
    simp only [CategoryTheory.Sheaf.H.map_apply, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀]
    rw [← Ext.comp_sum, ← Ext.mk₀_sum, hT, Ext.comp_mk₀_id]
  have hX (y : ((pullback f).obj M).H n) : y = ∑ j,
      CategoryTheory.Sheaf.H.map ((pullback f ⋙ toAbFunctor X).map (ι j)) n
        (CategoryTheory.Sheaf.H.map ((pullback f ⋙ toAbFunctor X).map (π j)) n y) := by
    simp only [CategoryTheory.Sheaf.H.map_apply, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀]
    rw [← Ext.comp_sum, ← Ext.mk₀_sum, hT', Ext.comp_mk₀_id]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hY x]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have : CategoryTheory.Sheaf.H.map ((toAbFunctor Y).map (π j)) n x = 0 := by
      apply (h j).1
      rw [pullbackCohomologyMap_naturality, hx, map_zero, map_zero]
    rw [this, map_zero]
  · intro y
    choose x hx using fun j ↦ (h j).2
      (CategoryTheory.Sheaf.H.map ((pullback f ⋙ toAbFunctor X).map (π j)) n y)
    refine ⟨∑ j, CategoryTheory.Sheaf.H.map ((toAbFunctor Y).map (ι j)) n (x j), ?_⟩
    rw [map_sum, hX y]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [pullbackCohomologyMap_naturality, hx]
    rfl

/-- The morphism of short complexes of abelian sheaves `f⁻¹ S → f^* S`, for a short complex `S` of
`𝒪_Y`-modules. -/
def abPullbackToPullbackShortComplex (S : ShortComplex Y.Modules) :
    (S.map (toAbFunctor Y)).map (abPullback f) ⟶ (S.map (pullback f)).map (toAbFunctor X) where
  τ₁ := abPullbackToPullback f S.X₁
  τ₂ := abPullbackToPullback f S.X₂
  τ₃ := abPullbackToPullback f S.X₃
  comm₁₂ := (abPullbackToPullback_naturality f S.f).symm
  comm₂₃ := (abPullbackToPullback_naturality f S.g).symm

/-- `Hⁿ(Y, M) → Hⁿ(X, f^* M)` commutes with connecting maps: for a short complex `S` of
`𝒪_Y`-modules whose underlying abelian sheaves form a short exact sequence, and such that those of
`f^* S` do too (e.g. `S` short exact and `f` flat). -/
lemma pullbackCohomologyMap_comp_extClass {S : ShortComplex Y.Modules}
    (hS : (S.map (toAbFunctor Y)).ShortExact)
    (hS' : ((S.map (pullback f)).map (toAbFunctor X)).ShortExact) (n : ℕ) (x : S.X₃.H n) :
    pullbackCohomologyMap f S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (pullbackCohomologyMap f S.X₃ n x).comp hS'.extClass rfl :=
  TopCat.Sheaf.globalCohomologyPullbackMap_comp_extClass (f := f.base) hS hS'
    (abPullbackToPullbackShortComplex f S) n x

/-- **Čech computation of `Hⁿ(Y, M) → Hⁿ(X, f^* M)`.** For a finite open cover `U` of `Y` such
that `M` is acyclic on the finite intersections of the `Uᵢ` and `f^* M` on those of the `f⁻¹ Uᵢ`,
the map `Hⁿ(Y, M) → Hⁿ(X, f^* M)` is bijective if and only if the map of Čech cohomology
`Ȟⁿ(U, M) → Ȟⁿ(f⁻¹ U, f^* M)` induced by the unit `M → f_* f^* M` is. -/
theorem bijective_pullbackCohomologyMap_iff_cech {k : ℕ} (U : Fin k → Opens Y.carrier)
    (hU : ⨆ i, U i = ⊤) (M : Y.Modules) (hM : TopCat.Sheaf.IsLerayAcyclic U M.toAbSheaf)
    (hM' : TopCat.Sheaf.IsLerayAcyclic (fun i ↦ (Opens.map f.base).obj (U i))
      ((pullback f).obj M).toAbSheaf) (n : ℕ) :
    Function.Bijective (pullbackCohomologyMap f M n) ↔
      Function.Bijective (HomologicalComplex.homologyMap
        (TopCat.Presheaf.cechPullbackComplexMap f.base U
          (TopCat.Sheaf.pullbackAdjoint (f := f.base) (abPullbackToPullback f M))) n) := by
  rw [pullbackCohomologyMap_eq]
  exact TopCat.Sheaf.bijective_globalCohomologyPullbackMap_iff U hU hM hM' _ n

end AlgebraicGeometry.LocallyRingedSpace.Modules
