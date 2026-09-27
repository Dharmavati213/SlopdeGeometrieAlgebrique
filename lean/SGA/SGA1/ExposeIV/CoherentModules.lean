/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIV.Schemes
import SGA.Foundations.QuasiCoherent.StalkModule

/-!
# SGA 1, Exposé IV, §6: coherent sheaves on schemes

The statements of IV.6.6, IV.6.10 and IV.6.11 for a coherent sheaf `F` on `X`, for a morphism
`f : X → Y` locally of finite type over a locally noetherian scheme. A coherent sheaf is taken to
be a quasi-coherent module of finite type (these agree on locally noetherian schemes, which is
where SGA uses them). `F` is flat over `Y` at `x` (`Scheme.Modules.FlatAt f F x`) if the stalk
`F_x` is a flat module over `𝒪_{Y, f(x)}`.

* IV.6.6: `isOpenMap_of_flatAt`;
* IV.6.10: `isOpen_setOf_flatAt`;
* IV.6.11: `exists_nonempty_forall_flatAt`.

For `F = 𝒪_X` these specialize to the statements of `Schemes` (`flatAt_unit_iff`).

As in SGA, all three reduce to the affine statements of `OpenMorphisms` and `FlatLocus`, through
the description of stalks of quasi-coherent modules over affine opens
(`Scheme.Modules.flatAt_iff`).
-/

universe u

open AlgebraicGeometry CategoryTheory Scheme.Modules

namespace SGA.SGA1.ExposeIV

variable {X Y : Scheme.{u}}

lemma _root_.AlgebraicGeometry.IsAffineOpen.fromSpec_mem {V : X.Opens} (hV : IsAffineOpen V)
    (P : PrimeSpectrum Γ(X, V)) : hV.fromSpec P ∈ V := by
  rw [← SetLike.mem_coe, ← hV.range_fromSpec]
  exact ⟨P, rfl⟩

lemma _root_.AlgebraicGeometry.IsAffineOpen.primeIdealOf_fromSpec {V : X.Opens}
    (hV : IsAffineOpen V) (P : PrimeSpectrum Γ(X, V)) :
    hV.primeIdealOf ⟨hV.fromSpec P, hV.fromSpec_mem P⟩ = P :=
  hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨_, hV.fromSpec_mem P⟩)

set_option backward.isDefEq.respectTransparency.types false in
/-- For `F = 𝒪_X`, flatness of `F` over `Y` at `x` is flatness of the stalk map of `f` at `x`. -/
theorem flatAt_unit_iff (f : X ⟶ Y) (x : X) :
    FlatAt f (SheafOfModules.unit X.ringCatSheaf) x ↔ (f.stalkMap x).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  rw [flatAt_iff f _ hU hV hVU ⟨x, hxV⟩, flat_stalkMap_iff U hU V hV hVU hxV]
  let := (f.appLE U V hVU).hom.toAlgebra
  exact flat_localizedModule_iff_flat_localization _

set_option backward.isDefEq.respectTransparency.types false in
/-- IV.6.10: let `f : X → Y` be locally of finite type, with `Y` locally noetherian, and `F` a
coherent sheaf on `X` (a quasi-coherent module of finite type). The set of points `x` of `X` at
which `F` is flat over `Y`, i.e. `F_x` is flat over `𝒪_{Y,f(x)}`, is open. -/
theorem isOpen_setOf_flatAt (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] : IsOpen {x : X | F.FlatAt f x} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finiteType_appLE hU hV hVU
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have := F.finite_sections hV
  algebraize [(f.appLE U V hVU).hom]
  let : Module Γ(Y, U) Γ(F, V) := Module.compHom _ (algebraMap Γ(Y, U) Γ(X, V))
  have : IsScalarTower Γ(Y, U) Γ(X, V) Γ(F, V) := IsScalarTower.of_compHom _ _ _
  let O := {P : PrimeSpectrum Γ(X, V) |
    Module.Flat Γ(Y, U) (LocalizedModule P.asIdeal.primeCompl Γ(F, V))}
  have hO : IsOpen O := isOpen_flatLocus
  have key (y : X) (hy : y ∈ V) : F.FlatAt f y ↔ hV.primeIdealOf ⟨y, hy⟩ ∈ O :=
    flatAt_iff f F hU hV hVU ⟨y, hy⟩
  refine ⟨hV.fromSpec '' O, ?_, hV.fromSpec.isOpenEmbedding.isOpenMap _ hO,
    ⟨_, (key x hxV).1 hx, hV.fromSpec_primeIdealOf ⟨x, hxV⟩⟩⟩
  rintro _ ⟨P, hP, rfl⟩
  refine (key _ (hV.fromSpec_mem P)).2 ?_
  rw [hV.primeIdealOf_fromSpec]
  exact hP

set_option backward.isDefEq.respectTransparency.types false in
/-- IV.6.6: let `f : X → Y` be locally of finite type, with `Y` locally noetherian, and `F` a
coherent sheaf on `X` with support `X` (all stalks nonzero), flat over `Y`. Then `f` is open.
(SGA assumes `f` of finite type; the statement is local.) As in SGA, one reduces to the affine case
`isOpenMap_comap_of_flat`. -/
theorem isOpenMap_of_flatAt (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hsupp : ∀ x : X, Nontrivial (F.presheaf.stalk x)) (hflat : ∀ x : X, F.FlatAt f x) :
    IsOpenMap f := by
  intro W hW
  refine isOpen_iff_forall_mem_open.mpr ?_
  rintro _ ⟨x, hxW, rfl⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finiteType_appLE hU hV hVU
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have := F.finite_sections hV
  algebraize [(f.appLE U V hVU).hom]
  let : Module Γ(Y, U) Γ(F, V) := Module.compHom _ (algebraMap Γ(Y, U) Γ(X, V))
  have : IsScalarTower Γ(Y, U) Γ(X, V) Γ(F, V) := IsScalarTower.of_compHom _ _ _
  -- the localizations of `Γ(F, V)` are flat over `Γ(Y, U)`
  have hloc (P : PrimeSpectrum Γ(X, V)) :
      Module.Flat Γ(Y, U) (LocalizedModule P.asIdeal.primeCompl Γ(F, V)) := by
    have := (flatAt_iff f F hU hV hVU ⟨_, hV.fromSpec_mem P⟩).1 (hflat _)
    rwa [hV.primeIdealOf_fromSpec] at this
  have hflatM : Module.Flat Γ(Y, U) Γ(F, V) :=
    Module.flat_of_isLocalized_maximal Γ(X, V) Γ(F, V)
      (fun P _ ↦ LocalizedModule P.primeCompl Γ(F, V))
      (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl Γ(F, V))
      fun P hP ↦ hloc ⟨P, hP.isPrime⟩
  have hsuppM : Module.support Γ(X, V) Γ(F, V) = Set.univ := by
    refine Set.eq_univ_of_forall fun P ↦ ?_
    rw [Module.mem_support_iff]
    have e := F.stalkLinearEquiv hV ⟨_, hV.fromSpec_mem P⟩
    rw [hV.primeIdealOf_fromSpec] at e
    have := hsupp (hV.fromSpec P)
    exact e.toEquiv.symm.nontrivial
  have hopen := isOpenMap_comap_of_flat (A := Γ(Y, U)) (B := Γ(X, V)) (M := Γ(F, V)) hsuppM
  have hfg : (f : X → Y) ∘ hV.fromSpec = hU.fromSpec ∘ Spec.map (f.appLE U V hVU) := by
    ext p
    simp only [Function.comp_apply, ← Scheme.Hom.comp_apply,
      IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU]
  refine ⟨hU.fromSpec '' (PrimeSpectrum.comap (algebraMap Γ(Y, U) Γ(X, V)) ''
    (hV.fromSpec ⁻¹' W)), ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
    exact ⟨hV.fromSpec P, hP, congr_fun hfg P⟩
  · exact hU.fromSpec.isOpenEmbedding.isOpenMap _
      (hopen _ (hW.preimage hV.fromSpec.continuous))
  · refine ⟨_, ⟨hV.primeIdealOf ⟨x, hxV⟩, ?_, rfl⟩, ?_⟩
    · change hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) ∈ W
      rw [hV.fromSpec_primeIdealOf]
      exact hxW
    · have := congr_fun hfg (hV.primeIdealOf ⟨x, hxV⟩)
      simp only [Function.comp_apply] at this
      rw [hV.fromSpec_primeIdealOf] at this
      exact this.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine form of IV.6.11 (generic flatness), transported to stalks: for affine opens
`V ⊆ f⁻¹ W` with `Γ(Y, W)` a noetherian domain and `F` coherent, there is `g ≠ 0` in `Γ(Y, W)`
such that `F` is flat over `Y` at every point of `V` above `D(g)`. -/
lemma exists_ne_zero_forall_flatAt (f : X ⟶ Y) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] {W : Y.Opens} (hW : IsAffineOpen W)
    [IsNoetherianRing Γ(Y, W)] [IsDomain Γ(Y, W)] {V : X.Opens} (hV : IsAffineOpen V)
    (hVW : V ≤ f ⁻¹ᵁ W) :
    ∃ g : Γ(Y, W), g ≠ 0 ∧ ∀ x ∈ V, f x ∈ Y.basicOpen g → F.FlatAt f x := by
  have := f.finiteType_appLE hW hV hVW
  have := F.finite_sections hV
  algebraize [(f.appLE W V hVW).hom]
  let : Module Γ(Y, W) Γ(F, V) := Module.compHom _ (algebraMap Γ(Y, W) Γ(X, V))
  have : IsScalarTower Γ(Y, W) Γ(X, V) Γ(F, V) := IsScalarTower.of_compHom _ _ _
  obtain ⟨g, hg0, hflat⟩ := exists_forall_flat_localizedModule (A := Γ(Y, W)) (B := Γ(X, V))
    (M := Γ(F, V))
  refine ⟨g, hg0, fun x hxV hx ↦ ?_⟩
  rw [flatAt_iff f F hW hV hVW ⟨x, hxV⟩]
  refine hflat _ fun hmem ↦ ?_
  have hxb : x ∈ X.basicOpen (f.appLE W V hVW g) := by
    rw [Scheme.basicOpen_appLE]
    exact ⟨hxV, hx⟩
  have : hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) ∈ X.basicOpen (f.appLE W V hVW g) := by
    rwa [hV.fromSpec_primeIdealOf]
  rw [← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen] at this
  exact this hmem

/-- IV.6.11: let `f : X → Y` be of finite type, with `Y` integral and locally noetherian, and `F`
a coherent sheaf on `X`. There is a nonempty open `V ⊆ Y` such that `F` is flat over `Y` at every
point of `f⁻¹(V)`. The proof uses generic freeness (IV.6.7) on a finite affine cover of `f⁻¹(W)`,
`W` an affine open of `Y`, as noted in SGA after IV.6.11. -/
theorem exists_nonempty_forall_flatAt (f : X ⟶ Y) [IsIntegral Y] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ ∀ x, f x ∈ V → F.FlatAt f x := by
  classical
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : Nonempty W := ⟨⟨y, hyW⟩⟩
  have : IsNoetherianRing Γ(Y, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let ι := {V : X.affineOpens // (V : X.Opens) ≤ f ⁻¹ᵁ W}
  obtain ⟨t, ht⟩ := (f.isCompact_preimage hW.isCompact).elim_finite_subcover
    (fun V : ι ↦ (V.1 : Set X)) (fun V ↦ V.1.1.2) (by
      intro x hx
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx (f ⁻¹ᵁ W).2
      exact Set.mem_iUnion.2 ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩)
  choose g hg0 hflat using fun V : ι ↦ exists_ne_zero_forall_flatAt f F hW V.1.2 V.2
  refine ⟨Y.basicOpen (∏ V ∈ t, g V), ?_, fun x hx ↦ ?_⟩
  · have hne : Y.basicOpen (∏ V ∈ t, g V) ≠ ⊥ := by
      rw [ne_eq, basicOpen_eq_bot_iff]
      exact Finset.prod_ne_zero_iff.2 fun V _ ↦ hg0 V
    by_contra h
    exact hne ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).1 h)
  · have hxW : x ∈ f ⁻¹ᵁ W := Y.basicOpen_le _ hx
    obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.1 (ht hxW)
    refine hflat V x hxV ?_
    rw [← Finset.mul_prod_erase t g hVt, Scheme.basicOpen_mul] at hx
    exact hx.1

end SGA.SGA1.ExposeIV
