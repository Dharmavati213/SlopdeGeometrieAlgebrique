/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.CoherentAffineCharts
import SGA.SGA2.ExposeIII.SheafHartogsGluing

/-!
# Hartogs for finitely presented modules on locally noetherian schemes

This is III.3.5 for actual scheme modules, using mathlib's local finite
presentation condition (the coherent-module condition on a locally
noetherian scheme). Both the stalk modules and section restrictions are
the actual ones. Affine coefficient presentations and all scalar
compatibilities are proved, and unique extension is glued on a basis.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The genuine affine-chart Hartogs equivalence, with the depth condition
on the ambient module's literal stalks. -/
theorem affineChart_moduleRestriction_iff (M : X.Modules) [M.IsFinitePresentation]
    (U W : X.Opens) (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) (affineModuleCoefficients (M.restrict hU.fromSpec))] :
    (∀ x : X, x ∈ U → x ∉ W → (2 : ℕ∞) ≤ moduleStalkDepth M x) ↔
      Function.Bijective (M.presheaf.map (homOfLE inf_le_left : U ⊓ W ⟶ U).op) := by
  let R := Γ(X, U)
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let f : Spec R ⟶ X := hU.fromSpec
  let N := M.restrict f
  have (p : PrimeSpectrum R) :
      Module.Finite ((Spec R).presheaf.stalk p) (schemeModuleStalk N p) :=
    affineQuasicoherentStalkFinite N p
  let P : Opens (PrimeSpectrum R) := f ⁻¹ᵁ W
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
    ((P : Set (PrimeSpectrum R))ᶜ)).mp P.isOpen.isClosed_compl
  have hW : affineSupportComplement I = f ⁻¹ᵁ W := by
    apply Opens.ext
    change (PrimeSpectrum.zeroLocus (I : Set R))ᶜ = (P : Set (PrimeSpectrum R))
    rw [← hI, compl_compl]
  have hdepth :
      (∀ x : X, x ∈ U → x ∉ W → (2 : ℕ∞) ≤ moduleStalkDepth M x) ↔
      (∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
        (2 : ℕ∞) ≤ moduleStalkDepth N p) := by
    constructor
    · intro h p hp
      rw [moduleStalkDepth_restrict f M p]
      apply h (f p)
      · exact (show Set.range f ⊆ (U : Set X) from hU.range_fromSpec.le) ⟨p, rfl⟩
      · rw [← hI] at hp
        exact hp
    · intro h x hx hxW
      have hxrange : x ∈ Set.range f := hU.range_fromSpec.symm ▸ hx
      obtain ⟨p, rfl⟩ := hxrange
      rw [← moduleStalkDepth_restrict f M p]
      apply h p
      rw [← hI]
      exact hxW
  rw [hdepth, affineQuasicoherent_hartogs_iff N I]
  rw [← ConcreteCategory.isIso_iff_bijective, ← ConcreteCategory.isIso_iff_bijective]
  let j : affineSupportComplement I ⟶ (⊤ : (Spec R).Opens) := homOfLE le_top
  have ht : f ''ᵁ (⊤ : (Spec R).Opens) = U :=
    f.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  have hp : f ''ᵁ affineSupportComplement I = U ⊓ W := by
    rw [hW, f.image_preimage_eq_opensRange_inf, show f.opensRange = U from hU.opensRange_fromSpec]
  constructor
  · intro h
    have : IsIso (M.presheaf.map (f.opensFunctor.map j).op) := h
    exact isIso_presheaf_map_of_eq M.presheaf _ (f.opensFunctor.map j) hp.symm ht.symm
  · intro h
    have := h
    exact isIso_presheaf_map_of_eq M.presheaf (f.opensFunctor.map j)
      (homOfLE inf_le_left : U ⊓ W ⟶ U) hp ht

/-- The actual underlying abelian sheaf of a scheme module. -/
def schemeModuleAbSheaf (M : X.Modules) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj M

/-- Literal stalk depth at least two gives actual unique extension of
module sections on every open, by genuine sheaf gluing on finite affine charts. -/
theorem isIso_moduleRestriction_of_stalkDepth (M : X.Modules) [M.IsFinitePresentation]
    (W : X.Opens) (h : ∀ x : X, x ∉ W → (2 : ℕ∞) ≤ moduleStalkDepth M x)
    (V : X.Opens) :
    IsIso (M.presheaf.map (homOfLE inf_le_left : V ⊓ W ⟶ V).op) := by
  let B := {U : X.Opens // ∃ hU : IsAffineOpen U,
    Module.Finite Γ(X, U) (affineModuleCoefficients (M.restrict hU.fromSpec))}
  apply isIso_restriction_of_basis (schemeModuleAbSheaf M) W (fun U : B => U.1)
    (by
      apply Opens.isBasis_iff_nbhd.mpr
      intro V x hx
      obtain ⟨U, hU, hxU, hUV, hfin⟩ := exists_affine_mem_subset_finiteCoefficients M hx
      exact ⟨U, ⟨⟨U, hU, hfin⟩, rfl⟩, hxU, hUV⟩)
  intro U
  obtain ⟨hU, hfin⟩ := U.2
  have := hfin
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ((affineChart_moduleRestriction_iff M U.1 W hU).mp (fun x _ hx => h x hx))

/-- **III.3.5:** on a locally noetherian scheme, a finitely presented actual
module has depth at least two along a closed subset exactly when restriction
of its actual sections is bijective on every open. -/
theorem coherent_hartogs_iff (M : X.Modules) [M.IsFinitePresentation] (Z : Closeds X) :
    (∀ x : X, x ∈ Z → (2 : ℕ∞) ≤ moduleStalkDepth M x) ↔
      ∀ V : X.Opens, Function.Bijective
        (M.presheaf.map (homOfLE inf_le_left : V ⊓ Z.compl ⟶ V).op) := by
  classical
  constructor
  · intro h V
    have := isIso_moduleRestriction_of_stalkDepth M Z.compl (fun x hx => h x (not_not.mp hx)) V
    exact ConcreteCategory.bijective_of_isIso _
  · intro h x hxZ
    obtain ⟨U, hU, hxU, _, hfin⟩ :=
      exists_affine_mem_subset_finiteCoefficients M (show x ∈ (⊤ : X.Opens) from trivial)
    have := hfin
    exact (affineChart_moduleRestriction_iff M U Z.compl hU).mpr (h U) x hxU
      (fun hxc => hxc hxZ)

/-- The actual extension equivalence on every open of a locally noetherian
scheme for a coherent module satisfying the literal stalk-depth condition. -/
def coherentHartogsEquiv (M : X.Modules) [M.IsFinitePresentation] (Z : Closeds X)
    (h : ∀ x : X, x ∈ Z → (2 : ℕ∞) ≤ moduleStalkDepth M x) (V : X.Opens) :
    Γ(M, V) ≃+ Γ(M, V ⊓ Z.compl) :=
  AddEquiv.ofBijective (M.presheaf.map (homOfLE inf_le_left : V ⊓ Z.compl ⟶ V).op).hom
    ((coherent_hartogs_iff M Z).mp h V)

end SGA.SGA2.ExposeIII
