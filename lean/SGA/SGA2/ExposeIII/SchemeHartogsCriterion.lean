/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.SchemeHartogs

/-! # SGA 2, III.3.5: the structure-sheaf Hartogs criterion in both directions -/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Actual bijective structure restriction on the affine-open basis forces
literal local structure-ring depth at least two along the omitted closed set. -/
theorem structureStalkDepth_two_le_of_affineRestriction_bijective (Z : Closeds X)
    (h : ∀ (U : X.Opens), IsAffineOpen U → Function.Bijective
      (X.presheaf.map (homOfLE inf_le_left : U ⊓ Z.compl ⟶ U).op))
    (x : X) (hx : x ∈ Z) :
    (2 : ℕ∞) ≤ structureStalkDepth X x := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (show x ∈ (⊤ : X.Opens) from trivial)
  let R := Γ(X, U)
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let f : Spec R ⟶ X := hU.fromSpec
  let P : Opens (PrimeSpectrum R) := f ⁻¹ᵁ Z.compl
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
    ((P : Set (PrimeSpectrum R))ᶜ)).mp P.isOpen.isClosed_compl
  have hW : affineSupportComplement I = f ⁻¹ᵁ Z.compl := by
    apply Opens.ext
    change (PrimeSpectrum.zeroLocus (I : Set R))ᶜ = (P : Set (PrimeSpectrum R))
    rw [← hI, compl_compl]
  have hpreU : f ⁻¹ᵁ U = ⊤ := hU.fromSpec_preimage_self
  have hpreUZ : f ⁻¹ᵁ (U ⊓ Z.compl) = affineSupportComplement I := by
    rw [Scheme.Hom.preimage_inf, hpreU, top_inf_eq, hW]
  have : IsIso (X.presheaf.map (homOfLE inf_le_left : U ⊓ Z.compl ⟶ U).op) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (h U hU)
  have : IsIso (f.app U) := f.isIso_app U
    (by rw [show f.opensRange = U from hU.opensRange_fromSpec])
  have : IsIso (f.app (U ⊓ Z.compl)) := f.isIso_app (U ⊓ Z.compl)
    (by rw [show f.opensRange = U from hU.opensRange_fromSpec]; exact inf_le_left)
  have : IsIso (f.app U ≫ (Spec R).presheaf.map
      ((Opens.map f.base).map (homOfLE inf_le_left : U ⊓ Z.compl ⟶ U)).op) := by
    erw [← f.naturality (homOfLE inf_le_left : U ⊓ Z.compl ⟶ U).op]
    infer_instance
  have := IsIso.of_isIso_comp_left (f.app U) ((Spec R).presheaf.map
    ((Opens.map f.base).map (homOfLE inf_le_left : U ⊓ Z.compl ⟶ U)).op)
  have := isIso_presheaf_map_of_eq (Spec R).presheaf
    (homOfLE le_top : affineSupportComplement I ⟶ ⊤)
    ((Opens.map f.base).map (homOfLE inf_le_left : U ⊓ Z.compl ⟶ U)) hpreUZ.symm hpreU.symm
  have hd : (2 : ℕ∞) ≤ depth I (ModuleCat.of R R) :=
    (two_le_depth_iff_affineRestriction_bijective I (ModuleCat.of R R)).mpr
      (ConcreteCategory.bijective_of_isIso ((Spec R).presheaf.map
        (homOfLE le_top : affineSupportComplement I ⟶ ⊤).op))
  have hxrange : x ∈ Set.range f := by
    change x ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]
    exact hxU
  obtain ⟨p, rfl⟩ := hxrange
  rw [structureStalkDepth_eq_of_isOpenImmersion f p, ← localDepth_self_eq_structureStalkDepth]
  apply (le_depth_iff_forall_localDepth I (ModuleCat.of R R) 2).mp hd p
  rw [← hI]
  exact fun hp ↦ hp hx

/-- **III.3.5, structure-sheaf case:** literal stalk depth at least two is
equivalent to unique extension of actual structure sections on every open. -/
theorem structureStalkDepth_two_le_iff_restriction_bijective (Z : Closeds X) :
    (∀ x : X, x ∈ Z → (2 : ℕ∞) ≤ structureStalkDepth X x) ↔
      ∀ V : X.Opens, Function.Bijective
        (X.presheaf.map (homOfLE inf_le_left : V ⊓ Z.compl ⟶ V).op) :=
  ⟨fun h V ↦ structureRestriction_bijective_of_stalkDepth Z h V,
    fun h x hx ↦ structureStalkDepth_two_le_of_affineRestriction_bijective Z (fun U _ ↦ h U) x hx⟩

end SGA.SGA2.ExposeIII
