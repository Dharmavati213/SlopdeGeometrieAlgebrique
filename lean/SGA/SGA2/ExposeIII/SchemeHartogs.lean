/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.AffineHartogs
import SGA.SGA2.ExposeIII.AffineStalkDepth
import SGA.SGA2.ExposeIII.SheafHartogsGluing
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Structure-sheaf Hartogs on locally noetherian schemes

The hypothesis is depth at least two of the actual local structure ring
at every point of the closed support. Affine Hartogs is transported along
actual affine-open immersions, and the genuine sheaf gluing criterion
then gives unique extension on every open.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

/-- Depth of the actual local structure ring, regarded as a module over itself. -/
def structureStalkDepth (X : Scheme.{u}) (x : X) : ℕ∞ :=
  depth (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))

/-- Self-module depth is invariant under an isomorphism of noetherian local rings. -/
theorem depth_self_eq_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) :
    depth (IsLocalRing.maximalIdeal A) (ModuleCat.of A A) =
      depth (IsLocalRing.maximalIdeal B) (ModuleCat.of B B) := by
  have h := depth_eq_of_semilinearEquiv e (IsLocalRing.maximalIdeal A)
    (M := ModuleCat.of A A) (N := ModuleCat.of B B) e.toSemilinearEquiv
  rw [IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective] at h
  exact h

/-- The self-localization module convention computes depth of the actual
local structure ring of an affine scheme. -/
theorem localDepth_self_eq_structureStalkDepth {R : CommRingCat.{u}} [IsNoetherianRing R]
    (p : PrimeSpectrum R) :
    localDepth (ModuleCat.of R R) p = structureStalkDepth (Spec R) p := by
  let e : LocalizedModule.AtPrime p.asIdeal R ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal :=
    (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl R)
      (Algebra.linearMap R (Localization.AtPrime p.asIdeal))).extendScalarsOfIsLocalization
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
  exact (depth_eq_of_linearEquiv (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
    (M := ModuleCat.of (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal R))
    (N := ModuleCat.of (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) e).trans
      (depth_self_eq_of_ringEquiv (affineStalkRingEquiv p).toRingEquiv)

/-- Actual local structure-ring depth is unchanged by an open immersion. -/
theorem structureStalkDepth_eq_of_isOpenImmersion {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    structureStalkDepth Y (f x) = structureStalkDepth X x :=
  depth_self_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Hartogs on an actual affine open inside a locally noetherian scheme.
The stalk condition is stated in the ambient scheme and is transported
through the canonical affine-open morphism, not assumed on a new model. -/
theorem isIso_affineOpen_restriction_of_structureStalkDepth
    (U W : X.Opens) (hU : IsAffineOpen U)
    (h : ∀ x : X, x ∈ U → x ∉ W → (2 : ℕ∞) ≤ structureStalkDepth X x) :
    IsIso (X.presheaf.map (homOfLE inf_le_left : U ⊓ W ⟶ U).op) := by
  let R := Γ(X, U)
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let f : Spec R ⟶ X := hU.fromSpec
  let P : Opens (PrimeSpectrum R) := f ⁻¹ᵁ W
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal
    ((P : Set (PrimeSpectrum R))ᶜ)).mp P.isOpen.isClosed_compl
  have hW : affineSupportComplement I = f ⁻¹ᵁ W := by
    apply Opens.ext
    change (PrimeSpectrum.zeroLocus (I : Set R))ᶜ = (P : Set (PrimeSpectrum R))
    rw [← hI, compl_compl]
  have hlocal : ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      (2 : ℕ∞) ≤ localDepth (ModuleCat.of R R) p := by
    intro p hp
    rw [localDepth_self_eq_structureStalkDepth,
      ← structureStalkDepth_eq_of_isOpenImmersion f p]
    apply h (f p)
    · exact (show Set.range hU.fromSpec ⊆ (U : Set X) from hU.range_fromSpec.le) ⟨p, rfl⟩
    · rw [← hI] at hp
      exact hp
  have hres : IsIso ((Spec R).presheaf.map
      (homOfLE le_top : affineSupportComplement I ⟶ ⊤).op) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (affineStructureRestriction_bijective I
        ((le_depth_iff_forall_localDepth I (ModuleCat.of R R) 2).mpr hlocal))
  have hpreU : f ⁻¹ᵁ U = ⊤ := hU.fromSpec_preimage_self
  have hpreUW : f ⁻¹ᵁ (U ⊓ W) = affineSupportComplement I := by
    rw [Scheme.Hom.preimage_inf, hpreU, top_inf_eq, hW]
  have hres' : IsIso ((Spec R).presheaf.map
      ((Opens.map f.base).map (homOfLE inf_le_left : U ⊓ W ⟶ U)).op) :=
    isIso_presheaf_map_of_eq (Spec R).presheaf _
      (homOfLE le_top : affineSupportComplement I ⟶ ⊤) hpreUW hpreU
  have happU : IsIso (f.app U) := f.isIso_app U
    (by rw [show f.opensRange = U from hU.opensRange_fromSpec])
  have happUW : IsIso (f.app (U ⊓ W)) := f.isIso_app (U ⊓ W)
    (by rw [show f.opensRange = U from hU.opensRange_fromSpec]; exact inf_le_left)
  have : IsIso (X.presheaf.map (homOfLE inf_le_left : U ⊓ W ⟶ U).op ≫ f.app (U ⊓ W)) := by
    rw [f.naturality]
    exact IsIso.comp_isIso' happU hres'
  exact IsIso.of_isIso_comp_right _ (f.app (U ⊓ W))

/-- Unique extension of structure-sheaf sections across the omitted set,
on every open, follows from the actual local depth condition. -/
theorem isIso_structureRestriction_of_stalkDepth (W : X.Opens)
    (h : ∀ x : X, x ∉ W → (2 : ℕ∞) ≤ structureStalkDepth X x)
    (V : X.Opens) :
    IsIso (X.presheaf.map (homOfLE inf_le_left : V ⊓ W ⟶ V).op) := by
  apply isIso_restriction_of_basis X.sheaf W (fun U : X.affineOpens => U.1)
    (by simpa only [Subtype.range_coe] using X.isBasis_affineOpens)
  intro U
  exact isIso_affineOpen_restriction_of_structureStalkDepth U.1 W U.2
    (fun x _ hx => h x hx)

/-- **III.3.5, structure-sheaf Hartogs:** on a locally noetherian scheme,
actual local structure-ring depth at least two along a closed subset
gives bijective restriction on every open of the scheme. -/
theorem structureRestriction_bijective_of_stalkDepth (Z : Closeds X)
    (h : ∀ x : X, x ∈ Z → (2 : ℕ∞) ≤ structureStalkDepth X x)
    (V : X.Opens) :
    Function.Bijective (X.presheaf.map
      (homOfLE inf_le_left : V ⊓ Z.compl ⟶ V).op) := by
  classical
  have := isIso_structureRestriction_of_stalkDepth Z.compl
    (fun x hx => h x (not_not.mp hx)) V
  exact ConcreteCategory.bijective_of_isIso _

/-- The every-open Hartogs restriction is an actual ring equivalence. -/
def structureHartogsRingEquiv (Z : Closeds X)
    (h : ∀ x : X, x ∈ Z → (2 : ℕ∞) ≤ structureStalkDepth X x)
    (V : X.Opens) :
    X.presheaf.obj (op V) ≃+* X.presheaf.obj (op (V ⊓ Z.compl)) :=
  RingEquiv.ofBijective (X.presheaf.map
    (homOfLE inf_le_left : V ⊓ Z.compl ⟶ V).op).hom
      (structureRestriction_bijective_of_stalkDepth Z h V)

/-- In particular, the actual global restriction
`Γ(X, O_X) → Γ(X \ Z, O_X)` is bijective. -/
theorem structureGlobalRestriction_bijective_of_stalkDepth (Z : Closeds X)
    (h : ∀ x : X, x ∈ Z → (2 : ℕ∞) ≤ structureStalkDepth X x) :
    Function.Bijective (X.presheaf.map (homOfLE le_top : Z.compl ⟶ ⊤).op) := by
  classical
  have := isIso_structureRestriction_of_stalkDepth Z.compl
    (fun x hx => h x (not_not.mp hx)) ⊤
  have := isIso_presheaf_map_of_eq X.presheaf
    (homOfLE le_top : Z.compl ⟶ ⊤)
    (homOfLE inf_le_left : ⊤ ⊓ Z.compl ⟶ ⊤) (by simp) rfl
  exact ConcreteCategory.bijective_of_isIso _

/-- The actual global Hartogs ring isomorphism. -/
def structureGlobalHartogsRingEquiv (Z : Closeds X)
    (h : ∀ x : X, x ∈ Z → (2 : ℕ∞) ≤ structureStalkDepth X x) :
    X.presheaf.obj (op ⊤) ≃+* X.presheaf.obj (op Z.compl) :=
  RingEquiv.ofBijective (X.presheaf.map (homOfLE le_top : Z.compl ⟶ ⊤).op).hom
    (structureGlobalRestriction_bijective_of_stalkDepth Z h)

end SGA.SGA2.ExposeIII
