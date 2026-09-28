/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.RingedModuleFlasqueAcyclic

/-!
# SGA 2, V.3.2: supported sections commute with ringed-space pushforward

The supported sections of a direct image are the supported sections on the
inverse image, with scalars restricted along the actual structure-sheaf map.
This is a natural isomorphism of module-valued functors, including on global
sections the ring homomorphism appearing in Lemma V.3.2.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
  {R : Sheaf RingCat.{u} X} {S : Sheaf RingCat.{u} Y}
  (φ : S ⟶ (Sheaf.pushforward RingCat f).obj R)

/-- On any open of the target, supported sections commute with direct image
and restriction of scalars along the structure-sheaf map. -/
def ringedModulePushforwardSupportedSectionsIso (Z : Closeds Y) (U : Opens Y) :
    ringedModulePushforward f φ ⋙ moduleGammaZSectionsFunctor S Z U ≅
      moduleGammaZSectionsFunctor R (Z.preimage f.hom.continuous) ((Opens.map f).obj U) ⋙
        ModuleCat.restrictScalars (φ.hom.app (op U)).hom :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The homomorphism `Γ(Y,S) → Γ(X,R)` induced by a morphism of ringed spaces. -/
def ringedGlobalRingHom : S.obj.obj (op (⊤ : Opens Y)) →+* R.obj.obj (op (⊤ : Opens X)) :=
  (φ.hom.app (op ⊤)).hom

/-- The functor comparison at degree zero underlying the abutment in V.3.2,
as an isomorphism of modules over the target's global ring. -/
def ringedModulePushforwardSupportedGlobalIso (Z : Closeds Y) :
    ringedModulePushforward f φ ⋙ moduleGammaZSectionsFunctor S Z ⊤ ≅
      moduleGammaZSectionsFunctor R (Z.preimage f.hom.continuous) ⊤ ⋙
        ModuleCat.restrictScalars (ringedGlobalRingHom f φ) :=
  ringedModulePushforwardSupportedSectionsIso f φ Z ⊤

end SGA.SGA2.ExposeV
