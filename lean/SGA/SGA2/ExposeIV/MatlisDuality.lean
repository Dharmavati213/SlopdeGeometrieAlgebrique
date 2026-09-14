/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.MatlisCompletedHomComparison
import SGA.SGA2.ExposeIV.MatlisCompleteCompletion

/-!
# IV.5.1: Matlis duality over a noetherian local ring

The source and target are the literal original categories `CA` and `DA`.
The forward functor is original-ring Hom itself. The inverse is completed-ring
Hom, interpreted through the proved actual completion and restriction
equivalences, which preserve underlying additive groups up to their original
canonical maps. No completeness hypothesis on the base ring is imposed.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (H : ModuleCat.{u} R) (hH : SupportedDualizingModule H)

/-- The actual completion transports first give an equivalence of the
original categories with the completed-Hom model for its forward functor. -/
def matlisTransportedAntiEquivalence :
    (MatlisArtinianModuleCat R)ᵒᵖ ≌ MatlisCompleteModuleCat R :=
  (matlisCompletedRingAntiEquivalence H hH).trans
    (matlisCompleteFiniteCompletionEquivalence (R := R)).symm

/-- The proved original Hom comparison lifts to the literal full category
`DA`, retaining the actual pointwise linear comparison. -/
def matlisTransportedHomIso :
    (matlisTransportedAntiEquivalence H hH).functor ≅ matlisHomToComplete H hH :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _ ((matlisCompletedRingHomIso H hH).app X))
    (fun f => by
      apply ObjectProperty.hom_ext
      exact (matlisCompletedRingHomIso H hH).hom.naturality f)

/-- **SGA 2, IV.5.1.** Actual original-ring Hom is an equivalence from the
opposite locally Artinian finite-socle category to the original complete
finite-power-quotient category. Its inverse is actual completed-ring Hom
through the canonical completion/restriction comparisons. -/
def matlisAntiEquivalence : (MatlisArtinianModuleCat R)ᵒᵖ ≌ MatlisCompleteModuleCat R :=
  (matlisTransportedAntiEquivalence H hH).changeFunctor (matlisTransportedHomIso H hH)

instance : (matlisHomToComplete H hH).Additive where
  map_add {X Y f g} := by
    apply ObjectProperty.hom_ext
    exact (moduleHomDual H).map_add (f := f.unop.hom.op) (g := g.unop.hom.op)

instance : (matlisHomToComplete H hH).Linear R where
  map_smul f r := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact g.hom.map_smul r (f.unop.hom.hom x)

/-- The forward functor is exactly the original Hom functor, not merely
isomorphic to it after forgetting the property. -/
@[simp] theorem matlisAntiEquivalence_functor :
    (matlisAntiEquivalence H hH).functor = matlisHomToComplete H hH := rfl

/-- The inverse is the specified actual completion, completed-ring Hom,
and restriction of scalars; changing the forward comparison leaves it unchanged. -/
@[simp] theorem matlisAntiEquivalence_inverse :
    (matlisAntiEquivalence H hH).inverse =
      (matlisCompleteFiniteCompletionEquivalence (R := R)).functor ⋙
        (matlisCompletedRingAntiEquivalence H hH).inverse := rfl

/-- The original linear Hom values and original precomposition maps are
unchanged by the final categorical packaging. -/
theorem matlisAntiEquivalence_functor_forget :
    (matlisAntiEquivalence H hH).functor ⋙ (matlisCompleteModuleProperty R).ι =
      (matlisArtinianModuleProperty R).ι.op ⋙ moduleHomDual H := rfl

end SGA.SGA2.ExposeIV
