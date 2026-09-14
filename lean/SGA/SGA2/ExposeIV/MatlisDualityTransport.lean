/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.MatlisDuality

/-!
# IV.5.1: the two natural completion-transport squares

Transporting either original Matlis functor through the actual `CA` and
`DA` completion equivalences recovers completed-ring Hom. The comparisons
are natural isomorphisms in the full original categories, not merely
objectwise identifications after forgetting to abelian groups.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

private def cancelInverseFunctor {C D E : Type*} [Category C] [Category D] [Category E]
    (K : C ⥤ E) (e : D ≌ E) : (K ⋙ e.inverse) ⋙ e.functor ≅ K :=
  Functor.associator K e.inverse e.functor ≪≫
    Functor.isoWhiskerLeft K e.counitIso ≪≫ Functor.rightUnitor K

private def transportFunctorComparison {C D E : Type*}
    [Category C] [Category D] [Category E]
    (F : C ⥤ D) (K : C ⥤ E) (e : D ≌ E) (h : K ⋙ e.inverse ≅ F) :
    F ⋙ e.functor ≅ K :=
  Functor.isoWhiskerRight h.symm e.functor ≪≫ cancelInverseFunctor K e

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (H : ModuleCat.{u} R) (hH : SupportedDualizingModule H)

/-- **IV.5.1, forward transport.** Complete the actual original Hom value,
or complete the `CA` source and then take actual completed-ring Hom: these
are naturally isomorphic as objects of the literal completed `DA` category. -/
def matlisDualityForwardCompletionIso :
    matlisHomToComplete H hH ⋙ (matlisCompleteCompletionEquivalence (R := R)).functor ≅
      (matlisArtinianCompletionEquivalence (R := R)).functor.op ⋙
        matlisHomToComplete (matlisCompletedCoefficient H) hH.completion :=
  transportFunctorComparison (matlisHomToComplete H hH)
    ((matlisArtinianCompletionEquivalence (R := R)).functor.op ⋙
      matlisHomToComplete (matlisCompletedCoefficient H) hH.completion)
    (matlisCompleteCompletionEquivalence (R := R)) (matlisTransportedHomIso H hH)

/-- **IV.5.1, inverse transport.** Complete the original inverse-Hom value,
or complete the `DA` source and apply the actual complete-base inverse Hom:
these are naturally isomorphic in the opposite completed `CA` category. -/
def matlisDualityInverseCompletionIso :
    (matlisAntiEquivalence H hH).inverse ⋙
        (matlisArtinianCompletionEquivalence (R := R)).functor.op ≅
      (matlisCompleteCompletionEquivalence (R := R)).functor ⋙
        (matlisCompleteCategoryAntiEquivalence
          (matlisCompletedCoefficient H) hH.completion).inverse :=
  cancelInverseFunctor
    ((matlisCompleteCompletionEquivalence (R := R)).functor ⋙
      (matlisCompleteCategoryAntiEquivalence
        (matlisCompletedCoefficient H) hH.completion).inverse)
    (matlisArtinianCompletionEquivalence (R := R)).op

end SGA.SGA2.ExposeIV
