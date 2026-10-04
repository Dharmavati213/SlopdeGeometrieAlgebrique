/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Topos.Sheaf
import SGA.Foundations.Etale.Functoriality

/-!
# Monomorphisms of étale sheaves are regular

Every monomorphism of sheaves of sets on the small étale site of a scheme `X` is regular, i.e.
the equalizer of two morphisms (`AlgebraicGeometry.Scheme.isRegularMonoCategory_sheaf`). The
category of étale sheaves of sets on `X` is equivalent to the category of sheaves on the
essentially small site of affine étale `X`-schemes, which is a topos (it has a subobject
classifier, `CategoryTheory.Sheaf.instHasSubobjectClassifierTypeOfEssentiallySmall`), hence a
regular mono category.

This is used to show that cohomological properness in dimension `≤ 0` passes to subsheaves
(SGA 1 XIII 1.13 1) applied to `F ⟶ G ⇉ G ⊔_F G`).

We also record the dual of mathlib's `isIso_app_coconePt_of_preservesColimit`: a natural
transformation between two functors preserving a limit, which is an isomorphism on the diagram,
is an isomorphism at the limit (`CategoryTheory.isIso_app_conePt_of_preservesLimit`). It shows
that cohomological properness in dimension `≤ 0` is stable under finite limits.

## References

* [SGA 4, Exposé IV, 1.2][sga4]
-/

universe u

open CategoryTheory Limits

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

/-- Regular monomorphisms can be transported back along an equivalence. -/
noncomputable def RegularMono.ofEquivalence (e : C ≌ D) {X Y : C} {f : X ⟶ Y}
    (h : RegularMono (e.functor.map f)) : RegularMono f :=
  RegularMono.ofArrowIso (Arrow.isoMk (e.unitIso.app X).symm (e.unitIso.app Y).symm (by
      simp only [Arrow.mk_left, Arrow.mk_right, Functor.id_obj, Functor.comp_obj, Arrow.mk_hom]
      exact (e.unitIso.inv.naturality f).symm))
    { Z := e.inverse.obj h.Z
      left := e.inverse.map h.left
      right := e.inverse.map h.right
      w := by rw [← e.inverse.map_comp, h.w, e.inverse.map_comp]
      isLimit := isLimitForkMapOfIsLimit e.inverse h.w h.isLimit }

/-- A natural transformation `α : L ⟶ L'` between functors preserving the limit of `K`, which is
an isomorphism at every object of the diagram, is an isomorphism at the limit (dual of
`isIso_app_coconePt_of_preservesColimit`). (The same statement is
`SGA.SGA2.ExposeIV.isIso_app_conePt_of_preservesLimit`, which should become an alias of this
one.) -/
lemma isIso_app_conePt_of_preservesLimit {J : Type*} [Category* J] (K : J ⥤ C) {L L' : C ⥤ D}
    (α : L ⟶ L') [IsIso (Functor.whiskerLeft K α)] (c : Cone K) (hc : IsLimit c)
    [PreservesLimit K L] [PreservesLimit K L'] :
    IsIso (α.app c.pt) := by
  let e := IsLimit.conePointsIsoOfNatIso
    (isLimitOfPreserves L hc) (isLimitOfPreserves L' hc) (asIso (Functor.whiskerLeft K α))
  have he : e.hom = α.app c.pt :=
    (isLimitOfPreserves L' hc).hom_ext fun j ↦
      (IsLimit.conePointsIsoOfNatIso_hom_comp _ _ _ j).trans (α.naturality (c.π.app j))
  rw [← he]
  infer_instance

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every monomorphism of étale sheaves of sets is regular (the category of sheaves of sets on
the small étale site is equivalent to a Grothendieck topos on an essentially small site). -/
instance isRegularMonoCategory_sheaf (X : Scheme.{u}) :
    IsRegularMonoCategory (Sheaf X.smallEtaleTopology (Type u)) where
  regularMonoOfMono {F G} m _ := by
    let E := (AffineEtale.Spec X).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology X) X.smallEtaleTopology
    have : Mono (E.map m) := inferInstance
    exact ⟨⟨RegularMono.ofEquivalence E.asEquivalence (regularMonoOfMono (E.map m))⟩⟩

end AlgebraicGeometry.Scheme
