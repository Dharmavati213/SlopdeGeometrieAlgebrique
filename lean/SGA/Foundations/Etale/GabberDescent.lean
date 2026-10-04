/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.LocalAcyclicityBaseChange

/-!
# Descent of sections along a surjective morphism

For a surjective morphism `π : X' ⟶ X` and an étale sheaf of sets `F` on `X`, the unit
`F ⟶ π_* π^* F` is injective on sections (`Scheme.injective_map_etaleAdjunction_unit`, from
`SGA.Foundations.Etale.LocalAcyclicityBaseChange`). Hence a section of `π^* F` over `X' ×_X U`
which is étale-locally on `U` the image of sections of `F` comes from a unique section of `F`
over `U` (`AlgebraicGeometry.Scheme.exists_etaleAdjunction_unit_eq_of_surjective`). This is the
form of the descent of sections along finite surjective morphisms (Stacks 09Z3 in degree `0`)
used in Gabber's proof of the proper base change theorem: there the local condition is checked
near the closed fibre of a proper scheme over a henselian local ring, and propagated by
properness.

The underlying statement is general: a section of a sheaf which is locally in the image of a
morphism of sheaves injective on sections lies in its image
(`CategoryTheory.exists_app_eq_of_injective`).

## References

* [Stacks Project, Tag 09Z3](https://stacks.math.columbia.edu/tag/09Z3)
* [Stacks Project, Tag 09ZF](https://stacks.math.columbia.edu/tag/09ZF)
-/

universe v u

open CategoryTheory Limits Opposite

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A section of a sheaf of types `G` which is `J`-locally in the image of a morphism `u : F ⟶ G`
injective on sections (its `Presheaf.imageSieve` is a covering sieve) is in the image of `u`. -/
theorem exists_app_eq_of_injective {F G : Sheaf J (Type v)} (u : F ⟶ G)
    (hu : ∀ V : C, Function.Injective (u.hom.app (op V))) {U : C} (s : G.obj.obj (op U))
    (hs : Presheaf.imageSieve u.hom s ∈ J U) :
    ∃ f : F.obj.obj (op U), u.hom.app (op U) f = s := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  have hG := (isSheaf_iff_isSheaf_of_type _ _).1 G.property
  let S : Sieve U := Presheaf.imageSieve u.hom s
  let x : Presieve.FamilyOfElements F.obj S.arrows := fun _ _ hg ↦ hg.choose
  have hx {V : C} (g : V ⟶ U) (hg : S.arrows g) : u.hom.app (op V) (x g hg) = G.obj.map g.op s :=
    hg.choose_spec
  have hcomp : x.Compatible := by
    intro Y₁ Y₂ W g₁ g₂ f₁ f₂ h₁ h₂ e
    apply hu
    rw [NatTrans.naturality_apply u.hom g₁.op, NatTrans.naturality_apply u.hom g₂.op, hx, hx,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, e]
  obtain ⟨f, hf, -⟩ := hF S hs x hcomp
  refine ⟨f, (hG S hs).isSeparatedFor.ext fun V g hg ↦ ?_⟩
  rw [← NatTrans.naturality_apply u.hom g.op f, hf g hg, hx g hg]

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- **Descent of sections along a surjective morphism**: for `π : X' ⟶ X` surjective and an étale
sheaf `F` on `X`, a section of `π^* F` over `X' ×_X U` which is, near every point of `U`, the image
of a section of `F` over an étale neighbourhood, is the image of a section of `F` over `U`. -/
theorem exists_etaleAdjunction_unit_eq_of_surjective {X X' : Scheme.{u}} (π : X' ⟶ X)
    [Surjective π] (F : Sheaf X.smallEtaleTopology (Type u)) {U : X.Etale}
    (s : ((etalePullback π).obj F).obj.obj (op ((Etale.pullback π).obj U)))
    (hs : ∀ x : U.left, ∃ (V : X.Etale) (g : V ⟶ U) (v : V.left) (f : F.obj.obj (op V)),
      g.left v = x ∧ ((etaleAdjunction π).unit.app F).hom.app (op V) f =
        ((etalePullback π).obj F).obj.map ((Etale.pullback π).map g).op s) :
    ∃ f : F.obj.obj (op U), ((etaleAdjunction π).unit.app F).hom.app (op U) f = s := by
  refine exists_app_eq_of_injective ((etaleAdjunction π).unit.app F) (fun V a b hab ↦ ?_) s ?_
  · have := injective_map_etaleAdjunction_unit (K := F) (𝟙 ((Etale.pullback π).obj V))
    exact this (by simpa using hab)
  · rw [mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨V, g, v, f, hv, hf⟩ := hs x
    exact ⟨V, g, v, ⟨f, hf⟩, hv⟩

end AlgebraicGeometry.Scheme
