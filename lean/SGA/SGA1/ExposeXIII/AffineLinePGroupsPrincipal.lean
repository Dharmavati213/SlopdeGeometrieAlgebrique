/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.FundamentalGroupCohomology
import SGA.SGA1.ExposeV.GaloisEquivalence
import SGA.SGA1.ExposeV.FiniteEtaleGalois

/-!
# XIII.2.13: principal coverings under base change and change of geometric point

V.6 (functoriality of `π₁`) for the homomorphisms `π → G` attached to pointed principal coverings
(V.5.11, XI.5). Let `H : C ⥤ D` be a functor between categories with fibre functors `F' : C ⥤ Fin`
and `F : D ⥤ Fin`, and `e : H ⋙ F ≅ F'`. Then `H` carries a principal object `P` of `C` under a
group `G` to a principal object of `D` (`ExposeXI.PrincipalObject.mapFunctor`), and the homomorphism
attached to the image of the point `x` is the composite of the one attached to `x` with
`autMap H e : Aut F → Aut F'` (`ExposeXI.PrincipalObject.hom_mapFunctor`). Two special cases are
used for XIII.2.13:

* `H` the base change `A ↦ S ⊗_R A` of finite étale algebras along `R → S`, with
  `e = FiniteEtale.fiberIsoBaseChangeFiber`; then `autMap H e` is the homomorphism
  `π₁(Spec S, a) → π₁(Spec R, a)` (`AffineLinePGroups.fundamentalGroupMap`, which generalizes
  `SGA.SGA1.ExposeV.genericPointMap` from fields to all `R`-algebras);
* `H` the identity and `e` an isomorphism of fibre functors (a class of paths, V.7); then
  `autMap H e` is the change of base point.

For a commutative group `G` the homomorphism attached to a principal object does not depend on the
point (`ExposeXI.PrincipalObject.hom_eq_hom_of_commute`), and an equivariant isomorphism between
`H(P)` and a principal object `Q` of `D` identifies the homomorphism of `Q` with that of `P`
composed with `autMap H e` (`ExposeXI.PrincipalObject.hom_eq_of_isIso_mapFunctor`).
-/

universe u w

open CategoryTheory PreGaloisCategory

namespace SGA.SGA1.ExposeXI.PrincipalObject

section Functor

variable {C D : Type*} [Category C] [Category D] {F : D ⥤ FintypeCat.{w}}
  {F' : C ⥤ FintypeCat.{w}} {G : Type w} [Group G] (H : C ⥤ D) (e : H ⋙ F ≅ F')

omit [Group G] in
private lemma inv_app_hom_app_apply (X : C) (x : F.obj (H.obj X)) :
    e.inv.app X (e.hom.app X x) = x := by
  rw [← FintypeCat.comp_apply, ← NatTrans.comp_app, e.hom_inv_id, NatTrans.id_app,
    FintypeCat.id_apply]

omit [Group G] in
private lemma hom_app_inv_app_apply (X : C) (x : F'.obj X) :
    e.hom.app X (e.inv.app X x) = x := by
  rw [← FintypeCat.comp_apply, ← NatTrans.comp_app, e.inv_hom_id, NatTrans.id_app,
    FintypeCat.id_apply]

omit [Group G] in
private lemma inv_app_naturality_apply {X Y : C} (f : X ⟶ Y) (x : F'.obj X) :
    e.inv.app Y (F'.map f x) = F.map (H.map f) (e.inv.app X x) :=
  NatTrans.naturality_apply e.inv f x

/-- The image of a principal object `P` of `C` under a functor `H : C ⥤ D` compatible with the
fibre functors (`e : H ⋙ F ≅ F'`): the object `H(P)` with the action `H(α)`. -/
@[simps X]
noncomputable def mapFunctor (P : PrincipalObject F' G) : PrincipalObject F G where
  X := H.obj P.X
  α := (H.mapAut P.X).op.comp P.α
  isPrincipalHomogeneous x y := by
    have key (g : G) (z : F.obj (H.obj P.X)) :
        F.map (((H.mapAut P.X).op.comp P.α) g).unop.hom z =
          e.inv.app P.X (P.act g (e.hom.app P.X z)) := by
      rw [inv_app_naturality_apply, inv_app_hom_app_apply]
      rfl
    obtain ⟨g, hg, hu⟩ := P.isPrincipalHomogeneous (e.hom.app P.X x) (e.hom.app P.X y)
    refine ⟨g, ?_, fun g' hg' ↦ hu g' ?_⟩
    · beta_reduce
      rw [key]
      change e.inv.app P.X (F'.map (P.α g).unop.hom _) = y
      rw [hg, inv_app_hom_app_apply]
    · beta_reduce at hg' ⊢
      rw [key] at hg'
      change F'.map (P.α g').unop.hom _ = _
      rw [← hg', hom_app_inv_app_apply]
  nonempty := ⟨e.inv.app P.X P.nonempty.some⟩

lemma mapFunctor_act (P : PrincipalObject F' G) (g : G) (x : F'.obj P.X) :
    (P.mapFunctor H e).act g (e.inv.app P.X x) = e.inv.app P.X (P.act g x) := by
  change F.map (H.map (P.α g).unop.hom) _ = _
  rw [inv_app_naturality_apply]

/-- V.6, V.5.11: the homomorphism `π → G` attached to the point `e⁻¹(x)` of `H(P)` is the
homomorphism attached to `x`, composed with `autMap H e : Aut F → Aut F'`. -/
theorem hom_mapFunctor (P : PrincipalObject F' G) (x : F'.obj P.X) (σ : Aut F) :
    (P.mapFunctor H e).hom (e.inv.app P.X x) σ = P.hom x (ExposeV.autMap H e σ) := by
  refine ((P.mapFunctor H e).hom_eq_iff (e.inv.app P.X x) σ _).mpr ?_
  rw [mapFunctor_act, hom_spec]
  change e.inv.app P.X ((ExposeV.autMap H e σ).hom.app P.X x) = σ.hom.app (H.obj P.X) _
  rw [ExposeV.autMap_hom_app, FintypeCat.comp_apply, FintypeCat.comp_apply,
    inv_app_hom_app_apply]

end Functor

section Morphism

variable {C : Type*} [Category C] {F : C ⥤ FintypeCat.{w}} {G : Type w} [Group G]

/-- XI.5: an equivariant morphism of principal objects (it is automatically an isomorphism, but
this is not needed) preserves the homomorphism `π → G` of corresponding points. This is
`ExposeXI.PrincipalObject.torsorHom_map` for morphisms. -/
lemma hom_map_of_equivariant (P Q : PrincipalObject F G) (f : P.X ⟶ Q.X)
    (hf : ∀ g, (P.α g).unop.hom ≫ f = f ≫ (Q.α g).unop.hom) (x : F.obj P.X) :
    Q.hom (F.map f x) = P.hom x := by
  ext σ
  rw [hom_eq_iff, mulAction_naturality, ← hom_spec P x σ]
  change F.map (Q.α _).unop.hom (F.map f x) = F.map f (F.map (P.α _).unop.hom x)
  rw [← FintypeCat.comp_apply, ← F.map_comp, ← hf, F.map_comp, FintypeCat.comp_apply]

end Morphism

section Commutative

variable {C : Type*} [Category C] {F : C ⥤ FintypeCat.{w}} {G : Type w} [Group G]

/-- For a commutative group `G`, the homomorphism `π → G` attached to a principal object does not
depend on the point. -/
lemma hom_eq_hom_of_commute (hc : ∀ a b : G, a * b = b * a) (P : PrincipalObject F G)
    (x y : F.obj P.X) : P.hom x = P.hom y := by
  obtain ⟨g, rfl⟩ := (P.isPrincipalHomogeneous.bijective x).2 y
  ext σ
  change P.hom x σ = P.hom (P.act g x) σ
  rw [torsorHom_act, hc g⁻¹, inv_mul_cancel_right]

omit [Group G] in
/-- For a commutative group `G`: if `Q` is isomorphic to the image `H(P)` of a principal object
`P` of `C`, the homomorphism attached to `Q` is the one attached to `P`, composed with
`autMap H e`. -/
lemma hom_eq_of_isIso_mapFunctor {C' : Type*} [Category C'] {F' : C' ⥤ FintypeCat.{w}}
    [Group G] (hc : ∀ a b : G, a * b = b * a) (H : C' ⥤ C) (e : H ⋙ F ≅ F')
    (P : PrincipalObject F' G) (Q : PrincipalObject F G) (h : (P.mapFunctor H e).IsIso Q)
    (x : F'.obj P.X) (y : F.obj Q.X) (σ : Aut F) :
    Q.hom y σ = P.hom x (ExposeV.autMap H e σ) := by
  obtain ⟨φ, hφ⟩ := h
  have h1 := P.hom_mapFunctor H e x σ
  have h2 := (P.mapFunctor H e).torsorHom_map Q φ hφ (e.inv.app P.X x)
  rw [Q.hom_eq_hom_of_commute hc y (F.map φ.hom (e.inv.app P.X x))]
  exact (congrArg (fun f : Aut F →* G ↦ f σ) h2).trans h1

end Commutative

end SGA.SGA1.ExposeXI.PrincipalObject

namespace SGA.SGA1.ExposeXIII.AffineLinePGroups

open CommAlgCat

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (Ω : Type u) [Field Ω]
  [Algebra S Ω] [Algebra R Ω] [IsScalarTower R S Ω]

/-- V.6: the homomorphism `π₁(Spec S, a) → π₁(Spec R, a)` induced by an `R`-algebra `S`, for a
geometric point `a : S → Ω`: base change `A ↦ S ⊗_R A` of finite étale algebras, with the
identification of the fibres `Hom_S(S ⊗_R A, Ω) = Hom_R(A, Ω)`
(`FiniteEtale.fiberIsoBaseChangeFiber`). For a field `S` this is
`SGA.SGA1.ExposeV.genericPointMap`. -/
noncomputable def fundamentalGroupMap :
    Aut (ExposeV.fiberFunctor S Ω) →* Aut (ExposeV.fiberFunctor R Ω) :=
  ExposeV.autMap (FiniteEtale.baseChange.{u} R S).op
    (FiniteEtale.fiberIsoBaseChangeFiber.{u} R Ω S).symm

lemma continuous_fundamentalGroupMap : Continuous (fundamentalGroupMap R S Ω) :=
  ExposeV.continuous_autMap _ _

/-- `fundamentalGroupMap` as a continuous homomorphism. -/
noncomputable def fundamentalGroupContinuousMap :
    ContinuousMonoidHom (Aut (ExposeV.fiberFunctor S Ω)) (Aut (ExposeV.fiberFunctor R Ω)) :=
  ⟨fundamentalGroupMap R S Ω, continuous_fundamentalGroupMap R S Ω⟩

/-- V.6, V.5.11: base change of a pointed principal covering along `R → S` composes its
homomorphism `π₁(Spec R) → G` with `π₁(Spec S) → π₁(Spec R)`. -/
theorem hom_mapFunctor_baseChange {G : Type u} [Group G]
    (P : ExposeXI.PrincipalObject (ExposeV.fiberFunctor R Ω) G)
    (x : (ExposeV.fiberFunctor R Ω).obj P.X) (σ : Aut (ExposeV.fiberFunctor S Ω)) :
    (P.mapFunctor (FiniteEtale.baseChange.{u} R S).op
        (FiniteEtale.fiberIsoBaseChangeFiber.{u} R Ω S).symm).hom
      ((FiniteEtale.fiberIsoBaseChangeFiber.{u} R Ω S).hom.app P.X x) σ =
      P.hom x (fundamentalGroupMap R S Ω σ) :=
  P.hom_mapFunctor _ _ x σ

end SGA.SGA1.ExposeXIII.AffineLinePGroups

namespace SGA.SGA1.ExposeXIII.AffineLinePGroups

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (Ω : Type u) [Field Ω]
  [Algebra S Ω] [Algebra R Ω] (h : algebraMap R Ω = (algebraMap S Ω).comp f)

/-- V.6: `fundamentalGroupMap` for a ring homomorphism `f : R → S` (instead of an `R`-algebra
structure on `S`) and a geometric point `S → Ω`, where `Ω` is an `R`-algebra through `f`
(hypothesis `h`). -/
noncomputable def fundamentalGroupMapOfRingHom :
    Aut (ExposeV.fiberFunctor S Ω) →* Aut (ExposeV.fiberFunctor R Ω) :=
  letI := f.toAlgebra
  haveI : IsScalarTower R S Ω := IsScalarTower.of_algebraMap_eq' h
  fundamentalGroupMap R S Ω

lemma continuous_fundamentalGroupMapOfRingHom :
    Continuous (fundamentalGroupMapOfRingHom f Ω h) :=
  letI := f.toAlgebra
  haveI : IsScalarTower R S Ω := IsScalarTower.of_algebraMap_eq' h
  continuous_fundamentalGroupMap R S Ω

end SGA.SGA1.ExposeXIII.AffineLinePGroups
