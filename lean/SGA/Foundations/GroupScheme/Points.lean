/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.RingHom.Unramified
import SGA.Foundations.CommAlg.PurityStalk

/-!
# Points of a scheme with values in a local ring, and stalk maps

General scheme lemmas used for group schemes (`MulNCotangent`), stated for any scheme.

* `Scheme.specPt x f = Spec.map f ≫ X.fromSpecStalk x : Spec C ⟶ X` for a point `x` and a
  homomorphism `f : 𝒪_{X,x} ⟶ C`. For `C` local and `f` local, every morphism `Spec C ⟶ X` is of
  this form, uniquely (mathlib's `SpecToEquivOfLocalRing`; `Scheme.specPt_stalkClosedPointTo`,
  `Scheme.specPt_injective`).
* `Scheme.Hom.stalkAlgebraMap s x : R ⟶ 𝒪_{X,x}`, the structure map of a stalk of a scheme
  `s : X ⟶ Spec R` over `R`, and `Scheme.specPt_comp_eq_specMap`.
* `Scheme.Hom.formallyUnramified_stalkMap_of_comp_eq`: if `α ≫ f = f ≫ β` with `α`, `β`
  isomorphisms, `f` is unramified at `α y` as soon as it is unramified at `y`.
* `Scheme.Hom.isClosed_singleton_of_isClosed_singleton_apply`: for `f` locally quasi-finite, a
  point is closed as soon as its image is (its closure lies in the discrete fibre).
* `Scheme.Hom.surjective_of_isDominant_comp`: if `X` and `Y` are irreducible, `q : Y ⟶ X` is
  locally quasi-finite and `g : X ⟶ Y` universally closed with `g ≫ q` dominant, then `g` is
  surjective (it maps the generic point to the generic point).
* `eq_comp_pointOfClosedPoint`: over an algebraically closed field `K`, a point `Spec Ω ⟶ X`
  of a `K`-scheme locally of finite type at a closed point `x` factors through the `K`-point
  at `x`.

Reference: EGA I (2nd ed.) 2.4.4 (morphisms from the spectrum of a local ring); EGA II 6.2
(quasi-finite morphisms); Stacks 01TF.
-/

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {C D : CommRingCat.{u}}

/-- The morphism `Spec C ⟶ X` given by a point `x` of `X` and a homomorphism `𝒪_{X,x} ⟶ C`. -/
noncomputable def specPt (x : X) (f : X.presheaf.stalk x ⟶ C) : Spec C ⟶ X :=
  Spec.map f ≫ X.fromSpecStalk x

lemma specMap_comp_specPt (x : X) (f : X.presheaf.stalk x ⟶ C) (φ : C ⟶ D) :
    Spec.map φ ≫ specPt x f = specPt x (f ≫ φ) := by
  rw [specPt, specPt, Spec.map_comp, Category.assoc]

lemma specPt_comp (x : X) (f : X.presheaf.stalk x ⟶ C) (g : X ⟶ Y) :
    specPt x f ≫ g = specPt (g x) (g.stalkMap x ≫ f) := by
  rw [specPt, specPt, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp,
    Category.assoc]

lemma specPt_congr {x y : X} (h : y = x) (f : X.presheaf.stalk y ⟶ C) :
    specPt y f = specPt x (eqToHom (by rw [h]) ≫ f) := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

lemma specPt_closedPoint [IsLocalRing C] (x : X) (f : X.presheaf.stalk x ⟶ C) [IsLocalHom f.hom] :
    specPt x f (closedPoint C) = x := by
  change X.fromSpecStalk x (Spec.map f (closedPoint C)) = x
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- A morphism `Spec C ⟶ X` with `C` local determines the local homomorphism `𝒪_{X,x} ⟶ C`. -/
lemma specPt_injective [IsLocalRing C] {x : X} {f f' : X.presheaf.stalk x ⟶ C} [IsLocalHom f.hom]
    [IsLocalHom f'.hom] (h : specPt x f = specPt x f') : f = f' := by
  have h' := (SpecToEquivOfLocalRing X C).symm.injective
    (a₁ := ⟨x, f, inferInstance⟩) (a₂ := ⟨x, f', inferInstance⟩) h
  rw [Sigma.mk.inj_iff] at h'
  exact congrArg Subtype.val (eq_of_heq h'.2)

lemma specPt_stalkClosedPointTo [IsLocalRing C] (v : Spec C ⟶ X) :
    specPt (v (closedPoint C)) (Scheme.stalkClosedPointTo v) = v :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk v

/-- The structure map `R ⟶ 𝒪_{X,x}` of a stalk of a scheme `s : X ⟶ Spec R` over `R`. -/
noncomputable def Hom.stalkAlgebraMap {R : CommRingCat.{u}} (s : X ⟶ Spec R) (x : X) :
    R ⟶ X.presheaf.stalk x :=
  (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ (s x) trivial ≫ s.stalkMap x

lemma specPt_comp_eq_specMap {R : CommRingCat.{u}} (s : X ⟶ Spec R) (x : X)
    (f : X.presheaf.stalk x ⟶ C) : specPt x f ≫ s = Spec.map (s.stalkAlgebraMap x ≫ f) := by
  rw [specPt_comp, specPt, Spec.fromSpecStalk_eq, ← Spec.map_comp, Hom.stalkAlgebraMap]
  simp only [Category.assoc]

/-- If `α ≫ f = f ≫ β` with `α`, `β` isomorphisms, `f` is unramified at `α y` as soon as it is
unramified at `y`. -/
lemma Hom.formallyUnramified_stalkMap_of_comp_eq {f α β : X ⟶ X} [IsIso α] [IsIso β]
    (h : α ≫ f = f ≫ β) {y : X} (hy : (f.stalkMap y).hom.FormallyUnramified) :
    (f.stalkMap (α y)).hom.FormallyUnramified := by
  have h₁ : ((f ≫ β).stalkMap y).hom.FormallyUnramified := by
    have := (RingHom.FormallyUnramified.respectsIso.cancel_left_isIso (β.stalkMap (f y))
      (f.stalkMap y)).mpr hy
    rw [Scheme.Hom.stalkMap_comp]
    exact this
  rw [← h, Scheme.Hom.stalkMap_comp] at h₁
  exact (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso (f.stalkMap (α y))
    (α.stalkMap y)).mp h₁

/-- For `f` locally quasi-finite, a point whose image is closed is closed: its closure lies in
the fibre, which is discrete. -/
lemma Hom.isClosed_singleton_of_isClosed_singleton_apply (f : X ⟶ Y) [LocallyQuasiFinite f]
    {x : X} (hx : IsClosed {f x}) : IsClosed {x} := by
  have := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  refine isClosed_iff_clusterPt.mpr fun z hz ↦ ?_
  have hxz : x ⤳ z := specializes_iff_mem_closure.mpr (mem_closure_iff_clusterPt.mpr hz)
  have hfz : f z = f x := ((hxz.map f.continuous).mem_closed hx rfl).symm ▸ rfl
  have hs : (⟨x, rfl⟩ : f ⁻¹' {f x}) ⤳ ⟨z, hfz⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp hxz
  exact (congrArg Subtype.val hs.eq).symm

/-- Let `X` and `Y` be irreducible, `q : Y ⟶ X` locally quasi-finite and `g : X ⟶ Y`
universally closed with `g ≫ q` dominant. Then `g` maps the generic point of `X` to that of `Y`
(both lie in the discrete fibre of `q` over the generic point of `X`), so `g` is surjective. -/
lemma Hom.surjective_of_isDominant_comp [IrreducibleSpace X] [IrreducibleSpace Y] (g : X ⟶ Y)
    (q : Y ⟶ X) [LocallyQuasiFinite q] [IsDominant (g ≫ q)] [UniversallyClosed g] :
    Surjective g := by
  have h₁ : q (g (genericPoint X)) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply]
    exact (g ≫ q).genericPoint_eq_of_isDominant
  have h₂ : genericPoint Y ⤳ g (genericPoint X) := genericPoint_specializes _
  have h₃ : q (genericPoint Y) = genericPoint X := by
    have := h₂.map q.continuous
    rw [h₁] at this
    exact (this.antisymm (genericPoint_specializes _)).eq
  have hξ : genericPoint Y = g (genericPoint X) := by
    have := (q.isDiscrete_preimage_singleton (genericPoint X)).to_subtype
    have hs : (⟨_, h₃⟩ : q ⁻¹' {genericPoint X}) ⤳ ⟨_, h₁⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp h₂
    exact congrArg Subtype.val hs.eq
  exact ⟨fun z ↦ (genericPoint_specializes z).mem_closed g.isClosedMap.isClosed_range
    ⟨_, hξ.symm⟩⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Over an algebraically closed field `K`, a point `c : Spec Ω ⟶ X` of a `K`-scheme locally
of finite type at a closed point `x` factors through the `K`-point at `x`: it is
`Spec Ω ⟶ Spec K ⟶ X`. -/
lemma eq_comp_pointOfClosedPoint {K Ω : Type u} [Field K] [IsAlgClosed K] [Field Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {x : X} (hx : IsClosed {x})
    (c : Spec (.of Ω) ⟶ X) (hc : c (closedPoint Ω) = x) :
    c = (c ≫ f) ≫ pointOfClosedPoint f x hx := by
  subst hc
  have key (φ : X.residueField (c (closedPoint Ω)) ⟶ .of Ω) :
      Spec.map φ ≫ X.fromSpecResidueField _ =
        (Spec.map φ ≫ X.fromSpecResidueField _ ≫ f) ≫ pointOfClosedPoint f _ hx := by
    rw [pointOfClosedPoint, ← SpecMap_residueFieldIsoBase_inv f _ hx, Category.assoc,
      ← Spec.map_comp_assoc (residueFieldIsoBase f _ hx).hom, Iso.hom_inv_id, Spec.map_id,
      Category.id_comp]
  have hy := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X c
  calc c = _ := hy.symm
    _ = _ := key _
    _ = (c ≫ f) ≫ pointOfClosedPoint f _ hx := by rw [← Category.assoc, hy]

end AlgebraicGeometry
