/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Fields.GeometricallyReducedScheme
import SGA.SGA1.ExposeX.CoveringOfBase
import SGA.SGA1.ExposeX.ProperOverField

/-!
# SGA 1, Exposé X, 1.7: the fundamental group of a product

X.1.7: for `X` proper and connected and `Y` locally noetherian and connected over an algebraically
closed field `k`, `π₁(X ×ₖ Y) → π₁(X) × π₁(Y)` is an isomorphism. SGA applies X.1.4 to the second
projection `Z = X ×ₖ Y ⟶ Y`, whose geometric fibre at a rational point is `X`. We follow this for a
rational base point and `X` reduced (SGA reduces to this case by replacing `X` by `X_red`):

* `Γ(X, 𝒪_X) = k` for `X` proper, connected and reduced over `k` (`isIso_app_of_isProper`, in
  `ProperOverField`), hence `𝒪_Y = pr₂_* 𝒪_Z` by flat base change (`isIso_app_snd`);
* X.1.7 itself, from X.1.2 through X.1.4
  (`bijective_map_prod_of_steinFactorizationEtaleStatement`), with the group theory in
  `bijective_prod_of_bijective_comp`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeX

section Group

variable {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]

/-- X.1.7 (group-theoretic part). Let `i : A → B`, `p : B → C`, `q : B → D` with
`A → B → C → 1` exact and `q ∘ i` bijective. Then `(q, p) : B → D × C` is bijective. -/
theorem bijective_prod_of_bijective_comp (i : A →* B) (p : B →* C) (q : B →* D)
    (hqi : Function.Bijective (q.comp i)) (hex : i.range = p.ker) (hp : Function.Surjective p) :
    Function.Bijective (q.prod p) := by
  let φ := MulEquiv.ofBijective (q.comp i) hqi
  have h := bijective_prod_of_retraction i p (φ.symm.toMonoidHom.comp q)
    (MonoidHom.ext fun a ↦ φ.symm_apply_apply a) hex hp
  have e : q.prod p = (φ.toMonoidHom.prodMap (MonoidHom.id C)).comp
      ((φ.symm.toMonoidHom.comp q).prod p) := by
    ext b
    · exact (φ.apply_symm_apply (q b)).symm
    · rfl
  rw [e, MonoidHom.coe_comp, MonoidHom.coe_prodMap]
  exact (φ.bijective.prodMap Function.bijective_id).comp h

end Group

section GlobalSections

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (s : X ⟶ Spec (.of k))
  (t : Y ⟶ Spec (.of k))

/-- For `X` proper, connected and reduced over `k` algebraically closed, the second projection
`pr₂ : X ×ₖ Y ⟶ Y` has `𝒪_Y = pr₂_* 𝒪_{X ×ₖ Y}` (flat base change of `k = Γ(X, 𝒪_X)`). -/
theorem isIso_app_snd [IsProper s] [IsReduced X] [ConnectedSpace X] (V : Y.Opens) :
    IsIso ((pullback.snd s t).app V) :=
  CohomologyAux.isIso_app_pullback_snd s t (isIso_app_of_isProper s) V

end GlobalSections

section Product

/-- A morphism `t : Spec k ⟶ Spec K` of spectra of fields with a retraction is an
isomorphism. -/
lemma isIso_of_comp_eq_id {k K : Type u} [Field k] [Field K] {t : Spec (.of k) ⟶ Spec (.of K)}
    {g : Spec (.of K) ⟶ Spec (.of k)} (h : t ≫ g = 𝟙 _) : IsIso t := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective t
  obtain ⟨γ, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj] at h
  have hsurj : Function.Surjective ψ := fun x ↦ ⟨γ x, congrArg (fun φ ↦ φ.hom x) h⟩
  have : IsIso ψ := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨ψ.hom.injective, hsurj⟩
  infer_instance

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sY : Y ⟶ Spec (.of k))

/-- **X.1.7** (for a rational base point and `X` reduced; from X.1.2). Let `k` be algebraically
closed, `X` proper, connected and reduced over `k`, `Y` locally noetherian and connected over `k`,
and `c` a rational point of `X ×ₖ Y`. Then `π₁(X ×ₖ Y, c) → π₁(X, c) × π₁(Y, c)` is an
isomorphism.

As in SGA: X.1.4 applies to `pr₂ : X ×ₖ Y ⟶ Y` (proper, separable as `X` is geometrically reduced,
and `𝒪_Y = pr₂_* 𝒪`); the geometric fibre at `pr₂(c)` maps isomorphically to `X`, so
`π₁(X̄) → π₁(X ×ₖ Y) → π₁(X)` is bijective, and the group theory concludes. -/
theorem bijective_map_prod_of_steinFactorizationEtaleStatement
    (hStein : SteinFactorizationEtaleStatement.{u}) [IsProper sX] [IsReduced X] [ConnectedSpace X]
    [IsLocallyNoetherian Y] [ConnectedSpace Y] (c : Spec (.of k) ⟶ pullback sX sY)
    (hc : c ≫ pullback.snd sX sY ≫ sY = 𝟙 _) :
    Function.Bijective ((ExposeV.etaleFundamentalGroup.map k (pullback.fst sX sY) c).prod
      (ExposeV.etaleFundamentalGroup.map k (pullback.snd sX sY) c)) := by
  have : IsSeparable sX :=
    (isSeparable_iff_of_field sX).mpr (GeometricallyReduced.of_perfectField sX)
  let f := pullback.snd sX sY
  let b := c ≫ f
  let y := b (IsLocalRing.closedPoint k)
  let φ := Y.descResidueField (Scheme.stalkClosedPointTo b)
  have hb : Spec.map φ ≫ Y.fromSpecResidueField y = b :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k Y b
  let _ : Algebra (Y.residueField y) k := φ.hom.toAlgebra
  let ψ := IsAlgClosed.lift (R := Y.residueField y) (S := AlgebraicClosure (Y.residueField y))
    (M := k)
  let t : Spec (.of k) ⟶ Spec (.of (AlgebraicClosure (Y.residueField y))) :=
    Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have ht : t ≫ geometricPoint Y y = b := by
    rw [geometricPoint, ← Category.assoc, ← Spec.map_comp, ← hb]
    congr 2
    ext x
    exact ψ.commutes x
  let a : Spec (.of k) ⟶ pullback f (geometricPoint Y y) := pullback.lift c t ht.symm
  obtain ⟨hex, hsurj⟩ := homotopyExactSequence hStein f (isIso_app_snd sX sY) y k a
  -- the geometric fibre `X̄ = X ×ₖ Y ×_Y Spec κ(y)ᵃˡᵍ` maps isomorphically to `X`
  have hiso : IsIso (pullback.fst f (geometricPoint Y y) ≫ pullback.fst sX sY) := by
    have hsq := (IsPullback.of_hasPullback f (geometricPoint Y y)).paste_horiz
      (IsPullback.of_hasPullback sX sY)
    have htg : t ≫ geometricPoint Y y ≫ sY = 𝟙 _ := by
      rw [← Category.assoc, ht, Category.assoc, hc]
    have : IsIso t := isIso_of_comp_eq_id htg
    have : IsIso (t ≫ geometricPoint Y y ≫ sY) := by rw [htg]; infer_instance
    have : IsIso (geometricPoint Y y ≫ sY) := IsIso.of_isIso_comp_left t _
    exact hsq.isIso_fst_of_isIso
  have hbij : Function.Bijective
      ((ExposeV.etaleFundamentalGroup.map k (pullback.fst sX sY)
        (a ≫ pullback.fst f (geometricPoint Y y))).comp
        (ExposeV.etaleFundamentalGroup.map k (pullback.fst f (geometricPoint Y y)) a)) := by
    have : (ExposeV.FEt.pullback (pullback.fst sX sY) ⋙
        ExposeV.FEt.pullback (pullback.fst f (geometricPoint Y y))).IsEquivalence :=
      Functor.isEquivalence_of_iso
        (MorphismProperty.Over.pullbackComp (pullback.fst f (geometricPoint Y y))
          (pullback.fst sX sY))
    rw [ExposeV.etaleFundamentalGroup.map, ExposeV.etaleFundamentalGroup.map,
      ExposeV.autMap_comp]
    exact ExposeV.autMap_bijective _ _
  have key := bijective_prod_of_bijective_comp _ _ _ hbij hex hsurj
  rwa [pullback.lift_fst] at key

end Product

end SGA.SGA1.ExposeX
