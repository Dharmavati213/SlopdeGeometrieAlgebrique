/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FiniteType
import SGA.Foundations.Limits.SpreadingOut

/-!
# Noetherian approximation of rings and of affine schemes

An `R`-algebra `A` is the filtered colimit of its finitely generated `R`-subalgebras; if `R` is
noetherian, they are noetherian rings. For `R = ℤ` this is the absolute noetherian approximation of
the affine scheme `Spec A` (the affine case of Thomason–Trobaugh C.9, Stacks 01ZA): `Spec A` is the
limit of the cofiltered diagram of the noetherian affine schemes `Spec B`, `B ⊆ A` of finite type
over `ℤ`, with affine transition maps.

* `Algebra.FGSubalgebra R A`: the finitely generated `R`-subalgebras of `A`, a directed order.
* `Algebra.FGSubalgebra.diagram R A`, `Algebra.FGSubalgebra.cocone R A`,
  `Algebra.FGSubalgebra.isColimitCocone R A`: the diagram `B ↦ B` and its colimit `A`.
* `Algebra.FGSubalgebra.schemeDiagram R A`, `Algebra.FGSubalgebra.isLimitSpecCone R A`: the
  diagram `B ↦ Spec B` of affine schemes and its limit `Spec A`; instances: the members are
  affine, noetherian when `R` is, and the transition maps are affine.
* `AlgebraicGeometry.Scheme.noetherianApproximation_of_isAffine`: the conclusion of
  `Scheme.NoetherianApproximationStatement` (Stacks 01ZA) for affine schemes. The statement for
  non-affine quasi-compact and quasi-separated schemes is not proved.

The same diagram is built inside SGA 1 files (`SGA.SGA1.ExposeIX.FGSubalg` in
`SGA.SGA1.ExposeIX.ProperDescentLimit`, `SGA.SGA1.ExposeX.FGSubalgebra` in
`SGA.SGA1.ExposeX.BaseChangeAlgClosed`), which Foundations cannot import; those are to become
aliases of the definitions here.

## References

* [EGA IV₃, 8.2.2, 8.2.3][EGA4]
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [R. W. Thomason, T. Trobaugh, *Higher algebraic K-theory of schemes and of derived categories*,
  Appendix C][TT90]
-/

universe u v

open CategoryTheory Limits AlgebraicGeometry

namespace Algebra

variable (R : Type v) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

/-- The finitely generated `R`-subalgebras of `A`, ordered by inclusion. -/
abbrev FGSubalgebra : Type u := {B : Subalgebra R A // B.FG}

namespace FGSubalgebra

instance : IsDirectedOrder (FGSubalgebra R A) where
  directed B C := ⟨⟨B.1 ⊔ C.1, B.2.sup C.2⟩, (le_sup_left : B.1 ≤ B.1 ⊔ C.1),
    (le_sup_right : C.1 ≤ B.1 ⊔ C.1)⟩

instance : Nonempty (FGSubalgebra R A) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

/-- The diagram `B ↦ B` of the finitely generated `R`-subalgebras of `A`. -/
@[simps]
noncomputable abbrev diagram : FGSubalgebra R A ⥤ CommRingCat.{u} where
  obj B := CommRingCat.of B.1
  map f := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom

/-- The cocone of the inclusions `B ⟶ A`. -/
@[simps]
noncomputable abbrev cocone : Cocone (diagram R A) where
  pt := CommRingCat.of A
  ι := { app B := CommRingCat.ofHom B.1.val.toRingHom }

/-- An `R`-algebra is the filtered colimit of its finitely generated subalgebras. -/
noncomputable def isColimitCocone : IsColimit (cocone R A) := by
  have : ReflectsColimit (diagram R A) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{u})
    (Types.FilteredColimit.isColimitOf _ _ (fun (x : A) ↦ ?_)
    fun (i j : FGSubalgebra R A) xi xj hij ↦ ?_)
  · classical
    exact ⟨⟨Algebra.adjoin R {x}, ⟨{x}, by simp⟩⟩, ⟨x, Algebra.subset_adjoin rfl⟩, rfl⟩
  · obtain ⟨m, him, hjm⟩ := exists_ge_ge i j
    exact ⟨m, homOfLE him, homOfLE hjm, Subtype.ext hij⟩

/-- A finitely generated algebra over a noetherian ring is noetherian (Hilbert's basis theorem). -/
instance [IsNoetherianRing R] (B : FGSubalgebra R A) : IsNoetherianRing B.1 :=
  have : Algebra.FiniteType R B.1 := (Subalgebra.fg_iff_finiteType B.1).mp B.2
  Algebra.FiniteType.isNoetherianRing R B.1

/-- The diagram `B ↦ Spec B` of affine schemes. -/
noncomputable abbrev schemeDiagram : (FGSubalgebra R A)ᵒᵖ ⥤ Scheme.{u} :=
  (diagram R A).op ⋙ Scheme.Spec

/-- The cone of the morphisms `Spec A ⟶ Spec B`. -/
noncomputable abbrev specCone : Cone (schemeDiagram R A) :=
  Scheme.Spec.mapCone (cocone R A).op

/-- `Spec A` is the limit of the `Spec B`, `B ⊆ A` finitely generated over `R` (for `R = ℤ`:
absolute noetherian approximation of an affine scheme). -/
noncomputable def isLimitSpecCone : IsLimit (specCone R A) :=
  isLimitOfPreserves Scheme.Spec (isColimitCocone R A).op

instance (B : (FGSubalgebra R A)ᵒᵖ) : IsAffine ((schemeDiagram R A).obj B) :=
  inferInstanceAs (IsAffine (Spec _))

instance [IsNoetherianRing R] (B : (FGSubalgebra R A)ᵒᵖ) :
    IsNoetherian ((schemeDiagram R A).obj B) :=
  inferInstanceAs (IsNoetherian (Spec (CommRingCat.of B.unop.1)))

instance {B C : (FGSubalgebra R A)ᵒᵖ} (f : B ⟶ C) : IsAffineHom ((schemeDiagram R A).map f) :=
  isAffineHom_of_isAffine _

end FGSubalgebra

end Algebra

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Absolute noetherian approximation for affine schemes (the affine case of Stacks 01ZA and of
`Scheme.NoetherianApproximationStatement`): an affine scheme `X` is the limit of the cofiltered
diagram, with affine transition maps, of the affine schemes `Spec B` of finite type over `ℤ`,
`B ⊆ Γ(X, ⊤)` finitely generated. -/
theorem Scheme.noetherianApproximation_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I) (E : I ⥤ Scheme.{u})
      (c : Cone E), Nonempty (IsLimit c) ∧ Nonempty (c.pt ≅ X) ∧
        (∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)) ∧ ∀ i, CompactSpace (E.obj i) ∧
          ∃ g : E.obj i ⟶ Spec (.of (ULift.{u} ℤ)), LocallyOfFiniteType g := by
  let A := Γ(X, ⊤)
  refine ⟨(Algebra.FGSubalgebra ℤ A)ᵒᵖ, inferInstance, inferInstance,
    Algebra.FGSubalgebra.schemeDiagram ℤ A, Algebra.FGSubalgebra.specCone ℤ A,
    ⟨Algebra.FGSubalgebra.isLimitSpecCone ℤ A⟩, ⟨X.isoSpec.symm⟩, fun _ ↦ inferInstance,
    fun B ↦ ⟨inferInstance, ?_⟩⟩
  -- `Spec B ⟶ Spec ℤ` is of finite type
  let φ : CommRingCat.of (ULift.{u} ℤ) ⟶ CommRingCat.of B.unop.1 :=
    CommRingCat.ofHom ((Int.castRingHom B.unop.1).comp ULift.ringEquiv.toRingHom)
  refine ⟨Spec.map φ, HasRingHomProperty.Spec_iff.mpr ?_⟩
  have : Algebra.FiniteType ℤ B.unop.1 := (Subalgebra.fg_iff_finiteType B.unop.1).mp B.unop.2
  have h₁ : (Int.castRingHom B.unop.1).FiniteType := by
    rw [show Int.castRingHom B.unop.1 = algebraMap ℤ B.unop.1 from rfl]
    exact RingHom.finiteType_algebraMap.mpr this
  exact h₁.comp (RingHom.FiniteType.of_surjective _ ULift.ringEquiv.surjective)

end AlgebraicGeometry
