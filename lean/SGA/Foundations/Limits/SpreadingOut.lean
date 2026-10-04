/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Spreading out schemes of finite presentation: statements

The interface statements of EGA IV 8 (limit methods) for schemes, used by several streams of the
SGA 1 formalization (registry row A4 of `notes/topics/out-of-scope-plan.md`).

* `AlgebraicGeometry.Scheme.SpreadingOutStatement` (EGA IV 8.8.2 (ii), Stacks 01ZM): over the
  limit of a cofiltered diagram of quasi-compact and quasi-separated schemes with affine
  transition maps, every scheme of finite presentation is the base change of a scheme of finite
  presentation over some member of the diagram.
* `AlgebraicGeometry.Scheme.SpreadingOutSubfieldStatement`: the special case of a field, the
  union of its finitely generated subfields: a scheme of finite type and quasi-separated over a
  field `K` is defined over a finitely generated subfield of `K`.
* `AlgebraicGeometry.Scheme.NoetherianApproximationStatement` (absolute noetherian approximation,
  Thomason–Trobaugh C.9, Stacks 01ZA): every quasi-compact and quasi-separated scheme is the limit
  of a cofiltered diagram of schemes of finite type over `ℤ` with affine transition maps.

The first two statements are proved: `Scheme.spreadingOutStatement` in
`SGA.Foundations.Limits.SpreadingOutGluing`, `Scheme.spreadingOutSubfieldStatement` (and the
variant over a countable algebraically closed subfield,
`Scheme.exists_isPullback_of_isAlgClosed_countable`) in
`SGA.Foundations.Limits.SpreadingOutSubfield`.
`Scheme.NoetherianApproximationStatement` is proved only for affine schemes
(`Scheme.noetherianApproximation_of_isAffine`, `SGA.Foundations.Limits.SpreadingOutNoetherian`).

The parts of EGA IV 8.8.2 about morphisms are proved, in
`SGA.Foundations.Limits.FiniteEtale`: `Scheme.exists_hom_of_isPullback` (8.8.2 (i), existence),
`Scheme.exists_map_comp_eq_of_isPullback` (uniqueness) and `Scheme.exists_iso_of_isPullback`
(isomorphisms), from mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`.
Properties of morphisms (EGA IV 8.10.5) are in `SGA.Foundations.Limits.PropertiesLimit` and the
files `SGA.Foundations.Limits.PropertiesLimit*`.

## References

* [EGA IV₃, 8.8.2, 8.10.5][EGA4]
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- EGA IV 8.8.2 (ii) (Stacks 01ZM), statement: let `c.pt = lim E i` be the limit of a cofiltered
diagram `E : I ⥤ Scheme` (`I : Type u`, morphisms in `Type u`) of quasi-compact and
quasi-separated schemes with affine transition maps. Every `c.pt`-scheme `X` of finite
presentation (`q : X ⟶ c.pt` locally of finite presentation, quasi-compact and quasi-separated) is
the base change `X ≅ X_j ×_{E j} c.pt` of an `E j`-scheme `X_j` of finite presentation, for some
`j`. -/
def Scheme.SpreadingOutStatement : Prop :=
  ∀ ⦃I : Type u⦄ [Category.{u} I] [IsCofiltered I] (E : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, CompactSpace (E.obj i)]
    [∀ i, QuasiSeparatedSpace (E.obj i)] (c : Cone E) (_ : IsLimit c) ⦃X : Scheme.{u}⦄
    (q : X ⟶ c.pt) [LocallyOfFinitePresentation q] [QuasiCompact q] [QuasiSeparated q],
    ∃ (j : I) (Xj : Scheme.{u}) (qj : Xj ⟶ E.obj j) (e : X ⟶ Xj),
      LocallyOfFinitePresentation qj ∧ QuasiCompact qj ∧ QuasiSeparated qj ∧
        IsPullback e q qj (c.π.app j)

/-- EGA IV 8.8.2 (ii) over a field, statement: let `K` be a field and `X` a `K`-scheme of finite
type and quasi-separated (equivalently, of finite presentation). There are a finitely generated
subfield `K₀ = ℤ(s) ⊆ K` (`s` a finite subset of `K`) and a `K₀`-scheme `X₀` of finite type and
quasi-separated with `X ≅ X₀ ×_{K₀} K`. -/
def Scheme.SpreadingOutSubfieldStatement : Prop :=
  ∀ (K : Type u) [Field K] ⦃X : Scheme.{u}⦄ (q : X ⟶ Spec (.of K)) [LocallyOfFiniteType q]
    [QuasiCompact q] [QuasiSeparated q],
    ∃ (s : Finset K) (X₀ : Scheme.{u}) (q₀ : X₀ ⟶ Spec (.of (Subfield.closure (s : Set K))))
      (e : X ⟶ X₀), LocallyOfFiniteType q₀ ∧ QuasiCompact q₀ ∧ QuasiSeparated q₀ ∧
        IsPullback e q q₀ (Spec.map (CommRingCat.ofHom (Subfield.closure (s : Set K)).subtype))

/-- Absolute noetherian approximation (Thomason–Trobaugh C.9, Stacks 01ZA), statement: every
quasi-compact and quasi-separated scheme `X` is the limit of a cofiltered diagram
`E : I ⥤ Scheme` (`I : Type u`) with affine transition maps of schemes of finite type over `ℤ`
(the morphism to `Spec ℤ` is locally of finite type and `E i` is quasi-compact); in particular
every `E i` is noetherian. -/
def Scheme.NoetherianApproximationStatement : Prop :=
  ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X],
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I) (E : I ⥤ Scheme.{u}) (c : Cone E),
      Nonempty (IsLimit c) ∧ Nonempty (c.pt ≅ X) ∧ (∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)) ∧
        ∀ i, CompactSpace (E.obj i) ∧
          ∃ g : E.obj i ⟶ Spec (.of (ULift.{u} ℤ)), LocallyOfFiniteType g

end AlgebraicGeometry
