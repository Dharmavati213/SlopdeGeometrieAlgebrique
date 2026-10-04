/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Limits.EtaleSectionsGluing
import SGA.Foundations.Etale.LocalAcyclicityStrictLocalization

/-!
# Sections over a limit as sections along a morphism

The restriction `F(E k) ⟶ Γ(c.pt, p^* F)` of SGA 4 VII 5.7 in degree `0`
(`AlgebraicGeometry.Scheme.toLimitSections`, `SGA.Foundations.Limits.EtaleSectionsGluing`) is the
section of `p^* F` along the projection `c.pt ⟶ E k`
(`AlgebraicGeometry.Scheme.sectionAlong`, in
`SGA.Foundations.Etale.LocalAcyclicityStrictLocalization`).
This connects the limit theorem with the base change criteria stated with `sectionAlong`,
`etaleSectionsRestrict` and `etaleSquareRestrict`.

## References

* [SGA 4, Exposé VII, 5.7][sga4]
-/

universe u

open CategoryTheory Limits Opposite

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (Type u))
  {I : Type u} [Category.{u} I] {E : I ⥤ Scheme.{u}} (t : E ⟶ (Functor.const I).obj X)
  [∀ k, Etale (t.app k)] {c : Cone E} {p : c.pt ⟶ X} (hp : ∀ k, c.π.app k ≫ t.app k = p)

/-- The restriction of a section of `F` over `E k` to the limit `c.pt` is its section along the
projection `c.pt ⟶ E k`. -/
lemma toLimitSections_eq_sectionAlong (k : I) (s : F.obj.obj (op (Etale.mk (t.app k)))) :
    toLimitSections F t hp k s = sectionAlong F p (Etale.mk (t.app k)) (c.π.app k) (hp k) s :=
  rfl

/-- **Sections over a cofiltered limit, surjectivity** (SGA 4 VII 5.7 in degree `0`), in terms of
`sectionAlong`: every section of `p^* F` over the limit `c.pt` is the section along some
projection `c.pt ⟶ E k` of a section of `F` over `E k`. -/
theorem exists_sectionAlong_eq [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]
    [∀ k, CompactSpace (E.obj k)] [∀ k, QuasiSeparatedSpace (E.obj k)] (hc : IsLimit c)
    (σ : ((etalePullback p).obj F).obj.obj (op (Etale.top c.pt))) :
    ∃ (k : I) (s : F.obj.obj (op (Etale.mk (t.app k)))),
      sectionAlong F p (Etale.mk (t.app k)) (c.π.app k) (hp k) s = σ :=
  exists_toLimitSections_eq F hp hc σ

end AlgebraicGeometry.Scheme
