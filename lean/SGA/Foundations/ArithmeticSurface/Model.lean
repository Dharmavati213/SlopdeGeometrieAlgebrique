/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Models of curves over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K` and residue field `k`. A *model* of a
`K`-scheme `C` is a flat `R`-scheme of finite type `X` with an isomorphism `X_K ≅ C` (Stacks,
Section 0C2R); it is *regular* if `X` is a regular scheme, *proper* if `X → Spec R` is.

* `AlgebraicGeometry.closedFibre g = X ×_R Spec k` for `g : X ⟶ Spec R`, as in
  `SGA.SGA1.ExposeXIII.SemistableReductionStatement`, with its structure morphism
  `AlgebraicGeometry.closedFibreHom g : X_k ⟶ Spec k`;
* `AlgebraicGeometry.IsRegularProperModel g f`: `X` (with `g : X ⟶ Spec R`) is a regular proper
  model of `C` (with `f : C ⟶ Spec K`): `g` is proper and flat, every local ring of `X` is a
  regular local ring, and the generic fibre `X ×_R K` is isomorphic to `C` over `K`.
* `AlgebraicGeometry.isNoetherian_closedFibre`, `finite_irreducibleComponents_closedFibre`: for `g`
  proper (and `R` noetherian) the closed fibre is noetherian, so it has finitely many irreducible
  components.

## References

* [Stacks Project, Section 0C2R (Models)](https://stacks.math.columbia.edu/tag/0C2R)
* [Q. Liu, *Algebraic Geometry and Arithmetic Curves*, 10.1]
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (g : X ⟶ Spec (.of R))

/-- The closed fibre `X_k = X ×_{Spec R} Spec k` of a scheme `X` over a local ring `R` with residue
field `k`. -/
noncomputable abbrev closedFibre : Scheme.{u} :=
  pullback g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))

/-- The structure morphism `X_k ⟶ Spec k` of the closed fibre. -/
noncomputable abbrev closedFibreHom : closedFibre g ⟶ Spec (.of (IsLocalRing.ResidueField R)) :=
  pullback.snd _ _

/-- The closed fibre of a proper scheme over a noetherian local ring is noetherian. -/
lemma isNoetherian_closedFibre [IsNoetherianRing R] [IsProper g] :
    IsNoetherian (closedFibre g) := by
  have : IsLocallyNoetherian (closedFibre g) :=
    LocallyOfFiniteType.isLocallyNoetherian (closedFibreHom g)
  exact ⟨⟩

/-- The closed fibre of a proper scheme over a noetherian local ring has finitely many irreducible
components. -/
lemma finite_irreducibleComponents_closedFibre [IsNoetherianRing R] [IsProper g] :
    Finite (irreducibleComponents (closedFibre g)) := by
  have := isNoetherian_closedFibre g
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype

variable {K : Type u} [Field K] [Algebra R K] {C : Scheme.{u}} (f : C ⟶ Spec (.of K))

/-- `X` (over `Spec R`) is a *regular proper model* of `C` (over `Spec K`, `K` the fraction field
of `R`): `X → Spec R` is proper and flat, every local ring of `X` is regular, and the generic
fibre `X ×_R K` is isomorphic to `C` over `K` (Stacks, Section 0C2R). -/
def IsRegularProperModel : Prop :=
  IsProper g ∧ Flat g ∧ (∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) ∧
    ∃ e : pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅ C,
      e.hom ≫ f = pullback.snd _ _

end AlgebraicGeometry
