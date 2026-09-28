/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.Restriction
import SGA.Foundations.Etale.TorsorCech

/-!
# Torsors on the small étale site

For a sheaf of groups `G` on the small étale site of a scheme `Y`:

* torsors restrict along étale morphisms `g : Y' ⟶ Y` (`Scheme.etaleRestrictTorsor`), since
  composition with `g` is continuous and cocontinuous;
* every `G`-torsor is trivialized by an étale covering family indexed by the points of `Y`
  (`Scheme.exists_etale_trivialization`), so that its class is described by a Čech cocycle
  (`CategoryTheory.H1.trivializedByEquiv`).

## References

* [SGA 4, Exposé VII, 1][sga4]
* [J. S. Milne, *Étale cohomology*, III 4][milne1980]
-/

universe u

open CategoryTheory Limits Opposite

-- See the comment in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

/-- The final object `Y` of the small étale site of `Y`. -/
noncomputable def Etale.top (Y : Scheme.{u}) : Y.Etale :=
  Etale.mk (𝟙 Y)

/-- `Y` is the final object of its small étale site. -/
noncomputable def Etale.isTerminalTop (Y : Scheme.{u}) : IsTerminal (Etale.top Y) :=
  IsTerminal.ofUniqueHom (fun W ↦ MorphismProperty.Over.homMk W.hom (Category.comp_id _))
    (fun W f ↦ MorphismProperty.Over.Hom.ext (by
      have := MorphismProperty.Over.w f
      exact (Category.comp_id _).symm.trans this))

variable {Y' Y : Scheme.{u}} {G : Y.Etaleᵒᵖ ⥤ GrpCat.{u}}

/-- The restriction of a torsor on the small étale site of `Y` along an étale morphism
`g : Y' ⟶ Y`. -/
noncomputable abbrev etaleRestrictTorsor (g : Y' ⟶ Y) [Etale g]
    (P : Torsor Y.smallEtaleTopology G) : Torsor Y'.smallEtaleTopology ((Etale.map g).op ⋙ G) :=
  P.restrict Y'.smallEtaleTopology (Etale.map g)

/-- Every torsor on the small étale site of `Y` is trivialized by an étale covering family
indexed by the points of `Y`. -/
theorem exists_etale_trivialization (P : Torsor Y.smallEtaleTopology G) :
    ∃ U : Y → Y.Etale, Y.smallEtaleTopology.CoversTop U ∧
      ∀ y, Nonempty (P.obj.obj (op (U y))) := by
  have h := (mem_smallEtaleTopology_iff _ _).1 (P.nonemptySieve_mem (Etale.top Y))
  choose U f v hf hv using h
  refine ⟨U, (GrothendieckTopology.coversTop_iff_of_isTerminal _ _ (Etale.isTerminalTop Y) U).2
    ((mem_smallEtaleTopology_iff _ _).2 fun y ↦ ⟨U y, f y, v y, ⟨y, ⟨𝟙 _⟩⟩, hv y⟩), hf⟩

/-- Every class in `H¹(Y_et, G)` is trivialized by an étale covering family indexed by the points
of `Y`. -/
theorem H1.exists_etale_isTrivializedBy (c : H1 Y.smallEtaleTopology G) :
    ∃ U : Y → Y.Etale, Y.smallEtaleTopology.CoversTop U ∧ c.IsTrivializedBy U := by
  obtain ⟨P, rfl⟩ := H1.mk_surjective c
  obtain ⟨U, hU, hP⟩ := exists_etale_trivialization P
  exact ⟨U, hU, P, rfl, hP⟩

end AlgebraicGeometry.Scheme
