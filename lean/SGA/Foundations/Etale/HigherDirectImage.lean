/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Sites.LeftExact
import SGA.Foundations.Etale.Functoriality
import SGA.Foundations.Etale.TorsorPresheaf

/-!
# The first higher direct image of a sheaf of groups

Let `F : D ⥤ C` be a functor between sites and `G` a sheaf of groups on `C`. The first higher
direct image `R¹F_* G` is the sheaf associated with the presheaf `V ↦ H¹(C/F(V), G)` on `D`
(`H1.higherDirectImagePresheaf`, `H1.higherDirectImage`). For a morphism of schemes
`f : X ⟶ Y` and the base change functor `Scheme.Etale.pullback f : Y.Etale ⥤ X.Etale`, this is
`R¹f_* G`, the sheaf associated with `V ↦ H¹(X ×_Y V, G)` (`Scheme.etaleR1Pushforward`).

The values are isomorphism classes of torsors, which live in the universe above that of the
sections of `G`; accordingly `R¹f_* G` is a sheaf of sets in `Type (u + 1)`.

## References

* [SGA 4, Exposé V, 5.1][sga4]
* [J. Giraud, *Cohomologie non abélienne*, V 2.1][giraud1971]
-/

universe w v' u' v u

open CategoryTheory Opposite Limits

namespace CategoryTheory.H1

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (G : Cᵒᵖ ⥤ GrpCat.{w})
  {D : Type u'} [Category.{v'} D] (K : GrothendieckTopology D) (F : D ⥤ C)

/-- The presheaf `V ↦ H¹(C/F(V), G)` on `D`. -/
noncomputable abbrev higherDirectImagePresheaf : Dᵒᵖ ⥤ Type _ :=
  F.op ⋙ presheaf J G

/-- The first higher direct image `R¹F_* G`: the sheaf associated with
`V ↦ H¹(C/F(V), G)`. -/
noncomputable def higherDirectImage
    [HasWeakSheafify K (Type (max u v (w + 1)))] :
    Sheaf K (Type (max u v (w + 1))) :=
  (presheafToSheaf K _).obj (higherDirectImagePresheaf J G F)

variable {J G}

/-- Every section of the presheaf `V ↦ H¹(C/F(V), G)` is locally trivial when `F` is the
identity; in general, the sections of `R¹F_* G` come from classes of torsors over the `F(V)`. -/
lemma higherDirectImagePresheaf_id_locallyTrivial
    (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat)) {U : C}
    (c : (higherDirectImagePresheaf J G (𝟭 C)).obj (op U)) :
    ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
      (higherDirectImagePresheaf J G (𝟭 C)).map f.op c = presheafTrivialClass hG V :=
  exists_covering_map_eq_trivialClass hG c

end CategoryTheory.H1

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (G : X.Etaleᵒᵖ ⥤ GrpCat.{u})

/-- The presheaf `V ↦ H¹(X ×_Y V, G)` on the small étale site of `Y`, where `X ×_Y V` is
seen as the object `(Etale.pullback f).obj V` of the small étale site of `X`. -/
noncomputable abbrev etaleR1PushforwardPresheaf : Y.Etaleᵒᵖ ⥤ Type (u + 1) :=
  H1.higherDirectImagePresheaf X.smallEtaleTopology G (Etale.pullback f)

/-- The first higher direct image `R¹f_* G` of a sheaf of groups `G` on the small étale site of
`X`: the sheaf on the small étale site of `Y` associated with `V ↦ H¹(X ×_Y V, G)`. -/
noncomputable def etaleR1Pushforward : Sheaf Y.smallEtaleTopology (Type (u + 1)) :=
  (presheafToSheaf Y.smallEtaleTopology (Type (u + 1))).obj (etaleR1PushforwardPresheaf f G)

/-- The distinguished section of `R¹f_* G` over `V`, the class of the trivial torsor. -/
noncomputable def etaleR1PushforwardPresheafTrivial
    (hG : Presieve.IsSheaf X.smallEtaleTopology (G ⋙ CategoryTheory.forget GrpCat)) (V : Y.Etale) :
    (etaleR1PushforwardPresheaf f G).obj (op V) :=
  H1.presheafTrivialClass hG ((Etale.pullback f).obj V)

lemma etaleR1PushforwardPresheaf_map_trivial
    (hG : Presieve.IsSheaf X.smallEtaleTopology (G ⋙ CategoryTheory.forget GrpCat))
    {V W : Y.Etale} (φ : W ⟶ V) :
    (etaleR1PushforwardPresheaf f G).map φ.op (etaleR1PushforwardPresheafTrivial f G hG V) =
      etaleR1PushforwardPresheafTrivial f G hG W :=
  H1.presheaf_map_trivialClass hG ((Etale.pullback f).map φ)

end AlgebraicGeometry.Scheme
