/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.ProperDescentLimit
import SGA.Foundations.Limits.PropertiesLimitProper
import SGA.Foundations.Limits.PropertiesLimitSurjective
import SGA.Foundations.Limits.SpreadingOutGluing
import SGA.Foundations.Limits.SpreadingOutNoetherian

/-!
# SGA 1, Exposé IX, 4.12 over an arbitrary base

IX.4.12: a proper surjective morphism of finite presentation `g : S' ⟶ S` is an effective descent
morphism for étale coverings (`effectiveDescentOfProperStatement`). SGA reduces to a noetherian
base by EGA IV 8. Here: by IX.4.5 (`DescentDatum.isEffective_iff_forall_fromSpecStalk`) it suffices
to treat the base change of `g` to `Spec 𝒪_{S,x}`. The local ring `A = 𝒪_{S,x}` is the filtered
union of its subrings `B` of finite type over `ℤ` (noetherian); the base change of `g` descends to
a morphism `Y_B ⟶ Spec B` of finite presentation (EGA IV 8.8.2 (ii),
`Scheme.exists_isPullback_of_isLimit_of_locallyOfFinitePresentation`), proper and surjective after
enlarging `B` (EGA IV 8.10.5 (vi), (xii): `Scheme.limitDescends_surjective`,
`Scheme.limitDescends_isProper_of_isNoetherian`, the latter by Chow's lemma). Over `Spec A` the
descent datum is then effective by IX.4.12 over a noetherian base
(`DescentDatum.isEffective_of_isPullback_specMap`, in `SGA.SGA1.ExposeIX.ProperDescentLimit`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeIX

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.12 after base change to a local ring (or any ring `A`): let `q : X ⟶ Spec A` be proper,
surjective and of finite presentation. Every descent datum relative to `q` on a finite étale
`X`-scheme is effective. -/
theorem DescentDatum.isEffective_of_isProper_specMap {A : CommRingCat.{u}} {X X' : Scheme.{u}}
    (q : X ⟶ Spec A) [IsProper q] [Surjective q] [LocallyOfFinitePresentation q]
    {a : X' ⟶ X} [IsFinite a] [Etale a] (D : DescentDatum q a) : D.IsEffective etaleCovering := by
  -- `Spec A` is the limit of the `Spec B`, `B ⊆ A` of finite type over `ℤ`
  let E := Algebra.FGSubalgebra.schemeDiagram ℤ A
  let c := Algebra.FGSubalgebra.specCone ℤ A
  have hc : IsLimit c := Algebra.FGSubalgebra.isLimitSpecCone ℤ A
  let q' : X ⟶ c.pt := q
  have : IsProper q' := ‹IsProper q›
  have : Surjective q' := ‹Surjective q›
  have : LocallyOfFinitePresentation q' := ‹LocallyOfFinitePresentation q›
  -- the morphism descends to some `Spec B` (EGA IV 8.8.2 (ii))
  obtain ⟨j, Xj, qj, e, _, _, _, h⟩ :=
    Scheme.exists_isPullback_of_isLimit_of_locallyOfFinitePresentation hc q'
  let M₀ : Scheme.LimitModel c q' j := { obj := Xj, hom := qj, proj := e, isPullback := h }
  -- proper and surjective at some level (EGA IV 8.10.5 (vi), (xii))
  obtain ⟨k₁, g₁, hp⟩ := Scheme.limitDescends_isProper_of_isNoetherian hc M₀.hom M₀.isPullback
  let M₁ := M₀.lower g₁
  have : IsProper M₁.hom := hp
  obtain ⟨k₂, g₂, hs⟩ := Scheme.limitDescends_surjective E c hc M₁.hom M₁.proj q' M₁.isPullback
    inferInstance
  let M₂ := M₁.lower g₂
  have : Surjective M₂.hom := hs
  have : IsProper M₂.hom := MorphismProperty.pullback_snd _ _ ‹IsProper M₁.hom›
  have hsq : IsPullback M₂.proj q M₂.hom
      (Spec.map ((Algebra.FGSubalgebra.cocone ℤ A).ι.app k₂.unop) ≫ 𝟙 _) := by
    rw [Category.comp_id]
    exact M₂.isPullback
  have : IsNoetherianRing (CommRingCat.of k₂.unop.1) := inferInstanceAs (IsNoetherianRing k₂.unop.1)
  exact D.isEffective_of_isPullback_specMap (R := CommRingCat.of k₂.unop.1) M₂.hom (𝟙 _) _ hsq

set_option backward.isDefEq.respectTransparency false in
/-- **IX.4.12**: a proper surjective morphism of finite presentation is an effective descent
morphism for étale coverings, over an arbitrary base. (Over a locally noetherian base this is
`isEffectiveDescentMorphism_of_isProper`; the general case is reduced to it by EGA IV 8, see the
module docstring.) -/
theorem isEffectiveDescentMorphism_of_isProper_of_locallyOfFinitePresentation {S' S : Scheme.{u}}
    (g : S' ⟶ S) [IsProper g] [Surjective g] [LocallyOfFinitePresentation g] :
    IsEffectiveDescentMorphism g etaleCovering := by
  refine ⟨isDescentMorphism_of_isProper, fun X' a D ha ↦ ?_⟩
  have : IsFinite a := ha.1
  have : Etale a := ha.2
  have ha' : etaleFinitePresentation a := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hfp : D.IsEffective etaleFinitePresentation := by
    rw [D.isEffective_iff_forall_fromSpecStalk ha']
    intro x
    have : IsFinite (pullback.snd a (pullback.fst g (S.fromSpecStalk x))) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have : Etale (pullback.snd a (pullback.fst g (S.fromSpecStalk x))) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    exact ((D.baseChange (S.fromSpecStalk x)).isEffective_of_isProper_specMap
      (pullback.snd g (S.fromSpecStalk x))).of_le
        fun _ _ f h ↦ have : IsFinite f := h.1; ⟨⟨h.2, inferInstance⟩, inferInstance⟩
  -- the descended scheme is finite over `S`: proper, since `X' = Y ×_S S'` is, and quasi-finite
  obtain ⟨Y, b, v, hb, hv, hact⟩ := hfp
  have : Etale b := hb.1.1
  have : IsProper b := (isProper_iff_of_isPullback hv.flip).mp inferInstance
  have : LocallyQuasiFinite b := locallyQuasiFinite_of_formallyUnramified b
  exact ⟨Y, b, v, ⟨.of_isProper_of_locallyQuasiFinite b, inferInstance⟩, hv, hact⟩

/-- **IX.4.12** holds: `EffectiveDescentOfProperStatement`. -/
theorem effectiveDescentOfProperStatement : EffectiveDescentOfProperStatement.{u} :=
  fun _ _ g _ _ _ ↦ isEffectiveDescentMorphism_of_isProper_of_locallyOfFinitePresentation g

end SGA.SGA1.ExposeIX
