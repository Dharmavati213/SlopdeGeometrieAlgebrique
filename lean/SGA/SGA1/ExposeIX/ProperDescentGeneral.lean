/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.ProperDescentGeneralModel
import SGA.SGA1.ExposeIX.ProperDescentGeometricFibres

/-!
# SGA 1, Exposé IX, 6.7, 6.8 and 6.11 over an arbitrary base

Let `f : X ⟶ S` be proper, surjective, of finite presentation, with geometrically connected
fibres; `S` is arbitrary.

* `mem_essImage_of_forall_isGeometricallyTrivial_of_locallyOfFinitePresentation` (**IX.6.7**): an
  étale covering of `X` which is geometrically trivial on every fibre `X_s` comes from an étale
  covering of `S`. For every `s`, an action of `X ×_S X ⇉ X` on `Y` exists over `Spec 𝒪_{S,s}`
  (`exists_isActAt_fromSpecStalk_of_locallyOfFinitePresentation`, by a noetherian model over
  `𝒪_{S,s}` and IX.1.10 over the completion of its base, see
  `SGA.SGA1.ExposeIX.ProperDescentGeneralModel`); it spreads out to a neighbourhood of `s`, the
  local actions glue by uniqueness, and IX.4.12 over an arbitrary base concludes.
* `properDescentStatement` (**IX.6.8**): `ProperDescentStatement` holds.
* `ker_autMap_eq_geometricFibres_of_locallyOfFinitePresentation`, `geometricFibresStatement`
  (**IX.6.11**): `GeometricFibresStatement` holds.

Unlike SGA, the proof does not reduce `f` itself to a noetherian base, so it does not need the
constructibility of the geometric connectedness of fibres (EGA IV 9.7.7): only the fibre of the
model over the image of the closed point of `Spec 𝒪_{S,s}` is used, and its geometric
connectedness and the geometric triviality of `Y` on it descend from the fibre `X_s` along a field
extension.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MorphismProperty PreGaloisCategory

namespace SGA.SGA1.ExposeIX

local notation "FEt" => (SGA.SGA1.ExposeV.finiteEtaleHom : MorphismProperty Scheme)
local notation "pb" => MorphismProperty.Over.pullback FEt ⊤

section General

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]
  [GeometricallyConnected f]

/-- IX.6.6–6.7 over `Spec 𝒪_{S,s}`, `S` arbitrary: if `Y` is geometrically trivial on the fibre
`X_s`, it carries an action of `X ×_S X ⇉ X` (a descent datum in the form of IX.4) over
`Spec 𝒪_{S,s}` (`f` proper, of finite presentation, with geometrically connected fibres). -/
theorem exists_isActAt_fromSpecStalk_of_locallyOfFinitePresentation
    (Y : MorphismProperty.Over FEt ⊤ X) (s : S)
    (hY : IsGeometricallyTrivial (f.fiberToSpecResidueField s) ((pb (f.fiberι s)).obj Y)) :
    ∃ e, IsActAt f Y (S.fromSpecStalk s) e := by
  have : IsProper (pullback.snd f (S.fromSpecStalk s)) := inferInstance
  have : LocallyOfFinitePresentation (pullback.snd f (S.fromSpecStalk s)) := inferInstance
  obtain ⟨M⟩ := nonempty_properFEtModel (pullback.snd f (S.fromSpecStalk s))
    ((pb (pullback.fst f (S.fromSpecStalk s))).obj Y)
  exact M.exists_isActAt_fromSpecStalk (M.mem_essImage_compl hY)

variable [Surjective f]

/-- **IX.6.7** over an arbitrary base: let `f : X ⟶ S` be proper, surjective, of finite
presentation, with geometrically connected fibres. An étale covering `Y` of `X` which is
geometrically trivial on every fibre `X_s` comes from an étale covering of `S`. -/
theorem mem_essImage_of_forall_isGeometricallyTrivial_of_locallyOfFinitePresentation
    (Y : MorphismProperty.Over FEt ⊤ X)
    (hY : ∀ s, IsGeometricallyTrivial (f.fiberToSpecResidueField s) ((pb (f.fiberι s)).obj Y)) :
    (pb f).essImage Y := by
  refine mem_essImage_of_forall_exists_localAct_of_locallyOfFinitePresentation f Y fun s ↦ ?_
  obtain ⟨e, he⟩ := exists_isActAt_fromSpecStalk_of_locallyOfFinitePresentation f Y s (hY s)
  exact exists_isLocalAct_of_isActAt_stalk_of_locallyOfFinitePresentation f Y s he

/-- **IX.6.8**, the essential image, over an arbitrary base: for `f : X ⟶ S` proper, surjective, of
finite presentation, with geometrically connected fibres, an étale covering of `X` comes from `S`
iff it is geometrically trivial on every fibre. -/
theorem mem_essImage_iff_forall_isGeometricallyTrivial_of_locallyOfFinitePresentation
    (Y : MorphismProperty.Over FEt ⊤ X) :
    (pb f).essImage Y ↔
      ∀ s, IsGeometricallyTrivial (f.fiberToSpecResidueField s) ((pb (f.fiberι s)).obj Y) :=
  ⟨fun h s ↦ isGeometricallyTrivial_of_mem_essImage f s h,
    mem_essImage_of_forall_isGeometricallyTrivial_of_locallyOfFinitePresentation f Y⟩

end General

/-- **IX.6.8** holds (`ProperDescentStatement`): for `f : X ⟶ S` proper, surjective, of finite
presentation, with geometrically connected fibres, over an arbitrary base `S`, `f` is an effective
descent morphism for étale coverings (IX.4.12,
`isEffectiveDescentMorphism_of_isProper_of_locallyOfFinitePresentation`), `f^*` is fully faithful
on étale coverings, and its essential image consists of the étale coverings of `X` which are
geometrically trivial on every fibre. -/
theorem properDescentStatement : ProperDescentStatement.{u} := fun _ _ f _ _ _ _ ↦
  ⟨isEquivalence_fetComparison_of_isEffectiveDescentMorphism f
      (isEffectiveDescentMorphism_of_isProper_of_locallyOfFinitePresentation f),
    full_pullback_of_isProper_of_geometricallyConnected f, faithful_pullback_of_surjective f,
    mem_essImage_iff_forall_isGeometricallyTrivial_of_locallyOfFinitePresentation f⟩

/-- **IX.6.11** over an arbitrary base: for `f : X ⟶ S` proper, surjective, of finite
presentation, with geometrically connected fibres, the kernel of `π₁(X) → π₁(S)` is the closed
normal subgroup generated by the images of the `π₁(X̄_s) → π₁(X)`, `s ∈ S` (for any classes of
paths `d s`). By `ker_eq_iff_forall_isCompletelyDecomposed` this is IX.6.8 over an arbitrary base
combined with IX.6.2 on the fibres
(`isGeometricallyTrivial_iff_isCompletelyDecomposed_geometricFiber`), as in
`ker_autMap_eq_geometricFibres_of_isLocallyNoetherian`. -/
theorem ker_autMap_eq_geometricFibres_of_locallyOfFinitePresentation {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [Surjective f] [LocallyOfFinitePresentation f]
    [GeometricallyConnected f] (F' : MorphismProperty.Over FEt ⊤ X ⥤ FintypeCat.{u})
    [FiberFunctor F'] [FiberFunctor (pb f ⋙ F')]
    (G : ∀ s, MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{u})
    [∀ s, FiberFunctor (G s)] (d : ∀ s, pb (geometricFiberι f s) ⋙ G s ≅ F') :
    (autMap (pb f) F').ker =
      (Subgroup.normalClosure (⋃ s, Set.range (pathMap F'
        (fun s ↦ pb (geometricFiberι f s)) G d s))).topologicalClosure := by
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F'
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor (pb f ⋙ F')
  have (s : S) := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor (G s)
  refine (ker_eq_iff_forall_isCompletelyDecomposed (pb f) F' (fun s ↦ pb (geometricFiberι f s)) G d
    (surjective_autMap_of_isProper f F')).mpr fun Y ↦ ?_
  simp only [← isGeometricallyTrivial_iff_isCompletelyDecomposed_geometricFiber f]
  exact mem_essImage_iff_forall_isGeometricallyTrivial_of_locallyOfFinitePresentation f Y

/-- **IX.6.11** holds (`GeometricFibresStatement`), over an arbitrary base
(`ker_autMap_eq_geometricFibres_of_locallyOfFinitePresentation`; the connectedness of `X` in the
statement is not used). -/
theorem geometricFibresStatement : GeometricFibresStatement.{u} :=
  fun _ _ f _ _ _ _ _ F' _ _ G _ d ↦
    ker_autMap_eq_geometricFibres_of_locallyOfFinitePresentation f F' G d

end SGA.SGA1.ExposeIX
