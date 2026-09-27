/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeI.Infinitesimal
import SGA.SGA1.ExposeI.Unibranch
import SGA.SGA1.ExposeIX.NilImmersion
import SGA.SGA1.ExposeIX.TopologicalInvariance

/-!
# SGA 1, Exposé I: invariance of the étale site (I.8.3 and the statement of I.11)

* I.8.3 (`etaleBaseChange_isEquivalence`): base change along a closed immersion `S₀ ⟶ S` with
  the same underlying space is an equivalence from étale `S`-schemes to étale `S₀`-schemes. Full
  faithfulness is I.5.5 (`etaleBaseChange_full_and_faithful`); essential surjectivity glues the
  local lifts of I.8.1, which is done in Exposé IX (IX.1.7,
  `SGA.SGA1.ExposeIX.essSurj_pullback_etale_of_isClosedImmersion`).
* I.11 (`etale_baseChange_isEquivalence_of_universalHomeomorph`): the same holds along a finite,
  radicial, surjective morphism (IX.4.10,
  `SGA.SGA1.ExposeIX.isEquivalence_pullback_etale_of_isFinite`).

This file imports Exposé IX, so it must not be imported by the files of Exposé I that Exposé IX
depends on.
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry CategoryTheory

/-- I.8.3, essential surjectivity: along a closed immersion `S₀ ⟶ S` with the same underlying
space, every étale `S₀`-scheme is `X ×_S S₀` for an étale `S`-scheme `X` (IX.1.7). -/
theorem etaleBaseChange_essSurj {S S₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i]
    [Surjective i] : (etaleBaseChange i).EssSurj :=
  ExposeIX.essSurj_pullback_etale_of_isClosedImmersion i

/-- I.8.3: base change along a closed immersion `S₀ ⟶ S` with the same underlying space is an
equivalence from étale `S`-schemes to étale `S₀`-schemes (full faithfulness is I.5.5). -/
theorem etaleBaseChange_isEquivalence {S S₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i]
    [Surjective i] : (etaleBaseChange i).IsEquivalence where
  faithful := (etaleBaseChange_full_and_faithful i).2
  full := (etaleBaseChange_full_and_faithful i).1
  essSurj := etaleBaseChange_essSurj i

set_option backward.isDefEq.respectTransparency.types false in
/-- I.11 and IX.4.10: base change along a finite, radicial, surjective morphism `Y' ⟶ Y` (a
universal homeomorphism) is an equivalence from étale `Y`-schemes to étale `Y'`-schemes. We
assume `Y' ⟶ Y` of finite presentation, which holds under the exposé's standing locally
noetherian hypothesis (`etale_baseChange_isEquivalence_of_universalHomeomorph'`). -/
theorem etale_baseChange_isEquivalence_of_universalHomeomorph {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsFinite g] [UniversallyInjective g] [Surjective g] [LocallyOfFinitePresentation g] :
    (MorphismProperty.Over.pullback @Etale ⊤ g : Y.Etale ⥤ Y'.Etale).IsEquivalence :=
  ExposeIX.isEquivalence_pullback_etale_of_isFinite g

set_option backward.isDefEq.respectTransparency.types false in
/-- I.11 and IX.4.10 over a locally noetherian base (the exposé's standing hypothesis): base
change along a finite, radicial, surjective morphism `Y' ⟶ Y` is an equivalence on étale
schemes. -/
theorem etale_baseChange_isEquivalence_of_universalHomeomorph' {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsLocallyNoetherian Y] [IsFinite g] [UniversallyInjective g] [Surjective g] :
    (MorphismProperty.Over.pullback @Etale ⊤ g : Y.Etale ⥤ Y'.Etale).IsEquivalence :=
  etale_baseChange_isEquivalence_of_universalHomeomorph g

end SGA.SGA1.ExposeI
