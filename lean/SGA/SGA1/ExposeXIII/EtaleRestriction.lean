/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.Restriction
import SGA.SGA1.ExposeXIII.EtaleBaseChange

/-!
# SGA 1, Exposé XIII, §1: étale base change

For an étale morphism `g : Y' ⟶ Y`, the inverse image `g^*` of étale sheaves is the restriction
(`Scheme.etalePullbackIsoRestrict`), and the base change morphism of a cartesian square along
`g` is an isomorphism (`Scheme.isIso_etaleBaseChangeMap_of_etale`, in
`SGA.Foundations.Etale.Restriction`). This is the (trivial) étale case of the base change
theorems of SGA 4 VIII; it is used in XIII 1.5 c) (cohomological properness is local on `Y`
for the étale topology).
-/
