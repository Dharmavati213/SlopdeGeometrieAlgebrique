/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.FiniteModuleComparison
import SGA.SGA2.ExposeV.TopLocalCohomologyExactness
import SGA.SGA2.ExposeV.LocalDualityTargetExactness

/-!
# V.2.1: canonical local duality in top degree for all finite modules

The actual canonical map
`Hⁿ_m(M) → Hom_R(Ext⁰_R(M,R), Hⁿ_m(R))`
is an isomorphism for every finite module over a regular local ring of
dimension `n`. The proof uses the rank-one case, additivity, the genuine
finite-presentation argument, and proved right exactness of both original
functors. Lower degrees require the boundary comparison and are not
asserted here.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing Functor
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The finite-presentation criterion applied to the original canonical
map, with its injectivity and upper-vanishing hypotheses explicit. -/
theorem localDualityMap_top_finite_isIso [IsNoetherianRing R]
    (J : Ideal R) (n : ℕ)
    [Injective ((_root_.localCohomology J n).obj (ModuleCat.of R R))]
    (hzero : ∀ M : ModuleCat.{u} R,
      IsZero ((_root_.localCohomology J (n + 1)).obj M))
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsIso (localDualityMap J M (ModuleCat.of R R) n 0 n (add_zero n)) := by
  let F := _root_.localCohomology J n
  let G := localDualityTargetFunctor J (ModuleCat.of R R) 0 n
  let α := localDualityNatTrans J (ModuleCat.of R R) n 0 n (add_zero n)
  have : PreservesFiniteColimits F :=
    localCohomology_preservesFiniteColimits_of_vanishing J n hzero
  have : PreservesFiniteColimits G :=
    localDualityTarget_preservesFiniteColimits J (ModuleCat.of R R) n
  have : IsIso (α.app (ModuleCat.of R R)) := localDualityMap_ring_top_isIso R J n
  exact isIso_app_finite α
    (fun S hS => hS.exact.map_of_epi_of_preservesCokernel G hS.epi_g inferInstance) M

/-- **V.2.1, top degree, every finite module.** The unchanged canonical
local-duality map is an isomorphism in the actual Krull dimension. -/
theorem regularLocal_localDualityMap_top_isIso [IsRegularLocalRing R]
    (n : ℕ) (hdim : ringKrullDim R = n) (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsIso (localDualityMap (maximalIdeal R) M (ModuleCat.of R R)
      n 0 n (add_zero n)) := by
  have := regularLocal_localCohomology_injective n hdim
  exact localDualityMap_top_finite_isIso (maximalIdeal R) n
    (fun N => regularLocal_localCohomology_isZero_of_gt n hdim N (n + 1) (by omega)) M

/-- The actual top-degree canonical natural transformation is a natural
isomorphism on the original category of finite modules. -/
def regularLocal_localDualityTopNatIso [IsRegularLocalRing R]
    (n : ℕ) (hdim : ringKrullDim R = n) :
    forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙
        _root_.localCohomology (maximalIdeal R) n ≅
      forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙
        localDualityTargetFunctor (maximalIdeal R) (ModuleCat.of R R) 0 n := by
  let α := whiskerLeft (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))
    (localDualityNatTrans (maximalIdeal R) (ModuleCat.of R R) n 0 n (add_zero n))
  have (M : FGModuleCat.{u} R) : IsIso (α.app M) :=
    regularLocal_localDualityMap_top_isIso n hdim M.obj
  exact NatIso.ofComponents (fun M => asIso (α.app M)) (fun f => α.naturality f)

/-- The forward components are literally the original canonical maps. -/
@[simp]
theorem regularLocal_localDualityTopNatIso_hom_app [IsRegularLocalRing R]
    (n : ℕ) (hdim : ringKrullDim R = n) (M : FGModuleCat.{u} R) :
    (regularLocal_localDualityTopNatIso n hdim).hom.app M =
      localDualityMap (maximalIdeal R) M.obj (ModuleCat.of R R)
        n 0 n (add_zero n) := rfl

end SGA.SGA2.ExposeV
