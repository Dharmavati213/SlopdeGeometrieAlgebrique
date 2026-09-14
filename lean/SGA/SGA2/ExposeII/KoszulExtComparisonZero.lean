/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.KoszulExtComparison
import SGA.SGA2.ExposeII.KoszulCohomologyZero

/-!
# SGA 2, Exposé II, (7.5)–(7.6): the comparison in degree zero

The actual map from quotient Ext to Koszul cohomology is an isomorphism in
degree zero. This verifies the starting degree for dimension shifting for
the constructed comparison, rather than just supplying unrelated object
isomorphisms.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- A degree-zero homology isomorphism induces an isomorphism on degree-zero
Hom cohomology, for every coefficient module. -/
theorem isIso_homComplexCohomologyMap_zero
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    [IsIso (homologyMap f 0)] (E : ModuleCat.{u} R) :
    IsIso (homologyMap ((homComplexFunctor (ComplexShape.down ℕ) E).map f.op) 0) := by
  have : IsIso (homologyMap ((homComplexFunctor (ComplexShape.down ℕ) E).map f.op) 0 ≫
      (homComplexHomologyZeroIso K E).hom) := by
    rw [homComplexHomologyZeroIso_hom_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (homComplexHomologyZeroIso K E).hom

/-- If the augmentation identifies zeroth homology with the resolved
object, its Ext comparison is an isomorphism in degree zero. -/
theorem isIso_extToHomComplexCohomology_zero
    (K : ChainComplex (ModuleCat.{u} R) ℕ) [∀ n, Projective (K.X n)]
    {X : ModuleCat.{u} R} (a : K ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj X)
    [IsIso (homologyMap a 0)] (E : ModuleCat.{u} R) :
    IsIso (extToHomComplexCohomology K a E 0) := by
  let P := projectiveResolution X
  let k := liftToResolution K a P
  have : IsIso (homologyMap k 0 ≫ homologyMap P.π 0) := by
    rw [← homologyMap_comp]
    change IsIso (homologyMap (liftToResolution K a P ≫ P.π) 0)
    rw [liftToResolution_commutes]
    infer_instance
  have : IsIso (homologyMap k 0) := IsIso.of_isIso_comp_right _ (homologyMap P.π 0)
  have := isIso_homComplexCohomologyMap_zero k E
  change IsIso ((P.isoExt 0 E).hom ≫
    homologyMap ((homComplexFunctor (ComplexShape.down ℕ) E).map k.op) 0)
  infer_instance

/-- II.(7.5): the canonical finite-stage Ext-to-Koszul comparison is an
isomorphism in degree zero, without noetherian hypotheses. -/
instance koszulExtComparison_zero_isIso (fs : List R) (E : ModuleCat.{u} R) :
    IsIso (koszulExtComparison fs E 0) :=
  isIso_extToHomComplexCohomology_zero _ (koszulAugmentation fs) E

/-- The degree-zero finite-stage isomorphisms form an isomorphism of diagrams. -/
instance koszulExtComparisonDiagram_zero_isIso (fs : List R) (E : ModuleCat.{u} R) :
    IsIso (koszulExtComparisonDiagram fs E 0) := by
  have : ∀ n, IsIso ((koszulExtComparisonDiagram fs E 0).app n) :=
    fun n ↦ koszulExtComparison_zero_isIso _ E
  exact NatIso.isIso_of_isIso_app _

/-- II.(7.5)–(7.6): the constructed comparison on direct limits is an
isomorphism in degree zero over any commutative ring. -/
instance stableKoszulExtComparison_zero_isIso (fs : List R) (E : ModuleCat.{u} R) :
    IsIso (stableKoszulExtComparison fs E 0) :=
  inferInstanceAs (IsIso (colimMap (koszulExtComparisonDiagram fs E 0)))

end SGA.SGA2.ExposeII
