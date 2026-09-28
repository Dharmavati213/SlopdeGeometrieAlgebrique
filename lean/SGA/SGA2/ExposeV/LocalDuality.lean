/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.LocalDualityTopFinite
import SGA.SGA2.ExposeV.LocalDualityYonedaCompatibility
import SGA.SGA2.ExposeV.RegularLocalFiniteFreeVanishing
import SGA.SGA2.ExposeV.KernelComparison

/-!
# V.2.1: the canonical local duality theorem

Over a regular local ring of dimension `n`, the original canonical map
`Hⁱ_m(M) → Hom_R(Extʲ_R(M,R), Hⁿ_m(R))`, with `i+j=n`, is an isomorphism
for every finite module. Descending induction starts with the proved
top-degree case and uses the original finite free cover, its finite kernel,
and the proved exact Yoneda sequences on the unchanged functor values.

Above dimension `n`, the original local cohomology already vanishes. No
extra Ext or local-cohomology objects, boundary-identification assumptions,
global dimension hypothesis, or completeness hypothesis are introduced.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing Functor

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **V.2.1.** The original canonical local-duality map is an isomorphism
in every complementary pair of nonnegative degrees for every finite module. -/
theorem regularLocal_localDualityMap_isIso (n : ℕ) (hdim : ringKrullDim R = n)
    (i j : ℕ) (h : i + j = n) (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsIso (localDualityMap (maximalIdeal R) M (ModuleCat.of R R) i j n h) := by
  induction j generalizing i M with
  | zero =>
      have hi : i = n := by omega
      subst i
      exact regularLocal_localDualityMap_top_isIso n hdim M
  | succ j ih =>
      obtain ⟨r, q, hq⟩ := Module.Finite.exists_fin' R M
      let Q := ModuleCat.of R (Fin r → R)
      let q' : Q ⟶ M := ModuleCat.ofHom q
      let S := moduleKernelShortComplex q'
      let K := S.X₁
      let k := S.f
      have hS := moduleKernelShortComplex_shortExact q' hq
      have hnext : (i + 1) + j = n := by omega
      let A := ShortComplex.mk _ _ (localCohomologyYonedaBoundary_comp (maximalIdeal R) S hS i)
      let B := ShortComplex.mk _ _
        (localDualityTargetYonedaBoundary_comp (maximalIdeal R) (ModuleCat.of R R) S hS j n)
      let φ : A ⟶ B :=
        { τ₁ := localDualityMap (maximalIdeal R) M (ModuleCat.of R R) i (j + 1) n h
          τ₂ := localDualityMap (maximalIdeal R) K (ModuleCat.of R R) (i + 1) j n hnext
          τ₃ := localDualityMap (maximalIdeal R) Q (ModuleCat.of R R) (i + 1) j n hnext
          comm₁₂ := (localDualityMap_yoneda_connecting (maximalIdeal R)
            (ModuleCat.of R R) S hS i j n hnext h).symm
          comm₂₃ := (localDualityMap_naturality (maximalIdeal R)
            (ModuleCat.of R R) (i + 1) j n hnext k).symm }
      have : IsIso φ.τ₂ := ih (i + 1) hnext K
      have : IsIso φ.τ₃ := ih (i + 1) hnext Q
      have : Mono A.f := localCohomologyYonedaBoundary_mono (maximalIdeal R) S hS i
        (regularLocal_localCohomology_finiteFree_isZero_of_lt n hdim r i (by omega))
      have : Mono B.f := localDualityTargetYonedaBoundary_mono (maximalIdeal R)
        (ModuleCat.of R R) S hS j n (moduleExt_finiteFree_isZero (ModuleCat.of R R) r j)
      exact isIso_left_of_exact_of_isIso_of_mono φ
        (localCohomologyYoneda_exact₁ (maximalIdeal R) S hS i)

/-- **V.2.1, natural form.** All components of the original canonical
transformation are isomorphisms on the actual category of finite modules. -/
def regularLocal_localDualityNatIso (n : ℕ) (hdim : ringKrullDim R = n)
    (i j : ℕ) (h : i + j = n) :
    forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙
        _root_.localCohomology (maximalIdeal R) i ≅
      forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) ⋙
        localDualityTargetFunctor (maximalIdeal R) (ModuleCat.of R R) j n := by
  let α := whiskerLeft (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))
    (localDualityNatTrans (maximalIdeal R) (ModuleCat.of R R) i j n h)
  have (M : FGModuleCat.{u} R) : IsIso (α.app M) :=
    regularLocal_localDualityMap_isIso n hdim i j h M.obj
  exact NatIso.ofComponents (fun M => asIso (α.app M)) (fun f => α.naturality f)

/-- The natural isomorphism has the unchanged canonical map as its
forward component, not an independently selected isomorphism. -/
@[simp]
theorem regularLocal_localDualityNatIso_hom_app (n : ℕ) (hdim : ringKrullDim R = n)
    (i j : ℕ) (h : i + j = n) (M : FGModuleCat.{u} R) :
    (regularLocal_localDualityNatIso n hdim i j h).hom.app M =
      localDualityMap (maximalIdeal R) M.obj (ModuleCat.of R R) i j n h := rfl

end SGA.SGA2.ExposeV
