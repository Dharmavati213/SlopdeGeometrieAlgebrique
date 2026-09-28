/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.HomOrthogonalLength

/-!
# SGA 2, IV §5: ideals and submodules of the actual dualizing coefficient

The actual evaluation `Hom_R(R,H) ≃ H` turns orthogonality into annihilation
by an ideal. In the Artinian local case every module has support at the
unique maximal ideal, so the original injective residue-field criterion
applies to the entire specified `H`, with no invisible off-support summand.
No new definition of dualizing module is introduced.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Actual evaluation at `1`, with the original scalar action on `H`. -/
def moduleHomRingValueEquiv (H : ModuleCat.{u} R) :
    (moduleHomDual H).obj (op (ModuleCat.of R R)) ≃ₗ[R] H :=
  (ModuleCat.homLinearEquiv (S := R)).trans (LinearMap.ringLmapEquivSelf R R H)

@[simp] theorem moduleHomRingValueEquiv_apply (H : ModuleCat.{u} R)
    (f : (moduleHomDual H).obj (op (ModuleCat.of R R))) :
    moduleHomRingValueEquiv H f = ModuleCat.Hom.hom f 1 := rfl

@[simp] theorem moduleHomRingValueEquiv_symm_apply (H : ModuleCat.{u} R) (x : H) (r : R) :
    ModuleCat.Hom.hom ((moduleHomRingValueEquiv H).symm x) r = r • x := rfl

/-- The original orthogonal anti-isomorphism, followed by actual evaluation
at `1`. The supported ring hypothesis ensures the entire `H` is detected. -/
def supportedHomIdealOrderIso (J : Ideal R) (H : ModuleCat.{u} R)
    (hfin : FiniteSupportedHomValues J H) (hbid : SupportedModuleBiduality J H)
    (hR : supportedModuleProperty J (ModuleCat.of R R)) :
    Ideal R ≃o (Submodule R H)ᵒᵈ :=
  (supportedHomOrthogonalOrderIso J H hfin hbid (ModuleCat.of R R) hR).trans
    (Submodule.orderIsoMapComap (moduleHomRingValueEquiv H)).dual

/-- The submodule associated to an ideal is exactly its annihilator in
the specified original `H`, not an abstractly chosen corresponding submodule. -/
theorem mem_supportedHomIdealOrderIso (J : Ideal R) (H : ModuleCat.{u} R)
    (hfin : FiniteSupportedHomValues J H) (hbid : SupportedModuleBiduality J H)
    (hR : supportedModuleProperty J (ModuleCat.of R R)) (I : Ideal R) (x : H) :
    x ∈ OrderDual.ofDual (supportedHomIdealOrderIso J H hfin hbid hR I) ↔
      ∀ r ∈ I, r • x = 0 := by
  change x ∈ (homOrthogonal H (ModuleCat.of R R) I).map
    (moduleHomRingValueEquiv H).toLinearMap ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩ r hr
    change r • ModuleCat.Hom.hom f 1 = 0
    rw [← (ModuleCat.Hom.hom f).map_smul, smul_eq_mul, mul_one]
    exact hf r hr
  · intro hx
    refine ⟨(moduleHomRingValueEquiv H).symm x, ?_,
      (moduleHomRingValueEquiv H).apply_symm_apply x⟩
    intro r hr
    exact hx r hr

variable [IsArtinianRing R] [IsLocalRing R]

/-- In an Artinian local ring every actual module is supported at the
maximal ideal. Thus the coefficient in the ideal duality has no undetected
off-support part. -/
theorem artinianLocal_module_support (M : ModuleCat.{u} R) :
    supportedModuleProperty (IsLocalRing.maximalIdeal R) M := by
  intro p _
  change IsLocalRing.maximalIdeal R ≤ p.asIdeal
  exact (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime p.asIdeal).symm.le

/-- **IV §5, Artinian local ideal example:** the actual injective
coefficient satisfying the residue-field duality tests has an order-reversing
bijection between the original ideals and all its original submodules. -/
def artinianLocalHomIdealOrderIso (H : ModuleCat.{u} R) [Injective H]
    (hres : moduleHomDualResidueTests (IsLocalRing.maximalIdeal R) H) :
    Ideal R ≃o (Submodule R H)ᵒᵈ := by
  have hfin : FiniteSupportedHomValues (IsLocalRing.maximalIdeal R) H := by
    intro M hM hs
    have := hM
    exact moduleHomDual_finite_of_artinian_support (IsLocalRing.maximalIdeal R) H hres M hs
  have hbid : SupportedModuleBiduality (IsLocalRing.maximalIdeal R) H := by
    intro M hM hs
    have := hM
    exact moduleBidualEvaluation_isIso_of_artinian_support
      (IsLocalRing.maximalIdeal R) H hres M hs
  exact supportedHomIdealOrderIso (IsLocalRing.maximalIdeal R) H hfin hbid
    (artinianLocal_module_support (ModuleCat.of R R))

/-- The Artinian local correspondence is literally annihilation by the ideal. -/
theorem mem_artinianLocalHomIdealOrderIso (H : ModuleCat.{u} R) [Injective H]
    (hres : moduleHomDualResidueTests (IsLocalRing.maximalIdeal R) H) (I : Ideal R) (x : H) :
    x ∈ OrderDual.ofDual (artinianLocalHomIdealOrderIso H hres I) ↔
      ∀ r ∈ I, r • x = 0 :=
  mem_supportedHomIdealOrderIso _ H _ _ _ I x

end SGA.SGA2.ExposeIV
