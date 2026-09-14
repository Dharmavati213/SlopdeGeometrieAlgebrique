/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorAntiEquivalence

/-!
# SGA 2, IV §5: actual orthogonal submodules

Orthogonality means that the original linear maps into the specified `H`
vanish on the given submodule. Canonical reflexivity of genuine supported
quotients proves both double-orthogonal identities, hence the order-reversing
bijection. The original functor version uses its specified evaluation `φ_T`.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Functor

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Actual maps into `H` vanishing on the specified original submodule. -/
def homOrthogonal (H M : ModuleCat.{u} R) (N : Submodule R M) :
    Submodule R ((moduleHomDual H).obj (op M)) where
  carrier := {f | ∀ x ∈ N, ModuleCat.Hom.hom f x = 0}
  zero_mem' := by intro x _; rfl
  add_mem' := by
    intro f g hf hg x hx
    change ModuleCat.Hom.hom f x + ModuleCat.Hom.hom g x = 0
    rw [hf x hx, hg x hx, add_zero]
  smul_mem' := by
    intro r f hf x hx
    change r • ModuleCat.Hom.hom f x = 0
    rw [hf x hx, smul_zero]

/-- Actual elements annihilated by every original map in the dual submodule. -/
def homCoorthogonal (H M : ModuleCat.{u} R)
    (P : Submodule R ((moduleHomDual H).obj (op M))) : Submodule R M where
  carrier := {x | ∀ f ∈ P, ModuleCat.Hom.hom f x = 0}
  zero_mem' := by intro f _; exact map_zero _
  add_mem' := by
    intro x y hx hy f hf
    rw [(ModuleCat.Hom.hom f).map_add, hx f hf, hy f hf, add_zero]
  smul_mem' := by
    intro r x hx f hf
    rw [(ModuleCat.Hom.hom f).map_smul, hx f hf, smul_zero]

@[simp] theorem mem_homOrthogonal (H M : ModuleCat.{u} R) (N : Submodule R M)
    (f : (moduleHomDual H).obj (op M)) :
    f ∈ homOrthogonal H M N ↔ ∀ x ∈ N, ModuleCat.Hom.hom f x = 0 := Iff.rfl

@[simp] theorem mem_homCoorthogonal (H M : ModuleCat.{u} R)
    (P : Submodule R ((moduleHomDual H).obj (op M))) (x : M) :
    x ∈ homCoorthogonal H M P ↔ ∀ f ∈ P, ModuleCat.Hom.hom f x = 0 := Iff.rfl

/-- Original Hom maps distinguish an element outside a submodule, using
canonical reflexivity of the actual quotient, not an assumed cogenerator. -/
theorem mem_submodule_of_hom_vanishing (J : Ideal R) (H : ModuleCat.{u} R)
    (hbid : SupportedModuleBiduality J H) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hSupp : supportedModuleProperty J M) (N : Submodule R M) (x : M)
    (hx : ∀ f : M ⟶ H, (∀ y ∈ N, f y = 0) → f x = 0) : x ∈ N := by
  let Q := ModuleCat.of R (M ⧸ N)
  let q : M ⟶ Q := ModuleCat.ofHom N.mkQ
  have hQ : supportedModuleProperty J Q :=
    (Module.support_subset_of_surjective N.mkQ N.mkQ_surjective).trans hSupp
  have := hbid Q inferInstance hQ
  have hz : moduleBidualEvaluation H Q (N.mkQ x) = 0 := by
    apply ModuleCat.hom_ext
    ext f
    change ModuleCat.Hom.hom f (N.mkQ x) = 0
    exact hx (q ≫ f) (by
      intro y hy
      change ModuleCat.Hom.hom f (N.mkQ y) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hy, map_zero])
  have hzero : N.mkQ x = 0 := by
    apply ((ModuleCat.mono_iff_injective (moduleBidualEvaluation H Q)).mp inferInstance)
    simpa only [map_zero] using hz
  exact (Submodule.Quotient.mk_eq_zero N).mp hzero

/-- The actual double orthogonal of an original submodule is itself. -/
theorem homCoorthogonal_homOrthogonal (J : Ideal R) (H : ModuleCat.{u} R)
    (hbid : SupportedModuleBiduality J H) (M : ModuleCat.{u} R) [Module.Finite R M]
    (hSupp : supportedModuleProperty J M) (N : Submodule R M) :
    homCoorthogonal H M (homOrthogonal H M N) = N := by
  apply le_antisymm
  · intro x hx
    exact mem_submodule_of_hom_vanishing J H hbid M hSupp N x hx
  · intro x hx f hf
    exact hf x hx

/-- The other double-orthogonal identity uses surjectivity of the original
canonical bidual map to express each dual functional as evaluation. -/
theorem homOrthogonal_homCoorthogonal (J : Ideal R) (H : ModuleCat.{u} R)
    (hfin : FiniteSupportedHomValues J H) (hbid : SupportedModuleBiduality J H)
    (M : ModuleCat.{u} R) [Module.Finite R M] (hSupp : supportedModuleProperty J M)
    (P : Submodule R ((moduleHomDual H).obj (op M))) :
    homOrthogonal H M (homCoorthogonal H M P) = P := by
  have := hfin M inferInstance hSupp
  have := hbid M inferInstance hSupp
  have hsD : supportedModuleProperty J ((moduleHomDual H).obj (op M)) :=
    (moduleHomDual_support_subset H M).trans hSupp
  apply le_antisymm
  · intro f hf
    apply mem_submodule_of_hom_vanishing J H hbid _ hsD P f
    intro g hg
    obtain ⟨x, hx⟩ := ((ModuleCat.epi_iff_surjective (moduleBidualEvaluation H M)).mp
      inferInstance) g
    have hxP : x ∈ homCoorthogonal H M P := by
      intro k hk
      have hh := hg k hk
      rw [← hx] at hh
      exact hh
    have hh := hf x hxP
    rw [← hx]
    exact hh
  · intro f hf x hx
    exact hx f hf

/-- **IV §5 orthogonality:** a genuine order-reversing bijection of all
submodules, with the stated vanishing orthogonal and coorthogonal maps. -/
def supportedHomOrthogonalOrderIso (J : Ideal R) (H : ModuleCat.{u} R)
    (hfin : FiniteSupportedHomValues J H) (hbid : SupportedModuleBiduality J H)
    (M : ModuleCat.{u} R) [Module.Finite R M] (hSupp : supportedModuleProperty J M) :
    Submodule R M ≃o (Submodule R ((moduleHomDual H).obj (op M)))ᵒᵈ where
  toFun N := OrderDual.toDual (homOrthogonal H M N)
  invFun P := homCoorthogonal H M (OrderDual.ofDual P)
  left_inv N := homCoorthogonal_homOrthogonal J H hbid M hSupp N
  right_inv P := homOrthogonal_homCoorthogonal J H hfin hbid M hSupp (OrderDual.ofDual P)
  map_rel_iff' := by
    intro N P
    change homOrthogonal H M P ≤ homOrthogonal H M N ↔ N ≤ P
    constructor
    · intro h x hx
      rw [← homCoorthogonal_homOrthogonal J H hbid M hSupp P]
      intro f hf
      exact h hf x hx
    · intro h f hf x hx
      exact hf x (h hx)

variable [IsNoetherianRing R]
variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- The orthogonality anti-isomorphism for the original dual functor.
The canonical IV.1.3 evaluation identifies its actual values with Hom. -/
def supportedFunctorOrthogonalOrderIso (h : SupportedFunctorDuality J T)
    (M : SupportedFGModuleCat J) :
    Submodule R M.obj ≃o (Submodule R (supportedFunctorValue J T M))ᵒᵈ := by
  let := supportedFunctorDuality_leftExact J T h
  let href : SupportedFunctorReflexive J T :=
    ⟨supportedFunctorDuality_finiteValues J T h,
      supportedFunctorDuality_bidually_reflexive J T h _⟩
  let hhom := (supportedFunctor_reflexive_iff_homBidual J T).mp href
  exact (supportedHomOrthogonalOrderIso J (supportedFunctorColimit J T)
    hhom.1 hhom.2 M.obj.obj M.property).trans
      (Submodule.orderIsoMapComap
        ((supportedFunctorRepresentationIso J T).app (op M)).toLinearEquiv).symm.dual

/-- Membership is precisely vanishing of the original canonical
evaluation on the specified submodule. -/
theorem mem_supportedFunctorOrthogonalOrderIso (h : SupportedFunctorDuality J T)
    [PreservesFiniteLimits T] (M : SupportedFGModuleCat J) (N : Submodule R M.obj)
    (t : supportedFunctorValue J T M) :
    t ∈ OrderDual.ofDual (supportedFunctorOrthogonalOrderIso J T h M N) ↔
      ∀ x ∈ N, ModuleCat.Hom.hom
        ((supportedFunctorRepresentationIso J T).hom.app (op M) t) x = 0 := Iff.rfl

end SGA.SGA2.ExposeIV
