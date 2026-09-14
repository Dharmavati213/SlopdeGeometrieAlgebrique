/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.HomQuotientAnnihilator
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.LinearAlgebra.Pi

/-!
# The dual of an annihilator is the actual quotient of the dual

For an injective coefficient module and a finitely generated ideal, the
kernel of restriction to the ideal annihilator is precisely the ideal times
the original Hom module. The nontrivial inclusion uses a finite generating
family: a functional vanishing on the annihilator extends along the map to
the finite product given by multiplication by those generators.

No finiteness or reflexivity of the source module is assumed. The resulting
quotient comparison retains the original restriction map.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped BigOperators

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

/-- Restrict an original linear functional to the literal ideal annihilator. -/
def homIdealAnnihilatorRestriction (J : Ideal R) (H X : ModuleCat.{u} R) :
    (moduleHomDual H).obj (op X) ⟶
      (moduleHomDual H).obj (op (ModuleCat.of R
        (Submodule.torsionBySet R X (J : Set R)))) :=
  (moduleHomDual H).map
    (ModuleCat.ofHom (Submodule.torsionBySet R X (J : Set R)).subtype).op

@[simp]
theorem homIdealAnnihilatorRestriction_apply (J : Ideal R) (H X : ModuleCat.{u} R)
    (f : X ⟶ H) (x : Submodule.torsionBySet R X (J : Set R)) :
    ModuleCat.Hom.hom (homIdealAnnihilatorRestriction J H X f) x = f.hom x.val := rfl

/-- Injectivity of the coefficient makes the specified actual restriction surjective. -/
theorem homIdealAnnihilatorRestriction_surjective (J : Ideal R)
    (H X : ModuleCat.{u} R) [Injective H] :
    Function.Surjective (homIdealAnnihilatorRestriction J H X) := by
  intro f
  let i : ModuleCat.of R (Submodule.torsionBySet R X (J : Set R)) ⟶ X :=
    ModuleCat.ofHom (Submodule.torsionBySet R X (J : Set R)).subtype
  have : Mono i := (ModuleCat.mono_iff_injective i).mpr Subtype.val_injective
  obtain ⟨g, hg⟩ := Injective.factors f i
  exact ⟨g, hg⟩

instance (J : Ideal R) (H X : ModuleCat.{u} R) [Injective H] :
    Epi (homIdealAnnihilatorRestriction J H X) :=
  (ModuleCat.epi_iff_surjective _).mpr
    (homIdealAnnihilatorRestriction_surjective J H X)

/-- An injective module extends a functional along any map whose kernel it kills. -/
private theorem injective_factor_of_ker_le (H X Y : ModuleCat.{u} R) [Injective H]
    (a : X →ₗ[R] Y) (f : X →ₗ[R] H) (h : a.ker ≤ f.ker) :
    ∃ g : Y →ₗ[R] H, g.comp a = f := by
  let a' : ModuleCat.of R (X ⧸ a.ker) ⟶ Y :=
    ModuleCat.ofHom (a.ker.liftQ a le_rfl)
  have : Mono a' := (ModuleCat.mono_iff_injective a').mpr
    (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))
  obtain ⟨g, hg⟩ := Injective.factors (ModuleCat.ofHom (a.ker.liftQ f h)) a'
  refine ⟨g.hom, ?_⟩
  ext x
  exact ConcreteCategory.congr_hom hg (a.ker.mkQ x)

/-- Multiples by the ideal vanish on its actual annihilator. -/
theorem ideal_smul_le_ker_homIdealAnnihilatorRestriction
    (J : Ideal R) (H X : ModuleCat.{u} R) :
    J • (⊤ : Submodule R ((moduleHomDual H).obj (op X))) ≤
      (homIdealAnnihilatorRestriction J H X).hom.ker := by
  apply Submodule.smul_le.mpr
  intro r hr f _
  apply ModuleCat.hom_ext
  ext x
  change r • f.hom x.val = 0
  rw [← f.hom.map_smul]
  have hx : r • x.val = 0 :=
    ((Submodule.mem_torsionBySet_iff _ _).mp x.property) ⟨r, hr⟩
  rw [hx, map_zero]

/-- For a finitely generated ideal, every functional zero on the annihilator
is an ideal multiple in the original Hom module. -/
theorem ker_homIdealAnnihilatorRestriction_le_ideal_smul
    (J : Ideal R) (hJ : J.FG) (H X : ModuleCat.{u} R) [Injective H] :
    (homIdealAnnihilatorRestriction J H X).hom.ker ≤
      J • (⊤ : Submodule R ((moduleHomDual H).obj (op X))) := by
  classical
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hJ
  intro f hf
  let a : X →ₗ[R] (Fin n → X) :=
    LinearMap.pi (fun i => s i • (LinearMap.id : X →ₗ[R] X))
  have hker : a.ker ≤ f.hom.ker := by
    intro x hx
    have hx' : ∀ r ∈ J, r • x = 0 := by
      intro r hr
      rw [← hs] at hr
      induction hr using Submodule.span_induction with
      | mem r hr =>
          obtain ⟨i, rfl⟩ := hr
          exact congrFun hx i
      | zero => exact zero_smul R x
      | add r t _ _ hr ht => rw [add_smul, hr, ht, zero_add]
      | smul r t _ ht => rw [smul_eq_mul, mul_smul, ht, smul_zero]
    have hxAnn : x ∈ Submodule.torsionBySet R X (J : Set R) := by
      rw [Submodule.mem_torsionBySet_iff]
      exact fun r => hx' r.val r.property
    exact congrArg (fun g : ModuleCat.of R
      (Submodule.torsionBySet R X (J : Set R)) ⟶ H => g.hom ⟨x, hxAnn⟩) hf
  obtain ⟨g, hg⟩ := injective_factor_of_ker_le H X (ModuleCat.of R (Fin n → X))
    a f.hom hker
  let φ : Fin n → (X ⟶ H) := fun i =>
    ModuleCat.ofHom (g.comp (LinearMap.single R (fun _ : Fin n => X) i))
  have hfSum : f = ∑ i, s i • φ i := by
    apply ModuleCat.hom_ext
    ext x
    have hsum : a x = ∑ i, s i • Pi.single i x := by
      ext i
      simp [a, Pi.single_apply]
    calc
      f.hom x = g (a x) := (LinearMap.congr_fun hg x).symm
      _ = ∑ i, s i • g (Pi.single i x) := by rw [hsum, map_sum]; simp
      _ = (∑ i, s i • φ i).hom x := by simp [φ]
  rw [hfSum]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem_smul
    (hs ▸ Submodule.subset_span (Set.mem_range_self i)) Submodule.mem_top

/-- The kernel of the original restriction is literally the ideal times the dual. -/
theorem ker_homIdealAnnihilatorRestriction (J : Ideal R) (hJ : J.FG)
    (H X : ModuleCat.{u} R) [Injective H] :
    (homIdealAnnihilatorRestriction J H X).hom.ker =
      J • (⊤ : Submodule R ((moduleHomDual H).obj (op X))) :=
  le_antisymm (ker_homIdealAnnihilatorRestriction_le_ideal_smul J hJ H X)
    (ideal_smul_le_ker_homIdealAnnihilatorRestriction J H X)

/-- The actual restriction descended to the actual ideal quotient of the dual. -/
def quotientHomIdealAnnihilatorRestriction (J : Ideal R) (H X : ModuleCat.{u} R) :
    ModuleCat.of R (((moduleHomDual H).obj (op X)) ⧸
      (J • (⊤ : Submodule R ((moduleHomDual H).obj (op X))))) ⟶
      (moduleHomDual H).obj (op (ModuleCat.of R
        (Submodule.torsionBySet R X (J : Set R)))) :=
  ModuleCat.ofHom ((J • (⊤ : Submodule R ((moduleHomDual H).obj (op X)))).liftQ
    (homIdealAnnihilatorRestriction J H X).hom
      (ideal_smul_le_ker_homIdealAnnihilatorRestriction J H X))

/-- Bijectivity of the specified quotient-restriction comparison. -/
theorem quotientHomIdealAnnihilatorRestriction_bijective (J : Ideal R) (hJ : J.FG)
    (H X : ModuleCat.{u} R) [Injective H] :
    Function.Bijective (quotientHomIdealAnnihilatorRestriction J H X) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ _ _
      (ker_homIdealAnnihilatorRestriction J hJ H X).le
  · intro f
    obtain ⟨g, hg⟩ := homIdealAnnihilatorRestriction_surjective J H X f
    exact ⟨Submodule.Quotient.mk g, hg⟩

/-- For a finitely generated ideal and injective coefficient, the dual of its
annihilator is the actual ideal quotient of the original dual. -/
def homIdealAnnihilatorQuotientIso (J : Ideal R) (hJ : J.FG)
    (H X : ModuleCat.{u} R) [Injective H] :
    ModuleCat.of R (((moduleHomDual H).obj (op X)) ⧸
      (J • (⊤ : Submodule R ((moduleHomDual H).obj (op X))))) ≅
      (moduleHomDual H).obj (op (ModuleCat.of R
        (Submodule.torsionBySet R X (J : Set R)))) :=
  (LinearEquiv.ofBijective (quotientHomIdealAnnihilatorRestriction J H X).hom
    (quotientHomIdealAnnihilatorRestriction_bijective J hJ H X)).toModuleIso

/-- The comparison sends a quotient class to the original restricted functional. -/
@[simp]
theorem homIdealAnnihilatorQuotientIso_apply_mk (J : Ideal R) (hJ : J.FG)
    (H X : ModuleCat.{u} R) [Injective H] (f : X ⟶ H)
    (x : Submodule.torsionBySet R X (J : Set R)) :
    ModuleCat.Hom.hom ((homIdealAnnihilatorQuotientIso J hJ H X).hom
      (Submodule.Quotient.mk f)) x = f.hom x.val := rfl

/-- The comparison composed with the original quotient projection is the
original restriction map, as an equality of actual module morphisms. -/
@[reassoc]
theorem homIdealAnnihilatorQuotientIso_mkQ (J : Ideal R) (hJ : J.FG)
    (H X : ModuleCat.{u} R) [Injective H] :
    ModuleCat.ofHom ((J • (⊤ : Submodule R ((moduleHomDual H).obj (op X)))).mkQ) ≫
      (homIdealAnnihilatorQuotientIso J hJ H X).hom =
        homIdealAnnihilatorRestriction J H X := rfl

end SGA.SGA2.ExposeIV
