/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.LocalSocleDuality

/-!
# Actual quotient Hom as an annihilator in the original dual

The comparison is precomposition with the original quotient projection.
It holds for arbitrary modules and arbitrary coefficient modules, without
finite generation or a duality assumption. In particular it identifies the
socle of a dual with the dual of the original residue quotient.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Actual precomposition with the quotient map, with its vanishing recorded. -/
def quotientHomOrthogonalMap (H M : ModuleCat.{u} R) (N : Submodule R M) :
    (moduleHomDual H).obj (op (ModuleCat.of R (M ⧸ N))) ⟶
      ModuleCat.of R (homOrthogonal H M N) :=
  ModuleCat.ofHom
    { toFun := fun f => ⟨ModuleCat.ofHom N.mkQ ≫ f, fun x hx => by
        change f (N.mkQ x) = 0
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hx, map_zero]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Quotient factorization proves bijectivity of the specified original map. -/
theorem quotientHomOrthogonalMap_bijective (H M : ModuleCat.{u} R)
    (N : Submodule R M) : Function.Bijective (quotientHomOrthogonalMap H M N) := by
  constructor
  · intro f g h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := N.mkQ_surjective x
    exact congrArg (fun k : homOrthogonal H M N => k.val.hom y) h
  · intro f
    let g : ModuleCat.of R (M ⧸ N) ⟶ H :=
      ModuleCat.ofHom (N.liftQ f.val.hom (fun _ hx => f.property _ hx))
    refine ⟨g, ?_⟩
    apply Subtype.ext
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- The original quotient dual is the literal orthogonal submodule. -/
def quotientHomOrthogonalIso (H M : ModuleCat.{u} R) (N : Submodule R M) :
    (moduleHomDual H).obj (op (ModuleCat.of R (M ⧸ N))) ≅
      ModuleCat.of R (homOrthogonal H M N) :=
  LinearEquiv.toModuleIso (LinearEquiv.ofBijective
    (quotientHomOrthogonalMap H M N).hom (quotientHomOrthogonalMap_bijective H M N))

/-- Vanishing on `J M` is exactly annihilation by `J` in the original Hom module. -/
theorem homOrthogonal_ideal_smul (J : Ideal R) (H M : ModuleCat.{u} R) :
    homOrthogonal H M (J • (⊤ : Submodule R M)) =
      Submodule.torsionBySet R ((moduleHomDual H).obj (op M)) (J : Set R) := by
  ext f
  rw [mem_homOrthogonal, Submodule.mem_torsionBySet_iff]
  simp only [Subtype.forall, SetLike.mem_coe]
  constructor
  · intro hf r hr
    apply ModuleCat.hom_ext
    ext x
    change r • f.hom x = 0
    rw [← f.hom.map_smul]
    exact hf _ (Submodule.smul_mem_smul hr Submodule.mem_top)
  · intro hf x hx
    have hle : J • (⊤ : Submodule R M) ≤ f.hom.ker := by
      apply Submodule.smul_le.mpr
      intro r hr y _
      change f.hom (r • y) = 0
      rw [f.hom.map_smul]
      exact congrArg (fun g : M ⟶ H => g.hom y) (hf r hr)
    exact hle hx

/-- Actual ideal-quotient duality, with the original scalar action on the annihilator. -/
def quotientHomIdealAnnihilatorIso (J : Ideal R) (H M : ModuleCat.{u} R) :
    (moduleHomDual H).obj (op (ModuleCat.of R (M ⧸ (J • (⊤ : Submodule R M))))) ≅
      ModuleCat.of R (Submodule.torsionBySet R ((moduleHomDual H).obj (op M)) (J : Set R)) :=
  quotientHomOrthogonalIso H M (J • ⊤) ≪≫
    (LinearEquiv.ofEq _ _ (homOrthogonal_ideal_smul J H M)).toModuleIso

/-- The annihilator comparison retains the original quotient-precomposition map. -/
@[simp] theorem quotientHomIdealAnnihilatorIso_apply
    (J : Ideal R) (H M : ModuleCat.{u} R)
    (f : ModuleCat.of R (M ⧸ (J • (⊤ : Submodule R M))) ⟶ H) (x : M) :
    ModuleCat.Hom.hom ((quotientHomIdealAnnihilatorIso J H M).hom f).val x =
      f ((J • (⊤ : Submodule R M)).mkQ x) := rfl

end SGA.SGA2.ExposeIV
