/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.FiniteFreeComparison
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The finite-presentation comparison argument

An additive natural comparison, invertible on the ring, is invertible on
finite modules if both functors preserve epimorphisms and the target takes
short exact sequences to exact sequences. The kernel of the finite free
cover is finite because the ring is noetherian. No presentation or
comparison is postulated.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable {F G : ModuleCat.{u} R ⥤ ModuleCat.{u} R} [F.Additive] [G.Additive]
variable (α : F ⟶ G) [IsIso (α.app (ModuleCat.of R R))]

/-- A finite free cover proves surjectivity of the original comparison. -/
theorem epi_app_finite [G.PreservesEpimorphisms]
    (M : ModuleCat.{u} R) [Module.Finite R M] : Epi (α.app M) := by
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R M
  let q' : ModuleCat.of R (Fin n → R) ⟶ M := ModuleCat.ofHom q
  have : Epi q' := (ModuleCat.epi_iff_surjective _).mpr hq
  have := isIso_app_finiteFree α n
  have : Epi (F.map q' ≫ α.app M) := by
    rw [α.naturality]
    infer_instance
  exact epi_of_epi (F.map q') (α.app M)

/-- The finite-presentation step of V.2.1, stated for the actual natural
comparison and actual short exact coefficient sequences. -/
theorem isIso_app_finite [IsNoetherianRing R]
    [F.PreservesEpimorphisms] [G.PreservesEpimorphisms]
    (hG : ∀ (S : ShortComplex (ModuleCat.{u} R)), S.ShortExact → (S.map G).Exact)
    (M : ModuleCat.{u} R) [Module.Finite R M] : IsIso (α.app M) := by
  have := epi_app_finite α M
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨?_, (ModuleCat.epi_iff_surjective _).mp inferInstance⟩
  apply (injective_iff_map_eq_zero (α.app M).hom).mpr
  intro x hx
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R M
  let P := ModuleCat.of R (Fin n → R)
  let K := ModuleCat.of R q.ker
  let q' : P ⟶ M := ModuleCat.ofHom q
  let k : K ⟶ P := ModuleCat.ofHom q.ker.subtype
  let S : ShortComplex (ModuleCat.{u} R) := ShortComplex.mk k q' (by
    apply ModuleCat.hom_ext
    ext x
    exact x.property)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.moduleCat_exact_iff _).mpr (fun y hy => ⟨⟨y, hy⟩, rfl⟩)
      mono_f := (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hq }
  have : Epi q' := hS.epi_g
  have : IsIso (α.app P) := isIso_app_finiteFree α n
  have : Epi (α.app K) := epi_app_finite α K
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (F.map q')).mp inferInstance x
  have hy' : G.map q' (α.app P y) = 0 := by
    have h := ConcreteCategory.congr_hom (α.naturality q') y
    simp only [ModuleCat.comp_apply] at h
    rw [← h, hy]
    exact hx
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hG S hS) _ hy'
  obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective (α.app K)).mp inferInstance z
  have hyw : F.map k w = y := by
    apply (ModuleCat.mono_iff_injective (α.app P)).mp inferInstance
    have h := ConcreteCategory.congr_hom (α.naturality k) w
    simp only [ModuleCat.comp_apply] at h
    rw [h, hw]
    exact hz
  rw [← hy, ← hyw]
  change (F.map k ≫ F.map q') w = 0
  rw [← F.map_comp, S.zero, F.map_zero]
  rfl

end SGA.SGA2.ExposeV
