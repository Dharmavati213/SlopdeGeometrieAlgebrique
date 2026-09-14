/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.DepthLocalization

/-!
# SGA 2, Exposé III, Remark 2.7: finite depth and support

We prove that depth is finite exactly when the module support meets `V(I)`.
No dimension bound is assumed: noetherianness rules out an infinite sequence
of strict enlargements of submodules obtained by adjoining regular elements.
-/

noncomputable section

universe u

open CategoryTheory RingTheory.Sequence
open scoped Pointwise

namespace SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R]

/-- A zero module has infinite depth, over any commutative ring. -/
theorem depth_eq_top_of_subsingleton (I : Ideal R) (M : ModuleCat.{u} R)
    [Subsingleton M] : depth I M = ⊤ := by
  apply top_unique
  rw [← ENat.iSup_natCast]
  apply iSup_le
  intro n
  have hreg : IsWeaklyRegular M (List.replicate n (0 : R)) :=
    ⟨fun _ _ _ _ _ ↦ Subsingleton.elim _ _⟩
  have hmem : ∀ r ∈ List.replicate n (0 : R), r ∈ I := by
    intro r hr
    obtain rfl := (List.mem_replicate.mp hr).2
    exact I.zero_mem
  simpa only [List.length_replicate] using length_le_depth I M _ hmem hreg

/-- The successive quotient used to enlarge a regular sequence. -/
def quotSMulTopQuotientEquivSup (M : ModuleCat.{u} R) (N : Submodule R M) (f : R) :
    QuotSMulTop f (M ⧸ N) ≃ₗ[R] M ⧸ (N ⊔ f • (⊤ : Submodule R M)) :=
  Submodule.quotEquivOfEq (f • (⊤ : Submodule R (M ⧸ N)))
    ((f • (⊤ : Submodule R M)).map N.mkQ) (by
      rw [Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ]) ≪≫ₗ
    Submodule.quotientQuotientEquivQuotientSup N (f • ⊤)

variable [IsNoetherianRing R]

/-- Infinite depth forces `IM = M`: otherwise noetherianness forbids repeated
strict enlargements of the submodules defined by regular sequences. -/
theorem ideal_smul_top_eq_top_of_depth_eq_top (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] (hdepth : depth I M = ⊤) :
    I • (⊤ : Submodule R M) = ⊤ := by
  by_contra hproper
  have hbot : depth I (ModuleCat.of R (M ⧸ (⊥ : Submodule R M))) = ⊤ := by
    rw [depth_eq_of_linearEquiv I
      (M := ModuleCat.of R (M ⧸ (⊥ : Submodule R M))) (N := M)
      (Submodule.quotEquivOfEqBot _ rfl)]
    exact hdepth
  obtain ⟨N, ⟨hNle, hNdepth⟩, hNmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R M)
      {N : Submodule R M | N ≤ I • ⊤ ∧ depth I (ModuleCat.of R (M ⧸ N)) = ⊤}
      ⟨⊥, bot_le, hbot⟩
  let Q := ModuleCat.of R (M ⧸ N)
  have hNproper : N ≠ ⊤ := ne_top_of_le_ne_top hproper hNle
  have : Nontrivial Q := Submodule.Quotient.nontrivial_iff.mpr hNproper
  obtain ⟨f, hf, hreg⟩ := (one_le_depth_iff_exists_regular I Q).mp (by simp [Q, hNdepth])
  have hQdepth : depth I (ModuleCat.of R (QuotSMulTop f Q)) = ⊤ := by
    have hh := III_2_5 I Q hf hreg
    rw [show depth I Q = ⊤ from hNdepth] at hh
    simpa only [ENat.add_eq_top, ENat.one_ne_top, or_false] using hh.symm
  let P : Submodule R M := N ⊔ f • ⊤
  have hPle : P ≤ I • ⊤ := by
    apply sup_le hNle
    intro m hm
    obtain ⟨x, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists m f ⊤).mp hm
    exact Submodule.smul_mem_smul hf (Submodule.mem_top)
  have hPdepth : depth I (ModuleCat.of R (M ⧸ P)) = ⊤ := by
    rw [← depth_eq_of_linearEquiv I
      (M := ModuleCat.of R (QuotSMulTop f (M ⧸ N)))
      (N := ModuleCat.of R (M ⧸ P)) (quotSMulTopQuotientEquivSup M N f)]
    exact hQdepth
  apply hNmax P ⟨hPle, hPdepth⟩
  refine lt_iff_le_not_ge.mpr ⟨le_sup_left, ?_⟩
  intro hPN
  obtain ⟨q, hq⟩ := exists_ne (0 : Q)
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective N q
  apply hq
  apply hreg.right_eq_zero_of_smul
  rw [← N.mkQ.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hPN ((show f • (⊤ : Submodule R M) ≤ P from le_sup_right)
    (Submodule.smul_mem_pointwise_smul m f ⊤ Submodule.mem_top))

/-- If support misses `V(I)`, all relevant local modules vanish and depth is infinite. -/
theorem depth_eq_top_of_disjoint_support (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M]
    (h : Disjoint (Module.support R M) (PrimeSpectrum.zeroLocus (I : Set R))) :
    depth I M = ⊤ := by
  rw [III_2_9]
  apply iInf_eq_top.mpr
  intro p
  apply iInf_eq_top.mpr
  intro hp
  have : Subsingleton (LocalizedModule.AtPrime p.asIdeal M) :=
    Module.notMem_support_iff.mp (fun hpM ↦ Set.disjoint_left.mp h hpM hp)
  exact depth_eq_top_of_subsingleton _ _

/-- III.2.7 in its infinite-depth form. -/
theorem depth_eq_top_iff_disjoint_support (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] :
    depth I M = ⊤ ↔
      Disjoint (Module.support R M) (PrimeSpectrum.zeroLocus (I : Set R)) := by
  constructor
  · intro h
    apply Set.disjoint_iff_inter_eq_empty.mpr
    rw [← Module.support_quotient, ideal_smul_top_eq_top_of_depth_eq_top I M h]
    exact Module.support_eq_empty
  · exact depth_eq_top_of_disjoint_support I M

/-- An algebraic form of III.2.7: infinite depth is equivalent to `IM = M`. -/
theorem depth_eq_top_iff_ideal_smul_top_eq_top (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] : depth I M = ⊤ ↔ I • (⊤ : Submodule R M) = ⊤ := by
  rw [depth_eq_top_iff_disjoint_support, Set.disjoint_iff_inter_eq_empty,
    ← Module.support_quotient, Module.support_eq_empty_iff, Submodule.Quotient.subsingleton_iff]

/-- Properness of `IM` is exactly the hypothesis that depth is finite. -/
theorem depth_lt_top_iff_ideal_smul_top_ne_top (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] : depth I M < ⊤ ↔ I • (⊤ : Submodule R M) ≠ ⊤ := by
  rw [lt_top_iff_ne_top, ne_eq, depth_eq_top_iff_ideal_smul_top_eq_top]

/-- III.2.7: finite depth is equivalent to a nonempty intersection with `V(I)`. -/
theorem III_2_7 (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth I M < ⊤ ↔
      (Module.support R M ∩ PrimeSpectrum.zeroLocus (I : Set R)).Nonempty := by
  rw [lt_top_iff_ne_top, ne_eq, depth_eq_top_iff_disjoint_support,
    Set.disjoint_iff_inter_eq_empty, Set.nonempty_iff_ne_empty]

end SGA.SGA2.ExposeIII
