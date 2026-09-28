/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.AffineSupport
import SGA.SGA2.ExposeII.InjectiveTorsion
import SGA.SGA2.ExposeII.FiniteFractionCover
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# SGA 2, Exposé II, Corollary 10: injective associated sheaves

Over a noetherian ring, every section of the sheaf associated to an injective
module extends globally. The algebraic argument splits off ideal-power torsion
and extends the resulting compatible numerators from an ideal to the ring.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

/-- Compatible numerators over finitely many principal opens are the
multiples of one element, up to ideal-power torsion. -/
theorem exists_smul_eq_mod_powerTorsion_of_compatible
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (E : ModuleCat.{u} R) [Injective E] {ι : Type u} [Finite ι]
    (a : ι → E) (b : ι → R) (hab : ∀ i j, b j • a i = b i • a j) :
    ∃ x : E, ∀ i, a i - b i • x ∈ powerTorsion (Ideal.span (Set.range b)) E := by
  classical
  let := Fintype.ofFinite ι
  let I := Ideal.span (Set.range b)
  obtain ⟨r, hr⟩ := exists_powerTorsion_retraction I E
  let p := Fintype.linearCombination R b
  let q₀ := Fintype.linearCombination R a
  let q : (ι → R) →ₗ[R] E := q₀ - (powerTorsion I E).subtype.comp (r.comp q₀)
  have hker : p.ker ≤ q.ker := by
    intro c hc
    have hbc (j : ι) : b j • q₀ c = 0 := by
      have hc' : ∑ i, c i • b i = 0 := hc
      calc
        b j • q₀ c = ∑ i, c i • (b j • a i) := by
          simp only [q₀, Fintype.linearCombination_apply, Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact smul_comm _ _ _
        _ = ∑ i, c i • (b i • a j) := by simp_rw [hab]
        _ = (∑ i, c i • b i) • a j := by simp [Finset.sum_smul, smul_smul]
        _ = 0 := by rw [hc', zero_smul]
    have hI : I ≤ (LinearMap.toSpanSingleton R E (q₀ c)).ker := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hbc j
    have hqc : q₀ c ∈ powerTorsion I E :=
      (mem_powerTorsion_iff I E (q₀ c)).mpr
        ⟨1, fun t ht ↦ hI (by simpa only [pow_one] using ht)⟩
    have hrqc := congrArg (fun f : powerTorsion I E →ₗ[R] powerTorsion I E ↦
      (f ⟨q₀ c, hqc⟩ : E)) hr
    change q₀ c - (r (q₀ c) : E) = 0
    exact sub_eq_zero.mpr hrqc.symm
  obtain ⟨g, hg⟩ := exists_linearMap_extension_of_ker_le
    (A := ModuleCat.of R (ι → R)) (B := ModuleCat.of R R) p q hker
  refine ⟨g 1, fun i ↦ ?_⟩
  have hgi := congrArg (fun f : (ι → R) →ₗ[R] E ↦ f (Pi.single i 1)) hg
  have he : b i • g 1 = a i - (r (a i) : E) := by
    simpa [p, q, q₀, ← g.map_smul] using hgi
  rw [he, sub_sub_cancel]
  exact (r (a i)).property

/-- A section of an injective associated sheaf on a quasi-compact open
extends to an element of the original module. This uses the concrete
locally-fraction-valued model of the associated sheaf. -/
theorem structureSheaf_toOpen_surjective_of_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (E : ModuleCat.{u} R) [Injective E] (U : Opens (PrimeSpectrum.Top R))
    (hU : IsCompact (U : Set (PrimeSpectrum.Top R))) :
    Function.Surjective (StructureSheaf.toOpenₗ R E U) := by
  intro s
  obtain ⟨ι, inst, a, b, hle, hcover, hab, hs⟩ :=
    exists_normalized_finite_fraction_cover U hU s
  let := inst
  obtain ⟨x, hx⟩ := exists_smul_eq_mod_powerTorsion_of_compatible E a b hab
  refine ⟨x, (structureSheafInType R E).eq_of_locally_eq'
    (fun i ↦ PrimeSpectrum.basicOpen (b i)) U (fun i ↦ (hle i).hom) hcover _ _ ?_⟩
  intro i
  rw [hs i]
  apply Subtype.ext
  apply funext
  intro z
  obtain ⟨n, hn⟩ := (mem_powerTorsion_iff _ E _).mp (hx i)
  have hnil : b i ^ n • (a i - b i • x) = 0 :=
    hn _ (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) n)
  refine LocalizedModule.mk_eq.mpr
    ⟨⟨b i ^ n, z.val.asIdeal.primeCompl.pow_mem z.property n⟩, ?_⟩
  simpa only [Submonoid.smul_def, Subtype.coe_mk, one_smul, smul_sub, sub_eq_zero]
    using (sub_eq_zero.mp (by simpa only [smul_sub] using hnil)).symm

/-- II.10 over a noetherian ring: an injective module surjects onto
the actual associated-sheaf sections on every open subset of its spectrum. -/
theorem tilde_toOpen_surjective_of_injective {R : CommRingCat.{u}}
    [IsNoetherianRing R] (E : ModuleCat.{u} R) [Injective E] (U : (Spec R).Opens) :
    Function.Surjective (tilde.toOpen E U) := by
  let : NoetherianSpace (PrimeSpectrum.Top R) :=
    inferInstanceAs (NoetherianSpace (PrimeSpectrum R))
  have h := structureSheaf_toOpen_surjective_of_injective E U (NoetherianSpace.isCompact _)
  exact ((tilde.modulesSpecToSheafIso E).app (op U)).toLinearEquiv.symm.surjective.comp h

/-- Every restriction of the associated sheaf of an injective module over
a noetherian ring is surjective. -/
theorem tilde_restriction_surjective_of_injective {R : CommRingCat.{u}}
    [IsNoetherianRing R] (E : ModuleCat.{u} R) [Injective E]
    {U V : (Spec R).Opens} (hVU : V ≤ U) :
    Function.Surjective ((affineTildeSheaf E).presheaf.map (homOfLE hVU).op) := by
  intro s
  obtain ⟨x, hx⟩ := tilde_toOpen_surjective_of_injective E V s
  exact ⟨tilde.toOpen E U x,
    (ConcreteCategory.congr_hom (tilde.toOpen_res E U V (homOfLE hVU)) x).trans hx⟩

/-- II.10, the noetherian-ring case: the sheaf associated with every
injective module is flasque. -/
theorem affineTildeSheaf_isFlasque_of_injective {R : CommRingCat.{u}}
    [IsNoetherianRing R] (E : ModuleCat.{u} R) [Injective E] :
    TopCat.Sheaf.IsFlasque (affineTildeSheaf E) where
  epi f := (ModuleCat.epi_iff_surjective _).mpr
    (tilde_restriction_surjective_of_injective E (leOfHom f.unop))

/-- The same flasqueness statement after forgetting scalar multiplication,
in the abelian-sheaf language used for local cohomology in Exposé I. -/
theorem affineTildeAbSheaf_isFlasque_of_injective {R : CommRingCat.{u}}
    [IsNoetherianRing R] (E : ModuleCat.{u} R) [Injective E] :
    TopCat.Sheaf.IsFlasque (affineTildeAbSheaf E) where
  epi f := (AddCommGrpCat.epi_iff_surjective _).mpr
    (tilde_restriction_surjective_of_injective E (leOfHom f.unop))

end SGA.SGA2.ExposeII
