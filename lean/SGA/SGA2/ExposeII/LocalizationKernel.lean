/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.FiniteGenerators
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# SGA 2, Exposé II, (4.2) and (7.5): the kernel of localization

For a finite family generating `I`, an element belongs to ideal-power torsion
if and only if it becomes zero in each localization `M[1/fₐ]`. Thus the
kernel of the map to the product of these localizations is `powerTorsion I M`.
This supplies the module calculation at the start of the affine supported
sections sequence. Identifying the localized modules with sections of the
associated sheaf is a separate geometric comparison.
-/

noncomputable section

universe u v w

namespace SGA.SGA2.ExposeII

variable {R : Type u} [CommRing R] {ι : Type v} (f : ι → R)
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- An element vanishes on localization at `r` precisely when some power
of `r` annihilates it. -/
theorem away_mkLinearMap_eq_zero_iff (r : R) (x : M) :
    LocalizedModule.mkLinearMap (Submonoid.powers r) M x = 0 ↔
      ∃ n : ℕ, r ^ n • x = 0 := by
  change x ∈ LinearMap.ker (LocalizedModule.mkLinearMap (Submonoid.powers r) M) ↔ _
  rw [LocalizedModule.mem_ker_mkLinearMap_iff]
  constructor
  · rintro ⟨a, ⟨n, rfl⟩, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨r ^ n, ⟨n, rfl⟩, hn⟩

/-- Ideal-power torsion is detected by vanishing in the localizations at
any finite generating family. -/
theorem mem_powerTorsion_iff_localization_eq_zero [Finite ι] (x : M) :
    x ∈ powerTorsion (Ideal.span (Set.range f)) M ↔
      ∀ a, LocalizedModule.mkLinearMap (Submonoid.powers (f a)) M x = 0 := by
  rw [mem_powerTorsion_span_iff_forall]
  simp only [away_mkLinearMap_eq_zero_iff]

/-- The map from a module to its localizations on a family of principal opens. -/
def localizationFamilyMap :
    M →ₗ[R] (∀ a : ι, LocalizedModule (Submonoid.powers (f a)) M) :=
  LinearMap.pi fun a => LocalizedModule.mkLinearMap (Submonoid.powers (f a)) M

/-- The algebraic kernel calculation for II.(4.2). -/
theorem localizationFamilyMap_ker [Finite ι] :
    LinearMap.ker (localizationFamilyMap f M) =
      powerTorsion (Ideal.span (Set.range f)) M := by
  ext x
  rw [mem_powerTorsion_iff_localization_eq_zero]
  change (fun a => LocalizedModule.mkLinearMap (Submonoid.powers (f a)) M x) = 0 ↔ _
  exact funext_iff

/-- The supported-section inclusion followed by localization is exact. -/
theorem powerTorsion_subtype_range_eq_localizationFamilyMap_ker [Finite ι] :
    LinearMap.range (powerTorsion (Ideal.span (Set.range f)) M).subtype =
      LinearMap.ker (localizationFamilyMap f M) := by
  rw [Submodule.range_subtype, localizationFamilyMap_ker]

end SGA.SGA2.ExposeII
