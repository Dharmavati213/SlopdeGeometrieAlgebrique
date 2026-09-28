/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Differentials.BaseChange
import SGA.Foundations.Differentials.Exact
import SGA.Foundations.Differentials.Smooth
import SGA.Foundations.Differentials.Unramified

/-!
# SGA 1, Exposé II, §4: the sheaf of relative differentials

Scheme-level forms of the results of §4, using the sheaf `Ω¹_{X/Y}` of `SGA.Foundations`
(`AlgebraicGeometry.Scheme.Hom.relativeDifferentials`):

* the exact sequence (4.2 bis) `f^* Ω¹_{Y/Z} → Ω¹_{X/Z} → Ω¹_{X/Y} → 0`;
* II.4.1: `f` is unramified iff `f^* Ω¹_{Y/Z} → Ω¹_{X/Z}` is an epimorphism;
* II.4.3 (ii): `Ω¹_{X/Y}` is locally free, of rank `n` for `f` smooth of relative dimension `n`;
* the comparison of `Γ(U, Ω¹_{X/Y})` with `Ω¹` of rings on affine opens, by which the pointwise
  statements of II.4 reduce to the ring-level files `Differentials`, `Jacobian`, `Coordinates`;
* the base change of `Ω¹`, in particular to the fibres.

The injectivity in II.4.3 (i) and the isomorphism of II.4.6, which need the sections of
`f^* Ω¹_{Y/Z}` on affine opens, are in `SGA.SGA1.ExposeII.SheafDifferentials`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace SGA.SGA1.ExposeII

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- II, formula (4.2 bis), for schemes: `f^* Ω¹_{Y/Z} → Ω¹_{X/Z} → Ω¹_{X/Y} → 0` is exact. -/
theorem exact_relativeDifferentials :
    (f.relativeDifferentialsShortComplex g).Exact ∧ Epi (f.relativeDifferentialsMap g) :=
  f.relativeDifferentialsShortComplex_exact g

/-- II.4.1, for schemes: `f` is (formally) unramified iff `f^* Ω¹_{Y/Z} → Ω¹_{X/Z}` is an
epimorphism, i.e. iff `Ω¹_{X/Y} = 0`. -/
theorem formallyUnramified_iff_epi_pullbackRelativeDifferentialsMap :
    FormallyUnramified f ↔ Epi (f.pullbackRelativeDifferentialsMap g) := by
  rw [← f.isZero_relativeDifferentials_iff]
  have h := (f.relativeDifferentialsShortComplex_exact g).1
  have key : Epi (f.pullbackRelativeDifferentialsMap g) ↔ f.relativeDifferentialsMap g = 0 :=
    h.epi_f_iff
  rw [key]
  refine ⟨fun hz ↦ hz.eq_of_tgt _ _, fun h0 ↦ ?_⟩
  have : Epi (0 : (f ≫ g).relativeDifferentials ⟶ f.relativeDifferentials) :=
    h0 ▸ inferInstance
  exact IsZero.of_epi_zero (f ≫ g).relativeDifferentials f.relativeDifferentials

/-- II.4.3 (ii), for schemes: if `f` is smooth, `Ω¹_{X/Y}` is locally free (`SGA.Foundations`). -/
theorem isLocallyFree_relativeDifferentials_of_smooth [Smooth f] :
    f.relativeDifferentials.IsLocallyFree :=
  inferInstance

/-- II.4.3 (ii), for schemes: if `f` is smooth of relative dimension `n`, then `Ω¹_{X/Y}` is free
of rank `n` on an affine open neighbourhood of every point (`SGA.Foundations`). -/
theorem exists_relativeDifferentials_restrict_iso_free (n : ℕ) [SmoothOfRelativeDimension n f]
    (x : X) : ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      Nonempty (f.relativeDifferentials.restrict hU.fromSpec ≅
        SheafOfModules.free (ULift.{u} (Fin n))) :=
  f.exists_relativeDifferentials_restrict_iso_free n x

/-- The sections of `Ω¹_{X/Y}` over an affine open `U ⊆ f⁻¹(V)`, `V` affine, are `Ω¹_{A/R}` for
`A = Γ(X, U)`, `R = Γ(Y, V)` (`SGA.Foundations`): the pointwise statements of II.4 on affine opens
are the ring-level statements of `SGA.SGA1.ExposeII.Differentials` and
`SGA.SGA1.ExposeII.Jacobian`. -/
noncomputable def relativeDifferentialsAppEquiv {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) :
    Γ(f.relativeDifferentials, U) ≃ₗ[Γ(X, U)] CommRingCat.KaehlerDifferential (f.appLE V U e) :=
  f.relativeDifferentialsAppEquiv hU hV e

/-- `Ω¹` commutes with base change (`SGA.Foundations`); in particular the restriction of
`Ω¹_{X/Y}` to a fibre `X_y` is `Ω¹_{X_y/κ(y)}`, as used in II.2.1 and II.4.10–II.4.13. -/
theorem nonempty_relativeDifferentials_baseChange_iso {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {h : Y' ⟶ Y} (H : IsPullback g' f' f h) :
    Nonempty ((Scheme.Modules.pullback g').obj f.relativeDifferentials ≅
      f'.relativeDifferentials) :=
  ⟨Scheme.Hom.relativeDifferentialsBaseChangeIso H⟩

end SGA.SGA1.ExposeII
