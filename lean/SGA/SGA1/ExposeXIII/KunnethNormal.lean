/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeII.PermanenceSmooth

/-!
# Normality for the Künneth formula XIII.4.6: smooth over normal is normal (II.3.1)

In the main lemma of the resolution-free proof of XIII.4.6 in characteristic `0`
(`SGA.SGA1.ExposeXIII.bijective_map_prod_of_isNormalScheme_of_invariance`), normality of
`X ×ₖ T` is used only to make every connected étale covering of `X ×ₖ T` irreducible (it is
normal by I.9.10, `SGA.SGA1.ExposeXIII.irreducibleSpace_left_of_isNormalScheme`), so that its
generic fibre over `X` is connected. There `X` is normal and `T` is smooth over `k`, so
`X ×ₖ T → X` is smooth, and normality ascends along smooth morphisms: this is the "normal, ascent"
branch of II.3.1 (`SGA.SGA1.ExposeII.isSmoothAt_permanence`,
`SGA.SGA1.ExposeII.permanence_of_mem_smoothLocus` in `SGA/SGA1/ExposeII/PermanenceSmooth.lean`).
Those are stated over a locally noetherian base, which II.3.1 needs for the regular case only; we
record the normal ascent without that hypothesis, as a corollary of the same ring-level lemmas
(`ExposeII.IsSmoothAt.of_smooth_localizationAtPrime`,
`ExposeII.isDomain_and_isIntegrallyClosed_localization_of_smooth`):

* `isDomain_and_isIntegrallyClosed_localization_of_isSmoothAt` (affine, pointwise);
* `isNormalScheme_of_smooth_of_isNormalScheme` (scheme level).

Normality is `ExposeI.IsNormalScheme`; `ExposeX.IsNormalScheme` has the same body, so the result
applies to it by `id`.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace SGA.SGA1.ExposeXIII

open Algebra in
/-- II.3.1 (normal, ascent), affine pointwise form, without the noetherian hypothesis: let `S` be
of finite presentation over `R`, smooth over `R` at the prime `Q`, over `p = Q ∩ R`. If `R_p` is
an integrally closed domain, so is `S_Q`. -/
theorem isDomain_and_isIntegrallyClosed_localization_of_isSmoothAt {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [FinitePresentation R S] (Q : Ideal S) [Q.IsPrime]
    [IsSmoothAt R Q]
    (hp : IsDomain (Localization.AtPrime (Q.under R)) ∧
      IsIntegrallyClosed (Localization.AtPrime (Q.under R))) :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  obtain ⟨_, _⟩ := hp
  exact ExposeII.IsSmoothAt.of_smooth_localizationAtPrime (R := R) Q
    (fun T _ ↦ IsDomain T ∧ IsIntegrallyClosed T)
    (fun T T' _ _ e h ↦ ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv e h)
    fun S' _ _ _ Q' _ _ ↦ ExposeII.isDomain_and_isIntegrallyClosed_localization_of_smooth
      (A := Localization.AtPrime (Q.under R)) Q'

/-- II.3.1 (normal, ascent), without the noetherian hypothesis: if `f : X ⟶ Y` is smooth and the
local rings of `Y` are integrally closed domains, so are those of `X` (EGA IV 6.5.4, 17.5.7;
Stacks 033C). For `Y` locally noetherian this is `ExposeII.permanence_of_mem_smoothLocus`. -/
theorem isNormalScheme_of_smooth_of_isNormalScheme {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (hY : ExposeI.IsNormalScheme Y) : ExposeI.IsNormalScheme X := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have hx : x ∈ f.smoothLocus := by
    rw [f.smoothLocus_eq_top]
    trivial
  have : Algebra.IsSmoothAt Γ(Y, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    (formallySmooth_stalkMap_iff U hU V hV hVU hxV).mp hx
  have hpq : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.under Γ(Y, U) =
      (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).1)
  have hp := ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv
    (ExposeI.stalkEquivLocalization hU (f x) (hVU hxV)) (hY (f x))
  exact ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv
    (ExposeI.stalkEquivLocalization hV x hxV).symm
    (isDomain_and_isIntegrallyClosed_localization_of_isSmoothAt _
      (ExposeI.isDomain_and_isIntegrallyClosed_localization_congr hpq.symm hp))

end SGA.SGA1.ExposeXIII
