/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.FiniteEtaleAlgebraization
import SGA.Foundations.Cohomology.ProperFiniteness
import SGA.Foundations.Cohomology.SteinAlgebraization
import SGA.Foundations.Cohomology.SteinFactorization
import SGA.Foundations.CommAlg.RegularLocalRing
import SGA.Foundations.Projective.Chow
import SGA.SGA1.ExposeI.DominantUnramified
import SGA.SGA1.ExposeII.Permanence
import SGA.SGA1.ExposeIX.ExactSequenceCompleteLocal
import SGA.SGA1.ExposeX.PurityDenseOpen
import SGA.SGA1.ExposeX.Semicontinuity

/-!
# SGA 1, Exposé X, 2.1 for a normal scheme over a complete local ring

X.2.1 (IX.1.10): for `A` a complete noetherian local ring and `X` proper over `Spec A` with closed
fibre `X₀`, base change `X' ↦ X' ×_X X₀` is an equivalence of the categories of étale coverings.
The repository proves it for `X` projective over `A`
(`isEquivalence_pullback_closedFibreInclusion_of_isClosedImmersion`); the general case is
`CompleteLocalBaseStatement`, which rests on Grothendieck's existence theorem for proper
morphisms.

We prove it when `X` is **integral and normal**, by Chow's lemma (EGA II 5.6.1): there is a
proper birational `p : X' ⟶ X` with `X'` projective over `A`. Since `X` is normal,
`p_* 𝒪_{X'} = 𝒪_X` (`app_bijective_of_isNormalScheme`: `Γ(X', p⁻¹ V)` is finite over `Γ(X, V)`
and contained in the function field, so equal to `Γ(X, V)`, which is integrally closed), and the
algebraization of formal étale coverings descends from `X'` to `X` along such a `p`
(`AlgebraicGeometry.CohomologyAux.formalAlgebraizable_of_stein`; EGA III 5.1.4 via Chow's lemma).

This covers every `X` smooth over a regular complete local ring (then `X` is regular, hence
normal; an integral `X` is the case `X` connected).

## Main results

* `isIntegral_of_isDomain_stalk`, `isIntegral_of_isNormalScheme`, `isIntegral_of_isRegularScheme`:
  a connected locally noetherian scheme whose local rings are domains is integral (a corollary of
  `SGA.SGA1.ExposeI.irreducibleSpace_of_isDomain_stalk`; so X.2.1 below applies to every connected
  normal `X`); `isRegularScheme_of_smooth`, `isIntegral_and_isNormalScheme_of_smooth`: a (connected)
  scheme smooth over a regular local ring is regular (integral and normal).
* `app_bijective_of_isNormalScheme`: a proper surjection `p : X' ⟶ X` of integral schemes which
  is an isomorphism over a nonempty open, onto a normal locally noetherian `X`, induces
  `Γ(X, V) ≅ Γ(X', p⁻¹ V)` for every affine open `V` (EGA III 4.3.12, the case `p_* 𝒪 = 𝒪`).
* `essSurj_pullback_thickening_of_isNormalScheme` and
  `isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme`: X.2.1 for `X` integral and
  normal.
* `liftsFiniteEtale_fiberι_closedPoint_of_isNormalScheme`: the lifting of étale coverings from the
  closed fibre (the hypothesis `hlift` of X.2.2 and of
  `SGA.SGA1.ExposeX.injective_map_closedFibre_of_completeLocal`) for such `X`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing Topology

namespace SGA.SGA1.ExposeX

section Integral

/-- A connected locally noetherian scheme whose local rings are domains is integral: it is
irreducible (`SGA.SGA1.ExposeI.irreducibleSpace_of_isDomain_stalk`) and reduced. -/
theorem isIntegral_of_isDomain_stalk {X : Scheme.{u}} [IsLocallyNoetherian X] [ConnectedSpace X]
    (h : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IsIntegral X := by
  have : IrreducibleSpace X := ExposeI.irreducibleSpace_of_isDomain_stalk h
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := have := h x; inferInstance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- A connected, locally noetherian, normal scheme is integral. -/
theorem isIntegral_of_isNormalScheme {X : Scheme.{u}} [IsLocallyNoetherian X] [ConnectedSpace X]
    (hX : IsNormalScheme X) : IsIntegral X :=
  isIntegral_of_isDomain_stalk fun x ↦ (hX x).1

/-- A connected, locally noetherian, regular scheme is integral. -/
theorem isIntegral_of_isRegularScheme {X : Scheme.{u}} [IsLocallyNoetherian X] [ConnectedSpace X]
    (hX : IsRegularScheme X) : IsIntegral X :=
  isIntegral_of_isNormalScheme (isNormalScheme_of_isRegularScheme hX)

/-- A scheme smooth over a regular local ring is regular (II.5.3 at every point). -/
theorem isRegularScheme_of_smooth (R : Type u) [CommRing R] [IsRegularLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f] : IsRegularScheme X :=
  ExposeII.isRegularLocalRing_stalk_of_smooth f fun p ↦
    IsRegularLocalRing.of_ringEquiv (Spec.stalkIso (.of R) p).commRingCatIsoToRingEquiv.symm

/-- A connected scheme smooth over a regular local ring (for instance over a field) is integral and
normal: it is regular. -/
theorem isIntegral_and_isNormalScheme_of_smooth (R : Type u) [CommRing R] [IsRegularLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f] [ConnectedSpace X] :
    IsIntegral X ∧ IsNormalScheme X := by
  have hreg := isRegularScheme_of_smooth R f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact ⟨isIntegral_of_isRegularScheme hreg, isNormalScheme_of_isRegularScheme hreg⟩

end Integral

section Normal

variable {X X' : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X] [IsIntegral X']

set_option backward.isDefEq.respectTransparency false in
/-- A proper birational morphism onto a normal scheme has `p_* 𝒪_{X'} = 𝒪_X` (EGA III 4.3.12,
Hartshorne III.11.4): let `p : X' ⟶ X` be a proper surjective morphism of integral schemes, `X`
locally noetherian and normal, which is an isomorphism over a nonempty open `U`. Then
`p^♯ : Γ(X, V) → Γ(X', p⁻¹ V)` is bijective for every affine open `V`. Indeed `Γ(X', p⁻¹ V)` is
integral over `Γ(X, V)` (EGA III 3.2.1), and it embeds into the function field of `X` through
`p⁻¹(U ∩ V) ≅ U ∩ V`; `Γ(X, V)` is integrally closed in its fraction field. -/
theorem app_bijective_of_isNormalScheme (hX : IsNormalScheme X) (p : X' ⟶ X) [IsProper p]
    [Surjective p] (U : X.Opens) (hU : (U : Set X).Nonempty) (hiso : IsIso (p ∣_ U))
    (V : X.Opens) (hV : IsAffineOpen V) : Function.Bijective (p.app V) := by
  by_cases hVne : (V : Set X).Nonempty
  swap
  · obtain rfl : V = ⊥ := by
      ext x
      simpa using fun hx ↦ hVne ⟨x, hx⟩
    have : Subsingleton Γ(X', p ⁻¹ᵁ ⊥) := by
      rw [Scheme.Hom.preimage_bot]
      infer_instance
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  have : Nonempty V := hVne.to_subtype
  -- `W = U ∩ V`, written as the image of an open of `U`
  let W : X.Opens := U.ι ''ᵁ (U.ι ⁻¹ᵁ V)
  have hWV : W ≤ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  obtain ⟨x, hxV, hxU⟩ := nonempty_preirreducible_inter V.2 U.2 hVne hU
  have : Nonempty W := ⟨⟨x, ⟨⟨x, hxU⟩, hxV, rfl⟩⟩⟩
  have : Nonempty (p ⁻¹ᵁ W) := by
    obtain ⟨y, hy⟩ := p.surjective x
    exact ⟨⟨y, by rw [Scheme.Hom.mem_preimage, hy]; exact ⟨⟨x, hxU⟩, hxV, rfl⟩⟩⟩
  have : IsIso (p.app W) := by
    have h : IsIso ((p ∣_ U).app (U.ι ⁻¹ᵁ V)) := inferInstance
    rw [morphismRestrict_app] at h
    exact IsIso.of_isIso_comp_right (p.app W)
      (X'.presheaf.map (eqToHom (image_morphismRestrict_preimage p U (U.ι ⁻¹ᵁ V))).op)
  -- the restriction maps and `e : Γ(X, W) ≅ Γ(X', p⁻¹ W)`
  let r := X.presheaf.map (homOfLE hWV).op
  let r' := X'.presheaf.map (homOfLE (p.preimage_mono hWV)).op
  have hr : Function.Injective r := map_injective_of_isIntegral X _
  have hr' : Function.Injective r' := map_injective_of_isIntegral X' _
  have hnat (a : Γ(X, V)) : p.app W (r a) = r' (p.app V a) :=
    CohomologyAux.app_map_apply p hWV a
  let e : Γ(X, W) ≃+* Γ(X', p ⁻¹ᵁ W) := (asIso (p.app W)).commRingCatIsoToRingEquiv
  have he (c : Γ(X, W)) : e c = p.app W c := rfl
  refine ⟨fun a b hab ↦ hr (e.injective ?_), fun b ↦ ?_⟩
  · rw [he, he, hnat, hnat, hab]
  -- surjectivity: `b` is integral over `Γ(X, V)` and lies in the function field
  have := isIntegrallyClosed_of_isAffineOpen hX hV
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  let _ := (p.app V).hom.toAlgebra
  have := CohomologyAux.isIntegral_app_of_isProper p hV
  let θ : Γ(X', p ⁻¹ᵁ V) →+* X.functionField :=
    (X.germToFunctionField W).hom.comp (e.symm.toRingHom.comp r'.hom)
  have hθ (a : Γ(X, V)) : θ (p.app V a) = X.germToFunctionField V a := by
    change X.germToFunctionField W (e.symm (r' (p.app V a))) = _
    rw [← hnat, ← he, RingEquiv.symm_apply_apply]
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  let θa : Γ(X', p ⁻¹ᵁ V) →ₐ[Γ(X, V)] X.functionField := { θ with commutes' := hθ }
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    ((Algebra.IsIntegral.isIntegral (R := Γ(X, V)) b).map θa)
  refine ⟨a, hr' ?_⟩
  have hra : r a = e.symm (r' b) := by
    apply X.germToFunctionField_injective W
    change _ = θ b
    rw [TopCat.Presheaf.germ_res_apply]
    exact ha
  rw [← hnat, ← he, hra, RingEquiv.apply_symm_apply]

end Normal

section CompleteLocal

open CohomologyAux Scheme in
/-- X.2.1 (IX.1.10), essential surjectivity along the first thickening `X ⊗_A A/𝔪 ⟶ X`, for `X`
integral and normal: let `A` be a complete noetherian local ring and `X` integral, normal and
proper over `Spec A`. Then every étale covering of `X ⊗_A A/𝔪` extends to `X`. From Chow's lemma
(`exists_isHProjective_of_isProper`), the projective case of the existence theorem
(`formalAlgebraizable_of_isClosedImmersion`) and its descent along `p` with `p_* 𝒪 = 𝒪`
(`formalAlgebraizable_of_stein`, `app_bijective_of_isNormalScheme`). -/
theorem essSurj_pullback_thickening_of_isNormalScheme (A : CommRingCat.{u}) [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] {X : Scheme.{u}} (f : X ⟶ Spec A)
    [IsProper f] [IsIntegral X] (hX : IsNormalScheme X) :
    (FiniteEtale.pullback (thickening.ι f (maximalIdeal A) 0)).EssSurj := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨X', p, U, hp, hsurj, hpf, hU, hiso, hX'⟩ := exists_isHProjective_of_isProper f
  obtain ⟨σ, _, κ, hκ, hκf⟩ := hpf.exists_isClosedImmersion
  have h' : FormalAlgebraizable (maximalIdeal A) (p ≫ f) :=
    formalAlgebraizable_of_isClosedImmersion (maximalIdeal A) (p ≫ f) κ hκf.symm
  have : IsAffineHom (pullback.diagonal (terminal.from X')) :=
    isAffineHom_diagonal_of_isSeparated (p ≫ f)
  have hXf := formalAlgebraizable_of_stein (maximalIdeal A) f p
    (app_bijective_of_isNormalScheme hX p U hU hiso) h'
  exact essSurj_pullback_thickening_of_formalAlgebraizable (maximalIdeal A) f
    ExposeIX.finiteEtale_h83 hXf

/-- **X.2.1 for `X` integral and normal** (IX.1.10): let `A` be a complete noetherian local ring
and `X` an integral normal scheme, proper over `Spec A`, with closed fibre `X₀`. Then
`X' ↦ X' ×_X X₀` is an equivalence from the étale coverings of `X` to those of `X₀`. -/
theorem isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsIntegral X] (hX : IsNormalScheme X) :
    (FEt.pullback (closedFibreInclusion A f)).IsEquivalence :=
  ExposeIX.isEquivalence_pullback_closedFibre_of_essSurj A f
    (essSurj_pullback_thickening_of_isNormalScheme (.of A) f hX)

/-- X.2.1 for `X` integral and normal: for every geometric point `t` of the closed fibre `X₀`,
`π₁(X₀, t) → π₁(X, t)` is bijective. -/
theorem bijective_map_of_isNormalScheme (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsIntegral X] (hX : IsNormalScheme X) (Ω : Type u)
    [Field Ω] (t : Spec (.of Ω) ⟶ pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap A (ResidueField A))))) :
    Function.Bijective (ExposeV.etaleFundamentalGroup.map Ω (closedFibreInclusion A f) t) :=
  have := isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme A f hX
  ExposeV.autMap_bijective _ _

set_option backward.isDefEq.respectTransparency false in
/-- X.2.1 for `X` integral and normal gives the lifting of étale coverings from the closed fibre
`X ×_{Spec A} Spec κ(𝔪)` used in X.2.2 (`ExposeIX.LiftsFiniteEtale`). -/
theorem liftsFiniteEtale_fiberι_closedPoint_of_isNormalScheme (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] [IsIntegral X] (hX : IsNormalScheme X) :
    ExposeIX.LiftsFiniteEtale (f.fiberι (closedPoint A)) :=
  have : (MorphismProperty.Over.pullback ExposeV.finiteEtaleHom ⊤
      (pullback.fst f (ExposeIX.specQuotient (maximalIdeal A)))).IsEquivalence :=
    isEquivalence_pullback_closedFibreInclusion_of_isNormalScheme A f hX
  ExposeIX.liftsFiniteEtale_fiberι_closedPoint A f

end CompleteLocal

end SGA.SGA1.ExposeX
