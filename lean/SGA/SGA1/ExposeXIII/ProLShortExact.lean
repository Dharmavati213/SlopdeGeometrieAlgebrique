/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.RegularLocalRing
import SGA.Foundations.Smooth.GeometricallyReduced
import SGA.SGA1.ExposeX.NormalCompleteLocalBase
import SGA.SGA1.ExposeX.SpecializationGeometric
import SGA.SGA1.ExposeXIII.ProperHomotopySequence

/-!
# SGA 1, Exposé XIII, 4.3–4.5 when `π₁(X_s̄) → π₁(X)` is injective

XIII.4.3 asserts that `1 → π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` is exact; the new point beyond
XIII.4.1 is the injectivity of `u : π₁^L(X_s̄) → π'₁(X)`. When the map `π₁(X_s̄) → π₁(X)` itself
is injective with image the kernel of `π₁(X) → π₁(S)` (the "full" homotopy exact sequence), `u`
is injective for **every** set of primes `L` (`isProLShortExact_of_injective`; a closed subgroup
`K` of `π₁(X)` meets `π'₁`'s kernel in the pro-`L` kernel of `K`).

This happens over a field (IX.6.1) and, more generally, at the geometric points over the closed
point of a local base when the étale coverings of the closed fibre lift to `X` (for a complete
noetherian local base this is X.2.1, IX.1.10, proved when `X` is projective and when `X` is integral
and normal, `SGA.SGA1.ExposeX.liftsFiniteEtale_fiberι_closedPoint_of_isNormalScheme`; the
injectivity is `SGA.SGA1.ExposeX.injective_map_closedFibre_of_completeLocal`).

XIII.4.3 itself is not stated in Lean (its hypotheses, cohomological properness in dimension `≤ 1`
for sheaves of `L`-groups, `1`-constructibility of the direct image of the stack of torsors and
local `1`-asphericity, have no definitions yet). The results below prove its conclusion, the
exactness of the sequence (XIII.4.3.1), under other hypotheses. We obtain:

* `isProLShortExact_of_liftsFiniteEtale`, `isProLShortExact_of_field`: the sequence (XIII.4.3.1)
  `1 → π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` is exact, for every `L`, for `f` proper, flat, with
  separable connected geometric fibres, at the closed point of a local base over which the étale
  coverings of the closed fibre lift, resp. over a field (no section and no smoothness are
  needed);
* `isProLShortExact_of_isNormalScheme`, `isProLShortExact_of_isRegularLocalRing`: the same at the
  closed point of a complete local base when `X` is normal (X.2.1 for normal `X`), in particular
  the second part of XIII.4.4 at the closed point of a complete regular local base;
* `properSmoothHomotopyExactSequence_of_field`: the second part of XIII.4.4
  (`ProperSmoothHomotopyExactSequenceStatement`) when `S` is the spectrum of a field (without
  the section);
* `exists_semidirectProduct_of_section_of_isProLShortExact` and its specializations: XIII.4.5,
  `π'₁(X) ≅ π₁^L(X_s̄) ⋊ π₁(S)` when a section is given (the decomposition records that the
  complement lifts `π₁(S)`; that it is the image of `π₁(g)` is not part of the statement).

At the geometric generic point of a complete discrete valuation ring with separably closed
residue field the conclusion follows from the core of X.3.8
(`SGA.SGA1.ExposeXIII.properSmoothHomotopyExactSequence_of_isDiscreteValuationRing`,
`SGA.SGA1.ExposeXIII.ProperSmoothTame`). The general second part of XIII.4.4 is open.
-/

universe u

namespace SGA.SGA1.ExposeXIII

open AlgebraicGeometry CategoryTheory Limits IsLocalRing

section Group

variable (L : Set ℕ) {G'' G' G : Type*} [Group G''] [Group G'] [Group G]
  [TopologicalSpace G''] [TopologicalSpace G'] [IsTopologicalGroup G']

omit [IsTopologicalGroup G'] in
/-- If `h' : π₁(X_s̄) → π₁(X)` is injective with image the kernel of `h : π₁(X) → π₁(S)`, then
`1 → π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` is exact as soon as `π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` is.
Here `h'` is a homeomorphism onto `ker h`, so the pro-`L` kernel of `ker h` (which contains
`(primeKernel L h).comap h'`) is the image of that of `π₁(X_s̄)`. -/
theorem isProLShortExact_of_injective [CompactSpace G''] [T2Space G'] (h' : G'' →* G')
    (h : G' →* G) (hh' : Continuous h') (hex : IsProLExact L h' h)
    (hinj : Function.Injective h') (hr : h'.range = h.ker) :
    IsProLShortExact L h' h := by
  refine ⟨hex, ?_⟩
  have hmem (x : G'') : h' x ∈ h.ker := hr ▸ ⟨x, rfl⟩
  let k : G'' →* h.ker := h'.codRestrict h.ker hmem
  have hk : Continuous k := hh'.subtype_mk _
  have hbij : Function.Bijective k := by
    refine ⟨fun x y hxy ↦ hinj (congrArg Subtype.val hxy), fun y ↦ ?_⟩
    have hy : (y : G') ∈ h'.range := by rw [hr]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let e : G'' ≃* h.ker := MulEquiv.ofBijective k hbij
  have he : Continuous e := hk
  let t := he.homeoOfEquivCompactToT2 (f := e.toEquiv)
  have hsymm : Continuous e.symm := t.symm.continuous
  rintro x ⟨y, hy, hyx⟩
  have := proLKernel_le_comap L e.symm.toMonoidHom hsymm hy
  have hey : e.symm y = x := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact Subtype.ext hyx
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hey] at this

/-- Replace the normal factor `A` of a semidirect product decomposition `A ⋊ C ≃* B` by an
isomorphic group. -/
theorem exists_semidirectProduct_congr_left {A A' C B : Type*} [Group A] [Group A'] [Group C]
    [Group B] {φ : C →* MulAut A} (e : A ⋊[φ] C ≃* B) (fn : A' ≃* A) :
    ∃ (φ' : C →* MulAut A') (e' : A' ⋊[φ'] C ≃* B),
      (∀ x, e' (SemidirectProduct.inl x) = e (SemidirectProduct.inl (fn x))) ∧
      ∀ c, e' (SemidirectProduct.inr c) = e (SemidirectProduct.inr c) :=
  ⟨_, (SemidirectProduct.congr' (φ₁ := φ) fn.symm (MulEquiv.refl C)).symm.trans e,
    fun _ ↦ rfl, fun _ ↦ congrArg e (SemidirectProduct.ext (map_one fn.symm.symm) rfl)⟩

end Group

section Section

/-- XIII.4.5: let `f` be proper, flat, with separable connected geometric fibres over a connected
locally noetherian `S`, with a section `g`, and `a` a geometric point of `X_s̄` lying on `g(S)`. If
`1 → π₁^L(X_s̄, a) → π'₁(X, a) → π₁(S, a) → 1` is exact (the conclusion (XIII.4.3.1) of
XIII.4.3), then `π'₁(X, a)` is a semidirect product of `π₁(S, a)` by `π₁^L(X_s̄, a)`: the normal
factor is the image of `π₁^L(X_s̄, a)` and the complement maps onto `π₁(S, a)` by the identity
(the statement does not record that the complement is the image of `π₁(g)`). -/
theorem exists_semidirectProduct_of_section_of_isProLShortExact (L : Set ℕ) {X S : Scheme.{u}}
    (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyConnected f] [GeometricallyReduced f]
    [IsLocallyNoetherian S] [ConnectedSpace S] (g : S ⟶ X) (hgf : g ≫ f = 𝟙 S) (Ω₀ : Type u)
    [Field Ω₀] [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ S) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f s)
    (ha : ((a ≫ pullback.fst f s) ≫ f) ≫ g = a ≫ pullback.fst f s)
    (hex : IsProLShortExact L (FundamentalGroup.map (pullback.fst f s) a)
      (FundamentalGroup.map f (a ≫ pullback.fst f s))) :
    ∃ (φ : FundamentalGroup ((a ≫ pullback.fst f s) ≫ f) →*
        MulAut (ProLQuotient L (FundamentalGroup a)))
      (e : ProLQuotient L (FundamentalGroup a) ⋊[φ] FundamentalGroup ((a ≫ pullback.fst f s) ≫ f)
        ≃* PrimeQuotient L (FundamentalGroup.map f (a ≫ pullback.fst f s))),
      (∀ x, e (SemidirectProduct.inl x) = proLToPrimeQuotient L
        (FundamentalGroup.map (pullback.fst f s) a) (FundamentalGroup.map f _)
        (FundamentalGroup.continuous_map _ _) hex.1.1 x) ∧
      ∀ c, primeQuotientLift L (FundamentalGroup.map f (a ≫ pullback.fst f s))
        (e (SemidirectProduct.inr c)) = c := by
  obtain ⟨hcomp, φ, e, he₁, he₂⟩ :=
    exists_semidirectProduct_of_section L f g hgf Ω₀ s Ω a ha
  have hinj := ((isProLShortExact_iff _ _ (FundamentalGroup.continuous_map _ _) hcomp).mp hex).1
  obtain ⟨φ', e', he₁', he₂'⟩ := exists_semidirectProduct_congr_left e (MonoidHom.ofInjective hinj)
  refine ⟨φ', e', fun x ↦ ?_, fun c ↦ ?_⟩
  · rw [he₁', he₁]
    rfl
  · rw [he₂', he₂]

end Section

section LocalBase

variable (R : Type u) [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  [IsProper f] [GeometricallyConnected f]

/-- IX.6.1 at the closed point of a local base: let `R` be a local ring, `f : X ⟶ Spec R` proper
with geometrically connected fibres, and assume that the étale coverings of the closed fibre `X₀`
lift to `X` (this is X.2.1, IX.1.10 when `R` is complete noetherian: proved when `X` is projective
and when `X` is integral and normal,
`SGA.SGA1.ExposeX.liftsFiniteEtale_fiberι_closedPoint_of_isNormalScheme`;
`SGA.SGA1.ExposeX.CompleteLocalBaseStatement` in general). Then for every geometric point `s̄` over
the closed point, `π₁(X_s̄) → π₁(X)` is injective. -/
theorem injective_map_fst_of_liftsFiniteEtale
    (hlift : ExposeIX.LiftsFiniteEtale (f.fiberι (closedPoint R))) (Ω₀ : Type u) [Field Ω₀]
    [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ Spec (.of R))
    (hs : ∀ x, s.base x = closedPoint R) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f s) :
    Function.Injective (FundamentalGroup.map (pullback.fst f s) a) := by
  obtain ⟨y, _, rfl⟩ := exists_eq_comp_geometricPoint Ω₀ s
  obtain rfl : y = ExposeX.closedPt R := by
    obtain ⟨x⟩ : Nonempty (Spec (.of Ω₀)) := inferInstance
    rw [ExposeX.closedPt, ← hs x]
    exact (Scheme.fromSpecResidueField_apply y _).symm
  exact ExposeX.injective_map_closedFibre_of_completeLocal R f Ω₀ hlift Ω a

/-- The conclusion (XIII.4.3.1) of XIII.4.3 at the closed point of a local base, for every set of
primes `L`, under a lifting hypothesis instead of XIII.4.3's (no section, no cohomological
hypotheses): with `R`, `f` as in `injective_map_fst_of_liftsFiniteEtale`, `R` noetherian, `f`
moreover flat with geometrically reduced fibres, and the étale coverings of the closed fibre
lifting to `X`, the sequence `1 → π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` is exact at every geometric
point `s̄` over the closed point. -/
theorem isProLShortExact_of_liftsFiniteEtale [IsNoetherianRing R] (L : Set ℕ) [Flat f]
    [GeometricallyReduced f]
    (hlift : ExposeIX.LiftsFiniteEtale (f.fiberι (closedPoint R))) (Ω₀ : Type u) [Field Ω₀]
    [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ Spec (.of R))
    (hs : ∀ x, s.base x = closedPoint R) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f s) :
    IsProLShortExact L (FundamentalGroup.map (pullback.fst f s) a)
      (FundamentalGroup.map f (a ≫ pullback.fst f s)) := by
  obtain ⟨-, -, hr⟩ := properHomotopyExactSequenceFull f Ω₀ s Ω a
  exact isProLShortExact_of_injective L _ _ (FundamentalGroup.continuous_map _ _)
    (properHomotopyExactSequence L f Ω₀ s Ω a)
    (injective_map_fst_of_liftsFiniteEtale R f hlift Ω₀ s hs Ω a) hr

/-- The conclusion (XIII.4.3.1) of XIII.4.3 at the closed point of a complete local base, for `X`
normal (no section, no cohomological hypotheses): with `R` a complete noetherian local ring and
`f : X ⟶ Spec R` proper, flat, with separable connected geometric fibres and `X` normal, the
sequence `1 → π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` is exact at
every geometric point `s̄` over the closed point, for every set of primes `L` (the lifting of
étale coverings from the closed fibre is X.2.1 for normal `X`,
`SGA.SGA1.ExposeX.liftsFiniteEtale_fiberι_closedPoint_of_isNormalScheme`). -/
theorem isProLShortExact_of_isNormalScheme [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (L : Set ℕ) [Flat f] [GeometricallyReduced f]
    (hX : ExposeX.IsNormalScheme X) (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀]
    (s : Spec (.of Ω₀) ⟶ Spec (.of R)) (hs : ∀ x, s.base x = closedPoint R) (Ω : Type u)
    [Field Ω] [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback f s) :
    IsProLShortExact L (FundamentalGroup.map (pullback.fst f s) a)
      (FundamentalGroup.map f (a ≫ pullback.fst f s)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_universally_isQuotientMap f
    (ExposeIX.universally_isQuotientMap_of_universallyClosed f)
  have : IsIntegral X := ExposeX.isIntegral_of_isNormalScheme hX
  exact isProLShortExact_of_liftsFiniteEtale R f L
    (ExposeX.liftsFiniteEtale_fiberι_closedPoint_of_isNormalScheme R f hX) Ω₀ s hs Ω a

end LocalBase

/-- XIII.4.4, second part, over a complete regular local base, at the closed point (and for every
set of primes `L`, without the section): let `R` be a complete regular local ring and
`f : X ⟶ Spec R` proper and smooth with geometrically connected fibres. Then
`1 → π₁^L(X_s̄) → π'₁(X) → π₁(S) → 1` is exact at every geometric point `s̄` over the closed
point. (`X` is regular, hence normal, so X.2.1 applies.) -/
theorem isProLShortExact_of_isRegularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    [Smooth f] [GeometricallyConnected f] (L : Set ℕ) (Ω₀ : Type u) [Field Ω₀]
    [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ Spec (.of R)) (hs : ∀ x, s.base x = closedPoint R)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback f s) :
    IsProLShortExact L (FundamentalGroup.map (pullback.fst f s) a)
      (FundamentalGroup.map f (a ≫ pullback.fst f s)) := by
  exact isProLShortExact_of_isNormalScheme R f L
    (ExposeX.isNormalScheme_of_isRegularScheme (ExposeX.isRegularScheme_of_smooth R f)) Ω₀ s hs Ω a

section Field

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  [GeometricallyConnected f]

/-- IX.6.1 at every geometric point: for `f : X ⟶ Spec k` proper with geometrically connected
fibres and any geometric point `s̄ : Spec Ω₀ ⟶ Spec k` (`Ω₀` algebraically closed),
`π₁(X_s̄) → π₁(X)` is injective. -/
theorem injective_map_fst_of_field (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀]
    (s : Spec (.of Ω₀) ⟶ Spec (.of k)) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f s) :
    Function.Injective (FundamentalGroup.map (pullback.fst f s) a) :=
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  injective_map_fst_of_liftsFiniteEtale k f (ExposeIX.liftsFiniteEtale_fiberι_of_subsingleton f _)
    Ω₀ s (fun _ ↦ Subsingleton.elim _ _) Ω a

/-- The conclusion (XIII.4.3.1) of XIII.4.3 over a field, for every set of primes `L`: for
`f : X ⟶ Spec k` proper, flat, with separable connected geometric fibres, the sequence
`1 → π₁^L(X_s̄) → π'₁(X) → π₁(k) → 1` is exact at every geometric point `s̄` (from IX.6.1; no
section, no smoothness and none of XIII.4.3's cohomological hypotheses are needed). -/
theorem isProLShortExact_of_field (L : Set ℕ) [Flat f] [GeometricallyReduced f]
    (Ω₀ : Type u) [Field Ω₀] [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ Spec (.of k))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback f s) :
    IsProLShortExact L (FundamentalGroup.map (pullback.fst f s) a)
      (FundamentalGroup.map f (a ≫ pullback.fst f s)) :=
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  isProLShortExact_of_liftsFiniteEtale k f L (ExposeIX.liftsFiniteEtale_fiberι_of_subsingleton f _)
    Ω₀ s (fun _ ↦ Subsingleton.elim _ _) Ω a

/-- XIII.4.4, second part, when `S = Spec k` is the spectrum of a field
(`ProperSmoothHomotopyExactSequenceStatement` restricted to such `S`), without the section:
for `f : X ⟶ Spec k` proper and smooth with geometrically connected fibres, the sequence
`1 → π₁^L(X_s̄) → π'₁(X) → π₁(k) → 1` is exact, `L` the primes different from `char k`. -/
theorem properSmoothHomotopyExactSequence_of_field [Smooth f] (Ω₀ : Type u) [Field Ω₀]
    [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ Spec (.of k)) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (a : Spec (.of Ω) ⟶ pullback f s) :
    IsProLShortExact (primesInvertibleOn (Spec (.of k)))
      (FundamentalGroup.map (pullback.fst f s) a)
      (FundamentalGroup.map f (a ≫ pullback.fst f s)) :=
  isProLShortExact_of_field k f _ Ω₀ s Ω a

/-- XIII.4.5 over a field: for `f : X ⟶ Spec k` proper, flat, with separable connected geometric
fibres and a section `g`, and `a` a geometric point of `X_s̄` on `g(Spec k)`, `π'₁(X, a)` is a
semidirect product of `π₁(Spec k, a)` by `π₁^L(X_s̄, a)`, for every set of primes `L` (as in
`exists_semidirectProduct_of_section_of_isProLShortExact`, the complement is only recorded to lift
`π₁(Spec k, a)`). -/
theorem exists_semidirectProduct_of_section_of_field (L : Set ℕ) [Flat f]
    [GeometricallyReduced f] (g : Spec (.of k) ⟶ X) (hgf : g ≫ f = 𝟙 _) (Ω₀ : Type u)
    [Field Ω₀] [IsAlgClosed Ω₀] (s : Spec (.of Ω₀) ⟶ Spec (.of k)) (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback f s)
    (ha : ((a ≫ pullback.fst f s) ≫ f) ≫ g = a ≫ pullback.fst f s) :
    ∃ (φ : FundamentalGroup ((a ≫ pullback.fst f s) ≫ f) →*
        MulAut (ProLQuotient L (FundamentalGroup a)))
      (e : ProLQuotient L (FundamentalGroup a) ⋊[φ] FundamentalGroup ((a ≫ pullback.fst f s) ≫ f)
        ≃* PrimeQuotient L (FundamentalGroup.map f (a ≫ pullback.fst f s))),
      (∀ x, e (SemidirectProduct.inl x) = proLToPrimeQuotient L
        (FundamentalGroup.map (pullback.fst f s) a) (FundamentalGroup.map f _)
        (FundamentalGroup.continuous_map _ _)
        (isProLShortExact_of_field k f L Ω₀ s Ω a).1.1 x) ∧
      ∀ c, primeQuotientLift L (FundamentalGroup.map f (a ≫ pullback.fst f s))
        (e (SemidirectProduct.inr c)) = c :=
  exists_semidirectProduct_of_section_of_isProLShortExact L f g hgf Ω₀ s Ω a ha
    (isProLShortExact_of_field k f L Ω₀ s Ω a)

end Field

end SGA.SGA1.ExposeXIII
