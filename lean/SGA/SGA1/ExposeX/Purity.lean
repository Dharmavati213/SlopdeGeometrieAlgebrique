/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.EtaleCoverings
import SGA.SGA1.ExposeX.GaloisFunctors
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import SGA.Foundations.CommAlg.Purity
import SGA.Foundations.CommAlg.PuncturedSpectrum
import SGA.Foundations.CommAlg.PurityScheme
import SGA.Foundations.CommAlg.PurityQuasiFinite

/-!
# SGA 1, Exposé X, §3: the purity theorem and its consequences

The purity theorem of Zariski–Nagata is proved in all dimensions:

* X.3.2, local form (`localPurity`, and `formallyEtale_of_finite` for `B` finite over `A`): the
  algebraic core `IsRegularLocalRing.etale_of_isWeaklyRegular_of_two_le_ringKrullDim` is proved by
  induction on the dimension (`SGA.Foundations.CommAlg.PurityInduction`), using depth,
  Auslander–Buchsbaum and the discriminant in dimension `2`, and a hypersurface section, lifting of
  finite étale algebras over complete rings and a divisor argument in dimension `≥ 3`;
* X.3.1, global form (`purity` in `PurityTheorem`), from X.3.2 at the stalks;
* X.3.3 (`purityCoverings`, `isEquivalence_pullback_of_isRegularScheme`): étale coverings extend
  across closed subsets of codimension `≥ 2` of a regular scheme, by gluing the X.3.2 extensions
  with the relative normalization; with the isomorphism of fundamental groups
  (`bijective_autWhiskerLeft_of_isRegularScheme`), and the case `X = Spec A`, `U` the punctured
  spectrum (`isEquivalence_pullback_puncturedSpectrum`);
* X.3.4, birational invariance (`BirationalInvarianceStatement`, proved as `birationalInvariance`
  in `PurityBirational`): a rational map from a regular scheme to a proper one is defined in
  codimension `1` (valuative criterion), so X.3.3 applies; restriction of étale coverings to a
  dense open of a normal scheme is fully faithful (`PurityDenseOpen`).

The group theory of X.3.6 (Abhyankar's lemma) and of X.3.8 ⇒ X.3.9 is in `Specialization`.

X.3.8 is stated over a locally noetherian base in `TameSpecialization`
(`TameSpecializationStatement`) and proved over a complete discrete valuation ring with separably
closed residue field, for the closed and the generic point
(`exists_tameSpecialization_of_isDiscreteValuationRing`, `TameLiftingSpecialization`).

Not formalized: X.3.5 (remark), X.3.7 (a reformulation, via X.2.1, of the extension problem for
principal coverings), X.3.10 (it needs the transcendental computation X.2.6), X.3.11 (remark).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.PreGaloisCategory

namespace SGA.SGA1.ExposeX

/-- A scheme is *regular* if its local rings are regular local rings. -/
def IsRegularScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- A scheme is *normal* if its local rings are integrally closed domains. -/
def IsNormalScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

/-- A morphism is *étale at* `x` if it is étale on an open neighbourhood of `x`. -/
def EtaleAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)

/-- X.3.1, purity theorem of Zariski–Nagata (SGA 2 X.3.4; proved in `purity`). Let `f : X ⟶ Y` be a
quasi-finite dominant morphism of integral schemes, `X` normal and `Y` regular and locally
noetherian, and let `Z` be the set of points where `f` is not étale. If `Z ≠ X`, then `Z` has
codimension `1` at each of its points: the local ring of `X` at the generic point `z` of any
irreducible component of `Z` (a point of `Z` with no proper generization in `Z`) has
dimension `1`. -/
def PurityStatement : Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [IsDominant f] [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y],
    IsNormalScheme X → IsRegularScheme Y → {x : X | ¬ EtaleAt f x} ≠ Set.univ →
    ∀ z : X, ¬ EtaleAt f z → (∀ w : X, ¬ EtaleAt f w → w ⤳ z → w = z) →
      ringKrullDim (X.presheaf.stalk z) = 1

/-- X.3.2, the local form of X.3.1 (proved in `localPurity`). Let `A` be a regular local ring and
`A → B` an injective local homomorphism, with `B` a normal local ring, essentially of finite
type and quasi-finite over `A`. If `dim A ≥ 2` and `B` is étale over `A` at every non-maximal
prime of `B`, then `B` is étale over `A`. -/
def LocalPurityStatement : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [IsRegularLocalRing A] [IsLocalRing B] [IsDomain B]
    [IsIntegrallyClosed B] [Algebra A B] [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [Algebra.QuasiFinite A B], Function.Injective (algebraMap A B) → 2 ≤ ringKrullDim A →
    (∀ (p : Ideal B) [p.IsPrime], p ≠ IsLocalRing.maximalIdeal B → Algebra.IsEtaleAt A p) →
      Algebra.FormallyEtale A B

/-- X.3.2 for `B` finite over `A` (SGA 2 X.3.4; Stacks 0BMB). Let `A` be a regular local ring of
dimension `≥ 2` and `A → B` an injective finite homomorphism, with `B` a normal local domain. If `B`
is étale over `A` at every non-maximal prime of `B`, then `B` is étale over `A`. Compared with
`LocalPurityStatement`, `B` is finite (not only quasi-finite) over `A`; the general case is
`localPurity`.

The proof (`IsRegularLocalRing.etale_of_isIntegrallyClosed_of_two_le_ringKrullDim`) is by
induction on `dim A`. In dimension `2`, `B` has depth `2`, hence is free over `A` by
Auslander–Buchsbaum, and its discriminant is a unit away from the closed point, hence a unit
(I.4.10). In dimension `≥ 3` one completes `A`, cuts by a hypersurface `f ∉ 𝔪²`, lifts the
covering of `V(f)` given by induction to a finite étale `A`-algebra `C`, and compares `B` with `C`
through the `f`-adic thickenings (the Lefschetz argument of SGA 2 X.3.4, in algebraic form). -/
theorem formallyEtale_of_finite (A B : Type u) [CommRing A] [CommRing B]
    [IsRegularLocalRing A] [IsLocalRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B]
    [Module.Finite A B] (hinj : Function.Injective (algebraMap A B)) (hdim : 2 ≤ ringKrullDim A)
    (h : ∀ (p : Ideal B) [p.IsPrime], p ≠ IsLocalRing.maximalIdeal B → Algebra.IsEtaleAt A p) :
    Algebra.FormallyEtale A B := by
  have := IsRegularLocalRing.etale_of_isIntegrallyClosed_of_two_le_ringKrullDim hinj hdim
    fun q _ hq ↦ h q fun hqm ↦ hq ?_
  · infer_instance
  subst hqm
  have : (IsLocalRing.maximalIdeal B).comap (algebraMap A B) |>.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  exact IsLocalRing.eq_maximalIdeal this

/-- X.3.2, purity theorem of Zariski–Nagata, local form (SGA 2 X.3.4; Stacks 0BMB). Let `A` be a
regular local ring of dimension `≥ 2` and `A → B` an injective local homomorphism, with `B` a
normal local domain, essentially of finite type and quasi-finite over `A`. If `B` is étale over `A`
at every non-maximal prime, then `B` is étale over `A`.

As in SGA, one reduces to `B` finite over `A` by completing: `B` has dimension `≥ 2` (Zariski's
main theorem and going down), hence depth `≥ 2`; over the completion `Â` the local ring of
`Â ⊗_A B` is a localization of a finite `Â`-algebra, étale by the finite case, and étaleness
descends along the faithfully flat `A → Â` (`IsRegularLocalRing.formallyEtale_of_quasiFinite`). -/
theorem localPurity : LocalPurityStatement.{u} :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hinj hdim h ↦
    IsRegularLocalRing.formallyEtale_of_quasiFinite hinj hdim h

/-- X.3.3 (proved in `purityCoverings`). Let `X` be a regular locally noetherian scheme and `U` an
open subset whose complement has codimension `≥ 2` (every point `x ∉ U` has
`dim 𝒪_{X,x} ≥ 2`). Then `X' ↦ X' ×_X U` is an equivalence from the étale coverings of `X` to
those of `U`. -/
def PurityCoveringsStatement : Prop :=
  ∀ ⦃X : Scheme.{u}⦄ [IsLocallyNoetherian X], IsRegularScheme X → ∀ U : X.Opens,
    (∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x)) → (FEt.pullback U.ι).IsEquivalence

/-- X.3.3, last assertion (from the first, by V.6.10): in the situation of X.3.3, if the étale
coverings of `X` and `U` form Galois categories with compatible fibre functors (at a geometric
point of `U`), then `π₁(U) → π₁(X)` is an isomorphism. -/
theorem bijective_autWhiskerLeft_of_purity (h : PurityCoveringsStatement.{u}) {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hX : IsRegularScheme X) (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x)) [GaloisCategory (FEt X)]
    [GaloisCategory (FEt U)] {F : FEt X ⥤ FintypeCat.{u}} {F' : FEt U ⥤ FintypeCat.{u}}
    [FiberFunctor F] [FiberFunctor F'] (e : FEt.pullback U.ι ⋙ F' ≅ F) :
    Function.Bijective (autWhiskerLeft _ e) :=
  have := h hX U hU
  autWhiskerLeft_bijective_of_isEquivalence _ e

/-- X.3.3 (SGA 2 X.3.4; Stacks 0BMB). Let `X` be a regular locally noetherian scheme and `U` an open
subset whose complement has codimension `≥ 2`. Then `X' ↦ X' ×_X U` is an equivalence from the
étale coverings of `X` to those of `U`.

The inverse sends an étale covering `W` of `U` to the normalization of `X` in `W`; it is étale over
`X` by X.3.2 applied at the points of `X \ U`, on affine neighbourhoods `V` with a regular sequence
`a, b ∈ Γ(V)` vanishing on `V \ U` (`AlgebraicGeometry.exists_isWeaklyRegular_basicOpen_sup_le`),
and full faithfulness is Hartogs on such neighbourhoods
(`AlgebraicGeometry.isEquivalence_pullback_of_isRegularLocalRing`). -/
theorem isEquivalence_pullback_of_isRegularScheme {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : IsRegularScheme X) (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x)) :
    (FEt.pullback U.ι).IsEquivalence :=
  AlgebraicGeometry.isEquivalence_pullback_of_isRegularLocalRing U (fun x _ ↦ hX x) hU

/-- X.3.3: `PurityCoveringsStatement` holds. -/
theorem purityCoverings : PurityCoveringsStatement.{u} :=
  fun _ _ hX U hU ↦ isEquivalence_pullback_of_isRegularScheme hX U hU

/-- X.3.3, last assertion: if `X` is regular and locally noetherian and `X \ U` has codimension
`≥ 2`, then with compatible fibre functors on the étale coverings of `X` and of `U`, the map
`π₁(U) → π₁(X)` is an isomorphism. -/
theorem bijective_autWhiskerLeft_of_isRegularScheme {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : IsRegularScheme X) (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x))
    [GaloisCategory (FEt X)] [GaloisCategory (FEt U)] {F : FEt X ⥤ FintypeCat.{u}}
    {F' : FEt U ⥤ FintypeCat.{u}} [FiberFunctor F] [FiberFunctor F']
    (e : FEt.pullback U.ι ⋙ F' ≅ F) :
    Function.Bijective (autWhiskerLeft _ e) :=
  bijective_autWhiskerLeft_of_purity purityCoverings hX U hU e

/-- X.3.3 for regular schemes of dimension `≤ 2`, a special case of
`isEquivalence_pullback_of_isRegularScheme`. -/
theorem isEquivalence_pullback_of_isRegularScheme_of_ringKrullDim_le_two {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hX : IsRegularScheme X)
    (_hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2) (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x)) :
    (FEt.pullback U.ι).IsEquivalence :=
  isEquivalence_pullback_of_isRegularScheme hX U hU

/-- X.3.3, last assertion, for regular schemes of dimension `≤ 2`: with compatible fibre functors on
the étale coverings of `X` and of `U`, the map `π₁(U) → π₁(X)` is an isomorphism. -/
theorem bijective_autWhiskerLeft_of_ringKrullDim_le_two {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : IsRegularScheme X) (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2)
    (U : X.Opens) (hU : ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x))
    [GaloisCategory (FEt X)] [GaloisCategory (FEt U)] {F : FEt X ⥤ FintypeCat.{u}}
    {F' : FEt U ⥤ FintypeCat.{u}} [FiberFunctor F] [FiberFunctor F']
    (e : FEt.pullback U.ι ⋙ F' ≅ F) :
    Function.Bijective (autWhiskerLeft _ e) :=
  have := isEquivalence_pullback_of_isRegularScheme_of_ringKrullDim_le_two hX hdim U hU
  autWhiskerLeft_bijective_of_isEquivalence _ e

/-- X.3.3 for the spectrum of a regular local ring (SGA 2 X.3.4; Stacks 0BMB): if `A` is a
regular local ring of dimension `≥ 2` and `U` is the punctured spectrum `Spec A \ {𝔪}`, then
`X' ↦ X' ×_X U` is an equivalence from the étale coverings of `Spec A` to those of `U`. This is
`PurityCoveringsStatement` for `X = Spec A` and the largest proper open `U` whose complement has
codimension `≥ 2`.

Full faithfulness is Hartogs (an étale covering `Spec B` is flat, so `B = Γ(U ×_X Spec B)`);
essential surjectivity extends a covering `W` of `U` by `Spec Γ(W)`, which is finite over `A`,
of depth `2` and étale over `U`, hence étale over `A` by the algebraic form of X.3.2
(`IsRegularLocalRing.etale_of_isWeaklyRegular_of_two_le_ringKrullDim`, proved by induction on the
dimension; see `SGA.Foundations.CommAlg.PurityInduction`). -/
theorem isEquivalence_pullback_puncturedSpectrum (A : CommRingCat.{u}) [IsRegularLocalRing A]
    (hdim : 2 ≤ ringKrullDim A) : (FEt.pullback (puncturedSpectrum A).ι).IsEquivalence :=
  AlgebraicGeometry.isEquivalence_pullback_puncturedSpectrum hdim

/-- X.3.3, last assertion, for the punctured spectrum `U` of a regular local ring `A` of dimension
`≥ 2`: with compatible fibre functors on the étale coverings of `Spec A` and of `U`, the map
`π₁(U) → π₁(Spec A)` is an isomorphism. -/
theorem bijective_autWhiskerLeft_puncturedSpectrum (A : CommRingCat.{u}) [IsRegularLocalRing A]
    (hdim : 2 ≤ ringKrullDim A) [GaloisCategory (FEt (Spec A))]
    [GaloisCategory (FEt (puncturedSpectrum A))] {F : FEt (Spec A) ⥤ FintypeCat.{u}}
    {F' : FEt (puncturedSpectrum A) ⥤ FintypeCat.{u}} [FiberFunctor F] [FiberFunctor F']
    (e : FEt.pullback (puncturedSpectrum A).ι ⋙ F' ≅ F) :
    Function.Bijective (autWhiskerLeft _ e) :=
  have := isEquivalence_pullback_puncturedSpectrum A hdim
  autWhiskerLeft_bijective_of_isEquivalence _ e

/-- X.3.4, birational invariance of the fundamental group (proved in `birationalInvariance`,
`SGA.SGA1.ExposeX.PurityBirational`). Let `X`, `Y` be integral, regular and proper over a field
`k`, and `φ` a birational map from `X` to `Y` (an isomorphism `U ≅ V` of dense open subschemes over
`k`). Then there is an equivalence between the étale coverings of `X` and of `Y` compatible with
`φ` on `U`; with fibre functors at a geometric point of `U`, it gives the canonical isomorphism of
fundamental groups. -/
def BirationalInvarianceStatement : Prop :=
  ∀ (k : Type u) [Field k] ⦃X Y : Scheme.{u}⦄ (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [IsProper sX] [IsProper sY] [IsIntegral X] [IsIntegral Y], IsRegularScheme X →
    IsRegularScheme Y → ∀ φ : X.PartialIso Y, φ.IsOver sX sY →
    ∃ E : FEt X ≌ FEt Y,
      Nonempty (E.functor ⋙ FEt.pullback (φ.iso.hom ≫ φ.target.ι) ≅ FEt.pullback φ.source.ι)

end SGA.SGA1.ExposeX
