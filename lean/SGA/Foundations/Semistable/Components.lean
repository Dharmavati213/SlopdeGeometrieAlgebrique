/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.PowerSeries.Basic
import SGA.Foundations.Cohomology.EulerCharacteristic
import SGA.Foundations.Semistable.SmoothCurve

/-!
# Components, multiplicities and intersection numbers of a curve over a field

The numerical invariants of a curve `Y` over a field `k` (in the application, the special fibre
`X_k` of a regular model `X` of a curve over a discrete valuation ring, Stacks, Situation 0C5Y)
which enter the proof of the semistable reduction theorem (Stacks, Sections 0CEG and 0CEI):

* `Scheme.componentGenericPoint Z`: the generic point `ξ` of an irreducible component `Z` of `Y`;
* `Scheme.componentMultiplicity Z = length 𝒪_{Y,ξ}`, the multiplicity of `Z` in `Y` (Stacks, Tag
  0C5Z (3) and Chow Homology, Definition 02QT);
* `Scheme.componentIdeal Z x ⊆ 𝒪_{Y,x}`: the prime ideal of `Z` in the local ring at `x ∈ Z`, the
  kernel of `𝒪_{Y,x} → 𝒪_{Y,ξ} → κ(ξ)` (`⊤` if `x ∉ Z`);
* `Scheme.componentIntersection p Z W = ∑_x dim_k 𝒪_{Y,x} / (𝔭_Z + 𝔭_W)`: the degree over `k` of the
  scheme theoretic intersection of the reduced components `Z` and `W`;
* `Scheme.intersectionMatrix p`: the matrix `(Cᵢ · Cⱼ)`, see the deviation below;
* `Scheme.componentSubscheme Z`: the reduced closed subscheme on `Z`, and
  `Scheme.componentGenus p Z = dim_k H¹(Z, 𝒪_Z)`;
* `Scheme.componentGeometricGenus p Z = dim_k H¹(Zᵛ, 𝒪)`, `Zᵛ` the normalization of `Z` (the
  relative normalization of `Y` in `Spec κ(ξ)`), and `Scheme.geometricGenus p = ∑_Z`, which is
  `g_geom(Y/k)` of Stacks, Section 0CE0, when `k` is algebraically closed;
* `Scheme.reduction Y = Y_red` (the closed subscheme of the nilradical), reduced
  (`Scheme.isReduced_reduction`);
* `Scheme.existsUnique_component_of_isDomain_stalk`: if `𝒪_{Y,z}` is a domain, `z` lies on a
  unique irreducible component, of multiplicity `1` (its local rings at generizations of `z` are
  domains, `Scheme.isDomain_stalk_of_specializes`);
* `multicrossSubring k n = {(f₁, …, fₙ) ∈ k⟦t⟧ⁿ | f₁(0) = ⋯ = fₙ(0)}` and
  `Scheme.IsMulticrossPoint Y y`: the completed local ring of `Y` at `y` is this ring for some
  `n ≥ 2` (Stacks, Definition 0C1W, equation 0C1U);

## Deviations

* **Intersection numbers.** Stacks defines `(Cᵢ · Cⱼ) = deg_{Cᵢ}(𝒪_X(Cⱼ)|_{Cᵢ})` on the regular
  model `X`. For `i ≠ j` this is `deg(Cᵢ ∩ Cⱼ)` (Stacks, proof of Tag 0C64), the formula used here,
  which only involves `Y = X_k`. The self-intersection is then determined by
  `∑ⱼ mⱼ (Cᵢ · Cⱼ) = 0` (Stacks, Tag 0C66 (2)): we *define* `(Cᵢ · Cᵢ)` as
  `-(∑_{j ≠ i} mⱼ (Cᵢ · Cⱼ)) / mᵢ` (integer division). That `mᵢ` divides the sum, and that the
  result is Stacks' self-intersection, are statements about regular models (Tags 0C64, 0C66),
  part of `AlgebraicGeometry.NumericalTypeOfModelStatement`; they are not proved here.
* The definitions make sense for any scheme over `k`, but they are the invariants of Stacks only
  for proper curves (for instance, `componentIntersection` sums over all points of `Z ∩ W`, which
  are closed points when `Y` has dimension `1`), and the residue degree factor `[κ(x) : k]` of
  Stacks is contained in `dim_k`.
* The multicross condition asks for a ring isomorphism of completions, as in
  `SGA.SGA1.ExposeXIII.IsSemistableCurve`.

## References

* [Stacks Project, Chapter 55 (Semistable Reduction), Sections 0C5Y, 0C6Y](https://stacks.math.columbia.edu/tag/0C5Y)
* [Stacks Project, Chapter 53 (Algebraic Curves), Sections 0C1T, 0CE0](https://stacks.math.columbia.edu/tag/0C1T)
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

variable {Y : Scheme.{u}}

section Components

/-- The generic point of an irreducible component `Z` of a scheme. -/
noncomputable def componentGenericPoint (Z : irreducibleComponents Y) : Y :=
  Z.2.1.genericPoint

lemma isGenericPoint_componentGenericPoint (Z : irreducibleComponents Y) :
    IsGenericPoint (componentGenericPoint Z) Z.1 := by
  have h := Z.2.1.isGenericPoint_genericPoint_closure
  rwa [(isClosed_of_mem_irreducibleComponents _ Z.2).closure_eq] at h

lemma componentGenericPoint_specializes_iff (Z : irreducibleComponents Y) (x : Y) :
    componentGenericPoint Z ⤳ x ↔ x ∈ Z.1 :=
  isGenericPoint_iff_specializes.mp (isGenericPoint_componentGenericPoint Z) x

lemma componentGenericPoint_mem (Z : irreducibleComponents Y) : componentGenericPoint Z ∈ Z.1 :=
  (componentGenericPoint_specializes_iff Z _).mp specializes_rfl

/-- The multiplicity of an irreducible component `Z` of a scheme `Y`: the length of the local ring
`𝒪_{Y,ξ}` at its generic point (Stacks, Chow Homology, Definition 02QT; for the special fibre of
a regular model this is the multiplicity `mᵢ` of `X_k = ∑ mᵢ Cᵢ`, Stacks, Tag 0C5Z (3)). It is
`0` if the length is infinite (which does not happen for locally noetherian `Y`). -/
noncomputable def componentMultiplicity (Z : irreducibleComponents Y) : ℕ :=
  (Module.length (Y.presheaf.stalk (componentGenericPoint Z))
    (Y.presheaf.stalk (componentGenericPoint Z))).toNat

open Classical in
/-- The prime ideal of an irreducible component `Z` in the local ring `𝒪_{Y,x}` at a point
`x ∈ Z`: the kernel of `𝒪_{Y,x} → 𝒪_{Y,ξ} → κ(ξ)`, `ξ` the generic point of `Z`. Its quotient is
the local ring of the reduced component `Z` at `x`. We set it to `⊤` if `x ∉ Z`. -/
noncomputable def componentIdeal (Z : irreducibleComponents Y) (x : Y) :
    Ideal (Y.presheaf.stalk x) :=
  if h : componentGenericPoint Z ⤳ x then
    RingHom.ker (Y.presheaf.stalkSpecializes h ≫ Y.residue (componentGenericPoint Z)).hom
  else ⊤

lemma componentIdeal_of_notMem (Z : irreducibleComponents Y) {x : Y} (hx : x ∉ Z.1) :
    componentIdeal Z x = ⊤ := by
  rw [componentIdeal, dite_eq_right ((componentGenericPoint_specializes_iff Z x).not.mpr hx)]

/-- The reduced closed subscheme with underlying set an irreducible component `Z` (the vanishing
ideal of `Z`). -/
noncomputable def componentSubscheme (Z : irreducibleComponents Y) : Scheme.{u} :=
  (IdealSheafData.vanishingIdeal ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subscheme

/-- The closed immersion of the reduced component `Z` into `Y`. -/
noncomputable def componentSubschemeι (Z : irreducibleComponents Y) :
    componentSubscheme Z ⟶ Y :=
  (IdealSheafData.vanishingIdeal ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι

/-- The reduced scheme `Y_red`: the closed subscheme defined by the nilradical. -/
noncomputable abbrev reduction (Y : Scheme.{u}) : Scheme.{u} := Y.nilradical.subscheme

/-- The closed immersion `Y_red ⟶ Y`. -/
noncomputable abbrev reductionι (Y : Scheme.{u}) : Y.reduction ⟶ Y := Y.nilradical.subschemeι

/-- `Y_red` is reduced: it is covered by the spectra of the rings `Γ(Y, U) / nil(Γ(Y, U))`. -/
instance isReduced_reduction (Y : Scheme.{u}) : IsReduced Y.reduction := by
  have : ∀ i, IsReduced (Y.nilradical.subschemeCover.openCover.X i) := by
    rintro (U : Y.affineOpens)
    have : _root_.IsReduced (Γ(Y, U.1) ⧸ Y.nilradical.ideal U) := by
      have h : Y.nilradical.ideal U = ((⊥ : Y.IdealSheafData).ideal U).radical := rfl
      rw [h]
      exact (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical _)
    exact (inferInstance : IsReduced (Spec (.of (Γ(Y, U.1) ⧸ Y.nilradical.ideal U))))
  exact IsReduced.of_openCover (X := Y.reduction) Y.nilradical.subschemeCover.openCover

/-- The local rings of `Y_red` are quotients of those of `Y`, so their dimension is not larger. -/
lemma ringKrullDim_stalk_reduction_le (Y : Scheme.{u}) (y : Y.reduction) :
    ringKrullDim (Y.reduction.presheaf.stalk y) ≤
      ringKrullDim (Y.presheaf.stalk (Y.reductionι y)) :=
  ringKrullDim_le_of_surjective _ (Y.reductionι.stalkMap_surjective y)

section DomainStalk

/-- If the local ring of a scheme at `z` is a domain, so is its local ring at every generization of
`z` (a localization of a domain). -/
lemma isDomain_stalk_of_specializes {ξ z : Y} (h : ξ ⤳ z) [IsDomain (Y.presheaf.stalk z)] :
    IsDomain (Y.presheaf.stalk ξ) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hξU : ξ ∈ U := h.mem_open U.isOpen hzU
  let _ := Y.presheaf.algebra_section_stalk ⟨ξ, hξU⟩
  have hloc := hU.isLocalization_stalk ⟨ξ, hξU⟩
  have hgerm : ∀ r : Γ(Y, U), Y.presheaf.stalkSpecializes h (Y.presheaf.germ U z hzU r) =
      Y.presheaf.germ U ξ hξU r := fun r ↦ by
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have halg : ∀ r : Γ(Y, U), algebraMap Γ(Y, U) (Y.presheaf.stalk ξ) r =
      Y.presheaf.germ U ξ hξU r := fun _ ↦ rfl
  -- an element of `A` whose germ at `z` vanishes has vanishing germ at `ξ`
  have hz0 : ∀ r : Γ(Y, U), Y.presheaf.germ U z hzU r = 0 →
      algebraMap Γ(Y, U) (Y.presheaf.stalk ξ) r = 0 := fun r hr ↦ by
    rw [halg, ← hgerm, hr, map_zero]
  set M := (hU.primeIdealOf ⟨ξ, hξU⟩).asIdeal.primeCompl
  have hmk0 : ∀ (a₀ : Γ(Y, U)) (s : M), Y.presheaf.germ U z hzU a₀ = 0 →
      IsLocalization.mk' (Y.presheaf.stalk ξ) a₀ s = 0 := fun a₀ s ha ↦ by
    rw [IsLocalization.mk'_eq_iff_eq_mul, zero_mul]
    exact hz0 a₀ ha
  refine @NoZeroDivisors.to_isDomain _ _ inferInstance ⟨fun {a b} hab ↦ ?_⟩
  obtain ⟨⟨a₀, s⟩, rfl⟩ := IsLocalization.mk'_surjective M a
  obtain ⟨⟨b₀, t⟩, rfl⟩ := IsLocalization.mk'_surjective M b
  rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff] at hab
  obtain ⟨c, hc⟩ := hab
  have h0 : Y.presheaf.germ U z hzU c * (Y.presheaf.germ U z hzU a₀ *
      Y.presheaf.germ U z hzU b₀) = 0 := by
    rw [← map_mul, ← map_mul, hc, map_zero]
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd (hz0 c h1) (IsLocalization.map_units (Y.presheaf.stalk ξ) c).ne_zero
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inl (hmk0 a₀ s h2)
    · exact Or.inr (hmk0 b₀ t h2)

/-- The generic point of an irreducible component has no proper generization. -/
lemma eq_componentGenericPoint_of_specializes (Z : irreducibleComponents Y) {y : Y}
    (h : y ⤳ componentGenericPoint Z) : y = componentGenericPoint Z := by
  have hZ := isGenericPoint_componentGenericPoint Z
  have hsub : Z.1 ⊆ closure {y} := by
    rw [← hZ.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp h))
      isClosed_closure
  have heq : closure {y} = Z.1 :=
    (Z.2.2 isIrreducible_singleton.closure hsub).antisymm hsub
  exact (h.antisymm ((componentGenericPoint_specializes_iff Z y).mpr
    (heq ▸ subset_closure (Set.mem_singleton y)))).eq

/-- If the local ring at the generic point `ξ` of an irreducible component is a domain, it is a
field: `Spec 𝒪_{Y,ξ}` has a single point, since `ξ` has no proper generization. -/
lemma isField_stalk_componentGenericPoint (Z : irreducibleComponents Y)
    [IsDomain (Y.presheaf.stalk (componentGenericPoint Z))] :
    IsField (Y.presheaf.stalk (componentGenericPoint Z)) := by
  set ξ := componentGenericPoint Z
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  let p : Spec (Y.presheaf.stalk ξ) := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : Y.fromSpecStalk ξ p = ξ := by
    have : Y.fromSpecStalk ξ p ∈ Set.range (Y.fromSpecStalk ξ) := Set.mem_range_self p
    rw [range_fromSpecStalk] at this
    exact eq_componentGenericPoint_of_specializes Z this
  have : p = IsLocalRing.closedPoint (Y.presheaf.stalk ξ) :=
    (Y.fromSpecStalk ξ).isEmbedding.injective (hp.trans fromSpecStalk_closedPoint.symm)
  exact (congrArg PrimeSpectrum.asIdeal this).symm

/-- If the local ring at the generic point of an irreducible component is a domain, the
multiplicity of the component is `1`. -/
lemma componentMultiplicity_eq_one (Z : irreducibleComponents Y)
    [IsDomain (Y.presheaf.stalk (componentGenericPoint Z))] : componentMultiplicity Z = 1 := by
  let := (isField_stalk_componentGenericPoint Z).toField
  rw [componentMultiplicity, Module.length_eq_one]
  rfl

/-- If the local ring of `Y` at `z` is a domain, then `z` lies on a unique irreducible component,
and that component has multiplicity `1`. -/
lemma existsUnique_component_of_isDomain_stalk (z : Y) [IsDomain (Y.presheaf.stalk z)] :
    ∃ Z : irreducibleComponents Y, z ∈ Z.1 ∧ (∀ W : irreducibleComponents Y, z ∈ W.1 → W = Z) ∧
      componentMultiplicity Z = 1 := by
  obtain ⟨Z, hZ, hzZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {z}
    isIrreducible_singleton
  let Z' : irreducibleComponents Y := ⟨Z, hZ⟩
  -- the image `η` of the generic point of `Spec 𝒪_{Y,z}` generizes every generization of `z`
  let p : Spec (Y.presheaf.stalk z) := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : ∀ W : irreducibleComponents Y, z ∈ W.1 →
      Y.fromSpecStalk z p = componentGenericPoint W := fun W hzW ↦ by
    have hW : componentGenericPoint W ∈ Set.range (Y.fromSpecStalk z) := by
      rw [range_fromSpecStalk]
      exact (componentGenericPoint_specializes_iff W z).mpr hzW
    obtain ⟨q, hq⟩ := hW
    refine eq_componentGenericPoint_of_specializes W ?_
    rw [← hq]
    exact ((PrimeSpectrum.le_iff_specializes p q).mp bot_le).map (Y.fromSpecStalk z).continuous
  have hZz : z ∈ Z'.1 := hzZ rfl
  have huniq : ∀ W : irreducibleComponents Y, z ∈ W.1 → W = Z' := fun W hzW ↦ by
    have h := (hη W hzW).symm.trans (hη Z' hZz)
    apply Subtype.ext
    rw [← (isGenericPoint_componentGenericPoint W).def,
      ← (isGenericPoint_componentGenericPoint Z').def, h]
  refine ⟨Z', hZz, huniq, ?_⟩
  have : IsDomain (Y.presheaf.stalk (componentGenericPoint Z')) :=
    isDomain_stalk_of_specializes ((componentGenericPoint_specializes_iff Z' z).mpr hZz)
  exact componentMultiplicity_eq_one Z'

end DomainStalk

end Components

section OverField

variable {k : Type u} [Field k] (p : Y ⟶ Spec (.of k))

/-- The local contribution `dim_k 𝒪_{Y,x} / (𝔭_Z + 𝔭_W)` at `x` to the intersection number of
two irreducible components `Z` and `W` of a scheme `Y` over `k`: the `k`-dimension of the local
ring at `x` of the scheme theoretic intersection of the reduced components (`0` if `x ∉ Z ∩ W`,
or if this dimension is infinite). -/
noncomputable def localIntersectionNumber (Z W : irreducibleComponents Y) (x : Y) : ℕ :=
  letI := (stalkStructureMap p x).hom.toAlgebra
  Module.finrank k (Y.presheaf.stalk x ⧸ (componentIdeal Z x ⊔ componentIdeal W x))

lemma localIntersectionNumber_of_notMem_left (Z W : irreducibleComponents Y) {x : Y}
    (hx : x ∉ Z.1) : localIntersectionNumber p Z W x = 0 := by
  let := (stalkStructureMap p x).hom.toAlgebra
  have : Subsingleton (Y.presheaf.stalk x ⧸ (componentIdeal Z x ⊔ componentIdeal W x)) := by
    rw [componentIdeal_of_notMem Z hx, top_sup_eq]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

/-- The intersection number `(Z · W) = deg_k (Z ∩ W) = ∑_x dim_k 𝒪_{Z ∩ W, x}` of two irreducible
components of a scheme `Y` over `k`, for `Z ≠ W` (Stacks, proof of Tag 0C64: for the special fibre
of a regular model this is `deg_{Cᵢ}(𝒪_X(Cⱼ)|_{Cᵢ})`). The sum is over the points of `Z ∩ W`
(`localIntersectionNumber` vanishes elsewhere); it is `0` if infinitely many terms are nonzero. -/
noncomputable def componentIntersection (Z W : irreducibleComponents Y) : ℕ :=
  ∑ᶠ x, localIntersectionNumber p Z W x

open Classical in
/-- The intersection matrix `((Cᵢ · Cⱼ))` of the irreducible components of a scheme `Y` over `k`:
`componentIntersection` off the diagonal and, on the diagonal,
`(Cᵢ · Cᵢ) = -(∑_{j ≠ i} mⱼ (Cᵢ · Cⱼ)) / mᵢ` with `mⱼ = componentMultiplicity`.

Deviation: for the special fibre of a regular model, Stacks defines the diagonal entries as the
degrees `deg_{Cᵢ}(𝒪_X(Cᵢ)|_{Cᵢ})`; they satisfy `∑ⱼ mⱼ (Cᵢ · Cⱼ) = 0` (Stacks, Tag 0C66 (2)), so
they agree with the formula used here. That the division is exact is part of
`AlgebraicGeometry.NumericalTypeOfModelStatement`. -/
noncomputable def intersectionMatrix [Fintype (irreducibleComponents Y)] :
    Matrix (irreducibleComponents Y) (irreducibleComponents Y) ℤ :=
  fun Z W ↦ if Z = W then
      -(∑ V ∈ Finset.univ.erase Z,
          (componentMultiplicity V : ℤ) * componentIntersection p Z V) /
        componentMultiplicity Z
    else componentIntersection p Z W

/-- The genus `dim_k H¹(Z, 𝒪_Z)` of the reduced irreducible component `Z` of a scheme `Y` over
`k` (Stacks' `gᵢ` of Tag 0CA4 when `H⁰(Z, 𝒪_Z) = k`, for instance for `k` algebraically closed and
`Y` proper). -/
noncomputable def componentGenus (Z : irreducibleComponents Y) : ℕ :=
  (componentSubschemeι Z ≫ p).genus

/-- The geometric genus `dim_k H¹(Zᵛ, 𝒪)` of an irreducible component `Z` of a scheme `Y` over
`k`, where `Zᵛ` is the normalization of the reduced component, taken as the relative
normalization of `Y` in `Spec κ(ξ)` (`ξ` the generic point of `Z`). For `k` algebraically closed
and `Y` proper of dimension `1` this is the geometric genus `g_geom(Z/k)` of Stacks, Section 0CE0
(the genus of the normalization). -/
noncomputable def componentGeometricGenus [QuasiSeparatedSpace Y]
    (Z : irreducibleComponents Y) : ℕ :=
  ((Y.fromSpecResidueField (componentGenericPoint Z)).fromNormalization ≫ p).genus

/-- The geometric genus `g_geom(Y/k) = ∑_Z g_geom(Z/k)` of a scheme `Y` over `k`, the sum over the
irreducible components (Stacks, Section 0CE0 and Tag 0CE1, for `k` algebraically closed; Stacks
sums over the components of dimension `1`, and a component of dimension `0` contributes `0`). -/
noncomputable def geometricGenus [QuasiSeparatedSpace Y] [Fintype (irreducibleComponents Y)] :
    ℕ :=
  ∑ Z, componentGeometricGenus p Z

end OverField

end Scheme

section Multicross

variable (k : Type u) [Field k]

/-- The complete local ring `{(f₁, …, fₙ) ∈ k⟦t⟧ⁿ | f₁(0) = ⋯ = fₙ(0)}` of `n` smooth branches
through a point in general position (Stacks, equation 0C1U). For `n = 1` it is `k⟦t⟧`, for
`n = 2` it is isomorphic to `k⟦u, v⟧/(uv)`. -/
def multicrossSubring (n : ℕ) : Subring (Fin n → PowerSeries k) where
  carrier := {f | ∀ i j, PowerSeries.constantCoeff (f i) = PowerSeries.constantCoeff (f j)}
  mul_mem' {f g} hf hg i j := by simp only [Pi.mul_apply, map_mul, hf i j, hg i j]
  one_mem' i j := by simp
  add_mem' {f g} hf hg i j := by simp only [Pi.add_apply, map_add, hf i j, hg i j]
  zero_mem' i j := by simp
  neg_mem' {f} hf i j := by simp only [Pi.neg_apply, map_neg, hf i j]

/-- A point `y` of a scheme `Y` (a closed point of a curve over the algebraically closed field `k`)
is a *multicross singularity* if the completion of `𝒪_{Y,y}` is isomorphic to
`multicrossSubring k n` for some `n ≥ 2` (Stacks, Definition 0C1W; `n = 2` is a node). As in
`SGA.SGA1.ExposeXIII.IsSemistableCurve`, a ring isomorphism is asked for. -/
def Scheme.IsMulticrossPoint {Y : Scheme.{u}} (y : Y) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
    (Y.presheaf.stalk y) ≃+* multicrossSubring k n)

end Multicross

end AlgebraicGeometry
