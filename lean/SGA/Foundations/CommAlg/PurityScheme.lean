/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Normalization
import SGA.Foundations.CommAlg.PuncturedSpectrum
import SGA.Foundations.CommAlg.RegularPair
import SGA.SGA2.ExposeIII.DepthLocalization

/-!
# Purity for locally noetherian schemes

Let `X` be a locally noetherian scheme and `U ⊆ X` an open subset such that `𝒪_{X,x}` is regular of
dimension `≥ 2` at every point `x ∉ U`. Then base change `X' ↦ X' ×_X U` is an equivalence between
finite étale `X`-schemes and finite étale `U`-schemes
(`AlgebraicGeometry.isEquivalence_pullback_of_isRegularLocalRing`; SGA 1 X.3.3, SGA 2 X.3.4,
Stacks 0BMB).

## Strategy

* Charts (`exists_isWeaklyRegular_basicOpen_sup_le`): every point has an affine neighbourhood `V`
  with a regular sequence `a, b ∈ Γ(V)` such that `D(a) ∪ D(b) ⊆ U`: the ideal of `V \ U` has depth
  `≥ 2` since the local rings at its points do (SGA 2 III.2.9).
* Hartogs over a chart (`bijective_restrict_preimage_of_basicOpen_sup_le`): for `Y ⟶ X` affine and
  flat, `Γ(Y_V) → Γ(Y_{V ∩ U})` is bijective (sections over `Y_{V ∩ U}` are determined on `D(a)`,
  and `Γ(Y_V) → Γ(D(a) ∪ D(b))` is bijective).
* Purity over a chart (`finite_etale_app_of_basicOpen_sup_le`): a finite étale `w : W ⟶ U` has
  `Γ(V) → Γ(w⁻¹(V ∩ U))` finite étale; the target has depth `≥ 2`, is finite by
  `Module.finite_of_isLocalization_pair`, and étale by the purity theorem at the local rings of the
  points of `V \ U` (`Algebra.etale_of_isWeaklyRegular_of_forall_notMem`).
* Gluing is done by mathlib's relative normalization `Scheme.Hom.normalization`: the extension of
  `W` is the normalization of `X` in `W ⟶ U ⟶ X`, finite étale by the above
  (`finite_etale_fromNormalization`) and restricting to `W` over `U` because normalization commutes
  with smooth base change; a finite étale `Y` is the normalization of `X` in `Y ×_X U`
  (`isIso_normalizationDesc_pullbackFst`), which gives full faithfulness through the universal
  property of the normalization (`faithful_pullback_of_isIso_normalizationDesc`,
  `full_pullback_of_isIso_normalizationDesc`, which also serve for dense opens of normal
  schemes).
-/

universe u

open CategoryTheory Limits IsLocalRing RingTheory.Sequence


namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The point of an affine open `V` corresponding to a prime of `Γ(V)` lies in `V`. -/
lemma IsAffineOpen.fromSpec_mem {V : X.Opens} (hV : IsAffineOpen V) (p : PrimeSpectrum Γ(X, V)) :
    hV.fromSpec p ∈ V := by
  have : hV.fromSpec p ∈ Set.range hV.fromSpec := Set.mem_range_self p
  rwa [hV.range_fromSpec] at this

/-- The point of `V` corresponding to `p` lies in `D(f)` iff `f ∉ p`. -/
lemma IsAffineOpen.fromSpec_mem_basicOpen_iff {V : X.Opens} (hV : IsAffineOpen V)
    {f : Γ(X, V)} {p : PrimeSpectrum Γ(X, V)} :
    hV.fromSpec p ∈ X.basicOpen f ↔ f ∉ p.asIdeal := by
  change p ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f ↔ _
  rw [hV.fromSpec_preimage_basicOpen]
  rfl

/-- The local ring of `Γ(X, V)` at a prime `p` is the stalk of `X` at the corresponding point. -/
noncomputable def IsAffineOpen.localizationAtPrimeEquivStalk {V : X.Opens} (hV : IsAffineOpen V)
    (p : PrimeSpectrum Γ(X, V)) :
    Localization.AtPrime p.asIdeal ≃+* X.presheaf.stalk (hV.fromSpec p) :=
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hV.fromSpec p, hV.fromSpec_mem p⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec p)) p.asIdeal :=
    hV.isLocalization_stalk' p (hV.fromSpec_mem p)
  (IsLocalization.algEquiv p.asIdeal.primeCompl _ _).toRingEquiv

/-- Bijectivity of a restriction map only depends on the source open. -/
lemma Scheme.bijective_presheaf_map_congr' {X : Scheme.{u}} {V V' W : X.Opens} (h : V = V')
    (hV : V ≤ W) (hV' : V' ≤ W) :
    Function.Bijective (X.presheaf.map (homOfLE hV).op) ↔
      Function.Bijective (X.presheaf.map (homOfLE hV').op) := by
  subst h; rfl

/-- Restriction between equal opens is bijective. -/
lemma Scheme.bijective_presheaf_map_of_eq {X : Scheme.{u}} {V W : X.Opens} (h : V ≤ W)
    (h' : V = W) : Function.Bijective (X.presheaf.map (homOfLE h).op) := by
  subst h'
  have : homOfLE h = 𝟙 V := Subsingleton.elim _ _
  rw [this]
  exact ConcreteCategory.bijective_of_isIso _

section Chart

variable (U : X.Opens)

/-- If `D(a) ∪ D(b) ⊆ U`, every prime of `Γ(V)` whose point is not in `U` contains `a` and `b`. -/
lemma mem_of_fromSpec_notMem {V : X.Opens} (hV : IsAffineOpen V) {a b : Γ(X, V)}
    (hab : X.basicOpen a ⊔ X.basicOpen b ≤ U) (p : PrimeSpectrum Γ(X, V))
    (hp : hV.fromSpec p ∉ U) : a ∈ p.asIdeal ∧ b ∈ p.asIdeal := by
  constructor <;> by_contra h <;> apply hp
  · exact hab (TopologicalSpace.Opens.mem_sup.mpr (Or.inl (hV.fromSpec_mem_basicOpen_iff.mpr h)))
  · exact hab (TopologicalSpace.Opens.mem_sup.mpr (Or.inr (hV.fromSpec_mem_basicOpen_iff.mpr h)))

omit U in
/-- The local depth (SGA 2, III) of a noetherian ring at a prime is the depth of its
localization. -/
lemma localDepth_self_eq (R : Type u) [CommRing R] [IsNoetherianRing R] (p : PrimeSpectrum R) :
    SGA.SGA2.ExposeIII.localDepth (ModuleCat.of R R) p =
      (maximalIdeal (Localization.AtPrime p.asIdeal)).depth (Localization.AtPrime p.asIdeal) := by
  let Rp := Localization.AtPrime p.asIdeal
  let e₀ : LocalizedModule p.asIdeal.primeCompl R ≃ₗ[R] Rp :=
    IsLocalizedModule.iso p.asIdeal.primeCompl (Algebra.linearMap R Rp)
  let e : LocalizedModule p.asIdeal.primeCompl R ≃ₗ[Rp] Rp :=
    LinearEquiv.extendScalarsOfIsLocalizationEquiv p.asIdeal.primeCompl Rp e₀
  change SGA.SGA2.ExposeIII.depth _ (ModuleCat.of Rp (LocalizedModule p.asIdeal.primeCompl R)) = _
  rw [← Ideal.depth_eq_sga2Depth, Ideal.depth_eq_of_linearEquiv e]

variable {U} in
/-- Charts exist: if `X` is locally noetherian with regular local rings of dimension `≥ 2` at the
points outside `U`, every point has an affine open neighbourhood `V` with a regular sequence
`a, b ∈ Γ(V)` such that `D(a) ∪ D(b) ⊆ U`. Take `a, b` in the ideal of `V \ U`, which has depth
`≥ 2` since the local rings at its points do (SGA 2 III.2.9). -/
theorem exists_isWeaklyRegular_basicOpen_sup_le [IsLocallyNoetherian X]
    (hreg : ∀ x : X, x ∉ U → IsRegularLocalRing (X.presheaf.stalk x))
    (hU : ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x)) (x : X) :
    ∃ (V : X.Opens) (a b : Γ(X, V)), x ∈ V ∧ IsAffineOpen V ∧
      X.basicOpen a ⊔ X.basicOpen b ≤ U ∧ IsWeaklyRegular Γ(X, V) [a, b] := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let Z : Set (PrimeSpectrum Γ(X, V)) := {q | hV.fromSpec q ∉ U}
  have hZ : IsClosed Z := (U.isOpen.preimage hV.fromSpec.continuous).isClosed_compl
  let I := PrimeSpectrum.vanishingIdeal Z
  have hdepth : ((2 : ℕ) : ℕ∞) ≤ I.depth Γ(X, V) := by
    rw [Ideal.depth_eq_sga2Depth, SGA.SGA2.ExposeIII.le_depth_iff_forall_localDepth]
    intro q hq
    have hqZ : q ∈ Z := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq] at hq
      exact hq
    rw [localDepth_self_eq]
    have : IsRegularLocalRing (X.presheaf.stalk (hV.fromSpec q)) := hreg _ hqZ
    have : IsRegularLocalRing (Localization.AtPrime q.asIdeal) :=
      IsRegularLocalRing.of_ringEquiv (hV.localizationAtPrimeEquivStalk q).symm
    have h := IsRegularLocalRing.depth_eq_ringKrullDim (R := Localization.AtPrime q.asIdeal)
    rw [ringKrullDim_eq_of_ringEquiv (hV.localizationAtPrimeEquivStalk q)] at h
    have h2 := hU _ hqZ
    rw [← h] at h2
    exact WithBot.coe_le_coe.mp h2
  obtain ⟨rs, hlen, hmem, hrs⟩ := (Ideal.le_depth_iff I Γ(X, V) 2).mp hdepth
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have hle : ∀ c ∈ I, X.basicOpen c ≤ U := by
    intro c hc y hy
    have hyV : y ∈ V := X.basicOpen_le c hy
    obtain ⟨q, rfl⟩ : y ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hyV
    by_contra hyU
    exact (hV.fromSpec_mem_basicOpen_iff.mp hy)
      ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hc q hyU)
  exact ⟨V, a, b, hxV, hV, sup_le (hle a (hmem a (by simp))) (hle b (hmem b (by simp))), hrs⟩

/-- Sections of an affine flat `y : Y ⟶ X` over `y⁻¹(V ∩ U)` (`V` affine) are determined by their
restriction to `y⁻¹ D(a)`, for `a ∈ Γ(V)` a nonzerodivisor: `V ∩ U` is covered by basic opens
`D(f) ⊆ U`, on whose preimages `a` stays a nonzerodivisor by flatness. -/
theorem injective_restrict_preimage_basicOpen {V : X.Opens} (hV : IsAffineOpen V) {a : Γ(X, V)}
    (ha : a ∈ nonZeroDivisors Γ(X, V)) {Y : Scheme.{u}} (y : Y ⟶ X) [IsAffineHom y] [Flat y]
    (h : Y.basicOpen (y.app V a) ≤ y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U) :
    Function.Injective (Y.presheaf.map (homOfLE h).op) := by
  have hYV : IsAffineOpen (y ⁻¹ᵁ V) := hV.preimage y
  let _ := (y.app V).hom.toAlgebra
  have : Module.Flat Γ(X, V) Γ(Y, y ⁻¹ᵁ V) := by
    change (y.app V).hom.Flat
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE (P := @Flat) y inferInstance ⟨V, hV⟩ ⟨_, hYV⟩ le_rfl
  let O := y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U
  let ι := {f : Γ(X, V) // X.basicOpen f ≤ U}
  let Uf : ι → Y.Opens := fun f ↦ Y.basicOpen (y.app V f.1)
  have hUf : ∀ f : ι, Uf f ≤ O := fun f ↦ by
    change Y.basicOpen _ ≤ _
    rw [← Scheme.preimage_basicOpen]
    exact le_inf (y.preimage_mono (X.basicOpen_le _)) (y.preimage_mono f.2)
  -- `a` stays a nonzerodivisor on the `Γ(Uf)`
  have hareg : ∀ (f : ι) (t : Γ(Y, Uf f)),
      algebraMap Γ(Y, y ⁻¹ᵁ V) Γ(Y, Uf f) (y.app V a) * t = 0 → t = 0 := by
    intro f t ht
    let Yf := Γ(Y, Uf f)
    have := hYV.isLocalization_basicOpen (y.app V f.1)
    let _ : Algebra Γ(X, V) Yf :=
      ((algebraMap Γ(Y, y ⁻¹ᵁ V) Yf).comp (algebraMap Γ(X, V) Γ(Y, y ⁻¹ᵁ V))).toAlgebra
    have : IsScalarTower Γ(X, V) Γ(Y, y ⁻¹ᵁ V) Yf := IsScalarTower.of_algebraMap_eq' rfl
    have : Module.Flat Γ(Y, y ⁻¹ᵁ V) Yf :=
      IsLocalization.flat Yf (Submonoid.powers (y.app V f.1))
    have : Module.Flat Γ(X, V) Yf := Module.Flat.trans Γ(X, V) Γ(Y, y ⁻¹ᵁ V) Yf
    have har : IsSMulRegular Yf a := Module.Flat.isSMulRegular_of_nonZeroDivisors ha
    exact har.right_eq_zero_of_smul (by rw [Algebra.smul_def]; exact ht)
  intro s t hst
  refine Y.sheaf.eq_of_locally_eq' Uf O (fun f ↦ homOfLE (hUf f)) ?_ s t fun f ↦ ?_
  · rintro w ⟨hwV, hwU⟩
    obtain ⟨f, hfU, hwf⟩ := hV.exists_basicOpen_le ⟨y w, hwU⟩ hwV
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hfU⟩, ?_⟩
    change w ∈ Y.basicOpen _
    rw [← Scheme.preimage_basicOpen]
    exact hwf
  · have hUfa : IsAffineOpen (Uf f) := hYV.basicOpen (y.app V f.1)
    let af : Γ(Y, Uf f) := algebraMap Γ(Y, y ⁻¹ᵁ V) Γ(Y, Uf f) (y.app V a)
    have hL := hUfa.isLocalization_basicOpen af
    have hle' : Y.basicOpen af ≤ Y.basicOpen (y.app V a) := by
      change Y.basicOpen ((Y.presheaf.map (homOfLE (Y.basicOpen_le _) : Uf f ⟶ y ⁻¹ᵁ V).op)
        (y.app V a)) ≤ _
      rw [Scheme.basicOpen_res]
      exact inf_le_right
    have e : ∀ z : Γ(Y, O), algebraMap Γ(Y, Uf f) Γ(Y, Y.basicOpen af)
        (Y.presheaf.map (homOfLE (hUf f)).op z) =
          Y.presheaf.map (homOfLE hle').op (Y.presheaf.map (homOfLE h).op z) := by
      intro z
      change (Y.presheaf.map _) ((Y.presheaf.map _) z) = (Y.presheaf.map _) ((Y.presheaf.map _) z)
      simp only [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
    have h1 : algebraMap Γ(Y, Uf f) Γ(Y, Y.basicOpen af)
        (Y.presheaf.map (homOfLE (hUf f)).op s) =
        algebraMap Γ(Y, Uf f) Γ(Y, Y.basicOpen af) (Y.presheaf.map (homOfLE (hUf f)).op t) := by
      rw [e, e, hst]
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers af) h1
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
    rw [← hn, ← sub_eq_zero, ← mul_sub] at hc
    have hpow : ∀ n : ℕ, ∀ u : Γ(Y, Uf f), af ^ n * u = 0 → u = 0 := by
      intro n
      induction n with
      | zero => intro u hu; simpa using hu
      | succ n ih =>
        intro u hu
        exact ih u (hareg f _ (by rw [← mul_assoc, ← pow_succ']; exact hu))
    exact sub_eq_zero.mp (hpow n _ hc)

/-- Hartogs over a chart: if `a, b` is a regular sequence on `Γ(V)` (`V` affine) with
`D(a) ∪ D(b) ⊆ U`, then for every affine flat `y : Y ⟶ X` the restriction
`Γ(y⁻¹V) → Γ(y⁻¹(V ∩ U))` is bijective. -/
theorem bijective_restrict_preimage_of_basicOpen_sup_le {V : X.Opens} (hV : IsAffineOpen V)
    {a b : Γ(X, V)} (hab : X.basicOpen a ⊔ X.basicOpen b ≤ U)
    (hreg : IsWeaklyRegular Γ(X, V) [a, b]) {Y : Scheme.{u}} (y : Y ⟶ X) [IsAffineHom y]
    [Flat y] :
    Function.Bijective (Y.presheaf.map (homOfLE inf_le_left : y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U ⟶ y ⁻¹ᵁ V).op) := by
  have hYV : IsAffineOpen (y ⁻¹ᵁ V) := hV.preimage y
  have hflat : (y.app V).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE (P := @Flat) y inferInstance ⟨V, hV⟩ ⟨_, hYV⟩ le_rfl
  let := (y.app V).hom.toAlgebra
  have : Module.Flat Γ(X, V) Γ(Y, y ⁻¹ᵁ V) := hflat
  have hreg' : IsWeaklyRegular Γ(Y, y ⁻¹ᵁ V) [y.app V a, y.app V b] :=
    hreg.of_flat (S := Γ(Y, y ⁻¹ᵁ V))
  have htop := Scheme.bijective_restrict_basicOpen_sup_of_isCompact Y hYV.isCompact
    hYV.isQuasiSeparated hreg'
  have hDa : ∀ c : Γ(X, V), X.basicOpen c ≤ U →
      Y.basicOpen (y.app V c) ≤ y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U := fun c hc ↦ by
    rw [← Scheme.preimage_basicOpen]
    exact le_inf (y.preimage_mono (X.basicOpen_le _)) (y.preimage_mono hc)
  have hW : Y.basicOpen (y.app V a) ⊔ Y.basicOpen (y.app V b) ≤ y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U :=
    sup_le (hDa a (le_sup_left.trans hab)) (hDa b (le_sup_right.trans hab))
  have ha0 : a ∈ nonZeroDivisors Γ(X, V) := by
    have ha := ((isWeaklyRegular_cons_iff _ a [b]).mp hreg).1
    exact mem_nonZeroDivisors_iff_right.mpr fun z hz ↦
      ha.right_eq_zero_of_smul (by rw [smul_eq_mul, mul_comm, hz])
  have hinj := injective_restrict_preimage_basicOpen U hV ha0 y (hDa a (le_sup_left.trans hab))
  let r1 := Y.presheaf.map (homOfLE inf_le_left : y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U ⟶ y ⁻¹ᵁ V).op
  let r2 := Y.presheaf.map (homOfLE hW :
    Y.basicOpen (y.app V a) ⊔ Y.basicOpen (y.app V b) ⟶ y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U).op
  let r3 := Y.presheaf.map (homOfLE le_sup_left : Y.basicOpen (y.app V a) ⟶
    Y.basicOpen (y.app V a) ⊔ Y.basicOpen (y.app V b)).op
  have e1 : ∀ z, r2 (r1 z) = Y.presheaf.map (homOfLE (sup_le (Y.basicOpen_le _)
      (Y.basicOpen_le _)) : Y.basicOpen (y.app V a) ⊔ Y.basicOpen (y.app V b) ⟶
        y ⁻¹ᵁ V).op z := fun z ↦ by
    simp only [r1, r2, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  have e2 : ∀ z, r3 (r2 z) = Y.presheaf.map (homOfLE (hDa a (le_sup_left.trans hab))).op z :=
    fun z ↦ by
      simp only [r2, r3, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  have hr2 : Function.Injective r2 := fun s t hst ↦ hinj (by rw [← e2, ← e2, hst])
  refine ⟨fun s t hst ↦ htop.1 (by rw [← e1, ← e1]; exact congrArg r2 hst), fun s ↦ ?_⟩
  obtain ⟨t, ht⟩ := htop.2 (r2 s)
  exact ⟨t, hr2 (by rw [e1, ht])⟩

/-- Hartogs over a chart for the open immersion `Y ×_X U ⟶ Y`. -/
theorem bijective_pullbackFst_app_of_basicOpen_sup_le {V : X.Opens} (hV : IsAffineOpen V)
    {a b : Γ(X, V)} (hab : X.basicOpen a ⊔ X.basicOpen b ≤ U)
    (hB : IsWeaklyRegular Γ(X, V) [a, b]) {Y : Scheme.{u}} (y : Y ⟶ X) [IsAffineHom y]
    [Flat y] : Function.Bijective ((pullback.fst y U.ι).app (y ⁻¹ᵁ V)) := by
  have hH := bijective_restrict_preimage_of_basicOpen_sup_le U hV hab hB y
  have h1 := Scheme.Hom.appLE_appIso_inv (pullback.fst y U.ι)
    (le_refl ((pullback.fst y U.ι) ⁻¹ᵁ y ⁻¹ᵁ V))
  rw [← Scheme.Hom.app_eq_appLE] at h1
  have h2 : Function.Bijective (Y.presheaf.map
      (homOfLE ((Scheme.Hom.image_preimage_eq_opensRange_inf
        (pullback.fst y U.ι) (y ⁻¹ᵁ V)).trans_le inf_le_right) :
        (pullback.fst y U.ι) ''ᵁ (pullback.fst y U.ι ⁻¹ᵁ y ⁻¹ᵁ V) ⟶ y ⁻¹ᵁ V).op) := by
    refine (Scheme.bijective_presheaf_map_congr' ?_ inf_le_left _).mp hH
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_pullbackFst,
      Scheme.Opens.opensRange_ι, inf_comm]
  rw [← h1, ConcreteCategory.coe_comp] at h2
  exact (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso _) _).mp h2

end Chart

section FiniteEtale

variable {U : X.Opens} {W : Scheme.{u}} (w : W ⟶ U)

/-- Over an affine open `D ⊆ U`, a finite `w : W ⟶ U` has finite sections: `Γ(D) → Γ(w⁻¹D)` is
finite. -/
lemma finite_appLE_of_le [IsFinite w] {D : X.Opens} (hD : IsAffineOpen D) (hDU : D ≤ U)
    {O : W.Opens} (e : O ≤ (w ≫ U.ι) ⁻¹ᵁ D) (hO : O = (w ≫ U.ι) ⁻¹ᵁ D) :
    ((w ≫ U.ι).appLE D O e).hom.Finite := by
  rw [Scheme.Hom.comp_appLE]
  have hD' : IsAffineOpen (U.ι ⁻¹ᵁ D) :=
    hD.preimage_of_isOpenImmersion U.ι (by rwa [Scheme.Opens.opensRange_ι])
  have h1 : Function.Bijective (U.ι.app D) := by
    rw [Scheme.Opens.ι_app]
    refine Scheme.bijective_presheaf_map_of_eq _ ?_
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hDU]
  have h2 : (w.appLE (U.ι ⁻¹ᵁ D) O e).hom.Finite := by
    change ((w.app (U.ι ⁻¹ᵁ D) ≫ W.presheaf.map (homOfLE e).op).hom).Finite
    rw [CommRingCat.hom_comp]
    exact RingHom.Finite.comp
      (RingHom.Finite.of_surjective _ (Scheme.bijective_presheaf_map_of_eq _ hO).2)
      (w.finite_app _ hD')
  rw [CommRingCat.hom_comp]
  exact RingHom.Finite.comp h2 (RingHom.Finite.of_surjective _ h1.2)

/-- Over an affine open `D ⊆ U`, an étale `w : W ⟶ U` has étale sections. -/
lemma etale_appLE_of_le [IsFinite w] [Etale w] {D : X.Opens} (hD : IsAffineOpen D) (hDU : D ≤ U)
    {O : W.Opens} (e : O ≤ (w ≫ U.ι) ⁻¹ᵁ D) (hO : O = (w ≫ U.ι) ⁻¹ᵁ D) :
    ((w ≫ U.ι).appLE D O e).hom.Etale := by
  have hD' : IsAffineOpen (U.ι ⁻¹ᵁ D) :=
    hD.preimage_of_isOpenImmersion U.ι (by rwa [Scheme.Opens.opensRange_ι])
  have hO' : IsAffineOpen O := hO ▸ hD'.preimage w
  exact HasRingHomProperty.appLE (P := @Etale) (w ≫ U.ι) inferInstance ⟨D, hD⟩ ⟨O, hO'⟩ e

variable [IsLocallyNoetherian X]
  (hreg : ∀ x : X, x ∉ U → IsRegularLocalRing (X.presheaf.stalk x))
  (hU : ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x))
include hreg hU

/-- Purity over a chart: if `a, b` is a regular sequence on `Γ(V)` (`V` affine) with
`D(a) ∪ D(b) ⊆ U`, and `w : W ⟶ U` is finite étale, then `Γ(V) → Γ(W, w⁻¹(V ∩ U))` is finite
étale: its target has depth `≥ 2` (regularity of `a, b` is local on `W`), it is finite by
`Module.finite_of_isLocalization_pair`, and étale by purity at the primes of `V \ U`
(`Algebra.etale_of_isWeaklyRegular_of_forall_notMem`). -/
theorem finite_etale_app_of_basicOpen_sup_le {V : X.Opens} (hV : IsAffineOpen V)
    {a b : Γ(X, V)} (hab : X.basicOpen a ⊔ X.basicOpen b ≤ U)
    (hB : IsWeaklyRegular Γ(X, V) [a, b]) [IsFinite w] [Etale w] :
    ((w ≫ U.ι).app V).hom.Finite ∧ ((w ≫ U.ι).app V).hom.Etale := by
  set g := w ≫ U.ι with hg
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let C := Γ(W, g ⁻¹ᵁ V)
  let _ : Algebra Γ(X, V) C := (g.app V).hom.toAlgebra
  have hqc : IsCompact (g ⁻¹ᵁ V : Set W) := g.isCompact_preimage hV.isCompact
  have hqs : IsQuasiSeparated (g ⁻¹ᵁ V : Set W) := g.isQuasiSeparated_preimage hV.isQuasiSeparated
  have hpre : ∀ f : Γ(X, V), W.basicOpen (g.app V f) = g ⁻¹ᵁ X.basicOpen f := fun f ↦
    (Scheme.preimage_basicOpen g f).symm
  have hmap : ∀ f : Γ(X, V), Algebra.algebraMapSubmonoid C (Submonoid.powers f) =
      Submonoid.powers (g.app V f) := fun f ↦ Submonoid.map_powers _ _
  have hgU : g ⁻¹ᵁ U = ⊤ := by
    rw [hg, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
  -- local data at `f` with `D(f) ⊆ U`: `Γ(W, g⁻¹D(f))` is finite étale over `Γ(X, D(f))`
  have hloc : ∀ f : Γ(X, V), X.basicOpen f ≤ U →
      letI := ((algebraMap C Γ(W, W.basicOpen (g.app V f))).comp
        (algebraMap Γ(X, V) C)).toAlgebra
      Algebra.FormallyEtale Γ(X, V) Γ(W, W.basicOpen (g.app V f)) ∧
        Module.Flat Γ(X, V) Γ(W, W.basicOpen (g.app V f)) := by
    intro f hfU
    let Cf := Γ(W, W.basicOpen (g.app V f))
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := hV.isLocalization_basicOpen f
    let _ : Algebra Γ(X, V) Cf := ((algebraMap C Cf).comp (algebraMap Γ(X, V) C)).toAlgebra
    let _ : Algebra Γ(X, X.basicOpen f) Cf :=
      (g.appLE (X.basicOpen f) (W.basicOpen (g.app V f)) (hpre f).le).hom.toAlgebra
    have : IsScalarTower Γ(X, V) Γ(X, X.basicOpen f) Cf := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      change (g.app V ≫ W.presheaf.map _).hom = (X.presheaf.map _ ≫ g.appLE _ _ _).hom
      rw [Scheme.Hom.map_appLE]
      rfl
    have : Algebra.Etale Γ(X, X.basicOpen f) Cf :=
      etale_appLE_of_le w (hV.basicOpen f) hfU (hpre f).le (hpre f)
    have : Algebra.FormallyEtale Γ(X, V) Γ(X, X.basicOpen f) :=
      Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)
    have : Module.Flat Γ(X, V) Γ(X, X.basicOpen f) := IsLocalization.flat _ (Submonoid.powers f)
    exact ⟨Algebra.FormallyEtale.comp Γ(X, V) Γ(X, X.basicOpen f) Cf,
      Module.Flat.trans Γ(X, V) Γ(X, X.basicOpen f) Cf⟩
  -- `a, b` is regular on the `Γ(W, g⁻¹D(f))`
  have hregf : ∀ f : Γ(X, V), X.basicOpen f ≤ U →
      IsWeaklyRegular Γ(W, W.basicOpen (g.app V f))
        [W.presheaf.map (homOfLE (W.basicOpen_le (g.app V f))).op (g.app V a),
          W.presheaf.map (homOfLE (W.basicOpen_le (g.app V f))).op (g.app V b)] := by
    intro f hfU
    let _ := ((algebraMap C Γ(W, W.basicOpen (g.app V f))).comp
        (algebraMap Γ(X, V) C)).toAlgebra
    have := (hloc f hfU).2
    exact hB.of_flat (S := Γ(W, W.basicOpen (g.app V f)))
  -- the cover of `g⁻¹V` by the `g⁻¹D(f)`, `D(f) ⊆ U`
  let ι := {f : Γ(X, V) // X.basicOpen f ≤ U}
  let Uf : ι → W.Opens := fun f ↦ W.basicOpen (g.app V f.1)
  have hcover : g ⁻¹ᵁ V ≤ ⨆ f, Uf f := by
    intro z hz
    have hzU : g z ∈ U := by
      have : z ∈ g ⁻¹ᵁ U := by rw [hgU]; trivial
      exact this
    obtain ⟨f, hfU, hzf⟩ := hV.exists_basicOpen_le ⟨g z, hzU⟩ hz
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hfU⟩, ?_⟩
    change z ∈ W.basicOpen _
    rw [hpre]
    exact hzf
  have h2 : ∀ f h : ι, ∀ s : Γ(W, Uf f ⊓ Uf h),
      W.presheaf.map (homOfLE (inf_le_left.trans (W.basicOpen_le _))).op (g.app V a) * s = 0 →
        s = 0 := by
    intro f h s hs
    have hfh : X.basicOpen (f.1 * h.1) ≤ U := by
      rw [Scheme.basicOpen_mul]
      exact inf_le_left.trans f.2
    have hE : W.basicOpen (g.app V (f.1 * h.1)) = Uf f ⊓ Uf h := by
      rw [map_mul, Scheme.basicOpen_mul]
    let τ := W.presheaf.map (eqToHom hE).op
    have hτ : Function.Injective τ :=
      (ConcreteCategory.bijective_of_isIso (W.presheaf.map (eqToHom hE).op)).1
    have hx' := ((isWeaklyRegular_cons_iff _ _ _).mp (hregf _ hfh)).1
    have e1 : τ (W.presheaf.map (homOfLE (inf_le_left.trans (W.basicOpen_le _)) :
        Uf f ⊓ Uf h ⟶ g ⁻¹ᵁ V).op (g.app V a)) =
        W.presheaf.map (homOfLE (W.basicOpen_le _) :
          W.basicOpen (g.app V (f.1 * h.1)) ⟶ g ⁻¹ᵁ V).op (g.app V a) := by
      change (W.presheaf.map _ ≫ W.presheaf.map (eqToHom hE).op) (g.app V a) = _
      rw [← Functor.map_comp]
      rfl
    apply hτ
    rw [map_zero]
    apply hx'
    change _ * τ s = _ * 0
    rw [mul_zero, ← e1, ← map_mul, hs, map_zero]
  have hC : IsWeaklyRegular C [a, b] := by
    have := Scheme.isWeaklyRegular_of_le_iSup W Uf (fun f ↦ W.basicOpen_le _) hcover
      (a := g.app V a) (b := g.app V b) (fun f ↦ hregf f.1 f.2) h2
    exact (isWeaklyRegular_map_algebraMap_iff (R := Γ(X, V)) (S := C) (M := C) [a, b]).mp this
  -- finiteness
  have hDa : X.basicOpen a ≤ U := le_sup_left.trans hab
  have hDb : X.basicOpen b ≤ U := le_sup_right.trans hab
  have hfin : Module.Finite Γ(X, V) C := by
    have hxC : IsSMulRegular C a := ((isWeaklyRegular_cons_iff C a [b]).mp hC).1
    have : IsLocalization.Away a Γ(X, X.basicOpen a) := hV.isLocalization_basicOpen a
    have : IsLocalization.Away (g.app V a) Γ(W, W.basicOpen (g.app V a)) :=
      isLocalization_basicOpen_of_qcqs hqc hqs _
    have : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers a))
        Γ(W, W.basicOpen (g.app V a)) := by rw [hmap]; infer_instance
    let _ : Algebra Γ(X, V) Γ(W, W.basicOpen (g.app V a)) :=
      ((algebraMap C Γ(W, W.basicOpen (g.app V a))).comp (algebraMap Γ(X, V) C)).toAlgebra
    have : IsScalarTower Γ(X, V) C Γ(W, W.basicOpen (g.app V a)) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : Algebra Γ(X, X.basicOpen a) Γ(W, W.basicOpen (g.app V a)) :=
      (g.appLE (X.basicOpen a) (W.basicOpen (g.app V a)) (hpre a).le).hom.toAlgebra
    have : IsScalarTower Γ(X, V) Γ(X, X.basicOpen a) Γ(W, W.basicOpen (g.app V a)) := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      change (g.app V ≫ W.presheaf.map _).hom = (X.presheaf.map _ ≫ g.appLE _ _ _).hom
      rw [Scheme.Hom.map_appLE]
      rfl
    have : Module.Finite Γ(X, X.basicOpen a) Γ(W, W.basicOpen (g.app V a)) :=
      finite_appLE_of_le w (hV.basicOpen a) hDa (hpre a).le (hpre a)
    have : Algebra.Etale Γ(X, X.basicOpen a) Γ(W, W.basicOpen (g.app V a)) :=
      etale_appLE_of_le w (hV.basicOpen a) hDa (hpre a).le (hpre a)
    have : IsNoetherianRing Γ(X, X.basicOpen a) :=
      IsLocalization.isNoetherianRing (Submonoid.powers a) _ ‹_›
    have : Module.FinitePresentation Γ(X, X.basicOpen a) Γ(W, W.basicOpen (g.app V a)) :=
      Module.finitePresentation_of_finite _ _
    have : Module.Projective Γ(X, X.basicOpen a) Γ(W, W.basicOpen (g.app V a)) :=
      Module.Flat.projective_of_finitePresentation
    have : IsLocalization.Away b Γ(X, X.basicOpen b) := hV.isLocalization_basicOpen b
    have : IsLocalization.Away (g.app V b) Γ(W, W.basicOpen (g.app V b)) :=
      isLocalization_basicOpen_of_qcqs hqc hqs _
    have : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers b))
        Γ(W, W.basicOpen (g.app V b)) := by rw [hmap]; infer_instance
    let _ : Algebra Γ(X, V) Γ(W, W.basicOpen (g.app V b)) :=
      ((algebraMap C Γ(W, W.basicOpen (g.app V b))).comp (algebraMap Γ(X, V) C)).toAlgebra
    have : IsScalarTower Γ(X, V) C Γ(W, W.basicOpen (g.app V b)) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let _ : Algebra Γ(X, X.basicOpen b) Γ(W, W.basicOpen (g.app V b)) :=
      (g.appLE (X.basicOpen b) (W.basicOpen (g.app V b)) (hpre b).le).hom.toAlgebra
    have : IsScalarTower Γ(X, V) Γ(X, X.basicOpen b) Γ(W, W.basicOpen (g.app V b)) := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      change (g.app V ≫ W.presheaf.map _).hom = (X.presheaf.map _ ≫ g.appLE _ _ _).hom
      rw [Scheme.Hom.map_appLE]
      rfl
    have : Module.Finite Γ(X, X.basicOpen b) Γ(W, W.basicOpen (g.app V b)) :=
      finite_appLE_of_le w (hV.basicOpen b) hDb (hpre b).le (hpre b)
    exact Module.finite_of_isLocalization_pair hB hxC (Γ(X, X.basicOpen a))
      (Γ(W, W.basicOpen (g.app V a))) (Γ(X, X.basicOpen b)) (Γ(W, W.basicOpen (g.app V b)))
  refine ⟨hfin, ?_⟩
  -- étaleness: purity at the primes of `V \ U`
  let T : Set (Ideal Γ(X, V)) := {p | ∃ hp : p.IsPrime, hV.fromSpec ⟨p, hp⟩ ∈ U}
  refine Algebra.etale_of_isWeaklyRegular_of_forall_notMem hB hC T (fun Q _ hQ ↦ ?_)
    (fun p hpI hp ↦ ?_)
  · obtain ⟨hp, hpU⟩ := hQ
    obtain ⟨f, hfU, hpf⟩ := hV.exists_basicOpen_le ⟨_, hpU⟩ (hV.fromSpec_mem _)
    have hfp : f ∉ Q.comap (algebraMap Γ(X, V) C) := hV.fromSpec_mem_basicOpen_iff.mp hpf
    have hL : IsLocalization.Away (g.app V f) Γ(W, W.basicOpen (g.app V f)) :=
      isLocalization_basicOpen_of_qcqs hqc hqs _
    let _ := ((algebraMap C Γ(W, W.basicOpen (g.app V f))).comp
        (algebraMap Γ(X, V) C)).toAlgebra
    have := (hloc f hfU).1
    have : IsScalarTower Γ(X, V) C Γ(W, W.basicOpen (g.app V f)) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let e : Localization.Away (algebraMap Γ(X, V) C f) ≃ₐ[C] Γ(W, W.basicOpen (g.app V f)) :=
      IsLocalization.algEquiv (Submonoid.powers (g.app V f)) _ _
    have : Algebra.FormallyEtale Γ(X, V) (Localization.Away (algebraMap Γ(X, V) C f)) :=
      Algebra.FormallyEtale.of_equiv (e.restrictScalars Γ(X, V)).symm
    exact (Algebra.basicOpen_subset_etaleLocus_iff (R := Γ(X, V))).mpr this
      (show (⟨Q, ‹_›⟩ : PrimeSpectrum C) ∈ PrimeSpectrum.basicOpen (algebraMap Γ(X, V) C f)
        from hfp)
  · have hpU : hV.fromSpec ⟨p, hpI⟩ ∉ U := fun h ↦ hp ⟨hpI, h⟩
    obtain ⟨ha, hb⟩ := mem_of_fromSpec_notMem U hV hab ⟨p, hpI⟩ hpU
    have : IsRegularLocalRing (X.presheaf.stalk (hV.fromSpec ⟨p, hpI⟩)) := hreg _ hpU
    refine ⟨ha, hb, IsRegularLocalRing.of_ringEquiv
      (hV.localizationAtPrimeEquivStalk ⟨p, hpI⟩).symm, ?_⟩
    rw [ringKrullDim_eq_of_ringEquiv (hV.localizationAtPrimeEquivStalk ⟨p, hpI⟩)]
    exact hU _ hpU

end FiniteEtale

section Normalization

/-- Equal morphisms have equal `appLE`. -/
lemma Scheme.Hom.appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens)
    (V : X.Opens) (e₁ : V ≤ f ⁻¹ᵁ U) (e₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V e₁ = g.appLE U V e₂ := by
  subst h; rfl

/-- If `Γ(V) → Γ(f⁻¹V)` is integral (`V` affine), the relative normalization of `X` in `Y` has
the same sections over `V` as `Y`. -/
lemma Scheme.Hom.bijective_toNormalization_appLE {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f]
    [QuasiSeparated f] {V : X.Opens} (hV : IsAffineOpen V) (hint : (f.app V).hom.IsIntegral)
    (e : f ⁻¹ᵁ V ≤ f.toNormalization ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ V) :
    Function.Bijective (f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ V) (f ⁻¹ᵁ V) e) := by
  let := (f.app V).hom.toAlgebra
  have htop : integralClosure Γ(X, V) Γ(Y, f ⁻¹ᵁ V) = ⊤ := by
    rw [integralClosure_eq_top_iff, ← algebraMap_isIntegral_iff]
    exact hint
  rw [← f.normalizationObjIso_hom_val hV, ConcreteCategory.coe_comp]
  refine Function.Bijective.comp ⟨Subtype.val_injective, fun z ↦ ⟨⟨z, ?_⟩, rfl⟩⟩
    (ConcreteCategory.bijective_of_isIso _)
  rw [htop]
  exact Algebra.mem_top

/-- `f.app V` factors through the sections of the relative normalization. -/
lemma Scheme.Hom.fromNormalization_app_comp_toNormalization_appLE {X Y : Scheme.{u}}
    (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] (V : X.Opens)
    (e : f ⁻¹ᵁ V ≤ f.toNormalization ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ V) :
    f.fromNormalization.app V ≫ f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ V) (f ⁻¹ᵁ V) e =
      f.app V := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE]
  exact Scheme.Hom.appLE_congr_hom f.toNormalization_fromNormalization _ _ _ _

/-- Étaleness of `n.app V` transported along equalities of opens. -/
lemma etale_app_comp_eqToHom {N X : Scheme.{u}} (n : N ⟶ X) {V V' : X.Opens} (hVV : V' = V)
    {O : N.Opens} (h : O = n ⁻¹ᵁ V') (hn : (n.app V).hom.Etale) :
    ((n.app V' ≫ N.presheaf.map (eqToHom h).op).hom).Etale := by
  subst hVV; subst h; simpa using hn

variable {U : X.Opens} [IsLocallyNoetherian X]
  (hreg : ∀ x : X, x ∉ U → IsRegularLocalRing (X.presheaf.stalk x))
  (hU : ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x))
include hreg hU

/-- The extension of a finite étale `W ⟶ U` across `X \ U`: the relative normalization of `X` in
`W` is finite étale over `X`. -/
theorem finite_etale_fromNormalization {W : Scheme.{u}} (w : W ⟶ U) [IsFinite w] [Etale w] :
    IsFinite (w ≫ U.ι).fromNormalization ∧ Etale (w ≫ U.ι).fromNormalization := by
  set g := w ≫ U.ι with hg
  set n := g.fromNormalization
  choose V a b hxV hV hab hB using exists_isWeaklyRegular_basicOpen_sup_le hreg hU
  have hcov : ⨆ x, V x = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩
  have hn : ∀ x, (n.app (V x)).hom.Etale := by
    intro x
    obtain ⟨hfin, het⟩ :=
      finite_etale_app_of_basicOpen_sup_le w hreg hU (hV x) (hab x) (hB x)
    have e : g ⁻¹ᵁ V x ≤ g.toNormalization ⁻¹ᵁ n ⁻¹ᵁ V x := by
      rw [← Scheme.Hom.comp_preimage, g.toNormalization_fromNormalization]
    have hbij := g.bijective_toNormalization_appLE (hV x) hfin.to_isIntegral e
    have hc := g.fromNormalization_app_comp_toNormalization_appLE (V x) e
    have : IsIso (g.toNormalization.appLE (n ⁻¹ᵁ V x) (g ⁻¹ᵁ V x) e) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    have hn' : n.app (V x) = g.app (V x) ≫ inv (g.toNormalization.appLE _ _ e) := by
      rw [← hc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [hn', CommRingCat.hom_comp]
    exact RingHom.Etale.stableUnderComposition _ _ het
      (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _))
  have het : Etale n := by
    have : IsZariskiLocalAtTarget @Etale.{u} :=
      HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale.{u}) (Q := RingHom.Etale)
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Etale.{u}) V hcov]
    intro x
    have : IsAffine (V x) := hV x
    have : IsAffine (n ⁻¹ᵁ V x) := (hV x).preimage n
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale.{u}), morphismRestrict_appTop]
    exact etale_app_comp_eqToHom n (Scheme.Opens.ι_image_top _) _ (hn x)
  exact ⟨(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType n).mpr ⟨inferInstance, inferInstance⟩,
    het⟩

omit [IsLocallyNoetherian X] in
omit hreg hU in
/-- The sections of the relative normalization of `X` in `f : Y ⟶ X` over an affine open `V` are
the elements of `Γ(f⁻¹V)` integral over `Γ(V)`. -/
lemma Scheme.Hom.injective_toNormalization_appLE_and_range {Y : Scheme.{u}} (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] {V : X.Opens} (hV : IsAffineOpen V)
    (e : f ⁻¹ᵁ V ≤ f.toNormalization ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ V) :
    Function.Injective (f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ V) (f ⁻¹ᵁ V) e) ∧
      ∀ z, z ∈ Set.range (f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ V) (f ⁻¹ᵁ V) e) ↔
        (f.app V).hom.IsIntegralElem z := by
  let := (f.app V).hom.toAlgebra
  rw [← f.normalizationObjIso_hom_val hV, ConcreteCategory.coe_comp]
  have hbij := ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hV).hom
  refine ⟨Subtype.val_injective.comp hbij.1, fun z ↦ ⟨?_, fun hz ↦ ?_⟩⟩
  · rintro ⟨w, rfl⟩
    exact ((f.normalizationObjIso hV).hom w).2
  · obtain ⟨w, hw⟩ := hbij.2 ⟨z, hz⟩
    exact ⟨w, congrArg Subtype.val hw⟩

omit [IsLocallyNoetherian X] in
omit hreg hU in
/-- Let `y : Y ⟶ X` be integral and `j : Z ⟶ Y` with `j ≫ y` quasi-compact and quasi-separated.
If `X` is covered by affine opens `Vᵢ` such that `Γ(y⁻¹Vᵢ) → Γ(j⁻¹y⁻¹Vᵢ)` is injective with image
containing every element integral over `Γ(Vᵢ)`, then `Y` is the relative normalization of `X` in
`Z`. -/
lemma Scheme.Hom.isIso_normalizationDesc_of_injective {Y Z : Scheme.{u}} (j : Z ⟶ Y)
    (y : Y ⟶ X) [IsIntegralHom y] [QuasiCompact (j ≫ y)] [QuasiSeparated (j ≫ y)] {ι : Type*}
    (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hcov : ⨆ i, V i = ⊤)
    (hj : ∀ i, Function.Injective (j.app (y ⁻¹ᵁ V i)))
    (hint : ∀ i (z : Γ(Z, j ⁻¹ᵁ y ⁻¹ᵁ V i)), ((j ≫ y).app (V i)).hom.IsIntegralElem z →
      z ∈ Set.range (j.app (y ⁻¹ᵁ V i))) :
    IsIso ((j ≫ y).normalizationDesc j y rfl) := by
  have hcov' : ⨆ i, y ⁻¹ᵁ V i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme.{u}) _ hcov').mpr fun i ↦ ?_
  have hYV : IsAffineOpen (y ⁻¹ᵁ V i) := (hV i).preimage y
  change IsIso (((j ≫ y).normalizationDesc j y rfl) ∣_ y ⁻¹ᵁ V i)
  rw [isIso_morphismRestrict_iff_isIso_app _ hYV, ConcreteCategory.isIso_iff_bijective]
  have e : (j ≫ y) ⁻¹ᵁ V i ≤ (j ≫ y).toNormalization ⁻¹ᵁ (j ≫ y).fromNormalization ⁻¹ᵁ V i := by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
  have hN := (j ≫ y).injective_toNormalization_appLE_and_range (hV i) e
  have hO : ((j ≫ y).normalizationDesc j y rfl) ⁻¹ᵁ y ⁻¹ᵁ V i =
      (j ≫ y).fromNormalization ⁻¹ᵁ V i := by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.normalizationDesc_comp]
  have key : ∀ (O : (j ≫ y).normalization.Opens)
      (e' : (j ≫ y) ⁻¹ᵁ V i ≤ (j ≫ y).toNormalization ⁻¹ᵁ O),
      O = (j ≫ y).fromNormalization ⁻¹ᵁ V i →
        Function.Injective ((j ≫ y).toNormalization.appLE O ((j ≫ y) ⁻¹ᵁ V i) e') ∧
        ∀ z, z ∈ Set.range ((j ≫ y).toNormalization.appLE O ((j ≫ y) ⁻¹ᵁ V i) e') ↔
          ((j ≫ y).app (V i)).hom.IsIntegralElem z := by
    rintro O e' rfl
    exact hN
  have e'' : (j ≫ y) ⁻¹ᵁ V i ≤
      (j ≫ y).toNormalization ⁻¹ᵁ ((j ≫ y).normalizationDesc j y rfl) ⁻¹ᵁ y ⁻¹ᵁ V i := by
    rw [hO]; exact e
  obtain ⟨hinj, hrange⟩ := key _ e'' hO
  have hcomp : ((j ≫ y).normalizationDesc j y rfl).app (y ⁻¹ᵁ V i) ≫
      (j ≫ y).toNormalization.appLE _ ((j ≫ y) ⁻¹ᵁ V i) e'' = j.app (y ⁻¹ᵁ V i) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE]
    exact Scheme.Hom.appLE_congr_hom ((j ≫ y).toNormalization_normalizationDesc _ _ rfl) _ _ _ _
  have hcomp' : ∀ w, (j ≫ y).toNormalization.appLE _ ((j ≫ y) ⁻¹ᵁ V i) e''
      (((j ≫ y).normalizationDesc j y rfl).app (y ⁻¹ᵁ V i) w) = j.app (y ⁻¹ᵁ V i) w := fun w ↦ by
    rw [← hcomp]; rfl
  refine ⟨fun w w' hww' ↦ hj i ?_, fun w ↦ ?_⟩
  · rw [← hcomp', ← hcomp', hww']
  · obtain ⟨b, hb⟩ := hint i _ ((hrange _).mp ⟨w, rfl⟩)
    exact ⟨b, hinj (by rw [hcomp', hb])⟩

omit [IsLocallyNoetherian X] in
omit hreg hU in
/-- Let `y : Y ⟶ X` be integral and `j : Z ⟶ Y` with `j ≫ y` quasi-compact and quasi-separated.
If `X` is covered by affine opens `Vᵢ` with `Γ(y⁻¹Vᵢ) → Γ(j⁻¹y⁻¹Vᵢ)` bijective, then `Y` is the
relative normalization of `X` in `Z`. -/
lemma Scheme.Hom.isIso_normalizationDesc_of_bijective {Y Z : Scheme.{u}} (j : Z ⟶ Y)
    (y : Y ⟶ X) [IsIntegralHom y] [QuasiCompact (j ≫ y)] [QuasiSeparated (j ≫ y)] {ι : Type*}
    (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hcov : ⨆ i, V i = ⊤)
    (hj : ∀ i, Function.Bijective (j.app (y ⁻¹ᵁ V i))) :
    IsIso ((j ≫ y).normalizationDesc j y rfl) :=
  Scheme.Hom.isIso_normalizationDesc_of_injective j y V hV hcov (fun i ↦ (hj i).1)
    fun i z _ ↦ (hj i).2 z

/-- For `y : Y ⟶ X` finite étale, `Y` is the relative normalization of `X` in `Y ×_X U`
(Hartogs). -/
theorem isIso_normalizationDesc_pullbackFst {Y : Scheme.{u}} (y : Y ⟶ X) [IsFinite y]
    [Etale y] :
    IsIso ((pullback.fst y U.ι ≫ y).normalizationDesc (pullback.fst y U.ι) y rfl) := by
  choose V a b hxV hV hab hB using exists_isWeaklyRegular_basicOpen_sup_le hreg hU
  have hcov : ⨆ x, V x = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩
  exact Scheme.Hom.isIso_normalizationDesc_of_bijective _ y V hV hcov fun x ↦
    bijective_pullbackFst_app_of_basicOpen_sup_le U (hV x) (hab x) (hB x) y

omit hreg hU in
/-- Faithfulness of base change to `U` for finite étale schemes, when `Y₁` is the relative
normalization of `X` in `Y₁ ×_X U`. -/
theorem pullbackFst_cancel {Y₁ Y₂ : Scheme.{u}} (y₁ : Y₁ ⟶ X) (y₂ : Y₂ ⟶ X) [IsFinite y₁]
    [IsFinite y₂]
    [IsIso ((pullback.fst y₁ U.ι ≫ y₁).normalizationDesc (pullback.fst y₁ U.ι) y₁ rfl)]
    {ψ ψ' : Y₁ ⟶ Y₂} (hψ : ψ ≫ y₂ = y₁) (hψ' : ψ' ≫ y₂ = y₁)
    (h : pullback.fst y₁ U.ι ≫ ψ = pullback.fst y₁ U.ι ≫ ψ') : ψ = ψ' := by
  rw [← cancel_epi ((pullback.fst y₁ U.ι ≫ y₁).normalizationDesc (pullback.fst y₁ U.ι) y₁ rfl)]
  refine Scheme.Hom.normalization.hom_ext _ _ _ y₂ ?_ ?_ ?_
  · rw [Scheme.Hom.toNormalization_normalizationDesc_assoc,
      Scheme.Hom.toNormalization_normalizationDesc_assoc]
    exact h
  · rw [Category.assoc, hψ, Scheme.Hom.normalizationDesc_comp]
  · rw [Category.assoc, hψ', Scheme.Hom.normalizationDesc_comp]

omit hreg hU in
/-- Fullness of base change to `U` for finite étale schemes, when `Y₁` is the relative
normalization of `X` in `Y₁ ×_X U`. -/
theorem exists_pullbackFst_comp_eq {Y₁ Y₂ : Scheme.{u}} (y₁ : Y₁ ⟶ X) (y₂ : Y₂ ⟶ X)
    [IsFinite y₁] [IsFinite y₂]
    [IsIso ((pullback.fst y₁ U.ι ≫ y₁).normalizationDesc (pullback.fst y₁ U.ι) y₁ rfl)]
    (φ : pullback y₁ U.ι ⟶ pullback y₂ U.ι) (hφ : φ ≫ pullback.snd y₂ U.ι = pullback.snd y₁ U.ι) :
    ∃ ψ : Y₁ ⟶ Y₂, ψ ≫ y₂ = y₁ ∧ pullback.fst y₁ U.ι ≫ ψ = φ ≫ pullback.fst y₂ U.ι := by
  have H : pullback.fst y₁ U.ι ≫ y₁ = (φ ≫ pullback.fst y₂ U.ι) ≫ y₂ := by
    rw [Category.assoc, pullback.condition, pullback.condition, reassoc_of% hφ]
  let d₁ := (pullback.fst y₁ U.ι ≫ y₁).normalizationDesc (pullback.fst y₁ U.ι) y₁ rfl
  let ψ₀ := (pullback.fst y₁ U.ι ≫ y₁).normalizationDesc (φ ≫ pullback.fst y₂ U.ι) y₂ H
  refine ⟨inv d₁ ≫ ψ₀, ?_, ?_⟩
  · rw [Category.assoc, Scheme.Hom.normalizationDesc_comp, IsIso.inv_comp_eq,
      Scheme.Hom.normalizationDesc_comp]
  · have : pullback.fst y₁ U.ι ≫ inv d₁ = (pullback.fst y₁ U.ι ≫ y₁).toNormalization := by
      rw [IsIso.comp_inv_eq, Scheme.Hom.toNormalization_normalizationDesc]
    rw [reassoc_of% this, Scheme.Hom.toNormalization_normalizationDesc]

omit hreg hU in
/-- Base change of étale coverings from `X` to `U` is faithful if every étale covering `Y` of `X`
is the relative normalization of `X` in `Y ×_X U`. -/
theorem faithful_pullback_of_isIso_normalizationDesc
    (H : ∀ {Y : Scheme.{u}} (y : Y ⟶ X) [IsFinite y] [Etale y],
      IsIso ((pullback.fst y U.ι ≫ y).normalizationDesc (pullback.fst y U.ι) y rfl)) :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ U.ι).Faithful where
  map_injective {Y₁ Y₂} ψ ψ' h := by
    have : IsFinite (Y₁.hom : Y₁.left ⟶ X) := Y₁.prop.1
    have : Etale (Y₁.hom : Y₁.left ⟶ X) := Y₁.prop.2
    have : IsFinite (Y₂.hom : Y₂.left ⟶ X) := Y₂.prop.1
    have := H (Y₁.hom : Y₁.left ⟶ X)
    ext1
    refine pullbackFst_cancel (U := U) Y₁.hom Y₂.hom (MorphismProperty.Over.w ψ)
      (MorphismProperty.Over.w ψ') ?_
    rw [← MorphismProperty.Over.pullback_map_left_fst U _ ψ,
      ← MorphismProperty.Over.pullback_map_left_fst U _ ψ', h]

omit hreg hU in
/-- Base change of étale coverings from `X` to `U` is full if every étale covering `Y` of `X`
is the relative normalization of `X` in `Y ×_X U`. -/
theorem full_pullback_of_isIso_normalizationDesc
    (H : ∀ {Y : Scheme.{u}} (y : Y ⟶ X) [IsFinite y] [Etale y],
      IsIso ((pullback.fst y U.ι ≫ y).normalizationDesc (pullback.fst y U.ι) y rfl)) :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ U.ι).Full where
  map_surjective {Y₁ Y₂} φ := by
    have : IsFinite (Y₁.hom : Y₁.left ⟶ X) := Y₁.prop.1
    have : Etale (Y₁.hom : Y₁.left ⟶ X) := Y₁.prop.2
    have : IsFinite (Y₂.hom : Y₂.left ⟶ X) := Y₂.prop.1
    have := H (Y₁.hom : Y₁.left ⟶ X)
    obtain ⟨ψ, hψ, hfst⟩ := exists_pullbackFst_comp_eq (U := U) Y₁.hom Y₂.hom φ.left
      (MorphismProperty.Over.w φ)
    refine ⟨MorphismProperty.Over.homMk ψ hψ trivial, ?_⟩
    ext1
    apply pullback.hom_ext
    · exact (MorphismProperty.Over.pullback_map_left_fst U _ _).trans hfst
    · exact (MorphismProperty.Over.pullback_map_left_snd U _ _).trans
        (MorphismProperty.Over.w φ).symm

/-- Purity, faithfulness: base change of étale coverings from `X` to `U` is faithful. -/
theorem faithful_pullback_of_isRegularLocalRing :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ U.ι).Faithful :=
  faithful_pullback_of_isIso_normalizationDesc fun y _ _ ↦
    isIso_normalizationDesc_pullbackFst hreg hU y

/-- Purity, fullness: base change of étale coverings from `X` to `U` is full. -/
theorem full_pullback_of_isRegularLocalRing :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ U.ι).Full :=
  full_pullback_of_isIso_normalizationDesc fun y _ _ ↦
    isIso_normalizationDesc_pullbackFst hreg hU y

/-- Purity, essential surjectivity: every étale covering of `U` extends to an étale covering of
`X`, namely the relative normalization of `X` in it. -/
theorem essSurj_pullback_of_isRegularLocalRing :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ U.ι).EssSurj where
  mem_essImage W := by
    let w : W.left ⟶ U := W.hom
    have : IsFinite w := W.prop.1
    have : Etale w := W.prop.2
    obtain ⟨hfin, het⟩ := finite_etale_fromNormalization hreg hU w
    have hcomp : pullback.fst (w ≫ U.ι) U.ι ≫ w = pullback.snd (w ≫ U.ι) U.ι := by
      rw [← cancel_mono U.ι, Category.assoc]
      exact pullback.condition
    let l : W.left ⟶ pullback (w ≫ U.ι) U.ι := pullback.lift (𝟙 _) w (by simp)
    have : IsIso l := ⟨⟨pullback.fst (w ≫ U.ι) U.ι, pullback.lift_fst _ _ _, by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, pullback.lift_snd, hcomp, Category.id_comp]⟩⟩
    have : IsIntegralHom (pullback.snd (w ≫ U.ι) U.ι) := by
      rw [← hcomp]; infer_instance
    let E : W.left ⟶ pullback (w ≫ U.ι).fromNormalization U.ι :=
      l ≫ (pullback.snd (w ≫ U.ι) U.ι).toNormalization ≫ (w ≫ U.ι).normalizationPullback U.ι
    have : IsIso E := inferInstance
    have hE : E ≫ pullback.snd (w ≫ U.ι).fromNormalization U.ι = w := by
      simp only [E, l, Category.assoc, Scheme.Hom.normalizationPullback_snd,
        Scheme.Hom.toNormalization_fromNormalization, pullback.lift_snd]
    let Y : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ X :=
      MorphismProperty.Over.mk ⊤ (w ≫ U.ι).fromNormalization ⟨hfin, het⟩
    refine ⟨Y, ⟨MorphismProperty.Over.isoMk (asIso E).symm ?_⟩⟩
    change inv E ≫ w = pullback.snd (w ≫ U.ι).fromNormalization U.ι
    rw [IsIso.inv_comp_eq, hE]

end Normalization

/-- **Purity** (SGA 1 X.3.3; SGA 2 X.3.4; Stacks 0BMB). Let `X` be a locally noetherian scheme
and `U ⊆ X` an open such that `𝒪_{X,x}` is regular of dimension `≥ 2` at every point `x ∉ U`.
Then `X' ↦ X' ×_X U` is an equivalence from finite étale `X`-schemes to finite étale `U`-schemes.
The inverse is the relative normalization of `X` in a finite étale `U`-scheme. -/
theorem isEquivalence_pullback_of_isRegularLocalRing [IsLocallyNoetherian X] (U : X.Opens)
    (hreg : ∀ x : X, x ∉ U → IsRegularLocalRing (X.presheaf.stalk x))
    (hU : ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x)) :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ U.ι).IsEquivalence := by
  have := full_pullback_of_isRegularLocalRing hreg hU
  have := faithful_pullback_of_isRegularLocalRing hreg hU
  have := essSurj_pullback_of_isRegularLocalRing hreg hU
  exact { }

/-- Purity for schemes of dimension `≤ 2`, a special case of
`isEquivalence_pullback_of_isRegularLocalRing`. -/
theorem isEquivalence_pullback_of_ringKrullDim_le_two [IsLocallyNoetherian X] (U : X.Opens)
    (hreg : ∀ x : X, x ∉ U → IsRegularLocalRing (X.presheaf.stalk x))
    (_hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2)
    (hU : ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x)) :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ U.ι).IsEquivalence :=
  isEquivalence_pullback_of_isRegularLocalRing U hreg hU

end AlgebraicGeometry
