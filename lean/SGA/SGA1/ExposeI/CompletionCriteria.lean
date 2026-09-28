/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeI.Etale
import SGA.SGA1.ExposeI.QuasiFinite
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeIV.Completion
import SGA.SGA1.ExposeIV.CompletionCriterion
import SGA.Foundations.Formal.AdicRing
import SGA.Foundations.Formal.CompletionNoetherian

/-!
# SGA 1, Exposé I: criteria through completions

For a local homomorphism `A → B` of noetherian local rings, with completions `Â → B̂`
(`completionMap`):

* I.2.1, (i) ⇔ (iii) (`finite_quotient_iff_finite_completion`): `A → B` is quasi-finite iff `B̂`
  is finite over `Â`. The residue fields and the `𝔪_A`-adic topology do not change under
  completion, and complete Nakayama gives finiteness.
* I.3.7, completed form (`isUnramifiedLocalHom_iff_surjective_completionMap`): with trivial
  residue field extension, `A → B` is unramified iff `Â → B̂` is surjective (complete Nakayama,
  since `B̂/𝔪_A B̂` is the residue field).
* I.4.2 (`isEtaleLocalHom_iff_completion`): `A → B` is étale iff `Â → B̂` is. Flatness is the
  completion criterion IV.5.8 (Exposé IV); for unramifiedness, `B̂` is faithfully flat over `B`.
* I.4.4 (`isEtaleLocalHom_iff_bijective_completionMap`): with trivial residue field extension,
  `A → B` is étale iff `Â → B̂` is an isomorphism.
* I.9.4 (`isReduced_completion_of_etale`): if `A → B` is étale and `Â` is reduced, so is `B̂`.
-/

universe u

namespace SGA.SGA1.ExposeI

open IsLocalRing AdicCompletion

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

/-- The map of completions `Â → B̂`, as a map of `A`-algebras. -/
noncomputable def completionAlgHom :
    AdicCompletion (maximalIdeal A) A →ₐ[A] AdicCompletion (maximalIdeal B) B :=
  { completionMap A B with
    commutes' a := by
      rw [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, completionMap_algebraMap, ← IsScalarTower.algebraMap_apply] }

lemma completionAlgHom_apply (x : AdicCompletion (maximalIdeal A) A) :
    completionAlgHom A B x = completionMap A B x := rfl

/-- `B̂` is `𝔪_A`-adically separated as an `A`-module. -/
instance isHausdorff_maximalIdeal_completion :
    IsHausdorff (maximalIdeal A) (AdicCompletion (maximalIdeal B) B) where
  haus' x hx := by
    refine IsHausdorff.haus' (I := maximalIdeal B) x fun n ↦ ?_
    have := (hx n)
    rw [SModEq.zero] at this ⊢
    refine Submodule.smul_induction_on this (fun a ha y _ ↦ ?_) fun y z hy hz ↦ add_mem hy hz
    rw [← algebraMap_smul B a y]
    exact Submodule.smul_mem_smul (maximalIdeal_pow_le_comap A B n ha) trivial

omit [IsLocalHom (algebraMap A B)] in
/-- `𝔪_A B̂ = 𝔪_B̂` when `𝔪_A B = 𝔪_B`. -/
lemma smul_top_eq_maximalIdeal_completion [IsNoetherianRing B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    (maximalIdeal A • ⊤ : Submodule A (AdicCompletion (maximalIdeal B) B)) =
      (maximalIdeal (AdicCompletion (maximalIdeal B) B)).restrictScalars A := by
  rw [Ideal.smul_top_eq_map, AdicCompletion.maximalIdeal_eq_map, ← hm, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- The canonical map `Â → B̂` is compatible with the truncations, in the sense of IV.5.8. -/
lemma isCompletionMap_completionMap :
    ExposeIV.IsCompletionMap (map_maximalIdeal_le (algebraMap A B)) (completionMap A B) :=
  fun n x ↦ evalₐ_completionMap A B n x

variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- I.3.7, necessity, completed form: if `A → B` is an unramified local homomorphism of
noetherian local rings with trivial residue field extension, then `Â → B̂` is surjective, i.e.
`B̂` is a quotient of `Â`. -/
theorem surjective_completionMap_of_isUnramifiedLocalHom (h : IsUnramifiedLocalHom A B)
    (hk : Function.Surjective (ResidueField.map (algebraMap A B))) :
    Function.Surjective (completionMap A B) := by
  have : IsPrecomplete (maximalIdeal A) (AdicCompletion (maximalIdeal A) A) :=
    (AdicCompletion.isAdicComplete (maximalIdeal A).fg_of_isNoetherianRing).toIsPrecomplete
  let f := (completionAlgHom A B).toLinearMap
  refine surjective_of_mkQ_comp_surjective (I := maximalIdeal A) (f := f) fun z ↦ ?_
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
  obtain ⟨b, hb⟩ := (AdicCompletion.residueField_map_bijective B).2 (residue _ z)
  obtain ⟨b, rfl⟩ := residue_surjective b
  obtain ⟨a, ha⟩ := hk (residue B b)
  obtain ⟨a, rfl⟩ := residue_surjective a
  refine ⟨algebraMap A _ a, ?_⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, f,
    AlgHom.toLinearMap_apply, AlgHom.commutes]
  rw [Submodule.Quotient.eq, smul_top_eq_maximalIdeal_completion A B h.1,
    Submodule.restrictScalars_mem, ← residue_eq_zero_iff, map_sub, sub_eq_zero,
    IsScalarTower.algebraMap_apply A B (AdicCompletion (maximalIdeal B) B), ← hb,
    ← ha, ResidueField.map_residue, ResidueField.map_residue]

/-- I.3.7, completed form: let `A → B` be a local homomorphism of noetherian local rings with
trivial residue field extension. Then `A → B` is unramified iff `B̂` is a quotient of `Â`. (SGA's
alternative hypothesis, `k(A)` algebraically closed, reduces to this one: both sides force the
residue field extension to be trivial.) -/
theorem isUnramifiedLocalHom_iff_surjective_completionMap
    (hk : Function.Bijective (ResidueField.map (algebraMap A B))) :
    IsUnramifiedLocalHom A B ↔ Function.Surjective (completionMap A B) :=
  ⟨fun h ↦ surjective_completionMap_of_isUnramifiedLocalHom A B h hk.2,
    fun h ↦ (isUnramifiedLocalHom_of_surjective_completionMap h).1⟩

/-- I.4.2 and I.4.4, flatness (from IV.5.8): `A → B` is flat iff `B̂` is flat over `Â`. -/
theorem flat_iff_flat_completion :
    Module.Flat A B ↔
      letI := Module.compHom (AdicCompletion (maximalIdeal B) B) (completionMap A B)
      Module.Flat (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) :=
  ExposeIV.flat_iff_flat_completion (M := B) (maximalIdeal A) (maximalIdeal B)
    (map_maximalIdeal_le _) (maximalIdeal_le_jacobson _) (completionMap A B)
    (isCompletionMap_completionMap A B)

/-- I.4.4, completed form: let `A → B` be a local homomorphism of noetherian local rings with
trivial residue field extension. Then `A → B` is étale iff `Â → B̂` is an isomorphism. (SGA's
alternative hypothesis, `k(A)` algebraically closed, reduces to this one: both sides force the
residue field extension to be trivial.) -/
theorem isEtaleLocalHom_iff_bijective_completionMap
    (hk : Function.Bijective (ResidueField.map (algebraMap A B))) :
    IsEtaleLocalHom A B ↔ Function.Bijective (completionMap A B) := by
  constructor
  · intro h
    refine ⟨fun x y hxy ↦ AdicCompletion.ext_evalₐ fun n ↦ ?_,
      surjective_completionMap_of_isUnramifiedLocalHom A B h.2 hk.2⟩
    have := congrArg (evalₐ (maximalIdeal B) n) hxy
    rw [evalₐ_completionMap, evalₐ_completionMap] at this
    exact (bijective_quotientMap_pow_of_isEtaleLocalHom h (Or.inl hk) n).1 this
  · intro hbij
    refine ⟨(flat_iff_flat_completion A B).mpr ?_,
      (isUnramifiedLocalHom_of_surjective_completionMap hbij.2).1⟩
    let := Module.compHom (AdicCompletion (maximalIdeal B) B) (completionMap A B)
    let f : AdicCompletion (maximalIdeal A) A →ₗ[AdicCompletion (maximalIdeal A) A]
        AdicCompletion (maximalIdeal B) B :=
      { toFun := completionMap A B
        map_add' := map_add _
        map_smul' a x := by
          rw [smul_eq_mul, map_mul]
          rfl }
    exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective f hbij).symm

/-- The residue field isomorphism `k(A) ≅ k(Â)`. -/
noncomputable def residueFieldEquivCompletion (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    ResidueField R ≃+* ResidueField (AdicCompletion (maximalIdeal R) R) :=
  RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective R)

section Completion

local notation "Ah" => AdicCompletion (maximalIdeal A) A
local notation "Bh" => AdicCompletion (maximalIdeal B) B

/-- The square of residue fields `k(A) → k(B)`, `k(Â) → k(B̂)` commutes. -/
lemma residueField_map_completionMap_comp :
    (ResidueField.map (completionMap A B)).comp
      (residueFieldEquivCompletion A : ResidueField A →+* ResidueField Ah) =
    (residueFieldEquivCompletion B : ResidueField B →+* ResidueField Bh).comp
      (ResidueField.map (algebraMap A B)) := by
  ext x
  obtain ⟨y, rfl⟩ := residue_surjective x
  simp only [residueFieldEquivCompletion, RingHom.coe_comp, RingHom.coe_coe,
    Function.comp_apply, RingEquiv.ofBijective_apply, ResidueField.map_residue]
  exact congrArg _ (completionMap_algebraMap A B y)

lemma residueField_map_comp_symm :
    (ResidueField.map (algebraMap A B)).comp
      ((residueFieldEquivCompletion A).symm : ResidueField Ah →+* ResidueField A) =
    ((residueFieldEquivCompletion B).symm : ResidueField Bh →+* ResidueField B).comp
      (ResidueField.map (completionMap A B)) := by
  ext x
  obtain ⟨y, rfl⟩ := (residueFieldEquivCompletion A).surjective x
  have := congrArg (· y) (residueField_map_completionMap_comp A B)
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at this
  simp [this]

omit [IsLocalHom (algebraMap A B)] [IsNoetherianRing A] in
/-- `B̂` is faithfully flat over `B`. -/
lemma faithfullyFlat_completion : Module.FaithfullyFlat B Bh := by
  have := ExposeIV.flat_adicCompletion (maximalIdeal B)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

omit [IsNoetherianRing A] in
/-- Ideals of `B` are contracted from `B̂`. -/
lemma comap_map_completion (I : Ideal B) : (I.map (algebraMap B Bh)).comap (algebraMap B Bh) = I :=
  have := faithfullyFlat_completion B
  Ideal.comap_map_eq_self_of_faithfullyFlat I

omit [IsNoetherianRing B] in
/-- `𝔪_Â B̂ = (𝔪_A B) B̂`. -/
lemma map_maximalIdeal_completionMap :
    (maximalIdeal Ah).map (completionMap A B) =
      ((maximalIdeal A).map (algebraMap A B)).map (algebraMap B Bh) := by
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, Ideal.map_map,
    show (completionMap A B).comp (algebraMap A Ah) = (algebraMap B Bh).comp (algebraMap A B) from
      RingHom.ext (completionMap_algebraMap A B)]

/-- `𝔪_Â B̂ = 𝔪_B̂` iff `𝔪_A B = 𝔪_B`. -/
lemma map_maximalIdeal_completionMap_eq_iff :
    (maximalIdeal Ah).map (completionMap A B) = maximalIdeal Bh ↔
      (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
  rw [map_maximalIdeal_completionMap, AdicCompletion.maximalIdeal_eq_map]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rw [← comap_map_completion B ((maximalIdeal A).map _), h, comap_map_completion]

/-- I.4.2, unramified part: `A → B` is unramified (I.3.2 b)) iff `Â → B̂` is. The residue fields
do not change under completion, and `𝔪_A B̂ = 𝔪_B B̂` iff `𝔪_A B = 𝔪_B` since `B̂` is faithfully
flat over `B`. -/
theorem isUnramifiedLocalHom_iff_completion :
    letI := (completionMap A B).toAlgebra
    haveI : IsLocalHom (algebraMap Ah Bh) := isLocalHom_completionMap A B
    IsUnramifiedLocalHom A B ↔ IsUnramifiedLocalHom Ah Bh := by
  let := (completionMap A B).toAlgebra
  have : IsLocalHom (algebraMap Ah Bh) := isLocalHom_completionMap A B
  have he := residueField_map_completionMap_comp A B
  have he' := residueField_map_comp_symm A B
  refine and_congr (map_maximalIdeal_completionMap_eq_iff A B).symm
    (and_congr ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩ ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩)
  · exact Module.Finite.of_equiv_equiv _ _ he
  · exact Module.Finite.of_equiv_equiv _ _ he'
  · exact Algebra.IsSeparable.of_equiv_equiv _ _ he
  · exact Algebra.IsSeparable.of_equiv_equiv _ _ he'

/-- I.4.2: a local homomorphism `A → B` of noetherian local rings is étale (flat and unramified,
I.4.1 b)) iff `Â → B̂` is. Flatness is IV.5.8 (Exposé IV), unramifiedness
`isUnramifiedLocalHom_iff_completion`. -/
theorem isEtaleLocalHom_iff_completion :
    letI := (completionMap A B).toAlgebra
    haveI : IsLocalHom (algebraMap Ah Bh) := isLocalHom_completionMap A B
    IsEtaleLocalHom A B ↔ IsEtaleLocalHom Ah Bh := by
  let := (completionMap A B).toAlgebra
  have : IsLocalHom (algebraMap Ah Bh) := isLocalHom_completionMap A B
  exact and_congr (flat_iff_flat_completion A B) (isUnramifiedLocalHom_iff_completion A B)

/-- `B̂` is `𝔪_Â`-adically separated as an `Â`-module. -/
lemma isHausdorff_maximalIdeal_completion_completion :
    letI := (completionMap A B).toAlgebra
    IsHausdorff (maximalIdeal Ah) Bh := by
  let := (completionMap A B).toAlgebra
  have : IsLocalHom (algebraMap Ah Bh) := isLocalHom_completionMap A B
  refine ⟨fun x hx ↦ IsHausdorff.haus' (I := maximalIdeal B) x fun n ↦ ?_⟩
  have := hx n
  rw [SModEq.zero] at this ⊢
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  refine Submodule.smul_induction_on this (fun a ha y _ ↦ ?_) fun y z hy hz ↦ add_mem hy hz
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ ?_
  have hle : (maximalIdeal Ah ^ n).map (algebraMap Ah Bh) ≤ maximalIdeal Bh ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (map_maximalIdeal_le _) n
  rw [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map]
  exact hle (Ideal.mem_map_of_mem _ ha)

/-- I.2.1, (i) ⇔ (iii): for a local homomorphism `A → B` of noetherian local rings, `B/𝔪_A B` is
finite over `A` (i.e. `A → B` is quasi-finite) iff `B̂` is finite over `Â`. By I.2.1 (i) ⇔ (ii)
for `A → B` and for `Â → B̂` (whose residue fields and whose `𝔪_A B`-adic topology are those of
`A`, `B`), `B̂/𝔪_Â B̂` is finite over `Â`; complete Nakayama concludes. -/
theorem finite_quotient_iff_finite_completion :
    letI := (completionMap A B).toAlgebra
    Module.Finite A (B ⧸ (maximalIdeal A).map (algebraMap A B)) ↔ Module.Finite Ah Bh := by
  let := (completionMap A B).toAlgebra
  have : IsLocalHom (algebraMap Ah Bh) := isLocalHom_completionMap A B
  have hmap : (maximalIdeal Ah).map (algebraMap Ah Bh) =
      ((maximalIdeal A).map (algebraMap A B)).map (algebraMap B Bh) :=
    map_maximalIdeal_completionMap A B
  rw [finite_quotient_iff]
  constructor
  · rintro ⟨⟨n, hn⟩, hk⟩
    have hkh : Module.Finite (ResidueField Ah) (ResidueField Bh) :=
      Module.Finite.of_equiv_equiv _ _ (residueField_map_completionMap_comp A B)
    have hnh : maximalIdeal Bh ^ n ≤ (maximalIdeal Ah).map (algebraMap Ah Bh) := by
      rw [AdicCompletion.maximalIdeal_eq_map (R := B), ← Ideal.map_pow, hmap]
      exact Ideal.map_mono hn
    have hq := (finite_quotient_iff Ah Bh).mpr ⟨⟨n, hnh⟩, hkh⟩
    have := isHausdorff_maximalIdeal_completion_completion A B
    have : Module.Finite Ah (Bh ⧸ (maximalIdeal Ah • ⊤ : Submodule Ah Bh)) := by
      rw [Ideal.smul_top_eq_map]
      exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv Ah _).symm
    exact Module.Finite.of_isHausdorff_of_finite_quotient (I := maximalIdeal Ah)
  · intro hfin
    have hq : Module.Finite Ah (Bh ⧸ (maximalIdeal Ah).map (algebraMap Ah Bh)) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ Ah _).toLinearMap
        Ideal.Quotient.mk_surjective
    obtain ⟨⟨n, hn⟩, hkh⟩ := (finite_quotient_iff Ah Bh).mp hq
    refine ⟨⟨n, ?_⟩, Module.Finite.of_equiv_equiv _ _ (residueField_map_comp_symm A B)⟩
    calc maximalIdeal B ^ n ≤ (maximalIdeal Bh ^ n).comap (algebraMap B Bh) := by
          rw [AdicCompletion.maximalIdeal_eq_map (R := B), ← Ideal.map_pow]
          exact Ideal.le_comap_map
      _ ≤ ((maximalIdeal Ah).map (algebraMap Ah Bh)).comap (algebraMap B Bh) :=
          Ideal.comap_mono hn
      _ = _ := by rw [hmap, comap_map_completion]

/-- I.9.4: let `A → B` be a local étale homomorphism of noetherian local rings (flat, formally
unramified and essentially of finite type), with `A` analytically reduced (`Â` reduced). Then
`B` is analytically reduced, and a fortiori reduced. As in SGA: `B̂` is finite (I.2.1) and étale
(I.4.2) over `Â`, and I.9.3 applies. -/
theorem isReduced_completion_of_etale [Module.Flat A B] [Algebra.FormallyUnramified A B]
    [Algebra.EssFiniteType A B] [IsReduced Ah] : IsReduced Bh ∧ IsReduced B := by
  let := (completionMap A B).toAlgebra
  have : IsLocalHom (algebraMap Ah Bh) := isLocalHom_completionMap A B
  have hU : IsUnramifiedLocalHom A B := isUnramifiedLocalHom_iff_formallyUnramified.mpr ‹_›
  obtain ⟨hflat, hUh⟩ := (isEtaleLocalHom_iff_completion A B).mp ⟨‹_›, hU⟩
  have : Module.Finite Ah Bh := (finite_quotient_iff_finite_completion A B).mp
    ((finite_quotient_iff A B).mpr ⟨⟨1, by rw [pow_one, hU.1]⟩, hU.2.1⟩)
  have : Algebra.FormallyUnramified Ah Bh := isUnramifiedLocalHom_iff_formallyUnramified.mp hUh
  have hBh : IsReduced Bh := isReduced_of_flat_of_formallyUnramified (A := Ah)
  refine ⟨hBh, isReduced_of_injective (algebraMap B Bh) ?_⟩
  have := faithfullyFlat_completion B
  exact FaithfulSMul.algebraMap_injective B Bh

end Completion

end SGA.SGA1.ExposeI
