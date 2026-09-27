/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import SGA.Foundations.Cohomology.GeometricConnectedness
import SGA.Foundations.Cohomology.ProjectiveSpace
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeXI.Geometry
import SGA.SGA1.ExposeXI.ProjectiveLineAlgebra

/-!
# The standard charts of the projective line

For a field `k`, the projective line `ℙ¹_k = Proj k[x₀, x₁]` is covered by `U₀ = D₊(x₀)` and
`U₁ = D₊(x₁)`, with intersection the torus `D₊(x₀x₁)`. With `t = x₁/x₀` we identify
`Γ(U₀) = k[t]`, `Γ(U₁) = k[t⁻¹]` and `Γ(D₊(x₀x₁)) = k[t, t⁻¹]` compatibly with restriction
(`chartEquiv₀`, `chartEquiv₁`, `torusEquiv`), using the embedding of all these rings into the
Laurent polynomial ring `k[x₀^±, x₁^±]` (`projectiveSpace.sectionToLaurent`); and the torus is
the non-vanishing locus of `t` in `U₀` and of `t⁻¹` in `U₁` (`basicOpen_chartCoord₀`,
`basicOpen_chartCoord₁`).
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization LaurentPolynomial

namespace SGA.SGA1.ExposeXI.ProjectiveLine

section Laurent

variable (k : Type u) [Field k]

/-- The exponent `(-n, n)` of `(x₁/x₀)ⁿ`. -/
def lineExp : ℤ →+ (Fin 2 → ℤ) := zmultiplesHom _ ![-1, 1]

variable {k} in
lemma lineExp_apply (n : ℤ) : lineExp n = ![-n, n] := by
  funext i
  fin_cases i <;> simp [lineExp]

lemma lineExp_injective : Function.Injective lineExp := fun m n h ↦ by
  simpa [lineExp_apply] using congrFun h 1

lemma mem_range_lineExp_iff {μ : Fin 2 → ℤ} : μ ∈ Set.range lineExp ↔ μ 0 + μ 1 = 0 := by
  constructor
  · rintro ⟨n, rfl⟩
    simp [lineExp_apply]
  · intro h
    refine ⟨μ 1, funext fun i ↦ ?_⟩
    fin_cases i
    · simp [lineExp_apply]
      omega
    · simp [lineExp_apply]

/-- `k[T, T⁻¹] → k[x₀^±, x₁^±]`, `T ↦ x₁/x₀`. -/
noncomputable def lineLaurent : k[T;T⁻¹] →+* projectiveSpace.Laurent (Fin 2) k :=
  AddMonoidAlgebra.mapDomainRingHom k lineExp

variable {k}

lemma lineLaurent_injective : Function.Injective (lineLaurent k) :=
  AddMonoidAlgebra.mapDomain_injective lineExp_injective

lemma coeff_lineLaurent_lineExp (g : k[T;T⁻¹]) (n : ℤ) :
    (lineLaurent k g).coeff (lineExp n) = g.coeff n :=
  Finsupp.mapDomain_apply lineExp_injective _ _

lemma coeff_lineLaurent_of_notMem (g : k[T;T⁻¹]) {μ : Fin 2 → ℤ}
    (hμ : μ ∉ Set.range lineExp) : (lineLaurent k g).coeff μ = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ hμ

lemma mem_range_lineLaurent_iff {ℓ : projectiveSpace.Laurent (Fin 2) k} :
    ℓ ∈ Set.range (lineLaurent k) ↔ ∀ μ ∈ ℓ.coeff.support, μ 0 + μ 1 = 0 := by
  constructor
  · rintro ⟨g, rfl⟩ μ hμ
    by_contra h
    exact Finsupp.mem_support_iff.1 hμ
      (coeff_lineLaurent_of_notMem g (mt mem_range_lineExp_iff.1 h))
  · intro h
    exact ⟨_, AddMonoidAlgebra.mapDomain_comapDomain
      (fun μ hμ ↦ mem_range_lineExp_iff.2 (h μ hμ)) lineExp_injective⟩

/-- A Laurent polynomial without negative exponents is a polynomial. -/
lemma exists_toLaurent_eq {g : k[T;T⁻¹]} (h : ∀ n ∈ g.coeff.support, 0 ≤ n) :
    ∃ p : Polynomial k, Polynomial.toLaurent p = g :=
  ⟨Polynomial.ofFinsupp (AddMonoidAlgebra.comapDomain _ Nat.cast_injective g),
    AddMonoidAlgebra.mapDomain_comapDomain
      (fun n hn ↦ ⟨n.toNat, Int.toNat_of_nonneg (h n hn)⟩) Nat.cast_injective⟩

lemma mem_range_lineLaurent_toLaurent_iff {ℓ : projectiveSpace.Laurent (Fin 2) k} :
    ℓ ∈ Set.range (lineLaurent k ∘ Polynomial.toLaurent) ↔
      ∀ μ ∈ ℓ.coeff.support, μ 0 + μ 1 = 0 ∧ 0 ≤ μ 1 := by
  constructor
  · rintro ⟨p, rfl⟩ μ hμ
    have hμ' : μ ∈ Set.range lineExp := by
      by_contra h
      exact Finsupp.mem_support_iff.1 hμ (coeff_lineLaurent_of_notMem _ h)
    obtain ⟨n, rfl⟩ := hμ'
    refine ⟨mem_range_lineExp_iff.1 ⟨n, rfl⟩, ?_⟩
    rw [Finsupp.mem_support_iff, Function.comp_apply, coeff_lineLaurent_lineExp] at hμ
    have : n ∈ (Polynomial.toLaurent p).coeff.support := Finsupp.mem_support_iff.2 hμ
    rw [support_coeff_toLaurent] at this
    obtain ⟨m, -, rfl⟩ := Finset.mem_map.1 this
    simp [lineExp_apply]
  · intro h
    obtain ⟨g, rfl⟩ := mem_range_lineLaurent_iff.2 fun μ hμ ↦ (h μ hμ).1
    obtain ⟨p, rfl⟩ := exists_toLaurent_eq (g := g) fun n hn ↦ by
      have := (h (lineExp n) (by
        rw [Finsupp.mem_support_iff, coeff_lineLaurent_lineExp]
        exact Finsupp.mem_support_iff.1 hn)).2
      simpa [lineExp_apply] using this
    exact ⟨p, rfl⟩

lemma mem_range_lineLaurent_toLaurentInv_iff {ℓ : projectiveSpace.Laurent (Fin 2) k} :
    ℓ ∈ Set.range (lineLaurent k ∘ toLaurentInv k) ↔
      ∀ μ ∈ ℓ.coeff.support, μ 0 + μ 1 = 0 ∧ 0 ≤ μ 0 := by
  constructor
  · rintro ⟨p, rfl⟩ μ hμ
    have hμ' : μ ∈ Set.range lineExp := by
      by_contra h
      exact Finsupp.mem_support_iff.1 hμ (coeff_lineLaurent_of_notMem _ h)
    obtain ⟨n, rfl⟩ := hμ'
    refine ⟨mem_range_lineExp_iff.1 ⟨n, rfl⟩, ?_⟩
    rw [Finsupp.mem_support_iff, Function.comp_apply, coeff_lineLaurent_lineExp,
      toLaurentInv_apply, invert_apply] at hμ
    have : -n ∈ (Polynomial.toLaurent p).coeff.support := Finsupp.mem_support_iff.2 hμ
    rw [support_coeff_toLaurent] at this
    obtain ⟨m, -, hm⟩ := Finset.mem_map.1 this
    simp only [Nat.castEmbedding_apply] at hm
    simp [lineExp_apply]
    omega
  · intro h
    obtain ⟨g, rfl⟩ := mem_range_lineLaurent_iff.2 fun μ hμ ↦ (h μ hμ).1
    obtain ⟨p, hp⟩ := exists_toLaurent_eq (g := invert g) fun n hn ↦ by
      rw [Finsupp.mem_support_iff, invert_apply] at hn
      have := (h (lineExp (-n)) (by
        rw [Finsupp.mem_support_iff, coeff_lineLaurent_lineExp]
        exact hn)).2
      simpa [lineExp_apply] using this
    refine ⟨p, ?_⟩
    rw [Function.comp_apply, toLaurentInv_apply, hp, involutive_invert]

end Laurent

section RingEquiv

variable {R S L : Type*} [CommRing R] [CommRing S] [CommRing L]

/-- Two injective ring maps with the same image identify their sources. -/
noncomputable def ringEquivOfRangeEq (α : R →+* L) (β : S →+* L) (hα : Function.Injective α)
    (hβ : Function.Injective β) (h : Set.range α = Set.range β) : R ≃+* S :=
  (RingEquiv.ofBijective α.rangeRestrict
      ⟨fun x y hxy ↦ hα (congrArg Subtype.val hxy), α.rangeRestrict_surjective⟩).trans
    ((RingEquiv.subringCongr (SetLike.coe_injective (by simpa [RingHom.coe_range] using h))).trans
      (RingEquiv.ofBijective β.rangeRestrict
        ⟨fun x y hxy ↦ hβ (congrArg Subtype.val hxy), β.rangeRestrict_surjective⟩).symm)

lemma ringEquivOfRangeEq_spec (α : R →+* L) (β : S →+* L) (hα : Function.Injective α)
    (hβ : Function.Injective β) (h : Set.range α = Set.range β) (r : R) :
    β (ringEquivOfRangeEq α β hα hβ h r) = α r := by
  set e := RingEquiv.ofBijective β.rangeRestrict
    ⟨fun x y hxy ↦ hβ (congrArg Subtype.val hxy), β.rangeRestrict_surjective⟩
  have := congrArg Subtype.val (e.apply_symm_apply ((RingEquiv.subringCongr
    (SetLike.coe_injective (by simpa [RingHom.coe_range] using h))) (α.rangeRestrict r)))
  exact this

end RingEquiv

section Charts

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The projective line `Proj k[x₀, x₁]`. -/
local notation "ℙ¹" => Proj (homogeneousSubmodule (Fin 2) k)

/-- The chart `U₀ = D₊(x₀)`. -/
noncomputable abbrev chart₀ : (ℙ¹).Opens := Proj.basicOpen _ (projectiveSpace.prodX (Fin 2) k {0})

/-- The chart `U₁ = D₊(x₁)`. -/
noncomputable abbrev chart₁ : (ℙ¹).Opens := Proj.basicOpen _ (projectiveSpace.prodX (Fin 2) k {1})

lemma torus_le_chart₀ : projectiveSpace.torus (Fin 2) k ≤ chart₀ k :=
  projectiveSpace.torus_le_basicOpen_prodX _

lemma torus_le_chart₁ : projectiveSpace.torus (Fin 2) k ≤ chart₁ k :=
  projectiveSpace.torus_le_basicOpen_prodX _

lemma mem_monomialSet_iff {I : Finset (Fin 2)} {μ : Fin 2 → ℤ} :
    μ ∈ projectiveSpace.monomialSet I ↔ μ 0 + μ 1 = 0 ∧ ∀ i ∉ I, 0 ≤ μ i := by
  simp [projectiveSpace.monomialSet, Fin.sum_univ_two]

lemma range_sectionToLaurent_torus :
    Set.range (projectiveSpace.sectionToLaurent (Fin 2) k _ le_rfl) =
      Set.range (lineLaurent k) := by
  rw [projectiveSpace.range_sectionToLaurent_of_eq Finset.univ_nonempty rfl]
  ext ℓ
  rw [mem_range_lineLaurent_iff]
  simp only [Set.mem_ofPred_eq, Set.subset_def, Finset.mem_coe, mem_monomialSet_iff,
    Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff, implies_true, and_true]

lemma range_sectionToLaurent_chart₀ :
    Set.range (projectiveSpace.sectionToLaurent (Fin 2) k _ (torus_le_chart₀ k)) =
      Set.range (lineLaurent k ∘ Polynomial.toLaurent) := by
  rw [projectiveSpace.range_sectionToLaurent_of_eq (Finset.singleton_nonempty 0) rfl]
  ext ℓ
  rw [mem_range_lineLaurent_toLaurent_iff]
  simp only [Set.mem_ofPred_eq, Set.subset_def, Finset.mem_coe, mem_monomialSet_iff,
    Finset.mem_singleton]
  refine forall₂_congr fun μ _ ↦ and_congr_right fun _ ↦ ⟨fun h ↦ h 1 (by decide), ?_⟩
  intro h i hi
  obtain rfl : i = 1 := by fin_cases i <;> simp_all
  exact h

lemma range_sectionToLaurent_chart₁ :
    Set.range (projectiveSpace.sectionToLaurent (Fin 2) k _ (torus_le_chart₁ k)) =
      Set.range (lineLaurent k ∘ toLaurentInv k) := by
  rw [projectiveSpace.range_sectionToLaurent_of_eq (Finset.singleton_nonempty 1) rfl]
  ext ℓ
  rw [mem_range_lineLaurent_toLaurentInv_iff]
  simp only [Set.mem_ofPred_eq, Set.subset_def, Finset.mem_coe, mem_monomialSet_iff,
    Finset.mem_singleton]
  refine forall₂_congr fun μ _ ↦ and_congr_right fun _ ↦ ⟨fun h ↦ h 0 (by decide), ?_⟩
  intro h i hi
  obtain rfl : i = 0 := by fin_cases i <;> simp_all
  exact h

/-- `Γ(D₊(x₀x₁)) = k[t, t⁻¹]`, `t = x₁/x₀`. -/
noncomputable def torusEquiv : Γ(ℙ¹, projectiveSpace.torus (Fin 2) k) ≃+* k[T;T⁻¹] :=
  ringEquivOfRangeEq _ (lineLaurent k)
    (projectiveSpace.injective_sectionToLaurent_of_eq Finset.univ_nonempty rfl le_rfl)
    lineLaurent_injective (range_sectionToLaurent_torus k)

/-- `Γ(D₊(x₀)) = k[t]`, `t = x₁/x₀`. -/
noncomputable def chartEquiv₀ : Γ(ℙ¹, chart₀ k) ≃+* Polynomial k :=
  ringEquivOfRangeEq _ ((lineLaurent k).comp Polynomial.toLaurent)
    (projectiveSpace.injective_sectionToLaurent_of_eq (Finset.singleton_nonempty 0) rfl _)
    (lineLaurent_injective.comp Polynomial.toLaurent_injective) (range_sectionToLaurent_chart₀ k)

/-- `Γ(D₊(x₁)) = k[t⁻¹]`, `t = x₁/x₀`. -/
noncomputable def chartEquiv₁ : Γ(ℙ¹, chart₁ k) ≃+* Polynomial k :=
  ringEquivOfRangeEq _ ((lineLaurent k).comp (toLaurentInv k).toRingHom)
    (projectiveSpace.injective_sectionToLaurent_of_eq (Finset.singleton_nonempty 1) rfl _)
    (lineLaurent_injective.comp toLaurentInv_injective) (range_sectionToLaurent_chart₁ k)

variable {k}

lemma lineLaurent_torusEquiv (s : Γ(ℙ¹, projectiveSpace.torus (Fin 2) k)) :
    lineLaurent k (torusEquiv k s) = projectiveSpace.sectionToLaurent (Fin 2) k _ le_rfl s :=
  ringEquivOfRangeEq_spec (projectiveSpace.sectionToLaurent (Fin 2) k _ le_rfl)
    (lineLaurent k) _ _ _ s

lemma lineLaurent_chartEquiv₀ (s : Γ(ℙ¹, chart₀ k)) :
    lineLaurent k (Polynomial.toLaurent (chartEquiv₀ k s)) =
      projectiveSpace.sectionToLaurent (Fin 2) k _ (torus_le_chart₀ k) s :=
  ringEquivOfRangeEq_spec (projectiveSpace.sectionToLaurent (Fin 2) k _ (torus_le_chart₀ k))
    ((lineLaurent k).comp Polynomial.toLaurent) _ _ _ s

lemma lineLaurent_chartEquiv₁ (s : Γ(ℙ¹, chart₁ k)) :
    lineLaurent k (toLaurentInv k (chartEquiv₁ k s)) =
      projectiveSpace.sectionToLaurent (Fin 2) k _ (torus_le_chart₁ k) s :=
  ringEquivOfRangeEq_spec (projectiveSpace.sectionToLaurent (Fin 2) k _ (torus_le_chart₁ k))
    ((lineLaurent k).comp (toLaurentInv k).toRingHom) _ _ _ s

lemma torusEquiv_res₀ (s : Γ(ℙ¹, chart₀ k)) :
    torusEquiv k ((ℙ¹).presheaf.map (homOfLE (torus_le_chart₀ k)).op s) =
      Polynomial.toLaurent (chartEquiv₀ k s) := by
  apply lineLaurent_injective
  rw [lineLaurent_torusEquiv, projectiveSpace.sectionToLaurent_map (torus_le_chart₀ k),
    lineLaurent_chartEquiv₀]

lemma torusEquiv_res₁ (s : Γ(ℙ¹, chart₁ k)) :
    torusEquiv k ((ℙ¹).presheaf.map (homOfLE (torus_le_chart₁ k)).op s) =
      toLaurentInv k (chartEquiv₁ k s) := by
  apply lineLaurent_injective
  rw [lineLaurent_torusEquiv, projectiveSpace.sectionToLaurent_map (torus_le_chart₁ k),
    lineLaurent_chartEquiv₁]

end Charts

section BasicOpen

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- On `D₊(f)`, the non-vanishing locus of `gᵈ/fᵉ` is `D₊(fg)`. -/
lemma basicOpen_awayToSection_isLocalizationElem {f g : A} {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hg : g ∈ 𝒜 e) (he : 0 < e) :
    (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g := by
  set U := Proj.basicOpen 𝒜 f
  have hι : U.ι = (Proj.basicOpenIsoSpec 𝒜 f hf hd).hom ≫ Proj.awayι 𝒜 f hf hd := by
    rw [← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have h1 : U.ι ⁻¹ᵁ Proj.basicOpen 𝒜 g =
      U.ι ⁻¹ᵁ (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) := by
    conv_lhs => rw [hι]
    rw [Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen 𝒜 hf hd hg he,
      Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec]
    erw [Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen]
    rw [Scheme.Opens.toSpecΓ_preimage_basicOpen]
  have h2 := congrArg (U.ι ''ᵁ ·) h1
  simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at h2
  rw [h2, inf_eq_right.2 (Scheme.basicOpen_le _ _)]

end BasicOpen

section Cover

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

local notation "ℙ¹" => Proj (homogeneousSubmodule (Fin 2) k)

lemma chart₀_sup_chart₁ : chart₀ k ⊔ chart₁ k = ⊤ := by
  rw [eq_top_iff, ← projectiveSpace.iSup_stdCover (σ := Fin 2) (A := k)]
  refine iSup_le fun i ↦ ?_
  fin_cases i
  · refine le_sup_of_le_left ?_
    rw [chart₀, projectiveSpace.prodX_singleton]
    exact le_rfl
  · refine le_sup_of_le_right ?_
    rw [chart₁, projectiveSpace.prodX_singleton]
    exact le_rfl

lemma chart₀_inf_chart₁ : chart₀ k ⊓ chart₁ k = projectiveSpace.torus (Fin 2) k := by
  rw [projectiveSpace.torus, projectiveSpace.prodX_univ_eq {0}, Proj.basicOpen_mul]
  rfl

/-- The coordinate `t = x₁/x₀` on `U₀`. -/
noncomputable def chartCoord₀ : Γ(ℙ¹, chart₀ k) :=
  Proj.awayToSection _ _ (Away.isLocalizationElem (projectiveSpace.prodX_mem (A := k) {0})
    (projectiveSpace.prodX_mem (A := k) ({1} : Finset (Fin 2))))

/-- The coordinate `t⁻¹ = x₀/x₁` on `U₁`. -/
noncomputable def chartCoord₁ : Γ(ℙ¹, chart₁ k) :=
  Proj.awayToSection _ _ (Away.isLocalizationElem (projectiveSpace.prodX_mem (A := k) {1})
    (projectiveSpace.prodX_mem (A := k) ({0} : Finset (Fin 2))))

lemma basicOpen_chartCoord₀ : (ℙ¹).basicOpen (chartCoord₀ k) = projectiveSpace.torus (Fin 2) k := by
  rw [chartCoord₀, basicOpen_awayToSection_isLocalizationElem _ _ (by simp) _ (by simp),
    chart₀_inf_chart₁]

lemma basicOpen_chartCoord₁ : (ℙ¹).basicOpen (chartCoord₁ k) = projectiveSpace.torus (Fin 2) k := by
  rw [chartCoord₁, basicOpen_awayToSection_isLocalizationElem _ _ (by simp) _ (by simp),
    inf_comm, chart₀_inf_chart₁]

lemma chartEquiv₀_chartCoord₀ : chartEquiv₀ k (chartCoord₀ k) = Polynomial.X := by
  apply Polynomial.toLaurent_injective
  apply lineLaurent_injective
  rw [lineLaurent_chartEquiv₀, chartCoord₀, projectiveSpace.sectionToLaurent_awayToSection,
    projectiveSpace.awayToLaurent_mk]
  simp only [Finset.card_singleton, pow_one]
  rw [projectiveSpace.toLaurent_prodX, projectiveSpace.invX, AddMonoidAlgebra.single_mul_single,
    Polynomial.toLaurent_X, T, lineLaurent, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single, mul_one]
  congr 1
  funext i
  fin_cases i <;> simp [projectiveSpace.indicator, lineExp_apply]

lemma chartEquiv₁_chartCoord₁ : chartEquiv₁ k (chartCoord₁ k) = Polynomial.X := by
  apply toLaurentInv_injective
  apply lineLaurent_injective
  rw [lineLaurent_chartEquiv₁, chartCoord₁, projectiveSpace.sectionToLaurent_awayToSection,
    projectiveSpace.awayToLaurent_mk]
  simp only [Finset.card_singleton, pow_one]
  rw [projectiveSpace.toLaurent_prodX, projectiveSpace.invX, AddMonoidAlgebra.single_mul_single,
    toLaurentInv_apply, Polynomial.toLaurent_X, invert_T, T, lineLaurent,
    AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, mul_one]
  congr 1
  funext i
  fin_cases i <;> simp [projectiveSpace.indicator, lineExp_apply]

end Cover


-- The instance `HasAffineProperty (isomorphisms Scheme) _` is only found with this option.
set_option backward.isDefEq.respectTransparency.types false in
/-- An affine morphism which is bijective on the sections over an affine open `V` of the target is
an isomorphism over `V`. -/
lemma isIso_morphismRestrict_of_bijective {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    {V : Y.Opens} (hV : IsAffineOpen V) (hb : Function.Bijective (f.app V).hom) :
    IsIso (f ∣_ V) := by
  have : IsAffine V.toScheme := hV
  refine (HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)).mpr
    ⟨hV.preimage f, ?_⟩
  rw [morphismRestrict_appTop]
  have : IsIso (f.app V) := (ConcreteCategory.isIso_iff_bijective _).2 hb
  have : IsIso (f.app (V.ι ''ᵁ ⊤)) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
    exact this
  exact IsIso.comp_isIso' this (Functor.map_isIso _ _)

section Main

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k]

local notation "ℙ¹" => Proj (homogeneousSubmodule (Fin 2) k)

/-- The key step of XI.1.1 in dimension `r ≥ 2` (by the generic line through a point), over any
field `k`: let `f : Y ⟶ ℙ¹_k` be finite étale, such that `Γ(Y, f⁻¹(U₀ ∩ U₁))` is a domain. Then
a ring homomorphism `χ : Γ(Y, f⁻¹ U₀) → k` over the evaluation `k[t] → k` at `t = 0` (a rational
point of `Y` over the point `t = 0`) is unique. Indeed `B₀ ∩ B₁` (the global sections) is then a
field, finite over `k` of dimension at least the degree `d` of `B₀` over `k[t]`
(`exists_le_finrank_inter_range`), and `χ` embeds it into `k`, so `d ≤ 1`. -/
theorem ringHom_eq_of_isDomain {Y : Scheme.{u}} (f : Y ⟶ ℙ¹) [IsFinite f] [Etale f]
    (hW : IsDomain Γ(Y, f ⁻¹ᵁ projectiveSpace.torus (Fin 2) k))
    (χ₁ χ₂ : Γ(Y, f ⁻¹ᵁ chart₀ k) →+* k)
    (h₁ : ∀ p, χ₁ (f.app (chart₀ k) ((chartEquiv₀ k).symm p)) = p.eval 0)
    (h₂ : ∀ p, χ₂ (f.app (chart₀ k) ((chartEquiv₀ k).symm p)) = p.eval 0) : χ₁ = χ₂ := by
  classical
  let U₀ := chart₀ k
  let U₁ := chart₁ k
  let U := projectiveSpace.torus (Fin 2) k
  have hU₀ : IsAffineOpen U₀ :=
    Proj.isAffineOpen_basicOpen _ _ (projectiveSpace.prodX_mem {0}) (by simp)
  have hU₁ : IsAffineOpen U₁ :=
    Proj.isAffineOpen_basicOpen _ _ (projectiveSpace.prodX_mem {1}) (by simp)
  have hV₀ : IsAffineOpen (f ⁻¹ᵁ U₀) := hU₀.preimage f
  have hV₁ : IsAffineOpen (f ⁻¹ᵁ U₁) := hU₁.preimage f
  have hle₀ : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U₀ := f.preimage_mono (torus_le_chart₀ k)
  have hle₁ : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U₁ := f.preimage_mono (torus_le_chart₁ k)
  let φ₀ : Polynomial k →+* Γ(Y, f ⁻¹ᵁ U₀) := (f.app U₀).hom.comp (chartEquiv₀ k).symm.toRingHom
  let φ₁ : Polynomial k →+* Γ(Y, f ⁻¹ᵁ U₁) := (f.app U₁).hom.comp (chartEquiv₁ k).symm.toRingHom
  let φ : k[T;T⁻¹] →+* Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.comp (torusEquiv k).symm.toRingHom
  let _ : Algebra (Polynomial k) Γ(Y, f ⁻¹ᵁ U₀) := φ₀.toAlgebra
  let _ : Algebra (Polynomial k) Γ(Y, f ⁻¹ᵁ U₁) := φ₁.toAlgebra
  let _ : Algebra k[T;T⁻¹] Γ(Y, f ⁻¹ᵁ U) := φ.toAlgebra
  let _ : Algebra Γ(Y, f ⁻¹ᵁ U₀) Γ(Y, f ⁻¹ᵁ U) := (Y.presheaf.map (homOfLE hle₀).op).hom.toAlgebra
  let _ : Algebra Γ(Y, f ⁻¹ᵁ U₁) Γ(Y, f ⁻¹ᵁ U) := (Y.presheaf.map (homOfLE hle₁).op).hom.toAlgebra
  let _ : Algebra k Γ(Y, f ⁻¹ᵁ U) := (φ.comp (algebraMap k k[T;T⁻¹])).toAlgebra
  have : IsScalarTower k k[T;T⁻¹] Γ(Y, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale (Polynomial k) Γ(Y, f ⁻¹ᵁ U₀) :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (chartEquiv₀ k).symm.bijective)
      (by
        have := HasRingHomProperty.appLE @Etale f inferInstance ⟨U₀, hU₀⟩ ⟨_, hV₀⟩ le_rfl
        rwa [Scheme.Hom.appLE_eq_app] at this)
  have : Algebra.Etale (Polynomial k) Γ(Y, f ⁻¹ᵁ U₁) :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (chartEquiv₁ k).symm.bijective)
      (by
        have := HasRingHomProperty.appLE @Etale f inferInstance ⟨U₁, hU₁⟩ ⟨_, hV₁⟩ le_rfl
        rwa [Scheme.Hom.appLE_eq_app] at this)
  have : Module.Finite (Polynomial k) Γ(Y, f ⁻¹ᵁ U₀) :=
    RingHom.Finite.comp (f.finite_app U₀ hU₀) (chartEquiv₀ k).symm.finite
  have : Module.Finite (Polynomial k) Γ(Y, f ⁻¹ᵁ U₁) :=
    RingHom.Finite.comp (f.finite_app U₁ hU₁) (chartEquiv₁ k).symm.finite
  have h₀ : ∀ p, algebraMap Γ(Y, f ⁻¹ᵁ U₀) Γ(Y, f ⁻¹ᵁ U)
      (algebraMap (Polynomial k) Γ(Y, f ⁻¹ᵁ U₀) p) =
        algebraMap k[T;T⁻¹] Γ(Y, f ⁻¹ᵁ U) (Polynomial.toLaurent p) := by
    intro p
    have hp : (torusEquiv k).symm (Polynomial.toLaurent p) =
        (ℙ¹).presheaf.map (homOfLE (torus_le_chart₀ k)).op ((chartEquiv₀ k).symm p) := by
      apply (torusEquiv k).injective
      rw [RingEquiv.apply_symm_apply, torusEquiv_res₀, RingEquiv.apply_symm_apply]
    change (Y.presheaf.map (homOfLE hle₀).op) (f.app U₀ ((chartEquiv₀ k).symm p)) =
      f.app U ((torusEquiv k).symm (Polynomial.toLaurent p))
    rw [hp, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  have h₁' : ∀ p, algebraMap Γ(Y, f ⁻¹ᵁ U₁) Γ(Y, f ⁻¹ᵁ U)
      (algebraMap (Polynomial k) Γ(Y, f ⁻¹ᵁ U₁) p) =
        algebraMap k[T;T⁻¹] Γ(Y, f ⁻¹ᵁ U) (toLaurentInv k p) := by
    intro p
    have hp : (torusEquiv k).symm (toLaurentInv k p) =
        (ℙ¹).presheaf.map (homOfLE (torus_le_chart₁ k)).op ((chartEquiv₁ k).symm p) := by
      apply (torusEquiv k).injective
      rw [RingEquiv.apply_symm_apply, torusEquiv_res₁, RingEquiv.apply_symm_apply]
    change (Y.presheaf.map (homOfLE hle₁).op) (f.app U₁ ((chartEquiv₁ k).symm p)) =
      f.app U ((torusEquiv k).symm (toLaurentInv k p))
    rw [hp, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  have hX₀ : algebraMap (Polynomial k) Γ(Y, f ⁻¹ᵁ U₀) Polynomial.X = f.app U₀ (chartCoord₀ k) := by
    change f.app U₀ ((chartEquiv₀ k).symm Polynomial.X) = _
    rw [← chartEquiv₀_chartCoord₀, RingEquiv.symm_apply_apply]
  have hX₁ : algebraMap (Polynomial k) Γ(Y, f ⁻¹ᵁ U₁) Polynomial.X = f.app U₁ (chartCoord₁ k) := by
    change f.app U₁ ((chartEquiv₁ k).symm Polynomial.X) = _
    rw [← chartEquiv₁_chartCoord₁, RingEquiv.symm_apply_apply]
  have hW₀ : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ U₀)
      (Submonoid.powers (Polynomial.X : Polynomial k))) Γ(Y, f ⁻¹ᵁ U) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, hX₀]
    refine hV₀.isLocalization_of_eq_basicOpen (f.app U₀ (chartCoord₀ k)) (homOfLE hle₀) ?_
    rw [← Scheme.preimage_basicOpen, basicOpen_chartCoord₀]
  have hW₁ : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ U₁)
      (Submonoid.powers (Polynomial.X : Polynomial k))) Γ(Y, f ⁻¹ᵁ U) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, hX₁]
    refine hV₁.isLocalization_of_eq_basicOpen (f.app U₁ (chartCoord₁ k)) (homOfLE hle₁) ?_
    rw [← Scheme.preimage_basicOpen, basicOpen_chartCoord₁]
  exact ringHom_eq_of_isDomain_of_isLocalization h₀ h₁' hW₀ hW₁ (fun _ ↦ hW) χ₁ χ₂ h₁ h₂

/-- XI.1.1 for `r = 1`, the key step: a connected finite étale covering of `ℙ¹_k`, `k`
algebraically closed, is an isomorphism. Over the charts `U₀ = Spec k[t]`, `U₁ = Spec k[t⁻¹]` it
is given by finite étale algebras `B₀`, `B₁` of the same degree `d`, and its ring of global
functions is `B₀ ∩ B₁`, of dimension `≥ d` by the Riemann–Roch inequality
(`exists_le_finrank_inter_range`); as it is a connected reduced finite `k`-algebra, it is `k`, so
`d = 1`. -/
theorem isIso_of_isFinite_of_etale [IsAlgClosed k] {Y : Scheme.{u}} (f : Y ⟶ ℙ¹) [IsFinite f]
    [Etale f] [ConnectedSpace Y] : IsIso f := by
  classical
  set U₀ := chart₀ k
  set U₁ := chart₁ k
  set U := projectiveSpace.torus (Fin 2) k
  have hU₀ : IsAffineOpen U₀ :=
    Proj.isAffineOpen_basicOpen _ _ (projectiveSpace.prodX_mem {0}) (by simp)
  have hU₁ : IsAffineOpen U₁ :=
    Proj.isAffineOpen_basicOpen _ _ (projectiveSpace.prodX_mem {1}) (by simp)
  have hV₀ : IsAffineOpen (f ⁻¹ᵁ U₀) := hU₀.preimage f
  have hV₁ : IsAffineOpen (f ⁻¹ᵁ U₁) := hU₁.preimage f
  have hle₀ : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U₀ := f.preimage_mono (torus_le_chart₀ k)
  have hle₁ : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U₁ := f.preimage_mono (torus_le_chart₁ k)
  -- The algebras `B₀ = Γ(f⁻¹U₀)` over `k[t]`, `B₁ = Γ(f⁻¹U₁)` over `k[t⁻¹]`, and their common
  -- localization `W = Γ(f⁻¹(U₀ ∩ U₁))` over `k[t, t⁻¹]`.
  let φ₀ : Polynomial k →+* Γ(Y, f ⁻¹ᵁ U₀) := (f.app U₀).hom.comp (chartEquiv₀ k).symm.toRingHom
  let φ₁ : Polynomial k →+* Γ(Y, f ⁻¹ᵁ U₁) := (f.app U₁).hom.comp (chartEquiv₁ k).symm.toRingHom
  let φ : k[T;T⁻¹] →+* Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.comp (torusEquiv k).symm.toRingHom
  let _ : Algebra (Polynomial k) Γ(Y, f ⁻¹ᵁ U₀) := φ₀.toAlgebra
  let _ : Algebra (Polynomial k) Γ(Y, f ⁻¹ᵁ U₁) := φ₁.toAlgebra
  let _ : Algebra k[T;T⁻¹] Γ(Y, f ⁻¹ᵁ U) := φ.toAlgebra
  let _ : Algebra Γ(Y, f ⁻¹ᵁ U₀) Γ(Y, f ⁻¹ᵁ U) := (Y.presheaf.map (homOfLE hle₀).op).hom.toAlgebra
  let _ : Algebra Γ(Y, f ⁻¹ᵁ U₁) Γ(Y, f ⁻¹ᵁ U) := (Y.presheaf.map (homOfLE hle₁).op).hom.toAlgebra
  let _ : Algebra k Γ(Y, f ⁻¹ᵁ U) := (φ.comp (algebraMap k k[T;T⁻¹])).toAlgebra
  have : IsScalarTower k k[T;T⁻¹] Γ(Y, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale (Polynomial k) Γ(Y, f ⁻¹ᵁ U₀) :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (chartEquiv₀ k).symm.bijective)
      (by
        have := HasRingHomProperty.appLE @Etale f inferInstance ⟨U₀, hU₀⟩ ⟨_, hV₀⟩ le_rfl
        rwa [Scheme.Hom.appLE_eq_app] at this)
  have : Algebra.Etale (Polynomial k) Γ(Y, f ⁻¹ᵁ U₁) :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (chartEquiv₁ k).symm.bijective)
      (by
        have := HasRingHomProperty.appLE @Etale f inferInstance ⟨U₁, hU₁⟩ ⟨_, hV₁⟩ le_rfl
        rwa [Scheme.Hom.appLE_eq_app] at this)
  have : Module.Finite (Polynomial k) Γ(Y, f ⁻¹ᵁ U₀) :=
    RingHom.Finite.comp (f.finite_app U₀ hU₀) (chartEquiv₀ k).symm.finite
  have : Module.Finite (Polynomial k) Γ(Y, f ⁻¹ᵁ U₁) :=
    RingHom.Finite.comp (f.finite_app U₁ hU₁) (chartEquiv₁ k).symm.finite
  -- Compatibility with the restriction maps.
  have h₀ : ∀ p, algebraMap Γ(Y, f ⁻¹ᵁ U₀) Γ(Y, f ⁻¹ᵁ U)
      (algebraMap (Polynomial k) Γ(Y, f ⁻¹ᵁ U₀) p) =
        algebraMap k[T;T⁻¹] Γ(Y, f ⁻¹ᵁ U) (Polynomial.toLaurent p) := by
    intro p
    have hp : (torusEquiv k).symm (Polynomial.toLaurent p) =
        (ℙ¹).presheaf.map (homOfLE (torus_le_chart₀ k)).op ((chartEquiv₀ k).symm p) := by
      apply (torusEquiv k).injective
      rw [RingEquiv.apply_symm_apply, torusEquiv_res₀, RingEquiv.apply_symm_apply]
    change (Y.presheaf.map (homOfLE hle₀).op) (f.app U₀ ((chartEquiv₀ k).symm p)) =
      f.app U ((torusEquiv k).symm (Polynomial.toLaurent p))
    rw [hp, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  have h₁ : ∀ p, algebraMap Γ(Y, f ⁻¹ᵁ U₁) Γ(Y, f ⁻¹ᵁ U)
      (algebraMap (Polynomial k) Γ(Y, f ⁻¹ᵁ U₁) p) =
        algebraMap k[T;T⁻¹] Γ(Y, f ⁻¹ᵁ U) (toLaurentInv k p) := by
    intro p
    have hp : (torusEquiv k).symm (toLaurentInv k p) =
        (ℙ¹).presheaf.map (homOfLE (torus_le_chart₁ k)).op ((chartEquiv₁ k).symm p) := by
      apply (torusEquiv k).injective
      rw [RingEquiv.apply_symm_apply, torusEquiv_res₁, RingEquiv.apply_symm_apply]
    change (Y.presheaf.map (homOfLE hle₁).op) (f.app U₁ ((chartEquiv₁ k).symm p)) =
      f.app U ((torusEquiv k).symm (toLaurentInv k p))
    rw [hp, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
    rfl
  -- `W` is the localization of `B₀` at `t` and of `B₁` at `t⁻¹`.
  have hX₀ : algebraMap (Polynomial k) Γ(Y, f ⁻¹ᵁ U₀) Polynomial.X = f.app U₀ (chartCoord₀ k) := by
    change f.app U₀ ((chartEquiv₀ k).symm Polynomial.X) = _
    rw [← chartEquiv₀_chartCoord₀, RingEquiv.symm_apply_apply]
  have hX₁ : algebraMap (Polynomial k) Γ(Y, f ⁻¹ᵁ U₁) Polynomial.X = f.app U₁ (chartCoord₁ k) := by
    change f.app U₁ ((chartEquiv₁ k).symm Polynomial.X) = _
    rw [← chartEquiv₁_chartCoord₁, RingEquiv.symm_apply_apply]
  have hW₀ : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ U₀)
      (Submonoid.powers (Polynomial.X : Polynomial k))) Γ(Y, f ⁻¹ᵁ U) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, hX₀]
    refine hV₀.isLocalization_of_eq_basicOpen (f.app U₀ (chartCoord₀ k)) (homOfLE hle₀) ?_
    rw [← Scheme.preimage_basicOpen, basicOpen_chartCoord₀]
  have hW₁ : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y, f ⁻¹ᵁ U₁)
      (Submonoid.powers (Polynomial.X : Polynomial k))) Γ(Y, f ⁻¹ᵁ U) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, hX₁]
    refine hV₁.isLocalization_of_eq_basicOpen (f.app U₁ (chartCoord₁ k)) (homOfLE hle₁) ?_
    rw [← Scheme.preimage_basicOpen, basicOpen_chartCoord₁]
  obtain ⟨Γ', hΓ', hfin, hle⟩ := exists_le_finrank_inter_range h₀ h₁ hW₀ hW₁
  -- `B₀ → W` and `B₁ → W` are injective (`t` is a non-zero-divisor on the free module `B₀`).
  have hinj : ∀ {B : Type u} [CommRing B] [Algebra (Polynomial k) B]
      [Algebra.Etale (Polynomial k) B] [Module.Finite (Polynomial k) B] [Algebra B Γ(Y, f ⁻¹ᵁ U)],
      IsLocalization (Algebra.algebraMapSubmonoid B
        (Submonoid.powers (Polynomial.X : Polynomial k))) Γ(Y, f ⁻¹ᵁ U) →
      Function.Injective (algebraMap B Γ(Y, f ⁻¹ᵁ U)) := by
    intro B _ _ _ _ _ hW
    refine IsLocalization.injective (M := Algebra.algebraMapSubmonoid B
      (Submonoid.powers (Polynomial.X : Polynomial k))) _ ?_
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro z hz
    have : (Polynomial.X ^ n : Polynomial k) • z = 0 := by rw [Algebra.smul_def, mul_comm]; exact hz
    exact (smul_eq_zero.1 this).resolve_left (pow_ne_zero _ Polynomial.X_ne_zero)
  have hinj₀ := hinj hW₀
  have hinj₁ := hinj hW₁
  -- The global sections of `Y` are `Γ' = B₀ ∩ B₁`.
  have hcov : ⊤ ≤ f ⁻¹ᵁ U₀ ⊔ f ⁻¹ᵁ U₁ := by
    rw [← Scheme.Hom.preimage_sup, chart₀_sup_chart₁]
    exact le_rfl
  have hinf : f ⁻¹ᵁ U₀ ⊓ f ⁻¹ᵁ U₁ ≤ f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.preimage_inf, chart₀_inf_chart₁]
  let r : Γ(Y, ⊤) →+* Γ(Y, f ⁻¹ᵁ U) := (Y.presheaf.map (homOfLE le_top).op).hom
  have hr₀ : ∀ s : Γ(Y, ⊤), algebraMap Γ(Y, f ⁻¹ᵁ U₀) Γ(Y, f ⁻¹ᵁ U)
      (Y.presheaf.map (homOfLE le_top : f ⁻¹ᵁ U₀ ⟶ ⊤).op s) = r s := fun s ↦ by
    change (Y.presheaf.map (homOfLE hle₀).op) _ = _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have hr₁ : ∀ s : Γ(Y, ⊤), algebraMap Γ(Y, f ⁻¹ᵁ U₁) Γ(Y, f ⁻¹ᵁ U)
      (Y.presheaf.map (homOfLE le_top : f ⁻¹ᵁ U₁ ⟶ ⊤).op s) = r s := fun s ↦ by
    change (Y.presheaf.map (homOfLE hle₁).op) _ = _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have hmem : ∀ s, r s ∈ Γ' := fun s ↦ (hΓ' _).2 ⟨⟨_, hr₀ s⟩, ⟨_, hr₁ s⟩⟩
  have hsurj : ∀ w ∈ Γ', ∃ s, r s = w := by
    intro w hw
    obtain ⟨⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩⟩ := (hΓ' w).1 hw
    obtain ⟨s, hs₀, -⟩ := CohomologyAux.exists_glue₂_sections Y hcov b₀ b₁ (by
      have := congrArg (fun x ↦ (Y.presheaf.map (homOfLE hinf).op) x) (hb₀.trans hb₁.symm)
      change (Y.presheaf.map (homOfLE hle₀).op ≫ Y.presheaf.map (homOfLE hinf).op) b₀ =
        (Y.presheaf.map (homOfLE hle₁).op ≫ Y.presheaf.map (homOfLE hinf).op) b₁ at this
      rw [← Functor.map_comp, ← Functor.map_comp] at this
      exact this)
    exact ⟨s, by rw [← hr₀, hs₀, hb₀]⟩
  have hrinj : Function.Injective r := by
    intro s s' h
    refine TopCat.Sheaf.eq_of_locally_eq₂ Y.sheaf (homOfLE le_top : f ⁻¹ᵁ U₀ ⟶ ⊤)
      (homOfLE le_top) hcov s s' ?_ ?_
    · apply hinj₀
      change algebraMap Γ(Y, f ⁻¹ᵁ U₀) Γ(Y, f ⁻¹ᵁ U)
        (Y.presheaf.map (homOfLE le_top : f ⁻¹ᵁ U₀ ⟶ ⊤).op s) = algebraMap Γ(Y, f ⁻¹ᵁ U₀)
        Γ(Y, f ⁻¹ᵁ U) (Y.presheaf.map (homOfLE le_top : f ⁻¹ᵁ U₀ ⟶ ⊤).op s')
      rw [hr₀, hr₀, h]
    · apply hinj₁
      change algebraMap Γ(Y, f ⁻¹ᵁ U₁) Γ(Y, f ⁻¹ᵁ U)
        (Y.presheaf.map (homOfLE le_top : f ⁻¹ᵁ U₁ ⟶ ⊤).op s) = algebraMap Γ(Y, f ⁻¹ᵁ U₁)
        Γ(Y, f ⁻¹ᵁ U) (Y.presheaf.map (homOfLE le_top : f ⁻¹ᵁ U₁ ⟶ ⊤).op s')
      rw [hr₁, hr₁, h]
  -- `Γ'` is a connected reduced finite `k`-algebra, hence `k`.
  let Γ'' : Subalgebra k Γ(Y, f ⁻¹ᵁ U) :=
    { carrier := Γ'
      mul_mem' := fun {a b} ha hb ↦ by
        obtain ⟨s, rfl⟩ := hsurj a ha
        obtain ⟨t, rfl⟩ := hsurj b hb
        rw [← map_mul]
        exact hmem _
      add_mem' := fun ha hb ↦ Γ'.add_mem ha hb
      algebraMap_mem' := fun c ↦ by
        refine (hΓ' _).2 ⟨⟨algebraMap (Polynomial k) _ (Polynomial.C c), ?_⟩,
          ⟨algebraMap (Polynomial k) _ (Polynomial.C c), ?_⟩⟩
        · rw [h₀, Polynomial.toLaurent_C, LaurentPolynomial.C_eq_algebraMap]
          rfl
        · rw [h₁, toLaurentInv_apply, Polynomial.toLaurent_C, invert_C,
            LaurentPolynomial.C_eq_algebraMap]
          rfl }
  have hΓ'' : Subalgebra.toSubmodule Γ'' = Γ' := SetLike.coe_injective rfl
  have hfin'' : FiniteDimensional k Γ'' := by
    rw [← Subalgebra.finiteDimensional_toSubmodule, hΓ'']
    exact hfin
  let e : Γ(Y, ⊤) ≃+* Γ'' := RingEquiv.ofBijective (r.codRestrict Γ'' hmem)
    ⟨fun s t h ↦ hrinj (congrArg Subtype.val h), fun w ↦ by
      obtain ⟨s, hs⟩ := hsurj w.1 w.2
      exact ⟨s, Subtype.ext hs⟩⟩
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨Classical.arbitrary Y, trivial⟩⟩
  have : Nontrivial Γ'' := e.injective.nontrivial
  have htriv : CohomologyAux.TrivialIdempotents Γ'' :=
    (CohomologyAux.trivialIdempotents_of_connectedSpace Y).of_ringEquiv e
  have : IsReduced Γ(Y, f ⁻¹ᵁ U₀) := ExposeI.isReduced_of_flat_of_formallyUnramified
    (A := Polynomial k)
  have : IsReduced Γ'' := ⟨fun x hx ↦ by
    obtain ⟨⟨b₀, hb₀⟩, -⟩ := (hΓ' x.1).1 x.2
    obtain ⟨n, hn⟩ := hx
    have h0 : b₀ ^ n = 0 := hinj₀ (by
      rw [map_pow, hb₀, map_zero]
      exact congrArg Subtype.val hn)
    have := IsReduced.eq_zero b₀ ⟨n, h0⟩
    exact Subtype.ext (by rw [← hb₀, this, map_zero]; rfl)⟩
  have : IsArtinianRing Γ'' := IsArtinianRing.of_finite k Γ''
  have hfield := ExposeI.isField_of_isArtinianRing_of_isReduced Γ'' htriv
  have : IsDomain Γ'' := hfield.isDomain
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ'')
  have hone : Module.finrank k Γ'' = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap k Γ'') hbij).finrank_eq,
      Module.finrank_self]
  have hΓ'1 : Module.finrank k Γ' = 1 := by
    rw [← hΓ'', Subalgebra.finrank_toSubmodule, hone]
  -- Hence `B₀` and `B₁` have rank one over `k[t]`, `k[t⁻¹]`.
  obtain ⟨b₀, -, -, -⟩ := exists_basis_of_isLocalization (Polynomial.toLaurent : Polynomial k →+* _)
    (Polynomial.X : Polynomial k) LaurentPolynomial.isLocalization hW₀ h₀
    (Module.Free.chooseBasis (Polynomial k) Γ(Y, f ⁻¹ᵁ U₀))
  obtain ⟨b₁, -, -, -⟩ := exists_basis_of_isLocalization (toLaurentInv k).toRingHom
    (Polynomial.X : Polynomial k) (isLocalization_toLaurentInv k) hW₁ h₁
    (Module.Free.chooseBasis (Polynomial k) Γ(Y, f ⁻¹ᵁ U₁))
  have hrank : Module.finrank (Polynomial k) Γ(Y, f ⁻¹ᵁ U₁) =
      Module.finrank (Polynomial k) Γ(Y, f ⁻¹ᵁ U₀) := by
    rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_eq_card_chooseBasisIndex,
      ← Module.finrank_eq_card_basis b₀, ← Module.finrank_eq_card_basis b₁]
  have hrank₀ : Module.finrank (Polynomial k) Γ(Y, f ⁻¹ᵁ U₀) = 1 := by
    refine le_antisymm (hΓ'1 ▸ hle) (Nat.one_le_iff_ne_zero.2 fun h0 ↦ ?_)
    rw [Module.finrank_eq_zero_iff_of_free] at h0
    have h10 : (1 : Γ(Y, f ⁻¹ᵁ U)) = 0 := by
      rw [← map_one (algebraMap Γ(Y, f ⁻¹ᵁ U₀) Γ(Y, f ⁻¹ᵁ U)), Subsingleton.elim (1 : _) 0,
        map_zero]
    exact one_ne_zero (Subtype.ext h10 : (1 : Γ'') = 0)
  have hrank₁ : Module.finrank (Polynomial k) Γ(Y, f ⁻¹ᵁ U₁) = 1 := hrank.trans hrank₀
  -- So `f` is an isomorphism over `U₀` and over `U₁`.
  have hbij₀ : Function.Bijective (f.app U₀).hom := by
    have := bijective_algebraMap_of_finrank_eq_one hrank₀
    have hc : (f.app U₀).hom = φ₀.comp (chartEquiv₀ k).toRingHom := by
      ext x
      simp [φ₀]
    rw [hc]
    exact this.comp (chartEquiv₀ k).bijective
  have hbij₁ : Function.Bijective (f.app U₁).hom := by
    have := bijective_algebraMap_of_finrank_eq_one hrank₁
    have hc : (f.app U₁).hom = φ₁.comp (chartEquiv₁ k).toRingHom := by
      ext x
      simp [φ₁]
    rw [hc]
    exact this.comp (chartEquiv₁ k).bijective
  have hiso : ∀ V : (ℙ¹).Opens, IsAffineOpen V → Function.Bijective (f.app V).hom →
      IsIso (f ∣_ V) := fun V hV hb ↦ isIso_morphismRestrict_of_bijective f hV hb
  rw [← MorphismProperty.isomorphisms.iff, IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) (fun b : Bool ↦ cond b U₀ U₁) ?_]
  · rintro (_ | _)
    · exact hiso U₁ hU₁ hbij₁
    · exact hiso U₀ hU₀ hbij₀
  · rw [iSup_bool_eq]
    exact chart₀_sup_chart₁ k

variable (k)

/-- The projective line is non-empty. -/
instance nonempty_projectiveLine : Nonempty ℙ¹ := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hbot : chart₀ k = ⊥ := by
    ext x
    exact isEmptyElim x
  have : Subsingleton Γ(ℙ¹, chart₀ k) :=
    CommRingCat.subsingleton_of_isTerminal ((ℙ¹).sheaf.isTerminalOfEqEmpty hbot)
  have : Nontrivial Γ(ℙ¹, chart₀ k) := (chartEquiv₀ k).symm.injective.nontrivial
  exact not_subsingleton _ ‹_›

/-- The projective line is connected: an idempotent function is `0` or `1` on both charts
`Spec k[t]`, `Spec k[t⁻¹]`, compatibly on their intersection. -/
instance connectedSpace_projectiveLine : ConnectedSpace ℙ¹ := by
  refine CohomologyAux.connectedSpace_of_trivialIdempotents _ fun e he ↦ ?_
  have hcov : ⊤ ≤ chart₀ k ⊔ chart₁ k := (chart₀_sup_chart₁ k).ge
  set e₀ := (ℙ¹).presheaf.map (homOfLE le_top : chart₀ k ⟶ ⊤).op e
  set e₁ := (ℙ¹).presheaf.map (homOfLE le_top : chart₁ k ⟶ ⊤).op e
  have h₀ : e₀ = 0 ∨ e₀ = 1 := by
    have := IsIdempotentElem.iff_eq_zero_or_one.1
      ((he.map ((ℙ¹).presheaf.map (homOfLE le_top : chart₀ k ⟶ ⊤).op).hom).map (chartEquiv₀ k))
    simpa only [map_eq_zero_iff _ (chartEquiv₀ k).injective,
      (chartEquiv₀ k).map_eq_one_iff] using this
  have h₁ : e₁ = 0 ∨ e₁ = 1 := by
    have := IsIdempotentElem.iff_eq_zero_or_one.1
      ((he.map ((ℙ¹).presheaf.map (homOfLE le_top : chart₁ k ⟶ ⊤).op).hom).map (chartEquiv₁ k))
    simpa only [map_eq_zero_iff _ (chartEquiv₁ k).injective,
      (chartEquiv₁ k).map_eq_one_iff] using this
  have hcompat : Polynomial.toLaurent (chartEquiv₀ k e₀) = toLaurentInv k (chartEquiv₁ k e₁) := by
    rw [← torusEquiv_res₀, ← torusEquiv_res₁]
    simp only [e₀, e₁]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  rcases h₀ with h₀ | h₀ <;> rcases h₁ with h₁ | h₁
  · left
    refine TopCat.Sheaf.eq_of_locally_eq₂ (ℙ¹).sheaf (homOfLE le_top : chart₀ k ⟶ ⊤)
      (homOfLE le_top) hcov e 0 ?_ ?_
    · exact h₀.trans (map_zero _).symm
    · exact h₁.trans (map_zero _).symm
  · rw [h₀, h₁, map_zero, map_zero, map_one, map_one] at hcompat
    exact absurd hcompat zero_ne_one
  · rw [h₀, h₁, map_zero, map_zero, map_one, map_one] at hcompat
    exact absurd hcompat one_ne_zero
  · right
    refine TopCat.Sheaf.eq_of_locally_eq₂ (ℙ¹).sheaf (homOfLE le_top : chart₀ k ⟶ ⊤)
      (homOfLE le_top) hcov e 1 ?_ ?_
    · exact h₀.trans (map_one _).symm
    · exact h₁.trans (map_one _).symm

/-- XI.1.1 for `r = 1`: the projective line over an algebraically closed field is simply
connected. -/
theorem isSimplyConnected_projectiveLine [IsAlgClosed k] :
    IsSimplyConnected (projectiveSpace k 1) :=
  ⟨connectedSpace_projectiveLine k, fun _ f _ _ _ ↦ isIso_of_isFinite_of_etale f⟩

end Main

end SGA.SGA1.ExposeXI.ProjectiveLine
