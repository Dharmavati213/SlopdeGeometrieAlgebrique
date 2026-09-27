/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import SGA.Foundations.Projective.Segre

/-!
# Chow's lemma

Chow's lemma (EGA II 5.6.1, Hartshorne Ex. II.4.10, Stacks 0200): for an integral scheme `X`,
separated and of finite type over an affine scheme `S`, there are an integral scheme `X'` and an
H-projective surjective morphism `π : X' ⟶ X` which is an isomorphism over a non-empty open subset
of `X`, such that `X'` is H-quasi-projective over `S` (H-projective if `X` is proper over `S`).

The proof follows Hartshorne: cover `X` by finitely many non-empty affine open subsets `Vₖ`,
embed each `Vₖ` as a closed subscheme of a standard chart `D₊(xᵢ) ≅ 𝔸ⁿ_S` of a projective space
`Pₖ` over `S` (`ProjectiveSpace.exists_isClosedImmersion_basicOpen`), let `U = ⋂ Vₖ` (non-empty
since `X` is irreducible, affine since `X` is separated), `Q = ∏_S Pₖ`, and let `X'` be the
scheme-theoretic closure of the graph of `U ⟶ Q` in `X ×_S Q`. Over `U`, this closure is the graph
itself; over the open subset of `Q` where the `k`-th coordinate lies in `D₊(xᵢ)`, it is contained
in the graph of `Q ⊇ Oₖ ⟶ Pₖ ⊇ Vₖ`, which gives that `X' ⟶ Q` is an immersion.

## Main results

- `AlgebraicGeometry.exists_isHProjective_isIso_morphismRestrict`: Chow's lemma.
- `AlgebraicGeometry.exists_isHProjective_of_isProper`: the version for proper morphisms.
- `AlgebraicGeometry.IsHProjective.of_isHQuasiProjective`: a proper H-quasi-projective morphism
  is H-projective.
- `AlgebraicGeometry.ProjectiveSpace.exists_isClosedImmersion_basicOpen`: an affine scheme of
  finite type over an affine scheme `S` is a closed subscheme of `𝔸ⁿ_S ⊆ ℙⁿ_S`.
- `AlgebraicGeometry.Scheme.Hom.isSchemeTheoreticallyDominant_toImage`: a quasi-compact morphism
  is scheme-theoretically dominant onto its scheme-theoretic image.

The noetherian hypothesis of EGA is not needed here; on the other hand `X` is assumed integral (the
case needed for the dévissage of EGA III 3.2.1) and `S` affine.
-/

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- The scheme-theoretic image of a quasi-compact morphism is scheme-theoretically dense. -/
instance Scheme.Hom.isSchemeTheoreticallyDominant_toImage (f : X ⟶ Y) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  constructor
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun U : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ U, U.2.preimage f.imageι⟩) ?_ fun U ↦ ?_
  · change ⨆ U : Y.affineOpens, f.imageι ⁻¹ᵁ U.1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective U)

/-- A quasi-compact immersion which is universally closed is a closed immersion. -/
lemma IsClosedImmersion.of_isImmersion_of_universallyClosed (f : X ⟶ Y) [IsImmersion f]
    [QuasiCompact f] [UniversallyClosed f] : IsClosedImmersion f := by
  have : Surjective f.toImage := surjective_of_isDominant_of_isClosed_range _
    (f.toImage.isClosedMap.isClosed_range)
  have : IsIso f.toImage := Flat.isIso_of_surjective_of_mono _
  rw [← f.toImage_imageι]
  infer_instance

/-- A proper H-quasi-projective morphism is H-projective. -/
lemma IsHProjective.of_isHQuasiProjective (f : X ⟶ S) [h : IsHQuasiProjective f] [IsProper f] :
    IsHProjective f := by
  obtain ⟨σ, _, i, _, _, rfl⟩ := h
  have : IsProper i := IsProper.of_comp i (ℙ(σ; S) ↘ S)
  have := IsClosedImmersion.of_isImmersion_of_universallyClosed i
  exact ⟨σ, inferInstance, i, inferInstance, rfl⟩

namespace ProjectiveSpace

set_option backward.isDefEq.respectTransparency.types false in
/-- An affine scheme of finite type over an affine scheme `S` is a closed subscheme of a standard
affine chart `D₊(xᵢ) ≅ 𝔸ⁿ_S` of a projective space over `S`. -/
theorem exists_isClosedImmersion_basicOpen [IsAffine X] [IsAffine S] (g : X ⟶ S)
    [LocallyOfFiniteType g] :
    ∃ (σ : Type u) (_ : Finite σ) (i : σ) (c : X ⟶ basicOpen S i),
      IsClosedImmersion c ∧ c ≫ (basicOpen S i).ι ≫ ℙ(σ; S) ↘ S = g := by
  have hft : g.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp ‹_›
  let := g.appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  let v : {j : Option s // j ≠ none} → Γ(X, ⊤) :=
    fun j ↦ ((j.1.get (Option.ne_none_iff_isSome.mp j.2)) : Γ(X, ⊤))
  let h : X ⟶ 𝔸({j : Option s // j ≠ none}; S) := AffineSpace.homOfVector g v
  have hg : (𝔸({j : Option s // j ≠ none}; S) ↘ S).appTop ≫ h.appTop = g.appTop := by
    rw [← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over]
  have hsurj : Function.Surjective h.appTop := by
    intro x
    have hx : x ∈ Algebra.adjoin Γ(S, ⊤) (s : Set Γ(X, ⊤)) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact ⟨AffineSpace.coord S ⟨some ⟨x, hx⟩, Option.some_ne_none _⟩,
        AffineSpace.homOfVector_appTop_coord _ _ _⟩
    | algebraMap r => exact ⟨(𝔸({j : Option s // j ≠ none}; S) ↘ S).appTop r, congr($hg r)⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ _ _⟩
  have := IsClosedImmersion.of_surjective_of_isAffine h hsurj
  refine ⟨Option s, inferInstance, none, h ≫ (basicOpenIsoAffineSpace S none).inv,
    inferInstance, ?_⟩
  rw [Category.assoc, ← basicOpenIsoAffineSpace_hom_over, Iso.inv_hom_id_assoc,
    AffineSpace.homOfVector_over]

end ProjectiveSpace

lemma exists_finite_affine_cover (X : Scheme.{u}) [CompactSpace X] :
    ∃ (n : ℕ) (V : Fin n → X.Opens), (∀ k, IsAffineOpen (V k)) ∧
      (∀ k, (V k : Set X).Nonempty) ∧ ⨆ k, V k = ⊤ := by
  choose V hV hxV using fun x : X ↦
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ (⊤ : X.Opens) from trivial))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ (V x : Set X))
    (fun x ↦ (V x).2) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, (hxV x).1⟩)
  refine ⟨t.card, fun k ↦ V (t.equivFin.symm k), fun k ↦ hV _, fun k ↦ ⟨_, (hxV _).1⟩, ?_⟩
  refine top_le_iff.mp fun x _ ↦ ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

lemma dense_iInter_of_nonempty {T : Type*} [TopologicalSpace T] [PreirreducibleSpace T]
    {ι : Type*} [Finite ι] (V : ι → Set T) (hV : ∀ k, IsOpen (V k)) (hV' : ∀ k, (V k).Nonempty) :
    Dense (⋂ k, V k) := by
  classical
  have := Fintype.ofFinite ι
  suffices ∀ s : Finset ι, Dense (⋂ k ∈ s, V k) by simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    rw [Finset.set_biInter_insert]
    exact ((hV a).dense (hV' a)).inter_of_isOpen_left ih (hV a)

/-- Finitely many `S`-morphisms `U ⟶ Pₖ` to H-projective `S`-schemes factor through a common
H-projective `S`-scheme (the fibre product of the `Pₖ`). -/
theorem exists_isHProjective_of_forall (U : Scheme.{u}) (u : U ⟶ S) (n : ℕ)
    (P : Fin n → Scheme.{u}) (π : ∀ k, P k ⟶ S) [∀ k, IsHProjective (π k)]
    (ψ : ∀ k, U ⟶ P k) (hψ : ∀ k, ψ k ≫ π k = u) :
    ∃ (Q : Scheme.{u}) (πQ : Q ⟶ S) (_ : IsHProjective πQ) (p : ∀ k, Q ⟶ P k) (j : U ⟶ Q),
      (∀ k, p k ≫ π k = πQ) ∧ (∀ k, j ≫ p k = ψ k) ∧ j ≫ πQ = u := by
  induction n with
  | zero => exact ⟨S, 𝟙 S, inferInstance, fun k ↦ k.elim0, u, fun k ↦ k.elim0,
      fun k ↦ k.elim0, Category.comp_id _⟩
  | succ n ih =>
    obtain ⟨Q, πQ, hQ, p, j, hp, hj, hju⟩ := ih (fun k ↦ P k.castSucc) (fun k ↦ π k.castSucc)
      (fun k ↦ ψ k.castSucc) (fun k ↦ hψ _)
    have : IsHProjective (pullback.fst πQ (π (Fin.last n))) :=
      IsHProjective.of_isPullback (IsPullback.of_hasPullback πQ (π (Fin.last n))).flip
    refine ⟨pullback πQ (π (Fin.last n)), pullback.fst _ _ ≫ πQ, inferInstance,
      Fin.lastCases (motive := fun k ↦ pullback πQ (π (Fin.last n)) ⟶ P k) (pullback.snd _ _)
        (fun k ↦ pullback.fst _ _ ≫ p k),
      pullback.lift j (ψ (Fin.last n)) (by rw [hju, hψ]), fun k ↦ ?_, fun k ↦ ?_, ?_⟩
    · induction k using Fin.lastCases with
      | last => simp [pullback.condition]
      | cast k => simp [hp]
    · induction k using Fin.lastCases with
      | last => simp only [Fin.lastCases_last, pullback.lift_snd]
      | cast k => simp only [Fin.lastCases_castSucc, pullback.lift_fst_assoc, hj]
    · rw [pullback.lift_fst_assoc, hju]

set_option backward.isDefEq.respectTransparency.types false in
/-- **Chow's lemma** (EGA II 5.6.1, Hartshorne Ex. II.4.10, Stacks 0200), for an integral scheme
`X` separated and of finite type over an affine scheme `S`: there are an integral scheme `X'` and
an H-projective surjective morphism `π : X' ⟶ X` such that `X'` is H-quasi-projective over `S` and
`π` is an isomorphism over a non-empty open subset `U` of `X`. -/
theorem exists_isHProjective_isIso_morphismRestrict [IsAffine S] (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsIntegral X] :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X) (U : X.Opens), IsHProjective π ∧ Surjective π ∧
      IsHQuasiProjective (π ≫ f) ∧ (U : Set X).Nonempty ∧ IsIso (π ∣_ U) ∧ IsIntegral X' := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
  obtain ⟨n, V, hVa, hVn, hVc⟩ := exists_finite_affine_cover X
  choose σ hσ i c hc hco using fun k ↦
    have : IsAffine (V k) := hVa k
    ProjectiveSpace.exists_isClosedImmersion_basicOpen ((V k).ι ≫ f)
  have : Nonempty (Fin n) := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨k, -⟩ := TopologicalSpace.Opens.mem_iSup.mp (hVc.ge (Set.mem_univ x))
    exact ⟨k⟩
  let U : X.Opens := ⨅ k, V k
  have hU : (U : Set X) = ⋂ k, (V k : Set X) := TopologicalSpace.Opens.coe_iInf _
  have hUd : Dense (U : Set X) := hU ▸ dense_iInter_of_nonempty _ (fun k ↦ (V k).2) hVn
  have hUn : (U : Set X).Nonempty := hUd.nonempty
  have hUa : IsAffineOpen U := IsAffineOpen.iInf hVa
  have hUV : ∀ k, U ≤ V k := fun k ↦ iInf_le _ k
  have hπk : ∀ k, IsHProjective (ℙ(σ k; S) ↘ S) := fun k ↦ have := hσ k; inferInstance
  obtain ⟨Q, πQ, hQ, p, j, hp, hj, hju⟩ := exists_isHProjective_of_forall U (U.ι ≫ f) n
    (fun k ↦ ℙ(σ k; S)) (fun k ↦ ℙ(σ k; S) ↘ S)
    (fun k ↦ X.homOfLE (hUV k) ≫ c k ≫ (ProjectiveSpace.basicOpen S (i k)).ι)
    (fun k ↦ by rw [Category.assoc, Category.assoc, hco, X.homOfLE_ι_assoc])
  have := hQ
  have : IsAffine U := hUa
  let j' : U.toScheme ⟶ pullback f πQ := pullback.lift U.ι j (by rw [hju])
  have hj'₁ : j' ≫ pullback.fst f πQ = U.ι := pullback.lift_fst _ _ _
  have hj'₂ : j' ≫ pullback.snd f πQ = j := pullback.lift_snd _ _ _
  have : QuasiCompact j' := by
    have : QuasiCompact (j' ≫ pullback.fst f πQ) := by rw [hj'₁]; infer_instance
    exact QuasiCompact.of_comp j' (pullback.fst f πQ)
  let ι' : j'.image ⟶ pullback f πQ := j'.imageι
  let t : U.toScheme ⟶ j'.image := j'.toImage
  have ht : t ≫ ι' = j' := j'.toImage_imageι
  let π : j'.image ⟶ X := ι' ≫ pullback.fst f πQ
  let q : j'.image ⟶ Q := ι' ≫ pullback.snd f πQ
  have htπ : t ≫ π = U.ι := by rw [← Category.assoc, ht, hj'₁]
  have htq : t ≫ q = j := by rw [← Category.assoc, ht, hj'₂]
  have hπq : π ≫ f = q ≫ πQ := by simp only [π, q, Category.assoc, pullback.condition]
  have : IsHProjective (pullback.fst f πQ) :=
    IsHProjective.of_isPullback (IsPullback.of_hasPullback f πQ).flip
  have hπ : IsHProjective π := inferInstance
  have : IsReduced j'.image := IsSchemeTheoreticallyDominant.isReduced t
  refine ⟨j'.image, π, U, hπ, ?_, ?_, hUn, ?_, ?_⟩
  · -- `π` is closed and its image contains the dense subset `U`.
    constructor
    have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
    have hUπ : (U : Set X) ⊆ Set.range π := fun x hx ↦
      ⟨t ⟨x, hx⟩, by rw [← Scheme.Hom.comp_apply, htπ]; rfl⟩
    rw [← Set.range_eq_univ, ← hcl.closure_eq]
    exact Set.eq_univ_of_univ_subset (hUd.closure_eq ▸ closure_mono hUπ)
  · -- `π ≫ f = q ≫ πQ`, and `q` is a quasi-compact immersion.
    have hker : ∀ (W : (pullback f πQ).Opens) (hW : Set.range t ⊆ Set.range (ι' ⁻¹ᵁ W).ι),
        (ι' ∣_ W).ker = (IsOpenImmersion.lift (ι' ⁻¹ᵁ W).ι t hW ≫ ι' ∣_ W).ker := by
      intro W hW
      have : IsSchemeTheoreticallyDominant (IsOpenImmersion.lift (ι' ⁻¹ᵁ W).ι t hW) :=
        IsSchemeTheoreticallyDominant.of_isPullback
          (IsOpenImmersion.isPullback_lift_id t (ι' ⁻¹ᵁ W).ι hW).flip
      rw [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot (IsOpenImmersion.lift _ t hW),
        Scheme.IdealSheafData.map_bot]
    have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
      ⟨fun i hi f hf ↦ by have := hi; have := hf; infer_instance⟩
    let O : Fin n → Q.Opens := fun k ↦ p k ⁻¹ᵁ ProjectiveSpace.basicOpen S (i k)
    have : IsImmersion q := by
      refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) O ?_ fun k ↦ ?_
      · -- `q` maps `π⁻¹(Vₖ)` into `Oₖ`: on `π⁻¹(Vₖ)`, `pₖ ∘ q = cₖ ∘ π`, as both agree on the
        -- dense open image of `U` and `ℙ(σₖ; S)` is separated.
        rintro _ ⟨x, rfl⟩
        obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (hVc.ge (Set.mem_univ (π x)))
        refine TopologicalSpace.Opens.mem_iSup.mpr ⟨k, ?_⟩
        let Z := π ⁻¹ᵁ V k
        have hrange : Set.range t ⊆ Set.range Z.ι := by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          change π (t y) ∈ V k
          rw [← Scheme.Hom.comp_apply, htπ]
          exact hUV k y.2
        let tZ := IsOpenImmersion.lift Z.ι t hrange
        have htZ : tZ ≫ Z.ι = t := IsOpenImmersion.lift_fac _ _ _
        have : IsSchemeTheoreticallyDominant tZ :=
          IsSchemeTheoreticallyDominant.of_isPullback
            (IsOpenImmersion.isPullback_lift_id t Z.ι hrange).flip
        have : QuasiCompact tZ := by
          have : QuasiCompact (tZ ≫ Z.ι) := by rw [htZ]; infer_instance
          exact QuasiCompact.of_comp tZ Z.ι
        have hσk := hσ k
        have hab : Z.ι ≫ q ≫ p k =
            (π ∣_ V k) ≫ c k ≫ (ProjectiveSpace.basicOpen S (i k)).ι := by
          refine ext_of_isDominant_of_isSeparated (ℙ(σ k; S) ↘ S) ?_ tZ ?_
          · simp only [Category.assoc, hco, hp]
            rw [← hπq, morphismRestrict_ι_assoc]
          · rw [← Category.assoc, htZ, ← Category.assoc, htq, hj]
            have : tZ ≫ π ∣_ V k = X.homOfLE (hUV k) := by
              rw [← cancel_mono (V k).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, htZ,
                htπ, X.homOfLE_ι]
            rw [reassoc_of% this]
        have hx : x ∈ Z := hk
        have := congr($hab ⟨x, hx⟩)
        simp only [Scheme.Hom.comp_apply] at this
        change p k (q x) ∈ ProjectiveSpace.basicOpen S (i k)
        rw [show q x = q (Z.ι ⟨x, hx⟩) from rfl, this]
        have := Set.mem_range_self (f := (ProjectiveSpace.basicOpen S (i k)).ι)
          (c k ((π ∣_ V k) ⟨x, hx⟩))
        rwa [Scheme.Opens.range_ι] at this
      · -- over `Oₖ`, `q` factors through the closed subscheme `Γₖ = Vₖ ×_{D₊(xᵢ)} Oₖ`.
        have hσk := hσ k
        let D := ProjectiveSpace.basicOpen S (i k)
        let pk : (O k).toScheme ⟶ D.toScheme := p k ∣_ D
        let γ : pullback (c k) pk ⟶ pullback f πQ :=
          pullback.lift (pullback.fst (c k) pk ≫ (V k).ι) (pullback.snd (c k) pk ≫ (O k).ι) (by
            rw [Category.assoc, Category.assoc, ← hco, pullback.condition_assoc,
              morphismRestrict_ι_assoc, hp])
        let Yk := pullback.snd f πQ ⁻¹ᵁ O k
        have hγ : Set.range γ ⊆ Set.range Yk.ι := by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          change pullback.snd f πQ (γ y) ∈ O k
          rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply]
          exact (pullback.snd (c k) pk y).2
        let γ' := IsOpenImmersion.lift Yk.ι γ hγ
        have hγ' : γ' ≫ Yk.ι = γ := IsOpenImmersion.lift_fac _ _ _
        have hγ's : γ' ≫ (pullback.snd f πQ ∣_ O k) = pullback.snd (c k) pk := by
          rw [← cancel_mono (O k).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hγ',
            pullback.lift_snd]
        have : IsClosedImmersion γ' := by
          have : IsClosedImmersion (γ' ≫ (pullback.snd f πQ ∣_ O k)) := by
            rw [hγ's]; infer_instance
          exact IsClosedImmersion.of_comp γ' (pullback.snd f πQ ∣_ O k)
        have hjD : ∀ y, p k (j y) ∈ D := fun y ↦ by
          rw [← Scheme.Hom.comp_apply, hj]
          have := Set.mem_range_self (f := D.ι) (c k (X.homOfLE (hUV k) y))
          rwa [Scheme.Opens.range_ι] at this
        have hrange : Set.range t ⊆ Set.range (ι' ⁻¹ᵁ Yk).ι := by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          change p k (q (t y)) ∈ D
          rw [← Scheme.Hom.comp_apply t q, htq]
          exact hjD y
        have hjO : Set.range j ⊆ Set.range (O k).ι := by
          rintro _ ⟨y, rfl⟩
          rw [Scheme.Opens.range_ι]
          exact hjD y
        let sk : U.toScheme ⟶ pullback (c k) pk :=
          pullback.lift (X.homOfLE (hUV k)) (IsOpenImmersion.lift (O k).ι j hjO) (by
            rw [← cancel_mono D.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
              IsOpenImmersion.lift_fac_assoc, hj])
        have hs : IsOpenImmersion.lift (ι' ⁻¹ᵁ Yk).ι t hrange ≫ ι' ∣_ Yk = sk ≫ γ' := by
          rw [← cancel_mono Yk.ι, Category.assoc, morphismRestrict_ι,
            IsOpenImmersion.lift_fac_assoc, ht, Category.assoc, hγ']
          apply pullback.hom_ext
          · rw [hj'₁, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, X.homOfLE_ι]
          · rw [hj'₂, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
              IsOpenImmersion.lift_fac]
        have hker' : γ'.ker ≤ (ι' ∣_ Yk).ker := by
          rw [hker Yk hrange, hs]
          exact Scheme.Hom.le_ker_comp sk γ'
        let ℓ := IsClosedImmersion.lift γ' (ι' ∣_ Yk) hker'
        have hℓ : ℓ ≫ γ' = ι' ∣_ Yk := IsClosedImmersion.lift_fac _ _ _
        have : IsClosedImmersion ℓ := by
          have : IsClosedImmersion (ℓ ≫ γ') := by rw [hℓ]; infer_instance
          exact IsClosedImmersion.of_comp_isClosedImmersion ℓ γ'
        change IsImmersion ((ι' ≫ pullback.snd f πQ) ∣_ O k)
        rw [morphismRestrict_comp, ← hℓ, Category.assoc, hγ's]
        have := hc k
        exact (inferInstance : IsImmersion (ℓ ≫ pullback.snd (c k) pk))
    have : QuasiCompact q := inferInstance
    rw [hπq]
    infer_instance
  · -- over `U`, `π` has the inverse `t`.
    let W := pullback.fst f πQ ⁻¹ᵁ U
    have hrange : Set.range t ⊆ Set.range (ι' ⁻¹ᵁ W).ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      change π (t x) ∈ U
      rw [← Scheme.Hom.comp_apply, htπ]
      exact x.2
    let t' := IsOpenImmersion.lift (ι' ⁻¹ᵁ W).ι t hrange
    have ht' : t' ≫ (ι' ⁻¹ᵁ W).ι = t := IsOpenImmersion.lift_fac _ _ _
    have : IsSchemeTheoreticallyDominant t' :=
      IsSchemeTheoreticallyDominant.of_isPullback
        (IsOpenImmersion.isPullback_lift_id t (ι' ⁻¹ᵁ W).ι hrange).flip
    have hW : Set.range j' ⊆ Set.range W.ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      change pullback.fst f πQ (j' x) ∈ U
      rw [← Scheme.Hom.comp_apply, hj'₁]
      exact x.2
    let g := IsOpenImmersion.lift W.ι j' hW
    have hg : g ≫ W.ι = j' := IsOpenImmersion.lift_fac _ _ _
    have hgsec : g ≫ (pullback.fst f πQ ∣_ U) = 𝟙 _ := by
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hg, hj'₁,
        Category.id_comp]
    have : IsClosedImmersion g := by
      have : IsClosedImmersion (g ≫ (pullback.fst f πQ ∣_ U)) := by rw [hgsec]; infer_instance
      exact IsClosedImmersion.of_comp g (pullback.fst f πQ ∣_ U)
    have htk : t' ≫ (ι' ∣_ W) = g := by
      rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, ht', hg, ht]
    have : IsClosedImmersion t' := by
      have : IsClosedImmersion (t' ≫ ι' ∣_ W) := by rw [htk]; infer_instance
      exact IsClosedImmersion.of_comp_isClosedImmersion t' (ι' ∣_ W)
    have : IsIso t' := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr t'.ker_eq_bot
    have h1 : t' ≫ (ι' ∣_ W ≫ pullback.fst f πQ ∣_ U) = 𝟙 _ := by
      rw [← Category.assoc, htk, hgsec]
    change IsIso ((ι' ≫ pullback.fst f πQ) ∣_ U)
    rw [morphismRestrict_comp, IsIso.eq_inv_of_hom_inv_id h1]
    exact IsIso.inv_isIso (f := t')
  · -- `X'` is reduced and irreducible, as the closure of the image of `U`.
    have hUirr : IsIrreducible (U : Set X) :=
      ⟨hUn, (IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset U.2
        (Set.subset_univ _)⟩
    have : IrreducibleSpace U := Subtype.irreducibleSpace hUirr
    have : IrreducibleSpace j'.image := by
      rw [irreducibleSpace_def]
      have := ((IrreducibleSpace.isIrreducible_univ U).image t t.continuous.continuousOn).closure
      rwa [Set.image_univ, t.denseRange.closure_range] at this
    exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Chow's lemma for a proper morphism (EGA II 5.6.1, Hartshorne Ex. II.4.10): for an integral
scheme `X` proper over an affine scheme `S`, there are an integral scheme `X'`, H-projective over
`S`, and an H-projective surjective morphism `π : X' ⟶ X` which is an isomorphism over a non-empty
open subset of `X`. -/
theorem exists_isHProjective_of_isProper [IsAffine S] (f : X ⟶ S) [IsProper f] [IsIntegral X] :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X) (U : X.Opens), IsHProjective π ∧ Surjective π ∧
      IsHProjective (π ≫ f) ∧ (U : Set X).Nonempty ∧ IsIso (π ∣_ U) ∧ IsIntegral X' := by
  obtain ⟨X', π, U, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_isHProjective_isIso_morphismRestrict f
  exact ⟨X', π, U, h₁, h₂, IsHProjective.of_isHQuasiProjective (π ≫ f), h₄, h₅, h₆⟩

end AlgebraicGeometry
