/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import SGA.Foundations.Formal.CompletionNoetherian
import SGA.Foundations.Formal.FormalScheme

/-!
# Formal completion of a scheme along a closed subscheme

Let `X` be a scheme and `𝓘` a quasi-coherent ideal sheaf, defining the closed subscheme
`Z = V(𝓘)`. The *formal completion* `X̂` of `X` along `Z` (EGA I, §10.8) is the colimit of the
infinitesimal neighbourhoods `Xₙ = V(𝓘ⁿ⁺¹)` of `Z`: its underlying space is `Z` and its structure
sheaf is `lim← 𝒪_X ⧸ 𝓘ⁿ⁺¹`. It comes with a canonical morphism `X̂ ⟶ X` of locally ringed spaces.
For `X` affine with `𝓘 = Ĩ`, `X̂ = Spf (Γ(X, 𝒪) , I)` (`formalCompletionIsoSpf`), which is
`Spf Â` for the `I`-adic completion `Â` of `Γ(X, 𝒪)`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.infinitesimalDiagram 𝓘`: `n ↦ V(𝓘ⁿ⁺¹)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.formalCompletion 𝓘`: the formal completion `X̂`.
* `AlgebraicGeometry.Scheme.IdealSheafData.formalCompletionι 𝓘 : X̂ ⟶ X`.
* `AlgebraicGeometry.Scheme.IdealSheafData.formalCompletionHomeomorph`: `X̂ ≃ₜ Z`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (𝓘 : X.IdealSheafData)

lemma pow_succ_antitone {m n : ℕ} (h : m ≤ n) : 𝓘 ^ (n + 1) ≤ 𝓘 ^ (m + 1) :=
  fun U ↦ by simpa using Ideal.pow_le_pow_right (I := 𝓘.ideal U) (Nat.succ_le_succ h)

/-- The infinitesimal neighbourhoods `V(𝓘) ⟶ V(𝓘²) ⟶ V(𝓘³) ⟶ ⋯` of `V(𝓘)`. -/
noncomputable abbrev infinitesimalDiagram : ℕ ⥤ Scheme.{u} where
  obj n := (𝓘 ^ (n + 1)).subscheme
  map f := inclusion (𝓘.pow_succ_antitone (leOfHom f))
  map_id _ := inclusion_id _
  map_comp _ _ := (inclusion_comp _ _).symm

instance : IsThickeningSequence 𝓘.infinitesimalDiagram where
  isClosedImmersion n := by
    have h₁ : IsClosedImmersion (𝓘 ^ (n + 1 + 1)).subschemeι := inferInstance
    have : IsClosedImmersion (inclusion (𝓘.pow_succ_antitone n.le_succ) ≫
        (𝓘 ^ (n + 1 + 1)).subschemeι) := by
      rw [inclusion_subschemeι]
      infer_instance
    exact @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ _ _ h₁ this
  surjective n := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨z, hz⟩ : (𝓘 ^ (n + 1 + 1)).subschemeι y ∈ Set.range (𝓘 ^ (n + 1)).subschemeι := by
      rw [range_subschemeι, support_pow_succ, ← support_pow_succ 𝓘 (n + 1), ← range_subschemeι]
      exact ⟨y, rfl⟩
    refine ⟨z, (𝓘 ^ (n + 1 + 1)).subschemeι.isClosedEmbedding.injective ?_⟩
    change (inclusion (𝓘.pow_succ_antitone n.le_succ) ≫ (𝓘 ^ (n + 1 + 1)).subschemeι) z = _
    rw [inclusion_subschemeι, hz]

/-- The formal completion `X̂` of `X` along the closed subscheme `V(𝓘)` (EGA I, §10.8): the colimit
of the infinitesimal neighbourhoods `V(𝓘ⁿ⁺¹)`, with structure sheaf `lim← 𝒪_X ⧸ 𝓘ⁿ⁺¹`. -/
noncomputable abbrev formalCompletion : LocallyRingedSpace.{u} :=
  formalColimit 𝓘.infinitesimalDiagram

/-- The canonical morphism `X̂ ⟶ X` of locally ringed spaces (EGA I, §10.8), induced by the
closed immersions `V(𝓘ⁿ⁺¹) ⟶ X`. -/
noncomputable def formalCompletionι : 𝓘.formalCompletion ⟶ X.toLocallyRingedSpace :=
  formalColimit.desc _ (fun n ↦ (𝓘 ^ (n + 1)).subschemeι.toLRSHom) fun _ ↦
    (Scheme.Hom.comp_toLRSHom _ _).symm.trans
      (congr_arg Scheme.Hom.toLRSHom (inclusion_subschemeι _))

@[reassoc (attr := simp)]
lemma ι_formalCompletionι (n : ℕ) :
    formalColimit.ι 𝓘.infinitesimalDiagram n ≫ 𝓘.formalCompletionι =
      (𝓘 ^ (n + 1)).subschemeι.toLRSHom :=
  formalColimit.ι_desc _ _ _ n

lemma formalCompletionι_base_homeomorph (n : ℕ) (y : 𝓘.infinitesimalDiagram.obj n) :
    𝓘.formalCompletionι.base (formalColimit.homeomorph 𝓘.infinitesimalDiagram n y) =
      (𝓘 ^ (n + 1)).subschemeι y := by
  change (formalColimit.ι _ n ≫ 𝓘.formalCompletionι).base y = _
  rw [ι_formalCompletionι]

/-- The underlying continuous map of `X̂ ⟶ X` is a closed embedding (EGA I, §10.8). -/
lemma isClosedEmbedding_formalCompletionι :
    Topology.IsClosedEmbedding 𝓘.formalCompletionι.base := by
  let h := formalColimit.homeomorph 𝓘.infinitesimalDiagram 0
  have : ⇑𝓘.formalCompletionι.base = (𝓘 ^ (0 + 1)).subschemeι.base ∘ h.symm := by
    ext x
    obtain ⟨y, rfl⟩ := h.surjective x
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
    exact 𝓘.formalCompletionι_base_homeomorph 0 y
  rw [this]
  exact (𝓘 ^ (0 + 1)).subschemeι.isClosedEmbedding.comp h.symm.isClosedEmbedding

/-- The underlying space of `X̂` is the support `V(𝓘)` of `𝓘` (EGA I, §10.8). -/
lemma range_formalCompletionι : Set.range 𝓘.formalCompletionι.base = 𝓘.support := by
  let h := formalColimit.homeomorph 𝓘.infinitesimalDiagram 0
  rw [← h.surjective.range_comp, ← support_pow_succ 𝓘 0, ← range_subschemeι]
  congr 1
  ext y
  exact 𝓘.formalCompletionι_base_homeomorph 0 y

section IsAffine

variable [IsAffine X]

/-- The whole space, as an affine open of an affine scheme. -/
abbrev topAffineOpen (X : Scheme.{u}) [IsAffine X] : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩

/-- For `X` affine, `V(𝓘) = Spec (Γ(X, 𝒪) ⧸ Γ(X, 𝓘))`. -/
noncomputable def subschemeIsoSpecTop :
    Spec (.of (Γ(X, ⊤) ⧸ 𝓘.ideal (topAffineOpen X))) ≅ 𝓘.subscheme := by
  have : IsOpenImmersion (𝓘.subschemeCover.f (topAffineOpen X)) :=
    𝓘.subschemeCover.map_prop _
  have : Epi (𝓘.subschemeCover.f (topAffineOpen X)).base := by
    rw [TopCat.epi_iff_surjective, ← Set.range_eq_univ]
    have := congr_arg SetLike.coe (𝓘.opensRange_subschemeCover_map (topAffineOpen X))
    rw [Scheme.Hom.coe_opensRange] at this
    rw [this]
    rfl
  have h := IsOpenImmersion.isIso (𝓘.subschemeCover.f (topAffineOpen X))
  exact @asIso _ _ _ _ (𝓘.subschemeCover.f (topAffineOpen X)) h

@[simp]
lemma subschemeIsoSpecTop_hom :
    𝓘.subschemeIsoSpecTop.hom = 𝓘.subschemeCover.f (topAffineOpen X) := rfl

/-- For `X` affine, `V(𝓘ⁿ⁺¹) = Spec (Γ(X, 𝒪) ⧸ Iⁿ⁺¹)` with `I = Γ(X, 𝓘)`, naturally in `n`. -/
noncomputable def infinitesimalDiagramIsoSpfDiagram :
    Spf.diagram Γ(X, ⊤) (𝓘.ideal (topAffineOpen X)) ≅ 𝓘.infinitesimalDiagram :=
  NatIso.ofComponents (fun n ↦ (𝓘 ^ (n + 1)).subschemeIsoSpecTop) fun {m n} f ↦ by
    simp only [subschemeIsoSpecTop_hom]
    exact (subSchemeCover_map_inclusion (𝓘.pow_succ_antitone (leOfHom f)) _).symm

/-- For `X` affine, the formal completion of `X` along `V(𝓘)` is `Spf (Γ(X, 𝒪), I)` with
`I = Γ(X, 𝓘)` (EGA I, §10.8): its ring of global sections is `lim← Γ(X, 𝒪) ⧸ Iⁿ⁺¹`
(`Scheme.formalColimit.isLimitΓcone`), the `I`-adic completion of `Γ(X, 𝒪)`. -/
noncomputable def formalCompletionIsoSpf :
    𝓘.formalCompletion ≅ Spf Γ(X, ⊤) (𝓘.ideal (topAffineOpen X)) :=
  HasColimit.isoOfNatIso
    (Functor.isoWhiskerRight (𝓘.infinitesimalDiagramIsoSpfDiagram).symm
      Scheme.forgetToLocallyRingedSpace)

/-- For `X` affine and noetherian, the formal completion of `X` along a closed subscheme is a
(affine) locally noetherian formal scheme: it is `Spf` of the completion of `Γ(X, 𝒪)`. -/
theorem isLocallyNoetherianFormalScheme_formalCompletion_of_isAffine
    [IsNoetherianRing Γ(X, ⊤)] :
    LocallyRingedSpace.IsLocallyNoetherianFormalScheme 𝓘.formalCompletion :=
  LocallyRingedSpace.IsLocallyNoetherianFormalScheme.prop_of_iso
    (𝓘.formalCompletionIsoSpf).symm (Spf.isLocallyNoetherianFormalScheme_of_isNoetherianRing _ _)

end IsAffine

end AlgebraicGeometry.Scheme.IdealSheafData
