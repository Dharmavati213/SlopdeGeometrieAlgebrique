/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Formal.Completion
import SGA.Foundations.Formal.OpenImmersion

/-!
# The formal completion is local on the scheme

Let `X` be a scheme, `𝓘` a quasi-coherent ideal sheaf and `f : U ⟶ X` an open immersion. The
formal completion of `U` along `V(𝓘|_U)` is an open formal subscheme of the formal completion
`X̂` of `X` along `V(𝓘)` (EGA I, §10.8): `Scheme.IdealSheafData.formalCompletionMap` is an open
immersion. Consequently the formal completion of a locally noetherian scheme along a closed
subscheme is a locally noetherian formal scheme
(`Scheme.IdealSheafData.isLocallyNoetherianFormalScheme_formalCompletion`), being covered by
the formal completions of affine noetherian opens, which are formal spectra of complete noetherian
rings.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

namespace LocallyRingedSpace.IsLocallyNoetherianFormalScheme

/-- A locally ringed space covered by open immersions from locally noetherian formal schemes is
a locally noetherian formal scheme. -/
theorem of_isOpenImmersion_cover {T : LocallyRingedSpace.{u}}
    (h : ∀ t : T, ∃ (S : LocallyRingedSpace.{u}) (φ : S ⟶ T) (_ : IsOpenImmersion φ),
      S.IsLocallyNoetherianFormalScheme ∧ t ∈ Set.range φ.base) :
    T.IsLocallyNoetherianFormalScheme := by
  intro t
  obtain ⟨S, φ, hφ, hS, s, rfl⟩ := h t
  obtain ⟨N, A, _, I, hA, hI, ⟨e⟩⟩ := hS s
  let W : OpenNhds (φ.base s) :=
    ⟨hφ.base_open.isOpenMap.functor.obj N.1, ⟨s, N.2, rfl⟩⟩
  refine ⟨W, A, inferInstance, I, hA, hI, ⟨?_ ≪≫ e⟩⟩
  refine isoOfRangeEq (T.ofRestrict W.isOpenEmbedding) (S.ofRestrict N.isOpenEmbedding ≫ φ) ?_
  rw [comp_base, TopCat.coe_comp, Set.range_comp]
  change Set.range (Opens.inclusion' W.1) = φ.base '' Set.range (Opens.inclusion' N.1)
  rw [Opens.set_range_inclusion', Opens.set_range_inclusion']
  rfl

end LocallyRingedSpace.IsLocallyNoetherianFormalScheme

namespace Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- Pulling back an ideal sheaf along an open immersion commutes with powers. -/
lemma comap_pow_of_isOpenImmersion (𝓘 : X.IdealSheafData) (f : Y ⟶ X) [IsOpenImmersion f]
    (k : ℕ) : (𝓘 ^ k).comap f = 𝓘.comap f ^ k := by
  ext V : 2
  let e := (f.appIso V).symm.commRingCatIsoToRingEquiv
  have h (J : X.IdealSheafData) : (J.comap f).ideal V =
      (J.ideal ⟨f ''ᵁ V, V.2.image_of_isOpenImmersion f⟩).comap e.toRingHom := by
    rw [ideal_comap_of_isOpenImmersion]
    rfl
  rw [ideal_pow, Pi.pow_apply, h, h, ideal_pow, Pi.pow_apply]
  change Ideal.comap e _ = Ideal.comap e _ ^ k
  rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]

/-- For an open immersion `f`, the closed subscheme `V(f⁻¹ 𝓙)` is an open subscheme of `V(𝓙)`. -/
lemma isOpenImmersion_subschemeMap (J : Y.IdealSheafData) (K : X.IdealSheafData) (f : Y ⟶ X)
    [IsOpenImmersion f] (H : K ≤ J.map f) (hJ : J = K.comap f) :
    IsOpenImmersion (subschemeMap J K f H) := by
  subst hJ
  rw [← comapIso_hom_snd]
  infer_instance

variable (𝓘 : X.IdealSheafData) (f : Y ⟶ X) [IsOpenImmersion f]

lemma pow_le_map_comap_pow (n : ℕ) : 𝓘 ^ n ≤ (𝓘.comap f ^ n).map f := by
  rw [← comap_pow_of_isOpenImmersion]
  exact le_map_comap _ f

/-- The open immersions `V((f⁻¹𝓘)ⁿ⁺¹) ⟶ V(𝓘ⁿ⁺¹)`, as a morphism of thickening sequences. -/
noncomputable def infinitesimalDiagramMap :
    (𝓘.comap f).infinitesimalDiagram ⟶ 𝓘.infinitesimalDiagram where
  app n := subschemeMap _ _ f (𝓘.pow_le_map_comap_pow f (n + 1))
  naturality {m n} h := by
    rw [← cancel_mono (𝓘 ^ (n + 1)).subschemeι]
    simp

instance (n : ℕ) : IsOpenImmersion ((𝓘.infinitesimalDiagramMap f).app n) :=
  isOpenImmersion_subschemeMap _ _ f (𝓘.pow_le_map_comap_pow f (n + 1))
    (comap_pow_of_isOpenImmersion 𝓘 f (n + 1)).symm

/-- The open immersion of formal completions `Û ⟶ X̂` induced by an open immersion `U ⟶ X`
(EGA I, §10.8). -/
noncomputable def formalCompletionMap : (𝓘.comap f).formalCompletion ⟶ 𝓘.formalCompletion :=
  formalColimit.map (𝓘.infinitesimalDiagramMap f)

instance : LocallyRingedSpace.IsOpenImmersion (𝓘.formalCompletionMap f) :=
  formalColimit.isOpenImmersion_map _

@[reassoc (attr := simp)]
lemma formalCompletionMap_formalCompletionι :
    𝓘.formalCompletionMap f ≫ 𝓘.formalCompletionι =
      (𝓘.comap f).formalCompletionι ≫ f.toLRSHom := by
  refine formalColimit.hom_ext _ fun n ↦ ?_
  rw [formalCompletionMap, formalColimit.ι_map_assoc, ι_formalCompletionι,
    ι_formalCompletionι_assoc, ← Scheme.Hom.comp_toLRSHom, ← Scheme.Hom.comp_toLRSHom]
  congr 1
  exact subschemeMap_subschemeι _ _ f (𝓘.pow_le_map_comap_pow f (n + 1))

/-- The formal completion of `U` is the part of `X̂` lying over `U`. -/
lemma range_formalCompletionMap :
    Set.range (𝓘.formalCompletionMap f).base =
      𝓘.formalCompletionι.base ⁻¹' Set.range f.base := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(𝓘.comap f).formalCompletionι.base y,
      (congr($(𝓘.formalCompletionMap_formalCompletionι f).base y)).symm⟩
  · rintro ⟨u, hu⟩
    obtain ⟨z, rfl⟩ := (formalColimit.homeomorph 𝓘.infinitesimalDiagram 0).surjective x
    rw [formalCompletionι_base_homeomorph] at hu
    have hu' : u ∈ Set.range ((𝓘.comap f) ^ (0 + 1)).subschemeι := by
      rw [range_subschemeι, support_pow_succ, support_comap]
      change f u ∈ (𝓘.support : Set X)
      rw [hu, ← support_pow_succ 𝓘 0, ← range_subschemeι]
      exact ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hu'
    refine ⟨formalColimit.homeomorph _ 0 w, ?_⟩
    have h₁ : (𝓘.infinitesimalDiagramMap f).app 0 w = z := by
      apply (𝓘 ^ (0 + 1)).subschemeι.isClosedEmbedding.injective
      rw [← Scheme.Hom.comp_apply, infinitesimalDiagramMap, subschemeMap_subschemeι,
        Scheme.Hom.comp_apply, hw, hu]
    rw [← h₁]
    exact congr($(formalColimit.ι_map (𝓘.infinitesimalDiagramMap f) 0).base w)

end Scheme.IdealSheafData

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The formal completion of a locally noetherian scheme along a closed subscheme is a locally
noetherian formal scheme (EGA I, §10.8): it is covered by the formal completions of the affine
noetherian opens, which are formal spectra of complete noetherian rings. -/
theorem isLocallyNoetherianFormalScheme_formalCompletion [IsLocallyNoetherian X]
    (𝓘 : X.IdealSheafData) :
    LocallyRingedSpace.IsLocallyNoetherianFormalScheme 𝓘.formalCompletion := by
  refine LocallyRingedSpace.IsLocallyNoetherianFormalScheme.of_isOpenImmersion_cover fun x ↦ ?_
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := 𝓘.formalCompletionι.base x) trivial
  have : IsAffine U.toScheme := hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsNoetherianRing Γ(U.toScheme, ⊤) :=
    isNoetherianRing_of_ringEquiv _ U.topIso.symm.commRingCatIsoToRingEquiv
  refine ⟨_, 𝓘.formalCompletionMap U.ι, inferInstance,
    (𝓘.comap U.ι).isLocallyNoetherianFormalScheme_formalCompletion_of_isAffine, ?_⟩
  rw [range_formalCompletionMap, Set.mem_preimage, Scheme.Opens.range_ι]
  exact hxU

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (𝓘 : Y.IdealSheafData) (𝓙 : X.IdealSheafData) (f : Y ⟶ X)

/-- If `f : Y ⟶ X` maps each `V(𝓘ⁿ⁺¹)` into `V(𝓙ⁿ⁺¹)` (that is, `𝓙ⁿ⁺¹ ⊆ f_*𝓘ⁿ⁺¹`), the induced
morphism of infinitesimal neighbourhoods. -/
noncomputable def infinitesimalDiagramHom (h : ∀ n, 𝓙 ^ (n + 1) ≤ (𝓘 ^ (n + 1)).map f) :
    𝓘.infinitesimalDiagram ⟶ 𝓙.infinitesimalDiagram where
  app n := subschemeMap _ _ f (h n)
  naturality {m n} g := by
    rw [← cancel_mono (𝓙 ^ (n + 1)).subschemeι]
    simp

/-- Functoriality of formal completions (EGA I, §10.9): a morphism `f : Y ⟶ X` mapping each
`V(𝓘ⁿ⁺¹)` into `V(𝓙ⁿ⁺¹)` induces `Ŷ ⟶ X̂`, compatible with `f`. -/
noncomputable def formalCompletionHom (h : ∀ n, 𝓙 ^ (n + 1) ≤ (𝓘 ^ (n + 1)).map f) :
    𝓘.formalCompletion ⟶ 𝓙.formalCompletion :=
  formalColimit.map (infinitesimalDiagramHom 𝓘 𝓙 f h)

@[reassoc (attr := simp)]
lemma formalCompletionHom_formalCompletionι (h : ∀ n, 𝓙 ^ (n + 1) ≤ (𝓘 ^ (n + 1)).map f) :
    formalCompletionHom 𝓘 𝓙 f h ≫ 𝓙.formalCompletionι = 𝓘.formalCompletionι ≫ f.toLRSHom := by
  refine formalColimit.hom_ext _ fun n ↦ ?_
  rw [formalCompletionHom, formalColimit.ι_map_assoc, ι_formalCompletionι,
    ι_formalCompletionι_assoc, ← Scheme.Hom.comp_toLRSHom, ← Scheme.Hom.comp_toLRSHom]
  congr 1
  exact subschemeMap_subschemeι _ _ f (h n)

end AlgebraicGeometry.Scheme.IdealSheafData
