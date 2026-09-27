/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Differentials.BaseChangeAffine
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Base change of `Ω`

For a cartesian square of schemes
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
the canonical map `g'^* Ω_{X/Y} ⟶ Ω_{X'/Y'}` (`Scheme.Hom.relativeDifferentialsBaseChange`)
is an isomorphism (`Scheme.Hom.relativeDifferentialsBaseChangeIso`; EGA IV 16.4.5, Stacks Project,
Tag 01V0).

The map is adjoint to `Ω_{X/Y} ⟶ g'_* Ω_{X'/Y'}`, `d a ↦ d (g'^♯ a)`. To show that it is an
isomorphism we check it on the charts `Spec (Γ(X, U) ⊗_{Γ(Y, V)} Γ(Y', V')) ⟶ X'` given by affine
opens, where it follows from the bijectivity of `Der_{A'}(B ⊗_A A', N) → Der_A(B, N)`
(`AlgebraicGeometry.BaseChangeChart.bijective_pushforward`) and the universal properties.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TensorProduct

noncomputable section

namespace AlgebraicGeometry

namespace BaseChangeChart

section Tensor

variable {A B A' : CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ A')

/-- The ring `B ⊗_A A'` for ring homomorphisms `φ : A ⟶ B` and `ψ : A ⟶ A'`. -/
def tensorRing : CommRingCat.{u} :=
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  CommRingCat.of (B ⊗[A] A')

/-- The map `B ⟶ B ⊗_A A'`. -/
def tensorInl : B ⟶ tensorRing φ ψ :=
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom

/-- The map `A' ⟶ B ⊗_A A'`. -/
def tensorInr : A' ⟶ tensorRing φ ψ :=
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom

lemma isPushout_tensor : IsPushout φ ψ (tensorInl φ ψ) (tensorInr φ ψ) := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  exact CommRingCat.isPushout_tensorProduct A B A'

lemma mem_closure_tensor (c : tensorRing φ ψ) :
    c ∈ Subring.closure (Set.range (tensorInl φ ψ) ∪ Set.range (tensorInr φ ψ)) := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  change c ∈ Subring.closure (Set.range (fun b : B ↦ (b ⊗ₜ[A] (1 : A') : B ⊗[A] A')) ∪
    Set.range (fun a' : A' ↦ ((1 : B) ⊗ₜ[A] a' : B ⊗[A] A')))
  induction c using TensorProduct.induction_on with
  | zero => exact Subring.zero_mem _
  | tmul b a' =>
    rw [show b ⊗ₜ[A] a' = (b ⊗ₜ[A] (1 : A')) * ((1 : B) ⊗ₜ[A] a') by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨b, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨a', rfl⟩))
  | add x y hx hy => exact Subring.add_mem _ hx hy

-- `letI` is needed here: the `Module (B ⊗[A] A') N` instance must be inlined.
set_option linter.style.haveILetI false in
lemma exists_extension_tensor (N : Type u) [AddCommGroup N] [Module (tensorRing φ ψ) N]
    (δ : B →+ N) (hδ : ∀ x y, δ (x * y) = tensorInl φ ψ x • δ y + tensorInl φ ψ y • δ x)
    (hδA : ∀ a, δ (φ a) = 0) :
    ∃ δ' : tensorRing φ ψ →+ N, (∀ x y, δ' (x * y) = x • δ' y + y • δ' x) ∧
      (∀ b, δ' (tensorInl φ ψ b) = δ b) ∧ ∀ a', δ' (tensorInr φ ψ a') = 0 := by
  letI := φ.hom.toAlgebra
  letI := ψ.hom.toAlgebra
  letI : Module (B ⊗[A] A') N := ‹Module (tensorRing φ ψ) N›
  refine ⟨derivationExtend δ hδ hδA, derivationExtend_mul δ hδ hδA, fun b ↦ ?_, fun a' ↦ ?_⟩
  · change ((1 : B) ⊗ₜ[A] (1 : A')) • δ b = δ b
    rw [← Algebra.TensorProduct.one_def, one_smul]
  · change ((1 : B) ⊗ₜ[A] a') • δ 1 = 0
    have h1 : δ 1 = 0 := by simpa using hδA 1
    rw [h1, smul_zero]

end Tensor

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) {U : X.Opens} {V : Y.Opens}
  {V' : Y'.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
  (eU : U ≤ f ⁻¹ᵁ V) (eV' : V' ≤ g ⁻¹ᵁ V)

/-- The ring `Γ(X, U) ⊗_{Γ(Y, V)} Γ(Y', V')`. -/
abbrev ring : CommRingCat.{u} := tensorRing (f.appLE V U eU) (g.appLE V V' eV')

/-- The map `Spec (Γ(X, U) ⊗_{Γ(Y, V)} Γ(Y', V')) ⟶ X`. -/
abbrev fst : Spec (ring f g eU eV') ⟶ X :=
  Spec.map (tensorInl (f.appLE V U eU) (g.appLE V V' eV')) ≫ hU.fromSpec

/-- The map `Spec (Γ(X, U) ⊗_{Γ(Y, V)} Γ(Y', V')) ⟶ Y'`. -/
abbrev snd : Spec (ring f g eU eV') ⟶ Y' :=
  Spec.map (tensorInr (f.appLE V U eU) (g.appLE V V' eV')) ≫ hV'.fromSpec

include hV in
lemma fst_comp_eq : fst f g hU eU eV' ≫ f = snd f g hV' eU eV' ≫ g := by
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hV hU eU, Category.assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec g hV hV' eV', ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, (isPushout_tensor _ _).w]

/-- The local bijectivity for the chart `Spec (Γ(X, U) ⊗_{Γ(Y, V)} Γ(Y', V'))`. -/
theorem bijective_pushforward_chart (q : Spec (ring f g eU eV') ⟶ X)
    (p : Spec (ring f g eU eV') ⟶ Y') (hq : q = fst f g hU eU eV') (hp : p = snd f g hV' eU eV')
    (w : p ≫ g = q ≫ f) (N : (Spec (ring f g eU eV')).Modules) :
    Function.Bijective fun D : N.Derivation p ↦ ((D.restrictScalars p g).congrHom w).pushforward :=
  bijective_pushforward f g hU hV' eU _ _ (mem_closure_tensor _ _)
    (fun N _ _ δ hδ hδA ↦ exists_extension_tensor _ _ N δ hδ hδA) q p hq hp w N

section Pullback

variable {X' : Scheme.{u}} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (h : IsPullback g' f' f g)

/-- The chart `Spec (Γ(X, U) ⊗_{Γ(Y, V)} Γ(Y', V')) ⟶ X'` of the fibre product. -/
def chart : Spec (ring f g eU eV') ⟶ X' :=
  h.lift (fst f g hU eU eV') (snd f g hV' eU eV') (fst_comp_eq f g hU hV hV' eU eV')

@[reassoc (attr := simp)]
lemma chart_fst : chart f g hU hV hV' eU eV' h ≫ g' = fst f g hU eU eV' := h.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma chart_snd : chart f g hU hV hV' eU eV' h ≫ f' = snd f g hV' eU eV' := h.lift_snd _ _ _

lemma chart_eq : chart f g hU hV hV' eU eV' h =
    (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_tensor _ _)).isoPullback.hom ≫
      pullback.map _ _ _ _ hU.fromSpec hV'.fromSpec hV.fromSpec
        (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU eU)
        (IsAffineOpen.SpecMap_appLE_fromSpec g hV hV' eV') ≫ h.isoPullback.inv := by
  apply h.hom_ext
  · rw [chart_fst, Category.assoc, Category.assoc, h.isoPullback_inv_fst, pullback.lift_fst,
      ← Category.assoc, IsPullback.isoPullback_hom_fst]
  · rw [chart_snd, Category.assoc, Category.assoc, h.isoPullback_inv_snd, pullback.lift_snd,
      ← Category.assoc, IsPullback.isoPullback_hom_snd]

instance isOpenImmersion_chart : IsOpenImmersion (chart f g hU hV hV' eU eV' h) := by
  rw [chart_eq]
  infer_instance

lemma mem_range_chart (x : X') (hx : g' x ∈ U) (hx' : f' x ∈ V') :
    x ∈ Set.range (chart f g hU hV hV' eU eV' h) := by
  let e := (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_tensor (f.appLE V U eU)
    (g.appLE V V' eV'))).isoPullback
  have hy : h.isoPullback.hom x ∈ Set.range (pullback.map _ _ _ _ hU.fromSpec hV'.fromSpec
      hV.fromSpec (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU eU)
      (IsAffineOpen.SpecMap_appLE_fromSpec g hV hV' eV')) := by
    rw [Scheme.Pullback.range_map]
    refine ⟨?_, ?_⟩
    · change pullback.fst f g (h.isoPullback.hom x) ∈ Set.range hU.fromSpec
      rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst, hU.range_fromSpec]
      exact hx
    · change pullback.snd f g (h.isoPullback.hom x) ∈ Set.range hV'.fromSpec
      rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_snd, hV'.range_fromSpec]
      exact hx'
  obtain ⟨z, hz⟩ := hy
  refine ⟨e.inv z, ?_⟩
  have h₁ : e.hom (e.inv z) = z := by rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
  have h₂ : h.isoPullback.inv (h.isoPullback.hom x) = x := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback.hom_inv_id]; rfl
  rw [chart_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h₁, hz, h₂]

end Pullback

end BaseChangeChart

namespace Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

lemma Hom.app_presheaf_map (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (x : Γ(M, V)) :
    φ.app U (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app V x) :=
  congr($(φ.mapPresheaf.naturality i.op) x)

/-- A morphism of `𝒪_X`-modules whose restrictions along a family of open immersions covering `X`
are isomorphisms is an isomorphism. -/
lemma isIso_of_isIso_restrictFunctor_map (φ : M ⟶ N)
    (H : ∀ x : X, ∃ (S : Scheme.{u}) (k : S ⟶ X) (_ : IsOpenImmersion k), x ∈ Set.range k ∧
      IsIso ((restrictFunctor k).map φ)) : IsIso φ := by
  choose S k hk hx hiso using H
  have hbij (x : X) (W : X.Opens) :
      Function.Bijective (φ.app ((k x) ''ᵁ ((k x) ⁻¹ᵁ W))) :=
    (ConcreteCategory.isIso_iff_bijective _).mp
      (inferInstanceAs (IsIso (((restrictFunctor (k x)).map φ).app ((k x) ⁻¹ᵁ W))))
  have hmem (x : X) (W : X.Opens) (hxW : x ∈ W) : x ∈ (k x) ''ᵁ ((k x) ⁻¹ᵁ W) := by
    obtain ⟨p, hp⟩ := hx x
    exact ⟨p, by simpa [hp] using hxW, hp⟩
  have hinj (W : X.Opens) (s : Γ(M, W)) (hs : φ.app W s = 0) : s = 0 := by
    refine eq_zero_of_locally s fun x hxW ↦ ⟨_, (k x).image_preimage_le W, hmem x W hxW, ?_⟩
    apply (hbij x W).1
    rw [map_zero, Hom.app_presheaf_map, hs, map_zero]
  rw [Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun s t hst ↦ ?_, fun t ↦ ?_⟩
  · rw [← sub_eq_zero]
    exact hinj V _ (by rw [map_sub, hst, sub_self])
  · let U : V → X.Opens := fun x ↦ (k x) ''ᵁ ((k x) ⁻¹ᵁ V)
    have hUV (x : V) : U x ≤ V := (k x).image_preimage_le V
    let sf : ∀ x : V, Γ(M, U x) := fun x ↦
      (hbij x V).2 (N.presheaf.map (homOfLE (hUV x)).op t) |>.choose
    have hsf (x : V) : φ.app (U x) (sf x) = N.presheaf.map (homOfLE (hUV x)).op t :=
      (hbij x V).2 (N.presheaf.map (homOfLE (hUV x)).op t) |>.choose_spec
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := ⟨M.presheaf, M.isSheaf⟩)
      (U := U) V (fun x ↦ homOfLE (hUV x)) (fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hmem x V hx⟩)
      sf (fun x y ↦ by
        rw [← sub_eq_zero]
        refine hinj _ _ ?_
        change φ.app (U x ⊓ U y) (M.presheaf.map (homOfLE inf_le_left).op (sf x) -
          M.presheaf.map (homOfLE inf_le_right).op (sf y)) = 0
        rw [map_sub, sub_eq_zero, Hom.app_presheaf_map, Hom.app_presheaf_map, hsf, hsf]
        exact presheaf_map_map N _ _ _ _ t)
    refine ⟨s, ?_⟩
    rw [← sub_eq_zero]
    refine eq_zero_of_locally _ fun x hx ↦ ⟨U ⟨x, hx⟩, hUV ⟨x, hx⟩, hmem x V hx, ?_⟩
    rw [map_sub, sub_eq_zero, ← Hom.app_presheaf_map]
    change φ.app (U ⟨x, hx⟩) (M.presheaf.map (homOfLE (hUV ⟨x, hx⟩)).op s) = _
    rw [hs ⟨x, hx⟩, hsf]

end Scheme.Modules

namespace Scheme.Hom

open Scheme.Modules

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (h : IsPullback g' f' f g)

/-- The derivation `𝒪_X → g'_* M`, `a ↦ D (g'^♯ a)`, induced by a derivation `D : 𝒪_{X'} → M`
relative to `f'`. -/
def baseChangeDerivation {M : X'.Modules} (D : M.Derivation f') :
    ((pushforward g').obj M).Derivation f :=
  ((D.restrictScalars f' g).congrHom h.w.symm).pushforward

@[simp]
lemma baseChangeDerivation_app {M : X'.Modules} (D : M.Derivation f') (T : X.Opens)
    (a : Γ(X, T)) : (baseChangeDerivation h D).app T a = D.app (g' ⁻¹ᵁ T) (g'.app T a) :=
  rfl

/-- The canonical map `g'^* Ω_{X/Y} ⟶ Ω_{X'/Y'}` for a cartesian square, adjoint to
`Ω_{X/Y} ⟶ g'_* Ω_{X'/Y'}`, `d a ↦ d (g'^♯ a)`. -/
def relativeDifferentialsBaseChange :
    (Scheme.Modules.pullback g').obj f.relativeDifferentials ⟶ f'.relativeDifferentials :=
  ((pullbackPushforwardAdjunction g').homEquiv _ _).symm
    (f.isUniversal.desc (baseChangeDerivation h f'.universalDerivation))

lemma relativeDifferentialsBaseChange_homEquiv :
    (pullbackPushforwardAdjunction g').homEquiv _ _ (relativeDifferentialsBaseChange h) =
      f.isUniversal.desc (baseChangeDerivation h f'.universalDerivation) :=
  Equiv.apply_symm_apply _ _

section restrict

variable {S : Scheme.{u}} (k : S ⟶ X') [IsOpenImmersion k]
  (w : (k ≫ f') ≫ g = (k ≫ g') ≫ f)

/-- The map `Der_{k ≫ f'}(𝒪_S, N) → Der_f(𝒪_X, g'_* k_* N)`. -/
abbrev restrictBaseChangeDerivation {N : S.Modules} (D : N.Derivation (k ≫ f')) :
    ((pushforward g').obj ((pushforward k).obj N)).Derivation f :=
  ((D.restrictScalars (k ≫ f') g).congrHom w).pushforward

/-- The map `Hom(k^* g'^* Ω_{X/Y}, N) → Der_f(𝒪_X, g'_* k_* N)` given by adjunction. -/
def restrictPullbackHomDerivation {N : S.Modules}
    (u : (Scheme.Modules.restrictFunctor k).obj
      ((Scheme.Modules.pullback g').obj f.relativeDifferentials) ⟶ N) :
    ((pushforward g').obj ((pushforward k).obj N)).Derivation f :=
  f.universalDerivation.postcomp ((pullbackPushforwardAdjunction g').homEquiv _ _
    ((Scheme.Modules.restrictAdjunction k).homEquiv _ _ u))

lemma restrictPullbackHomDerivation_injective {N : S.Modules} :
    Function.Injective (restrictPullbackHomDerivation k (f := f) (g' := g') (N := N)) :=
  fun _ _ e ↦ ((Scheme.Modules.restrictAdjunction k).homEquiv _ _).injective
    (((pullbackPushforwardAdjunction g').homEquiv _ _).injective
      (f.isUniversal.postcomp_injective _ _ e))

lemma restrictPullbackHomDerivation_comp {N N' : S.Modules}
    (u : (Scheme.Modules.restrictFunctor k).obj
      ((Scheme.Modules.pullback g').obj f.relativeDifferentials) ⟶ N) (v : N ⟶ N') :
    restrictPullbackHomDerivation k (u ≫ v) =
      (restrictPullbackHomDerivation k u).postcomp
        ((pushforward g').map ((pushforward k).map v)) := by
  rw [restrictPullbackHomDerivation, restrictPullbackHomDerivation,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    ← Derivation.postcomp_comp]

omit [IsOpenImmersion k] in
lemma restrictBaseChangeDerivation_postcomp {N N' : S.Modules} (D : N.Derivation (k ≫ f'))
    (v : N ⟶ N') :
    restrictBaseChangeDerivation k w (D.postcomp v) =
      (restrictBaseChangeDerivation k w D).postcomp
        ((pushforward g').map ((pushforward k).map v)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma restrictPullbackHomDerivation_restrict_map {N : S.Modules}
    (β : f'.relativeDifferentials.restrict k ⟶ N) :
    restrictPullbackHomDerivation k
        ((Scheme.Modules.restrictFunctor k).map (relativeDifferentialsBaseChange h) ≫ β) =
      restrictBaseChangeDerivation k w ((f'.universalDerivation.restrict k).postcomp β) := by
  rw [restrictPullbackHomDerivation, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, relativeDifferentialsBaseChange_homEquiv,
    Derivation.postcomp_comp, Derivation.Universal.fac]
  ext T a
  change ((Scheme.Modules.restrictAdjunction k).homEquiv _ _ β).app (g' ⁻¹ᵁ T)
      (f'.universalDerivation.app (g' ⁻¹ᵁ T) (g'.app T a)) =
    β.app (k ⁻¹ᵁ g' ⁻¹ᵁ T) ((f'.universalDerivation.restrict k).app (k ⁻¹ᵁ g' ⁻¹ᵁ T)
      ((k ≫ g').app T a))
  rw [Derivation.restrictAdjunction_homEquiv_app, ← Derivation.app_map, Derivation.restrict_app]
  congr 2
  exact (congr($(k.app_appIso_inv (g' ⁻¹ᵁ T)) (g'.app T a))).symm

/-- If `Der_{k ≫ f'}(𝒪_S, N) → Der_f(𝒪_X, g'_* k_* N)` is bijective for every `N`, then the
restriction of `g'^* Ω_{X/Y} ⟶ Ω_{X'/Y'}` along the open immersion `k` is an isomorphism. -/
theorem isIso_restrictFunctor_map_relativeDifferentialsBaseChange
    (hk : ∀ N : S.Modules, Function.Bijective (restrictBaseChangeDerivation k w (N := N))) :
    IsIso ((Scheme.Modules.restrictFunctor k).map (relativeDifferentialsBaseChange h)) := by
  set c := (Scheme.Modules.restrictFunctor k).map (relativeDifferentialsBaseChange h)
  obtain ⟨DQ, hDQ⟩ := (hk _).2 (restrictPullbackHomDerivation k
    (𝟙 ((Scheme.Modules.restrictFunctor k).obj
      ((Scheme.Modules.pullback g').obj f.relativeDifferentials))))
  let e := (f'.isUniversal.restrict k).desc DQ
  have he : (f'.universalDerivation.restrict k).postcomp e = DQ :=
    (f'.isUniversal.restrict k).fac DQ
  refine ⟨e, ?_, ?_⟩
  · apply restrictPullbackHomDerivation_injective k
    rw [restrictPullbackHomDerivation_restrict_map h k w, he, hDQ]
  · apply (f'.isUniversal.restrict k).postcomp_injective
    apply (hk _).1
    rw [Derivation.postcomp_comp, he, restrictBaseChangeDerivation_postcomp, hDQ,
      ← restrictPullbackHomDerivation_comp, Category.id_comp, ← Category.comp_id c,
      restrictPullbackHomDerivation_restrict_map h k w]

end restrict

/-- Base change for the sheaf of differentials: for a cartesian square, the canonical map
`g'^* Ω_{X/Y} ⟶ Ω_{X'/Y'}` is an isomorphism (EGA IV 16.4.5; Stacks Project, Tag 01V0). -/
instance isIso_relativeDifferentialsBaseChange : IsIso (relativeDifferentialsBaseChange h) := by
  refine isIso_of_isIso_restrictFunctor_map _ fun x ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (g' x))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show g' x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).2
  have hx' : f' x ∈ g ⁻¹ᵁ V := by
    change g (f' x) ∈ V
    rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]
    exact hxV
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hV'V⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open hx' (g ⁻¹ᵁ V).2
  let k := BaseChangeChart.chart f g hU hV hV' hUV hV'V h
  have : IsOpenImmersion k := BaseChangeChart.isOpenImmersion_chart f g hU hV hV' hUV hV'V h
  have w : (k ≫ f') ≫ g = (k ≫ g') ≫ f := by rw [Category.assoc, Category.assoc, h.w]
  refine ⟨_, k, inferInstance,
    BaseChangeChart.mem_range_chart f g hU hV hV' hUV hV'V h x hxU hxV', ?_⟩
  exact isIso_restrictFunctor_map_relativeDifferentialsBaseChange h k w fun N ↦
    BaseChangeChart.bijective_pushforward_chart f g hU hV' hUV hV'V (k ≫ g') (k ≫ f')
      (BaseChangeChart.chart_fst f g hU hV hV' hUV hV'V h)
      (BaseChangeChart.chart_snd f g hU hV hV' hUV hV'V h) w N

/-- Base change for the sheaf of differentials: `g'^* Ω_{X/Y} ≅ Ω_{X'/Y'}` for a cartesian
square (EGA IV 16.4.5; Stacks Project, Tag 01V0). -/
def relativeDifferentialsBaseChangeIso :
    (Scheme.Modules.pullback g').obj f.relativeDifferentials ≅ f'.relativeDifferentials :=
  asIso (relativeDifferentialsBaseChange h)

end Scheme.Hom

end AlgebraicGeometry
