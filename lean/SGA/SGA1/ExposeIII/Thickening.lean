/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.Schemes
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# SGA 1, Exposé III, 4.2: isomorphisms can be checked modulo a nilpotent ideal

Lemma III.4.2: let `Y₀ ⊆ Y` be defined by a locally nilpotent ideal, `u : X ⟶ X'` a morphism of
`Y`-schemes with `X` flat over `Y`. Then `u` is an isomorphism if and only if its reduction
`u₀ : X ×_Y Y₀ ⟶ X' ×_Y Y₀` is one. SGA: "the proof is easy, by passing to the affine case".

We prove it (`isIso_of_isPullback`, `isIso_iff_isIso_of_isPullback`) for `Y` locally noetherian
and `Y₀ ⊆ Y` a closed subscheme with the same underlying space (the situation of III.4.1). The
reduction `u₀` is given by cartesian squares. We also prove the variant for closed immersions,
without flatness (`isClosedImmersion_of_isPullback`), Corollary III.5.7 one level at a time
(`isIso_of_isIso_reduction`), and the local uniqueness of smooth lifts of III.4.1
(`exists_iso_of_smooth`).

The passage to the affine case is not immediate, since the preimage of an affine open under `u`
is not known to be affine; we first show that `u` is a homeomorphism, so that the
preimages of small enough basic opens of affine opens are basic opens of affine opens. On affine
opens, the sections of `X ×_Y Y₀` are `Γ(X, U) ⧸ J Γ(X, U)` (`surjective_appLE_and_ker_eq_map`,
from the pushout of rings `isPushout_appTop_of_isPullback`), and the ring case is
`bijective_iff_bijective_quotientMap`.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SGA.SGA1.ExposeIII

section Pushout

/-- In a pushout square of commutative rings `R → B`, `R → R₀`, `B → B₀`, `R₀ → B₀`, if `R → R₀`
is surjective with kernel `J`, then `B → B₀` is surjective with kernel `J B`. -/
lemma surjective_and_ker_eq_map_of_isPushout {R B R₀ B₀ : CommRingCat.{u}} {a : R ⟶ B}
    {ρ : R ⟶ R₀} {ρB : B ⟶ B₀} {b : R₀ ⟶ B₀} (h : IsPushout a ρ ρB b)
    (hρ : Function.Surjective ρ) :
    Function.Surjective ρB ∧ RingHom.ker ρB.hom = (RingHom.ker ρ.hom).map a.hom := by
  set K := (RingHom.ker ρ.hom).map a.hom
  let mkQ : B ⟶ CommRingCat.of (B ⧸ K) := CommRingCat.ofHom (Ideal.Quotient.mk K)
  let r₀ : R₀ ⟶ CommRingCat.of (B ⧸ K) := CommRingCat.ofHom
    ((Ideal.quotientMap (I := RingHom.ker ρ.hom) K a.hom Ideal.le_comap_map).comp
      (RingHom.quotientKerEquivOfSurjective hρ).symm.toRingHom)
  have hr₀ (r : R) : r₀ (ρ r) = Ideal.Quotient.mk K (a r) := by
    change Ideal.quotientMap (I := RingHom.ker ρ.hom) K a.hom Ideal.le_comap_map
      ((RingHom.quotientKerEquivOfSurjective hρ).symm (ρ.hom r)) = _
    rw [show (RingHom.quotientKerEquivOfSurjective hρ).symm (ρ.hom r) =
      Ideal.Quotient.mk _ r from (RingEquiv.symm_apply_eq _).mpr rfl]
    rfl
  have w : a ≫ mkQ = ρ ≫ r₀ := by
    ext r
    exact (hr₀ r).symm
  let d : B₀ ⟶ CommRingCat.of (B ⧸ K) := h.desc mkQ r₀ w
  have hK : K ≤ RingHom.ker ρB.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have := congr($(h.w) r)
    change ρB (a r) = b (ρ r) at this
    rw [this, RingHom.mem_ker.mp hr, map_zero]
  let q : CommRingCat.of (B ⧸ K) ⟶ B₀ := CommRingCat.ofHom (Ideal.Quotient.lift K ρB.hom hK)
  have hdq : d ≫ q = 𝟙 _ := by
    refine h.hom_ext ?_ ?_
    · rw [IsPushout.inl_desc_assoc, Category.comp_id]
      ext x
      rfl
    · rw [IsPushout.inr_desc_assoc, Category.comp_id]
      ext y
      obtain ⟨r, rfl⟩ := hρ y
      change q (r₀ (ρ r)) = b (ρ r)
      rw [hr₀]
      change ρB (a r) = b (ρ r)
      exact congr($(h.w) r)
  have hd (x : B) : d (ρB x) = Ideal.Quotient.mk K x := by
    change (ρB ≫ d) x = _
    rw [IsPushout.inl_desc]
    rfl
  refine ⟨fun y ↦ ?_, le_antisymm (fun x hx ↦ ?_) hK⟩
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (d y)
    refine ⟨x, ?_⟩
    have := congr($hdq y)
    change q (d y) = y at this
    rw [← this, ← hx]
    rfl
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← hd, RingHom.mem_ker.mp hx, map_zero]

variable {X Y X₀ Y₀ : Scheme.{u}} {f : X ⟶ Y} {i : Y₀ ⟶ Y} {iX : X₀ ⟶ X} {fX : X₀ ⟶ Y₀}

/-- Sections of a base change along a closed immersion over affine opens: if `X₀ = X ×_Y Y₀`, `Y₀`
closed in `Y`, `W ⊆ Y` and `U ⊆ f⁻¹ W` affine, then `Γ(X, U) → Γ(X₀, U₀)` is surjective with kernel
`J Γ(X, U)`, where `J` is the kernel of `Γ(Y, W) → Γ(Y₀, W₀)`. -/
lemma surjective_appLE_and_ker_eq_map (hX : IsPullback iX fX f i) [IsClosedImmersion i]
    {W : Y.Opens} (hW : IsAffineOpen W) {U : X.Opens} (hU : IsAffineOpen U) (hUW : U ≤ f ⁻¹ᵁ W) :
    Function.Surjective (iX.appLE U (iX ⁻¹ᵁ U) le_rfl) ∧
      RingHom.ker (iX.appLE U (iX ⁻¹ᵁ U) le_rfl).hom =
        (RingHom.ker (i.appLE W (i ⁻¹ᵁ W) le_rfl).hom).map (f.appLE W U hUW).hom := by
  have : IsClosedImmersion iX := MorphismProperty.of_isPullback hX.flip ‹_›
  have hle : iX ⁻¹ᵁ U ≤ fX ⁻¹ᵁ (i ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← hX.w, Scheme.Hom.comp_preimage]
    exact Scheme.Hom.preimage_mono _ hUW
  have hsq := Scheme.Hom.isPullback_resLE hX (US := W) (UT := i ⁻¹ᵁ W) (UX := U)
    (UY := iX ⁻¹ᵁ U) le_rfl hUW (inf_eq_left.mpr hle).symm
  have : IsAffine W := hW
  have : IsAffine U := hU
  have : IsAffine (i ⁻¹ᵁ W) := hW.preimage i
  have hpo := isPushout_appTop_of_isPullback hsq
  have hpo' : IsPushout (f.appLE W U hUW) (i.appLE W (i ⁻¹ᵁ W) le_rfl)
      (iX.appLE U (iX ⁻¹ᵁ U) le_rfl) (fX.appLE (i ⁻¹ᵁ W) (iX ⁻¹ᵁ U) hle) :=
    hpo.of_iso W.topIso U.topIso (i ⁻¹ᵁ W).topIso (iX ⁻¹ᵁ U).topIso
      (by rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id])
      (by rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id])
      (by rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id])
      (by rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id])
  have hρ : Function.Surjective (i.appLE W (i ⁻¹ᵁ W) le_rfl) := by
    have := i.app_surjective W hW
    rwa [Scheme.Hom.app_eq_appLE] at this
  exact surjective_and_ker_eq_map_of_isPushout hpo' hρ

end Pushout

section Topology

/-- A surjective closed embedding is an open map. -/
lemma isOpenMap_of_isClosedEmbedding_of_surjective {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {g : α → β} (hg : Topology.IsClosedEmbedding g)
    (hs : Function.Surjective g) : IsOpenMap g := fun S hS ↦ by
  have : g '' S = (g '' Sᶜ)ᶜ := by
    rw [Set.image_compl_eq ⟨hg.injective, hs⟩, compl_compl]
  rw [this]
  exact (hg.isClosedMap _ hS.isClosed_compl).isOpen_compl

end Topology

set_option backward.isDefEq.respectTransparency false in
/-- Lemma III.4.2: let `Y` be a locally noetherian scheme, `Y₀ ⊆ Y` a closed subscheme with the same
underlying space (so defined by a locally nilpotent ideal), and `u : X ⟶ X'` a morphism of
`Y`-schemes with `X` flat over `Y`. If the reduction `u₀ : X ×_Y Y₀ ⟶ X' ×_Y Y₀` of `u` is an
isomorphism, so is `u`. Here `X₀ = X ×_Y Y₀` and `X'₀ = X' ×_Y Y₀` are given by cartesian squares
and `u₀` is any morphism compatible with `u`.

SGA states it for a locally nilpotent ideal on an arbitrary `Y`; we assume `Y` locally noetherian,
so that the ideal is nilpotent on affine opens. -/
theorem isIso_of_isPullback {X X' Y Y₀ X₀ X'₀ : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (f' : X' ⟶ Y) [Flat f] (i : Y₀ ⟶ Y) [IsClosedImmersion i]
    (hi : Function.Surjective i) {iX : X₀ ⟶ X} {fX : X₀ ⟶ Y₀} (hX : IsPullback iX fX f i)
    {iX' : X'₀ ⟶ X'} {fX' : X'₀ ⟶ Y₀} (hX' : IsPullback iX' fX' f' i)
    (u : X ⟶ X') (hu : u ≫ f' = f) (u₀ : X₀ ⟶ X'₀) [IsIso u₀] (hu₀ : u₀ ≫ iX' = iX ≫ u) :
    IsIso u := by
  have : IsClosedImmersion iX := MorphismProperty.of_isPullback hX.flip ‹_›
  have : IsClosedImmersion iX' := MorphismProperty.of_isPullback hX'.flip ‹_›
  have hiX : Function.Surjective iX :=
    (MorphismProperty.of_isPullback (P := @Surjective) hX.flip ⟨hi⟩).surj
  have hiX' : Function.Surjective iX' :=
    (MorphismProperty.of_isPullback (P := @Surjective) hX'.flip ⟨hi⟩).surj
  have hu₀x (z : X₀) : u (iX z) = iX' (u₀ z) := by
    rw [← Scheme.Hom.comp_apply, ← hu₀, Scheme.Hom.comp_apply]
  have hinv (z' : X'₀) : u₀ (inv u₀ z') = z' := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  have hinv' (z : X₀) : inv u₀ (u₀ z) = z := by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
  -- `u` is a homeomorphism
  have hsurj : Function.Surjective u := fun x' ↦ by
    obtain ⟨z', rfl⟩ := hiX' x'
    exact ⟨iX (inv u₀ z'), by rw [hu₀x, hinv]⟩
  have hinj : Function.Injective u := fun a b hab ↦ by
    obtain ⟨a, rfl⟩ := hiX a
    obtain ⟨b, rfl⟩ := hiX b
    rw [hu₀x, hu₀x] at hab
    have := iX'.isClosedEmbedding.injective hab
    rw [← hinv' a, ← hinv' b, this]
  have hopen : IsOpenMap u := fun O hO ↦ by
    have : u '' O = iX' '' (u₀ '' (iX ⁻¹' O)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨z, rfl⟩ := hiX x
        exact ⟨u₀ z, ⟨z, hx, rfl⟩, (hu₀x z).symm⟩
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨iX z, hz, hu₀x z⟩
    rw [this]
    exact isOpenMap_of_isClosedEmbedding_of_surjective iX'.isClosedEmbedding hiX' _
      (u₀.isOpenEmbedding.isOpenMap _ (hO.preimage iX.continuous))
  -- the question is local on `X'`
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme) fun x' ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj x'
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  have hxW' : u x ∈ f' ⁻¹ᵁ W := by
    change f' (u x) ∈ W
    rw [← Scheme.Hom.comp_apply, hu]
    exact hxW
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hV'W⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    hxW' (f' ⁻¹ᵁ W).2
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ f ⁻¹ᵁ W ⊓ u ⁻¹ᵁ V' from ⟨hxW, hxV'⟩) (f ⁻¹ᵁ W ⊓ u ⁻¹ᵁ V').2
  have hVW : V ≤ f ⁻¹ᵁ W := fun y hy ↦ (hVle hy).1
  have hVV' : V ≤ u ⁻¹ᵁ V' := fun y hy ↦ (hVle hy).2
  -- a basic open `U' = D(g)` of `V'` around `u x` inside `u(V)`
  obtain ⟨g, hgle, hxg⟩ := hV'.exists_basicOpen_le (V := ⟨u '' V, hopen _ V.2⟩)
    ⟨u x, ⟨x, hxV, rfl⟩⟩ hxV'
  set U' := X'.basicOpen g
  have hU' : IsAffineOpen U' := hV'.basicOpen g
  set U := u ⁻¹ᵁ U'
  have hUV : U ≤ V := fun y hy ↦ by
    obtain ⟨z, hz, hzy⟩ := hgle hy
    rwa [← hinj hzy]
  have hU : IsAffineOpen U := by
    have h1 : U = X.basicOpen (X.presheaf.map (homOfLE hVV').op (u.app V' g)) := by
      rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
      exact (inf_eq_right.mpr hUV).symm
    rw [h1]
    exact hV.basicOpen _
  refine ⟨U', hxg, ?_⟩
  have : IsAffine U' := hU'
  refine (HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)).mpr
    ⟨hU, ?_⟩
  have hres : u.resLE U' U le_rfl = u ∣_ U' := by simp [Scheme.Hom.resLE]
  rw [← hres, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  suffices IsIso (u.appLE U' U le_rfl) by infer_instance
  rw [ConcreteCategory.isIso_iff_bijective]
  -- the ring case
  have hUW : U ≤ f ⁻¹ᵁ W := hUV.trans hVW
  have hU'W : U' ≤ f' ⁻¹ᵁ W := (X'.basicOpen_le g).trans hV'W
  set W₀ := i ⁻¹ᵁ W
  set ρ := i.appLE W W₀ le_rfl
  have : IsNoetherianRing Γ(Y, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hJ : IsNilpotent (RingHom.ker ρ.hom) :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).mpr
      (ker_appLE_le_nilradical i hi hW.isCompact)
  obtain ⟨-, hkU⟩ := surjective_appLE_and_ker_eq_map hX hW hU hUW
  obtain ⟨hsU', hkU'⟩ := surjective_appLE_and_ker_eq_map hX' hW hU' hU'W
  -- the reduction `u₀` over `U'₀`
  set U₀ := iX ⁻¹ᵁ U
  set U'₀ := iX' ⁻¹ᵁ U'
  have hU₀ : U₀ = u₀ ⁻¹ᵁ U'₀ := by
    change iX ⁻¹ᵁ (u ⁻¹ᵁ U') = u₀ ⁻¹ᵁ (iX' ⁻¹ᵁ U')
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hu₀]
  set ψ := u₀.appLE U'₀ U₀ hU₀.le
  have hψ : Function.Bijective ψ := by
    rw [← ConcreteCategory.isIso_iff_bijective]
    have : homOfLE hU₀.le = eqToHom hU₀ := Subsingleton.elim _ _
    change IsIso (u₀.app U'₀ ≫ X₀.presheaf.map (homOfLE hU₀.le).op)
    rw [this]
    infer_instance
  have hcomm (b' : Γ(X', U')) :
      iX.appLE U U₀ le_rfl (u.appLE U' U le_rfl b') = ψ (iX'.appLE U' U'₀ le_rfl b') := by
    have h1 : u.appLE U' U le_rfl ≫ iX.appLE U U₀ le_rfl =
        iX'.appLE U' U'₀ le_rfl ≫ ψ := by
      simp only [ψ, Scheme.Hom.appLE_comp_appLE]
      congr 1
      exact hu₀.symm
    exact congr($h1 b')
  -- the ring case, III.4.2 for rings
  let : Algebra Γ(Y, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
  let : Algebra Γ(Y, W) Γ(X', U') := (f'.appLE W U' hU'W).hom.toAlgebra
  have : Module.Flat Γ(Y, W) Γ(X, U) :=
    HasRingHomProperty.appLE @Flat f inferInstance ⟨W, hW⟩ ⟨U, hU⟩ hUW
  let φ : Γ(X', U') →ₐ[Γ(Y, W)] Γ(X, U) :=
    { (u.appLE U' U le_rfl).hom with
      commutes' := fun r ↦ by
        have h1 : f'.appLE W U' hU'W ≫ u.appLE U' U le_rfl = f.appLE W U hUW := by
          simp only [Scheme.Hom.appLE_comp_appLE]
          congr 1
        exact congr($h1 r) }
  change Function.Bijective φ
  refine (bijective_iff_bijective_quotientMap hJ φ).mpr ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hy
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change b' ∈ (RingHom.ker ρ.hom).map (f'.appLE W U' hU'W).hom
    change φ b' ∈ (RingHom.ker ρ.hom).map (f.appLE W U hUW).hom at hy
    rw [← hkU'] at ⊢
    rw [← hkU, RingHom.mem_ker] at hy
    rw [RingHom.mem_ker]
    apply hψ.1
    rw [map_zero, ← hcomm]
    exact hy
  · intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := hψ.2 (iX.appLE U U₀ le_rfl b)
    obtain ⟨b', rfl⟩ := hsU' c
    refine ⟨Ideal.Quotient.mk _ b', ?_⟩
    rw [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
    change φ b' - b ∈ (RingHom.ker ρ.hom).map (f.appLE W U hUW).hom
    rw [← hkU, RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (hcomm b').trans hc

/-- Lemma III.4.2, both directions: under the hypotheses of `isIso_of_isPullback`, `u` is an
isomorphism if and only if its reduction `u₀` is one. -/
theorem isIso_iff_isIso_of_isPullback {X X' Y Y₀ X₀ X'₀ : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (f' : X' ⟶ Y) [Flat f] (i : Y₀ ⟶ Y) [IsClosedImmersion i]
    (hi : Function.Surjective i) {iX : X₀ ⟶ X} {fX : X₀ ⟶ Y₀} (hX : IsPullback iX fX f i)
    {iX' : X'₀ ⟶ X'} {fX' : X'₀ ⟶ Y₀} (hX' : IsPullback iX' fX' f' i)
    (u : X ⟶ X') (hu : u ≫ f' = f) (u₀ : X₀ ⟶ X'₀) (hu₀ : u₀ ≫ iX' = iX ≫ u) :
    IsIso u ↔ IsIso u₀ := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ isIso_of_isPullback f f' i hi hX hX' u hu u₀ hu₀⟩
  have hu₀f : u₀ ≫ fX' = fX := by
    rw [← cancel_mono i, Category.assoc, ← hX'.w, reassoc_of% hu₀, hu, hX.w]
  have hf' : inv u ≫ f = f' := by rw [← hu, IsIso.inv_hom_id_assoc]
  let v₀ : X'₀ ⟶ X₀ := hX.lift (iX' ≫ inv u) fX' (by rw [Category.assoc, hf', hX'.w])
  refine ⟨v₀, hX.hom_ext ?_ ?_, hX'.hom_ext ?_ ?_⟩
  · simp [v₀, reassoc_of% hu₀]
  · simp [v₀, hu₀f]
  · simp [v₀, hu₀]
  · simp [v₀, hu₀f]

set_option backward.isDefEq.respectTransparency false in
/-- Lemma III.4.2, the variant for closed immersions noted after it, which needs no flatness: under
the hypotheses of `isIso_of_isPullback` except flatness, if the reduction `u₀` of `u` is a closed
immersion, so is `u`. As for III.4.2, `u` is first seen to be a closed embedding; the question is
then local on `X'`, and on small enough affine opens it is `surjective_of_surjective_mod`. -/
theorem isClosedImmersion_of_isPullback {X X' Y Y₀ X₀ X'₀ : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (f' : X' ⟶ Y) (i : Y₀ ⟶ Y) [IsClosedImmersion i]
    (hi : Function.Surjective i) {iX : X₀ ⟶ X} {fX : X₀ ⟶ Y₀} (hX : IsPullback iX fX f i)
    {iX' : X'₀ ⟶ X'} {fX' : X'₀ ⟶ Y₀} (hX' : IsPullback iX' fX' f' i)
    (u : X ⟶ X') (hu : u ≫ f' = f) (u₀ : X₀ ⟶ X'₀) [IsClosedImmersion u₀]
    (hu₀ : u₀ ≫ iX' = iX ≫ u) :
    IsClosedImmersion u := by
  have : IsClosedImmersion iX := MorphismProperty.of_isPullback hX.flip ‹_›
  have : IsClosedImmersion iX' := MorphismProperty.of_isPullback hX'.flip ‹_›
  have hiX : Function.Surjective iX :=
    (MorphismProperty.of_isPullback (P := @Surjective) hX.flip ⟨hi⟩).surj
  have hu₀x (z : X₀) : u (iX z) = iX' (u₀ z) := by
    rw [← Scheme.Hom.comp_apply, ← hu₀, Scheme.Hom.comp_apply]
  -- `u` is a closed embedding
  let e := IsHomeomorph.homeomorph iX
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨iX.isClosedEmbedding.isEmbedding, hiX⟩)
  have hue : (u : X → X') = (iX' ∘ u₀) ∘ e.symm := by
    funext y
    have : iX (e.symm y) = y := e.apply_symm_apply y
    simp only [Function.comp_apply]
    rw [← hu₀x, this]
  have hemb : Topology.IsEmbedding u := by
    rw [hue]
    exact (iX'.isClosedEmbedding.isEmbedding.comp u₀.isClosedEmbedding.isEmbedding).comp
      e.symm.isEmbedding
  have hrange : IsClosed (Set.range u) := by
    rw [hue, Set.range_comp, e.symm.range_coe, Set.image_univ, Set.range_comp]
    exact iX'.isClosedEmbedding.isClosedMap _ u₀.isClosedEmbedding.isClosed_range
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsClosedImmersion)
    fun x' ↦ ?_
  by_cases hx' : x' ∈ Set.range u
  swap
  · obtain ⟨_, ⟨U', -, rfl⟩, hxU', hU'⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      hx' hrange.isOpen_compl
    refine ⟨U', hxU', ?_⟩
    have : IsEmpty (u ⁻¹ᵁ U').toScheme := ⟨fun ⟨y, hy⟩ ↦ hU' hy ⟨y, rfl⟩⟩
    infer_instance
  obtain ⟨x, rfl⟩ := hx'
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  have hxW' : u x ∈ f' ⁻¹ᵁ W := by
    change f' (u x) ∈ W
    rw [← Scheme.Hom.comp_apply, hu]
    exact hxW
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hV'W⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    hxW' (f' ⁻¹ᵁ W).2
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ f ⁻¹ᵁ W ⊓ u ⁻¹ᵁ V' from ⟨hxW, hxV'⟩) (f ⁻¹ᵁ W ⊓ u ⁻¹ᵁ V').2
  have hVW : V ≤ f ⁻¹ᵁ W := fun y hy ↦ (hVle hy).1
  have hVV' : V ≤ u ⁻¹ᵁ V' := fun y hy ↦ (hVle hy).2
  -- an open `O` of `X'` with `u⁻¹ O = V`, and a basic open `U' = D(g)` of `V'` inside it
  obtain ⟨O, hO, hOV⟩ := hemb.isInducing.isOpen_iff.mp V.2
  obtain ⟨g, hgle, hxg⟩ := hV'.exists_basicOpen_le (V := ⟨O, hO⟩)
    ⟨u x, (show x ∈ u ⁻¹' O by rw [hOV]; exact hxV)⟩ hxV'
  set U' := X'.basicOpen g
  have hU' : IsAffineOpen U' := hV'.basicOpen g
  set U := u ⁻¹ᵁ U'
  have hUV : U ≤ V := fun y hy ↦ by
    have : y ∈ u ⁻¹' O := hgle hy
    rwa [hOV] at this
  have hU : IsAffineOpen U := by
    have h1 : U = X.basicOpen (X.presheaf.map (homOfLE hVV').op (u.app V' g)) := by
      rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
      exact (inf_eq_right.mpr hUV).symm
    rw [h1]
    exact hV.basicOpen _
  refine ⟨U', hxg, ?_⟩
  have : IsAffine U' := hU'
  have : IsAffine U := hU
  refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
  have hres : u.resLE U' U le_rfl = u ∣_ U' := by simp [Scheme.Hom.resLE]
  rw [← hres, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  suffices Function.Surjective (u.appLE U' U le_rfl) by
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso U.topIso.inv).2.comp
      (this.comp (ConcreteCategory.bijective_of_isIso U'.topIso.hom).2)
  -- the ring case
  have hUW : U ≤ f ⁻¹ᵁ W := hUV.trans hVW
  have hU'W : U' ≤ f' ⁻¹ᵁ W := (X'.basicOpen_le g).trans hV'W
  set W₀ := i ⁻¹ᵁ W
  set ρ := i.appLE W W₀ le_rfl
  have : IsNoetherianRing Γ(Y, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hJ : IsNilpotent (RingHom.ker ρ.hom) :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).mpr
      (ker_appLE_le_nilradical i hi hW.isCompact)
  obtain ⟨-, hkU⟩ := surjective_appLE_and_ker_eq_map hX hW hU hUW
  obtain ⟨hsU', -⟩ := surjective_appLE_and_ker_eq_map hX' hW hU' hU'W
  set U₀ := iX ⁻¹ᵁ U
  set U'₀ := iX' ⁻¹ᵁ U'
  have hU₀ : U₀ = u₀ ⁻¹ᵁ U'₀ := by
    change iX ⁻¹ᵁ (u ⁻¹ᵁ U') = u₀ ⁻¹ᵁ (iX' ⁻¹ᵁ U')
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hu₀]
  set ψ := u₀.appLE U'₀ U₀ hU₀.le
  have hψ : Function.Surjective ψ := by
    have hU'₀ : IsAffineOpen U'₀ := hU'.preimage iX'
    have h1 := u₀.app_surjective U'₀ hU'₀
    have : homOfLE hU₀.le = eqToHom hU₀ := Subsingleton.elim _ _
    change Function.Surjective (u₀.app U'₀ ≫ X₀.presheaf.map (homOfLE hU₀.le).op)
    rw [this]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).2.comp h1
  have hcomm (b' : Γ(X', U')) :
      iX.appLE U U₀ le_rfl (u.appLE U' U le_rfl b') = ψ (iX'.appLE U' U'₀ le_rfl b') := by
    have h1 : u.appLE U' U le_rfl ≫ iX.appLE U U₀ le_rfl =
        iX'.appLE U' U'₀ le_rfl ≫ ψ := by
      simp only [ψ, Scheme.Hom.appLE_comp_appLE]
      congr 1
      exact hu₀.symm
    exact congr($h1 b')
  let : Algebra Γ(Y, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
  let : Algebra Γ(Y, W) Γ(X', U') := (f'.appLE W U' hU'W).hom.toAlgebra
  let φ : Γ(X', U') →ₐ[Γ(Y, W)] Γ(X, U) :=
    { (u.appLE U' U le_rfl).hom with
      commutes' := fun r ↦ by
        have h1 : f'.appLE W U' hU'W ≫ u.appLE U' U le_rfl = f.appLE W U hUW := by
          simp only [Scheme.Hom.appLE_comp_appLE]
          congr 1
        exact congr($h1 r) }
  change Function.Surjective φ
  refine surjective_of_surjective_mod hJ φ fun b ↦ ?_
  obtain ⟨c, hc⟩ := hψ (iX.appLE U U₀ le_rfl b)
  obtain ⟨b', rfl⟩ := hsU' c
  refine ⟨b', ?_⟩
  change φ b' - b ∈ (RingHom.ker ρ.hom).map (f.appLE W U hUW).hom
  rw [← hkU, RingHom.mem_ker, map_sub, sub_eq_zero]
  exact (hcomm b').trans hc

/-- The closed immersion `Spec (A ⧸ I) ⟶ Spec (A ⧸ Iⁿ⁺¹)` is surjective. -/
lemma surjective_SpecMap_factor {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) :
    Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_self n.succ_ne_zero : I ^ (n + 1) ≤ I)))) := by
  set φ := Ideal.Quotient.factor (Ideal.pow_le_self n.succ_ne_zero : I ^ (n + 1) ≤ I)
  have hφ : Function.Surjective φ := Ideal.Quotient.factor_surjective _
  have hker : RingHom.ker φ ≤ nilradical (A ⧸ I ^ (n + 1)) := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    refine ⟨n + 1, ?_⟩
    rw [← map_pow, Ideal.zero_eq_bot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hx _
  exact (PrimeSpectrum.isHomeomorph_comap φ (fun x ↦ ⟨1, one_pos, by simpa using hφ x⟩)
    hker).surjective

/-- Corollary III.5.7, one infinitesimal neighbourhood at a time (scheme form): let `A` be a
noetherian ring, `I` an ideal, `Sₙ = Spec (A ⧸ Iⁿ⁺¹)` and `S₀ = Spec (A ⧸ I)`. A morphism
`gₙ : Yₙ ⟶ Xₙ` of `Sₙ`-schemes with `Yₙ` flat over `Sₙ` is an isomorphism as soon as its reduction
`g₀ : Yₙ ×_{Sₙ} S₀ ⟶ Xₙ ×_{Sₙ} S₀` is one ("proceeding as in III.4.2"). Hence, under the
hypotheses of III.5.6, if `g₀` is an isomorphism then so are all `gₙ`, i.e. `ĝ` is. -/
theorem isIso_of_isIso_reduction {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (n : ℕ) {Xn Yn X₀ Y₀ : Scheme.{u}} (fX : Xn ⟶ Spec (.of (A ⧸ I ^ (n + 1))))
    (fY : Yn ⟶ Spec (.of (A ⧸ I ^ (n + 1)))) [Flat fY]
    {iX : X₀ ⟶ Xn} {pX : X₀ ⟶ Spec (.of (A ⧸ I))}
    (hX : IsPullback iX pX fX (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_self n.succ_ne_zero : I ^ (n + 1) ≤ I)))))
    {iY : Y₀ ⟶ Yn} {pY : Y₀ ⟶ Spec (.of (A ⧸ I))}
    (hY : IsPullback iY pY fY (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_self n.succ_ne_zero : I ^ (n + 1) ≤ I)))))
    (g : Yn ⟶ Xn) (hg : g ≫ fX = fY) (g₀ : Y₀ ⟶ X₀) [IsIso g₀] (hg₀ : g₀ ≫ iX = iY ≫ g) :
    IsIso g := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_self n.succ_ne_zero : I ^ (n + 1) ≤ I)))) :=
    .spec_of_surjective _ (Ideal.Quotient.factor_surjective (Ideal.pow_le_self n.succ_ne_zero))
  exact isIso_of_isPullback fY fX (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (Ideal.pow_le_self n.succ_ne_zero : I ^ (n + 1) ≤ I)))) (surjective_SpecMap_factor I n)
    hY hX g hg g₀ hg₀

set_option backward.isDefEq.respectTransparency false in
/-- III.4.1, uniqueness: two smooth `Y`-schemes `X₁`, `X₂` lifting the same `Y₀`-scheme (i.e. with
an isomorphism `e₀ : X₁ ×_Y Y₀ ≅ X₂ ×_Y Y₀` over `Y₀`) are isomorphic over `Y` in a neighbourhood
of every point, by an isomorphism compatible with `e₀`. As in SGA: `e₀` extends locally to a
`Y`-morphism by the infinitesimal lifting property of smooth morphisms (III.3.1,
`exists_extension_of_smooth`), which is an isomorphism onto its image by III.4.2
(`isIso_of_isPullback`). Here `Y` is locally noetherian and `Y₀ ⊆ Y` has the same underlying space,
as in III.4.1; the isomorphism is not unique (Remark III.4.3). -/
theorem exists_iso_of_smooth {Y Y₀ X₁ X₂ Z₁ Z₂ : Scheme.{u}} [IsLocallyNoetherian Y]
    (j : Y₀ ⟶ Y) [IsClosedImmersion j] (hj : Function.Surjective j)
    (f₁ : X₁ ⟶ Y) [Smooth f₁] (f₂ : X₂ ⟶ Y) [Smooth f₂]
    {k₁ : Z₁ ⟶ X₁} {p₁ : Z₁ ⟶ Y₀} (h₁ : IsPullback k₁ p₁ f₁ j)
    {k₂ : Z₂ ⟶ X₂} {p₂ : Z₂ ⟶ Y₀} (h₂ : IsPullback k₂ p₂ f₂ j)
    (e₀ : Z₁ ≅ Z₂) (he₀ : e₀.hom ≫ p₂ = p₁) (z : Z₁) :
    ∃ (V₁ : X₁.Opens) (V₂ : X₂.Opens) (_ : k₁ z ∈ V₁) (φ : V₁.toScheme ≅ V₂.toScheme),
      φ.hom ≫ V₂.ι ≫ f₂ = V₁.ι ≫ f₁ ∧
        (k₁ ∣_ V₁) ≫ φ.hom ≫ V₂.ι = (k₁ ⁻¹ᵁ V₁).ι ≫ e₀.hom ≫ k₂ := by
  have : IsClosedImmersion k₁ := MorphismProperty.of_isPullback h₁.flip ‹_›
  have : IsClosedImmersion k₂ := MorphismProperty.of_isPullback h₂.flip ‹_›
  have hk₁ : Function.Surjective k₁ :=
    (MorphismProperty.of_isPullback (P := @Surjective) h₁.flip ⟨hj⟩).surj
  have hk₂ : Function.Surjective k₂ :=
    (MorphismProperty.of_isPullback (P := @Surjective) h₂.flip ⟨hj⟩).surj
  obtain ⟨U, hzU, g, hgf, hgk⟩ := exists_extension_of_smooth f₂ f₁ k₁ hk₁ (e₀.hom ≫ k₂)
    (by rw [Category.assoc, h₂.w, reassoc_of% he₀, h₁.w]) z
  -- the image of `g` is open
  have hg (a : (k₁ ⁻¹ᵁ U).toScheme) : g ((k₁ ∣_ U) a) = k₂ (e₀.hom a.1) := by
    rw [← Scheme.Hom.comp_apply, hgk]
    rfl
  have hrange : Set.range g = k₂ '' (e₀.hom '' (k₁ ⁻¹' U)) := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨a, ha⟩ := hk₁ w.1
      have haU : a ∈ k₁ ⁻¹ᵁ U := by
        change k₁ a ∈ U
        rw [ha]; exact w.2
      have : (k₁ ∣_ U) ⟨a, haU⟩ = w := Subtype.ext (by
        rw [morphismRestrict_base_coe]; exact ha)
      rw [← this, hg]
      exact ⟨e₀.hom a, ⟨a, haU, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨(k₁ ∣_ U) ⟨a, ha⟩, hg ⟨a, ha⟩⟩
  have hopen : IsOpen (Set.range g) := by
    rw [hrange]
    exact isOpenMap_of_isClosedEmbedding_of_surjective k₂.isClosedEmbedding hk₂ _
      (e₀.hom.isOpenEmbedding.isOpenMap _ (U.2.preimage k₁.continuous))
  set V₂ : X₂.Opens := ⟨Set.range g, hopen⟩
  let g' : U.toScheme ⟶ V₂.toScheme :=
    IsOpenImmersion.lift V₂.ι g (by rw [Scheme.Opens.range_ι]; exact le_rfl)
  have hg' : g' ≫ V₂.ι = g := IsOpenImmersion.lift_fac _ _ _
  -- the pullback squares over `U` and `V₂`
  have hX := (isPullback_morphismRestrict k₁ U).paste_vert h₁
  have hX' := (isPullback_morphismRestrict k₂ V₂).paste_vert h₂
  have heq : k₁ ⁻¹ᵁ U = e₀.hom ⁻¹ᵁ (k₂ ⁻¹ᵁ V₂) := by
    ext a
    constructor
    · intro ha
      exact ⟨(k₁ ∣_ U) ⟨a, ha⟩, hg ⟨a, ha⟩⟩
    · rintro ⟨w, hw⟩
      obtain ⟨b, hb⟩ := hk₁ w.1
      have hbU : b ∈ k₁ ⁻¹ᵁ U := by
        change k₁ b ∈ U
        rw [hb]; exact w.2
      have : (k₁ ∣_ U) ⟨b, hbU⟩ = w := Subtype.ext (by
        rw [morphismRestrict_base_coe]; exact hb)
      rw [← this, hg] at hw
      have := e₀.hom.isOpenEmbedding.injective (k₂.isClosedEmbedding.injective hw)
      rw [← this]
      exact hbU
  let u₀ : (k₁ ⁻¹ᵁ U).toScheme ⟶ (k₂ ⁻¹ᵁ V₂).toScheme :=
    (Z₁.isoOfEq heq).hom ≫ (e₀.hom ∣_ (k₂ ⁻¹ᵁ V₂))
  have hu₀ : u₀ ≫ (k₂ ∣_ V₂) = (k₁ ∣_ U) ≫ g' := by
    rw [← cancel_mono V₂.ι]
    simp only [Category.assoc, hg', hgk, u₀, morphismRestrict_ι, morphismRestrict_ι_assoc,
      Scheme.isoOfEq_hom_ι_assoc]
  have hu : g' ≫ V₂.ι ≫ f₂ = U.ι ≫ f₁ := by rw [reassoc_of% hg', hgf]
  have : IsIso g' := isIso_of_isPullback (U.ι ≫ f₁) (V₂.ι ≫ f₂) j hj hX hX' g' hu u₀ hu₀
  refine ⟨U, V₂, hzU, asIso g', hu, ?_⟩
  rw [asIso_hom, hg', hgk]

end SGA.SGA1.ExposeIII
