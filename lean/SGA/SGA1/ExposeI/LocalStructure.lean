/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import SGA.SGA1.ExposeI.StandardEtale
import SGA.SGA1.ExposeI.Unramified

/-!
# SGA 1, Exposé I, I.7.8: local structure of unramified morphisms

Corollary I.7.8: a morphism `f : X ⟶ Y` of finite type is unramified at `x` iff, on an open
neighbourhood `U` of `x`, `f` factors as a closed immersion `U ⟶ X'` followed by an étale
morphism `X' ⟶ Y`. In affine charts `Spec B ⊆ X` over `Spec A ⊆ Y`, mathlib's local structure
theorem (I.7.6–I.7.7, Zariski-local form) gives `g ∉ q` and a standard étale `A`-algebra
`P = (A[t]/(F))[1/h]` with a surjection `P → B[1/g]`; take `U = Spec B[1/g]` and
`X' = Spec P`.
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry CategoryTheory

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-- I.7.8: let `f : X ⟶ Y` be locally of finite type and `x ∈ X`. Then `f` is unramified at `x`
iff there is an open neighbourhood `U` of `x` such that `U ⟶ Y` factors as a closed immersion
`U ⟶ X'` followed by an étale morphism `X' ⟶ Y`. -/
theorem formallyUnramified_stalkMap_iff_exists_isClosedImmersion_etale (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) :
    (f.stalkMap x).hom.FormallyUnramified ↔
      ∃ (U : X.Opens) (_ : x ∈ U) (X' : Scheme.{u}) (i : U.toScheme ⟶ X') (e : X' ⟶ Y),
        IsClosedImmersion i ∧ Etale e ∧ i ≫ e = U.ι ≫ f := by
  constructor
  · intro hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'V⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxV (V.2.preimage f.continuous)
    have := f.finiteType_appLE hV hU' hU'V
    algebraize [(f.appLE V U' hU'V).hom]
    set q := hU'.primeIdealOf ⟨x, hxU'⟩
    have hq : Algebra.IsUnramifiedAt Γ(Y, V) q.asIdeal :=
      (formallyUnramified_stalkMap_iff f V hV U' hU' hU'V hxU').mp hx
    obtain ⟨g, hgq, P, φ, hφ⟩ := exists_standardEtale_surjection (A := Γ(Y, V)) q.asIdeal
    -- the open subscheme `Spec B[1/g]` of `X`
    let j : Spec (.of (Localization.Away g)) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U') (Localization.Away g))) ≫ hU'.fromSpec
    have hxj : x ∈ j.opensRange := by
      have hqr : q ∈ Set.range (PrimeSpectrum.comap
          (algebraMap Γ(X, U') (Localization.Away g))) := by
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
        exact hgq
      obtain ⟨Q, hQ⟩ := hqr
      refine ⟨Q, ?_⟩
      simp only [j, Scheme.Hom.comp_apply]
      exact (congrArg hU'.fromSpec hQ).trans (hU'.fromSpec_primeIdealOf ⟨x, hxU'⟩)
    refine ⟨j.opensRange, hxj, Spec (.of P.Ring),
      j.isoOpensRange.inv ≫ Spec.map (CommRingCat.ofHom φ.toRingHom),
      Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V) P.Ring)) ≫ hV.fromSpec, ?_, ?_, ?_⟩
    · have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ.toRingHom) hφ
      infer_instance
    · have hP : Algebra.Etale Γ(Y, V) P.Ring := inferInstance
      have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, V) P.Ring))) :=
        HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hP)
      infer_instance
    · have hcomp : CommRingCat.ofHom (algebraMap Γ(Y, V) P.Ring) ≫
          CommRingCat.ofHom φ.toRingHom =
          f.appLE V U' hU'V ≫ CommRingCat.ofHom (algebraMap Γ(X, U') (Localization.Away g)) := by
        ext a
        change φ (algebraMap _ _ a) = algebraMap Γ(X, U') (Localization.Away g) (algebraMap _ _ a)
        rw [φ.commutes, ← IsScalarTower.algebraMap_apply]
      rw [← j.isoOpensRange_inv_comp, Category.assoc, Category.assoc, ← Spec.map_comp_assoc,
        hcomp, Spec.map_comp_assoc, IsAffineOpen.SpecMap_appLE_fromSpec f hV hU' hU'V]
      simp only [j, Category.assoc]
  · rintro ⟨U, hxU, X', i, e, _, _, h⟩
    have : FormallyUnramified (U.ι ≫ f) := h ▸ inferInstance
    have key (y : U.toScheme) (hy : ((U.ι ≫ f).stalkMap y).hom.FormallyUnramified) :
        (f.stalkMap (U.ι y)).hom.FormallyUnramified := by
      rw [Scheme.Hom.stalkMap_comp] at hy
      exact (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso _ _).mp hy
    exact key ⟨x, hxU⟩ (FormallyUnramified.stalkMap _ _)

end SGA.SGA1.ExposeI
