/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import SGA.Foundations.Limits.PropertiesLimitEtale
import SGA.Foundations.Limits.PropertiesLimitProper

/-!
# Affine, finite, monomorphisms and open immersions over a limit descend to a finite level

EGA IV 8.10.5 for further properties: let `c.pt = lim E i` be the limit of a cofiltered diagram of
quasi-compact and quasi-separated schemes with affine transition maps, `X_j ⟶ E j` of finite
presentation and `X ⟶ c.pt` its base change. If `X ⟶ c.pt` is

* affine: `AlgebraicGeometry.Scheme.limitDescends_isAffineHom` (8.10.5 (viii)); over affine
  members, `X` is the limit of the `X_j ×_{E j} E k` and some of them is affine (Stacks 01Z6,
  mathlib's `Scheme.exists_isAffine_of_isLimit`);
* finite: `AlgebraicGeometry.Scheme.limitDescends_isFinite` (8.10.5 (x)): finite is proper and
  affine;
* a monomorphism: `AlgebraicGeometry.Scheme.limitDescends_mono` (the diagonal is an isomorphism
  and isomorphisms descend);
* an open immersion: `AlgebraicGeometry.Scheme.limitDescends_isOpenImmersion` (8.10.5 (ii)): an
  étale monomorphism is an open immersion (mathlib's `IsOpenImmersion.of_flat_of_mono`),

then so is `X_j ×_{E j} E k ⟶ E k` for some `k`.

## References

* [EGA IV₃, 8.10.5][EGA4]
* [Stacks Project, Limits of schemes, Section 32.8][stacks]
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5 (viii): affineness of a morphism of finite presentation descends along limits
of cofiltered diagrams of quasi-compact and quasi-separated schemes with affine transition maps. -/
theorem Scheme.limitDescends_isAffineHom : Scheme.LimitDescendsStatement.{u} @IsAffineHom := by
  refine Scheme.limitDescends_of_affine ?_
  intro I _ _ E _ _ c hc j X Xj qj _ _ _ e q h hq
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : IsAffineHom q := hq
  have : IsAffine X := isAffine_of_isAffineHom q
  have (k : Over j) : CompactSpace ((Scheme.baseChangeDiagram E qj).obj k) :=
    Scheme.compactSpace_baseChangeDiagram qj k
  have (k : Over j) : QuasiSeparatedSpace ((Scheme.baseChangeDiagram E qj).obj k) :=
    Scheme.quasiSeparatedSpace_baseChangeDiagram qj k
  have : IsAffine (Scheme.baseChangeCone h).pt := ‹IsAffine X›
  obtain ⟨k, hk⟩ := Scheme.exists_isAffine_of_isLimit (Scheme.baseChangeDiagram E qj)
    (Scheme.baseChangeCone h) (Scheme.isLimitBaseChangeCone hc h)
  have : IsAffine (pullback qj (E.map k.hom)) := hk
  exact ⟨k.left, k.hom, isAffineHom_of_isAffine _⟩

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5 (x): finiteness of a morphism of finite presentation descends along limits of
cofiltered diagrams of quasi-compact and quasi-separated schemes with affine transition maps
(finite = proper and affine). -/
theorem Scheme.limitDescends_isFinite : Scheme.LimitDescendsStatement.{u} @IsFinite := by
  intro I _ _ E _ _ _ c hc j X Xj qj _ _ _ e q h hq
  have : IsFinite q := hq
  obtain ⟨k₁, g₁, h₁⟩ := Scheme.limitDescends_isAffineHom E c hc qj e q h inferInstance
  let M₀ : Scheme.LimitModel c q j := { obj := Xj, hom := qj, proj := e, isPullback := h }
  let M₁ := M₀.lower g₁
  obtain ⟨k₂, g₂, h₂⟩ := Scheme.properLimitStatement E c hc M₁.hom M₁.proj q M₁.isPullback
    inferInstance
  refine ⟨k₂, g₂ ≫ g₁, ?_⟩
  have hA : IsAffineHom (pullback.snd M₁.hom (E.map g₂)) :=
    MorphismProperty.pullback_snd _ _ h₁
  have hF : IsFinite (pullback.snd M₁.hom (E.map g₂)) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨h₂, hA⟩
  have := (MorphismProperty.arrow_mk_iso_iff @IsFinite
    (Scheme.pullbackSndCompArrowIso qj (E.map g₂) (E.map g₁))).mpr hF
  exact Scheme.of_pullback_snd_eq (E.map_comp g₂ g₁).symm this

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5 for monomorphisms: a morphism of finite presentation whose base change to the
limit is a monomorphism becomes a monomorphism at a finite level (its diagonal is an isomorphism,
and isomorphisms descend). -/
theorem Scheme.limitDescends_mono :
    Scheme.LimitDescendsStatement.{u} (MorphismProperty.monomorphisms Scheme.{u}) := by
  intro I _ _ E _ _ _ c hc j X Xj qj _ _ _ e q h hq
  have : Mono q := hq
  have hZ := IsPullback.pullback_map_fst h h
  have hY := h.diagonal
  obtain ⟨k, hk⟩ := Scheme.limitDescends_relative Scheme.limitDescends_isIso hc
    (pullback.fst qj qj ≫ qj) (pullback.diagonal qj) hZ hY
    (inferInstance : IsIso (pullback.diagonal q))
  refine ⟨k.left, k.hom, ?_⟩
  -- the diagonal at level `k` is a base change of `Δ_{X_j/E j}`
  have hk' := IsPullback.of_hasPullback qj (E.map k.hom)
  have hW := IsPullback.pullback_map_fst hk' hk'
  have hD := hk'.diagonal
  have h1 := Scheme.pullback_snd_comp_of_isStableUnderBaseChange (pullback.diagonal qj)
    hW.isoPullback.hom (pullback.fst (pullback.fst qj qj ≫ qj) (E.map k.hom)) hk
  rw [IsPullback.isoPullback_hom_fst] at h1
  have h2 : IsIso (pullback.diagonal (pullback.snd qj (E.map k.hom))) :=
    (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme.{u})
      (Arrow.isoMk (hD.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)) (Iso.refl _)
        (by simp))).mpr h1
  exact (pullback.isIso_diagonal_iff _).mp h2

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5 (ii): a morphism of finite presentation whose base change to the limit is an
open immersion becomes an open immersion at a finite level (it is étale and a monomorphism at a
finite level, EGA IV 17.7.8, and an étale monomorphism is an open immersion). -/
theorem Scheme.limitDescends_isOpenImmersion :
    Scheme.LimitDescendsStatement.{u} @IsOpenImmersion := by
  intro I _ _ E _ _ _ c hc j X Xj qj _ _ _ e q h hq
  have : IsOpenImmersion q := hq
  obtain ⟨k₁, g₁, h₁⟩ := Scheme.limitDescends_etale E c hc qj e q h inferInstance
  let M₀ : Scheme.LimitModel c q j := { obj := Xj, hom := qj, proj := e, isPullback := h }
  let M₁ := M₀.lower g₁
  obtain ⟨k₂, g₂, h₂⟩ := Scheme.limitDescends_mono E c hc M₁.hom M₁.proj q M₁.isPullback
    (inferInstance : Mono q)
  refine ⟨k₂, g₂ ≫ g₁, ?_⟩
  have : Etale (pullback.snd M₁.hom (E.map g₂)) := MorphismProperty.pullback_snd _ _ h₁
  have : Mono (pullback.snd M₁.hom (E.map g₂)) := h₂
  have hO : IsOpenImmersion (pullback.snd M₁.hom (E.map g₂)) := IsOpenImmersion.of_flat_of_mono _
  have := (MorphismProperty.arrow_mk_iso_iff @IsOpenImmersion
    (Scheme.pullbackSndCompArrowIso qj (E.map g₂) (E.map g₁))).mpr hO
  exact Scheme.of_pullback_snd_eq (E.map_comp g₂ g₁).symm this

end AlgebraicGeometry
