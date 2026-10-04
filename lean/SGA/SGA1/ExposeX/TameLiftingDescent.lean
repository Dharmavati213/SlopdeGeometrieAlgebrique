/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Limits.FiniteEtale
import SGA.SGA1.ExposeV.GaloisAxioms
import SGA.SGA1.ExposeX.EtaleCoverings
import SGA.SGA1.ExposeX.GaloisFunctors

/-!
# SGA 1, Exposé X, 3.8: descending a Galois covering together with its automorphisms

In the proof of X.3.8 a principal covering `Z` of the geometric generic fibre `X_{K̄}`, with group
`G`, is written as the inverse image of a principal covering of `X_{K'}` with the same group, for
a finite extension `K'` of `K` ("there exists a finite subextension `K'` of `K̄` and a principal
covering `Z_{K'}` of `X_{K'}` with group `G` inducing `Z`"). The covering descends by the limit
theorem for étale coverings (EGA IV 8.8.2, 17.7.8); for the group action to descend as well, the
automorphisms of `Z` have to descend, at a common level. This file provides the bookkeeping.

* `LiftsEndos H Y`: every endomorphism of `H Y` is `H` of an endomorphism of `Y`; it is stable
  under isomorphisms of objects and of functors and under composition, and holds for full `H`.
* `isConnected_of_isConnected_obj`, `isGalois_of_liftsEndos`, `natCard_aut_eq_of_isGalois`: for
  a functor of Galois categories compatible with fibre functors, `Y` is Galois as soon as `H Y` is
  Galois and `LiftsEndos H Y`, and then `Aut Y` and `Aut (H Y)` have the same cardinality.
* `exists_liftsEndos_of_isLimit`: if `c.pt = lim Eᵢ` (cofiltered, affine transition maps,
  quasi-compact and quasi-separated `Eᵢ`), every étale covering `Y` of `c.pt` with finitely many
  endomorphisms is the inverse image of an étale covering `Yⱼ` of some `Eⱼ` with
  `LiftsEndos (c.π.app j)^* Yⱼ`
  (`AlgebraicGeometry.Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale` for the object,
  `AlgebraicGeometry.Scheme.exists_hom_of_isPullback` for each endomorphism, and a common lower
  bound of the finitely many levels).
-/

universe w u

open CategoryTheory Limits PreGaloisCategory AlgebraicGeometry

namespace SGA.SGA1.ExposeX

section Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]

/-- Every endomorphism of `H.obj Y` is the image under `H` of an endomorphism of `Y`. -/
def LiftsEndos (H : C ⥤ D) (Y : C) : Prop :=
  ∀ τ : H.obj Y ⟶ H.obj Y, ∃ ψ : Y ⟶ Y, H.map ψ = τ

theorem LiftsEndos.of_full (H : C ⥤ D) [H.Full] (Y : C) : LiftsEndos H Y :=
  fun τ ↦ ⟨H.preimage τ, H.map_preimage τ⟩

theorem LiftsEndos.of_iso {H : C ⥤ D} {Y Y' : C} (h : LiftsEndos H Y) (i : Y ≅ Y') :
    LiftsEndos H Y' := by
  intro τ
  obtain ⟨ψ, hψ⟩ := h (H.map i.hom ≫ τ ≫ H.map i.inv)
  refine ⟨i.inv ≫ ψ ≫ i.hom, ?_⟩
  rw [Functor.map_comp, Functor.map_comp, hψ]
  simp only [Category.assoc, ← H.map_comp_assoc, Iso.inv_hom_id, H.map_id, Category.id_comp]
  rw [← H.map_comp, i.inv_hom_id, H.map_id, Category.comp_id]

theorem LiftsEndos.of_natIso {H H' : C ⥤ D} {Y : C} (h : LiftsEndos H Y) (ρ : H ≅ H') :
    LiftsEndos H' Y := by
  intro τ
  obtain ⟨ψ, hψ⟩ := h (ρ.hom.app Y ≫ τ ≫ ρ.inv.app Y)
  refine ⟨ψ, ?_⟩
  calc H'.map ψ = ρ.inv.app Y ≫ H.map ψ ≫ ρ.hom.app Y := by
        rw [ρ.hom.naturality ψ, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    _ = τ := by rw [hψ]; simp

theorem LiftsEndos.comp {H₁ : C ⥤ D} {H₂ : D ⥤ E} {Y : C} (h₁ : LiftsEndos H₁ Y)
    (h₂ : LiftsEndos H₂ (H₁.obj Y)) : LiftsEndos (H₁ ⋙ H₂) Y := by
  intro τ
  obtain ⟨ψ₁, hψ₁⟩ := h₂ τ
  obtain ⟨ψ, hψ⟩ := h₁ ψ₁
  exact ⟨ψ, by rw [Functor.comp_map, hψ, hψ₁]⟩

theorem LiftsEndos.of_comp {H₁ : C ⥤ D} {H₂ : D ⥤ E} {Y : C} (h : LiftsEndos (H₁ ⋙ H₂) Y) :
    LiftsEndos H₂ (H₁.obj Y) := by
  intro τ
  obtain ⟨ψ, hψ⟩ := h τ
  exact ⟨H₁.map ψ, hψ⟩

end Functor

section GaloisCategory

variable {C D : Type*} [Category C] [Category D] [GaloisCategory C] [GaloisCategory D]
  {F : C ⥤ FintypeCat.{w}} [FiberFunctor F] {F' : D ⥤ FintypeCat.{w}} [FiberFunctor F']
  (H : C ⥤ D) (e : H ⋙ F' ≅ F)

include e in
/-- A functor of Galois categories compatible with fibre functors reflects connectedness. -/
theorem isConnected_of_isConnected_obj (Y : C) [IsConnected (H.obj Y)] : IsConnected Y := by
  obtain ⟨y⟩ := nonempty_fiber_of_isConnected F' (H.obj Y)
  have : Nonempty (F.obj Y) := ⟨e.hom.app Y y⟩
  have : MulAction.IsPretransitive (Aut F) (F.obj Y) := by
    refine ⟨fun x x' ↦ ?_⟩
    let y₁ : F'.obj (H.obj Y) := e.inv.app Y x
    let y₂ : F'.obj (H.obj Y) := e.inv.app Y x'
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F') y₁ y₂
    refine ⟨autWhiskerLeft H e σ, ?_⟩
    rw [autWhiskerLeft_smul]
    change e.hom.app Y (σ • y₁) = x'
    rw [hσ]
    exact FintypeCat.inv_hom_id_apply (e.app Y) x'
  exact isConnected_of_isPretransitive F Y

include e in
/-- A criterion for being Galois: for a functor `H` of Galois categories compatible with fibre
functors, `Y` is Galois if `H Y` is Galois and every endomorphism of `H Y` comes from an
endomorphism of `Y`. -/
theorem isGalois_of_liftsEndos (Y : C) [IsGalois (H.obj Y)] (h : LiftsEndos H Y) :
    IsGalois Y := by
  have := isConnected_of_isConnected_obj H e Y
  rw [isGalois_iff_pretransitive F]
  refine ⟨fun x x' ↦ ?_⟩
  let y₁ : F'.obj (H.obj Y) := e.inv.app Y x
  let y₂ : F'.obj (H.obj Y) := e.inv.app Y x'
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut (H.obj Y)) y₁ y₂
  obtain ⟨ψ, hψ⟩ := h σ.hom
  have := ExposeV.isIso_of_isConnected F ψ
  refine ⟨asIso ψ, ?_⟩
  change F.map ψ x = x'
  have hnat := congrArg (fun φ ↦ φ (e.inv.app Y x)) (e.hom.naturality ψ)
  simp only [Functor.comp_map, FintypeCat.comp_apply, hψ] at hnat
  change F'.map σ.hom (e.inv.app Y x) = e.inv.app Y x' at hσ
  have hx (z : F.obj Y) : e.hom.app Y (e.inv.app Y z) = z := by
    rw [← FintypeCat.comp_apply, Iso.inv_hom_id_app, FintypeCat.id_apply]
  rw [hσ, hx] at hnat
  rw [hnat, hx]

include e in
/-- If `Y` and `H Y` are Galois, they have the same number of automorphisms (both are the
cardinality of the fibre). -/
theorem natCard_aut_eq_of_isGalois (Y : C) [IsGalois Y] [IsGalois (H.obj Y)] :
    Nat.card (Aut Y) = Nat.card (Aut (H.obj Y)) := by
  obtain ⟨y⟩ := nonempty_fiber_of_isConnected F Y
  rw [Nat.card_congr (evaluationEquivOfIsGalois F Y y),
    Nat.card_congr (evaluationEquivOfIsGalois F' (H.obj Y) (e.inv.app Y y))]
  exact Nat.card_congr (FintypeCat.equivEquivIso.symm (e.app Y)).symm

end GaloisCategory

section Limit

variable {I : Type u} [Category.{u} I] {E : I ⥤ Scheme.{u}} {c : Cone E} [IsCofiltered I]
  [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, CompactSpace (E.obj i)]
  [∀ i, QuasiSeparatedSpace (E.obj i)]

set_option backward.isDefEq.respectTransparency false in
/-- The limit theorem for étale coverings with their endomorphisms: let `c.pt = lim Eᵢ` be the
limit of a cofiltered diagram of quasi-compact and quasi-separated schemes with affine transition
maps, and `Y` an étale covering of `c.pt` with finitely many endomorphisms. Then `Y` is the
inverse image of an étale covering `Yⱼ` of some `Eⱼ` such that every endomorphism of `Y` comes from
an endomorphism of `Yⱼ` (EGA IV 8.8.2, 17.7.8). -/
theorem exists_liftsEndos_of_isLimit (hc : IsLimit c) (Y : FEt c.pt) [Finite (Y ⟶ Y)] :
    ∃ (j : I) (Yj : FEt (E.obj j)), Nonempty ((FEt.pullback (c.π.app j)).obj Yj ≅ Y) ∧
      LiftsEndos (FEt.pullback (c.π.app j)) Yj := by
  classical
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  obtain ⟨j, Yj, qj, e, hfin, het, hY⟩ :=
    Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale hc Y.hom
  -- each endomorphism descends to some level
  have hτ (τ : Y ⟶ Y) : ∃ (k : Over j) (b : pullback qj (E.map k.hom) ⟶ Yj),
      b ≫ qj = pullback.snd qj (E.map k.hom) ≫ E.map k.hom ∧
        (Scheme.baseChangeCone hY).π.app k ≫ b = τ.left ≫ e :=
    Scheme.exists_hom_of_isPullback hc qj hY (τ.left ≫ e) (by
      rw [Category.assoc, hY.w, ← Category.assoc, MorphismProperty.Over.w τ])
  choose k b hb hb' using hτ
  -- a common level
  have : Fintype (Y ⟶ Y) := Fintype.ofFinite _
  obtain ⟨ℓ, hℓ⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  have g (τ : Y ⟶ Y) : ℓ ⟶ k τ := (hℓ (Finset.mem_image_of_mem k (Finset.mem_univ τ))).some
  let b' (τ : Y ⟶ Y) : pullback qj (E.map ℓ.hom) ⟶ Yj :=
    (Scheme.baseChangeDiagram E qj).map (g τ) ≫ b τ
  have hb'' (τ : Y ⟶ Y) :
      b' τ ≫ qj = pullback.snd qj (E.map ℓ.hom) ≫ E.map ℓ.hom := by
    simp only [b', Category.assoc, hb, Scheme.baseChangeDiagram_map, pullback.map,
      pullback.lift_snd_assoc, ← E.map_comp, Over.w (g τ)]
  have hπ (τ : Y ⟶ Y) : (Scheme.baseChangeCone hY).π.app ℓ ≫ b' τ = τ.left ≫ e := by
    rw [← hb' τ, ← (Scheme.baseChangeCone hY).w (g τ), Category.assoc]
  -- the covering at level `ℓ` and its endomorphisms
  let Yjo : FEt (E.obj j) := MorphismProperty.Over.mk ⊤ qj ⟨hfin, het⟩
  let Yℓ : FEt (E.obj ℓ.left) := (FEt.pullback (E.map ℓ.hom)).obj Yjo
  let ψ' (τ : Y ⟶ Y) : pullback qj (E.map ℓ.hom) ⟶ pullback qj (E.map ℓ.hom) :=
    pullback.lift (b' τ) (pullback.snd _ _) (hb'' τ)
  let ψ (τ : Y ⟶ Y) : Yℓ ⟶ Yℓ :=
    MorphismProperty.Over.homMk (ψ' τ) (pullback.lift_snd _ _ _)
  -- the comparison with `Y`
  have hsq : IsPullback ((Scheme.baseChangeCone hY).π.app ℓ) Y.hom Yℓ.hom (c.π.app ℓ.left) :=
    Scheme.isPullback_baseChangeCone hY ℓ
  let Φ : (FEt.pullback (c.π.app ℓ.left)).obj Yℓ ≅ Y :=
    (MorphismProperty.Over.isoMk hsq.isoPullback (IsPullback.isoPullback_hom_snd _)).symm
  refine ⟨ℓ.left, Yℓ, ⟨Φ⟩, fun τ' ↦ ?_⟩
  let τ : Y ⟶ Y := Φ.inv ≫ τ' ≫ Φ.hom
  refine ⟨ψ τ, ?_⟩
  suffices key : (FEt.pullback (c.π.app ℓ.left)).map (ψ τ) = Φ.hom ≫ τ ≫ Φ.inv by
    rw [key]
    simp [τ]
  have key₂ : (Scheme.baseChangeCone hY).π.app ℓ ≫ ψ' τ =
      τ.left ≫ (Scheme.baseChangeCone hY).π.app ℓ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, hπ]
      simp only [Scheme.baseChangeCone_π_app, pullback.lift_fst]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd]
      simp only [Scheme.baseChangeCone_π_app, pullback.lift_snd]
      rw [← Category.assoc τ.left, MorphismProperty.Over.w τ]
  ext : 1
  change _ = hsq.isoPullback.inv ≫ τ.left ≫ hsq.isoPullback.hom
  rw [Iso.eq_inv_comp]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_fst]
    simp only [MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst]
    exact key₂
  · rw [Category.assoc, Category.assoc, IsPullback.isoPullback_hom_snd]
    simp only [MorphismProperty.Over.pullback_map_left, pullback.lift_snd]
    rw [IsPullback.isoPullback_hom_snd, MorphismProperty.Over.w τ]

end Limit

end SGA.SGA1.ExposeX
