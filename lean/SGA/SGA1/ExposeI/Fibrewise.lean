/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.LocalRing
import SGA.SGA1.ExposeI.FiberStalk
import SGA.SGA1.ExposeI.Fundamental
import SGA.SGA1.ExposeIV.LocalCriterion

/-!
# SGA 1, Exposé I, I.5.7–I.5.9: fibrewise criteria

For `Y`-schemes `p : X ⟶ Y`, `p' : X' ⟶ Y` and a `Y`-morphism `g : X ⟶ X'`, SGA compares `g`
with its restrictions `g_y = g ⊗_Y κ(y) : X_y ⟶ X'_y` to the fibres (`fiberMap`). As in the
exposé, `Y` is locally noetherian and `X`, `X'` are of finite type over `Y`; a point `x` of `X`
over `y` is also written as a point `z` of `X_y` (`x = p.fiberι y z`, or `z = p.asFiber x`).

The local rings of the fibres at `z` and `g_y(z)` are `C/𝔪_y C` and `B/𝔪_y B`, where
`B = 𝒪_{X',g(x)}` and `C = 𝒪_{X,x}` (`FiberStalk`), so each criterion reduces to local algebra
(`stalkMap_iff_stalkMap_fiberMap`):

* I.5.8: `g` is quasi-finite (resp. unramified) at `x` iff `g_y` is
  (`quasiFiniteAt_iff_quasiFiniteAt_fiberMap'`, `formallyUnramified_stalkMap_iff_fiberMap'`).
  Quasi-finiteness at `x` means that `x` is isolated in its fibre, and the fibres of `g` and
  `g_y` through `x` are homeomorphic; for unramifiedness, `C/IC` unramified over `B/I` with
  `I ⊆ 𝔪_B` forces `𝔪_B C = 𝔪_C` and a separable residue extension
  (`formallyUnramified_iff_formallyUnramified_quotient`).
* I.5.9: if moreover `X`, `X'` are flat over `Y`, `g` is flat (resp. étale, i.e. flat and
  unramified, I.4.1) at `x` iff `g_y` is (`flat_stalkMap_iff_flat_stalkMap_fiberMap'`,
  `etaleAt_iff_etaleAt_fiberMap`). The flat case is the fibrewise flatness criterion
  (EGA IV 11.3.10), proved as IV.5.9.
* I.5.7: under the hypotheses of I.5.9, `g` is an open immersion (resp. an isomorphism) iff every
  `g_y` is (`isOpenImmersion_iff_forall_isOpenImmersion_fiberMap`,
  `isIso_iff_forall_isIso_fiberMap`). As in SGA, sufficiency combines I.5.8, I.5.9 and I.5.1: `g`
  is étale, injective, and has trivial residue field extensions.
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

variable {X X' Y : Scheme.{u}} (p : X ⟶ Y) (p' : X' ⟶ Y) (g : X ⟶ X') (hg : g ≫ p' = p)

/-- The restriction `g ⊗_Y κ(y) : X_y ⟶ X'_y` of a `Y`-morphism to the fibres over `y`. -/
noncomputable def fiberMap (y : Y) : p.fiber y ⟶ p'.fiber y :=
  pullback.map _ _ _ _ g (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hg]) (by simp)

/-- `g_y` composed with `X'_y ⟶ X'` is `X_y ⟶ X` composed with `g`. -/
@[reassoc]
lemma fiberMap_fiberι (y : Y) : fiberMap p p' g hg y ≫ p'.fiberι y = p.fiberι y ≫ g := by
  simp only [fiberMap, Scheme.Hom.fiberι]
  exact pullback.lift_fst _ _ _

/-- `g_y` is a morphism over `Spec κ(y)`. -/
@[reassoc]
lemma fiberMap_fiberToSpecResidueField (y : Y) :
    fiberMap p p' g hg y ≫ p'.fiberToSpecResidueField y = p.fiberToSpecResidueField y := by
  simp only [fiberMap, Scheme.Hom.fiberToSpecResidueField]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

lemma fiberι_fiberMap_apply (y : Y) (z : p.fiber y) :
    p'.fiberι y (fiberMap p p' g hg y z) = g (p.fiberι y z) := by
  rw [← Scheme.Hom.comp_apply, fiberMap_fiberι, Scheme.Hom.comp_apply]

/-- The stalk maps of `g_y` at `z` and of `g` at the image `x` of `z` are compatible with the
surjections `𝒪_{X,x} → 𝒪_{X_y,z}`: `ψ' ≫ g_y = (𝒪_{X',x'} ≅ 𝒪_{X', g x}) ≫ g ≫ ψ`. -/
lemma stalkMap_fiberι_comp_stalkMap_fiberMap (y : Y) (z : p.fiber y) :
    (p'.fiberι y).stalkMap (fiberMap p p' g hg y z) ≫ (fiberMap p p' g hg y).stalkMap z =
      (X'.presheaf.stalkCongr (.of_eq (fiberι_fiberMap_apply p p' g hg y z))).hom ≫
        g.stalkMap (p.fiberι y z) ≫ (p.fiberι y).stalkMap z := by
  have h := Scheme.Hom.stalkMap_congr_hom _ _ (fiberMap_fiberι p p' g hg y) z
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h
  exact h

section Local

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Algebra A C] [IsScalarTower A B C] [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
  [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]

/-- I.5.9, local form (flatness): for local noetherian `A → B → C` with `B` and `C` flat over
`A`, `C` is flat over `B` iff `C/𝔪_A C` is flat over `B/𝔪_A B`. This is IV.5.9. -/
theorem flat_iff_flat_quotient_maximalIdeal [IsNoetherianRing A] [IsNoetherianRing B]
    [IsNoetherianRing C] [Module.Flat A B] [Module.Flat A C] :
    Module.Flat B C ↔
      Module.Flat (B ⧸ (maximalIdeal A).map (algebraMap A B))
        (C ⧸ ((maximalIdeal A).map (algebraMap A B)).map (algebraMap B C)) := by
  rw [ExposeIV.flat_iff_flat_and_flat_fibre (A := A) (C := C) (M := C)]
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor C
    ((maximalIdeal A).map (algebraMap A B))
  exact ⟨fun ⟨_, _⟩ ↦ Module.Flat.of_linearEquiv e.toLinearEquiv,
    fun _ ↦ ⟨inferInstance, Module.Flat.of_linearEquiv e.symm.toLinearEquiv⟩⟩

variable {A B C}

open Algebra in
/-- I.5.8, local form (unramifiedness): if `B → C` is a local homomorphism essentially of finite
type and `I ⊆ 𝔪_B`, then `C` is unramified over `B` iff `C/IC` is unramified over `B/I`. -/
theorem formallyUnramified_iff_formallyUnramified_quotient [EssFiniteType B C] (I : Ideal B)
    (hI : I ≤ maximalIdeal B) :
    FormallyUnramified B C ↔ FormallyUnramified (B ⧸ I) (C ⧸ I.map (algebraMap B C)) := by
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ?_⟩
  have hJm : I.map (algebraMap B C) ≤ maximalIdeal C := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu ↦ (mem_maximalIdeal _).mp (hI ha) (isUnit_of_map_unit _ _ hu)
  have : FormallyUnramified B (C ⧸ I.map (algebraMap B C)) :=
    .comp B (B ⧸ I) (C ⧸ I.map (algebraMap B C))
  have : Nontrivial (C ⧸ I.map (algebraMap B C)) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal C).ne_top hJm)
  have : IsLocalRing (C ⧸ I.map (algebraMap B C)) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (algebraMap C (C ⧸ I.map (algebraMap B C))) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (algebraMap B (C ⧸ I.map (algebraMap B C))) :=
    inferInstanceAs (IsLocalHom ((algebraMap C _).comp (algebraMap B C)))
  have : EssFiniteType B (C ⧸ I.map (algebraMap B C)) := .comp B C _
  -- `𝔪_B C = 𝔪_C`, since this holds modulo `IC ⊆ 𝔪_B C`
  have hmax : (maximalIdeal B).map (algebraMap B C) = maximalIdeal C := by
    have h1 := FormallyUnramified.map_maximalIdeal (R := B) (S := C ⧸ I.map (algebraMap B C))
    rw [IsScalarTower.algebraMap_eq B C (C ⧸ I.map (algebraMap B C)), ← Ideal.map_map] at h1
    have h2 := congrArg (Ideal.comap (algebraMap C (C ⧸ I.map (algebraMap B C)))) h1
    rw [Ideal.comap_map_of_surjective' (algebraMap C (C ⧸ I.map (algebraMap B C)))
        Ideal.Quotient.mk_surjective, maximalIdeal_comap] at h2
    rw [← h2, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, left_eq_sup]
    exact Ideal.map_mono hI
  -- the residue field extension is separable, as `κ(C)` is a quotient of `C/IC`
  have : FormallyUnramified B (ResidueField C) :=
    .of_surjective (Ideal.Quotient.liftₐ (I.map (algebraMap B C))
      (IsScalarTower.toAlgHom B C (ResidueField C)) fun a ha ↦ by
        simpa [residue_eq_zero_iff] using hJm ha)
      (by
        intro w
        obtain ⟨c, rfl⟩ := residue_surjective w
        exact ⟨Ideal.Quotient.mk _ c, rfl⟩)
  have : FormallyUnramified (ResidueField B) (ResidueField C) := .of_restrictScalars B _ _
  have : EssFiniteType B (ResidueField C) := .comp _ C _
  have : EssFiniteType (ResidueField B) (ResidueField C) := .of_comp B _ _
  have : Algebra.IsSeparable (ResidueField B) (ResidueField C) :=
    FormallyUnramified.isSeparable _ _
  exact FormallyUnramified.of_map_maximalIdeal hmax

end Local

set_option backward.isDefEq.respectTransparency false in
/-- The reduction of the fibrewise criteria to local algebra. Let `x ∈ X` be the image of
`z ∈ X_y`, `A = 𝒪_{Y,y}`, `B = 𝒪_{X',g(x)}`, `C = 𝒪_{X,x}`. The local rings of the fibres at `z`
and `g_y(z)` are `C/𝔪_A C` and `B/𝔪_A B` (`stalkFiberEquiv`), so a property `P` of ring maps
which respects isomorphisms and satisfies `P(B → C) ↔ P(B/𝔪_A B → C/𝔪_A C)` holds for `g` at
`x` iff it holds for `g_y` at `z`. The equivalence may use a property `Q` of the structure maps
`A → B`, `A → C` (flatness, for I.5.9). -/
theorem stalkMap_iff_stalkMap_fiberMap
    (P Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hP : RingHom.RespectsIso P) (hQ : RingHom.RespectsIso Q)
    (H : ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
      [Algebra A C] [IsScalarTower A B C] [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
      [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)] [IsNoetherianRing A]
      [IsNoetherianRing B] [IsNoetherianRing C] [Algebra.EssFiniteType B C],
      Q (algebraMap A B) → Q (algebraMap A C) →
        (P (algebraMap B C) ↔ P (algebraMap (B ⧸ (maximalIdeal A).map (algebraMap A B))
          (C ⧸ ((maximalIdeal A).map (algebraMap A B)).map (algebraMap B C)))))
    [IsLocallyNoetherian Y] [LocallyOfFiniteType p] [LocallyOfFiniteType p']
    (hQp : ∀ x, Q (p.stalkMap x).hom) (hQp' : ∀ x, Q (p'.stalkMap x).hom) (y : Y)
    (z : p.fiber y) :
    P (g.stalkMap (p.fiberι y z)).hom ↔ P ((fiberMap p p' g hg y).stalkMap z).hom := by
  subst hg
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (g ≫ p')
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian p'
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g p'
  have hx' := fiberι_fiberMap_apply (g ≫ p') p' g rfl y z
  have hcomp := stalkMap_fiberι_comp_stalkMap_fiberMap (g ≫ p') p' g rfl y z
  -- the local rings `A = 𝒪_{Y,y}`, `B = 𝒪_{X',x'}`, `C = 𝒪_{X,x}`
  let c := X'.presheaf.stalkCongr (.of_eq hx')
  let β := c.hom ≫ g.stalkMap ((g ≫ p').fiberι y z)
  let αB := p'.stalkMap (p'.fiberι y (fiberMap (g ≫ p') p' g rfl y z))
  let cY := Y.presheaf.stalkCongr (.of_eq (congrArg p' hx'))
  have hαβ : αB ≫ β = cY.hom ≫ (g ≫ p').stalkMap ((g ≫ p').fiberι y z) := by
    rw [Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_congr_point_assoc p' _ _ hx']
  have hcsurj : Function.Surjective c.hom := (ConcreteCategory.bijective_of_isIso c.hom).2
  have hcYsurj : Function.Surjective cY.hom := (ConcreteCategory.bijective_of_isIso cY.hom).2
  have : IsLocalHom c.hom.hom := IsLocalHom.of_surjective _ hcsurj
  have : IsLocalHom β.hom :=
    inferInstanceAs (IsLocalHom ((g.stalkMap ((g ≫ p').fiberι y z)).hom.comp c.hom.hom))
  let A := Y.presheaf.stalk (p' (p'.fiberι y (fiberMap (g ≫ p') p' g rfl y z)))
  let B := X'.presheaf.stalk (p'.fiberι y (fiberMap (g ≫ p') p' g rfl y z))
  let C := X.presheaf.stalk ((g ≫ p').fiberι y z)
  let : Algebra A B := αB.hom.toAlgebra
  let : Algebra B C := β.hom.toAlgebra
  let : Algebra A C := (αB ≫ β).hom.toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom αB.hom)
  have : IsLocalHom (algebraMap B C) := inferInstanceAs (IsLocalHom β.hom)
  have : Algebra.EssFiniteType B C :=
    (RingHom.EssFiniteType.respectsIso.cancel_left_isIso c.hom _).mpr
      (LocallyOfFiniteType.stalkMap g _)
  have hQB : Q (algebraMap A B) := hQp' _
  have hQC : Q (algebraMap A C) := by
    change Q (αB ≫ β).hom
    rw [hαβ]
    exact (hQ.cancel_left_isIso cY.hom _).mpr (hQp _)
  have key := H A B C hQB hQC
  -- `P` for `B → C` is `P` for `g` at `x`
  have h₁ : P (algebraMap B C) ↔ P (g.stalkMap ((g ≫ p').fiberι y z)).hom :=
    hP.cancel_left_isIso c.hom _
  -- the fibres
  have hI : ((maximalIdeal A).map (algebraMap A B)).map (algebraMap B C) =
      (maximalIdeal (Y.presheaf.stalk ((g ≫ p') ((g ≫ p').fiberι y z)))).map
        ((g ≫ p').stalkMap ((g ≫ p').fiberι y z)).hom := by
    rw [Ideal.map_map]
    change (maximalIdeal A).map (αB ≫ β).hom = _
    rw [hαβ, CommRingCat.hom_comp, ← Ideal.map_map, map_maximalIdeal_of_surjective _ hcYsurj]
    rfl
  let eB := stalkFiberEquiv p' y (fiberMap (g ≫ p') p' g rfl y z)
  let eC := (Ideal.quotEquivOfEq hI).trans (stalkFiberEquiv (g ≫ p') y z)
  have hsq (b : B ⧸ (maximalIdeal A).map (algebraMap A B)) :
      ((fiberMap (g ≫ p') p' g rfl y).stalkMap z).hom (eB b) =
        eC (algebraMap _ (C ⧸ ((maximalIdeal A).map (algebraMap A B)).map
          (algebraMap B C)) b) := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have := congr(($hcomp).hom b)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  have h₂ : P (algebraMap (B ⧸ (maximalIdeal A).map (algebraMap A B))
      (C ⧸ ((maximalIdeal A).map (algebraMap A B)).map (algebraMap B C))) ↔
        P ((fiberMap (g ≫ p') p' g rfl y).stalkMap z).hom := by
    have hG : ((fiberMap (g ≫ p') p' g rfl y).stalkMap z).hom =
        (eC.toRingHom.comp (algebraMap _ _)).comp eB.symm.toRingHom := by
      refine RingHom.ext fun w ↦ ?_
      obtain ⟨b, rfl⟩ := eB.surjective w
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
      exact hsq b
    have hG' : algebraMap (B ⧸ (maximalIdeal A).map (algebraMap A B))
        (C ⧸ ((maximalIdeal A).map (algebraMap A B)).map (algebraMap B C)) =
        (eC.symm.toRingHom.comp ((fiberMap (g ≫ p') p' g rfl y).stalkMap z).hom).comp
          eB.toRingHom := by
      refine RingHom.ext fun b ↦ ?_
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      have := congrArg eC.symm (hsq b)
      rw [RingEquiv.symm_apply_apply] at this
      exact this.symm
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [hG]
      exact hP.2 _ eB.symm (hP.1 _ eC h)
    · rw [hG']
      exact hP.2 _ eB (hP.1 _ eC.symm h)
  rw [← h₁, key, h₂]

/-- The trivial property of ring maps respects isomorphisms. -/
lemma respectsIso_true :
    RingHom.RespectsIso (fun {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S) ↦ True) :=
  ⟨fun _ _ _ ↦ trivial, fun _ _ _ ↦ trivial⟩

/-- I.5.9 (flatness): if `X` and `X'` are flat and of finite type over the locally noetherian `Y`,
then `g` is flat at `x` iff its restriction `g_y : X_y ⟶ X'_y` to the fibres over `y = p(x)` is
flat at `x` (EGA IV 11.3.10; here IV.5.9). The point `x` is given as a point `z` of `X_y`. -/
theorem flat_stalkMap_iff_flat_stalkMap_fiberMap [IsLocallyNoetherian Y] [Flat p] [Flat p']
    [LocallyOfFiniteType p] [LocallyOfFiniteType p'] (y : Y) (z : p.fiber y) :
    (g.stalkMap (p.fiberι y z)).hom.Flat ↔ ((fiberMap p p' g hg y).stalkMap z).hom.Flat := by
  refine stalkMap_iff_stalkMap_fiberMap p p' g hg (fun f ↦ f.Flat) (fun f ↦ f.Flat)
    RingHom.Flat.respectsIso RingHom.Flat.respectsIso ?_ (Flat.stalkMap p) (Flat.stalkMap p') y z
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB hC
  rw [RingHom.flat_algebraMap_iff] at hB hC ⊢
  rw [RingHom.flat_algebraMap_iff]
  exact flat_iff_flat_quotient_maximalIdeal A B C

/-- I.5.8 (unramifiedness): if `X` and `X'` are of finite type over the locally noetherian `Y`,
then `g` is unramified at `x` iff `g_y : X_y ⟶ X'_y` is unramified at `x`. -/
theorem formallyUnramified_stalkMap_iff_fiberMap [IsLocallyNoetherian Y]
    [LocallyOfFiniteType p] [LocallyOfFiniteType p'] (y : Y) (z : p.fiber y) :
    (g.stalkMap (p.fiberι y z)).hom.FormallyUnramified ↔
      ((fiberMap p p' g hg y).stalkMap z).hom.FormallyUnramified := by
  refine stalkMap_iff_stalkMap_fiberMap p p' g hg (fun f ↦ f.FormallyUnramified) (fun _ ↦ True)
    RingHom.FormallyUnramified.respectsIso respectsIso_true ?_ (fun _ ↦ trivial)
    (fun _ ↦ trivial) y z
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [RingHom.formallyUnramified_algebraMap, RingHom.formallyUnramified_algebraMap]
  refine formallyUnramified_iff_formallyUnramified_quotient _ ?_
  rw [Ideal.map_le_iff_le_comap]
  exact (maximalIdeal_comap (algebraMap A B)).ge

lemma isOpen_singleton_asFiber_iff {T S : Scheme.{u}} (f : T ⟶ S) (x : T) :
    IsOpen {f.asFiber x} ↔ IsOpen ({⟨x, rfl⟩} : Set (f ⁻¹' {f x})) := by
  rw [← (f.fiberHomeo (f x)).isOpen_image, Set.image_singleton]
  have : f.fiberHomeo (f x) (f.asFiber x) = ⟨x, rfl⟩ := Subtype.ext (f.fiberι_asFiber x)
  rw [this]

lemma locallyOfFiniteType_fiberMap [LocallyOfFiniteType p] (y : Y) :
    LocallyOfFiniteType (fiberMap p p' g hg y) := by
  have : LocallyOfFiniteType (p.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd p (Y.fromSpecResidueField y)))
  have : LocallyOfFiniteType (fiberMap p p' g hg y ≫ p'.fiberToSpecResidueField y) := by
    rwa [fiberMap_fiberToSpecResidueField]
  exact locallyOfFiniteType_of_comp _ (p'.fiberToSpecResidueField y)

include hg in
/-- A point of `X` with the same image under `g` as a point of `X_y` lies in `X_y`. -/
lemma exists_fiberι_eq_of_apply_eq (y : Y) (z : p.fiber y) {t : X}
    (ht : g t = g (p.fiberι y z)) : ∃ w, p.fiberι y w = t := by
  have htY : t ∈ p ⁻¹' {y} := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hg, Scheme.Hom.comp_apply, ht, ← Scheme.Hom.comp_apply, hg, apply_fiberι]
  rw [← p.range_fiberι y] at htY
  exact htY

/-- I.5.8 (quasi-finiteness): if `X` and `X'` are of finite type over `Y`, then `g` is
quasi-finite at the image `x` of `z ∈ X_y` iff `g_y` is quasi-finite at `z`: the fibres of `g`
and `g_y` through `x` and `z` are homeomorphic. -/
theorem quasiFiniteAt_iff_quasiFiniteAt_fiberMap [LocallyOfFiniteType p]
    [LocallyOfFiniteType p'] (y : Y) (z : p.fiber y) :
    g.QuasiFiniteAt (p.fiberι y z) ↔ (fiberMap p p' g hg y).QuasiFiniteAt z := by
  have : LocallyOfFiniteType g := by
    subst hg
    exact locallyOfFiniteType_of_comp g p'
  have := locallyOfFiniteType_fiberMap p p' g hg y
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber,
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, isOpen_singleton_asFiber_iff,
    isOpen_singleton_asFiber_iff]
  -- `X_y ⟶ X` induces a homeomorphism from the fibre of `g_y` through `z` to that of `g`
  have hmaps : Set.MapsTo (p.fiberι y) ((fiberMap p p' g hg y) ⁻¹' {fiberMap p p' g hg y z})
      (g ⁻¹' {g (p.fiberι y z)}) := by
    intro w hw
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw ⊢
    rw [← fiberι_fiberMap_apply p p' g hg y w, ← fiberι_fiberMap_apply p p' g hg y z, hw]
  have hφ : Topology.IsEmbedding hmaps.restrict := (p.fiberι y).isEmbedding.restrict hmaps
  have hφs : Function.Surjective hmaps.restrict := by
    rintro ⟨t, ht⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ht
    obtain ⟨w, rfl⟩ := exists_fiberι_eq_of_apply_eq p p' g hg y z ht
    refine ⟨⟨w, ?_⟩, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    apply (p'.fiberι y).isEmbedding.injective
    rw [fiberι_fiberMap_apply, fiberι_fiberMap_apply, ht]
  rw [← (hφ.toHomeomorphOfSurjective hφs).isOpen_image, Set.image_singleton]
  rfl

/-- I.5.8: if `X` and `X'` are of finite type over `Y`, then `g` is quasi-finite at `x` iff
`g_y` is, for `y = p(x)`. -/
theorem quasiFiniteAt_iff_quasiFiniteAt_fiberMap' [LocallyOfFiniteType p]
    [LocallyOfFiniteType p'] (x : X) :
    g.QuasiFiniteAt x ↔ (fiberMap p p' g hg (p x)).QuasiFiniteAt (p.asFiber x) := by
  conv_lhs => rw [← p.fiberι_asFiber x]
  exact quasiFiniteAt_iff_quasiFiniteAt_fiberMap p p' g hg (p x) (p.asFiber x)

/-- I.5.8: if `X` and `X'` are of finite type over the locally noetherian `Y`, then `g` is
unramified at `x` iff `g_y` is, for `y = p(x)`. -/
theorem formallyUnramified_stalkMap_iff_fiberMap' [IsLocallyNoetherian Y]
    [LocallyOfFiniteType p] [LocallyOfFiniteType p'] (x : X) :
    (g.stalkMap x).hom.FormallyUnramified ↔
      ((fiberMap p p' g hg (p x)).stalkMap (p.asFiber x)).hom.FormallyUnramified := by
  conv_lhs => rw [← p.fiberι_asFiber x]
  exact formallyUnramified_stalkMap_iff_fiberMap p p' g hg (p x) (p.asFiber x)

/-- I.5.9: if `X` and `X'` are flat and of finite type over the locally noetherian `Y`, then
`g` is flat at `x` iff `g_y` is, for `y = p(x)`. -/
theorem flat_stalkMap_iff_flat_stalkMap_fiberMap' [IsLocallyNoetherian Y] [Flat p] [Flat p']
    [LocallyOfFiniteType p] [LocallyOfFiniteType p'] (x : X) :
    (g.stalkMap x).hom.Flat ↔
      ((fiberMap p p' g hg (p x)).stalkMap (p.asFiber x)).hom.Flat := by
  conv_lhs => rw [← p.fiberι_asFiber x]
  exact flat_stalkMap_iff_flat_stalkMap_fiberMap p p' g hg (p x) (p.asFiber x)

/-- I.5.9 (étaleness): if `X` and `X'` are flat and of finite type over the locally noetherian
`Y`, then `g` is étale at `x` (flat and unramified at `x`, I.4.1) iff `g_y` is étale at `x`. -/
theorem etaleAt_iff_etaleAt_fiberMap [IsLocallyNoetherian Y] [Flat p] [Flat p']
    [LocallyOfFiniteType p] [LocallyOfFiniteType p'] (x : X) :
    ((g.stalkMap x).hom.Flat ∧ (g.stalkMap x).hom.FormallyUnramified) ↔
      (((fiberMap p p' g hg (p x)).stalkMap (p.asFiber x)).hom.Flat ∧
        ((fiberMap p p' g hg (p x)).stalkMap (p.asFiber x)).hom.FormallyUnramified) :=
  and_congr (flat_stalkMap_iff_flat_stalkMap_fiberMap' p p' g hg x)
    (formallyUnramified_stalkMap_iff_fiberMap' p p' g hg x)

/-- `g_y` is the base change of `g` along `X'_y ⟶ X'`. -/
lemma isPullback_fiberMap (y : Y) :
    IsPullback (p.fiberι y) (fiberMap p p' g hg y) g (p'.fiberι y) := by
  subst hg
  have s : IsPullback ((g ≫ p').fiberι y)
      (fiberMap (g ≫ p') p' g rfl y ≫ p'.fiberToSpecResidueField y) (g ≫ p')
      (Y.fromSpecResidueField y) := by
    rw [fiberMap_fiberToSpecResidueField]
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_bot s (fiberMap_fiberι _ _ _ _ _).symm
    (IsPullback.of_hasPullback p' (Y.fromSpecResidueField y))

set_option backward.isDefEq.respectTransparency false in
/-- If `g_y` has bijective stalk maps at `z` (e.g. is an open immersion), then the residue
field extension of `g` at the image of `z` is trivial. -/
lemma bijective_residueFieldMap_of_isIso_stalkMap_fiberMap (y : Y) (z : p.fiber y)
    [IsIso ((fiberMap p p' g hg y).stalkMap z)] :
    Function.Bijective (g.residueFieldMap (p.fiberι y z)) := by
  refine ⟨RingHom.injective _, fun w ↦ ?_⟩
  obtain ⟨c₀, rfl⟩ := X.residue_surjective _ w
  have hcomp := stalkMap_fiberι_comp_stalkMap_fiberMap p p' g hg y z
  obtain ⟨b, hb⟩ := (ConcreteCategory.bijective_of_isIso
    ((fiberMap p p' g hg y).stalkMap z)).2 ((p.fiberι y).stalkMap z c₀)
  obtain ⟨b', rfl⟩ := (p'.fiberι y).stalkMap_surjective _ b
  have h := congr(($hcomp).hom b')
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [hb] at h
  set c := X'.presheaf.stalkCongr (.of_eq (fiberι_fiberMap_apply p p' g hg y z))
  have h0 : ((p.fiberι y).stalkMap z).hom
      (c₀ - (g.stalkMap (p.fiberι y z)).hom (c.hom.hom b')) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact h
  have hker : c₀ - (g.stalkMap (p.fiberι y z)).hom (c.hom.hom b') ∈
      maximalIdeal (X.presheaf.stalk (p.fiberι y z)) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map ((p.fiberι y).stalkMap z).hom
    rw [h0] at this
    exact not_isUnit_zero this
  refine ⟨X'.residue _ (c.hom b'), ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]
  symm
  rw [← sub_eq_zero, ← map_sub]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hker

/-- I.5.7 (open immersions): if `X` and `X'` are flat and of finite type over the locally
noetherian `Y`, then `g` is an open immersion iff all its restrictions `g_y` to the fibres are.
As in SGA, sufficiency combines I.5.8, I.5.9 and I.5.1 (étale and radicial). -/
theorem isOpenImmersion_iff_forall_isOpenImmersion_fiberMap [IsLocallyNoetherian Y] [Flat p]
    [Flat p'] [LocallyOfFiniteType p] [LocallyOfFiniteType p'] :
    IsOpenImmersion g ↔ ∀ y, IsOpenImmersion (fiberMap p p' g hg y) := by
  refine ⟨fun _ y ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_fiberMap p p' g hg y) ‹_›, fun H ↦ ?_⟩
  have : LocallyOfFiniteType g := by
    subst hg
    exact locallyOfFiniteType_of_comp g p'
  have : Flat g := Flat.of_stalkMap g fun x ↦
    (flat_stalkMap_iff_flat_stalkMap_fiberMap' p p' g hg x).mpr (Flat.stalkMap _ _)
  have : FormallyUnramified g :=
    HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime fun x ↦
      (formallyUnramified_stalkMap_iff_fiberMap' p p' g hg x).mpr
        (FormallyUnramified.stalkMap _ _)
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian p'
  have : Etale g := Etale.of_formallyUnramified_of_flat g
  have : UniversallyInjective g := by
    have key : UniversallyInjective g ↔ Function.Injective g ∧
        ∀ x, (g.residueFieldMap x).hom.IsPurelyInseparable :=
      (tfae_universallyInjective g).out 1 3
    refine key.mpr ⟨fun a b hab ↦ ?_, fun x ↦ ?_⟩
    · have ha : a ∈ Set.range (p.fiberι (p a)) := by
        rw [p.range_fiberι]
        rfl
      generalize p a = y at ha
      obtain ⟨za, rfl⟩ := ha
      obtain ⟨zb, rfl⟩ := exists_fiberι_eq_of_apply_eq p p' g hg y za hab.symm
      rw [← fiberι_fiberMap_apply p p' g hg y za, ← fiberι_fiberMap_apply p p' g hg y zb] at hab
      rw [(fiberMap p p' g hg y).isOpenEmbedding.injective
        ((p'.fiberι y).isEmbedding.injective hab)]
    · rw [← p.fiberι_asFiber x]
      exact ringHom_isPurelyInseparable_of_bijective _
        (bijective_residueFieldMap_of_isIso_stalkMap_fiberMap p p' g hg _ _)
  exact isOpenImmersion_of_etale_of_universallyInjective g

/-- I.5.7 (isomorphisms): if `X` and `X'` are flat and of finite type over the locally
noetherian `Y`, then `g` is an isomorphism iff all its restrictions `g_y` to the fibres are. -/
theorem isIso_iff_forall_isIso_fiberMap [IsLocallyNoetherian Y] [Flat p] [Flat p']
    [LocallyOfFiniteType p] [LocallyOfFiniteType p'] :
    IsIso g ↔ ∀ y, IsIso (fiberMap p p' g hg y) := by
  simp only [isIso_iff_isOpenImmersion_and_surjective, forall_and,
    isOpenImmersion_iff_forall_isOpenImmersion_fiberMap p p' g hg]
  refine and_congr_right fun _ ↦ ⟨fun h y ↦ ⟨fun w ↦ ?_⟩, fun h ↦ ⟨fun x' ↦ ?_⟩⟩
  · obtain ⟨t, ht⟩ := h.surj (p'.fiberι y w)
    obtain ⟨z', rfl⟩ : ∃ z', p.fiberι y z' = t := by
      have : t ∈ p ⁻¹' {y} := by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        rw [← hg, Scheme.Hom.comp_apply, ht, apply_fiberι]
      rwa [← p.range_fiberι y] at this
    exact ⟨z', (p'.fiberι y).isEmbedding.injective (by rw [fiberι_fiberMap_apply, ht])⟩
  · obtain ⟨w, hw⟩ : ∃ w, p'.fiberι (p' x') w = x' := by
      rw [← Set.mem_range, p'.range_fiberι]
      rfl
    obtain ⟨z, hz⟩ := (h (p' x')).surj w
    exact ⟨p.fiberι _ z, by rw [← fiberι_fiberMap_apply p p' g hg _ z, hz, hw]⟩

end SGA.SGA1.ExposeI
