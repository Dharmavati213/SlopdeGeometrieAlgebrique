/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.ArithmeticSurface.Model
import SGA.Foundations.Semistable.SmoothCurve
import SGA.SGA1.ExposeI.FiberStalk

/-!
# The local rings of the closed fibre of a scheme over a local ring

For a scheme `X` over a local ring `R` (`g : X ⟶ Spec R`) with residue field `k`, the closed fibre
`X_k = X ×_R Spec k` (`AlgebraicGeometry.closedFibre g`, the fibre used in
`SemistableReductionStatement`) is a closed subscheme of `X`, and its local ring at a point `z`
with image `x` in `X` is `𝒪_{X,x} / 𝔪_R 𝒪_{X,x}` (`SGA.SGA1.ExposeXIII.ker_stalkMap_closedFibre`,
`SGA.SGA1.ExposeXIII.closedFibreStalkEquiv`; EGA I 3.6.5). For a discrete valuation ring with
uniformizer `π` this is `𝒪_{X,x} / π 𝒪_{X,x}`.

This is `SGA.SGA1.ExposeI.ker_stalkMap_fiberι` for the presentation `X ×_R Spec (R/𝔪)` of the
fibre (mathlib's `Scheme.Hom.fiber` uses `Spec κ(𝔪)` instead); the proof reuses
`SGA.SGA1.ExposeI.apply_eq_zero_of_stalkMap_eq_zero`. The `R`-algebra structure of `𝒪_{X,x}` is
`AlgebraicGeometry.stalkStructureMap g x`, which is natural (`stalkStructureMap_comp`,
`stalkStructureMap_comp_spec_map`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A]

/-- The structure maps `A → 𝒪` are natural: for `h : Z ⟶ Y` and `f : Y ⟶ Spec A`,
`(A → 𝒪_{Z,z}) = (A → 𝒪_{Y,h z} → 𝒪_{Z,z})`. -/
lemma stalkStructureMap_comp {Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ Spec (.of A)) (z : Z) :
    stalkStructureMap (h ≫ f) z = stalkStructureMap f (h z) ≫ h.stalkMap z := by
  apply Spec.map_injective
  rw [Spec_map_stalkStructureMap, Spec.map_comp, Spec_map_stalkStructureMap,
    Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]

/-- The structure map of `Y ⟶ Spec A ⟶ Spec B` is `B → A → 𝒪_{Y,y}`. -/
lemma stalkStructureMap_comp_spec_map {B : Type u} [CommRing B] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of A)) (φ : B →+* A) (y : Y) :
    stalkStructureMap (f ≫ Spec.map (CommRingCat.ofHom φ)) y =
      CommRingCat.ofHom φ ≫ stalkStructureMap f y := by
  apply Spec.map_injective
  rw [Spec_map_stalkStructureMap, Spec.map_comp, Spec_map_stalkStructureMap, Category.assoc]

end AlgebraicGeometry

namespace SGA.SGA1.ExposeXIII

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (g : X ⟶ Spec (.of R))

/-- The closed immersion `X_k ⟶ X` of the closed fibre. -/
noncomputable abbrev closedFibreι : closedFibre g ⟶ X := pullback.fst _ _

/-- `X_k ⟶ X` is a closed immersion (base change of `Spec (R/𝔪) ⟶ Spec R`). -/
instance : IsClosedImmersion (closedFibreι g) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (residue R))) :=
    IsClosedImmersion.spec_of_surjective _ (residue_surjective (R := R))
  infer_instance

lemma closedFibreι_comp : closedFibreι g ≫ g =
    closedFibreHom g ≫ Spec.map (CommRingCat.ofHom (residue R)) :=
  pullback.condition

/-- The elements of `𝔪_R` vanish in the local rings of the closed fibre. -/
lemma map_maximalIdeal_le_ker_stalkMap_closedFibreι (z : closedFibre g) :
    (maximalIdeal R).map (stalkStructureMap g (closedFibreι g z)).hom ≤
      RingHom.ker ((closedFibreι g).stalkMap z).hom := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, RingHom.mem_ker, ← CommRingCat.comp_apply, ← stalkStructureMap_comp,
    closedFibreι_comp, stalkStructureMap_comp_spec_map, CommRingCat.comp_apply]
  change (stalkStructureMap (closedFibreHom g) z).hom (residue R r) = 0
  rw [(residue_eq_zero_iff r).mpr hr, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The local ring of the closed fibre: the stalk map `𝒪_{X,x} → 𝒪_{X_k,z}` of `X_k ⟶ X` at a
point `z` with image `x` has kernel `𝔪_R 𝒪_{X,x}` (EGA I 3.6.5; the analogue of
`SGA.SGA1.ExposeI.ker_stalkMap_fiberι` for `X_k = X ×_R Spec (R/𝔪)`). -/
theorem ker_stalkMap_closedFibreι (z : closedFibre g) :
    RingHom.ker ((closedFibreι g).stalkMap z).hom =
      (maximalIdeal R).map (stalkStructureMap g (closedFibreι g z)).hom := by
  refine le_antisymm ?_ (map_maximalIdeal_le_ker_stalkMap_closedFibreι g z)
  set x := closedFibreι g z
  set J := (maximalIdeal R).map (stalkStructureMap g x).hom
  have hJ : J ≤ maximalIdeal (X.presheaf.stalk x) := by
    refine (map_maximalIdeal_le_ker_stalkMap_closedFibreι g z).trans fun a ha ↦ ?_
    rw [RingHom.mem_ker] at ha
    by_contra hm
    exact ((IsLocalRing.notMem_maximalIdeal.mp hm).map ((closedFibreι g).stalkMap z).hom).ne_zero
      ha
  have : Nontrivial (X.presheaf.stalk x ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hJ)
  have : IsLocalRing (X.presheaf.stalk x ⧸ J) :=
    .of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let Q : CommRingCat.{u} := .of (X.presheaf.stalk x ⧸ J)
  let mk : X.presheaf.stalk x ⟶ Q := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have hθ0 : ∀ r ∈ maximalIdeal R,
      (Ideal.Quotient.mk J).comp (stalkStructureMap g x).hom r = 0 := fun r hr ↦
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
  let θ : CommRingCat.of (ResidueField R) ⟶ Q :=
    CommRingCat.ofHom (Ideal.Quotient.lift (maximalIdeal R) _ hθ0)
  have hθ : CommRingCat.ofHom (residue R) ≫ θ = stalkStructureMap g x ≫ mk := by
    ext r
    rfl
  let h₁ : Spec Q ⟶ X := Spec.map mk ≫ X.fromSpecStalk x
  have w : h₁ ≫ g = Spec.map θ ≫ Spec.map (CommRingCat.ofHom (residue R)) := by
    rw [← Spec.map_comp, hθ, Spec.map_comp, Category.assoc, Spec_map_stalkStructureMap]
  let h' : Spec Q ⟶ closedFibre g := pullback.lift h₁ (Spec.map θ) w
  have hh' : h' ≫ closedFibreι g = h₁ := pullback.lift_fst _ _ _
  have : IsLocalHom mk.hom := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcp : h₁ (closedPoint Q) = x := by
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hz : h' (closedPoint Q) = z := (closedFibreι g).isEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hh', hcp])
  intro a ha
  rw [RingHom.mem_ker] at ha
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact ExposeI.apply_eq_zero_of_stalkMap_eq_zero (closedFibreι g) h' z mk hz hh' a ha

/-- The local ring of the closed fibre `X_k` at `z` is `𝒪_{X,x} / 𝔪_R 𝒪_{X,x}`, `x` the image of
`z` in `X`. -/
noncomputable def closedFibreStalkEquiv (z : closedFibre g) :
    X.presheaf.stalk (closedFibreι g z) ⧸
        (maximalIdeal R).map (stalkStructureMap g (closedFibreι g z)).hom ≃+*
      (closedFibre g).presheaf.stalk z :=
  (Ideal.quotEquivOfEq (ker_stalkMap_closedFibreι g z).symm).trans
    (RingHom.quotientKerEquivOfSurjective ((closedFibreι g).stalkMap_surjective z))

lemma closedFibreStalkEquiv_mk (z : closedFibre g) (a : X.presheaf.stalk (closedFibreι g z)) :
    closedFibreStalkEquiv g z (Ideal.Quotient.mk _ a) = ((closedFibreι g).stalkMap z).hom a :=
  rfl

/-- The image of the closed fibre in `X` is the preimage of the closed point of `Spec R`. -/
lemma range_closedFibreι : Set.range (closedFibreι g) = g ⁻¹' {closedPoint R} := by
  have : IsLocalHom (CommRingCat.ofHom (residue R)).hom :=
    inferInstanceAs (IsLocalHom (residue R))
  rw [Scheme.Pullback.range_fst]
  congr 1
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨closedPoint (ResidueField R), ?_⟩, ?_⟩
  · exact Spec_closedPoint (f := CommRingCat.ofHom (residue R))
  · rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum (ResidueField R)) w (closedPoint _)]
    exact Spec_closedPoint (f := CommRingCat.ofHom (residue R))

end SGA.SGA1.ExposeXIII
