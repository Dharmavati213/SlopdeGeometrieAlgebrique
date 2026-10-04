/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import SGA.Foundations.ArithmeticSurface.ModelStatements
import SGA.Foundations.CommAlg.RegularLocalRing
import SGA.SGA1.ExposeXIII.SemistableReductionFibre
import SGA.SGA2.ExposeIII.RegularLocalDomain

/-!
# A rational point of the generic fibre gives a smooth point on a component of multiplicity one

Stacks, Tag 0CE8 (1), (2) (`AlgebraicGeometry.RationalPointModelStatement`, one of the inputs of
the semistable reduction theorem, registry row A21), proved here:
`SGA.SGA1.ExposeXIII.rationalPointModelStatement`.

Let `X` be a regular proper model over a discrete valuation ring `R` (uniformizer `π`, residue
field `k`) of a curve `C` over `K = Frac R`, and `s ∈ C(K)`. By the valuative criterion of
properness, `s` extends to a section `σ : Spec R ⟶ X`; let `x = σ(closed point)` and `z` the
corresponding point of the closed fibre `X_k`. The ring map `σ^# : 𝒪_{X,x} → R` is a retraction of
`R → 𝒪_{X,x}`, so the image `a` of `π` is in `𝔪_x` but not in `𝔪_x²` (its image `π` is not in
`𝔪_R²`). Since `𝒪_{X,x}` is regular, `𝒪_{X,x}/(a)` is regular (Stacks, Tag 00NR,
`SGA.SGA2.ExposeIII.regularLocal_parameter_quotient`), and it is the local ring of `X_k` at `z`
(`SGA.SGA1.ExposeXIII.closedFibreStalkEquiv`). So `𝒪_{X_k,z}` is a regular local ring, hence a
domain, and `z` lies on a unique irreducible component of `X_k`, of multiplicity `1`
(`AlgebraicGeometry.Scheme.existsUnique_component_of_isDomain_stalk`). The point `z` is closed: it
is the image of the section `Spec k ⟶ X_k` induced by `σ`, a closed immersion since `X_k ⟶ Spec k`
is separated.

The residue field of `R` need not be algebraically closed for the proof; the statement assumes it
(as all the model statements of `SGA.Foundations.ArithmeticSurface.ModelStatements`). Stacks also
shows `H⁰(Cᵢ, 𝒪) = k` and Tag 0CE8 (3); these are not part of the statement.

## References

* [Stacks Project, Tag 0CE8](https://stacks.math.columbia.edu/tag/0CE8), Tag 00NR
-/

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace SGA.SGA1.ExposeXIII

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A uniformizer of a discrete valuation ring is not in `𝔪²`. -/
private lemma irreducible_notMem_maximalIdeal_sq {π : R} (hπ : Irreducible π) :
    π ∉ maximalIdeal R ^ 2 := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have h1 : π * (1 - π * c) = 0 := by rw [mul_sub, mul_one, ← mul_assoc, ← sq, ← hc, sub_self]
  rcases mul_eq_zero.mp h1 with h | h
  · exact hπ.ne_zero h
  · exact hπ.not_isUnit (IsUnit.of_mul_eq_one (b := c) (by rw [sub_eq_zero] at h; exact h.symm))

set_option backward.isDefEq.respectTransparency false in
/-- The key local computation: if `σ : Spec R ⟶ X` is a section of `g : X ⟶ Spec R` and `π` a
uniformizer of `R`, the image of `π` in the local ring of `X` at `σ(closed point)` lies in `𝔪` but
not in `𝔪²`. -/
private lemma image_uniformizer_mem_and_notMem_sq {X : Scheme.{u}} (g : X ⟶ Spec (.of R))
    (l : Spec (.of R) ⟶ X) (hl : l ≫ g = 𝟙 _) {π : R} (hπ : Irreducible π) :
    (stalkStructureMap g (l (closedPoint R))).hom π ∈ maximalIdeal _ ∧
      (stalkStructureMap g (l (closedPoint R))).hom π ∉ maximalIdeal _ ^ 2 := by
  set σ := Scheme.stalkClosedPointTo l
  have hret : stalkStructureMap g (l (closedPoint R)) ≫ σ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec_map_stalkStructureMap,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc, hl, Spec.map_id]
  have hσ : ∀ r, σ.hom ((stalkStructureMap g (l (closedPoint R))).hom r) = r := fun r ↦ by
    rw [← CommRingCat.comp_apply, hret]
    rfl
  have hmaxR : π ∈ maximalIdeal R := hπ.not_isUnit
  refine ⟨fun hu ↦ hmaxR ((hσ π) ▸ hu.map σ.hom), fun hsq ↦ ?_⟩
  have hle : (maximalIdeal (X.presheaf.stalk (l (closedPoint R)))).map σ.hom ≤ maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun a ha ↦ map_nonunit σ.hom a ha
  have := Ideal.mem_map_of_mem σ.hom hsq
  rw [Ideal.map_pow, hσ] at this
  exact irreducible_notMem_maximalIdeal_sq hπ (Ideal.pow_right_mono hle 2 this)

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks, Tag 0CE8 (1), (2)**: for a regular proper model `X` of a smooth proper geometrically
connected curve `C` with a `K`-rational point, over a discrete valuation ring with algebraically
closed residue field, the closed fibre `X_k` has a closed point at which it is regular, lying on a
unique irreducible component, of multiplicity `1`. -/
theorem rationalPointModelStatement : RationalPointModelStatement.{u} := by
  intro R _ _ _ _ K _ _ _ C f _ _ _ X g hX ⟨s, hs⟩
  obtain ⟨hprop, -, hreg, e, he⟩ := hX
  -- the `K`-point of `X` and its extension `l : Spec R ⟶ X`
  let t : Spec (.of K) ⟶ X := s ≫ e.inv ≫ pullback.fst _ _
  have hesnd : e.inv ≫ pullback.snd _ _ = f := by rw [← he, Iso.inv_hom_id_assoc]
  have htg : t ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    simp only [t, Category.assoc, pullback.condition]
    rw [← Category.assoc e.inv, hesnd, ← Category.assoc, hs, Category.id_comp]
  have hE : ValuativeCriterion.Existence g := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) g := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  let S : ValuativeCommSq g :=
    { R := R, K := K, i₁ := t, i₂ := 𝟙 _, commSq := ⟨by rw [htg, Category.comp_id]⟩ }
  obtain ⟨⟨l, -, hl⟩⟩ := (hE S).exists_lift
  change l ≫ g = 𝟙 _ at hl
  -- the point `x = l(closed point)` and the point `z` of the closed fibre over it
  have hgx : g (l (closedPoint R)) = closedPoint R := by
    rw [← Scheme.Hom.comp_apply, hl]
    rfl
  obtain ⟨z, hz⟩ : l (closedPoint R) ∈ Set.range (closedFibreι g) := by
    rw [range_closedFibreι]
    exact hgx
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨hmem, hsq⟩ := hz ▸ image_uniformizer_mem_and_notMem_sq g l hl hπ
  have : IsRegularLocalRing (X.presheaf.stalk (closedFibreι g z)) := hreg _
  -- the local ring of the closed fibre at `z` is regular
  have hregz : IsRegularLocalRing ((closedFibre g).presheaf.stalk z) := by
    obtain ⟨-, hq, -⟩ := SGA.SGA2.ExposeIII.regularLocal_parameter_quotient _ hmem hsq
    have hI : (maximalIdeal R).map (stalkStructureMap g (closedFibreι g z)).hom =
        Ideal.span {(stalkStructureMap g (closedFibreι g z)).hom π} := by
      rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    exact IsRegularLocalRing.of_ringEquiv
      ((Ideal.quotEquivOfEq hI).symm.trans (closedFibreStalkEquiv g z))
  -- `z` is a closed point: the image of the section `Spec k ⟶ X_k` induced by `l`
  have hzc : IsClosed ({z} : Set (closedFibre g)) := by
    let σk : Spec (.of (ResidueField R)) ⟶ closedFibre g :=
      pullback.lift (Spec.map (CommRingCat.ofHom (residue R)) ≫ l) (𝟙 _)
        (by rw [Category.assoc, hl, Category.comp_id, Category.id_comp])
    have hσk : σk ≫ closedFibreHom g = 𝟙 _ := pullback.lift_snd _ _ _
    have : IsClosedImmersion (σk ≫ closedFibreHom g) := by rw [hσk]; infer_instance
    have : IsClosedImmersion σk := IsClosedImmersion.of_comp σk (closedFibreHom g)
    have hrange : Set.range σk = {z} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨closedPoint (ResidueField R), ?_⟩, ?_⟩
      · apply (closedFibreι g).isEmbedding.injective
        rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hz]
        have : IsLocalHom (CommRingCat.ofHom (residue R)).hom :=
          inferInstanceAs (IsLocalHom (residue R))
        rw [Spec_closedPoint]
      · rintro _ ⟨w, rfl⟩
        rw [Subsingleton.elim (α := PrimeSpectrum (ResidueField R)) w (closedPoint _)]
        apply (closedFibreι g).isEmbedding.injective
        rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hz]
        have : IsLocalHom (CommRingCat.ofHom (residue R)).hom :=
          inferInstanceAs (IsLocalHom (residue R))
        rw [Spec_closedPoint]
    rw [← hrange]
    exact σk.isClosedEmbedding.isClosed_range
  obtain ⟨Z, hzZ, huniq, hm⟩ := Scheme.existsUnique_component_of_isDomain_stalk z
  exact ⟨z, Z, hzc, hzZ, huniq, hregz, hm⟩

end SGA.SGA1.ExposeXIII
