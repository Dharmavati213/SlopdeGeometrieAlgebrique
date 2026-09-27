/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import SGA.SGA1.ExposeXII.SchemePoints
import SGA.SGA1.ExposeXII.FiniteLimits

/-!
# SGA 1, Exposé XII, 3.1 (viii): separated schemes have Hausdorff spaces of points

XII.3.1 (viii) states that `f` is separated if and only if `f^an` is. For `X → Spec K` we prove
the direct implication on points: if `X` is separated over `K`, then `X(K)` is Hausdorff
(`SchemePoints.t2Space`). For affine opens `U`, `V`, the pairs of `K`-points of `U` and `V`
defining the same point of `X` are the points of the preimage of the diagonal in
`Spec (Γ(U) ⊗_K Γ(V))`, a closed subscheme; so they form a closed subset of `U(K) × V(K)`.
-/

universe u

noncomputable section

namespace SGA.SGA1.ExposeXII

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology Set Opposite
open scoped TensorProduct

namespace SchemePoints

attribute [local instance] sectionsAlgebra

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (.of K))]
  {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)

/-- The ring of `U ×_K V`. -/
abbrev prodRing (U V : X.Opens) : Type u := Γ(X, U) ⊗[K] Γ(X, V)

/-- The first projection `Spec (Γ(U) ⊗ Γ(V)) → X`. -/
def prodFst : Spec (.of (prodRing (K := K) U V)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := K) (S := K)).toRingHom) ≫
    hU.fromSpec

/-- The second projection `Spec (Γ(U) ⊗ Γ(V)) → X`. -/
def prodSnd : Spec (.of (prodRing (K := K) U V)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K)).toRingHom) ≫
    hV.fromSpec

lemma prodFst_over : prodFst (K := K) hU (V := V) ≫ X ↘ Spec (.of K) =
    Spec.map (CommRingCat.ofHom (algebraMap K (prodRing (K := K) U V))) := by
  rw [prodFst, Category.assoc, fromSpec_over, ← Spec.map_comp]
  congr 1

lemma prodSnd_over : prodSnd (K := K) (U := U) hV ≫ X ↘ Spec (.of K) =
    Spec.map (CommRingCat.ofHom (algebraMap K (prodRing (K := K) U V))) := by
  rw [prodSnd, Category.assoc, fromSpec_over, ← Spec.map_comp]
  congr 1
  ext c
  exact (Algebra.TensorProduct.includeRight (R := K) (A := Γ(X, U))).commutes c

/-- `Spec (Γ(U) ⊗_K Γ(V))` as a `K`-scheme. -/
abbrev prodOver : (Spec (.of (prodRing (K := K) U V))).Over (Spec (.of K)) :=
  .ofHom (Spec.map (CommRingCat.ofHom (algebraMap K (prodRing (K := K) U V))))

attribute [local instance] prodOver

variable (K) in
/-- The closed subscheme of `U ×_K V` where the two projections to `X` agree (the preimage of the
diagonal of `X`). -/
abbrev eqLocus : Scheme.{u} :=
  pullback (pullback.diagonal (X ↘ Spec (.of K)))
    (pullback.lift (prodFst (K := K) hU (V := V)) (prodSnd (U := U) hV)
      (by rw [prodFst_over, prodSnd_over]))

variable (K) in
/-- The closed immersion of the equalizer locus into `U ×_K V`. -/
abbrev eqLocusι : eqLocus K hU hV ⟶ Spec (.of (prodRing (K := K) U V)) := pullback.snd _ _

abbrev eqLocusOver : (eqLocus K hU hV).Over (Spec (.of K)) :=
  .ofHom (eqLocusι K hU hV ≫ Spec.map (CommRingCat.ofHom (algebraMap K (prodRing (K := K) U V))))

attribute [local instance] eqLocusOver

instance : (eqLocusι K hU hV).IsOver (Spec (.of K)) := ⟨rfl⟩

lemma eqLocusι_fst : eqLocusι K hU hV ≫ prodFst (K := K) hU = eqLocusι K hU hV ≫ prodSnd hV := by
  have h := pullback.condition (f := pullback.diagonal (X ↘ Spec (.of K)))
    (g := pullback.lift (prodFst (K := K) hU (V := V)) (prodSnd (U := U) hV)
      (by rw [prodFst_over, prodSnd_over]))
  have h₁ := congr($h ≫ pullback.fst _ _)
  have h₂ := congr($h ≫ pullback.snd _ _)
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, pullback.lift_fst,
    pullback.lift_snd, Category.comp_id] at h₁ h₂
  exact h₁.symm.trans h₂

lemma mem_range_map_eqLocusι (t : SchemePoints K (Spec (.of (prodRing (K := K) U V)))) :
    t ∈ range (map (K := K) (eqLocusι K hU hV)) ↔ t.1 ≫ prodFst hU = t.1 ≫ prodSnd hV := by
  obtain ⟨t, ht⟩ := t
  change _ ↔ t ≫ prodFst hU = t ≫ prodSnd hV
  constructor
  · rintro ⟨e, he⟩
    have he' : e.1 ≫ eqLocusι K hU hV = t := congr_arg Subtype.val he
    rw [← he', Category.assoc, Category.assoc, eqLocusι_fst]
  · intro h
    refine ⟨⟨pullback.lift (t ≫ prodFst hU) t ?_, ?_⟩, ext (pullback.lift_snd _ _ _)⟩
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst]
      · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd, h]
    · change pullback.lift _ _ _ ≫ eqLocusι K hU hV ≫ _ = _
      rw [pullback.lift_snd_assoc]
      exact ht

/-- `Γ(Spec R, ⊤) ≅ R`, as a `K`-algebra map. -/
def prodΓSpecAlgHom : Γ(Spec (.of (prodRing (K := K) U V)), ⊤) →ₐ[K] prodRing (K := K) U V :=
  { (Scheme.ΓSpecIso (.of (prodRing (K := K) U V))).hom.hom with
    commutes' := fun c ↦ by
      change ((structureMap K ⊤) ≫ (Scheme.ΓSpecIso (.of (prodRing (K := K) U V))).hom) c = _
      have : structureMap K (⊤ : (Spec (.of (prodRing (K := K) U V))).Opens) =
          (Scheme.ΓSpecIso (.of K)).inv ≫
            (Spec.map (CommRingCat.ofHom (algebraMap K (prodRing (K := K) U V)))).appTop := rfl
      rw [this, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
      rfl }

omit [X.Over (Spec (.of K))] in
lemma subsingleton_points_self (φ ψ : Points K K) : φ = ψ :=
  Points.ext fun a ↦ by
    rw [show a = algebraMap K K a from rfl, Points.apply_algebraMap, Points.apply_algebraMap]

/-- The pair of points `(φ, ψ)` as a point of `Γ(U) ⊗_K Γ(V)`. -/
def pairPoint (x : Points K Γ(X, U) × Points K Γ(X, V)) : Points K (prodRing (K := K) U V) :=
  Points.pair (A := K) ⟨x, subsingleton_points_self _ _⟩

/-- The point `(φ, ψ)` of `U ×_K V`. -/
def pairSchemePoint (x : Points K Γ(X, U) × Points K Γ(X, V)) :
    SchemePoints K (Spec (.of (prodRing (K := K) U V))) :=
  ⟨Spec.map (CommRingCat.ofHom (pairPoint x).toRingHom), by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap K (prodRing (K := K) U V))) = _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    exact (pairPoint x).apply_algebraMap c⟩

lemma pairSchemePoint_fst (x : Points K Γ(X, U) × Points K Γ(X, V)) :
    (pairSchemePoint x).1 ≫ prodFst hU = (chart hU x.1).1 := by
  simp only [pairSchemePoint, prodFst, chart, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  change pairPoint x (a ⊗ₜ 1) = x.1 a
  simp [pairPoint]

lemma pairSchemePoint_snd (x : Points K Γ(X, U) × Points K Γ(X, V)) :
    (pairSchemePoint x).1 ≫ prodSnd hV = (chart hV x.2).1 := by
  simp only [pairSchemePoint, prodSnd, chart, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  change pairPoint x (1 ⊗ₜ a) = x.2 a
  simp [pairPoint]

variable [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]

omit [T1Space K] in
lemma continuous_pairSchemePoint : Continuous (pairSchemePoint (K := K) (U := U) (V := V)) := by
  have h : pairSchemePoint (K := K) (U := U) (V := V) =
      chart (isAffineOpen_top _) ∘ Points.map prodΓSpecAlgHom ∘ pairPoint := by
    funext x
    apply Subtype.ext
    change Spec.map _ = Spec.map _ ≫ (isAffineOpen_top _).fromSpec
    have : CommRingCat.ofHom (Points.map prodΓSpecAlgHom (pairPoint x)).toRingHom =
        (Scheme.ΓSpecIso (.of (prodRing (K := K) U V))).hom ≫
          CommRingCat.ofHom (pairPoint x).toRingHom := rfl
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, this,
      Iso.inv_hom_id_assoc]
  rw [h]
  refine (continuous_chart _).comp ((Points.continuous_map _).comp ?_)
  have hc : Continuous fun x : Points K Γ(X, U) × Points K Γ(X, V) ↦
      (⟨x, subsingleton_points_self _ _⟩ : Points.FiberProduct K K Γ(X, U) Γ(X, V)) :=
    continuous_id.subtype_mk _
  exact Points.homeomorphTensorProduct.symm.continuous.comp hc

variable [IsSeparated (X ↘ Spec (.of K))]

/-- For `X` separated, the pairs of points of two affine charts that define the same point of
`X` form a closed subset: it is the set of points of the preimage of the (closed) diagonal. -/
lemma isClosed_setOf_chart_eq :
    IsClosed {x : Points K Γ(X, U) × Points K Γ(X, V) | chart hU x.1 = chart hV x.2} := by
  have : {x : Points K Γ(X, U) × Points K Γ(X, V) | chart hU x.1 = chart hV x.2} =
      pairSchemePoint ⁻¹' range (map (K := K) (eqLocusι K hU hV)) := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_range_map_eqLocusι, pairSchemePoint_fst,
      pairSchemePoint_snd]
    exact ⟨fun h ↦ congr_arg Subtype.val h, fun h ↦ Subtype.ext h⟩
  rw [this]
  exact (isClosedEmbedding_map _).isClosed_range.preimage continuous_pairSchemePoint

variable (K X) in
/-- XII.3.1 (viii), direct implication for `X → Spec K`: if `X` is separated over `K`, then
`X(K)` is Hausdorff. -/
theorem t2Space : T2Space (SchemePoints K X) := by
  refine ⟨fun p q hpq ↦ ?_⟩
  obtain ⟨U, hU, hpU⟩ := exists_isAffineOpen_mem p
  obtain ⟨V, hV, hqV⟩ := exists_isAffineOpen_mem q
  obtain ⟨φ, rfl⟩ := exists_chart_eq hU p hpU
  obtain ⟨ψ, rfl⟩ := exists_chart_eq hV q hqV
  have hmem : (φ, ψ) ∈ {x : Points K Γ(X, U) × Points K Γ(X, V) |
      chart hU x.1 = chart hV x.2}ᶜ := hpq
  obtain ⟨N₁, N₂, h₁, h₂, hφ, hψ, hN⟩ :=
    isOpen_prod_iff.mp (isClosed_setOf_chart_eq (K := K) hU hV).isOpen_compl φ ψ hmem
  refine ⟨chart hU '' N₁, chart hV '' N₂, (isOpenEmbedding_chart hU).isOpenMap _ h₁,
    (isOpenEmbedding_chart hV).isOpenMap _ h₂, ⟨φ, hφ, rfl⟩, ⟨ψ, hψ, rfl⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨φ', hφ', rfl⟩ ⟨ψ', hψ', he⟩
  have : (φ', ψ') ∈ {x : Points K Γ(X, U) × Points K Γ(X, V) | chart hU x.1 = chart hV x.2}ᶜ :=
    hN ⟨hφ', hψ'⟩
  exact this he.symm

end SchemePoints

end SGA.SGA1.ExposeXII
