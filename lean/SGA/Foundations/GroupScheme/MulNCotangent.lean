/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Ideal.Cotangent
import SGA.Foundations.GroupScheme.LocalEndomorphism
import SGA.Foundations.GroupScheme.Points

/-!
# Multiplication by `n` on the cotangent space of a monoid scheme

Let `A` be a monoid scheme over a field `k` (a monoid object in schemes over `Spec k`), `0` its
unit section, `𝒪 = 𝒪_{A,0}` with maximal ideal `𝔪`. Multiplication by `n`, `x ↦ xⁿ`, fixes `0`;
we show that its stalk map at `0` acts on the cotangent space `𝔪/𝔪²` as multiplication by `n`:
`[n]^♯ t - n t ∈ 𝔪²` for `t ∈ 𝔪` (`GroupScheme.powStalkEnd_sub_mem_sq`). Consequently, for `n`
invertible in `k` (and `A` locally noetherian), `[n]^♯` maps `𝔪` onto generators of `𝔪`
(`GroupScheme.map_maximalIdeal_stalkEnd_pow`) and is injective
(`GroupScheme.injective_stalkEnd_pow`); see `LocalEndomorphism`.

The proof is the infinitesimal Eckmann–Hilton argument, with points instead of the local ring of
`A ×ₖ A`. The points of `A` with values in the dual numbers `k[ε]` lying over `0` form a monoid
`T₀` (the tangent space), and `v ↦ D_v`, the derivation `𝒪 → k` underlying `v`, turns the
product into a sum (`GroupScheme.tangentDeriv_mul`): for `v, w ∈ T₀` consider the point
`c = v(ε₁) · w(ε₂)` with values in `k[ε₁, ε₂] = k ⊕ k²`; restricting `c` to the two axes gives
`v` and `w`, and restricting it to the diagonal gives `v · w`. Since `[n] ∘ v = vⁿ`, `[n]^♯` acts on
the derivations as multiplication by `n`, and derivations separate the points of `𝔪/𝔪²`.

Points `Spec C ⟶ X` with `C` local are described by a point `x` and a local homomorphism
`𝒪_{X,x} ⟶ C` (mathlib's `SpecToEquivOfLocalRing`; `Scheme.specPt` in `Points`).

References: Mumford, *Abelian varieties*, §4; Milne, *Abelian varieties*, Thm. 7.2; SGA 3 II 3.
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing

namespace AlgebraicGeometry.GroupScheme

section Origin

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [MonObj A]

/-- The origin of a monoid scheme `A` over `k`, as a point of the underlying space. -/
noncomputable def originPt : A.left := (η[A].left : Spec (.of k) ⟶ A.left) (closedPoint k)

/-- Evaluation at the origin, `𝒪_{A,0} ⟶ k`. -/
noncomputable def evalOrigin : A.left.presheaf.stalk (originPt A) ⟶ CommRingCat.of k :=
  Scheme.stalkClosedPointTo (η[A].left : Spec (.of k) ⟶ A.left)

instance : IsLocalHom (evalOrigin A).hom :=
  inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo _).hom)

lemma specPt_evalOrigin :
    Scheme.specPt (originPt A) (evalOrigin A) = (η[A].left : Spec (.of k) ⟶ A.left) :=
  Scheme.specPt_stalkClosedPointTo _

/-- The `k`-algebra structure of `𝒪_{A,0}`. -/
noncomputable abbrev originAlgebraMap : CommRingCat.of k ⟶ A.left.presheaf.stalk (originPt A) :=
  A.hom.stalkAlgebraMap (originPt A)

lemma specPt_comp_hom {C : CommRingCat.{u}} (f : A.left.presheaf.stalk (originPt A) ⟶ C) :
    Scheme.specPt (originPt A) f ≫ A.hom = Spec.map (originAlgebraMap A ≫ f) :=
  Scheme.specPt_comp_eq_specMap A.hom _ f

lemma originAlgebraMap_comp_evalOrigin : originAlgebraMap A ≫ evalOrigin A = 𝟙 _ := by
  rw [← Spec.map_inj, ← specPt_comp_hom, specPt_evalOrigin, Spec.map_id]
  exact Over.w η[A]

variable (k) in
/-- `Spec C` as a scheme over `k`, for a `k`-algebra `C`. -/
noncomputable abbrev specOver (C : Type u) [CommRing C] [Algebra k C] : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k C)))

/-- The morphism of `k`-schemes `Spec C' ⟶ Spec C` given by a `k`-algebra map `C →ₐ[k] C'`. -/
noncomputable def specOverMap {C C' : Type u} [CommRing C] [CommRing C'] [Algebra k C]
    [Algebra k C'] (φ : C →ₐ[k] C') : specOver k C' ⟶ specOver k C :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    dsimp
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact φ.commutes a)

lemma specOverMap_left {C C' : Type u} [CommRing C] [CommRing C'] [Algebra k C]
    [Algebra k C'] (φ : C →ₐ[k] C') :
    (specOverMap φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) :=
  rfl

lemma specOverMap_comp {C C' C'' : Type u} [CommRing C] [CommRing C'] [CommRing C'']
    [Algebra k C] [Algebra k C'] [Algebra k C''] (φ : C →ₐ[k] C') (φ' : C' →ₐ[k] C'') :
    specOverMap φ' ≫ specOverMap φ = specOverMap (φ'.comp φ) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, specOverMap_left, specOverMap_left, specOverMap_left, ← Spec.map_comp]
  rfl

lemma specOverMap_id (C : Type u) [CommRing C] [Algebra k C] :
    specOverMap (AlgHom.id k C) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  rw [specOverMap_left, Over.id_left]
  exact Spec.map_id _

/-- The `k`-point of `Spec C` given by an augmentation `C →ₐ[k] k`. -/
noncomputable def specOverPt {C : Type u} [CommRing C] [Algebra k C] (π : C →ₐ[k] k) :
    𝟙_ (Over (Spec (.of k))) ⟶ specOver k C :=
  Over.homMk (Spec.map (CommRingCat.ofHom π.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact π.commutes a)

end Origin

section PointsOverOrigin

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [MonObj A]
  {C : Type u} [CommRing C] [Algebra k C] [IsLocalRing C]

variable {A} in
/-- A point `v : Spec C ⟶ A` over `k` with `v ∘ π = 0` (for an augmentation `π : C → k`) maps
the closed point of `Spec C` to the origin. -/
lemma left_closedPoint_eq {π : C →ₐ[k] k} [IsLocalHom π.toRingHom] {v : specOver k C ⟶ A}
    (hv : specOverPt π ≫ v = η[A]) : v.left (closedPoint C) = originPt A := by
  have h₁ : Spec.map (CommRingCat.ofHom π.toRingHom) (closedPoint k) = closedPoint C :=
    Spec_closedPoint (f := CommRingCat.ofHom π.toRingHom)
  rw [← h₁]
  exact congrArg (fun f : 𝟙_ (Over (Spec (.of k))) ⟶ A ↦ f.left (closedPoint k)) hv

/-- The homomorphism `𝒪_{A,0} ⟶ C` underlying a point `v : Spec C ⟶ A` through the origin. -/
noncomputable def pointStalkHom (v : specOver k C ⟶ A) (hv : v.left (closedPoint C) = originPt A) :
    A.left.presheaf.stalk (originPt A) ⟶ CommRingCat.of C :=
  eqToHom (by rw [hv]) ≫ Scheme.stalkClosedPointTo v.left

instance (v : specOver k C ⟶ A) (hv : v.left (closedPoint C) = originPt A) :
    IsLocalHom (pointStalkHom A v hv).hom := by
  have : IsLocalHom (eqToHom (congrArg A.left.presheaf.stalk hv.symm)).hom :=
    isLocalHom_of_isIso _
  rw [pointStalkHom, CommRingCat.hom_comp]
  infer_instance

lemma left_eq_specPt (v : specOver k C ⟶ A) (hv : v.left (closedPoint C) = originPt A) :
    v.left = Scheme.specPt (originPt A) (pointStalkHom A v hv) := by
  rw [pointStalkHom, ← Scheme.specPt_congr hv]
  exact (Scheme.specPt_stalkClosedPointTo _).symm

lemma pointStalkHom_eq {v : specOver k C ⟶ A} (hv : v.left (closedPoint C) = originPt A)
    (f : A.left.presheaf.stalk (originPt A) ⟶ CommRingCat.of C) [IsLocalHom f.hom]
    (h : v.left = Scheme.specPt (originPt A) f) : pointStalkHom A v hv = f :=
  Scheme.specPt_injective ((left_eq_specPt A v hv).symm.trans h)

lemma pointStalkHom_congr {v v' : specOver k C ⟶ A} (h : v = v')
    (hv : v.left (closedPoint C) = originPt A) (hv' : v'.left (closedPoint C) = originPt A) :
    pointStalkHom A v hv = pointStalkHom A v' hv' := by
  subst h
  rfl

lemma specOverMap_comp_closedPoint {C' : Type u} [CommRing C'] [Algebra k C'] [IsLocalRing C']
    (φ : C →ₐ[k] C') [IsLocalHom φ.toRingHom] {v : specOver k C ⟶ A}
    (hv : v.left (closedPoint C) = originPt A) :
    (specOverMap φ ≫ v).left (closedPoint C') = originPt A := by
  rw [Over.comp_left, left_eq_specPt A v hv, specOverMap_left, Scheme.specMap_comp_specPt]
  have : IsLocalHom (pointStalkHom A v hv ≫ CommRingCat.ofHom φ.toRingHom).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.isLocalHom_comp _ _
  exact Scheme.specPt_closedPoint _ _

lemma pointStalkHom_specOverMap {C' : Type u} [CommRing C'] [Algebra k C'] [IsLocalRing C']
    (φ : C →ₐ[k] C') [IsLocalHom φ.toRingHom] (v : specOver k C ⟶ A)
    (hv : v.left (closedPoint C) = originPt A) :
    pointStalkHom A (specOverMap φ ≫ v) (specOverMap_comp_closedPoint A φ hv) =
      pointStalkHom A v hv ≫ CommRingCat.ofHom φ.toRingHom := by
  have : IsLocalHom (pointStalkHom A v hv ≫ CommRingCat.ofHom φ.toRingHom).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.isLocalHom_comp _ _
  refine pointStalkHom_eq A _ _ ?_
  rw [Over.comp_left, left_eq_specPt A v hv, specOverMap_left, Scheme.specMap_comp_specPt]

/-- The endomorphism of `𝒪_{A,0}` induced by an endomorphism `g` of `A` fixing the origin. -/
noncomputable def stalkEnd (g : A ⟶ A) (hg : g.left (originPt A) = originPt A) :
    A.left.presheaf.stalk (originPt A) ⟶ A.left.presheaf.stalk (originPt A) :=
  eqToHom (by rw [hg]) ≫ g.left.stalkMap (originPt A)

instance (g : A ⟶ A) (hg : g.left (originPt A) = originPt A) :
    IsLocalHom (stalkEnd A g hg).hom := by
  have : IsLocalHom (eqToHom (congrArg A.left.presheaf.stalk hg.symm)).hom :=
    isLocalHom_of_isIso _
  rw [stalkEnd, CommRingCat.hom_comp]
  infer_instance

lemma comp_closedPoint (g : A ⟶ A) (hg : g.left (originPt A) = originPt A)
    {v : specOver k C ⟶ A} (hv : v.left (closedPoint C) = originPt A) :
    (v ≫ g).left (closedPoint C) = originPt A := by
  change g.left (v.left (closedPoint C)) = _
  rw [hv, hg]

lemma pointStalkHom_comp (g : A ⟶ A) (hg : g.left (originPt A) = originPt A)
    (v : specOver k C ⟶ A) (hv : v.left (closedPoint C) = originPt A) :
    pointStalkHom A (v ≫ g) (comp_closedPoint A g hg hv) =
      stalkEnd A g hg ≫ pointStalkHom A v hv := by
  have : IsLocalHom (stalkEnd A g hg ≫ pointStalkHom A v hv).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.isLocalHom_comp _ _
  refine pointStalkHom_eq A _ _ ?_
  rw [Over.comp_left, left_eq_specPt A v hv, Scheme.specPt_comp, Scheme.specPt_congr hg, stalkEnd,
    Category.assoc]

end PointsOverOrigin

section Tangent

variable {k : Type u} [Field k]

attribute [local instance] TrivSqZeroExt.isLocalRing_of_field TrivSqZeroExt.isLocalHom_fstHom
  TrivSqZeroExt.isLocalHom_map

variable (A : Over (Spec (.of k))) [MonObj A]

/-- The tangent vectors of `A` at the origin with values in `M`: the points with values in
`k ⊕ M` (`M² = 0`) lying over the origin. -/
def TangentAt (M : Type u) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M] :
    Submonoid (specOver k (TrivSqZeroExt k M) ⟶ A) where
  carrier := {v | specOverPt (TrivSqZeroExt.fstHom k k M) ≫ v = η[A]}
  mul_mem' {v w} hv hw := by
    simp only [Set.mem_ofPred_eq] at hv hw ⊢
    rw [MonObj.comp_mul, hv, hw, MonObj.one_eq_one, _root_.mul_one]
  one_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [MonObj.comp_one, MonObj.one_eq_one]

variable {A}

lemma TangentAt.closedPoint_eq {M : Type u} [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
    [IsCentralScalar k M] {v : specOver k (TrivSqZeroExt k M) ⟶ A} (hv : v ∈ TangentAt A M) :
    v.left (closedPoint (TrivSqZeroExt k M)) = originPt A :=
  left_closedPoint_eq hv

/-- The derivation `𝒪_{A,0} → M` underlying a tangent vector. -/
noncomputable def tangentDeriv {M : Type u} [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
    [IsCentralScalar k M] (v : specOver k (TrivSqZeroExt k M) ⟶ A) (hv : v ∈ TangentAt A M)
    (t : A.left.presheaf.stalk (originPt A)) : M :=
  ((pointStalkHom A v (TangentAt.closedPoint_eq hv)).hom t).snd

lemma tangentDeriv_congr {M : Type u} [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
    [IsCentralScalar k M] {v v' : specOver k (TrivSqZeroExt k M) ⟶ A} (h : v = v')
    (hv : v ∈ TangentAt A M) (hv' : v' ∈ TangentAt A M) :
    tangentDeriv v hv = tangentDeriv v' hv' := by
  subst h
  rfl

/-- The `k`-point `Spec k ⟶ Spec (k ⊕ M) ⟶ Spec k ⟶ Spec (k ⊕ M)` is `x ↦ (fst x, 0)`. -/
lemma specOverMap_map_zero (M N : Type u) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
    [IsCentralScalar k M] [AddCommGroup N] [Module k N] [Module kᵐᵒᵖ N] [IsCentralScalar k N] :
    specOverMap (TrivSqZeroExt.map (0 : M →ₗ[k] N)) =
      toUnit _ ≫ specOverPt (TrivSqZeroExt.fstHom k k M) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.toUnit_left, specOverMap_left]
  change _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext x <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

private lemma specOverPt_comp_specOverMap (M N : Type u) [AddCommGroup M] [Module k M]
    [Module kᵐᵒᵖ M] [IsCentralScalar k M] [AddCommGroup N] [Module k N] [Module kᵐᵒᵖ N]
    [IsCentralScalar k N] (f : M →ₗ[k] N) :
    specOverPt (TrivSqZeroExt.fstHom k k N) ≫ specOverMap (TrivSqZeroExt.map f) =
      specOverPt (TrivSqZeroExt.fstHom k k M) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, specOverMap_left]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext x
  simp

private lemma specOverMap_comp_specOverMap {M N P : Type u} [AddCommGroup M] [Module k M]
    [Module kᵐᵒᵖ M] [IsCentralScalar k M] [AddCommGroup N] [Module k N] [Module kᵐᵒᵖ N]
    [IsCentralScalar k N] [AddCommGroup P] [Module k P] [Module kᵐᵒᵖ P] [IsCentralScalar k P]
    (f : M →ₗ[k] N) (g : N →ₗ[k] P) :
    specOverMap (TrivSqZeroExt.map g) ≫ specOverMap (TrivSqZeroExt.map f) =
      specOverMap (TrivSqZeroExt.map (g ∘ₗ f)) := by
  rw [specOverMap_comp, TrivSqZeroExt.map_comp_map]

private lemma specOverMap_map_id (M : Type u) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
    [IsCentralScalar k M] : specOverMap (TrivSqZeroExt.map (LinearMap.id : M →ₗ[k] M)) = 𝟙 _ := by
  rw [TrivSqZeroExt.map_id, specOverMap_id]

/-- The infinitesimal Eckmann–Hilton argument: on tangent vectors at the origin, the product of
`A` is the sum of derivations. -/
theorem tangentDeriv_mul {v w : specOver k (TrivSqZeroExt k k) ⟶ A} (hv : v ∈ TangentAt A k)
    (hw : w ∈ TangentAt A k) (t : A.left.presheaf.stalk (originPt A)) :
    tangentDeriv (v * w) ((TangentAt A k).mul_mem hv hw) t =
      tangentDeriv v hv t + tangentDeriv w hw t := by
  let I₁ := specOverMap (TrivSqZeroExt.map (LinearMap.inl k k k))
  let I₂ := specOverMap (TrivSqZeroExt.map (LinearMap.inr k k k))
  let Q₁ := specOverMap (TrivSqZeroExt.map (LinearMap.fst k k k))
  let Q₂ := specOverMap (TrivSqZeroExt.map (LinearMap.snd k k k))
  let Δ := specOverMap (TrivSqZeroExt.map (LinearMap.fst k k k + LinearMap.snd k k k))
  let c := (I₁ ≫ v) * (I₂ ≫ w)
  have hv' : specOverPt (TrivSqZeroExt.fstHom k k k) ≫ v = η[A] := hv
  have hw' : specOverPt (TrivSqZeroExt.fstHom k k k) ≫ w = η[A] := hw
  have hc : c ∈ TangentAt A (k × k) := by
    change specOverPt _ ≫ c = η[A]
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specOverPt_comp_specOverMap,
      specOverPt_comp_specOverMap, hv', hw', MonObj.one_eq_one, _root_.mul_one]
  have hz (u : specOver k (TrivSqZeroExt k k) ⟶ A)
      (hu : specOverPt (TrivSqZeroExt.fstHom k k k) ≫ u = η[A]) :
      specOverMap (TrivSqZeroExt.map (0 : k →ₗ[k] k)) ≫ u = 1 := by
    rw [specOverMap_map_zero, Category.assoc, hu, Hom.one_def]
  have h₁ : Q₁ ≫ c = v := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specOverMap_comp_specOverMap,
      specOverMap_comp_specOverMap, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr,
      specOverMap_map_id, Category.id_comp, hz w hw', _root_.mul_one]
  have h₂ : Q₂ ≫ c = w := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specOverMap_comp_specOverMap,
      specOverMap_comp_specOverMap, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr,
      specOverMap_map_id, Category.id_comp, hz v hv', _root_.one_mul]
  have h₃ : Δ ≫ c = v * w := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, specOverMap_comp_specOverMap,
      specOverMap_comp_specOverMap, LinearMap.add_comp, LinearMap.add_comp,
      LinearMap.fst_comp_inl, LinearMap.snd_comp_inl, LinearMap.fst_comp_inr,
      LinearMap.snd_comp_inr, add_zero, zero_add, specOverMap_map_id, Category.id_comp,
      Category.id_comp]
  have hc' := TangentAt.closedPoint_eq hc
  have key (f : k × k →ₗ[k] k) (u : specOver k (TrivSqZeroExt k k) ⟶ A)
      (hu : u ∈ TangentAt A k) (h : specOverMap (TrivSqZeroExt.map f) ≫ c = u) :
      tangentDeriv u hu t = f ((pointStalkHom A c hc').hom t).snd := by
    rw [← tangentDeriv_congr h (by rw [h]; exact hu) hu, tangentDeriv,
      pointStalkHom_congr A rfl _ (specOverMap_comp_closedPoint A _ hc'),
      pointStalkHom_specOverMap A _ c hc']
    simp
  rw [key _ v hv h₁, key _ w hw h₂, key _ _ _ h₃]
  simp

lemma origin_comp_closedPoint (g : A ⟶ A) (hg : η[A] ≫ g = η[A]) :
    g.left (originPt A) = originPt A :=
  congrArg (fun f : 𝟙_ (Over (Spec (.of k))) ⟶ A ↦ f.left (closedPoint k)) hg

lemma comp_mem_tangentAt {M : Type u} [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
    [IsCentralScalar k M] {v : specOver k (TrivSqZeroExt k M) ⟶ A} (hv : v ∈ TangentAt A M)
    (g : A ⟶ A) (hg : η[A] ≫ g = η[A]) : v ≫ g ∈ TangentAt A M := by
  change specOverPt _ ≫ v ≫ g = η[A]
  rw [← Category.assoc, show specOverPt _ ≫ v = η[A] from hv, hg]

/-- An endomorphism `g` of `A` fixing the origin acts on tangent vectors through its stalk map. -/
theorem tangentDeriv_comp {M : Type u} [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
    [IsCentralScalar k M] {v : specOver k (TrivSqZeroExt k M) ⟶ A} (hv : v ∈ TangentAt A M)
    (g : A ⟶ A) (hg : η[A] ≫ g = η[A]) (t : A.left.presheaf.stalk (originPt A)) :
    tangentDeriv (v ≫ g) (comp_mem_tangentAt hv g hg) t =
      tangentDeriv v hv ((stalkEnd A g (origin_comp_closedPoint g hg)).hom t) := by
  rw [tangentDeriv, tangentDeriv, pointStalkHom_congr A rfl _
    (comp_closedPoint A g (origin_comp_closedPoint g hg) (TangentAt.closedPoint_eq hv)),
    pointStalkHom_comp, CommRingCat.hom_comp, RingHom.comp_apply]

lemma pow_mem_tangentAt {v : specOver k (TrivSqZeroExt k k) ⟶ A} (hv : v ∈ TangentAt A k)
    (n : ℕ) : v ^ n ∈ TangentAt A k :=
  (TangentAt A k).pow_mem hv n

/-- The constant tangent vector has derivation `0`. -/
theorem tangentDeriv_one (t : A.left.presheaf.stalk (originPt A)) :
    tangentDeriv 1 ((TangentAt A k).one_mem) t = 0 := by
  have : IsLocalHom (algebraMap k (TrivSqZeroExt k k)) := TrivSqZeroExt.isLocalHom_algebraMap k
  have : IsLocalHom (evalOrigin A ≫ CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k k))).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.isLocalHom_comp _ _
  rw [tangentDeriv, pointStalkHom_eq A _ (evalOrigin A ≫
    CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k k)))]
  · simp [TrivSqZeroExt.algebraMap_eq_inl]
  · rw [Hom.one_def, Over.comp_left, Over.toUnit_left, ← specPt_evalOrigin]
    exact Scheme.specMap_comp_specPt _ _ _

theorem tangentDeriv_pow {v : specOver k (TrivSqZeroExt k k) ⟶ A} (hv : v ∈ TangentAt A k)
    (n : ℕ) (t : A.left.presheaf.stalk (originPt A)) :
    tangentDeriv (v ^ n) (pow_mem_tangentAt hv n) t = n • tangentDeriv v hv t := by
  induction n with
  | zero =>
    rw [tangentDeriv_congr (pow_zero v) _ ((TangentAt A k).one_mem), zero_smul, tangentDeriv_one]
  | succ n ih =>
    rw [tangentDeriv_congr (pow_succ v n) _ ((TangentAt A k).mul_mem (pow_mem_tangentAt hv n) hv),
      tangentDeriv_mul (pow_mem_tangentAt hv n) hv, ih, succ_nsmul]

lemma eta_comp_pow {n : ℕ} : η[A] ≫ (𝟙 A) ^ n = η[A] := by
  rw [MonObj.comp_pow, Category.comp_id, MonObj.one_eq_one, one_pow]

/-- Multiplication by `n` acts on tangent vectors at the origin as multiplication by `n`. -/
theorem tangentDeriv_stalkEnd_pow {v : specOver k (TrivSqZeroExt k k) ⟶ A}
    (hv : v ∈ TangentAt A k) (n : ℕ) (t : A.left.presheaf.stalk (originPt A)) :
    tangentDeriv v hv ((stalkEnd A ((𝟙 A) ^ n) (origin_comp_closedPoint _ eta_comp_pow)).hom t) =
      n • tangentDeriv v hv t := by
  rw [← tangentDeriv_comp hv _ eta_comp_pow, ← tangentDeriv_pow hv n t]
  apply congrFun
  apply tangentDeriv_congr
  rw [MonObj.comp_pow, Category.comp_id]

end Tangent

section Cotangent

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [MonObj A]

attribute [local instance] TrivSqZeroExt.isLocalRing_of_field TrivSqZeroExt.isLocalHom_fstHom

/-- The local ring `𝒪_{A,0}` of `A` at the origin. -/
noncomputable abbrev originStalk : CommRingCat.{u} := A.left.presheaf.stalk (originPt A)

lemma evalOrigin_originAlgebraMap (a : k) :
    (evalOrigin A).hom ((originAlgebraMap A).hom a) = a := by
  rw [← CommRingCat.comp_apply, originAlgebraMap_comp_evalOrigin]
  rfl

lemma evalOrigin_eq_zero {t : originStalk A} (ht : t ∈ maximalIdeal (originStalk A)) :
    (evalOrigin A).hom t = 0 := by
  by_contra h
  exact ht ((isUnit_map_iff (evalOrigin A).hom t).mp (isUnit_iff_ne_zero.mpr h))

lemma sub_originAlgebraMap_mem (r : originStalk A) :
    r - (originAlgebraMap A).hom ((evalOrigin A).hom r) ∈ maximalIdeal (originStalk A) := by
  intro h
  have := (h.map (evalOrigin A).hom).ne_zero
  rw [map_sub, evalOrigin_originAlgebraMap, sub_self] at this
  exact this rfl

/-- The class `[r - r(0)]` of `r ∈ 𝒪_{A,0}` in the cotangent space `𝔪/𝔪²`. -/
noncomputable def cotangentClass (r : originStalk A) : CotangentSpace (originStalk A) :=
  (maximalIdeal (originStalk A)).toCotangent ⟨_, sub_originAlgebraMap_mem A r⟩

lemma cotangentClass_of_mem {t : originStalk A} (ht : t ∈ maximalIdeal (originStalk A)) :
    cotangentClass A t = (maximalIdeal (originStalk A)).toCotangent ⟨t, ht⟩ := by
  rw [cotangentClass]
  congr 2
  rw [evalOrigin_eq_zero A ht, map_zero, sub_zero]

lemma cotangentClass_add (r s : originStalk A) :
    cotangentClass A (r + s) = cotangentClass A r + cotangentClass A s := by
  rw [cotangentClass, cotangentClass, cotangentClass, ← map_add]
  congr 1
  ext
  simp only [map_add, Submodule.coe_add]
  ring

lemma cotangentClass_algebraMap (a : k) : cotangentClass A ((originAlgebraMap A).hom a) = 0 := by
  rw [cotangentClass, Ideal.toCotangent_eq_zero]
  change (originAlgebraMap A).hom a - (originAlgebraMap A).hom
    ((evalOrigin A).hom ((originAlgebraMap A).hom a)) ∈ maximalIdeal (originStalk A) ^ 2
  rw [evalOrigin_originAlgebraMap, sub_self]
  exact zero_mem _

lemma cotangentClass_mul (r s : originStalk A) :
    cotangentClass A (r * s) =
      residue _ r • cotangentClass A s + residue _ s • cotangentClass A r := by
  set σ := (originAlgebraMap A).hom
  set ε := (evalOrigin A).hom
  have hres : residue (originStalk A) (σ (ε s)) = residue (originStalk A) s :=
    ((Ideal.Quotient.eq).mpr (sub_originAlgebraMap_mem A s)).symm
  have e1 : residue (originStalk A) r • cotangentClass A s = r • cotangentClass A s :=
    algebraMap_smul (ResidueField (originStalk A)) r _
  have e2 : residue (originStalk A) s • cotangentClass A r = σ (ε s) • cotangentClass A r := by
    rw [← hres]
    exact algebraMap_smul (ResidueField (originStalk A)) _ _
  rw [e1, e2, cotangentClass, cotangentClass, cotangentClass, ← map_smul, ← map_smul, ← map_add]
  congr 1
  ext
  simp only [map_mul, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
  ring

/-- The residue field of `𝒪_{A,0}` is `k`. -/
noncomputable def residueToField : ResidueField (originStalk A) →+* k :=
  ResidueField.lift (evalOrigin A).hom

lemma residueToField_residue (r : originStalk A) :
    residueToField A (residue _ r) = (evalOrigin A).hom r :=
  ResidueField.lift_residue_apply _ _

variable {A} in
/-- `r ↦ r(0) + ℓ([r - r(0)]) ε`. -/
noncomputable def cotangentPointFun (ℓ : Module.Dual (ResidueField (originStalk A))
    (CotangentSpace (originStalk A))) (r : originStalk A) : TrivSqZeroExt k k :=
  TrivSqZeroExt.inl ((evalOrigin A).hom r) +
    TrivSqZeroExt.inr (residueToField A (ℓ (cotangentClass A r)))

section CotangentPointFun

variable {A} (ℓ : Module.Dual (ResidueField (originStalk A)) (CotangentSpace (originStalk A)))

lemma fst_cotangentPointFun (r : originStalk A) :
    (cotangentPointFun ℓ r).fst = (evalOrigin A).hom r := by
  simp [cotangentPointFun]

lemma snd_cotangentPointFun (r : originStalk A) :
    (cotangentPointFun ℓ r).snd = residueToField A (ℓ (cotangentClass A r)) := by
  simp [cotangentPointFun]

lemma cotangentPointFun_one : cotangentPointFun ℓ 1 = 1 := by
  have h1 : cotangentClass A 1 = 0 := by
    simpa using cotangentClass_algebraMap A 1
  ext
  · rw [fst_cotangentPointFun, map_one, TrivSqZeroExt.fst_one]
  · rw [snd_cotangentPointFun, h1, map_zero, map_zero, TrivSqZeroExt.snd_one]

lemma cotangentPointFun_zero : cotangentPointFun ℓ 0 = 0 := by
  have h0 : cotangentClass A 0 = 0 := by
    simpa using cotangentClass_algebraMap A 0
  ext
  · rw [fst_cotangentPointFun, map_zero, TrivSqZeroExt.fst_zero]
  · rw [snd_cotangentPointFun, h0, map_zero, map_zero, TrivSqZeroExt.snd_zero]

lemma cotangentPointFun_mul (r s : originStalk A) :
    cotangentPointFun ℓ (r * s) = cotangentPointFun ℓ r * cotangentPointFun ℓ s := by
  ext
  · rw [fst_cotangentPointFun, map_mul, TrivSqZeroExt.fst_mul, fst_cotangentPointFun,
      fst_cotangentPointFun]
  · rw [snd_cotangentPointFun, TrivSqZeroExt.snd_mul, fst_cotangentPointFun,
      fst_cotangentPointFun, snd_cotangentPointFun, snd_cotangentPointFun, cotangentClass_mul,
      map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
      residueToField_residue, residueToField_residue, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    ring

lemma cotangentPointFun_add (r s : originStalk A) :
    cotangentPointFun ℓ (r + s) = cotangentPointFun ℓ r + cotangentPointFun ℓ s := by
  ext
  · rw [fst_cotangentPointFun, map_add, TrivSqZeroExt.fst_add, fst_cotangentPointFun,
      fst_cotangentPointFun]
  · rw [snd_cotangentPointFun, TrivSqZeroExt.snd_add, snd_cotangentPointFun,
      snd_cotangentPointFun, cotangentClass_add, map_add, map_add]

end CotangentPointFun

/-- The point of `A` with values in `k[ε]` given by a linear form `ℓ` on `𝔪/𝔪²`:
`r ↦ r(0) + ℓ([r - r(0)]) ε`. -/
noncomputable def cotangentPointHom (ℓ : Module.Dual (ResidueField (originStalk A))
    (CotangentSpace (originStalk A))) : originStalk A ⟶ CommRingCat.of (TrivSqZeroExt k k) :=
  CommRingCat.ofHom
  { toFun := cotangentPointFun ℓ
    map_one' := cotangentPointFun_one ℓ
    map_mul' := cotangentPointFun_mul ℓ
    map_zero' := cotangentPointFun_zero ℓ
    map_add' := cotangentPointFun_add ℓ }

variable {A} in
lemma fst_cotangentPointHom (ℓ : Module.Dual (ResidueField (originStalk A))
    (CotangentSpace (originStalk A))) (r : originStalk A) :
    ((cotangentPointHom A ℓ).hom r).fst = (evalOrigin A).hom r :=
  fst_cotangentPointFun ℓ r

variable {A} in
lemma snd_cotangentPointHom (ℓ : Module.Dual (ResidueField (originStalk A))
    (CotangentSpace (originStalk A))) (r : originStalk A) :
    ((cotangentPointHom A ℓ).hom r).snd = residueToField A (ℓ (cotangentClass A r)) :=
  snd_cotangentPointFun ℓ r

instance isLocalHom_cotangentPointHom
    (ℓ : Module.Dual (ResidueField (originStalk A)) (CotangentSpace (originStalk A))) :
    IsLocalHom (cotangentPointHom A ℓ).hom :=
  ⟨fun r hr ↦ by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, fst_cotangentPointHom] at hr
    exact (isUnit_map_iff _ r).mp hr⟩

lemma originAlgebraMap_comp_cotangentPointHom
    (ℓ : Module.Dual (ResidueField (originStalk A)) (CotangentSpace (originStalk A))) :
    originAlgebraMap A ≫ cotangentPointHom A ℓ =
      CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k k)) := by
  ext a
  · rw [CommRingCat.comp_apply, fst_cotangentPointHom, evalOrigin_originAlgebraMap]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  · rw [CommRingCat.comp_apply, snd_cotangentPointHom, cotangentClass_algebraMap]
    simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- The tangent vector at the origin given by a linear form `ℓ` on `𝔪/𝔪²`. -/
noncomputable def cotangentPoint
    (ℓ : Module.Dual (ResidueField (originStalk A)) (CotangentSpace (originStalk A))) :
    specOver k (TrivSqZeroExt k k) ⟶ A :=
  Over.homMk (Scheme.specPt (originPt A) (cotangentPointHom A ℓ)) (by
    rw [specPt_comp_hom, originAlgebraMap_comp_cotangentPointHom]
    rfl)

lemma cotangentPoint_mem
    (ℓ : Module.Dual (ResidueField (originStalk A)) (CotangentSpace (originStalk A))) :
    cotangentPoint A ℓ ∈ TangentAt A k := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Scheme.specPt _ _ = (η[A].left : Spec (.of k) ⟶ A.left)
  rw [Scheme.specMap_comp_specPt, ← specPt_evalOrigin]
  congr 1
  ext r
  exact fst_cotangentPointHom ℓ r

lemma tangentDeriv_cotangentPoint
    (ℓ : Module.Dual (ResidueField (originStalk A)) (CotangentSpace (originStalk A)))
    (t : originStalk A) :
    tangentDeriv (cotangentPoint A ℓ) (cotangentPoint_mem A ℓ) t =
      residueToField A (ℓ (cotangentClass A t)) := by
  rw [tangentDeriv, pointStalkHom_eq A _ (cotangentPointHom A ℓ) rfl]
  exact snd_cotangentPointHom ℓ t

/-- `r ↦ [r - r(0)]`, as an additive map `𝒪_{A,0} → 𝔪/𝔪²`. -/
noncomputable def cotangentClassHom : originStalk A →+ CotangentSpace (originStalk A) where
  toFun := cotangentClass A
  map_zero' := by simpa using cotangentClass_algebraMap A 0
  map_add' := cotangentClass_add A

/-- Multiplication by `n` on a monoid scheme `A` over a field acts on the cotangent space at the
origin as multiplication by `n`: `[n]^♯ t - n t ∈ 𝔪²` for every `t` in the maximal ideal `𝔪` of
`𝒪_{A,0}`. -/
theorem powStalkEnd_sub_mem_sq (n : ℕ) {t : originStalk A}
    (ht : t ∈ maximalIdeal (originStalk A)) :
    (stalkEnd A ((𝟙 A) ^ n) (origin_comp_closedPoint _ eta_comp_pow)).hom t - n * t ∈
      maximalIdeal (originStalk A) ^ 2 := by
  set φ := (stalkEnd A ((𝟙 A) ^ n) (origin_comp_closedPoint _ eta_comp_pow)).hom with hφ
  have hφt : φ t ∈ maximalIdeal (originStalk A) := map_nonunit φ t ht
  have hu : φ t - n * t ∈ maximalIdeal (originStalk A) :=
    sub_mem hφt (Ideal.mul_mem_left _ _ ht)
  rw [← Ideal.toCotangent_eq_zero _ ⟨_, hu⟩, ← cotangentClass_of_mem A hu]
  apply (Module.forall_dual_apply_eq_zero_iff (ResidueField (originStalk A)) _).mp
  intro ℓ
  apply (residueToField A).injective
  have h := tangentDeriv_stalkEnd_pow (cotangentPoint_mem A ℓ) n t
  rw [tangentDeriv_cotangentPoint, tangentDeriv_cotangentPoint] at h
  change residueToField A (ℓ (cotangentClassHom A (φ t - n * t))) = _
  rw [map_sub, ← nsmul_eq_mul, map_nsmul, map_sub, map_nsmul, map_sub, map_nsmul]
  change residueToField A (ℓ (cotangentClass A (φ t))) - _ = _
  rw [h, map_zero]
  simp [cotangentClassHom]

lemma isUnit_natCast_originStalk {n : ℕ} (hn : (n : k) ≠ 0) : IsUnit (n : originStalk A) := by
  rw [← map_natCast (originAlgebraMap A).hom]
  exact (isUnit_iff_ne_zero.mpr hn).map _

variable [IsLocallyNoetherian A.left]

/-- For `n` invertible in `k`, the stalk map of `[n]` at the origin maps `𝔪` onto a generating
set of `𝔪`. -/
theorem map_maximalIdeal_stalkEnd_pow {n : ℕ} (hn : (n : k) ≠ 0) :
    Ideal.map (stalkEnd A ((𝟙 A) ^ n) (origin_comp_closedPoint _ eta_comp_pow)).hom
      (maximalIdeal (originStalk A)) = maximalIdeal (originStalk A) :=
  map_maximalIdeal_eq_of_sub_mul_mem_sq (isUnit_natCast_originStalk A hn)
    fun _ ht ↦ powStalkEnd_sub_mem_sq A n ht

/-- For `n` invertible in `k`, the stalk map of `[n]` at the origin is injective. -/
theorem injective_stalkEnd_pow {n : ℕ} (hn : (n : k) ≠ 0) :
    Function.Injective (stalkEnd A ((𝟙 A) ^ n) (origin_comp_closedPoint _ eta_comp_pow)).hom :=
  injective_of_sub_mul_mem_sq (isUnit_natCast_originStalk A hn)
    fun _ ht ↦ powStalkEnd_sub_mem_sq A n ht

end Cotangent

end AlgebraicGeometry.GroupScheme
