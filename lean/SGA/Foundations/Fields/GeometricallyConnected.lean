/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Jacobson.Ring
import SGA.Foundations.Cohomology.GeometricConnectedness

/-!
# Connected schemes over an algebraically closed field are geometrically connected

Let `k` be an algebraically closed field.

* `IsAlgClosed.exists_algHom_ker_eq`, `IsAlgClosed.nonempty_algHom`,
  `IsAlgClosed.isNilpotent_of_forall_algHom_eq_zero`: Hilbert's Nullstellensatz for a finitely
  generated `k`-algebra `A`, in terms of its `k`-points `A →ₐ[k] k`. (These are the canonical
  copies; `SGA.SGA1.ExposeXII.Points.exists_ker_eq`, the converse half of
  `ExposeXII.Points.nonempty_iff_nontrivial` and
  `ExposeXII.Points.isNilpotent_of_forall_apply_eq_zero` in `SGA/SGA1/ExposeXII/Comparison.lean`
  state the same facts for `Points K A := A →ₐ[K] K`.)
* `AlgebraicGeometry.CohomologyAux.trivialIdempotents_tensorProduct_of_isAlgClosed`: if two
  nonzero `k`-algebras have no idempotents besides `0` and `1`, neither does their tensor product.
  For finitely generated algebras, an idempotent `e` of `R ⊗ₖ S` takes the same value at every
  `k`-point `(x, y)`, since its restrictions to `{x} × Spec S` and to `Spec R × {y}` are
  idempotents of `S` and of `R`; then `e` or `1 - e` lies in every maximal ideal, hence is
  nilpotent (Nullstellensatz). The general case reduces to this one, because `R₀ ⊗ₖ S₀ → R ⊗ₖ S`
  is injective for subalgebras `R₀ ⊆ R`, `S₀ ⊆ S` (`Algebra.TensorProduct.exists_fg_mem_range_map`).
  These lemmas are stated with the predicate `CohomologyAux.TrivialIdempotents` of
  `SGA.Foundations.Cohomology.TrivialIdempotents` and live in its namespace.
* `AlgebraicGeometry.geometricallyConnected_of_isAlgClosed`: every connected `k`-scheme is
  geometrically connected. No finiteness hypothesis is needed: for a field `K ⊇ k`, the
  projection `X_K → X` is flat, quasi-compact and surjective, hence a quotient map, and its
  fibres `Spec (κ(x) ⊗ₖ K)` are connected.
* `AlgebraicGeometry.GeometricallyConnected.connectedSpace_pullback_of_subsingleton`: over a
  one-point base, the product of two geometrically connected schemes is connected (two points `z`,
  `z'` of the product are joined through a point `w` with `pr₁ w = pr₁ z` and `pr₂ w = pr₂ z'`,
  inside the connected fibres of the projections). Hence `X ×ₖ Y` is connected for connected `X`,
  `Y` (`connectedSpace_pullback_of_isAlgClosed_of_connectedSpace`).

These generalize the proper case `SGA.SGA1.ExposeX.connectedSpace_pullback_of_isAlgClosed` and the
finite case `SGA.SGA1.ExposeX.trivialIdempotents_tensor_of_isAlgClosed`
(`SGA/SGA1/ExposeX/ProperOverField.lean`).

## References

* [Stacks Project, Algebra, Section 10.48 (Geometrically connected algebras)]
* [Stacks Project, Varieties, Section 33.7 (Geometrically connected schemes)]
* [EGA IV₂, 4.5]
-/

universe u

open CategoryTheory Limits TensorProduct

namespace IsAlgClosed

variable {k : Type*} [Field k] [IsAlgClosed k] {A : Type*} [CommRing A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- **Hilbert's Nullstellensatz**: a maximal ideal of a finitely generated algebra over an
algebraically closed field `k` is the kernel of a `k`-point. -/
theorem exists_algHom_ker_eq (m : Ideal A) [m.IsMaximal] :
    ∃ φ : A →ₐ[k] k, RingHom.ker φ = m := by
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) (Ideal.Quotient.mkₐ_surjective k m)
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  let e : k ≃ₐ[k] A ⧸ m :=
    AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext a
  simp only [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
    Ideal.Quotient.mkₐ_eq_mk, map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

variable (k A) in
/-- A nonzero finitely generated algebra over an algebraically closed field has a `k`-point. -/
theorem nonempty_algHom [Nontrivial A] : Nonempty (A →ₐ[k] k) :=
  have ⟨m, _⟩ := Ideal.exists_maximal A
  (exists_algHom_ker_eq (k := k) m).nonempty

/-- In a finitely generated algebra over an algebraically closed field, a function vanishing at
every `k`-point is nilpotent (it lies in every maximal ideal, and `A` is a Jacobson ring). -/
theorem isNilpotent_of_forall_algHom_eq_zero {a : A} (h : ∀ φ : A →ₐ[k] k, φ a = 0) :
    IsNilpotent a := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  rw [← mem_nilradical, nilradical, Ideal.radical_eq_jacobson, Ideal.jacobson,
    Submodule.mem_sInf]
  rintro m ⟨-, hm⟩
  obtain ⟨φ, rfl⟩ := exists_algHom_ker_eq (k := k) m
  exact RingHom.mem_ker.mpr (h φ)

end IsAlgClosed

namespace Algebra.TensorProduct

variable {k : Type*} [CommRing k] {R S : Type*} [CommRing R] [CommRing S] [Algebra k R]
  [Algebra k S]

/-- Every element of `R ⊗ₖ S` comes from `R₀ ⊗ₖ S₀` for finitely generated subalgebras
`R₀ ⊆ R`, `S₀ ⊆ S`. -/
theorem exists_fg_mem_range_map (z : R ⊗[k] S) :
    ∃ (R₀ : Subalgebra k R) (S₀ : Subalgebra k S), R₀.FG ∧ S₀.FG ∧
      z ∈ (map R₀.val S₀.val).range := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨⊥, ⊥, Subalgebra.fg_bot, Subalgebra.fg_bot, zero_mem _⟩
  | tmul a b =>
    refine ⟨Algebra.adjoin k {a}, Algebra.adjoin k {b}, ⟨{a}, by simp⟩, ⟨{b}, by simp⟩,
      ⟨⟨a, Algebra.subset_adjoin rfl⟩ ⊗ₜ
        ⟨b, Algebra.subset_adjoin rfl⟩, rfl⟩⟩
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨R₁, S₁, hR₁, hS₁, w₁, rfl⟩ := h₁
    obtain ⟨R₂, S₂, hR₂, hS₂, w₂, rfl⟩ := h₂
    refine ⟨R₁ ⊔ R₂, S₁ ⊔ S₂, hR₁.sup hR₂, hS₁.sup hS₂, ?_⟩
    have hle : ∀ (R' : Subalgebra k R) (S' : Subalgebra k S), R' ≤ R₁ ⊔ R₂ → S' ≤ S₁ ⊔ S₂ →
        (map R'.val S'.val).range ≤ (map (R₁ ⊔ R₂).val (S₁ ⊔ S₂).val).range := by
      rintro R' S' hR hS _ ⟨w, rfl⟩
      refine ⟨map (Subalgebra.inclusion hR) (Subalgebra.inclusion hS) w, ?_⟩
      have : (map (R₁ ⊔ R₂).val (S₁ ⊔ S₂).val).comp
          (map (Subalgebra.inclusion hR) (Subalgebra.inclusion hS)) = map R'.val S'.val := by
        rw [← map_comp]
        rfl
      exact DFunLike.congr_fun this w
    exact add_mem (hle R₁ S₁ le_sup_left le_sup_left ⟨w₁, rfl⟩)
      (hle R₂ S₂ le_sup_right le_sup_right ⟨w₂, rfl⟩)

end Algebra.TensorProduct

namespace AlgebraicGeometry.CohomologyAux

section Ring

variable {k : Type*} [Field k] [IsAlgClosed k]

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- Restriction of a function on `Spec (R ⊗ₖ S)` to the fibre `{x} × Spec S` over a `k`-point `x`
of `Spec R`. -/
private noncomputable abbrev restrictLeft (x : R →ₐ[k] k) : R ⊗[k] S →ₐ[k] S :=
  Algebra.TensorProduct.productMap ((Algebra.ofId k S).comp x) (AlgHom.id k S)

/-- Restriction of a function on `Spec (R ⊗ₖ S)` to the fibre `Spec R × {y}` over a `k`-point `y`
of `Spec S`. -/
private noncomputable abbrev restrictRight (y : S →ₐ[k] k) : R ⊗[k] S →ₐ[k] R :=
  Algebra.TensorProduct.productMap (AlgHom.id k R) ((Algebra.ofId k R).comp y)

omit [IsAlgClosed k] in
private lemma productMap_apply_eq_restrictLeft (x : R →ₐ[k] k) (y : S →ₐ[k] k)
    (z : R ⊗[k] S) : Algebra.TensorProduct.productMap x y z = y (restrictLeft x z) := by
  have : Algebra.TensorProduct.productMap x y = y.comp (restrictLeft x) :=
    Algebra.TensorProduct.ext' fun a b ↦ by simp [Algebra.TensorProduct.productMap_apply_tmul]
  rw [this, AlgHom.comp_apply]

omit [IsAlgClosed k] in
private lemma productMap_apply_eq_restrictRight (x : R →ₐ[k] k) (y : S →ₐ[k] k)
    (z : R ⊗[k] S) : Algebra.TensorProduct.productMap x y z = x (restrictRight y z) := by
  have : Algebra.TensorProduct.productMap x y = x.comp (restrictRight y) :=
    Algebra.TensorProduct.ext' fun a b ↦ by
      simp [Algebra.TensorProduct.productMap_apply_tmul]
  rw [this, AlgHom.comp_apply]

omit [IsAlgClosed k] in
/-- An algebra map sends an element that is `0` or `1` to the same value, whatever the map. -/
private lemma algHom_apply_eq_of_eq_zero_or_one {A : Type*} [CommRing A] [Algebra k A] {a : A}
    (ha : a = 0 ∨ a = 1) (φ ψ : A →ₐ[k] k) : φ a = ψ a := by
  rcases ha with rfl | rfl <;> simp

/-- The finitely generated case of `trivialIdempotents_tensorProduct_of_isAlgClosed`. -/
theorem trivialIdempotents_tensorProduct_of_finiteType [Algebra.FiniteType k R]
    [Algebra.FiniteType k S] [Nontrivial R] [Nontrivial S] (hR : TrivialIdempotents R)
    (hS : TrivialIdempotents S) : TrivialIdempotents (R ⊗[k] S) := by
  have : Algebra.FiniteType k (R ⊗[k] S) := Algebra.FiniteType.trans (S := R) inferInstance
    inferInstance
  intro e he
  obtain ⟨x₀⟩ := IsAlgClosed.nonempty_algHom k R
  obtain ⟨y₀⟩ := IsAlgClosed.nonempty_algHom k S
  -- every `k`-point of `Spec (R ⊗ₖ S)` takes the same value at `e`
  have hconst : ∀ φ : R ⊗[k] S →ₐ[k] k,
      φ e = Algebra.TensorProduct.productMap x₀ y₀ e := by
    intro φ
    let x := φ.comp Algebra.TensorProduct.includeLeft
    let y := φ.comp Algebra.TensorProduct.includeRight
    have hφ : φ = Algebra.TensorProduct.productMap x y :=
      Algebra.TensorProduct.ext' fun a b ↦ by
        rw [Algebra.TensorProduct.productMap_apply_tmul, ← mul_one a, ← one_mul b,
          ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, mul_one, one_mul]
        rfl
    rw [hφ, productMap_apply_eq_restrictLeft,
      algHom_apply_eq_of_eq_zero_or_one (hS _ (he.map (restrictLeft x))) y y₀,
      ← productMap_apply_eq_restrictLeft, productMap_apply_eq_restrictRight,
      algHom_apply_eq_of_eq_zero_or_one (hR _ (he.map (restrictRight y₀))) x x₀,
      ← productMap_apply_eq_restrictRight]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp
      (he.map (Algebra.TensorProduct.productMap x₀ y₀)) with h₀ | h₁
  · exact Or.inl (he.eq_zero_of_isNilpotent
      (IsAlgClosed.isNilpotent_of_forall_algHom_eq_zero (k := k) fun φ ↦ (hconst φ).trans h₀))
  · refine Or.inr (sub_eq_zero.mp (he.one_sub.eq_zero_of_isNilpotent
      (IsAlgClosed.isNilpotent_of_forall_algHom_eq_zero (k := k) fun φ ↦ ?_))).symm
    rw [map_sub, map_one, hconst φ, h₁, sub_self]

omit [IsAlgClosed k] in
/-- A subalgebra of an algebra with only trivial idempotents has only trivial idempotents. -/
theorem TrivialIdempotents.subalgebra (hR : TrivialIdempotents R) (R₀ : Subalgebra k R) :
    TrivialIdempotents R₀ := by
  intro e he
  rcases hR _ (he.map R₀.val) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- **Connectedness of products over an algebraically closed field** (Stacks, Algebra,
Section 10.48): if `R` and `S` are nonzero algebras over an algebraically closed field `k` with
connected spectra (only trivial idempotents), then `Spec (R ⊗ₖ S)` is connected. -/
theorem trivialIdempotents_tensorProduct_of_isAlgClosed [Nontrivial R] [Nontrivial S]
    (hR : TrivialIdempotents R) (hS : TrivialIdempotents S) :
    TrivialIdempotents (R ⊗[k] S) := by
  intro e he
  obtain ⟨R₀, S₀, hR₀, hS₀, e₀, rfl⟩ := Algebra.TensorProduct.exists_fg_mem_range_map e
  have : Algebra.FiniteType k R₀ := (Subalgebra.fg_iff_finiteType R₀).mp hR₀
  have : Algebra.FiniteType k S₀ := (Subalgebra.fg_iff_finiteType S₀).mp hS₀
  have hinj : Function.Injective (Algebra.TensorProduct.map R₀.val S₀.val) :=
    TensorProduct.map_injective_of_flat_flat R₀.val.toLinearMap S₀.val.toLinearMap
      Subtype.val_injective Subtype.val_injective
  have he₀ : IsIdempotentElem e₀ := hinj (by rw [map_mul]; exact he)
  rcases trivialIdempotents_tensorProduct_of_finiteType (hR.subalgebra R₀) (hS.subalgebra S₀)
      e₀ he₀ with rfl | rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr (map_one _)

end Ring

end AlgebraicGeometry.CohomologyAux

namespace AlgebraicGeometry

open CohomologyAux

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The spectrum of a nonzero `k`-algebra with only trivial idempotents is geometrically
connected over an algebraically closed field `k`. -/
theorem geometricallyConnected_spec_of_isAlgClosed (A : Type u) [CommRing A] [Algebra k A]
    [Nontrivial A] (hA : TrivialIdempotents A) :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun L _ _ ↦ ?_⟩
  have : Nontrivial (A ⊗[k] L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k A L
      (algebraMap k L).injective
  have hAL : TrivialIdempotents (A ⊗[k] L) :=
    trivialIdempotents_tensorProduct_of_isAlgClosed hA fun e he ↦
      IsIdempotentElem.iff_eq_zero_or_one.mp he
  -- `Γ(Spec (A ⊗ₖ L), ⊤) ≅ A ⊗ₖ L`
  let e := Scheme.ΓSpecIso (.of (A ⊗[k] L))
  have he := ConcreteCategory.bijective_of_isIso e.inv
  have := connectedSpace_of_trivialIdempotents (Spec (.of (A ⊗[k] L)))
    (hAL.of_surjective e.inv.hom he.2 fun x hx ↦
      ⟨1, (pow_one x).trans (he.1 (hx.trans (map_zero _).symm))⟩)
  exact (pullbackSpecIso k A L).hom.homeomorph.symm.connectedSpace_iff.mp ‹_›

/-- **A connected scheme over an algebraically closed field is geometrically connected**
(Stacks, Varieties, Section 33.7; EGA IV 4.5). For a field `K ⊇ k`, the projection
`X_K → X` is flat, quasi-compact and surjective, hence a quotient map, and its fibres are
connected (`geometricallyConnected_spec_of_isAlgClosed`). -/
theorem geometricallyConnected_of_isAlgClosed {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace X] : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ ↦ ?_⟩
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : GeometricallyConnected g :=
    geometricallyConnected_spec_of_isAlgClosed K fun e he ↦
      IsIdempotentElem.iff_eq_zero_or_one.mp he
  have : Surjective (pullback.fst f g) := inferInstance
  have hq := Flat.isQuotientMap_of_surjective (pullback.fst f g)
  rw [connectedSpace_iff_univ]
  simpa using hq.isCoinducing.isConnected_preimage_of_isClosed
    (pullback.fst f g).isConnected_preimage_singleton isClosed_univ isConnected_univ

/-- Over a one-point base `S`, the product `X ×_S Y` of two geometrically connected `S`-schemes
is connected: two points `z`, `z'` are joined through a point `w` with `pr₁ w = pr₁ z` and
`pr₂ w = pr₂ z'`, inside the connected fibres of the two projections. -/
theorem GeometricallyConnected.connectedSpace_pullback_of_subsingleton {X Y S : Scheme.{u}}
    (f : X ⟶ S)
    (g : Y ⟶ S) [GeometricallyConnected f] [GeometricallyConnected g] [Subsingleton S]
    [Nonempty S] : ConnectedSpace ↥(pullback f g) := by
  obtain ⟨s⟩ := ‹Nonempty S›
  obtain ⟨x, -⟩ := f.surjective s
  obtain ⟨y, -⟩ := g.surjective s
  obtain ⟨z₀, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y
    (Subsingleton.elim _ _)
  refine connectedSpace_iff_connectedComponent.mpr ⟨z₀, Set.eq_univ_of_forall fun z ↦ ?_⟩
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g)
    (pullback.fst f g z₀) (pullback.snd f g z) (Subsingleton.elim _ _)
  have h₁ : w ∈ connectedComponent z₀ :=
    ((pullback.fst f g).isConnected_preimage_singleton (pullback.fst f g z₀)).isPreconnected
      |>.subset_connectedComponent rfl hw₁
  have h₂ : z ∈ connectedComponent w :=
    ((pullback.snd f g).isConnected_preimage_singleton (pullback.snd f g z)).isPreconnected
      |>.subset_connectedComponent hw₂ rfl
  rwa [← connectedComponent_eq h₁] at h₂

/-- The product over an algebraically closed field `k` of two connected `k`-schemes is
connected (Stacks, Varieties, Section 33.7). -/
theorem connectedSpace_pullback_of_isAlgClosed_of_connectedSpace {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) [ConnectedSpace X] [ConnectedSpace Y] :
    ConnectedSpace ↥(pullback f g) := by
  have := geometricallyConnected_of_isAlgClosed f
  have := geometricallyConnected_of_isAlgClosed g
  exact GeometricallyConnected.connectedSpace_pullback_of_subsingleton f g

end AlgebraicGeometry
