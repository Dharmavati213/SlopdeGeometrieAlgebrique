/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PrimitiveElement

/-!
# SGA 1, Exposé XI, §4–§6: affine principal coverings

Let `G` be a finite group and `(G)_S` the constant `S`-group. For `S = Spec R` and
`P = Spec B` affine, a right action of `(G)_S` on `P` is an action of `G` on `B` by
`R`-algebra automorphisms, and `P ×_S (G)_S → P ×_S P` corresponds to the algebra map
`B ⊗_R B → ∏_{g ∈ G} B`, `x ⊗ y ↦ (x · g(y))_g`. By XI.4.2 (ii), `P` is a principal
homogeneous bundle under `(G)_S`, i.e. a principal covering with group `G` (V.2.7, XI.5), if and
only if this map is bijective and `B` is faithfully flat over `R`. This is the definition
`IsPrincipalCovering` used here; it only treats affine `S` and `P`.

Main results:

* `IsPrincipalCovering.etale`, `IsPrincipalCovering.finite`: a principal covering with finite
  group is finite étale (by descent along `R → B`, as in the proof of XI.4.2);
* `IsPrincipalCovering.mem_range_algebraMap_iff`: `R = B^G`, i.e. `S = P/G`;
* `adjoinRootProdXSubCEquiv`: `A[X]/∏(X - cᵢ) ≅ A^ι` when the `cᵢ - cⱼ` are units;
* `torsorMap_map_right`: the trivialization `B ⊗_R B ≅ ∏_G B` is `G`-equivariant
  (XI.4.2, (ii) ⇒ (i));
* `isPrincipalCovering_adjoinRoot`: a Galois criterion for `A[X]/(f)`, used for Kummer and
  Artin–Schreier coverings (XI.6);
* `isPrincipalCovering_of_isGalois`: a finite Galois field extension is a principal covering
  with its Galois group.
-/

namespace SGA.SGA1.ExposeXI

open Polynomial TensorProduct

section Split

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι]

/-- A monic polynomial of degree `#ι` vanishing at points `cᵢ` with unit differences is
`∏ (X - cᵢ)`. -/
theorem eq_prod_X_sub_C_of_isUnit_sub {f : A[X]} (hf : f.Monic)
    (hdeg : f.natDegree ≤ Fintype.card ι) {c : ι → A}
    (hc : Pairwise fun i j ↦ IsUnit (c i - c j)) (hroot : ∀ i, f.eval (c i) = 0) :
    f = ∏ i, (X - C (c i)) := by
  nontriviality A
  have hmon : ∀ i ∈ (Finset.univ : Finset ι), (X - C (c i)).Monic := fun i _ ↦ monic_X_sub_C _
  refine eq_of_monic_of_dvd_of_natDegree_le (monic_prod_of_monic _ _ hmon) hf ?_ ?_
  · exact Finset.prod_dvd_of_coprime
      (fun i _ j _ hij ↦ isCoprime_X_sub_C_of_isUnit_sub (hc hij))
      fun i _ ↦ dvd_iff_isRoot.mpr (hroot i)
  · refine hdeg.trans (le_of_eq ?_)
    rw [natDegree_prod_of_monic _ _ hmon]
    simp

omit [Fintype ι] in
theorem eval₂_algebraMap_pi_apply (c : ι → A) (p : A[X]) (j : ι) :
    p.eval₂ (algebraMap A (ι → A)) c j = p.eval (c j) := by
  induction p using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [eval₂_add, hp, hq]
  | monomial n a _ => simp [eval₂_mul, eval₂_pow]

omit [Fintype ι] in
theorem eval₂_prod_X_sub_C_eq_zero (c : ι → A) (s : Finset ι) (hs : ∀ j, j ∈ s) :
    (∏ i ∈ s, (X - C (c i))).eval₂ (Algebra.ofId A (ι → A) : A →+* (ι → A)) c = 0 := by
  funext j
  rw [Algebra.toRingHom_ofId, eval₂_algebraMap_pi_apply]
  simp [eval_prod, Finset.prod_eq_zero (hs j)]

/-- XI.6 (Chinese remainder theorem): evaluation at points with unit differences is
bijective on `A[X]/∏ (X - cᵢ)`. -/
theorem bijective_liftAlgHom_prod_X_sub_C (c : ι → A)
    (hc : Pairwise fun i j ↦ IsUnit (c i - c j)) :
    Function.Bijective (AdjoinRoot.liftAlgHom _ (Algebra.ofId A (ι → A)) c
      (eval₂_prod_X_sub_C_eq_zero c Finset.univ Finset.mem_univ)) := by
  constructor
  · refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    induction x using AdjoinRoot.induction_on with | ih p => ?_
    rw [AdjoinRoot.liftAlgHom_mk] at hx
    refine AdjoinRoot.mk_eq_zero.mpr (Finset.prod_dvd_of_coprime
      (fun i _ j _ hij ↦ isCoprime_X_sub_C_of_isUnit_sub (hc hij)) fun i _ ↦ ?_)
    have := congrFun hx i
    rw [Algebra.toRingHom_ofId, eval₂_algebraMap_pi_apply] at this
    exact dvd_iff_isRoot.mpr this
  · intro v
    obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal
      (I := fun i ↦ Ideal.span {X - C (c i)})
      (fun i j hij ↦ (Ideal.isCoprime_span_singleton_iff _ _).mpr
        (isCoprime_X_sub_C_of_isUnit_sub (hc hij))) (fun i ↦ C (v i))
    refine ⟨AdjoinRoot.mk _ r, funext fun i ↦ ?_⟩
    rw [AdjoinRoot.liftAlgHom_mk, Algebra.toRingHom_ofId, eval₂_algebraMap_pi_apply]
    have := dvd_iff_isRoot.mp (Ideal.mem_span_singleton.mp (hr i))
    simpa [sub_eq_zero] using this

/-- XI.6 (Chinese remainder theorem): if the `cᵢ - cⱼ` are units, evaluation at the `cᵢ`
identifies `A[X]/∏ (X - cᵢ)` with `A^ι`. -/
noncomputable def adjoinRootProdXSubCEquiv (c : ι → A)
    (hc : Pairwise fun i j ↦ IsUnit (c i - c j)) :
    AdjoinRoot (∏ i, (X - C (c i))) ≃ₐ[A] (ι → A) :=
  AlgEquiv.ofBijective _ (bijective_liftAlgHom_prod_X_sub_C c hc)

@[simp]
theorem adjoinRootProdXSubCEquiv_mk (c : ι → A) (hc : Pairwise fun i j ↦ IsUnit (c i - c j))
    (p : A[X]) (i : ι) :
    adjoinRootProdXSubCEquiv c hc (AdjoinRoot.mk _ p) i = p.eval (c i) := by
  rw [adjoinRootProdXSubCEquiv, AlgEquiv.ofBijective_apply, AdjoinRoot.liftAlgHom_mk,
    Algebra.toRingHom_ofId, eval₂_algebraMap_pi_apply]

@[simp]
theorem adjoinRootProdXSubCEquiv_root (c : ι → A) (hc : Pairwise fun i j ↦ IsUnit (c i - c j)) :
    adjoinRootProdXSubCEquiv c hc (AdjoinRoot.root _) = c := by
  rw [adjoinRootProdXSubCEquiv, AlgEquiv.ofBijective_apply, AdjoinRoot.liftAlgHom_root]

end Split

section BaseChange

variable {A : Type*} [CommRing A] (B : Type*) [CommRing B] [Algebra A B] (f : A[X])

/-- Base change of `A[X]/(f)`: `B ⊗_A A[X]/(f) ≅ B[X]/(f)`. -/
noncomputable def tensorAdjoinRootEquiv :
    B ⊗[A] AdjoinRoot f ≃ₐ[B] AdjoinRoot (f.map (algebraMap A B)) :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId B _)
      (AdjoinRoot.liftAlgHom f (Algebra.ofId A _) (AdjoinRoot.root _) (by
        change aeval (AdjoinRoot.root _) f = 0
        rw [← aeval_map_algebraMap B, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]))
      fun _ _ ↦ .all _ _)
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId B _) (1 ⊗ₜ AdjoinRoot.root f) (by
      change aeval (1 ⊗ₜ AdjoinRoot.root f) (f.map (algebraMap A B)) = 0
      rw [aeval_map_algebraMap, ← Algebra.TensorProduct.includeRight_apply, aeval_algHom_apply,
        AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]))
    (by ext; simp)
    (by ext; simp)

@[simp]
theorem tensorAdjoinRootEquiv_one_tmul_root :
    tensorAdjoinRootEquiv B f (1 ⊗ₜ AdjoinRoot.root f) = AdjoinRoot.root _ := by
  simp [tensorAdjoinRootEquiv]

end BaseChange

section PrincipalCovering

variable {G : Type*} [Group G] {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- The map `B ⊗_R B → ∏_{g ∈ G} B`, `x ⊗ y ↦ (x · g(y))_g`: the ring-theoretic form of
`P ×_S (G)_S → P ×_S P` (XI.4). -/
noncomputable def torsorMap (ρ : G →* (B ≃ₐ[R] B)) : B ⊗[R] B →ₐ[B] (G → B) :=
  Algebra.TensorProduct.lift (Algebra.ofId B (G → B)) (AlgHom.pi fun g ↦ (ρ g).toAlgHom)
    fun _ _ ↦ .all _ _

@[simp]
theorem torsorMap_tmul (ρ : G →* (B ≃ₐ[R] B)) (x y : B) (g : G) :
    torsorMap ρ (x ⊗ₜ y) g = x * ρ g y := by
  simp [torsorMap]

/-- XI.4.2, (ii) ⇒ (i) (affine case): the map `B ⊗_R B → ∏_G B` is `G`-equivariant, `G` acting
on the right factor of `B ⊗_R B` and by translation on `∏_G B`. Hence for a principal covering,
`IsPrincipalCovering.equiv` trivializes the covering after the faithfully flat base change
`R → B` (the diagonal section). -/
theorem torsorMap_map_right (ρ : G →* (B ≃ₐ[R] B)) (h : G) (x : B ⊗[R] B) (g : G) :
    torsorMap ρ (Algebra.TensorProduct.map (AlgHom.id B B) (ρ h).toAlgHom x) g =
      torsorMap ρ x (g * h) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [map_mul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- V.2.7, XI.4.2 (ii), XI.5 (affine case): `B` is a principal covering of `R` with group `G`
acting through `ρ`, i.e. `Spec B` is a principal homogeneous bundle over `Spec R` under the
constant group `(G)`: `B` is faithfully flat over `R` and `B ⊗_R B → ∏_G B` is bijective. -/
structure IsPrincipalCovering (ρ : G →* (B ≃ₐ[R] B)) : Prop where
  faithfullyFlat : Module.FaithfullyFlat R B
  bijective : Function.Bijective (torsorMap ρ)

namespace IsPrincipalCovering

variable {ρ : G →* (B ≃ₐ[R] B)} (hρ : IsPrincipalCovering ρ)
include hρ

/-- The isomorphism `B ⊗_R B ≅ ∏_G B`. -/
noncomputable def equiv : B ⊗[R] B ≃ₐ[B] (G → B) := AlgEquiv.ofBijective _ hρ.bijective

/-- A principal covering with finite group is étale (descent along `R → B`). -/
theorem etale [Finite G] : Algebra.Etale R B := by
  have := hρ.faithfullyFlat
  have : Algebra.Etale B (B ⊗[R] B) := .of_equiv hρ.equiv.symm
  exact .of_etale_tensorProduct_of_faithfullyFlat B

/-- A principal covering with finite group is finite (descent along `R → B`). -/
theorem finite [Finite G] : Module.Finite R B := by
  have := hρ.faithfullyFlat
  have : Module.Finite B (B ⊗[R] B) := .equiv hρ.equiv.symm.toLinearEquiv
  exact .of_finite_tensorProduct_of_faithfullyFlat B

/-- XI.4, V.2.7: `S` is the quotient of a principal covering by its group: the elements of `B`
fixed by `G` are exactly those of `R`. -/
theorem mem_range_algebraMap_iff (b : B) :
    b ∈ Set.range (algebraMap R B) ↔ ∀ g, ρ g b = b := by
  refine ⟨fun ⟨r, hr⟩ g ↦ by rw [← hr, AlgEquiv.commutes], fun hb ↦ ?_⟩
  have := hρ.faithfullyFlat
  rw [← (Algebra.IsEffective.of_faithfullyFlat R B).eqLocus_includeLeft_includeRight,
    SetLike.mem_coe, RingHom.mem_eqLocus]
  refine hρ.bijective.1 (funext fun g ↦ ?_)
  change torsorMap ρ (b ⊗ₜ 1) g = torsorMap ρ (1 ⊗ₜ b) g
  simp [hb]

/-- Principal coverings are transported along algebra isomorphisms. -/
theorem of_algEquiv {B' : Type*} [CommRing B'] [Algebra R B'] (e : B ≃ₐ[R] B') :
    IsPrincipalCovering ((AlgEquiv.autCongr e).toMonoidHom.comp ρ) := by
  have := hρ.faithfullyFlat
  refine ⟨.of_linearEquiv R B e.symm.toLinearEquiv, ?_⟩
  set ρ' := (AlgEquiv.autCongr e).toMonoidHom.comp ρ
  have key : ∀ z, torsorMap ρ' (Algebra.TensorProduct.congr e e z) =
      fun g ↦ e (torsorMap ρ z g) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => funext g; simp
    | tmul x y => funext g; simp [ρ']
    | add x y hx hy => funext g; simp only [map_add, hx, hy, Pi.add_apply]
  have hfun : ⇑(torsorMap ρ') = (fun v g ↦ e (v g)) ∘ torsorMap ρ ∘
      (Algebra.TensorProduct.congr e e).symm := by
    funext z
    rw [Function.comp_apply, Function.comp_apply, ← key, AlgEquiv.apply_symm_apply]
  rw [hfun]
  exact (Equiv.piCongrRight fun _ ↦ e.toEquiv).bijective.comp
    (hρ.bijective.comp (Algebra.TensorProduct.congr e e).symm.bijective)

/-- XI.4: base change `R → B` trivializes a principal covering. -/
theorem nonempty_algEquiv_pi : Nonempty (B ⊗[R] B ≃ₐ[B] (G → B)) := ⟨hρ.equiv⟩

end IsPrincipalCovering

end PrincipalCovering

section Criterion

variable {A : Type*} [CommRing A] {G : Type*} [Group G] [Fintype G]

/-- A free module with a nonempty basis is faithfully flat. -/
theorem faithfullyFlat_of_basis {M : Type*} [AddCommGroup M] [Module A M] {ι : Type*}
    [Nonempty ι] (b : Module.Basis ι A M) : Module.FaithfullyFlat A M :=
  .of_linearEquiv A (ι →₀ A) b.repr

/-- XI.6, Galois criterion: let `f` be monic of degree `#G` and let `G` act on `A[X]/(f)`
by `A`-algebra automorphisms. If the conjugates `g (root f)` have unit differences, then
`A[X]/(f)` is a principal covering of `A` with group `G`. -/
theorem isPrincipalCovering_adjoinRoot {f : A[X]} (hf : f.Monic)
    (hdeg : f.natDegree = Fintype.card G) (ρ : G →* (AdjoinRoot f ≃ₐ[A] AdjoinRoot f))
    (hρ : Pairwise fun g h ↦ IsUnit (ρ g (AdjoinRoot.root f) - ρ h (AdjoinRoot.root f))) :
    IsPrincipalCovering ρ := by
  set B := AdjoinRoot f
  set c : G → B := fun g ↦ ρ g (AdjoinRoot.root f)
  have hq : f.map (algebraMap A B) = ∏ g, (X - C (c g)) := by
    refine eq_prod_X_sub_C_of_isUnit_sub (hf.map _) (natDegree_map_le.trans hdeg.le) hρ
      fun g ↦ ?_
    rw [eval_map_algebraMap, aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self,
      map_zero]
  refine ⟨?_, ?_⟩
  · have : Nonempty (Fin (AdjoinRoot.powerBasis' hf).dim) :=
      ⟨⟨0, by rw [AdjoinRoot.powerBasis'_dim, hdeg]; exact Fintype.card_pos_iff.mpr ⟨1⟩⟩⟩
    exact faithfullyFlat_of_basis (AdjoinRoot.powerBasis' hf).basis
  · let E : B ⊗[A] B ≃ₐ[B] (G → B) := (tensorAdjoinRootEquiv B f).trans
        ((AdjoinRoot.algEquivOfEq B _ _ hq).trans (adjoinRootProdXSubCEquiv c hρ))
    have : torsorMap ρ = E.toAlgHom := by
      ext g
      simp [E, c, AdjoinRoot.algEquivOfEq_root]
    rw [this]
    exact E.bijective

end Criterion

section Galois

/-- V.2.7, XI.5: a finite Galois extension `L/K` is a principal covering of `Spec K` with group
`Gal(L/K)`. -/
theorem isPrincipalCovering_of_isGalois (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IsPrincipalCovering (MonoidHom.id (L ≃ₐ[K] L)) := by
  have : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite _
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  have hint : IsIntegral K α := .of_finite K α
  let e : AdjoinRoot (minpoly K α) ≃ₐ[K] L := (IntermediateField.adjoinRootEquivAdjoin K hint).trans
    ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  let ρ₀ := (AlgEquiv.autCongr e.symm).toMonoidHom
  have hρ₀ : IsPrincipalCovering ρ₀ := by
    refine isPrincipalCovering_adjoinRoot (minpoly.monic hint) ?_ ρ₀ fun g h hgh ↦ ?_
    · rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top',
        ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
    · set d := ρ₀ g (AdjoinRoot.root _) - ρ₀ h (AdjoinRoot.root _)
      have hd : e d ≠ 0 := fun h0 ↦ hgh (by
        have h1 : d = 0 := by simpa using congrArg e.symm h0
        have h2 : ρ₀ g = ρ₀ h := AlgEquiv.coe_toAlgHom_injective
          (AdjoinRoot.algHom_ext (sub_eq_zero.mp h1))
        exact (AlgEquiv.autCongr e.symm).injective h2)
      simpa using (isUnit_iff_ne_zero.mpr hd).map e.symm
  have := hρ₀.of_algEquiv e
  have heq : (AlgEquiv.autCongr e).toMonoidHom.comp ρ₀ = MonoidHom.id (L ≃ₐ[K] L) := by
    ext g x
    simp [ρ₀]
  rwa [heq] at this

end Galois

end SGA.SGA1.ExposeXI
