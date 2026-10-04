/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Product

/-!
# Products of covering maps

A product of two covering maps, or of finitely many, is a covering map, and its monodromy along a
product of paths is the product of the monodromies.

## Main results

* `IsEvenlyCovered.prodMap`, `IsEvenlyCovered.piMap`: products of evenly covered points.
* `IsCoveringMap.prodMap`, `IsCoveringMap.piMap` (finitely many factors): products of covering
  maps; `IsCoveringMap.id`: the identity is a covering map.
* `IsCoveringMap.monodromy_mk_of_forall_eq`: the monodromy along a path is the endpoint of any
  lift of it.
* `IsCoveringMap.monodromy_prodMap`, `IsCoveringMap.monodromy_piMap`: the monodromy of a product
  of covering maps along a product of homotopy classes of paths.

## References

* [A. Hatcher, *Algebraic Topology*, §1.3][hatcher02]
-/

open Topology Set

section Evenly

variable {E X E' X' : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace E']
  [TopologicalSpace X'] {f : E → X} {f' : E' → X'} {I I' : Type*} [TopologicalSpace I]
  [TopologicalSpace I']

/-- If `x` is evenly covered by `f` and `x'` by `f'`, then `(x, x')` is evenly covered by
`Prod.map f f'`. -/
theorem IsEvenlyCovered.prodMap {x : X} {x' : X'} (h : IsEvenlyCovered f x I)
    (h' : IsEvenlyCovered f' x' I') : IsEvenlyCovered (Prod.map f f') (x, x') (I × I') := by
  obtain ⟨hI, U, hxU, hU, hfU, H, hH⟩ := h
  obtain ⟨hI', U', hxU', hU', hfU', H', hH'⟩ := h'
  refine ⟨inferInstance, U ×ˢ U', ⟨hxU, hxU'⟩, hU.prod hU', hfU.prod hfU',
    { toFun e := (⟨((H ⟨e.1.1, e.2.1⟩).1.1, (H' ⟨e.1.2, e.2.2⟩).1.1),
          ⟨(H ⟨e.1.1, e.2.1⟩).1.2, (H' ⟨e.1.2, e.2.2⟩).1.2⟩⟩,
        ((H ⟨e.1.1, e.2.1⟩).2, (H' ⟨e.1.2, e.2.2⟩).2))
      invFun z := ⟨((H.symm (⟨z.1.1.1, z.1.2.1⟩, z.2.1)).1,
          (H'.symm (⟨z.1.1.2, z.1.2.2⟩, z.2.2)).1),
        ⟨(H.symm (⟨z.1.1.1, z.1.2.1⟩, z.2.1)).2, (H'.symm (⟨z.1.1.2, z.1.2.2⟩, z.2.2)).2⟩⟩
      left_inv e := by simp
      right_inv z := by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }, fun e ↦ ?_⟩
  exact Prod.ext (hH _) (hH' _)

/-- If `x i` is evenly covered by `f i` for each `i` in a finite type, then `x` is evenly covered
by `Pi.map f`. -/
theorem IsEvenlyCovered.piMap {ι : Type*} [Finite ι] {E X I : ι → Type*}
    [∀ i, TopologicalSpace (E i)] [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (I i)]
    {f : ∀ i, E i → X i} {x : ∀ i, X i} (h : ∀ i, IsEvenlyCovered (f i) (x i) (I i)) :
    IsEvenlyCovered (Pi.map f) x (∀ i, I i) := by
  choose hI U hxU hU hfU H hH using h
  refine ⟨inferInstance, univ.pi U, fun i _ ↦ hxU i, isOpen_set_pi finite_univ fun i _ ↦ hU i,
    isOpen_set_pi finite_univ fun i _ ↦ hfU i,
    { toFun e := (⟨fun i ↦ (H i ⟨e.1 i, e.2 i trivial⟩).1.1,
          fun i _ ↦ (H i ⟨e.1 i, e.2 i trivial⟩).1.2⟩,
        fun i ↦ (H i ⟨e.1 i, e.2 i trivial⟩).2)
      invFun z := ⟨fun i ↦ ((H i).symm (⟨z.1.1 i, z.1.2 i trivial⟩, z.2 i)).1,
        fun i _ ↦ ((H i).symm (⟨z.1.1 i, z.1.2 i trivial⟩, z.2 i)).2⟩
      left_inv e := by ext i; simp
      right_inv z := by
        refine Prod.ext (Subtype.ext (funext fun i ↦ ?_)) (funext fun i ↦ ?_)
        · exact congrArg (fun w ↦ (w.1 : X i)) ((H i).apply_symm_apply _)
        · exact congrArg Prod.snd ((H i).apply_symm_apply _)
      continuous_toFun := by
        have hc (i : ι) : Continuous fun e : Pi.map f ⁻¹' univ.pi U ↦ H i ⟨e.1 i, e.2 i trivial⟩ :=
          (H i).continuous.comp
            (Continuous.subtype_mk ((continuous_apply i).comp continuous_subtype_val) _)
        exact Continuous.prodMk (Continuous.subtype_mk (continuous_pi fun i ↦
          (continuous_subtype_val.comp continuous_fst).comp (hc i)) _)
          (continuous_pi fun i ↦ continuous_snd.comp (hc i))
      continuous_invFun := by
        refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
        refine continuous_subtype_val.comp ((H i).symm.continuous.comp ?_)
        refine Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_
        · exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
        · exact (continuous_apply i).comp continuous_snd }, fun e ↦ ?_⟩
  exact funext fun i ↦ hH i _

end Evenly

namespace IsCoveringMap

variable {E X E' X' : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace E']
  [TopologicalSpace X'] {f : E → X} {f' : E' → X'}

variable (X) in
/-- The identity is a covering map. -/
protected theorem id : IsCoveringMap (id : X → X) := fun x ↦
  IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Unit)
    ⟨inferInstance, univ, mem_univ x, isOpen_univ, isOpen_univ,
      (Homeomorph.Set.univ X).trans (Homeomorph.prodPUnit X).symm |>.trans
        ((Homeomorph.Set.univ X).symm.prodCongr (Homeomorph.refl _)), fun _ ↦ rfl⟩

/-- A product of two covering maps is a covering map. -/
protected theorem prodMap (hf : IsCoveringMap f) (hf' : IsCoveringMap f') :
    IsCoveringMap (Prod.map f f') := fun z ↦
  ((hf z.1).prodMap (hf' z.2)).to_isEvenlyCovered_preimage

/-- A product of finitely many covering maps is a covering map. -/
protected theorem piMap {ι : Type*} [Finite ι] {E X : ι → Type*} [∀ i, TopologicalSpace (E i)]
    [∀ i, TopologicalSpace (X i)] {f : ∀ i, E i → X i} (hf : ∀ i, IsCoveringMap (f i)) :
    IsCoveringMap (Pi.map f) := fun x ↦
  (IsEvenlyCovered.piMap fun i ↦ hf i (x i)).to_isEvenlyCovered_preimage

variable {p : E → X} (cov : IsCoveringMap p)

/-- The monodromy along a path `γ` sends the starting point of any lift `Γ` of `γ` to its
endpoint. -/
theorem monodromy_mk_of_forall_eq {x y : X} (γ : Path x y) {e₀ e₁ : E} (Γ : Path e₀ e₁)
    (hΓ : ∀ t, p (Γ t) = γ t) (h₀ : p e₀ = x) :
    (cov.monodromy (.mk γ) ⟨e₀, h₀⟩ : E) = e₁ := by
  have hy : p e₁ = y := by rw [← Γ.target, hΓ, γ.target]
  have h := cov.monodromy_eq_of_map_eq (γ := .mk γ) (ex := ⟨e₀, h₀⟩) (ey := ⟨e₁, hy⟩) (.mk Γ) ?_
  · exact congrArg Subtype.val h
  · exact congrArg Path.Homotopic.Quotient.mk (Path.ext (funext hΓ))

/-- The lift of a path `γ` starting at `e`, as a path from `e` to the monodromy of `γ` at `e`. -/
noncomputable def liftPathPath {x y : X} (γ : Path x y) (e : p ⁻¹' {x}) :
    Path (e : E) (cov.monodromy (.mk γ) e) where
  toContinuousMap := cov.liftPath γ e (γ.source.trans e.2.symm)
  source' := cov.liftPath_zero ..
  target' := rfl

theorem liftPathPath_lifts {x y : X} (γ : Path x y) (e : p ⁻¹' {x}) (t : unitInterval) :
    p (cov.liftPathPath γ e t) = γ t :=
  congrFun (cov.liftPath_lifts γ e (γ.source.trans e.2.symm)) t

/-- The monodromy of a product of covering maps along a product of homotopy classes of paths is
the product of the monodromies. -/
theorem monodromy_prodMap (cov' : IsCoveringMap f') {x y : X} {x' y' : X'}
    (γ : Path.Homotopic.Quotient x y) (γ' : Path.Homotopic.Quotient x' y')
    (e : Prod.map p f' ⁻¹' {(x, x')}) :
    ((cov.prodMap cov').monodromy (Path.Homotopic.prod γ γ') e : E × E') =
      ((cov.monodromy γ ⟨e.1.1, congrArg Prod.fst e.2⟩ : E),
        (cov'.monodromy γ' ⟨e.1.2, congrArg Prod.snd e.2⟩ : E')) := by
  induction γ using Path.Homotopic.Quotient.ind with | mk γ => ?_
  induction γ' using Path.Homotopic.Quotient.ind with | mk γ' => ?_
  rw [Path.Homotopic.prod_lift]
  exact (cov.prodMap cov').monodromy_mk_of_forall_eq (γ.prod γ')
    ((cov.liftPathPath γ ⟨e.1.1, congrArg Prod.fst e.2⟩).prod
      (cov'.liftPathPath γ' ⟨e.1.2, congrArg Prod.snd e.2⟩))
    (fun t ↦ Prod.ext (cov.liftPathPath_lifts γ _ t) (cov'.liftPathPath_lifts γ' _ t)) e.2

/-- The monodromy of a product of finitely many covering maps along a product of homotopy
classes of paths is the product of the monodromies. -/
theorem monodromy_piMap {ι : Type*} [Finite ι] {E X : ι → Type*} [∀ i, TopologicalSpace (E i)]
    [∀ i, TopologicalSpace (X i)] {f : ∀ i, E i → X i} (cov : ∀ i, IsCoveringMap (f i))
    {x y : ∀ i, X i} (γ : ∀ i, Path.Homotopic.Quotient (x i) (y i)) (e : Pi.map f ⁻¹' {x}) :
    ((IsCoveringMap.piMap cov).monodromy (Path.Homotopic.pi γ) e : ∀ i, E i) =
      fun i ↦ ((cov i).monodromy (γ i) ⟨e.1 i, congrFun e.2 i⟩ : E i) := by
  induction γ using Quotient.induction_on_pi with | _ γ => ?_
  change ((IsCoveringMap.piMap cov).monodromy
    (Path.Homotopic.pi fun i ↦ Path.Homotopic.Quotient.mk (γ i)) e : ∀ i, E i) =
      fun i ↦ ((cov i).monodromy (.mk (γ i)) ⟨e.1 i, congrFun e.2 i⟩ : E i)
  rw [Path.Homotopic.pi_lift]
  exact (IsCoveringMap.piMap cov).monodromy_mk_of_forall_eq (Path.pi γ)
    (Path.pi fun i ↦ (cov i).liftPathPath (γ i) ⟨e.1 i, congrFun e.2 i⟩)
    (fun t ↦ funext fun i ↦ (cov i).liftPathPath_lifts (γ i) _ t) e.2

end IsCoveringMap
