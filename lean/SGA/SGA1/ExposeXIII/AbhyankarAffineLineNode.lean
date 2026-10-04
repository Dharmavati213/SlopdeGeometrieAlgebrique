/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Patching.ProjectiveLineNodeTwist
import SGA.SGA1.ExposeXIII.AffineLinePGroupsNode
import SGA.SGA1.ExposeXIII.AffineLinePGroupsArtinSchreier

/-!
# XIII.2.13, case A: Harbater–Stevenson's node lemma

In the proof of Raynaud's patching theorem by Harbater–Stevenson (*Patching and thickening
problems*, J. Algebra 212 (1999), 272–304, proof of Theorem 6), two Galois covers of `ℙ¹` are
placed on the two components of the closed fibre of a nodal curve over `k⟦t⟧`; the patching needs
a Galois cover of the punctured node which restricts, on the two punctured branches, to the given
local covers. With the node ring `R̂_O = k⟦y⟧⟦t⟧[T]/(T² - yT + t²)` (geometrically
`k⟦t, u, v⟧/(uv - t²)`) and the punctured node `R' = R̂_O[1/(u + v - 2t)]`
(`PatchingProjectiveLine.nodePunctured`), the branches are the reductions `R' → k((y))`
(`nodePuncturedReduceOne`, `nodePuncturedReduceTwo`).

Main result (`AffineLinePGroups.exists_continuousMonoidHom_conj_nodePunctured`, the node lemma
in terms of fundamental groups): if `k` has characteristic `p` and every element of `k` has the
form `dᵖ - d` (e.g. `k` algebraically closed), then for every finite `p`-group `P` and continuous
homomorphisms `φ₁, φ₂ : π₁(Spec k((y))) → P` there is a continuous `ψ : π₁(Spec R') → P` whose
restrictions to the two branches are conjugate to `φ₁` and `φ₂`. The restrictions are the
homomorphisms `π₁(Spec k((y)), Ωᵢ) → π₁(Spec R', Ωᵢ) → π₁(Spec R', Ω)` induced by the reductions
(`AffineLinePGroups.fundamentalGroupMapOfRingHom`), followed by a change of geometric point along
any classes of paths `γᵢ` (V.7).

It is an instance of a general statement
(`AffineLinePGroups.exists_continuousMonoidHom_conj_of_ringHom`): for a domain `R` of
characteristic `p` with ring homomorphisms `rᵢ : R → Kᵢ` to fields such that every family
`(aᵢ) ∈ ∏ Kᵢ` is congruent to some `(rᵢ(e))` modulo `℘(Kᵢ) = {b - bᵖ}`, the same conclusion
holds. The proof combines the group theory of the induction along a central series
(`AffineLinePGroups.exists_continuousMonoidHom_conj`), the weak solutions of central embedding
problems for `π₁(Spec R)` (`SGA.SGA1.ExposeXIII.exists_lift_of_central_ker`) and Artin–Schreier
characters (`AffineLinePGroups.artinSchreierChar`; surjectivity on fields, naturality, change of
point). For the node, the congruence condition is
`PatchingProjectiveLine.exists_nodePunctured_reduce_eq`.

Harbater–Stevenson moreover make the cover totally ramified over `u = v = t` by an extra term
`h(t)` in the Artin–Schreier twists; that is not done here, and it is not needed for the route to
XIII.2.13 that only asks the inertia at the branch point to lie in `P`.
-/

universe u

open CategoryTheory PreGaloisCategory CommAlgCat

namespace SGA.SGA1.ExposeXIII.AffineLinePGroups

variable (p : ℕ) [hp : Fact p.Prime]

/-- V.6, XI.6.7: naturality of Artin–Schreier characters along a ring homomorphism. -/
theorem artinSchreierChar_ringHom {R S : Type u} [CommRing R] [CharP R p] [IsDomain R]
    [ConnectedSpace (PrimeSpectrum R)] [CommRing S] [CharP S p] [IsDomain S]
    [ConnectedSpace (PrimeSpectrum S)] (f : R →+* S) (Ω : Type u) [Field Ω] [Algebra R Ω]
    [Algebra S Ω] [IsSepClosed Ω] [CharP Ω p] (h : algebraMap R Ω = (algebraMap S Ω).comp f)
    (a : R) (σ : Aut (ExposeV.fiberFunctor S Ω)) :
    artinSchreierChar p Ω (f a) σ =
      artinSchreierChar p Ω a (fundamentalGroupMapOfRingHom f Ω h σ) := by
  let := f.toAlgebra
  have : IsScalarTower R S Ω := IsScalarTower.of_algebraMap_eq' h
  exact artinSchreierChar_algebraMap p Ω a σ

/-- The group theory of Harbater–Stevenson's node lemma for rings: let `R` be a domain of
characteristic `p` and `rᵢ : R → Kᵢ` ring homomorphisms to fields such that every family
`(aᵢ) ∈ ∏ Kᵢ` is congruent to some `(rᵢ(e))` modulo `℘(Kᵢ) = {b - bᵖ}` (hypothesis `hr`). Fix
geometric points `R → Ω` and `Kᵢ → Ωᵢ` (separably closed), with `R → Ωᵢ` through `rᵢ`, and
classes of paths `γᵢ` from the point `Ωᵢ` of `Spec R` to `Ω`. Then for every finite `p`-group
`P` and continuous homomorphisms `φᵢ : π₁(Spec Kᵢ, Ωᵢ) → P` there is a continuous
`ψ : π₁(Spec R, Ω) → P` with `ψ ∘ γᵢ ∘ π₁(rᵢ)` conjugate to `φᵢ` for each `i`. -/
theorem exists_continuousMonoidHom_conj_of_ringHom {R : Type u} [CommRing R] [IsDomain R]
    [CharP R p] {ι : Type*} {K : ι → Type u} [∀ i, Field (K i)] [∀ i, CharP (K i) p]
    (r : ∀ i, R →+* K i) (hr : ∀ a : ∀ i, K i, ∃ e : R, ∀ i, ∃ b : K i, r i e - a i = b - b ^ p)
    (Ω : Type u) [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
    (Ω' : ι → Type u) [∀ i, Field (Ω' i)] [∀ i, Algebra (K i) (Ω' i)] [∀ i, IsSepClosed (Ω' i)]
    [∀ i, Algebra R (Ω' i)] (hΩ : ∀ i, algebraMap R (Ω' i) = (algebraMap (K i) (Ω' i)).comp (r i))
    (γ : ∀ i, 𝟭 _ ⋙ ExposeV.fiberFunctor R (Ω' i) ≅ ExposeV.fiberFunctor R Ω)
    (P : Type u) [Group P] [Finite P] [TopologicalSpace P] [DiscreteTopology P]
    (hP : IsPGroup p P) (φ : ∀ i, ContinuousMonoidHom (Aut (ExposeV.fiberFunctor (K i) (Ω' i))) P) :
    ∃ ψ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor R Ω)) P, ∀ i, ∃ c : P, ∀ σ,
      ψ (ExposeV.autMap (𝟭 _) (γ i) (fundamentalGroupMapOfRingHom (r i) (Ω' i) (hΩ i) σ)) =
        c * φ i σ * c⁻¹ := by
  have : CharP Ω p := charP_of_algebra p R Ω
  have : ∀ i, CharP (Ω' i) p := fun i ↦ charP_of_algebra p (K i) (Ω' i)
  let ρ : ∀ i, ContinuousMonoidHom (Aut (ExposeV.fiberFunctor (K i) (Ω' i)))
      (Aut (ExposeV.fiberFunctor R Ω)) := fun i ↦
    ⟨(ExposeV.autMap (𝟭 _) (γ i)).comp (fundamentalGroupMapOfRingHom (r i) (Ω' i) (hΩ i)),
      (ExposeV.continuous_autMap _ _).comp (continuous_fundamentalGroupMapOfRingHom _ _ _)⟩
  refine exists_continuousMonoidHom_conj (Γ := Aut (ExposeV.fiberFunctor R Ω)) ?_ ρ ?_ P hP φ
  · intro H G _ _ _ _ _ _ _ ψ hψ π hπ hker hcard
    exact exists_lift_of_central_ker p R Ω ψ hψ π hπ hker hcard
  · intro D _ _ _ hD δ
    let eD : D ≃* DiscreteZMod.{u} p := mulEquivOfPrimeCardEq hD (natCard_discreteZMod p)
    choose a ha using fun i ↦ exists_artinSchreierChar_eq p (K i) (Ω' i)
      ⟨eD.toMonoidHom.comp (δ i).toMonoidHom,
        (continuous_of_discreteTopology (f := eD)).comp (δ i).continuous⟩
    obtain ⟨e, he⟩ := hr a
    refine ⟨⟨eD.symm.toMonoidHom.comp (artinSchreierChar p Ω e).toMonoidHom,
      (continuous_of_discreteTopology (f := eD.symm)).comp (artinSchreierChar p Ω e).continuous⟩,
      fun i σ ↦ ?_⟩
    obtain ⟨b, hb⟩ := he i
    change eD.symm (artinSchreierChar p Ω e (ExposeV.autMap (𝟭 _) (γ i)
      (fundamentalGroupMapOfRingHom (r i) (Ω' i) (hΩ i) σ))) = δ i σ
    rw [artinSchreierChar_autMap_id, ← artinSchreierChar_ringHom,
      artinSchreierChar_eq_of_sub_eq p (Ω' i) (r i e) (a i) b hb, ha i]
    exact eD.symm_apply_apply (δ i σ)

section Node

open PatchingProjectiveLine

variable {k : Type u} [Field k] [CharP k p]

/-- **Harbater–Stevenson's node lemma** (*Patching and thickening problems*, J. Algebra 212
(1999), proof of Theorem 6), in terms of fundamental groups and without the total ramification
over `u = v = t`: let `k` be a field of characteristic `p` in which every element has the form
`dᵖ - d` (e.g. `k` algebraically closed), `R'` the punctured node and `rᵢ : R' → k((y))` its two
reductions (`nodeReduce`). Fix geometric points `R' → Ω` and `k((y)) → Ωᵢ` (separably closed),
with `R' → Ωᵢ` through `rᵢ`, and classes of paths `γᵢ` from `Ωᵢ` to `Ω` in `Spec R'`. Then for
every finite `p`-group `P` and continuous homomorphisms `φᵢ : π₁(Spec k((y)), Ωᵢ) → P` there is a
continuous `ψ : π₁(Spec R', Ω) → P` whose restriction `ψ ∘ γᵢ ∘ π₁(rᵢ)` to each branch is
conjugate to `φᵢ`. -/
theorem exists_continuousMonoidHom_conj_nodePunctured (hk : ∀ c : k, ∃ d : k, d ^ p - d = c)
    (Ω : Type u) [Field Ω] [Algebra (nodePunctured k) Ω] [IsSepClosed Ω]
    (Ω' : Bool → Type u) [∀ i, Field (Ω' i)] [∀ i, Algebra (LaurentSeries k) (Ω' i)]
    [∀ i, IsSepClosed (Ω' i)] [∀ i, Algebra (nodePunctured k) (Ω' i)]
    (hΩ : ∀ i, algebraMap (nodePunctured k) (Ω' i) =
      (algebraMap (LaurentSeries k) (Ω' i)).comp (nodeReduce k i))
    (γ : ∀ i, 𝟭 _ ⋙ ExposeV.fiberFunctor (nodePunctured k) (Ω' i) ≅
      ExposeV.fiberFunctor (nodePunctured k) Ω)
    (P : Type u) [Group P] [Finite P] [TopologicalSpace P] [DiscreteTopology P]
    (hP : IsPGroup p P)
    (φ : ∀ i,
      ContinuousMonoidHom (Aut (ExposeV.fiberFunctor (LaurentSeries k) (Ω' i))) P) :
    ∃ ψ : ContinuousMonoidHom (Aut (ExposeV.fiberFunctor (nodePunctured k) Ω)) P,
      ∀ i, ∃ c : P, ∀ σ,
        ψ (ExposeV.autMap (𝟭 _) (γ i)
          (fundamentalGroupMapOfRingHom (nodeReduce k i) (Ω' i) (hΩ i) σ)) = c * φ i σ * c⁻¹ :=
  have : CharP (nodePunctured k) p := charP_nodePunctured k p
  have : CharP (LaurentSeries k) p :=
    charP_of_injective_algebraMap (algebraMap k (LaurentSeries k)).injective p
  exists_continuousMonoidHom_conj_of_ringHom p (nodeReduce k) (exists_nodeReduce_sub_eq p hk)
    Ω Ω' hΩ γ P hP φ

end Node

end SGA.SGA1.ExposeXIII.AffineLinePGroups
