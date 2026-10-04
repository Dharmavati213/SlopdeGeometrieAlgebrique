/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.GroupScheme.Points
import SGA.SGA1.ExposeIX.Pinching
import SGA.SGA1.ExposeX.TopologicallyFinite
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# SGA 1, Exposé IX, 5.4, consequence, for finite maps that are isomorphisms off finitely many points

Let `k` be an algebraically closed field, `D` a scheme of finite type over `k` and `g : C ⟶ D` a
finite surjective morphism from a connected scheme, which is an isomorphism over an open `U ⊆ D`
whose complement is a finite set of closed points (e.g. the normalization of a curve, or a finite
birational morphism onto a plane curve). Then `π₁(C)` is topologically finitely generated as soon
as `π₁(D)` is (`isTopologicallyFG_etaleFundamentalGroup_of_isFinite_of_isIso_morphismRestrict`);
the proof goes through the continuous surjection `π₁(D) ↠ π₁(C)` built in
`SGA.SGA1.ExposeIX.Pinching`, which is not stated as a separate theorem.

SGA does not use this result for X.2.9: there the curve case is X.2.6 for the (smooth)
normalization, and the proof of X.2.6 in characteristic `p` lifts the smooth curve itself to
`W(k)` (III.7.4) and applies X.2.3. This formalization plans a different route to the curve case
of X.2.9 in characteristic `p`: a finite birational morphism from the normal curve onto a plane
curve (`AlgebraicGeometry.planeCurve`), a lift of the plane curve to characteristic `0`, and this
file to pass from the plane curve back to the curve. That route is not finished: only this
pinching step and part of the plane model (`SGA.Foundations.Projective.PlaneModel`) are
formalized.

We check the hypotheses of the abstract form `isTopologicallyFG_etaleFundamentalGroup_of_pinching`:

* over `U`, `C ×_D C` is the diagonal, since `g` is a monomorphism there
  (`PinchingCurve.mem_range_diagonal_of_mono`); so the points off the diagonal lie over the finite
  set `D ∖ U`, in finitely many finite fibres of the finite morphism `C ×_D C ⟶ D`;
* they are closed, as points of discrete fibres over closed points, hence carry `k`-points
  (`AlgebraicGeometry.pointOfClosedPoint`, Nullstellensatz);
* `C ×_D C ×_C (C ×_D C)` is finite over `D`, hence noetherian, so it has finitely many connected
  components, each containing a closed point, hence a `k`-point.

SGA's hypotheses for IX.5.4 (`g` finite of finite presentation, `n(s) = 1` geometric point in the
fibre over each `s` outside a discrete set) are replaced by the ones above.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeIX

namespace PinchingCurve

variable {C D : Scheme.{u}} (g : C ⟶ D)

/-- If `g` is a monomorphism over an open `U` of the target, the points of `C ×_D C` lying over
`U` are on the diagonal. -/
lemma mem_range_diagonal_of_mono {U : D.Opens} (hU : Mono ((g ⁻¹ᵁ U).ι ≫ g))
    (z : ↥(pullback g g)) (hz : g (pullback.fst g g z) ∈ U) :
    z ∈ Set.range (pullback.diagonal g) := by
  set t := (pullback g g).fromSpecResidueField z
  have ht (x : _) : t x = z := Scheme.fromSpecResidueField_apply _ _
  have h₂ : g (pullback.snd g g z) = g (pullback.fst g g z) := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  have hr (p : pullback g g ⟶ C) (hp : g (p z) ∈ U) :
      Set.range (t ≫ p) ⊆ (g ⁻¹ᵁ U).ι.opensRange := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.opensRange_ι]
    change g (p (t x)) ∈ U
    rw [ht]
    exact hp
  let a := IsOpenImmersion.lift (g ⁻¹ᵁ U).ι (t ≫ pullback.fst g g) (hr _ hz)
  let b := IsOpenImmersion.lift (g ⁻¹ᵁ U).ι (t ≫ pullback.snd g g) (hr _ (h₂ ▸ hz))
  have ha : a ≫ (g ⁻¹ᵁ U).ι = t ≫ pullback.fst g g := IsOpenImmersion.lift_fac _ _ _
  have hb : b ≫ (g ⁻¹ᵁ U).ι = t ≫ pullback.snd g g := IsOpenImmersion.lift_fac _ _ _
  have hab : a = b := by
    refine hU.right_cancellation _ _ ?_
    rw [reassoc_of% ha, reassoc_of% hb, pullback.condition]
  have htd : t = (t ≫ pullback.fst g g) ≫ pullback.diagonal g := by
    refine pullback.hom_ext ?_ ?_
    · simp
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, ← ha, ← hb, hab]
  obtain ⟨x⟩ : Nonempty (Spec ((pullback g g).residueField z)) := inferInstance
  refine ⟨(t ≫ pullback.fst g g) x, ?_⟩
  calc pullback.diagonal g ((t ≫ pullback.fst g g) x)
      = ((t ≫ pullback.fst g g) ≫ pullback.diagonal g) x := rfl
    _ = t x := by rw [← htd]
    _ = z := ht x

end PinchingCurve

open PinchingCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C D : Scheme.{u}} (τ : D ⟶ Spec (.of k))
  [LocallyOfFiniteType τ] [CompactSpace D] (g : C ⟶ D) [IsFinite g] [Surjective g]
  [ConnectedSpace C]

include τ in
/-- **IX.5.4, consequence, for finite morphisms which are isomorphisms off finitely many closed
points**: let `k` be algebraically closed, `D` of finite type over `k` (`τ : D ⟶ Spec k` locally of
finite type, `D` quasi-compact), and `g : C ⟶ D` finite and surjective with `C` connected. Assume
`g` is an isomorphism over an open `U ⊆ D` whose complement is a finite set of closed points. If
`π₁(D)` is topologically finitely generated (at some geometric point), so is `π₁(C)`, at every
geometric point. (The proof, `isTopologicallyFG_etaleFundamentalGroup_of_pinching`, maps `π₁(D)`
continuously onto `π₁(C)`.)

SGA's IX.5.4 has instead `g` finite of finite presentation with one geometric point in the fibre
over each point outside a discrete set `T`, and no base field. -/
theorem isTopologicallyFG_etaleFundamentalGroup_of_isFinite_of_isIso_morphismRestrict
    (U : D.Opens) [IsIso (g ∣_ U)] (hU : (↑U : Set D)ᶜ.Finite)
    (hUc : ∀ d ∉ U, IsClosed ({d} : Set D)) {Ω₀ : Type u} [Field Ω₀] [IsSepClosed Ω₀]
    (s₀ : Spec (.of Ω₀) ⟶ D)
    (h : ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω₀ s₀))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ C) :
    ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup Ω s) := by
  have : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian τ
  have hDn : IsNoetherian D := { }
  have : ConnectedSpace D := g.surjective.connectedSpace g.continuous
  -- `g` is a monomorphism over `U`
  have hmono : Mono ((g ⁻¹ᵁ U).ι ≫ g) := by
    rw [← morphismRestrict_ι]
    infer_instance
  -- the projection `h : C ×_D C ⟶ D` and the structure morphism to `Spec k`
  set q : pullback g g ⟶ D := pullback.fst g g ≫ g
  have hoff : ∀ z ∈ Pinching.offDiag g, q z ∉ U := fun z hz hzU ↦
    hz (mem_range_diagonal_of_mono g hmono z hzU)
  have hZ : (Pinching.offDiag g).Finite := by
    refine (hU.preimage' fun d _ ↦ q.finite_preimage_singleton d).subset fun z hz ↦ ?_
    exact hoff z hz
  have hZc : ∀ z ∈ Pinching.offDiag g, IsClosed ({z} : Set ↥(pullback g g)) := fun z hz ↦
    q.isClosed_singleton_of_isClosed_singleton_apply (hUc _ (hoff z hz))
  have hZk : ∀ z ∈ Pinching.offDiag g, ∃ t : Spec (.of k) ⟶ pullback g g,
      t ≫ pullback.fst g g ≫ g ≫ τ = 𝟙 _ ∧ t (IsLocalRing.closedPoint k) = z := fun z hz ↦
    ⟨pointOfClosedPoint (pullback.fst g g ≫ g ≫ τ) z (hZc z hz), pointOfClosedPoint_comp _ _ _,
      pointOfClosedPoint_apply _ _ _ _⟩
  -- a `k`-point of `C`
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace g
  obtain ⟨c, -, hc⟩ := isClosed_univ.exists_closed_singleton (Set.univ_nonempty (α := C))
  let c₀ := pointOfClosedPoint (g ≫ τ) c hc
  -- the triple product
  set T := pullback (pullback.snd g g) (pullback.fst g g)
  let τ₃ : T ⟶ Spec (.of k) := tripleProj₂₁ g ≫ pullback.fst g g ≫ g ≫ τ
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace
    (tripleProj₂₁ g ≫ pullback.fst g g ≫ g)
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian τ₃
  have : IsNoetherian T := { }
  have := ExposeV.finite_connectedComponents_of_noetherianSpace T
  have hcc (c : ConnectedComponents T) : ∃ x : T, x ∈ ConnectedComponents.mk ⁻¹' {c} ∧
      IsClosed ({x} : Set T) := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    refine IsClosed.exists_closed_singleton ?_ ⟨x, rfl⟩
    rw [connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent
  choose x₃ hx₃ hx₃c using hcc
  let P₃ (c : ConnectedComponents T) : Spec (.of k) ⟶ T := pointOfClosedPoint τ₃ (x₃ c) (hx₃c c)
  have hP₃ (c : ConnectedComponents T) :
      ConnectedComponents.mk (P₃ c (IsLocalRing.closedPoint k)) = c := by
    have e := pointOfClosedPoint_apply τ₃ (x₃ c) (hx₃c c) (IsLocalRing.closedPoint k)
    simp only [P₃]
    rw [e]
    exact hx₃ c
  have hP₃k (c : ConnectedComponents T) :
      P₃ c ≫ tripleProj₂₁ g ≫ pullback.fst g g ≫ g ≫ τ = 𝟙 _ :=
    pointOfClosedPoint_comp τ₃ _ _
  -- conclude by the abstract form
  have hD : ExposeXIII.IsTopologicallyFG (ExposeV.etaleFundamentalGroup k (c₀ ≫ g)) :=
    (ExposeX.isTopologicallyFG_etaleFundamentalGroup_iff Ω₀ k s₀ (c₀ ≫ g)).mp h
  exact isTopologicallyFG_etaleFundamentalGroup_of_pinching hZ hZc τ hZk c₀ P₃ hP₃ hP₃k hD Ω s

end SGA.SGA1.ExposeIX
