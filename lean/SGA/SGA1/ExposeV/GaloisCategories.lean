/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Separation.Profinite
import SGA.Foundations.Pro.ContAction
import SGA.Foundations.Pro.Equivalence
import SGA.SGA1.ExposeV.GaloisAxioms

/-!
# SGA 1, Exposé V, §5: Galois categories

SGA defines a Galois category as a category equivalent to `C(π)` for a profinite group `π`
(V.5.1). By V.4.1 this is mathlib's `GaloisCategory`, and we prove the equivalence of the two
definitions (`galoisCategory_iff_exists_equivalence`); in the typical case `C = C(π)`, `π` is
the automorphism group of the forgetful fibre functor (`toAut_isHomeomorph_contAction`).

We then prove the results of §5 which mathlib lacks:

* V.5.3 and V.5.4: characterizations of connected objects by the action of `π`;
* V.5.5 and V.5.6 in functor form (a left exact functor `G` to finite sets instead of the
  functor `Hom(Q, -)` of a pro-object `Q`): `G` commutes with finite sums iff it is
  `X ↦ F(X)^H` for a closed subgroup `H` of `π`; it is a fibre functor iff it commutes with
  sums of two objects and is non-empty on non-initial objects;
* V.5.7: any two fibre functors are isomorphic and every morphism of fibre functors is an
  isomorphism, so the fibre functors form a connected groupoid `Γ`; `π_F` is determined up to
  inner automorphism, and the paths `Isom(F, F')` are principal homogeneous under `π_F`, `π_{F'}`;
* V.5.8: `X ↦ E_X` is an equivalence of `C` with the category of local systems on `Γ`;
* V.5.11: Galois objects correspond to open normal subgroups, and pointed principal homogeneous
  objects under a finite group `G` to continuous homomorphisms `π → G`.

We also prove the dictionary between pointed connected objects and open subgroups of `π_F`
used in §6 (stated in the discussion before V.6.4).

Pro-objects (`SGA.Foundations.Pro`): V.5.1 (fundamental pro-objects, the anti-equivalence with
fibre functors, `Aut F ≅ (Aut P)ᵒᵖ`), V.5.2 (`Pro C(π) ≃ C'(π)`, also for any Galois category
with a fibre functor), V.5.4 (iii), V.5.5 (all five conditions in the typical case) and V.5.6 for
pro-representations, V.5.9 (pro-objects as profinite local systems on the fundamental groupoid),
V.5.10, and V.5.11: the fundamental pro-group `Π` with its action on pro-objects, `F(Π) ≅ π_F`
functorially in `F`, the connectedness remark, and the objects `E_C`. The key step of V.5.2 is
also recorded as `exists_equivariant_factorization`.

Restrictions: V.5.9 and the constructions involving `Π` are stated for small categories (so that
`π_F` lies in the universe of the morphisms); in V.5.9 the profiniteness condition on a local
system is imposed at one fibre functor, which suffices by SGA's remark.
-/

universe u₁ u₂ v₁ v₂ v w

namespace SGA.SGA1.ExposeV

open CategoryTheory Limits PreGaloisCategory Functor

variable {C : Type u₁} [Category.{u₂} C]

/-! ### V.5.1: Galois categories -/

section Equivalence

variable {D : Type v₁} [Category.{v₂} D]

set_option backward.isDefEq.respectTransparency.types false in
/-- The axioms of a pre-Galois category are invariant under equivalence. -/
theorem preGaloisCategory_of_equiv (e : C ≌ D) [PreGaloisCategory D] :
    PreGaloisCategory C where
  hasTerminal := Adjunction.hasLimitsOfShape_of_equivalence e.functor
  hasPullbacks := Adjunction.hasLimitsOfShape_of_equivalence e.functor
  hasFiniteCoproducts := ⟨fun _ ↦ Adjunction.hasColimitsOfShape_of_equivalence e.functor⟩
  hasQuotientsByFiniteGroups _ _ _ := Adjunction.hasColimitsOfShape_of_equivalence e.functor
  monoInducesIsoOnDirectSummand {X Y} i _ := by
    obtain ⟨Z, u, ⟨hc⟩⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand (e.functor.map i)
    let u' : e.inverse.obj Z ⟶ Y := e.inverse.map u ≫ e.unitInv.app Y
    have hu' : e.functor.map u' = e.counit.app Z ≫ u := by simp [u']
    refine ⟨e.inverse.obj Z, u', ⟨isColimitOfReflects e.functor ?_⟩⟩
    refine (isColimitMapCoconeBinaryCofanEquiv e.functor i u').symm ?_
    rw [hu']
    exact (BinaryCofan.mk (e.functor.map i) u).isColimitCompRightIso (e.counit.app Z) hc

/-- A fibre functor composed with an equivalence is a fibre functor. -/
theorem fiberFunctor_comp_equivalence (e : C ≌ D) [PreGaloisCategory D] [PreGaloisCategory C]
    (F : D ⥤ FintypeCat.{w}) [FiberFunctor F] : FiberFunctor (e.functor ⋙ F) where
  preservesFiniteCoproducts := comp_preservesFiniteCoproducts _ _
  preservesQuotientsByFiniteGroups _ _ _ := inferInstance

/-- Being a Galois category is invariant under equivalence. -/
theorem galoisCategory_of_equiv (e : C ≌ D) [GaloisCategory D] : GaloisCategory C := by
  have := preGaloisCategory_of_equiv e
  have := fiberFunctor_comp_equivalence e (CategoryTheory.GaloisCategory.getFiberFunctor D)
  exact galoisCategory_of_fiberFunctor
    (e.functor ⋙ CategoryTheory.GaloisCategory.getFiberFunctor D)

open scoped FintypeCatDiscrete in
/-- V.5.1: SGA's definition of a Galois category (a category equivalent to the category `C(π)`
of finite sets with a continuous action of a profinite group `π`) agrees with mathlib's
`GaloisCategory`. -/
theorem galoisCategory_iff_exists_equivalence :
    GaloisCategory C ↔ ∃ (π : Type (max u₁ u₂)) (_ : Group π) (_ : TopologicalSpace π)
      (_ : IsTopologicalGroup π) (_ : CompactSpace π) (_ : T2Space π)
      (_ : TotallyDisconnectedSpace π), Nonempty (C ≌ ContAction FintypeCat.{u₂} π) := by
  refine ⟨fun _ ↦ ?_, fun ⟨π, _, _, _, _, _, _, ⟨e⟩⟩ ↦ galoisCategory_of_equiv e⟩
  let F := CategoryTheory.GaloisCategory.getFiberFunctor C
  exact ⟨Aut F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨equivalenceContAction F⟩⟩

end Equivalence

/-- A fibre functor isomorphic to a fibre functor is a fibre functor. -/
theorem fiberFunctor_of_natIso [PreGaloisCategory C] {F G : C ⥤ FintypeCat.{w}} [FiberFunctor F]
    (e : F ≅ G) : FiberFunctor G where
  preservesTerminalObjects := preservesLimitsOfShape_of_natIso e
  preservesPullbacks := preservesLimitsOfShape_of_natIso e
  preservesFiniteCoproducts := ⟨fun _ ↦ preservesColimitsOfShape_of_natIso e⟩
  preservesEpis := PreservesEpimorphisms.of_iso e
  preservesQuotientsByFiniteGroups _ _ _ := preservesColimitsOfShape_of_natIso e
  reflectsIsos := ⟨fun {X Y} f _ ↦ by
    have : IsIso (F.map f) := by
      rw [← NatIso.naturality_2 e f]
      infer_instance
    exact isIso_of_reflects_iso f F⟩

/-! ### V.5.3 and V.5.4: connected objects -/

section Connected

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- An object with non-empty fibre on which `Aut F` acts transitively is connected. -/
theorem isConnected_of_isPretransitive (X : C) [Nonempty (F.obj X)]
    [MulAction.IsPretransitive (Aut F) (F.obj X)] : IsConnected X where
  notInitial := (not_initial_iff_fiber_nonempty F X).2 inferInstance
  noTrivialComponent Y i _ hY := by
    obtain ⟨y⟩ := (not_initial_iff_fiber_nonempty F Y).1 hY
    have hs : Function.Surjective (F.map i) := fun x ↦ by
      obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (Aut F) (F.map i y) x
      exact ⟨σ • y, (mulAction_naturality F σ i y).symm⟩
    have : IsIso (F.map i) := (ConcreteCategory.isIso_iff_bijective _).2
      ⟨ConcreteCategory.injective_of_mono_of_preservesPullback (F.map i), hs⟩
    exact isIso_of_reflects_iso i F

/-- V.5.3: an object `X` is connected in the sense of SGA (it is not the sum of two non-initial
objects; the initial object is allowed) iff `π = Aut F` acts transitively on `F(X)`. -/
theorem isIndecomposable_iff_isPretransitive (X : C) :
    IsIndecomposable X ↔ MulAction.IsPretransitive (Aut F) (F.obj X) := by
  by_cases hX : Nonempty (F.obj X)
  · have hi : ¬ Nonempty (IsInitial X) := fun ⟨h⟩ ↦ (not_initial_iff_fiber_nonempty F X).2 hX h
    refine ⟨fun h ↦ ?_, fun _ ↦ ?_⟩
    · have := (isConnected_iff_isIndecomposable F X).2 ⟨h, hi⟩
      infer_instance
    · have := isConnected_of_isPretransitive F X
      exact fun {A B i j} hc ↦ ((isConnected_iff_isIndecomposable F X).1 this).1 hc
  · refine ⟨fun _ ↦ ⟨fun x ↦ (hX ⟨x⟩).elim⟩, fun _ {A B i j} _ ↦ Or.inl ?_⟩
    exact (initial_iff_fiber_empty F A).2 ⟨fun a ↦ hX ⟨F.map i a⟩⟩

/-- V.5.4: the following are equivalent: `X` is connected and not initial; `π` acts transitively
on `F(X)` and `F(X)` is non-empty; `X` is a quotient of a Galois object. SGA's condition (iii)
("`X` is isomorphic to a `P_i`") refers to a pro-object normalized to contain all connected
quotients of its terms; mathlib's pro-object is indexed by Galois objects only, so we state
(iii) as "`X` is a quotient of a Galois object". -/
theorem isConnected_tfae (X : C) :
    List.TFAE [IsConnected X,
      MulAction.IsPretransitive (Aut F) (F.obj X) ∧ Nonempty (F.obj X),
      ∃ (A : C) (_ : IsGalois A) (f : A ⟶ X), Epi f] := by
  tfae_have 1 → 2 := fun _ ↦ ⟨inferInstance, inferInstance⟩
  tfae_have 2 → 1 := fun ⟨_, _⟩ ↦ isConnected_of_isPretransitive F X
  tfae_have 1 → 3 := fun _ ↦ by
    obtain ⟨A, f, hA⟩ := exists_hom_from_galois_of_connected F X
    exact ⟨A, hA, f, epi_of_nonempty_of_isConnected F f⟩
  tfae_have 3 → 2 := fun ⟨A, _, f, _⟩ ↦ by
    have hs := surjective_on_fiber_of_epi F f
    obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
    refine ⟨⟨fun x y ↦ ?_⟩, ⟨F.map f a⟩⟩
    obtain ⟨b, rfl⟩ := hs x
    obtain ⟨c, rfl⟩ := hs y
    obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (Aut F) b c
    exact ⟨σ, mulAction_naturality F σ f b⟩
  tfae_finish

end Connected

/-! ### V.5.2: spaces with operators and finite quotients -/

/-- V.5.2, the key step of the proof: let `π` be a profinite group acting continuously on a
compact space `X`. Every continuous map `f` from `X` to a discrete space factors through a
`π`-equivariant continuous map from `X` to a finite discrete set with a continuous action of
`π`. (For `X` profinite this shows that `X` is the projective limit of its finite discrete
quotients with operators, i.e. that every compact totally disconnected space with operators
comes from a pro-object of `C(π)`.) -/
theorem exists_equivariant_factorization {π S : Type*} {X : Type v} [Group π] [TopologicalSpace π]
    [IsTopologicalGroup π] [CompactSpace π] [TotallyDisconnectedSpace π] [TopologicalSpace X]
    [CompactSpace X] [MulAction π X] [ContinuousSMul π X] [TopologicalSpace S]
    [DiscreteTopology S] (f : X → S) (hf : Continuous f) :
    ∃ (T : Type v) (_ : TopologicalSpace T) (_ : DiscreteTopology T) (_ : Finite T)
      (_ : MulAction π T) (_ : ContinuousSMul π T) (q : X → T) (h : T → S),
      Continuous q ∧ (∀ (g : π) (x : X), q (g • x) = g • q x) ∧ f = h ∘ q := by
  -- a neighbourhood of `1` whose elements preserve the fibres of `f`
  have hW : IsOpen {p : π × X | f (p.1 • p.2) = f p.2} :=
    (isOpen_discrete {p : S × S | p.1 = p.2}).preimage
      ((hf.comp continuous_smul).prodMk (hf.comp continuous_snd))
  obtain ⟨u, v, hu, -, hu1, hv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := 1))
    isCompact_univ hW (fun p hp ↦ by
      obtain ⟨h1, -⟩ := hp
      simp only [Set.mem_singleton_iff] at h1
      simp [h1])
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hu
    (hu1 rfl)
  have hNf (n : π) (hn : n ∈ N) (x : X) : f (n • x) = f x :=
    huv (Set.mk_mem_prod (hN hn) (hv (Set.mem_univ x)))
  have hNg (g n : π) (hn : n ∈ N) (x : X) : f (g • n • x) = f (g • x) := by
    have : g • n • x = (g * n * g⁻¹) • g • x := by simp [mul_smul]
    rw [this, hNf _ (N.isNormal'.conj_mem n hn g)]
  let r : Setoid X :=
    { r := fun x y ↦ ∀ g : π, f (g • x) = f (g • y)
      iseqv := ⟨fun _ _ ↦ rfl, fun h g ↦ (h g).symm, fun h h' g ↦ (h g).trans (h' g)⟩ }
  let T := Quotient r
  let _ : MulAction π T :=
    { smul := fun g ↦ Quotient.map (g • ·) fun x y h k ↦ by simpa only [smul_smul] using h (k * g)
      one_smul := Quotient.ind fun x ↦ congrArg (Quotient.mk r) (one_smul π x)
      mul_smul := fun g g' ↦ Quotient.ind fun x ↦ congrArg (Quotient.mk r) (mul_smul g g' x) }
  have hsmul (g : π) (x : X) : g • (Quotient.mk r x : T) = Quotient.mk r (g • x) := rfl
  let _ : TopologicalSpace T := ⊥
  have : DiscreteTopology T := ⟨rfl⟩
  have hfin : Finite T := by
    have : Finite (π ⧸ N.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
    have : Finite (Set.range f) := ((isCompact_range hf).finite_of_discrete).to_subtype
    let φ₀ (x : X) : π ⧸ N.toSubgroup → Set.range f := fun c ↦
      ⟨Quotient.liftOn' c (fun g ↦ f (g • x)) fun a b hab ↦ by
          have hab : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
          change f (a • x) = f (b • x)
          rw [show b = a * (a⁻¹ * b) from (mul_inv_cancel_left a b).symm, mul_smul,
            hNg _ _ hab],
        by induction c using QuotientGroup.induction_on with
          | H g => exact Set.mem_range_self _⟩
    let φ : T → (π ⧸ N.toSubgroup → Set.range f) := Quotient.lift φ₀
      fun x y hxy ↦ funext fun c ↦ Subtype.ext (by
        induction c using QuotientGroup.induction_on with | H g => exact hxy g)
    refine Finite.of_injective φ fun t t' h ↦ ?_
    induction t using Quotient.ind
    induction t' using Quotient.ind
    exact Quotient.sound fun g ↦ congrArg Subtype.val (congrFun h (QuotientGroup.mk g))
  have hcont : ContinuousSMul π T := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro t
    obtain ⟨x, rfl⟩ := Quotient.exists_rep t
    refine Subgroup.isOpen_mono (fun n hn ↦ ?_) N.isOpen'
    change Quotient.mk r (n • x) = Quotient.mk r x
    exact Quotient.sound fun g ↦ hNg g n hn x
  refine ⟨T, inferInstance, inferInstance, hfin, inferInstance, hcont, Quotient.mk r,
    Quotient.lift f fun x y hxy ↦ by simpa using (hxy : ∀ g : π, f (g • x) = f (g • y)) 1,
    ?_, fun g x ↦ rfl, rfl⟩
  rw [continuous_discrete_rng]
  intro t
  obtain ⟨x, rfl⟩ := Quotient.exists_rep t
  have : Finite (π ⧸ N.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
  have : Quotient.mk r ⁻¹' {Quotient.mk r x} =
      ⋂ c : π ⧸ N.toSubgroup, {y | f (c.out • y) = f (c.out • x)} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨fun h c ↦ Quotient.exact h c.out, fun h ↦ Quotient.sound fun g ↦ ?_⟩
    obtain ⟨⟨n, hn⟩, hgn⟩ := QuotientGroup.mk_out_eq_mul N.toSubgroup g
    have := h (QuotientGroup.mk g)
    rw [hgn, mul_smul, mul_smul, hNg _ _ hn, hNg _ _ hn] at this
    exact this
  rw [this]
  exact isOpen_iInter_of_finite fun c ↦ (isOpen_discrete {p : S × S | p.1 = p.2}).preimage
    ((hf.comp (continuous_const_smul _)).prodMk continuous_const)

/-! ### The typical case `C = C(π)` -/

section Quotient

open scoped FintypeCatDiscrete

variable {π : Type v} [Group π] [TopologicalSpace π] [IsTopologicalGroup π] [CompactSpace π]
  (U : OpenSubgroup π)

/-- The underlying type of the finite `π`-set `π/U`, in universe `w`. -/
abbrev QuotientCarrier : Type w := ULift.{w} (Fin (Nat.card (π ⧸ U.toSubgroup)))

/-- The identification of `QuotientCarrier U` with `π/U`. -/
noncomputable def quotientCarrierEquiv : QuotientCarrier.{v, w} U ≃ π ⧸ U.toSubgroup :=
  Equiv.ulift.trans (Finite.equivFin _).symm

noncomputable instance : MulAction π (QuotientCarrier.{v, w} U) :=
  (quotientCarrierEquiv U).mulAction π

lemma quotientCarrierEquiv_smul (g : π) (t : QuotientCarrier.{v, w} U) :
    quotientCarrierEquiv U (g • t) = g • quotientCarrierEquiv U t :=
  (quotientCarrierEquiv U).apply_symm_apply _

/-- The finite `π`-set `π/U` for an open subgroup `U` of a compact group `π`. -/
noncomputable def quotientAction : Action FintypeCat.{w} π :=
  Action.FintypeCat.ofMulAction π (FintypeCat.of (QuotientCarrier.{v, w} U))

lemma stabilizer_quotientAction (t : QuotientCarrier.{v, w} U) :
    (MulAction.stabilizer π (show (quotientAction.{v, w} U).V from t) : Set π) =
      MulAction.stabilizer π (quotientCarrierEquiv U t) := by
  ext g
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
  change g • t = t ↔ _
  rw [← quotientCarrierEquiv_smul, (quotientCarrierEquiv U).injective.eq_iff]

lemma isContinuous_quotientAction : (quotientAction.{v, w} U).IsContinuous := by
  rw [isContinuous_iff_isOpen_stabilizer]
  intro (t : QuotientCarrier.{v, w} U)
  rw [stabilizer_quotientAction]
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective (quotientCarrierEquiv U t)
  have : (MulAction.stabilizer π (quotientCarrierEquiv U t) : Set π) =
      (fun g ↦ (g * g₀)⁻¹ * g₀) ⁻¹' (U : Set π) := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage, ← hg₀]
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    rfl
  rw [this]
  exact U.isOpen.preimage (by fun_prop)

end Quotient

section Typical

open scoped FintypeCatDiscrete

variable {π : Type v} [Group π] [TopologicalSpace π] [IsTopologicalGroup π]

/-- The forgetful fibre functor of `C(π)`. -/
abbrev contActionForget (π : Type v) [Group π] [TopologicalSpace π] :
    ContAction FintypeCat.{w} π ⥤ FintypeCat.{w} :=
  ObjectProperty.ι _ ⋙ Action.forget _ _

instance (X : ContAction FintypeCat.{w} π) : MulAction π ((contActionForget π).obj X) :=
  inferInstanceAs (MulAction π X.obj.V)

set_option backward.isDefEq.respectTransparency.types false in
/-- A connected object of `C(π)` is a transitive `π`-set. -/
lemma isPretransitive_of_isConnected_contAction (X : ContAction FintypeCat.{w} π)
    [IsConnected X] : MulAction.IsPretransitive π X.obj.V := by
  let ι := ObjectProperty.ι (Action.IsContinuous : ObjectProperty (Action FintypeCat.{w} π))
  have : IsConnected (ι.obj X) := by
    refine ⟨fun h ↦ IsConnected.notInitial (IsInitial.isInitialOfObj ι _ h), fun Y i _ hY ↦ ?_⟩
    have hYc : Y.IsContinuous := ObjectProperty.prop_of_mono _ i X.property
    let Y' : ContAction FintypeCat.{w} π := ⟨Y, hYc⟩
    let i' : Y' ⟶ X := ObjectProperty.homMk i
    have : Mono i' := ι.mono_of_mono_map (inferInstanceAs (Mono i))
    have : IsIso i' :=
      IsConnected.noTrivialComponent Y' i' fun h ↦ hY (IsInitial.isInitialObj ι _ h)
    exact inferInstanceAs (IsIso (ι.map i'))
  exact FintypeCat.Action.pretransitive_of_isConnected π (ι.obj X)

variable [CompactSpace π] [T2Space π] [TotallyDisconnectedSpace π]

set_option backward.isDefEq.respectTransparency.types false in
/-- V.5.1, V.5.7 (typical case `C = C(π)`): a profinite group `π` is the fundamental group of
the forgetful fibre functor of `C(π)`. -/
instance : IsFundamentalGroup (contActionForget.{v, w} π) π where
  naturality g _ _ f x := Action.hom_smul f.hom g x
  transitive_of_isGalois X _ := isPretransitive_of_isConnected_contAction X
  continuous_smul X := X.property
  non_trivial' g h := by
    by_contra hg
    obtain ⟨W, ⟨hW1, hWc⟩, hW⟩ := (nhds_basis_clopen (1 : π)).mem_iff.1
      (isOpen_compl_singleton.mem_nhds (Ne.symm hg))
    obtain ⟨U, hU⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hWc hW1
    have hgU : g ∉ U := fun hgU ↦ hW (hU hgU) rfl
    let X : ContAction FintypeCat.{w} π := ⟨quotientAction.{v, w} U, isContinuous_quotientAction U⟩
    let t : QuotientCarrier.{v, w} U := (quotientCarrierEquiv U).symm (QuotientGroup.mk 1)
    have := h X t
    change g • t = t at this
    apply hgU
    have h2 := congrArg (quotientCarrierEquiv U) this
    rw [quotientCarrierEquiv_smul, Equiv.apply_symm_apply, MulAction.Quotient.smul_coe,
      smul_eq_mul, mul_one, QuotientGroup.eq, mul_one] at h2
    simpa using U.inv_mem h2

/-- V.5.1, V.5.7 (typical case `C = C(π)`): for a profinite group `π`, the canonical map
`π → Aut(forget)` to the automorphism group of the forgetful fibre functor of `C(π)` is an
isomorphism of topological groups. -/
theorem toAut_isHomeomorph_contAction :
    IsHomeomorph (toAut (contActionForget.{v, w} π) π) :=
  toAut_isHomeomorph _ _

end Typical

/-! ### Pointed connected objects and open subgroups

SGA 1 V.6, before V.6.4: "the connected pointed objects of `C` are identified with the open
subgroups of `π_F`. If `U`, `V` are the subgroups corresponding to connected pointed objects
`X`, `Y`, there is a pointed morphism `X → Y` iff `U ⊆ V`, and it is then unique." -/

section Pointed

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

set_option backward.isDefEq.respectTransparency.types false in
/-- V.6: for connected pointed `(X, x)` and pointed `(Y, y)` there is a morphism `f : X ⟶ Y`
with `F(f)(x) = y` iff the stabilizer of `x` is contained in that of `y`. -/
theorem exists_hom_iff_stabilizer_le {X Y : C} [IsConnected X] (x : F.obj X) (y : F.obj Y) :
    (∃ f : X ⟶ Y, F.map f x = y) ↔
      MulAction.stabilizer (Aut F) x ≤ MulAction.stabilizer (Aut F) y := by
  refine ⟨fun ⟨f, hf⟩ σ (hσ : σ • x = x) ↦ ?_, fun h ↦ ?_⟩
  · change σ • y = y
    rw [← hf, mulAction_naturality, hσ]
  · choose τ hτ using fun z : F.obj X ↦ MulAction.exists_smul_eq (Aut F) x z
    have key (σ : Aut F) : τ (σ • x) • y = σ • y := by
      have : σ⁻¹ * τ (σ • x) ∈ MulAction.stabilizer (Aut F) x := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, hτ, inv_smul_smul]
      have := h this
      rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff] at this
      exact this
    let φ : (functorToAction F).obj X ⟶ (functorToAction F).obj Y :=
      { hom := FintypeCat.homMk fun z ↦ τ z • y
        comm := fun σ ↦ by
          ext (z : F.obj X)
          change τ (σ • z) • y = σ • τ z • y
          calc τ (σ • z) • y = τ ((σ * τ z) • x) • y := by rw [mul_smul, hτ]
            _ = (σ * τ z) • y := key _
            _ = σ • τ z • y := mul_smul _ _ _ }
    obtain ⟨f, hf⟩ := (functorToAction F).map_surjective φ
    refine ⟨f, ?_⟩
    change ((functorToAction F).map f).hom x = y
    rw [hf]
    change τ x • y = y
    simpa using key 1

/-- V.6: a pointed morphism between connected pointed objects is unique. -/
theorem hom_ext_of_isConnected {X Y : C} [IsConnected X] (x : F.obj X) {f g : X ⟶ Y}
    (h : F.map f x = F.map g x) : f = g :=
  evaluation_injective_of_isConnected F X Y x h

lemma injective_hom_of_iso {G : Type*} [Group G] {A B : Action FintypeCat.{w} G} (e : A ≅ B) :
    Function.Injective e.hom.hom := by
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((Action.forget _ _).mapIso e).hom)
  exact ConcreteCategory.injective_of_mono_of_preservesPullback _

/-- Stabilizers are invariant under isomorphisms of finite `G`-sets. -/
lemma stabilizer_hom_apply {G : Type*} [Group G] {A B : Action FintypeCat.{w} G} (e : A ≅ B)
    (a : A.V) : MulAction.stabilizer G (e.hom.hom a) = MulAction.stabilizer G a := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, ← Action.hom_smul, (injective_hom_of_iso e).eq_iff]

/-- Transitivity is invariant under isomorphisms of finite `G`-sets. -/
lemma isPretransitive_of_iso {G : Type*} [Group G] {A B : Action FintypeCat.{w} G} (e : A ≅ B)
    [MulAction.IsPretransitive G B.V] : MulAction.IsPretransitive G A.V where
  exists_smul_eq a b := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (e.hom.hom a) (e.hom.hom b)
    exact ⟨g, injective_hom_of_iso e (by rw [Action.hom_smul, hg])⟩

open scoped FintypeCatDiscrete in
set_option backward.isDefEq.respectTransparency.types false in
/-- V.6: every open subgroup of `π_F` is the stabilizer of a point of the fibre of a connected
object. -/
theorem exists_isConnected_stabilizer_eq (V : OpenSubgroup (Aut F)) :
    ∃ (X : C) (x : F.obj X), IsConnected X ∧ MulAction.stabilizer (Aut F) x = V := by
  let e := quotientCarrierEquiv.{_, w} V
  let T' : ContAction FintypeCat.{w} (Aut F) :=
    ⟨quotientAction.{_, w} V, isContinuous_quotientAction V⟩
  let X := (functorToContAction F).objPreimage T'
  let i' : (functorToAction F).obj X ≅ quotientAction.{_, w} V :=
    (ObjectProperty.ι _).mapIso ((functorToContAction F).objObjPreimageIso T')
  let x : F.obj X := i'.inv.hom (e.symm (QuotientGroup.mk 1))
  have hx : MulAction.stabilizer (Aut F) x = V := by
    change MulAction.stabilizer (Aut F) (i'.symm.hom.hom _) = _
    rw [stabilizer_hom_apply i'.symm]
    apply SetLike.coe_injective
    rw [stabilizer_quotientAction, Equiv.apply_symm_apply]
    exact congrArg _ (MulAction.stabilizer_quotient V.toSubgroup)
  have : Nonempty (F.obj X) := ⟨x⟩
  have : MulAction.IsPretransitive (Aut F) (quotientAction.{_, w} V).V := ⟨fun t₁ t₂ ↦ by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut F) (e t₁) (e t₂)
    exact ⟨g, e.injective ((quotientCarrierEquiv_smul V g t₁).trans hg)⟩⟩
  have : MulAction.IsPretransitive (Aut F) (F.obj X) := isPretransitive_of_iso i'
  exact ⟨X, x, isConnected_of_isPretransitive F X, hx⟩

end Pointed

/-! ### V.5.6 and V.5.7: fibre functors form a connected groupoid -/

section FiberFunctors

variable [GaloisCategory C]

set_option backward.isDefEq.respectTransparency.types false in
/-- A fibre functor `F` admits a morphism to every functor `G` to finite sets whose values on
Galois objects are non-empty: a compatible family of points of the `G(A)`, for `A` running over
the pointed Galois objects of `F`, exists by compactness, and `F` is pro-represented by the
pointed Galois objects (V.4 c)). -/
theorem nonempty_hom_of_isGalois_nonempty (F : C ⥤ FintypeCat.{u₂}) [FiberFunctor F]
    (G : C ⥤ FintypeCat.{u₂}) (hG : ∀ (A : C) [IsGalois A], Nonempty (G.obj A)) :
    Nonempty (F ⟶ G) := by
  let D := PointedGaloisObject.incl F ⋙ G ⋙ FintypeCat.incl
  have (A : PointedGaloisObject F) : Nonempty (D.obj A) := hG A.obj
  have (A : PointedGaloisObject F) : Finite (D.obj A) := inferInstanceAs (Finite (G.obj A.obj))
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system D
  let c : Cocone ((PointedGaloisObject.incl F).op ⋙ coyoneda) :=
    { pt := G ⋙ FintypeCat.incl
      ι :=
        { app := fun A ↦ { app := fun X ↦ ↾fun (f : A.unop.obj ⟶ X) ↦ G.map f (s A.unop) }
          naturality := fun A B g ↦ by
            ext X (f : A.unop.obj ⟶ X)
            change G.map (g.unop.val ≫ f) (s B.unop) = G.map f (s A.unop)
            rw [G.map_comp, FintypeCat.comp_apply]
            congr 1
            exact hs g.unop } }
  exact ⟨((Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl).whiskeringRight C).preimage
    ((PointedGaloisObject.isColimit F).desc c)⟩

/-- `nonempty_hom_of_isGalois_nonempty` for functors to finite sets in any universe. -/
theorem nonempty_hom_of_isGalois_nonempty' (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (G : C ⥤ FintypeCat.{w}) (hG : ∀ (A : C) [IsGalois A], Nonempty (G.obj A)) :
    Nonempty (F ⟶ G) := by
  let e := FintypeCat.uSwitchEquivalence.{w, u₂}
  have : FiberFunctor (F ⋙ e.functor) := FiberFunctor.comp_right _
  obtain ⟨t⟩ := nonempty_hom_of_isGalois_nonempty (F ⋙ e.functor) (G ⋙ e.functor)
    fun A _ ↦ ⟨(FintypeCat.uSwitchEquiv (G.obj A)).symm (hG A).some⟩
  exact ⟨(e.fullyFaithfulFunctor.whiskeringRight C).preimage t⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- V.5.7 (and V.4 h)): every morphism between fibre functors is an isomorphism. -/
theorem isIso_of_fiberFunctor {F F' : C ⥤ FintypeCat.{w}} [FiberFunctor F] [FiberFunctor F']
    (t : F ⟶ F') : IsIso t := by
  suffices ∀ X, IsIso (t.app X) from NatIso.isIso_of_isIso_app t
  intro X
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy ↦ ?_, fun x' ↦ ?_⟩
  · obtain ⟨A, h, a, _, ha⟩ := exists_hom_from_galois_of_fiber F (X ⨯ X)
      ((fiberBinaryProductEquiv F X X).symm (x, y))
    have hx : F.map (h ≫ prod.fst) a = x := by simp [ha]
    have hy : F.map (h ≫ prod.snd) a = y := by simp [ha]
    have : h ≫ prod.fst = h ≫ prod.snd := by
      apply evaluation_injective_of_isConnected F' A X (t.app A a)
      simp only
      rw [← FunctorToFintypeCat.naturality, ← FunctorToFintypeCat.naturality, hx, hy, hxy]
    rw [← hx, ← hy, this]
  · obtain ⟨A, f, a', _, ha'⟩ := exists_hom_from_galois_of_fiber F' X x'
    obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut A) (t.app A a) a'
    refine ⟨F.map (σ.hom ≫ f) a, ?_⟩
    rw [FunctorToFintypeCat.naturality, F'.map_comp, FintypeCat.comp_apply]
    change F'.map f (σ • t.app A a) = x'
    rw [hσ, ha']

/-- V.5.7: any two fibre functors of a Galois category are isomorphic. -/
theorem nonempty_iso_of_fiberFunctor (F F' : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    [FiberFunctor F'] : Nonempty (F ≅ F') := by
  obtain ⟨t⟩ := nonempty_hom_of_isGalois_nonempty' F F'
    fun A _ ↦ nonempty_fiber_of_isConnected F' A
  have := isIso_of_fiberFunctor t
  exact ⟨asIso t⟩

section Functor

variable (G : C ⥤ FintypeCat.{w})

omit [GaloisCategory C] in
/-- A functor to finite sets commuting with the sum of two objects sends initial objects to
empty sets (since `∅ ⨿ ∅ = ∅` with equal inclusions). -/
lemma isEmpty_obj_of_isInitial [PreservesColimitsOfShape (Discrete WalkingPair) G] {I : C}
    (hI : IsInitial I) : IsEmpty (G.obj I) := by
  have hc : IsColimit (BinaryCofan.mk (𝟙 I) (𝟙 I)) :=
    ((BinaryCofan.isColimit_iff_isIso_inl hI _).2 (inferInstanceAs (IsIso (𝟙 I)))).some
  exact ⟨fun a ↦ Set.disjoint_left.1 (disjoint_range_map_of_isColimit G hc) ⟨a, rfl⟩ ⟨a, rfl⟩⟩

omit [GaloisCategory C] in
set_option backward.isDefEq.respectTransparency.types false in
lemma exists_map_fst_snd {A X : C} [HasBinaryProduct A X] [PreservesLimit (pair A X) G]
    (a : G.obj A) (x : G.obj X) :
    ∃ z : G.obj (A ⨯ X), G.map prod.fst z = a ∧ G.map prod.snd z = x := by
  have h := (isLimitMapConeBinaryFanEquiv (G ⋙ FintypeCat.incl) prod.fst prod.snd)
    (isLimitOfPreserves (G ⋙ FintypeCat.incl) (prodIsProd A X))
  obtain ⟨l, h₁, h₂⟩ := BinaryFan.IsLimit.lift' h (↾fun _ : PUnit.{w + 1} ↦ a) (↾fun _ ↦ x)
  exact ⟨l PUnit.unit, ConcreteCategory.congr_hom h₁ PUnit.unit,
    ConcreteCategory.congr_hom h₂ PUnit.unit⟩

omit [GaloisCategory C] in
set_option backward.isDefEq.respectTransparency.types false in
lemma ext_map_fst_snd {A X : C} [HasBinaryProduct A X] [PreservesLimit (pair A X) G]
    {z₁ z₂ : G.obj (A ⨯ X)} (h₁ : G.map prod.fst z₁ = G.map prod.fst z₂)
    (h₂ : G.map prod.snd z₁ = G.map prod.snd z₂) : z₁ = z₂ := by
  have h := (isLimitMapConeBinaryFanEquiv (G ⋙ FintypeCat.incl) prod.fst prod.snd)
    (isLimitOfPreserves (G ⋙ FintypeCat.incl) (prodIsProd A X))
  have := BinaryFan.IsLimit.hom_ext h (f := ↾fun _ : PUnit.{w + 1} ↦ z₁)
    (g := ↾fun _ : PUnit.{w + 1} ↦ z₂) (by ext; exact h₁) (by ext; exact h₂)
  exact ConcreteCategory.congr_hom this PUnit.unit

omit [GaloisCategory C] in
lemma exists_map_sigmaι {J : Type*} [Finite J] (f : J → C) [HasCoproduct f]
    [PreservesColimit (Discrete.functor f) G] (z : G.obj (∐ f)) :
    ∃ j b, G.map (Sigma.ι f j) b = z := by
  obtain ⟨⟨j⟩, b, hb⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (G ⋙ FintypeCat.incl) (coproductIsCoproduct f)) z
  exact ⟨j, b, hb⟩

variable [PreservesFiniteLimits G] [PreservesColimitsOfShape (Discrete WalkingPair) G]

set_option backward.isDefEq.respectTransparency.types false in
/-- For `G` left exact and commuting with sums of two objects, evaluation at a point of `G(A)`
is injective on morphisms out of a connected object `A`. -/
lemma evaluation_injective_of_leftExact (A X : C) [IsConnected A] (b : G.obj A) :
    Function.Injective fun f : A ⟶ X ↦ G.map f b := by
  intro f g (h : G.map f b = G.map g b)
  let e := (PreservesEqualizer.iso (G ⋙ FintypeCat.incl) f g ≪≫
    Types.equalizerIso (G.map f).hom (G.map g).hom).toEquiv
  have : IsIso (equalizer.ι f g) := by
    apply IsConnected.noTrivialComponent _ (equalizer.ι f g)
    exact fun hI ↦ (isEmpty_obj_of_isInitial G hI).false (e.symm ⟨b, h⟩)
  exact eq_of_epi_equalizer

variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

set_option backward.isDefEq.respectTransparency.types false in
/-- V.5.6, (iii) ⇒ (i), in functor form: a left exact functor `G` from a Galois category to
finite sets which commutes with sums of two objects and takes non-empty values on non-initial
objects is isomorphic to any fibre functor `F` (hence is a fibre functor). SGA phrases this for
the functor `Hom(P', -)` of a pro-object `P'`; every left exact functor to finite sets on an
artinian category is of this form. -/
theorem nonempty_iso_of_leftExact (hG : ∀ X : C, (IsInitial X → False) → Nonempty (G.obj X)) :
    Nonempty (F ≅ G) := by
  have hGal (A : C) [IsGalois A] : Nonempty (G.obj A) := hG A IsConnected.notInitial
  obtain ⟨t⟩ := nonempty_hom_of_isGalois_nonempty' F G fun A _ ↦ hGal A
  have : PreservesColimitsOfShape (Discrete PEmpty.{1}) G := by
    have hI : IsInitial (G.obj (⊥_ C)) :=
      ((Concrete.initial_iff_empty_of_preserves_of_reflects _).2
        (isEmpty_obj_of_isInitial G initialIsInitial)).some
    have := preservesInitial_of_iso G (initialIsInitial.uniqueUpToIso hI)
    exact preservesColimitsOfShape_pempty_of_preservesInitial G
  have hcoprod (J : Type u₂) [Finite J] : PreservesColimitsOfShape (Discrete J) G :=
    PreservesFiniteCoproducts.of_preserves_binary_and_initial G J
  suffices ∀ X, IsIso (t.app X) by
    have := NatIso.isIso_of_isIso_app t
    exact ⟨asIso t⟩
  intro X
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy ↦ ?_, fun x' ↦ ?_⟩
  · obtain ⟨A, h, a, _, ha⟩ := exists_hom_from_galois_of_fiber F (X ⨯ X)
      ((fiberBinaryProductEquiv F X X).symm (x, y))
    have hx : F.map (h ≫ prod.fst) a = x := by simp [ha]
    have hy : F.map (h ≫ prod.snd) a = y := by simp [ha]
    have : h ≫ prod.fst = h ≫ prod.snd := by
      apply evaluation_injective_of_leftExact G A X (t.app A a)
      simp only
      rw [← FunctorToFintypeCat.naturality, ← FunctorToFintypeCat.naturality, hx, hy, hxy]
    rw [← hx, ← hy, this]
  · -- `A × X` is the sum of copies of `A` indexed by `Hom(A, X)`, for a Galois `A` representing
    -- the fibre of `X`; `G` commutes with this decomposition.
    obtain ⟨A, a, _, hbij⟩ := exists_galois_representative F X
    have := hcoprod (A ⟶ X)
    let φ : ∐ (fun _ : A ⟶ X ↦ A) ⟶ A ⨯ X := Sigma.desc fun h ↦ prod.lift (𝟙 A) h
    have hφ (K : C ⥤ FintypeCat.{w}) (h : A ⟶ X) (b : K.obj A) :
        K.map φ (K.map (Sigma.ι _ h) b) = K.map (prod.lift (𝟙 A) h) b := by
      rw [← FintypeCat.comp_apply, ← K.map_comp, Sigma.ι_desc]
    have hfst (K : C ⥤ FintypeCat.{w}) (h : A ⟶ X) (b : K.obj A) :
        K.map prod.fst (K.map (prod.lift (𝟙 A) h) b) = b := by
      rw [← FintypeCat.comp_apply, ← K.map_comp, prod.lift_fst, K.map_id, FintypeCat.id_apply]
    have hsnd (K : C ⥤ FintypeCat.{w}) (h : A ⟶ X) (b : K.obj A) :
        K.map prod.snd (K.map (prod.lift (𝟙 A) h) b) = K.map h b := by
      rw [← FintypeCat.comp_apply, ← K.map_comp, prod.lift_snd]
    have : IsIso φ := by
      have : IsIso (F.map φ) := by
        rw [ConcreteCategory.isIso_iff_bijective]
        refine ⟨fun z₁ z₂ hz ↦ ?_, fun z ↦ ?_⟩
        · obtain ⟨h₁, a₁, rfl⟩ := exists_map_sigmaι F _ z₁
          obtain ⟨h₂, a₂, rfl⟩ := exists_map_sigmaι F _ z₂
          rw [hφ, hφ] at hz
          have e₁ := congrArg (F.map prod.fst) hz
          have e₂ := congrArg (F.map prod.snd) hz
          rw [hfst, hfst] at e₁
          rw [hsnd, hsnd] at e₂
          subst e₁
          obtain rfl := evaluation_injective_of_isConnected F A X a₁ e₂
          rfl
        · obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut A) (F.map prod.fst z) a
          obtain ⟨h₀, hh₀⟩ := hbij.2 (F.map prod.snd z)
          refine ⟨F.map (Sigma.ι _ (σ.hom ≫ h₀)) (F.map prod.fst z), ?_⟩
          rw [hφ]
          apply ext_map_fst_snd F
          · rw [hfst]
          · rw [hsnd, F.map_comp, FintypeCat.comp_apply]
            change F.map h₀ (σ • F.map prod.fst z) = _
            rw [hσ]
            exact hh₀
      exact isIso_of_reflects_iso φ F
    obtain ⟨p, hp₁, hp₂⟩ := exists_map_fst_snd G (t.app A a) x'
    obtain ⟨h, b, hb⟩ := exists_map_sigmaι G _ (G.map (inv φ) p)
    have hb' : G.map (prod.lift (𝟙 A) h) b = p := by
      rw [← hφ, hb, ← FintypeCat.comp_apply, ← G.map_comp, IsIso.inv_hom_id, G.map_id,
        FintypeCat.id_apply]
    refine ⟨F.map h a, ?_⟩
    rw [FunctorToFintypeCat.naturality, ← hp₂, ← hb', hsnd]
    congr 1
    rw [← hp₁, ← hb', hfst]

end Functor

end FiberFunctors

/-! ### The fundamental groupoid, change of fibre functor and paths -/

section Groupoid

variable (C) [GaloisCategory C]

/-- After V.5.7: the category of fibre functors of `C` (with values in finite sets of universe
`w`), SGA's fundamental groupoid `Γ`. -/
abbrev FiberFunctors : Type _ :=
  ObjectProperty.FullSubcategory fun F : C ⥤ FintypeCat.{w} ↦ FiberFunctor F

instance (F : FiberFunctors.{u₁, u₂, w} C) : FiberFunctor F.obj := F.property

/-- V.5.7: every morphism of the category of fibre functors is an isomorphism. -/
instance (F G : FiberFunctors.{u₁, u₂, w} C) (t : F ⟶ G) : IsIso t := by
  have : IsIso ((ObjectProperty.ι _).map t) := isIso_of_fiberFunctor t.hom
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map t

/-- V.5.7: the category of fibre functors is a groupoid. -/
noncomputable instance : Groupoid (FiberFunctors.{u₁, u₂, w} C) :=
  Groupoid.ofIsIso fun _ ↦ inferInstance

/-- V.5.7: the fundamental groupoid is non-empty. -/
instance : Nonempty (FiberFunctors.{u₁, u₂, w} C) :=
  ⟨⟨CategoryTheory.GaloisCategory.getFiberFunctor C ⋙ FintypeCat.uSwitch.{u₂, w},
    FiberFunctor.comp_right _⟩⟩

/-- V.5.7: the fundamental groupoid is connected: any two fibre functors are isomorphic. -/
theorem nonempty_iso_fiberFunctors (F G : FiberFunctors.{u₁, u₂, w} C) : Nonempty (F ≅ G) :=
  (nonempty_iso_of_fiberFunctor F.obj G.obj).map
    ((ObjectProperty.fullyFaithfulι _).preimageIso)

end Groupoid

/-! ### V.5.1: fundamental pro-objects -/

section ProObjects

open Opposite

variable [GaloisCategory C]

/-- V.5.1: a pro-object `P` of a Galois category is fundamental if the functor
`Hom(P, -) : C ⥤ Type` it pro-represents is (isomorphic to) a fibre functor. -/
def IsFundamentalProObject (P : Pro C) : Prop :=
  ∃ (F : C ⥤ FintypeCat.{u₂}) (_ : FiberFunctor F),
    Nonempty (F ⋙ FintypeCat.incl ≅ (Pro.coyoneda C).obj (op P))

/-- V.5.1: every fibre functor `F` is pro-representable by a pro-object `P_F` (V.4 c)), which is
then a fundamental pro-object. As everywhere in SGA, `C` is assumed essentially small. -/
theorem exists_iso_coyoneda [EssentiallySmall.{u₂} C] (F : C ⥤ FintypeCat.{u₂})
    [FiberFunctor F] :
    ∃ P : Pro C, Nonempty (F ⋙ FintypeCat.incl ≅ (Pro.coyoneda C).obj (op P)) := by
  obtain ⟨P, ⟨e⟩⟩ := Functor.isProRepresentable_iff_mem_essImage.1
    (isStrictlyProRepresentable_fiberFunctor F).isProRepresentable
  exact ⟨P.unop, ⟨e.symm⟩⟩

variable (C) in
/-- V.5.1: the category of fundamental pro-objects. -/
abbrev FundamentalProObjects : Type _ :=
  ObjectProperty.FullSubcategory (IsFundamentalProObject (C := C))

variable (C) in
/-- The functor pro-represented by a fundamental pro-object. -/
noncomputable abbrev fundamentalProObjectsCoyoneda :
    (FundamentalProObjects C)ᵒᵖ ⥤ C ⥤ Type u₂ :=
  (ObjectProperty.ι _).op ⋙ Pro.coyoneda C

variable (C) in
/-- The functor `F ↦ F` from fibre functors to functors `C ⥤ Type`. -/
noncomputable abbrev fiberFunctorsToTypes : FiberFunctors.{u₁, u₂, u₂} C ⥤ C ⥤ Type u₂ :=
  ObjectProperty.ι _ ⋙ (Functor.whiskeringRight C _ _).obj FintypeCat.incl

instance : ((Functor.whiskeringRight C _ _).obj FintypeCat.incl.{u₂}).Full :=
  ((Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl).whiskeringRight C).full

instance : ((Functor.whiskeringRight C _ _).obj FintypeCat.incl.{u₂}).Faithful :=
  ((Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl).whiskeringRight C).faithful

variable [EssentiallySmall.{u₂} C]

lemma fiberFunctorsToTypes_obj_mem_essImage (F : FiberFunctors.{u₁, u₂, u₂} C) :
    (fundamentalProObjectsCoyoneda C).essImage ((fiberFunctorsToTypes C).obj F) := by
  obtain ⟨P, ⟨e⟩⟩ := exists_iso_coyoneda F.obj
  exact ⟨op ⟨P, F.obj, F.property, ⟨e⟩⟩, ⟨e.symm⟩⟩

variable (C) in
/-- The functor from fibre functors to the essential image of `fundamentalProObjectsCoyoneda`. -/
noncomputable def fiberFunctorsLift :
    FiberFunctors.{u₁, u₂, u₂} C ⥤ (fundamentalProObjectsCoyoneda C).EssImageSubcategory :=
  ObjectProperty.lift _ (fiberFunctorsToTypes C) fiberFunctorsToTypes_obj_mem_essImage

instance : (fiberFunctorsLift C).Full :=
  Functor.Full.of_comp_faithful_iso (ObjectProperty.liftCompιIso _ _ _)

instance : (fiberFunctorsLift C).Faithful :=
  Functor.Faithful.of_comp_iso (ObjectProperty.liftCompιIso _ _ _)

instance : (fiberFunctorsLift C).EssSurj where
  mem_essImage Y := by
    obtain ⟨P, ⟨e⟩⟩ := Y.property
    obtain ⟨F, _, ⟨e'⟩⟩ := P.unop.property
    exact ⟨⟨F, inferInstance⟩, ⟨ObjectProperty.isoMk _ (e' ≪≫ e)⟩⟩

instance : (fiberFunctorsLift C).IsEquivalence where

variable (C) in
/-- V.5.1: the category of fibre functors of `C` (the fundamental groupoid) is anti-equivalent to
the category of fundamental pro-objects, via `F ↦ P_F`. -/
noncomputable def fiberFunctorsEquivalence :
    FiberFunctors.{u₁, u₂, u₂} C ≌ (FundamentalProObjects C)ᵒᵖ :=
  (fiberFunctorsLift C).asEquivalence.trans
    (fundamentalProObjectsCoyoneda C).toEssImage.asEquivalence.symm

omit [EssentiallySmall.{u₂} C] in
/-- The automorphism group of `op X` is the opposite of the automorphism group of `X`. -/
@[simps]
def autOpMulEquiv {D : Type*} [Category* D] (X : D) : Aut (op X) ≃* (Aut X)ᵐᵒᵖ where
  toFun σ := MulOpposite.op σ.unop
  invFun σ := σ.unop.op
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [EssentiallySmall.{u₂} C] in
/-- V.5.1: if `F` is pro-represented by `P`, the fundamental group `π = Aut F` is the opposite of
the group `Aut P` of automorphisms of the pro-object `P`. -/
noncomputable def autMulEquivAutProObject (F : C ⥤ FintypeCat.{u₂}) {P : Pro C}
    (e : F ⋙ FintypeCat.incl ≅ (Pro.coyoneda C).obj (op P)) : Aut F ≃* (Aut P)ᵐᵒᵖ :=
  (((Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl).whiskeringRight
    C).autMulEquivOfFullyFaithful F).trans <| (Aut.autMulEquivOfIso e).trans <|
      ((Pro.coyonedaFullyFaithful C).autMulEquivOfFullyFaithful (op P)).symm.trans
        (autOpMulEquiv P)

end ProObjects

/-! ### V.5.2: pro-objects of `C(π)` -/

section TypicalPro

open Opposite ContAction
open scoped FintypeCatDiscrete

variable (π : Type v) [Group π] [TopologicalSpace π] [IsTopologicalGroup π] [CompactSpace π]
  [TotallyDisconnectedSpace π]

/-- V.5.2: for a profinite group `π`, the category of pro-objects of `C(π)` is equivalent to the
category `C'(π)` of profinite spaces with a continuous action of `π`. The equivalence sends
`“lim” Q_i` to `lim Q_i` (`ContAction.proEquivalenceFunctorObjLimIso`) and restricts to the
identity on `C(π)` (`ContAction.proEquivalenceFunctorObjOfIso`); its inverse sends `X` to the
pro-object representing `E ↦ Hom(X, E)` (`ContAction.coyonedaObjProEquivalenceInverseIso`). -/
noncomputable abbrev proContActionEquivalence :
    Pro (ContAction FintypeCat.{w} π) ≌ ContAction Profinite.{w} π :=
  ContAction.proEquivalence π

variable [T2Space π]

/-- V.5.1 (typical case `C = C(π)`, `F` the forgetful functor): the fundamental pro-object is
`π` itself, i.e. the projective system of the discrete quotients of `π`. -/
noncomputable def contActionForgetIsoCoyoneda :
    contActionForget.{v, v} π ⋙ FintypeCat.incl ≅
      (Pro.coyoneda _).obj (op ((proEquivalence π).inverse.obj (regular π))) :=
  (homFunctorObjRegularIso π).symm ≪≫ (coyonedaObjProEquivalenceInverseIso _).symm

/-- V.5.1 (typical case): `π`, as a pro-object of `C(π)`, is a fundamental pro-object. -/
theorem isFundamentalProObject_regular :
    IsFundamentalProObject ((proEquivalence π).inverse.obj (regular π)) :=
  ⟨contActionForget π, inferInstance, ⟨contActionForgetIsoCoyoneda π⟩⟩

end TypicalPro

/-! ### V.5.2 for a Galois category; the fundamental pro-object and pro-group (V.5.11) -/

section ProEquivalence

open Opposite ContAction
open scoped FintypeCatDiscrete

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{u₂}) [FiberFunctor F]

/-- V.5.2, for a Galois category `C` identified with `C(π)`, `π = Aut F`, by V.4.1: the category of
pro-objects of `C` is equivalent to the category of profinite spaces with a continuous action of
`π`. The equivalence extends `F` (`proEquivalenceOfFiberFunctorObjOfIso`): it sends a pro-object
`P = “lim” P_i` to the profinite `π`-space `F(P) = lim F(P_i)`. -/
noncomputable def proEquivalenceOfFiberFunctor : Pro C ≌ ContAction Profinite.{u₂} (Aut F) :=
  (Pro.congr (equivalenceContAction F)).trans (ContAction.proEquivalence (Aut F))

/-- The equivalence `proEquivalenceOfFiberFunctor F` extends the fibre functor `F`. -/
noncomputable def proEquivalenceOfFiberFunctorObjOfIso (X : C) :
    (proEquivalenceOfFiberFunctor F).functor.obj (Pro.of.obj X) ≅
      (finiteToProfinite (Aut F)).obj ((functorToContAction F).obj X) :=
  (ContAction.proEquivalence (Aut F)).functor.mapIso
    (Pro.congrFunctorObjOfIso (equivalenceContAction F) X) ≪≫ proEquivalenceFunctorObjOfIso _

/-- The pro-object corresponding to a profinite `π`-space `X` pro-represents `Hom(X, F(-))`. -/
noncomputable def coyonedaObjProEquivalenceOfFiberFunctorInverseIso
    (X : ContAction Profinite.{u₂} (Aut F)) :
    (Pro.coyoneda C).obj (op ((proEquivalenceOfFiberFunctor F).inverse.obj X)) ≅
      functorToContAction F ⋙ (homFunctor (Aut F)).obj (op X) :=
  Pro.coyonedaObjCongrInverseObjIso (equivalenceContAction F) _ ≪≫
    Functor.isoWhiskerLeft (functorToContAction F) (coyonedaObjProEquivalenceInverseIso X)

/-- `coyonedaObjProEquivalenceOfFiberFunctorInverseIso` is natural in `X`. -/
lemma coyonedaObjProEquivalenceOfFiberFunctorInverseIso_hom_naturality
    {X Y : ContAction Profinite.{u₂} (Aut F)} (r : X ⟶ Y) :
    (Pro.coyoneda C).map ((proEquivalenceOfFiberFunctor F).inverse.map r).op ≫
        (coyonedaObjProEquivalenceOfFiberFunctorInverseIso F X).hom =
      (coyonedaObjProEquivalenceOfFiberFunctorInverseIso F Y).hom ≫
        Functor.whiskerLeft (functorToContAction F) ((homFunctor (Aut F)).map r.op) := by
  have h1 := Pro.coyonedaObjCongrInverseObjIso_hom_naturality (equivalenceContAction F)
    ((ContAction.proEquivalence (Aut F)).inverse.map r)
  have h2 := coyonedaObjProEquivalenceInverseIso_hom_naturality r
  change (Pro.coyoneda C).map ((Pro.congr (equivalenceContAction F)).inverse.map
      ((ContAction.proEquivalence (Aut F)).inverse.map r)).op ≫
      ((Pro.coyonedaObjCongrInverseObjIso (equivalenceContAction F) _).hom ≫
        Functor.whiskerLeft (equivalenceContAction F).functor
          (coyonedaObjProEquivalenceInverseIso X).hom) =
    ((Pro.coyonedaObjCongrInverseObjIso (equivalenceContAction F) _).hom ≫
        Functor.whiskerLeft (equivalenceContAction F).functor
          (coyonedaObjProEquivalenceInverseIso Y).hom) ≫
      Functor.whiskerLeft (equivalenceContAction F).functor ((homFunctor (Aut F)).map r.op)
  rw [reassoc_of% h1, Category.assoc, ← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp,
    h2]

end ProEquivalence

section SmallProObjects

open Opposite ContAction
open scoped FintypeCatDiscrete

variable {D : Type u₂} [SmallCategory D] [GaloisCategory D] (F : D ⥤ FintypeCat.{u₂})
  [FiberFunctor F]

/-- V.5.1: the fundamental pro-object `P_F` of a fibre functor `F`, the pro-object corresponding
to the regular `π`-space `π = Aut F` (V.5.2). (Stated for a small category `D`, so that
`Aut F` lies in the universe of the morphisms of `D`; every essentially small category is
equivalent to a small one.) -/
noncomputable def fundamentalProObject : Pro D :=
  (proEquivalenceOfFiberFunctor F).inverse.obj (regular (Aut F))

/-- V.5.1: `P_F` pro-represents `F`. -/
noncomputable def fundamentalProObjectIso :
    F ⋙ FintypeCat.incl ≅ (Pro.coyoneda D).obj (op (fundamentalProObject F)) :=
  (Functor.isoWhiskerLeft (functorToContAction F) (homFunctorObjRegularIso (Aut F))).symm ≪≫
    (coyonedaObjProEquivalenceOfFiberFunctorInverseIso F _).symm

lemma fundamentalProObjectIso_hom : (fundamentalProObjectIso F).hom =
    Functor.whiskerLeft (functorToContAction F) (homFunctorObjRegularIso (Aut F)).inv ≫
      (coyonedaObjProEquivalenceOfFiberFunctorInverseIso F _).inv :=
  rfl

lemma fundamentalProObjectIso_inv : (fundamentalProObjectIso F).inv =
    (coyonedaObjProEquivalenceOfFiberFunctorInverseIso F _).hom ≫
      Functor.whiskerLeft (functorToContAction F) (homFunctorObjRegularIso (Aut F)).hom :=
  rfl

lemma isFundamentalProObject_fundamentalProObject :
    IsFundamentalProObject (fundamentalProObject F) :=
  ⟨F, inferInstance, ⟨fundamentalProObjectIso F⟩⟩

/-- V.5.11: the fundamental pro-group `Π` of `D`: the pro-object corresponding (V.5.2) to the
profinite group `π = Aut F` acting on itself by conjugation. It is a pro-group
(`fundamentalProGroupRepresentableBy`), and `F(Π) = Hom(P_F, Π) ≅ π_F`
(`fundamentalProGroupFiberMulEquiv`). -/
noncomputable def fundamentalProGroup : Pro D :=
  (proEquivalenceOfFiberFunctor F).inverse.obj (conj (Aut F))

/-- V.5.11: the group structure of the fundamental pro-group: the groups `Hom(Q, Π)`, natural in
the pro-object `Q`. -/
noncomputable def fundamentalProGroupGrp : (Pro D)ᵒᵖ ⥤ GrpCat.{u₂} :=
  (proEquivalenceOfFiberFunctor F).functor.op ⋙ conjGrp (ContinuousMonoidHom.id (Aut F))

/-- V.5.11: `Π` is a pro-group: it represents the group-valued functor `fundamentalProGroupGrp F`
(i.e. it is a group object of `Pro D`, in the sense of `GrpObj.ofRepresentableBy`). -/
noncomputable def fundamentalProGroupRepresentableBy :
    (fundamentalProGroupGrp F ⋙ forget _).RepresentableBy (fundamentalProGroup F) where
  homEquiv := ((proEquivalenceOfFiberFunctor F).toAdjunction.homEquiv _ _).symm
  homEquiv_comp f g :=
    (proEquivalenceOfFiberFunctor F).toAdjunction.homEquiv_naturality_left_symm f g

/-- V.5.11: `F(Π) ≅ π_F`: the group `Hom(P_F, Π)` is isomorphic to `π = Aut F`. -/
noncomputable def fundamentalProGroupFiberMulEquiv :
    (fundamentalProGroupGrp F).obj (op (fundamentalProObject F)) ≃* Aut F :=
  (((conjGrp (ContinuousMonoidHom.id (Aut F))).mapIso
    ((proEquivalenceOfFiberFunctor F).counitIso.app
      (regular (Aut F))).op).groupIsoToMulEquiv.symm).trans (regularHomConjMulEquiv _ _)

/-- V.5.11: the fundamental pro-group acts on every pro-object `X` (the morphism `Π × X → X`),
in terms of points: for every pro-object `Q`, the group `Hom(Q, Π)` acts on `Hom(Q, X)`. Under
V.5.2 it is the action `(σ, x) ↦ σ • x` of `π` on `F(X)`. -/
noncomputable instance fundamentalProGroupAction (Q X : Pro D) :
    MulAction ((fundamentalProGroupGrp F).obj (op Q)) (Q ⟶ X) :=
  letI : MulAction ((fundamentalProGroupGrp F).obj (op Q))
      ((proEquivalenceOfFiberFunctor F).functor.obj Q ⟶
        (proEquivalenceOfFiberFunctor F).functor.obj X) :=
    inferInstanceAs (MulAction ((proEquivalenceOfFiberFunctor F).functor.obj Q ⟶
      conj (Aut F)) _)
  (proEquivalenceOfFiberFunctor F).fullyFaithfulFunctor.homEquiv.mulAction _

lemma functor_map_fundamentalProGroupAction_smul {Q X : Pro D}
    (f : (fundamentalProGroupGrp F).obj (op Q)) (u : Q ⟶ X) :
    (proEquivalenceOfFiberFunctor F).functor.map (f • u) =
      (show (proEquivalenceOfFiberFunctor F).functor.obj Q ⟶ conj (Aut F) from f) •
        (proEquivalenceOfFiberFunctor F).functor.map u :=
  (proEquivalenceOfFiberFunctor F).fullyFaithfulFunctor.homEquiv.apply_symm_apply _

/-- V.5.11: the action `Π × X → X` is natural in the pro-object `Q` of points. -/
lemma comp_fundamentalProGroupAction_smul {Q Q' X : Pro D} (φ : Q' ⟶ Q)
    (f : (fundamentalProGroupGrp F).obj (op Q)) (u : Q ⟶ X) :
    φ ≫ (f • u) = ((fundamentalProGroupGrp F).map φ.op f) • (φ ≫ u) :=
  (proEquivalenceOfFiberFunctor F).functor.map_injective (by
    rw [Functor.map_comp, functor_map_fundamentalProGroupAction_smul,
      functor_map_fundamentalProGroupAction_smul, Functor.map_comp, comp_smul]
    rfl)

/-- V.5.11: for every morphism `g : X ⟶ Y` of pro-objects, the square formed by the actions
`Π × X → X`, `Π × Y → Y` commutes. -/
lemma fundamentalProGroupAction_smul_comp {Q X Y : Pro D}
    (f : (fundamentalProGroupGrp F).obj (op Q)) (u : Q ⟶ X) (g : X ⟶ Y) :
    (f • u) ≫ g = f • (u ≫ g) :=
  (proEquivalenceOfFiberFunctor F).functor.map_injective (by
    rw [Functor.map_comp, functor_map_fundamentalProGroupAction_smul,
      functor_map_fundamentalProGroupAction_smul, Functor.map_comp, smul_comp])

end SmallProObjects

/-! ### Extension from one fibre functor to the fundamental groupoid -/

section GroupoidExtension

variable [GaloisCategory C] {E : Type*} [Category* E]
  {ξ ξ' : FiberFunctors.{u₁, u₂, w} C ⥤ E} (F₀ : FiberFunctors.{u₁, u₂, w} C)

/-- Since the fundamental groupoid is connected, a morphism `ξ(F₀) ⟶ ξ'(F₀)` compatible with the
automorphisms of `F₀` extends to a natural transformation `ξ ⟶ ξ'` (`extendHom_app_self`). -/
noncomputable def extendHom (m : ξ.obj F₀ ⟶ ξ'.obj F₀)
    (hm : ∀ τ : F₀ ⟶ F₀, ξ.map τ ≫ m = m ≫ ξ'.map τ) : ξ ⟶ ξ' where
  app F := ξ.map (nonempty_iso_fiberFunctors C F₀ F).some.inv ≫ m ≫
    ξ'.map (nonempty_iso_fiberFunctors C F₀ F).some.hom
  naturality {F G} s := by
    let t := fun F ↦ (nonempty_iso_fiberFunctors C F₀ F).some
    let τ : F₀ ⟶ F₀ := (t F).hom ≫ s ≫ (t G).inv
    have h1 : s ≫ (t G).inv = (t F).inv ≫ τ := by simp [τ]
    have h2 : τ ≫ (t G).hom = (t F).hom ≫ s := by simp [τ]
    change ξ.map s ≫ ξ.map (t G).inv ≫ m ≫ ξ'.map (t G).hom =
      (ξ.map (t F).inv ≫ m ≫ ξ'.map (t F).hom) ≫ ξ'.map s
    rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc, reassoc_of% (hm τ),
      ← Functor.map_comp, h2, Functor.map_comp, Category.assoc, Category.assoc]

lemma extendHom_app_self (m : ξ.obj F₀ ⟶ ξ'.obj F₀)
    (hm : ∀ τ : F₀ ⟶ F₀, ξ.map τ ≫ m = m ≫ ξ'.map τ) : (extendHom F₀ m hm).app F₀ = m := by
  let t := (nonempty_iso_fiberFunctors C F₀ F₀).some
  change ξ.map t.inv ≫ m ≫ ξ'.map t.hom = m
  rw [reassoc_of% (hm t.inv), ← Functor.map_comp, t.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- Natural transformations out of a functor on the fundamental groupoid are determined by
their component at one fibre functor. -/
lemma hom_ext_of_app_eq {α β : ξ ⟶ ξ'} (h : α.app F₀ = β.app F₀) : α = β := by
  ext F
  let t := (nonempty_iso_fiberFunctors C F₀ F).some
  have hα := α.naturality t.hom
  have hβ := β.naturality t.hom
  rw [← cancel_epi (ξ.map t.hom), hα, hβ, h]

/-- `extendHom` for isomorphisms. -/
noncomputable def extendIso (m : ξ.obj F₀ ≅ ξ'.obj F₀)
    (hm : ∀ τ : F₀ ⟶ F₀, ξ.map τ ≫ m.hom = m.hom ≫ ξ'.map τ) : ξ ≅ ξ' where
  hom := extendHom F₀ m.hom hm
  inv := extendHom F₀ m.inv fun τ ↦ by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hm, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  hom_inv_id := hom_ext_of_app_eq F₀ (by simp [extendHom_app_self])
  inv_hom_id := hom_ext_of_app_eq F₀ (by simp [extendHom_app_self])

@[simp]
lemma extendIso_hom_app_self (m : ξ.obj F₀ ≅ ξ'.obj F₀)
    (hm : ∀ τ : F₀ ⟶ F₀, ξ.map τ ≫ m.hom = m.hom ≫ ξ'.map τ) :
    (extendIso F₀ m hm).hom.app F₀ = m.hom :=
  extendHom_app_self F₀ m.hom hm

end GroupoidExtension

section AutFunctor

variable (C) [GaloisCategory C]

/-- The fundamental groups `π_F = Aut F` as a functor on the fundamental groupoid: a path
`F ⟶ G` acts by conjugation. -/
@[simps obj]
noncomputable def autFunctor : FiberFunctors.{u₁, u₂, w} C ⥤ GrpCat.{max u₁ w} where
  obj F := GrpCat.of (Aut F.obj)
  map s := GrpCat.ofHom (@asIso _ _ _ _ s.hom (isIso_of_fiberFunctor s.hom)).conjAut.toMonoidHom
  map_id F := by
    ext σ : 2
    change (@asIso _ _ _ _ (InducedCategory.Hom.hom (𝟙 F)) (isIso_of_fiberFunctor _)).conjAut σ = σ
    apply Aut.ext
    rw [Iso.conjAut_hom, Iso.conj_apply]
    simp
  map_comp s t := by
    ext σ : 2
    change (@asIso _ _ _ _ (s ≫ t).hom (isIso_of_fiberFunctor _)).conjAut σ =
      (@asIso _ _ _ _ t.hom (isIso_of_fiberFunctor _)).conjAut
        ((@asIso _ _ _ _ s.hom (isIso_of_fiberFunctor _)).conjAut σ)
    apply Aut.ext
    rw [Iso.conjAut_hom, Iso.conj_apply, Iso.conjAut_hom, Iso.conj_apply, Iso.conjAut_hom,
      Iso.conj_apply]
    simp

end AutFunctor

section FundamentalProGroupFiber

open Opposite ContAction
open scoped FintypeCatDiscrete

variable {D : Type u₂} [SmallCategory D] [GaloisCategory D] (F : D ⥤ FintypeCat.{u₂})
  [FiberFunctor F]

/-! #### `F(Π) ≅ π_F`, functorially in `F` -/

variable {F} in
/-- The morphism `P_G ⟶ P_F` of fundamental pro-objects induced by a path `s : F ⟶ G` of fibre
functors (V.5.1: fundamental pro-objects are anti-equivalent to fibre functors). -/
noncomputable def fundamentalProObjectMap {F G : FiberFunctors.{u₂, u₂, u₂} D} (s : F ⟶ G) :
    fundamentalProObject G.obj ⟶ fundamentalProObject F.obj :=
  ((Pro.coyonedaFullyFaithful D).preimage ((fundamentalProObjectIso F.obj).inv ≫
    Functor.whiskerRight s.hom FintypeCat.incl ≫ (fundamentalProObjectIso G.obj).hom)).unop

lemma coyoneda_map_fundamentalProObjectMap {F G : FiberFunctors.{u₂, u₂, u₂} D} (s : F ⟶ G) :
    (Pro.coyoneda D).map (fundamentalProObjectMap s).op = (fundamentalProObjectIso F.obj).inv ≫
      Functor.whiskerRight s.hom FintypeCat.incl ≫ (fundamentalProObjectIso G.obj).hom :=
  (Pro.coyonedaFullyFaithful D).map_preimage _

lemma fundamentalProObjectMap_id (F : FiberFunctors.{u₂, u₂, u₂} D) :
    fundamentalProObjectMap (𝟙 F) = 𝟙 _ := by
  apply Quiver.Hom.op_inj
  apply (Pro.coyonedaFullyFaithful D).map_injective
  rw [coyoneda_map_fundamentalProObjectMap]
  simp

lemma fundamentalProObjectMap_comp {F G H : FiberFunctors.{u₂, u₂, u₂} D} (s : F ⟶ G)
    (t : G ⟶ H) :
    fundamentalProObjectMap (s ≫ t) = fundamentalProObjectMap t ≫ fundamentalProObjectMap s := by
  apply Quiver.Hom.op_inj
  apply (Pro.coyonedaFullyFaithful D).map_injective
  rw [op_comp, Functor.map_comp, coyoneda_map_fundamentalProObjectMap,
    coyoneda_map_fundamentalProObjectMap, coyoneda_map_fundamentalProObjectMap]
  simp

/-- V.5.11: the fibres `F(Π) = Hom(P_F, Π)` of the fundamental pro-group, as a functor on the
fundamental groupoid. -/
@[simps obj]
noncomputable def fundamentalProGroupFiber : FiberFunctors.{u₂, u₂, u₂} D ⥤ GrpCat.{u₂} where
  obj G := (fundamentalProGroupGrp F).obj (op (fundamentalProObject G.obj))
  map s := (fundamentalProGroupGrp F).map (fundamentalProObjectMap s).op
  map_id G := by rw [fundamentalProObjectMap_id]; exact (fundamentalProGroupGrp F).map_id _
  map_comp s t := by
    rw [fundamentalProObjectMap_comp, op_comp]
    exact (fundamentalProGroupGrp F).map_comp _ _

/-- The automorphism of `P_F` induced by `σ ∈ π_F` corresponds, under V.5.2, to the right
multiplication by `σ` on `π`. -/
lemma fundamentalProObjectMap_eq (σ : (⟨F, inferInstance⟩ : FiberFunctors.{u₂, u₂, u₂} D) ⟶
    ⟨F, inferInstance⟩) :
    fundamentalProObjectMap σ = (proEquivalenceOfFiberFunctor F).inverse.map
      (regularRightMul (Aut F) (@asIso _ _ _ _ σ.hom (isIso_of_fiberFunctor _))) := by
  let σ' : Aut F := @asIso _ _ _ _ σ.hom (isIso_of_fiberFunctor _)
  have key : Functor.whiskerLeft (functorToContAction F) (homFunctorObjRegularIso (Aut F)).hom ≫
      Functor.whiskerRight σ.hom FintypeCat.incl ≫
      Functor.whiskerLeft (functorToContAction F) (homFunctorObjRegularIso (Aut F)).inv =
      Functor.whiskerLeft (functorToContAction F)
        ((homFunctor (Aut F)).map (regularRightMul (Aut F) σ').op) := by
    ext X (f : regular (Aut F) ⟶ (finiteToProfinite _).obj ((functorToContAction F).obj X))
    apply hom_ext_apply
    intro (h : Aut F)
    change h • σ'.hom.app X (f.hom.hom (toRegular _ 1)) = f.hom.hom (toRegular _ (h * σ'))
    have := hom_smul f (h * σ') (toRegular _ 1)
    rw [regular_smul, mul_one] at this
    rw [this, mul_smul]
    rfl
  have hnat := coyonedaObjProEquivalenceOfFiberFunctorInverseIso_hom_naturality F
    (regularRightMul (Aut F) σ')
  apply Quiver.Hom.op_inj
  apply (Pro.coyonedaFullyFaithful D).map_injective
  rw [coyoneda_map_fundamentalProObjectMap]
  have h3 : (Pro.coyoneda D).map ((proEquivalenceOfFiberFunctor F).inverse.map
      (regularRightMul (Aut F) σ')).op =
      (coyonedaObjProEquivalenceOfFiberFunctorInverseIso F (regular (Aut F))).hom ≫
        Functor.whiskerLeft (functorToContAction F)
          ((homFunctor (Aut F)).map (regularRightMul (Aut F) σ').op) ≫
        (coyonedaObjProEquivalenceOfFiberFunctorInverseIso F (regular (Aut F))).inv := by
    rw [← reassoc_of% hnat, Iso.hom_inv_id, Category.comp_id]
  refine Eq.trans ?_ h3.symm
  dsimp only
  rw [← key, fundamentalProObjectIso_hom, fundamentalProObjectIso_inv]
  exact (Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm))

lemma fundamentalProGroupFiberMulEquiv_apply
    (g : (fundamentalProGroupGrp F).obj (op (fundamentalProObject F))) :
    fundamentalProGroupFiberMulEquiv F g = conjVal
      (((proEquivalenceOfFiberFunctor F).counitIso.app (regular (Aut F))).inv ≫
        (g : (proEquivalenceOfFiberFunctor F).functor.obj (fundamentalProObject F) ⟶
          conj (Aut F))) (toRegular (Aut F) 1) :=
  rfl

/-- V.5.11: `F(Π) ≅ π_F`, functorially in the fibre functor `F`: an isomorphism between the
functors `F ↦ Hom(P_F, Π)` and `F ↦ Aut F` on the fundamental groupoid. -/
noncomputable def fundamentalProGroupFiberIso :
    fundamentalProGroupFiber F ≅ autFunctor.{u₂, u₂, u₂} D :=
  extendIso ⟨F, inferInstance⟩
    (@MulEquiv.toGrpIso ((fundamentalProGroupFiber F).obj ⟨F, inferInstance⟩)
      ((autFunctor.{u₂, u₂, u₂} D).obj ⟨F, inferInstance⟩) (fundamentalProGroupFiberMulEquiv F))
    fun τ ↦ by
    let τ' : Aut F := @asIso _ _ _ _ τ.hom (isIso_of_fiberFunctor _)
    let e := proEquivalenceOfFiberFunctor F
    let c := e.counitIso.app (regular (Aut F))
    ext g
    change fundamentalProGroupFiberMulEquiv F
        ((fundamentalProGroupGrp F).map (fundamentalProObjectMap τ).op g) =
      τ'.conjAut (fundamentalProGroupFiberMulEquiv F g)
    rw [fundamentalProObjectMap_eq]
    let r := regularRightMul (Aut F) τ'
    have hc : c.inv ≫ e.functor.map (e.inverse.map r) = r ≫ c.inv :=
      (e.counitIso.inv.naturality r).symm
    let g' : e.functor.obj (e.inverse.obj (regular (Aut F))) ⟶ conj (Aut F) := g
    have h1 : fundamentalProGroupFiberMulEquiv F
        ((fundamentalProGroupGrp F).map (e.inverse.map r).op g) =
        conjVal (c.inv ≫ g') (τ' • toRegular (Aut F) 1) := by
      refine (fundamentalProGroupFiberMulEquiv_apply F _).trans ?_
      change conjVal (c.inv ≫ e.functor.map (e.inverse.map r) ≫ g') _ = _
      rw [reassoc_of% hc]
      rfl
    refine h1.trans ?_
    rw [conjVal_smul]
    apply Aut.ext
    rw [Iso.conjAut_hom, Iso.conj_apply]
    rfl

end FundamentalProGroupFiber

/-! ### V.5.9: pro-objects as profinite local systems on the fundamental groupoid -/

section ProLocalSystems

open Opposite ContAction
open scoped FintypeCatDiscrete

variable {D : Type u₂} [SmallCategory D] [GaloisCategory D] (F : D ⥤ FintypeCat.{u₂})
  [FiberFunctor F]

/-- The set `Hom(Q, P)` of morphisms of pro-objects, with the topology of pointwise convergence of
the corresponding maps `F(Q) → F(P)` of profinite spaces (V.5.2). -/
@[nolint unusedArguments]
def ProHomSpace (_F : D ⥤ FintypeCat.{u₂}) (Q P : Pro D) : Type u₂ := Q ⟶ P

variable {F} in
/-- The underlying morphism. -/
def ProHomSpace.toHom {Q P : Pro D} (v : ProHomSpace F Q P) : Q ⟶ P := v

/-- A morphism, as a point of `ProHomSpace F Q P`. -/
def ProHomSpace.ofHom {Q P : Pro D} (v : Q ⟶ P) : ProHomSpace F Q P := v

omit [GaloisCategory D] [FiberFunctor F] in
@[simp]
lemma ProHomSpace.toHom_ofHom {Q P : Pro D} (v : Q ⟶ P) : (ProHomSpace.ofHom F v).toHom = v :=
  rfl

omit [GaloisCategory D] [FiberFunctor F] in
@[simp]
lemma ProHomSpace.ofHom_toHom {Q P : Pro D} (v : ProHomSpace F Q P) :
    ProHomSpace.ofHom F v.toHom = v :=
  rfl

noncomputable instance (Q P : Pro D) : TopologicalSpace (ProHomSpace F Q P) :=
  TopologicalSpace.induced (fun v : ProHomSpace F Q P ↦
    (ConcreteCategory.hom ((proEquivalenceOfFiberFunctor F).functor.map v.toHom).hom.hom :
      (proEquivalenceOfFiberFunctor F).functor.obj Q |>.obj.V → _)) inferInstance

variable {F} in
lemma continuous_proHomSpace_iff {X : Type*} [TopologicalSpace X] {Q P : Pro D}
    (f : X → ProHomSpace F Q P) : Continuous f ↔
      ∀ y, Continuous fun x ↦ ((proEquivalenceOfFiberFunctor F).functor.map
        (f x).toHom).hom.hom y := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

variable {F} in
lemma continuous_proHomSpace_comp {Q Q' P P' : Pro D} (ψ : Q' ⟶ Q) (g : P ⟶ P') :
    Continuous fun v : ProHomSpace F Q P ↦ ProHomSpace.ofHom F (ψ ≫ v.toHom ≫ g) := by
  rw [continuous_proHomSpace_iff]
  intro y
  simp only [ProHomSpace.toHom_ofHom, Functor.map_comp]
  change Continuous fun v : ProHomSpace F Q P ↦
    ((proEquivalenceOfFiberFunctor F).functor.map g).hom.hom
      (((proEquivalenceOfFiberFunctor F).functor.map v.toHom).hom.hom
        (((proEquivalenceOfFiberFunctor F).functor.map ψ).hom.hom y))
  exact (ConcreteCategory.hom
    ((proEquivalenceOfFiberFunctor F).functor.map g).hom.hom).continuous.comp
      ((continuous_apply _).comp continuous_induced_dom)

/-- V.5.9: the local system `E_P : F' ↦ F'(P) = Hom(P_{F'}, P)` on the fundamental groupoid
defined by a pro-object `P`. -/
@[simps obj]
noncomputable def proLocalSystemObj (P : Pro D) :
    FiberFunctors.{u₂, u₂, u₂} D ⥤ TopCat.{u₂} where
  obj G := TopCat.of (ProHomSpace F (fundamentalProObject G.obj) P)
  map s := TopCat.ofHom ⟨fun v ↦ ProHomSpace.ofHom F (fundamentalProObjectMap s ≫ v.toHom ≫ 𝟙 P),
    continuous_proHomSpace_comp _ _⟩
  map_id G := by
    ext v
    change ProHomSpace.ofHom F (fundamentalProObjectMap (𝟙 G) ≫ v.toHom ≫ 𝟙 P) = v
    rw [fundamentalProObjectMap_id, Category.id_comp, Category.comp_id]
    rfl
  map_comp s t := by
    ext v
    change ProHomSpace.ofHom F (fundamentalProObjectMap (s ≫ t) ≫ v.toHom ≫ 𝟙 P) =
      ProHomSpace.ofHom F (fundamentalProObjectMap t ≫
        (fundamentalProObjectMap s ≫ v.toHom ≫ 𝟙 P) ≫ 𝟙 P)
    rw [fundamentalProObjectMap_comp]
    simp

/-- V.5.9: the functor `P ↦ E_P` from pro-objects to local systems of topological spaces on the
fundamental groupoid. -/
@[simps obj]
noncomputable def proLocalSystem :
    Pro D ⥤ (FiberFunctors.{u₂, u₂, u₂} D ⥤ TopCat.{u₂}) where
  obj P := proLocalSystemObj F P
  map f :=
    { app G := TopCat.ofHom ⟨fun v ↦ ProHomSpace.ofHom F (𝟙 _ ≫ v.toHom ≫ f),
        continuous_proHomSpace_comp _ _⟩
      naturality G G' s := by
        ext v
        change ProHomSpace.ofHom F (𝟙 _ ≫ (fundamentalProObjectMap s ≫ v.toHom ≫ 𝟙 _) ≫ f) =
          ProHomSpace.ofHom F (fundamentalProObjectMap s ≫ (𝟙 _ ≫ v.toHom ≫ f) ≫ 𝟙 _)
        simp }
  map_id P := by
    ext G v
    change ProHomSpace.ofHom F (𝟙 _ ≫ v.toHom ≫ 𝟙 P) = v
    rw [Category.id_comp, Category.comp_id]
    rfl
  map_comp f g := by
    ext G v
    change ProHomSpace.ofHom F (𝟙 _ ≫ v.toHom ≫ f ≫ g) =
      ProHomSpace.ofHom F (𝟙 _ ≫ (𝟙 _ ≫ v.toHom ≫ f) ≫ g)
    simp

/-- The value of `E_P` at the base fibre functor `F` is `F(P)` (V.5.2): evaluation at the point
of `F(P_F) = π` corresponding to `1`. -/
noncomputable def proLocalSystemEval (P : Pro D) :
    ProHomSpace F (fundamentalProObject F) P →
      ((proEquivalenceOfFiberFunctor F).functor.obj P).obj.V :=
  fun v ↦ ((proEquivalenceOfFiberFunctor F).functor.map v.toHom).hom.hom
    (((proEquivalenceOfFiberFunctor F).counitIso.app (regular (Aut F))).inv.hom.hom
      (toRegular (Aut F) 1))

/-- The inverse of `proLocalSystemEval`. -/
noncomputable def proLocalSystemEvalInv (P : Pro D) :
    ((proEquivalenceOfFiberFunctor F).functor.obj P).obj.V →
      ProHomSpace F (fundamentalProObject F) P :=
  fun x ↦ ProHomSpace.ofHom F ((proEquivalenceOfFiberFunctor F).fullyFaithfulFunctor.preimage
    (((proEquivalenceOfFiberFunctor F).counitIso.app (regular (Aut F))).hom ≫
      (regularHomEquivOfProfinite (Aut F) _).symm x))

lemma proLocalSystemEval_inv (P : Pro D) (x) :
    proLocalSystemEval F P (proLocalSystemEvalInv F P x) = x := by
  simp only [proLocalSystemEval, proLocalSystemEvalInv, ProHomSpace.toHom_ofHom,
    Functor.FullyFaithful.map_preimage]
  change ((regularHomEquivOfProfinite (Aut F) _).symm x).hom.hom
    ((((proEquivalenceOfFiberFunctor F).counitIso.app (regular (Aut F))).inv ≫
      ((proEquivalenceOfFiberFunctor F).counitIso.app (regular (Aut F))).hom).hom.hom
        (toRegular (Aut F) 1)) = x
  rw [Iso.inv_hom_id]
  exact one_smul _ x

lemma proLocalSystemEvalInv_eval (P : Pro D) (v) :
    proLocalSystemEvalInv F P (proLocalSystemEval F P v) = v := by
  have h : (regularHomEquivOfProfinite (Aut F) _).symm (proLocalSystemEval F P v) =
      ((proEquivalenceOfFiberFunctor F).counitIso.app (regular (Aut F))).inv ≫
        (proEquivalenceOfFiberFunctor F).functor.map v.toHom :=
    (Equiv.symm_apply_eq _).2 rfl
  simp only [proLocalSystemEvalInv, h]
  erw [Iso.hom_inv_id_assoc, Functor.FullyFaithful.preimage_map]
  rfl

lemma continuous_proLocalSystemEval (P : Pro D) : Continuous (proLocalSystemEval F P) :=
  (continuous_apply _).comp continuous_induced_dom

lemma continuous_proLocalSystemEvalInv (P : Pro D) : Continuous (proLocalSystemEvalInv F P) := by
  rw [continuous_proHomSpace_iff]
  intro y
  simp only [proLocalSystemEvalInv, ProHomSpace.toHom_ofHom, Functor.FullyFaithful.map_preimage]
  let z : Aut F :=
    ((proEquivalenceOfFiberFunctor F).counitIso.app (regular (Aut F))).hom.hom.hom y
  change Continuous fun x ↦
    ((regularHomEquivOfProfinite (Aut F) _).symm x).hom.hom (toRegular (Aut F) z)
  simp only [regularHomEquivOfProfinite_symm_apply]
  exact continuous_id.const_smul z

/-- V.5.9: `E_P(F) = F(P)`, as topological spaces. -/
noncomputable def proLocalSystemEvalHomeo (P : Pro D) :
    ProHomSpace F (fundamentalProObject F) P ≃ₜ
      ((proEquivalenceOfFiberFunctor F).functor.obj P).obj.V where
  toFun := proLocalSystemEval F P
  invFun := proLocalSystemEvalInv F P
  left_inv := proLocalSystemEvalInv_eval F P
  right_inv := proLocalSystemEval_inv F P
  continuous_toFun := continuous_proLocalSystemEval F P
  continuous_invFun := continuous_proLocalSystemEvalInv F P

lemma proLocalSystemEval_comp {P P' : Pro D} (f : P ⟶ P')
    (v : ProHomSpace F (fundamentalProObject F) P) :
    proLocalSystemEval F P' (ProHomSpace.ofHom F (𝟙 _ ≫ v.toHom ≫ f)) =
      ((proEquivalenceOfFiberFunctor F).functor.map f).hom.hom (proLocalSystemEval F P v) := by
  simp only [proLocalSystemEval, ProHomSpace.toHom_ofHom, Category.id_comp, Functor.map_comp]
  rfl

lemma proLocalSystemObj_map_toHom (P : Pro D) {G G' : FiberFunctors.{u₂, u₂, u₂} D} (s : G ⟶ G')
    (v : ProHomSpace F (fundamentalProObject G.obj) P) :
    ProHomSpace.toHom (F := F) ((proLocalSystemObj F P).map s v) =
      fundamentalProObjectMap s ≫ v.toHom ≫ 𝟙 P :=
  rfl

/-- An endomorphism of `F` in the fundamental groupoid, as an element of `π_F`. -/
noncomputable def autOfFiberFunctorsHom
    (τ : (⟨F, inferInstance⟩ : FiberFunctors.{u₂, u₂, u₂} D) ⟶ ⟨F, inferInstance⟩) : Aut F :=
  @asIso _ _ _ _ τ.hom (isIso_of_fiberFunctor _)

/-- V.5.9: `E_P(F) = F(P)` is compatible with the operations of `π_F`. -/
lemma proLocalSystemEval_smul (P : Pro D)
    (τ : (⟨F, inferInstance⟩ : FiberFunctors.{u₂, u₂, u₂} D) ⟶ ⟨F, inferInstance⟩)
    (v : ProHomSpace F (fundamentalProObject F) P) :
    proLocalSystemEval F P ((proLocalSystemObj F P).map τ v) =
      (autOfFiberFunctorsHom F τ) • proLocalSystemEval F P v := by
  let τ' : Aut F := autOfFiberFunctorsHom F τ
  let e := proEquivalenceOfFiberFunctor F
  let c := e.counitIso.app (regular (Aut F))
  let r := regularRightMul (Aut F) τ'
  have hc : c.inv ≫ e.functor.map (e.inverse.map r) = r ≫ c.inv :=
    (e.counitIso.inv.naturality r).symm
  have hpt : (e.functor.map (e.inverse.map r)).hom.hom (c.inv.hom.hom (toRegular (Aut F) 1)) =
      τ' • c.inv.hom.hom (toRegular (Aut F) 1) := by
    have := congrArg (fun φ ↦ φ.hom.hom (toRegular (Aut F) 1)) hc
    simp only [comp_hom_apply] at this
    rw [this, ← hom_smul]
    congr 1
  unfold proLocalSystemEval
  rw [proLocalSystemObj_map_toHom, Category.comp_id, fundamentalProObjectMap_eq]
  refine (congrArg (fun φ ↦ φ.hom.hom (c.inv.hom.hom (toRegular (Aut F) 1)))
    (e.functor.map_comp (e.inverse.map r) v.toHom)).trans ?_
  exact (congrArg _ hpt).trans (hom_smul _ _ _)

/-- The operation of `π_G = Aut G` on `ξ(G)`, for a functor `ξ` from the fundamental groupoid to
topological spaces. -/
@[reducible]
def topGroupoidAction (ξ : FiberFunctors.{u₂, u₂, u₂} D ⥤ TopCat.{u₂})
    (G : FiberFunctors.{u₂, u₂, u₂} D) : MulAction (Aut G.obj) (ξ.obj G) where
  smul σ x := ξ.map (ObjectProperty.homMk σ.hom) x
  one_smul x := by
    change ξ.map (𝟙 G) x = x
    rw [ξ.map_id]
    rfl
  mul_smul σ τ x := by
    change ξ.map (ObjectProperty.homMk τ.hom ≫ ObjectProperty.homMk σ.hom) x = _
    rw [ξ.map_comp]
    rfl

variable (D) in
/-- The fibre functor `F`, as an object of the fundamental groupoid. -/
abbrev baseFiberFunctor : FiberFunctors.{u₂, u₂, u₂} D := ⟨F, inferInstance⟩

variable (D) in
/-- V.5.9: a local system `ξ` of topological spaces on the fundamental groupoid is profinite if
`ξ(F)` is compact, Hausdorff and totally disconnected, with a continuous action of `π_F`. (SGA
asks this for every fibre functor and notes that it suffices to check it for one, `Γ` being
connected.) -/
def IsProfiniteLocalSystem (ξ : FiberFunctors.{u₂, u₂, u₂} D ⥤ TopCat.{u₂}) : Prop :=
  CompactSpace (ξ.obj (baseFiberFunctor D F)) ∧ T2Space (ξ.obj (baseFiberFunctor D F)) ∧
    TotallyDisconnectedSpace (ξ.obj (baseFiberFunctor D F)) ∧
    @ContinuousSMul (Aut F) (ξ.obj (baseFiberFunctor D F))
      (topGroupoidAction ξ (baseFiberFunctor D F)).toSMul _ _

lemma autOfFiberFunctorsHom_homMk (σ : Aut F) :
    autOfFiberFunctorsHom F
      (ObjectProperty.homMk σ.hom : baseFiberFunctor D F ⟶ baseFiberFunctor D F) = σ :=
  Aut.ext rfl

lemma isProfiniteLocalSystem_proLocalSystemObj (P : Pro D) :
    IsProfiniteLocalSystem D F (proLocalSystemObj F P) := by
  let h := proLocalSystemEvalHomeo F P
  refine ⟨h.symm.compactSpace, h.isEmbedding.t2Space, h.symm.totallyDisconnectedSpace,
    @ContinuousSMul.mk _ _
      (topGroupoidAction (proLocalSystemObj F P) (baseFiberFunctor D F)).toSMul _ _ ?_⟩
  have key (σ : Aut F) (v : ProHomSpace F (fundamentalProObject F) P) :
      (proLocalSystemObj F P).map
        (ObjectProperty.homMk σ.hom : baseFiberFunctor D F ⟶ baseFiberFunctor D F) v =
        h.symm (σ • h v) := by
    apply h.injective
    rw [Homeomorph.apply_symm_apply]
    refine (proLocalSystemEval_smul F P _ v).trans ?_
    rw [autOfFiberFunctorsHom_homMk]
    rfl
  have : (fun p : Aut F × (proLocalSystemObj F P).obj (baseFiberFunctor D F) ↦
      (topGroupoidAction (proLocalSystemObj F P) (baseFiberFunctor D F)).toSMul.smul p.1 p.2) =
      fun p ↦ h.symm (p.1 • h p.2) := funext fun p ↦ key p.1 p.2
  refine this ▸ ?_
  exact h.symm.continuous.comp (continuous_fst.smul (h.continuous.comp continuous_snd))

/-- The operation of `π_F` on `E_P(F)` corresponds to its operation on `F(P)`. -/
lemma proLocalSystemObj_map_homMk (P : Pro D) (σ : Aut F)
    (v : ProHomSpace F (fundamentalProObject F) P) :
    (proLocalSystemObj F P).map
      (ObjectProperty.homMk σ.hom : baseFiberFunctor D F ⟶ baseFiberFunctor D F) v =
      (proLocalSystemEvalHomeo F P).symm (σ • proLocalSystemEvalHomeo F P v) := by
  apply (proLocalSystemEvalHomeo F P).injective
  rw [Homeomorph.apply_symm_apply]
  refine (proLocalSystemEval_smul F P _ v).trans ?_
  rw [autOfFiberFunctorsHom_homMk]
  rfl

variable (D) in
/-- V.5.9: the category of profinite local systems on the fundamental groupoid. -/
abbrev ProfiniteLocalSystems : Type _ :=
  ObjectProperty.FullSubcategory (IsProfiniteLocalSystem D F)

/-- V.5.9: the functor `P ↦ E_P` from pro-objects to profinite local systems on the fundamental
groupoid, `E_P(F') = F'(P)`. -/
noncomputable def toProfiniteLocalSystems : Pro D ⥤ ProfiniteLocalSystems D F :=
  ObjectProperty.lift _ (proLocalSystem F) (isProfiniteLocalSystem_proLocalSystemObj F)

instance : (toProfiniteLocalSystems F).Faithful where
  map_injective {P P'} f g h := by
    apply (proEquivalenceOfFiberFunctor F).functor.map_injective
    refine hom_ext_apply fun x ↦ ?_
    have h' := congrArg (fun α : (toProfiniteLocalSystems F).obj P ⟶
      (toProfiniteLocalSystems F).obj P' ↦ ConcreteCategory.hom
        (α.hom.app (baseFiberFunctor D F)) (proLocalSystemEvalInv F P x)) h
    have e1 := congrArg (proLocalSystemEval F P') h'
    change proLocalSystemEval F P' (ProHomSpace.ofHom F (𝟙 _ ≫ _ ≫ f)) =
      proLocalSystemEval F P' (ProHomSpace.ofHom F (𝟙 _ ≫ _ ≫ g)) at e1
    rwa [proLocalSystemEval_comp, proLocalSystemEval_comp, proLocalSystemEval_inv] at e1

/-- A morphism of local systems `E_P ⟶ E_{P'}`, at `F`, as a map `F(P) → F(P')`. -/
noncomputable def proLocalSystemFunAtBase {P P' : Pro D}
    (α : proLocalSystemObj F P ⟶ proLocalSystemObj F P')
    (x : ((proEquivalenceOfFiberFunctor F).functor.obj P).obj.V) :
    ((proEquivalenceOfFiberFunctor F).functor.obj P').obj.V :=
  proLocalSystemEvalHomeo F P' (α.app (baseFiberFunctor D F)
    ((proLocalSystemEvalHomeo F P).symm x))

lemma proLocalSystemFunAtBase_smul {P P' : Pro D}
    (α : proLocalSystemObj F P ⟶ proLocalSystemObj F P') (σ : Aut F)
    (x : ((proEquivalenceOfFiberFunctor F).functor.obj P).obj.V) :
    proLocalSystemFunAtBase F α (σ • x) = σ • proLocalSystemFunAtBase F α x := by
  have h1 : (proLocalSystemEvalHomeo F P).symm (σ • x) = (proLocalSystemObj F P).map
      (ObjectProperty.homMk σ.hom : baseFiberFunctor D F ⟶ baseFiberFunctor D F)
        ((proLocalSystemEvalHomeo F P).symm x) := by
    rw [proLocalSystemObj_map_homMk, Homeomorph.apply_symm_apply]
  have h2 := ConcreteCategory.congr_hom (α.naturality
    (ObjectProperty.homMk σ.hom : baseFiberFunctor D F ⟶ baseFiberFunctor D F))
      ((proLocalSystemEvalHomeo F P).symm x)
  have h3 := congrArg (proLocalSystemEvalHomeo F P') (proLocalSystemObj_map_homMk F P' σ
    (α.app (baseFiberFunctor D F) ((proLocalSystemEvalHomeo F P).symm x)))
  rw [Homeomorph.apply_symm_apply] at h3
  unfold proLocalSystemFunAtBase
  rw [h1]
  exact (congrArg (proLocalSystemEvalHomeo F P') h2).trans h3

/-- A morphism of local systems `E_P ⟶ E_{P'}` gives, at `F`, a morphism `F(P) ⟶ F(P')` of
profinite `π_F`-spaces. -/
noncomputable def proLocalSystemHomAtBase {P P' : Pro D}
    (α : proLocalSystemObj F P ⟶ proLocalSystemObj F P') :
    (proEquivalenceOfFiberFunctor F).functor.obj P ⟶
      (proEquivalenceOfFiberFunctor F).functor.obj P' :=
  ObjectProperty.homMk
    { hom := CompHausLike.ofHom _ ⟨proLocalSystemFunAtBase F α,
        (proLocalSystemEvalHomeo F P').continuous.comp
          ((ConcreteCategory.hom (α.app (baseFiberFunctor D F))).continuous.comp
            (proLocalSystemEvalHomeo F P).symm.continuous)⟩
      comm := fun σ ↦ ConcreteCategory.hom_ext _ _ (proLocalSystemFunAtBase_smul F α σ) }

instance : (toProfiniteLocalSystems F).Full where
  map_surjective {P P'} α := by
    let α' : proLocalSystemObj F P ⟶ proLocalSystemObj F P' := α.hom
    let e := proEquivalenceOfFiberFunctor F
    refine ⟨e.fullyFaithfulFunctor.preimage (proLocalSystemHomAtBase F α'), ?_⟩
    apply ObjectProperty.hom_ext
    apply hom_ext_of_app_eq (baseFiberFunctor D F)
    ext v
    apply (proLocalSystemEvalHomeo F P').injective
    have h3 := proLocalSystemEval_comp F (e.fullyFaithfulFunctor.preimage
      (proLocalSystemHomAtBase F α')) v
    rw [Functor.FullyFaithful.map_preimage] at h3
    refine h3.trans ?_
    exact congrArg (proLocalSystemEvalHomeo F P')
      (congrArg (α'.app (baseFiberFunctor D F)) ((proLocalSystemEvalHomeo F P).symm_apply_apply v))

/-- The profinite `π_F`-space `ξ(F)` of a profinite local system `ξ`. -/
noncomputable def ProfiniteLocalSystems.baseObj (ξ : ProfiniteLocalSystems D F) :
    ContAction Profinite.{u₂} (Aut F) :=
  haveI := ξ.property.1
  haveI := ξ.property.2.1
  haveI := ξ.property.2.2.1
  letI := topGroupoidAction ξ.obj (baseFiberFunctor D F)
  haveI := ξ.property.2.2.2
  ofProfinite (Aut F) (Profinite.of (ξ.obj.obj (baseFiberFunctor D F)))

lemma autOfFiberFunctorsHom_homMk_eq
    (τ : (⟨F, inferInstance⟩ : FiberFunctors.{u₂, u₂, u₂} D) ⟶ ⟨F, inferInstance⟩) :
    (ObjectProperty.homMk (autOfFiberFunctorsHom F τ).hom :
      baseFiberFunctor D F ⟶ baseFiberFunctor D F) = τ :=
  rfl

instance : (toProfiniteLocalSystems F).EssSurj where
  mem_essImage ξ := by
    let X := ProfiniteLocalSystems.baseObj F ξ
    let e := proEquivalenceOfFiberFunctor F
    let P := e.inverse.obj X
    let h : ProHomSpace F (fundamentalProObject F) P ≃ₜ X.obj.V :=
      (proLocalSystemEvalHomeo F P).trans (homeoOfIso (e.counitIso.app X))
    let m : (proLocalSystemObj F P).obj (baseFiberFunctor D F) ≅
        ξ.obj.obj (baseFiberFunctor D F) := TopCat.isoOfHomeo h
    refine ⟨P, ⟨ObjectProperty.isoMk _ (extendIso (baseFiberFunctor D F) m fun τ ↦ ?_)⟩⟩
    ext v
    let σ := autOfFiberFunctorsHom F τ
    have h1 : (proLocalSystemObj F P).map τ v = (proLocalSystemEvalHomeo F P).symm
        (σ • proLocalSystemEvalHomeo F P v) :=
      (congrArg (fun t ↦ (proLocalSystemObj F P).map t v)
        (autOfFiberFunctorsHom_homMk_eq F τ).symm).trans (proLocalSystemObj_map_homMk F P σ v)
    change h ((proLocalSystemObj F P).map τ v) = ξ.obj.map τ (h v)
    rw [h1]
    change (e.counitIso.app X).hom.hom.hom (proLocalSystemEvalHomeo F P
      ((proLocalSystemEvalHomeo F P).symm (σ • proLocalSystemEvalHomeo F P v))) = _
    rw [Homeomorph.apply_symm_apply, hom_smul]
    rfl

/-- V.5.9: the functor `P ↦ E_P` is an equivalence of the category of pro-objects of `D` with the
category of profinite local systems on the fundamental groupoid. -/
instance : (toProfiniteLocalSystems F).IsEquivalence where

end ProLocalSystems


section Paths

variable {F F' : C ⥤ FintypeCat.{w}}

set_option backward.isDefEq.respectTransparency.types false in
lemma continuous_conjAut (φ : F ≅ F') : Continuous φ.conjAut := by
  rw [(autEmbedding_isClosedEmbedding F').isInducing.continuous_iff, continuous_pi_iff]
  intro X
  have : (fun σ ↦ autEmbedding F' (φ.conjAut σ) X) =
      (fun τ : Aut (F.obj X) ↦ (φ.app X).conjAut τ) ∘ (fun a ↦ a X) ∘ autEmbedding F := by
    ext σ x
    simp [Iso.conjAut_apply]
  change Continuous (fun σ ↦ autEmbedding F' (φ.conjAut σ) X)
  rw [this]
  exact continuous_of_discreteTopology.comp
    ((continuous_apply X).comp (autEmbedding_isClosedEmbedding F).continuous)

/-- After V.5.7: an isomorphism (a path) `F ≅ F'` of fibre functors induces an isomorphism of
topological groups `π_F ≃ π_{F'}`. -/
noncomputable def conjAutContinuousMulEquiv (φ : F ≅ F') : Aut F ≃ₜ* Aut F' where
  toMulEquiv := φ.conjAut
  continuous_toFun := continuous_conjAut φ
  continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := φ.conjAut.toEquiv) (continuous_conjAut φ)

@[simp]
lemma conjAutContinuousMulEquiv_apply (φ : F ≅ F') (σ : Aut F) :
    conjAutContinuousMulEquiv φ σ = φ.conjAut σ :=
  rfl

/-- After V.5.7: the fundamental group is determined up to inner automorphism: two paths
`φ ψ : F ≅ F'` induce isomorphisms `π_F ≃ π_{F'}` which differ by an inner automorphism
of `π_{F'}`. -/
theorem conjAut_eq_mul_conjAut_mul (φ ψ : F ≅ F') :
    ∃ τ : Aut F', ∀ σ : Aut F, ψ.conjAut σ = τ * φ.conjAut σ * τ⁻¹ := by
  refine ⟨φ.symm ≪≫ ψ, fun σ ↦ Aut.ext ?_⟩
  change ψ.inv ≫ σ.hom ≫ ψ.hom =
    (ψ.inv ≫ φ.hom) ≫ (φ.inv ≫ σ.hom ≫ φ.hom) ≫ (φ.inv ≫ ψ.hom)
  simp

/-- After V.5.7: the set `Isom(F, F')` of paths from `F` to `F'` is a principal homogeneous
space under `π_F` acting by composition on the right. -/
@[simps]
def autEquivIso (φ : F ≅ F') : Aut F ≃ (F ≅ F') where
  toFun σ := σ ≪≫ φ
  invFun ψ := ψ ≪≫ φ.symm
  left_inv σ := Aut.ext (by change (σ.hom ≫ φ.hom) ≫ φ.inv = σ.hom; simp)
  right_inv ψ := Iso.ext (by simp)

/-- After V.5.7: the set `Isom(F, F')` of paths from `F` to `F'` is a principal homogeneous
space under `π_{F'}` acting by composition on the left. -/
@[simps]
def autEquivIso' (φ : F ≅ F') : Aut F' ≃ (F ≅ F') where
  toFun τ := φ ≪≫ τ
  invFun ψ := φ.symm ≪≫ ψ
  left_inv τ := Aut.ext (by change φ.inv ≫ φ.hom ≫ τ.hom = τ.hom; simp)
  right_inv ψ := Iso.ext (by simp)

end Paths

/-! ### V.5.11: Galois objects, sections, completely decomposed objects -/

section GaloisObjects

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- V.5.11: a connected object is Galois iff the stabilizer in `π` of a point of its fibre is a
normal subgroup, i.e. iff its fibre is `π/N` for an open normal subgroup `N`. -/
theorem isGalois_iff_normal_stabilizer (X : C) [IsConnected X] (x : F.obj X) :
    IsGalois X ↔ (MulAction.stabilizer (Aut F) x).Normal := by
  refine ⟨fun _ ↦ stabilizer_normal_of_isGalois F X x, fun hN ↦ ?_⟩
  have key (y : F.obj X) : ∃ φ : Aut X, F.map φ.hom x = y := by
    obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (Aut F) x y
    obtain ⟨f, hf⟩ := (exists_hom_iff_stabilizer_le F x (σ • x)).2 fun τ (hτ : τ • x = x) ↦ by
      have := hN.conj_mem τ hτ σ⁻¹
      rw [MulAction.mem_stabilizer_iff, inv_inv, mul_smul, mul_smul, inv_smul_eq_iff] at this
      exact this
    have := isIso_of_isConnected F f
    exact ⟨asIso f, hf⟩
  rw [isGalois_iff_pretransitive F X]
  refine ⟨fun y₁ y₂ ↦ ?_⟩
  obtain ⟨φ₁, rfl⟩ := key y₁
  obtain ⟨φ₂, rfl⟩ := key y₂
  refine ⟨φ₁.symm ≪≫ φ₂, ?_⟩
  change F.map (φ₁.inv ≫ φ₂.hom) (F.map φ₁.hom x) = _
  rw [F.map_comp, FintypeCat.comp_apply, ← FintypeCat.comp_apply (F.map φ₁.hom),
    ← F.map_comp, φ₁.hom_inv_id, F.map_id, FintypeCat.id_apply]

/-- V.5.11: every open normal subgroup of `π` is the stabilizer of a point of the fibre of a
Galois object. -/
theorem exists_isGalois_stabilizer_eq (V : OpenSubgroup (Aut F)) (hV : V.toSubgroup.Normal) :
    ∃ (X : C) (x : F.obj X), IsGalois X ∧ MulAction.stabilizer (Aut F) x = V := by
  obtain ⟨X, x, _, hx⟩ := exists_isConnected_stabilizer_eq F V
  exact ⟨X, x, (isGalois_iff_normal_stabilizer F X x).2 (hx ▸ hV), hx⟩

lemma subsingleton_obj_terminal :
    Subsingleton (F.obj (⊤_ C)) :=
  have h : IsTerminal ((F ⋙ FintypeCat.incl).obj (⊤_ C)) :=
    IsTerminal.isTerminalObj (F ⋙ FintypeCat.incl) (⊤_ C) terminalIsTerminal
  (Types.isTerminalEquivUnique _ h).instSubsingleton

lemma nonempty_obj_terminal :
    Nonempty (F.obj (⊤_ C)) :=
  have h : IsTerminal ((F ⋙ FintypeCat.incl).obj (⊤_ C)) :=
    IsTerminal.isTerminalObj (F ⋙ FintypeCat.incl) (⊤_ C) terminalIsTerminal
  ⟨(Types.isTerminalEquivUnique _ h).default⟩

/-- V.6, before V.6.5: the points of `F(Y)` fixed by `π` are exactly the images of the
sections `e ⟶ Y` of `Y` over the final object. -/
theorem forall_smul_eq_iff_exists_section {Y : C} (y : F.obj Y) :
    (∀ σ : Aut F, σ • y = y) ↔ ∃ s : ⊤_ C ⟶ Y, y ∈ Set.range (F.map s) := by
  have := subsingleton_obj_terminal F
  obtain ⟨p⟩ := nonempty_obj_terminal F
  refine ⟨fun h ↦ ?_, fun ⟨s, q, hq⟩ σ ↦ ?_⟩
  · have : MulAction.IsPretransitive (Aut F) (F.obj (⊤_ C)) :=
      ⟨fun a b ↦ ⟨1, Subsingleton.elim _ _⟩⟩
    have : Nonempty (F.obj (⊤_ C)) := ⟨p⟩
    have := isConnected_of_isPretransitive F (⊤_ C)
    obtain ⟨s, hs⟩ := (exists_hom_iff_stabilizer_le F p y).2 fun σ _ ↦ h σ
    exact ⟨s, p, hs⟩
  · rw [← hq, mulAction_naturality, Subsingleton.elim (σ • q) q]

/-- V.6, after V.6.4: an object is completely decomposed if it is a (finite) sum of copies of
the final object. -/
def IsCompletelyDecomposed (Y : C) : Prop :=
  ∃ n : ℕ, Nonempty (Y ≅ ∐ fun _ : Fin n ↦ ⊤_ C)

set_option backward.isDefEq.respectTransparency.types false in
/-- V.6, after V.6.4: `Y` is completely decomposed iff `π` acts trivially on `F(Y)`. -/
theorem isCompletelyDecomposed_iff (Y : C) :
    IsCompletelyDecomposed Y ↔ ∀ (σ : Aut F) (y : F.obj Y), σ • y = y := by
  have := subsingleton_obj_terminal F
  obtain ⟨p⟩ := nonempty_obj_terminal F
  refine ⟨fun ⟨n, ⟨e⟩⟩ σ y ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨j, q, hq⟩ := exists_map_sigmaι F _ (F.map e.hom y)
    refine (forall_smul_eq_iff_exists_section F y).2
      ⟨Sigma.ι (fun _ : Fin n ↦ ⊤_ C) j ≫ e.inv, q, ?_⟩ σ
    rw [F.map_comp, FintypeCat.comp_apply, hq, ← FintypeCat.comp_apply, ← F.map_comp,
      e.hom_inv_id, F.map_id, FintypeCat.id_apply]
  · let n := Nat.card (F.obj Y)
    let eY : Fin n ≃ F.obj Y := (Finite.equivFin (F.obj Y)).symm
    choose s hs using fun j : Fin n ↦ (forall_smul_eq_iff_exists_section F (eY j)).1 (h · _)
    have hs' (j : Fin n) : F.map (s j) p = eY j := by
      obtain ⟨q, hq⟩ := hs j
      rwa [Subsingleton.elim p q]
    let φ : (∐ fun _ : Fin n ↦ ⊤_ C) ⟶ Y := Sigma.desc s
    have hφ (j : Fin n) (q : F.obj (⊤_ C)) : F.map φ (F.map (Sigma.ι _ j) q) = eY j := by
      rw [← FintypeCat.comp_apply, ← F.map_comp, Sigma.ι_desc, Subsingleton.elim q p, hs']
    have : IsIso (F.map φ) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      refine ⟨fun z₁ z₂ hz ↦ ?_, fun y ↦ ⟨F.map (Sigma.ι _ (eY.symm y)) p, by simp [hφ]⟩⟩
      obtain ⟨j₁, q₁, rfl⟩ := exists_map_sigmaι F _ z₁
      obtain ⟨j₂, q₂, rfl⟩ := exists_map_sigmaι F _ z₂
      rw [hφ, hφ] at hz
      obtain rfl := eY.injective hz
      rw [Subsingleton.elim q₁ q₂]
    have := isIso_of_reflects_iso φ F
    exact ⟨n, ⟨(asIso φ).symm⟩⟩

/-- A closed subgroup of `π` is the intersection of the open subgroups containing it. -/
theorem exists_openSubgroup_le_of_notMem (K : Subgroup (Aut F)) (hK : IsClosed (K : Set (Aut F)))
    {g : Aut F} (hg : g ∉ K) : ∃ V : OpenSubgroup (Aut F), K ≤ V.toSubgroup ∧ g ∉ V := by
  have : (fun x ↦ g * x) ⁻¹' (K : Set (Aut F))ᶜ ∈ nhds (1 : Aut F) :=
    (continuous_const_mul g).continuousAt.preimage_mem_nhds
      (by simpa using hK.isOpen_compl.mem_nhds hg)
  obtain ⟨A, -, hA⟩ := (nhds_one_has_basis_stabilizers F).mem_iff.1 this
  let N := MulAction.stabilizer (Aut F) A.pt
  have hN : N.Normal := stabilizer_normal_of_isGalois F A.obj A.pt
  let V : Subgroup (Aut F) := K ⊔ N
  have hV : IsOpen (V : Set (Aut F)) :=
    Subgroup.isOpen_mono le_sup_right (stabilizer_isOpen (Aut F) A.pt)
  refine ⟨⟨V, hV⟩, le_sup_left, fun hgV ↦ ?_⟩
  change g ∈ V at hgV
  rw [← SetLike.mem_coe, Subgroup.mul_normal K N, Set.mem_mul] at hgV
  obtain ⟨k, hk, n, hn, rfl⟩ := hgV
  exact hA (N.inv_mem hn) (by simpa using hk)

end GaloisObjects

/-! ### V.5.8: `C` as the category of local systems on the fundamental groupoid -/

section LocalSystems

open scoped FintypeCatDiscrete

variable (C) [GaloisCategory C]

/-- V.5.8: the functor `X ↦ E_X` from `C` to functors on the fundamental groupoid `Γ`, where
`E_X(F) = F(X)` is the fibre of `X` at `F`. -/
def fiberFunctorEvaluation : C ⥤ (FiberFunctors.{u₁, u₂, w} C ⥤ FintypeCat.{w}) :=
  evaluation C FintypeCat.{w} ⋙ (whiskeringLeft _ _ FintypeCat.{w}).obj (ObjectProperty.ι _)

variable {C}

@[simp]
lemma fiberFunctorEvaluation_obj_obj (X : C) (F : FiberFunctors.{u₁, u₂, w} C) :
    ((fiberFunctorEvaluation C).obj X).obj F = F.obj.obj X :=
  rfl

@[simp]
lemma fiberFunctorEvaluation_obj_map (X : C) {F G : FiberFunctors.{u₁, u₂, w} C} (t : F ⟶ G) :
    ((fiberFunctorEvaluation C).obj X).map t = t.hom.app X :=
  rfl

@[simp]
lemma fiberFunctorEvaluation_map_app {X Y : C} (f : X ⟶ Y) (F : FiberFunctors.{u₁, u₂, w} C) :
    ((fiberFunctorEvaluation C).map f).app F = F.obj.map f :=
  rfl

instance : (fiberFunctorEvaluation.{u₁, u₂, w} C).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨F⟩ : Nonempty (FiberFunctors.{u₁, u₂, w} C) := inferInstance
    exact F.obj.map_injective (congrArg (fun t ↦ t.app F) h)

set_option backward.isDefEq.respectTransparency.types false in
instance : (fiberFunctorEvaluation.{u₁, u₂, w} C).Full where
  map_surjective {X Y} ξ := by
    obtain ⟨F₀⟩ : Nonempty (FiberFunctors.{u₁, u₂, w} C) := inferInstance
    let φ : (functorToAction F₀.obj).obj X ⟶ (functorToAction F₀.obj).obj Y :=
      { hom := ξ.app F₀
        comm := fun σ ↦ ξ.naturality (ObjectProperty.homMk σ.hom) }
    obtain ⟨f, hf⟩ := (functorToAction F₀.obj).map_surjective φ
    have hf' : F₀.obj.map f = ξ.app F₀ := congrArg Action.Hom.hom hf
    refine ⟨f, ?_⟩
    ext F : 2
    obtain ⟨t⟩ := nonempty_iso_fiberFunctors C F₀ F
    have h1 := ξ.naturality t.hom
    have h2 := t.hom.hom.naturality f
    simp only [fiberFunctorEvaluation_obj_map] at h1
    have : t.hom.hom.app X ≫ F.obj.map f = t.hom.hom.app X ≫ ξ.app F := by
      rw [← h2, hf']; exact h1.symm
    exact (cancel_epi (t.hom.hom.app X)).1 this


/-- The operation of `π_F = Aut F` on `ξ(F)`, for a functor `ξ` on the fundamental groupoid. -/
@[simps]
def groupoidAction (ξ : FiberFunctors.{u₁, u₂, w} C ⥤ FintypeCat.{w})
    (F : FiberFunctors.{u₁, u₂, w} C) : Aut F.obj →* End (ξ.obj F) where
  toFun σ := ξ.map (ObjectProperty.homMk σ.hom)
  map_one' := by
    change ξ.map (ObjectProperty.homMk (𝟙 F.obj)) = 𝟙 _
    rw [← ξ.map_id]
    rfl
  map_mul' σ τ := by
    change ξ.map (ObjectProperty.homMk (τ.hom ≫ σ.hom)) =
      ξ.map (ObjectProperty.homMk τ.hom) ≫ ξ.map (ObjectProperty.homMk σ.hom)
    rw [← ξ.map_comp]
    rfl

/-- The finite `π_F`-set `ξ(F)`. -/
def groupoidActionObj (ξ : FiberFunctors.{u₁, u₂, w} C ⥤ FintypeCat.{w})
    (F : FiberFunctors.{u₁, u₂, w} C) : Action FintypeCat.{w} (Aut F.obj) :=
  ⟨ξ.obj F, groupoidAction ξ F⟩

open scoped FintypeCatDiscrete in
set_option backward.isDefEq.respectTransparency.types false in
/-- V.5.8: a functor `ξ` on the fundamental groupoid is isomorphic to some `E_X` iff `π_F` acts
continuously on `ξ(F)`, for one (equivalently, every) object `F` of the groupoid. Together with
the full faithfulness of `X ↦ E_X`, this is SGA's equivalence of `C` with the category of such
"local systems" on the fundamental groupoid. -/
theorem mem_essImage_fiberFunctorEvaluation_iff
    (ξ : FiberFunctors.{u₁, u₂, w} C ⥤ FintypeCat.{w}) (F₀ : FiberFunctors.{u₁, u₂, w} C) :
    (fiberFunctorEvaluation C).essImage ξ ↔ (groupoidActionObj ξ F₀).IsContinuous := by
  constructor
  · rintro ⟨X, ⟨i⟩⟩
    let j : (functorToAction F₀.obj).obj X ≅ groupoidActionObj ξ F₀ :=
      Action.mkIso (i.app F₀) fun σ ↦ i.hom.naturality (ObjectProperty.homMk σ.hom)
    rw [isContinuous_iff_isOpen_stabilizer]
    intro y
    obtain ⟨x, rfl⟩ : ∃ x, j.hom.hom x = y := ⟨j.inv.hom y, by
      rw [← ConcreteCategory.comp_apply, ← Action.comp_hom, j.inv_hom_id]; rfl⟩
    rw [stabilizer_hom_apply j]
    exact stabilizer_isOpen (Aut F₀.obj) (show F₀.obj.obj X from x)
  · intro h
    let Y : ContAction FintypeCat.{w} (Aut F₀.obj) := ⟨groupoidActionObj ξ F₀, h⟩
    let X := (functorToContAction F₀.obj).objPreimage Y
    let ψ₀ : (functorToAction F₀.obj).obj X ≅ groupoidActionObj ξ F₀ :=
      (ObjectProperty.ι _).mapIso ((functorToContAction F₀.obj).objObjPreimageIso Y)
    let t (F : FiberFunctors.{u₁, u₂, w} C) : F₀ ≅ F := (nonempty_iso_fiberFunctors C F₀ F).some
    let ψ (F : FiberFunctors.{u₁, u₂, w} C) : F.obj.obj X ≅ ξ.obj F :=
      ((ObjectProperty.ι _).mapIso (t F)).symm.app X ≪≫ (Action.forget _ _).mapIso ψ₀ ≪≫
        ξ.mapIso (t F)
    refine ⟨X, ⟨NatIso.ofComponents ψ fun {F G} s ↦ ?_⟩⟩
    let τ : F₀ ⟶ F₀ := (t F).hom ≫ s ≫ (t G).inv
    have : IsIso τ.hom := isIso_of_fiberFunctor τ.hom
    have hτ : τ ≫ (t G).hom = (t F).hom ≫ s := by simp [τ]
    have hequiv := ψ₀.hom.comm (asIso τ.hom)
    change τ.hom.app X ≫ ψ₀.hom.hom = ψ₀.hom.hom ≫ ξ.map (ObjectProperty.homMk τ.hom) at hequiv
    change s.hom.app X ≫ (t G).inv.hom.app X ≫ ψ₀.hom.hom ≫ ξ.map (t G).hom =
      ((t F).inv.hom.app X ≫ ψ₀.hom.hom ≫ ξ.map (t F).hom) ≫ ξ.map s
    have h2' : (t F).inv ≫ τ = s ≫ (t G).inv := by simp [τ]
    have h2 : (t F).inv.hom.app X ≫ τ.hom.app X = s.hom.app X ≫ (t G).inv.hom.app X :=
      congrArg (fun φ : F ⟶ F₀ ↦ φ.hom.app X) h2'
    have h3 : ξ.map (t F).hom ≫ ξ.map s =
        ξ.map (ObjectProperty.homMk τ.hom) ≫ ξ.map (t G).hom := by
      rw [← ξ.map_comp, ← ξ.map_comp, ← hτ]
      rfl
    calc s.hom.app X ≫ (t G).inv.hom.app X ≫ ψ₀.hom.hom ≫ ξ.map (t G).hom
        = ((t F).inv.hom.app X ≫ τ.hom.app X) ≫ ψ₀.hom.hom ≫ ξ.map (t G).hom := by
          rw [h2, Category.assoc]
      _ = (t F).inv.hom.app X ≫ (τ.hom.app X ≫ ψ₀.hom.hom) ≫ ξ.map (t G).hom := by
          simp only [Category.assoc]
      _ = (t F).inv.hom.app X ≫ (ψ₀.hom.hom ≫ ξ.map (ObjectProperty.homMk τ.hom)) ≫
          ξ.map (t G).hom :=
          congrArg (fun k ↦ (t F).inv.hom.app X ≫ k ≫ ξ.map (t G).hom) hequiv
      _ = (t F).inv.hom.app X ≫ ψ₀.hom.hom ≫ ξ.map (ObjectProperty.homMk τ.hom) ≫
          ξ.map (t G).hom := by
          simp only [Category.assoc]
      _ = (t F).inv.hom.app X ≫ ψ₀.hom.hom ≫ ξ.map (t F).hom ≫ ξ.map s :=
          congrArg (fun k ↦ (t F).inv.hom.app X ≫ ψ₀.hom.hom ≫ k) h3.symm
      _ = ((t F).inv.hom.app X ≫ ψ₀.hom.hom ≫ ξ.map (t F).hom) ≫ ξ.map s := by
          simp only [Category.assoc]


/-- V.5.8: a local system on the fundamental groupoid is a functor `ξ : Γ ⥤ (finite sets)` such
that `π_F` acts continuously on `ξ(F)` for every `F`. -/
def IsContinuousLocalSystem (ξ : FiberFunctors.{u₁, u₂, w} C ⥤ FintypeCat.{w}) : Prop :=
  ∀ F, (groupoidActionObj ξ F).IsContinuous

variable (C) in
/-- V.5.8: the functor `X ↦ E_X` from `C` to local systems on the fundamental groupoid. -/
def toLocalSystems :
    C ⥤ ObjectProperty.FullSubcategory (IsContinuousLocalSystem.{u₁, u₂, w} (C := C)) :=
  ObjectProperty.lift _ (fiberFunctorEvaluation C) fun X F ↦
    (mem_essImage_fiberFunctorEvaluation_iff _ F).1 ⟨X, ⟨Iso.refl _⟩⟩

instance : (toLocalSystems.{u₁, u₂, w} C).Full :=
  Functor.Full.of_comp_faithful_iso (ObjectProperty.liftCompιIso _ _ _)

instance : (toLocalSystems.{u₁, u₂, w} C).Faithful :=
  Functor.Faithful.of_comp_iso (ObjectProperty.liftCompιIso _ _ _)

instance : (toLocalSystems.{u₁, u₂, w} C).EssSurj where
  mem_essImage ξ := by
    obtain ⟨F₀⟩ : Nonempty (FiberFunctors.{u₁, u₂, w} C) := inferInstance
    obtain ⟨X, ⟨i⟩⟩ := (mem_essImage_fiberFunctorEvaluation_iff ξ.obj F₀).2 (ξ.property F₀)
    exact ⟨X, ⟨ObjectProperty.isoMk _ i⟩⟩

/-- V.5.8: the functor `X ↦ E_X` is an equivalence of `C` with the category of local systems on
the fundamental groupoid. -/
instance : (toLocalSystems.{u₁, u₂, w} C).IsEquivalence where

end LocalSystems

/-! ### V.5.10: local systems on a family of fibre functors -/

section LocalSystemsFamily

open scoped FintypeCatDiscrete

variable [GaloisCategory C] {S : Type*} (Fs : S → FiberFunctors.{u₁, u₂, w} C)

/-- The groupoid `S` of V.5.10, with `Hom(s, s') = Hom(F_s, F_{s'})`, maps fully faithfully to the
fundamental groupoid; if `S` is non-empty, this is an equivalence (`Γ` is connected). -/
instance [Nonempty S] : (inducedFunctor Fs).IsEquivalence where
  essSurj := ⟨fun F ↦ by
    obtain ⟨s⟩ := ‹Nonempty S›
    exact ⟨s, ⟨(nonempty_iso_fiberFunctors C (Fs s) F).some⟩⟩⟩

/-- V.5.10: the functor `X ↦ E_X ∘ f`, `(E_X ∘ f)(s) = F_s(X)`. -/
def familyEvaluation : C ⥤ (InducedCategory _ Fs ⥤ FintypeCat.{w}) :=
  fiberFunctorEvaluation C ⋙ (Functor.whiskeringLeft _ _ FintypeCat.{w}).obj (inducedFunctor Fs)

/-- The finite `π_{F_s}`-set `ξ(s)`, for a functor `ξ` on `S`. -/
def familyActionObj (ξ : InducedCategory _ Fs ⥤ FintypeCat.{w}) (s : S) :
    Action FintypeCat.{w} (Aut (Fs s).obj) where
  V := ξ.obj s
  ρ :=
    { toFun σ := ξ.map (InducedCategory.homMk (ObjectProperty.homMk σ.hom))
      map_one' := by
        change ξ.map (InducedCategory.homMk (ObjectProperty.homMk (𝟙 (Fs s).obj))) = 𝟙 _
        rw [← ξ.map_id]
        rfl
      map_mul' σ τ := by
        change ξ.map (InducedCategory.homMk (ObjectProperty.homMk (τ.hom ≫ σ.hom))) =
          ξ.map (InducedCategory.homMk (ObjectProperty.homMk τ.hom)) ≫
            ξ.map (InducedCategory.homMk (ObjectProperty.homMk σ.hom))
        rw [← ξ.map_comp]
        rfl }

lemma isContinuous_familyActionObj_of_iso {ξ ξ' : InducedCategory _ Fs ⥤ FintypeCat.{w}}
    (e : ξ ≅ ξ') (s : S) (h : (familyActionObj Fs ξ' s).IsContinuous) :
    (familyActionObj Fs ξ s).IsContinuous := by
  let j : familyActionObj Fs ξ s ≅ familyActionObj Fs ξ' s :=
    Action.mkIso (e.app s) fun σ ↦ e.hom.naturality _
  rw [isContinuous_iff_isOpen_stabilizer] at h ⊢
  intro x
  rw [← stabilizer_hom_apply j]
  exact h _

variable (C) in
/-- V.5.10: continuity of the operations of the `π_{F_s}` on `ξ(s)`. -/
def IsContinuousFamilyLocalSystem (ξ : InducedCategory _ Fs ⥤ FintypeCat.{w}) : Prop :=
  ∀ s, (familyActionObj Fs ξ s).IsContinuous

variable [Nonempty S]

instance : (familyEvaluation Fs).Full := by
  have : ((Functor.whiskeringLeft _ _ FintypeCat.{w}).obj (inducedFunctor Fs)).IsEquivalence :=
    (inducedFunctor Fs).asEquivalence.symm.congrLeft.isEquivalence_functor
  unfold familyEvaluation
  infer_instance

instance : (familyEvaluation Fs).Faithful := by
  have : ((Functor.whiskeringLeft _ _ FintypeCat.{w}).obj (inducedFunctor Fs)).IsEquivalence :=
    (inducedFunctor Fs).asEquivalence.symm.congrLeft.isEquivalence_functor
  unfold familyEvaluation
  infer_instance

/-- V.5.10: a functor `ξ` on `S` is isomorphic to some `E_X ∘ f` iff `π_{F_s}` acts continuously on
`ξ(s)` for every `s`. Together with the full faithfulness of `X ↦ E_X ∘ f`, this is the variant
of V.5.8 with `Γ` replaced by `S` (for `S` a point, it is V.4.1). -/
theorem mem_essImage_familyEvaluation_iff (ξ : InducedCategory _ Fs ⥤ FintypeCat.{w}) :
    (familyEvaluation Fs).essImage ξ ↔ IsContinuousFamilyLocalSystem C Fs ξ := by
  constructor
  · rintro ⟨X, ⟨i⟩⟩ s
    refine isContinuous_familyActionObj_of_iso Fs i.symm s ?_
    exact (mem_essImage_fiberFunctorEvaluation_iff ((fiberFunctorEvaluation C).obj X) (Fs s)).1
      ⟨X, ⟨Iso.refl _⟩⟩
  · intro h
    obtain ⟨s₀⟩ := ‹Nonempty S›
    let e := (inducedFunctor Fs).asEquivalence
    let η : FiberFunctors.{u₁, u₂, w} C ⥤ FintypeCat.{w} := e.inverse ⋙ ξ
    let c : ((Functor.whiskeringLeft _ _ FintypeCat.{w}).obj (inducedFunctor Fs)).obj η ≅ ξ :=
      e.symm.congrLeft.counitIso.app ξ
    have hη : (groupoidActionObj η (Fs s₀)).IsContinuous :=
      isContinuous_familyActionObj_of_iso Fs c s₀ (h s₀)
    obtain ⟨X, ⟨i⟩⟩ := (mem_essImage_fiberFunctorEvaluation_iff η (Fs s₀)).2 hη
    exact ⟨X, ⟨Functor.isoWhiskerLeft (inducedFunctor Fs) i ≪≫ c⟩⟩

end LocalSystemsFamily

/-! ### V.5.5: left exact functors commuting with finite sums -/

section FixedPoints

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- V.5.5 (v): the functor `X ↦ F(X)^H` of the points of the fibre fixed by a subgroup `H` of
`π_F`. -/
@[simps]
def fixedPoints (H : Subgroup (Aut F)) : C ⥤ Type w where
  obj X := {x : F.obj X // ∀ h ∈ H, h • x = x}
  map f := ↾fun x ↦ ⟨F.map f x.1, fun h hh ↦ by rw [mulAction_naturality, x.2 h hh]⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- V.5.5, (v) ⇒ (ii): the functor of fixed points of a subgroup commutes with sums of two
objects. -/
instance (H : Subgroup (Aut F)) :
    PreservesColimitsOfShape (Discrete WalkingPair) (fixedPoints F H) where
  preservesColimit {K} := by
    let A := K.obj ⟨WalkingPair.left⟩
    let B := K.obj ⟨WalkingPair.right⟩
    suffices PreservesColimit (pair A B) (fixedPoints F H) from
      preservesColimit_of_iso_diagram _ (diagramIsoPair K).symm
    refine preservesColimit_of_preserves_colimit_cocone (coprodIsCoprod _ _) ?_
    obtain ⟨hl, hr, hc⟩ := (Types.binaryCofan_isColimit_iff _).1
      ⟨(isColimitMapCoconeBinaryCofanEquiv (F ⋙ FintypeCat.incl) _ _)
        (isColimitOfPreserves (F ⋙ FintypeCat.incl) (coprodIsCoprod A B))⟩
    refine (isColimitMapCoconeBinaryCofanEquiv (fixedPoints F H) _ _).symm
      ((Types.binaryCofan_isColimit_iff _).2 ⟨?_, ?_, ?_⟩).some
    · exact fun a b h ↦ Subtype.ext (hl (congrArg Subtype.val h))
    · exact fun a b h ↦ Subtype.ext (hr (congrArg Subtype.val h))
    · constructor
      · rw [Set.disjoint_iff]
        rintro _ ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
        exact Set.disjoint_iff.1 hc.1 ⟨⟨a.1, rfl⟩, ⟨b.1, congrArg Subtype.val hb⟩⟩
      · rw [codisjoint_iff, eq_top_iff]
        intro z _
        have hz := eq_top_iff.1 (codisjoint_iff.1 hc.2) (Set.mem_univ (z.1 : F.obj (A ⨿ B)))
        rcases hz with ⟨(a : F.obj A), ha⟩ | ⟨(b : F.obj B), hb⟩
        · change F.map coprod.inl a = z.1 at ha
          refine Or.inl ⟨⟨a, fun h hh ↦ hl ?_⟩, Subtype.ext ha⟩
          change F.map coprod.inl (h • a) = F.map coprod.inl a
          rw [← mulAction_naturality, ha, z.2 h hh]
        · change F.map coprod.inr b = z.1 at hb
          refine Or.inr ⟨⟨b, fun h hh ↦ hr ?_⟩, Subtype.ext hb⟩
          change F.map coprod.inr (h • b) = F.map coprod.inr b
          rw [← mulAction_naturality, hb, z.2 h hh]


variable (G : C ⥤ FintypeCat.{w}) [PreservesFiniteLimits G]
  [PreservesColimitsOfShape (Discrete WalkingPair) G]

omit [PreservesFiniteLimits G] in
/-- A functor to finite sets commuting with sums of two objects commutes with finite sums. -/
lemma preservesFiniteCoproducts_of_preservesBinary : PreservesFiniteCoproducts G := by
  have : PreservesColimitsOfShape (Discrete PEmpty.{1}) G := by
    have hI : IsInitial (G.obj (⊥_ C)) :=
      ((Concrete.initial_iff_empty_of_preserves_of_reflects _).2
        (isEmpty_obj_of_isInitial G initialIsInitial)).some
    have := preservesInitial_of_iso G (initialIsInitial.uniqueUpToIso hI)
    exact preservesColimitsOfShape_pempty_of_preservesInitial G
  exact ⟨fun n ↦ PreservesFiniteCoproducts.of_preserves_binary_and_initial G (Fin n)⟩

omit [PreservesFiniteLimits G] in
/-- Every point of `G(Y)` comes from a connected subobject of `Y`. -/
lemma exists_isConnected_map_eq (Y : C) (y : G.obj Y) :
    ∃ (X : C) (i : X ⟶ Y) (x : G.obj X), IsConnected X ∧ G.map i x = y := by
  have := preservesFiniteCoproducts_of_preservesBinary G
  obtain ⟨ι, _, f, e, hf⟩ := has_decomp_connected_components' Y
  obtain ⟨j, x, hx⟩ := exists_map_sigmaι G f (G.map e.inv y)
  refine ⟨f j, Sigma.ι f j ≫ e.hom, x, hf j, ?_⟩
  rw [G.map_comp, FintypeCat.comp_apply, hx, ← FintypeCat.comp_apply, ← G.map_comp,
    e.inv_hom_id, G.map_id, FintypeCat.id_apply]

/-- The points of `G` over connected objects. -/
abbrev ConnectedElements : Type _ :=
  ObjectProperty.FullSubcategory fun p : (G ⋙ FintypeCat.incl).Elements ↦ IsConnected p.1

set_option backward.isDefEq.respectTransparency.types false in
instance : IsCofilteredOrEmpty (ConnectedElements G) where
  cone_objs := fun ⟨⟨X₁, x₁⟩, h₁⟩ ⟨⟨X₂, x₂⟩, h₂⟩ ↦ by
    obtain ⟨p, hp₁, hp₂⟩ := exists_map_fst_snd G x₁ x₂
    obtain ⟨Z, i, z, hZ, hz⟩ := exists_isConnected_map_eq G _ p
    refine ⟨⟨⟨Z, z⟩, hZ⟩, ObjectProperty.homMk ⟨i ≫ prod.fst, ?_⟩,
      ObjectProperty.homMk ⟨i ≫ prod.snd, ?_⟩, trivial⟩
    · change G.map (i ≫ prod.fst) z = x₁
      rw [G.map_comp, FintypeCat.comp_apply, hz, hp₁]
    · change G.map (i ≫ prod.snd) z = x₂
      rw [G.map_comp, FintypeCat.comp_apply, hz, hp₂]
  cone_maps := fun ⟨⟨X, x⟩, hX⟩ ⟨⟨Y, y⟩, _⟩ f g ↦ by
    refine ⟨⟨⟨X, x⟩, hX⟩, 𝟙 _, ?_⟩
    have := hX
    have h : f.hom.val = g.hom.val := evaluation_injective_of_leftExact G X Y x
      (f.hom.property.trans g.hom.property.symm)
    ext
    simpa using h

include F in
/-- The final object of a Galois category is connected. -/
lemma isConnected_terminal : IsConnected (⊤_ C) := by
  have := subsingleton_obj_terminal F
  have := nonempty_obj_terminal F
  have : MulAction.IsPretransitive (Aut F) (F.obj (⊤_ C)) :=
    ⟨fun a b ↦ ⟨1, Subsingleton.elim _ _⟩⟩
  exact isConnected_of_isPretransitive F (⊤_ C)

set_option backward.isDefEq.respectTransparency.types false in
/-- V.5.5, (ii) ⇒ (v), in functor form: a left exact functor `G` to finite sets which commutes
with sums of two objects is isomorphic to `X ↦ F(X)^H` for a closed subgroup `H` of `π_F`.
(`G` is pro-represented by its points over connected objects, and `H` is the intersection of
the stabilizers of a compatible family of points of the fibres of these objects.) -/
theorem exists_iso_fixedPoints : ∃ H : Subgroup (Aut F), IsClosed (H : Set (Aut F)) ∧
    Nonempty (G ⋙ FintypeCat.incl ≅ fixedPoints F H) := by
  let J := ConnectedElements G
  let D : J ⥤ Type w :=
    ObjectProperty.ι _ ⋙ CategoryOfElements.π (G ⋙ FintypeCat.incl) ⋙ F ⋙ FintypeCat.incl
  have (j : J) : Nonempty (D.obj j) := by
    have := j.property
    exact nonempty_fiber_of_isConnected F j.obj.1
  have (j : J) : Finite (D.obj j) := inferInstanceAs (Finite (F.obj j.obj.1))
  obtain ⟨s₀, hs⟩ := nonempty_sections_of_finite_cofiltered_system D
  let s (k : J) : F.obj k.obj.1 := s₀ k
  have hs' {j j' : J} (f : j ⟶ j') : F.map f.hom.val (s j) = s j' := hs f
  let H : Subgroup (Aut F) := ⨅ j, MulAction.stabilizer (Aut F) (s j)
  have hH : IsClosed (H : Set (Aut F)) := by
    rw [Subgroup.coe_iInf]
    exact isClosed_iInter fun j ↦ Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen _ _)
  have key (j j' : J) {Y : C} (f : j.obj.1 ⟶ Y) (f' : j'.obj.1 ⟶ Y)
      (h : G.map f j.obj.2 = G.map f' j'.obj.2) : F.map f (s j) = F.map f' (s j') := by
    obtain ⟨k, p, p', -⟩ := IsCofilteredOrEmpty.cone_objs j j'
    have := k.property
    have hpf : p.hom.val ≫ f = p'.hom.val ≫ f' := by
      apply evaluation_injective_of_leftExact G k.obj.1 Y k.obj.2
      change G.map (p.hom.val ≫ f) k.obj.2 = G.map (p'.hom.val ≫ f') k.obj.2
      rw [G.map_comp, G.map_comp, FintypeCat.comp_apply, FintypeCat.comp_apply]
      change G.map f ((G ⋙ FintypeCat.incl).map p.hom.val k.obj.2) =
        G.map f' ((G ⋙ FintypeCat.incl).map p'.hom.val k.obj.2)
      rw [p.hom.property, p'.hom.property, h]
    rw [← hs' p, ← hs' p', ← FintypeCat.comp_apply, ← F.map_comp, hpf, F.map_comp,
      FintypeCat.comp_apply]
  choose X i x hX hx using exists_isConnected_map_eq G
  let j (Y : C) (y : G.obj Y) : J := ⟨⟨X Y y, x Y y⟩, hX Y y⟩
  let t (Y : C) (y : G.obj Y) : (fixedPoints F H).obj Y :=
    ⟨F.map (i Y y) (s (j Y y)), fun h hh ↦ by
      have : h ∈ MulAction.stabilizer (Aut F) (s (j Y y)) := Subgroup.mem_iInf.1 hh (j Y y)
      rw [mulAction_naturality, this]⟩
  have ht (Y : C) (k : J) (f : k.obj.1 ⟶ Y) : (t Y (G.map f k.obj.2)).1 = F.map f (s k) :=
    key (j Y _) k (i Y _) f (hx Y _)
  have hinj (Y : C) : Function.Injective (t Y) := by
    intro y₁ y₂ h
    obtain ⟨k, p, p', -⟩ := IsCofilteredOrEmpty.cone_objs (j Y y₁) (j Y y₂)
    have := k.property
    have e : p.hom.val ≫ i Y y₁ = p'.hom.val ≫ i Y y₂ := by
      apply evaluation_injective_of_isConnected F k.obj.1 Y (s k)
      change F.map (p.hom.val ≫ i Y y₁) (s k) = F.map (p'.hom.val ≫ i Y y₂) (s k)
      rw [F.map_comp, F.map_comp, FintypeCat.comp_apply, FintypeCat.comp_apply, hs' p, hs' p']
      exact congrArg Subtype.val h
    have h₁ : G.map (p.hom.val ≫ i Y y₁) k.obj.2 = y₁ := by
      rw [G.map_comp, FintypeCat.comp_apply]
      change G.map (i Y y₁) ((G ⋙ FintypeCat.incl).map p.hom.val k.obj.2) = y₁
      rw [p.hom.property]
      exact hx Y y₁
    have h₂ : G.map (p'.hom.val ≫ i Y y₂) k.obj.2 = y₂ := by
      rw [G.map_comp, FintypeCat.comp_apply]
      change G.map (i Y y₂) ((G ⋙ FintypeCat.incl).map p'.hom.val k.obj.2) = y₂
      rw [p'.hom.property]
      exact hx Y y₂
    rw [← h₁, ← h₂, e]
  have hsurj (Y : C) : Function.Surjective (t Y) := by
    intro z
    have : Nonempty J := by
      have := isConnected_terminal F
      have h : IsTerminal ((G ⋙ FintypeCat.incl).obj (⊤_ C)) :=
        IsTerminal.isTerminalObj (G ⋙ FintypeCat.incl) (⊤_ C) terminalIsTerminal
      exact ⟨⟨⟨⊤_ C, (Types.isTerminalEquivUnique _ h).default⟩, this⟩⟩
    obtain ⟨k, hk⟩ := isCompact_univ.elim_directed_family_closed
      (fun k : J ↦ (MulAction.stabilizer (Aut F) (s k) : Set (Aut F)) \
        MulAction.stabilizer (Aut F) z.1)
      (fun k ↦ (Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen _ _)).sdiff
        (stabilizer_isOpen _ _))
      (by
        rw [Set.disjoint_iff]
        rintro σ ⟨-, hσ⟩
        simp only [Set.mem_iInter, Set.mem_sdiff, SetLike.mem_coe] at hσ
        obtain ⟨k⟩ := this
        refine (hσ k).2 (z.2 σ ?_)
        exact Subgroup.mem_iInf.2 fun k ↦ (hσ k).1)
      (fun k₁ k₂ ↦ by
        obtain ⟨k, p₁, p₂, -⟩ := IsCofilteredOrEmpty.cone_objs k₁ k₂
        refine ⟨k, fun σ hσ ↦ ⟨?_, hσ.2⟩, fun σ hσ ↦ ⟨?_, hσ.2⟩⟩
        · change σ • s k₁ = s k₁
          rw [← hs' p₁, mulAction_naturality, hσ.1]
        · change σ • s k₂ = s k₂
          rw [← hs' p₂, mulAction_naturality, hσ.1])
    have hle : MulAction.stabilizer (Aut F) (s k) ≤ MulAction.stabilizer (Aut F) z.1 :=
      fun σ hσ ↦ by
        by_contra h
        exact Set.disjoint_left.1 hk (Set.mem_univ σ) ⟨hσ, h⟩
    have := k.property
    obtain ⟨f, hf⟩ := (exists_hom_iff_stabilizer_le F (s k) z.1).2 hle
    exact ⟨G.map f k.obj.2, Subtype.ext ((ht Y k f).trans hf)⟩
  refine ⟨H, hH, ⟨NatIso.ofComponents
    (fun Y ↦ (Equiv.ofBijective (t Y) ⟨hinj Y, hsurj Y⟩).toIso) fun {Y Y'} g ↦ ?_⟩⟩
  ext y
  apply Subtype.ext
  change (t Y' (G.map g y)).1 = F.map g (F.map (i Y y) (s (j Y y)))
  have : G.map g y = G.map (i Y y ≫ g) (j Y y).obj.2 := by
    rw [G.map_comp, FintypeCat.comp_apply]
    exact congrArg (G.map g) (hx Y y).symm
  rw [this, ht Y' (j Y y) (i Y y ≫ g), F.map_comp, FintypeCat.comp_apply]

end FixedPoints

section FixedPointsTFAE

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (G : C ⥤ FintypeCat.{w})
  [PreservesFiniteLimits G]

/-- V.5.5, (i) ⇔ (ii) ⇔ (v), in functor form: for a left exact functor `G` from a Galois
category to finite sets, the following are equivalent: `G` commutes with finite sums; `G`
commutes with sums of two objects; `G` is isomorphic to `X ↦ F(X)^H` for a closed subgroup `H`
of `π_F`. SGA states this for `G = Hom(Q, -)`, `Q` a pro-object; conditions (iii) and (iv),
which refer to the terms of `Q`, are not formalized. -/
theorem preservesFiniteCoproducts_tfae : List.TFAE
    [PreservesFiniteCoproducts G, PreservesColimitsOfShape (Discrete WalkingPair) G,
      ∃ H : Subgroup (Aut F), IsClosed (H : Set (Aut F)) ∧
        Nonempty (G ⋙ FintypeCat.incl ≅ fixedPoints F H)] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 → 1 := fun _ ↦ preservesFiniteCoproducts_of_preservesBinary G
  tfae_have 2 → 3 := fun _ ↦ exists_iso_fixedPoints F G
  tfae_have 3 → 2 := fun ⟨H, _, ⟨e⟩⟩ ↦ by
    have := preservesColimitsOfShape_of_natIso e.symm (J := Discrete WalkingPair)
    exact preservesColimitsOfShape_of_reflects_of_preserves G FintypeCat.incl
  tfae_finish

/-- V.5.6, (i) ⇔ (ii) ⇔ (iii), in functor form: for a left exact functor `G` to finite sets,
the following are equivalent: `G` is isomorphic to the fibre functor `F`; `G` is a fibre
functor; `G` commutes with sums of two objects and takes non-empty values on non-initial
objects. (Condition (iv) refers to the terms of a pro-object representing `G` and is not
formalized.) -/
theorem fiberFunctor_tfae : List.TFAE
    [Nonempty (F ≅ G), FiberFunctor G,
      PreservesColimitsOfShape (Discrete WalkingPair) G ∧
        ∀ X : C, (IsInitial X → False) → Nonempty (G.obj X)] := by
  tfae_have 1 → 2 := fun ⟨e⟩ ↦ fiberFunctor_of_natIso e
  tfae_have 2 → 3 := fun _ ↦ ⟨inferInstance, fun X hX ↦ (not_initial_iff_fiber_nonempty G X).1 hX⟩
  tfae_have 3 → 1 := fun ⟨_, h⟩ ↦ nonempty_iso_of_leftExact G F h
  tfae_finish

end FixedPointsTFAE

/-! ### V.5.4–V.5.6: the terms of a pro-object -/

section ProTerms

open Opposite

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{u₂}) [FiberFunctor F] {G : C ⥤ Type u₂}
  (R : G.ProRepresentation)

include F in
/-- A morphism from a connected object to a sum of two objects factors through one of them. -/
lemma exists_factor_coprod_of_isConnected {A X Y : C} [IsConnected A] (f : A ⟶ X ⨿ Y) :
    (∃ g : A ⟶ X, g ≫ coprod.inl = f) ∨ (∃ g : A ⟶ Y, g ≫ coprod.inr = f) := by
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  have hmem : F.map f a ∈ Set.range (F.map (coprod.inl : X ⟶ X ⨿ Y)) ∪
      Set.range (F.map (coprod.inr : Y ⟶ X ⨿ Y)) := by
    rw [range_map_union_of_isColimit F (coprodIsCoprod X Y)]
    trivial
  have key {Z : C} (i : Z ⟶ X ⨿ Y) [Mono i] (hi : F.map f a ∈ Set.range (F.map i)) :
      ∃ g : A ⟶ Z, g ≫ i = f := by
    obtain ⟨z, hz⟩ := hi
    let p := (fiberPullbackEquiv F f i).symm ⟨(a, z), hz.symm⟩
    have : IsIso (pullback.fst f i) := IsConnected.noTrivialComponent _ (pullback.fst f i)
      fun h ↦ ((initial_iff_fiber_empty F _).1 ⟨h⟩).false p
    exact ⟨inv (pullback.fst f i) ≫ pullback.snd f i, by simp [pullback.condition]⟩
  rcases hmem with h | h
  · exact Or.inl (key _ h)
  · exact Or.inr (key _ h)

include F in
/-- V.5.5, (iii) ⇒ (ii): if the terms of a pro-representation of `G` are connected, `G` commutes
with sums of two objects. -/
theorem preservesBinaryCoproducts_of_isConnected (hR : ∀ i, IsConnected (R.F.obj i)) :
    PreservesColimitsOfShape (Discrete WalkingPair) G where
  preservesColimit {K} := by
    suffices ∀ X Y : C, PreservesColimit (pair X Y) G from
      preservesColimit_of_iso_diagram _ (diagramIsoPair K).symm
    intro X Y
    refine preservesColimit_of_preserves_colimit_cocone (coprodIsCoprod X Y) ?_
    have inj {Z : C} (i : Z ⟶ X ⨿ Y) [Mono i] : Function.Injective (G.map i) := by
      intro x x' h
      obtain ⟨j, f, rfl⟩ := R.exists_map_elem x
      obtain ⟨j', f', rfl⟩ := R.exists_map_elem x'
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, R.map_elem_eq_iff] at h
      obtain ⟨k, p, p', hk⟩ := h
      exact (R.map_elem_eq_iff f f').2 ⟨k, p, p', (cancel_mono i).1 (by simpa using hk)⟩
    refine (isColimitMapCoconeBinaryCofanEquiv G _ _).symm
      ((Types.binaryCofan_isColimit_iff _).2 ⟨inj _, inj _, ?_, ?_⟩).some
    · rw [Set.disjoint_iff]
      rintro _ ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
      obtain ⟨j, f, rfl⟩ := R.exists_map_elem x
      obtain ⟨j', f', rfl⟩ := R.exists_map_elem y
      change G.map coprod.inr (G.map f' _) = G.map coprod.inl (G.map f _) at hy
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, R.map_elem_eq_iff] at hy
      obtain ⟨k, p, p', hk⟩ := hy
      have := hR k
      obtain ⟨a⟩ := nonempty_fiber_of_isConnected F (R.F.obj k)
      have h := congrArg (fun φ ↦ F.map φ a) hk
      simp only [Functor.map_comp, FintypeCat.comp_apply] at h
      exact Set.disjoint_left.1 (disjoint_range_map_of_isColimit F (coprodIsCoprod X Y))
        ⟨_, h.symm⟩ ⟨_, rfl⟩
    · rw [codisjoint_iff, eq_top_iff]
      intro z _
      obtain ⟨j, f, rfl⟩ := R.exists_map_elem z
      have := hR j
      rcases exists_factor_coprod_of_isConnected F f with ⟨g, rfl⟩ | ⟨g, rfl⟩
      · exact Or.inl ⟨G.map g (R.elem j), (Functor.map_comp_apply _ _ _ _).symm⟩
      · exact Or.inr ⟨G.map g (R.elem j), (Functor.map_comp_apply _ _ _ _).symm⟩

include F in
/-- V.4 d), V.5.5, (ii) ⇒ (iii): if `G` commutes with sums of two objects, the terms of a strict
pro-representation of `G` are connected. -/
theorem isConnected_of_preservesBinaryCoproducts (hR : R.IsStrict)
    [PreservesColimitsOfShape (Discrete WalkingPair) G] (i : R.I) : IsConnected (R.F.obj i) := by
  rw [isConnected_iff_isIndecomposable F]
  refine ⟨fun {A B ia ib} hc ↦ ?_, fun ⟨hI⟩ ↦ ?_⟩
  · have hG := (Types.binaryCofan_isColimit_iff _).1
      ⟨(isColimitMapCoconeBinaryCofanEquiv G ia ib) (isColimitOfPreserves G hc)⟩
    have hmem : R.elem i ∈ Set.range (G.map ia) ∪ Set.range (G.map ib) := by
      have h2 : Set.range (G.map ia) ∪ Set.range (G.map ib) = Set.univ :=
        codisjoint_iff.1 hG.2.2.codisjoint
      rw [h2]
      trivial
    -- if the universal element comes from a summand, the other summand has empty fibre
    have key {Z W : C} (u : Z ⟶ R.F.obj i) (v : W ⟶ R.F.obj i)
        (hc' : IsColimit (BinaryCofan.mk u v)) (h : R.elem i ∈ Set.range (G.map u)) :
        Nonempty (IsInitial W) := by
      obtain ⟨x, hx⟩ := h
      obtain ⟨j, f, rfl⟩ := R.exists_map_elem x
      rw [← Functor.map_comp_apply] at hx
      obtain ⟨k, p, p', hk⟩ := (R.map_elem_eq_iff (f ≫ u) (𝟙 _)).1
        (hx.trans (by simp))
      have := hR p'
      have hs := surjective_on_fiber_of_epi F (R.F.map p')
      refine (initial_iff_fiber_empty F W).2 ⟨fun w ↦ ?_⟩
      obtain ⟨c, hc⟩ := hs (F.map v w)
      have hcomp : F.map (R.F.map p') c = F.map u (F.map (R.F.map p ≫ f) c) := by
        rw [← FintypeCat.comp_apply, ← F.map_comp, Category.assoc, hk, Category.comp_id]
      exact Set.disjoint_left.1 (disjoint_range_map_of_isColimit F hc') ⟨_, hcomp.symm.trans hc⟩
        ⟨w, rfl⟩
    rcases hmem with h | h
    · exact Or.inr (key ia ib hc h)
    · have hc' : IsColimit (BinaryCofan.mk ib ia) :=
        BinaryCofan.isColimitFlip hc
      exact Or.inl (key ib ia hc' h)
  · have hc : IsColimit (BinaryCofan.mk (𝟙 (R.F.obj i)) (𝟙 (R.F.obj i))) :=
      ((BinaryCofan.isColimit_iff_isIso_inl hI _).2 (inferInstanceAs (IsIso (𝟙 _)))).some
    have hG := (Types.binaryCofan_isColimit_iff _).1
      ⟨(isColimitMapCoconeBinaryCofanEquiv G _ _) (isColimitOfPreserves G hc)⟩
    have h1 : R.elem i ∈ Set.range (G.map (𝟙 (R.F.obj i))) := ⟨R.elem i, by simp⟩
    exact Set.disjoint_left.1 hG.2.2.1 h1 h1

include F in
/-- If the terms of a pro-representation of `G` are connected, `G` takes finite values: choosing a
compatible family of points of the fibres of the terms, `G(X)` embeds into `F(X)`. -/
lemma finite_obj_of_isConnected (hR : ∀ i, IsConnected (R.F.obj i)) (X : C) :
    Finite (G.obj X) := by
  let D := R.F ⋙ F ⋙ FintypeCat.incl
  have (i : R.I) : Nonempty (D.obj i) := by
    have := hR i
    exact nonempty_fiber_of_isConnected F (R.F.obj i)
  have (i : R.I) : Finite (D.obj i) := inferInstanceAs (Finite (F.obj (R.F.obj i)))
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system D
  choose i f hf using fun x : G.obj X ↦ R.exists_map_elem x
  refine Finite.of_injective (fun x ↦ F.map (f x) (s (i x))) fun x x' h ↦ ?_
  obtain ⟨k, p, p', -⟩ := IsCofilteredOrEmpty.cone_objs (i x) (i x')
  have := hR k
  have e : R.F.map p ≫ f x = R.F.map p' ≫ f x' := by
    apply evaluation_injective_of_isConnected F _ X (s k)
    simp only [F.map_comp, FintypeCat.comp_apply]
    change F.map (f x) (D.map p (s k)) = F.map (f x') (D.map p' (s k))
    rw [hs p, hs p']
    exact h
  rw [← hf x, ← hf x']
  exact (R.map_elem_eq_iff _ _).2 ⟨k, p, p', e⟩

/-- A functor to types with finite values, as a functor to finite types. -/
@[simps]
noncomputable def toFintypeCat (G : C ⥤ Type u₂) (hG : ∀ X, Finite (G.obj X)) :
    C ⥤ FintypeCat.{u₂} where
  obj X := letI := Fintype.ofFinite (G.obj X); FintypeCat.of (G.obj X)
  map f := FintypeCat.homMk (G.map f)

/-- `toFintypeCat G` recovers `G`. -/
noncomputable def toFintypeCatCompIncl (G : C ⥤ Type u₂) (hG : ∀ X, Finite (G.obj X)) :
    toFintypeCat G hG ⋙ FintypeCat.incl ≅ G :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

include F in
/-- V.5.5, (i) ⇔ (ii) ⇔ (iii) ⇔ (v), for a pro-object: let `G` be pro-represented by a
cofiltered system `(Q_i)` with epimorphic transition morphisms. The following are equivalent:
(i) `G` commutes with finite sums; (ii) `G` commutes with sums of two objects; (iii) the `Q_i` are
connected (and non-initial); (v) `G ≅ (X ↦ F(X)^H)` for a closed subgroup `H` of `π = Aut F`.
Condition (iv) is `ContAction.proEquivalence`-dependent and is not stated here. -/
theorem proRepresentation_tfae (hR : R.IsStrict) : List.TFAE
    [PreservesFiniteCoproducts G, PreservesColimitsOfShape (Discrete WalkingPair) G,
      ∀ i, IsConnected (R.F.obj i),
      ∃ H : Subgroup (Aut F), IsClosed (H : Set (Aut F)) ∧ Nonempty (G ≅ fixedPoints F H)] := by
  tfae_have 1 → 2 := fun _ ↦ inferInstance
  tfae_have 2 → 3 := fun _ ↦ isConnected_of_preservesBinaryCoproducts F R hR
  tfae_have 3 → 4 := fun hc ↦ by
    have hfin := finite_obj_of_isConnected F R hc
    let G' := toFintypeCat G hfin
    let e := toFintypeCatCompIncl G hfin
    have := Functor.IsProRepresentable.preservesFiniteLimits ⟨R⟩
    have : PreservesFiniteLimits (G' ⋙ FintypeCat.incl) := preservesFiniteLimits_of_natIso e.symm
    have : PreservesFiniteLimits G' := preservesFiniteLimits_of_reflects_of_preserves G'
      FintypeCat.incl
    have := preservesBinaryCoproducts_of_isConnected F R hc
    have : PreservesColimitsOfShape (Discrete WalkingPair) (G' ⋙ FintypeCat.incl) :=
      preservesColimitsOfShape_of_natIso e.symm
    have : PreservesColimitsOfShape (Discrete WalkingPair) G' :=
      preservesColimitsOfShape_of_reflects_of_preserves G' FintypeCat.incl
    obtain ⟨H, hH, ⟨e'⟩⟩ := exists_iso_fixedPoints F G'
    exact ⟨H, hH, ⟨e.symm ≪≫ e'⟩⟩
  tfae_have 4 → 1 := fun ⟨H, _, ⟨e⟩⟩ ↦ by
    have : IsInitial ((fixedPoints F H).obj (⊥_ C)) := by
      refine ((Types.initial_iff_empty _).2 ⟨fun x ↦ ?_⟩).some
      exact ((initial_iff_fiber_empty F (⊥_ C)).1 ⟨initialIsInitial⟩).false x.1
    have := preservesInitial_of_iso (fixedPoints F H) (initialIsInitial.uniqueUpToIso this)
    have := preservesColimitsOfShape_pempty_of_preservesInitial (fixedPoints F H)
    have : PreservesFiniteCoproducts (fixedPoints F H) :=
      ⟨fun n ↦ PreservesFiniteCoproducts.of_preserves_binary_and_initial _ (Fin n)⟩
    exact ⟨fun n ↦ preservesColimitsOfShape_of_natIso e.symm⟩
  tfae_finish

include F in
/-- V.5.6, (iv) ⇒ (i): if `G` is pro-represented by a system `(P'_i)` such that the connected
objects of `C` are exactly the objects isomorphic to some `P'_i`, then `G` is isomorphic to the
fibre functor `F` (hence is a fibre functor, and the pro-object is fundamental). -/
theorem nonempty_iso_of_isConnected_iff
    (hR : ∀ X : C, IsConnected X ↔ ∃ i, Nonempty (X ≅ R.F.obj i)) :
    Nonempty (F ⋙ FintypeCat.incl ≅ G) := by
  have hc (i : R.I) : IsConnected (R.F.obj i) := (hR _).2 ⟨i, ⟨Iso.refl _⟩⟩
  have hfin := finite_obj_of_isConnected F R hc
  let G' := toFintypeCat G hfin
  let e := toFintypeCatCompIncl G hfin
  have := Functor.IsProRepresentable.preservesFiniteLimits ⟨R⟩
  have : PreservesFiniteLimits (G' ⋙ FintypeCat.incl) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteLimits G' := preservesFiniteLimits_of_reflects_of_preserves G'
    FintypeCat.incl
  have := preservesBinaryCoproducts_of_isConnected F R hc
  have : PreservesColimitsOfShape (Discrete WalkingPair) (G' ⋙ FintypeCat.incl) :=
    preservesColimitsOfShape_of_natIso e.symm
  have : PreservesColimitsOfShape (Discrete WalkingPair) G' :=
    preservesColimitsOfShape_of_reflects_of_preserves G' FintypeCat.incl
  obtain ⟨f⟩ := nonempty_iso_of_leftExact G' F fun X hX ↦ by
    obtain ⟨x⟩ := (not_initial_iff_fiber_nonempty F X).1 hX
    obtain ⟨Y, i, -, -, hY, -⟩ := fiber_in_connected_component F X x
    obtain ⟨j, ⟨φ⟩⟩ := (hR Y).1 hY
    exact ⟨G.map (φ.inv ≫ i) (R.elem j)⟩
  exact ⟨Functor.isoWhiskerRight f FintypeCat.incl ≪≫ e⟩

/-- V.4 c) and V.5.4 (iii): if `C` is essentially small, the fibre functor is pro-represented by
a normalized system `(P_i)`: its transition morphisms are epimorphisms, and the connected objects
of `C` are exactly the objects isomorphic to some `P_i`. -/
theorem exists_proRepresentation_normalized [EssentiallySmall.{u₂} C] :
    ∃ R : (F ⋙ FintypeCat.incl).ProRepresentation, R.IsStrict ∧
      ∀ X : C, IsConnected X ↔ ∃ i, Nonempty (X ≅ R.F.obj i) := by
  have := hasFiniteLimits (C := C)
  have (X : C) : IsArtinianObject X := isArtinianObject F X
  have := comp_preservesFiniteLimits F FintypeCat.incl
  refine ⟨Functor.minimalElementsProRepresentation _,
    Functor.minimalElementsProRepresentation_isStrict, fun X ↦ ?_⟩
  rw [Functor.exists_iso_minimalElementsProRepresentation_F_obj_iff]
  refine ⟨fun _ ↦ ?_, fun ⟨x, hx⟩ ↦ (isMinimalElement_iff_isConnected F x).1 hx⟩
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected F X
  exact ⟨x, (isMinimalElement_iff_isConnected F x).2 inferInstance⟩

end ProTerms

/-! ### V.5.11: principal homogeneous objects and homomorphisms `π → G` -/

section Torsors

variable (F : C ⥤ FintypeCat.{w}) {G : Type*} [Group G] {X : C}

/-- V.5.11: an object `X` with a right action `α : G → Aut(X)ᵒᵖ` of a group `G` is principal
homogeneous under `G` if `G` acts simply transitively on the fibre `F(X)`. SGA defines this by
`X × G_C ≅ X × X` and `X/G = e`, and notes that it amounts to this condition on the fibre. -/
def IsPrincipalHomogeneous (α : G →* (Aut X)ᵐᵒᵖ) : Prop :=
  ∀ x y : F.obj X, ∃! g : G, F.map (α g).unop.hom x = y

variable {F}

lemma IsPrincipalHomogeneous.bijective {α : G →* (Aut X)ᵐᵒᵖ} (hα : IsPrincipalHomogeneous F α)
    (x : F.obj X) : Function.Bijective fun g : G ↦ F.map (α g).unop.hom x :=
  ⟨fun _ _ h ↦ (hα x _).unique h rfl, fun y ↦ (hα x y).exists⟩

variable [GaloisCategory C] [FiberFunctor F]

/-- V.5.11: if `X` is connected and principal homogeneous under `G`, then `G → Aut(X)ᵒᵖ` is an
isomorphism. -/
theorem bijective_of_isPrincipalHomogeneous [IsConnected X] {α : G →* (Aut X)ᵐᵒᵖ}
    (hα : IsPrincipalHomogeneous F α) : Function.Bijective α := by
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected F X
  refine ⟨fun g g' h ↦ (hα.bijective x).1 (by simp only [h]), fun φ ↦ ?_⟩
  obtain ⟨g, hg⟩ := (hα.bijective x).2 (F.map φ.unop.hom x)
  refine ⟨g, MulOpposite.unop_injective (evaluation_aut_injective_of_isConnected F X x hg)⟩

variable (F) in
/-- V.5.11: a connected object is Galois iff it is principal homogeneous under `Aut(X)ᵒᵖ`. -/
theorem isGalois_iff_isPrincipalHomogeneous [IsConnected X] :
    IsGalois X ↔ IsPrincipalHomogeneous F (MonoidHom.id (Aut X)ᵐᵒᵖ) := by
  refine ⟨fun _ x y ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨φ, hφ⟩ := (evaluation_aut_bijective_of_isGalois F X x).2 y
    refine ⟨MulOpposite.op φ, hφ, fun ψ hψ ↦ MulOpposite.unop_injective ?_⟩
    exact (evaluation_aut_bijective_of_isGalois F X x).1 (hψ.trans hφ.symm)
  · obtain ⟨x⟩ := nonempty_fiber_of_isConnected F X
    have := (isGalois_tfae F X x).out 1 4
    refine this.2 ⟨fun φ ψ hφψ ↦ ?_, fun y ↦ ?_⟩
    · exact MulOpposite.op_injective ((h x _).unique hφψ rfl)
    · obtain ⟨φ, hφ, -⟩ := h x y
      exact ⟨φ.unop, hφ⟩

variable {α : G →* (Aut X)ᵐᵒᵖ} (hα : IsPrincipalHomogeneous F α) (a : F.obj X)

/-- V.5.11: a principal homogeneous `X` under `G` with a point `a ∈ F(X)` defines a
homomorphism `π → G`, `σ ↦ g` where `σ a = a g`. -/
noncomputable def torsorHom : Aut F →* G where
  toFun σ := (Equiv.ofBijective _ (hα.bijective a)).symm (σ • a)
  map_one' := by
    apply (Equiv.ofBijective _ (hα.bijective a)).injective
    rw [Equiv.apply_symm_apply, Equiv.ofBijective_apply, map_one]
    change (1 : Aut F) • a = F.map (𝟙 X) a
    rw [F.map_id, FintypeCat.id_apply, one_smul]
  map_mul' σ τ := by
    let e := Equiv.ofBijective _ (hα.bijective a)
    have h2 : F.map (α (e.symm (τ • a))).unop.hom a = τ • a := e.apply_symm_apply _
    have h1 : F.map (α (e.symm (σ • a))).unop.hom a = σ • a := e.apply_symm_apply _
    apply e.injective
    change e (e.symm ((σ * τ) • a)) =
      F.map (α (e.symm (σ • a) * e.symm (τ • a))).unop.hom a
    rw [e.apply_symm_apply, map_mul]
    change (σ * τ) • a =
      F.map ((α (e.symm (σ • a))).unop.hom ≫ (α (e.symm (τ • a))).unop.hom) a
    rw [F.map_comp, FintypeCat.comp_apply, h1]
    conv_lhs => rw [mul_smul, ← h2, mulAction_naturality]

omit [GaloisCategory C] [FiberFunctor F] in
lemma torsorHom_spec (σ : Aut F) : F.map (α (torsorHom hα a σ)).unop.hom a = σ • a :=
  (Equiv.ofBijective _ (hα.bijective a)).apply_symm_apply _

omit [GaloisCategory C] [FiberFunctor F] in
lemma torsorHom_eq_iff (σ : Aut F) (g : G) :
    torsorHom hα a σ = g ↔ F.map (α g).unop.hom a = σ • a :=
  ⟨fun h ↦ h ▸ torsorHom_spec hα a σ,
    fun h ↦ (hα.bijective a).1 ((torsorHom_spec hα a σ).trans h.symm)⟩

omit [GaloisCategory C] [FiberFunctor F] in
/-- V.5.11: the homomorphism `π → G` defined by a pointed principal homogeneous object is
continuous. -/
lemma continuous_torsorHom [TopologicalSpace G] [DiscreteTopology G] :
    Continuous (torsorHom hα a) := by
  have : Continuous fun σ : Aut F ↦ σ • a := continuous_id.smul continuous_const
  change Continuous fun σ ↦ (Equiv.ofBijective _ (hα.bijective a)).symm (σ • a)
  exact continuous_of_discreteTopology.comp this

open scoped FintypeCatDiscrete in
set_option backward.isDefEq.respectTransparency.types false in
/-- V.5.11: every continuous homomorphism `ρ : π → G` to a finite group comes from a pointed
principal homogeneous object under `G`. -/
theorem exists_torsorHom_eq {G : Type w} [Group G] [Finite G] [TopologicalSpace G]
    [DiscreteTopology G] (ρ : Aut F →* G) (hρ : Continuous ρ) :
    ∃ (X : C) (α : G →* (Aut X)ᵐᵒᵖ) (hα : IsPrincipalHomogeneous F α) (a : F.obj X),
      torsorHom hα a = ρ := by
  let _ : MulAction (Aut F) G := MulAction.compHom G ρ
  let T : Action FintypeCat.{w} (Aut F) := Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of G)
  have hT : T.IsContinuous := by
    rw [isContinuous_iff_isOpen_stabilizer]
    intro (g : G)
    have : (MulAction.stabilizer (Aut F) (show T.V from g) : Set (Aut F)) = ρ ⁻¹' {1} := by
      ext σ
      simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage,
        Set.mem_singleton_iff]
      change ρ σ * g = g ↔ _
      rw [mul_eq_right]
    rw [this]
    exact (isOpen_discrete _).preimage hρ
  let T' : ContAction FintypeCat.{w} (Aut F) := ⟨T, hT⟩
  let X := (functorToContAction F).objPreimage T'
  let ψ : (functorToAction F).obj X ≅ T :=
    (ObjectProperty.ι _).mapIso ((functorToContAction F).objObjPreimageIso T')
  let e : F.obj X ≃ G := (FintypeCat.equivEquivIso.symm ((Action.forget _ _).mapIso ψ))
  have he (σ : Aut F) (x : F.obj X) : e (σ • x) = ρ σ * e x := Action.hom_smul ψ.hom σ x
  have hr (g : G) : ∃ f : X ⟶ X, ∀ x, F.map f x = e.symm (e x * g) := by
    let φ : (functorToAction F).obj X ⟶ (functorToAction F).obj X :=
      { hom := FintypeCat.homMk fun x ↦ e.symm (e x * g)
        comm := fun σ ↦ by
          ext (x : F.obj X)
          change e.symm (e (σ • x) * g) = σ • e.symm (e x * g)
          apply e.injective
          rw [he, e.apply_symm_apply, he, e.apply_symm_apply, mul_assoc] }
    obtain ⟨f, hf⟩ := (functorToAction F).map_surjective φ
    exact ⟨f, fun x ↦ congrArg (fun k ↦ k.hom x) hf⟩
  choose f hf using hr
  have hfiso (g : G) : IsIso (f g) := by
    have : IsIso (F.map (f g)) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      refine ⟨fun x y h ↦ ?_, fun y ↦ ⟨e.symm (e y * g⁻¹), ?_⟩⟩
      · rw [hf, hf] at h
        simpa using h
      · rw [hf]
        simp
    exact isIso_of_reflects_iso _ F
  let β (g : G) : Aut X := asIso (f g)
  have hβ (g : G) (x : F.obj X) : F.map (β g).hom x = e.symm (e x * g) := hf g x
  let α : G →* (Aut X)ᵐᵒᵖ :=
    { toFun := fun g ↦ MulOpposite.op (β g)
      map_one' := by
        apply MulOpposite.unop_injective
        apply Aut.ext
        apply F.map_injective
        ext x
        change F.map (β 1).hom x = F.map (𝟙 X) x
        rw [hβ, F.map_id, FintypeCat.id_apply, mul_one, e.symm_apply_apply]
      map_mul' := fun g h ↦ by
        apply MulOpposite.unop_injective
        apply Aut.ext
        apply F.map_injective
        ext x
        change F.map (β (g * h)).hom x = F.map ((β g).hom ≫ (β h).hom) x
        rw [F.map_comp, FintypeCat.comp_apply, hβ, hβ, hβ, e.apply_symm_apply, mul_assoc] }
  have hα : IsPrincipalHomogeneous F α := fun x y ↦ by
    refine ⟨(e x)⁻¹ * e y, ?_, fun g hg ↦ ?_⟩
    · change F.map (β _).hom x = y
      rw [hβ, mul_inv_cancel_left, e.symm_apply_apply]
    · change F.map (β g).hom x = y at hg
      rw [hβ, e.symm_apply_eq] at hg
      rw [← hg, inv_mul_cancel_left]
  refine ⟨X, α, hα, e.symm 1, MonoidHom.ext fun σ ↦ (torsorHom_eq_iff hα _ σ _).2 ?_⟩
  change F.map (β (ρ σ)).hom (e.symm 1) = σ • e.symm 1
  apply e.injective
  rw [hβ, e.apply_symm_apply, e.apply_symm_apply, he, e.apply_symm_apply, one_mul, mul_one]

end Torsors

/-! ### V.5.5 (iv): the typical case `C = C(π)` -/

section TypicalProTerms

open Opposite ContAction
open scoped FintypeCatDiscrete

variable {π : Type v} [Group π] [TopologicalSpace π] [IsTopologicalGroup π] [CompactSpace π]
  [T2Space π] [TotallyDisconnectedSpace π]

/-- A transitive finite `π`-set is connected in `C(π)`. -/
lemma isConnected_of_isPretransitive_contAction (E : ContAction FintypeCat.{w} π)
    [Nonempty E.obj.V] [MulAction.IsPretransitive π E.obj.V] : IsConnected E := by
  have : Nonempty ((contActionForget π).obj E) := inferInstanceAs (Nonempty E.obj.V)
  have : MulAction.IsPretransitive (Aut (contActionForget.{v, w} π))
      ((contActionForget π).obj E) := ⟨fun x y ↦ by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq π (show E.obj.V from x) y
    exact ⟨toAut (contActionForget π) π g, (toAut_hom_app_apply (contActionForget π) g x).trans hg⟩⟩
  exact isConnected_of_isPretransitive (contActionForget π) E

variable (Q : Pro (ContAction FintypeCat.{w} π))
  (R : ((Pro.coyoneda _).obj (op Q)).ProRepresentation)

/-- The profinite `π`-space corresponding to a pro-object is the limit of the terms of any
pro-representation. -/
noncomputable def proEquivalenceFunctorObjIsoLimitObj :
    (proEquivalence π).functor.obj Q ≅ limitObj R.F :=
  (proEquivalence π).functor.mapIso ((Pro.coyonedaFullyFaithful _).preimageIso
    R.coyonedaIso).unop.symm.symm ≪≫ proEquivalenceFunctorObjLimIso R.F

/-- V.5.5, (iii) ⇔ (iv), typical case `C = C(π)`: let `Q = (Q_i)` be a pro-object of `C(π)`,
normalized (the transition morphisms of the pro-representation `R` are epimorphisms). Then the
`Q_i` are connected iff the profinite `π`-space `X` corresponding to `Q` (V.5.2) is non-empty and
homogeneous, i.e. (as `π` is compact) isomorphic to `π/H` with `H` the stabilizer of a point. -/
theorem isConnected_iff_isPretransitive (hR : R.IsStrict) :
    (∀ i, IsConnected (R.F.obj i)) ↔ Nonempty ((proEquivalence π).functor.obj Q).obj.V ∧
      MulAction.IsPretransitive π ((proEquivalence π).functor.obj Q).obj.V := by
  let e := proEquivalenceFunctorObjIsoLimitObj Q R
  constructor
  · intro hc
    have hn (i : R.I) : Nonempty (R.F.obj i).obj.V := by
      have := hc i
      exact nonempty_fiber_of_isConnected (contActionForget π) (R.F.obj i)
    have ht (i : R.I) : MulAction.IsPretransitive π (R.F.obj i).obj.V := by
      have := hc i
      exact isPretransitive_of_isConnected_contAction _
    have := nonempty_limitObj R.F hn
    have := isPretransitive_limitObj R.F ht
    exact ⟨ContAction.nonempty_of_iso e, ContAction.isPretransitive_of_iso e⟩
  · rintro ⟨hn, ht⟩
    let X := (proEquivalence π).functor.obj Q
    have hQ (q : InvariantQuotient π X) : IsConnected q.obj := by
      have : Nonempty q.obj.obj.V := ⟨q.1.proj (Classical.arbitrary _)⟩
      have : MulAction.IsPretransitive π q.obj.obj.V := ⟨fun a b ↦ by
        obtain ⟨x, rfl⟩ := q.1.proj_surjective a
        obtain ⟨y, rfl⟩ := q.1.proj_surjective b
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq π x y
        exact ⟨g, (DiscreteQuotient.proj_smul q.2 g x).symm.trans (congrArg q.1.proj hg)⟩⟩
      exact isConnected_of_isPretransitive_contAction q.obj
    have := preservesBinaryCoproducts_of_isConnected (contActionForget π)
      (proRepresentation X) hQ
    let i : (Pro.coyoneda _).obj (op Q) ≅ (homFunctor π).obj (op X) :=
      (Pro.coyoneda _).mapIso ((proEquivalence π).unitIso.app Q).op.symm ≪≫
        coyonedaObjProEquivalenceInverseIso X
    have : PreservesColimitsOfShape (Discrete WalkingPair) ((Pro.coyoneda _).obj (op Q)) :=
      preservesColimitsOfShape_of_natIso i.symm
    exact isConnected_of_preservesBinaryCoproducts (contActionForget π) R hR

/-- V.5.5, typical case `C = C(π)` (with `π` in the universe of the finite sets): for a pro-object
`Q = (Q_i)` of `C(π)`, normalized (the transition morphisms of the pro-representation `R` of
`G = Hom(Q, -)` are epimorphisms), the following are equivalent: (i) `G` commutes with finite
sums; (ii) `G` commutes with sums of two objects; (iii) the `Q_i` are connected (and non-initial);
(iv) `Q` is isomorphic to `π/H` for a closed subgroup `H` of `π` (via V.5.2); (v) `G` is
isomorphic to `X ↦ F(X)^H` for a closed subgroup `H` of `π_F ≅ π` (`F` the forgetful functor). -/
theorem proObject_tfae {π : Type w} [Group π] [TopologicalSpace π] [IsTopologicalGroup π]
    [CompactSpace π] [T2Space π] [TotallyDisconnectedSpace π]
    (Q : Pro (ContAction FintypeCat.{w} π))
    (R : ((Pro.coyoneda _).obj (op Q)).ProRepresentation) (hR : R.IsStrict) : List.TFAE
    [PreservesFiniteCoproducts ((Pro.coyoneda _).obj (op Q)),
      PreservesColimitsOfShape (Discrete WalkingPair) ((Pro.coyoneda _).obj (op Q)),
      ∀ i, IsConnected (R.F.obj i),
      ∃ (H : Subgroup π) (_ : IsClosed (H : Set π)),
        Nonempty ((proEquivalence π).functor.obj Q ≅ quotientSpace π H),
      ∃ H : Subgroup (Aut (contActionForget.{w, w} π)),
        IsClosed (H : Set (Aut (contActionForget.{w, w} π))) ∧
        Nonempty ((Pro.coyoneda _).obj (op Q) ≅ fixedPoints (contActionForget π) H)] := by
  have h := proRepresentation_tfae (contActionForget.{w, w} π) R hR
  tfae_have 1 ↔ 2 := h.out 1 2
  tfae_have 2 ↔ 3 := h.out 2 3
  tfae_have 3 ↔ 5 := h.out 3 4
  tfae_have 3 ↔ 4 := (isConnected_iff_isPretransitive Q R hR).trans
    (nonempty_isPretransitive_iff_exists_iso_quotientSpace _)
  tfae_finish

/-- V.5.11 (typical case `C = C(π)`): the fundamental pro-group, `π` acting on itself by
conjugation, is connected (its terms are connected, cf. V.5.5) iff `π` is trivial; unlike a
fundamental pro-object, it is in general not connected. -/
theorem isConnected_conj_iff {π : Type w} [Group π] [TopologicalSpace π] [IsTopologicalGroup π]
    [CompactSpace π] [T2Space π] [TotallyDisconnectedSpace π]
    (R : ((Pro.coyoneda _).obj
      (op ((proEquivalence π).inverse.obj (conj π)))).ProRepresentation) (hR : R.IsStrict) :
    (∀ i, IsConnected (R.F.obj i)) ↔ Subsingleton π := by
  rw [isConnected_iff_isPretransitive _ R hR, ← isPretransitive_conj_iff]
  let e : (proEquivalence π).functor.obj ((proEquivalence π).inverse.obj (conj π)) ≅ conj π :=
    (proEquivalence π).counitIso.app (conj π)
  have : Nonempty (conj π).obj.V := ⟨toConjVia (ContinuousMonoidHom.id π) 1⟩
  refine ⟨fun ⟨_, h⟩ ↦ ContAction.isPretransitive_of_iso e.symm, fun h ↦ ?_⟩
  exact ⟨ContAction.nonempty_of_iso e, ContAction.isPretransitive_of_iso e⟩

end TypicalProTerms

/-! ### V.5.11: the objects `E_C` -/

section ConstantObjects

open scoped FintypeCatDiscrete

/-- A finite set with the trivial action of `π`, as a continuous finite `π`-set. -/
@[simps obj_obj map]
def trivialContAction (π : Type v) [Group π] [TopologicalSpace π] [IsTopologicalGroup π] :
    FintypeCat.{w} ⥤ ContAction FintypeCat.{w} π where
  obj E := ⟨Action.trivial π E, by
    rw [isContinuous_iff_isOpen_stabilizer]
    intro x
    convert isOpen_univ
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_univ, iff_true]
    rfl⟩
  map f := ObjectProperty.homMk { hom := f }

/-- `trivialContAction π` composed with the forgetful functor is the identity. -/
def trivialContActionCompForgetIso (π : Type v) [Group π] [TopologicalSpace π]
    [IsTopologicalGroup π] :
    trivialContAction.{v, w} π ⋙ ObjectProperty.ι _ ⋙ Action.forget _ _ ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

instance (π : Type v) [Group π] [TopologicalSpace π] [IsTopologicalGroup π] :
    PreservesFiniteLimits (trivialContAction.{v, w} π) := by
  have := preservesFiniteLimits_of_natIso (trivialContActionCompForgetIso.{v, w} π).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (ObjectProperty.ι _ ⋙ Action.forget _ _)

instance (π : Type v) [Group π] [TopologicalSpace π] [IsTopologicalGroup π] :
    PreservesFiniteColimits (trivialContAction.{v, w} π) := by
  have := preservesFiniteColimits_of_natIso (trivialContActionCompForgetIso.{v, w} π).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ (ObjectProperty.ι _ ⋙ Action.forget _ _)

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- V.5.11: the object `E_C` of `C` defined by a finite set `E`, corresponding (V.5.8) to the
constant local system with value `E`, i.e. to `E` with the trivial action of `π`. -/
noncomputable def constObj : FintypeCat.{w} ⥤ C :=
  trivialContAction (Aut F) ⋙ (equivalenceContAction F).inverse

/-- V.5.11: the functor `E ↦ E_C` is exact. -/
instance : PreservesFiniteLimits (constObj F) := by
  unfold constObj
  exact comp_preservesFiniteLimits _ _

/-- V.5.11: the functor `E ↦ E_C` is exact. -/
instance : PreservesFiniteColimits (constObj F) := by
  unfold constObj
  exact comp_preservesFiniteColimits _ _

/-- V.5.11: the fibre of `E_C` is `E`. -/
noncomputable def constObjCompIso : constObj F ⋙ F ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft (trivialContAction (Aut F))
    (Functor.isoWhiskerRight (equivalenceContAction F).counitIso
      (ObjectProperty.ι _ ⋙ Action.forget _ _)) ≪≫ trivialContActionCompForgetIso _

/-- V.5.11: `E_C` is a sum of copies of the final object `e_C`: `π` acts trivially on its fibre. -/
theorem isCompletelyDecomposed_constObj (E : FintypeCat.{w}) :
    IsCompletelyDecomposed ((constObj F).obj E) := by
  rw [isCompletelyDecomposed_iff F]
  intro σ y
  let c := (equivalenceContAction F).counitIso.app ((trivialContAction (Aut F)).obj E)
  have h := Action.hom_smul ((ObjectProperty.ι _).map c.hom) σ y
  apply ((ConcreteCategory.isIso_iff_bijective
    ((ObjectProperty.ι _ ⋙ Action.forget _ _).map c.hom)).1 inferInstance).1
  exact h.trans rfl

end ConstantObjects

end SGA.SGA1.ExposeV
