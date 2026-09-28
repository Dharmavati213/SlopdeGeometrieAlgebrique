/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Category.FinTopCat
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import SGA.Foundations.Pro.Representable

/-!
# Pro-objects of finite continuous `π`-sets

Let `π` be a profinite group. We show that the category of pro-objects of the category
`ContAction FintypeCat π` of finite sets with a continuous action of `π` is equivalent to the
category `ContAction Profinite π` of profinite spaces with a continuous action of `π`
(`ContAction.proEquivalence`).

The functor `ContAction Profinite π ⥤ Pro (ContAction FintypeCat π)` sends `X` to the
pro-object representing `E ↦ Hom(X, E)`: this functor is pro-represented by the cofiltered
system of the `π`-invariant discrete quotients of `X`. The key point is that these are cofinal
among all discrete quotients (`DiscreteQuotient.exists_isInvariant_le`), because the open normal
subgroups of `π` form a basis of neighbourhoods of `1`.

## References

* [A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1)][sga1], Exposé V,
  Proposition 5.2
-/

universe w v

open CategoryTheory Limits Opposite Topology

/-! ### Invariant discrete quotients -/

namespace DiscreteQuotient

variable (π : Type*) [Group π] {X : Type*} [TopologicalSpace X] [MulAction π X]

/-- A discrete quotient of a space with an action of `π` is invariant if the action respects
its equivalence relation. -/
def IsInvariant (Q : DiscreteQuotient X) : Prop :=
  ∀ (g : π) ⦃x y : X⦄, Q.toSetoid x y → Q.toSetoid (g • x) (g • y)

lemma isInvariant_top : (⊤ : DiscreteQuotient X).IsInvariant π :=
  fun _ _ _ _ ↦ trivial

variable {π}

lemma IsInvariant.inf {Q Q' : DiscreteQuotient X} (hQ : Q.IsInvariant π) (hQ' : Q'.IsInvariant π) :
    (Q ⊓ Q').IsInvariant π :=
  fun g _ _ h ↦ ⟨hQ g h.1, hQ' g h.2⟩

/-- The action of `π` on an invariant discrete quotient. -/
@[reducible]
def mulActionOfIsInvariant {Q : DiscreteQuotient X} (hQ : Q.IsInvariant π) : MulAction π Q where
  smul g := Quotient.map' (g • ·) fun _ _ h ↦ hQ g h
  one_smul := Quotient.ind fun x ↦ congrArg Q.proj (one_smul π x)
  mul_smul g g' := Quotient.ind fun x ↦ congrArg Q.proj (mul_smul g g' x)

lemma proj_smul {Q : DiscreteQuotient X} (hQ : Q.IsInvariant π) (g : π) (x : X) :
    letI := mulActionOfIsInvariant hQ
    Q.proj (g • x) = g • Q.proj x :=
  rfl

/-- The key step of SGA 1 V.5.2: if a profinite group `π` acts continuously on a compact space
`X`, every discrete quotient of `X` is refined by a `π`-invariant discrete quotient. -/
theorem exists_isInvariant_le [TopologicalSpace π] [IsTopologicalGroup π] [CompactSpace π]
    [TotallyDisconnectedSpace π] [CompactSpace X] [ContinuousSMul π X] (Q : DiscreteQuotient X) :
    ∃ Q' : DiscreteQuotient X, Q'.IsInvariant π ∧ Q' ≤ Q := by
  let f : X → Q := Q.proj
  have hf : Continuous f := Q.proj_continuous
  -- a neighbourhood of `1` whose elements preserve the fibres of `f`
  have hW : IsOpen {p : π × X | f (p.1 • p.2) = f p.2} :=
    (isOpen_discrete {p : Q × Q | p.1 = p.2}).preimage
      ((hf.comp continuous_smul).prodMk (hf.comp continuous_snd))
  obtain ⟨u, v, hu, -, hu1, hv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := 1))
    isCompact_univ hW (fun p hp ↦ by
      obtain ⟨h1, -⟩ := hp
      simp only [Set.mem_singleton_iff] at h1
      simp [h1])
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hu (hu1 rfl)
  have hNf (n : π) (hn : n ∈ N) (x : X) : f (n • x) = f x :=
    huv (Set.mk_mem_prod (hN hn) (hv (Set.mem_univ x)))
  have hNg (g n : π) (hn : n ∈ N) (x : X) : f (g • n • x) = f (g • x) := by
    have : g • n • x = (g * n * g⁻¹) • g • x := by simp [mul_smul]
    rw [this, hNf _ (N.isNormal'.conj_mem n hn g)]
  have : Finite (π ⧸ N.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
  let r : Setoid X :=
    { r := fun x y ↦ ∀ g : π, f (g • x) = f (g • y)
      iseqv := ⟨fun _ _ ↦ rfl, fun h g ↦ (h g).symm, fun h h' g ↦ (h g).trans (h' g)⟩ }
  refine ⟨⟨r, fun x ↦ ?_⟩, fun g x y h k ↦ ?_, fun x y h ↦ ?_⟩
  · have : {y | ∀ g : π, f (g • x) = f (g • y)} =
        ⋂ c : π ⧸ N.toSubgroup, {y | f (c.out • x) = f (c.out • y)} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      refine ⟨fun h c ↦ h c.out, fun h g ↦ ?_⟩
      obtain ⟨⟨n, hn⟩, hgn⟩ := QuotientGroup.mk_out_eq_mul N.toSubgroup g
      have := h (QuotientGroup.mk g)
      rw [hgn, mul_smul, mul_smul, hNg _ _ hn, hNg _ _ hn] at this
      exact this
    change IsOpen {y | ∀ g : π, f (g • x) = f (g • y)}
    rw [this]
    exact isOpen_iInter_of_finite fun c ↦ (isOpen_discrete {p : Q × Q | p.1 = p.2}).preimage
      (continuous_const.prodMk (hf.comp (continuous_const_smul _)))
  · simpa only [smul_smul] using h (k * g)
  · have := (h : ∀ g : π, f (g • x) = f (g • y)) 1
    simp only [one_smul] at this
    exact Quotient.exact this

variable [TopologicalSpace π] [IsTopologicalGroup π] [CompactSpace π]
  [TotallyDisconnectedSpace π] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [ContinuousSMul π X]

variable (π) in
/-- The points of a profinite space with a continuous action of a profinite group `π` are
separated by the invariant discrete quotients. -/
theorem eq_of_forall_isInvariant_proj_eq {x y : X}
    (h : ∀ Q : DiscreteQuotient X, Q.IsInvariant π → Q.proj x = Q.proj y) : x = y := by
  refine eq_of_forall_proj_eq fun Q ↦ ?_
  obtain ⟨Q', hQ', hle⟩ := exists_isInvariant_le (π := π) Q
  rw [← ofLE_proj hle, ← ofLE_proj hle, h Q' hQ']

end DiscreteQuotient

/-! ### Cofiltered systems of finite sets -/

namespace CategoryTheory.Functor

variable {J : Type*} [Category* J] [IsCofilteredOrEmpty J] (F : J ⥤ Type*)
  [∀ j, Finite (F.obj j)]

/-- In a cofiltered system of finite sets, the eventual range at `i` is the range of some
transition map. -/
theorem exists_eventualRange_eq_range (i : J) :
    ∃ (j : J) (t : j ⟶ i), F.eventualRange i = Set.range (F.map t) :=
  (F.isMittagLeffler_iff_eventualRange.1
    (F.isMittagLeffler_of_exists_finite_range fun j ↦ ⟨j, 𝟙 j, Set.toFinite _⟩)) i

/-- In a cofiltered system of finite sets, every point of the eventual range at `i` is the value
at `i` of a section. -/
theorem exists_mem_sections_of_mem_eventualRange {i : J} {y : F.obj i}
    (hy : y ∈ F.eventualRange i) : ∃ s ∈ F.sections, s i = y := by
  have hML : F.IsMittagLeffler :=
    F.isMittagLeffler_of_exists_finite_range fun j ↦ ⟨j, 𝟙 j, Set.toFinite _⟩
  have (k : J) : Nonempty (F.toEventualRanges.obj k) := by
    obtain ⟨m, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i k
    obtain ⟨z, hz, -⟩ := hML.subset_image_eventualRange F a hy
    exact ⟨⟨_, F.eventualRange_mapsTo b hz⟩⟩
  obtain ⟨s, hs⟩ := F.toEventualRanges.eval_section_surjective_of_surjective
    (F.surjective_toEventualRanges hML) i ⟨y, hy⟩
  exact ⟨(F.toEventualRangesSectionsEquiv s).1, (F.toEventualRangesSectionsEquiv s).2,
    congrArg Subtype.val hs⟩

end CategoryTheory.Functor

/-! ### Quotients of profinite groups by closed subgroups -/

namespace QuotientGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- In a profinite group, an element outside a closed subgroup `H` stays outside `H N` for some
open normal subgroup `N`. -/
theorem exists_openNormalSubgroup_notMem_sup (H : Subgroup G) [IsClosed (H : Set G)] {g : G}
    (hg : g ∉ H) : ∃ N : OpenNormalSubgroup G, g ∉ H ⊔ N.toSubgroup := by
  have hU : IsOpen ((fun x ↦ g * x⁻¹) ⁻¹' (H : Set G)ᶜ) :=
    (IsClosed.isOpen_compl (s := (H : Set G))).preimage (continuous_const.mul continuous_inv)
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU
    (by simpa using hg)
  refine ⟨N, fun hmem ↦ ?_⟩
  rw [← SetLike.mem_coe, Subgroup.mul_normal H N.toSubgroup, Set.mem_mul] at hmem
  obtain ⟨h, hh, n, hn, rfl⟩ := hmem
  exact hN hn (by simpa using hh)

/-- The quotient of a profinite group by a closed subgroup is totally separated. -/
instance (H : Subgroup G) [IsClosed (H : Set G)] : TotallySeparatedSpace (G ⧸ H) := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y hxy
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have hab : a⁻¹ * b ∉ H := fun h ↦ hxy (QuotientGroup.eq.2 h)
  obtain ⟨N, hN⟩ := exists_openNormalSubgroup_notMem_sup H hab
  let K := H ⊔ N.toSubgroup
  have hK : IsClopen ((fun g ↦ a⁻¹ * g) ⁻¹' (K : Set G)) := by
    have hKo : IsOpen (K : Set G) := Subgroup.isOpen_mono le_sup_right N.isOpen'
    exact ⟨(Subgroup.isClosed_of_isOpen K hKo).preimage (continuous_const_mul _),
      hKo.preimage (continuous_const_mul _)⟩
  let V : Set (G ⧸ H) := {q | ∃ g : G, (g : G ⧸ H) = q ∧ a⁻¹ * g ∈ K}
  have hV : (QuotientGroup.mk ⁻¹' V : Set G) = (fun g ↦ a⁻¹ * g) ⁻¹' (K : Set G) := by
    ext g
    refine ⟨fun ⟨g', hg', hK'⟩ ↦ ?_, fun h ↦ ⟨g, rfl, h⟩⟩
    have : g'⁻¹ * g ∈ H := QuotientGroup.eq.1 hg'
    change a⁻¹ * g ∈ K
    have := K.mul_mem hK' (le_sup_left (a := H) this)
    simpa [mul_assoc] using this
  refine ⟨V, ?_, ⟨a, rfl, by simp⟩, fun ⟨g, hg, hgK⟩ ↦ ?_⟩
  · rw [← (QuotientGroup.isQuotientMap_mk H).isClopen_preimage, hV]
    exact hK
  · have hgb : g⁻¹ * b ∈ H := QuotientGroup.eq.1 hg
    exact hN (by simpa [mul_assoc] using K.mul_mem hgK (le_sup_left (a := H) hgb))

end QuotientGroup

/-! ### The categories `C(π)` and `C'(π)` -/

namespace ContAction

open scoped FintypeCatDiscrete

variable {π : Type v} [Group π] [TopologicalSpace π]

section Profinite

instance (X : ContAction Profinite.{w} π) : MulAction π X.obj.V :=
  Action.instMulAction X.obj

lemma smul_def (X : ContAction Profinite.{w} π) (g : π) (x : X.obj.V) :
    g • x = ConcreteCategory.hom (X.obj.ρ g) x :=
  rfl

instance (X : ContAction Profinite.{w} π) : ContinuousSMul π X.obj.V :=
  X.property

lemma hom_smul {X Y : ContAction Profinite.{w} π} (f : X ⟶ Y) (g : π) (x : X.obj.V) :
    f.hom.hom (g • x) = g • f.hom.hom x :=
  ConcreteCategory.congr_hom (f.hom.comm g) x

lemma comp_hom_apply {X Y Z : ContAction Profinite.{w} π} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X.obj.V) : (f ≫ g).hom.hom x = g.hom.hom (f.hom.hom x) :=
  rfl

/-- An isomorphism of profinite `π`-spaces is a homeomorphism. -/
@[simps]
def homeoOfIso {X Y : ContAction Profinite.{w} π} (i : X ≅ Y) : X.obj.V ≃ₜ Y.obj.V where
  toFun := i.hom.hom.hom
  invFun := i.inv.hom.hom
  left_inv x := congrArg (fun φ : X ⟶ X ↦ φ.hom.hom x) i.hom_inv_id
  right_inv y := congrArg (fun φ : Y ⟶ Y ↦ φ.hom.hom y) i.inv_hom_id
  continuous_toFun := (ConcreteCategory.hom i.hom.hom.hom).continuous
  continuous_invFun := (ConcreteCategory.hom i.inv.hom.hom).continuous

lemma hom_ext_apply {X Y : ContAction Profinite.{w} π} {f g : X ⟶ Y}
    (h : ∀ x, f.hom.hom x = g.hom.hom x) : f = g := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  exact ConcreteCategory.hom_ext _ _ h

variable (π) in
/-- A profinite space with a continuous action of `π`, as an object of
`ContAction Profinite π`. -/
@[simps obj_V]
def ofProfinite (X : Profinite.{w}) [MulAction π X] [ContinuousSMul π X] :
    ContAction Profinite.{w} π where
  obj :=
    { V := X
      ρ :=
        { toFun g := CompHausLike.ofHom _ ⟨(g • ·), continuous_const_smul g⟩
          map_one' := ConcreteCategory.hom_ext _ _ fun x ↦ one_smul π x
          map_mul' g g' := ConcreteCategory.hom_ext _ _ fun x ↦ mul_smul g g' x } }
  property := by
    change ContinuousSMul π X
    infer_instance

lemma ofProfinite_smul (X : Profinite.{w}) [MulAction π X] [ContinuousSMul π X] (g : π) (x : X) :
    g • (show (ofProfinite π X).obj.V from x) = g • x :=
  rfl

end Profinite

section Finite

instance (E : FintypeCat.{w}) : DiscreteTopology (FintypeCat.toProfinite.obj E) :=
  FintypeCat.discreteTopology E

/-- A finite `π`-set is continuous iff the stabilizers of its points are open. -/
lemma isContinuous_iff_isOpen_stabilizer [IsTopologicalGroup π] (E : Action FintypeCat.{w} π) :
    E.IsContinuous ↔ ∀ x : E.V, IsOpen (MulAction.stabilizer π x : Set π) :=
  continuousSMul_iff_stabilizer_isOpen (M := π) (X := E.V)

instance (E : ContAction FintypeCat.{w} π) : ContinuousSMul π E.obj.V :=
  E.property

lemma hom_smul_fintype {E E' : ContAction FintypeCat.{w} π} (f : E ⟶ E') (g : π) (x : E.obj.V) :
    f.hom.hom (g • x) = g • f.hom.hom x :=
  ConcreteCategory.congr_hom (f.hom.comm g) x

variable (π) in
/-- The inclusion of finite continuous `π`-sets into profinite `π`-spaces. -/
noncomputable def finiteToProfinite : ContAction FintypeCat.{w} π ⥤ ContAction Profinite.{w} π :=
  FintypeCat.toProfinite.mapContAction π fun E ↦ by
    change ContinuousSMul π E.obj.V
    infer_instance

end Finite

instance (E : ContAction FintypeCat.{w} π) : DiscreteTopology ((finiteToProfinite π).obj E).obj.V :=
  FintypeCat.discreteTopology E.obj.V

instance (E : ContAction FintypeCat.{w} π) : Finite ((finiteToProfinite π).obj E).obj.V :=
  inferInstanceAs (Finite E.obj.V)

variable (π) in
/-- The finite continuous `π`-sets form a full subcategory of the profinite `π`-spaces. -/
noncomputable def finiteToProfiniteFullyFaithful : (finiteToProfinite.{w} π).FullyFaithful where
  preimage {E E'} f := ObjectProperty.homMk
    { hom := FintypeCat.homMk fun x ↦ f.hom.hom x
      comm := fun g ↦ by
        ext x
        exact hom_smul f g x }
  map_preimage f := hom_ext_apply fun _ ↦ rfl
  preimage_map f := rfl

instance : (finiteToProfinite.{w} π).Full := (finiteToProfiniteFullyFaithful π).full
instance : (finiteToProfinite.{w} π).Faithful := (finiteToProfiniteFullyFaithful π).faithful

/-! ### The functor pro-represented by a profinite `π`-space -/

variable (π) in
/-- The functor `C'(π)ᵒᵖ ⥤ (C(π) ⥤ Type w)` sending a profinite `π`-space `X` to the functor
`E ↦ Hom(X, E)` on finite continuous `π`-sets. -/
noncomputable def homFunctor :
    (ContAction Profinite.{w} π)ᵒᵖ ⥤ ContAction FintypeCat.{w} π ⥤ Type w :=
  coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (finiteToProfinite π)

section Quotients

variable [IsTopologicalGroup π] (X : ContAction Profinite.{w} π)

variable (π) in
/-- The `π`-invariant discrete quotients of a profinite `π`-space, ordered by refinement. -/
abbrev InvariantQuotient : Type w :=
  {Q : DiscreteQuotient X.obj.V // Q.IsInvariant π}

instance : SemilatticeInf (InvariantQuotient π X) :=
  Subtype.semilatticeInf fun _ _ h h' ↦ h.inf h'

instance : Nonempty (InvariantQuotient π X) :=
  ⟨⟨⊤, DiscreteQuotient.isInvariant_top π⟩⟩

variable {X}

instance (Q : InvariantQuotient π X) : MulAction π Q.1 :=
  DiscreteQuotient.mulActionOfIsInvariant Q.2

noncomputable instance (Q : InvariantQuotient π X) : Fintype Q.1 :=
  Fintype.ofFinite _

/-- An invariant discrete quotient of `X`, as a finite continuous `π`-set. -/
noncomputable def InvariantQuotient.obj (Q : InvariantQuotient π X) :
    ContAction FintypeCat.{w} π where
  obj := Action.FintypeCat.ofMulAction π (FintypeCat.of Q.1)
  property := by
    rw [isContinuous_iff_isOpen_stabilizer]
    intro (q : Q.1)
    obtain ⟨x, rfl⟩ := Q.1.proj_surjective q
    have h : IsOpen ((fun g : π ↦ g • x) ⁻¹' (Q.1.proj ⁻¹' {Q.1.proj x})) :=
      (Q.1.isOpen_preimage _).preimage (continuous_id.smul continuous_const)
    convert h using 1
    ext g
    rfl

/-- The transition morphism between two invariant discrete quotients. -/
noncomputable def InvariantQuotient.map {Q Q' : InvariantQuotient π X} (h : Q ≤ Q') :
    Q.obj ⟶ Q'.obj :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (DiscreteQuotient.ofLE h)
      comm := fun g ↦ by
        ext (q : Q.1)
        obtain ⟨x, rfl⟩ := Q.1.proj_surjective q
        rfl }

lemma InvariantQuotient.map_apply {Q Q' : InvariantQuotient π X} (h : Q ≤ Q') (x : X.obj.V) :
    (InvariantQuotient.map h).hom.hom (Q.1.proj x) = Q'.1.proj x :=
  rfl

variable (X) in
/-- The cofiltered system of invariant discrete quotients of `X`, as finite `π`-sets. -/
@[simps obj]
noncomputable def quotientDiagram : InvariantQuotient π X ⥤ ContAction FintypeCat.{w} π where
  obj Q := Q.obj
  map f := InvariantQuotient.map f.le
  map_id Q := by
    ext (q : Q.1)
    obtain ⟨x, rfl⟩ := Q.1.proj_surjective q
    rfl
  map_comp f g := by
    ext (q : _)
    obtain ⟨x, rfl⟩ := DiscreteQuotient.proj_surjective _ q
    rfl

/-- The projection of `X` onto an invariant discrete quotient. -/
noncomputable def InvariantQuotient.proj (Q : InvariantQuotient π X) :
    X ⟶ (finiteToProfinite π).obj Q.obj :=
  ObjectProperty.homMk
    { hom := CompHausLike.ofHom _
        ⟨Q.1.proj, IsLocallyConstant.continuous (by exact Q.1.proj_isLocallyConstant)⟩
      comm := fun _ ↦ rfl }

lemma InvariantQuotient.proj_apply (Q : InvariantQuotient π X) (x : X.obj.V) :
    Q.proj.hom.hom x = Q.1.proj x :=
  rfl

lemma InvariantQuotient.proj_map {Q Q' : InvariantQuotient π X} (h : Q ≤ Q') :
    Q.proj ≫ (finiteToProfinite π).map (InvariantQuotient.map h) = Q'.proj :=
  rfl

variable (X) in
/-- The cocone exhibiting the functor `Hom(X, -)` as the colimit of the functors `Hom(X/Q, -)`,
for `Q` running over the invariant discrete quotients of `X`. -/
@[simps]
noncomputable def quotientCocone : Cocone ((quotientDiagram X).op ⋙ coyoneda) where
  pt := (homFunctor π).obj (op X)
  ι :=
    { app Q :=
        { app E := ↾fun (a : Q.unop.obj ⟶ E) ↦ Q.unop.proj ≫ (finiteToProfinite π).map a
          naturality E E' f := by
            ext (a : Q.unop.obj ⟶ E)
            change Q.unop.proj ≫ (finiteToProfinite π).map (a ≫ f) =
              (Q.unop.proj ≫ (finiteToProfinite π).map a) ≫ (finiteToProfinite π).map f
            rw [Functor.map_comp, Category.assoc] }
      naturality Q Q' g := by
        ext E (a : Q.unop.obj ⟶ E)
        change Q'.unop.proj ≫ (finiteToProfinite π).map (InvariantQuotient.map g.unop.le ≫ a) =
          Q.unop.proj ≫ (finiteToProfinite π).map a
        rw [Functor.map_comp, ← Category.assoc, InvariantQuotient.proj_map] }

/-- The invariant discrete quotient of `X` defined by the fibres of a morphism to a finite
continuous `π`-set. -/
noncomputable def fiberQuotient {E : ContAction FintypeCat.{w} π}
    (f : X ⟶ (finiteToProfinite π).obj E) : InvariantQuotient π X :=
  ⟨{ toSetoid := Setoid.ker f.hom.hom
     isOpen_setOfPred_rel x := by
      have : IsOpen (f.hom.hom ⁻¹' {f.hom.hom x}) :=
        ((ConcreteCategory.hom f.hom.hom).continuous.isOpen_preimage _ (by exact isOpen_discrete _))
      convert this using 1
      ext y
      exact eq_comm },
    fun g x y (h : f.hom.hom x = f.hom.hom y) ↦ by
      change f.hom.hom (g • x) = f.hom.hom (g • y)
      rw [hom_smul, hom_smul, h]⟩

/-- A morphism to a finite continuous `π`-set factors through the quotient by its fibres. -/
noncomputable def fiberQuotientLift {E : ContAction FintypeCat.{w} π}
    (f : X ⟶ (finiteToProfinite π).obj E) : (fiberQuotient f).obj ⟶ E :=
  ObjectProperty.homMk
    { hom := FintypeCat.homMk (Quotient.lift f.hom.hom fun _ _ h ↦ h)
      comm := fun g ↦ by
        ext (q : (fiberQuotient f).1)
        obtain ⟨x, rfl⟩ := (fiberQuotient f).1.proj_surjective q
        exact hom_smul f g x }

lemma fiberQuotient_proj_lift {E : ContAction FintypeCat.{w} π}
    (f : X ⟶ (finiteToProfinite π).obj E) :
    (fiberQuotient f).proj ≫ (finiteToProfinite π).map (fiberQuotientLift f) = f :=
  rfl

variable (X) in
/-- The functor `Hom(X, -)` is the colimit of the functors `Hom(X/Q, -)`. -/
noncomputable def isColimitQuotientCocone : IsColimit (quotientCocone X) :=
  evaluationJointlyReflectsColimits _ fun E ↦ Types.FilteredColimit.isColimitOf _ _
    (fun (f : X ⟶ (finiteToProfinite π).obj E) ↦
      ⟨op (fiberQuotient f), fiberQuotientLift f, (fiberQuotient_proj_lift f).symm⟩)
    (fun Q Q' (a : Q.unop.obj ⟶ E) (a' : Q'.unop.obj ⟶ E) h ↦ by
      refine ⟨op (Q.unop ⊓ Q'.unop), (homOfLE inf_le_left).op, (homOfLE inf_le_right).op, ?_⟩
      change InvariantQuotient.map inf_le_left ≫ a = InvariantQuotient.map inf_le_right ≫ a'
      ext (q : (Q.unop ⊓ Q'.unop).1)
      obtain ⟨x, rfl⟩ := DiscreteQuotient.proj_surjective _ q
      exact congrArg (fun φ : X ⟶ (finiteToProfinite π).obj E ↦ φ.hom.hom x) h)

variable (X) in
/-- The functor `Hom(X, -)` on finite continuous `π`-sets is pro-represented by the invariant
discrete quotients of `X`. -/
noncomputable def proRepresentation : ((homFunctor π).obj (op X)).ProRepresentation where
  I := InvariantQuotient π X
  F := quotientDiagram X
  ι := (quotientCocone X).ι
  isColimit := isColimitQuotientCocone X

end Quotients

/-! ### `Hom(X, -)` determines `X` -/

section FullyFaithful

variable [IsTopologicalGroup π] [CompactSpace π] [TotallyDisconnectedSpace π]

variable (Y : ContAction Profinite.{w} π)

variable (π) in
/-- The inclusion of the invariant discrete quotients into all discrete quotients. -/
def InvariantQuotient.incl : InvariantQuotient π Y ⥤ DiscreteQuotient Y.obj.V :=
  (Subtype.mono_coe _).functor

instance : (InvariantQuotient.incl π Y).Initial :=
  Functor.initial_of_exists_of_isCofiltered _
    (fun Q ↦ by
      obtain ⟨Q', hQ', hle⟩ := DiscreteQuotient.exists_isInvariant_le (π := π) Q
      exact ⟨⟨Q', hQ'⟩, ⟨homOfLE hle⟩⟩)
    (fun _ _ ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)

/-- A profinite `π`-space is the limit of its invariant discrete quotients. -/
noncomputable def isLimitInvariantQuotient :
    IsLimit (Y.obj.V.asLimitCone.whisker (InvariantQuotient.incl π Y)) :=
  (Functor.Initial.isLimitWhiskerEquiv _ _).symm Y.obj.V.asLimit

variable {Y}

lemma eq_of_forall_proj_eq {x y : Y.obj.V}
    (h : ∀ Q : InvariantQuotient π Y, Q.1.proj x = Q.1.proj y) : x = y :=
  DiscreteQuotient.eq_of_forall_isInvariant_proj_eq π fun Q hQ ↦ h ⟨Q, hQ⟩

lemma hom_ext_of_forall_proj {X : ContAction Profinite.{w} π} {f g : X ⟶ Y}
    (h : ∀ Q : InvariantQuotient π Y, f ≫ Q.proj = g ≫ Q.proj) : f = g := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  refine ConcreteCategory.hom_ext _ _ fun x ↦ eq_of_forall_proj_eq fun Q ↦ ?_
  exact congrArg (fun φ : X ⟶ (finiteToProfinite π).obj Q.obj ↦ φ.hom.hom x) (h Q)

omit [CompactSpace π] [TotallyDisconnectedSpace π] in
lemma InvariantQuotient.proj_hom_ext {X : ContAction Profinite.{w} π}
    {Q : InvariantQuotient π Y} {f g : X ⟶ (finiteToProfinite π).obj Q.obj}
    (h : ∀ x, f.hom.hom x = g.hom.hom x) : f = g := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  exact ConcreteCategory.hom_ext _ _ h

variable (π) in
instance : (homFunctor.{w} π).Faithful where
  map_injective {X Y} f g h := by
    apply Quiver.Hom.unop_inj
    refine hom_ext_of_forall_proj fun Q ↦ ?_
    exact congrArg (fun φ : (homFunctor π).obj X ⟶ (homFunctor π).obj Y ↦ φ.app Q.obj Q.proj) h

variable (π) in
instance : (homFunctor.{w} π).Full where
  map_surjective {X Y} η := by
    let X' := X.unop
    let c : Cone (InvariantQuotient.incl π X' ⋙ X'.obj.V.diagram) :=
      { pt := Y.unop.obj.V
        π :=
          { app Q := (η.app Q.obj Q.proj).hom.hom
            naturality Q Q' h := by
              have := ConcreteCategory.congr_hom (η.naturality (InvariantQuotient.map h.le))
                Q.proj
              change η.app Q'.obj (Q.proj ≫ (finiteToProfinite π).map (InvariantQuotient.map h.le))
                = η.app Q.obj Q.proj ≫ (finiteToProfinite π).map (InvariantQuotient.map h.le)
                at this
              rw [InvariantQuotient.proj_map] at this
              rw [this]
              exact Category.id_comp _ } }
    let f₀ : Y.unop.obj.V ⟶ X'.obj.V := (isLimitInvariantQuotient X').lift c
    have hf₀ (Q : InvariantQuotient π X') (y : Y.unop.obj.V) :
        Q.1.proj (f₀ y) = (η.app Q.obj Q.proj).hom.hom y :=
      ConcreteCategory.congr_hom ((isLimitInvariantQuotient X').fac c Q) y
    have heq (g : π) (y : Y.unop.obj.V) : f₀ (g • y) = g • f₀ y :=
      eq_of_forall_proj_eq fun Q ↦ by
        let φ : Y.unop ⟶ (finiteToProfinite π).obj Q.obj := η.app Q.obj Q.proj
        have h1 : Q.1.proj (f₀ (g • y)) = φ.hom.hom (g • y) := hf₀ Q _
        have h2 : Q.1.proj (f₀ y) = φ.hom.hom y := hf₀ Q _
        rw [h1, hom_smul, ← h2]
        rfl
    let f : Y.unop ⟶ X' := ObjectProperty.homMk
      { hom := f₀
        comm := fun g ↦ ConcreteCategory.hom_ext _ _ (heq g) }
    have hfQ (Q : InvariantQuotient π X') : f ≫ Q.proj = η.app Q.obj Q.proj :=
      InvariantQuotient.proj_hom_ext (hf₀ Q)
    refine ⟨f.op, ?_⟩
    ext E (u : X' ⟶ (finiteToProfinite π).obj E)
    change f ≫ u = η.app E u
    rw [← fiberQuotient_proj_lift u, ← Category.assoc, hfQ]
    exact (ConcreteCategory.congr_hom (η.naturality (fiberQuotientLift u))
      (fiberQuotient u).proj).symm

end FullyFaithful

/-! ### Cofiltered limits of finite continuous `π`-sets -/

section Limits

variable {I : Type w} [SmallCategory I] (D : I ⥤ ContAction FintypeCat.{w} π)

/-- The underlying diagram of profinite spaces. -/
noncomputable abbrev profiniteDiagram : I ⥤ Profinite.{w} :=
  D ⋙ finiteToProfinite π ⋙ ObjectProperty.ι _ ⋙ Action.forget _ _

/-- The limit of the underlying profinite spaces of `D`. -/
noncomputable abbrev LimitPt : Profinite.{w} :=
  (Profinite.limitCone.{w, w} (profiniteDiagram D)).pt

noncomputable instance : MulAction π (LimitPt D) where
  smul g x := ⟨fun i ↦ g • (show ((finiteToProfinite π).obj (D.obj i)).obj.V from x.1 i),
    fun {i j} f ↦ by
      change ((finiteToProfinite π).map (D.map f)).hom.hom
          (g • (show ((finiteToProfinite π).obj (D.obj i)).obj.V from x.1 i)) =
        g • (show ((finiteToProfinite π).obj (D.obj j)).obj.V from x.1 j)
      rw [hom_smul]
      exact congrArg (g • ·) (x.2 f)⟩
  one_smul x := Subtype.ext (funext fun i ↦
    one_smul π (show ((finiteToProfinite π).obj (D.obj i)).obj.V from x.1 i))
  mul_smul g g' x := Subtype.ext (funext fun i ↦
    mul_smul g g' (show ((finiteToProfinite π).obj (D.obj i)).obj.V from x.1 i))

lemma LimitPt.smul_val (g : π) (x : LimitPt D) (i : I) :
    (g • x).1 i = g • (show ((finiteToProfinite π).obj (D.obj i)).obj.V from x.1 i) :=
  rfl

noncomputable instance : ContinuousSMul π (LimitPt D) := by
  refine ⟨Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _⟩
  have h : Continuous fun x : LimitPt D ↦
      (show ((finiteToProfinite π).obj (D.obj i)).obj.V from x.1 i) :=
    (continuous_apply i).comp continuous_subtype_val
  exact continuous_fst.smul (h.comp continuous_snd)

/-- The limit of a diagram of finite continuous `π`-sets, as a profinite `π`-space. -/
noncomputable def limitObj : ContAction Profinite.{w} π :=
  ofProfinite π (LimitPt D)

/-- The projections of the limit. -/
noncomputable def limitπ (i : I) : limitObj D ⟶ (finiteToProfinite π).obj (D.obj i) :=
  ObjectProperty.homMk
    { hom := (Profinite.limitCone.{w, w} (profiniteDiagram D)).π.app i
      comm := fun _ ↦ ConcreteCategory.hom_ext _ _ fun _ ↦ rfl }

lemma limitπ_apply (i : I) (x : (limitObj D).obj.V) :
    (limitπ D i).hom.hom x = (x : LimitPt D).1 i :=
  rfl

lemma limitπ_map {i j : I} (f : i ⟶ j) :
    limitπ D i ≫ (finiteToProfinite π).map (D.map f) = limitπ D j :=
  hom_ext_apply fun x ↦ (x : LimitPt D).2 f

/-- The cocone exhibiting `Hom(lim D, -)` as the colimit of the functors `Hom(D i, -)`. -/
@[simps]
noncomputable def limitCocone : Cocone (D.op ⋙ coyoneda) where
  pt := (homFunctor π).obj (op (limitObj D))
  ι :=
    { app i :=
        { app E := ↾fun (a : D.obj i.unop ⟶ E) ↦ limitπ D i.unop ≫ (finiteToProfinite π).map a
          naturality E E' f := by
            ext (a : D.obj i.unop ⟶ E)
            change limitπ D i.unop ≫ (finiteToProfinite π).map (a ≫ f) =
              (limitπ D i.unop ≫ (finiteToProfinite π).map a) ≫ (finiteToProfinite π).map f
            rw [Functor.map_comp, Category.assoc] }
      naturality i j g := by
        ext E (a : D.obj i.unop ⟶ E)
        change limitπ D j.unop ≫ (finiteToProfinite π).map (D.map g.unop ≫ a) =
          limitπ D i.unop ≫ (finiteToProfinite π).map a
        rw [Functor.map_comp, ← Category.assoc, limitπ_map] }

/-- The underlying diagram of finite types. -/
noncomputable abbrev typeDiagram : I ⥤ Type w :=
  D ⋙ ObjectProperty.ι _ ⋙ Action.forget _ _ ⋙ FintypeCat.incl

instance (i : I) : Finite ((typeDiagram D).obj i) :=
  inferInstanceAs (Finite (D.obj i).obj.V)

/-- A section of the underlying diagram of finite types, as a point of the limit. -/
def LimitPt.mk (s : (typeDiagram D).sections) : LimitPt D :=
  ⟨s.1, fun f ↦ s.2 f⟩

lemma exists_limitPt_of_mem_eventualRange {i : I} {y : (D.obj i).obj.V}
    [IsCofilteredOrEmpty I] (hy : y ∈ (typeDiagram D).eventualRange i) :
    ∃ x : LimitPt D, x.1 i = y := by
  obtain ⟨s, hs, rfl⟩ := (typeDiagram D).exists_mem_sections_of_mem_eventualRange hy
  exact ⟨LimitPt.mk D ⟨s, hs⟩, rfl⟩

variable [IsCofiltered I]

/-- For a small cofiltered diagram `D` of finite continuous `π`-sets,
`Hom(lim D, E) = colim_i Hom(D i, E)`. -/
noncomputable def isColimitLimitCocone : IsColimit (limitCocone D) :=
  evaluationJointlyReflectsColimits _ fun E ↦ Types.FilteredColimit.isColimitOf _ _
    (fun (f : limitObj D ⟶ (finiteToProfinite π).obj E) ↦ by
      let lc : LocallyConstant (LimitPt D) ((finiteToProfinite π).obj E).obj.V :=
        ⟨fun x ↦ f.hom.hom x, (IsLocallyConstant.iff_continuous _).2
          (ConcreteCategory.hom f.hom.hom).continuous⟩
      obtain ⟨j, g, hg⟩ := Profinite.exists_locallyConstant _
        (Profinite.limitConeIsLimit.{w, w} (profiniteDiagram D)) lc
      have hfg (x : LimitPt D) : f.hom.hom x = g (x.1 j) :=
        congrArg (fun φ : LocallyConstant _ _ ↦ φ x) hg
      obtain ⟨k, t, hkt⟩ := (typeDiagram D).exists_eventualRange_eq_range j
      have hmem (z : (D.obj k).obj.V) :
          (D.map t).hom.hom z ∈ (typeDiagram D).eventualRange j := by
        rw [hkt]
        exact ⟨z, rfl⟩
      let a : D.obj k ⟶ E := ObjectProperty.homMk
        { hom := FintypeCat.homMk fun z ↦ g ((D.map t).hom.hom z)
          comm := fun σ ↦ by
            ext z
            change g ((D.map t).hom.hom (σ • z)) = σ • g ((D.map t).hom.hom z)
            obtain ⟨x, hx⟩ := exists_limitPt_of_mem_eventualRange D (hmem z)
            have h1 : (σ • x).1 j = (D.map t).hom.hom (σ • z) := by
              rw [LimitPt.smul_val, hom_smul_fintype]
              exact congrArg (σ • ·) hx
            rw [← h1, ← hx, ← hfg, ← hfg]
            exact hom_smul f σ x }
      refine ⟨op k, a, ?_⟩
      refine hom_ext_apply fun x ↦ ?_
      change f.hom.hom x = g ((D.map t).hom.hom ((x : LimitPt D).1 k))
      exact (hfg x).trans (congrArg g (x.2 t).symm))
    (fun i i' (a : D.obj i.unop ⟶ E) (a' : D.obj i'.unop ⟶ E) h ↦ by
      obtain ⟨m, p, p', -⟩ := IsCofilteredOrEmpty.cone_objs i.unop i'.unop
      obtain ⟨k, t, hkt⟩ := (typeDiagram D).exists_eventualRange_eq_range m
      refine ⟨op k, (t ≫ p).op, (t ≫ p').op, ?_⟩
      change D.map (t ≫ p) ≫ a = D.map (t ≫ p') ≫ a'
      ext z
      have hz : (D.map t).hom.hom z ∈ (typeDiagram D).eventualRange m := by
        rw [hkt]
        exact ⟨z, rfl⟩
      obtain ⟨x, hx⟩ := exists_limitPt_of_mem_eventualRange D hz
      have h' := congrArg (fun φ : limitObj D ⟶ (finiteToProfinite π).obj E ↦ φ.hom.hom x) h
      change a.hom.hom (x.1 i.unop) = a'.hom.hom (x.1 i'.unop) at h'
      rw [Functor.map_comp, Functor.map_comp]
      change a.hom.hom ((D.map p).hom.hom ((D.map t).hom.hom z)) =
        a'.hom.hom ((D.map p').hom.hom ((D.map t).hom.hom z))
      rw [← hx]
      rw [show (D.map p).hom.hom (x.1 m) = x.1 i.unop from x.2 p,
        show (D.map p').hom.hom (x.1 m) = x.1 i'.unop from x.2 p']
      exact h')

/-- The limit of a cofiltered diagram of non-empty finite `π`-sets is non-empty. -/
lemma nonempty_limitObj (hD : ∀ i, Nonempty (D.obj i).obj.V) : Nonempty (limitObj D).obj.V := by
  have (i : I) : Nonempty ((typeDiagram D).obj i) := hD i
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system (typeDiagram D)
  exact ⟨LimitPt.mk D ⟨s, hs⟩⟩

/-- The coordinate of a point of the limit. -/
abbrev LimitPt.coord (x : LimitPt D) (i : I) : (D.obj i).obj.V :=
  x.1 i

omit [IsCofiltered I] in
lemma LimitPt.map_coord (x : LimitPt D) {i j : I} (a : i ⟶ j) :
    (D.map a).hom.hom (LimitPt.coord D x i) = LimitPt.coord D x j :=
  x.2 a

omit [IsCofiltered I] in
lemma LimitPt.coord_smul (x : LimitPt D) (g : π) (i : I) :
    LimitPt.coord D (g • x) i = g • LimitPt.coord D x i :=
  rfl

/-- If a compact group `π` acts transitively on each term of a cofiltered diagram of finite
`π`-sets, it acts transitively on the limit. -/
lemma isPretransitive_limitObj [IsTopologicalGroup π] [CompactSpace π]
    (hD : ∀ i, MulAction.IsPretransitive π (D.obj i).obj.V) :
    MulAction.IsPretransitive π (limitObj D).obj.V := by
  have : Nonempty I := IsCofiltered.nonempty
  refine ⟨fun (x : LimitPt D) (y : LimitPt D) ↦ ?_⟩
  let S (i : I) : Set π := {g | g • LimitPt.coord D x i = LimitPt.coord D y i}
  have hS (i : I) : IsClosed (S i) := by
    have : Continuous fun g : π ↦ g • LimitPt.coord D x i := continuous_id.smul continuous_const
    exact (isClosed_discrete {LimitPt.coord D y i}).preimage this
  have sub {k i : I} (a : k ⟶ i) : S k ⊆ S i := fun g (hg : _ = _) ↦ by
    change g • LimitPt.coord D x i = LimitPt.coord D y i
    rw [← LimitPt.map_coord D x a, ← LimitPt.map_coord D y a, ← hom_smul_fintype]
    exact congrArg _ hg
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S
    (fun i j ↦ by
      obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i j
      exact ⟨k, sub a, sub b⟩)
    (fun i ↦ MulAction.exists_smul_eq π _ _) (fun i ↦ (hS i).isCompact) hS
  exact ⟨g, Subtype.ext (funext fun i ↦ Set.mem_iInter.1 hg i)⟩

end Limits

/-! ### The equivalence -/

section Equivalence

variable [IsTopologicalGroup π] [CompactSpace π] [TotallyDisconnectedSpace π]

omit [CompactSpace π] [TotallyDisconnectedSpace π] in
lemma homFunctor_obj_mem_essImage (X : ContAction Profinite.{w} π) :
    (Pro.coyoneda (ContAction FintypeCat.{w} π)).essImage ((homFunctor π).obj (op X)) :=
  Functor.isProRepresentable_iff_mem_essImage.1 ⟨proRepresentation X⟩

variable (π) in
/-- `X ↦ Hom(X, -)`, as a functor to the essential image of `Pro.coyoneda`. -/
noncomputable def homFunctorLift :
    (ContAction Profinite.{w} π)ᵒᵖ ⥤
      (Pro.coyoneda (ContAction FintypeCat.{w} π)).EssImageSubcategory :=
  ObjectProperty.lift _ (homFunctor π) fun X ↦ homFunctor_obj_mem_essImage X.unop

instance : (homFunctorLift.{w} π).Full :=
  Functor.Full.of_comp_faithful_iso (ObjectProperty.liftCompιIso _ _ _)

instance : (homFunctorLift.{w} π).Faithful :=
  Functor.Faithful.of_comp_iso (ObjectProperty.liftCompιIso _ _ _)

instance : (homFunctorLift.{w} π).EssSurj where
  mem_essImage Y := by
    obtain ⟨P, ⟨e⟩⟩ := Y.property
    let R := Pro.proRepresentation P.unop
    exact ⟨op (limitObj R.F), ⟨ObjectProperty.isoMk _
      ((isColimitLimitCocone R.F).coconePointUniqueUpToIso R.isColimit ≪≫ e)⟩⟩

variable (π) in
/-- The functor `C'(π)ᵒᵖ ⥤ (Pro C(π))ᵒᵖ` sending a profinite `π`-space `X` to the pro-object
representing `E ↦ Hom(X, E)`. -/
noncomputable def toProOp :
    (ContAction Profinite.{w} π)ᵒᵖ ⥤ (Pro (ContAction FintypeCat.{w} π))ᵒᵖ :=
  homFunctorLift π ⋙ (Pro.coyoneda (ContAction FintypeCat.{w} π)).toEssImage.inv

instance : (homFunctorLift.{w} π).IsEquivalence where

instance : (toProOp.{w} π).IsEquivalence := by
  unfold toProOp
  infer_instance

variable (π) in
/-- SGA 1 V.5.2: for a profinite group `π`, the category of pro-objects of the category of
finite sets with a continuous action of `π` is equivalent to the category of profinite spaces
with a continuous action of `π`. The inverse equivalence sends `X` to the pro-object
pro-representing `E ↦ Hom(X, E)` (`coyonedaObjProEquivalenceInverseIso`). -/
noncomputable def proEquivalence :
    Pro (ContAction FintypeCat.{w} π) ≌ ContAction Profinite.{w} π :=
  (toProOp π).asEquivalence.unop.symm

/-- The pro-object corresponding to a profinite `π`-space `X` pro-represents `Hom(X, -)`. -/
noncomputable def coyonedaObjProEquivalenceInverseIso (X : ContAction Profinite.{w} π) :
    (Pro.coyoneda _).obj (op ((proEquivalence π).inverse.obj X)) ≅ (homFunctor π).obj (op X) :=
  (Pro.coyoneda _).essImage.ι.mapIso
    ((Pro.coyoneda _).toEssImage.asEquivalence.counitIso.app ((homFunctorLift π).obj (op X)))

/-- `coyonedaObjProEquivalenceInverseIso` is natural in `X`. -/
lemma coyonedaObjProEquivalenceInverseIso_hom_naturality {X Y : ContAction Profinite.{w} π}
    (r : X ⟶ Y) :
    (Pro.coyoneda _).map ((proEquivalence π).inverse.map r).op ≫
        (coyonedaObjProEquivalenceInverseIso X).hom =
      (coyonedaObjProEquivalenceInverseIso Y).hom ≫ (homFunctor π).map r.op :=
  congrArg (Pro.coyoneda _).essImage.ι.map
    ((Pro.coyoneda _).toEssImage.asEquivalence.counitIso.hom.naturality
      ((homFunctorLift π).map r.op))

/-- SGA 1 V.5.2: the pro-object `“lim” D` of a small cofiltered diagram of finite continuous
`π`-sets corresponds to the limit of `D` (a profinite `π`-space). -/
noncomputable def proEquivalenceInverseObjLimitObjIso {I : Type w} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ ContAction FintypeCat.{w} π) :
    (proEquivalence π).inverse.obj (limitObj D) ≅ (Pro.lim I).obj D :=
  ((Pro.coyonedaFullyFaithful _).preimageIso
    (coyonedaObjProEquivalenceInverseIso (limitObj D) ≪≫
      (isColimitLimitCocone D).coconePointUniqueUpToIso (Pro.isColimitLimCocone D))).unop.symm

/-- SGA 1 V.5.2: the equivalence sends `“lim” D` to the limit of `D`. -/
noncomputable def proEquivalenceFunctorObjLimIso {I : Type w} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ ContAction FintypeCat.{w} π) :
    (proEquivalence π).functor.obj ((Pro.lim I).obj D) ≅ limitObj D :=
  (proEquivalence π).functor.mapIso (proEquivalenceInverseObjLimitObjIso D).symm ≪≫
    (proEquivalence π).counitIso.app _

/-- `Hom(E, -)` for a finite continuous `π`-set `E`, computed in profinite `π`-spaces. -/
noncomputable def homFunctorObjFiniteIso (E : ContAction FintypeCat.{w} π) :
    (homFunctor π).obj (op ((finiteToProfinite π).obj E)) ≅ coyoneda.obj (op E) :=
  NatIso.ofComponents (fun _ ↦ (finiteToProfiniteFullyFaithful π).homEquiv.symm.toIso)
    fun {X Y} f ↦ by
      ext (u : (finiteToProfinite π).obj E ⟶ (finiteToProfinite π).obj X)
      apply (finiteToProfiniteFullyFaithful π).map_injective
      change (finiteToProfinite π).map ((finiteToProfiniteFullyFaithful π).preimage
          (u ≫ (finiteToProfinite π).map f)) =
        (finiteToProfinite π).map ((finiteToProfiniteFullyFaithful π).preimage u ≫ f)
      simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]

/-- SGA 1 V.5.2: `C(π)` is the full subcategory of `C'(π)` of finite discrete spaces, and the
equivalence restricts to it: the pro-object corresponding to a finite `π`-set `E` is
`Pro.of E`. -/
noncomputable def proEquivalenceInverseObjFiniteIso (E : ContAction FintypeCat.{w} π) :
    (proEquivalence π).inverse.obj ((finiteToProfinite π).obj E) ≅ Pro.of.obj E :=
  ((Pro.coyonedaFullyFaithful _).preimageIso
    (coyonedaObjProEquivalenceInverseIso _ ≪≫ homFunctorObjFiniteIso E ≪≫
      (Pro.ofOpCompCoyonedaIso.app (op E)).symm)).unop.symm

/-- SGA 1 V.5.2: the equivalence sends `Pro.of E` to `E`. -/
noncomputable def proEquivalenceFunctorObjOfIso (E : ContAction FintypeCat.{w} π) :
    (proEquivalence π).functor.obj (Pro.of.obj E) ≅ (finiteToProfinite π).obj E :=
  (proEquivalence π).functor.mapIso (proEquivalenceInverseObjFiniteIso E).symm ≪≫
    (proEquivalence π).counitIso.app _

end Equivalence

/-! ### The regular `π`-space -/

section Regular

variable (π) [IsTopologicalGroup π] [CompactSpace π] [T2Space π] [TotallyDisconnectedSpace π]

/-- The profinite group `π` acting on itself by left translations. -/
noncomputable def regular : ContAction Profinite.{v} π :=
  letI : MulAction π (Profinite.of π) := inferInstanceAs (MulAction π π)
  letI : ContinuousSMul π (Profinite.of π) := inferInstanceAs (ContinuousSMul π π)
  ofProfinite π (Profinite.of π)

/-- An element of `π`, as a point of the regular `π`-space. -/
abbrev toRegular (g : π) : (regular π).obj.V := g

lemma regular_smul (g h : π) : g • toRegular π h = toRegular π (g * h) :=
  rfl

/-- Right multiplication by `σ`, an automorphism of the regular `π`-space. -/
noncomputable def regularRightMul (σ : π) : regular π ⟶ regular π :=
  ObjectProperty.homMk
    { hom := CompHausLike.ofHom _ ⟨fun (h : π) ↦ toRegular π (h * σ), by
        exact (continuous_id (X := π)).mul continuous_const⟩
      comm := fun g ↦ ConcreteCategory.hom_ext _ _ fun (h : π) ↦
        congrArg (toRegular π) (mul_assoc g h σ) }

lemma regularRightMul_apply (σ h : π) :
    (regularRightMul π σ).hom.hom (toRegular π h) = toRegular π (h * σ) :=
  rfl

/-- Evaluation at `1` identifies morphisms from the regular `π`-space with points. -/
noncomputable def regularHomEquiv (E : ContAction FintypeCat.{v} π) :
    (regular π ⟶ (finiteToProfinite π).obj E) ≃ E.obj.V where
  toFun f := f.hom.hom (toRegular π 1)
  invFun x := ObjectProperty.homMk
    { hom := CompHausLike.ofHom _ ⟨fun g : π ↦ g • x,
        (continuous_id.smul continuous_const : Continuous fun g : π ↦ g • (show E.obj.V from x))⟩
      comm := fun g ↦ ConcreteCategory.hom_ext _ _ fun h ↦ mul_smul g (h : π) x }
  left_inv f := hom_ext_apply fun (g : π) ↦ by
    change g • f.hom.hom (toRegular π 1) = f.hom.hom (toRegular π g)
    rw [← hom_smul, regular_smul, mul_one]
  right_inv x := one_smul π x

/-- Evaluation at `1` identifies morphisms from the regular `π`-space to a profinite `π`-space
`X` with the points of `X`. -/
noncomputable def regularHomEquivOfProfinite (X : ContAction Profinite.{v} π) :
    (regular π ⟶ X) ≃ X.obj.V where
  toFun f := f.hom.hom (toRegular π 1)
  invFun x := ObjectProperty.homMk
    { hom := CompHausLike.ofHom _ ⟨fun g : π ↦ g • x,
        (continuous_id.smul continuous_const : Continuous fun g : π ↦ g • x)⟩
      comm := fun g ↦ ConcreteCategory.hom_ext _ _ fun h ↦ mul_smul g (h : π) x }
  left_inv f := hom_ext_apply fun (g : π) ↦ by
    change g • f.hom.hom (toRegular π 1) = f.hom.hom (toRegular π g)
    rw [← hom_smul, regular_smul, mul_one]
  right_inv x := one_smul π x

lemma regularHomEquivOfProfinite_symm_apply (X : ContAction Profinite.{v} π) (x : X.obj.V)
    (g : π) : ((regularHomEquivOfProfinite π X).symm x).hom.hom (toRegular π g) = g • x :=
  rfl

/-- The regular `π`-space pro-represents the forgetful functor: `Hom(π, E) = E` via evaluation
at `1`. -/
noncomputable def homFunctorObjRegularIso :
    (homFunctor π).obj (op (regular π)) ≅
      ObjectProperty.ι _ ⋙ Action.forget _ _ ⋙ FintypeCat.incl :=
  NatIso.ofComponents (fun E ↦ (regularHomEquiv π E).toIso) fun _ ↦ rfl

end Regular

/-! ### Homogeneous spaces -/

section Homogeneous

lemma nonempty_of_iso {X Y : ContAction Profinite.{w} π} (e : X ≅ Y) [Nonempty Y.obj.V] :
    Nonempty X.obj.V :=
  ⟨e.inv.hom.hom (Classical.arbitrary _)⟩

lemma isPretransitive_of_iso {X Y : ContAction Profinite.{w} π} (e : X ≅ Y)
    [MulAction.IsPretransitive π Y.obj.V] : MulAction.IsPretransitive π X.obj.V where
  exists_smul_eq x x' := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq π (e.hom.hom.hom x) (e.hom.hom.hom x')
    refine ⟨g, ?_⟩
    have h (z : X.obj.V) : e.inv.hom.hom (e.hom.hom.hom z) = z :=
      congrArg (fun φ : X ⟶ X ↦ φ.hom.hom z) e.hom_inv_id
    have := congrArg e.inv.hom.hom hg
    rwa [hom_smul, h, h] at this

/-- A morphism of profinite `π`-spaces which is bijective is an isomorphism. -/
lemma isIso_of_bijective {X Y : ContAction Profinite.{w} π} (f : X ⟶ Y)
    (hf : Function.Bijective f.hom.hom) : IsIso f := by
  have : IsIso ((ObjectProperty.ι _).map f).hom := CompHausLike.isIso_of_bijective _ hf
  have : IsIso ((ObjectProperty.ι _).map f) := Action.isIso_of_hom_isIso _
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map f

variable [IsTopologicalGroup π] [CompactSpace π] [TotallyDisconnectedSpace π]

variable (π) in
/-- The profinite `π`-space `π/H`, for a closed subgroup `H` of a profinite group `π`. -/
noncomputable def quotientSpace (H : Subgroup π) [IsClosed (H : Set π)] :
    ContAction Profinite.{v} π :=
  ofProfinite π (Profinite.of (π ⧸ H))

instance (H : Subgroup π) [IsClosed (H : Set π)] : Nonempty (quotientSpace π H).obj.V :=
  ⟨(QuotientGroup.mk 1 : π ⧸ H)⟩

instance (H : Subgroup π) [IsClosed (H : Set π)] :
    MulAction.IsPretransitive π (quotientSpace π H).obj.V :=
  inferInstanceAs (MulAction.IsPretransitive π (π ⧸ H))

/-- A profinite `π`-space is homogeneous (non-empty, with a transitive action) iff it is
isomorphic to `π/H` for a closed subgroup `H` (the stabilizer of a point). -/
theorem nonempty_isPretransitive_iff_exists_iso_quotientSpace (X : ContAction Profinite.{v} π) :
    (Nonempty X.obj.V ∧ MulAction.IsPretransitive π X.obj.V) ↔
      ∃ (H : Subgroup π) (_ : IsClosed (H : Set π)), Nonempty (X ≅ quotientSpace π H) := by
  refine ⟨fun ⟨⟨a⟩, ht⟩ ↦ ?_, fun ⟨H, _, ⟨e⟩⟩ ↦ ⟨nonempty_of_iso e, isPretransitive_of_iso e⟩⟩
  let H := MulAction.stabilizer π a
  have hc : Continuous fun g : π ↦ g • a := continuous_id.smul continuous_const
  have : IsClosed (H : Set π) := isClosed_singleton.preimage hc
  let φ : π ⧸ H → X.obj.V := MulAction.ofQuotientStabilizer π a
  have hφ : Continuous φ := (QuotientGroup.isQuotientMap_mk H).continuous_iff.2 hc
  let f : quotientSpace π H ⟶ X := ObjectProperty.homMk
    { hom := CompHausLike.ofHom _ ⟨φ, hφ⟩
      comm := fun g ↦ ConcreteCategory.hom_ext _ _ fun q ↦
        MulAction.ofQuotientStabilizer_smul π a g q }
  have hf : Function.Bijective f.hom.hom := by
    refine ⟨MulAction.injective_ofQuotientStabilizer π a, fun x ↦ ?_⟩
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq π a x
    exact ⟨(QuotientGroup.mk g : π ⧸ H), MulAction.ofQuotientStabilizer_mk π a g⟩
  have := isIso_of_bijective f hf
  exact ⟨H, inferInstance, ⟨(asIso f).symm⟩⟩

end Homogeneous

/-! ### Profinite groups with an action by conjugation -/

section Conj

variable {ρ : Type w} [Group ρ] [TopologicalSpace ρ] [IsTopologicalGroup ρ] [CompactSpace ρ]
  [T2Space ρ] [TotallyDisconnectedSpace ρ]

/-- The action of `π` on `ρ` by conjugation through `u : π → ρ`. -/
@[reducible]
def conjMulAction (u : π →* ρ) : MulAction π (Profinite.of ρ) where
  smul g h := u g * (show ρ from h) * (u g)⁻¹
  one_smul h := show u 1 * (show ρ from h) * (u 1)⁻¹ = h by simp
  mul_smul g g' h :=
    show u (g * g') * (show ρ from h) * (u (g * g'))⁻¹ =
      u g * (u g' * (show ρ from h) * (u g')⁻¹) * (u g)⁻¹ by
      rw [map_mul]
      group

lemma continuousSMul_conjMulAction (u : π →ₜ* ρ) :
    @ContinuousSMul π (Profinite.of ρ) (conjMulAction u.toMonoidHom).toSMul _ _ :=
  @ContinuousSMul.mk π (Profinite.of ρ) (conjMulAction u.toMonoidHom).toSMul _ _
    (((u.continuous.comp continuous_fst).mul continuous_snd).mul
      (u.continuous.comp continuous_fst).inv)

/-- A profinite group `ρ` on which `π` acts by conjugation through a continuous homomorphism
`u : π → ρ`. It is a group object of the category of profinite `π`-spaces
(`ContAction.conjGrp`). -/
noncomputable def conjVia (u : π →ₜ* ρ) : ContAction Profinite.{w} π :=
  @ofProfinite π _ _ (Profinite.of ρ) (conjMulAction u.toMonoidHom) (continuousSMul_conjMulAction u)

variable (u : π →ₜ* ρ)

/-- An element of `ρ`, as a point of `conjVia u`. -/
abbrev toConjVia (g : ρ) : (conjVia u).obj.V := g

lemma conjVia_smul (g : π) (h : ρ) : g • toConjVia u h = toConjVia u (u g * h * (u g)⁻¹) :=
  rfl

variable {u}

/-- The underlying map of a morphism to `conjVia u`. -/
noncomputable abbrev conjVal {X : ContAction Profinite.{w} π} (f : X ⟶ conjVia u)
    (x : X.obj.V) : ρ :=
  f.hom.hom x

lemma conjVal_smul {X : ContAction Profinite.{w} π} (f : X ⟶ conjVia u) (g : π) (x : X.obj.V) :
    conjVal f (g • x) = u g * conjVal f x * (u g)⁻¹ :=
  hom_smul f g x

lemma conj_hom_ext {X : ContAction Profinite.{w} π} {f f' : X ⟶ conjVia u}
    (h : ∀ x, conjVal f x = conjVal f' x) : f = f' :=
  hom_ext_apply h

/-- The morphism `X ⟶ conjVia u` given by a suitably equivariant continuous map to `ρ`. -/
noncomputable def conjMk {X : ContAction Profinite.{w} π} (φ : X.obj.V → ρ) (hφ : Continuous φ)
    (hφ' : ∀ (g : π) x, φ (g • x) = u g * φ x * (u g)⁻¹) : X ⟶ conjVia u :=
  ObjectProperty.homMk
    { hom := CompHausLike.ofHom _ ⟨φ, hφ⟩
      comm := fun g ↦ ConcreteCategory.hom_ext _ _ fun x ↦ hφ' g x }

@[simp]
lemma conjVal_conjMk {X : ContAction Profinite.{w} π} (φ : X.obj.V → ρ) (hφ : Continuous φ)
    (hφ' : ∀ (g : π) x, φ (g • x) = u g * φ x * (u g)⁻¹) (x : X.obj.V) :
    conjVal (conjMk φ hφ hφ') x = φ x :=
  rfl

lemma continuous_conjVal {X : ContAction Profinite.{w} π} (f : X ⟶ conjVia u) :
    Continuous (conjVal f) :=
  (ConcreteCategory.hom f.hom.hom).continuous

/-- Morphisms to `conjVia u` form a group under pointwise multiplication. -/
noncomputable instance (X : ContAction Profinite.{w} π) : Group (X ⟶ conjVia u) where
  mul f f' := conjMk (fun x ↦ conjVal f x * conjVal f' x)
    ((continuous_conjVal f).mul (continuous_conjVal f'))
    fun g x ↦ by simp only [conjVal_smul]; group
  one := conjMk (fun _ ↦ 1) continuous_const fun g _ ↦ by group
  inv f := conjMk (fun x ↦ (conjVal f x)⁻¹) (continuous_conjVal f).inv
    fun g x ↦ by simp only [conjVal_smul]; group
  mul_assoc f f' f'' := conj_hom_ext fun _ ↦ mul_assoc _ _ _
  one_mul f := conj_hom_ext fun _ ↦ one_mul _
  mul_one f := conj_hom_ext fun _ ↦ mul_one _
  inv_mul_cancel f := conj_hom_ext fun _ ↦ inv_mul_cancel _

lemma conjVal_mul {X : ContAction Profinite.{w} π} (f f' : X ⟶ conjVia u) (x : X.obj.V) :
    conjVal (f * f') x = conjVal f x * conjVal f' x :=
  rfl

lemma conjVal_one {X : ContAction Profinite.{w} π} (x : X.obj.V) :
    conjVal (1 : X ⟶ conjVia u) x = 1 :=
  rfl

variable (u) in
/-- The functor of points of the group object `conjVia u`: `X ↦ Hom(X, conjVia u)` with
pointwise multiplication. -/
@[simps obj]
noncomputable def conjGrp : (ContAction Profinite.{w} π)ᵒᵖ ⥤ GrpCat.{w} where
  obj X := GrpCat.of (X.unop ⟶ conjVia u)
  map φ := GrpCat.ofHom
    { toFun f := φ.unop ≫ f
      map_one' := conj_hom_ext fun _ ↦ rfl
      map_mul' _ _ := conj_hom_ext fun _ ↦ rfl }

variable (u) in
/-- `conjVia u` represents its functor of points: it is a group object. -/
def conjGrpRepresentableBy : (conjGrp u ⋙ forget _).RepresentableBy (conjVia u) where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

/-- A continuous homomorphism `φ : ρ → ρ'` with `u' = φ ∘ u` induces a morphism of group objects
`conjVia u ⟶ conjVia u'`. -/
noncomputable def conjViaMap {ρ' : Type w} [Group ρ'] [TopologicalSpace ρ'] [IsTopologicalGroup ρ']
    [CompactSpace ρ'] [T2Space ρ'] [TotallyDisconnectedSpace ρ'] {u' : π →ₜ* ρ'} (φ : ρ →ₜ* ρ')
    (h : ∀ g, φ (u g) = u' g) : conjVia u ⟶ conjVia u' :=
  conjMk (fun x ↦ φ (show ρ from x)) (φ.continuous.comp continuous_id) fun g x ↦ by
    change φ (u g * (show ρ from x) * (u g)⁻¹) = u' g * φ (show ρ from x) * (u' g)⁻¹
    rw [map_mul, map_mul, map_inv, h]

/-- Composition with `conjViaMap φ` is a homomorphism of groups. -/
lemma conjViaMap_mul {ρ' : Type w} [Group ρ'] [TopologicalSpace ρ'] [IsTopologicalGroup ρ']
    [CompactSpace ρ'] [T2Space ρ'] [TotallyDisconnectedSpace ρ'] {u' : π →ₜ* ρ'} (φ : ρ →ₜ* ρ')
    (h : ∀ g, φ (u g) = u' g) {X : ContAction Profinite.{w} π} (f f' : X ⟶ conjVia u) :
    (f * f') ≫ conjViaMap φ h = (f ≫ conjViaMap φ h) * (f' ≫ conjViaMap φ h) :=
  conj_hom_ext fun _ ↦ map_mul φ _ _

end Conj

section ConjSelf

variable (π) [IsTopologicalGroup π] [CompactSpace π] [T2Space π] [TotallyDisconnectedSpace π]

/-- The profinite group `π` acting on itself by conjugation. -/
noncomputable abbrev conj : ContAction Profinite.{v} π :=
  conjVia (ContinuousMonoidHom.id π)

/-- Evaluation at `1` is an isomorphism of groups `Hom(π, conjVia u) ≃* ρ`, where `π` is the
regular `π`-space. -/
noncomputable def regularHomConjMulEquiv {ρ : Type v} [Group ρ] [TopologicalSpace ρ]
    [IsTopologicalGroup ρ] [CompactSpace ρ] [T2Space ρ] [TotallyDisconnectedSpace ρ]
    (u : π →ₜ* ρ) : (regular π ⟶ conjVia u) ≃* ρ where
  toFun f := conjVal f (toRegular π 1)
  invFun r := conjMk (fun (h : π) ↦ u h * r * (u h)⁻¹)
    (by
      have hu : Continuous fun h : π ↦ u h := u.continuous
      exact (hu.mul continuous_const).mul hu.inv)
    fun k (h : π) ↦
      show u (k * h) * r * (u (k * h))⁻¹ = u k * (u h * r * (u h)⁻¹) * (u k)⁻¹ by
        rw [map_mul]
        group
  left_inv f := conj_hom_ext fun (h : π) ↦ by
    change u h * conjVal f (toRegular π 1) * (u h)⁻¹ = conjVal f (toRegular π h)
    rw [← conjVal_smul, regular_smul, mul_one]
  right_inv r := by
    change u 1 * r * (u 1)⁻¹ = r
    simp
  map_mul' _ _ := rfl

/-- `π` acts transitively on itself by conjugation iff `π` is trivial. -/
theorem isPretransitive_conj_iff : MulAction.IsPretransitive π (conj π).obj.V ↔ Subsingleton π := by
  refine ⟨fun h ↦ ⟨fun a b ↦ ?_⟩, fun h ↦ ⟨fun a b ↦ ⟨1, Subsingleton.elim (α := π) _ _⟩⟩⟩
  have key (g : π) : g = 1 := by
    obtain ⟨k, hk⟩ := h.exists_smul_eq (toConjVia (ContinuousMonoidHom.id π) 1)
      (toConjVia (ContinuousMonoidHom.id π) g)
    change (ContinuousMonoidHom.id π) k * 1 * ((ContinuousMonoidHom.id π) k)⁻¹ = g at hk
    simpa using hk.symm
  rw [key a, key b]

/-- Morphisms to `conj π` act on morphisms to any profinite `π`-space `X`: `(f • u)(y) =
f(y) • u(y)`. This is the action `π × X → X`, in terms of points. -/
noncomputable instance (Y X : ContAction Profinite.{v} π) : MulAction (Y ⟶ conj π) (Y ⟶ X) where
  smul f u := ObjectProperty.homMk
    { hom := CompHausLike.ofHom _ ⟨fun y ↦ conjVal f y • u.hom.hom y,
        (continuous_conjVal f).smul (ConcreteCategory.hom u.hom.hom).continuous⟩
      comm := fun g ↦ ConcreteCategory.hom_ext _ _ fun y ↦ by
        change conjVal f (g • y) • u.hom.hom (g • y) = g • (conjVal f y • u.hom.hom y)
        rw [conjVal_smul, hom_smul, ← mul_smul, ← mul_smul]
        simp }
  one_smul u := hom_ext_apply fun _ ↦ one_smul π _
  mul_smul f f' u := hom_ext_apply fun _ ↦ mul_smul _ _ _

lemma smul_hom_apply {Y X : ContAction Profinite.{v} π} (f : Y ⟶ conj π) (u : Y ⟶ X)
    (y : Y.obj.V) : (f • u).hom.hom y = conjVal f y • u.hom.hom y :=
  rfl

/-- The action is natural in `Y`. -/
lemma comp_smul {Y Y' X : ContAction Profinite.{v} π} (φ : Y' ⟶ Y) (f : Y ⟶ conj π)
    (u : Y ⟶ X) : φ ≫ (f • u) = (φ ≫ f) • (φ ≫ u) :=
  rfl

/-- The action is natural in `X`. -/
lemma smul_comp {Y X X' : ContAction Profinite.{v} π} (f : Y ⟶ conj π) (u : Y ⟶ X)
    (g : X ⟶ X') : (f • u) ≫ g = f • (u ≫ g) :=
  hom_ext_apply fun y ↦ hom_smul g (conjVal f y) (u.hom.hom y)

end ConjSelf

/-! ### Restriction of operations -/

section Res

variable {π' : Type*} [Group π'] [TopologicalSpace π'] (u : π' →ₜ* π)

/-- Restriction of operations commutes with the inclusion of finite `π`-sets into profinite
`π`-spaces. -/
noncomputable def resFiniteToProfiniteIso (Y : ContAction FintypeCat.{w} π) :
    (ContAction.res _ u).obj ((finiteToProfinite π).obj Y) ≅
      (finiteToProfinite π').obj ((ContAction.res _ u).obj Y) :=
  ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _) fun _ ↦ rfl)

variable {ρ : Type w} [Group ρ] [TopologicalSpace ρ] [IsTopologicalGroup ρ] [CompactSpace ρ]
  [T2Space ρ] [TotallyDisconnectedSpace ρ] (u' : π →ₜ* ρ)

/-- Restricting `conjVia u'` along `u` gives `conjVia (u' ∘ u)`. -/
noncomputable def resConjViaIso : (ContAction.res _ u).obj (conjVia u') ≅ conjVia (u'.comp u) :=
  ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _) fun _ ↦ rfl)

end Res

end ContAction
