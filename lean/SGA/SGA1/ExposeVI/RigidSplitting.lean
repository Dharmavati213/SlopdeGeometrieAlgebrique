/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.Splittings
import SGA.SGA1.ExposeVI.FiberedProducts
import SGA.SGA1.ExposeVI.Products
import SGA.SGA1.ExposeVI.SplitEquivalence
import Mathlib.CategoryTheory.CodiscreteCategory

/-!
# SGA 1, Exposé VI, end of VI.9: splittings of categories with rigid fibers

SGA: if the fibers of a fibered category `𝒳` are rigid, one may replace `𝒳` by an `E`-equivalent
category whose fibers are rigid *and reduced*; such a category has a unique cleavage, and it is a
splitting.

* `exists_isSplitting_of_rigid`: for `𝒳` fibered with rigid fibers, the full subcategory `𝒳'` of
  chosen representatives of the vertical isomorphism classes is `E`-equivalent to `𝒳` (its
  inclusion is an `E`-equivalence), its fibers are rigid and reduced, and it has exactly one
  cleavage, which is a splitting.
* SGA asserts that "the question of existence of a splitting is not modified if one replaces `𝒳`
  by an `E`-equivalent category", so that `𝒳` itself admits a splitting. For splittings in the
  sense of VI.9 (normalized cleavages whose transports compose) this is false:
  `not_exists_isSplitting_threeToTwo` gives a fibered category (in groupoids) over the rigid
  connected groupoid with two objects, with rigid fibers, which admits no splitting. What survives
  is the statement up to `E`-equivalence above.
-/

universe v₁ v₂ u₁ u₂ w₁ w₂ w₃ t₁ t₂ t₃

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u₁} [Category.{v₁} E] {C : Type u₂} [Category.{v₂} C] (p : C ⥤ E)

/-- Two objects of `𝒳` are vertically isomorphic if they are isomorphic by an isomorphism lying
over an identity. -/
def VertIso (x y : C) : Prop := ∃ (S : E) (e : x ≅ y), IsHomLift p (𝟙 S) e.hom

namespace VertIso

variable {p}

theorem refl (x : C) : VertIso p x x := ⟨p.obj x, Iso.refl x, IsHomLift.id rfl⟩

theorem symm {x y : C} (h : VertIso p x y) : VertIso p y x := by
  obtain ⟨S, e, he⟩ := h
  exact ⟨S, e.symm, IsHomLift.lift_id_inv p _ e⟩

theorem trans {x y z : C} (h : VertIso p x y) (h' : VertIso p y z) : VertIso p x z := by
  obtain ⟨S, e, he⟩ := h
  obtain ⟨S', e', he'⟩ := h'
  obtain rfl : S = S' :=
    (IsHomLift.codomain_eq p (𝟙 S) e.hom).symm.trans (IsHomLift.domain_eq p (𝟙 S') e'.hom)
  exact ⟨S, e ≪≫ e', by simpa using (inferInstance : IsHomLift p (𝟙 S ≫ 𝟙 S) (e.hom ≫ e'.hom))⟩

end VertIso

/-- A chosen representative of the vertical isomorphism class of `x`. -/
noncomputable def canonRep (x : C) : C :=
  @Classical.epsilon C ⟨x⟩ (VertIso p x)

theorem vertIso_canonRep (x : C) : VertIso p x (canonRep p x) :=
  @Classical.epsilon_spec C (VertIso p x) ⟨x, VertIso.refl x⟩

theorem canonRep_eq {x y : C} (h : VertIso p x y) : canonRep p x = canonRep p y := by
  have : VertIso p x = VertIso p y :=
    funext fun z ↦ propext ⟨fun h' ↦ h.symm.trans h', fun h' ↦ h.trans h'⟩
  unfold canonRep
  rw [this]

theorem canonRep_canonRep (x : C) : canonRep p (canonRep p x) = canonRep p x :=
  (canonRep_eq p (vertIso_canonRep p x)).symm

/-- The full subcategory of `𝒳` formed by the chosen representatives. -/
def canonReps : ObjectProperty C := fun x ↦ canonRep p x = x

/-- The inclusion of the representatives, an `E`-functor. -/
def canonRepsInclusion :
    BasedFunctor (BasedCategory.ofFunctor ((canonReps p).ι ⋙ p)) (BasedCategory.ofFunctor p) where
  toFunctor := (canonReps p).ι
  w := rfl

instance : (canonRepsInclusion p).toFunctor.Full :=
  inferInstanceAs ((canonReps p).ι).Full

instance : (canonRepsInclusion p).toFunctor.Faithful :=
  inferInstanceAs ((canonReps p).ι).Faithful

/-- VI.9: the inclusion of the representatives is an `E`-equivalence. -/
theorem isBasedEquivalence_canonRepsInclusion : IsBasedEquivalence (canonRepsInclusion p) := by
  refine (isBasedEquivalence_iff _).mpr ⟨inferInstance, inferInstance, fun y ↦ ?_⟩
  obtain ⟨S, e, he⟩ := vertIso_canonRep p y
  obtain rfl : S = p.obj y := (IsHomLift.domain_eq p (𝟙 S) e.hom).symm
  exact ⟨⟨canonRep p y, canonRep_canonRep p y⟩, e.symm, IsHomLift.lift_id_inv p (p.obj y) e⟩

variable {p}

/-- VI.9: the fibers of the category of representatives are rigid if those of `𝒳` are. -/
theorem canonReps_rigid (hr : ∀ S, IsRigidCategory (Fiber p S)) (S : E) :
    IsRigidCategory (Fiber ((canonReps p).ι ⋙ p) S) := by
  intro a e
  have h := hr S ((fiberMap (canonRepsInclusion p) S).obj a)
    ((fiberMap (canonRepsInclusion p) S).mapIso e)
  apply Iso.ext
  apply (fiberMap (canonRepsInclusion p) S).map_injective
  exact (congrArg Iso.hom h).trans ((fiberMap (canonRepsInclusion p) S).map_id a).symm

variable (p) in
/-- VI.9: the fibers of the category of representatives are reduced. -/
theorem canonReps_reduced (S : E) : IsReducedCategory (Fiber ((canonReps p).ι ⋙ p) S) := by
  rintro a b ⟨e⟩
  have hv : VertIso p a.val.obj b.val.obj :=
    ⟨S, (canonReps p).ι.mapIso (Fiber.fiberInclusion.mapIso e),
      (isHomLift_comp_iff (canonReps p).ι p (𝟙 S) e.hom.val).mp e.hom.property⟩
  have h : a.val.obj = b.val.obj :=
    a.val.property.symm.trans ((canonRep_eq p hv).trans b.val.property)
  exact Subtype.ext (ObjectProperty.FullSubcategory.ext h)

/-- VI.9: if `𝒳` is fibered with rigid fibers, it is `E`-equivalent to a (full) subcategory `𝒳'`
which has exactly one cleavage, and this cleavage is a splitting. -/
theorem exists_isSplitting_of_rigid [IsFibered p] (hr : ∀ S, IsRigidCategory (Fiber p S)) :
    ∃ P : ObjectProperty C,
      ∃ F : BasedFunctor (BasedCategory.ofFunctor (P.ι ⋙ p)) (BasedCategory.ofFunctor p),
        F.toFunctor = P.ι ∧ IsBasedEquivalence F ∧
        ∃ K : Cleavage (P.ι ⋙ p), K.IsSplitting ∧ ∀ K' : Cleavage (P.ι ⋙ p), K' = K := by
  refine ⟨canonReps p, canonRepsInclusion p, rfl, isBasedEquivalence_canonRepsInclusion p, ?_⟩
  have : IsFibered (BasedCategory.ofFunctor p).p := inferInstanceAs (IsFibered p)
  have : IsFibered ((canonReps p).ι ⋙ p) :=
    isFibered_of_isBasedEquivalence_inverse _ (isBasedEquivalence_canonRepsInclusion p)
  let K : Cleavage ((canonReps p).ι ⋙ p) := Cleavage.ofIsPreFibered
  exact ⟨K, K.isSplitting_of_rigid_reduced (canonReps_rigid hr) (canonReps_reduced p),
    fun K' ↦ K'.eq_of_rigid_reduced (canonReps_rigid hr) (canonReps_reduced p) K⟩

/-! ### Composition of `E`-equivalences -/

section Compose

variable {X : BasedCategory.{w₁, t₁} E} {Y : BasedCategory.{w₂, t₂} E}
  {Z : BasedCategory.{w₃, t₃} E}

/-- VI.4.3: a composite of `E`-equivalences is an `E`-equivalence. -/
theorem IsBasedEquivalence.comp {F : BasedFunctor X Y} {G : BasedFunctor Y Z}
    (hF : IsBasedEquivalence F) (hG : IsBasedEquivalence G) :
    IsBasedEquivalence (BasedFunctor.comp F G) := by
  obtain ⟨hF₁, hF₂, hF₃⟩ := (isBasedEquivalence_iff F).mp hF
  obtain ⟨hG₁, hG₂, hG₃⟩ := (isBasedEquivalence_iff G).mp hG
  refine (isBasedEquivalence_iff _).mpr ⟨?_, ?_, fun z ↦ ?_⟩
  · exact inferInstanceAs (F.toFunctor ⋙ G.toFunctor).Full
  · exact inferInstanceAs (F.toFunctor ⋙ G.toFunctor).Faithful
  · obtain ⟨y, e, he⟩ := hG₃ z
    obtain ⟨x, e', he'⟩ := hF₃ y
    have hy : Y.p.obj y = Z.p.obj z :=
      (G.w_obj y).symm.trans (IsHomLift.domain_eq _ (𝟙 (Z.p.obj z)) e.hom)
    have : IsHomLift Z.p (𝟙 (Z.p.obj z)) (G.map e'.hom) := by
      have : IsHomLift Y.p (𝟙 (Z.p.obj z)) e'.hom := hy ▸ he'
      exact G.preserves_isHomLift _ _
    exact ⟨x, G.mapIso e' ≪≫ e, by
      change IsHomLift Z.p (𝟙 (Z.p.obj z)) (G.map e'.hom ≫ e.hom)
      infer_instance⟩

/-- VI.4.3: an isomorphism of categories over `E` is an `E`-equivalence. -/
theorem isBasedEquivalence_of_isIso (F : BasedFunctor X Y) [F.toFunctor.IsIso] :
    IsBasedEquivalence F := by
  refine (isBasedEquivalence_iff F).mpr ⟨inferInstance, inferInstance, fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := (Functor.IsIso.bijective_obj F.toFunctor).2 y
  exact ⟨x, eqToIso hx, IsHomLift.eqToHom_codomain_lift_id hx rfl⟩

end Compose

/-- VI.9: a fibered category with rigid fibers is `E`-equivalent to the split category defined by
a functor `φ : Eᵒᵖ ⥤ Cat` whose values are rigid and reduced categories. -/
theorem exists_basedEquivalent_split_of_rigid [IsFibered p]
    (hr : ∀ S, IsRigidCategory (Fiber p S)) :
    ∃ φ : Eᵒᵖ ⥤ Cat.{v₂, u₂}, (∀ S, IsRigidCategory (φ.obj S) ∧ IsReducedCategory (φ.obj S)) ∧
      ∃ F : BasedFunctor
        (BasedCategory.ofFunctor (LaxCoGrothendieck.forget (laxOfFunctor φ).toLaxFunctor))
        (BasedCategory.ofFunctor p), IsBasedEquivalence F := by
  have : IsFibered (BasedCategory.ofFunctor p).p := inferInstanceAs (IsFibered p)
  have : IsFibered ((canonReps p).ι ⋙ p) :=
    isFibered_of_isBasedEquivalence_inverse _ (isBasedEquivalence_canonRepsInclusion p)
  let K : Cleavage ((canonReps p).ι ⋙ p) := Cleavage.ofIsPreFibered
  have hK : K.IsSplitting := K.isSplitting_of_rigid_reduced (canonReps_rigid hr)
    (canonReps_reduced p)
  refine ⟨hK.toFunctor, fun S ↦ ⟨canonReps_rigid hr S.unop, canonReps_reduced p S.unop⟩,
    BasedFunctor.comp hK.fromLaxCoGrothendieckBased (canonRepsInclusion p), ?_⟩
  have : hK.fromLaxCoGrothendieckBased.toFunctor.IsIso :=
    inferInstanceAs hK.fromLaxCoGrothendieck.IsIso
  exact (isBasedEquivalence_of_isIso _).comp (isBasedEquivalence_canonRepsInclusion p)

/-! ### A fibered category with rigid fibers and no splitting -/

/-- The projection from the codiscrete category on three objects `0, 1, 2` to the codiscrete
category on two objects (the rigid connected groupoid with two objects), sending `0` to `false`
and `1, 2` to `true`. -/
def threeToTwo : Codiscrete (Fin 3) ⥤ Codiscrete Bool :=
  Codiscrete.functorOfFun fun i ↦ decide (i ≠ 0)

theorem threeToTwo_isFibered : IsFibered threeToTwo := by
  refine IsFibered.of_exists_isStronglyCartesian fun a R f ↦ ?_
  let b : Codiscrete (Fin 3) := ⟨if R.as then 1 else 0⟩
  have hb : threeToTwo.obj b = R := by
    obtain ⟨r⟩ := R
    cases r <;> rfl
  have : IsHomLift threeToTwo f (Codiscrete.iso b a).hom :=
    IsHomLift.of_fac' threeToTwo f _ hb rfl (Subsingleton.elim _ _)
  exact ⟨b, (Codiscrete.iso b a).hom, inferInstance⟩

/-- The fibers of `threeToTwo` are rigid (but the fiber over `true` is not reduced). -/
theorem threeToTwo_rigid (S : Codiscrete Bool) : IsRigidCategory (Fiber threeToTwo S) :=
  fun _ _ ↦ Iso.ext (Subtype.ext (Subsingleton.elim _ _))

theorem threeToTwo_not_reduced : ¬ IsReducedCategory (Fiber threeToTwo ⟨true⟩) := by
  intro h
  have := h ⟨⟨1⟩, rfl⟩ ⟨⟨2⟩, rfl⟩
    ⟨⟨⟨(), IsHomLift.of_fac' _ _ _ rfl rfl (Subsingleton.elim _ _)⟩,
      ⟨(), IsHomLift.of_fac' _ _ _ rfl rfl (Subsingleton.elim _ _)⟩,
      Subtype.ext (Subsingleton.elim _ _), Subtype.ext (Subsingleton.elim _ _)⟩⟩
  have := congrArg (fun x ↦ x.val.as) this
  simp at this

/-- VI.9: `threeToTwo` is fibered, with rigid fibers, but admits no splitting: SGA's reduction
"the existence of a splitting is not modified by passing to an `E`-equivalent category" fails for
normalized splittings. -/
theorem not_exists_isSplitting_threeToTwo :
    ¬ ∃ K : Cleavage threeToTwo, K.IsSplitting := by
  rintro ⟨K, hK⟩
  let f₁ : (⟨false⟩ : Codiscrete Bool) ⟶ ⟨true⟩ := ()
  let g₁ : (⟨true⟩ : Codiscrete Bool) ⟶ ⟨false⟩ := ()
  have hcomp := hK.pullback_comp f₁ g₁
  rw [show g₁ ≫ f₁ = 𝟙 _ from Subsingleton.elim _ _, hK.1.pullback_id] at hcomp
  -- every object over `false` is `0`
  have hfalse : ∀ w w' : Fiber threeToTwo ⟨false⟩, w = w' := by
    rintro ⟨⟨i⟩, hi⟩ ⟨⟨j⟩, hj⟩
    have hi' : i = 0 := by
      by_contra h
      have := congrArg Codiscrete.as hi
      simp [threeToTwo, Codiscrete.functorOfFun, Codiscrete.functor, h] at this
    have hj' : j = 0 := by
      by_contra h
      have := congrArg Codiscrete.as hj
      simp [threeToTwo, Codiscrete.functorOfFun, Codiscrete.functor, h] at this
    subst hi' hj'
    rfl
  let y : Fiber threeToTwo ⟨true⟩ := ⟨⟨1⟩, rfl⟩
  let z : Fiber threeToTwo ⟨true⟩ := ⟨⟨2⟩, rfl⟩
  have hy := Functor.congr_obj hcomp y
  have hz := Functor.congr_obj hcomp z
  have : y = z :=
    calc y = (K.pullback f₁ ⋙ K.pullback g₁).obj y := hy.symm
      _ = (K.pullback f₁ ⋙ K.pullback g₁).obj z := by
        simp only [Functor.comp_obj]
        rw [hfalse ((K.pullback f₁).obj y) ((K.pullback f₁).obj z)]
      _ = z := hz
  have := congrArg (fun x ↦ x.val.as) this
  simp [y, z] at this

end SGA.SGA1.ExposeVI
