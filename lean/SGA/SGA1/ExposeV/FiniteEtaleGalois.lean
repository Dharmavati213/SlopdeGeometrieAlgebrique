/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import SGA.SGA1.ExposeV.FiniteEtaleAlgebra


/-!
# SGA 1, Exposé V, §7: finite étale coverings of a connected affine scheme form a Galois category

Let `R` be a ring with `Spec R` connected and `a : R → Ω` a geometric point (`Ω` separably
closed; the axioms are first checked for `Ω` algebraically closed and then transferred, since
the points with values in `Ω` and in an algebraic closure of `Ω` agree).
The category of étale coverings of `Spec R` is the opposite of mathlib's category
`CommAlgCat.FiniteEtale R` of finite étale `R`-algebras, and the functor `F(X)` of geometric
points over `a` is mathlib's `CommAlgCat.FiniteEtale.fiber R Ω`, `S ↦ Hom_R(S, Ω)`.

We verify the axioms (G 1)–(G 6) of V.4 in mathlib's form (`PreGaloisCategory`,
`PreGaloisCategory.FiberFunctor`):

* (G 1) finite limits: the terminal covering is `R`, fiber products are tensor products;
* (G 2) finite sums are products of algebras, and the quotient by a finite group is the algebra
  of invariants (finite étale by V.3.4, `finite_etale_fixedPoints`);
* (G 3) every monomorphism of coverings is the inclusion of a direct summand
  (V.3.5, V.3.6: an epimorphism of finite étale algebras is surjective with idempotent kernel);
* (G 4), (G 5): `Hom_R(-, Ω)` is exact on these (co)limits; on quotients this is the classical
  fact that the geometric points of `A^G` are the `G`-orbits of those of `A`;
* (G 6) is V.3.7 (`bijective_of_bijective_comp`).

Consequently (mathlib's Galois theory) `π₁(Spec R, a) := Aut F` is a profinite group and `F`
induces an equivalence with finite continuous `π₁`-sets (`equivContAction`). We also prove that a
covering is connected in the Galois category iff its algebra has no nontrivial idempotents
(`isConnected_op_iff`), and that `#F(X)` is the degree of `X` (`card_fiber_eq_rankAtStalk`).

The (co)limits are first constructed in `CommAlgCat R` (`CommAlgCatPushout`, `CommAlgCatLimits`);
the full subcategory of finite étale algebras is shown to be closed under them.
-/

universe u

open CategoryTheory Limits TensorProduct

namespace SGA.SGA1.ExposeV

namespace CommAlgCatPushout

variable {R : Type u} [CommRing R] {A B C : CommAlgCat.{u} R} (f : B ⟶ A) (g : B ⟶ C)

/-- The tensor product `A ⊗[B] C` as a pushout cocone in `CommAlgCat R`. -/
noncomputable def pushoutCocone : PushoutCocone f g :=
  letI := f.hom.toRingHom.toAlgebra
  letI := g.hom.toRingHom.toAlgebra
  haveI : IsScalarTower R B A := .of_algebraMap_eq' f.hom.comp_algebraMap.symm
  haveI : IsScalarTower R B C := .of_algebraMap_eq' g.hom.comp_algebraMap.symm
  PushoutCocone.mk (W := CommAlgCat.of R (A ⊗[B] C))
    (CommAlgCat.ofHom Algebra.TensorProduct.includeLeft)
    (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight.restrictScalars R)) (by
      ext b
      change (f b) ⊗ₜ[B] (1 : C) = (1 : A) ⊗ₜ[B] g b
      rw [show f b = algebraMap B A b from rfl, show g b = algebraMap B C b from rfl,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])

/-- The tensor product is a pushout in `CommAlgCat R`. -/
noncomputable def pushoutCoconeIsColimit : IsColimit (pushoutCocone f g) :=
  letI := f.hom.toRingHom.toAlgebra
  letI := g.hom.toRingHom.toAlgebra
  haveI : IsScalarTower R B A := .of_algebraMap_eq' f.hom.comp_algebraMap.symm
  haveI : IsScalarTower R B C := .of_algebraMap_eq' g.hom.comp_algebraMap.symm
  PushoutCocone.IsColimit.mk _
    (fun s ↦
      letI : Algebra B s.pt := (f ≫ s.inl).hom.toRingHom.toAlgebra
      haveI : IsScalarTower R B s.pt :=
        .of_algebraMap_eq' (f ≫ s.inl).hom.comp_algebraMap.symm
      let f' : A →ₐ[B] s.pt := { s.inl.hom with commutes' := fun _ ↦ rfl }
      let g' : C →ₐ[B] s.pt := { s.inr.hom with commutes' := fun b ↦
        (congr($(s.condition).hom b)).symm }
      CommAlgCat.ofHom
        ((Algebra.TensorProduct.lift f' g' fun _ _ ↦ .all _ _).restrictScalars R))
    (fun s ↦ by
      ext a
      simp only [CommAlgCat.hom_comp,
        CommAlgCat.hom_ofHom, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.lift_tmul, map_one,
        mul_one]
      rfl)
    (fun s ↦ by
      ext c
      simp only [CommAlgCat.hom_comp,
        CommAlgCat.hom_ofHom, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.lift_tmul, map_one,
        one_mul]
      rfl)
    (fun s m h₁ h₂ ↦ by
      ext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a c =>
        have : (a ⊗ₜ[B] c : A ⊗[B] C) = (a ⊗ₜ 1) * (1 ⊗ₜ c) := by simp
        rw [this, map_mul]
        have e₁ := congr($(h₁).hom a)
        have e₂ := congr($(h₂).hom c)
        simp only [CommAlgCat.hom_comp, AlgHom.comp_apply, CommAlgCat.hom_ofHom,
          AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.includeRight_apply] at e₁ e₂
        simp only [CommAlgCat.hom_ofHom, AlgHom.restrictScalars_apply, map_mul,
          Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul]
        rw [e₁, e₂]
        rfl
      | add x y hx hy => simp [hx, hy])

lemma pushoutCocone_pt_prop [Algebra.Etale R B] [Module.Finite R A] [Algebra.Etale R A]
    [Module.Finite R C] [Algebra.Etale R C] :
    CommAlgCat.finiteEtale R (pushoutCocone f g).pt := by
  let _ := f.hom.toRingHom.toAlgebra
  let _ := g.hom.toRingHom.toAlgebra
  have : IsScalarTower R B A := .of_algebraMap_eq' f.hom.comp_algebraMap.symm
  have : IsScalarTower R B C := .of_algebraMap_eq' g.hom.comp_algebraMap.symm
  exact finite_etale_tensorProduct (R := R) (B := B) (A := A) (C := C)

end CommAlgCatPushout

namespace CommAlgCatLimits

variable {R : Type u} [CommRing R]

/-- The product algebra as a fan in `CommAlgCat R`. -/
noncomputable def piFan {J : Type} (f : J → CommAlgCat.{u} R) : Fan f :=
  Fan.mk (CommAlgCat.of R (Π j, f j)) fun j ↦ CommAlgCat.ofHom (Pi.evalAlgHom R _ j)

/-- The product algebra is a product in `CommAlgCat R`. -/
noncomputable def piFanIsLimit {J : Type} (f : J → CommAlgCat.{u} R) : IsLimit (piFan f) :=
  Fan.IsLimit.mk _ (fun s ↦ CommAlgCat.ofHom (AlgHom.pi fun j ↦ (s.proj j).hom))
    (fun s j ↦ by ext x; rfl)
    (fun s m hm ↦ by
      ext x
      funext j
      exact congr($(hm j).hom x))

variable {G : Type*} [Monoid G] (K : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.{u} R)

/-- The joint fixed points of the endomorphisms `K.map g` of `K.obj (op star)`. -/
def fixedSubalgebra : Subalgebra R (K.obj (Opposite.op (SingleObj.star G))) :=
  ⨅ g : G, AlgHom.equalizer (K.map (Quiver.Hom.op (g : SingleObj.star G ⟶ SingleObj.star G))).hom
    (AlgHom.id R _)

lemma mem_fixedSubalgebra {x : K.obj (Opposite.op (SingleObj.star G))} :
    x ∈ fixedSubalgebra K ↔
      ∀ g : G, (K.map (Quiver.Hom.op (g : SingleObj.star G ⟶ SingleObj.star G))) x = x := by
  simp [fixedSubalgebra, Algebra.mem_iInf, AlgHom.mem_equalizer]

/-- The fixed points as a cone. -/
noncomputable def fixedCone : Cone K where
  pt := CommAlgCat.of R (fixedSubalgebra K)
  π :=
    { app := fun _ ↦ CommAlgCat.ofHom (fixedSubalgebra K).val
      naturality := by
        intro _ _ g
        ext x
        exact ((mem_fixedSubalgebra K).mp x.2 g.unop).symm }

/-- The fixed points are a limit. -/
noncomputable def fixedConeIsLimit : IsLimit (fixedCone K) where
  lift s := CommAlgCat.ofHom ((s.π.app (Opposite.op (SingleObj.star G))).hom.codRestrict _
    fun y ↦ (mem_fixedSubalgebra K).mpr fun g ↦ by
      have := s.w (j := Opposite.op (SingleObj.star G)) (j' := Opposite.op (SingleObj.star G))
        (Quiver.Hom.op (g : SingleObj.star G ⟶ SingleObj.star G))
      exact congr($(this).hom y))
  fac s _ := by
    ext y
    rfl
  uniq s m hm := by
    ext y
    exact Subtype.ext (congr($(hm (Opposite.op (SingleObj.star G))).hom y))

/-- The left action of `G` on `K.obj (op star)` given by `g • x = K.map (g⁻¹).op x`. -/
@[reducible] noncomputable def fixedAction {G : Type*} [Group G]
    (K : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.{u} R) :
    MulSemiringAction G (K.obj (Opposite.op (SingleObj.star G))) where
  smul g x := K.map (Quiver.Hom.op (g⁻¹ : SingleObj.star G ⟶ SingleObj.star G)) x
  one_smul x := by
    change K.map (Quiver.Hom.op (1⁻¹ : SingleObj.star G ⟶ SingleObj.star G)) x = x
    rw [inv_one, ← SingleObj.id_as_one, op_id, K.map_id]
    rfl
  mul_smul g h x := by
    change K.map (Quiver.Hom.op ((g * h)⁻¹ : SingleObj.star G ⟶ SingleObj.star G)) x =
      K.map (Quiver.Hom.op (g⁻¹ : SingleObj.star G ⟶ SingleObj.star G))
        (K.map (Quiver.Hom.op (h⁻¹ : SingleObj.star G ⟶ SingleObj.star G)) x)
    rw [mul_inv_rev, ← SingleObj.comp_as_mul, op_comp, K.map_comp]
    rfl
  smul_zero g := map_zero _
  smul_add g x y := map_add _ x y
  smul_one g := map_one _
  smul_mul g x y := map_mul _ x y

lemma fixedAction_smulCommClass {G : Type*} [Group G] (K : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.{u} R) :
    letI := fixedAction K
    SMulCommClass G R (K.obj (Opposite.op (SingleObj.star G))) :=
  letI := fixedAction K
  ⟨fun g r x ↦ map_smul (K.map (Quiver.Hom.op (g⁻¹ : SingleObj.star G ⟶ _))).hom r x⟩

lemma fixedSubalgebra_eq {G : Type*} [Group G] (K : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.{u} R) :
    letI := fixedAction K
    letI := fixedAction_smulCommClass K
    fixedSubalgebra K = FixedPoints.subalgebra R _ G := by
  let _ := fixedAction K
  have := fixedAction_smulCommClass K
  ext x
  rw [mem_fixedSubalgebra]
  constructor
  · intro h g
    exact h g⁻¹
  · intro h g
    have : K.map (Quiver.Hom.op (g⁻¹⁻¹ : SingleObj.star G ⟶ SingleObj.star G)) x = x := h g⁻¹
    rwa [inv_inv] at this

end CommAlgCatLimits

section TypesSingleObj

/-- A cocone in types over `SingleObj G` is a colimit when its leg is surjective with fibers the
`G`-orbits. -/
lemma nonempty_isColimit_singleObj {G : Type*} [Group G] {K : SingleObj G ⥤ Type u}
    (c : Cocone K) (hsurj : Function.Surjective (c.ι.app (SingleObj.star G)))
    (hinj : ∀ x y, c.ι.app (SingleObj.star G) x = c.ι.app (SingleObj.star G) y →
      ∃ g : G, K.map (g : SingleObj.star G ⟶ SingleObj.star G) x = y) :
    Nonempty (IsColimit c) := by
  rw [Types.isColimit_iff_coconeTypesIsColimit]
  refine ⟨⟨fun a b hab ↦ ?_, fun z ↦ ?_⟩⟩
  · obtain ⟨⟨⟩, x, rfl⟩ := K.ιColimitType_jointly_surjective a
    obtain ⟨⟨⟩, y, rfl⟩ := K.ιColimitType_jointly_surjective b
    obtain ⟨g, rfl⟩ := hinj x y hab
    exact (K.ιColimitType_map (g : SingleObj.star G ⟶ SingleObj.star G) x).symm
  · obtain ⟨x, rfl⟩ := hsurj z
    exact ⟨K.ιColimitType _ x, rfl⟩

end TypesSingleObj

section Closure

variable {C : Type*} [Category* C] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (J : Type*) [Category* J]

lemma isClosedUnderColimitsOfShape_of_exists
    (h : ∀ K : J ⥤ C, (∀ j, P (K.obj j)) → ∃ c : Cocone K, Nonempty (IsColimit c) ∧ P c.pt) :
    P.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨hX⟩
    obtain ⟨c, ⟨hc⟩, hP⟩ := h hX.diag hX.prop_diag_obj
    exact P.prop_of_iso (hc.coconePointUniqueUpToIso hX.isColimit) hP

lemma isClosedUnderLimitsOfShape_of_exists
    (h : ∀ K : J ⥤ C, (∀ j, P (K.obj j)) → ∃ c : Cone K, Nonempty (IsLimit c) ∧ P c.pt) :
    P.IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro X ⟨hX⟩
    obtain ⟨c, ⟨hc⟩, hP⟩ := h hX.diag hX.prop_diag_obj
    exact P.prop_of_iso (hc.conePointUniqueUpToIso hX.isLimit) hP

end Closure

section FiniteEtaleClosure

variable (R : Type u) [CommRing R]

instance : (CommAlgCat.finiteEtale.{u} R).IsClosedUnderIsomorphisms where
  of_iso e h := by
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨Module.Finite.equiv (CommAlgCat.algEquivOfIso e).toLinearEquiv,
      Algebra.Etale.of_equiv (CommAlgCat.algEquivOfIso e)⟩

instance : (CommAlgCat.finiteEtale.{u} R).IsClosedUnderColimitsOfShape WalkingSpan :=
  isClosedUnderColimitsOfShape_of_exists _ _ fun K hK ↦ by
    obtain ⟨_, _⟩ := hK .zero
    obtain ⟨_, _⟩ := hK .left
    obtain ⟨_, _⟩ := hK .right
    refine ⟨(Cocone.precompose (diagramIsoSpan K).hom).obj
      (CommAlgCatPushout.pushoutCocone (K.map WalkingSpan.Hom.fst) (K.map WalkingSpan.Hom.snd)),
      ⟨(IsColimit.precomposeHomEquiv _ _).symm (CommAlgCatPushout.pushoutCoconeIsColimit _ _)⟩,
      CommAlgCatPushout.pushoutCocone_pt_prop _ _⟩

instance : (CommAlgCat.finiteEtale.{u} R).IsClosedUnderColimitsOfShape (Discrete PEmpty.{1}) :=
  isClosedUnderColimitsOfShape_of_exists _ _ fun K _ ↦ by
    refine ⟨(Cocone.precompose (Functor.emptyExt K (Functor.empty _)).hom).obj
      (asEmptyCocone (CommAlgCat.of R R)),
      ⟨(IsColimit.precomposeHomEquiv _ _).symm (CommAlgCat.isInitialSelf (R := R))⟩, ?_⟩
    exact ⟨inferInstanceAs (Module.Finite R R), inferInstanceAs (Algebra.Etale R R)⟩

instance (J : Type) [Finite J] :
    (CommAlgCat.finiteEtale.{u} R).IsClosedUnderLimitsOfShape (Discrete J) :=
  isClosedUnderLimitsOfShape_of_exists _ _ fun K hK ↦ by
    have h₁ (j : J) : Module.Finite R (K.obj ⟨j⟩) := (hK ⟨j⟩).1
    have h₂ (j : J) : Algebra.Etale R (K.obj ⟨j⟩) := (hK ⟨j⟩).2
    refine ⟨(Cone.postcompose (Discrete.natIsoFunctor (F := K)).symm.hom).obj
      (CommAlgCatLimits.piFan fun j ↦ K.obj ⟨j⟩),
      ⟨(IsLimit.postcomposeHomEquiv _ _).symm (CommAlgCatLimits.piFanIsLimit _)⟩, ?_⟩
    exact ⟨inferInstanceAs (Module.Finite R (Π j, K.obj ⟨j⟩)),
      inferInstanceAs (Algebra.Etale R (Π j, K.obj ⟨j⟩))⟩

instance (J : Type) [Finite J] :
    (CommAlgCat.finiteEtale.{u} R).IsClosedUnderLimitsOfShape (Discrete J)ᵒᵖ :=
  .of_equivalence (Discrete.opposite J).symm

instance (G : Type u) [Group G] [Finite G] [ConnectedSpace (PrimeSpectrum R)] :
    (CommAlgCat.finiteEtale.{u} R).IsClosedUnderLimitsOfShape (SingleObj G)ᵒᵖ :=
  isClosedUnderLimitsOfShape_of_exists _ _ fun K hK ↦ by
    refine ⟨CommAlgCatLimits.fixedCone K, ⟨CommAlgCatLimits.fixedConeIsLimit K⟩, ?_⟩
    obtain ⟨_, _⟩ := hK (Opposite.op (SingleObj.star G))
    let _ := CommAlgCatLimits.fixedAction K
    have := CommAlgCatLimits.fixedAction_smulCommClass K
    obtain ⟨_, _⟩ := finite_etale_fixedPoints (R := R) (K.obj (Opposite.op (SingleObj.star G))) G
    let e := Subalgebra.equivOfEq _ _ (CommAlgCatLimits.fixedSubalgebra_eq K).symm
    exact ⟨Module.Finite.equiv e.toLinearEquiv, Algebra.Etale.of_equiv e⟩

end FiniteEtaleClosure


section FiniteEtaleInstances

variable (R : Type u) [CommRing R]

open CommAlgCat

instance : (CommAlgCat.finiteEtale.{u} R).IsClosedUnderColimitsOfShape WalkingCospanᵒᵖ :=
  .of_equivalence walkingCospanOpEquiv.symm

instance : (CommAlgCat.finiteEtale.{u} R).IsClosedUnderColimitsOfShape (Discrete PEmpty.{1})ᵒᵖ :=
  .of_equivalence (Discrete.opposite PEmpty).symm

instance : HasFiniteProducts (FiniteEtale.{u} R) := ⟨fun _ ↦ inferInstance⟩

instance (G : Type u) [Group G] : HasLimitsOfShape (SingleObj G)ᵒᵖ (CommAlgCat.{u} R) :=
  (hasLimitsOfSizeShrink.{u, 0, u, u} (CommAlgCat.{u} R)).has_limits_of_shape _

attribute [local instance] hasLimitsOfShape_op_of_hasColimitsOfShape

instance : HasPullbacks (FiniteEtale.{u} R)ᵒᵖ := inferInstance

instance : HasTerminal (FiniteEtale.{u} R)ᵒᵖ := inferInstance

instance : HasFiniteCoproducts (FiniteEtale.{u} R)ᵒᵖ := inferInstance

instance [ConnectedSpace (PrimeSpectrum R)] (G : Type u) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) (FiniteEtale.{u} R)ᵒᵖ := inferInstance

end FiniteEtaleInstances

section YonedaColimits

variable (R : Type u) [CommRing R] (Ω : Type u) [Field Ω] [Algebra R Ω]

open CommAlgCat

/-- `Hom_R(-, Ω)` sends finite products of `R`-algebras to disjoint unions (`Ω` a field). -/
instance preservesColimitsOfShape_discrete_yoneda (J : Type) [Finite J] :
    PreservesColimitsOfShape (Discrete J) (yoneda.obj (CommAlgCat.of R Ω)) := by
  have (f : J → (CommAlgCat.{u} R)ᵒᵖ) :
      PreservesColimit (Discrete.functor f) (yoneda.obj (CommAlgCat.of R Ω)) := by
    classical
    let c : Cofan f := (CommAlgCatLimits.piFan fun j ↦ (f j).unop).op
    have hc : IsColimit c := Fan.IsLimit.op (CommAlgCatLimits.piFanIsLimit _)
    refine preservesColimit_of_preserves_colimit_cocone hc ?_
    refine (isColimitMapCoconeCofanMkEquiv _ _ _).symm ?_
    refine Nonempty.some ((Cofan.nonempty_isColimit_iff_bijective_fromSigma _).mpr ⟨?_, ?_⟩)
    · rintro ⟨i, x⟩ ⟨j, y⟩ h
      change (f i).unop ⟶ CommAlgCat.of R Ω at x
      change (f j).unop ⟶ CommAlgCat.of R Ω at y
      change CommAlgCat.ofHom (Pi.evalAlgHom R (fun j ↦ (f j).unop) i) ≫ x =
        CommAlgCat.ofHom (Pi.evalAlgHom R (fun j ↦ (f j).unop) j) ≫ y at h
      have h' : ∀ a : Π j, (f j).unop, x.hom (a i) = y.hom (a j) := fun a ↦ congr($(h).hom a)
      obtain rfl : i = j := by
        by_contra hij
        have := h' (Pi.single i 1)
        simp [Pi.single_eq_of_ne' hij] at this
      congr
      exact CommAlgCat.hom_ext (AlgHom.ext fun a ↦ by simpa using h' (Pi.single i a))
    · intro z
      change CommAlgCat.of R (Π j, (f j).unop) ⟶ CommAlgCat.of R Ω at z
      have hD : ∀ e : Ω, IsIdempotentElem e → e = 0 ∨ e = 1 :=
        fun e he ↦ IsIdempotentElem.iff_eq_zero_or_one.mp he
      obtain ⟨i, hi⟩ := exists_single_one hD z.hom.toRingHom
      let x : ((f i).unop : Type u) →ₐ[R] Ω :=
        { toFun := fun a ↦ z.hom (Pi.single i a)
          map_one' := hi
          map_mul' := fun a b ↦ by rw [← map_mul, ← Pi.single_mul]
          map_zero' := by simp
          map_add' := fun a b ↦ by rw [← map_add, ← Pi.single_add]
          commutes' := fun r ↦ by
            have : (Pi.single i (algebraMap R _ r) : Π j, (f j).unop) =
                algebraMap R _ r * Pi.single i 1 := by
              ext j
              by_cases hj : j = i
              · subst hj; simp
              · simp [hj]
            simp only [this, map_mul, AlgHom.commutes]
            erw [hi]
            rw [mul_one] }
      refine ⟨⟨i, CommAlgCat.ofHom x⟩, ?_⟩
      change CommAlgCat.ofHom (Pi.evalAlgHom R (fun j ↦ (f j).unop) i) ≫ CommAlgCat.ofHom x = z
      ext a
      exact (apply_eq_apply_single_of_single_one z.hom.toRingHom hi a).symm
  exact preservesColimitsOfShape_of_discrete _

/-- `Hom_R(-, Ω)` sends invariants under a finite group to orbit sets (`Ω` algebraically
closed). -/
instance preservesColimitsOfShape_singleObj_yoneda [IsAlgClosed Ω] (G : Type u) [Group G]
    [Finite G] : PreservesColimitsOfShape (SingleObj G) (yoneda.obj (CommAlgCat.of R Ω)) where
  preservesColimit {K} := by
    let c : Cocone K := coconeOfConeLeftOp (CommAlgCatLimits.fixedCone K.leftOp)
    have hc : IsColimit c :=
      isColimitCoconeOfConeLeftOp K (CommAlgCatLimits.fixedConeIsLimit K.leftOp)
    refine preservesColimit_of_preserves_colimit_cocone hc (Nonempty.some ?_)
    let _ : MulSemiringAction G (K.obj (SingleObj.star G)).unop :=
      CommAlgCatLimits.fixedAction K.leftOp
    have : SMulCommClass G R (K.obj (SingleObj.star G)).unop :=
      CommAlgCatLimits.fixedAction_smulCommClass K.leftOp
    have h_eq : CommAlgCatLimits.fixedSubalgebra K.leftOp =
        FixedPoints.subalgebra R (K.obj (SingleObj.star G)).unop G :=
      CommAlgCatLimits.fixedSubalgebra_eq K.leftOp
    apply nonempty_isColimit_singleObj
    · intro z
      obtain ⟨x, hx⟩ := exists_comp_val_eq_of_fixedPoints G
        (z.hom.comp (Subalgebra.equivOfEq _ _ h_eq.symm).toAlgHom)
      refine ⟨CommAlgCat.ofHom x, CommAlgCat.hom_ext (AlgHom.ext fun b ↦ ?_)⟩
      exact congr($hx ⟨b.1, h_eq ▸ b.2⟩)
    · intro x y h
      have h' : x.hom.comp (FixedPoints.subalgebra R _ G).val =
          y.hom.comp (FixedPoints.subalgebra R _ G).val := by
        ext ⟨a, ha⟩
        exact congr($(h).hom ⟨a, h_eq ▸ ha⟩)
      obtain ⟨g, hg⟩ := exists_eq_comp_smul_of_comp_val_eq G x.hom y.hom h'
      refine ⟨g⁻¹, CommAlgCat.hom_ext (AlgHom.ext fun a ↦ ?_)⟩
      exact (hg a).symm

end YonedaColimits

section Fiber

variable (R : Type u) [CommRing R] (Ω : Type u) [Field Ω] [Algebra R Ω]

open CommAlgCat

/-- The fiber functor `S ↦ Hom_R(S, Ω)` at the geometric point `R → Ω` (mathlib's
`CommAlgCat.FiniteEtale.fiber`), with universes fixed. -/
abbrev fiberFunctor : (FiniteEtale.{u} R)ᵒᵖ ⥤ FintypeCat.{u} := FiniteEtale.fiber R Ω

/-- The fiber functor, followed by the inclusion into types, is the restriction of the functor
corepresented by `Ω` on `R`-algebras. -/
noncomputable def fiberInclIso :
    fiberFunctor R Ω ⋙ FintypeCat.incl ≅
      (CommAlgCat.finiteEtale.{u} R).ι.op ⋙ yoneda.obj (CommAlgCat.of R Ω) :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun := fun x ↦ CommAlgCat.ofHom x
      invFun := fun x ↦ x.hom
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl })
    (fun _ ↦ rfl)

lemma preservesLimitsOfShape_fiber (J : Type*) [Category* J]
    [PreservesColimitsOfShape Jᵒᵖ (CommAlgCat.finiteEtale.{u} R).ι] :
    PreservesLimitsOfShape J (fiberFunctor R Ω) := by
  have := preservesLimitsOfShape_op J (CommAlgCat.finiteEtale.{u} R).ι
  have : PreservesLimitsOfShape J
      ((CommAlgCat.finiteEtale.{u} R).ι.op ⋙ yoneda.obj (CommAlgCat.of R Ω)) :=
    comp_preservesLimitsOfShape _ _
  have : PreservesLimitsOfShape J (fiberFunctor R Ω ⋙ FintypeCat.incl) :=
    preservesLimitsOfShape_of_natIso (fiberInclIso R Ω).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves (F := fiberFunctor R Ω)
    (G := FintypeCat.incl)

lemma preservesColimitsOfShape_fiber (J : Type*) [Category* J]
    [PreservesLimitsOfShape Jᵒᵖ (CommAlgCat.finiteEtale.{u} R).ι]
    [PreservesColimitsOfShape J (yoneda.obj (CommAlgCat.of R Ω))] :
    PreservesColimitsOfShape J (fiberFunctor R Ω) := by
  have := preservesColimitsOfShape_op J (CommAlgCat.finiteEtale.{u} R).ι
  have : PreservesColimitsOfShape J
      ((CommAlgCat.finiteEtale.{u} R).ι.op ⋙ yoneda.obj (CommAlgCat.of R Ω)) :=
    comp_preservesColimitsOfShape _ _
  have : PreservesColimitsOfShape J (fiberFunctor R Ω ⋙ FintypeCat.incl) :=
    preservesColimitsOfShape_of_natIso (fiberInclIso R Ω).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves (F := fiberFunctor R Ω)
    (G := FintypeCat.incl)

example : PreservesLimitsOfShape WalkingCospan (fiberFunctor R Ω) :=
  preservesLimitsOfShape_fiber R Ω _

example : PreservesLimitsOfShape (Discrete PEmpty.{1}) (fiberFunctor R Ω) :=
  preservesLimitsOfShape_fiber R Ω _

end Fiber

section Algebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- If `φ : B → A` is surjective with kernel generated by an idempotent `e`, then
`B ≅ A × B/(1 - e)`. -/
lemma bijective_prod_mk_of_ker_eq (φ : B →ₐ[R] A) (hφ : Function.Surjective φ) {e : B}
    (he : IsIdempotentElem e) (hker : RingHom.ker φ = Ideal.span {e}) :
    Function.Bijective (φ.prod (Ideal.Quotient.mkₐ R (Ideal.span {1 - e}))) := by
  have hφe : φ e = 0 := by
    change e ∈ RingHom.ker φ
    rw [hker]
    exact Ideal.mem_span_singleton_self e
  refine ⟨fun b b' h ↦ ?_, fun ⟨a, q⟩ ↦ ?_⟩
  · simp only [AlgHom.prod_apply, Prod.mk.injEq, Ideal.Quotient.mkₐ_eq_mk] at h
    rw [← sub_eq_zero]
    have h₁ : b - b' ∈ Ideal.span {e} := by
      rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
      exact h.1
    have h₂ : b - b' ∈ Ideal.span {1 - e} := by
      rw [← Ideal.Quotient.eq]
      exact h.2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h₁
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h₂
    have : b - b' = (b - b') * e := by rw [← hc, mul_assoc, he.eq]
    rw [this, ← hd]
    linear_combination (-d) * he.eq
  · obtain ⟨b₁, rfl⟩ := hφ a
    obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨(1 - e) * b₁ + e * b₂, Prod.ext ?_ ?_⟩
    · simp [hφe]
    · change Ideal.Quotient.mk _ ((1 - e) * b₁ + e * b₂) = Ideal.Quotient.mk _ b₂
      rw [Ideal.Quotient.eq]
      exact Ideal.mem_span_singleton.mpr ⟨b₁ - b₂, by ring⟩

end Algebra

section Galois

variable (R : Type u) [CommRing R]

open CommAlgCat PreGaloisCategory

/-- V.3.5, V.3.6 (affine): an epimorphism of finite étale `R`-algebras is surjective. -/
lemma surjective_of_epi {A B : FiniteEtale.{u} R} (φ : B ⟶ A) [Epi φ] :
    Function.Surjective φ.hom.hom := by
  let _ := φ.hom.hom.toRingHom.toAlgebra
  have : IsScalarTower R B A := .of_algebraMap_eq' φ.hom.hom.comp_algebraMap.symm
  have : Algebra.Etale B A := .of_restrictScalars R B A
  have : Module.Finite B A := .of_restrictScalars_finite R B A
  obtain ⟨h₁, h₂⟩ := finite_etale_tensorProduct (R := R) (B := B) (A := A) (C := A)
  let T : FiniteEtale.{u} R := ⟨CommAlgCat.of R (A ⊗[B] A), ⟨h₁, h₂⟩⟩
  let inl : A ⟶ T := ObjectProperty.homMk (CommAlgCat.ofHom Algebra.TensorProduct.includeLeft)
  let inr : A ⟶ T := ObjectProperty.homMk
    (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight.restrictScalars R))
  have hw : φ ≫ inl = φ ≫ inr := by
    ext b
    change φ.hom b ⊗ₜ[B] (1 : A) = (1 : A) ⊗ₜ[B] φ.hom b
    rw [show φ.hom b = algebraMap B A b from rfl, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have h := (cancel_epi φ).mp hw
  exact surjective_algebraMap_of_tmul_eq (A := B) (B := A) fun a ↦ congr($(h).hom.hom a)

/-- V.4 (G 3) for finite étale algebras: an epimorphism `B → A` of finite étale algebras
identifies `B` with a product `A × Z`. In the opposite category: every monomorphism is the
inclusion of a direct summand. -/
lemma monoInducesIsoOnDirectSummand {X Y : (FiniteEtale.{u} R)ᵒᵖ} (i : X ⟶ Y) [Mono i] :
    ∃ (Z : (FiniteEtale.{u} R)ᵒᵖ) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  have hsurj := surjective_of_epi R i.unop
  obtain ⟨e, he, hker⟩ := exists_isIdempotentElem_ker_eq i.unop.hom.hom hsurj
  obtain ⟨h₁, h₂⟩ := finite_etale_quotient_one_sub (R := R) (T := Y.unop) he
  let Z : FiniteEtale.{u} R := ⟨CommAlgCat.of R (Y.unop ⧸ Ideal.span {1 - e}), ⟨h₁, h₂⟩⟩
  let π : Y.unop ⟶ Z := ObjectProperty.homMk (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R _))
  let E := AlgEquiv.ofBijective _ (bijective_prod_mk_of_ker_eq i.unop.hom.hom hsurj he hker)
  have hE : ∀ y, E y = (i.unop.hom y, Ideal.Quotient.mk _ y) := fun _ ↦ rfl
  have hlim : IsLimit (BinaryFan.mk i.unop π) := BinaryFan.isLimitMk
    (fun s ↦ ObjectProperty.homMk (CommAlgCat.ofHom
      (E.symm.toAlgHom.comp (s.fst.hom.hom.prod s.snd.hom.hom))))
    (fun s ↦ by
      ext d
      exact congr_arg Prod.fst (E.apply_symm_apply (s.fst.hom d, s.snd.hom d)))
    (fun s ↦ by
      ext d
      exact congr_arg Prod.snd (E.apply_symm_apply (s.fst.hom d, s.snd.hom d)))
    (fun s m h₁ h₂ ↦ by
      ext d
      apply E.injective
      change E (m.hom d) = E (E.symm (s.fst.hom d, s.snd.hom d))
      rw [AlgEquiv.apply_symm_apply, hE]
      exact Prod.ext congr($(h₁).hom.hom d) congr($(h₂).hom.hom d))
  exact ⟨Opposite.op Z, π.op, ⟨BinaryFan.IsLimit.op hlim⟩⟩

variable [ConnectedSpace (PrimeSpectrum R)]

/-- V.7 (G 1)–(G 3) for an affine connected base: the opposite of the category of finite étale
`R`-algebras (the category of finite étale coverings of `Spec R`) is a pre-Galois category. -/
instance preGaloisCategory : PreGaloisCategory (FiniteEtale.{u} R)ᵒᵖ where
  hasQuotientsByFiniteGroups G _ _ := inferInstance
  monoInducesIsoOnDirectSummand i _ := monoInducesIsoOnDirectSummand R i

variable (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]

omit [ConnectedSpace (PrimeSpectrum R)] in
/-- V.7 (G 5), epimorphisms: the fiber functor sends epimorphisms of coverings (monomorphisms of
algebras) to surjections. -/
lemma fiberFunctor_preservesEpimorphisms : (fiberFunctor R Ω).PreservesEpimorphisms where
  preserves {X Y} f _ := by
    let φ := f.unop.hom.hom
    have hcancel : ∀ u₁ u₂ : (Fin 2 → Y.unop) →ₐ[R] Y.unop, φ.comp u₁ = φ.comp u₂ → u₁ = u₂ := by
      intro u₁ u₂ h
      let W : FiniteEtale.{u} R := FiniteEtale.of R (Fin 2 → Y.unop)
      let v₁ : W ⟶ Y.unop := ObjectProperty.homMk (CommAlgCat.ofHom u₁)
      let v₂ : W ⟶ Y.unop := ObjectProperty.homMk (CommAlgCat.ofHom u₂)
      have : v₁ ≫ f.unop = v₂ ≫ f.unop := by
        ext x
        exact congr($h x)
      have h' := (cancel_mono f.unop).mp this
      ext x
      exact congr($(h').hom.hom x)
    have hspec := comap_surjective_of_cancel φ hcancel
    let _ := φ.toRingHom.toAlgebra
    have : Module.Finite Y.unop X.unop := .of_restrictScalars_finite R Y.unop X.unop
    have hsurj : Function.Surjective ((fiberFunctor R Ω).map f) := by
      intro y
      obtain ⟨x, hx⟩ := exists_lift_of_isIntegral_of_surjective hspec y.toRingHom
      refine ⟨{ x with commutes' := fun r ↦ ?_ }, AlgHom.ext fun b ↦ congr($hx b)⟩
      have h1 : algebraMap R X.unop r = φ (algebraMap R Y.unop r) := (φ.commutes r).symm
      change x (algebraMap R X.unop r) = _
      rw [h1]
      exact (congr($hx (algebraMap R Y.unop r))).trans (y.commutes r)
    have : Epi (FintypeCat.incl.map ((fiberFunctor R Ω).map f)) :=
      (epi_iff_surjective _).mpr hsurj
    exact FintypeCat.incl.epi_of_epi_map this

/-- V.3.7 (affine) = (G 6): the fiber functor reflects isomorphisms. -/
lemma fiberFunctor_reflectsIsomorphisms : (fiberFunctor R Ω).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    have hb : Function.Bijective ((fiberFunctor R Ω).map f) :=
      (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
    have hφ := bijective_of_bijective_comp Ω f.unop.hom.hom hb
    let e := AlgEquiv.ofBijective _ hφ
    have : IsIso f.unop := by
      have : (FiniteEtale.isoMk e).hom = f.unop := rfl
      rw [← this]
      infer_instance
    exact (isIso_unop_iff f).mp this

/-- V.7 (G 4)–(G 6) for an affine connected base: `S ↦ Hom_R(S, Ω)` is a fiber functor when
`Ω` is algebraically closed (see `fiberFunctor_fiberFunctor` for separably closed `Ω`). -/
lemma fiberFunctor_of_isAlgClosed : FiberFunctor (fiberFunctor R Ω) where
  preservesTerminalObjects := preservesLimitsOfShape_fiber R Ω _
  preservesPullbacks := preservesLimitsOfShape_fiber R Ω _
  preservesFiniteCoproducts := ⟨fun _ ↦ preservesColimitsOfShape_fiber R Ω _⟩
  preservesEpis := fiberFunctor_preservesEpimorphisms R Ω
  preservesQuotientsByFiniteGroups _ _ _ := preservesColimitsOfShape_fiber R Ω _
  reflectsIsos := fiberFunctor_reflectsIsomorphisms R Ω

end Galois

section FiberFunctorOfIso

open PreGaloisCategory

variable {C : Type*} [Category* C] [PreGaloisCategory C]

/-- A functor isomorphic to a fiber functor is a fiber functor. -/
lemma fiberFunctor_of_iso {F G : C ⥤ FintypeCat.{u}} [FiberFunctor F] (e : F ≅ G) :
    FiberFunctor G where
  preservesTerminalObjects := preservesLimitsOfShape_of_natIso e
  preservesPullbacks := preservesLimitsOfShape_of_natIso e
  preservesFiniteCoproducts := ⟨fun _ ↦ preservesColimitsOfShape_of_natIso e⟩
  preservesEpis := Functor.PreservesEpimorphisms.ofRetract ⟨e.inv, e.hom, e.inv_hom_id⟩
  preservesQuotientsByFiniteGroups _ _ _ := preservesColimitsOfShape_of_natIso e
  reflectsIsos := reflectsIsomorphisms_of_iso e

end FiberFunctorOfIso

section SepClosed

variable (R : Type u) [CommRing R] (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]

open CommAlgCat PreGaloisCategory

/-- For `Ω` separably closed, the geometric points with values in `Ω` and in an algebraic
closure of `Ω` agree. -/
noncomputable def fiberFunctorAlgebraicClosureIso :
    fiberFunctor R Ω ≅ fiberFunctor R (AlgebraicClosure Ω) :=
  let ι : Ω →ₐ[R] AlgebraicClosure Ω := IsScalarTower.toAlgHom R Ω (AlgebraicClosure Ω)
  have hι : Function.Injective ι := (algebraMap Ω (AlgebraicClosure Ω)).injective
  have key (w : ι.range) : ι ((AlgEquiv.ofInjective ι hι).symm w) = w :=
    congr_arg Subtype.val ((AlgEquiv.ofInjective ι hι).apply_symm_apply w)
  NatIso.ofComponents (fun A ↦ FintypeCat.equivEquivIso
    { toFun := fun (x : A.unop →ₐ[R] Ω) ↦ ι.comp x
      invFun := fun (y : A.unop →ₐ[R] AlgebraicClosure Ω) ↦
        (AlgEquiv.ofInjective ι hι).symm.toAlgHom.comp
        (y.codRestrict ι.range fun a ↦ by
          obtain ⟨b, hb⟩ := algHom_apply_mem_range_of_isSepClosed Ω (AlgebraicClosure Ω) y a
          exact ⟨b, hb⟩)
      left_inv := fun (x : A.unop →ₐ[R] Ω) ↦ AlgHom.ext fun a ↦ by
        apply hι
        exact key _
      right_inv := fun (y : A.unop →ₐ[R] AlgebraicClosure Ω) ↦ AlgHom.ext fun a ↦ by
        exact key _ })
    (fun _ ↦ rfl)

variable [ConnectedSpace (PrimeSpectrum R)]

/-- V.7 (G 4)–(G 6) for an affine connected base: for a geometric point `R → Ω` (`Ω`
separably closed), `S ↦ Hom_R(S, Ω)` is a fiber functor. -/
instance fiberFunctor_fiberFunctor : FiberFunctor (fiberFunctor R Ω) :=
  have := fiberFunctor_of_isAlgClosed R (AlgebraicClosure Ω)
  fiberFunctor_of_iso (fiberFunctorAlgebraicClosureIso R Ω).symm

/-- V.7: the category of finite étale coverings of `Spec R` (`Spec R` connected) is a Galois
category. -/
instance galoisCategory : GaloisCategory (FiniteEtale.{u} R)ᵒᵖ where
  hasFiberFunctor := ⟨fiberFunctor R
    (AlgebraicClosure (Classical.arbitrary (PrimeSpectrum R)).asIdeal.ResidueField),
    inferInstance⟩

end SepClosed

section FundamentalGroup

variable (R : Type u) [CommRing R] [ConnectedSpace (PrimeSpectrum R)]
  (Ω : Type u) [Field Ω] [IsSepClosed Ω] [Algebra R Ω]

open CommAlgCat PreGaloisCategory

open scoped FintypeCatDiscrete

/-- V.7: the fundamental group `π₁(Spec R, a)` of a connected affine scheme at the geometric
point `a : Spec Ω → Spec R`, defined as the automorphism group of the fiber functor. It is a
profinite group (compact, Hausdorff, totally disconnected topological group). -/
abbrev fundamentalGroup := Aut (fiberFunctor R Ω)

example : IsTopologicalGroup (fundamentalGroup R Ω) := inferInstance
example : CompactSpace (fundamentalGroup R Ω) := inferInstance
example : T2Space (fundamentalGroup R Ω) := inferInstance
example : TotallyDisconnectedSpace (fundamentalGroup R Ω) := inferInstance

/-- V.7: the fiber functor defines an equivalence between the category of finite étale
coverings of `Spec R` and the category of finite sets with a continuous action of
`π₁(Spec R, a)`. -/
noncomputable def equivContAction :
    (FiniteEtale.{u} R)ᵒᵖ ≌ ContAction FintypeCat (fundamentalGroup R Ω) :=
  (functorToContAction (fiberFunctor R Ω)).asEquivalence

/-- V.7: the number of geometric points of an étale covering over `a` is its degree, the rank
of the corresponding finite étale algebra (at any point, `Spec R` being connected). -/
lemma card_fiber_eq_rankAtStalk (A : FiniteEtale.{u} R) (p : PrimeSpectrum R) :
    Nat.card ((fiberFunctor R Ω).obj (Opposite.op A)) = Module.rankAtStalk (R := R) A p := by
  rw [← rankAtStalk_eq_of_preconnected (A := A) (geomPointImage Ω) p]
  exact card_algHom_eq_rankAtStalk (R := R) (A := A) Ω

lemma nonempty_fiber_iff (A : FiniteEtale.{u} R) :
    Nonempty ((fiberFunctor R Ω).obj (Opposite.op A)) ↔ Nontrivial A := by
  refine ⟨fun ⟨x⟩ ↦ ?_, fun _ ↦ nonempty_algHom_of_nontrivial (R := R) (A := A) Ω⟩
  let x' : A →ₐ[R] Ω := x
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have : x' 1 = x' 0 := congr_arg x' (Subsingleton.elim _ _)
  simp at this

/-- V.7: an étale covering is connected in the Galois category if and only if it is
topologically connected, i.e. its algebra is nonzero and has no idempotents other than `0`
and `1`. -/
theorem isConnected_op_iff (A : FiniteEtale.{u} R) :
    IsConnected (Opposite.op A) ↔ Nontrivial A ∧ ∀ e : A, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  let Ω' := AlgebraicClosure (Classical.arbitrary (PrimeSpectrum R)).asIdeal.ResidueField
  have hinit : ∀ X : (FiniteEtale.{u} R)ᵒᵖ, (IsInitial X → False) ↔ Nontrivial X.unop :=
    fun X ↦ (not_initial_iff_fiber_nonempty (fiberFunctor R Ω') X).trans
      (nonempty_fiber_iff R Ω' X.unop)
  constructor
  · intro h
    have hA : Nontrivial A := (hinit _).mp h.notInitial
    refine ⟨hA, fun e he ↦ ?_⟩
    by_contra! hne
    obtain ⟨h₁, h₂⟩ := finite_etale_quotient_one_sub (R := R) (T := A) he
    have hZ := nontrivial_quotient_one_sub he hne.1
    let Z : FiniteEtale.{u} R := ⟨CommAlgCat.of R (A ⧸ Ideal.span {1 - e}), ⟨h₁, h₂⟩⟩
    let π : A ⟶ Z := ObjectProperty.homMk (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R _))
    have : Epi π := ⟨fun g₁ g₂ hg ↦ by
      ext z
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact congr($(hg).hom.hom a)⟩
    have hiso : IsIso π.op := h.noTrivialComponent (Opposite.op Z) π.op ((hinit _).mpr hZ)
    have : IsIso π := (isIso_op_iff π).mp hiso
    have hinj : Function.Injective π.hom.hom :=
      ((ConcreteCategory.isIso_iff_bijective ((ObjectProperty.ι _).map π)).mp inferInstance).1
    apply hne.2
    have : 1 - e = 0 := hinj (by
      change Ideal.Quotient.mk _ (1 - e) = Ideal.Quotient.mk _ 0
      rw [Ideal.Quotient.eq, sub_zero]
      exact Ideal.mem_span_singleton_self _)
    exact (sub_eq_zero.mp this).symm
  · rintro ⟨hA, hid⟩
    refine ⟨(hinit _).mpr hA, fun Y i _ hY ↦ ?_⟩
    have hsurj := surjective_of_epi R i.unop
    obtain ⟨e, he, hker⟩ := exists_isIdempotentElem_ker_eq i.unop.hom.hom hsurj
    have hY' : Nontrivial Y.unop := (hinit _).mp hY
    rcases hid e he with rfl | rfl
    · have hinj : Function.Injective i.unop.hom.hom := by
        rw [injective_iff_map_eq_zero]
        intro a ha
        have : a ∈ RingHom.ker i.unop.hom.hom := ha
        rwa [hker, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at this
      let E := AlgEquiv.ofBijective _ ⟨hinj, hsurj⟩
      have : IsIso i.unop := by
        have : (FiniteEtale.isoMk E).hom = i.unop := rfl
        rw [← this]
        infer_instance
      exact (isIso_unop_iff i).mp this
    · exfalso
      have : (1 : A) ∈ RingHom.ker i.unop.hom.hom := by
        rw [hker]
        exact Ideal.mem_span_singleton_self _
      simp at this

/-- V.7: an étale covering of `Spec R` is connected in the Galois category if and only if it is
connected as a topological space. -/
theorem isConnected_op_iff_connectedSpace (A : FiniteEtale.{u} R) :
    IsConnected (Opposite.op A) ↔ ConnectedSpace (PrimeSpectrum A) :=
  (isConnected_op_iff R A).trans (connectedSpace_primeSpectrum_iff A).symm

end FundamentalGroup

end SGA.SGA1.ExposeV
