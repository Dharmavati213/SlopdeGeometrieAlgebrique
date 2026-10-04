/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.GroupScheme.MulNCotangent
import SGA.SGA1.ExposeI.DominantUnramified
import SGA.SGA1.ExposeII.Field
import SGA.SGA1.ExposeXI.AbelianVarietyIsogeny

/-!
# SGA 1, Exposé XI.2: `n_A` is étale for `n` invertible, and XI.2.1 in characteristic `0`

Proof of `MulNEtaleStatement` (in `TateModule`): for `n` invertible in `k`, multiplication by `n`
on an abelian variety is étale (`etale_mulN`), through I.9.11
(`ExposeI.etale_of_dominant_of_formallyUnramified`; `A` is normal, being smooth over `k`).
Ingredients:

* `isDominant_of_injective_stalkMap`: an endomorphism of an irreducible scheme which fixes a point
  `x` with `𝒪_x` a domain and is injective on `𝒪_x` fixes the generic point, hence is dominant.
  For `n_A` with `n` invertible the injectivity is `GroupScheme.injective_stalkEnd_pow`, so
  `n_A` is dominant (`isDominant_mulN`);
* `formallyUnramified_stalkMap_mulN_origin`: `n_A` is unramified at the origin, since it maps
  `𝔪` onto generators of `𝔪` (`GroupScheme.map_maximalIdeal_stalkEnd_pow`, the cotangent
  computation) and is compatible with the `k`-structures;
* `formallyUnramified_mulN`: translating by `k`-points (`τ_x ∘ n_A = n_A ∘ τ_{xⁿ}`), `n_A` is
  unramified at every closed point, hence everywhere (`A` is a Jacobson space).

Hence `n_A` is an isogeny for `n` invertible (`mulNIsogeny_of_ne_zero`), and the covering `n_A`
itself realises `K_n` faithfully, which gives XI.2.1 in characteristic `0`
(`exists_tateModule_equiv_of_charZero`). In characteristic `p > 0`, `p_A` is not étale (if
`dim A > 0`); that case is in `AbelianVarietyQuotient`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Topology MonoidalCategory CartesianMonoidalCategory

namespace SGA.SGA1.ExposeXI

/-- An endomorphism `f` of an irreducible scheme fixing a point `x` such that `𝒪_x` is a domain
and `f^♯ : 𝒪_{f x} → 𝒪_x` is injective maps the generic point to itself; in particular it is
dominant. -/
theorem isDominant_of_injective_stalkMap {X : Scheme.{u}} [IrreducibleSpace X] (f : X ⟶ X)
    {x : X} (hx : f x = x) [IsDomain (X.presheaf.stalk x)]
    (hinj : Function.Injective (f.stalkMap x).hom) : IsDominant f := by
  have : IsDomain (X.presheaf.stalk (f x)) := by rw [hx]; infer_instance
  let ξ := genericPoint X
  -- the image of the prime `0` of `𝒪_y` is the generic point, for `y = x` and `y = f x`
  -- (this is `ExposeI.fromSpecStalk_bot`, in `ExposeI/GeometricPoints`, which pulls in VIII's
  -- descent; not imported here)
  have hgen (y : X) [IsDomain (X.presheaf.stalk y)] :
      X.fromSpecStalk y ⟨⊥, Ideal.isPrime_bot⟩ = ξ :=
    ((ExposeI.specializes_of_isDomain_stalk ((genericPoint_spec X).specializes trivial)).antisymm
      ((genericPoint_spec X).specializes trivial)).eq
  have hcomm := congrArg (fun g : Spec (X.presheaf.stalk x) ⟶ X ↦ g ⟨⊥, Ideal.isPrime_bot⟩)
    (Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x))
  change X.fromSpecStalk (f x) (Spec.map (f.stalkMap x) ⟨⊥, Ideal.isPrime_bot⟩) =
    f (X.fromSpecStalk x ⟨⊥, Ideal.isPrime_bot⟩) at hcomm
  have hbot : (Spec.map (f.stalkMap x) ⟨⊥, Ideal.isPrime_bot⟩ : Spec (X.presheaf.stalk (f x))) =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk (f x))) :=
    PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hinj)
  rw [hbot, hgen, hgen] at hcomm
  refine ⟨?_⟩
  have hξ : ξ ∈ Set.range f := ⟨ξ, hcomm.symm⟩
  rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro z
  exact closure_mono (Set.singleton_subset_iff.mpr hξ) ((genericPoint_spec X).specializes
    trivial).mem_closure

open MonObj in
/-- Multiplication by `n` on a smooth connected monoid scheme over a field is dominant when `n` is
invertible in the field: its stalk map at the origin is injective
(`GroupScheme.injective_stalkEnd_pow`). -/
theorem isDominant_mulN {k : Type u} [Field k] (A : Over (Spec (.of k))) [MonObj A]
    [Smooth A.hom] [ConnectedSpace A.left] {n : ℕ} (hn : (n : k) ≠ 0) :
    IsDominant (mulN A n).left := by
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsIntegral A.left := ExposeX.isIntegral_of_isRegularScheme
    (ExposeII.isRegularLocalRing_stalk_of_smooth_field k A.hom)
  have hx := GroupScheme.origin_comp_closedPoint (A := A) ((𝟙 A) ^ n) GroupScheme.eta_comp_pow
  have hinj := GroupScheme.injective_stalkEnd_pow A hn
  rw [GroupScheme.stalkEnd, CommRingCat.hom_comp, RingHom.coe_comp] at hinj
  exact isDominant_of_injective_stalkMap ((𝟙 A) ^ n).left hx
    ((Function.Injective.of_comp_iff' _ (ConcreteCategory.bijective_of_isIso _)).mp hinj)

section Unramified

open IsLocalRing GroupScheme

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [MonObj A]

open MonObj in
/-- Multiplication by `n` is unramified at the origin when `n` is invertible in `k`. -/
theorem formallyUnramified_stalkMap_mulN_origin [LocallyOfFiniteType A.hom] {n : ℕ}
    (hn : (n : k) ≠ 0) :
    ((mulN A n).left.stalkMap (originPt A)).hom.FormallyUnramified := by
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  set f := (mulN A n).left with hf
  set x₀ := originPt A
  set g := f.stalkMap x₀ with hg
  have hx : f x₀ = x₀ := origin_comp_closedPoint (A := A) ((𝟙 A) ^ n) eta_comp_pow
  -- `g` maps `𝔪_{f x₀}` onto generators of `𝔪_{x₀}`
  have hmap : Ideal.map g.hom (maximalIdeal (A.left.presheaf.stalk (f x₀))) =
      maximalIdeal (A.left.presheaf.stalk x₀) := by
    have h₁ := map_maximalIdeal_stalkEnd_pow A hn
    rw [stalkEnd, CommRingCat.hom_comp, ← Ideal.map_map,
      map_maximalIdeal_of_surjective _ (ConcreteCategory.bijective_of_isIso _).2] at h₁
    exact h₁
  -- `g` is compatible with the `k`-structures, modulo `𝔪_{x₀}`
  let res : A.left.presheaf.stalk x₀ ⟶
      CommRingCat.of (ResidueField (A.left.presheaf.stalk x₀)) :=
    CommRingCat.ofHom (residue (A.left.presheaf.stalk x₀))
  have hcompat : A.hom.stalkAlgebraMap (f x₀) ≫ g ≫ res = originAlgebraMap A ≫ res := by
    rw [← Spec.map_inj, ← Scheme.specPt_comp_eq_specMap, ← Scheme.specPt_comp, Category.assoc,
      Over.w, specPt_comp_hom]
  have : LocallyOfFiniteType (f ≫ A.hom) := by rw [hf, Over.w]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f A.hom
  have h₃ := LocallyOfFiniteType.stalkMap f x₀
  algebraize [g.hom]
  have : IsLocalHom (algebraMap (A.left.presheaf.stalk (f x₀)) (A.left.presheaf.stalk x₀)) :=
    inferInstanceAs (IsLocalHom g.hom)
  have hsurj : Function.Surjective (algebraMap (ResidueField (A.left.presheaf.stalk (f x₀)))
      (ResidueField (A.left.presheaf.stalk x₀))) := by
    intro z
    obtain ⟨r, rfl⟩ := residue_surjective z
    refine ⟨residue _ ((A.hom.stalkAlgebraMap (f x₀)).hom ((evalOrigin A).hom r)), ?_⟩
    rw [ResidueField.algebraMap_residue]
    have h₂ := congrArg (fun φ ↦ φ.hom ((evalOrigin A).hom r)) hcompat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, res] at h₂
    refine h₂.trans ?_
    exact ((Ideal.Quotient.eq).mpr (sub_originAlgebraMap_mem A r)).symm
  have : Algebra.IsSeparable (ResidueField (A.left.presheaf.stalk (f x₀)))
      (ResidueField (A.left.presheaf.stalk x₀)) := by
    let e := AlgEquiv.ofBijective (Algebra.ofId (ResidueField (A.left.presheaf.stalk (f x₀)))
      (ResidueField (A.left.presheaf.stalk x₀))) ⟨RingHom.injective _, hsurj⟩
    exact Algebra.IsSeparable.of_algHom (E' := ResidueField (A.left.presheaf.stalk (f x₀)))
      (f := e.symm.toAlgHom)
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hmap

end Unramified

section Translation

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]

open MonObj in
/-- For `n` invertible in `k`, multiplication by `n` on a commutative group scheme which is
smooth and connected over an algebraically closed field is unramified. -/
theorem formallyUnramified_mulN [IsAlgClosed k] [Smooth A.hom] [ConnectedSpace A.left] {n : ℕ}
    (hn : (n : k) ≠ 0) : FormallyUnramified (mulN A n).left := by
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  set f := (mulN A n).left with hf
  have : LocallyOfFiniteType (f ≫ A.hom) := by rw [hf, Over.w]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f A.hom
  have h₀ := formallyUnramified_stalkMap_mulN_origin A hn
  let U : Set A.left := {y | (f.stalkMap y).hom.FormallyUnramified}
  have hU : IsOpen U := ExposeI.isOpen_setOf_formallyUnramified_stalkMap f
  -- every closed point is a translate of the origin
  have hclosed (a : A.left) (ha : a ∈ closedPoints A.left) : a ∈ U := by
    let p := pointOfClosedPoint A.hom a ha
    let x : 𝟙_ (Over (Spec (.of k))) ⟶ A := Over.homMk p (pointOfClosedPoint_comp A.hom a ha)
    have hτ : unitSection A ≫ (GrpObj.mulRight x).hom.left = p := by
      rw [← pointLeft_one, pointLeft_comp_mulRight, _root_.one_mul]
      rfl
    have ha' : (GrpObj.mulRight x).hom.left (GroupScheme.originPt A) = a := by
      change (unitSection A ≫ (GrpObj.mulRight x).hom.left) (IsLocalRing.closedPoint k) = a
      rw [hτ]
      exact pointOfClosedPoint_apply A.hom a ha _
    have : IsIso (GrpObj.mulRight x).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight x).hom))
    have : IsIso (GrpObj.mulRight (x ^ n)).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight (x ^ n)).hom))
    rw [← ha']
    exact Scheme.Hom.formallyUnramified_stalkMap_of_comp_eq
      (congrArg CommaMorphism.left (mulRight_hom_comp_mulN A x n)) h₀
  have hUuniv : U = Set.univ := by
    by_contra hne
    obtain ⟨a, haU, ha⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
      hU.isClosed_compl.isLocallyClosed
    exact haU (hclosed a ha)
  exact HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime
    fun y ↦ (hUuniv ▸ Set.mem_univ y : y ∈ U)

end Translation

section Etale

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left]

/-- A standard fact used in XI.2 (Mumford, *Abelian varieties*, §4, Application 2): for an
abelian variety `A` over an algebraically closed field `k` (here: a commutative group scheme,
proper, smooth and connected over `k`) and `n` invertible in `k`, multiplication by `n` is étale.
It is unramified (its cotangent map at `0` is multiplication by `n`, then translate) and dominant
(injective on `𝒪_{A,0}`), so I.9.11 applies, `A` being normal. -/
theorem etale_mulN {n : ℕ} (hn : (n : k) ≠ 0) : Etale (mulN A n).left := by
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  set f := (mulN A n).left with hf
  have : LocallyOfFiniteType (f ≫ A.hom) := by rw [hf, Over.w]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f A.hom
  have : IsProper (f ≫ A.hom) := by rw [hf, Over.w]; infer_instance
  have : IsProper f := IsProper.of_comp f A.hom
  have : FormallyUnramified f := formallyUnramified_mulN A hn
  have : IsDominant f := isDominant_mulN A hn
  exact ExposeI.etale_of_dominant_of_formallyUnramified f (ExposeX.isNormalScheme_of_isRegularScheme
    (ExposeII.isRegularLocalRing_stalk_of_smooth_field k A.hom))

/-- For `n` invertible in `k`, multiplication by `n` on an abelian variety is an isogeny: finite
(étale and proper, Zariski's main theorem) and surjective (dominant and proper). This is the case
of `MulNIsogenyStatement` with `n` invertible. -/
theorem mulNIsogeny_of_ne_zero {n : ℕ} (hn : (n : k) ≠ 0) :
    IsFinite (mulN A n).left ∧ Surjective (mulN A n).left := by
  have := etale_mulN A hn
  set f := (mulN A n).left with hf
  have : IsProper (f ≫ A.hom) := by rw [hf, Over.w]; infer_instance
  have : IsProper f := IsProper.of_comp f A.hom
  have : IsDominant f := isDominant_mulN A hn
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite f, inferInstance⟩

/-- For `n` invertible in `k`, the étale covering `n_A` itself realises `K_n` faithfully: the
identity of `A` lifts `n_A` through it and is injective on `K_n`. -/
theorem exists_lift_mulN_injective_of_ne_zero {n : ℕ} (hn : (n : k) ≠ 0) :
    ∃ (Y : ExposeV.FEt A.left) (g : A.left ⟶ Y.left), g ≫ Y.hom = (mulN A n).left ∧
      ∀ a b : torsionPoints A n, pointLeft A a ≫ g = pointLeft A b ≫ g → a = b := by
  have := etale_mulN A hn
  have := (mulNIsogeny_of_ne_zero A hn).1
  refine ⟨MorphismProperty.Over.mk ⊤ (mulN A n).left ⟨inferInstance, inferInstance⟩, 𝟙 _,
    Category.id_comp _, fun a b h ↦ Subtype.ext (Over.OverMorphism.ext ?_)⟩
  have h' : pointLeft A a ≫ 𝟙 A.left = pointLeft A b ≫ 𝟙 A.left := h
  rwa [Category.comp_id, Category.comp_id] at h'

end Etale

/-- `MulNEtaleStatement` holds: multiplication by `n` on an abelian variety is étale for `n`
invertible in the base field. -/
theorem mulNEtaleStatement : MulNEtaleStatement.{u} := by
  intro k _ _ A _ _ _ _ n hn
  have := isCommMonObj_of_smooth A
  exact etale_mulN A hn

/-- XI.2.1 in characteristic `0`: for an abelian variety `A` over an algebraically closed field of
characteristic `0`, the canonical map `T(A) → π₁(A, 0)` is an isomorphism of topological groups;
this is the conclusion of `AbelianVarietyFundamentalGroupStatement` for such `A`. -/
theorem exists_tateModule_equiv_of_charZero (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left] :
    haveI := isCommMonObj_of_smooth A
    AbelianVarietyFundamentalGroupConclusion k A := by
  have := isCommMonObj_of_smooth A
  have hn (n : ℕ) (h : 0 < n) : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr h.ne'
  exact exists_tateModule_equiv_of_isogeny k A (fun n h ↦ mulNIsogeny_of_ne_zero A (hn n h))
    fun n ↦ exists_lift_mulN_injective_of_ne_zero A (hn n n.pos)

end SGA.SGA1.ExposeXI
