/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.UnirationalCovers
import SGA.SGA1.ExposeV.FundamentalGroupBasePoint
import SGA.SGA1.ExposeXIII.AffineLinePrimeToP
import SGA.Foundations.Limits.GeometricFiberCard
import Mathlib.FieldTheory.SeparableDegree

/-!
# The order of `π₁` of a unirational variety divides the degree of a parametrization (XI.1.4)

A characteristic-free partial result towards XI.1.4 (Serre): let `X` be a proper normal integral
scheme over an algebraically closed field `k` and `L ⊇ K(X)` a finite extension which is purely
transcendental over `k`, i.e. a dominant, generically finite rational map `ℙʳ ⇢ X` of degree
`m = [L : K(X)]`. Then `#π₁(X, s̄)` divides the separable degree `[L : K(X)]_s`
(`natCard_etaleFundamentalGroup_dvd_finSepDegree`), hence `m`
(`natCard_etaleFundamentalGroup_dvd_finrank`). `π₁(X)` is finite by XI.1.3; the universal
covering `A ⟶ X` has `#π₁` geometric points in each fibre, `[K(A) : K(X)]_s` of them over the
generic point, and its function field embeds in `L` over `K(X)` (step (3) of Serre's proof,
`exists_ringHom_comp_functionFieldHom_eq`).

* the universal covering: in a Galois category with finite `Aut F`, there is a Galois object `A`
  with `#F(A) = #Aut F`, the case `N = ⊥` of `ExposeXIII.exists_isGalois_card_fiber_eq_index`;
* `finSepDegree_eq_of_ringEquiv`: separable degrees are invariant under compatible ring
  isomorphisms;
* `geometricFiberCard_genericPoint_eq_finSepDegree`: for an integral finite étale covering
  `Y ⟶ X`, the number of geometric points over the generic point is `[K(Y) : K(X)]_s`;
* `finSepDegree_functionField_dvd`: `[K(Y) : K(X)]_s` divides `[L : K(X)]_s`;
* `isSimplyConnected_of_isPurelyInseparable`: if `L/K(X)` is purely inseparable, `X` is simply
  connected (complement to the 2003 addendum to XI.1.4 on weakly and strongly unirational
  varieties in characteristic `p`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeXI

section Degree

/-- Separable degrees are invariant under compatible ring isomorphisms of the base and of the
extension: if `j ∘ (F → E) = (F' → E') ∘ i`, then `[E : F]_s = [E' : F']_s`. -/
theorem finSepDegree_eq_of_ringEquiv {F E F' E' : Type*} [Field F] [Field E] [Field F']
    [Field E'] [Algebra F E] [Algebra F' E'] [Algebra.IsAlgebraic F' E'] (i : F ≃+* F')
    (j : E ≃+* E') (h : ∀ x, j (algebraMap F E x) = algebraMap F' E' (i x)) :
    Field.finSepDegree F E = Field.finSepDegree F' E' := by
  let _ : Algebra F F' := i.toRingHom.toAlgebra
  let _ : Algebra F E' := ((algebraMap F' E').comp i.toRingHom).toAlgebra
  have : IsScalarTower F F' E' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let jF : E ≃ₐ[F] E' := { j with commutes' := h }
  let iF : F ≃ₐ[F] F' := { i with commutes' := fun _ ↦ rfl }
  rw [Field.finSepDegree_eq_of_equiv F E E' jF,
    ← Field.finSepDegree_mul_finSepDegree_of_isAlgebraic F F' E',
    ← Field.finSepDegree_eq_of_equiv F F F' iF, Field.finSepDegree_self, one_mul]

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) [IsFinite π] [Etale π]

/-- The only point of an integral finite étale covering `Y` of `X` over the generic point of `X` is
the generic point of `Y`. -/
lemma eq_genericPoint_of_apply_eq (y : Y) (hy : π y = genericPoint X) : y = genericPoint Y :=
  (eq_of_specializes_of_isDiscrete (π.isDiscrete_preimage_singleton (genericPoint X))
    (Set.mem_preimage.mpr (genericPoint_eq_of_isFinite_of_etale π)) (Set.mem_preimage.mpr hy)
    (genericPoint_specializes y)).symm

/-- The geometric number of points of an integral finite étale covering `π : Y ⟶ X` over the
generic point of `X` is the separable degree `[K(Y) : K(X)]_s`. -/
lemma geometricFiberCard_genericPoint_eq_finSepDegree :
    letI := (functionFieldHom π (genericPoint_eq_of_isFinite_of_etale π)).hom.toAlgebra
    π.geometricFiberCard (genericPoint X) =
      Field.finSepDegree X.functionField Y.functionField := by
  have hπ := genericPoint_eq_of_isFinite_of_etale π
  let _ := (functionFieldHom π hπ).hom.toAlgebra
  -- the fibre over the generic point is the generic point
  have h1 : π.geometricFiberCard (genericPoint X) = π.geometricFiberCard (π (genericPoint Y)) := by
    rw [hπ]
  have hsub : ∀ y : π ⁻¹' {π (genericPoint Y)}, y = ⟨genericPoint Y, rfl⟩ :=
    fun y ↦ Subtype.ext (eq_genericPoint_of_apply_eq π y.1 (y.2.trans hπ))
  rw [h1, Scheme.Hom.geometricFiberCard, finsum_eq_single _ ⟨genericPoint Y, rfl⟩
    (fun y hy ↦ (hy (hsub y)).elim)]
  dsimp only
  let _ := (π.residueFieldMap (genericPoint Y)).hom.toAlgebra
  have : FiniteDimensional (X.residueField (π (genericPoint Y)))
      (Y.residueField (genericPoint Y)) := π.finiteDimensional_residueField _
  -- `K(X) ≅ κ(η_X)` and `K(Y) ≅ κ(η_Y)`, compatibly
  have hsp : π (genericPoint Y) ⤳ genericPoint X := by rw [hπ]
  have hsurj : ∀ (x : X) (hx : x = genericPoint X) (h : x ⤳ genericPoint X),
      Function.Surjective (X.presheaf.stalkSpecializes h) := by
    rintro x rfl h
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact Function.surjective_id
  let i : X.functionField ≃+* X.residueField (π (genericPoint Y)) :=
    RingEquiv.ofBijective (X.presheaf.stalkSpecializes hsp ≫ X.residue (π (genericPoint Y))).hom
      ⟨RingHom.injective _, by
        rw [CommRingCat.hom_comp, RingHom.coe_comp]
        exact (X.residue_surjective _).comp (hsurj _ hπ hsp)⟩
  let j : Y.functionField ≃+* Y.residueField (genericPoint Y) :=
    RingEquiv.ofBijective (Y.residue (genericPoint Y)).hom
      ⟨RingHom.injective _, Y.residue_surjective _⟩
  refine (finSepDegree_eq_of_ringEquiv i j fun x ↦ ?_).symm
  have e : (X.presheaf.stalkSpecializes hsp ≫ X.residue (π (genericPoint Y))) ≫
      π.residueFieldMap (genericPoint Y) = functionFieldHom π hπ ≫ Y.residue (genericPoint Y) := by
    rw [Category.assoc, Scheme.residue_residueFieldMap, functionFieldHom, Category.assoc]
  exact (congrArg (fun φ ↦ φ.hom x) e).symm

/-- The geometric number of points of an integral finite étale covering `Y ⟶ X` at the generic
point, the separable degree `[κ(η_Y) : κ(η_X)]_s`, divides the degree `[K(Y) : K(X)]`. -/
lemma geometricFiberCard_genericPoint_dvd_finrank :
    letI := (functionFieldHom π (genericPoint_eq_of_isFinite_of_etale π)).hom.toAlgebra
    π.geometricFiberCard (genericPoint X) ∣ Module.finrank X.functionField Y.functionField := by
  let _ := (functionFieldHom π (genericPoint_eq_of_isFinite_of_etale π)).hom.toAlgebra
  rw [geometricFiberCard_genericPoint_eq_finSepDegree]
  exact Field.finSepDegree_dvd_finrank _ _

end Degree

section Unirational

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The fibre at `s̄` of an étale covering `p : Y ⟶ X` is the set of points of `Y` over `s̄`. -/
noncomputable def fiberEquivPointsOver {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ X)
    (A : ExposeV.FEt X) :
    (ExposeV.FEt.fiber Ω s).obj A ≃ (A.hom : A.left ⟶ X).PointsOver s :=
  (ExposeV.FEt.fiberEquiv Ω s A).trans
    { toFun := fun g ↦ ⟨g.left, Over.w g⟩
      invFun := fun a ↦ Over.homMk a.1 a.2
      left_inv := fun g ↦ by ext; rfl
      right_inv := fun a ↦ rfl }

/-- XI.1.4, step (3) of Serre's proof, separable-degree form: let `X` be a proper integral scheme
over an algebraically closed field `k` and `L ⊇ K(X)` a finite extension which is purely
transcendental over `k`. Then the separable degree `[K(Y) : K(X)]_s` of every integral finite étale
covering `Y` of `X` divides `[L : K(X)]_s` (`K(Y)` embeds in `L` over `K(X)`,
`exists_ringHom_comp_functionFieldHom_eq`). -/
theorem finSepDegree_functionField_dvd {Y : Scheme.{u}} [IsIntegral Y] (π : Y ⟶ X) [IsFinite π]
    [Etale π] (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    (hL : letI : Algebra k L := ((algebraMap X.functionField L).comp (functionFieldMap f)).toAlgebra
      IsPurelyTranscendental k L) :
    letI := (functionFieldHom π (genericPoint_eq_of_isFinite_of_etale π)).hom.toAlgebra
    Field.finSepDegree X.functionField Y.functionField ∣
      Field.finSepDegree X.functionField L := by
  let hπ := genericPoint_eq_of_isFinite_of_etale π
  obtain ⟨φ, hφ⟩ := exists_ringHom_comp_functionFieldHom_eq f π hπ L hL
  let _ := (functionFieldHom π hπ).hom.toAlgebra
  let _ := φ.toAlgebra
  have : IsScalarTower X.functionField Y.functionField L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (DFunLike.congr_fun hφ x).symm
  have : Module.Finite Y.functionField L :=
    Module.Finite.of_restrictScalars_finite X.functionField Y.functionField L
  exact Dvd.intro _
    (Field.finSepDegree_mul_finSepDegree_of_isAlgebraic X.functionField Y.functionField L)

/-- **XI.1.4, partial result** (any characteristic): let `X` be a proper normal integral scheme
over an algebraically closed field `k` and `L ⊇ K(X)` a finite extension which is purely
transcendental over `k` (a dominant generically finite rational map `ℙʳ ⇢ X`). Then the order of
`π₁(X, s̄)` (finite by XI.1.3) divides the separable degree `[L : K(X)]_s`.

The universal covering `A ⟶ X` (a Galois covering with `#F(A) = #π₁`) is integral, `#F(A)` is the
separable degree of `K(A)/K(X)` (`geometricFiberCard_genericPoint_eq_finSepDegree`), and `K(A)`
embeds in `L` over `K(X)` (`finSepDegree_functionField_dvd`). -/
theorem natCard_etaleFundamentalGroup_dvd_finSepDegree (hX : IsNormalScheme X) (L : Type u)
    [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
    (hL : letI : Algebra k L := ((algebraMap X.functionField L).comp (functionFieldMap f)).toAlgebra
      IsPurelyTranscendental k L)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Nat.card (ExposeV.etaleFundamentalGroup Ω s) ∣ Field.finSepDegree X.functionField L := by
  let _ := (functionFieldMap f).toAlgebra
  have hfin : HasFiniteFundamentalGroup X := by
    refine hasFiniteFundamentalGroup_of_isUnirational f hX ⟨L, inferInstance, inferInstance,
      inferInstance, ?_⟩
    exact hL
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  -- move to the geometric point at the generic point
  let Ω' := AlgebraicClosure (X.residueField (genericPoint X))
  let s' : Spec (.of Ω') ⟶ X := ExposeV.geometricPointAt X (genericPoint X)
  have : ConnectedSpace X := hfin.1
  obtain ⟨φ⟩ := ExposeV.etaleFundamentalGroup.nonempty_continuousMulEquiv Ω Ω' s s'
  rw [Nat.card_congr φ.toEquiv]
  have := hfin.2 Ω' s'
  obtain ⟨A, -, hA, hcard⟩ := ExposeXIII.exists_isGalois_card_fiber_eq_index
    (ExposeV.FEt.fiber Ω' s') ⊥ (isOpen_discrete _)
  have : IsGalois A := hA
  rw [← Subgroup.index_bot, ← hcard]
  -- the universal covering `A` is an integral finite étale covering
  have : ConnectedSpace A.left := ExposeV.FEt.connectedSpace_of_isConnected A
  let p : A.left ⟶ X := A.hom
  have : IsFinite p := A.prop.1
  have : Etale p := A.prop.2
  have : IsIntegral A.left :=
    isIntegral_of_etale_of_isNormalScheme (fun x ↦ ⟨inferInstance, hX x⟩) p
  have e : Nat.card (p.PointsOver s') = p.geometricFiberCard (genericPoint X) :=
    p.natCard_pointsOver (genericPoint X)
      (CommRingCat.ofHom (algebraMap (X.residueField (genericPoint X)) Ω'))
      (p.finite_preimage_singleton _)
  calc Nat.card ((ExposeV.FEt.fiber Ω' s').obj A) = Nat.card (p.PointsOver s') :=
        Nat.card_congr (fiberEquivPointsOver s' A)
    _ = p.geometricFiberCard (genericPoint X) := e
    _ = _ := geometricFiberCard_genericPoint_eq_finSepDegree p
    _ ∣ _ := finSepDegree_functionField_dvd f p L hL

/-- **XI.1.4, partial result** (any characteristic): under the hypotheses of
`natCard_etaleFundamentalGroup_dvd_finSepDegree`, the order of `π₁(X, s̄)` divides the degree
`[L : K(X)]` of the parametrization. In particular `X` is simply connected if it has a
parametrization of degree `1` (rational `X`, XI.1.1). -/
theorem natCard_etaleFundamentalGroup_dvd_finrank (hX : IsNormalScheme X) (L : Type u) [Field L]
    [Algebra X.functionField L] [FiniteDimensional X.functionField L]
    (hL : letI : Algebra k L := ((algebraMap X.functionField L).comp (functionFieldMap f)).toAlgebra
      IsPurelyTranscendental k L)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Nat.card (ExposeV.etaleFundamentalGroup Ω s) ∣ Module.finrank X.functionField L :=
  (natCard_etaleFundamentalGroup_dvd_finSepDegree f hX L hL Ω s).trans
    (Field.finSepDegree_dvd_finrank _ _)

/-- **XI.1.4, Remarks (2003 addendum), purely inseparable parametrizations** (any
characteristic): a proper normal integral scheme `X` over an algebraically closed field `k` with a
unirational parametrization `L ⊇ K(X)` such that `L/K(X)` is purely inseparable (`X` is
"purely inseparably unirational", e.g. a normal proper model of a Zariski surface `z^p = g(x, y)`
in characteristic `p`) is
simply connected: `#π₁(X)` divides `[L : K(X)]_s = 1`. SGA's addendum contrasts Shioda's weakly
unirational surfaces with nontrivial `π₁` and the strongly (separably) unirational ones, which are
simply connected by Kollár; this is the opposite, purely inseparable, extreme. -/
theorem isSimplyConnected_of_isPurelyInseparable (hX : IsNormalScheme X) (L : Type u) [Field L]
    [Algebra X.functionField L] [FiniteDimensional X.functionField L]
    [IsPurelyInseparable X.functionField L]
    (hL : letI : Algebra k L := ((algebraMap X.functionField L).comp (functionFieldMap f)).toAlgebra
      IsPurelyTranscendental k L) :
    IsSimplyConnected X := by
  let _ := (functionFieldMap f).toAlgebra
  have hfin : HasFiniteFundamentalGroup X := by
    refine hasFiniteFundamentalGroup_of_isUnirational f hX ⟨L, inferInstance, inferInstance,
      inferInstance, ?_⟩
    exact hL
  have : ConnectedSpace X := hfin.1
  let Ω := AlgebraicClosure (X.residueField (genericPoint X))
  let s : Spec (.of Ω) ⟶ X := ExposeV.geometricPointAt X (genericPoint X)
  have h := natCard_etaleFundamentalGroup_dvd_finSepDegree f hX L hL Ω s
  rw [IsPurelyInseparable.finSepDegree_eq_one, Nat.dvd_one] at h
  exact (isSimplyConnected_iff_subsingleton Ω s).2 (Nat.card_eq_one_iff_unique.mp h).1

end Unirational

end SGA.SGA1.ExposeXI
