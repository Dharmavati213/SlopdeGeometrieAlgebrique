/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.RationalVarieties

/-!
# Unirational parametrizations (XI.1.3, XI.1.4)

The common first steps of XI.1.3 (`π₁` of a unirational variety is finite) and of steps (1) and
(3) of Serre's proof of XI.1.4. A unirational parametrization of `K(X)` is a finite extension
`L ⊇ K(X)` purely transcendental over `k`; it is the function field of `ℙʳ`, so it gives a
dominant generically finite rational map `ℙʳ ⇢ X`.

* `IsPurelyTranscendental.exists_finite`: a purely transcendental extension of finite
  transcendence degree has a finite transcendence basis generating it;
* `exists_proj_parametrization`: `L` is the function field of `ℙ^s = Proj k[x_∞, x_i : i ∈ s]`,
  with `τ : K(X) → K(ℙ^s)` over `k` and `K(ℙ^s)` finite over `K(X)`;
* `exists_algHom_fractionRing_of_isUnirational`: `K(X)` embeds over `k` into
  `k(x_i : i ∈ σ) = FractionRing (MvPolynomial σ k)`, `σ` finite, which is finite over `K(X)`;
* `exists_isSimplyConnected_extension`: a rational map `P ⇢ X` from a regular simply connected
  `P`, given at the generic point by `τ : K(X) → K(P)`, is defined on an open `U ∋ η_P` with
  complement of codimension `≥ 2` (EGA IV 20.4.5, `ExposeX.exists_extension_of_isRegularScheme`),
  and `U` is simply connected (purity X.3.3).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXI

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- A field `L` finite over a field `K` essentially of finite type over `k`, and purely
transcendental over `k`, is generated over `k` by a finite algebraically independent set. -/
theorem IsPurelyTranscendental.exists_finite [Algebra.EssFiniteType k K] {L : Type u} [Field L]
    [Algebra K L] [Algebra k L] [IsScalarTower k K L] [FiniteDimensional K L]
    (h : IsPurelyTranscendental k L) :
    ∃ s : Set L, Finite s ∧ AlgebraicIndependent k ((↑) : s → L) ∧
      IntermediateField.adjoin k s = ⊤ := by
  obtain ⟨s, hs, hadj⟩ := h
  have : Algebra.EssFiniteType k L := Algebra.EssFiniteType.comp k K L
  exact ⟨s, finite_of_algebraicIndependent hs, hs, hadj⟩

/-- A unirational field `K` over `k` (essentially of finite type) embeds over `k` into a rational
function field `k(x_i : i ∈ σ) = FractionRing (MvPolynomial σ k)` in finitely many variables, which
is finite over `K`. -/
theorem exists_algHom_fractionRing_of_isUnirational [Algebra.EssFiniteType k K]
    (h : IsUnirational k K) :
    ∃ (σ : Type u) (_ : Finite σ) (ι : K →ₐ[k] FractionRing (MvPolynomial σ k)),
      letI := ι.toRingHom.toAlgebra; FiniteDimensional K (FractionRing (MvPolynomial σ k)) := by
  obtain ⟨L, _, _, _, hL⟩ := h
  let _ : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨s, _, hs, hadj⟩ := IsPurelyTranscendental.exists_finite (K := K) hL
  have hrange : IntermediateField.adjoin k (Set.range ((↑) : s → L)) = ⊤ := by
    rwa [Subtype.range_coe]
  -- `L ≅ k(x_i : i ∈ s)`.
  let eF : FractionRing (MvPolynomial s k) ≃ₐ[k] L :=
    hs.aevalEquivField.trans ((IntermediateField.equivOfEq hrange).trans IntermediateField.topEquiv)
  let ι : K →ₐ[k] FractionRing (MvPolynomial s k) :=
    eF.symm.toAlgHom.comp (IsScalarTower.toAlgHom k K L)
  refine ⟨s, inferInstance, ι, ?_⟩
  let _ : Algebra K (FractionRing (MvPolynomial s k)) := ι.toRingHom.toAlgebra
  let g : L →ₗ[K] FractionRing (MvPolynomial s k) :=
    { toFun := eF.symm
      map_add' := map_add _
      map_smul' := fun y l ↦ by
        rw [Algebra.smul_def, map_mul, RingHom.id_apply, Algebra.smul_def]
        rfl }
  exact Module.Finite.of_surjective g eF.symm.surjective

end Field

section Proj

open AlgebraicGeometry.ProjectiveSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (sX : X ⟶ Spec (.of k))

/-- XI.1.3, XI.1.4: a unirational parametrization `L` of `K(X)` (finite over `K(X)`, purely
transcendental over `k`) is the function field of `ℙ^s = Proj k[x_∞, x_i : i ∈ s]` for a finite
`s`: there are `ρ : K(ℙ^s) ≅ L` and, with `τ = ρ⁻¹ ∘ (K(X) → L)`, the rational map `ℙ^s ⇢ X` over
`k` given by `τ`, with `K(ℙ^s)` finite over `K(X)`. -/
theorem exists_proj_parametrization [LocallyOfFiniteType sX] (L : Type u) [Field L]
    [Algebra X.functionField L] [FiniteDimensional X.functionField L]
    (hL : letI : Algebra k L :=
        ((algebraMap X.functionField L).comp (functionFieldMap sX)).toAlgebra
      IsPurelyTranscendental k L) :
    ∃ (s : Set L) (_ : Finite s) (y : Proj (grading (Option s) k)) (_ : y = genericPoint _)
      (ρ : (Proj (grading (Option s) k)).presheaf.stalk y ⟶ CommRingCat.of L) (_ : IsIso ρ),
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField L) ≫ inv ρ) ≫
          X.fromSpecStalk (genericPoint X) ≫ sX =
        (Proj (grading (Option s) k)).fromSpecStalk y ≫ projToSpec (Option s) k ∧
      letI := (CommRingCat.ofHom (algebraMap X.functionField L) ≫ inv ρ).hom.toAlgebra
      Module.Finite X.functionField ((Proj (grading (Option s) k)).presheaf.stalk y) := by
  let _ := (functionFieldMap sX).toAlgebra
  let _ : Algebra k L := ((algebraMap X.functionField L).comp (algebraMap k _)).toAlgebra
  have : IsScalarTower k X.functionField L := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.EssFiniteType k X.functionField := essFiniteType_functionFieldMap sX
  obtain ⟨s, _, hs, hadj⟩ := IsPurelyTranscendental.exists_finite (K := X.functionField) hL
  obtain ⟨y, hy, ρ, hρ, hρs⟩ := exists_functionField_iso_proj L s hs hadj
  let τ : X.functionField ⟶ (Proj (grading (Option s) k)).presheaf.stalk y :=
    CommRingCat.ofHom (algebraMap X.functionField L) ≫ inv ρ
  refine ⟨s, inferInstance, y, hy, ρ, hρ, ?_, ?_⟩
  · rw [fromSpecStalk_comp_eq_SpecMap, ← Spec.map_comp]
    have e : CommRingCat.ofHom (functionFieldMap sX) ≫
        CommRingCat.ofHom (algebraMap X.functionField L) ≫ inv ρ =
          CommRingCat.ofHom (algebraMap k L) ≫ inv ρ := rfl
    rw [e, Spec.map_comp, ← hρs, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id,
      Spec.map_id, Category.id_comp]
  · let _ := τ.hom.toAlgebra
    let e : L ≃ₐ[X.functionField] (Proj (grading (Option s) k)).presheaf.stalk y :=
      AlgEquiv.ofRingEquiv (f := (asIso ρ).symm.commRingCatIsoToRingEquiv) fun _ ↦ rfl
    exact Module.Finite.equiv e.toLinearEquiv

end Proj

section Extension

variable {S X P : Scheme.{u}} (sX : X ⟶ S) (sP : P ⟶ S) [IsIntegral X] [IsIntegral P]
  [IsLocallyNoetherian P] [LocallyOfFiniteType sX] [UniversallyClosed sX] [X.IsSeparated]

/-- XI.1.3, XI.1.4: let `X` be integral, separated, universally closed and locally of finite type
over `S`, and `P` integral, regular, locally noetherian and simply connected, with a map of
function fields `τ : K(X) → K(P)` over `S` (a dominant rational map `P ⇢ X`). Then the rational
map is defined on an open `U ∋ η_P` of `P` whose complement has codimension `≥ 2` (EGA IV 20.4.5),
and `U` is simply connected (purity X.3.3): there is `g : U ⟶ X` mapping the generic point
`w = η_P` of `U` to `η_X`, which is `τ` at `w`. -/
theorem exists_isSimplyConnected_extension (hP : ExposeX.IsRegularScheme P)
    (hPs : IsSimplyConnected P) {y : P} (hy : y = genericPoint P)
    (τ : X.functionField ⟶ P.presheaf.stalk y)
    (hτ : Spec.map τ ≫ X.fromSpecStalk (genericPoint X) ≫ sX = P.fromSpecStalk y ≫ sP) :
    ∃ (U : P.Opens) (hU : y ∈ U) (g : U.toScheme ⟶ X), IsSimplyConnected U ∧
      (haveI : Nonempty U := ⟨⟨y, hU⟩⟩; (⟨y, hU⟩ : U.toScheme) = genericPoint U) ∧
      g ⟨y, hU⟩ = genericPoint X ∧
      U.toScheme.fromSpecStalk ⟨y, hU⟩ ≫ g =
        Spec.map (U.ι.stalkMap ⟨y, hU⟩) ≫ Spec.map τ ≫ X.fromSpecStalk (genericPoint X) := by
  subst hy
  let ψ : Spec (P.presheaf.stalk (genericPoint P)) ⟶ X :=
    Spec.map τ ≫ X.fromSpecStalk (genericPoint X)
  have hψ : ψ ≫ sX = P.fromSpecStalk (genericPoint P) ≫ sP := by
    rw [Category.assoc]
    exact hτ
  -- Extend `ψ` to an open `U` of `P` with complement of codimension `≥ 2`.
  let F := Scheme.PartialMap.ofFromSpecStalk sP sX ψ hψ
  have hFη : genericPoint P ∈ F.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sP sX ψ hψ
  have hFψ : F.domain.fromSpecStalkOfMem _ hFη ≫ F.hom = ψ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sP sX ψ hψ
  have hF : F.hom ≫ sX = F.domain.ι ≫ sP := Scheme.PartialMap.ofFromSpecStalk_comp sP sX ψ hψ
  obtain ⟨U, hFU, g, hg, hcodim⟩ := ExposeX.exists_extension_of_isRegularScheme sP sX hP F hF
  have := ExposeX.isEquivalence_pullback_of_isRegularScheme hP U hcodim
  have hηU : genericPoint P ∈ U := hFU hFη
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  -- The generic point `w` of `U`, and `g` at `w`.
  let w : U.toScheme := ⟨genericPoint P, hηU⟩
  let sm : P.presheaf.stalk (genericPoint P) ⟶ U.toScheme.presheaf.stalk w := U.ι.stalkMap w
  have : IsIso sm := inferInstanceAs (IsIso (U.ι.stalkMap w))
  have hUw : U.toScheme.fromSpecStalk w ≫ g = Spec.map sm ≫ ψ := by
    have e0 : Spec.map sm ≫ Spec.map (inv sm) = 𝟙 _ := by
      rw [← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id]
    have e1 : U.toScheme.fromSpecStalk w =
        Spec.map sm ≫ U.fromSpecStalkOfMem (genericPoint P) hηU :=
      ((Category.id_comp _).symm.trans (congrArg (· ≫ U.toScheme.fromSpecStalk w) e0.symm)).trans
        (Category.assoc _ _ _)
    have e2 : U.fromSpecStalkOfMem (genericPoint P) hηU =
        F.domain.fromSpecStalkOfMem _ hFη ≫ P.homOfLE hFU := by
      rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι]
    rw [e1, e2]
    exact (Category.assoc _ _ _).trans (congrArg (Spec.map sm ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg _ hg).trans hFψ)))
  refine ⟨U, hηU, g,
    isSimplyConnected_of_equivalence (ExposeV.FEt.pullback U.ι).asEquivalence.symm hPs, ?_, ?_,
    hUw⟩
  · apply U.ι.isOpenEmbedding.injective
    rw [genericPoint_eq_of_isOpenImmersion U.ι]
    rfl
  · have h := congrArg (fun m ↦ m (IsLocalRing.closedPoint _)) hUw
    change g (U.toScheme.fromSpecStalk w (IsLocalRing.closedPoint _)) =
      X.fromSpecStalk _ (Spec.map τ (Spec.map sm (IsLocalRing.closedPoint _))) at h
    simpa only [Scheme.fromSpecStalk_closedPoint, Spec_closedPoint] using h

end Extension

end SGA.SGA1.ExposeXI
