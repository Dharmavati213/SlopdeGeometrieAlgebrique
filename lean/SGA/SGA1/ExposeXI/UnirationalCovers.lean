/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.UnirationalVarieties
import SGA.SGA1.ExposeXI.UnirationalCoversParametrization

/-!
# Étale coverings of unirational varieties are unirational (XI.1.4, step 3)

Step (3) of Serre's proof of XI.1.4: an integral finite étale covering `Y` of a proper integral
unirational scheme `X` over an algebraically closed field `k` is again unirational (a connected
covering is integral when `X` is normal, `isIntegral_of_etale_of_isNormalScheme`). As in XI.1.3, a
parametrization `K(X) ⊆ L = K(ℙʳ)` is a rational map `ℙʳ ⇢ X` defined on an open `U ⊆ ℙʳ` with
complement of codimension `≥ 2`; `U` is simply connected, so the map lifts to `U ⟶ Y`, and the lift
embeds `K(Y)` into `L` over `K(X)`.

* `functionFieldHom π hπ : K(X) ⟶ K(Y)`: the map of function fields of a morphism of integral
  schemes mapping the generic point to the generic point, and
  `functionFieldMap_comp`: it is compatible with the structure maps `k → K(X) → K(Y)`.
* `exists_functionFieldHom_comp_eq`: the general form, for `ℙʳ` replaced by a regular simply
  connected `P` with `K(P)` over `K(X)` (the extension to `U ⊆ P` is
  `exists_isSimplyConnected_extension`, shared with XI.1.3).
* `exists_ringHom_comp_functionFieldHom_eq`: for a unirational parametrization `L` of `K(X)`,
  `K(Y)` embeds in `L` over `K(X)`; hence `finrank_functionField_dvd`: `[K(Y) : K(X)]` divides
  `[L : K(X)]`, in every characteristic.
* `isUnirational_of_isFinite_of_etale`: `K(Y)` is unirational over `k`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeXI

section FunctionFieldHom

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The map of function fields `K(X) → K(Y)` induced by a morphism `π : Y ⟶ X` of integral schemes
which maps the generic point to the generic point. -/
noncomputable def functionFieldHom (π : Y ⟶ X) (hπ : π (genericPoint Y) = genericPoint X) :
    X.functionField ⟶ Y.functionField :=
  X.presheaf.stalkSpecializes (by rw [hπ]; exact specializes_rfl) ≫ π.stalkMap (genericPoint Y)

@[reassoc]
lemma SpecMap_functionFieldHom_fromSpecStalk (π : Y ⟶ X)
    (hπ : π (genericPoint Y) = genericPoint X) :
    Spec.map (functionFieldHom π hπ) ≫ X.fromSpecStalk (genericPoint X) =
      Y.fromSpecStalk (genericPoint Y) ≫ π := by
  rw [functionFieldHom, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- The structure maps of function fields over `k` are compatible with `functionFieldHom`. -/
lemma functionFieldMap_comp {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (π : Y ⟶ X)
    (hπ : π (genericPoint Y) = genericPoint X) :
    functionFieldMap (π ≫ f) = (functionFieldHom π hπ).hom.comp (functionFieldMap f) := by
  have h : CommRingCat.ofHom (functionFieldMap (π ≫ f)) =
      CommRingCat.ofHom (functionFieldMap f) ≫ functionFieldHom π hπ := by
    apply Spec.map_injective
    rw [← fromSpecStalk_comp_eq_SpecMap, Spec.map_comp, ← fromSpecStalk_comp_eq_SpecMap,
      SpecMap_functionFieldHom_fromSpecStalk_assoc]
  exact congrArg CommRingCat.Hom.hom h

end FunctionFieldHom

section Lift

variable {S X P Y : Scheme.{u}} (sX : X ⟶ S) (sP : P ⟶ S) [IsIntegral X] [IsIntegral P]
  [IsIntegral Y] [IsLocallyNoetherian P] [LocallyOfFiniteType sX] [UniversallyClosed sX]
  [X.IsSeparated]

/-- XI.1.3, XI.1.4: let `X` be integral, locally noetherian, separated, universally closed and
locally of finite type over `S`, and `P` integral, regular, locally noetherian and simply
connected, with a map of function fields `τ : K(X) → K(P)` over `S` (a dominant rational map
`P ⇢ X`). Then for every finite étale `π : Y ⟶ X` with `Y` integral, `τ` factors through
`K(Y)`: the rational map is defined on an open `U ⊆ P` with complement of codimension `≥ 2`,
which is simply connected, so it lifts to `U ⟶ Y`. -/
theorem exists_functionFieldHom_comp_eq (hP : ExposeX.IsRegularScheme P)
    (hPs : IsSimplyConnected P) {y : P} (hy : y = genericPoint P)
    (τ : X.functionField ⟶ P.presheaf.stalk y)
    (hτ : Spec.map τ ≫ X.fromSpecStalk (genericPoint X) ≫ sX = P.fromSpecStalk y ≫ sP)
    (π : Y ⟶ X) [IsFinite π] [Etale π] (hπ : π (genericPoint Y) = genericPoint X) :
    ∃ φ : Y.functionField ⟶ P.presheaf.stalk y, functionFieldHom π hπ ≫ φ = τ := by
  subst hy
  obtain ⟨U, hηU, g, hU, -, hgw, hUw⟩ := exists_isSimplyConnected_extension sX sP hP hPs rfl τ hτ
  let w : U.toScheme := ⟨genericPoint P, hηU⟩
  let sm : P.presheaf.stalk (genericPoint P) ⟶ U.toScheme.presheaf.stalk w := U.ι.stalkMap w
  have : IsIso sm := inferInstanceAs (IsIso (U.ι.stalkMap w))
  -- Lift `g` to `Y`.
  let Z : ExposeV.FEt X := MorphismProperty.Over.mk ⊤ π ⟨inferInstance, inferInstance⟩
  have : ConnectedSpace Z.left := inferInstanceAs (ConnectedSpace Y)
  have : IsConnected Z := ExposeV.FEt.isConnected_of_connectedSpace Z
  let u := ExposeV.geometricPointAt U w
  obtain ⟨z⟩ := nonempty_fiber_of_isConnected (ExposeV.FEt.fiber _ (u ≫ g)) Z
  obtain ⟨ℓ, hℓ, -⟩ := exists_lift_of_isSimplyConnected hU g Z _ u z
  change U.toScheme ⟶ Y at ℓ
  change ℓ ≫ π = g at hℓ
  -- The lift maps the generic point of `U` to that of `Y`.
  have hℓw : ℓ w = genericPoint Y := by
    have h1 : π (ℓ w) = genericPoint X := by
      change (ℓ ≫ π) w = _
      rw [hℓ, hgw]
    exact (eq_of_specializes_of_isDiscrete (π.isDiscrete_preimage_singleton (genericPoint X))
      (Set.mem_preimage.mpr hπ) (Set.mem_preimage.mpr h1) (genericPoint_specializes _)).symm
  obtain ⟨φ', -, hφ'⟩ := exists_SpecMap_fromSpecStalk (U.toScheme.fromSpecStalk w ≫ ℓ)
    (genericPoint Y) (by
      change ℓ (U.toScheme.fromSpecStalk w (IsLocalRing.closedPoint _)) = _
      rw [Scheme.fromSpecStalk_closedPoint, hℓw])
  refine ⟨φ' ≫ inv sm, ?_⟩
  have key : functionFieldHom π hπ ≫ φ' = τ ≫ sm := by
    apply SpecMap_fromSpecStalk_injective (y := genericPoint X)
    rw [Spec.map_comp, Category.assoc, SpecMap_functionFieldHom_fromSpecStalk,
      ← Category.assoc, hφ', Category.assoc, hℓ, hUw, Spec.map_comp, Category.assoc]
    rfl
  rw [← Category.assoc, key, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end Lift

section Unirational

open AlgebraicGeometry.ProjectiveSpace

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Spec (.of k))

/-- XI.1.4, step (3) of Serre's proof, field form: let `X` be a proper integral scheme over an
algebraically closed field `k` and `L ⊇ K(X)` a finite extension which is purely transcendental
over `k`. Then the function field of every integral finite étale covering `Y` of `X` embeds into
`L` over `K(X)`. No assumption on the characteristic is needed. -/
theorem exists_ringHom_comp_functionFieldHom_eq [IsAlgClosed k] [IsProper f] (π : Y ⟶ X)
    [IsFinite π] [Etale π] (hπ : π (genericPoint Y) = genericPoint X) (L : Type u) [Field L]
    [Algebra X.functionField L] [FiniteDimensional X.functionField L]
    (hL : letI : Algebra k L := ((algebraMap X.functionField L).comp (functionFieldMap f)).toAlgebra
      IsPurelyTranscendental k L) :
    ∃ φ : Y.functionField →+* L,
      φ.comp (functionFieldHom π hπ).hom = algebraMap X.functionField L := by
  obtain ⟨s, _, y, hy, ρ, _, hτ, -⟩ := exists_proj_parametrization f L hL
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  obtain ⟨φ, hφ⟩ := exists_functionFieldHom_comp_eq f (projToSpec (Option s) k)
    (ProjectiveSpace.isRegularScheme_proj k _) (isSimplyConnected_proj' _) hy _ hτ π hπ
  refine ⟨(φ ≫ ρ).hom, ?_⟩
  have e : functionFieldHom π hπ ≫ φ ≫ ρ = CommRingCat.ofHom (algebraMap X.functionField L) := by
    rw [← Category.assoc, hφ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact congrArg CommRingCat.Hom.hom e

/-- A finite étale morphism of integral schemes maps the generic point to the generic point. -/
lemma genericPoint_eq_of_isFinite_of_etale (π : Y ⟶ X) [IsFinite π] [Etale π] :
    π (genericPoint Y) = genericPoint X :=
  genericPoint_eq_of_surjective π (ProjectiveSpace.surjective_of_isFinite_of_etale π)

/-- XI.1.4, step (3), degree form: let `X` be a proper integral scheme over an algebraically closed
field `k` and `L ⊇ K(X)` a finite extension which is purely transcendental over `k`. Then the
degree `[K(Y) : K(X)]` of every integral finite étale covering `Y` of `X` divides `[L : K(X)]`. -/
theorem finrank_functionField_dvd [IsAlgClosed k] [IsProper f] (π : Y ⟶ X) [IsFinite π]
    [Etale π] (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    (hL : letI : Algebra k L := ((algebraMap X.functionField L).comp (functionFieldMap f)).toAlgebra
      IsPurelyTranscendental k L) :
    letI := (functionFieldHom π (genericPoint_eq_of_isFinite_of_etale π)).hom.toAlgebra
    Module.finrank X.functionField Y.functionField ∣ Module.finrank X.functionField L := by
  let hπ := genericPoint_eq_of_isFinite_of_etale π
  obtain ⟨φ, hφ⟩ := exists_ringHom_comp_functionFieldHom_eq f π hπ L hL
  let _ := (functionFieldHom π hπ).hom.toAlgebra
  let _ := φ.toAlgebra
  have : IsScalarTower X.functionField Y.functionField L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (DFunLike.congr_fun hφ x).symm
  have : Module.Finite Y.functionField L :=
    Module.Finite.of_restrictScalars_finite X.functionField Y.functionField L
  exact Dvd.intro _ (Module.finrank_mul_finrank X.functionField Y.functionField L)

/-- XI.1.4, step (3) of Serre's proof: every integral finite étale covering `Y` of a proper
integral unirational scheme `X` over an algebraically closed field `k` is unirational over `k`:
`K(Y)` embeds in a unirational parametrization of `K(X)`. No assumption on the characteristic
is needed. -/
theorem isUnirational_of_isFinite_of_etale [IsAlgClosed k] [IsProper f] (π : Y ⟶ X) [IsFinite π]
    [Etale π] (h : letI := (functionFieldMap f).toAlgebra; IsUnirational k X.functionField) :
    letI := (functionFieldMap (π ≫ f)).toAlgebra; IsUnirational k Y.functionField := by
  let hπ := genericPoint_eq_of_isFinite_of_etale π
  obtain ⟨L, _, _, _, hL⟩ := h
  obtain ⟨φ, hφ⟩ := exists_ringHom_comp_functionFieldHom_eq f π hπ L hL
  let _ := (functionFieldHom π hπ).hom.toAlgebra
  let _ := φ.toAlgebra
  have : IsScalarTower X.functionField Y.functionField L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (DFunLike.congr_fun hφ x).symm
  have hfin : Module.Finite Y.functionField L :=
    Module.Finite.of_restrictScalars_finite X.functionField Y.functionField L
  have e : φ.comp (functionFieldMap (π ≫ f)) =
      (algebraMap X.functionField L).comp (functionFieldMap f) := by
    rw [functionFieldMap_comp f π hπ, ← RingHom.comp_assoc, hφ]
  refine ⟨L, inferInstance, φ.toAlgebra, hfin, ?_⟩
  change @IsPurelyTranscendental k L _ _ (φ.comp (functionFieldMap (π ≫ f))).toAlgebra
  rw [e]
  exact hL

end Unirational

end SGA.SGA1.ExposeXI
