/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.ClosedImmersionSections
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Polynomial.Module.TensorProduct

/-!
# Sections of inverse images over affine opens, and affine base change

* `Scheme.Modules.pullbackSectionsEquiv`: for `g : T ⟶ X`, `U ⊆ X` and `g⁻¹ U` affine and `M`
  quasi-coherent, `Γ(g^* M, g⁻¹ U) ≅ Γ(T, g⁻¹ U) ⊗_{Γ(X, U)} Γ(M, U)`, `c ⊗ s ↦ c • g^* s`
  (EGA I 1.6.5; Stacks 01I9).
* `CohomologyAux.isPushout_baseChange`: for `X ⟶ Spec A`, `A ⟶ C` and `V ⊆ X` affine, the ring of
  the inverse image of `V` in `X ×_A C` is `Γ(X, V) ⊗_A C` (EGA I 3.2.2).
* `CohomologyAux.baseChangePolynomialIso`, `CohomologyAux.pullbackPolynomialSectionsEquiv`: over
  `A[t]`, `Γ(X ×_A A[t], q⁻¹ V) ≅ Γ(X, V)[t]` and `Γ(q^* M, q⁻¹ V) ≅ Γ(M, V)[t]`.
-/

universe u

open CategoryTheory Limits Opposite TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

open ModuleCat ChangeOfRings

variable {T X : Scheme.{u}} (g : T ⟶ X) (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}
  (hU : IsAffineOpen U) (hW : IsAffineOpen (g ⁻¹ᵁ U))

/-- **Sections of an inverse image over an affine open** (EGA I 1.6.5, Stacks 01I9): for `U` and
`g⁻¹ U` affine and `M` quasi-coherent, `Γ(g^* M, g⁻¹ U) ≅ Γ(T, g⁻¹ U) ⊗_{Γ(X, U)} Γ(M, U)`. -/
noncomputable def pullbackSectionsEquiv :
    Γ((pullback g).obj M, g ⁻¹ᵁ U) ≃+
      (extendScalars (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom).obj (ModuleCat.of Γ(X, U) Γ(M, U)) :=
  (AddEquiv.ofBijective (pullbackCompare g M hU hW) (pullbackCompare_bijective g M hU hW)).trans
    ((pullbackSpecMapΓAddEquiv _ ((pullback hU.fromSpec).obj M)).trans
      (((extendScalars (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom).mapIso
        (fromSpecSectionsEquiv M hU).symm.toModuleIso).toLinearEquiv.toAddEquiv))

lemma pullbackSectionsEquiv_pullbackApp (s : Γ(M, U)) :
    pullbackSectionsEquiv g M hU hW (pullbackApp g M U s) =
      (1 : Γ(T, g ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U), (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom] s := by
  change ((extendScalars _).map (fromSpecSectionsEquiv M hU).symm.toModuleIso.hom)
    (pullbackSpecMapΓAddEquiv _ _ (pullbackCompare g M hU hW (pullbackApp g M U s))) = _
  rw [pullbackCompare_pullbackApp, pullbackSpecMapΓAddEquiv_pullbackApp]
  change (1 : Γ(T, g ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U), (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom]
    (fromSpecSectionsEquiv M hU).symm (fromSpecSectionsEquiv M hU s) = _
  rw [LinearEquiv.symm_apply_apply]

lemma pullbackSectionsEquiv_smul (c : Γ(T, g ⁻¹ᵁ U)) (z : Γ((pullback g).obj M, g ⁻¹ᵁ U)) :
    pullbackSectionsEquiv g M hU hW (c • z) = c • pullbackSectionsEquiv g M hU hW z := by
  change ((extendScalars _).map (fromSpecSectionsEquiv M hU).symm.toModuleIso.hom)
    (pullbackSpecMapΓAddEquiv _ _ (pullbackCompare g M hU hW (c • z))) = _
  rw [pullbackCompare_smul, pullbackSpecMapΓAddEquiv_smul]
  exact ((extendScalars _).map (fromSpecSectionsEquiv M hU).symm.toModuleIso.hom).hom.map_smul c _

/-- The inverse image of sections in terms of tensor products: `c ⊗ s ↦ c • g^* s`. -/
lemma pullbackSectionsEquiv_symm_tmul (c : Γ(T, g ⁻¹ᵁ U)) (s : Γ(M, U)) :
    (pullbackSectionsEquiv g M hU hW).symm
        (c ⊗ₜ[Γ(X, U), (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom] s) =
      c • pullbackApp g M U s := by
  apply (pullbackSectionsEquiv g M hU hW).injective
  refine (AddEquiv.apply_symm_apply _ _).trans ?_
  rw [pullbackSectionsEquiv_smul, pullbackSectionsEquiv_pullbackApp]
  exact ((ExtendScalars.smul_tmul (M := ModuleCat.of Γ(X, U) Γ(M, U)) _ c 1 s).trans
    (by rw [mul_one]; rfl)).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.CohomologyAux

set_option backward.isDefEq.respectTransparency.types false in
instance isAffineHom_pullback_fst {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsAffineHom g] :
    IsAffineHom (pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ ‹_›

set_option backward.isDefEq.respectTransparency.types false in
lemma isAffineHom_of_isPullback {X Y S P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ S}
    {g : Y ⟶ S} (H : IsPullback fst snd f g) [IsAffineHom g] : IsAffineHom fst :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip ‹_›

section BaseChange

variable {A C : CommRingCat.{u}} {β : A ⟶ C} {X Y : Scheme.{u}} {f : X ⟶ Spec A} {g : Y ⟶ X}
  {g' : Y ⟶ Spec C} (H : IsPullback g g' f (Spec.map β)) {V : X.Opens} (hV : IsAffineOpen V)

include H hV in
/-- **Affine base change** (EGA I 3.2.2): for a pullback square `Y = X ×_{Spec A} Spec C` and
`V ⊆ X` affine, the ring of the inverse image of `V` in `Y` is `Γ(X, V) ⊗_A C`: the square of
rings is a pushout. -/
lemma isPushout_baseChange :
    IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ V le_top) β (g.appLE V (g ⁻¹ᵁ V) le_rfl)
      ((Scheme.ΓSpecIso C).inv ≫ g'.appLE ⊤ (g ⁻¹ᵁ V) le_top) := by
  have hUY : g ⁻¹ᵁ V = g ⁻¹ᵁ V ⊓ g' ⁻¹ᵁ ⊤ := by simp
  have h := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) le_top le_top hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H le_top le_top hUY (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  refine h.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · exact Scheme.ΓSpecIso_naturality β
  · simp
  · simp

end BaseChange

section Polynomial

open Polynomial

variable {A : CommRingCat.{u}} {X Y : Scheme.{u}} {f : X ⟶ Spec A} {V : X.Opens}
  (hV : IsAffineOpen V)

/-- The morphism `A ⟶ A[t]`. -/
noncomputable abbrev polyC (A : CommRingCat.{u}) : A ⟶ CommRingCat.of A[X] :=
  CommRingCat.ofHom Polynomial.C

variable (f) in
/-- The structure map `A → Γ(X, V)`. -/
noncomputable abbrev structMap : A ⟶ Γ(X, V) := (Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ V le_top

/-- The pushout square `A → A[t]`, `A → R`, `R → R[t]`. -/
lemma isPushout_polynomial {A R : CommRingCat.{u}} (φ : A ⟶ R) :
    IsPushout φ (polyC A) (polyC R) (CommRingCat.ofHom (Polynomial.mapRingHom φ.hom)) := by
  let _ : Algebra A R := φ.hom.toAlgebra
  refine (CommRingCat.isPushout_tensorProduct A R A[X]).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (polyEquivTensor A R).symm.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    change (polyEquivTensor A R).symm (r ⊗ₜ 1) = C r
    rw [polyEquivTensor_symm_apply_tmul_eq_smul, Polynomial.map_one, Polynomial.smul_eq_C_mul,
      mul_one]
  · refine CommRingCat.hom_ext (RingHom.ext fun p ↦ ?_)
    change (polyEquivTensor A R).symm (1 ⊗ₜ p) = p.map φ.hom
    rw [polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]
    rfl

variable {g : Y ⟶ X} {g' : Y ⟶ Spec (CommRingCat.of A[X])}
  (H : IsPullback g g' f (Spec.map (polyC A)))

/-- `Γ(X ×_A A[t], g⁻¹ V) ≅ Γ(X, V)[t]` for `V` affine. -/
noncomputable def baseChangePolynomialIso :
    Γ(Y, g ⁻¹ᵁ V) ≅ CommRingCat.of Γ(X, V)[X] :=
  (isPushout_baseChange H hV).isoIsPushout _ _ (isPushout_polynomial (structMap f))

@[reassoc]
lemma appLE_baseChangePolynomialIso :
    g.appLE V (g ⁻¹ᵁ V) le_rfl ≫ (baseChangePolynomialIso hV H).hom = polyC Γ(X, V) :=
  IsPushout.inl_isoIsPushout_hom _ _ _ _

@[reassoc]
lemma structure_baseChangePolynomialIso :
    ((Scheme.ΓSpecIso (CommRingCat.of A[X])).inv ≫ g'.appLE ⊤ (g ⁻¹ᵁ V) le_top) ≫
      (baseChangePolynomialIso hV H).hom =
      CommRingCat.ofHom (Polynomial.mapRingHom (structMap f).hom) :=
  IsPushout.inr_isoIsPushout_hom _ _ _ _

variable (M : X.Modules) [M.IsQuasicoherent]

open ModuleCat ChangeOfRings in
/-- The ring isomorphism `Γ(Y, g⁻¹ V) ≅ Γ(X, V)[t]` as a `Γ(X, V)`-linear map. -/
noncomputable def baseChangePolynomialLinearEquiv :
    (restrictScalars (g.appLE V (g ⁻¹ᵁ V) le_rfl).hom).obj (ModuleCat.of _ Γ(Y, g ⁻¹ᵁ V))
      ≃ₗ[Γ(X, V)] Γ(X, V)[X] where
  toFun c := (baseChangePolynomialIso hV H).hom (show Γ(Y, g ⁻¹ᵁ V) from c)
  invFun p := (show Γ(Y, g ⁻¹ᵁ V) from (baseChangePolynomialIso hV H).inv p)
  map_add' x y := map_add _ _ _
  map_smul' r c := by
    change (baseChangePolynomialIso hV H).hom
        (g.appLE V _ le_rfl r * (show Γ(Y, g ⁻¹ᵁ V) from c)) = _
    rw [map_mul, ← ConcreteCategory.comp_apply, appLE_baseChangePolynomialIso,
      RingHom.id_apply, Polynomial.smul_eq_C_mul]
    rfl
  left_inv c := by
    change (baseChangePolynomialIso hV H).inv ((baseChangePolynomialIso hV H).hom c) = c
    exact (baseChangePolynomialIso hV H).hom_inv_id_apply c
  right_inv p := (baseChangePolynomialIso hV H).inv_hom_id_apply p

open ModuleCat ChangeOfRings in
include hV H in
/-- `Γ(Y, g⁻¹ V) ⊗_{Γ(X, V)} N ≅ N[t]`. -/
noncomputable def polynomialTensorEquiv (N : Type u) [AddCommGroup N] [Module Γ(X, V) N] :
    (extendScalars (g.appLE V (g ⁻¹ᵁ V) le_rfl).hom).obj (ModuleCat.of Γ(X, V) N) ≃+
      PolynomialModule Γ(X, V) N :=
  ((TensorProduct.congr (baseChangePolynomialLinearEquiv hV H) (LinearEquiv.refl _ _)).trans
    ((PolynomialModule.polynomialTensorProductLEquivPolynomialModule Γ(X, V) N).restrictScalars
      Γ(X, V))).toAddEquiv

open ModuleCat ChangeOfRings in
lemma polynomialTensorEquiv_tmul (N : Type u) [AddCommGroup N] [Module Γ(X, V) N]
    (c : Γ(Y, g ⁻¹ᵁ V)) (n : N) :
    polynomialTensorEquiv hV H N (c ⊗ₜ[Γ(X, V), (g.appLE V (g ⁻¹ᵁ V) le_rfl).hom] n) =
      (baseChangePolynomialIso hV H).hom c • PolynomialModule.single Γ(X, V) 0 n :=
  rfl

/-- **Sections of the inverse image to `X ×_A A[t]`**: for `V` affine and `M` quasi-coherent,
`Γ(g^* M, g⁻¹ V) ≅ Γ(M, V)[t]`. -/
noncomputable def pullbackPolynomialSectionsEquiv :
    Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ V) ≃+ PolynomialModule Γ(X, V) Γ(M, V) :=
  have : IsAffineHom g := isAffineHom_of_isPullback H
  (Scheme.Modules.pullbackSectionsEquiv g M hV (hV.preimage g)).trans
    (polynomialTensorEquiv hV H Γ(M, V))

open ModuleCat ChangeOfRings in
lemma pullbackPolynomialSectionsEquiv_smul_pullbackApp (c : Γ(Y, g ⁻¹ᵁ V)) (m : Γ(M, V)) :
    pullbackPolynomialSectionsEquiv hV H M (c • Scheme.Modules.pullbackApp g M V m) =
      (baseChangePolynomialIso hV H).hom c • PolynomialModule.single Γ(X, V) 0 m := by
  have : IsAffineHom g := isAffineHom_of_isPullback H
  have h := Scheme.Modules.pullbackSectionsEquiv_symm_tmul g M hV (hV.preimage g) c m
  have h2 : Scheme.Modules.pullbackSectionsEquiv g M hV (hV.preimage g)
      (c • Scheme.Modules.pullbackApp g M V m) =
        c ⊗ₜ[Γ(X, V), (g.appLE V (g ⁻¹ᵁ V) le_rfl).hom] m := by
    rw [← h]; exact AddEquiv.apply_symm_apply _ _
  rw [pullbackPolynomialSectionsEquiv, AddEquiv.trans_apply, h2]
  exact polynomialTensorEquiv_tmul hV H Γ(M, V) c m

end Polynomial

end AlgebraicGeometry.CohomologyAux
