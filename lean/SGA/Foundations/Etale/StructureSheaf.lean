/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.AffineSpace
import SGA.Foundations.Etale.Representable
import SGA.Foundations.Etale.TorsorProduct

/-!
# The structure sheaf and the multiplicative group on the small étale site

The functor `V ↦ Γ(V, 𝒪_V)` on schemes is represented by the affine line `Spec ℤ[T]`
(`AffineSpace.toSpecMvPolyIntEquiv`), hence it is a sheaf for the étale topology, which is
subcanonical (`Scheme.isSheaf_etaleTopology_Γ`). Restricting to the small étale site of a scheme
`X` gives the étale structure sheaf `𝒪_{X_et}` (`Scheme.etaleStructurePresheaf`), and its units
form the sheaf of commutative groups `𝔾_m` on `X_et` (`Scheme.etaleGm`), so that
`H¹(X_et, 𝔾_m)` is a commutative group.

Units of any sheaf of commutative rings form a sheaf of groups
(`PresheafOfCommRings.isSheaf_units`).

## References

* [SGA 4, Exposé VII, 2][sga4]
-/

universe w v u

open CategoryTheory Limits Opposite

-- See the comment in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.PresheafOfCommRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The presheaf of groups of units of a presheaf of commutative rings. -/
@[simps obj]
def units (O : Cᵒᵖ ⥤ CommRingCat.{w}) : Cᵒᵖ ⥤ GrpCat.{w} where
  obj U := GrpCat.of (O.obj U)ˣ
  map f := GrpCat.ofHom (Units.map (O.map f).hom.toMonoidHom)
  map_id U := by
    ext a
    simp
  map_comp f g := by
    ext a
    simp

variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

@[simp]
lemma coe_units_map {U V : Cᵒᵖ} (f : U ⟶ V) (a : (O.obj U)ˣ) :
    ((show (O.obj V)ˣ from (units O).map f a) : O.obj V) = O.map f a :=
  rfl

lemma isCommutative_units : PresheafOfGroups.IsCommutative (units O) :=
  fun _ a b ↦ mul_comm (show (O.obj _)ˣ from a) b

variable {O}

/-- The units of a sheaf of commutative rings form a sheaf of groups. -/
lemma isSheaf_units (hO : Presieve.IsSheaf J (O ⋙ CategoryTheory.forget CommRingCat)) :
    Presieve.IsSheaf J (units O ⋙ CategoryTheory.forget GrpCat) := by
  intro U S hS x hx
  have hO := hO S hS
  let x' : ∀ ⦃V : C⦄ (f : V ⟶ U), S f → (O.obj (op V))ˣ := fun V f hf ↦ x f hf
  let a : Presieve.FamilyOfElements (O ⋙ CategoryTheory.forget _) S :=
    fun V f hf ↦ ((x' f hf : (O.obj (op V))ˣ) : O.obj (op V))
  let b : Presieve.FamilyOfElements (O ⋙ CategoryTheory.forget _) S :=
    fun V f hf ↦ (((x' f hf)⁻¹ : (O.obj (op V))ˣ) : O.obj (op V))
  have hx' : ∀ ⦃V₁ V₂ W : C⦄ (g₁ : W ⟶ V₁) (g₂ : W ⟶ V₂) (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U)
      (h₁ : S f₁) (h₂ : S f₂), g₁ ≫ f₁ = g₂ ≫ f₂ →
        (show (O.obj (op W))ˣ from (units O).map g₁.op (x' f₁ h₁)) =
          (units O).map g₂.op (x' f₂ h₂) :=
    fun V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ w ↦ hx g₁ g₂ h₁ h₂ w
  have ha : a.Compatible := fun V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congr_arg (fun u : (O.obj (op W))ˣ ↦ (u : O.obj (op W))) (hx' g₁ g₂ f₁ f₂ h₁ h₂ w)
  have hb : b.Compatible := fun V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congr_arg (fun u : (O.obj (op W))ˣ ↦ ((u⁻¹ : (O.obj (op W))ˣ) : O.obj (op W)))
      (hx' g₁ g₂ f₁ f₂ h₁ h₂ w)
  obtain ⟨s, hs, -⟩ := hO a ha
  obtain ⟨t, ht, -⟩ := hO b hb
  have hst : s * t = 1 := by
    refine hO.isSeparatedFor.ext fun V f hf ↦ ?_
    change O.map f.op (s * t) = O.map f.op 1
    rw [map_mul, map_one]
    have e₁ : O.map f.op s = a f hf := hs f hf
    have e₂ : O.map f.op t = b f hf := ht f hf
    rw [e₁, e₂]
    exact (x' f hf).mul_inv
  let v : (O.obj (op U))ˣ := ⟨s, t, hst, by rw [mul_comm]; exact hst⟩
  refine ⟨v, fun V f hf ↦ Units.ext (hs f hf), fun v' hv' ↦ Units.ext ?_⟩
  refine hO.isSeparatedFor.ext fun V f hf ↦ ?_
  exact (congr_arg (fun w : (O.obj (op V))ˣ ↦ (w : O.obj (op V))) (hv' f hf)).trans
    (hs f hf).symm

end CategoryTheory.PresheafOfCommRings

namespace AlgebraicGeometry.Scheme

/-- Global sections `V ↦ Γ(V, 𝒪_V)` are represented by the affine line over `ℤ`. -/
noncomputable def yonedaAffineLineIso :
    yoneda.obj (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))) ≅
      Scheme.Γ ⋙ CategoryTheory.forget CommRingCat :=
  NatIso.ofComponents
    (fun V ↦ Equiv.toIso ((AffineSpace.toSpecMvPolyIntEquiv PUnit).trans
      (Equiv.funUnique PUnit _)))
    (fun {V W} f ↦ by
      ext g
      exact AffineSpace.toSpecMvPolyIntEquiv_comp PUnit f.unop g PUnit.unit)

/-- The global sections functor is a sheaf for the étale topology. -/
lemma isSheaf_etaleTopology_Γ :
    Presieve.IsSheaf etaleTopology (Scheme.Γ ⋙ CategoryTheory.forget CommRingCat) := by
  exact Presieve.isSheaf_iso _ yonedaAffineLineIso
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

variable (X : Scheme.{u})

/-- The structure sheaf `𝒪_{X_et}` on the small étale site: `V ↦ Γ(V, 𝒪_V)`. -/
noncomputable abbrev etaleStructurePresheaf : X.Etaleᵒᵖ ⥤ CommRingCat.{u} :=
  (Etale.forget X ⋙ CategoryTheory.Over.forget X).op ⋙ Scheme.Γ

lemma isSheaf_etaleStructurePresheaf :
    Presieve.IsSheaf X.smallEtaleTopology
      (X.etaleStructurePresheaf ⋙ CategoryTheory.forget CommRingCat) :=
  have : (Etale.forget X ⋙ CategoryTheory.Over.forget X).IsContinuous X.smallEtaleTopology
      etaleTopology :=
    Functor.isContinuous_comp _ _ _ (etaleTopology.over X) _
  Functor.op_comp_isSheaf_of_isSheaf_type _ _ isSheaf_etaleTopology_Γ

/-- The multiplicative group `𝔾_m` on the small étale site of `X`: `V ↦ Γ(V, 𝒪_V)ˣ`. -/
noncomputable abbrev etaleGm : X.Etaleᵒᵖ ⥤ GrpCat.{u} :=
  PresheafOfCommRings.units X.etaleStructurePresheaf

lemma isSheaf_etaleGm :
    Presieve.IsSheaf X.smallEtaleTopology (X.etaleGm ⋙ CategoryTheory.forget GrpCat) :=
  PresheafOfCommRings.isSheaf_units X.isSheaf_etaleStructurePresheaf

lemma isCommutative_etaleGm : PresheafOfGroups.IsCommutative X.etaleGm :=
  PresheafOfCommRings.isCommutative_units _

/-- `H¹(X_et, 𝔾_m)` is a commutative group under the contracted product of torsors. -/
noncomputable instance : CommGroup (H1 X.smallEtaleTopology X.etaleGm) :=
  H1.commGroup X.isCommutative_etaleGm X.isSheaf_etaleGm

end AlgebraicGeometry.Scheme
