/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Ramification.Inertia
import SGA.Foundations.Ramification.IntegralClosure
import SGA.SGA1.ExposeV.FiniteEtaleGalois
import SGA.SGA1.ExposeV.FundamentalGroup
import SGA.SGA1.ExposeV.GaloisAxioms
import SGA.SGA1.ExposeV.QuotientHasQuotients
import SGA.SGA1.ExposeXIII.AffineLinePrimeToP
import SGA.SGA1.ExposeXIII.TameRamification

/-!
# SGA 1, Exposé X, 3.8: Galois coverings and tame ramification at a divisor

In the proof of X.3.8, a Galois covering `Z` of the generic fibre `X_K` of a smooth scheme over a
discrete valuation ring, of degree `n` prime to the residue characteristic `p`, is shown to be
tamely ramified along the closed fibre: at a generic point `ξ` of the closed fibre, the function
field of `Z` is a Galois extension of that of `X` of degree `n`, so its inertia groups have order
prime to `p` (X.3). This file proves the three steps of this argument.

* `isGalois_obj_of_isConnected`: a functor of Galois categories compatible with fibre functors
  sends a Galois object with connected image to a Galois object; `isGalois_of_iso`.
* `isTamelyRamifiedAt_and_dvd_of_isGalois`, `isTamelyRamifiedAt_and_dvd_of_card`: a Galois
  extension of the fraction field of a discrete valuation ring, of degree `n` prime to the residue
  characteristic, is tamely ramified with ramification indices dividing `n` (from
  `ExposeXIII.isTameExtension_of_isGalois` and `ExposeXIII.ramificationIdx_dvd_finrank`).
* `isDomain_and_finrank_eq_card_aut_of_isGalois`: for a Galois object `B` of the étale coverings of
  `Spec A` (`A` a noetherian normal domain with fraction field `K`), `K ⊗_A B` is a Galois field
  extension of `K` whose degree is the number of automorphisms of `B`.
  (A Galois covering of a normal base gives a Galois extension of the function field; cf. V.8.2
  and I.10.1.)
* `isGalois_op_finiteEtale_of_isGalois`: the sections `Γ(Z, Z⁻¹ V)` of a Galois covering `Z` of a
  connected scheme `S` over an affine open `V` form a Galois object over `Γ(S, V)`, with the same
  number of automorphisms (base change to an affine chart).
-/


universe u w

open CategoryTheory PreGaloisCategory IsLocalRing TensorProduct

namespace SGA.SGA1.ExposeX

section GaloisCategory

variable {C D : Type*} [Category C] [Category D] [GaloisCategory C] [GaloisCategory D]
  (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (F' : D ⥤ FintypeCat.{w}) [FiberFunctor F']
  (H : C ⥤ D) (e : H ⋙ F' ≅ F)

include F e in
/-- A functor of Galois categories compatible with fibre functors sends a Galois object to a
Galois object as soon as its image is connected: the automorphisms of `Z` act transitively on
`F(Z) ≅ F'(H Z)` through `H`. -/
theorem isGalois_obj_of_isConnected (Z : C) [IsGalois Z] [IsConnected (H.obj Z)] :
    IsGalois (H.obj Z) := by
  rw [isGalois_iff_pretransitive F']
  refine ⟨fun y y' ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Aut Z)
    (e.hom.app Z y) (e.hom.app Z y')
  refine ⟨H.mapIso σ, ?_⟩
  have hinj : Function.Injective (e.hom.app Z) := fun a b hab ↦ by
    simpa using congrArg (e.inv.app Z) hab
  apply hinj
  change e.hom.app Z (F'.map (H.map σ.hom) y) = e.hom.app Z y'
  have := congrArg (fun φ ↦ φ y) (e.hom.naturality σ.hom)
  simp only [Functor.comp_map, FintypeCat.comp_apply] at this
  rw [this]
  exact hσ

include F' in
/-- Being Galois is invariant under isomorphism. -/
theorem isGalois_of_iso {X Y : D} (i : X ≅ Y) [IsGalois X] : IsGalois Y := by
  have : IsConnected Y := ExposeV.isConnected_of_iso i
  rw [isGalois_iff_pretransitive F']
  refine ⟨fun y y' ↦ ?_⟩
  obtain ⟨σ, hσ⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Aut X)
    (F'.map i.inv y) (F'.map i.inv y')
  refine ⟨i.symm ≪≫ σ ≪≫ i, ?_⟩
  change F'.map (i.inv ≫ σ.hom ≫ i.hom) y = y'
  rw [F'.map_comp, F'.map_comp, FintypeCat.comp_apply, FintypeCat.comp_apply]
  change F'.map i.hom (σ • F'.map i.inv y) = y'
  rw [hσ, ← FintypeCat.comp_apply, ← F'.map_comp, i.inv_hom_id, F'.map_id, FintypeCat.id_apply]

end GaloisCategory

section Tame

variable (V K : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]

/-- A finite Galois extension `L/K` of the fraction field of a discrete valuation ring `V` of
degree prime to the residue characteristic is tamely ramified over `V` (in the sense of X.3), with
ramification indices dividing `[L : K]`: the inertia groups have order dividing `[L : K]`
(`ExposeXIII.isTameExtension_of_isGalois`, compared with the classical notion by
`ExposeXIII.isTameExtension_iff_isTamelyRamifiedOver`), and so do the ramification indices
(`ExposeXIII.ramificationIdx_dvd_finrank`). -/
theorem isTamelyRamifiedAt_and_dvd_of_isGalois (L : Type*) [Field L] [Algebra K L] [Algebra V L]
    [IsScalarTower V K L] [FiniteDimensional K L] [IsGalois K L]
    (hL : (Module.finrank K L : V) ∉ maximalIdeal V) (Q : Ideal (integralClosure V L))
    [Q.IsPrime] (hQ : Q.LiesOver (maximalIdeal V)) :
    ExposeXIII.IsTamelyRamifiedAt V Q ∧ Q.ramificationIdx V ∣ Module.finrank K L := by
  have h : ¬ ringChar (ResidueField V) ∣ Module.finrank K L := by
    rw [ExposeXIII.not_ringChar_dvd_iff, ne_eq,
      ← ExposeXIII.natCast_mem_iff_residueField V (maximalIdeal V)]
    exact hL
  exact ⟨(ExposeXIII.isTameExtension_iff_isTamelyRamifiedOver V L).mp
    (ExposeXIII.isTameExtension_of_isGalois V L h) Q hQ,
    ExposeXIII.ramificationIdx_dvd_finrank V L Q⟩

/-- The same, for a `K`-algebra `B` which is a domain, finite over `K`, with at least `[B : K]`
automorphisms (so `B` is a Galois field extension of `K`): if `[B : K]` is prime to the residue
characteristic, the normalization of `V` in `B` is tamely ramified over `V`, with ramification
indices dividing `[B : K]`. -/
theorem isTamelyRamifiedAt_and_dvd_of_card (B : Type*) [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra V B] [IsScalarTower V K B] [Module.Finite K B]
    (hB : Module.finrank K B ≤ Nat.card (B ≃ₐ[K] B))
    (hL : (Module.finrank K B : V) ∉ maximalIdeal V) (Q : Ideal (integralClosure V B))
    [Q.IsPrime] (hQ : Q.LiesOver (maximalIdeal V)) :
    ExposeXIII.IsTamelyRamifiedAt V Q ∧ Q.ramificationIdx V ∣ Module.finrank K B := by
  have hfield : IsField B := by
    have : Algebra.IsIntegral K B := Algebra.IsIntegral.of_finite K B
    exact (Algebra.IsIntegral.isField_iff_isField (algebraMap K B).injective).mp (Field.toIsField K)
  let : Field B := hfield.toField
  have : IsGalois K B :=
    IsGalois.of_card_aut_eq_finrank K B
      (le_antisymm (by rw [Nat.card_eq_fintype_card]; exact AlgEquiv.card_le) hB)
  exact isTamelyRamifiedAt_and_dvd_of_isGalois V K B hL Q hQ

end Tame

section Algebra

open CommAlgCat

variable {A : Type u} [CommRing A] [IsDomain A] (B : FiniteEtale.{u} A)
  (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]

/-- A Galois covering of a normal base gives a Galois extension of the function field (cf. V.8.2
and I.10.1), in algebra form: let `A` be a noetherian normal domain with fraction field `K` and `B`
a finite étale `A`-algebra which is a Galois object of the category of étale coverings of `Spec A`.
Then `K ⊗_A B` is a domain (so a field), its degree is the number of automorphisms of `B`, and it
has at least that many `K`-automorphisms (those of `B`, base changed): `K ⊗_A B` is a Galois field
extension of `K`. -/
theorem isDomain_and_finrank_eq_card_aut_of_isGalois [IsIntegrallyClosed A] [IsNoetherianRing A]
    [IsGalois (Opposite.op B)] :
    IsDomain (K ⊗[A] B) ∧ Module.finrank K (K ⊗[A] B) = Nat.card (Aut (Opposite.op B)) ∧
      Module.finrank K (K ⊗[A] B) ≤ Nat.card ((K ⊗[A] B) ≃ₐ[K] (K ⊗[A] B)) := by
  classical
  -- `B` is a domain, and `A → B` is injective
  have : ConnectedSpace (PrimeSpectrum B) :=
    (ExposeV.isConnected_op_iff_connectedSpace A B).mp inferInstance
  have : IsDomain B := ExposeXIII.isDomain_of_etale_of_connectedSpace (R := A)
  have hAB : Function.Injective (algebraMap A B) := by
    have : Module.IsTorsionFree A B := inferInstance
    exact Module.isTorsionFree_iff_algebraMap_injective.mp this
  -- `K ⊗_A B` is the localization of `B` at the nonzero elements of `A`
  let : Algebra B (K ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (K ⊗[A] B) :=
    IsLocalization.tensorRight (A := K) (S := B) (nonZeroDivisors A)
  have hle : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hAB).mpr (nonZeroDivisors.ne_zero ha))
  have hdom : IsDomain (K ⊗[A] B) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (K ⊗[A] B) hle
  have hBinj : Function.Injective (algebraMap B (K ⊗[A] B)) :=
    IsLocalization.injective (K ⊗[A] B) hle
  -- the degree is the number of geometric points, i.e. of automorphisms of `B`
  let Ω := AlgebraicClosure K
  let F := ExposeV.fiberFunctor A Ω
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected F (Opposite.op B)
  have h₁ : Module.finrank K (K ⊗[A] B) = Nat.card (B →ₐ[A] Ω) := by
    rw [Nat.card_congr (AlgHom.liftEquiv A K B Ω),
      ExposeV.card_algHom_eq_rankAtStalk (R := K) (A := K ⊗[A] B) Ω,
      Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id]
  have h₂ : Nat.card (B →ₐ[A] Ω) = Nat.card (Aut (Opposite.op B)) :=
    (Nat.card_congr (evaluationEquivOfIsGalois F (Opposite.op B) x)).symm
  refine ⟨hdom, h₁.trans h₂, ?_⟩
  -- the automorphisms of `B` extend to `K ⊗_A B`
  have hfield : IsField (K ⊗[A] B) := by
    have : Algebra.IsIntegral K (K ⊗[A] B) := Algebra.IsIntegral.of_finite K (K ⊗[A] B)
    exact (Algebra.IsIntegral.isField_iff_isField (algebraMap K (K ⊗[A] B)).injective).mp
      (Field.toIsField K)
  let : Field (K ⊗[A] B) := hfield.toField
  let ι : (B.obj ≃ₐ[A] B.obj) → ((K ⊗[A] B) ≃ₐ[K] (K ⊗[A] B)) :=
    fun σ ↦ Algebra.TensorProduct.congr AlgEquiv.refl σ
  have hι : Function.Injective ι := by
    intro σ τ h
    ext b
    apply hBinj
    have := congrArg (fun φ : (K ⊗[A] B) ≃ₐ[K] (K ⊗[A] B) ↦ φ ((1 : K) ⊗ₜ b)) h
    simp only [ι, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul] at this
    exact this
  rw [h₁, h₂, Nat.card_congr (ExposeXIII.autOpEquivAlgEquiv B)]
  exact Nat.card_le_card_of_injective ι hι

end Algebra

section Scheme

open AlgebraicGeometry Limits CommAlgCat

variable {S : Scheme.{u}} [ConnectedSpace S] (Z : ExposeV.FEt S) {V : S.Opens}
  (hV : IsAffineOpen V)

set_option backward.isDefEq.respectTransparency false in
include hV in
/-- Base change of a Galois covering to an affine chart: let `Z` be a Galois étale covering of a
connected scheme `S` and `V ⊆ S` an affine open with `Γ(S, V)` a domain and `Z ×_S V` integral and
nonempty. Then `Γ(Z, Z⁻¹ V)` is a Galois object of the category of étale coverings of
`Spec Γ(S, V)`, with as many automorphisms as `Z`. (The base change of `Z` to `Spec Γ(S, V)` is
`Spec Γ(Z, Z⁻¹ V)`, and it is connected.) -/
theorem isGalois_op_finiteEtale_of_isGalois [IsGalois Z] [IsDomain Γ(S, V)]
    [IsDomain Γ(Z.left, Z.hom ⁻¹ᵁ V)] [Algebra Γ(S, V) Γ(Z.left, Z.hom ⁻¹ᵁ V)]
    (hφ : algebraMap Γ(S, V) Γ(Z.left, Z.hom ⁻¹ᵁ V) = (Z.hom.app V).hom)
    [Module.Finite Γ(S, V) Γ(Z.left, Z.hom ⁻¹ᵁ V)] [Algebra.Etale Γ(S, V) Γ(Z.left, Z.hom ⁻¹ᵁ V)] :
    IsGalois (Opposite.op (FiniteEtale.of Γ(S, V) Γ(Z.left, Z.hom ⁻¹ᵁ V))) ∧
      Nat.card (Aut (Opposite.op (FiniteEtale.of Γ(S, V) Γ(Z.left, Z.hom ⁻¹ᵁ V)))) =
        Nat.card (Aut Z) := by
  classical
  let B : FiniteEtale Γ(S, V) := FiniteEtale.of Γ(S, V) Γ(Z.left, Z.hom ⁻¹ᵁ V)
  have : IsFinite Z.hom := Z.prop.1
  have hW : IsAffineOpen (Z.hom ⁻¹ᵁ V) := hV.preimage Z.hom
  -- the base change of `Z` to `Spec A` is `Spec W₀`
  have hsq : IsPullback hW.fromSpec (Spec.map (Z.hom.app V)) Z.hom hV.fromSpec := by
    refine (IsOpenImmersion.isPullback (Spec.map (Z.hom.app V)) hW.fromSpec hV.fromSpec Z.hom
      ?_ ?_).flip
    · rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec Z.hom hV hW le_rfl]
    · rw [hV.opensRange_fromSpec, hW.opensRange_fromSpec]
  let P := (ExposeV.FEt.pullback hV.fromSpec).obj Z
  let Q := (ExposeV.specFunctor Γ(S, V)).obj (Opposite.op B)
  have hQ : Q.hom = Spec.map (Z.hom.app V) := by
    change Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(Z.left, Z.hom ⁻¹ᵁ V))) = _
    rw [hφ]
    rfl
  let iPQ : P ≅ Q := MorphismProperty.Over.isoMk hsq.isoPullback.symm (by
    change hsq.isoPullback.inv ≫ Q.hom = pullback.snd _ _
    rw [hQ, IsPullback.isoPullback_inv_snd])
  -- a geometric point of `Spec A`
  let Ω := AlgebraicClosure (FractionRing Γ(S, V))
  let s : Spec (CommRingCat.of Ω) ⟶ Spec Γ(S, V) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Ω))
  let := ExposeV.algebraOfPoint Γ(S, V) Ω s
  let H := ExposeV.FEt.pullback hV.fromSpec ⋙ (ExposeV.specEquivalence Γ(S, V)).inverse
  let F' := ExposeV.fiberFunctor Γ(S, V) Ω
  let F := ExposeV.FEt.fiber Ω (s ≫ hV.fromSpec)
  let e : H ⋙ F' ≅ F :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (ExposeV.FEt.pullback hV.fromSpec)
        (ExposeV.FEt.fiberSpecIso Γ(S, V) Ω s).symm ≪≫
      ExposeV.FEt.pullbackFiberIso Ω hV.fromSpec s
  -- `H Z ≅ Spec W₀` is connected
  let iH : H.obj Z ≅ Opposite.op B :=
    (ExposeV.specEquivalence Γ(S, V)).inverse.mapIso iPQ ≪≫
      ((ExposeV.specEquivalence Γ(S, V)).unitIso.app (Opposite.op B)).symm
  have : ConnectedSpace (PrimeSpectrum Γ(Z.left, Z.hom ⁻¹ᵁ V)) := inferInstance
  have : IsConnected (Opposite.op B) :=
    (ExposeV.isConnected_op_iff_connectedSpace Γ(S, V) B).mpr this
  have : IsConnected (H.obj Z) := ExposeV.isConnected_of_iso iH.symm
  have : IsGalois (H.obj Z) := isGalois_obj_of_isConnected F F' H e Z
  have hgal : IsGalois (Opposite.op B) := isGalois_of_iso F' iH
  refine ⟨hgal, ?_⟩
  obtain ⟨x⟩ := nonempty_fiber_of_isConnected F' (Opposite.op B)
  obtain ⟨z⟩ := nonempty_fiber_of_isConnected F Z
  rw [Nat.card_congr (evaluationEquivOfIsGalois F' (Opposite.op B) x),
    Nat.card_congr (evaluationEquivOfIsGalois F Z z)]
  exact Nat.card_congr ((FintypeCat.equivEquivIso.symm (F'.mapIso iH)).symm.trans
    (FintypeCat.equivEquivIso.symm (e.app Z)))

end Scheme

end SGA.SGA1.ExposeX
