/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.RelativeSpecUniversal
import SGA.Foundations.Cohomology.ExistenceFullyFaithful
import SGA.Foundations.Differentials.AffineOpens
import SGA.Foundations.Differentials.QuasiCoherent
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Étaleness of algebraized finite algebras

Let `A` be a noetherian `I`-adically complete ring, `f : X ⟶ Spec A` proper, and `B` a coherent,
locally projective `𝒪_X`-algebra (a `ModuleAlgebra`) whose reduction `G = B / I B` is an unramified
`𝒪_X`-algebra. Then `Spec_X B ⟶ X` is étale (EGA III 5.4.5 in the case of finite étale covers;
SGA 1 III.7, IX.1.10).

* `kaehler_smul_top_eq_top`: if `T' = T / J T` is formally unramified over `R`, then
  `Ω[T/R] = J Ω[T/R]` (conormal sequence).
* `ModuleAlgebra.homRingHom`: an algebra morphism `B ⟶ G` on sections, as a ring homomorphism.
* `kaehler_relSpecSections_eq_smul`: `Ω = I Ω` for `Spec_X B ⟶ X` over each affine open.
* `pushforwardDifferentialsEquiv`: `Γ(U, p_* Ω_{Y/X}) ≅ Ω[Γ(Y, p⁻¹ U)/Γ(X, U)]` for `p` affine.
* `etale_relativeSpecHom_of_reduction`: the main result. The coherent module `p_* Ω` satisfies
  `Q = I Q`, hence vanishes by the uniqueness half of the existence theorem
  (`eq_zero_of_comp_toQuotientIdealPow_eq_zero`); flat, finitely presented and unramified algebras
  are étale.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

section OmegaLemma

variable {R T T' : Type u} [CommRing R] [CommRing T] [CommRing T'] [Algebra R T] [Algebra R T']
  [Algebra T T'] [IsScalarTower R T T']

/-- If `T' = T / J T` is formally unramified over `R`, then `Ω[T/R] = J Ω[T/R]`. -/
theorem kaehler_smul_top_eq_top (J : Ideal R) (hsurj : Function.Surjective (algebraMap T T'))
    (hker : RingHom.ker (algebraMap T T') = J.map (algebraMap R T))
    [Algebra.FormallyUnramified R T'] :
    (J • ⊤ : Submodule R Ω[T⁄R]) = ⊤ := by
  classical
  -- Step 1: `T' ⊗[T] Ω[T⁄R] = 0`.
  have hD : ∀ y ∈ J.map (algebraMap R T),
      (1 : T') ⊗ₜ[T] KaehlerDifferential.D R T y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, -, rfl⟩ := hx
      rw [Derivation.map_algebraMap, tmul_zero]
    | zero => rw [map_zero, tmul_zero]
    | add x y _ _ hx hy => rw [map_add, tmul_add, hx, hy, add_zero]
    | smul t x hx' hx =>
      have hx0 : algebraMap T T' x = 0 := by
        rw [← RingHom.mem_ker, hker]
        exact hx'
      rw [smul_eq_mul, Derivation.leibniz, tmul_add, tmul_smul, tmul_smul, hx, smul_zero,
        zero_add, smul_tmul', Algebra.smul_def, hx0, zero_mul, zero_tmul]
  have h1 : ∀ x : T' ⊗[T] Ω[T⁄R], x = 0 := by
    intro x
    have hx : KaehlerDifferential.mapBaseChange R T T' x = 0 := Subsingleton.elim _ _
    obtain ⟨c, rfl⟩ :=
      (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R T T' hsurj x).mp hx
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ c
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
    exact hD y.1 (hker ▸ y.2)
  -- Step 2: `Ω / K Ω = 0` for `K = ker (T → T')`.
  let K := RingHom.ker (algebraMap T T')
  let e : T' ≃ₐ[T] T ⧸ K :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId T T') hsurj).symm
  let E : T' ⊗[T] Ω[T⁄R] ≃ₗ[T] Ω[T⁄R] ⧸ (K • ⊤ : Submodule T Ω[T⁄R]) :=
    (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl T Ω[T⁄R])).trans
      (quotTensorEquivQuotSMul Ω[T⁄R] K)
  have h2 : (K • ⊤ : Submodule T Ω[T⁄R]) = ⊤ := by
    rw [eq_top_iff]
    intro ω _
    rw [← Submodule.Quotient.mk_eq_zero]
    have := congrArg E (h1 (E.symm (Submodule.Quotient.mk ω)))
    rwa [LinearEquiv.apply_symm_apply, map_zero] at this
  -- Step 3: `K Ω ⊆ J Ω`.
  have hsub : ∀ a ∈ J.map (algebraMap R T), ∀ w : Ω[T⁄R],
      a • w ∈ (J • ⊤ : Submodule R Ω[T⁄R]) := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro w
      rw [algebraMap_smul]
      exact Submodule.smul_mem_smul hj Submodule.mem_top
    | zero => intro w; rw [zero_smul]; exact zero_mem _
    | add x y _ _ hx hy => intro w; rw [add_smul]; exact add_mem (hx w) (hy w)
    | smul t x _ hx =>
      intro w
      rw [smul_eq_mul, mul_comm, mul_smul]
      exact hx (t • w)
  rw [eq_top_iff]
  intro ω _
  have hω : ω ∈ (K • ⊤ : Submodule T Ω[T⁄R]) := by rw [h2]; exact Submodule.mem_top
  rw [show K = J.map (algebraMap R T) from hker] at hω
  exact Submodule.smul_induction_on (p := fun z ↦ z ∈ (J • ⊤ : Submodule R Ω[T⁄R])) hω
    (fun a ha w _ ↦ hsub a ha w) (fun x y hx hy ↦ add_mem hx hy)

end OmegaLemma

section Reduction

variable {X : Scheme.{u}} {B G : X.Modules} (algB : ModuleAlgebra B) (alg : ModuleAlgebra G)
  (red : B ⟶ G)
  (hmul : ∀ (U : X.Opens) (x y : Γ(B, U)),
    red.app U (mulApp algB.mul U x y) = mulApp alg.mul U (red.app U x) (red.app U y))
  (hone : red.app ⊤ algB.one = alg.one)

include hmul hone in
/-- An algebra morphism `B ⟶ G`, on sections over `U`, as a ring homomorphism. -/
def ModuleAlgebra.homRingHom (U : X.Opens) : algB.Sections U →+* alg.Sections U where
  toFun (x : Γ(B, U)) := (red.app U x : Γ(G, U))
  map_mul' (x y : Γ(B, U)) := hmul U x y
  map_one' := by
    change red.app U (B.presheaf.map (homOfLE le_top).op algB.one) =
      G.presheaf.map (homOfLE le_top).op alg.one
    rw [hom_app_presheaf_map, hone]
  map_zero' := (red.app U).hom.map_zero
  map_add' (x y : Γ(B, U)) := (red.app U).hom.map_add x y

lemma ModuleAlgebra.homRingHom_apply (U : X.Opens) (x : Γ(B, U)) :
    algB.homRingHom alg red hmul hone U x = red.app U x := rfl

lemma ModuleAlgebra.homRingHom_algebraMap (U : X.Opens) (r : Γ(X, U)) :
    algB.homRingHom alg red hmul hone U (algebraMap Γ(X, U) (algB.Sections U) r) =
      algebraMap Γ(X, U) (alg.Sections U) r := by
  rw [ModuleAlgebra.algebraMap_def, ModuleAlgebra.algebraMap_def]
  change red.app U (r • (algB.oneApp U : Γ(B, U))) = r • (alg.oneApp U : Γ(G, U))
  rw [Scheme.Modules.Hom.app_smul]
  congr 1
  exact (algB.homRingHom alg red hmul hone U).map_one

end Reduction

section Etale

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A)
  {B G : X.Modules} [B.IsQuasicoherent] (algB : ModuleAlgebra B) (alg : ModuleAlgebra G)
  (red : B ⟶ G)
  (hmul : ∀ (U : X.Opens) (x y : Γ(B, U)),
    red.app U (mulApp algB.mul U x y) = mulApp alg.mul U (red.app U x) (red.app U y))
  (hone : red.app ⊤ algB.one = alg.one)
  (hsurj : ∀ {U : X.Opens}, IsAffineOpen U → Function.Surjective (red.app U))
  (hker : ∀ {U : X.Opens}, IsAffineOpen U → ∀ x : Γ(B, U),
    red.app U x = 0 ↔ x ∈ (idealV f I U 1 • ⊤ : Submodule Γ(X, U) Γ(B, U)))
  (hunr : ∀ U : X.AffineZariskiSite,
    Algebra.FormallyUnramified Γ(X, U.toOpens) (alg.Sections U.toOpens))

/-- The ring `Γ(Spec_X B, p⁻¹ U)` as an algebra over `Γ(X, U)`. -/
abbrev ModuleAlgebra.relSpecSections (U : X.AffineZariskiSite) : Type u :=
  Γ(algB.relativeSpec, algB.relativeSpecHom ⁻¹ᵁ U.toOpens)

/-- The structure map `Γ(X, U) → Γ(Spec_X B, p⁻¹ U)`. -/
abbrev ModuleAlgebra.relSpecAppLE (U : X.AffineZariskiSite) :=
  algB.relativeSpecHom.appLE U.toOpens (algB.relativeSpecHom ⁻¹ᵁ U.toOpens) le_rfl

lemma ModuleAlgebra.sectionsIso_hom_appLE (U : X.AffineZariskiSite) (r : Γ(X, U.toOpens)) :
    (algB.sectionsIso U).hom (algB.relSpecAppLE U r) =
      algebraMap Γ(X, U.toOpens) (algB.Sections U.toOpens) r := by
  rw [ModuleAlgebra.relSpecAppLE, ← Scheme.Hom.app_eq_appLE, algB.relativeSpecHom_app U]
  change (algB.sectionsIso U).hom ((algB.sectionsIso U).inv _) = _
  rw [Iso.inv_hom_id_apply]
  rfl

include hmul hone hsurj hker hunr in
/-- The Kähler differentials of `Spec_X B` over `X`, on the inverse image of an affine open `U`,
satisfy `Ω = I Ω`, since `B / I B` is unramified. -/
theorem kaehler_relSpecSections_eq_smul (U : X.AffineZariskiSite) :
    letI := (algB.relSpecAppLE U).hom.toAlgebra
    (idealV f I U.toOpens 1 • ⊤ :
      Submodule Γ(X, U.toOpens) Ω[algB.relSpecSections U⁄Γ(X, U.toOpens)]) = ⊤ := by
  let _ := (algB.relSpecAppLE U).hom.toAlgebra
  let σ : algB.relSpecSections U ≃ₐ[Γ(X, U.toOpens)] algB.Sections U.toOpens :=
    AlgEquiv.ofRingEquiv (f := (algB.sectionsIso U).commRingCatIsoToRingEquiv)
      (algB.sectionsIso_hom_appLE U)
  let ψ : algB.relSpecSections U →+* alg.Sections U.toOpens :=
    (algB.homRingHom alg red hmul hone U.toOpens).comp σ.toRingEquiv.toRingHom
  let _ : Algebra (algB.relSpecSections U) (alg.Sections U.toOpens) := ψ.toAlgebra
  have : IsScalarTower Γ(X, U.toOpens) (algB.relSpecSections U) (alg.Sections U.toOpens) :=
    .of_algebraMap_eq fun r ↦ by
      change _ = algB.homRingHom alg red hmul hone U.toOpens (σ (algebraMap _ _ r))
      rw [AlgEquiv.commutes, ModuleAlgebra.homRingHom_algebraMap]
  have := hunr U
  refine kaehler_smul_top_eq_top (T' := alg.Sections U.toOpens) (idealV f I U.toOpens 1) ?_ ?_
  · exact (hsurj U.2).comp σ.surjective
  · ext t
    rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem Γ(X, U.toOpens),
      ← Ideal.smul_top_eq_map]
    let e : algB.relSpecSections U ≃ₗ[Γ(X, U.toOpens)] Γ(B, U.toOpens) :=
      σ.toLinearEquiv.trans (LinearEquiv.refl _ Γ(B, U.toOpens))
    refine (hker U.2 (e t)).trans ⟨fun h ↦ ?_, fun h ↦ mem_smul_top_of_linearMap _ e.toLinearMap h⟩
    have := mem_smul_top_of_linearMap _ e.symm.toLinearMap h
    rwa [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this

end Etale

section PushforwardDifferentials

variable {X Y : Scheme.{u}} (p : Y ⟶ X) [IsAffineHom p]

/-- `Γ(U, p_* Ω_{Y/X}) ≅ Ω[Γ(Y, p⁻¹ U)/Γ(X, U)]` as `Γ(X, U)`-modules, for `p` affine and `U`
an affine open. -/
def pushforwardDifferentialsEquiv {U : X.Opens} (hU : IsAffineOpen U) :
    letI := (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    Γ((Scheme.Modules.pushforward p).obj p.relativeDifferentials, U) ≃ₗ[Γ(X, U)]
      Ω[Γ(Y, p ⁻¹ᵁ U)⁄Γ(X, U)] :=
  letI := (p.appLE U (p ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  { (p.relativeDifferentialsAppEquiv (hU.preimage p) hU le_rfl).toAddEquiv with
    map_smul' r x := by
      let e := p.relativeDifferentialsAppEquiv (hU.preimage p) hU le_rfl
      have h1 := e.map_smul (p.app U r) (show Γ(p.relativeDifferentials, p ⁻¹ᵁ U) from x)
      refine h1.trans ?_
      rw [Scheme.Hom.app_eq_appLE]
      exact algebraMap_smul (A := Γ(Y, p ⁻¹ᵁ U)) r (show Ω[Γ(Y, p ⁻¹ᵁ U)⁄Γ(X, U)] from e x) }

end PushforwardDifferentials

section EtaleProper

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} (f : X ⟶ Spec A) [IsProper f]
  {B G : X.Modules} [B.IsQuasicoherent] [B.IsFiniteType] (algB : ModuleAlgebra B)
  (alg : ModuleAlgebra G) (red : B ⟶ G)
  (hmul : ∀ (U : X.Opens) (x y : Γ(B, U)),
    red.app U (mulApp algB.mul U x y) = mulApp alg.mul U (red.app U x) (red.app U y))
  (hone : red.app ⊤ algB.one = alg.one)
  (hsurj : ∀ {U : X.Opens}, IsAffineOpen U → Function.Surjective (red.app U))
  (hker : ∀ {U : X.Opens}, IsAffineOpen U → ∀ x : Γ(B, U),
    red.app U x = 0 ↔ x ∈ (idealV f I U 1 • ⊤ : Submodule Γ(X, U) Γ(B, U)))
  (hunr : ∀ U : X.AffineZariskiSite,
    Algebra.FormallyUnramified Γ(X, U.toOpens) (alg.Sections U.toOpens))
  (hproj : ∀ {U : X.Opens}, IsAffineOpen U → Module.Projective Γ(X, U) Γ(B, U))

lemma smul_top_pow_eq_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (J : Ideal R)
    (h : (J • ⊤ : Submodule R M) = ⊤) (n : ℕ) : (J ^ n • ⊤ : Submodule R M) = ⊤ := by
  induction n with
  | zero => rw [pow_zero, Submodule.one_smul]
  | succ n ih => rw [pow_succ, Submodule.mul_smul, h, ih]

include hmul hone hsurj hker hunr hproj in
/-- **Étaleness of the algebraization** (EGA III 5.4.5 / SGA 1 III.7): let `A` be a noetherian
`I`-adically complete ring, `X` proper over `Spec A` and `B` a coherent `𝒪_X`-algebra, locally
projective, whose reduction `B / I B` is unramified over `X`. Then `Spec_X B ⟶ X` is (finite)
étale. The module `Q = p_* Ω` of relative differentials satisfies `Q = I Q` on affine opens, hence
vanishes by the uniqueness half of the existence theorem. -/
theorem etale_relativeSpecHom_of_reduction : Etale algB.relativeSpecHom := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let p := algB.relativeSpecHom
  let Q := (Scheme.Modules.pushforward p).obj p.relativeDifferentials
  have hQq : Q.IsQuasicoherent := isQuasicoherent_pushforward p _
  -- the algebra isomorphism `Γ(p⁻¹ U) ≅ Γ(B, U)`
  have hfin : ∀ U : X.AffineZariskiSite,
      letI := (algB.relSpecAppLE U).hom.toAlgebra
      Module.Finite Γ(X, U.toOpens) (algB.relSpecSections U) := fun U ↦ by
    let _ := (algB.relSpecAppLE U).hom.toAlgebra
    let σ : algB.relSpecSections U ≃ₐ[Γ(X, U.toOpens)] algB.Sections U.toOpens :=
      AlgEquiv.ofRingEquiv (f := (algB.sectionsIso U).commRingCatIsoToRingEquiv)
        (algB.sectionsIso_hom_appLE U)
    have : Module.Finite Γ(X, U.toOpens) (algB.Sections U.toOpens) :=
      finite_sections_of_isFiniteType B U.2
    exact Module.Finite.equiv σ.symm.toLinearEquiv
  have hQfin : ∀ U : X.AffineZariskiSite, Module.Finite Γ(X, U.toOpens) Γ(Q, U.toOpens) :=
    fun U ↦ by
    let _ := (algB.relSpecAppLE U).hom.toAlgebra
    have := hfin U
    have : Module.Finite Γ(X, U.toOpens) Ω[algB.relSpecSections U⁄Γ(X, U.toOpens)] :=
      Module.Finite.trans (algB.relSpecSections U) _
    exact Module.Finite.equiv (pushforwardDifferentialsEquiv p U.2).symm
  have : Q.IsFiniteType :=
    isFiniteType_of_finite_sections Q (fun U : X.AffineZariskiSite ↦ U.toOpens) (by
      refine top_le_iff.mp fun x _ ↦ ?_
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U.1, U.2⟩, hU⟩) (fun U ↦ U.2) hQfin
  have : Q.IsCoherent := { isQuasicoherent := hQq, isFiniteType := this }
  -- `Q = I Q` on affine opens
  have hQI : ∀ U : X.AffineZariskiSite,
      (idealV f I U.toOpens 1 • ⊤ : Submodule Γ(X, U.toOpens) Γ(Q, U.toOpens)) = ⊤ := fun U ↦ by
    let _ := (algB.relSpecAppLE U).hom.toAlgebra
    have h := kaehler_relSpecSections_eq_smul I f algB alg red hmul hone hsurj hker hunr U
    refine eq_top_iff.mpr fun x _ ↦ ?_
    have hx := mem_smul_top_of_linearMap (idealV f I U.toOpens 1)
      (pushforwardDifferentialsEquiv p U.2).symm.toLinearMap
      (h.ge (Submodule.mem_top (x := pushforwardDifferentialsEquiv p U.2 x)))
    rwa [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hx
  have hQ0 : 𝟙 Q = 0 := by
    refine eq_zero_of_comp_toQuotientIdealPow_eq_zero I f (𝟙 Q) fun n ↦ ?_
    refine hom_ext_of_affine fun U hU s ↦ ?_
    rw [Category.id_comp]
    change (Q.toQuotientIdealPow f I n).app U s = 0
    rw [toQuotientIdealPow_app_eq_zero_iff' I f Q hU,
      smul_top_pow_eq_top _ (hQI ⟨U, hU⟩) (n + 1)]
    exact Submodule.mem_top
  refine algB.etale_relativeSpecHom fun U ↦ ?_
  let _ := (algB.relSpecAppLE U).hom.toAlgebra
  have : Subsingleton Γ(Q, U.toOpens) := ⟨fun x y ↦ by
    have hx : (𝟙 Q : Q ⟶ Q).app U.toOpens x = x := rfl
    have hy : (𝟙 Q : Q ⟶ Q).app U.toOpens y = y := rfl
    rw [← hx, ← hy, hQ0]
    rfl⟩
  have : Subsingleton Ω[algB.relSpecSections U⁄Γ(X, U.toOpens)] :=
    (pushforwardDifferentialsEquiv p U.2).symm.injective.subsingleton
  have : Algebra.FormallyUnramified Γ(X, U.toOpens) (algB.relSpecSections U) := ⟨this⟩
  let σ : algB.relSpecSections U ≃ₐ[Γ(X, U.toOpens)] algB.Sections U.toOpens :=
    AlgEquiv.ofRingEquiv (f := (algB.sectionsIso U).commRingCatIsoToRingEquiv)
      (algB.sectionsIso_hom_appLE U)
  have : Algebra.FormallyUnramified Γ(X, U.toOpens) (algB.Sections U.toOpens) :=
    .of_equiv σ
  have : IsNoetherianRing Γ(X, U.toOpens) :=
    IsLocallyNoetherian.component_noetherian ⟨U.toOpens, U.2⟩
  have : Module.Finite Γ(X, U.toOpens) (algB.Sections U.toOpens) :=
    finite_sections_of_isFiniteType B U.2
  have : Algebra.FinitePresentation Γ(X, U.toOpens) (algB.Sections U.toOpens) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.Projective Γ(X, U.toOpens) (algB.Sections U.toOpens) := hproj U.2
  exact Algebra.Etale.of_formallyUnramified_of_flat

end EtaleProper

end AlgebraicGeometry.CohomologyAux
