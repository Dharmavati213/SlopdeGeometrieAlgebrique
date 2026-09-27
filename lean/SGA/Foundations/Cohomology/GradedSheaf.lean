/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.AdicSheafSystem
import SGA.Foundations.Cohomology.ExistenceFullyFaithful
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Algebra.Order.Antidiag.Finsupp
import SGA.Foundations.QuasiCoherent.Pullback

/-!
# The graded sheaf of an adic system

Let `A` be a ring, `I = (a_σ)` a finitely generated ideal, `f : X ⟶ Spec A` with `X` noetherian,
and `(G_n)` an adic system of `𝒪_X`-modules (`AdicSystem`) with `G₀` of finite type. On
`Y = X ×_A A[y_σ]` (`GradedSetup`, with the affine projection `q : Y ⟶ X`) we construct a
quasi-coherent module of finite type `grSheaf` (EGA III 4.1.7 / 5.2.1 in the form of
EGA 0_III 10.1.1 and Hartshorne II.9.6: "the graded sheaf `⊕ₖ Iᵏ G_k`") such that every graded
piece `I^{k+1} G_{k+1} = ker(G_{k+1} → G_k)` (`AdicSystem.grSucc`) is a direct summand of
`q_* grSheaf`:

* `GradedSetup.gen`: the surjection `⊕_{|α| = k+1} G₀ ⟶ I^{k+1} G_{k+1}`,
  `(x_α) ↦ Σ a^α x̃_α`, with kernel `rel k`;
* `GradedSetup.grSheaf`: `q^* G₀` modulo the images of `q^*(rel j)` under
  `(x_α) ↦ Σ y^α x_α`, `j < degBound` (the relations stabilize by noetherianity,
  `GradedSetup.exists_stab`);
* `GradedSetup.iMap : I^{k+1} G_{k+1} ⟶ q_* grSheaf` and the projection
  `GradedSetup.πMap : q_* grSheaf ⟶ I^{k+1} G_{k+1}` onto the degree `k + 1` part,
  with `iMap_πMap : iMap ≫ πMap = 𝟙` (the degree components of `Σ_β c_β y^β x` are
  `Σ_{|β| = k+1} c_β a^β x̃`, `GradedSetup.lamFun`, and kill the relations by the combinatorial
  identity `AdicSystem.sum_coeff_mulUp_eq_zero`);
* `GradedSetup.isCoherent_grSheaf`: `grSheaf` is coherent.

These are used to obtain the vanishing of `H¹(X, I^{k+1} G_{k+1}(d))` uniformly in `k`
(`SGA.Foundations.Cohomology.UniformVanishing`), the key step of the existence theorem.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

section Helpers

variable {X : Scheme.{u}}

/-- Sections of a cokernel over an affine open: surjectivity. -/
lemma cokernel_π_app_surjective {P Q : X.Modules} [P.IsQuasicoherent] [Q.IsQuasicoherent]
    (φ : P ⟶ Q) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective ((cokernel.π φ).app U) := by
  have hS := shortExact_kernelSequence (cokernel.π φ)
  have : (kernel (cokernel.π φ)).IsQuasicoherent := isQuasicoherent_image φ
  exact TopCat.Sheaf.surjective_app_of_subsingleton_H'_one
    (Scheme.Modules.shortExact_abShortComplex hS) U
    ((kernel (cokernel.π φ)).H'_subsingleton_of_isAffineOpen hU 0)

/-- Sections of a cokernel over an affine open: the kernel. -/
lemma cokernel_π_app_eq_zero_iff {P Q : X.Modules} [P.IsQuasicoherent] [Q.IsQuasicoherent]
    (φ : P ⟶ Q) {U : X.Opens} (hU : IsAffineOpen U) (t : Γ(Q, U)) :
    (cokernel.π φ).app U t = 0 ↔ t ∈ Set.range (φ.app U) := by
  have hS := shortExact_kernelSequence (cokernel.π φ)
  constructor
  · intro h
    obtain ⟨w, rfl⟩ := exists_app_eq_of_shortExact hS U t h
    obtain ⟨v, rfl⟩ := surjective_factorThruImage_app φ hU w
    refine ⟨v, ?_⟩
    have e : Abelian.factorThruImage φ ≫ (ShortComplex.kernelSequence (cokernel.π φ)).f = φ :=
      Abelian.image.fac φ
    conv_lhs => rw [← e]
    rfl
  · rintro ⟨v, rfl⟩
    rw [← Scheme.Modules.Hom.comp_app_apply, cokernel.condition]
    rfl

/-- A morphism out of a quasi-coherent module vanishing on the sections over the members of an
affine open cover is zero. -/
lemma eq_zero_of_app_affineCover {P Q : X.Modules} [P.IsQuasicoherent] (φ : P ⟶ Q) {ι : Type*}
    (V : ι → X.Opens) (hV : ⨆ i, V i = ⊤) (hVa : ∀ i, IsAffineOpen (V i))
    (h : ∀ i (m : Γ(P, V i)), φ.app (V i) m = 0) : φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext m
  apply Q.isSheaf.section_ext (U := op W)
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hV.ge (Set.mem_univ x))
  obtain ⟨c, hcW, hxc⟩ := (hVa i).exists_basicOpen_le ⟨x, hx⟩ hi
  refine ⟨X.basicOpen c, hcW, hxc, ?_⟩
  rw [← hom_app_presheaf_map]
  have h0 : ∀ m', (1 : Γ(X, V i)) • φ.app (V i) m' = 0 := fun m' ↦ by rw [one_smul, h i m']
  have h1 := app_eq_zero_of_smul_eq_zero φ (hVa i) 1 h0 (U := X.basicOpen c)
    (by rw [Scheme.basicOpen_one]; exact X.basicOpen_le c) (P.presheaf.map (homOfLE hcW).op m)
  rw [h1]
  change 0 = Q.presheaf.map (homOfLE hcW).op 0
  rw [map_zero]

/-- Morphisms out of a quasi-coherent module agreeing on sections over affine opens are equal. -/
lemma hom_ext_of_affine {P Q : X.Modules} [P.IsQuasicoherent] {φ ψ : P ⟶ Q}
    (h : ∀ (U : X.Opens) (_ : IsAffineOpen U) (m : Γ(P, U)), φ.app U m = ψ.app U m) :
    φ = ψ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_app_affineCover _ (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X)
    (fun U ↦ U.2) fun U m ↦ ?_
  rw [Scheme.Modules.Hom.sub_app]
  change φ.app U.1 m - ψ.app U.1 m = 0
  rw [h U.1 U.2 m, sub_self]

/-- Affine-local data for a morphism out of a direct image `g_* M`, given on sections
`Γ(M, g⁻¹ V)` over affine opens `V`. -/
noncomputable def AffineHomData.ofPushforward {Z W : Scheme.{u}} (g : Z ⟶ W) (M : Z.Modules)
    (N : W.Modules) (φ : ∀ V : W.Opens, IsAffineOpen V → Γ(M, g ⁻¹ᵁ V) →+ Γ(N, V))
    (hsmul : ∀ (V : W.Opens) (hV : IsAffineOpen V) (r : Γ(W, V)) (t : Γ(M, g ⁻¹ᵁ V)),
      φ V hV (g.app V r • t) = r • φ V hV t)
    (hnat : ∀ {V V' : W.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
      (t : Γ(M, g ⁻¹ᵁ V)),
      φ V' hV' (M.presheaf.map (homOfLE (g.preimage_mono h)).op t) =
        N.presheaf.map (homOfLE h).op (φ V hV t)) :
    AffineHomData ((Scheme.Modules.pushforward g).obj M) N where
  toFun V hV :=
    { toFun := φ V hV
      map_add' := map_add _
      map_smul' := hsmul V hV }
  naturality hV hV' h t := hnat hV hV' h t

lemma AffineHomData.ofPushforward_toFun {Z W : Scheme.{u}} (g : Z ⟶ W) (M : Z.Modules)
    (N : W.Modules) (φ : ∀ V : W.Opens, IsAffineOpen V → Γ(M, g ⁻¹ᵁ V) →+ Γ(N, V))
    (hsmul hnat) (V : W.Opens) (hV : IsAffineOpen V) (t : Γ(M, g ⁻¹ᵁ V)) :
    (AffineHomData.ofPushforward g M N φ hsmul hnat).toFun V hV t = φ V hV t := rfl

end Helpers

lemma presheaf_map_appLE_apply' {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) {V V' : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V) (x : Γ(Y, U)) :
    X.presheaf.map (homOfLE h).op (f.appLE U V e x) = f.appLE U V' (h.trans e) x := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

lemma appLE_presheaf_map_apply' {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} (V : X.Opens)
    (h : U' ≤ U) (e : V ≤ f ⁻¹ᵁ U') (x : Γ(Y, U)) :
    f.appLE U' V e (Y.presheaf.map (homOfLE h).op x) =
      f.appLE U V (e.trans (f.preimage_mono h)) x := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]

section MvPolynomialBaseChange

variable (σ : Type)

/-- `A ⟶ A[yᵢ : i ∈ σ]`. -/
abbrev mvC (A : CommRingCat.{u}) : A ⟶ CommRingCat.of (MvPolynomial σ A) :=
  CommRingCat.ofHom MvPolynomial.C

/-- The pushout square `A → A[y]`, `A → R`, `R → R[y]`. -/
lemma isPushout_mvPolynomial {A R : CommRingCat.{u}} (φ : A ⟶ R) :
    IsPushout φ (mvC σ A) (mvC σ R) (CommRingCat.ofHom (MvPolynomial.map φ.hom)) := by
  let _ : Algebra A R := φ.hom.toAlgebra
  refine (CommRingCat.isPushout_tensorProduct A R (MvPolynomial σ A)).of_iso (Iso.refl _)
    (Iso.refl _) (Iso.refl _)
    (MvPolynomial.algebraTensorAlgEquiv A R).toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    change MvPolynomial.algebraTensorAlgEquiv A R (r ⊗ₜ 1) = MvPolynomial.C r
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, _root_.map_one, MvPolynomial.smul_eq_C_mul,
      mul_one]
  · refine CommRingCat.hom_ext (RingHom.ext fun p ↦ ?_)
    change MvPolynomial.algebraTensorAlgEquiv A R (1 ⊗ₜ p) = MvPolynomial.map φ.hom p
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    rfl

variable {σ} {A : CommRingCat.{u}} {X Y : Scheme.{u}} {f : X ⟶ Spec A} {q : Y ⟶ X}
  {g' : Y ⟶ Spec (CommRingCat.of (MvPolynomial σ A))}
  (H : IsPullback q g' f (Spec.map (mvC σ A)))

/-- `Γ(X ×_A A[y], q⁻¹ U) ≅ Γ(X, U)[y]` for `U` affine. -/
def baseChangeMvIso {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(Y, q ⁻¹ᵁ U) ≅ CommRingCat.of (MvPolynomial σ Γ(X, U)) :=
  (isPushout_baseChange H hU).isoIsPushout _ _ (isPushout_mvPolynomial σ (structMap f))

@[reassoc]
lemma appLE_baseChangeMvIso {U : X.Opens} (hU : IsAffineOpen U) :
    q.appLE U (q ⁻¹ᵁ U) le_rfl ≫ (baseChangeMvIso H hU).hom = mvC σ Γ(X, U) :=
  IsPushout.inl_isoIsPushout_hom _ _ _ _

@[reassoc]
lemma structure_baseChangeMvIso {U : X.Opens} (hU : IsAffineOpen U) :
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial σ A))).inv ≫ g'.appLE ⊤ (q ⁻¹ᵁ U) le_top) ≫
      (baseChangeMvIso H hU).hom =
      CommRingCat.ofHom (MvPolynomial.map (structMap f (V := U)).hom) :=
  IsPushout.inr_isoIsPushout_hom _ _ _ _

lemma baseChangeMvIso_appLE {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U)) :
    (baseChangeMvIso H hU).hom (q.appLE U (q ⁻¹ᵁ U) le_rfl r) = MvPolynomial.C r :=
  ConcreteCategory.congr_hom (appLE_baseChangeMvIso H hU) r

lemma baseChangeMvIso_structure {U : X.Opens} (hU : IsAffineOpen U)
    (p : MvPolynomial σ A) :
    (baseChangeMvIso H hU).hom (g'.appLE ⊤ (q ⁻¹ᵁ U) le_top
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial σ A))).inv p)) =
      MvPolynomial.map (structMap f (V := U)).hom p :=
  ConcreteCategory.congr_hom (structure_baseChangeMvIso H hU) p

/-- The isomorphisms `Γ(X ×_A A[y], q⁻¹ U) ≅ Γ(X, U)[y]` commute with restrictions. -/
lemma baseChangeMvIso_res {U U' : X.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (h : U' ≤ U) (c : Γ(Y, q ⁻¹ᵁ U)) :
    (baseChangeMvIso H hU').hom (Y.presheaf.map (homOfLE (q.preimage_mono h)).op c) =
      MvPolynomial.map (X.presheaf.map (homOfLE h).op).hom ((baseChangeMvIso H hU).hom c) := by
  have e := (isPushout_baseChange H hU).hom_ext (W := CommRingCat.of (MvPolynomial σ Γ(X, U')))
    (l := (Y.presheaf.map (homOfLE (q.preimage_mono h)).op ≫ (baseChangeMvIso H hU').hom))
    (k := (baseChangeMvIso H hU).hom ≫
      CommRingCat.ofHom (MvPolynomial.map (X.presheaf.map (homOfLE h).op).hom)) ?_ ?_
  · exact (ConcreteCategory.congr_hom e c).symm
  · refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    rw [baseChangeMvIso_appLE, presheaf_map_appLE_apply', ← appLE_presheaf_map_apply' q (q ⁻¹ᵁ U')
      h le_rfl, baseChangeMvIso_appLE, MvPolynomial.map_C]
  · refine CommRingCat.hom_ext (RingHom.ext fun p ↦ ?_)
    have e2' : structMap f (V := U) ≫ X.presheaf.map (homOfLE h).op = structMap f (V := U') := by
      simp only [structMap, Category.assoc]
      congr 1
      exact Scheme.Hom.appLE_map _ _ _
    have e2 : (X.presheaf.map (homOfLE h).op).hom.comp (structMap f (V := U)).hom =
        (structMap f (V := U')).hom := by
      rw [← CommRingCat.hom_comp, e2']
    change (MvPolynomial.map (X.presheaf.map (homOfLE h).op).hom)
        ((baseChangeMvIso H hU).hom (g'.appLE ⊤ (q ⁻¹ᵁ U) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial σ A))).inv p))) =
      (baseChangeMvIso H hU').hom (Y.presheaf.map (homOfLE (q.preimage_mono h)).op
        (g'.appLE ⊤ (q ⁻¹ᵁ U) le_top
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial σ A))).inv p)))
    rw [baseChangeMvIso_structure]
    erw [presheaf_map_appLE_apply']
    rw [baseChangeMvIso_structure, MvPolynomial.map_map, e2]

end MvPolynomialBaseChange

section MvTensor

open ModuleCat ChangeOfRings

variable {σ : Type} {A : CommRingCat.{u}} {X Y : Scheme.{u}} {f : X ⟶ Spec A} {q : Y ⟶ X}
  {g' : Y ⟶ Spec (CommRingCat.of (MvPolynomial σ A))}
  (H : IsPullback q g' f (Spec.map (mvC σ A))) {U : X.Opens} (hU : IsAffineOpen U)

/-- The ring isomorphism `Γ(Y, q⁻¹ U) ≅ Γ(X, U)[y]` as a `Γ(X, U)`-linear map. -/
def baseChangeMvLinearEquiv :
    (restrictScalars (q.appLE U (q ⁻¹ᵁ U) le_rfl).hom).obj (ModuleCat.of _ Γ(Y, q ⁻¹ᵁ U))
      ≃ₗ[Γ(X, U)] MvPolynomial σ Γ(X, U) where
  toFun c := (baseChangeMvIso H hU).hom (show Γ(Y, q ⁻¹ᵁ U) from c)
  invFun p := (show Γ(Y, q ⁻¹ᵁ U) from (baseChangeMvIso H hU).inv p)
  map_add' x y := map_add _ _ _
  map_smul' r c := by
    change (baseChangeMvIso H hU).hom
        (q.appLE U _ le_rfl r * (show Γ(Y, q ⁻¹ᵁ U) from c)) = _
    rw [map_mul, baseChangeMvIso_appLE, RingHom.id_apply, MvPolynomial.smul_eq_C_mul]
  left_inv c := by
    change (baseChangeMvIso H hU).inv ((baseChangeMvIso H hU).hom c) = c
    exact (baseChangeMvIso H hU).hom_inv_id_apply c
  right_inv p := (baseChangeMvIso H hU).inv_hom_id_apply p

variable (N : X.Modules) [N.IsQuasicoherent]

include hU H in
/-- `Γ(q^* N, q⁻¹ U) ≅ Γ(X, U)[y] ⊗_{Γ(X, U)} Γ(N, U)`. -/
def pullbackMvSectionsEquiv :
    Γ((Scheme.Modules.pullback q).obj N, q ⁻¹ᵁ U) ≃+
      TensorProduct Γ(X, U) (MvPolynomial σ Γ(X, U)) Γ(N, U) :=
  have : IsAffineHom q := isAffineHom_of_isPullback H
  (Scheme.Modules.pullbackSectionsEquiv q N hU (hU.preimage q)).trans
    (TensorProduct.congr (baseChangeMvLinearEquiv H hU) (LinearEquiv.refl _ _)).toAddEquiv

lemma pullbackMvSectionsEquiv_smul_pullbackApp (c : Γ(Y, q ⁻¹ᵁ U)) (m : Γ(N, U)) :
    pullbackMvSectionsEquiv H hU N (c • Scheme.Modules.pullbackApp q N U m) =
      (baseChangeMvIso H hU).hom c ⊗ₜ m := by
  have : IsAffineHom q := isAffineHom_of_isPullback H
  have h := Scheme.Modules.pullbackSectionsEquiv_symm_tmul q N hU (hU.preimage q) c m
  have h2 : Scheme.Modules.pullbackSectionsEquiv q N hU (hU.preimage q)
      (c • Scheme.Modules.pullbackApp q N U m) =
        c ⊗ₜ[Γ(X, U), (q.appLE U (q ⁻¹ᵁ U) le_rfl).hom] m := by
    rw [← h]; exact AddEquiv.apply_symm_apply _ _
  rw [pullbackMvSectionsEquiv]
  erw [AddEquiv.trans_apply, h2]
  rfl

lemma pullbackMvSectionsEquiv_smul (r : Γ(X, U))
    (t : Γ((Scheme.Modules.pullback q).obj N, q ⁻¹ᵁ U)) :
    pullbackMvSectionsEquiv H hU N (q.appLE U (q ⁻¹ᵁ U) le_rfl r • t) =
      r • pullbackMvSectionsEquiv H hU N t := by
  have : IsAffineHom q := isAffineHom_of_isPullback H
  rw [pullbackMvSectionsEquiv]
  erw [AddEquiv.trans_apply, AddEquiv.trans_apply, Scheme.Modules.pullbackSectionsEquiv_smul]
  exact (TensorProduct.congr (baseChangeMvLinearEquiv H hU) (LinearEquiv.refl _ _)).map_smul r _

end MvTensor

section Monomials

variable {A : Type*} [CommRing A] {σ : Type*} (a : σ → A)

/-- `a^α = ∏ aᵢ^{αᵢ}`. -/
def aPow (α : σ →₀ ℕ) : A := α.prod fun i e ↦ a i ^ e

lemma aPow_add (α β : σ →₀ ℕ) : aPow a (α + β) = aPow a α * aPow a β :=
  Finsupp.prod_add_index' (fun _ ↦ pow_zero _) fun _ _ _ ↦ pow_add _ _ _

lemma aPow_mem {J : Ideal A} (ha : ∀ i, a i ∈ J) (α : σ →₀ ℕ) : aPow a α ∈ J ^ α.degree := by
  induction α using Finsupp.induction with
  | zero => simp [aPow]
  | single_add i n α hi hn ih =>
    rw [aPow_add, map_add, pow_add]
    refine Ideal.mul_mem_mul ?_ ih
    rw [aPow, Finsupp.prod_single_index (by simp), Finsupp.degree_single]
    exact Ideal.pow_mem_pow (ha i) n

variable [Fintype σ] [DecidableEq σ]

/-- The monomials of degree `k` in the variables `σ`. -/
abbrev mon (σ : Type*) [Fintype σ] [DecidableEq σ] (k : ℕ) : Finset (σ →₀ ℕ) :=
  (Finset.univ : Finset σ).finsuppAntidiag k

omit [DecidableEq σ] in
lemma mem_mon [DecidableEq σ] {k : ℕ} {α : σ →₀ ℕ} : α ∈ mon σ k ↔ α.degree = k := by
  simp only [mon, Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum, Finset.subset_univ,
    and_true]

lemma aPow_mem_of_mem_mon {J : Ideal A} (ha : ∀ i, a i ∈ J) {k : ℕ} {α : σ →₀ ℕ}
    (hα : α ∈ mon σ k) : aPow a α ∈ J ^ k := by
  rw [← mem_mon.mp hα]
  exact aPow_mem a ha α

/-- `Jᵏ` is spanned by the monomials of degree `k` in generators of `J`. -/
lemma pow_le_span_aPow {J : Ideal A} (hspan : Ideal.span (Set.range a) = J) (k : ℕ) :
    J ^ k ≤ Ideal.span ((fun α ↦ aPow a α) '' (mon σ k : Set (σ →₀ ℕ))) := by
  induction k with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
    refine Ideal.subset_span ⟨0, ?_, by simp [aPow]⟩
    simp
  | succ k ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono ih hspan.ge).trans ?_
    rw [Ideal.span_mul_span, Ideal.span_le]
    rintro _ ⟨_, ⟨α, hα, rfl⟩, _, ⟨i, rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨α + Finsupp.single i 1, ?_, ?_⟩
    · rw [Finset.mem_coe, mem_mon, map_add, Finsupp.degree_single, mem_mon.mp hα]
    · change aPow a (α + Finsupp.single i 1) = aPow a α * a i
      rw [aPow_add]
      congr 1
      rw [aPow, Finsupp.prod_single_index (by simp), pow_one]

end Monomials

section Graded

open Scheme.Modules (pullbackApp)

variable {A : CommRingCat.{u}} {I : Ideal A} {X : Scheme.{u}}
  {f : X ⟶ Spec A} {σ : Type} [Fintype σ] [DecidableEq σ] (a : σ → A) (ha : ∀ i, a i ∈ I)
  (G : AdicSystem I f)

/-- The generators `⊕_{|α| = k+1} G₀ ⟶ I^{k+1} G_{k+1}`, `(xα) ↦ Σ a^α x̃α`. -/
def genMap (k : ℕ) : (⨁ fun _ : mon σ (k + 1) ↦ G.obj 0) ⟶ G.grSucc k :=
  biproduct.desc fun α ↦ G.mulGr k (aPow_mem_of_mem_mon a ha α.2)

lemma genMap_app (k : ℕ) (U : X.Opens) (x : Γ(⨁ fun _ : mon σ (k + 1) ↦ G.obj 0, U)) :
    (genMap a ha G k).app U x = ∑ α : mon σ (k + 1),
      (G.mulGr k (aPow_mem_of_mem_mon a ha α.2)).app U
        ((biproduct.π (fun _ : mon σ (k + 1) ↦ G.obj 0) α).app U x) := by
  have e : genMap a ha G k = ∑ α : mon σ (k + 1),
      biproduct.π (fun _ : mon σ (k + 1) ↦ G.obj 0) α ≫
        G.mulGr k (aPow_mem_of_mem_mon a ha α.2) := by
    unfold genMap
    exact biproduct.desc_eq (f := fun _ : mon σ (k + 1) ↦ G.obj 0)
  rw [e, modules_sum_app_apply]
  rfl

lemma genMap_app_ι (k : ℕ) (U : X.Opens) (α : mon σ (k + 1)) (x : Γ(G.obj 0, U)) :
    (genMap a ha G k).app U ((biproduct.ι (fun _ : mon σ (k + 1) ↦ G.obj 0) α).app U x) =
      (G.mulGr k (aPow_mem_of_mem_mon a ha α.2)).app U x := by
  rw [← Scheme.Modules.Hom.comp_app_apply, genMap, biproduct.ι_desc]

lemma genMap_app_surjective (hspan : Ideal.span (Set.range a) = I) (k : ℕ) {U : X.Opens}
    (hU : IsAffineOpen U) : Function.Surjective ((genMap a ha G k).app U) := by
  intro y
  let T : Submodule Γ(X, U) Γ(G.obj (k + 1), U) :=
    LinearMap.range (appLinearMap (genMap a ha G k ≫ kernel.ι (G.map k)) U)
  have key : ∀ r ∈ Ideal.span (structMapV f U '' ((fun α ↦ aPow a α) '' (mon σ (k + 1) : Set _))),
      ∀ m : Γ(G.obj (k + 1), U), r • m ∈ T := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem x hx =>
      intro m
      obtain ⟨_, ⟨α, hα, rfl⟩, rfl⟩ := hx
      refine ⟨(biproduct.ι (fun _ : mon σ (k + 1) ↦ G.obj 0) ⟨α, hα⟩).app U
        ((G.toZero (k + 1)).app U m), ?_⟩
      change (kernel.ι (G.map k)).app U ((genMap a ha G k).app U _) = _
      rw [genMap_app_ι, G.mulGr_app k _ hU, G.mulUp_toZero]
    | zero => intro m; rw [zero_smul]; exact T.zero_mem
    | add x y _ _ hx hy => intro m; rw [add_smul]; exact T.add_mem (hx m) (hy m)
    | smul t x _ hx => intro m; rw [smul_eq_mul, mul_comm, mul_smul]; exact hx _
  have hT : (idealV f I U 1 ^ (k + 1) • ⊤ : Submodule Γ(X, U) Γ(G.obj (k + 1), U)) ≤ T := by
    rw [Submodule.smul_le]
    intro r hr m _
    rw [← AdicSystem.idealV_eq_pow, idealV] at hr
    have hr' := Ideal.map_mono (f := structMapV f U) (pow_le_span_aPow a hspan (k + 1)) hr
    rw [Ideal.map_span] at hr'
    exact key r hr' m
  obtain ⟨x, hx⟩ := hT ((G.mem_range_grSucc_ι k hU _).mp ⟨y, rfl⟩)
  exact ⟨x, G.grSucc_ι_app_injective k U hx⟩

lemma epi_genMap (hspan : Ideal.span (Set.range a) = I) (k : ℕ) : Epi (genMap a ha G k) :=
  epi_of_surjective_app _ _ (fun V : X.affineOpens ↦ V.1) (iSup_affineOpens_eq_top X)
    (fun V ↦ V.2) fun V ↦ genMap_app_surjective a ha G hspan k V.2

end Graded

namespace AdicSystem

variable {A : CommRingCat.{u}} {I : Ideal A} {X : Scheme.{u}} {f : X ⟶ Spec A}
  (G : AdicSystem I f)

lemma mulUp_congr (k : ℕ) {U : X.Opens} (hU : IsAffineOpen U) {b c : A} (h : b = c)
    (hb : b ∈ I ^ k) (hc : c ∈ I ^ k) : G.mulUp k hU hb = G.mulUp k hU hc := by
  subst h; rfl

variable {σ : Type} [Fintype σ] [DecidableEq σ] (a : σ → A) (ha : ∀ i, a i ∈ I)

/-- **Relations in degree `J` propagate to degree `K`** (the algebraic core of the graded
sheaf): if `Σ_α a^α x̃α = 0` at level `J` (`|α| = J`), then for every polynomial `P`,
`Σ_α Σ_{|β| = K} coeff_β(P y^α) a^β x̃α = 0` at level `K`. -/
lemma sum_coeff_mulUp_eq_zero {U : X.Opens} (hU : IsAffineOpen U) (J K : ℕ)
    (x : mon σ J → Γ(G.obj 0, U))
    (hx : ∑ α : mon σ J, G.mulUp J hU (aPow_mem_of_mem_mon a ha α.2) (x α) = 0)
    (P : MvPolynomial σ Γ(X, U)) :
    ∑ α : mon σ J, ∑ β : mon σ K, MvPolynomial.coeff β.1 (P * MvPolynomial.monomial α.1 1) •
      G.mulUp K hU (aPow_mem_of_mem_mon a ha β.2) (x α) = 0 := by
  induction P using MvPolynomial.induction_on' with
  | add p p' hp hp' =>
    simp only [add_mul, MvPolynomial.coeff_add, add_smul, Finset.sum_add_distrib, hp, hp',
      add_zero]
  | monomial γ r =>
    simp only [MvPolynomial.monomial_mul_monomial, mul_one, MvPolynomial.coeff_monomial]
    by_cases hK : K = J + γ.degree
    · subst hK
      have e : ∀ α : mon σ J, ∑ β : mon σ (J + γ.degree),
          (if γ + α.1 = β.1 then r else 0) •
            G.mulUp (J + γ.degree) hU (aPow_mem_of_mem_mon a ha β.2) (x α) =
          r • G.mulUp (J + γ.degree) hU (show aPow a γ * aPow a α.1 ∈ I ^ (J + γ.degree) by
            rw [add_comm, pow_add]
            exact Ideal.mul_mem_mul (aPow_mem a ha γ) (aPow_mem_of_mem_mon a ha α.2)) (x α) := by
        intro α
        have hmem : γ + α.1 ∈ mon σ (J + γ.degree) := by
          rw [mem_mon, map_add, mem_mon.mp α.2, add_comm]
        rw [Finset.sum_eq_single ⟨γ + α.1, hmem⟩]
        · rw [ite_eq_left rfl, G.mulUp_congr _ hU (aPow_add a γ α.1)]
        · intro β _ hβ
          rw [ite_eq_right (fun h ↦ hβ (Subtype.ext h.symm)), zero_smul]
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [Finset.sum_congr rfl fun α _ ↦ e α, ← Finset.smul_sum]
      have := G.sum_mulUp_eq_zero Finset.univ J γ.degree hU (fun α : mon σ J ↦ aPow a α.1)
        (fun α ↦ aPow_mem_of_mem_mon a ha α.2) (aPow_mem a ha γ) x hx
      rw [this, smul_zero]
    · refine Finset.sum_eq_zero fun α _ ↦ Finset.sum_eq_zero fun β _ ↦ ?_
      rw [ite_eq_right, zero_smul]
      intro h
      apply hK
      have h1 := mem_mon.mp β.2
      rw [← h, map_add, mem_mon.mp α.2] at h1
      omega

end AdicSystem

section GradedSheaf

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- The data for the graded sheaf of an adic system: generators `a : σ → A` of `I` and the base
change `Y = X ×_A A[yᵢ : i ∈ σ]`. -/
structure GradedSetup where
  /-- The index type of the generators. -/
  σ : Type
  [fintype : Fintype σ]
  [decEq : DecidableEq σ]
  /-- The generators of `I`. -/
  a : σ → A
  mem (i : σ) : a i ∈ I
  span : Ideal.span (Set.range a) = I
  /-- The base change `X ×_A A[y]`. -/
  Y : Scheme.{u}
  /-- The projection `Y ⟶ X`. -/
  q : Y ⟶ X
  /-- The projection `Y ⟶ Spec A[y]`. -/
  g' : Y ⟶ Spec (CommRingCat.of (MvPolynomial σ A))
  isPullback : IsPullback q g' f (Spec.map (mvC σ A))

namespace GradedSetup

attribute [instance] fintype decEq

variable {I f} (S : GradedSetup I f) (G : AdicSystem I f)

instance : IsAffineHom S.q := isAffineHom_of_isPullback S.isPullback

/-- The generators in degree `k + 1`. -/
abbrev gen (k : ℕ) : (⨁ fun _ : mon S.σ (k + 1) ↦ G.obj 0) ⟶ G.grSucc k :=
  genMap S.a S.mem G k

instance (k : ℕ) : Epi (S.gen G k) := epi_genMap S.a S.mem G S.span k

/-- The relations among the generators in degree `k + 1`. -/
abbrev rel (k : ℕ) : X.Modules := kernel (S.gen G k)

lemma shortExact_rel (k : ℕ) :
    (ShortComplex.mk (kernel.ι (S.gen G k)) (S.gen G k) (kernel.condition _)).ShortExact :=
  shortExact_kernelSequence (S.gen G k)

instance (k : ℕ) : (S.rel G k).IsQuasicoherent := by
  have : (⨁ fun _ : mon S.σ (k + 1) ↦ G.obj 0).IsQuasicoherent := isQuasicoherent_biproduct _
  exact isQuasicoherent_X₁_of_shortExact (S.shortExact_rel G k)

/-- The global section `y^α` of `𝒪_Y`. -/
def yMon (α : S.σ →₀ ℕ) : Γ(S.Y, ⊤) :=
  S.g'.appTop ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial S.σ A))).inv
    (MvPolynomial.monomial α 1))

/-- `q^*(⊕_{|α|=k+1} G₀) ⟶ q^* G₀`, `(xα) ↦ Σ y^α xα`. -/
def psi (k : ℕ) : (Scheme.Modules.pullback S.q).obj (⨁ fun _ : mon S.σ (k + 1) ↦ G.obj 0) ⟶
    (Scheme.Modules.pullback S.q).obj (G.obj 0) :=
  ∑ α : mon S.σ (k + 1), (Scheme.Modules.pullback S.q).map
    (biproduct.π (fun _ : mon S.σ (k + 1) ↦ G.obj 0) α) ≫
      ((Scheme.Modules.pullback S.q).obj (G.obj 0)).smulEnd (S.yMon α)

/-- The relations, pulled back to `Y`, in `q^* G₀`. -/
def phi (k : ℕ) : (Scheme.Modules.pullback S.q).obj (S.rel G k) ⟶
    (Scheme.Modules.pullback S.q).obj (G.obj 0) :=
  (Scheme.Modules.pullback S.q).map (kernel.ι (S.gen G k)) ≫ S.psi G k

/-- The relations of degree `≤ M`. -/
def phiLe (M : ℕ) : (⨁ fun k : Fin M ↦ (Scheme.Modules.pullback S.q).obj (S.rel G k)) ⟶
    (Scheme.Modules.pullback S.q).obj (G.obj 0) :=
  biproduct.desc fun k ↦ S.phi G k

section Stabilization

variable [CompactSpace X] [IsLocallyNoetherian X] [(G.obj 0).IsFiniteType]

instance : ((Scheme.Modules.pullback S.q).obj (G.obj 0)).IsQuasicoherent := inferInstance

omit [CompactSpace X] [(G.obj 0).IsFiniteType] in
lemma isNoetherianRing_preimage {V : X.Opens} (hV : IsAffineOpen V) :
    IsNoetherianRing Γ(S.Y, S.q ⁻¹ᵁ V) := by
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  exact isNoetherianRing_of_ringEquiv _
    (baseChangeMvIso S.isPullback hV).commRingCatIsoToRingEquiv.symm

/-- **Stabilization of the relations**: by noetherianity, the relations of degree `≤ M₀` generate
all relations. -/
lemma exists_stab : ∃ M₀ : ℕ, ∀ k, S.phi G k ≫ cokernel.π (S.phiLe G M₀) = 0 := by
  classical
  obtain ⟨r, V, hcov, hV⟩ := exists_cechCover' X
  let W : Fin r → S.Y.Opens := fun i ↦ S.q ⁻¹ᵁ V i
  have hW : ∀ i, IsAffineOpen (W i) := fun i ↦ (hV i).preimage S.q
  let P := (Scheme.Modules.pullback S.q).obj (G.obj 0)
  have hnoeth : ∀ i, _root_.IsNoetherian Γ(S.Y, W i) Γ(P, W i) := fun i ↦ by
    have := S.isNoetherianRing_preimage (hV i)
    have := finite_sections_of_isFiniteType P (hW i)
    infer_instance
  let c : ∀ i, ℕ →o Submodule Γ(S.Y, W i) Γ(P, W i) := fun i ↦
    ⟨fun M ↦ ⨆ (k : ℕ) (_ : k < M), LinearMap.range (appLinearMap (S.phi G k) (W i)),
      fun M M' h ↦ iSup₂_mono' fun k hk ↦ ⟨k, lt_of_lt_of_le hk h, le_rfl⟩⟩
  choose n hn using fun i ↦ (monotone_stabilizes_iff_noetherian.mpr (hnoeth i)) (c i)
  refine ⟨Finset.univ.sup n, fun k ↦ ?_⟩
  have hWcov : ⨆ i, W i = ⊤ := by
    rw [show (⨆ i, W i) = S.q ⁻¹ᵁ (⨆ i, V i) from (Scheme.Hom.preimage_iSup _ _).symm, hcov,
      Scheme.Hom.preimage_top]
  have : (⨁ fun k : Fin (Finset.univ.sup n) ↦
      (Scheme.Modules.pullback S.q).obj (S.rel G k)).IsQuasicoherent :=
    isQuasicoherent_biproduct _
  refine eq_zero_of_app_affineCover _ W hWcov hW fun i x ↦ ?_
  rw [Scheme.Modules.Hom.comp_app_apply, cokernel_π_app_eq_zero_iff _ (hW i)]
  have hni : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  have h1 : (S.phi G k).app (W i) x ∈ c i (max (k + 1) (Finset.univ.sup n)) :=
    Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem (by omega) ⟨x, rfl⟩)
  rw [← hn i _ (le_trans hni (le_max_right _ _)), hn i _ hni] at h1
  have h2 : c i (Finset.univ.sup n) ≤
      LinearMap.range (appLinearMap (S.phiLe G (Finset.univ.sup n)) (W i)) := by
    refine iSup₂_le fun k' hk' ↦ ?_
    rintro _ ⟨y, rfl⟩
    refine ⟨(biproduct.ι (fun k : Fin (Finset.univ.sup n) ↦
      (Scheme.Modules.pullback S.q).obj (S.rel G k)) ⟨k', hk'⟩).app (W i) y, ?_⟩
    change (S.phiLe G _).app (W i) _ = _
    rw [← Scheme.Modules.Hom.comp_app_apply, phiLe, biproduct.ι_desc]
    rfl
  obtain ⟨y, hy⟩ := h2 h1
  exact ⟨y, hy⟩

end Stabilization

section Sheaf

variable [CompactSpace X] [IsLocallyNoetherian X] [(G.obj 0).IsFiniteType]

/-- The degree bound for the relations. -/
def degBound : ℕ := (S.exists_stab G).choose

lemma phi_comp_π (k : ℕ) : S.phi G k ≫ cokernel.π (S.phiLe G (S.degBound G)) = 0 :=
  (S.exists_stab G).choose_spec k

/-- **The graded sheaf** `⊕ₖ Iᵏ Gₖ` of an adic system, as a module on `Y = X ×_A A[y]`:
`q^* G₀` modulo the relations. -/
def grSheaf : S.Y.Modules := cokernel (S.phiLe G (S.degBound G))

/-- The projection `q^* G₀ ⟶ grSheaf`. -/
abbrev grπ : (Scheme.Modules.pullback S.q).obj (G.obj 0) ⟶ S.grSheaf G := cokernel.π _

/-- `⊕_{|α|=k+1} G₀ ⟶ q_* grSheaf`, adjoint to `(xα) ↦ Σ y^α xα`. -/
def jMap (k : ℕ) : (⨁ fun _ : mon S.σ (k + 1) ↦ G.obj 0) ⟶
    (Scheme.Modules.pushforward S.q).obj (S.grSheaf G) :=
  (Scheme.Modules.pullbackPushforwardAdjunction S.q).homEquiv _ _ (S.psi G k ≫ S.grπ G)

lemma kernel_ι_jMap (k : ℕ) : kernel.ι (S.gen G k) ≫ S.jMap G k = 0 := by
  rw [jMap, ← Adjunction.homEquiv_naturality_left, ← Category.assoc]
  change (Scheme.Modules.pullbackPushforwardAdjunction S.q).homEquiv _ _
    (S.phi G k ≫ S.grπ G) = 0
  have h : S.phi G k ≫ S.grπ G = 0 := S.phi_comp_π G k
  rw [h, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]

/-- The inclusion `I^{k+1} G_{k+1} ⟶ q_* grSheaf` of the graded piece of degree `k + 1`. -/
def iMap (k : ℕ) : G.grSucc k ⟶ (Scheme.Modules.pushforward S.q).obj (S.grSheaf G) :=
  (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (S.gen G k))).desc
    (CokernelCofork.ofπ (S.jMap G k) (S.kernel_ι_jMap G k))

@[reassoc]
lemma gen_iMap (k : ℕ) : S.gen G k ≫ S.iMap G k = S.jMap G k :=
  (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (S.gen G k))).fac _ WalkingParallelPair.one

end Sheaf

section Lambda

variable {U : X.Opens} (hU : IsAffineOpen U)

/-- The bilinear map `(P, x) ↦ Σ_{|β| = k+1} coeff_β(P) a^β x̃`. -/
def bil (k : ℕ) : MvPolynomial S.σ Γ(X, U) →ₗ[Γ(X, U)] Γ(G.obj 0, U) →ₗ[Γ(X, U)]
    Γ(G.grSucc k, U) :=
  LinearMap.mk₂ Γ(X, U)
    (fun P x ↦ ∑ β : mon S.σ (k + 1), MvPolynomial.coeff β.1 P •
      G.mulGrFun k (aPow_mem_of_mem_mon S.a S.mem β.2) hU x)
    (fun P P' x ↦ by simp only [MvPolynomial.coeff_add, add_smul, Finset.sum_add_distrib])
    (fun r P x ↦ by simp only [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul, Finset.smul_sum])
    (fun P x x' ↦ by simp only [map_add, smul_add, Finset.sum_add_distrib])
    (fun r P x ↦ by simp only [LinearMap.map_smul, smul_comm _ r, Finset.smul_sum])

/-- The degree `k + 1` component `Γ(q^* G₀, q⁻¹ U) → Γ(I^{k+1} G_{k+1}, U)`. -/
def lamFun (k : ℕ) : Γ((Scheme.Modules.pullback S.q).obj (G.obj 0), S.q ⁻¹ᵁ U) →+
    Γ(G.grSucc k, U) :=
  (TensorProduct.lift (S.bil G hU k)).toAddMonoidHom.comp
    (pullbackMvSectionsEquiv S.isPullback hU (G.obj 0)).toAddMonoidHom

lemma lamFun_smul_pullbackApp (k : ℕ) (c : Γ(S.Y, S.q ⁻¹ᵁ U)) (m : Γ(G.obj 0, U)) :
    S.lamFun G hU k (c • Scheme.Modules.pullbackApp S.q (G.obj 0) U m) =
      ∑ β : mon S.σ (k + 1), MvPolynomial.coeff β.1 ((baseChangeMvIso S.isPullback hU).hom c) •
        G.mulGrFun k (aPow_mem_of_mem_mon S.a S.mem β.2) hU m := by
  simp only [lamFun, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    pullbackMvSectionsEquiv_smul_pullbackApp, LinearMap.toAddMonoidHom_coe,
    TensorProduct.lift.tmul]
  rfl

lemma lamFun_smul (k : ℕ) (r : Γ(X, U))
    (t : Γ((Scheme.Modules.pullback S.q).obj (G.obj 0), S.q ⁻¹ᵁ U)) :
    S.lamFun G hU k (S.q.appLE U (S.q ⁻¹ᵁ U) le_rfl r • t) = r • S.lamFun G hU k t := by
  simp only [lamFun, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    pullbackMvSectionsEquiv_smul, LinearMap.toAddMonoidHom_coe, LinearMap.map_smul]

end Lambda

section Relations

variable {U : X.Opens} (hU : IsAffineOpen U)

lemma baseChangeMvIso_yMon (α : S.σ →₀ ℕ) :
    (baseChangeMvIso S.isPullback hU).hom
      (S.Y.presheaf.map (homOfLE (le_top : S.q ⁻¹ᵁ U ≤ ⊤)).op (S.yMon α)) =
      MvPolynomial.monomial α 1 := by
  have e : S.Y.presheaf.map (homOfLE (le_top : S.q ⁻¹ᵁ U ≤ ⊤)).op (S.yMon α) =
      S.g'.appLE ⊤ (S.q ⁻¹ᵁ U) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial S.σ A))).inv
          (MvPolynomial.monomial α 1)) := by
    rw [yMon, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact presheaf_map_appLE_apply' _ _ _ _ _
  rw [e, baseChangeMvIso_structure, MvPolynomial.map_monomial, map_one]

lemma smulEnd_app_apply {Z : Scheme.{u}} (M : Z.Modules) (r : Γ(Z, ⊤)) (V : Z.Opens)
    (m : Γ(M, V)) :
    (M.smulEnd r).app V m = Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r • m :=
  rfl

lemma psi_app_pullbackApp (k : ℕ) (w : Γ(⨁ fun _ : mon S.σ (k + 1) ↦ G.obj 0, U)) :
    (S.psi G k).app (S.q ⁻¹ᵁ U) (Scheme.Modules.pullbackApp S.q _ U w) =
      ∑ α : mon S.σ (k + 1), S.Y.presheaf.map (homOfLE (le_top : S.q ⁻¹ᵁ U ≤ ⊤)).op (S.yMon α) •
        Scheme.Modules.pullbackApp S.q (G.obj 0) U
          ((biproduct.π (fun _ : mon S.σ (k + 1) ↦ G.obj 0) α).app U w) := by
  rw [psi, modules_sum_app_apply]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [Scheme.Modules.Hom.comp_app_apply, ← Scheme.Modules.pullbackApp_naturality,
    smulEnd_app_apply]

end Relations

section Mu

variable {U : X.Opens} (hU : IsAffineOpen U)

lemma mulGr_app_eq_mulGrFun (k : ℕ) {b : A} (hb : b ∈ I ^ (k + 1)) (x : Γ(G.obj 0, U)) :
    (G.mulGr k hb).app U x = G.mulGrFun k hb hU x := by
  rw [AdicSystem.mulGr, AffineHomData.toHom_app _ hU]

lemma gen_app_eq_sum (k : ℕ) (w : Γ(⨁ fun _ : mon S.σ (k + 1) ↦ G.obj 0, U)) :
    (S.gen G k).app U w = ∑ α : mon S.σ (k + 1),
      G.mulGrFun k (aPow_mem_of_mem_mon S.a S.mem α.2) hU
        ((biproduct.π (fun _ : mon S.σ (k + 1) ↦ G.obj 0) α).app U w) := by
  rw [genMap_app]
  exact Finset.sum_congr rfl fun α _ ↦ mulGr_app_eq_mulGrFun G hU k _ _

lemma pullbackMvSectionsEquiv_symm_tmul (N : X.Modules) [N.IsQuasicoherent]
    (P : MvPolynomial S.σ Γ(X, U)) (m : Γ(N, U)) :
    (pullbackMvSectionsEquiv S.isPullback hU N).symm (P ⊗ₜ m) =
      (baseChangeMvIso S.isPullback hU).inv P • Scheme.Modules.pullbackApp S.q N U m := by
  apply (pullbackMvSectionsEquiv S.isPullback hU N).injective
  rw [AddEquiv.apply_symm_apply, pullbackMvSectionsEquiv_smul_pullbackApp,
    Iso.inv_hom_id_apply]

/-- The degree components kill the relations. -/
lemma lamFun_phi (j k : ℕ) (w : Γ((Scheme.Modules.pullback S.q).obj (S.rel G j), S.q ⁻¹ᵁ U)) :
    S.lamFun G hU k ((S.phi G j).app (S.q ⁻¹ᵁ U) w) = 0 := by
  obtain ⟨v, rfl⟩ := (pullbackMvSectionsEquiv S.isPullback hU (S.rel G j)).symm.surjective w
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add v v' hv hv' => rw [map_add, map_add, map_add, hv, hv', add_zero]
  | tmul P z =>
    rw [pullbackMvSectionsEquiv_symm_tmul, Scheme.Modules.Hom.app_smul, phi,
      Scheme.Modules.Hom.comp_app_apply, ← Scheme.Modules.pullbackApp_naturality,
      psi_app_pullbackApp, Finset.smul_sum, map_sum]
    simp only [smul_smul, lamFun_smul_pullbackApp, map_mul, Iso.inv_hom_id_apply,
      S.baseChangeMvIso_yMon hU]
    apply G.grSucc_ι_app_injective k U
    rw [map_zero, map_sum]
    simp only [map_sum, Scheme.Modules.Hom.app_smul, G.mulGrFun_spec]
    have hz : (S.gen G j).app U ((kernel.ι (S.gen G j)).app U z) = 0 := by
      rw [← Scheme.Modules.Hom.comp_app_apply, kernel.condition]
      rfl
    rw [S.gen_app_eq_sum G hU] at hz
    have hx := congrArg ((kernel.ι (G.map j)).app U) hz
    rw [map_sum, map_zero] at hx
    simp only [G.mulGrFun_spec] at hx
    exact AdicSystem.sum_coeff_mulUp_eq_zero G S.a S.mem hU (j + 1) (k + 1)
      (fun α ↦ (biproduct.π (fun _ : mon S.σ (j + 1) ↦ G.obj 0) α).app U
        ((kernel.ι (S.gen G j)).app U z)) hx P

lemma mulGrFun_res (k : ℕ) {b : A} (hb : b ∈ I ^ (k + 1)) {V W : X.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (h : W ≤ V) (x : Γ(G.obj 0, V)) :
    G.mulGrFun k hb hW ((G.obj 0).presheaf.map (homOfLE h).op x) =
      (G.grSucc k).presheaf.map (homOfLE h).op (G.mulGrFun k hb hV x) := by
  rw [← mulGr_app_eq_mulGrFun G hW, ← mulGr_app_eq_mulGrFun G hV, hom_app_presheaf_map]

/-- Naturality of the degree components under restriction between affine opens. -/
lemma lamFun_res (k : ℕ) {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V)
    (t : Γ((Scheme.Modules.pullback S.q).obj (G.obj 0), S.q ⁻¹ᵁ V)) :
    S.lamFun G hW k (((Scheme.Modules.pullback S.q).obj (G.obj 0)).presheaf.map
        (homOfLE (S.q.preimage_mono h)).op t) =
      (G.grSucc k).presheaf.map (homOfLE h).op (S.lamFun G hV k t) := by
  obtain ⟨v, rfl⟩ := (pullbackMvSectionsEquiv S.isPullback hV (G.obj 0)).symm.surjective t
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v v' hv hv' => simp only [map_add, hv, hv']
  | tmul P m =>
    have e : homOfLE (S.q.preimage_mono h) = (Opens.map S.q.base).map (homOfLE h) := rfl
    rw [S.pullbackMvSectionsEquiv_symm_tmul hV, Scheme.Modules.map_smul, e,
      ← Scheme.Modules.pullbackApp_map, ← e, lamFun_smul_pullbackApp, lamFun_smul_pullbackApp,
      map_sum, baseChangeMvIso_res S.isPullback hV hW h, Iso.inv_hom_id_apply]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    rw [MvPolynomial.coeff_map, Scheme.Modules.map_smul, mulGrFun_res G k _ hV hW h]

end Mu

section Descent

variable [CompactSpace X] [IsLocallyNoetherian X] [(G.obj 0).IsFiniteType]

omit [CompactSpace X] [IsLocallyNoetherian X] [(G.obj 0).IsFiniteType] in
lemma phiLe_app (M : ℕ) (V : S.Y.Opens)
    (w : Γ(⨁ fun k : Fin M ↦ (Scheme.Modules.pullback S.q).obj (S.rel G k), V)) :
    (S.phiLe G M).app V w = ∑ k : Fin M, (S.phi G k).app V
      ((biproduct.π (fun k : Fin M ↦ (Scheme.Modules.pullback S.q).obj (S.rel G k)) k).app V
        w) := by
  have e : S.phiLe G M = ∑ k : Fin M,
      biproduct.π (fun k : Fin M ↦ (Scheme.Modules.pullback S.q).obj (S.rel G k)) k ≫
        S.phi G k := by
    unfold phiLe
    exact biproduct.desc_eq
  rw [e, modules_sum_app_apply]
  rfl

instance isQuasicoherent_grSheaf : (S.grSheaf G).IsQuasicoherent := by
  have : (⨁ fun k : Fin (S.degBound G) ↦
      (Scheme.Modules.pullback S.q).obj (S.rel G k)).IsQuasicoherent :=
    isQuasicoherent_biproduct _
  exact isQuasicoherent_cokernel _

variable {U : X.Opens} (hU : IsAffineOpen U)

omit [CompactSpace X] [IsLocallyNoetherian X] [(G.obj 0).IsFiniteType] in
lemma lamFun_phiLe (k M : ℕ)
    (w : Γ(⨁ fun k : Fin M ↦ (Scheme.Modules.pullback S.q).obj (S.rel G k), S.q ⁻¹ᵁ U)) :
    S.lamFun G hU k ((S.phiLe G M).app (S.q ⁻¹ᵁ U) w) = 0 := by
  rw [phiLe_app, map_sum]
  exact Finset.sum_eq_zero fun j _ ↦ S.lamFun_phi G hU _ _ _

lemma grπ_app_surjective (hU : IsAffineOpen U) :
    Function.Surjective ((S.grπ G).app (S.q ⁻¹ᵁ U)) := by
  have : (⨁ fun k : Fin (S.degBound G) ↦
      (Scheme.Modules.pullback S.q).obj (S.rel G k)).IsQuasicoherent :=
    isQuasicoherent_biproduct _
  exact cokernel_π_app_surjective _ (hU.preimage S.q)

lemma lamFun_eq_zero_of_grπ (k : ℕ)
    (x : Γ((Scheme.Modules.pullback S.q).obj (G.obj 0), S.q ⁻¹ᵁ U))
    (hx : (S.grπ G).app (S.q ⁻¹ᵁ U) x = 0) : S.lamFun G hU k x = 0 := by
  have : (⨁ fun k : Fin (S.degBound G) ↦
      (Scheme.Modules.pullback S.q).obj (S.rel G k)).IsQuasicoherent :=
    isQuasicoherent_biproduct _
  obtain ⟨w, rfl⟩ := (cokernel_π_app_eq_zero_iff _ (hU.preimage S.q) x).mp hx
  exact S.lamFun_phiLe G hU k _ w

/-- The additive map `Γ(q^* G₀, q⁻¹ U) → Γ(grSheaf, q⁻¹ U)` of sections. -/
def grπAdd : Γ((Scheme.Modules.pullback S.q).obj (G.obj 0), S.q ⁻¹ᵁ U) →+
    Γ(S.grSheaf G, S.q ⁻¹ᵁ U) :=
  (appLinearMap (S.grπ G) (S.q ⁻¹ᵁ U)).toAddMonoidHom

/-- The degree `k + 1` component `Γ(grSheaf, q⁻¹ U) → Γ(I^{k+1} G_{k+1}, U)`. -/
def muFun (k : ℕ) : Γ(S.grSheaf G, S.q ⁻¹ᵁ U) →+ Γ(G.grSucc k, U) :=
  (QuotientAddGroup.lift (S.grπAdd G (U := U)).ker (S.lamFun G hU k)
    fun x hx ↦ S.lamFun_eq_zero_of_grπ G hU k x hx).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective (S.grπAdd G (U := U))
      (S.grπ_app_surjective G hU)).symm.toAddMonoidHom

lemma muFun_grπ (k : ℕ) (x : Γ((Scheme.Modules.pullback S.q).obj (G.obj 0), S.q ⁻¹ᵁ U)) :
    S.muFun G hU k ((S.grπ G).app (S.q ⁻¹ᵁ U) x) = S.lamFun G hU k x := by
  have e : (QuotientAddGroup.quotientKerEquivOfSurjective (S.grπAdd G (U := U))
      (S.grπ_app_surjective G hU)).symm ((S.grπ G).app (S.q ⁻¹ᵁ U) x) =
      (x : _ ⧸ (S.grπAdd G (U := U)).ker) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [muFun, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom, e]
  rfl

lemma muFun_smul (k : ℕ) (r : Γ(X, U)) (t : Γ(S.grSheaf G, S.q ⁻¹ᵁ U)) :
    S.muFun G hU k (S.q.app U r • t) = r • S.muFun G hU k t := by
  obtain ⟨x, rfl⟩ := S.grπ_app_surjective G hU t
  rw [← Scheme.Modules.Hom.app_smul, muFun_grπ, muFun_grπ, Scheme.Hom.app_eq_appLE,
    lamFun_smul]

lemma muFun_res (k : ℕ) {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V)
    (t : Γ(S.grSheaf G, S.q ⁻¹ᵁ V)) :
    S.muFun G hW k ((S.grSheaf G).presheaf.map (homOfLE (S.q.preimage_mono h)).op t) =
      (G.grSucc k).presheaf.map (homOfLE h).op (S.muFun G hV k t) := by
  obtain ⟨x, rfl⟩ := S.grπ_app_surjective G hV t
  rw [← hom_app_presheaf_map, muFun_grπ, muFun_grπ, lamFun_res]

omit [CompactSpace X] [IsLocallyNoetherian X] [(G.obj 0).IsFiniteType] in
lemma lamFun_psi (k : ℕ) (w : Γ(⨁ fun _ : mon S.σ (k + 1) ↦ G.obj 0, U)) :
    S.lamFun G hU k ((S.psi G k).app (S.q ⁻¹ᵁ U) (Scheme.Modules.pullbackApp S.q _ U w)) =
      (S.gen G k).app U w := by
  rw [psi_app_pullbackApp, map_sum, S.gen_app_eq_sum G hU]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [lamFun_smul_pullbackApp, S.baseChangeMvIso_yMon hU]
  rw [Fintype.sum_eq_single α fun β hβ ↦ by
    rw [MvPolynomial.coeff_monomial]
    split_ifs with h
    · exact absurd (Subtype.ext h).symm hβ
    · exact zero_smul _ _]
  rw [MvPolynomial.coeff_monomial]
  split_ifs with h
  · rw [one_smul]
  · exact absurd rfl h

end Descent

section Retraction

variable [CompactSpace X] [IsLocallyNoetherian X] [(G.obj 0).IsFiniteType]


instance isQuasicoherent_pushforward_grSheaf :
    ((Scheme.Modules.pushforward S.q).obj (S.grSheaf G)).IsQuasicoherent :=
  isQuasicoherent_pushforward S.q _

/-- **The projection** `q_* grSheaf ⟶ I^{k+1} G_{k+1}` onto the graded piece of degree `k + 1`. -/
def πMap (k : ℕ) : (Scheme.Modules.pushforward S.q).obj (S.grSheaf G) ⟶ G.grSucc k :=
  (AffineHomData.ofPushforward S.q (S.grSheaf G) (G.grSucc k) (fun _ hV ↦ S.muFun G hV k)
    (fun _ hV r t ↦ S.muFun_smul G hV k r t) (fun hV hW h t ↦ S.muFun_res G k hV hW h t)).toHom

lemma πMap_app (k : ℕ) {U : X.Opens} (hU : IsAffineOpen U)
    (t : Γ((Scheme.Modules.pushforward S.q).obj (S.grSheaf G), U)) :
    (S.πMap G k).app U t = S.muFun G hU k t := by
  unfold πMap
  exact AffineHomData.toHom_app _ hU t

lemma jMap_app (k : ℕ) (U : X.Opens) (w : Γ(⨁ fun _ : mon S.σ (k + 1) ↦ G.obj 0, U)) :
    (S.jMap G k).app U w = (S.grπ G).app (S.q ⁻¹ᵁ U)
      ((S.psi G k).app (S.q ⁻¹ᵁ U) (Scheme.Modules.pullbackApp S.q _ U w)) := by
  rw [jMap, Adjunction.homEquiv_unit]
  rfl

/-- **The graded piece `I^{k+1} G_{k+1}` is a direct summand of `q_* grSheaf`**. -/
@[reassoc (attr := simp)]
lemma iMap_πMap (k : ℕ) : S.iMap G k ≫ S.πMap G k = 𝟙 _ := by
  rw [← cancel_epi (S.gen G k), gen_iMap_assoc, Category.comp_id]
  have : (⨁ fun _ : mon S.σ (k + 1) ↦ G.obj 0).IsQuasicoherent := isQuasicoherent_biproduct _
  refine hom_ext_of_affine fun U hU w ↦ ?_
  rw [Scheme.Modules.Hom.comp_app_apply, jMap_app]
  refine (S.πMap_app G k hU _).trans ?_
  rw [muFun_grπ, lamFun_psi]

end Retraction

section Coherence

variable [CompactSpace X] [IsLocallyNoetherian X] [(G.obj 0).IsFiniteType]

/-- The graded sheaf is of finite type: it is a quotient of `q^* G₀`. -/
instance isFiniteType_grSheaf : (S.grSheaf G).IsFiniteType := by
  have : (⨁ fun k : Fin (S.degBound G) ↦
      (Scheme.Modules.pullback S.q).obj (S.rel G k)).IsQuasicoherent :=
    isQuasicoherent_biproduct _
  refine isFiniteType_of_finite_sections _ (fun W : S.Y.affineOpens ↦ (W : S.Y.Opens))
    (iSup_affineOpens_eq_top S.Y) (fun W ↦ W.2) fun W ↦ ?_
  have := finite_sections_of_isFiniteType ((Scheme.Modules.pullback S.q).obj (G.obj 0)) W.2
  exact Module.Finite.of_surjective (appLinearMap (S.grπ G) W)
    (cokernel_π_app_surjective _ W.2)

/-- The graded sheaf is coherent. -/
instance isCoherent_grSheaf : (S.grSheaf G).IsCoherent where
  isQuasicoherent := inferInstance
  isFiniteType := inferInstance

end Coherence

end GradedSetup

end GradedSheaf

end AlgebraicGeometry.CohomologyAux
