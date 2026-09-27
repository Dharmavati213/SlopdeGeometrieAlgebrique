/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import SGA.SGA1.ExposeXI.AffineSheaves
import SGA.SGA1.ExposeXI.ArtinSchreierCohomology
import SGA.SGA1.ExposeXI.ZariskiComparison

/-!
# SGA 1, Exposé XI.5.1 for `𝔾_a`: principal bundles under the additive group

XI.5.1 says that every principal homogeneous bundle under `𝔾_{a,S}` is locally trivial. We prove
the stronger statement that every fpqc torsor under `𝔾_{a,S}` is trivial over each affine open
subset of `S` (`nonempty_section_of_isAffineOpen`), hence locally trivial
(`isLocallyTrivial_Ga`), and trivial when `S` is affine (`H1_Ga_eq_one_of_isAffine`), so that
`H¹(S, 𝔾_a) ≅ H¹(S_Zar, 𝒪_S)` (XI.5.3, `h1GaEquivZariski`).

SGA reduces this to descent of extensions of `𝒪` by `𝒪` (VIII.1.1). We argue with the Amitsur
complex, which is the same thing: over `Spec A`, a torsor trivialized on a faithfully flat
`Spec B` gives a cocycle `c ∈ B ⊗_A B`, `c₁₃ = c₁₂ + c₂₃`; after tensoring with `B` the cocycle
becomes the coboundary of `c`, so by faithful flatness `c = 1 ⊗ b - b ⊗ 1`
(`exists_eq_amitsurD`), and the section translated by `-b` descends to `Spec A`.
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry TensorProduct

namespace SGA.SGA1.ExposeXI

section Amitsur

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Faithfully flat descent of images: if `1 ⊗ n` lies in the image of `B ⊗ f`, then `n` lies in
the image of `f`. -/
lemma mem_range_of_one_tmul_mem_range [Module.FaithfullyFlat A B] {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (n : N)
    (h : (1 : B) ⊗ₜ[A] n ∈ LinearMap.range (f.lTensor B)) : n ∈ LinearMap.range f := by
  let q := (LinearMap.range f).mkQ
  have hex' := lTensor_exact B (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _)
  have h0 : q.lTensor B ((1 : B) ⊗ₜ[A] n) = 0 := (hex' _).2 h
  rw [LinearMap.lTensor_tmul] at h0
  have : q n = 0 := Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) _
    (by rw [TensorProduct.mk_apply, h0, map_zero])
  exact (Submodule.Quotient.mk_eq_zero _).1 this

variable (A B) in
/-- The first differential `b ↦ 1 ⊗ b - b ⊗ 1` of the Amitsur complex of `A → B`. -/
noncomputable def amitsurD : B →ₗ[A] B ⊗[A] B :=
  TensorProduct.mk A B B 1 - (TensorProduct.mk A B B).flip 1

lemma amitsurD_apply (b : B) : amitsurD A B b = 1 ⊗ₜ b - b ⊗ₜ 1 := rfl

/-- XI.5.1 for `𝔾_a` (Amitsur): for `A → B` faithfully flat, every `1`-cocycle `c ∈ B ⊗_A B`,
i.e. `c₁₃ = c₁₂ + c₂₃` in `B ⊗_A B ⊗_A B`, is a coboundary `1 ⊗ b - b ⊗ 1`. -/
theorem exists_eq_amitsurD [Module.FaithfullyFlat A B] (c : B ⊗[A] B)
    (hc : Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) c =
      Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) c +
      (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) c) :
    ∃ b : B, c = 1 ⊗ₜ b - b ⊗ₜ 1 := by
  have hD : ((amitsurD A B).lTensor B : B ⊗[A] B →ₗ[A] B ⊗[A] (B ⊗[A] B)) =
      (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toLinearMap -
      (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    simp [amitsurD_apply, TensorProduct.tmul_sub]
  have key : (amitsurD A B).lTensor B c = (1 : B) ⊗ₜ[A] c := by
    rw [hD, LinearMap.sub_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, hc,
      add_sub_cancel_left]
    rfl
  obtain ⟨b, hb⟩ := mem_range_of_one_tmul_mem_range (amitsurD A B) c ⟨c, key⟩
  exact ⟨b, hb.symm⟩

end Amitsur

section Affine

variable {S : Scheme.{u}} {A : CommRingCat.{u}} (a : Spec A ⟶ S)

lemma affOverHom_comp {B B' B'' : CommRingCat.{u}} {φ : A ⟶ B} {φ' : A ⟶ B'} {φ'' : A ⟶ B''}
    (ψ : B ⟶ B') (ψ' : B' ⟶ B'') (hψ : φ ≫ ψ = φ') (hψ' : φ' ≫ ψ' = φ'') :
    affOverHom a ψ' hψ' ≫ affOverHom a ψ hψ =
      affOverHom a (ψ ≫ ψ') (by rw [← Category.assoc, hψ, hψ']) := by
  ext
  exact (Spec.map_comp ψ ψ').symm

lemma affOverHom_congr {B B' : CommRingCat.{u}} {φ : A ⟶ B} {φ' : A ⟶ B'} {ψ ψ' : B ⟶ B'}
    (hψ : φ ≫ ψ = φ') (hψ' : φ ≫ ψ' = φ') (h : ψ = ψ') :
    affOverHom a ψ hψ = affOverHom a ψ' hψ' := by
  subst h
  rfl

/-- A section of `𝔾_a` over `T`, as an element of `Γ(T, 𝒪_T)`. -/
abbrev gaVal {T : Over S} (x : (Ga S).obj (op T)) : Γ(T.left, ⊤) :=
  Multiplicative.toAdd x

lemma gaVal_mul {T : Over S} (x y : (Ga S).obj (op T)) : gaVal (x * y) = gaVal x + gaVal y :=
  rfl

lemma ΓSpecIso_Ga_map_affOverHom {B B' : CommRingCat.{u}} {φ : A ⟶ B} {φ' : A ⟶ B'}
    (ψ : B ⟶ B') (hψ : φ ≫ ψ = φ') (m : (Ga S).obj (op (affOver a φ))) :
    (Scheme.ΓSpecIso B').hom (gaVal ((Ga S).map (affOverHom a ψ hψ).op m)) =
      ψ ((Scheme.ΓSpecIso B).hom (gaVal m)) := by
  change (Scheme.ΓSpecIso B').hom ((Spec.map ψ).appTop (gaVal m)) = _
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]

lemma Ga_ext_ΓSpecIso {B : CommRingCat.{u}} {φ : A ⟶ B} {m m' : (Ga S).obj (op (affOver a φ))}
    (h : (Scheme.ΓSpecIso B).hom (gaVal m) =
      (Scheme.ΓSpecIso B).hom (gaVal m')) : m = m' :=
  Multiplicative.toAdd.injective
    ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso B).hom).1 inferInstance |>.1 h)

/-- XI.5.1 for `𝔾_a`, over an affine base: an fpqc torsor under `𝔾_{a,S}` with a section over
`Spec B`, for a faithfully flat `A`-algebra `B`, has a section over `Spec A`. -/
theorem nonempty_section_Ga_of_faithfullyFlat (Q : Torsor (fpqc S) (Ga S)) (B : Type u)
    [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (e : Q.obj.obj (op (affOver a (CommRingCat.ofHom (algebraMap A B) : A ⟶ .of B)))) :
    Nonempty (Q.obj.obj (op (Over.mk a))) := by
  let φ : A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  have hφ : φ.hom.FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  let P : CommRingCat.{u} := CommRingCat.of (B ⊗[A] B)
  let inl : CommRingCat.of B ⟶ P := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let inr : CommRingCat.of B ⟶ P := CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  have h : IsPushout φ φ inl inr := CommRingCat.isPushout_tensorProduct A B B
  let e₁ := Q.obj.map (affOverHom a inl rfl).op e
  let e₂ := Q.obj.map (affOverHom a inr h.w.symm).op e
  let d := Q.diff e₁ e₂
  let c : P := (Scheme.ΓSpecIso P).hom (gaVal d)
  let P₃ : CommRingCat.{u} := CommRingCat.of (B ⊗[A] (B ⊗[A] B))
  let q₁₂ : P ⟶ P₃ := CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom
  let q₁₃ : P ⟶ P₃ := CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
    (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom
  let q₂₃ : P ⟶ P₃ := CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom
  have r₁ : inl ≫ q₁₂ = inl ≫ q₁₃ := by
    ext x
    rfl
  have r₂ : inr ≫ q₁₂ = inl ≫ q₂₃ := by
    ext x
    rfl
  have r₃ : inr ≫ q₁₃ = inr ≫ q₂₃ := by
    ext x
    rfl
  have hφ₁₂ : (φ ≫ inl) ≫ q₁₂ = φ ≫ inl ≫ q₁₂ := Category.assoc _ _ _
  have hφ₁₃ : (φ ≫ inl) ≫ q₁₃ = φ ≫ inl ≫ q₁₂ := by rw [Category.assoc, r₁]
  have hφ₂₃ : (φ ≫ inl) ≫ q₂₃ = φ ≫ inl ≫ q₁₂ := by
    rw [Category.assoc, ← r₂, ← Category.assoc, ← h.w, Category.assoc]
  let m₁₂ := affOverHom a q₁₂ hφ₁₂
  let m₁₃ := affOverHom a q₁₃ hφ₁₃
  let m₂₃ := affOverHom a q₂₃ hφ₂₃
  have E₁ : Q.obj.map m₁₂.op e₁ = Q.obj.map m₁₃.op e₁ := by
    simp only [e₁, ← Functor.map_comp_apply, ← op_comp, m₁₂, m₁₃, affOverHom_comp]
    exact congr_arg (fun k ↦ Q.obj.map (Quiver.Hom.op k) e) (affOverHom_congr a _ _ r₁)
  have E₂ : Q.obj.map m₁₂.op e₂ = Q.obj.map m₂₃.op e₁ := by
    simp only [e₁, e₂, ← Functor.map_comp_apply, ← op_comp, m₁₂, m₂₃, affOverHom_comp]
    exact congr_arg (fun k ↦ Q.obj.map (Quiver.Hom.op k) e) (affOverHom_congr a _ _ r₂)
  have E₃ : Q.obj.map m₁₃.op e₂ = Q.obj.map m₂₃.op e₂ := by
    simp only [e₂, ← Functor.map_comp_apply, ← op_comp, m₁₃, m₂₃, affOverHom_comp]
    exact congr_arg (fun k ↦ Q.obj.map (Quiver.Hom.op k) e) (affOverHom_congr a _ _ r₃)
  have h₁₂ : (Ga S).map m₁₂.op d = Q.diff (Q.obj.map m₁₂.op e₁) (Q.obj.map m₁₂.op e₂) :=
    Q.map_diff _ _ _
  have h₁₃ : (Ga S).map m₁₃.op d = Q.diff (Q.obj.map m₁₂.op e₁) (Q.obj.map m₁₃.op e₂) := by
    rw [E₁]
    exact Q.map_diff _ _ _
  have h₂₃ : (Ga S).map m₂₃.op d = Q.diff (Q.obj.map m₁₂.op e₂) (Q.obj.map m₁₃.op e₂) := by
    rw [E₂, E₃]
    exact Q.map_diff _ _ _
  have hcoc : (Ga S).map m₂₃.op d * (Ga S).map m₁₂.op d = (Ga S).map m₁₃.op d := by
    rw [h₁₂, h₁₃, h₂₃]
    exact Q.diff_mul_diff _ _ _
  have k₁₂ : (Scheme.ΓSpecIso P₃).hom (gaVal ((Ga S).map m₁₂.op d)) = q₁₂ c :=
    ΓSpecIso_Ga_map_affOverHom a q₁₂ hφ₁₂ d
  have k₁₃ : (Scheme.ΓSpecIso P₃).hom (gaVal ((Ga S).map m₁₃.op d)) = q₁₃ c :=
    ΓSpecIso_Ga_map_affOverHom a q₁₃ hφ₁₃ d
  have k₂₃ : (Scheme.ΓSpecIso P₃).hom (gaVal ((Ga S).map m₂₃.op d)) = q₂₃ c :=
    ΓSpecIso_Ga_map_affOverHom a q₂₃ hφ₂₃ d
  have key : (Scheme.ΓSpecIso P₃).hom (gaVal ((Ga S).map m₂₃.op d)) +
      (Scheme.ΓSpecIso P₃).hom (gaVal ((Ga S).map m₁₂.op d)) =
      (Scheme.ΓSpecIso P₃).hom (gaVal ((Ga S).map m₁₃.op d)) := by
    rw [← map_add]
    exact congr_arg (fun m ↦ (Scheme.ΓSpecIso P₃).hom (gaVal m)) hcoc
  have hc : q₁₃ c = q₁₂ c + q₂₃ c := by
    rw [k₂₃, k₁₂, k₁₃] at key
    rw [← key, add_comm]
  obtain ⟨b, hb⟩ := exists_eq_amitsurD c hc
  let g : (Ga S).obj (op (affOver a φ)) :=
    Multiplicative.ofAdd (-(Scheme.ΓSpecIso (.of B)).inv b)
  have hg : Q.obj.map (affOverHom a inl rfl).op (g • e) =
      Q.obj.map (affOverHom a inr h.w.symm).op (g • e) := by
    rw [Torsor.map_smul', Torsor.map_smul']
    change _ • e₁ = _ • e₂
    rw [← Q.diff_smul e₁ e₂, smul_smul]
    congr 1
    refine Ga_ext_ΓSpecIso a ?_
    change (Scheme.ΓSpecIso P).hom (gaVal ((Ga S).map (affOverHom a inl rfl).op g)) =
      (Scheme.ΓSpecIso P).hom (gaVal ((Ga S).map (affOverHom a inr h.w.symm).op g) +
        gaVal (Q.diff e₁ e₂))
    rw [map_add, ΓSpecIso_Ga_map_affOverHom, ΓSpecIso_Ga_map_affOverHom]
    change inl ((Scheme.ΓSpecIso (.of B)).hom (-(Scheme.ΓSpecIso (.of B)).inv b)) =
      inr ((Scheme.ΓSpecIso (.of B)).hom (-(Scheme.ΓSpecIso (.of B)).inv b)) + c
    rw [map_neg, Iso.inv_hom_id_apply, map_neg, map_neg, hb]
    change -(b ⊗ₜ[A] (1 : B)) = -((1 : B) ⊗ₜ[A] b) + ((1 : B) ⊗ₜ[A] b - b ⊗ₜ[A] (1 : B))
    abel
  obtain ⟨y, -⟩ := exists_descend_of_faithfullyFlat Q.isSheaf a φ hφ inl inr h _ hg
  exact ⟨y⟩

/-- XI.5.1 for `𝔾_a`: every fpqc torsor under `𝔾_{a,S}` has a section over every affine
`S`-scheme `Spec A`. -/
theorem nonempty_section_Ga (Q : Torsor (fpqc S) (Ga S)) :
    Nonempty (Q.obj.obj (op (Over.mk a))) := by
  obtain ⟨B, φ, hφ, ⟨e⟩⟩ := exists_faithfullyFlat_section Q.isSheaf a
    (Q.nonemptySieve (Over.mk a)) (Q.nonemptySieve_mem _) fun _ _ hf ↦ hf
  exact @nonempty_section_Ga_of_faithfullyFlat _ _ a Q B _ φ.hom.toAlgebra
    (@RingHom.faithfullyFlat_algebraMap_iff _ _ _ _ φ.hom.toAlgebra |>.1 hφ) e

end Affine

section Global

variable {S : Scheme.{u}}

/-- XI.5.1 for `𝔾_a`: an fpqc torsor under `𝔾_{a,S}` is trivial over every affine open subset
of `S`. -/
theorem nonempty_section_of_isAffineOpen (Q : Torsor (fpqc S) (Ga S)) {U : S.Opens}
    (hU : IsAffineOpen U) : Nonempty (Q.obj.obj (op ((opensToOver S).obj U))) := by
  obtain ⟨s⟩ := nonempty_section_Ga hU.fromSpec Q
  exact ⟨Q.obj.map (Over.homMk hU.isoSpec.hom hU.isoSpec_hom_fromSpec :
    (opensToOver S).obj U ⟶ Over.mk hU.fromSpec).op s⟩

/-- XI.5.1 for `𝔾_a`: every fpqc torsor under `𝔾_{a,S}` (in particular every principal
homogeneous bundle) is locally trivial. -/
theorem isLocallyTrivial_Ga (Q : Torsor (fpqc S) (Ga S)) : IsLocallyTrivial Q := fun x ↦ by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨U, hxU, nonempty_section_of_isAffineOpen Q hU⟩

/-- XI.5.3 for `𝔾_a`: `H¹(S, 𝔾_{a,S}) ≅ H¹(S_Zar, 𝒪_S(𝔾_a))`, the Zariski cohomology of the
sheaf `𝒪_S` (written multiplicatively). -/
noncomputable def h1GaEquivZariski :
    H1 (fpqc S) (Ga S) ≃ H1 (Opens.grothendieckTopology S) (zariskiSheaf (Ga S)) :=
  h1EquivOfLocallyTrivial (isSheaf_Ga S) isLocallyTrivial_Ga

/-- XI.5.1 for `𝔾_a`, affine base: over an affine scheme every fpqc torsor under `𝔾_a` is
trivial, i.e. `H¹(S, 𝒪_S) = 0`. -/
theorem H1_Ga_eq_trivialClass_of_isAffine [IsAffine S] (c : H1 (fpqc S) (Ga S)) :
    c = H1.trivialClass _ _ (isSheaf_Ga S) := by
  obtain ⟨Q, rfl⟩ := H1.mk_surjective c
  obtain ⟨s⟩ := nonempty_section_Ga S.isoSpec.inv Q
  refine (Torsor.class_eq_trivialClass_iff_of_isTerminal Over.mkIdTerminal _ Q).2
    ⟨Q.obj.map (Over.homMk S.isoSpec.hom (by simp) : Over.mk (𝟙 S) ⟶ Over.mk S.isoSpec.inv).op s⟩

/-- XI.6.9, example of an affine base: if `S` is affine of characteristic `p`, then
`H¹(S, ℤ/p) ≅ Γ(S, 𝒪_S) / ℘ Γ(S, 𝒪_S)` (classical Artin–Schreier theory). -/
theorem artinSchreierLeft_bijective_of_isAffine [IsAffine S] (p : ℕ) [Fact p.Prime]
    (hS : (p : Γ(S, ⊤)) = 0) : Function.Bijective (artinSchreierLeft S p hS) :=
  artinSchreierLeft_bijective S p hS fun x _ ↦ H1_Ga_eq_trivialClass_of_isAffine x

end Global

end SGA.SGA1.ExposeXI
