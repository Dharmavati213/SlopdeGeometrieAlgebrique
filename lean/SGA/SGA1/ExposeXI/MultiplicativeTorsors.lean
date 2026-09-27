/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Free
import SGA.SGA1.ExposeVIII.ModuleProperties
import SGA.SGA1.ExposeXI.AdditiveTorsors

/-!
# SGA 1, Exposé XI.5.1 for `𝔾_m`: Hilbert's theorem 90

XI.5.1 says that every principal homogeneous bundle under `𝔾_{m,S}` is locally trivial; SGA
proves it by fpqc descent of invertible Modules (VIII.1.1, VIII.1.12). We follow this proof over
an affine base: a torsor under `𝔾_m` trivialized over a faithfully flat `Spec B → Spec A` gives
a cocycle `c ∈ (B ⊗_A B)ˣ`, which is a descent datum `b ↦ (b ⊗ 1) c` on the `B`-module `B`
(`unitDescentDatum`). The descended module `M` is locally free of rank one (VIII.1.12), so near
each point of `Spec A` it has a generator `m`, which is a unit of `B` there and satisfies
`1 ⊗ m = (m ⊗ 1) c` (`exists_generator_of_cocycle`); the section of the torsor translated by
`m⁻¹` then descends.
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry TensorProduct

namespace SGA.SGA1.ExposeXI

section Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

open Algebra.TensorProduct

/-- The three maps `B ⊗_A B → B ⊗_A B ⊗_A B`: `x ⊗ y ↦ x ⊗ y ⊗ 1`. -/
noncomputable abbrev q₁₂ : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
  map (AlgHom.id A B) (includeLeft : B →ₐ[A] B ⊗[A] B)

/-- `x ⊗ y ↦ x ⊗ 1 ⊗ y`. -/
noncomputable abbrev q₁₃ : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
  map (AlgHom.id A B) (includeRight : B →ₐ[A] B ⊗[A] B)

/-- `x ⊗ y ↦ 1 ⊗ x ⊗ y`. -/
noncomputable abbrev q₂₃ : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
  includeRight

/-- The multiplication `B ⊗_A B ⊗_A B → B`. -/
noncomputable abbrev mul₃ : B ⊗[A] (B ⊗[A] B) →ₐ[A] B :=
  (lmul' A).comp (map (AlgHom.id A B) (lmul' A))

lemma mul₃_q₁₂ : (mul₃ : B ⊗[A] (B ⊗[A] B) →ₐ[A] B).comp q₁₂ = lmul' A := by
  ext x <;> simp

lemma mul₃_q₁₃ : (mul₃ : B ⊗[A] (B ⊗[A] B) →ₐ[A] B).comp q₁₃ = lmul' A := by
  ext x <;> simp

lemma mul₃_q₂₃ : (mul₃ : B ⊗[A] (B ⊗[A] B) →ₐ[A] B).comp q₂₃ = lmul' A := by
  ext x <;> simp

variable {c : B ⊗[A] B} (hc : q₁₃ c = q₁₂ c * q₂₃ c) (hu : IsUnit c)
include hc hu

/-- A `1`-cocycle restricts to `1` on the diagonal. -/
lemma lmul'_eq_one_of_cocycle : lmul' A c = 1 := by
  have h := congr_arg (mul₃ (A := A) (B := B)) hc
  rw [map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply, mul₃_q₁₂,
    mul₃_q₁₃, mul₃_q₂₃] at h
  exact (hu.map (lmul' A)).mul_eq_left.1 h.symm

omit hc hu in
lemma liftBaseChange_id_apply (z : B ⊗[A] B) :
    LinearMap.liftBaseChange B (LinearMap.id : B →ₗ[A] B) z = lmul' A z := by
  induction z with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

omit hc hu in
lemma lTensor_theta_apply (z : B ⊗[A] B) :
    (((LinearMap.mulRight B c).comp (Algebra.linearMap B (B ⊗[A] B))).restrictScalars A).lTensor B
      z = q₁₂ z * q₂₃ c := by
  induction z with
  | zero => simp
  | tmul x y =>
    simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.algebraMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy, add_mul]

omit hc hu in
lemma lTensor_mk_one_apply (z : B ⊗[A] B) :
    (TensorProduct.mk A B B 1).lTensor B z = q₁₃ z := by
  induction z with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- XI.5.1 for `𝔾_m`: a unit `1`-cocycle `c ∈ (B ⊗_A B)ˣ` is a descent datum `b ↦ (b ⊗ 1) c` on
the `B`-module `B` (VIII.1). -/
noncomputable def unitDescentDatum : ExposeVIII.ModuleDescentDatum A B B where
  coaction := (LinearMap.mulRight B c).comp (Algebra.linearMap B (B ⊗[A] B))
  counit b := by
    change LinearMap.liftBaseChange B LinearMap.id (algebraMap B (B ⊗[A] B) b * c) = b
    rw [← Algebra.smul_def, LinearMap.map_smul, liftBaseChange_id_apply,
      lmul'_eq_one_of_cocycle hc hu, smul_eq_mul, mul_one]
  coassoc b := by
    rw [lTensor_theta_apply, lTensor_mk_one_apply]
    change q₁₂ (algebraMap B (B ⊗[A] B) b * c) * q₂₃ c = q₁₃ (algebraMap B (B ⊗[A] B) b * c)
    rw [map_mul, map_mul, hc, mul_assoc]
    congr 1

lemma unitDescentDatum_coaction (b : B) :
    (unitDescentDatum hc hu).coaction b = (b ⊗ₜ[A] 1) * c := by
  change algebraMap B (B ⊗[A] B) b * c = _
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl

variable [Module.FaithfullyFlat A B]

set_option backward.isDefEq.respectTransparency false in
/-- XI.5.1 for `𝔾_m` (local freeness of the descended module): near each point `𝔭` of `Spec A`,
a unit `1`-cocycle `c` is the coboundary of an element `m` of `B`: there are `r ∉ 𝔭` and
`m, m' ∈ B` with `m m' = rᴺ` (so `m` is a unit over `D(r)`) and `1 ⊗ m = (m ⊗ 1) c`. -/
theorem exists_generator_of_cocycle (p : Ideal A) [p.IsPrime] :
    ∃ r ∉ p, ∃ (m m' : B) (N : ℕ), m * m' = algebraMap A B r ^ N ∧
      (1 : B) ⊗ₜ[A] m = (m ⊗ₜ[A] 1) * c := by
  have : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact ‹p.IsPrime›.ne_top (Subsingleton.elim _ _)
  have : Nontrivial B := (FaithfulSMul.algebraMap_injective A B).nontrivial
  let D := unitDescentDatum hc hu
  let M := D.invariants
  have : Module.Finite A M := D.finite_invariants
  have : Module.FinitePresentation A M := D.finitePresentation_invariants
  have : Module.Projective A M := D.projective_invariants
  have hrank : Module.rankAtStalk M ⟨p, inferInstance⟩ = 1 :=
    D.rankAtStalk_invariants 1 (fun q ↦ congr_fun Module.rankAtStalk_self q) _
  have : Module.Flat A M := inferInstance
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing (R := Localization.AtPrime p)
      (P := LocalizedModule p.primeCompl M)
  obtain ⟨r, hr, hfree, hrk⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (M := M) (M' := LocalizedModule p.primeCompl M) p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  have : Nontrivial (Localization (Submonoid.powers r)) :=
    (show Localization (Submonoid.powers r) →+* Localization.AtPrime p from
      IsLocalization.map (M := Submonoid.powers r) (T := p.primeCompl) _ (RingHom.id A)
        (Submonoid.powers_le.mpr hr)).domain_nontrivial
  let β := Module.basisUnique (Fin 1) (hrk.trans hrank)
  obtain ⟨m₀, s₀, hβ⟩ : ∃ (m₀ : M) (s₀ : Submonoid.powers r), β 0 = LocalizedModule.mk m₀ s₀ := by
    induction β 0 using LocalizedModule.induction_on with
    | h m s => exact ⟨m, s, rfl⟩
  have key (x : M) : ∃ (N : ℕ) (a : A), r ^ N • x = a • m₀ := by
    have hx : LocalizedModule.mk x 1 = β.repr (LocalizedModule.mk x 1) 0 • β 0 := by
      conv_lhs => rw [← β.sum_repr (LocalizedModule.mk x 1)]
      simp
    obtain ⟨⟨a, t⟩, ht⟩ := IsLocalization.mk'_surjective (Submonoid.powers r)
      (β.repr (LocalizedModule.mk x 1) 0)
    rw [← ht, hβ, ← Localization.mk_eq_mk', LocalizedModule.mk_smul_mk,
      LocalizedModule.mk_eq] at hx
    obtain ⟨w, hw⟩ := hx
    obtain ⟨j, hj⟩ := w.2
    obtain ⟨k, hk⟩ := (t * s₀).2
    have hj' : r ^ j = w := hj
    have hk' : r ^ k = ((t * s₀ : Submonoid.powers r) : A) := hk
    refine ⟨j + k, r ^ j * a, ?_⟩
    rw [one_smul, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def, ← hj', ← hk',
      smul_smul] at hw
    rw [pow_add, hw, mul_smul]
  have hsurj := (D.descentMap_bijective).2 1
  obtain ⟨y, hy⟩ := hsurj
  have hind : ∀ y : B ⊗[A] M, ∃ (N : ℕ) (m' : B),
      algebraMap A B r ^ N * D.descentMap y = m' * (m₀ : B) := by
    intro y
    induction y with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul b x =>
      obtain ⟨N, a, h⟩ := key x
      refine ⟨N, b * algebraMap A B a, ?_⟩
      rw [ExposeVIII.ModuleDescentDatum.descentMap_tmul, smul_eq_mul]
      have h' := congr_arg (fun z : M ↦ (z : B)) h
      simp only [Submodule.coe_smul, Algebra.smul_def, map_pow] at h'
      rw [mul_left_comm, h', mul_assoc]
    | add y z hy hz =>
      obtain ⟨N₁, m₁, h₁⟩ := hy
      obtain ⟨N₂, m₂, h₂⟩ := hz
      refine ⟨N₁ + N₂, algebraMap A B r ^ N₂ * m₁ + algebraMap A B r ^ N₁ * m₂, ?_⟩
      rw [map_add, pow_add]
      linear_combination (algebraMap A B r ^ N₂) * h₁ + (algebraMap A B r ^ N₁) * h₂
  obtain ⟨N, m', hm'⟩ := hind y
  rw [hy, mul_one] at hm'
  refine ⟨r, hr, m₀, m', N, by rw [hm', mul_comm], ?_⟩
  have hinv : D.coaction m₀ = 1 ⊗ₜ[A] (m₀ : B) := m₀.2
  rw [unitDescentDatum_coaction] at hinv
  exact hinv.symm

end Algebra

section Scheme

variable {S : Scheme.{u}} {A : CommRingCat.{u}} (a : Spec A ⟶ S)

/-- A section of `𝔾_m` over `T`, as an element of `Γ(T, 𝒪_T)`. -/
abbrev gmVal {T : Over S} (m : (Gm S).obj (op T)) : Γ(T.left, ⊤) :=
  ((show (Γ(T.left, ⊤))ˣ from m) : Γ(T.left, ⊤))

lemma gmVal_mul {T : Over S} (m m' : (Gm S).obj (op T)) : gmVal (m * m') = gmVal m * gmVal m' :=
  rfl

omit a in
lemma gmVal_map {T T' : Over S} (f : T' ⟶ T) (m : (Gm S).obj (op T)) :
    gmVal ((Gm S).map f.op m) = f.left.appTop (gmVal m) :=
  rfl

lemma ΓSpecIso_Gm_map_affOverHom {B B' : CommRingCat.{u}} {φ : A ⟶ B} {φ' : A ⟶ B'}
    (ψ : B ⟶ B') (hψ : φ ≫ ψ = φ') (m : (Gm S).obj (op (affOver a φ))) :
    (Scheme.ΓSpecIso B').hom (gmVal ((Gm S).map (affOverHom a ψ hψ).op m)) =
      ψ ((Scheme.ΓSpecIso B).hom (gmVal m)) := by
  change (Scheme.ΓSpecIso B').hom ((Spec.map ψ).appTop _) = _
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]

/-- A global section whose basic open is everything is a unit. -/
lemma isUnit_of_basicOpen_eq_top {X : Scheme.{u}} (s : Γ(X, ⊤)) (h : X.basicOpen s = ⊤) :
    IsUnit s :=
  X.toRingedSpace.isUnit_of_isUnit_germ ⊤ s fun x _ ↦
    (X.mem_basicOpen_top s x).1 (by rw [h]; trivial)

set_option backward.isDefEq.respectTransparency.types false in
/-- XI.5.1 for `𝔾_m` over an affine base (Hilbert 90): an fpqc torsor under `𝔾_{m,S}` with a
section over `Spec B`, for a faithfully flat `A`-algebra `B`, has sections over basic open
neighbourhoods `D(r)` of every point of `Spec A`. -/
theorem exists_basicOpen_section_Gm_of_faithfullyFlat (Q : Torsor (fpqc S) (Gm S)) (B : Type u)
    [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (e : Q.obj.obj (op (affOver a (CommRingCat.ofHom (algebraMap A B) : A ⟶ .of B))))
    (x : PrimeSpectrum A) :
    ∃ r : A, r ∉ x.asIdeal ∧ Nonempty (Q.obj.obj
      (op (Over.mk (((Spec A).basicOpen ((Scheme.ΓSpecIso A).inv r)).ι ≫ a)))) := by
  let φ : A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  have hφ : φ.hom.FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  let P : CommRingCat.{u} := CommRingCat.of (B ⊗[A] B)
  let inl : CommRingCat.of B ⟶ P := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let inr : CommRingCat.of B ⟶ P := CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  have h : IsPushout φ φ inl inr := CommRingCat.isPushout_tensorProduct A B B
  let e₁ := Q.obj.map (affOverHom a inl rfl).op e
  let e₂ := Q.obj.map (affOverHom a inr h.w.symm).op e
  let u := Q.diff e₁ e₂
  let c : B ⊗[A] B := (Scheme.ΓSpecIso P).hom (gmVal u)
  let P₃ : CommRingCat.{u} := CommRingCat.of (B ⊗[A] (B ⊗[A] B))
  let Q₁₂ : P ⟶ P₃ := CommRingCat.ofHom (q₁₂ (A := A) (B := B)).toRingHom
  let Q₁₃ : P ⟶ P₃ := CommRingCat.ofHom (q₁₃ (A := A) (B := B)).toRingHom
  let Q₂₃ : P ⟶ P₃ := CommRingCat.ofHom (q₂₃ (A := A) (B := B)).toRingHom
  have r₁ : inl ≫ Q₁₂ = inl ≫ Q₁₃ := by
    ext x
    rfl
  have r₂ : inr ≫ Q₁₂ = inl ≫ Q₂₃ := by
    ext x
    rfl
  have r₃ : inr ≫ Q₁₃ = inr ≫ Q₂₃ := by
    ext x
    rfl
  have hφ₁₂ : (φ ≫ inl) ≫ Q₁₂ = φ ≫ inl ≫ Q₁₂ := Category.assoc _ _ _
  have hφ₁₃ : (φ ≫ inl) ≫ Q₁₃ = φ ≫ inl ≫ Q₁₂ := by rw [Category.assoc, r₁]
  have hφ₂₃ : (φ ≫ inl) ≫ Q₂₃ = φ ≫ inl ≫ Q₁₂ := by
    rw [Category.assoc, ← r₂, ← Category.assoc, ← h.w, Category.assoc]
  let m₁₂ := affOverHom a Q₁₂ hφ₁₂
  let m₁₃ := affOverHom a Q₁₃ hφ₁₃
  let m₂₃ := affOverHom a Q₂₃ hφ₂₃
  have E₁ : Q.obj.map m₁₂.op e₁ = Q.obj.map m₁₃.op e₁ := by
    simp only [e₁, ← Functor.map_comp_apply, ← op_comp, m₁₂, m₁₃, affOverHom_comp]
    exact congr_arg (fun k ↦ Q.obj.map (Quiver.Hom.op k) e) (affOverHom_congr a _ _ r₁)
  have E₂ : Q.obj.map m₁₂.op e₂ = Q.obj.map m₂₃.op e₁ := by
    simp only [e₁, e₂, ← Functor.map_comp_apply, ← op_comp, m₁₂, m₂₃, affOverHom_comp]
    exact congr_arg (fun k ↦ Q.obj.map (Quiver.Hom.op k) e) (affOverHom_congr a _ _ r₂)
  have E₃ : Q.obj.map m₁₃.op e₂ = Q.obj.map m₂₃.op e₂ := by
    simp only [e₂, ← Functor.map_comp_apply, ← op_comp, m₁₃, m₂₃, affOverHom_comp]
    exact congr_arg (fun k ↦ Q.obj.map (Quiver.Hom.op k) e) (affOverHom_congr a _ _ r₃)
  have h₁₂ : (Gm S).map m₁₂.op u = Q.diff (Q.obj.map m₁₂.op e₁) (Q.obj.map m₁₂.op e₂) :=
    Q.map_diff _ _ _
  have h₁₃ : (Gm S).map m₁₃.op u = Q.diff (Q.obj.map m₁₂.op e₁) (Q.obj.map m₁₃.op e₂) := by
    rw [E₁]
    exact Q.map_diff _ _ _
  have h₂₃ : (Gm S).map m₂₃.op u = Q.diff (Q.obj.map m₁₂.op e₂) (Q.obj.map m₁₃.op e₂) := by
    rw [E₂, E₃]
    exact Q.map_diff _ _ _
  have hcoc : (Gm S).map m₂₃.op u * (Gm S).map m₁₂.op u = (Gm S).map m₁₃.op u := by
    rw [h₁₂, h₁₃, h₂₃]
    exact Q.diff_mul_diff _ _ _
  have k₁₂ := ΓSpecIso_Gm_map_affOverHom a Q₁₂ hφ₁₂ u
  have k₁₃ := ΓSpecIso_Gm_map_affOverHom a Q₁₃ hφ₁₃ u
  have k₂₃ := ΓSpecIso_Gm_map_affOverHom a Q₂₃ hφ₂₃ u
  have hc : q₁₃ c = q₁₂ c * q₂₃ c := by
    have key : (Scheme.ΓSpecIso P₃).hom (gmVal ((Gm S).map m₂₃.op u)) *
        (Scheme.ΓSpecIso P₃).hom (gmVal ((Gm S).map m₁₂.op u)) =
        (Scheme.ΓSpecIso P₃).hom (gmVal ((Gm S).map m₁₃.op u)) := by
      rw [← map_mul, ← gmVal_mul]
      exact congr_arg (fun m ↦ (Scheme.ΓSpecIso P₃).hom (gmVal m)) hcoc
    rw [k₁₂, k₁₃, k₂₃] at key
    exact key.symm.trans (mul_comm _ _)
  have hu : IsUnit c :=
    (Units.isUnit (show (Γ((affOver a (φ ≫ inl)).left, ⊤))ˣ from u)).map
      (Scheme.ΓSpecIso P).hom.hom
  obtain ⟨r, hr, m, m', N, hmm', hrel⟩ := exists_generator_of_cocycle hc hu x.asIdeal
  refine ⟨r, hr, ?_⟩
  let rΓ : Γ(Spec A, ⊤) := (Scheme.ΓSpecIso A).inv r
  let W : (Spec A).Opens := (Spec A).basicOpen rΓ
  let f : Spec (CommRingCat.of B) ⟶ Spec A := Spec.map φ
  obtain ⟨hfl, hsu⟩ := (flat_and_surjective_SpecMap_iff φ).2 hφ
  let V : (Spec (CommRingCat.of B)).Opens := f ⁻¹ᵁ W
  let TW : Over S := Over.mk (V.ι ≫ f ≫ a)
  let YW : Over S := Over.mk (W.ι ≫ a)
  let g : TW ⟶ YW := Over.homMk (f ∣_ W) (by
    change (f ∣_ W) ≫ W.ι ≫ a = V.ι ≫ f ≫ a
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc])
  have : Flat g.left := (inferInstance : Flat (f ∣_ W))
  have : Surjective g.left := IsZariskiLocalAtTarget.restrict (P := @Surjective) hsu W
  have : QuasiCompact g.left := (inferInstance : QuasiCompact (f ∣_ W))
  let incl : TW ⟶ affOver a φ := Over.homMk V.ι rfl
  let mB : Γ(Spec (CommRingCat.of B), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of B)).inv m
  let m'B : Γ(Spec (CommRingCat.of B), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of B)).inv m'
  let tB : Γ(Spec (CommRingCat.of B), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv (algebraMap A B r)
  have htB : tB = f.appTop rΓ := by
    have := congr_arg (fun k ↦ k r) (Scheme.ΓSpecIso_inv_naturality φ)
    simp only [CommRingCat.comp_apply] at this
    exact this
  have ht : IsUnit (V.ι.appTop tB) := by
    refine isUnit_of_basicOpen_eq_top _ ?_
    rw [← Scheme.preimage_basicOpen_top, htB, ← Scheme.preimage_basicOpen_top]
    exact Scheme.Opens.ι_preimage_self V
  have hprod : V.ι.appTop mB * V.ι.appTop m'B = (V.ι.appTop tB) ^ N := by
    have : mB * m'B = tB ^ N := by
      simp only [mB, m'B, tB, ← map_mul, ← map_pow, hmm']
    rw [← map_mul, this, map_pow]
  have hsV : IsUnit (V.ι.appTop mB) := isUnit_of_mul_isUnit_left (hprod ▸ ht.pow N)
  let mV : (Gm S).obj (op TW) := hsV.unit
  have hmV : gmVal mV = V.ι.appTop mB := rfl
  suffices hcompat : ∀ ⦃Z : Over S⦄ (p₁ p₂ : Z ⟶ TW), p₁ ≫ g = p₂ ≫ g →
      Q.obj.map p₁.op (mV⁻¹ • Q.obj.map incl.op e) = Q.obj.map p₂.op (mV⁻¹ • Q.obj.map incl.op e) by
    obtain ⟨y, -⟩ := exists_descend_of_fpqc Q.isSheaf g _ hcompat
    exact ⟨y⟩
  intro Z p₁ p₂ hp
  have hpb := isPullback_SpecMap_of_isPushout φ φ inl inr h
  have hq : (p₁ ≫ incl).left ≫ Spec.map φ = (p₂ ≫ incl).left ≫ Spec.map φ := by
    have := congr_arg (fun k ↦ k.left ≫ W.ι) hp
    simp only [Over.comp_left, Category.assoc] at this
    simpa [g, incl, morphismRestrict_ι] using this
  let k : Z ⟶ affOver a (φ ≫ inl) :=
    Over.homMk (hpb.lift (p₁ ≫ incl).left (p₂ ≫ incl).left hq) (by
      change hpb.lift (p₁ ≫ incl).left (p₂ ≫ incl).left hq ≫ Spec.map (φ ≫ inl) ≫ a = Z.hom
      rw [Spec.map_comp, ← Category.assoc, ← Category.assoc, hpb.lift_fst, Category.assoc]
      exact Over.w (p₁ ≫ incl))
  have k₁ : k ≫ affOverHom a inl rfl = p₁ ≫ incl := by
    ext
    exact hpb.lift_fst _ _ _
  have k₂ : k ≫ affOverHom a inr h.w.symm = p₂ ≫ incl := by
    ext
    exact hpb.lift_snd _ _ _
  have hx₁ : Q.obj.map p₁.op (Q.obj.map incl.op e) = Q.obj.map k.op e₁ := by
    rw [← Functor.map_comp_apply, ← op_comp, ← k₁, op_comp, Functor.map_comp_apply]
  have hx₂ : Q.obj.map p₂.op (Q.obj.map incl.op e) = Q.obj.map k.op e₂ := by
    rw [← Functor.map_comp_apply, ← op_comp, ← k₂, op_comp, Functor.map_comp_apply]
  rw [Torsor.map_smul', Torsor.map_smul', hx₁, hx₂, ← Q.diff_smul e₁ e₂, Torsor.map_smul',
    smul_smul]
  congr 1
  have key : (Gm S).map p₂.op mV = (Gm S).map p₁.op mV * (Gm S).map k.op u := by
    apply Units.ext
    change gmVal ((Gm S).map p₂.op mV) = gmVal ((Gm S).map p₁.op mV) * gmVal ((Gm S).map k.op u)
    rw [gmVal_map, gmVal_map, gmVal_map, hmV]
    change (p₂ ≫ incl).left.appTop mB = (p₁ ≫ incl).left.appTop mB * k.left.appTop (gmVal u)
    rw [← k₁, ← k₂, Over.comp_left, Over.comp_left, Scheme.Hom.comp_appTop,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, CommRingCat.comp_apply, ← map_mul]
    congr 1
    have hu' : gmVal u = (Scheme.ΓSpecIso P).inv c := by
      simp only [c, Iso.hom_inv_id_apply]
    have hl : (Scheme.ΓSpecIso P).inv (inl m) = (Spec.map inl).appTop mB :=
      ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality inl) m
    have hr' : (Scheme.ΓSpecIso P).inv (inr m) = (Spec.map inr).appTop mB :=
      ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality inr) m
    change (Spec.map inr).appTop mB = (Spec.map inl).appTop mB * (show Γ(Spec P, ⊤) from gmVal u)
    rw [← hl, ← hr', hu', ← map_mul]
    exact congr_arg _ hrel
  rw [map_inv, map_inv, key, mul_inv_rev, Gm_isCommutative S _ ((Gm S).map k.op u)⁻¹,
    mul_assoc, inv_mul_cancel, mul_one]

end Scheme

section Global

variable {S : Scheme.{u}}

/-- XI.5.1 for `𝔾_m` (Hilbert's theorem 90): every fpqc torsor under `𝔾_{m,S}` (in particular
every principal homogeneous bundle) is locally trivial for the Zariski topology. -/
theorem isLocallyTrivial_Gm (Q : Torsor (fpqc S) (Gm S)) : IsLocallyTrivial Q := fun x ↦ by
  obtain ⟨_, ⟨U, hU', rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU'
  let a := hU.fromSpec
  obtain ⟨B, φ, hφ, ⟨e⟩⟩ := exists_faithfullyFlat_section Q.isSheaf a
    (Q.nonemptySieve (Over.mk a)) (Q.nonemptySieve_mem _) fun _ _ hf ↦ hf
  have hx : x ∈ Set.range a := by rw [hU.range_fromSpec]; exact hxU
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨r, hr, ⟨s⟩⟩ := @exists_basicOpen_section_Gm_of_faithfullyFlat _ _ a Q B _
    φ.hom.toAlgebra (@RingHom.faithfullyFlat_algebraMap_iff _ _ _ _ φ.hom.toAlgebra |>.1 hφ) e y
  let W := (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv r)
  have hyW : y ∈ W := by
    change y ∈ (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv r)
    rw [basicOpen_eq_of_affine]
    exact hr
  have : IsOpenImmersion a := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hrange : Set.range ((W.ι ≫ a).opensRange.ι) ⊆ Set.range (W.ι ≫ a) := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange]
  refine ⟨(W.ι ≫ a).opensRange, ?_, ⟨Q.obj.map (Over.homMk (IsOpenImmersion.lift (W.ι ≫ a)
    (W.ι ≫ a).opensRange.ι hrange) (IsOpenImmersion.lift_fac _ _ _) :
      (opensToOver S).obj (W.ι ≫ a).opensRange ⟶ Over.mk (W.ι ≫ a)).op s⟩⟩
  rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]
  exact ⟨⟨y, hyW⟩, rfl⟩

end Global

end SGA.SGA1.ExposeXI
