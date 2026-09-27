/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.Free
import SGA.SGA1.ExposeXI.MultiplicativeTorsors

/-!
# SGA 1, Exposé XI.5.1 for `GL_n`: principal bundles under `GL_n` are locally trivial

XI.5.1 says that every principal homogeneous bundle under `GL_{n,S}` is locally trivial for the
Zariski topology; SGA proves it by fpqc descent of locally free Modules (VIII.1.1, VIII.1.12). We
follow this proof over an affine base, as for `𝔾_m = GL_1` (`MultiplicativeTorsors`): a torsor
under `GL_n` trivialized over a faithfully flat `Spec B → Spec A` gives a cocycle
`C ∈ GL_n(B ⊗_A B)`, which is a descent datum `v ↦ C (v ⊗ 1)` on the `B`-module `Bⁿ`
(`matrixDescentDatum`). The descended module `M` is locally free of rank `n` (VIII.1.12), so near
each point of `Spec A` it has a basis `m₁, …, mₙ`, whose matrix `G` is invertible there and
satisfies `C (G ⊗ 1) = 1 ⊗ G` (`exists_matrix_of_cocycle`); the section of the torsor translated
by `G⁻¹` then descends (`exists_basicOpen_section_GLn_of_faithfullyFlat`).

* `GLn S n`: the fpqc sheaf of groups `T ↦ GL_n(Γ(T, 𝒪_T))` (`isSheaf_GLn`);
* `isLocallyTrivial_GLn`: XI.5.1 for `GL_n`;
* `h1GLnEquivZariski`: XI.5.3 for `GL_n`, `H¹(S, GL_n) ≅ H¹(S_Zar, GL_n(𝒪_S))`. The further
  identification of the Zariski cohomology set with isomorphism classes of locally free
  `𝒪_S`-Modules of rank `n` is not formalized.
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry TensorProduct Matrix

namespace SGA.SGA1.ExposeXI

section Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}

open Algebra.TensorProduct

variable (A B n) in
/-- The coordinates `B ⊗_A Bⁿ ≅ (B ⊗_A B)ⁿ`. -/
noncomputable abbrev coordEquiv : B ⊗[A] (Fin n → B) ≃ₗ[B] (Fin n → B ⊗[A] B) :=
  TensorProduct.piRight A B B (fun _ : Fin n ↦ B)

variable (A B n) in
/-- The coordinates `B ⊗_A (B ⊗_A Bⁿ) ≅ (B ⊗_A B ⊗_A B)ⁿ`. -/
noncomputable abbrev coordEquiv₃ : B ⊗[A] (B ⊗[A] (Fin n → B)) ≃ₗ[A] (Fin n → B ⊗[A] (B ⊗[A] B)) :=
  LinearEquiv.lTensor B ((coordEquiv A B n).restrictScalars A) ≪≫ₗ
    TensorProduct.piRight A A B (fun _ : Fin n ↦ B ⊗[A] B)

lemma coordEquiv₃_tmul (x : B) (z : B ⊗[A] (Fin n → B)) :
    coordEquiv₃ A B n (x ⊗ₜ z) = fun i ↦ x ⊗ₜ coordEquiv A B n z i :=
  rfl

/-- The vector `v ⊗ 1` of `(B ⊗_A B)ⁿ`. -/
abbrev tmulOneVec (v : Fin n → B) : Fin n → B ⊗[A] B := fun j ↦ v j ⊗ₜ[A] (1 : B)

variable (C : Matrix (Fin n) (Fin n) (B ⊗[A] B))

/-- The `B`-linear map `v ↦ C (v ⊗ 1)` from `Bⁿ` to `(B ⊗_A B)ⁿ`. -/
noncomputable def matrixCoactionAux : (Fin n → B) →ₗ[B] (Fin n → B ⊗[A] B) where
  toFun v := C *ᵥ tmulOneVec v
  map_add' v w := by
    rw [← mulVec_add]
    congr 1
    funext j
    simp [tmulOneVec, add_tmul]
  map_smul' b v := by
    rw [RingHom.id_apply, ← mulVec_smul]
    congr 1

/-- The coaction `v ↦ C (v ⊗ 1)` on `Bⁿ`. -/
noncomputable def matrixCoaction : (Fin n → B) →ₗ[B] B ⊗[A] (Fin n → B) :=
  (coordEquiv A B n).symm.toLinearMap ∘ₗ matrixCoactionAux C

lemma coordEquiv_matrixCoaction (v : Fin n → B) :
    coordEquiv A B n (matrixCoaction C v) = C *ᵥ tmulOneVec v := by
  simp [matrixCoaction, matrixCoactionAux]

lemma liftBaseChange_id_eq (y : B ⊗[A] (Fin n → B)) :
    LinearMap.liftBaseChange B (LinearMap.id : (Fin n → B) →ₗ[A] (Fin n → B)) y =
      fun i ↦ lmul' A (coordEquiv A B n y i) := by
  induction y with
  | zero => ext; simp
  | tmul x f => ext i; simp
  | add x y hx hy => rw [map_add, hx, hy, map_add]; ext i; simp

lemma coordEquiv₃_lTensor_coaction (y : B ⊗[A] (Fin n → B)) :
    coordEquiv₃ A B n (((matrixCoaction C).restrictScalars A).lTensor B y) =
      (q₂₃ (A := A) (B := B)).mapMatrix C *ᵥ fun j ↦ q₁₂ (coordEquiv A B n y j) := by
  induction y with
  | zero => ext; simp [mulVec, dotProduct]
  | tmul x f =>
    rw [LinearMap.lTensor_tmul, coordEquiv₃_tmul]
    change (fun i ↦ x ⊗ₜ coordEquiv A B n (matrixCoaction C f) i) = _
    rw [coordEquiv_matrixCoaction]
    funext i
    simp only [mulVec, dotProduct, tmul_sum, AlgHom.mapMatrix_apply, map_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, ← mulVec_add]
    congr 1
    funext j
    simp

lemma coordEquiv₃_lTensor_mk (y : B ⊗[A] (Fin n → B)) :
    coordEquiv₃ A B n ((TensorProduct.mk A B (Fin n → B) 1).lTensor B y) =
      fun i ↦ q₁₃ (coordEquiv A B n y i) := by
  induction y with
  | zero => ext; simp
  | tmul x f => rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    funext i
    simp

variable {C} (hc : (q₁₃ (A := A) (B := B)).mapMatrix C = q₂₃.mapMatrix C * q₁₂.mapMatrix C)
  (hu : IsUnit C)
include hc hu

/-- A `1`-cocycle restricts to `1` on the diagonal. -/
lemma lmul'_mapMatrix_eq_one : (lmul' A : B ⊗[A] B →ₐ[A] B).mapMatrix C = 1 := by
  have h := congrArg (mul₃ (A := A) (B := B)).mapMatrix hc
  have e (q : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) (hq : mul₃.comp q = lmul' A) :
      (mul₃ (A := A) (B := B)).mapMatrix (q.mapMatrix C) = (lmul' A).mapMatrix C := by
    simp only [AlgHom.mapMatrix_apply, map_map]
    rw [← hq]
    rfl
  rw [map_mul, e _ mul₃_q₁₃, e _ mul₃_q₂₃, e _ mul₃_q₁₂] at h
  exact ((hu.map (lmul' A : B ⊗[A] B →ₐ[A] B).mapMatrix).mul_eq_left).1 h.symm

/-- XI.5.1 for `GL_n`: a `1`-cocycle `C ∈ GL_n(B ⊗_A B)` is a descent datum `v ↦ C (v ⊗ 1)` on
the `B`-module `Bⁿ` (VIII.1). -/
noncomputable def matrixDescentDatum : ExposeVIII.ModuleDescentDatum A B (Fin n → B) where
  coaction := matrixCoaction C
  counit v := by
    rw [liftBaseChange_id_eq, coordEquiv_matrixCoaction]
    funext i
    have := RingHom.map_mulVec (lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom C (tmulOneVec v) i
    change lmul' A ((C *ᵥ tmulOneVec v) i) = v i
    rw [show lmul' A ((C *ᵥ tmulOneVec v) i) = _ from this]
    change ((lmul' A : B ⊗[A] B →ₐ[A] B).mapMatrix C *ᵥ _) i = _
    rw [lmul'_mapMatrix_eq_one hc hu, one_mulVec]
    simp
  coassoc v := by
    apply (coordEquiv₃ A B n).injective
    rw [coordEquiv₃_lTensor_coaction, coordEquiv₃_lTensor_mk, coordEquiv_matrixCoaction]
    have hq (q : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) (hq : ∀ b : B, q (b ⊗ₜ 1) = q₁₃ (b ⊗ₜ 1)) :
        (fun j ↦ q ((C *ᵥ tmulOneVec v) j)) =
          q.mapMatrix C *ᵥ fun j ↦ q₁₃ (tmulOneVec (A := A) v j) := by
      funext j
      refine (RingHom.map_mulVec q.toRingHom C (tmulOneVec v) j).trans ?_
      congr 1
      funext k
      exact hq (v k)
    have h₁₂ := hq q₁₂ fun b ↦ by simp
    have h₁₃ := hq q₁₃ fun b ↦ rfl
    rw [h₁₂, h₁₃, mulVec_mulVec, ← hc]

lemma matrixDescentDatum_coaction (v : Fin n → B) :
    (matrixDescentDatum hc hu).coaction v = matrixCoaction C v :=
  rfl

lemma mem_invariants_matrixDescentDatum {v : Fin n → B} :
    v ∈ (matrixDescentDatum hc hu).invariants ↔ C *ᵥ tmulOneVec v = fun j ↦ (1 : B) ⊗ₜ[A] v j := by
  rw [ExposeVIII.ModuleDescentDatum.mem_invariants, matrixDescentDatum_coaction,
    ← (coordEquiv A B n).injective.eq_iff, coordEquiv_matrixCoaction]
  rfl

variable [Module.FaithfullyFlat A B]

set_option backward.isDefEq.respectTransparency false in
/-- XI.5.1 for `GL_n` (local freeness of the descended module): near each point `𝔭` of `Spec A`,
a `1`-cocycle `C ∈ GL_n(B ⊗_A B)` is the coboundary of a matrix `G` over `B`: there are `r ∉ 𝔭`
and matrices `G, G'` over `B` with `G G'` diagonal with entries powers of `r` (so `G` is invertible
over `D(r)`) and `C (G ⊗ 1) = 1 ⊗ G`. The columns of `G` are a basis of the descended module over
`D(r)`. -/
theorem exists_matrix_of_cocycle (p : Ideal A) [p.IsPrime] :
    ∃ r ∉ p, ∃ (G G' : Matrix (Fin n) (Fin n) B) (N : Fin n → ℕ),
      G * G' = Matrix.diagonal (fun i ↦ algebraMap A B r ^ N i) ∧
      C * G.map (fun b ↦ b ⊗ₜ[A] (1 : B)) = G.map (fun b ↦ (1 : B) ⊗ₜ[A] b) := by
  have : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact ‹p.IsPrime›.ne_top (Subsingleton.elim _ _)
  have : Nontrivial B := (FaithfulSMul.algebraMap_injective A B).nontrivial
  let D := matrixDescentDatum hc hu
  let M := D.invariants
  have : Module.Finite A M := D.finite_invariants
  have : Module.FinitePresentation A M := D.finitePresentation_invariants
  have : Module.Projective A M := D.projective_invariants
  have hrank : Module.rankAtStalk M ⟨p, inferInstance⟩ = n :=
    D.rankAtStalk_invariants n (fun q ↦ by
      rw [congr_fun Module.rankAtStalk_eq_finrank_of_free q, Module.finrank_fin_fun]
      rfl) _
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
  let β := Module.finBasisOfFinrankEq (Localization (Submonoid.powers r))
    (LocalizedModule (Submonoid.powers r) M) (hrk.trans hrank)
  let f := LocalizedModule.mkLinearMap (Submonoid.powers r) M
  obtain ⟨⟨b₀, hb₀⟩, hint⟩ :=
    IsLocalizedModule.exist_integer_multiples_of_finite (Submonoid.powers r) f fun j ↦ β j
  choose m hm using hint
  obtain ⟨k₀, hk₀⟩ := hb₀
  -- Every element of `M` is, up to a power of `r`, a combination of the `m j`.
  have key (x : M) : ∃ (N : ℕ) (a : Fin n → A), r ^ N • x = ∑ j, a j • m j := by
    obtain ⟨⟨b₁, ⟨k₁, hk₁⟩⟩, hc₁⟩ := IsLocalization.exist_integer_multiples_of_finite
      (Submonoid.powers r) (fun j ↦ β.repr (f x) j)
    choose a ha using hc₁
    have e : f ((b₀ * b₁) • x) = f (∑ j, a j • m j) := by
      rw [map_sum, map_smul]
      conv_lhs => rw [← β.sum_repr (f x)]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_smul, hm j, smul_smul, ← algebraMap_smul (Localization (Submonoid.powers r)) (b₀ * b₁),
        ← algebraMap_smul (Localization (Submonoid.powers r)) (a j * b₀), smul_smul, map_mul, map_mul]
      have ha' : algebraMap A (Localization (Submonoid.powers r)) (a j) =
          algebraMap A _ b₁ * β.repr (f x) j := by
        rw [ha j, Algebra.smul_def]
      rw [ha']
      congr 1
      ring
    obtain ⟨k, hk⟩ := IsLocalizedModule.Away.exists_of_eq (f := f) r e
    refine ⟨k + (k₀ + k₁), fun j ↦ r ^ k * a j, ?_⟩
    have hk₀' : r ^ k₀ = b₀ := hk₀
    have hk₁' : r ^ k₁ = b₁ := hk₁
    rw [pow_add, pow_add, mul_smul, hk₀', hk₁', hk, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ smul_smul _ _ _
  -- The same holds for the elements of `B ⊗_A M = Bⁿ`, with coefficients in `B`.
  have hind : ∀ y : B ⊗[A] M, ∃ (N : ℕ) (b : Fin n → B),
      algebraMap A B r ^ N • D.descentMap y = ∑ j, b j • (m j : Fin n → B) := by
    intro y
    induction y with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul b x =>
      obtain ⟨N, a, h⟩ := key x
      refine ⟨N, fun j ↦ b * algebraMap A B (a j), ?_⟩
      rw [ExposeVIII.ModuleDescentDatum.descentMap_tmul, smul_comm, ← map_pow, algebraMap_smul]
      have h' := congrArg (fun z : M ↦ (z : Fin n → B)) h
      simp only [Submodule.coe_smul, Submodule.coe_sum] at h'
      rw [h', Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← algebraMap_smul B (a j), smul_smul]
    | add y z hy hz =>
      obtain ⟨N₁, b₁, h₁⟩ := hy
      obtain ⟨N₂, b₂, h₂⟩ := hz
      refine ⟨N₁ + N₂, fun j ↦ algebraMap A B r ^ N₂ * b₁ j + algebraMap A B r ^ N₁ * b₂ j, ?_⟩
      rw [map_add, smul_add, pow_add]
      conv_lhs => rw [mul_comm (algebraMap A B r ^ N₁), mul_smul, h₁, mul_comm, mul_smul, h₂]
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [smul_smul, smul_smul, add_smul]
  choose y hy using fun i : Fin n ↦ (D.descentMap_bijective).2 (Pi.single i 1)
  choose N b hNb using fun i ↦ hind (y i)
  refine ⟨r, hr, Matrix.of fun i j ↦ (m j : Fin n → B) i, Matrix.of fun j i ↦ b i j, N, ?_, ?_⟩
  · ext k i
    have := congr_fun (hNb i) k
    rw [hy i] at this
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this
    rw [Matrix.mul_apply, diagonal_apply]
    simp only [of_apply]
    rw [Finset.sum_congr rfl fun j _ ↦ mul_comm _ _, ← this, Pi.single_apply]
    split_ifs with hki
    · subst hki
      simp
    · simp
  · ext i j
    have hinv := (mem_invariants_matrixDescentDatum hc hu).1 (m j).2
    have := congr_fun hinv i
    simp only [mulVec, dotProduct] at this
    rw [Matrix.mul_apply]
    simp only [map_apply, of_apply]
    exact this

end Algebra

section Sheaf

variable (S : Scheme.{u}) (n : ℕ)

/-- XI.5.1: the sheaf of groups `GL_{n,S}` on `S`-schemes, `T ↦ GL_n(Γ(T, 𝒪_T))`. -/
noncomputable def GLn : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (GL (Fin n) Γ(T.unop.left, ⊤))
  map f := GrpCat.ofHom (Matrix.GeneralLinearGroup.map f.unop.left.appTop.hom)
  map_id T := by
    refine GrpCat.hom_ext (MonoidHom.ext fun x ↦ Units.ext ?_)
    ext i j
    change (𝟙 T.unop.left : T.unop.left ⟶ _).appTop ((x : Matrix _ _ _) i j) = (x : Matrix _ _ _) i j
    simp only [Scheme.Hom.id_appTop]
    rfl
  map_comp f g := by
    refine GrpCat.hom_ext (MonoidHom.ext fun x ↦ Units.ext ?_)
    ext i j
    change (g.unop.left ≫ f.unop.left).appTop ((x : Matrix _ _ _) i j) =
      g.unop.left.appTop (f.unop.left.appTop ((x : Matrix _ _ _) i j))
    rw [Scheme.Hom.comp_appTop]
    rfl

variable {S n} in
/-- A section of `GL_n` over `T`, as a matrix over `Γ(T, 𝒪_T)`. -/
abbrev glVal {T : Over S} (m : (GLn S n).obj (op T)) : Matrix (Fin n) (Fin n) Γ(T.left, ⊤) :=
  ((show GL (Fin n) Γ(T.left, ⊤) from m) : Matrix (Fin n) (Fin n) Γ(T.left, ⊤))

variable {S n} in
lemma glVal_mul {T : Over S} (m m' : (GLn S n).obj (op T)) :
    glVal (m * m') = glVal m * glVal m' :=
  rfl

variable {S n} in
lemma glVal_map {T T' : Over S} (f : T' ⟶ T) (m : (GLn S n).obj (op T)) :
    glVal ((GLn S n).map f.op m) = (glVal m).map f.left.appTop :=
  rfl

/-- XI.5.1: `GL_{n,S}` is an fpqc sheaf: the entries of a matrix which is locally invertible glue,
and so do the entries of the local inverses. -/
theorem isSheaf_GLn : Presieve.IsSheaf (fpqc S) (GLn S n ⋙ CategoryTheory.forget GrpCat) := by
  have hO := isSheaf_ringPresheaf S
  intro T R hR x hx
  let val (i j : Fin n) :
      Presieve.FamilyOfElements (ringPresheaf S ⋙ CategoryTheory.forget CommRingCat) R :=
    fun V f hf ↦ glVal (n := n) (T := V) (x f hf) i j
  let inv (i j : Fin n) :
      Presieve.FamilyOfElements (ringPresheaf S ⋙ CategoryTheory.forget CommRingCat) R :=
    fun V f hf ↦ glVal (n := n) (T := V) (x f hf)⁻¹ i j
  have hval (i j : Fin n) : (val i j).Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congr_arg (fun y : (GLn S n).obj (op Z) ↦ glVal y i j) (hx g₁ g₂ h₁ h₂ w)
  have hinv (i j : Fin n) : (inv i j).Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congr_arg (fun y : (GLn S n).obj (op Z) ↦ glVal y⁻¹ i j) (hx g₁ g₂ h₁ h₂ w)
  choose a ha using fun i j ↦ (hO R hR (val i j) (hval i j)).exists
  choose b hb using fun i j ↦ (hO R hR (inv i j) (hinv i j)).exists
  let Am : Matrix (Fin n) (Fin n) Γ(T.left, ⊤) := Matrix.of a
  let Bm : Matrix (Fin n) (Fin n) Γ(T.left, ⊤) := Matrix.of b
  have hAf : ∀ ⦃V : Over S⦄ (f : V ⟶ T) (hf : R f), Am.map f.left.appTop = glVal (x f hf) :=
    fun V f hf ↦ by ext i j; exact ha i j f hf
  have hBf : ∀ ⦃V : Over S⦄ (f : V ⟶ T) (hf : R f), Bm.map f.left.appTop = glVal (x f hf)⁻¹ :=
    fun V f hf ↦ by ext i j; exact hb i j f hf
  have hsep : ∀ M M' : Matrix (Fin n) (Fin n) Γ(T.left, ⊤),
      (∀ ⦃V : Over S⦄ (f : V ⟶ T), R f → M.map f.left.appTop = M'.map f.left.appTop) → M = M' := by
    intro M M' h
    ext i j
    exact (hO R hR).isSeparatedFor.ext fun V f hf ↦ congr_fun (congr_fun (h f hf) i) j
  have hAB : Am * Bm = 1 := hsep _ _ fun V f hf ↦ by
    rw [Matrix.map_mul, hAf f hf, hBf f hf, ← glVal_mul, mul_inv_cancel, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have hBA : Bm * Am = 1 := hsep _ _ fun V f hf ↦ by
    rw [Matrix.map_mul, hAf f hf, hBf f hf, ← glVal_mul, inv_mul_cancel, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  let g : GL (Fin n) Γ(T.left, ⊤) := ⟨Am, Bm, hAB, hBA⟩
  refine ⟨g, fun V f hf ↦ Units.ext (hAf f hf), fun (v : GL (Fin n) Γ(T.left, ⊤)) hv ↦
    Units.ext (hsep _ _ fun V f hf ↦ ?_)⟩
  rw [hAf f hf]
  exact congr_arg (fun y : (GLn S n).obj (op V) ↦ glVal y) (hv f hf)

end Sheaf

section Scheme

variable {S : Scheme.{u}} {n : ℕ} {A : CommRingCat.{u}} (a : Spec A ⟶ S)

lemma ΓSpecIso_GLn_map_affOverHom {B B' : CommRingCat.{u}} {φ : A ⟶ B} {φ' : A ⟶ B'}
    (ψ : B ⟶ B') (hψ : φ ≫ ψ = φ') (m : (GLn S n).obj (op (affOver a φ))) :
    (glVal ((GLn S n).map (affOverHom a ψ hψ).op m)).map (Scheme.ΓSpecIso B').hom =
      ((glVal m).map (Scheme.ΓSpecIso B).hom).map ψ := by
  ext i j
  change (Scheme.ΓSpecIso B').hom ((Spec.map ψ).appTop _) = _
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- XI.5.1 for `GL_n` over an affine base: an fpqc torsor under `GL_{n,S}` with a section over
`Spec B`, for a faithfully flat `A`-algebra `B`, has sections over basic open neighbourhoods
`D(r)` of every point of `Spec A`. -/
theorem exists_basicOpen_section_GLn_of_faithfullyFlat (Q : Torsor (fpqc S) (GLn S n))
    (B : Type u) [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
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
  let C : Matrix (Fin n) (Fin n) (B ⊗[A] B) := (glVal u).map (Scheme.ΓSpecIso P).hom
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
  have h₁₂ : (GLn S n).map m₁₂.op u = Q.diff (Q.obj.map m₁₂.op e₁) (Q.obj.map m₁₂.op e₂) :=
    Q.map_diff _ _ _
  have h₁₃ : (GLn S n).map m₁₃.op u = Q.diff (Q.obj.map m₁₂.op e₁) (Q.obj.map m₁₃.op e₂) := by
    rw [E₁]
    exact Q.map_diff _ _ _
  have h₂₃ : (GLn S n).map m₂₃.op u = Q.diff (Q.obj.map m₁₂.op e₂) (Q.obj.map m₁₃.op e₂) := by
    rw [E₂, E₃]
    exact Q.map_diff _ _ _
  have hcoc : (GLn S n).map m₂₃.op u * (GLn S n).map m₁₂.op u = (GLn S n).map m₁₃.op u := by
    rw [h₁₂, h₁₃, h₂₃]
    exact Q.diff_mul_diff _ _ _
  have k₁₂ := ΓSpecIso_GLn_map_affOverHom a Q₁₂ hφ₁₂ u
  have k₁₃ := ΓSpecIso_GLn_map_affOverHom a Q₁₃ hφ₁₃ u
  have k₂₃ := ΓSpecIso_GLn_map_affOverHom a Q₂₃ hφ₂₃ u
  have hc : (q₁₃ (A := A) (B := B)).mapMatrix C = q₂₃.mapMatrix C * q₁₂.mapMatrix C := by
    have key := congr_arg (fun m ↦ (glVal m).map (Scheme.ΓSpecIso P₃).hom) hcoc
    simp only [glVal_mul, Matrix.map_mul] at key
    rw [k₁₂, k₁₃, k₂₃] at key
    exact key.symm
  have hu : IsUnit C :=
    (Units.isUnit (show GL (Fin n) Γ((affOver a (φ ≫ inl)).left, ⊤) from u)).map
      (Scheme.ΓSpecIso P).hom.hom.mapMatrix
  obtain ⟨r, hr, G, G', N, hGG', hrel⟩ := exists_matrix_of_cocycle hc hu x.asIdeal
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
  let ρB := (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let GB : Matrix (Fin n) (Fin n) Γ(Spec (CommRingCat.of B), ⊤) := G.map ρB
  let G'B : Matrix (Fin n) (Fin n) Γ(Spec (CommRingCat.of B), ⊤) := G'.map ρB
  let tB : Γ(Spec (CommRingCat.of B), ⊤) := ρB (algebraMap A B r)
  have htB : tB = f.appTop rΓ := by
    have := congr_arg (fun k ↦ k r) (Scheme.ΓSpecIso_inv_naturality φ)
    simp only [CommRingCat.comp_apply] at this
    exact this
  have ht : IsUnit (V.ι.appTop tB) := by
    refine isUnit_of_basicOpen_eq_top _ ?_
    rw [← Scheme.preimage_basicOpen_top, htB, ← Scheme.preimage_basicOpen_top]
    exact Scheme.Opens.ι_preimage_self V
  have hprod : GB.map V.ι.appTop.hom * G'B.map V.ι.appTop.hom =
      diagonal (fun i ↦ V.ι.appTop tB ^ N i) := by
    have hGB : GB * G'B = diagonal (fun i ↦ tB ^ N i) := by
      rw [← Matrix.map_mul, hGG', diagonal_map (map_zero _)]
      simp [tB]
    rw [← Matrix.map_mul, hGB, diagonal_map (map_zero _)]
    simp
  have hsV : IsUnit (GB.map V.ι.appTop.hom) := by
    rw [isUnit_iff_isUnit_det]
    refine isUnit_of_mul_isUnit_left (y := (G'B.map V.ι.appTop.hom).det) ?_
    rw [← det_mul, hprod, det_diagonal]
    exact IsUnit.prod_univ_iff.2 fun i ↦ ht.pow _
  let mV : (GLn S n).obj (op TW) := hsV.unit
  have hmV : glVal mV = GB.map V.ι.appTop.hom := rfl
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
  -- The relation `C (G ⊗ 1) = 1 ⊗ G`, over `Spec (B ⊗_A B)`.
  have hl (y : B) : (Spec.map inl).appTop (ρB y) = (Scheme.ΓSpecIso P).inv (inl y) :=
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality inl) y).symm
  have hr' (y : B) : (Spec.map inr).appTop (ρB y) = (Scheme.ΓSpecIso P).inv (inr y) :=
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality inr) y).symm
  let uP : Matrix (Fin n) (Fin n) Γ(Spec P, ⊤) := glVal u
  have hu' : uP = C.map (Scheme.ΓSpecIso P).inv.hom := by
    ext i j
    simp [C, uP]
  have hrelP : GB.map (Spec.map inr).appTop.hom = uP * GB.map (Spec.map inl).appTop.hom := by
    have e₁ : GB.map (Spec.map inr).appTop.hom =
        (G.map fun b ↦ (1 : B) ⊗ₜ[A] b).map (Scheme.ΓSpecIso P).inv.hom := by
      ext i j
      exact hr' (G i j)
    have e₂ : GB.map (Spec.map inl).appTop.hom =
        (G.map fun b ↦ b ⊗ₜ[A] (1 : B)).map (Scheme.ΓSpecIso P).inv.hom := by
      ext i j
      exact hl (G i j)
    rw [e₁, e₂, hu', ← Matrix.map_mul, ← hrel]
  have key : (GLn S n).map p₂.op mV = (GLn S n).map k.op u * (GLn S n).map p₁.op mV := by
    apply Units.ext
    change glVal ((GLn S n).map p₂.op mV) =
      glVal ((GLn S n).map k.op u) * glVal ((GLn S n).map p₁.op mV)
    rw [glVal_map, glVal_map, glVal_map, hmV, Matrix.map_map, Matrix.map_map]
    have c₁ : (fun y ↦ p₁.left.appTop (V.ι.appTop y)) =
        fun y ↦ k.left.appTop ((Spec.map inl).appTop y) := by
      funext y
      change (V.ι.appTop ≫ p₁.left.appTop) y = ((Spec.map inl).appTop ≫ k.left.appTop) y
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
      exact congrArg (fun m ↦ m.left.appTop y) k₁.symm
    have c₂ : (fun y ↦ p₂.left.appTop (V.ι.appTop y)) =
        fun y ↦ k.left.appTop ((Spec.map inr).appTop y) := by
      funext y
      change (V.ι.appTop ≫ p₂.left.appTop) y = ((Spec.map inr).appTop ≫ k.left.appTop) y
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
      exact congrArg (fun m ↦ m.left.appTop y) k₂.symm
    ext i j
    have hP := congr_fun (congr_fun hrelP i) j
    simp only [Matrix.map_apply, Matrix.mul_apply, Function.comp_apply] at hP ⊢
    refine (congr_fun c₂ (GB i j)).trans ?_
    refine (congrArg k.left.appTop.hom hP).trans ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_mul]
    exact congrArg _ (congr_fun c₁ (GB l j)).symm
  rw [_root_.map_inv, _root_.map_inv, key, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel,
    mul_one]

end Scheme

section Global

variable {S : Scheme.{u}} {n : ℕ}

/-- XI.5.1 for `GL_n`: every fpqc torsor under `GL_{n,S}` (in particular every principal
homogeneous bundle) is locally trivial for the Zariski topology. -/
theorem isLocallyTrivial_GLn (Q : Torsor (fpqc S) (GLn S n)) : IsLocallyTrivial Q := fun x ↦ by
  obtain ⟨_, ⟨U, hU', rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU'
  let a := hU.fromSpec
  obtain ⟨B, φ, hφ, ⟨e⟩⟩ := exists_faithfullyFlat_section Q.isSheaf a
    (Q.nonemptySieve (Over.mk a)) (Q.nonemptySieve_mem _) fun _ _ hf ↦ hf
  have hx : x ∈ Set.range a := by rw [hU.range_fromSpec]; exact hxU
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨r, hr, ⟨s⟩⟩ := @exists_basicOpen_section_GLn_of_faithfullyFlat _ _ _ a Q B _
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

variable (S n) in
/-- XI.5.3 for `GL_n`: `H¹(S, GL_{n,S}) ≅ H¹(S_Zar, GL_n(𝒪_S))`, the Zariski cohomology of the
sheaf `GL_n(𝒪_S)`. -/
noncomputable def h1GLnEquivZariski :
    H1 (fpqc S) (GLn S n) ≃ H1 (Opens.grothendieckTopology S) (zariskiSheaf (GLn S n)) :=
  h1EquivOfLocallyTrivial (isSheaf_GLn S n) isLocallyTrivial_GLn

end Global

end SGA.SGA1.ExposeXI
