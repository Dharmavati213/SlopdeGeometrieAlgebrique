/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.ProjectiveSpace
import SGA.Foundations.Cohomology.InvertibleSheaf
import SGA.Foundations.Projective.TwistingSheaf

/-!
# Cohomology of the twisting sheaves `𝒪(d)` on projective space

Let `X = Proj A[xᵢ : i ∈ σ]` (`σ` finite, non-empty) and `𝒪(d)` the `d`-th tensor power of
Serre's twisting sheaf (`Proj.twistingSheaf`, a line bundle trivialized on the `D₊(xᵢ)` with
transition functions `xⱼ / xᵢ`), as an `𝒪_X`-module (`Scheme.LineBundle.toModules`).

Sections of `𝒪(d)` over an open containing the torus embed into the Laurent polynomials
(`twistToLaurent`: `s ↦ xᵢ^d sᵢ`), and over `D₊(x_I)` the image is spanned by the monomials `x^μ`
of degree `d` with `μᵢ ≥ 0` for `i ∉ I`. We deduce, with the Čech complex of the standard cover
(Stacks Project, Tag 01XT; EGA III 2.1.12; Hartshorne III.5.1):
* `Hᵖ(X, 𝒪(d)) = 0` for `0 < p < r` and `p > r`, where `r + 1 = #σ`;
* `Hʳ(X, 𝒪(d)) = 0` for `d > -r - 1`.
-/

universe v u

open CategoryTheory TopologicalSpace Opposite MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry.projectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ : Type v} {A : Type u} [CommRing A]

section xPow

variable [DecidableEq σ]

variable (A) in
/-- The Laurent monomial `xᵢ^d`. -/
noncomputable def xPow (i : σ) (d : ℤ) : Laurent σ A :=
  AddMonoidAlgebra.single (d • Pi.single i 1) 1

lemma xPow_add (i : σ) (d e : ℤ) : xPow A i (d + e) = xPow A i d * xPow A i e := by
  rw [xPow, xPow, xPow, AddMonoidAlgebra.single_mul_single, add_smul, one_mul]

lemma xPow_zero (i : σ) : xPow A i 0 = 1 := by
  rw [xPow, zero_smul]
  rfl

lemma xPow_mul_xPow_neg (i : σ) (d : ℤ) : xPow A i d * xPow A i (-d) = 1 := by
  rw [← xPow_add, add_neg_cancel, xPow_zero]

lemma toLaurent_X_eq (i : σ) : toLaurent σ A (X i) = xPow A i 1 := by
  rw [toLaurent_X, xPow, one_smul]

lemma coeff_xPow_mul (i : σ) (d : ℤ) (ℓ : Laurent σ A) (μ : σ → ℤ) :
    (xPow A i d * ℓ).coeff μ = ℓ.coeff (μ - d • Pi.single i 1) := by
  rw [mul_comm, xPow, coeff_mul_single_one]

end xPow

lemma X_mem (i : σ) : (X i : MvPolynomial σ A) ∈ homogeneousSubmodule σ A 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X A i)

variable [Fintype σ] [DecidableEq σ] [Nonempty σ]

lemma prodX_erase_mem (i : σ) {a : MvPolynomial σ A} (ha : a ∈ homogeneousSubmodule σ A 1) :
    a * prodX σ A (Finset.univ.erase i) ∈
      homogeneousSubmodule σ A (1 • (Finset.univ : Finset σ).card) := by
  have h := SetLike.mul_mem_graded ha (prodX_mem (A := A) (Finset.univ.erase i))
  have hc : 1 + (Finset.univ.erase i).card = 1 • (Finset.univ : Finset σ).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), one_smul]
    have := (card_univ_pos (σ := σ))
    omega
  rwa [hc] at h

/-- On the torus, the section `a / xᵢ` of `𝒪` (for `a` of degree `1`) is `a ∏_{j ≠ i} xⱼ / ∏ xⱼ`. -/
lemma fracSection_eq_awayToSection (i : σ) {a : MvPolynomial σ A}
    (ha : a ∈ homogeneousSubmodule σ A 1) (h : torus σ A ≤ Proj.basicOpen _ (X i)) :
    Proj.fracSection _ ha (X_mem i) (torus σ A) h =
      Proj.awayToSection _ (prodX σ A Finset.univ)
        (Away.mk _ (prodX_mem _) 1 _ (prodX_erase_mem i ha)) := by
  refine Proj.section_ext _ fun x ↦ ?_
  rw [Proj.val_fracSection_apply]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [Away.val_mk, Localization.mk_eq_mk', Localization.mk_eq_mk', IsLocalization.map_mk',
    IsLocalization.mk'_eq_iff_eq]
  congr 1
  simp only [RingHom.id_apply, pow_one]
  rw [prodX, prodX, ← Finset.mul_prod_erase Finset.univ X (Finset.mem_univ i)]
  ring

/-- The image in the Laurent polynomials of the section `a / xᵢ` of `𝒪`. -/
lemma sectionToLaurent_fracSection (i : σ) {a : MvPolynomial σ A}
    (ha : a ∈ homogeneousSubmodule σ A 1) {V : (Proj (homogeneousSubmodule σ A)).Opens}
    (hV : torus σ A ≤ V) (hV' : V ≤ Proj.basicOpen _ (X i)) :
    sectionToLaurent σ A V hV (Proj.fracSection _ ha (X_mem i) V hV') =
      toLaurent σ A a * xPow A i (-1) := by
  rw [← sectionToLaurent_map hV (torus_le_basicOpen_prodX Finset.univ) hV, Proj.map_fracSection,
    fracSection_eq_awayToSection i ha (hV.trans hV'), sectionToLaurent_awayToSection,
    awayToLaurent_mk, pow_one, map_mul, mul_assoc]
  congr 1
  rw [toLaurent_prodX, invX, xPow, AddMonoidAlgebra.single_mul_single, one_mul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp [indicator]
  · simp [indicator, hj]

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
/-- A unit of the Laurent polynomials which is a monomial has monomial powers. -/
lemma val_zpow_of_val {u : (Laurent σ A)ˣ} {e : σ → ℤ}
    (hu : (u : Laurent σ A) = AddMonoidAlgebra.single e 1) (d : ℤ) :
    ((u ^ d : (Laurent σ A)ˣ) : Laurent σ A) = AddMonoidAlgebra.single (d • e) 1 := by
  have hinv : ((u⁻¹ : (Laurent σ A)ˣ) : Laurent σ A) = AddMonoidAlgebra.single (-e) 1 := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hu, AddMonoidAlgebra.single_mul_single, add_neg_cancel, one_mul]
    rfl
  induction d using Int.induction_on with
  | zero =>
    rw [zpow_zero, zero_smul]
    rfl
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, ih, hu, AddMonoidAlgebra.single_mul_single, one_mul,
      add_smul, one_smul]
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, ih, hinv, AddMonoidAlgebra.single_mul_single, one_mul,
      sub_smul, one_smul, sub_eq_add_neg]

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
lemma iSup_stdCover_ulift :
    ⨆ i : ULift.{max u v} σ, Proj.basicOpen (homogeneousSubmodule σ A) (X i.down) = ⊤ :=
  le_antisymm le_top ((iSup_stdCover σ A).ge.trans
    (iSup_le fun i ↦ le_iSup (fun j : ULift.{max u v} σ ↦
      Proj.basicOpen (homogeneousSubmodule σ A) (X j.down)) ⟨i⟩))

variable (σ A) in
/-- Serre's twisting line bundle `𝒪(1)` on `Proj A[xᵢ]` (`Proj.twistingSheaf`, indexed by
`ULift σ`): it is trivialized on the `D₊(xᵢ)`, with transition functions `xⱼ / xᵢ`. -/
noncomputable abbrev twistingBundle : (Proj (homogeneousSubmodule σ A)).LineBundle :=
  Proj.twistingSheaf (homogeneousSubmodule σ A) (fun i : ULift.{max u v} σ ↦ X i.down)
    (fun i ↦ X_mem i.down) iSup_stdCover_ulift

variable (σ A) in
/-- The twisting sheaf `𝒪(d)` on `Proj A[xᵢ]`, as an `𝒪`-module. -/
noncomputable abbrev twist (d : ℤ) : (Proj (homogeneousSubmodule σ A)).Modules :=
  (twistingBundle σ A).toModules d

variable (σ A) in
/-- The index of `D₊(xᵢ)` in the trivializing cover of `𝒪(1)`. -/
def idx (i : σ) : (twistingBundle σ A).ι := ULift.up i

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
lemma idx_surjective : Function.Surjective (idx σ A) := fun i ↦ ⟨i.down, rfl⟩

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
@[simp]
lemma twistingBundle_U (i : σ) : (twistingBundle σ A).U (idx σ A i) = stdCover σ A i :=
  rfl

variable (σ A) in
/-- The transition function `(xⱼ / xᵢ)^d` of `𝒪(d)` on `D₊(xᵢ) ∩ D₊(xⱼ)`. -/
noncomputable def transStd (d : ℤ) (i j : σ) :
    Γ(Proj (homogeneousSubmodule σ A), stdCover σ A i ⊓ stdCover σ A j) :=
  (twistingBundle σ A).trans d (idx σ A i) (idx σ A j)

/-- The transition function `(xⱼ / xᵢ)^d` of `𝒪(d)`, as a Laurent polynomial. -/
lemma sectionToLaurent_trans (d : ℤ) (i j : σ) :
    sectionToLaurent σ A _ (le_inf (torus_le_stdCover i) (torus_le_stdCover j))
        (transStd σ A d i j) = xPow A j d * xPow A i (-d) := by
  set φ := sectionToLaurent σ A _ (le_inf (torus_le_stdCover i) (torus_le_stdCover j))
  have hg : ((Units.map φ.toMonoidHom ((twistingBundle σ A).g (idx σ A i) (idx σ A j)) :
      (Laurent σ A)ˣ) : Laurent σ A) =
        AddMonoidAlgebra.single (Pi.single j 1 - Pi.single i 1) 1 := by
    change φ (Proj.fracSection _ (X_mem j) (X_mem i) _ inf_le_left) = _
    rw [sectionToLaurent_fracSection, toLaurent_X_eq, xPow, xPow,
      AddMonoidAlgebra.single_mul_single, one_mul, one_smul, neg_one_smul, sub_eq_add_neg]
  have e1 : φ (transStd σ A d i j) =
      ((Units.map φ.toMonoidHom ((twistingBundle σ A).g (idx σ A i) (idx σ A j)) ^ d :
        (Laurent σ A)ˣ) : Laurent σ A) :=
    congrArg Units.val
      (map_zpow (Units.map φ.toMonoidHom) ((twistingBundle σ A).g (idx σ A i) (idx σ A j)) d)
  rw [e1, val_zpow_of_val hg, xPow, xPow, AddMonoidAlgebra.single_mul_single, one_mul,
    smul_sub, neg_smul, sub_eq_add_neg]

/-- The `i`-th component of a section of `𝒪(d)`. -/
noncomputable def component (d : ℤ) (V : (Proj (homogeneousSubmodule σ A)).Opens) (i : σ) :
    (twistingBundle σ A).sectionsAddSubgroup d V →+ Γ(Proj (homogeneousSubmodule σ A),
      V ⊓ stdCover σ A i) :=
  (Pi.evalAddMonoidHom (fun j ↦ Γ(Proj (homogeneousSubmodule σ A),
    V ⊓ (twistingBundle σ A).U j)) (idx σ A i)).comp (AddSubgroup.subtype _)

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
lemma component_apply (d : ℤ) (V : (Proj (homogeneousSubmodule σ A)).Opens) (i : σ)
    (s : (twistingBundle σ A).sectionsAddSubgroup d V) :
    component d V i s = s.1 (idx σ A i) :=
  rfl

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
lemma component_resHom (d : ℤ) {V V' : (Proj (homogeneousSubmodule σ A)).Opens} (h : V' ≤ V)
    (i : σ) (s : (twistingBundle σ A).sectionsAddSubgroup d V) :
    component d V' i ((twistingBundle σ A).resHom d h s) =
      (Proj (homogeneousSubmodule σ A)).presheaf.map (homOfLE (inf_le_inf_right _ h :
        V' ⊓ stdCover σ A i ≤ V ⊓ stdCover σ A i)).op (component d V i s) :=
  rfl

/-- The embedding of the sections of `𝒪(d)` over an open `V` containing the torus into the
Laurent polynomials: `s ↦ xᵢ^d sᵢ` (independent of `i`, see `twistToLaurent_eq`). -/
noncomputable def twistToLaurent (d : ℤ) (V : (Proj (homogeneousSubmodule σ A)).Opens)
    (hV : torus σ A ≤ V) : (twistingBundle σ A).sectionsAddSubgroup d V →+ Laurent σ A :=
  (AddMonoidHom.mulLeft (xPow A (Classical.arbitrary σ) d)).comp
    ((sectionToLaurent σ A (V ⊓ stdCover σ A (Classical.arbitrary σ))
      (le_inf hV (torus_le_stdCover _))).toAddMonoidHom.comp (component d V _))

lemma twistToLaurent_indep (d : ℤ) {V : (Proj (homogeneousSubmodule σ A)).Opens}
    (hV : torus σ A ≤ V) (s : (twistingBundle σ A).sectionsAddSubgroup d V) (i j : σ) :
    xPow A i d * sectionToLaurent σ A (V ⊓ stdCover σ A i) (le_inf hV (torus_le_stdCover _))
        (component d V i s) =
      xPow A j d * sectionToLaurent σ A (V ⊓ stdCover σ A j) (le_inf hV (torus_le_stdCover _))
        (component d V j s) := by
  have hW : torus σ A ≤ V ⊓ (stdCover σ A i ⊓ stdCover σ A j) :=
    le_inf hV (le_inf (torus_le_stdCover i) (torus_le_stdCover j))
  have h := s.2 (idx σ A i) (idx σ A j)
  have h' : sectionToLaurent σ A _ hW ((Proj _).presheaf.map (homOfLE (le_inf inf_le_left
        (inf_le_right.trans inf_le_left) : V ⊓ (stdCover σ A i ⊓ stdCover σ A j) ≤
          V ⊓ stdCover σ A i)).op (component d V i s)) =
      sectionToLaurent σ A _ hW ((Proj _).presheaf.map (homOfLE (inf_le_right :
          V ⊓ (stdCover σ A i ⊓ stdCover σ A j) ≤ stdCover σ A i ⊓ stdCover σ A j)).op
        (transStd σ A d i j)) *
      sectionToLaurent σ A _ hW ((Proj _).presheaf.map (homOfLE (le_inf inf_le_left
        (inf_le_right.trans inf_le_right) : V ⊓ (stdCover σ A i ⊓ stdCover σ A j) ≤
          V ⊓ stdCover σ A j)).op (component d V j s)) := by
    rw [← map_mul]
    exact congrArg _ h
  rw [sectionToLaurent_map (le_inf hV (torus_le_stdCover i)) hW,
    sectionToLaurent_map (le_inf (torus_le_stdCover i) (torus_le_stdCover j)) hW,
    sectionToLaurent_map (le_inf hV (torus_le_stdCover j)) hW] at h'
  rw [h', sectionToLaurent_trans, ← mul_assoc, ← mul_assoc,
    mul_comm (xPow A i d), mul_assoc (xPow A j d), xPow_mul_xPow_neg, mul_one]

lemma twistToLaurent_eq (d : ℤ) {V : (Proj (homogeneousSubmodule σ A)).Opens}
    (hV : torus σ A ≤ V) (s : (twistingBundle σ A).sectionsAddSubgroup d V) (j : σ) :
    twistToLaurent d V hV s = xPow A j d * sectionToLaurent σ A (V ⊓ stdCover σ A j)
      (le_inf hV (torus_le_stdCover _)) (component d V j s) :=
  twistToLaurent_indep d hV s _ j

lemma twistToLaurent_resHom (d : ℤ) {V V' : (Proj (homogeneousSubmodule σ A)).Opens}
    (hV : torus σ A ≤ V) (hV' : torus σ A ≤ V') (h : V' ≤ V)
    (s : (twistingBundle σ A).sectionsAddSubgroup d V) :
    twistToLaurent d V' hV' ((twistingBundle σ A).resHom d h s) = twistToLaurent d V hV s := by
  rw [twistToLaurent_eq d hV' _ (Classical.arbitrary σ), twistToLaurent_eq d hV _
    (Classical.arbitrary σ), component_resHom, sectionToLaurent_map]

omit [Fintype σ] [Nonempty σ] in
lemma basicOpen_prodX_insert (j : σ) (I : Finset σ) :
    Proj.basicOpen (homogeneousSubmodule σ A) (prodX σ A (insert j I)) =
      Proj.basicOpen _ (prodX σ A I) ⊓ stdCover σ A j := by
  rw [basicOpen_prodX, basicOpen_prodX, Finset.iInf_insert, inf_comm]

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
lemma basicOpen_prodX_le {I : Finset σ} {j : σ} (hj : j ∈ I) :
    Proj.basicOpen (homogeneousSubmodule σ A) (prodX σ A I) ≤ stdCover σ A j := by
  rw [basicOpen_prodX]
  exact iInf₂_le j hj

lemma injective_twistToLaurent_of_eq (d : ℤ) {V : (Proj (homogeneousSubmodule σ A)).Opens}
    {I : Finset σ} (hV : V = Proj.basicOpen _ (prodX σ A I)) (hV' : torus σ A ≤ V) :
    Function.Injective (twistToLaurent d V hV') := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine Subtype.ext (funext fun j ↦ ?_)
  obtain ⟨j, rfl⟩ := idx_surjective j
  have h1 := twistToLaurent_eq d hV' s j
  rw [hs] at h1
  have h2 : sectionToLaurent σ A (V ⊓ stdCover σ A j) (le_inf hV' (torus_le_stdCover j))
      (component d V j s) = 0 := by
    rw [← one_mul (sectionToLaurent σ A _ _ _), ← xPow_mul_xPow_neg j (-d), neg_neg, mul_assoc,
      ← h1, mul_zero]
  have hVj : V ⊓ stdCover σ A j = Proj.basicOpen _ (prodX σ A (insert j I)) := by
    rw [basicOpen_prodX_insert, hV]
  exact injective_sectionToLaurent_of_eq (Finset.insert_nonempty j I) hVj _
    (h2.trans (map_zero _).symm)

variable (σ) in
/-- The exponents `μ` of the Laurent monomials `x^μ` which are sections of `𝒪(d)` over `D₊(x_I)`:
those of degree `d` with `μᵢ ≥ 0` for `i ∉ I`. -/
def monomialSetDeg (d : ℤ) (I : Finset σ) : Set (σ → ℤ) :=
  {μ | ∑ i, μ i = d ∧ ∀ i ∉ I, 0 ≤ μ i}

omit [Nonempty σ] in
lemma sum_sub_smul_single (μ : σ → ℤ) (d : ℤ) (j : σ) :
    ∑ i, (μ - d • (Pi.single j 1 : σ → ℤ)) i = ∑ i, μ i - d := by
  simp [Finset.sum_sub_distrib, Pi.single_apply]

omit [Nonempty σ] in
lemma support_xPow_mul_subset {d : ℤ} {I : Finset σ} {j : σ} (hj : j ∈ I) {ℓ : Laurent σ A}
    (hℓ : ↑ℓ.coeff.support ⊆ monomialSet I) :
    ↑(xPow A j d * ℓ).coeff.support ⊆ monomialSetDeg σ d I := by
  intro μ hμ
  rw [Finset.mem_coe, Finsupp.mem_support_iff, coeff_xPow_mul] at hμ
  have h := hℓ (Finsupp.mem_support_iff.mpr hμ)
  refine ⟨?_, fun i hi ↦ ?_⟩
  · have h0 := h.1
    rw [sum_sub_smul_single] at h0
    linarith
  · have hij : i ≠ j := fun h ↦ hi (h ▸ hj)
    simpa [Pi.single_apply, hij] using h.2 i hi

omit [Nonempty σ] in
lemma support_xPow_neg_mul_subset {d : ℤ} {I : Finset σ} {j : σ} (hj : j ∈ I)
    {ℓ : Laurent σ A} (hℓ : ↑ℓ.coeff.support ⊆ monomialSetDeg σ d I) :
    ↑(xPow A j (-d) * ℓ).coeff.support ⊆ monomialSet I := by
  intro μ hμ
  rw [Finset.mem_coe, Finsupp.mem_support_iff, coeff_xPow_mul] at hμ
  have h := hℓ (Finsupp.mem_support_iff.mpr hμ)
  refine ⟨?_, fun i hi ↦ ?_⟩
  · have h0 := h.1
    rw [sum_sub_smul_single] at h0
    linarith
  · have hij : i ≠ j := fun h ↦ hi (h ▸ hj)
    simpa [Pi.single_apply, hij] using h.2 i hi

/-- On an open `V ⊆ D₊(xⱼ)` containing the torus, the section of `𝒪(d)` whose `j`-th component
is (the restriction of) `t`. -/
noncomputable def ofComponent (d : ℤ) {V : (Proj (homogeneousSubmodule σ A)).Opens} {j : σ}
    (hVle : V ≤ stdCover σ A j) (t : Γ(Proj (homogeneousSubmodule σ A), V ⊓ stdCover σ A j)) :
    (twistingBundle σ A).sectionsAddSubgroup d V :=
  (twistingBundle σ A).ofUnit d (idx σ A j) hVle
    ((Proj (homogeneousSubmodule σ A)).presheaf.map (homOfLE (le_inf le_rfl hVle :
      V ≤ V ⊓ stdCover σ A j)).op t)

lemma twistToLaurent_ofComponent (d : ℤ) {V : (Proj (homogeneousSubmodule σ A)).Opens}
    (hV' : torus σ A ≤ V) {j : σ} (hVle : V ≤ stdCover σ A j)
    (t : Γ(Proj (homogeneousSubmodule σ A), V ⊓ stdCover σ A j)) :
    twistToLaurent d V hV' (ofComponent d hVle t) =
      xPow A j d * sectionToLaurent σ A _ (le_inf hV' (torus_le_stdCover j)) t := by
  have hc : component d V j (ofComponent d hVle t) =
      (Proj (homogeneousSubmodule σ A)).presheaf.map (homOfLE (inf_le_left :
        V ⊓ stdCover σ A j ≤ V)).op
        ((Proj (homogeneousSubmodule σ A)).presheaf.map (homOfLE (le_inf le_rfl hVle :
          V ≤ V ⊓ stdCover σ A j)).op t) :=
    (twistingBundle σ A).ofUnit_apply_self (idx σ A j) hVle _
  rw [twistToLaurent_eq d hV' _ j, hc, sectionToLaurent_map hV',
    sectionToLaurent_map (le_inf hV' (torus_le_stdCover j))]

lemma range_twistToLaurent_of_eq (d : ℤ) {V : (Proj (homogeneousSubmodule σ A)).Opens}
    {I : Finset σ} (hI : I.Nonempty) (hV : V = Proj.basicOpen _ (prodX σ A I))
    (hV' : torus σ A ≤ V) :
    Set.range (twistToLaurent d V hV') = {ℓ | ↑ℓ.coeff.support ⊆ monomialSetDeg σ d I} := by
  obtain ⟨j, hj⟩ := hI
  have hVj : V ⊓ stdCover σ A j = Proj.basicOpen _ (prodX σ A I) := by
    rw [hV]
    exact inf_eq_left.mpr (basicOpen_prodX_le hj)
  have hr := range_sectionToLaurent_of_eq ⟨j, hj⟩ hVj (le_inf hV' (torus_le_stdCover j))
  ext ℓ
  refine ⟨?_, fun hℓ ↦ ?_⟩
  · rintro ⟨s, rfl⟩
    rw [twistToLaurent_eq d hV' s j]
    exact support_xPow_mul_subset hj (hr.le ⟨_, rfl⟩)
  · obtain ⟨t, ht⟩ : xPow A j (-d) * ℓ ∈ Set.range (sectionToLaurent σ A (V ⊓ stdCover σ A j)
        (le_inf hV' (torus_le_stdCover j))) := by
      rw [hr]
      exact support_xPow_neg_mul_subset hj hℓ
    have hVle : V ≤ stdCover σ A j := by
      rw [hV]
      exact basicOpen_prodX_le hj
    refine ⟨ofComponent d hVle t, ?_⟩
    rw [twistToLaurent_ofComponent, ht, ← mul_assoc, xPow_mul_xPow_neg, one_mul]

section Global

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
lemma top_inf_stdCover (j : σ) :
    (⊤ : (Proj (homogeneousSubmodule σ A)).Opens) ⊓ stdCover σ A j =
      Proj.basicOpen _ (prodX σ A {j}) := by
  rw [top_inf_eq, stdCover_eq]

omit [Fintype σ] [Nonempty σ] in
lemma top_inf_stdCover_inf (i j : σ) :
    (⊤ : (Proj (homogeneousSubmodule σ A)).Opens) ⊓ (stdCover σ A i ⊓ stdCover σ A j) =
      Proj.basicOpen _ (prodX σ A {i, j}) := by
  rw [top_inf_eq, basicOpen_prodX_insert, ← stdCover_eq, inf_comm]

/-- Global sections of `𝒪(d)` embed into the Laurent polynomials. -/
lemma injective_twistToLaurent_top (d : ℤ) :
    Function.Injective (twistToLaurent d ⊤ (le_top : torus σ A ≤ ⊤)) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine Subtype.ext (funext fun j ↦ ?_)
  obtain ⟨j, rfl⟩ := idx_surjective j
  have h1 := twistToLaurent_eq d le_top s j
  rw [hs] at h1
  have h2 : sectionToLaurent σ A (⊤ ⊓ stdCover σ A j) (le_inf le_top (torus_le_stdCover j))
      (component d ⊤ j s) = 0 := by
    rw [← one_mul (sectionToLaurent σ A _ _ _), ← xPow_mul_xPow_neg j (-d), neg_neg, mul_assoc,
      ← h1, mul_zero]
  exact injective_sectionToLaurent_of_eq (Finset.singleton_nonempty j) (top_inf_stdCover j) _
    (h2.trans (map_zero _).symm)

/-- The image of the global sections of `𝒪(d)` in the Laurent polynomials: the span of the
monomials `x^μ` which are sections of `𝒪(d)` over every `D₊(xⱼ)`. -/
lemma range_twistToLaurent_top (d : ℤ) :
    Set.range (twistToLaurent d ⊤ (le_top : torus σ A ≤ ⊤)) =
      {ℓ | ∀ j, ↑ℓ.coeff.support ⊆ monomialSetDeg σ d {j}} := by
  have hr (j : σ) := range_sectionToLaurent_of_eq (A := A) (Finset.singleton_nonempty j)
    (top_inf_stdCover j) (le_inf le_top (torus_le_stdCover j))
  ext ℓ
  refine ⟨?_, fun hℓ ↦ ?_⟩
  · rintro ⟨s, rfl⟩ j
    rw [twistToLaurent_eq d le_top s j]
    exact support_xPow_mul_subset (Finset.mem_singleton_self j) ((hr j).le ⟨_, rfl⟩)
  · have ht (j : σ) : xPow A j (-d) * ℓ ∈ Set.range (sectionToLaurent σ A
        (⊤ ⊓ stdCover σ A j) (le_inf le_top (torus_le_stdCover j))) := by
      rw [hr j]
      exact support_xPow_neg_mul_subset (Finset.mem_singleton_self j) (hℓ j)
    choose t ht using ht
    refine ⟨⟨fun j ↦ t j.down, fun i j ↦ ?_⟩, ?_⟩
    · obtain ⟨i, rfl⟩ := idx_surjective i
      obtain ⟨j, rfl⟩ := idx_surjective j
      have hW : torus σ A ≤ ⊤ ⊓ (stdCover σ A i ⊓ stdCover σ A j) :=
        le_inf le_top (le_inf (torus_le_stdCover i) (torus_le_stdCover j))
      change (Proj _).presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          ⊤ ⊓ (stdCover σ A i ⊓ stdCover σ A j) ≤ ⊤ ⊓ stdCover σ A i)).op (t i) =
        (Proj _).presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ (stdCover σ A i ⊓ stdCover σ A j) ≤
          stdCover σ A i ⊓ stdCover σ A j)).op (transStd σ A d i j) *
        (Proj _).presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          ⊤ ⊓ (stdCover σ A i ⊓ stdCover σ A j) ≤ ⊤ ⊓ stdCover σ A j)).op (t j)
      apply injective_sectionToLaurent_of_eq (Finset.insert_nonempty i {j})
        (top_inf_stdCover_inf i j) hW
      rw [map_mul, sectionToLaurent_map (le_inf le_top (torus_le_stdCover i)),
        sectionToLaurent_map (le_inf (torus_le_stdCover i) (torus_le_stdCover j)),
        sectionToLaurent_map (le_inf le_top (torus_le_stdCover j)), ht, ht,
        sectionToLaurent_trans]
      linear_combination (-(xPow A i (-d) * ℓ)) * xPow_mul_xPow_neg (A := A) j d
    · rw [twistToLaurent_eq d le_top _ (Classical.arbitrary σ)]
      change xPow A _ d * sectionToLaurent σ A _ _ (t (Classical.arbitrary σ)) = ℓ
      rw [ht, ← mul_assoc, xPow_mul_xPow_neg, one_mul]

omit [DecidableEq σ] [Nonempty σ] in
/-- With at least two variables, the exponents allowed on every `D₊(xⱼ)` are those `≥ 0`. -/
lemma forall_mem_monomialSetDeg_singleton_iff (h : 2 ≤ Fintype.card σ) (d : ℤ) (μ : σ → ℤ) :
    (∀ j, μ ∈ monomialSetDeg σ d {j}) ↔ ∑ i, μ i = d ∧ ∀ i, 0 ≤ μ i := by
  classical
  have : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
  refine ⟨fun hμ ↦ ⟨(hμ (Classical.arbitrary σ)).1, fun i ↦ ?_⟩, fun hμ j ↦
    ⟨hμ.1, fun i _ ↦ hμ.2 i⟩⟩
  obtain ⟨j, hj⟩ : ∃ j, j ≠ i := by
    by_contra hall
    push Not at hall
    have : Fintype.card σ ≤ 1 := Fintype.card_le_one_iff.mpr fun a b ↦ (hall a).trans (hall b).symm
    omega
  exact (hμ j).2 i (by simpa [eq_comm] using hj.symm)

/-- **Global sections of `𝒪(n)`** (Stacks Project, Tag 01XT; Hartshorne II.5.13): with at least two
variables, `Γ(Proj A[xᵢ], 𝒪(n))` is the module of homogeneous polynomials of degree `n`. The map
sends a global section to the corresponding polynomial `xⱼⁿ sⱼ`. -/
theorem range_twistToLaurent_top_nat (h : 2 ≤ Fintype.card σ) (n : ℕ) :
    Set.range (twistToLaurent (n : ℤ) ⊤ (le_top : torus σ A ≤ ⊤)) =
      toLaurent σ A '' (homogeneousSubmodule σ A n : Set (MvPolynomial σ A)) := by
  rw [range_twistToLaurent_top]
  ext ℓ
  simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe]
  refine ⟨fun hℓ ↦ ?_, ?_⟩
  · have hℓ' (μ) (hμ : μ ∈ ℓ.coeff.support) : ∑ i, μ i = n ∧ ∀ i, 0 ≤ μ i :=
      (forall_mem_monomialSetDeg_singleton_iff h n μ).mp fun j ↦ hℓ j hμ
    obtain ⟨p, rfl⟩ := exists_toLaurent_eq fun μ hμ ↦ (hℓ' μ hμ).2
    refine ⟨p, (mem_homogeneousSubmodule _ _).mpr fun ν hν ↦ ?_, rfl⟩
    change Finsupp.weight (fun _ ↦ 1) ν = _
    rw [← Finsupp.degree_eq_weight_one]
    rw [← coeff_toLaurent_expHom] at hν
    have := (hℓ' _ (Finsupp.mem_support_iff.mpr hν)).1
    rw [sum_expHom] at this
    exact_mod_cast this
  · rintro ⟨p, hp, rfl⟩ j μ hμ
    by_cases hr : μ ∈ Set.range (expHom σ)
    · obtain ⟨ν, rfl⟩ := hr
      rw [Finset.mem_coe, Finsupp.mem_support_iff, coeff_toLaurent_expHom] at hμ
      refine ⟨?_, fun i _ ↦ by simp⟩
      rw [sum_expHom, degree_of_mem_support hp hμ]
    · exact absurd (coeff_toLaurent_of_notMem p hr) (Finsupp.mem_support_iff.mp hμ)

omit [DecidableEq σ] in
/-- With at least two variables, `𝒪(d)` has no non-zero global sections for `d < 0`
(Hartshorne II.5.13). -/
theorem twistToLaurent_top_eq_zero_of_neg (h : 2 ≤ Fintype.card σ) {d : ℤ} (hd : d < 0)
    (s : (twistingBundle σ A).sectionsAddSubgroup d ⊤) : s = 0 := by
  classical
  refine injective_twistToLaurent_top d ?_
  rw [map_zero]
  have hs : twistToLaurent d ⊤ le_top s ∈ Set.range (twistToLaurent d ⊤ le_top) := ⟨s, rfl⟩
  rw [range_twistToLaurent_top] at hs
  refine AddMonoidAlgebra.coeff_injective (Finsupp.ext fun μ ↦ ?_)
  by_contra hμ
  have h' := (forall_mem_monomialSetDeg_singleton_iff h d μ).mp fun j ↦
    hs j (Finsupp.mem_support_iff.mpr hμ)
  have : 0 ≤ ∑ i, μ i := Finset.sum_nonneg fun i _ ↦ h'.2 i
  omega

/-- **Global sections of `𝒪(n)`** (Hartshorne II.5.13): with at least two variables,
`Γ(Proj A[xᵢ], 𝒪(n)) ≅ A[xᵢ]ₙ`, the homogeneous polynomials of degree `n`. -/
noncomputable def twistGlobalSectionsEquiv (h : 2 ≤ Fintype.card σ) (n : ℕ) :
    (twistingBundle σ A).sectionsAddSubgroup n ⊤ ≃+ homogeneousSubmodule σ A n :=
  let g : homogeneousSubmodule σ A n →+ Laurent σ A :=
    (toLaurent σ A).toAddMonoidHom.comp (homogeneousSubmodule σ A n).subtype.toAddMonoidHom
  have hg : Function.Injective g := toLaurent_injective.comp Subtype.val_injective
  have hrange : (twistToLaurent (n : ℤ) ⊤ (le_top : torus σ A ≤ ⊤)).range = g.range := by
    refine SetLike.coe_injective ?_
    rw [AddMonoidHom.coe_range, AddMonoidHom.coe_range, range_twistToLaurent_top_nat h n]
    ext ℓ
    simp [g]
  (AddMonoidHom.ofInjective (injective_twistToLaurent_top (n : ℤ))).trans
    ((AddEquiv.addSubgroupCongr hrange).trans (AddMonoidHom.ofInjective hg).symm)

end Global

section Cech

open TopCat.Presheaf

omit [Fintype σ] [DecidableEq σ] [Nonempty σ] in
lemma mem_support_filter {f : (σ → ℤ) →₀ A} {P : (σ → ℤ) → Prop} [DecidablePred P]
    {μ : σ → ℤ} : μ ∈ (f.filter P).support ↔ μ ∈ f.support ∧ P μ := by
  rw [Finsupp.support_filter, Finset.mem_filter]

/-- The embeddings of the terms of the Čech complex of `𝒪(d)` into the Laurent polynomials. -/
noncomputable def twistCechEmbedding (d : ℤ) {m : ℕ} (x : Fin (m + 1) → σ) :
    (twist σ A d).toAbSheaf.obj.obj (op (TopCat.Presheaf.cechOpen (stdCover σ A) x)) →+
      ((σ → ℤ) →₀ A) :=
  AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom.comp (twistToLaurent d _ (torus_le_cechOpen x))

lemma range_twistCechEmbedding (d : ℤ) {m : ℕ} (x : Fin (m + 1) → σ) :
    Set.range (twistCechEmbedding (A := A) d x) =
      {f | ↑f.support ⊆ monomialSetDeg σ d (Finset.univ.image x)} := by
  have h := range_twistToLaurent_of_eq (A := A) d (image_nonempty x) (cechOpen_stdCover x)
    (torus_le_cechOpen x)
  ext f
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨s, rfl⟩
    exact (h.le ⟨s, rfl⟩ : _)
  · obtain ⟨s, hs⟩ : AddMonoidAlgebra.ofCoeff f ∈ Set.range (twistToLaurent d _
        (torus_le_cechOpen (A := A) x)) := by
      rw [h]
      exact hf
    exact ⟨s, congrArg AddMonoidAlgebra.coeff hs⟩

omit [Fintype σ] [DecidableEq σ] in
lemma nonnegIndex_spec_of_exists {μ : σ → ℤ} (h : ∃ i, 0 ≤ μ i) : 0 ≤ μ (nonnegIndex σ μ) := by
  rw [nonnegIndex, dite_eq_left h]
  exact h.choose_spec

lemma nonnegIndex_mem_deg (d : ℤ) {m : ℕ} (y : Fin (m + 1) → σ) (μ : σ → ℤ)
    (hμ : μ ∈ monomialSetDeg σ d (Finset.univ.image
      (Fin.cons (nonnegIndex σ μ) y : Fin (m + 2) → σ)) ∩ {μ | ¬ ∀ i, μ i < 0}) :
    μ ∈ monomialSetDeg σ d (Finset.univ.image y) ∩ {μ | ¬ ∀ i, μ i < 0} := by
  refine ⟨⟨hμ.1.1, fun i hi ↦ ?_⟩, hμ.2⟩
  by_cases hk : i = nonnegIndex σ μ
  · rw [hk]
    refine nonnegIndex_spec_of_exists ?_
    have := hμ.2
    push Not at this
    exact this
  · refine hμ.1.2 i fun h ↦ ?_
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
    induction a using Fin.cases with
    | zero => exact hk (by simpa using ha.symm)
    | succ a => exact hi (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, by simpa using ha⟩)

omit [DecidableEq σ] [Nonempty σ] in
/-- A monomial all of whose exponents are negative has degree at most `-#σ`. -/
lemma sum_le_of_forall_neg {μ : σ → ℤ} (h : ∀ i, μ i < 0) :
    ∑ i, μ i ≤ -(Fintype.card σ : ℤ) := by
  have : ∑ i, μ i ≤ ∑ _i : σ, (-1 : ℤ) := Finset.sum_le_sum fun i _ ↦ by linarith [h i]
  simpa using this

omit [DecidableEq σ] in
/-- The Čech complex of `𝒪(d)` for the standard cover of `Proj A[xᵢ]` is exact in degree `p + 1`
unless `p + 1 = #σ - 1` and `d ≤ -#σ` (Stacks Project, Tag 01XT). -/
theorem twist_cechComplex_exactAt (d : ℤ) (p : ℕ)
    (h : p + 2 ≠ Fintype.card σ ∨ -(Fintype.card σ : ℤ) < d) :
    (TopCat.Presheaf.cechComplex (stdCover σ A) (twist σ A d).toAbSheaf.obj).ExactAt (p + 1) := by
  classical
  refine TopCat.Presheaf.cechComplex_exactAt_of_embedding _ _ (fun x ↦ twistCechEmbedding d x)
    (fun x y h s ↦ congrArg AddMonoidAlgebra.coeff
      (twistToLaurent_resHom d (torus_le_cechOpen y) (torus_le_cechOpen x) h s))
    (fun x ↦ AddMonoidAlgebra.coeffAddEquiv.injective.comp
      (injective_twistToLaurent_of_eq d (cechOpen_stdCover x) (torus_le_cechOpen x)))
    p fun c hc hdc ↦ ?_
  simp only [range_twistCechEmbedding] at hc ⊢
  -- split `c` into the monomials with all exponents negative and the others
  let P : (σ → ℤ) → Prop := fun μ ↦ ∀ i, μ i < 0
  have hfilter (Q : (σ → ℤ) → Prop) [DecidablePred Q] :
      cechDConst (p + 1) (fun x ↦ (c x).filter Q) = 0 := by
    rw [show (fun x ↦ (c x).filter Q) = fun x ↦ Finsupp.filterAddHom Q (c x) from rfl,
      cechDConst_map, hdc]
    funext x
    simp
  -- the part with a non-negative exponent: cone construction
  obtain ⟨br, hbr, hdbr⟩ := TopCat.Presheaf.exists_cechDConst_eq_of_support
    (fun x ↦ monomialSetDeg σ d (Finset.univ.image x) ∩ {μ | ¬ ∀ i, μ i < 0}) (nonnegIndex σ)
    (nonnegIndex_mem_deg d) (fun x ↦ (c x).filter fun μ ↦ ¬ P μ)
    (fun x μ hμ ↦ ⟨hc x (mem_support_filter.mp hμ).1, (mem_support_filter.mp hμ).2⟩)
    (hfilter _)
  -- the part with all exponents negative
  obtain ⟨bn, hbn, hdbn⟩ : ∃ bn : (Fin (p + 1) → σ) → ((σ → ℤ) →₀ A),
      (∀ y, ↑(bn y).support ⊆ monomialSetDeg σ d (Finset.univ.image y)) ∧
        cechDConst p bn = fun x ↦ (c x).filter P := by
    by_cases hzero : ∀ x, (c x).filter P = 0
    · refine ⟨0, fun y μ hμ ↦ by simp at hμ, ?_⟩
      funext x
      rw [hzero x]
      simp [cechDConst]
    push Not at hzero
    obtain ⟨x₀, hx₀⟩ := hzero
    obtain ⟨μ₀, hμ₀⟩ := Finsupp.support_nonempty_iff.mpr hx₀
    have hμ₀P := (mem_support_filter.mp hμ₀).2
    have hμ₀c := hc x₀ (mem_support_filter.mp hμ₀).1
    have hcard : Fintype.card σ ≤ p + 1 := by
      rcases h with h | h
      · by_contra hlt
        have hlt : p + 2 < Fintype.card σ := by omega
        obtain ⟨i, hi⟩ : ∃ i, i ∉ Finset.univ.image x₀ := by
          by_contra hall
          push Not at hall
          have := Finset.card_le_card (fun i _ ↦ hall i : Finset.univ ⊆ Finset.univ.image x₀)
          have := Finset.card_image_le (s := Finset.univ) (f := x₀)
          simp only [Finset.card_univ, Fintype.card_fin] at *
          omega
        exact absurd (hμ₀P i) (not_lt.mpr (hμ₀c.2 i hi))
      · have := sum_le_of_forall_neg hμ₀P
        rw [hμ₀c.1] at this
        omega
    let G := (Finsupp.supported A ℤ {μ : σ → ℤ | ∑ i, μ i = d}).toAddSubgroup
    let cn : (Fin (p + 2) → σ) → G := fun x ↦ ⟨(c x).filter P, by
      rw [Submodule.mem_toAddSubgroup, Finsupp.mem_supported]
      exact fun μ hμ ↦ (hc x (mem_support_filter.mp hμ).1).1⟩
    have hcn : ∀ x, ¬ Function.Surjective x → cn x = 0 := by
      intro x hx
      refine Subtype.ext (Finsupp.ext fun μ ↦ ?_)
      rw [Finsupp.filter_apply]
      split_ifs with hP
      · refine Finsupp.notMem_support_iff.mp fun hμ ↦ hx fun i ↦ ?_
        by_contra hi
        push Not at hi
        exact absurd (hP i) (not_lt.mpr ((hc x hμ).2 i (by simpa [eq_comm] using hi)))
      · rfl
    have hdcn : cechDConst (p + 1) cn = 0 := by
      funext x
      refine Subtype.ext ?_
      have := congrFun (cechDConst_map G.subtype (p + 1) cn) x
      simp only [AddSubgroup.coe_subtype] at this
      rw [← this]
      exact congrFun (hfilter P) x
    obtain ⟨b', hb's, hdb'⟩ := TopCat.Presheaf.exists_cechDConst_eq_of_surjective
      (Fintype.card σ) rfl hcard cn hcn hdcn
    refine ⟨fun y ↦ (b' y : (σ → ℤ) →₀ A), fun y μ hμ ↦ ?_, ?_⟩
    · by_cases hy : Function.Surjective y
      · have hG := (b' y).2
        rw [Submodule.mem_toAddSubgroup, Finsupp.mem_supported] at hG
        refine ⟨hG hμ, fun i hi ↦ absurd ?_ hi⟩
        obtain ⟨a, rfl⟩ := hy i
        exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
      · have h0 : ((b' y : G) : (σ → ℤ) →₀ A) = 0 := by rw [hb's y hy]; rfl
        simp only [h0] at hμ
        simp at hμ
    · have := cechDConst_map G.subtype p b'
      simp only [AddSubgroup.coe_subtype] at this
      rw [this, hdb']
  refine ⟨bn + br, fun y μ hμ ↦ ?_, ?_⟩
  · rcases Finset.mem_union.mp (Finsupp.support_add hμ) with hμ | hμ
    · exact hbn y hμ
    · exact (hbr y hμ).1
  · rw [cechDConst_add, hdbn, hdbr]
    funext x
    exact Finsupp.filter_add_filter_not (c x) P

end Cech

end AlgebraicGeometry.projectiveSpace

namespace AlgebraicGeometry.projectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A]

/-- **Cohomology of `𝒪(d)` on projective space** (Stacks Project, Tag 01XT; EGA III 2.1.12;
Hartshorne III.5.1): on `ℙʳ_A = Proj A[x₀, …, x_r]`, `Hᵖ(ℙʳ_A, 𝒪(d)) = 0` for `0 < p < r` and
`p > r`, and also for `p = r` when `d > -r - 1`. (Stacks and Hartshorne moreover compute
`H⁰` and `Hʳ`.) -/
theorem H_twist_subsingleton (r p : ℕ) (d : ℤ) (h : p + 1 ≠ r ∨ -((r : ℤ) + 1) < d) :
    Subsingleton ((twist (Fin (r + 1)) A d).H (p + 1)) := by
  have hF {m : ℕ} (x : Fin (m + 1) → Fin (r + 1)) (q : ℕ) :
      Subsingleton ((twist (Fin (r + 1)) A d).toAbSheaf.H' (q + 1)
        (TopCat.Presheaf.cechOpen (stdCover (Fin (r + 1)) A) x)) :=
    (twist _ A d).H'_subsingleton_of_isAffineOpen (by
      rw [cechOpen_stdCover]
      exact Proj.isAffineOpen_basicOpen _ _ (prodX_mem _) (image_nonempty x).card_pos) q
  have hexact := twist_cechComplex_exactAt (σ := Fin (r + 1)) (A := A) d p (by
    rw [Fintype.card_fin]
    rcases h with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by push_cast; linarith))
  have h' := (TopCat.Sheaf.cechComplex_exactAt_iff_subsingleton_H' (X := (Proj _).carrier)
    (stdCover (Fin (r + 1)) A) p _ hF).mp hexact
  rw [iSup_stdCover] at h'
  exact h'

/-- `H⁰(ℙʳ_A, 𝒪(n)) ≅ A[x₀, …, x_r]ₙ` for `r ≥ 1` (Stacks Project, Tag 01XT; Hartshorne
III.5.1 (a)). -/
noncomputable def H_zero_twist_equiv (r : ℕ) (hr : 1 ≤ r) (n : ℕ) :
    (twist (Fin (r + 1)) A n).H 0 ≃+ homogeneousSubmodule (Fin (r + 1)) A n :=
  (Scheme.Modules.H.equiv₀ _).toAddEquiv.trans
    (twistGlobalSectionsEquiv (by rw [Fintype.card_fin]; omega) n)

/-- `H⁰(ℙʳ_A, 𝒪(d)) = 0` for `d < 0` and `r ≥ 1` (Stacks Project, Tag 01XT; Hartshorne
III.5.1 (a)). -/
theorem H_zero_twist_subsingleton_of_neg (r : ℕ) (hr : 1 ≤ r) {d : ℤ} (hd : d < 0) :
    Subsingleton ((twist (Fin (r + 1)) A d).H 0) := by
  refine ⟨fun a b ↦ (Scheme.Modules.H.equiv₀ _).injective ?_⟩
  rw [twistToLaurent_top_eq_zero_of_neg (by rw [Fintype.card_fin]; omega) hd
      ((Scheme.Modules.H.equiv₀ _) a),
    twistToLaurent_top_eq_zero_of_neg (by rw [Fintype.card_fin]; omega) hd
      ((Scheme.Modules.H.equiv₀ _) b)]

end AlgebraicGeometry.projectiveSpace
