/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import SGA.Foundations.Projective.SectionExtension

/-!
# The graded ring of sections of the powers of a line bundle

For a line bundle `L` on a scheme `X`, the sections of the powers `L^{⊗n}` form a graded ring
`Γ_*(L) = ⊕ₙ Γ(X, L^{⊗n})` (EGA 0_I 5.4.6, EGA II 3.3.1). We realize it as the external direct
sum of the submodules `Scheme.LineBundle.sectionSubmodule L R n` of the ring
`L.Fam ⊤ = ∏ᵢ Γ(Uᵢ, 𝒪_X)`, graded by the images of the summands (`DirectSum.lofGrading`).

## Main definitions and results

- `DirectSum.lofGrading`: the grading of an external direct sum `⊕ₙ Mₙ` of a graded family of
  submodules of an algebra, and its `GradedAlgebra` instance.
- `Scheme.LineBundle.sectionRing L R`: the graded `R`-algebra `Γ_*(L)`, for an `R`-algebra
  structure on `Γ(X, 𝒪_X)`; `Scheme.LineBundle.sectionGrading L R` is its grading.
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace DirectSum

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (M : ℕ → Submodule R B)
  [SetLike.GradedMonoid M]

/-- The `AddSubgroupClass` instance for submodules of `⊕ₙ Mₙ`; instance search does not find it
because the additive monoid structure of `⊕ₙ Mₙ` is not a projection of its group structure. -/
instance (priority := 100) addSubgroupClass_submodule :
    AddSubgroupClass (Submodule R (⨁ n, M n)) (⨁ n, M n) :=
  @Submodule.addSubgroupClass R (⨁ n, M n) _ _ _

/-- The grading of the external direct sum `⊕ₙ Mₙ` by the images of the summands. -/
def lofGrading (n : ℕ) : Submodule R (⨁ n, M n) :=
  LinearMap.range (DirectSum.lof R ℕ (fun n ↦ M n) n)

omit [SetLike.GradedMonoid M] in
lemma of_mem_lofGrading (n : ℕ) (x : M n) : DirectSum.of (fun n ↦ M n) n x ∈ lofGrading M n :=
  ⟨x, rfl⟩

instance : SetLike.GradedMonoid (lofGrading M) where
  one_mem := ⟨⟨1, SetLike.one_mem_graded M⟩, rfl⟩
  mul_mem := by
    rintro i j _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨⟨a * b, SetLike.GradedMul.mul_mem a.2 b.2⟩,
      (DirectSum.of_mul_of (A := fun n ↦ M n) a b).symm⟩

/-- The decomposition of `⊕ₙ Mₙ` along `lofGrading`. -/
noncomputable def lofDecompose : (⨁ n, M n) →+ ⨁ n, lofGrading M n :=
  DirectSum.toAddMonoid fun n ↦ (DirectSum.of (fun n ↦ lofGrading M n) n).comp
    (LinearMap.rangeRestrict (DirectSum.lof R ℕ (fun n ↦ M n) n)).toAddMonoidHom

lemma lofDecompose_of (n : ℕ) (x : M n) :
    lofDecompose M (DirectSum.of (fun n ↦ M n) n x) =
      DirectSum.of (fun n ↦ lofGrading M n) n ⟨_, of_mem_lofGrading M n x⟩ := by
  simp only [lofDecompose, DirectSum.toAddMonoid_of]
  rfl

noncomputable instance : GradedAlgebra (lofGrading M) where
  decompose' := lofDecompose M
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of n x =>
      rw [lofDecompose_of, DirectSum.coeAddMonoidHom_of]
    | add x y hx hy => simp only [map_add, hx, hy]
  right_inv y := by
    induction y using DirectSum.induction_on with
    | zero => simp
    | of n y =>
      obtain ⟨_, x, rfl⟩ := y
      rw [DirectSum.coeAddMonoidHom_of]
      exact lofDecompose_of M n x
    | add x y hx hy => simp only [map_add, hx, hy]

lemma decompose_of (n : ℕ) (x : M n) :
    DirectSum.decompose (lofGrading M) (DirectSum.of (fun n ↦ M n) n x) =
      DirectSum.of (fun n ↦ lofGrading M n) n ⟨_, of_mem_lofGrading M n x⟩ :=
  lofDecompose_of M n x

omit [SetLike.GradedMonoid M] in
lemma mem_lofGrading_iff {n : ℕ} {a : ⨁ n, M n} :
    a ∈ lofGrading M n ↔ ∃ x : M n, DirectSum.of (fun n ↦ M n) n x = a :=
  Iff.rfl

end DirectSum

namespace AlgebraicGeometry.Scheme.LineBundle

open DirectSum

variable {X : Scheme.{u}} (L : X.LineBundle) (R : Type u) [CommRing R] [Algebra R Γ(X, ⊤)]

/-- A ring `R` acting on `Γ(X, 𝒪_X)` acts on families of sections of `𝒪_X` over the opens
`V ∩ Uᵢ`. -/
noncomputable instance famAlgebra (V : X.Opens) : Algebra R (L.Fam V) :=
  ((L.famConst V).comp ((X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp
    (algebraMap R Γ(X, ⊤)))).toAlgebra

lemma algebraMap_fam (V : X.Opens) (r : R) :
    algebraMap R (L.Fam V) r =
      L.famConst V (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (algebraMap R Γ(X, ⊤) r)) :=
  rfl

lemma isSection_algebraMap (V : X.Opens) (r : R) : L.IsSection 0 V (algebraMap R (L.Fam V) r) :=
  isSection_famConst (L := L) _

/-- The sections of `L^{⊗n}` over `V`, as an `R`-submodule of `L.Fam V`. -/
def sectionSubmoduleOn (n : ℤ) (V : X.Opens) : Submodule R (L.Fam V) where
  carrier := {s | L.IsSection n V s}
  add_mem' hs ht := (L.sectionsAddSubgroup n V).add_mem hs ht
  zero_mem' := isSection_zero _
  smul_mem' r s hs := by
    rw [Set.mem_ofPred_eq, Algebra.smul_def]
    exact ((L.isSection_algebraMap R V r).mul hs).of_eq (zero_add _)

variable {L R} in
lemma mem_sectionSubmoduleOn {n : ℤ} {V : X.Opens} {s : L.Fam V} :
    s ∈ L.sectionSubmoduleOn R n V ↔ L.IsSection n V s :=
  Iff.rfl

/-- The sections of `L^{⊗n}` over `X`, as an `R`-submodule of `L.Fam ⊤`. -/
def sectionSubmodule (n : ℕ) : Submodule R (L.Fam ⊤) :=
  L.sectionSubmoduleOn R n ⊤

variable {L R} in
lemma mem_sectionSubmodule {n : ℕ} {s : L.Fam ⊤} :
    s ∈ L.sectionSubmodule R n ↔ L.IsSection n ⊤ s :=
  Iff.rfl

instance : SetLike.GradedMonoid (L.sectionSubmodule R) where
  one_mem := by
    rw [mem_sectionSubmodule, ← map_one (L.famConst ⊤)]
    exact isSection_famConst (L := L) _
  mul_mem i j s t hs ht := by
    rw [mem_sectionSubmodule] at hs ht ⊢
    exact (hs.mul ht).of_eq (by push_cast; ring)

/-- The graded `R`-algebra `Γ_*(L) = ⊕ₙ Γ(X, L^{⊗n})` of sections of the powers of `L`
(EGA 0_I 5.4.6). -/
abbrev sectionRing : Type u :=
  ⨁ n, L.sectionSubmodule R n

/-- The semiring structure of `Γ_*(L)` underlying its commutative ring structure. Declared with
high priority so that graded ring homomorphisms between section rings have the same instances as
the ones expected by `HomogeneousLocalization` and `Proj` (which assume commutative rings). -/
noncomputable instance (priority := 10000) sectionRing.instSemiring :
    Semiring (L.sectionRing R) :=
  (inferInstance : CommRing (L.sectionRing R)).toCommSemiring.toSemiring

/-- The grading of `Γ_*(L)`. -/
noncomputable abbrev sectionGrading : ℕ → Submodule R (L.sectionRing R) :=
  DirectSum.lofGrading (L.sectionSubmodule R)

/-- The ring homomorphism `Γ_*(L) → L.Fam ⊤` summing the homogeneous components. -/
noncomputable def coeFam : L.sectionRing R →ₐ[R] L.Fam ⊤ :=
  DirectSum.coeAlgHom (L.sectionSubmodule R)

variable {L R}

@[simp]
lemma coeFam_of (n : ℕ) (x : L.sectionSubmodule R n) :
    L.coeFam R (DirectSum.of (fun n ↦ L.sectionSubmodule R n) n x) = x :=
  DirectSum.coeAlgHom_of _ _ _

lemma isSection_coeFam {n : ℕ} {a : L.sectionRing R} (ha : a ∈ L.sectionGrading R n) :
    L.IsSection n ⊤ (L.coeFam R a) := by
  obtain ⟨x, rfl⟩ := ha
  change L.IsSection n ⊤ (L.coeFam R (DirectSum.of (fun n ↦ L.sectionSubmodule R n) n x))
  rw [coeFam_of]
  exact x.2

lemma eq_zero_of_coeFam_eq_zero {n : ℕ} {a : L.sectionRing R} (ha : a ∈ L.sectionGrading R n)
    (h : L.coeFam R a = 0) : a = 0 := by
  obtain ⟨x, rfl⟩ := ha
  change DirectSum.of (fun n ↦ L.sectionSubmodule R n) n x = 0
  change L.coeFam R (DirectSum.of (fun n ↦ L.sectionSubmodule R n) n x) = 0 at h
  rw [coeFam_of] at h
  rw [show x = 0 from Subtype.ext h, map_zero]

/-- The element of `Γ_*(L)` defined by a section of `L^{⊗n}`. -/
noncomputable def ofIsSection {n : ℕ} (s : L.Fam ⊤) (hs : L.IsSection n ⊤ s) : L.sectionRing R :=
  DirectSum.of (fun n ↦ L.sectionSubmodule R n) n ⟨s, hs⟩

lemma ofIsSection_mem {n : ℕ} (s : L.Fam ⊤) (hs : L.IsSection n ⊤ s) :
    L.ofIsSection (R := R) s hs ∈ L.sectionGrading R n :=
  DirectSum.of_mem_lofGrading _ n _

@[simp]
lemma coeFam_ofIsSection {n : ℕ} (s : L.Fam ⊤) (hs : L.IsSection n ⊤ s) :
    L.coeFam R (L.ofIsSection s hs) = s :=
  coeFam_of _ _

section Units

variable {V : X.Opens}

/-- A section is invertible on its non-vanishing locus. -/
lemma isUnit_famRes_famLocus {n : ℤ} {s : L.Fam V} (hs : L.IsSection n V s) :
    IsUnit (L.famRes (famLocus_le s) s) := by
  rw [Pi.isUnit_iff]
  intro i
  have h1 : L.famLocus V s ⊓ L.U i ≤ X.basicOpen (s i) := (famLocus_inf_U hs i).le
  have e : L.famRes (famLocus_le s) s i = X.presheaf.map (homOfLE h1).op
      (X.presheaf.map (homOfLE (X.basicOpen_le (s i))).op (s i)) := by
    rw [CohomologyAux.presheaf_map_map]
    rfl
  rw [e]
  exact (X.toRingedSpace.isUnit_res_basicOpen (s i)).map _

/-- If `u` is an invertible section of `L^{⊗e}` and `u y` is a section of `L^{⊗e}`, then `y` is a
section of `𝒪_X`. -/
lemma IsSection.of_isUnit_mul {e : ℤ} {u y : L.Fam V} (hu : L.IsSection e V u) (hu' : IsUnit u)
    (huy : L.IsSection e V (u * y)) : L.IsSection 0 V y := by
  intro i j
  have ha : IsUnit (X.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
      V ⊓ (L.U i ⊓ L.U j) ≤ V ⊓ L.U i)).op (u i)) := ((Pi.isUnit_iff.mp hu') i).map _
  have h := huy i j
  simp only [Pi.mul_apply, map_mul] at h
  rw [← mul_assoc, ← hu i j] at h
  rw [trans_zero, map_one, one_mul]
  exact ha.mul_left_cancel h

end Units

section Zero

variable (L) in
/-- The sections of `𝒪_X = L^{⊗0}` over `V`, as a subring of `L.Fam V`. -/
def sectionsZero (V : X.Opens) : Subring (L.Fam V) where
  carrier := {u | L.IsSection 0 V u}
  mul_mem' hu hv := (hu.mul hv).of_eq (add_zero 0)
  one_mem' := by
    rw [Set.mem_ofPred_eq, ← map_one (L.famConst V)]
    exact isSection_famConst (L := L) _
  add_mem' hu hv := (L.sectionsAddSubgroup 0 V).add_mem hu hv
  zero_mem' := isSection_zero 0
  neg_mem' hu := (L.sectionsAddSubgroup 0 V).neg_mem hu

lemma famConst_injective (V : X.Opens) : Function.Injective (L.famConst V) := by
  intro r r' h
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun i ↦ V ⊓ L.U i) V
    (fun i ↦ homOfLE inf_le_left) ?_ _ _ fun i ↦ congrFun h i
  rw [← inf_iSup_eq, L.iSup_eq_top, inf_top_eq]

lemma exists_famConst_eq {V : X.Opens} {u : L.Fam V} (hu : L.IsSection 0 V u) :
    ∃ r, L.famConst V r = u := by
  obtain ⟨r, hr, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun i ↦ V ⊓ L.U i) V
    (fun i ↦ homOfLE inf_le_left) (by rw [← inf_iSup_eq, L.iSup_eq_top, inf_top_eq]) u
    fun i j ↦ by
      have h := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) :
          (V ⊓ L.U i) ⊓ (V ⊓ L.U j) ≤ V ⊓ (L.U i ⊓ L.U j))).op) (hu i j)
      simp only [trans_zero, map_one, one_mul, CohomologyAux.presheaf_map_map] at h
      exact h
  exact ⟨r, funext hr⟩

variable (L) in
/-- Functions on `V` are the sections of `𝒪_X = L^{⊗0}` over `V`. -/
noncomputable def famConstEquiv (V : X.Opens) : Γ(X, V) ≃+* L.sectionsZero V :=
  RingEquiv.ofBijective ((L.famConst V).codRestrict _ fun r ↦ isSection_famConst (L := L) r)
    ⟨fun _ _ h ↦ famConst_injective V (congrArg Subtype.val h),
      fun u ↦ (exists_famConst_eq u.2).imp fun _ h ↦ Subtype.ext h⟩

@[simp]
lemma famConst_famConstEquiv_symm (V : X.Opens) (u : L.sectionsZero V) :
    L.famConst V ((L.famConstEquiv V).symm u) = u :=
  congrArg Subtype.val ((L.famConstEquiv V).apply_symm_apply u)

end Zero

section Away

open HomogeneousLocalization

variable {d : ℕ} {s : L.sectionRing R} (hs : s ∈ L.sectionGrading R d)

variable (L R) in
/-- The ring homomorphism `Γ_*(L) → L.Fam X_s` to families over the non-vanishing locus of
`s`. -/
noncomputable def toFamLocus (s : L.sectionRing R) :
    L.sectionRing R →+* L.Fam (L.famLocus ⊤ (L.coeFam R s)) :=
  (L.famRes (famLocus_le (L.coeFam R s))).comp (L.coeFam R).toRingHom

lemma toFamLocus_apply (a : L.sectionRing R) :
    L.toFamLocus R s a = L.famRes (famLocus_le (L.coeFam R s)) (L.coeFam R a) :=
  rfl

include hs in
lemma isUnit_toFamLocus : IsUnit (L.toFamLocus R s s) :=
  isUnit_famRes_famLocus (isSection_coeFam hs)

/-- The ring homomorphism `Γ_*(L)_(s) → L.Fam X_s`, `a / sⁿ ↦ a sⁿ⁻¹`. -/
noncomputable def awayToFam :
    Away (L.sectionGrading R) s →+* L.Fam (L.famLocus ⊤ (L.coeFam R s)) :=
  (IsLocalization.Away.lift s (isUnit_toFamLocus hs)).comp
    (algebraMap (Away (L.sectionGrading R) s) (Localization.Away s))

lemma toFamLocus_pow_mul_awayToFam (n : ℕ) (a : L.sectionRing R)
    (ha : a ∈ L.sectionGrading R (n • d)) :
    L.toFamLocus R s s ^ n * L.awayToFam hs (Away.mk _ hs n a ha) = L.toFamLocus R s a := by
  simp only [awayToFam, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.mk_eq_mk']
  rw [← map_pow, ← IsLocalization.Away.lift_eq (S := Localization.Away s) s
    (isUnit_toFamLocus hs) (s ^ n), ← map_mul, IsLocalization.mk'_spec'_mk,
    IsLocalization.Away.lift_eq]

lemma awayToFam_mk_eq_iff (n : ℕ) (a : L.sectionRing R) (ha : a ∈ L.sectionGrading R (n • d))
    (v : L.Fam (L.famLocus ⊤ (L.coeFam R s))) :
    L.awayToFam hs (Away.mk _ hs n a ha) = v ↔
      L.famRes (famLocus_le _) (L.coeFam R a) =
        L.famRes (famLocus_le _) (L.coeFam R s) ^ n * v := by
  simp only [awayToFam, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk, Localization.mk_eq_mk']
  unfold IsLocalization.Away.lift
  rw [IsLocalization.lift_mk'_spec, map_pow]
  rfl

lemma isSection_awayToFam (x : Away (L.sectionGrading R) s) :
    L.IsSection 0 _ (L.awayToFam hs x) := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ hs x
  have hsd := (isSection_coeFam hs).famRes (famLocus_le (L.coeFam R s))
  refine (hsd.pow n).of_isUnit_mul ((isUnit_toFamLocus hs).pow n) ?_
  have e := toFamLocus_pow_mul_awayToFam hs n a ha
  rw [toFamLocus_apply, toFamLocus_apply] at e
  rw [e]
  exact ((isSection_coeFam ha).famRes (famLocus_le _)).of_eq (by push_cast [smul_eq_mul]; ring)

/-- The ring homomorphism `Γ_*(L)_(s) → Γ(X_s, 𝒪_X)`, `a / sⁿ ↦ a / sⁿ` (EGA 0_I 5.5.4,
EGA II 3.3.1). -/
noncomputable def awayToSections :
    Away (L.sectionGrading R) s →+* Γ(X, L.famLocus ⊤ (L.coeFam R s)) :=
  (L.famConstEquiv _).symm.toRingHom.comp
    ((L.awayToFam hs).codRestrict _ (L.isSection_awayToFam hs))

@[simp]
lemma famConst_awayToSections (x : Away (L.sectionGrading R) s) :
    L.famConst _ (L.awayToSections hs x) = L.awayToFam hs x :=
  L.famConst_famConstEquiv_symm _ ⟨_, L.isSection_awayToFam hs x⟩

/-- EGA I 9.3.2 for the powers of a line bundle: if `X` is quasi-compact and quasi-separated,
then `Γ(X_s, 𝒪_X) = Γ_*(L)_(s)`. -/
theorem awayToSections_bijective [CompactSpace X] [QuasiSeparatedSpace X] :
    Function.Bijective (L.awayToSections hs) := by
  have hs' := isSection_coeFam hs
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun φ ↦ ?_⟩
  · obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ hs x
    have h0 : L.toFamLocus R s a = 0 := by
      rw [← toFamLocus_pow_mul_awayToFam hs n a ha, ← famConst_awayToSections, hx, map_zero,
        mul_zero]
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero (U := ⊤) isCompact_univ hs'
      (isSection_coeFam ha) h0
    have hm' : s ^ m * a = 0 := by
      refine eq_zero_of_coeFam_eq_zero (n := m • d + n • d)
        (SetLike.mul_mem_graded (SetLike.pow_mem_graded m hs) ha) ?_
      rw [map_mul, map_pow]
      exact hm
    ext
    rw [Away.val_mk, val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨s ^ m, m, rfl⟩, hm'⟩
  · obtain ⟨k, y, hy, hyr⟩ := exists_isSection_famRes_eq (U := ⊤) isCompact_univ
      isQuasiSeparated_univ hs' (isSection_famConst (L := L) φ)
    have hy' : L.IsSection ((k * d : ℕ) : ℤ) ⊤ y := hy.of_eq (by push_cast; ring)
    have ha : L.ofIsSection y hy' ∈ L.sectionGrading R (k • d) := by
      rw [smul_eq_mul]
      exact ofIsSection_mem y hy'
    refine ⟨Away.mk _ hs k (L.ofIsSection y hy') ha, ?_⟩
    apply famConst_injective
    rw [famConst_awayToSections, awayToFam_mk_eq_iff]
    simp only [coeFam_ofIsSection, hyr]

end Away

end AlgebraicGeometry.Scheme.LineBundle
