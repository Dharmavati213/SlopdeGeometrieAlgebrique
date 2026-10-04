/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import SGA.Foundations.Picard.Seesaw
import SGA.SGA1.ExposeXI.AbelianVarietyCube

/-!
# SGA 1, Exposé XI.2: the cube relation on an abelian variety from the openness step

The theorem of the cube for an abelian variety `A` (in the form `CubeRelation A`, Mumford,
*Abelian varieties*, §6, Corollary 2) is reduced here to its infinitesimal-and-formal part,
`AlgebraicGeometry.CubeOpennessStatement` (the hypothesis `hO`), using the group structure of `A`
instead of the semicontinuity and the curves of Mumford's proof:

* for a class `c ∈ Pic A`, let `M ∈ Pic (A × A × A)` be the class of
  `m₁₂₃^* c ⊗ m₁₂^* c⁻¹ ⊗ m₁₃^* c⁻¹ ⊗ m₂₃^* c⁻¹ ⊗ p₁^* c ⊗ p₂^* c ⊗ p₃^* c`, and `M_z` its
  restriction to `A × A × {z}` (`fiberClass`). The set `S` of rational points `z` with `M_z`
  trivial is a subgroup (`one_mem_fiberSet`, `mul_mem_fiberSet`, `inv_mem_fiberSet`):
  `M_z = Λ(t_z^* c ⊗ c⁻¹)` (`fiberClass_eq`) with
  `Λ(d) = m^* d ⊗ p₁^* d⁻¹ ⊗ p₂^* d⁻¹`, the kernel of `Λ` consists of translation invariant
  classes, and `z ↦ t_z^* c ⊗ c⁻¹` is a crossed homomorphism;
* by `hO` at the origin, `S` contains the rational points of a neighbourhood of `0`, hence all
  rational points (inside the proof of `cubeRelation_of_cubeOpenness`);
* by `hO` at every rational point and the gluing lemma
  `Scheme.LineBundle.class_eq_one_of_forall_trivial`, `M` is trivial
  (`cubeRelation_of_cubeOpenness`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace SGA.SGA1.ExposeXI

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

section Algebra

variable (c : A.left.Pic) {T : Over (Spec (.of k))}

omit [GrpObj A] in
/-- The inverse image along a morphism factoring through the base point is trivial. -/
lemma picPullback_toUnit_comp (z : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    picPullback A c (toUnit T ≫ z) = 1 := by
  rw [← pullback_picPullback, Subsingleton.elim (picPullback A c z) 1, map_one]

/-- The class `M_z = Λ(t_z^* c ⊗ c⁻¹)` on `A × A`, in terms of the cube class. -/
noncomputable def fiberClass (z : 𝟙_ (Over (Spec (.of k))) ⟶ A) : (A ⊗ A).left.Pic :=
  cubeClass c (fst A A) (snd A A) (toUnit (A ⊗ A) ≫ z)

variable (A) in
/-- Translation by a rational point `z`, `x ↦ x z`. -/
noncomputable def transl (z : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A ⟶ A := 𝟙 A * (toUnit A ≫ z)

lemma comp_transl (φ : T ⟶ A) (z : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    φ ≫ transl A z = φ * (toUnit T ≫ z) := by
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (φ ≫ toUnit A)]

lemma transl_one : transl A (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A) = 𝟙 A := by
  rw [transl, comp_one, _root_.mul_one]

lemma transl_mul (z w : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    transl A (z * w) = transl A z ≫ transl A w := by
  rw [comp_transl]
  simp only [transl, comp_mul, _root_.mul_assoc]

/-- The class `t_z^* c ⊗ c⁻¹`. -/
noncomputable def translDiff (z : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A.left.Pic :=
  picPullback A c (transl A z) * c⁻¹

lemma picPullback_translDiff (z : 𝟙_ (Over (Spec (.of k))) ⟶ A) (φ : T ⟶ A) :
    picPullback A (translDiff c z) φ =
      picPullback A c (φ * (toUnit T ≫ z)) * (picPullback A c φ)⁻¹ := by
  change Scheme.Pic.pullback φ.left (picPullback A c (transl A z) * c⁻¹) = _
  rw [map_mul, map_inv, pullback_picPullback, comp_transl]
  rfl

variable (A) in
/-- `Λ(d) = m^* d ⊗ p₁^* d⁻¹ ⊗ p₂^* d⁻¹` on `A × A`. -/
noncomputable def lambdaHom : A.left.Pic →* (A ⊗ A).left.Pic where
  toFun d := picPullback A d (fst A A * snd A A) * (picPullback A d (fst A A))⁻¹ *
    (picPullback A d (snd A A))⁻¹
  map_one' := by simp [picPullback]
  map_mul' d d' := by
    simp only [picPullback, map_mul, mul_inv]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

lemma fiberClass_eq (z : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    fiberClass c z = lambdaHom A (translDiff c z) := by
  simp only [fiberClass, cubeClass, lambdaHom, MonoidHom.coe_mk, OneHom.coe_mk,
    picPullback_translDiff, picPullback_toUnit_comp, _root_.mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/-- Classes in the kernel of `Λ` are translation invariant. -/
lemma pullback_transl_of_lambdaHom_eq_one {d : A.left.Pic} (hd : lambdaHom A d = 1)
    (w : 𝟙_ (Over (Spec (.of k))) ⟶ A) : picPullback A d (transl A w) = d := by
  have := congrArg (Scheme.Pic.pullback (lift (𝟙 A) (toUnit A ≫ w)).left) hd
  simp only [lambdaHom, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_inv, map_one,
    pullback_picPullback, comp_mul, lift_fst, lift_snd, picPullback_toUnit_comp, inv_one,
    _root_.mul_one] at this
  rw [← transl] at this
  have hid : picPullback A d (𝟙 A) = d := by
    rw [picPullback, Over.id_left, Scheme.Pic.pullback_id, MonoidHom.id_apply]
  rw [hid, mul_inv_eq_one] at this
  exact this

lemma translDiff_mul (z w : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    translDiff c (z * w) = picPullback A (translDiff c w) (transl A z) * translDiff c z := by
  rw [picPullback_translDiff, ← comp_transl, translDiff, translDiff, transl_mul, _root_.mul_assoc,
    inv_mul_cancel_left]

lemma translDiff_one : translDiff c (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A) = 1 := by
  rw [translDiff, transl_one, picPullback, Over.id_left, Scheme.Pic.pullback_id,
    MonoidHom.id_apply, mul_inv_cancel]

end Algebra

section Subgroup

variable (c : A.left.Pic)

/-- The set of rational points `z` such that `M_z` is trivial. -/
def fiberSet : Set (𝟙_ (Over (Spec (.of k))) ⟶ A) := {z | fiberClass c z = 1}

lemma mem_fiberSet_iff {z : 𝟙_ (Over (Spec (.of k))) ⟶ A} :
    z ∈ fiberSet c ↔ lambdaHom A (translDiff c z) = 1 := by
  rw [fiberSet, Set.mem_ofPred_eq, fiberClass_eq]

lemma one_mem_fiberSet : (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A) ∈ fiberSet c := by
  rw [mem_fiberSet_iff, translDiff_one, map_one]

lemma mul_mem_fiberSet {z w : 𝟙_ (Over (Spec (.of k))) ⟶ A} (hz : z ∈ fiberSet c)
    (hw : w ∈ fiberSet c) : z * w ∈ fiberSet c := by
  rw [mem_fiberSet_iff] at hz hw ⊢
  rw [translDiff_mul, pullback_transl_of_lambdaHom_eq_one hw, map_mul, hw, hz, _root_.mul_one]

lemma inv_mem_fiberSet {z : 𝟙_ (Over (Spec (.of k))) ⟶ A} (hz : z ∈ fiberSet c) :
    z⁻¹ ∈ fiberSet c := by
  rw [mem_fiberSet_iff] at hz ⊢
  have h := translDiff_mul c z⁻¹ z
  rw [_root_.inv_mul_cancel, translDiff_one, pullback_transl_of_lambdaHom_eq_one hz] at h
  rw [eq_inv_of_mul_eq_one_right h.symm, map_inv, hz, inv_one]

end Subgroup

section Geometry

variable (c : A.left.Pic)

lemma pullback_fiber_cubeClass (z : 𝟙_ (Over (Spec (.of k))) ⟶ A) :
    Scheme.Pic.pullback (lift (𝟙 (A ⊗ A)) (toUnit (A ⊗ A) ≫ z)).left
      (cubeClass c (fst _ _ ≫ fst _ _ : (A ⊗ A) ⊗ A ⟶ A) (fst _ _ ≫ snd _ _) (snd _ _)) =
    fiberClass c z := by
  rw [pullback_cubeClass, fiberClass]
  congr 1 <;> simp

/-- If `M` is trivial over `A × A × U`, then `M_z` is trivial for every rational point `z` in
`U`. -/
lemma mem_fiberSet_of_restrict {U : A.left.Opens}
    (hU : Scheme.Pic.pullback ((snd (A ⊗ A) A).left ⁻¹ᵁ U).ι
      (cubeClass c (fst _ _ ≫ fst _ _ : (A ⊗ A) ⊗ A ⟶ A) (fst _ _ ≫ snd _ _) (snd _ _)) = 1)
    {z : 𝟙_ (Over (Spec (.of k))) ⟶ A} (hz : Set.range z.left ⊆ U) : z ∈ fiberSet c := by
  set j := (lift (𝟙 (A ⊗ A)) (toUnit (A ⊗ A) ≫ z)).left with hj
  have hrange : Set.range j ⊆ Set.range ((snd (A ⊗ A) A).left ⁻¹ᵁ U).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (snd (A ⊗ A) A).left (j y) ∈ U
    rw [← Scheme.Hom.comp_apply, hj, ← Over.comp_left, lift_snd, Over.comp_left,
      Scheme.Hom.comp_apply]
    exact hz ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g ≫ ((snd (A ⊗ A) A).left ⁻¹ᵁ U).ι = j :=
    ⟨IsOpenImmersion.lift _ j hrange, IsOpenImmersion.lift_fac _ _ _⟩
  rw [fiberSet, Set.mem_ofPred_eq, ← pullback_fiber_cubeClass, ← hj, ← hg,
    Scheme.Pic.pullback_comp_apply, hU, map_one]

end Geometry

section Main

variable [IsAlgClosed k] [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left]

/-- Mumford, *Abelian varieties*, §6, Corollary 2, from the openness step of the theorem of the
cube (`hO`): the cube relation holds on an abelian variety. -/
theorem cubeRelation_of_cubeOpenness [IsCommMonObj A] (hO : CubeOpennessStatement.{u}) :
    CubeRelation A := by
  have : GeometricallyIntegral A.hom := geometricallyIntegral_of_smooth_of_isAlgClosed A.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  refine cubeRelation_of_proj fun c ↦ ?_
  set M := cubeClass c (fst _ _ ≫ fst _ _ : (A ⊗ A) ⊗ A ⟶ A) (fst _ _ ≫ snd _ _) (snd _ _)
    with hM
  have h₁ : Scheme.Pic.pullback
      (lift (lift (toUnit (A ⊗ A) ≫ η) (fst A A)) (snd A A)).left M = 1 := by
    rw [hM, cubeClass_proj_face₁, cubeClass_one_left]
  have h₂ : Scheme.Pic.pullback
      (lift (lift (fst A A) (toUnit (A ⊗ A) ≫ η)) (snd A A)).left M = 1 := by
    rw [hM, cubeClass_proj_face₂, cubeClass_one_middle]
  -- the openness step at a rational point of `S`
  have hopen (z : 𝟙_ (Over (Spec (.of k))) ⟶ A) (hz : z ∈ fiberSet c) :
      ∃ U : A.left.Opens, Set.range z.left ⊆ U ∧
        Scheme.Pic.pullback ((snd (A ⊗ A) A).left ⁻¹ᵁ U).ι M = 1 :=
    hO k A A A η η z M h₁ h₂ (by rw [pullback_fiber_cubeClass]; exact hz)
  -- `S` contains a neighbourhood of the origin, hence every rational point
  have hη : (η : 𝟙_ (Over (Spec (.of k))) ⟶ A) ∈ fiberSet c := by
    have : (η : 𝟙_ (Over (Spec (.of k))) ⟶ A) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [this]
    exact one_mem_fiberSet c
  obtain ⟨U₀, hU₀, hMU₀⟩ := hopen η hη
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsIntegral A.left := ExposeX.isIntegral_of_isRegularScheme
    (ExposeII.isRegularLocalRing_stalk_of_smooth_field k A.hom)
  -- rational points of `A` at closed points
  have hpt (x : A.left) (hx : IsClosed {x}) : ∃ z : 𝟙_ (Over (Spec (.of k))) ⟶ A,
      Set.range z.left = {x} := by
    refine ⟨Over.homMk (pointOfClosedPoint A.hom x hx) (pointOfClosedPoint_comp _ _ _), ?_⟩
    refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
    · obtain ⟨t⟩ : Nonempty (Spec (.of k)) := inferInstance
      exact ⟨t, pointOfClosedPoint_apply _ _ _ t⟩
    · rintro _ ⟨t, rfl⟩
      exact pointOfClosedPoint_apply _ _ _ t
  have hall (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : a ∈ fiberSet c := by
    let ψ : A ⟶ A := (toUnit A ≫ a) * (𝟙 A)⁻¹
    have haψ : a ≫ ψ = 1 := by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, toUnit_unique (a ≫ toUnit A) (𝟙 _),
        Category.id_comp, Category.comp_id, _root_.mul_inv_cancel]
    obtain ⟨t⟩ : Nonempty (Spec (.of k)) := inferInstance
    have hU₀ne : (U₀ : Set A.left).Nonempty := ⟨_, hU₀ ⟨t, rfl⟩⟩
    have hψne : (ψ.left ⁻¹ᵁ U₀ : Set A.left).Nonempty := by
      refine ⟨a.left t, ?_⟩
      change (a.left ≫ ψ.left) t ∈ U₀
      rw [← Over.comp_left, haψ, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
      exact hU₀ ⟨t, rfl⟩
    obtain ⟨x, ⟨hxU, hxψ⟩, hxc⟩ := nonempty_inter_closedPoints
      (nonempty_preirreducible_inter U₀.isOpen (ψ.left ⁻¹ᵁ U₀).isOpen hU₀ne hψne)
      (U₀.isOpen.inter (ψ.left ⁻¹ᵁ U₀).isOpen).isLocallyClosed
    obtain ⟨u, hu⟩ := hpt x hxc
    have hu₁ : u ∈ fiberSet c := mem_fiberSet_of_restrict c hMU₀ (by rw [hu]; simpa using hxU)
    have hu₂ : u ≫ ψ ∈ fiberSet c := by
      refine mem_fiberSet_of_restrict c hMU₀ ?_
      rintro _ ⟨s, rfl⟩
      rw [Over.comp_left, Scheme.Hom.comp_apply]
      have : u.left s = x := by
        have h : u.left s ∈ Set.range u.left := ⟨s, rfl⟩
        rwa [hu] at h
      rw [this]
      exact hxψ
    have e : u ≫ ψ = a * u⁻¹ := by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, toUnit_unique (u ≫ toUnit A) (𝟙 _),
        Category.id_comp, Category.comp_id]
    have := mul_mem_fiberSet c (e ▸ hu₂) hu₁
    rwa [_root_.inv_mul_cancel_right] at this
  -- every point has a neighbourhood over which `M` is trivial
  have hloc (w : A.left) : ∃ U : A.left.Opens, w ∈ U ∧
      Scheme.Pic.pullback ((snd (A ⊗ A) A).left ⁻¹ᵁ U).ι M = 1 := by
    obtain ⟨x, hxw, hxc⟩ := nonempty_inter_closedPoints (Z := closure {w})
      ⟨w, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    obtain ⟨z, hz⟩ := hpt x hxc
    obtain ⟨U, hzU, hMU⟩ := hopen z (hall z)
    have hxU : x ∈ U := hzU (by rw [hz]; rfl)
    exact ⟨U, (specializes_iff_mem_closure.2 hxw).mem_open U.isOpen hxU, hMU⟩
  -- glue, with `P = A × A` and the section `w ↦ (0, 0, w)`
  have : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom)
    infer_instance
  have hPP (V : (Spec (.of k)).Opens) : IsIso ((A ⊗ A).hom.app V) := by
    rw [← Over.w (snd A A), Scheme.Hom.comp_app]
    have h₁ := isIso_app_of_isProper_of_geometricallyIntegral A.hom V
    have h₂ := isIso_app_snd_tensor A A
      (isIso_app_of_isProper_of_geometricallyIntegral A.hom) (A.hom ⁻¹ᵁ V)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂
  obtain ⟨L, hL⟩ := Scheme.LineBundle.class_surjective _ M
  rw [← hL]
  refine Scheme.LineBundle.class_eq_one_of_forall_trivial (A ⊗ A) A hPP (lift η η) L ?_
    fun w ↦ ?_
  · rw [← Scheme.Pic.pullback_class, hL, hM, pullback_cubeClass]
    convert cubeClass_one_left c (1 : A ⟶ A) (𝟙 A) using 2 <;> simp [Hom.one_def]
  · obtain ⟨U, hwU, hMU⟩ := hloc w
    refine ⟨U, hwU, (L.class_pullback_ι_eq_one_iff _).1 ?_⟩
    rw [← Scheme.Pic.pullback_class, hL]
    exact hMU

end Main

end SGA.SGA1.ExposeXI
