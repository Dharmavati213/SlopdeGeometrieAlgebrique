/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import SGA.Foundations.Projective.LineBundle

/-!
# Serre's twisting sheaf `𝒪(1)` on `Proj`

Let `A` be an `ℕ`-graded ring and `(fᵢ)` a family of elements of degree `1` such that the basic
open subsets `D₊(fᵢ)` cover `Proj A` (e.g. a family generating `A` over `A₀`). Serre's twisting
sheaf `𝒪(1)` (EGA II 2.5.5) is the line bundle trivialized on the cover `D₊(fᵢ)` with transition
functions `gᵢⱼ = fⱼ / fᵢ`; a homogeneous element `a` of degree `d` is the section of `𝒪(d)` given
by `a / fᵢᵈ` on `D₊(fᵢ)`, with non-vanishing locus `D₊(a)` (EGA II 2.6.3).

## Main definitions and results

- `AlgebraicGeometry.Proj.fracSection`: the section `a / b` of `𝒪_{Proj A}` on `D₊(b)`, for `a` and
  `b` homogeneous of the same degree, and its basic open set `D₊(b) ∩ D₊(a)`.
- `AlgebraicGeometry.Proj.twistingSheaf`: the line bundle `𝒪(1)` attached to `(fᵢ)`.
- `AlgebraicGeometry.Proj.twistingSheaf.homogeneousSection`: the section of `𝒪(d)` defined by a
  homogeneous element of degree `d`, with non-vanishing locus `D₊(a)`.
- `AlgebraicGeometry.Proj.isAmple_twistingSheaf`, `Proj.isRelativelyAmple_twistingSheaf`:
  `𝒪(1)` is ample if `Proj A` is quasi-compact, and ample relative to `Proj A ⟶ Spec A₀` when the
  structure morphism is quasi-compact (EGA II 4.6.18).
- `AlgebraicGeometry.Proj.isQuasiProjective_toSpecZero`: if `A` is of finite type over `A₀` and
  the `D₊(fᵢ)` cover `Proj A`, then `Proj A ⟶ Spec A₀` is quasi-projective (EGA II 5.5.1 (ii)
  and 4.6.18).
-/

universe u

open CategoryTheory TopologicalSpace Opposite HomogeneousLocalization

namespace AlgebraicGeometry

namespace Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

section fracSection

set_option backward.isDefEq.respectTransparency false in
/-- Two sections of the structure sheaf of `Proj A` are equal if their values in the homogeneous
localizations `A_(x)` agree, computed in the localizations `A_x`. -/
lemma section_ext {U : (Proj 𝒜).Opens} {s t : Γ(Proj 𝒜, U)}
    (h : ∀ x : U, (s.1 x).val = (t.1 x).val) : s = t :=
  Subtype.ext (funext fun x ↦ HomogeneousLocalization.val_injective _ (h x))

set_option backward.isDefEq.respectTransparency false in
/-- The section `a / b` of `𝒪_{Proj A}` over an open subset of `D₊(b)`, where `a` and `b` are
homogeneous of the same degree. -/
def fracSection {d : ℕ} {a b : A} (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d) (U : (Proj 𝒜).Opens)
    (hU : U ≤ basicOpen 𝒜 b) : Γ(Proj 𝒜, U) :=
  ⟨fun x ↦ HomogeneousLocalization.mk ⟨d, ⟨a, ha⟩, ⟨b, hb⟩, hU x.2⟩,
    fun x ↦ ⟨U, x.2, 𝟙 U, d, ⟨a, ha⟩, ⟨b, hb⟩, fun y ↦ hU y.2, fun _ ↦ rfl⟩⟩

variable {𝒜}

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma val_fracSection_apply {d : ℕ} {a b : A} (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : U ≤ basicOpen 𝒜 b) (x : U) :
    ((fracSection 𝒜 ha hb U hU).1 x).val = Localization.mk a ⟨b, hU x.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma map_fracSection {d : ℕ} {a b : A} (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    {U V : (Proj 𝒜).Opens} (hU : U ≤ basicOpen 𝒜 b) (i : V ⟶ U) :
    (Proj 𝒜).presheaf.map i.op (fracSection 𝒜 ha hb U hU) =
      fracSection 𝒜 ha hb V ((leOfHom i).trans hU) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma fracSection_mul {d e : ℕ} {a b a' b' : A} (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (ha' : a' ∈ 𝒜 e) (hb' : b' ∈ 𝒜 e) (U : (Proj 𝒜).Opens) (hU : U ≤ basicOpen 𝒜 b)
    (hU' : U ≤ basicOpen 𝒜 b') :
    fracSection 𝒜 ha hb U hU * fracSection 𝒜 ha' hb' U hU' =
      fracSection 𝒜 (SetLike.mul_mem_graded ha ha') (SetLike.mul_mem_graded hb hb') U
        (by rw [basicOpen_mul]; exact le_inf hU hU') := by
  exact section_ext 𝒜 fun x ↦ rfl

set_option backward.isDefEq.respectTransparency false in
lemma fracSection_self {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) (U : (Proj 𝒜).Opens)
    (hU : U ≤ basicOpen 𝒜 a) : fracSection 𝒜 ha ha U hU = 1 := by
  refine section_ext 𝒜 fun x ↦ ?_
  exact (Localization.mk_self (⟨a, hU x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl)).trans
    val_one.symm

set_option backward.isDefEq.respectTransparency false in
/-- A section of `𝒪_{Proj A}` is invertible at `x` iff its value in `A_(x)` is a unit. -/
lemma mem_basicOpen_iff {U : (Proj 𝒜).Opens} (s : Γ(Proj 𝒜, U)) {x : Proj 𝒜} (hx : x ∈ U) :
    x ∈ (Proj 𝒜).basicOpen s ↔ IsUnit (s.1 ⟨x, hx⟩) := by
  rw [Scheme.mem_basicOpen _ _ _ hx, ← MulEquiv.isUnit_map (Proj.stalkIso' 𝒜 x).toMulEquiv]
  exact iff_of_eq (congrArg IsUnit (Proj.stalkIso'_germ 𝒜 U x hx s))

set_option backward.isDefEq.respectTransparency false in
/-- The basic open subset of `a / b` is `U ∩ D₊(a)`. -/
lemma basicOpen_fracSection {d : ℕ} {a b : A} (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hU : U ≤ basicOpen 𝒜 b) :
    (Proj 𝒜).basicOpen (fracSection 𝒜 ha hb U hU) = U ⊓ basicOpen 𝒜 a := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hxU : x ∈ U := (Proj 𝒜).basicOpen_le _ hx
    rw [mem_basicOpen_iff _ hxU, ← isUnit_iff_isUnit_val, val_fracSection_apply,
      Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff] at hx
    exact ⟨hxU, hx⟩
  · obtain ⟨hxU, hxa⟩ := hx
    rw [mem_basicOpen_iff _ hxU, ← isUnit_iff_isUnit_val, val_fracSection_apply,
      Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
    exact hxa

set_option backward.isDefEq.respectTransparency false in
lemma val_mul_apply {U : (Proj 𝒜).Opens} (s t : Γ(Proj 𝒜, U)) (x : U) :
    ((s * t).1 x).val = (s.1 x).val * (t.1 x).val :=
  val_mul _ _

set_option backward.isDefEq.respectTransparency false in
lemma val_pow_apply {U : (Proj 𝒜).Opens} (s : Γ(Proj 𝒜, U)) (n : ℕ) (x : U) :
    ((s ^ n).1 x).val = (s.1 x).val ^ n :=
  val_pow _ _

set_option backward.isDefEq.respectTransparency false in
lemma val_one_apply {U : (Proj 𝒜).Opens} (x : U) :
    ((1 : Γ(Proj 𝒜, U)).1 x).val = 1 :=
  val_one

/-- `a / b = a' / b'` as soon as `a b' = a' b`. -/
lemma fracSection_eq {d e : ℕ} {a b a' b' : A} (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (ha' : a' ∈ 𝒜 e) (hb' : b' ∈ 𝒜 e) (U : (Proj 𝒜).Opens) (hU : U ≤ basicOpen 𝒜 b)
    (hU' : U ≤ basicOpen 𝒜 b') (h : a * b' = a' * b) :
    fracSection 𝒜 ha hb U hU = fracSection 𝒜 ha' hb' U hU' := by
  refine section_ext 𝒜 fun x ↦ ?_
  rw [val_fracSection_apply, val_fracSection_apply, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; linear_combination h⟩

lemma fracSection_mul_fracSection_swap {d : ℕ} {a b : A} (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (hUa : U ≤ basicOpen 𝒜 a) (hUb : U ≤ basicOpen 𝒜 b) :
    fracSection 𝒜 ha hb U hUb * fracSection 𝒜 hb ha U hUa = 1 := by
  rw [fracSection_mul, fracSection_eq _ _ ha ha _ _ hUa (by ring), fracSection_self]

end fracSection

section twistingSheaf

variable {ι : Type u} (f : ι → A) (hf : ∀ i, f i ∈ 𝒜 1)
  (hcov : ⨆ i, basicOpen 𝒜 (f i) = ⊤)

/-- The transition function `fⱼ / fᵢ`, a unit on `D₊(fᵢ) ∩ D₊(fⱼ)`. -/
def twistingUnit (i j : ι) : Γ(Proj 𝒜, basicOpen 𝒜 (f i) ⊓ basicOpen 𝒜 (f j))ˣ where
  val := fracSection 𝒜 (hf j) (hf i) _ inf_le_left
  inv := fracSection 𝒜 (hf i) (hf j) _ inf_le_right
  val_inv := fracSection_mul_fracSection_swap (hf j) (hf i) _ inf_le_right inf_le_left
  inv_val := fracSection_mul_fracSection_swap (hf i) (hf j) _ inf_le_left inf_le_right

/-- Serre's twisting sheaf `𝒪(1)` on `Proj A` (EGA II 2.5.5), attached to a family `(fᵢ)` of
elements of degree `1` whose basic open subsets `D₊(fᵢ)` cover `Proj A`: the line bundle
trivialized on the `D₊(fᵢ)` with transition functions `gᵢⱼ = fⱼ / fᵢ`. -/
def twistingSheaf : (Proj 𝒜).LineBundle where
  ι := ι
  U i := basicOpen 𝒜 (f i)
  iSup_eq_top := hcov
  g i j := twistingUnit 𝒜 f hf i j
  cocycle i j k := by
    simp only [twistingUnit, map_fracSection]
    rw [fracSection_mul]
    exact fracSection_eq _ _ _ _ _ _ _ (by ring)

lemma pow_mem_of_mem_one {a : A} (ha : a ∈ 𝒜 1) (d : ℕ) : a ^ d ∈ 𝒜 d := by
  simpa using SetLike.pow_mem_graded d ha

lemma basicOpen_le_basicOpen_pow (a : A) (d : ℕ) : basicOpen 𝒜 a ≤ basicOpen 𝒜 (a ^ d) :=
  fun x hx h ↦ hx (x.isPrime.mem_of_pow_mem d h)

namespace twistingSheaf

variable {𝒜}

lemma homogeneousSection_compat {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) (i j : ι) :
    fracSection 𝒜 ha (pow_mem_of_mem_one 𝒜 (hf i) d) (basicOpen 𝒜 (f i) ⊓ basicOpen 𝒜 (f j))
        (inf_le_left.trans (basicOpen_le_basicOpen_pow 𝒜 _ _)) =
      fracSection 𝒜 (hf j) (hf i) _ inf_le_left ^ d * fracSection 𝒜 ha
        (pow_mem_of_mem_one 𝒜 (hf j) d) _
        (inf_le_right.trans (basicOpen_le_basicOpen_pow 𝒜 _ _)) := by
  refine section_ext 𝒜 fun x ↦ ?_
  rw [val_mul_apply, val_pow_apply, val_fracSection_apply, val_fracSection_apply,
    val_fracSection_apply, Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul,
    SubmonoidClass.coe_pow]; ring⟩

/-- The section `a` of `𝒪(d)` defined by a homogeneous element `a` of degree `d`: it is
`a / fᵢᵈ` on `D₊(fᵢ)` (EGA II 2.6.3). -/
def homogeneousSection {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) :
    (twistingSheaf 𝒜 f hf hcov).sections d :=
  ⟨fun (i : ι) ↦ fracSection 𝒜 ha (pow_mem_of_mem_one 𝒜 (hf i) d) (basicOpen 𝒜 (f i))
      (basicOpen_le_basicOpen_pow 𝒜 _ _),
    fun (i j : ι) ↦ homogeneousSection_compat f hf ha i j⟩

/-- The non-vanishing locus of the section of `𝒪(d)` defined by `a` is `D₊(a)`. -/
lemma nonvanishingLocus_homogeneousSection {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) :
    (twistingSheaf 𝒜 f hf hcov).nonvanishingLocus (homogeneousSection f hf hcov ha) =
      basicOpen 𝒜 a := by
  change ⨆ i : ι, (Proj 𝒜).basicOpen (fracSection 𝒜 ha (pow_mem_of_mem_one 𝒜 (hf i) d)
    (basicOpen 𝒜 (f i)) (basicOpen_le_basicOpen_pow 𝒜 _ _)) = _
  simp only [basicOpen_fracSection, ← iSup_inf_eq, hcov, top_inf_eq]

end twistingSheaf

open twistingSheaf

/-- `𝒪(1)` is ample on `Proj A` if `Proj A` is quasi-compact. -/
theorem isAmple_twistingSheaf [CompactSpace (Proj 𝒜)] :
    (twistingSheaf 𝒜 f hf hcov).IsAmple := by
  refine ⟨‹_›, fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
  refine ⟨1, one_pos, homogeneousSection f hf hcov (hf i), ?_, ?_⟩ <;>
    rw [nonvanishingLocus_homogeneousSection]
  exacts [hi, isAffineOpen_basicOpen 𝒜 _ (hf i) one_pos]

/-- `𝒪(1)` is ample relative to the structure morphism `Proj A ⟶ Spec A₀` when the latter is
quasi-compact (EGA II 4.6.18). -/
theorem isRelativelyAmple_twistingSheaf [QuasiCompact (toSpecZero 𝒜)] :
    (twistingSheaf 𝒜 f hf hcov).IsRelativelyAmple (toSpecZero 𝒜) := by
  refine Scheme.LineBundle.isRelativelyAmple_of_isAffineHom _ (fun _ : ι ↦ 1)
    (fun _ ↦ one_pos) (fun i ↦ homogeneousSection f hf hcov (hf i)) (fun x ↦ ?_) (fun i ↦ ?_)
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
    exact ⟨i, by rwa [nonvanishingLocus_homogeneousSection]⟩
  · have : IsAffine ((twistingSheaf 𝒜 f hf hcov).nonvanishingLocus
        (homogeneousSection f hf hcov (hf i))) := by
      rw [nonvanishingLocus_homogeneousSection]
      exact isAffineOpen_basicOpen 𝒜 _ (hf i) one_pos
    infer_instance

include hf hcov in
/-- EGA II 5.5.1 (ii) and 4.6.18: if `A` is of finite type over `A₀` and the basic open subsets of
a family of elements of degree `1` cover `Proj A` (e.g. `A` is generated by `A₁` over `A₀`), then
`Proj A ⟶ Spec A₀` is quasi-projective. -/
theorem isQuasiProjective_toSpecZero [Algebra.FiniteType (𝒜 0) A] :
    IsQuasiProjective (toSpecZero 𝒜) :=
  ⟨inferInstance, inferInstance, ⟨_, isRelativelyAmple_twistingSheaf 𝒜 f hf hcov⟩⟩

end twistingSheaf

end Proj

end AlgebraicGeometry
