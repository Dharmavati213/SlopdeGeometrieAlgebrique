/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import SGA.Foundations.Projective.Norm
import SGA.Foundations.Projective.AmpleFinite

/-!
# The norm of a line bundle along a finite locally free morphism

Let `h : X' ⟶ X` be finite locally free and `L` a line bundle on `X'` which is trivial over the
inverse images of the members of an open cover of `X`. The norms `N_h(e_W'/e_W)` of the ratios of
trivializations `e_W` of `L` over the inverse images `h⁻¹ W` are the transition functions of a
line bundle `N_h(L)` on `X` (EGA II 6.5), and the norms of sections of `L^{⊗n}` are sections of
`N_h(L)^{⊗n}`. If `L` is ample relative to `X' ⟶ S`, then `N_h(L)` is ample relative to `X ⟶ S`
(EGA II 6.6).

## Main definitions and results

- `Scheme.LineBundle.Trivialization`: a nowhere vanishing section of `L` over an open, and the
  coordinates `Trivialization.coord` of sections with respect to it.
- `Scheme.LineBundle.exists_isSection_one_forall_mem_famLocus`: a line bundle is trivial in a
  neighbourhood of any finite subset of an affine open;
  `Scheme.LineBundle.exists_trivialization_preimage`: for `h` finite, it is trivial over the
  inverse image of a neighbourhood of `x` if the fibre of `x` lies in an affine open.
- `Scheme.LineBundle.normBundle`: the norm `N_h(L)`, and `Scheme.LineBundle.normFam`: the norm of
  a section, with `mem_famLocus_normFam`: `N_h(s)(x) ≠ 0` iff `s` does not vanish over `x`.
- `Scheme.LineBundle.isAmple_pullback_normBundle`,
  `Scheme.LineBundle.IsRelativelyAmple.exists_of_isFinite`: the norm of an ample (relatively
  ample) line bundle along a finite locally free surjective morphism is ample (relatively ample).
- `IsQuasiProjective.of_isFinite_comp`: if `h` is finite locally free surjective, `f` is of
  finite type and quasi-separated and `h ≫ f` is quasi-projective, then `f` is quasi-projective
  (EGA II 6.6.4).
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

lemma Scheme.isUnit_of_le_basicOpen {X : Scheme.{u}} {U : X.Opens} {a : Γ(X, U)}
    (h : U ≤ X.basicOpen a) : IsUnit a :=
  X.toRingedSpace.isUnit_of_isUnit_germ U a fun x hx ↦ (X.mem_basicOpen a x hx).mp (h hx)

lemma Scheme.mem_basicOpen_add {X : Scheme.{u}} {U : X.Opens} {a b : Γ(X, U)} {x : X}
    (ha : x ∈ X.basicOpen a) (hb : x ∉ X.basicOpen b) : x ∈ X.basicOpen (a + b) := by
  have hx : x ∈ U := X.basicOpen_le a ha
  rw [X.mem_basicOpen _ x hx] at ha hb ⊢
  rw [map_add]
  by_contra H
  have hb' : -(X.presheaf.germ U x hx b) ∈ nonunits _ := fun h ↦ hb (by simpa using h.neg)
  have := IsLocalRing.nonunits_add H hb'
  rw [add_neg_cancel_right] at this
  exact this ha

namespace Scheme.LineBundle

variable {X : Scheme.{u}} {L : X.LineBundle}

lemma famLocus_of_isUnit {V : X.Opens} {u : L.Fam V} (hu : IsUnit u) : L.famLocus V u = V := by
  refine le_antisymm (famLocus_le u) fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (L.iSup_eq_top.ge (Set.mem_univ x))
  refine Opens.mem_iSup.mpr ⟨i, ?_⟩
  rw [Scheme.basicOpen_of_isUnit _ ((Pi.isUnit_iff.mp hu) i)]
  exact ⟨hx, hi⟩

lemma isUnit_of_le_famLocus {V : X.Opens} {n : ℤ} {s : L.Fam V} (hs : L.IsSection n V s)
    (h : V ≤ L.famLocus V s) : IsUnit s := by
  refine Pi.isUnit_iff.mpr fun i ↦ Scheme.isUnit_of_le_basicOpen ?_
  rw [← famLocus_inf_U hs i]
  exact inf_le_inf_right _ h

variable (L) in
/-- A trivialization of `L` over an open `V`: a section of `L` over `V` which is a unit, that is,
which vanishes nowhere on `V`. -/
structure Trivialization (V : X.Opens) where
  /-- The generating section. -/
  e : L.Fam V
  isSection : L.IsSection ((1 : ℕ) : ℤ) V e
  isUnit : IsUnit e

namespace Trivialization

variable {V V' : X.Opens} (τ : L.Trivialization V)

lemma isSection_pow (n : ℕ) : L.IsSection n V (τ.e ^ n) :=
  (τ.isSection.pow n).of_eq (by push_cast; ring)

lemma existsUnique_coord {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) :
    ∃! c : Γ(X, V), L.famConst V c * τ.e ^ n = s := by
  have hu : IsUnit (τ.e ^ n) := τ.isUnit.pow n
  refine existsUnique_of_exists_of_unique ?_ fun c c' hc hc' ↦ ?_
  · have hy : L.IsSection 0 V (↑hu.unit⁻¹ * s) := by
      refine (τ.isSection_pow n).of_isUnit_mul hu ?_
      rw [← mul_assoc, hu.mul_val_inv, one_mul]
      exact hs
    obtain ⟨c, hc⟩ := exists_famConst_eq hy
    refine ⟨c, ?_⟩
    rw [hc, mul_comm, ← mul_assoc, hu.mul_val_inv, one_mul]
  · exact famConst_injective V (hu.mul_left_injective (hc.trans hc'.symm))

/-- The coordinate `s / eⁿ ∈ Γ(X, V)` of a section `s` of `L^{⊗n}` over `V` with respect to a
trivialization `e` of `L` over `V`. -/
noncomputable def coord {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) : Γ(X, V) :=
  (τ.existsUnique_coord hs).exists.choose

lemma famConst_coord_mul {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) :
    L.famConst V (τ.coord hs) * τ.e ^ n = s :=
  (τ.existsUnique_coord hs).exists.choose_spec

lemma eq_coord {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) {c : Γ(X, V)}
    (hc : L.famConst V c * τ.e ^ n = s) : c = τ.coord hs :=
  (τ.existsUnique_coord hs).unique hc (τ.famConst_coord_mul hs)

lemma coord_congr {n : ℕ} {s s' : L.Fam V} (hs : L.IsSection n V s) (hs' : L.IsSection n V s')
    (h : s = s') : τ.coord hs = τ.coord hs' := by
  subst h
  rfl

omit τ in
@[ext]
lemma ext {τ σ : L.Trivialization V} (h : τ.e = σ.e) : τ = σ := by
  cases τ
  cases σ
  cases h
  rfl

/-- The restriction of a trivialization to a smaller open. -/
noncomputable def res (h : V' ≤ V) : L.Trivialization V' :=
  ⟨L.famRes h τ.e, τ.isSection.famRes h, τ.isUnit.map _⟩

lemma res_res {V'' : X.Opens} (h₁ : V' ≤ V) (h₂ : V'' ≤ V') :
    (τ.res h₁).res h₂ = τ.res (h₂.trans h₁) :=
  ext (famRes_famRes h₁ h₂ τ.e)

lemma coord_res (h : V' ≤ V) {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) :
    (τ.res h).coord (hs.famRes h) = X.presheaf.map (homOfLE h).op (τ.coord hs) := by
  refine ((τ.res h).eq_coord _ ?_).symm
  rw [← famRes_famConst, res, ← map_pow, ← map_mul, τ.famConst_coord_mul]

lemma coord_self : τ.coord τ.isSection = 1 :=
  (τ.eq_coord _ (by rw [map_one, one_mul, pow_one])).symm

lemma coord_mul {m n : ℕ} {s t : L.Fam V} (hs : L.IsSection m V s) (ht : L.IsSection n V t) :
    τ.coord ((hs.mul ht).of_eq (Nat.cast_add m n).symm) = τ.coord hs * τ.coord ht := by
  refine (τ.eq_coord _ ?_).symm
  rw [map_mul, pow_add, mul_mul_mul_comm, τ.famConst_coord_mul, τ.famConst_coord_mul]

lemma coord_eq_mul (σ : L.Trivialization V) {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) :
    τ.coord hs = τ.coord σ.isSection ^ n * σ.coord hs := by
  have ha : L.famConst V (τ.coord σ.isSection) * τ.e = σ.e := by
    simpa only [pow_one] using τ.famConst_coord_mul σ.isSection
  refine (τ.eq_coord _ ?_).symm
  rw [map_mul, map_pow, mul_comm (L.famConst V _ ^ n), mul_assoc, ← mul_pow, ha,
    σ.famConst_coord_mul]

lemma coord_mul_coord (σ ρ : L.Trivialization V) :
    τ.coord σ.isSection * σ.coord ρ.isSection = τ.coord ρ.isSection := by
  rw [τ.coord_eq_mul σ ρ.isSection, pow_one, mul_comm]

lemma isUnit_coord (σ : L.Trivialization V) : IsUnit (τ.coord σ.isSection) :=
  IsUnit.of_mul_eq_one _ ((τ.coord_mul_coord σ τ).trans τ.coord_self)

lemma basicOpen_coord {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) :
    X.basicOpen (τ.coord hs) = L.famLocus V s := by
  conv_rhs => rw [← τ.famConst_coord_mul hs]
  rw [famLocus_mul _ (τ.isSection_pow n), famLocus_famConst, famLocus_of_isUnit (τ.isUnit.pow n),
    inf_eq_left.mpr (X.basicOpen_le _)]

end Trivialization

section Affine

variable {U : X.Opens}

omit L in
lemma _root_.AlgebraicGeometry.IsAffineOpen.mem_basicOpen_iff (hU : IsAffineOpen U)
    (c : Γ(X, U)) (y : U) : y.1 ∈ X.basicOpen c ↔ c ∉ (hU.primeIdealOf y).asIdeal := by
  rw [← hU.fromSpec_primeIdealOf y]
  change hU.primeIdealOf y ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c ↔ _
  rw [hU.fromSpec_preimage_basicOpen]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Over an affine open `U`, every point of `U` lies in the non-vanishing locus of a section of
`L` over `U`: a local generator of `L` near the point, multiplied by a power of a function
defining a small basic open, extends to `U`. -/
lemma exists_isSection_one_mem_famLocus (hU : IsAffineOpen U) {y : X} (hy : y ∈ U) :
    ∃ s : L.Fam U, L.IsSection ((1 : ℕ) : ℤ) U s ∧ y ∈ L.famLocus U s := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (L.iSup_eq_top.ge (Set.mem_univ y))
  obtain ⟨a, ha, hya⟩ := hU.exists_basicOpen_le (V := L.U i) ⟨y, hi⟩ hy
  have hloc : L.famLocus U (L.famConst U a) ≤ L.U i := by
    rw [famLocus_famConst]
    exact ha
  obtain ⟨t, ht, ht1⟩ := exists_isSection_famUnit_eq (L := L) i ((1 : ℕ) : ℤ) hloc 1
  have htl : L.famLocus _ t = L.famLocus U (L.famConst U a) := by
    rw [famLocus_eq_basicOpen_famUnit i ht hloc, ht1, Scheme.basicOpen_one]
  obtain ⟨k, y', hy', e⟩ := exists_isSection_famRes_eq hU.isCompact hU.isQuasiSeparated
    (isSection_famConst (L := L) a) ht
  refine ⟨L.famConst U a * y', ((isSection_famConst a).mul hy').of_eq (by simp), ?_⟩
  rw [famLocus_mul_eq hy' ht e, htl, famLocus_famConst]
  exact hya

set_option backward.isDefEq.respectTransparency false in
/-- A line bundle is trivial in a neighbourhood of any finite subset `F` of an affine open `U`:
there is a section of `L` over `U` which does not vanish at the points of `F` (prime avoidance
in `Γ(U, 𝒪_X)`, choosing a point of `F` whose prime ideal is minimal). -/
theorem exists_isSection_one_forall_mem_famLocus (hU : IsAffineOpen U) (F : Finset U) :
    ∃ s : L.Fam U, L.IsSection ((1 : ℕ) : ℤ) U s ∧ ∀ y ∈ F, y.1 ∈ L.famLocus U s := by
  classical
  induction F using Finset.strongInduction with
  | H F ih =>
  rcases F.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, isSection_zero _, by simp⟩
  let P : U → PrimeSpectrum Γ(X, U) := hU.primeIdealOf
  have hP : Function.Injective P := fun y z h ↦ Subtype.ext <| by
    rw [← hU.fromSpec_primeIdealOf y, ← hU.fromSpec_primeIdealOf z]
    exact congrArg hU.fromSpec h
  obtain ⟨q, hqs, hqmin⟩ :=
    ((F.image P : Finset _) : Set (PrimeSpectrum Γ(X, U))).toFinite.exists_minimal
      (by simpa using hne)
  obtain ⟨y₀, hy₀F, rfl⟩ := Finset.mem_image.mp hqs
  obtain ⟨s, hs, hsF⟩ := ih _ (Finset.erase_ssubset hy₀F)
  by_cases hs₀ : y₀.1 ∈ L.famLocus U s
  · refine ⟨s, hs, fun y hy ↦ ?_⟩
    by_cases h : y = y₀
    · exact h ▸ hs₀
    · exact hsF y (Finset.mem_erase.mpr ⟨h, hy⟩)
  obtain ⟨t, ht, hty⟩ := exists_isSection_one_mem_famLocus (L := L) hU y₀.2
  have ha (z : F.erase y₀) : ∃ a : Γ(X, U), a ∈ (P z.1).asIdeal ∧ a ∉ (P y₀).asIdeal := by
    have hz := Finset.mem_erase.mp z.2
    by_contra! H
    have hle : P z.1 ≤ P y₀ := fun a ha ↦ H a ha
    have hzF : P z.1 ∈ ((F.image P : Finset _) : Set (PrimeSpectrum Γ(X, U))) :=
      Finset.mem_coe.mpr (Finset.mem_image_of_mem P hz.2)
    exact hz.1 (hP (le_antisymm hle (hqmin hzF hle)))
  choose a haz hay using ha
  let c : Γ(X, U) := ∏ z : F.erase y₀, a z
  have hc₀ : c ∉ (P y₀).asIdeal := by
    intro h
    obtain ⟨z, -, hz⟩ := (Ideal.IsPrime.prod_mem_iff (p := (P y₀).asIdeal)).mp h
    exact hay z hz
  have hcz (z : U) (hz : z ∈ F.erase y₀) : c ∈ (P z).asIdeal :=
    Ideal.mem_of_dvd (I := (P z).asIdeal) (Finset.dvd_prod_of_mem _ (Finset.mem_univ ⟨z, hz⟩))
      (haz ⟨z, hz⟩)
  have hct : L.IsSection ((1 : ℕ) : ℤ) U (L.famConst U c * t) :=
    ((isSection_famConst c).mul ht).of_eq (zero_add _)
  have hsum : L.IsSection ((1 : ℕ) : ℤ) U (s + L.famConst U c * t) :=
    (L.sectionsAddSubgroup _ U).add_mem hs hct
  refine ⟨_, hsum, fun y hy ↦ ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (L.iSup_eq_top.ge (Set.mem_univ y.1))
  have hyi : y.1 ∈ U ⊓ L.U i := ⟨y.2, hi⟩
  rw [mem_famLocus_iff hsum hi, Pi.add_apply]
  have hcti : X.basicOpen ((L.famConst U c * t) i) = (U ⊓ L.U i) ⊓ X.basicOpen c ⊓
      X.basicOpen (t i) := by
    rw [Pi.mul_apply, Scheme.basicOpen_mul, famConst_apply, Scheme.basicOpen_res]
  by_cases h : y = y₀
  · subst h
    rw [add_comm]
    refine Scheme.mem_basicOpen_add ?_ fun h' ↦ hs₀ ((mem_famLocus_iff hs hi).mpr h')
    rw [hcti]
    exact ⟨⟨hyi, (hU.mem_basicOpen_iff c y).mpr hc₀⟩, (mem_famLocus_iff ht hi).mp hty⟩
  · have hyF : y ∈ F.erase y₀ := Finset.mem_erase.mpr ⟨h, hy⟩
    refine Scheme.mem_basicOpen_add ((mem_famLocus_iff hs hi).mp (hsF y hyF)) ?_
    rw [hcti]
    exact fun h' ↦ (hU.mem_basicOpen_iff c y).mp h'.1.2 (hcz y hyF)

end Affine

section Fibre

variable {X' : Scheme.{u}} (h : X' ⟶ X) [IsFinite h] {L : X'.LineBundle}

set_option backward.isDefEq.respectTransparency false in
/-- If the fibre of a finite morphism `h : X' ⟶ X` over `x` lies in an affine open of `X'`, then a
line bundle on `X'` is trivial over the inverse image of a neighbourhood of `x`. -/
theorem exists_trivialization_preimage (x : X) {U : X'.Opens} (hU : IsAffineOpen U)
    (hxU : ∀ y, h y = x → y ∈ U) :
    ∃ W : X.Opens, x ∈ W ∧ Nonempty (L.Trivialization (h ⁻¹ᵁ W)) := by
  classical
  have hfin : (h ⁻¹' {x}).Finite := h.finite_preimage_singleton x
  obtain ⟨s, hs, hsF⟩ := exists_isSection_one_forall_mem_famLocus (L := L) hU
    (hfin.toFinset.subtype (· ∈ U))
  have hC : IsClosed (h '' (L.famLocus U s : Set X')ᶜ) :=
    h.isClosedMap _ (L.famLocus U s).isOpen.isClosed_compl
  let W : X.Opens := ⟨(h '' (L.famLocus U s : Set X')ᶜ)ᶜ, hC.isOpen_compl⟩
  have hxW : x ∈ W := by
    rintro ⟨y, hyC, hyx⟩
    refine hyC (hsF ⟨y, hxU y hyx⟩ (Finset.mem_subtype.mpr ?_))
    simpa using hyx
  have hWU : h ⁻¹ᵁ W ≤ L.famLocus U s := fun y hy ↦ by
    by_contra hy'
    exact hy ⟨y, hy', rfl⟩
  have hle : h ⁻¹ᵁ W ≤ U := hWU.trans (famLocus_le s)
  refine ⟨W, hxW, ⟨⟨L.famRes hle s, hs.famRes hle, isUnit_of_le_famLocus (hs.famRes hle) ?_⟩⟩⟩
  rw [famLocus_famRes]
  exact le_inf le_rfl hWU

end Fibre

section NormBundle

variable {X' : Scheme.{u}} (h : X' ⟶ X) (L : X'.LineBundle)

/-- The opens `W` of `X` together with a trivialization of `L` over `h⁻¹ W`: the index set of the
trivializing cover of the norm of `L`. -/
def NormIndex : Type u := Σ W : X.Opens, L.Trivialization (h ⁻¹ᵁ W)

variable {h L}

namespace NormIndex

variable (p q r : NormIndex h L)

/-- The coordinate over an open `V' ⊆ h⁻¹ W_p` of a section of `L^{⊗n}` over `V₀ ⊇ V'`, with
respect to the trivialization of `p`. -/
noncomputable def coordOn {V' V₀ : X'.Opens} (hp : V' ≤ h ⁻¹ᵁ p.1) (hV : V' ≤ V₀) {n : ℕ}
    {s : L.Fam V₀} (hs : L.IsSection n V₀ s) : Γ(X', V') :=
  (p.2.res hp).coord (hs.famRes hV)

lemma coordOn_res {V' V'' V₀ : X'.Opens} (hp : V' ≤ h ⁻¹ᵁ p.1) (hV : V' ≤ V₀) (h' : V'' ≤ V')
    {n : ℕ} {s : L.Fam V₀} (hs : L.IsSection n V₀ s) :
    X'.presheaf.map (homOfLE h').op (p.coordOn hp hV hs) =
      p.coordOn (h'.trans hp) (h'.trans hV) hs := by
  rw [coordOn, ← Trivialization.coord_res, Trivialization.res_res]
  exact Trivialization.coord_congr _ _ _ (famRes_famRes _ _ _)

/-- The ratio `e_q / e_p` of the trivializations of `p` and `q` over an open
`V ⊆ h⁻¹(W_p ∩ W_q)`. -/
noncomputable abbrev ratioOn {V : X'.Opens} (hp : V ≤ h ⁻¹ᵁ p.1) (hq : V ≤ h ⁻¹ᵁ q.1) :
    Γ(X', V) :=
  p.coordOn hp hq q.2.isSection

lemma ratioOn_mul {V : X'.Opens} (hp : V ≤ h ⁻¹ᵁ p.1) (hq : V ≤ h ⁻¹ᵁ q.1)
    (hr : V ≤ h ⁻¹ᵁ r.1) : p.ratioOn q hp hq * q.ratioOn r hq hr = p.ratioOn r hp hr :=
  (p.2.res hp).coord_mul_coord (q.2.res hq) (r.2.res hr)

lemma isUnit_ratioOn {V : X'.Opens} (hp : V ≤ h ⁻¹ᵁ p.1) (hq : V ≤ h ⁻¹ᵁ q.1) :
    IsUnit (p.ratioOn q hp hq) :=
  (p.2.res hp).isUnit_coord (q.2.res hq)

lemma coordOn_eq_mul {V V₀ : X'.Opens} (hp : V ≤ h ⁻¹ᵁ p.1) (hq : V ≤ h ⁻¹ᵁ q.1) (hV : V ≤ V₀)
    {n : ℕ} {s : L.Fam V₀} (hs : L.IsSection n V₀ s) :
    p.coordOn hp hV hs = p.ratioOn q hp hq ^ n * q.coordOn hq hV hs :=
  (p.2.res hp).coord_eq_mul (q.2.res hq) (hs.famRes hV)

end NormIndex

variable [IsFinite h] [Flat h] [LocallyOfFinitePresentation h]

/-- The transition function `N_h(e_q / e_p)` of the norm of `L`. -/
noncomputable def normTrans (p q : NormIndex h L) : Γ(X, p.1 ⊓ q.1)ˣ :=
  ((p.isUnit_ratioOn q (h.preimage_mono inf_le_left) (h.preimage_mono inf_le_right)).map
    (h.norm (p.1 ⊓ q.1))).unit

lemma coe_normTrans (p q : NormIndex h L) : (normTrans p q : Γ(X, p.1 ⊓ q.1)) =
    h.norm (p.1 ⊓ q.1) (p.ratioOn q (h.preimage_mono inf_le_left) (h.preimage_mono inf_le_right)) :=
  IsUnit.unit_spec _

variable (h L) in
set_option backward.isDefEq.respectTransparency false in
/-- The norm `N_h(L)` of a line bundle `L` on `X'` along a finite locally free `h : X' ⟶ X`, given
that `L` is trivial over the inverse images of the members of an open cover of `X` (EGA II 6.5):
its trivializing opens are the opens `W` with a trivialization `e_W` of `L` over `h⁻¹ W`, with
transition functions `N_h(e_W' / e_W)`. -/
noncomputable def normBundle
    (hL : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ Nonempty (L.Trivialization (h ⁻¹ᵁ W))) :
    X.LineBundle where
  ι := NormIndex h L
  U p := p.1
  iSup_eq_top := top_le_iff.mp fun x _ ↦ by
    obtain ⟨W, hxW, ⟨τ⟩⟩ := hL x
    exact Opens.mem_iSup.mpr ⟨⟨W, τ⟩, hxW⟩
  g := normTrans
  cocycle p q r := by
    rw [coe_normTrans, coe_normTrans, coe_normTrans, ← h.norm_res, ← h.norm_res, ← h.norm_res,
      ← map_mul, NormIndex.coordOn_res, NormIndex.coordOn_res, NormIndex.coordOn_res]
    exact congrArg _ (NormIndex.ratioOn_mul _ _ _ _ _ _)

end NormBundle

section NormSections

variable {X' : Scheme.{u}} {h : X' ⟶ X} [IsFinite h] [Flat h] [LocallyOfFinitePresentation h]
  {L : X'.LineBundle} {hL : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ Nonempty (L.Trivialization (h ⁻¹ᵁ W))}

variable (hL) in
/-- The norm `N_h(s)` of a section `s` of `L^{⊗n}` over `h⁻¹ V`: the section of `N_h(L)^{⊗n}` over
`V` whose coordinate with respect to `N_h(e_W)` is the norm of the coordinate of `s` with respect
to `e_W`. -/
noncomputable def normFam {V : X.Opens} {n : ℕ} {s : L.Fam (h ⁻¹ᵁ V)}
    (hs : L.IsSection n (h ⁻¹ᵁ V) s) : (normBundle h L hL).Fam V :=
  fun p ↦ h.norm (V ⊓ p.1)
    (p.coordOn (h.preimage_mono inf_le_right) (h.preimage_mono inf_le_left) hs)

lemma norm_coordOn_res {V : X.Opens} {n : ℕ} {s : L.Fam (h ⁻¹ᵁ V)}
    (hs : L.IsSection n (h ⁻¹ᵁ V) s) (p q : NormIndex h L) :
    X.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
        V ⊓ (p.1 ⊓ q.1) ≤ V ⊓ p.1)).op
      (h.norm (V ⊓ p.1) (p.coordOn (h.preimage_mono inf_le_right)
        (h.preimage_mono inf_le_left) hs)) =
    X.presheaf.map (homOfLE (inf_le_right : V ⊓ (p.1 ⊓ q.1) ≤ p.1 ⊓ q.1)).op
        (h.norm (p.1 ⊓ q.1) (p.ratioOn q (h.preimage_mono inf_le_left)
          (h.preimage_mono inf_le_right)) ^ n) *
      X.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          V ⊓ (p.1 ⊓ q.1) ≤ V ⊓ q.1)).op
        (h.norm (V ⊓ q.1) (q.coordOn (h.preimage_mono inf_le_right)
          (h.preimage_mono inf_le_left) hs)) := by
  rw [← map_pow, ← h.norm_res, ← h.norm_res, ← h.norm_res, ← map_mul, map_pow,
    NormIndex.coordOn_res, NormIndex.coordOn_res, NormIndex.coordOn_res]
  exact congrArg _ (NormIndex.coordOn_eq_mul _ _ _ _ _ _)

set_option backward.isDefEq.respectTransparency false in
lemma isSection_normFam {V : X.Opens} {n : ℕ} {s : L.Fam (h ⁻¹ᵁ V)}
    (hs : L.IsSection n (h ⁻¹ᵁ V) s) : (normBundle h L hL).IsSection n V (normFam hL hs) := by
  intro p q
  rw [trans_natCast]
  exact norm_coordOn_res hs p q

set_option backward.isDefEq.respectTransparency false in
/-- `N_h(s)` does not vanish at `x ∈ V` iff `s` does not vanish at any point over `x`. -/
lemma mem_famLocus_normFam {V : X.Opens} {n : ℕ} {s : L.Fam (h ⁻¹ᵁ V)}
    (hs : L.IsSection n (h ⁻¹ᵁ V) s) {x : X} :
    x ∈ (normBundle h L hL).famLocus V (normFam hL hs) ↔
      x ∈ V ∧ ∀ y, h y = x → y ∈ L.famLocus (h ⁻¹ᵁ V) s := by
  have hcomp (p : NormIndex h L) (hx : x ∈ V ⊓ p.1) :
      x ∈ X.basicOpen (normFam hL hs p) ↔ ∀ y, h y = x → y ∈ L.famLocus (h ⁻¹ᵁ V) s := by
    rw [normFam, h.mem_basicOpen_norm_iff _ hx]
    refine forall₂_congr fun y hy ↦ ?_
    rw [NormIndex.coordOn, Trivialization.basicOpen_coord, famLocus_famRes]
    have : y ∈ h ⁻¹ᵁ (V ⊓ p.1) := show h y ∈ V ⊓ p.1 from hy ▸ hx
    exact ⟨fun h' ↦ h'.2, fun h' ↦ ⟨this, h'⟩⟩
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := Opens.mem_iSup.mp hx
    have hxp : x ∈ V ⊓ p.1 := X.basicOpen_le _ hp
    exact ⟨hxp.1, (hcomp p hxp).mp hp⟩
  · rintro ⟨hxV, hy⟩
    obtain ⟨W, hxW, ⟨τ⟩⟩ := hL x
    exact Opens.mem_iSup.mpr ⟨⟨W, τ⟩, (hcomp ⟨W, τ⟩ ⟨hxV, hxW⟩).mpr hy⟩

set_option backward.isDefEq.respectTransparency false in
/-- EGA II 6.6: let `h : X' ⟶ X` be finite, locally free and surjective, and `V` a quasi-compact
quasi-separated open of `X`. If `L` is ample over `h⁻¹ V`, then its norm `N_h(L)` is ample over
`V`: a point `x ∈ V` and an affine neighbourhood `W₀ ⊆ V` being given, there is a section `s` of
some `L^{⊗d}` over `h⁻¹ V` not vanishing on the fibre of `x`, with `X'_s ⊆ h⁻¹ W₀`; then `N_h(s)`
does not vanish at `x`, and `X_{N_h(s)} ⊆ W₀` is quasi-compact, hence quasi-affine. -/
theorem isAmple_pullback_normBundle [Surjective h] {V : X.Opens} [CompactSpace V]
    [QuasiSeparatedSpace V] (hamp : (L.pullback (h ⁻¹ᵁ V).ι).IsAmple) :
    ((normBundle h L hL).pullback V.ι).IsAmple := by
  classical
  refine isAmple_pullback_of_forall_exists fun x hxV ↦ ?_
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hxW₀, hW₀V⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hfin : (h ⁻¹' {x}).Finite := h.finite_preimage_singleton x
  have hmem (y : X') : y ∈ hfin.toFinset ↔ h y = x := by simp
  obtain ⟨d, hd, s, hs, hsF, hsO⟩ := exists_famLocus_le_of_isAmple_pullback hamp hfin.toFinset
    (O := h ⁻¹ᵁ W₀) (fun y hy ↦ show h y ∈ W₀ from ((hmem y).mp hy) ▸ hxW₀)
    (h.preimage_mono hW₀V)
  refine ⟨d, hd, normFam hL hs, isSection_normFam hs,
    (mem_famLocus_normFam hs).mpr ⟨hxV, fun y hy ↦ hsF y ((hmem y).mpr hy)⟩, ?_⟩
  have hle : (normBundle h L hL).famLocus V (normFam hL hs) ≤ W₀ := fun z hz ↦ by
    obtain ⟨-, hz'⟩ := (mem_famLocus_normFam hs).mp hz
    obtain ⟨y, rfl⟩ := h.surjective z
    exact hsO (hz' y rfl)
  have hc : IsCompact ((normBundle h L hL).famLocus V (normFam hL hs) : Set X) :=
    isCompact_famLocus (isCompact_iff_compactSpace.mpr ‹CompactSpace V›) (isSection_normFam hs)
  have : CompactSpace ((normBundle h L hL).famLocus V (normFam hL hs)) :=
    isCompact_iff_compactSpace.mp hc
  have : IsAffine W₀ := hW₀
  exact .of_isImmersion (X.homOfLE hle)

end NormSections

section Relative

variable {X' S : Scheme.{u}} (h : X' ⟶ X) [IsFinite h] [Flat h] [LocallyOfFinitePresentation h]
  [Surjective h] (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]

set_option backward.isDefEq.respectTransparency false in
/-- EGA II 6.6: let `h : X' ⟶ X` be finite, locally free and surjective, and `f : X ⟶ S`
quasi-compact and quasi-separated. If a line bundle `L` on `X'` is ample relative to `h ≫ f`,
its norm `N_h(L)` is ample relative to `f`. -/
theorem IsRelativelyAmple.exists_of_isFinite {L : X'.LineBundle}
    (hL : L.IsRelativelyAmple (h ≫ f)) : ∃ N : X.LineBundle, N.IsRelativelyAmple f := by
  classical
  have htriv (x : X) : ∃ W : X.Opens, x ∈ W ∧ Nonempty (L.Trivialization (h ⁻¹ᵁ W)) := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    have hfin : (h ⁻¹' {x}).Finite := h.finite_preimage_singleton x
    let U := (h ≫ f) ⁻¹ᵁ V
    have hFU (y : X') (hy : h y = x) : y ∈ U := show f (h y) ∈ V from hy ▸ hxV
    obtain ⟨A, hA, hFA⟩ := (hL.2 V hV).exists_isAffineOpen_of_finite
      (hfin.toFinset.subtype (· ∈ U))
    refine exists_trivialization_preimage h x (U := U.ι ''ᵁ A)
      (U.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hA) fun y hy ↦ ?_
    refine (Scheme.Hom.apply_mem_image_iff U.ι (x := ⟨y, hFU y hy⟩)).mpr ?_
    exact hFA _ (Finset.mem_subtype.mpr (by simpa using hy))
  refine ⟨normBundle h L htriv, inferInstance, fun V hV ↦ ?_⟩
  have : CompactSpace (f ⁻¹ᵁ V) :=
    isCompact_iff_compactSpace.mp (f.isCompact_preimage hV.isCompact)
  have : QuasiSeparatedSpace (f ⁻¹ᵁ V) := (isQuasiSeparated_iff_quasiSeparatedSpace _
    (f ⁻¹ᵁ V).isOpen).mp (f.isQuasiSeparated_preimage hV.isQuasiSeparated)
  refine isAmple_pullback_normBundle ?_
  have := hL.2 V hV
  rwa [Scheme.Hom.comp_preimage] at this

/-- EGA II 6.6.4: let `h : X' ⟶ X` be finite, locally free and surjective, and `f : X ⟶ S` of
finite type and quasi-separated. If `h ≫ f` is quasi-projective, so is `f`: the norm of a line
bundle on `X'` ample relative to `h ≫ f` is ample relative to `f`. -/
theorem _root_.AlgebraicGeometry.IsQuasiProjective.of_isFinite_comp [LocallyOfFiniteType f]
    [IsQuasiProjective (h ≫ f)] : IsQuasiProjective f := by
  obtain ⟨L, hL⟩ := IsQuasiProjective.exists_isRelativelyAmple (f := h ≫ f)
  exact ⟨inferInstance, inferInstance, IsRelativelyAmple.exists_of_isFinite h f hL⟩

end Relative

end Scheme.LineBundle

end AlgebraicGeometry
