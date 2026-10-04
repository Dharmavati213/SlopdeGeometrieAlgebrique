/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Projective.ProjectiveSpaceHom
import SGA.Foundations.Picard.Basic

/-!
# Quasi-projective morphisms over an affine base map affinely to projective space

Let `f : X ⟶ S` be quasi-projective (`IsQuasiProjective f`, a relatively ample line bundle) with
`S` affine. Then `f` factors as an affine morphism `X ⟶ ℙ(σ; S)` followed by the projection, for
some finite `σ` (`IsQuasiProjective.exists_isAffineHom_projectiveSpace`; EGA II 4.5.2, 5.3.2).
Conversely an affine morphism into `ℙ(σ; S)` gives quasi-projectivity
(`IsQuasiProjective.comp_of_isAffineHom`), so over an affine base, quasi-projective means "admits
an affine morphism into some `ℙ(σ; S)` over `S`". The advantage of the morphism over the line
bundle is that morphisms of schemes of finite presentation spread out over limits (EGA IV 8.8.2),
which is how XI.1.4 descends quasi-projectivity to a countable subfield.

The proof: an ample `L` has finitely many sections `sⱼ` of powers `L^{⊗nⱼ}` whose non-vanishing
loci are affine and cover `X`; replacing `sⱼ` by `sⱼ^{N / nⱼ}`, `N = ∏ nⱼ`, they become sections of
the single line bundle `L^{⊗N}`, and the morphism they define (`ProjectiveSpace.homOfSections`)
has inverse images of the standard affine opens `D₊(xⱼ)` equal to the affine `X_{sⱼ}`.

## Main definitions and results

* `Scheme.LineBundle.sectionsPow`: a section of `L^{⊗n}` as a section of degree one of the power
  `L.pow n` (`Scheme.LineBundle.pow`, from `SGA.Foundations.Picard.Basic`);
  `Scheme.LineBundle.sections.pow`: powers of sections.
* `Scheme.LineBundle.IsAmple.exists_finite_sections_pow`: an ample line bundle has a power with
  finitely many sections of degree one whose non-vanishing loci are affine and cover `X`.
* `IsQuasiProjective.exists_isAffineHom_projectiveSpace`, and for proper `f` its finite form
  `IsQuasiProjective.exists_isFinite_projectiveSpace`.

## References

* [EGA II, 4.5.2, 5.3.2][EGA2]
-/

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme.LineBundle

variable {X : Scheme.{u}} (L : X.LineBundle)

/-- A section of `L^{⊗n}` is a section of degree one of the power `L.pow n`
(`Scheme.LineBundle.pow`, `SGA.Foundations.Picard.Basic`). -/
def sectionsPow {n : ℕ} (s : L.sections n) : (L.pow n).sections 1 :=
  ⟨s.1, fun i j ↦ by
    have hg : Units.val (L.g i j ^ (n : ℤ)) ^ 1 = Units.val (L.g i j) ^ n := by
      rw [_root_.pow_one, zpow_natCast, Units.val_pow_eq_pow_val]
    exact (s.2 i j).trans (congrArg (· * _) hg.symm)⟩

@[simp]
lemma nonvanishingLocus_sectionsPow {n : ℕ} (s : L.sections n) :
    (L.pow n).nonvanishingLocus (L.sectionsPow s) = L.nonvanishingLocus s :=
  rfl

variable {L} in
/-- The `m`-th power of a section of `L^{⊗n}`, a section of `L^{⊗k}` for `k = n m`. -/
def sections.pow {n : ℕ} (s : L.sections n) (m k : ℕ) (hk : n * m = k) : L.sections k :=
  ⟨fun i ↦ s.1 i ^ m, fun i j ↦ by rw [map_pow, s.2 i j, mul_pow, ← pow_mul, hk, map_pow]⟩

@[simp]
lemma nonvanishingLocus_sections_pow {n : ℕ} (s : L.sections n) {m k : ℕ} (hk : n * m = k)
    (hm : 0 < m) : L.nonvanishingLocus (s.pow m k hk) = L.nonvanishingLocus s := by
  simp only [nonvanishingLocus, sections.pow, Scheme.basicOpen_pow _ _ hm]

/-- EGA II 4.5.2: an ample line bundle has a power `L^{⊗N}` with finitely many sections of degree
one whose non-vanishing loci are affine and cover `X`. -/
theorem IsAmple.exists_finite_sections_pow (hL : L.IsAmple) :
    ∃ (σ : Type u) (_ : Finite σ) (N : ℕ) (s : σ → (L.pow (N : ℤ)).sections 1),
      (∀ x, ∃ i, x ∈ (L.pow (N : ℤ)).nonvanishingLocus (s i)) ∧
        ∀ i, IsAffineOpen ((L.pow (N : ℤ)).nonvanishingLocus (s i)) := by
  classical
  have := hL.1
  choose n hn s hxs hs using hL.2
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (L.nonvanishingLocus (s x) : Set X)) (fun x ↦ (L.nonvanishingLocus (s x)).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxs x⟩)
  let N := ∏ x ∈ t, n x
  have hdvd (x : t) : n x ∣ N := Finset.dvd_prod_of_mem _ x.2
  have hN : 0 < N := Finset.prod_pos fun x _ ↦ hn x
  have hm (x : t) : 0 < N / n x := Nat.div_pos (Nat.le_of_dvd hN (hdvd x)) (hn x)
  let s' (x : t) : (L.pow (N : ℤ)).sections 1 :=
    L.sectionsPow ((s x).pow (N / n x) N (Nat.mul_div_cancel' (hdvd x)))
  have hloc (x : t) : (L.pow (N : ℤ)).nonvanishingLocus (s' x) = L.nonvanishingLocus (s x) := by
    rw [nonvanishingLocus_sectionsPow, nonvanishingLocus_sections_pow _ _ _ (hm x)]
  refine ⟨t, inferInstance, N, s', fun x ↦ ?_, fun x ↦ hloc x ▸ hs x⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact ⟨⟨y, hy⟩, by rw [hloc]; exact hxy⟩

end Scheme.LineBundle

/-- **A quasi-projective morphism to an affine scheme factors through an affine morphism into
projective space** (EGA II 4.5.2, 5.3.2): for `f : X ⟶ S` quasi-projective with `S`
affine there are a finite type `σ` and an affine morphism `φ : X ⟶ ℙ(σ; S)` over `S`. The
converse is `IsQuasiProjective.comp_of_isAffineHom`. -/
theorem IsQuasiProjective.exists_isAffineHom_projectiveSpace {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsQuasiProjective f] :
    ∃ (σ : Type u) (_ : Finite σ) (φ : X ⟶ ℙ(σ; S)), IsAffineHom φ ∧ φ ≫ ℙ(σ; S) ↘ S = f := by
  obtain ⟨L, hL⟩ := IsQuasiProjective.exists_isRelativelyAmple (f := f)
  have hamp : (L.pullback (⊤ : X.Opens).ι).IsAmple := by
    have := hL.2 ⊤ (isAffineOpen_top S)
    rwa [Scheme.Hom.preimage_top] at this
  obtain ⟨σ, _, N, s, hs, haff⟩ := hamp.exists_finite_sections_pow
  let ψ := ProjectiveSpace.homOfSections ((⊤ : X.Opens).ι ≫ f) _ s hs
  have hψ : IsAffineHom ψ := by
    refine isAffineHom_of_forall_exists_isAffineOpen (f := ψ) fun y ↦ ?_
    obtain ⟨i, hi⟩ : ∃ i, y ∈ ProjectiveSpace.basicOpen S i := by
      simpa using (ProjectiveSpace.iSup_basicOpen (σ := σ) S).ge (Set.mem_univ y)
    refine ⟨_, hi, ?_, ?_⟩
    · have : IsAffine (ProjectiveSpace.basicOpen S i) :=
        isAffine_of_isAffineHom ((ProjectiveSpace.basicOpen S i).ι ≫ ℙ(σ; S) ↘ S)
      exact this
    · rw [ProjectiveSpace.homOfSections_preimage_basicOpen]
      exact haff i
  refine ⟨σ, inferInstance, X.topIso.inv ≫ ψ, inferInstance, ?_⟩
  rw [Category.assoc, ProjectiveSpace.homOfSections_over, ← Category.assoc, Scheme.toIso_inv_ι,
    Category.id_comp]

/-- A proper quasi-projective morphism to an affine scheme factors through a **finite** morphism
into projective space: the affine morphism of
`IsQuasiProjective.exists_isAffineHom_projectiveSpace` is proper (`f` is proper and `ℙ(σ; S)` is
separated over `S`), and proper affine morphisms are finite. Coherent cohomology of `X` is then
that of a coherent sheaf on `ℙ(σ; S)` (the direct image). -/
theorem IsQuasiProjective.exists_isFinite_projectiveSpace {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsQuasiProjective f] [IsProper f] :
    ∃ (σ : Type u) (_ : Finite σ) (φ : X ⟶ ℙ(σ; S)), IsFinite φ ∧ φ ≫ ℙ(σ; S) ↘ S = f := by
  obtain ⟨σ, _, φ, hφ, hφf⟩ := IsQuasiProjective.exists_isAffineHom_projectiveSpace f
  have : IsProper (φ ≫ ℙ(σ; S) ↘ S) := by rw [hφf]; infer_instance
  have : IsProper φ := IsProper.of_comp φ (ℙ(σ; S) ↘ S)
  exact ⟨σ, inferInstance, φ, IsFinite.iff_isProper_and_isAffineHom.mpr ⟨this, hφ⟩, hφf⟩

end AlgebraicGeometry
