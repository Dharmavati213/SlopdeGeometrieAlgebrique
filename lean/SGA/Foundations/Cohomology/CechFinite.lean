/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.ProjectiveSpaceTwist
import SGA.Foundations.Cohomology.AffineOpenVanishing
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Data.Int.Interval

/-!
# Finiteness of the cohomology of `𝒪(d)` on projective space

For a noetherian ring `A`, every cohomology module `Hᵖ(ℙʳ_A, 𝒪(d))` is a finitely generated
`Γ(ℙʳ_A, 𝒪) = A`-module (Serre, FAC §62; EGA III 2.1.12; Hartshorne III.5.1). The interesting
cases are `p = 0` (homogeneous polynomials of degree `d`) and `p = r`, `d ≤ -r - 1` (spanned by
the classes of the Laurent monomials `x^μ` with all `μᵢ < 0` and `∑ μᵢ = d`).

The proof goes through Čech cohomology for the standard cover (Leray's theorem,
`Scheme.Modules.cechHomologyLinearEquiv`): the Čech cochains of `𝒪(d)` embed into families of
Laurent polynomials; every cocycle of positive degree is cohomologous to one whose Laurent
monomials have all exponents negative (the cone construction of
`SGA.Foundations.Cohomology.ProjectiveSpaceTwist`), and there are finitely many such monomials of a
given degree; a degree-`0` cocycle only involves the finitely many monomials which are global
sections. As `A` is noetherian, the cocycles supported on a finite set of monomials form a finitely
generated `A`-module, and `A` acts on Čech cohomology through the constants of `Γ(ℙʳ_A, 𝒪)`.

The general principle is `CohomologyAux.finite_homology_of_generators`: the homology of a cochain
complex of abelian groups with an action of a ring `R` is a finitely generated `R`-module as soon
as finitely many cocycles generate all cocycles modulo coboundaries.
-/

universe v u

open CategoryTheory Limits TopologicalSpace Opposite MvPolynomial TopCat.Presheaf

namespace AlgebraicGeometry.CohomologyAux

open HomologicalComplex in
/-- **Finite generation of homology**: let `K` be a cochain complex of abelian groups on whose
`n`-th homology a ring `R` acts through endomorphisms `ρ a` of `K`. If finitely many `n`-cocycles
`zⱼ` generate all `n`-cocycles modulo coboundaries, i.e. every cocycle is `d b + ∑ⱼ (ρ aⱼ) zⱼ`, then
`Hⁿ(K)` is a finitely generated `R`-module. -/
theorem finite_homology_of_generators {R : Type*} [Semiring R]
    (K : CochainComplex AddCommGrpCat.{u} ℕ) (i n : ℕ) [Module R (K.homology n)]
    (ρ : R → (K ⟶ K)) (hρ : ∀ (a : R) (h : K.homology n), a • h = homologyMap (ρ a) n h)
    {k : ℕ} (z : Fin k → K.X n) (hz : ∀ j, K.d n (n + 1) (z j) = 0)
    (hgen : ∀ c : K.X n, K.d n (n + 1) c = 0 →
      ∃ (b : K.X i) (a : Fin k → R), c = K.d i n b + ∑ j, (ρ (a j)).f n (z j)) :
    Module.Finite R (K.homology n) := by
  classical
  have hnext : (ComplexShape.up ℕ).next n = n + 1 := CochainComplex.next ℕ n
  have hlift : ∀ c : K.X n, K.d n (n + 1) c = 0 → ∃ w : K.cycles n, K.iCycles n w = c := by
    intro c hc
    refine ⟨(K.sc n).abCyclesIso.inv ⟨c, ?_⟩, (K.sc n).abCyclesIso_inv_apply_iCycles _⟩
    change K.d n ((ComplexShape.up ℕ).next n) c = 0
    rw [hnext]
    exact hc
  choose w hw using fun j ↦ hlift (z j) (hz j)
  have hπ : Function.Surjective (K.homologyπ n) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  have hi : Function.Injective (K.iCycles n) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  refine ⟨⟨Finset.univ.image fun j ↦ K.homologyπ n (w j), ?_⟩⟩
  rw [eq_top_iff]
  rintro h -
  obtain ⟨v, rfl⟩ := hπ h
  have hv : K.d n (n + 1) (K.iCycles n v) = 0 := by
    rw [← ConcreteCategory.comp_apply, K.iCycles_d]
    rfl
  obtain ⟨b, a, hab⟩ := hgen _ hv
  have hv' : v = K.toCycles i n b + ∑ j, cyclesMap (ρ (a j)) n (w j) := by
    apply hi
    rw [map_add, map_sum, hab]
    congr 1
    · rw [← ConcreteCategory.comp_apply, K.toCycles_i]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply, hw]
  rw [hv', map_add, map_sum, ← ConcreteCategory.comp_apply, K.toCycles_comp_homologyπ]
  change 0 + _ ∈ _
  rw [zero_add]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← homologyπ_naturality, ConcreteCategory.comp_apply, ← hρ]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

end AlgebraicGeometry.CohomologyAux

namespace AlgebraicGeometry.projectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ : Type v} {A : Type u} [CommRing A] [Fintype σ] [DecidableEq σ] [Nonempty σ]

/-! ## Constants act on Laurent coefficients by scalars -/

section Scalars

/-- Every `a ∈ A` is the Laurent image of a global function (the constant `a`). -/
lemma exists_sectionToLaurent_top_eq (a : A) :
    ∃ c : Γ(Proj (homogeneousSubmodule σ A), ⊤),
      sectionToLaurent σ A ⊤ le_top c = AddMonoidAlgebra.single 0 a := by
  refine ⟨(Proj.toSpecZero (homogeneousSubmodule σ A)).appTop
    ((Scheme.ΓSpecIso _).inv (algebraMap A (homogeneousSubmodule σ A 0) a)), ?_⟩
  rw [sectionToLaurent_appTop]
  have e : (Scheme.ΓSpecIso (CommRingCat.of (homogeneousSubmodule σ A 0))).hom
      ((Scheme.ΓSpecIso _).inv (algebraMap A (homogeneousSubmodule σ A 0) a)) =
        algebraMap A (homogeneousSubmodule σ A 0) a :=
    Iso.inv_hom_id_apply _ _
  rw [e]
  change toLaurent σ A (algebraMap A (MvPolynomial σ A) a) = _
  rw [MvPolynomial.algebraMap_eq, C_apply, toLaurent_monomial, map_zero]

lemma twistToLaurent_smul (d : ℤ)
    {V : (Proj (homogeneousSubmodule σ A)).Opens} (hV : torus σ A ≤ V)
    (c : Γ(Proj (homogeneousSubmodule σ A), ⊤))
    (s : (twistingBundle σ A).sectionsAddSubgroup d V) :
    twistToLaurent d V hV ((Proj (homogeneousSubmodule σ A)).presheaf.map
      (homOfLE (le_top : V ≤ ⊤)).op c • s) =
        sectionToLaurent σ A ⊤ le_top c * twistToLaurent d V hV s := by
  have h (j : σ) : sectionToLaurent σ A (V ⊓ stdCover σ A j) (le_inf hV (torus_le_stdCover _))
      (component d V j ((Proj (homogeneousSubmodule σ A)).presheaf.map
        (homOfLE (le_top : V ≤ ⊤)).op c • s)) =
      sectionToLaurent σ A ⊤ le_top c * sectionToLaurent σ A (V ⊓ stdCover σ A j)
        (le_inf hV (torus_le_stdCover _)) (component d V j s) := by
    change sectionToLaurent σ A (V ⊓ stdCover σ A j) (le_inf hV (torus_le_stdCover _))
        ((Proj (homogeneousSubmodule σ A)).presheaf.map
          (homOfLE (inf_le_left : V ⊓ stdCover σ A j ≤ V)).op
          ((Proj (homogeneousSubmodule σ A)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op c) *
            component d V j s) = _
    rw [map_mul, CohomologyAux.presheaf_map_map, sectionToLaurent_map le_top]
  rw [twistToLaurent_eq d hV _ (Classical.arbitrary σ),
    twistToLaurent_eq d hV s (Classical.arbitrary σ), h]
  ring

/-- A constant `a` acts on the Laurent coefficients of Čech cochains of `𝒪(d)` as the scalar
`a`. -/
lemma twistCechEmbedding_smulHom (d : ℤ) {m : ℕ} (x : Fin (m + 1) → σ)
    (c : Γ(Proj (homogeneousSubmodule σ A), ⊤)) {a : A}
    (hc : sectionToLaurent σ A ⊤ le_top c = AddMonoidAlgebra.single 0 a)
    (s : (twist σ A d).toAbSheaf.obj.obj (op (cechOpen (stdCover σ A) x))) :
    twistCechEmbedding d x (((twist σ A d).smulHom c).hom.app _ s) =
      a • twistCechEmbedding d x s := by
  classical
  change AddMonoidAlgebra.coeff (twistToLaurent d _ (torus_le_cechOpen x)
      ((Proj (homogeneousSubmodule σ A)).presheaf.map
        (homOfLE (le_top : cechOpen (stdCover σ A) x ≤ ⊤)).op c •
        @id ((twistingBundle σ A).sectionsAddSubgroup d (cechOpen (stdCover σ A) x)) s)) =
    a • AddMonoidAlgebra.coeff (twistToLaurent d _ (torus_le_cechOpen x)
      (@id ((twistingBundle σ A).sectionsAddSubgroup d (cechOpen (stdCover σ A) x)) s))
  rw [twistToLaurent_smul, hc]
  ext μ
  rw [AddMonoidAlgebra.coeff_single_zero_mul, Finsupp.smul_apply, smul_eq_mul]

end Scalars

/-! ## Finiteness of the relevant sets of monomials -/

section Monomials

variable (σ) in
/-- The exponents of degree `d` all of whose entries are negative. -/
def negMonomials (d : ℤ) : Set (σ → ℤ) :=
  {μ | ∑ i, μ i = d ∧ ∀ i, μ i < 0}

variable (σ) in
/-- The exponents of degree `d` whose monomials are sections of `𝒪(d)` over every `D₊(xⱼ)`. -/
def globalMonomials (d : ℤ) : Set (σ → ℤ) :=
  {μ | ∀ j, μ ∈ monomialSetDeg σ d {j}}

omit [DecidableEq σ] [Nonempty σ] in
lemma finite_negMonomials (d : ℤ) : (negMonomials σ d).Finite := by
  classical
  refine (Set.Finite.pi (t := fun _ : σ ↦ Set.Icc d (-1)) fun _ ↦ Set.finite_Icc _ _).subset ?_
  rintro μ ⟨hsum, hneg⟩ i -
  refine ⟨?_, by linarith [hneg i]⟩
  rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : ∑ j ∈ Finset.univ.erase i, μ j ≤ 0 := Finset.sum_nonpos fun j _ ↦ (hneg j).le
  linarith

omit [DecidableEq σ] [Nonempty σ] in
lemma finite_globalMonomials (d : ℤ) : (globalMonomials σ d).Finite := by
  classical
  refine (Set.Finite.pi (t := fun _ : σ ↦ Set.Icc (min d 0) (max d 0))
    fun _ ↦ Set.finite_Icc _ _).subset ?_
  intro μ hμ i _
  by_cases hcard : 2 ≤ Fintype.card σ
  · obtain ⟨hsum, hnn⟩ := (forall_mem_monomialSetDeg_singleton_iff hcard d μ).mp hμ
    have : μ i ≤ d := by
      rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have : 0 ≤ ∑ j ∈ Finset.univ.erase i, μ j := Finset.sum_nonneg fun j _ ↦ hnn j
      linarith
    exact ⟨min_le_right _ _ |>.trans (hnn i), this.trans (le_max_left _ _)⟩
  · have : Subsingleton σ := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hsum := (hμ i).1
    rw [Finset.sum_eq_single i (fun b _ hb ↦ absurd (Subsingleton.elim b i) hb) (by simp)] at hsum
    rw [hsum]
    exact ⟨min_le_left _ _, le_max_left _ _⟩

end Monomials

/-! ## Generators of the Čech cocycles -/

section Generators

variable [IsNoetherianRing A]

/-- For a finite set `T` of exponents, finitely many Čech `n`-cocycles `zⱼ` of `𝒪(d)` generate
over `Γ(𝒪)` all the `n`-cocycles whose Laurent coefficients are supported in `T`. -/
lemma exists_cocycle_generators (d : ℤ) (n : ℕ) {T : Set (σ → ℤ)} (hT : T.Finite) :
    ∃ (k : ℕ) (z : Fin k → CechCochain (stdCover σ A) (twist σ A d).toAbSheaf.obj n),
      (∀ j, cechD _ _ n (z j) = 0) ∧
      ∀ c : CechCochain (stdCover σ A) (twist σ A d).toAbSheaf.obj n, cechD _ _ n c = 0 →
        (∀ x, ↑(twistCechEmbedding d x (c x)).support ⊆ T) →
        ∃ a : Fin k → Γ(Proj (homogeneousSubmodule σ A), ⊤),
          c = ∑ j, cechCochainMap _ ((twist σ A d).smulHom (a j)).hom n (z j) := by
  classical
  let W : Submodule A ((Fin (n + 1) → σ) → ((σ → ℤ) →₀ A)) :=
    { carrier := {f | (∀ x, ↑(f x).support ⊆ T) ∧
        (∀ x, ↑(f x).support ⊆ monomialSetDeg σ d (Finset.univ.image x)) ∧ cechDConst n f = 0}
      add_mem' := fun {f g} hf hg ↦ ⟨fun x μ hμ ↦ by
          rcases Finset.mem_union.mp (Finsupp.support_add hμ) with h | h
          · exact hf.1 x h
          · exact hg.1 x h,
        fun x μ hμ ↦ by
          rcases Finset.mem_union.mp (Finsupp.support_add hμ) with h | h
          · exact hf.2.1 x h
          · exact hg.2.1 x h,
        by rw [cechDConst_add, hf.2.2, hg.2.2, add_zero]⟩
      zero_mem' := ⟨fun x ↦ by
          rw [Pi.zero_apply, Finsupp.support_zero, Finset.coe_empty]
          exact Set.empty_subset _, fun x ↦ by
          rw [Pi.zero_apply, Finsupp.support_zero, Finset.coe_empty]
          exact Set.empty_subset _, by
        funext x
        simp [cechDConst]⟩
      smul_mem' := fun a f hf ↦ ⟨fun x μ hμ ↦ hf.1 x (Finsupp.support_smul hμ),
        fun x μ hμ ↦ hf.2.1 x (Finsupp.support_smul hμ), by
          have h := cechDConst_map (DistribSMul.toAddMonoidHom ((σ → ℤ) →₀ A) a) n f
          simp only [DistribSMul.toAddMonoidHom_apply] at h
          change cechDConst n (fun x ↦ a • f x) = 0
          rw [h, hf.2.2]
          funext x
          simp⟩ }
  -- `W` is contained in a finitely generated submodule
  let Tf := hT.toFinset
  let G : ((Fin (n + 1) → σ) → (Tf → A)) →ₗ[A] ((Fin (n + 1) → σ) → ((σ → ℤ) →₀ A)) :=
    LinearMap.pi fun x ↦ ∑ μ : Tf, (Finsupp.lsingle μ.1) ∘ₗ (LinearMap.proj μ) ∘ₗ
      (LinearMap.proj x)
  have hG (g : (Fin (n + 1) → σ) → (Tf → A)) (x : Fin (n + 1) → σ) :
      G g x = ∑ μ : Tf, Finsupp.single μ.1 (g x μ) := by
    rw [LinearMap.pi_apply, LinearMap.sum_apply]
    rfl
  have hWG : W ≤ LinearMap.range G := by
    intro f hf
    refine ⟨fun x μ ↦ f x μ.1, funext fun x ↦ ?_⟩
    rw [hG, Finset.sum_coe_sort Tf fun μ ↦ Finsupp.single μ (f x μ)]
    conv_rhs => rw [← Finsupp.sum_single (f x)]
    exact (Finsupp.sum_of_support_subset (f x) (fun μ hμ ↦ hT.mem_toFinset.mpr (hf.1 x hμ))
      Finsupp.single fun _ _ ↦ Finsupp.single_zero _).symm
  have hWfg : W.FG := Submodule.FG.of_le (by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map G) hWG
  obtain ⟨k, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hWfg
  have hfW (j : Fin k) : f j ∈ W := hf ▸ Submodule.subset_span ⟨j, rfl⟩
  -- lift the generators to cochains
  have hrange (j : Fin k) (x : Fin (n + 1) → σ) : f j x ∈ Set.range (twistCechEmbedding d x) := by
    rw [range_twistCechEmbedding]
    exact (hfW j).2.1 x
  choose z hz using hrange
  have hΦ : ∀ {m m' : ℕ} (x : Fin (m + 1) → σ) (y : Fin (m' + 1) → σ)
      (h : cechOpen (stdCover σ A) x ≤ cechOpen (stdCover σ A) y)
      (s : (twist σ A d).toAbSheaf.obj.obj (op (cechOpen (stdCover σ A) y))),
      twistCechEmbedding d x ((twist σ A d).toAbSheaf.obj.map (homOfLE h).op s) =
        twistCechEmbedding d y s := fun x y h s ↦ congrArg AddMonoidAlgebra.coeff
    (twistToLaurent_resHom d (torus_le_cechOpen y) (torus_le_cechOpen x) h s)
  have hinj {m : ℕ} (x : Fin (m + 1) → σ) : Function.Injective (twistCechEmbedding (A := A) d x) :=
    AddMonoidAlgebra.coeffAddEquiv.injective.comp
      (injective_twistToLaurent_of_eq d (cechOpen_stdCover x) (torus_le_cechOpen x))
  refine ⟨k, fun j x ↦ z j x, fun j ↦ funext fun x ↦ hinj x ?_, fun c hc hcT ↦ ?_⟩
  · rw [cechD_embedding _ _ _ hΦ, Pi.zero_apply, map_zero]
    change cechDConst n (fun y ↦ twistCechEmbedding d y (z j y)) x = 0
    simp only [hz]
    exact congrFun (hfW j).2.2 x
  · have hcW : (fun x ↦ twistCechEmbedding d x (c x)) ∈ W := by
      refine ⟨hcT, fun x ↦ ?_, ?_⟩
      · exact ((range_twistCechEmbedding (A := A) d x).le ⟨c x, rfl⟩ : _)
      · funext x
        rw [← cechD_embedding _ _ _ hΦ, hc]
        exact map_zero _
    rw [← hf] at hcW
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hcW
    choose e he using fun j ↦ exists_sectionToLaurent_top_eq (σ := σ) (a j)
    refine ⟨e, funext fun x ↦ hinj x ?_⟩
    rw [Finset.sum_apply, map_sum]
    have := congrFun ha x
    rw [Finset.sum_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [cechCochainMap_apply, twistCechEmbedding_smulHom d x _ (he j), hz]
    rfl

omit [IsNoetherianRing A] in
/-- Every Čech cocycle of positive degree of `𝒪(d)` is cohomologous to one whose Laurent
monomials have all exponents negative. -/
lemma exists_cechD_sub_support (d : ℤ) (p : ℕ)
    (c : CechCochain (stdCover σ A) (twist σ A d).toAbSheaf.obj (p + 1))
    (hc : cechD _ _ (p + 1) c = 0) :
    ∃ b : CechCochain (stdCover σ A) (twist σ A d).toAbSheaf.obj p, ∀ x,
      ↑(twistCechEmbedding d x ((c - cechD _ _ p b) x)).support ⊆ negMonomials σ d := by
  classical
  have hΦ : ∀ {m m' : ℕ} (x : Fin (m + 1) → σ) (y : Fin (m' + 1) → σ)
      (h : cechOpen (stdCover σ A) x ≤ cechOpen (stdCover σ A) y)
      (s : (twist σ A d).toAbSheaf.obj.obj (op (cechOpen (stdCover σ A) y))),
      twistCechEmbedding d x ((twist σ A d).toAbSheaf.obj.map (homOfLE h).op s) =
        twistCechEmbedding d y s := fun x y h s ↦ congrArg AddMonoidAlgebra.coeff
    (twistToLaurent_resHom d (torus_le_cechOpen y) (torus_le_cechOpen x) h s)
  let ĉ : (Fin (p + 2) → σ) → ((σ → ℤ) →₀ A) := fun x ↦ twistCechEmbedding d x (c x)
  have hĉ (x : Fin (p + 2) → σ) : ↑(ĉ x).support ⊆ monomialSetDeg σ d (Finset.univ.image x) := by
    exact ((range_twistCechEmbedding (A := A) d x).le ⟨c x, rfl⟩ : _)
  have hdĉ : cechDConst (p + 1) ĉ = 0 := by
    funext x
    rw [← cechD_embedding _ _ _ hΦ, hc]
    exact map_zero _
  let P : (σ → ℤ) → Prop := fun μ ↦ ∀ i, μ i < 0
  have hfilter : cechDConst (p + 1) (fun x ↦ (ĉ x).filter fun μ ↦ ¬ P μ) = 0 := by
    rw [show (fun x ↦ (ĉ x).filter fun μ ↦ ¬ P μ) =
        fun x ↦ Finsupp.filterAddHom (fun μ ↦ ¬ P μ) (ĉ x) from rfl, cechDConst_map, hdĉ]
    funext x
    simp
  obtain ⟨br, hbr, hdbr⟩ := TopCat.Presheaf.exists_cechDConst_eq_of_support
    (fun x ↦ monomialSetDeg σ d (Finset.univ.image x) ∩ {μ | ¬ ∀ i, μ i < 0}) (nonnegIndex σ)
    (nonnegIndex_mem_deg d) (fun x ↦ (ĉ x).filter fun μ ↦ ¬ P μ)
    (fun x μ hμ ↦ ⟨hĉ x (mem_support_filter.mp hμ).1, (mem_support_filter.mp hμ).2⟩) hfilter
  have hbr' (y : Fin (p + 1) → σ) : br y ∈ Set.range (twistCechEmbedding d y) := by
    rw [range_twistCechEmbedding]
    exact fun μ hμ ↦ (hbr y hμ).1
  choose b hb using hbr'
  refine ⟨b, fun x μ hμ ↦ ?_⟩
  have hx : twistCechEmbedding d x ((c - cechD _ _ p b) x) = (ĉ x).filter P := by
    rw [Pi.sub_apply, map_sub, cechD_embedding _ _ _ hΦ]
    change ĉ x - cechDConst p (fun y ↦ twistCechEmbedding d y (b y)) x = _
    simp only [hb]
    rw [hdbr, sub_eq_iff_eq_add]
    exact (Finsupp.filter_add_filter_not (ĉ x) P).symm
  rw [hx] at hμ
  exact ⟨(hĉ x (mem_support_filter.mp hμ).1).1, (mem_support_filter.mp hμ).2⟩

omit [IsNoetherianRing A] in
/-- The Laurent monomials of a Čech `0`-cocycle of `𝒪(d)` are global sections. -/
lemma support_subset_globalMonomials (d : ℤ)
    (c : CechCochain (stdCover σ A) (twist σ A d).toAbSheaf.obj 0)
    (hc : cechD _ _ 0 c = 0) (x : Fin 1 → σ) :
    ↑(twistCechEmbedding d x (c x)).support ⊆ globalMonomials σ d := by
  classical
  have hΦ : ∀ {m m' : ℕ} (x : Fin (m + 1) → σ) (y : Fin (m' + 1) → σ)
      (h : cechOpen (stdCover σ A) x ≤ cechOpen (stdCover σ A) y)
      (s : (twist σ A d).toAbSheaf.obj.obj (op (cechOpen (stdCover σ A) y))),
      twistCechEmbedding d x ((twist σ A d).toAbSheaf.obj.map (homOfLE h).op s) =
        twistCechEmbedding d y s := fun x y h s ↦ congrArg AddMonoidAlgebra.coeff
    (twistToLaurent_resHom d (torus_le_cechOpen y) (torus_le_cechOpen x) h s)
  let ĉ : (Fin 1 → σ) → ((σ → ℤ) →₀ A) := fun x ↦ twistCechEmbedding d x (c x)
  have hĉ (x : Fin 1 → σ) : ↑(ĉ x).support ⊆ monomialSetDeg σ d (Finset.univ.image x) := by
    exact ((range_twistCechEmbedding (A := A) d x).le ⟨c x, rfl⟩ : _)
  have hdĉ : cechDConst 0 ĉ = 0 := by
    funext x
    rw [← cechD_embedding _ _ _ hΦ, hc]
    exact map_zero _
  -- a `0`-cocycle is constant
  have hconst (y : Fin 1 → σ) : ĉ y = ĉ x := by
    have h := congrFun hdĉ ![x 0, y 0]
    simp only [cechDConst, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, pow_zero,
      one_smul, Fin.val_succ, zero_add, pow_one, neg_one_smul, add_zero, Pi.zero_apply,
      Fin.succAbove_zero] at h
    have e0 : (![x 0, y 0] : Fin 2 → σ) ∘ Fin.succ = y := by
      funext a
      rw [Fin.fin_one_eq_zero a]
      rfl
    have e1 : (![x 0, y 0] : Fin 2 → σ) ∘ (Fin.succ 0).succAbove = x := by
      funext a
      rw [Fin.fin_one_eq_zero a]
      rfl
    rw [e0, e1, ← sub_eq_add_neg, sub_eq_zero] at h
    exact h
  intro μ hμ j
  have h := hĉ ![j] (by rw [hconst]; exact hμ)
  have e : (Finset.univ.image (![j] : Fin 1 → σ)) = {j} := by
    ext i
    simp [eq_comm]
  rw [e] at h
  exact h

end Generators

/-! ## Finiteness of `Hᵖ(ℙʳ_A, 𝒪(d))` -/

section Finite

variable [IsNoetherianRing A]

/-- The Čech cohomology of `𝒪(d)` for the standard cover of `ℙʳ_A` is a finitely generated
`Γ(ℙʳ_A, 𝒪)`-module, for `A` noetherian. -/
theorem finite_cechHomology_twist (r : ℕ) (d : ℤ) (n : ℕ) :
    Module.Finite Γ(Proj (homogeneousSubmodule (Fin (r + 1)) A), ⊤)
      ((cechComplex (stdCover (Fin (r + 1)) A) (twist (Fin (r + 1)) A d).presheaf).homology n) := by
  let F := twist (Fin (r + 1)) A d
  let K := cechComplex (stdCover (Fin (r + 1)) A) F.presheaf
  let ρ : Γ(Proj (homogeneousSubmodule (Fin (r + 1)) A), ⊤) → (K ⟶ K) :=
    fun a ↦ cechComplexMap _ (F.smulHom a).hom
  cases n with
  | zero =>
    obtain ⟨k, z, hz, hgen⟩ := exists_cocycle_generators (σ := Fin (r + 1)) (A := A) d 0
      (finite_globalMonomials d)
    refine CohomologyAux.finite_homology_of_generators K 0 0 ρ (fun _ _ ↦ rfl) z
      (fun j ↦ (cechComplex_d_apply _ _ 0 _).trans (hz j)) fun c hc ↦ ?_
    have hc' : cechD _ _ 0 c = 0 := (cechComplex_d_apply _ _ 0 c).symm.trans hc
    obtain ⟨a, ha⟩ := hgen c hc' (support_subset_globalMonomials d c hc')
    refine ⟨0, a, ?_⟩
    rw [map_zero, zero_add, ha]
    rfl
  | succ p =>
    obtain ⟨k, z, hz, hgen⟩ := exists_cocycle_generators (σ := Fin (r + 1)) (A := A) d (p + 1)
      (finite_negMonomials d)
    refine CohomologyAux.finite_homology_of_generators K p (p + 1) ρ (fun _ _ ↦ rfl) z
      (fun j ↦ (cechComplex_d_apply _ _ (p + 1) _).trans (hz j)) fun c hc ↦ ?_
    let c' : CechCochain (stdCover (Fin (r + 1)) A) (twist (Fin (r + 1)) A d).toAbSheaf.obj
      (p + 1) := c
    have hc' : cechD _ _ (p + 1) c' = 0 := (cechComplex_d_apply _ _ (p + 1) c).symm.trans hc
    obtain ⟨b, hb⟩ := exists_cechD_sub_support d p c' hc'
    have hdc : cechD _ _ (p + 1) (c' - cechD _ _ p b) = 0 := by
      rw [map_sub, hc', cechD_cechD, sub_zero]
    obtain ⟨a, ha⟩ := hgen _ hdc hb
    have e : (K.d p (p + 1)) b = cechD _ _ p b := cechComplex_d_apply _ _ p b
    refine ⟨b, a, ?_⟩
    rw [e]
    exact sub_eq_iff_eq_add'.mp ha

/-- **Finiteness of the cohomology of `𝒪(d)`** (Serre, FAC §62; EGA III 2.1.12; Hartshorne
III.5.1): for `A` noetherian, every `Hᵖ(ℙʳ_A, 𝒪(d))` is a finitely generated module over
`Γ(ℙʳ_A, 𝒪) = A`. This includes `Hʳ(ℙʳ_A, 𝒪(d))` for `d ≤ -r - 1` (which EGA and Hartshorne compute
explicitly, as the dual of `H⁰(ℙʳ_A, 𝒪(-d-r-1))`) and `H⁰(ℙʳ_A, 𝒪(d)) = A[x₀, …, x_r]_d`. -/
theorem finite_H_twist (r : ℕ) (d : ℤ) (n : ℕ) :
    Module.Finite Γ(Proj (homogeneousSubmodule (Fin (r + 1)) A), ⊤)
      ((twist (Fin (r + 1)) A d).H n) := by
  have hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin (r + 1)),
      IsAffineOpen (cechOpen (stdCover (Fin (r + 1)) A) x) := fun x ↦ by
    rw [cechOpen_stdCover]
    exact Proj.isAffineOpen_basicOpen _ _ (prodX_mem _) (image_nonempty x).card_pos
  have := finite_cechHomology_twist (A := A) r d n
  have h := Module.Finite.equiv
    ((twist (Fin (r + 1)) A d).cechHomologyLinearEquiv (stdCover (Fin (r + 1)) A) n hU)
  rw [iSup_stdCover] at h
  exact h

end Finite

end AlgebraicGeometry.projectiveSpace
