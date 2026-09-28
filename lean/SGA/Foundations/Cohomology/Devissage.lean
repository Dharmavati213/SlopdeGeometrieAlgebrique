/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.LerayTransfer
import SGA.Foundations.Cohomology.ClosedImmersionSections
import SGA.Foundations.Projective.Chow

/-!
# Dévissage of coherent modules

The reduction steps of EGA III 3.1.2 and 3.2.1, for the property "all cohomology modules are
finitely generated over `A`" of coherent modules on a noetherian scheme `X` over `Spec A`.

* `CohomologyAux.VanishesOff M T`: the sections of `M` over opens disjoint from `T` vanish.
* `CohomologyAux.finiteCohomology_of_vanishesOff_range`: for a closed immersion `ι : Z ⟶ X`, a
  coherent module supported in `ι(Z)` is killed by a power of the ideal `𝓘` of `Z` and has the
  filtration `N ⊇ 𝓘 N ⊇ 𝓘² N ⊇ ⋯` with quotients `ι_* ι^*(𝓘ᵏ N)` (EGA I 4.1.2 via
  `ClosedImmersionSections`).
* `CohomologyAux.finiteCohomology_of_vanishesOff_union`: the reducible case, via the kernel and
  image of `M → j_* j^* M` for `j` the inclusion of the complement of a closed subset.
* `CohomologyAux.exists_integral_closedImmersion`: the reduced structure on an irreducible closed
  subset, as a scheme-theoretic image of `Spec κ(ξ)`.
* `CohomologyAux.finiteCohomology_of_integral_step`: noetherian induction on the support reduces
  finiteness of cohomology for all coherent modules to the case of an integral closed subscheme,
  knowing it for modules supported in proper closed subsets.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

variable {X : Scheme.{u}}

section Vanishing

/-- An `𝒪_X`-module `M` *vanishes off* a subset `T ⊆ X` if its sections over every open disjoint
from `T` are zero, i.e. `Supp M ⊆ T` (for `T` closed). -/
def VanishesOff (M : X.Modules) (T : Set X) : Prop :=
  ∀ V : X.Opens, Disjoint (V : Set X) T → ∀ s : Γ(M, V), s = 0

lemma VanishesOff.mono {M : X.Modules} {T T' : Set X} (h : VanishesOff M T) (hT : T ⊆ T') :
    VanishesOff M T' :=
  fun V hV s ↦ h V (hV.mono_right hT) s

lemma VanishesOff.of_app_injective {M N : X.Modules} (φ : M ⟶ N)
    (hφ : ∀ V, Function.Injective (φ.app V)) {T : Set X} (h : VanishesOff N T) :
    VanishesOff M T :=
  fun V hV s ↦ hφ V (by rw [h V hV (φ.app V s), map_zero])

/-- A module all of whose sections vanish has vanishing cohomology. -/
lemma finiteCohomology_of_forall_eq_zero {R : Type*} [CommRing R] (ρ : R →+* Γ(X, ⊤))
    (M : X.Modules) (h : ∀ (V : X.Opens) (s : Γ(M, V)), s = 0) : FiniteCohomology ρ M := by
  have hid : 𝟙 M = 0 := Scheme.Modules.hom_ext _ _ fun V ↦ by
    ext s
    exact (h V _).trans (h V _).symm
  intro p
  let _ := Module.compHom (M.H p) ρ
  have : Subsingleton (M.H p) := ⟨fun x y ↦ by
    have hx : x = 0 := by
      have := congrArg (fun φ ↦ Scheme.Modules.H'.map φ p ⊤ x) hid
      simp only [Scheme.Modules.H'.map_id, Scheme.Modules.H'.map_zero] at this
      exact this
    have hy : y = 0 := by
      have := congrArg (fun φ ↦ Scheme.Modules.H'.map φ p ⊤ y) hid
      simp only [Scheme.Modules.H'.map_id, Scheme.Modules.H'.map_zero] at this
      exact this
    rw [hx, hy]⟩
  exact ⟨⟨∅, Subsingleton.elim _ _⟩⟩

/-- A module vanishing off the empty set has vanishing cohomology. -/
lemma finiteCohomology_of_vanishesOff_empty {R : Type*} [CommRing R] (ρ : R →+* Γ(X, ⊤))
    (M : X.Modules) (h : VanishesOff M ∅) : FiniteCohomology ρ M :=
  finiteCohomology_of_forall_eq_zero ρ M fun V s ↦ h V (Set.disjoint_empty _) s

/-- A quasi-coherent module with vanishing sections over the members of an affine open cover is
zero. -/
lemma eq_zero_of_affine_cover (N : X.Modules) [N.IsQuasicoherent] {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ a, IsAffineOpen (U a)) (hcov : ⨆ a, U a = ⊤)
    (h : ∀ a (s : Γ(N, U a)), s = 0) (V : X.Opens) (s : Γ(N, V)) : s = 0 := by
  have hbasic : ∀ (a : ι) (c : Γ(X, U a)) (t : Γ(N, X.basicOpen c)), t = 0 := by
    intro a c t
    obtain ⟨m, k, hm⟩ := exists_pow_smul_eq_map N (hU a) c t
    rw [h a m, map_zero] at hm
    have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le c)).op (c ^ k)) := by
      rw [map_pow]
      exact (X.toRingedSpace.isUnit_res_basicOpen c).pow k
    rw [← one_smul Γ(X, X.basicOpen c) t, ← hu.val_inv_mul, mul_smul, hm, smul_zero]
  have hx : ∀ x : V, ∃ (a : ι) (c : Γ(X, U a)), X.basicOpen c ≤ V ∧ x.1 ∈ X.basicOpen c := by
    intro x
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x.1))
    obtain ⟨c, hc, hxc⟩ := (hU a).exists_basicOpen_le x ha
    exact ⟨a, c, hc, hxc⟩
  choose a c hc hxc using hx
  refine TopCat.Sheaf.eq_of_locally_eq' N.toAbSheaf (fun x : V ↦ X.basicOpen (c x)) V
    (fun x ↦ homOfLE (hc x)) (fun x hxV ↦ Opens.mem_iSup.mpr ⟨⟨x, hxV⟩, hxc ⟨x, hxV⟩⟩) s 0
    fun x ↦ ?_
  rw [map_zero]
  exact hbasic (a x) (c x) _

end Vanishing

/-- A quasi-compact scheme has a finite affine open cover. -/
lemma exists_cechCover' (X : Scheme.{u}) [CompactSpace X] :
    ∃ (n : ℕ) (U : Fin n → X.Opens), ⨆ i, U i = ⊤ ∧ ∀ i, IsAffineOpen (U i) := by
  choose V hV hxV using fun x : X ↦
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ (⊤ : X.Opens) from trivial))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X ↦ (V x : Set X))
    (fun x ↦ (V x).2) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, (hxV x).1⟩)
  refine ⟨t.card, fun k ↦ V (t.equivFin.symm k), ?_, fun k ↦ hV _⟩
  refine top_le_iff.mp fun x _ ↦ ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

section Filtration

variable {Z : Scheme.{u}} (ι : Z ⟶ X)

/-- The unit `N → ι_* ι^* N`. -/
noncomputable abbrev unitPushPull (N : X.Modules) :
    N ⟶ (Scheme.Modules.pushforward ι).obj ((Scheme.Modules.pullback ι).obj N) :=
  (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app N

lemma unitPushPull_app (N : X.Modules) (V : X.Opens) :
    (unitPushPull ι N).app V = Scheme.Modules.pullbackApp ι N V := rfl

/-- For a closed immersion `ι` and `N` quasi-coherent, `N → ι_* ι^* N` is an epimorphism
(EGA I 4.1.2). -/
instance epi_unitPushPull [IsClosedImmersion ι] (N : X.Modules) [N.IsQuasicoherent] :
    Epi (unitPushPull ι N) := by
  have : ((Scheme.Modules.pushforward ι).obj ((Scheme.Modules.pullback ι).obj N)).IsQuasicoherent :=
    isQuasicoherent_pushforward ι _
  exact epi_of_surjective_app _ (unitPushPull ι N) (fun U : X.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top X) (fun U ↦ U.2)
    (fun U ↦ Scheme.Modules.surjective_pullbackApp_of_isClosedImmersion ι N U.2)

/-- The `𝒪_X`-module `𝓘 N`, the kernel of `N → ι_* ι^* N`, where `𝓘` is the ideal of `ι`. -/
noncomputable abbrev idealMul (N : X.Modules) : X.Modules := kernel (unitPushPull ι N)

/-- `0 → 𝓘 N → N → ι_* ι^* N → 0`. -/
lemma shortExact_idealMul [IsClosedImmersion ι] (N : X.Modules) [N.IsQuasicoherent] :
    (ShortComplex.kernelSequence (unitPushPull ι N)).ShortExact :=
  shortExact_kernelSequence _

/-- `N` is killed by the `k`-th power of the ideal of `ι` over the members of `U`. -/
def KilledOn {n : ℕ} (U : Fin n → X.Opens) (k : ℕ) (N : X.Modules) : Prop :=
  ∀ a, ∀ r ∈ (RingHom.ker (ι.app (U a)).hom) ^ k, ∀ s : Γ(N, U a), r • s = 0

variable [IsClosedImmersion ι]

lemma killedOn_idealMul {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ a, IsAffineOpen (U a)) (k : ℕ)
    (N : X.Modules) [N.IsQuasicoherent] (h : KilledOn ι U (k + 1) N) :
    KilledOn ι U k (idealMul ι N) := by
  intro a r hr s
  have hS := shortExact_idealMul ι N
  apply app_injective_of_shortExact hS (U a)
  change (kernel.ι (unitPushPull ι N)).app (U a) (r • s) =
    (kernel.ι (unitPushPull ι N)).app (U a) 0
  rw [map_zero, Scheme.Modules.Hom.app_smul]
  set t := (kernel.ι (unitPushPull ι N)).app (U a) s
  have ht : Scheme.Modules.pullbackApp ι N (U a) t = 0 := by
    change (kernel.ι (unitPushPull ι N) ≫ unitPushPull ι N).app (U a) s = 0
    rw [kernel.condition]
    rfl
  have hmem := Scheme.Modules.mem_smul_top_of_pullbackApp_eq_zero ι N (hU a) t ht
  have hle : (RingHom.ker (ι.app (U a)).hom) ^ (k + 1) • (⊤ : Submodule Γ(X, U a) Γ(N, U a)) = ⊥ :=
    eq_bot_iff.mpr (Submodule.smul_le.mpr fun r' hr' m _ ↦ by
      rw [Submodule.mem_bot]; exact h a r' hr' m)
  have : r • t ∈ (RingHom.ker (ι.app (U a)).hom) ^ (k + 1) •
      (⊤ : Submodule Γ(X, U a) Γ(N, U a)) := by
    rw [pow_succ, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr hmem
  rw [hle] at this
  exact (Submodule.mem_bot _).mp this

omit [IsClosedImmersion ι] in
lemma forall_eq_zero_of_killedOn_zero {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ a, IsAffineOpen (U a))
    (hcov : ⨆ a, U a = ⊤) (N : X.Modules) [N.IsQuasicoherent] (h : KilledOn ι U 0 N)
    (V : X.Opens) (s : Γ(N, V)) : s = 0 :=
  eq_zero_of_affine_cover N U hU hcov (fun a s ↦ by
    rw [← one_smul Γ(X, U a) s]
    exact h a 1 (by rw [pow_zero, Ideal.one_eq_top]; trivial) s) V s

omit [IsClosedImmersion ι] in
/-- A section of the structure sheaf in the ideal of `ι` does not vanish at any point of the image
of `ι`. -/
lemma basicOpen_disjoint_range {U : X.Opens} (r : Γ(X, U)) (hr : ι.app U r = 0) :
    Disjoint (X.basicOpen r : Set X) (Set.range ι) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨z, rfl⟩
  have : z ∈ ι ⁻¹ᵁ X.basicOpen r := hx
  rw [Scheme.preimage_basicOpen, hr, Scheme.basicOpen_zero] at this
  exact this

/-- In a finitely generated module, elements which are killed by powers of `f` elementwise are
killed by a common power. -/
lemma exists_pow_smul_eq_zero_of_finite {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (f : R) (h : ∀ m : M, ∃ k : ℕ, f ^ k • m = 0) :
    ∃ k : ℕ, ∀ m : M, f ^ k • m = 0 := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := M)
  choose k hk using h
  refine ⟨S.sup k, fun m ↦ ?_⟩
  have hm : m ∈ Submodule.span R (S : Set M) := hS.symm ▸ Submodule.mem_top
  refine Submodule.span_induction (fun x hx ↦ ?_) (by rw [smul_zero]) (fun x y _ _ hx hy ↦ ?_)
    (fun a x _ hx ↦ ?_) hm
  · have hle : k x ≤ S.sup k := Finset.le_sup hx
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hk x, smul_zero]
  · rw [smul_add, hx, hy, add_zero]
  · rw [smul_comm, hx, smul_zero]

omit [IsClosedImmersion ι] in
/-- **Coherent modules supported on a closed subscheme are killed by a power of its ideal**
(EGA I 9.3.4, 5.2.3 for sections): if `X` is locally noetherian, `ι` a closed immersion and `N`
coherent with support in the image of `ι`, then over finitely many affine opens `N` is killed by a
power of the ideal of `ι`. -/
lemma exists_killedOn [IsLocallyNoetherian X] {n : ℕ} (U : Fin n → X.Opens)
    (hU : ∀ a, IsAffineOpen (U a)) (N : X.Modules) [N.IsCoherent]
    (hN : VanishesOff N (Set.range ι)) : ∃ k, KilledOn ι U k N := by
  have hq : N.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have ht : N.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have key : ∀ a, ∃ k : ℕ, ∀ r ∈ (RingHom.ker (ι.app (U a)).hom) ^ k, ∀ s : Γ(N, U a),
      r • s = 0 := by
    intro a
    have hR : IsNoetherianRing Γ(X, U a) :=
      IsLocallyNoetherian.component_noetherian ⟨U a, hU a⟩
    have hfin : Module.Finite Γ(X, U a) Γ(N, U a) := finite_sections_of_isFiniteType N (hU a)
    let J := Module.annihilator Γ(X, U a) Γ(N, U a)
    have hrad : RingHom.ker (ι.app (U a)).hom ≤ J.radical := by
      intro f hf
      have hloc : ∀ m : Γ(N, U a), ∃ k : ℕ, f ^ k • m = 0 := fun m ↦
        exists_pow_smul_eq_zero N (hU a) f m
          (hN _ (basicOpen_disjoint_range ι f (RingHom.mem_ker.mp hf)) _)
      obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_finite f hloc
      exact ⟨k, Module.mem_annihilator.mpr hk⟩
    obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
      (IsNoetherian.noetherian _)
    exact ⟨k, fun r hr s ↦ Module.mem_annihilator.mp (hk hr) s⟩
  choose k hk using key
  refine ⟨Finset.univ.sup k, fun a r hr s ↦ ?_⟩
  exact hk a r (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ a)) hr) s

/-- **Dévissage along a closed subscheme** (EGA III 3.1.2, first step): let `X` be noetherian and
`ι : Z ⟶ X` a closed immersion such that `ι_* ι^* N` has finite cohomology for every coherent `N`.
Then every coherent module supported in `ι(Z)` has finite cohomology (by the filtration
`N ⊇ 𝓘 N ⊇ 𝓘² N ⊇ ⋯`). -/
theorem finiteCohomology_of_vanishesOff_range [IsLocallyNoetherian X] [CompactSpace X]
    {R : Type*} [CommRing R] [IsNoetherianRing R] (ρ : R →+* Γ(X, ⊤))
    (hZ : ∀ N : X.Modules, N.IsCoherent →
      FiniteCohomology ρ ((Scheme.Modules.pushforward ι).obj ((Scheme.Modules.pullback ι).obj N)))
    (N : X.Modules) [N.IsCoherent] (hN : VanishesOff N (Set.range ι)) :
    FiniteCohomology ρ N := by
  obtain ⟨n, U, hcov, hU⟩ := exists_cechCover' X
  obtain ⟨k, hk⟩ := exists_killedOn ι U hU N hN
  clear hN
  induction k generalizing N with
  | zero =>
    have : N.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
    exact finiteCohomology_of_forall_eq_zero ρ N
      (forall_eq_zero_of_killedOn_zero ι U hU hcov N hk)
  | succ k ih =>
    have : N.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
    have hS := shortExact_idealMul ι N
    have : ((Scheme.Modules.pushforward ι).obj
        ((Scheme.Modules.pullback ι).obj N)).IsQuasicoherent := isQuasicoherent_pushforward ι _
    have : (ShortComplex.kernelSequence (unitPushPull ι N)).X₂.IsQuasicoherent :=
      ‹N.IsQuasicoherent›
    have : (ShortComplex.kernelSequence (unitPushPull ι N)).X₃.IsQuasicoherent :=
      ‹((Scheme.Modules.pushforward ι).obj ((Scheme.Modules.pullback ι).obj N)).IsQuasicoherent›
    have : (ShortComplex.kernelSequence (unitPushPull ι N)).X₁.IsQuasicoherent :=
      isQuasicoherent_X₁_of_shortExact hS
    have : (ShortComplex.kernelSequence (unitPushPull ι N)).X₂.IsCoherent := ‹N.IsCoherent›
    have hK : (idealMul ι N).IsCoherent := isCoherent_X₁_of_shortExact hS
    have h₁ := ih (idealMul ι N) (killedOn_idealMul ι U hU k N hk)
    exact FiniteCohomology.of_shortExact₂ hS h₁ (hZ N inferInstance)

end Filtration

section Reducible

/-- Monomorphisms of `𝒪_X`-modules are injective on sections. -/
lemma app_injective_of_mono {M N : X.Modules} (φ : M ⟶ N) [Mono φ] (V : X.Opens) :
    Function.Injective (φ.app V) := by
  have : Mono (Scheme.Modules.Hom.toAbSheaf φ) :=
    (Scheme.Modules.toAbSheafFunctor X).map_mono φ
  exact CategoryTheory.Sheaf.app_injective_of_mono (Scheme.Modules.Hom.toAbSheaf φ) V

/-- An open subset of an affine open with compact underlying set is a finite union of basic
opens. -/
lemma exists_basicOpen_cover {U : X.Opens} (hU : IsAffineOpen U) (V : X.Opens) (hVU : V ≤ U)
    (hV : IsCompact (V : Set X)) :
    ∃ (n : ℕ) (c : Fin n → Γ(X, U)), ⨆ k, X.basicOpen (c k) = V := by
  have hx : ∀ x : V, ∃ f : Γ(X, U), X.basicOpen f ≤ V ∧ x.1 ∈ X.basicOpen f :=
    fun x ↦ hU.exists_basicOpen_le x (hVU x.2)
  choose f hf hxf using hx
  obtain ⟨t, ht⟩ := hV.elim_finite_subcover (fun x : V ↦ (X.basicOpen (f x) : Set X))
    (fun x ↦ (X.basicOpen (f x)).2) (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxf ⟨x, hx⟩⟩)
  refine ⟨t.card, fun k ↦ f (t.equivFin.symm k), le_antisymm (iSup_le fun k ↦ hf _) ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

/-- The direct image of a quasi-coherent module along the inclusion of an open subset of a
noetherian scheme is quasi-coherent. -/
lemma isQuasicoherent_pushforward_ι [IsNoetherian X] (O : X.Opens) (M : O.toScheme.Modules)
    [M.IsQuasicoherent] : ((Scheme.Modules.pushforward O.ι).obj M).IsQuasicoherent := by
  refine isQuasicoherent_pushforward_of_cover O.ι M fun U hU ↦ ?_
  obtain ⟨n, c, hc⟩ := exists_basicOpen_cover hU (U ⊓ O) inf_le_left
    (NoetherianSpace.isCompact _)
  have hle : ∀ k, X.basicOpen (c k) ≤ O.ι.opensRange := fun k ↦ by
    rw [Scheme.Opens.opensRange_ι]
    exact ((le_iSup (fun k ↦ X.basicOpen (c k)) k).trans hc.le).trans inf_le_right
  refine ⟨n, fun k ↦ O.ι ⁻¹ᵁ X.basicOpen (c k), fun k ↦ ?_, fun k l ↦ ?_, ?_⟩
  · exact (hU.basicOpen (c k)).preimage_of_isOpenImmersion O.ι (hle k)
  · rw [← Scheme.Hom.preimage_inf, ← Scheme.basicOpen_mul]
    exact (hU.basicOpen _).preimage_of_isOpenImmersion O.ι
      ((X.basicOpen_mul _ _).le.trans (inf_le_left.trans (hle k)))
  · rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self,
      inf_top_eq]

/-- **Dévissage for a reducible support** (EGA III 3.1.2): let `X` be noetherian, `T₂ ⊆ X` closed
and `M` coherent, vanishing off `T₁ ∪ T₂`. Writing `j` for the inclusion of `X ∖ T₂`, the
kernel of `M → j_* j^* M` vanishes off `T₂` and its image vanishes off `T₁`; hence if all coherent
modules vanishing off `T₁` or off `T₂` have finite cohomology, so has `M`. -/
theorem finiteCohomology_of_vanishesOff_union [IsNoetherian X] {R : Type*} [CommRing R]
    [IsNoetherianRing R] (ρ : R →+* Γ(X, ⊤)) {T₁ T₂ : Set X} (hT₂ : IsClosed T₂)
    (h₁ : ∀ N : X.Modules, N.IsCoherent → VanishesOff N T₁ → FiniteCohomology ρ N)
    (h₂ : ∀ N : X.Modules, N.IsCoherent → VanishesOff N T₂ → FiniteCohomology ρ N)
    (M : X.Modules) [M.IsCoherent] (hM : VanishesOff M (T₁ ∪ T₂)) :
    FiniteCohomology ρ M := by
  have : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let O : X.Opens := ⟨T₂ᶜ, hT₂.isOpen_compl⟩
  let η := unitPushPull O.ι M
  have : ((Scheme.Modules.pushforward O.ι).obj
      ((Scheme.Modules.pullback O.ι).obj M)).IsQuasicoherent := isQuasicoherent_pushforward_ι O _
  have hS := shortExact_kernelSequence (Abelian.factorThruImage η)
  have : (Abelian.image η).IsQuasicoherent := isQuasicoherent_image η
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage η)).X₂.IsQuasicoherent :=
    ‹M.IsQuasicoherent›
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage η)).X₃.IsQuasicoherent :=
    ‹(Abelian.image η).IsQuasicoherent›
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage η)).X₁.IsQuasicoherent :=
    isQuasicoherent_X₁_of_shortExact hS
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage η)).X₂.IsCoherent :=
    ‹M.IsCoherent›
  have hK := isCoherent_X₁_of_shortExact hS
  have hI := isCoherent_X₃_of_shortExact hS
  refine FiniteCohomology.of_shortExact₂ hS (h₂ _ hK ?_) (h₁ _ hI ?_)
  · -- the kernel vanishes off `T₂`
    intro V hV s
    apply app_injective_of_shortExact hS V
    rw [map_zero]
    apply (Scheme.Modules.pullbackApp_bijective_of_isOpenImmersion O.ι M V (by
      rw [Scheme.Opens.opensRange_ι]
      exact fun x hx ↦ Set.disjoint_left.mp hV hx)).1
    refine Eq.trans ?_ (map_zero _).symm
    have h0 : kernel.ι (Abelian.factorThruImage η) ≫ η = 0 := by
      calc kernel.ι (Abelian.factorThruImage η) ≫ η =
          kernel.ι (Abelian.factorThruImage η) ≫ (Abelian.factorThruImage η ≫
            Abelian.image.ι η) := by rw [Abelian.image.fac]
        _ = 0 := by rw [kernel.condition_assoc, zero_comp]
    change (kernel.ι (Abelian.factorThruImage η) ≫ η).app V s = 0
    rw [h0]
    rfl
  · -- the image vanishes off `T₁`
    intro V hV s
    apply app_injective_of_mono (Abelian.image.ι η) V
    refine Eq.trans ?_ (map_zero _).symm
    have hW : Function.Surjective (Scheme.Modules.pullbackApp O.ι M (V ⊓ O)) :=
      (Scheme.Modules.pullbackApp_bijective_of_isOpenImmersion O.ι M (V ⊓ O) (by
        rw [Scheme.Opens.opensRange_ι]; exact inf_le_right)).2
    have h0 : ∀ t : Γ((Scheme.Modules.pullback O.ι).obj M, O.ι ⁻¹ᵁ (V ⊓ O)), t = 0 := by
      intro t
      obtain ⟨m, rfl⟩ := hW t
      rw [hM (V ⊓ O) ?_ m, map_zero]
      rw [Set.disjoint_union_right]
      exact ⟨hV.mono_left inf_le_left, Set.disjoint_left.mpr fun x hx hx' ↦ hx.2 hx'⟩
    have he : O.ι ⁻¹ᵁ (V ⊓ O) = O.ι ⁻¹ᵁ V := by
      rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]
    apply ((Scheme.Modules.pullback O.ι).obj M).presheaf.map_injective_of_eq
      (homOfLE he.le) he
    refine Eq.trans ?_ (map_zero _).symm
    exact h0 _

end Reducible

section Main

/-- Every module vanishes off `X`. -/
lemma vanishesOff_univ (M : X.Modules) : VanishesOff M Set.univ := by
  intro V hV s
  have hV' : V = ⊥ := by
    ext x
    exact ⟨fun hx ↦ (Set.disjoint_left.mp hV hx (Set.mem_univ x)).elim, fun hx ↦ hx.elim⟩
  subst hV'
  exact TopCat.Sheaf.eq_of_locally_eq' M.toAbSheaf (fun i : PEmpty.{1} ↦ i.elim) ⊥
    (fun i ↦ i.elim) (fun x hx ↦ hx.elim) _ _ (fun i ↦ i.elim)

/-- The direct image of a coherent module along a closed immersion is coherent (EGA I 9.2.2). -/
lemma isCoherent_pushforward_of_isClosedImmersion {Z : Scheme.{u}} (ι : Z ⟶ X)
    [IsClosedImmersion ι] (G : Z.Modules) [G.IsCoherent] :
    ((Scheme.Modules.pushforward ι).obj G).IsCoherent where
  isQuasicoherent := by
    have := (Scheme.Modules.IsCoherent.isQuasicoherent : G.IsQuasicoherent)
    exact isQuasicoherent_pushforward ι G
  isFiniteType := by
    have := (Scheme.Modules.IsCoherent.isQuasicoherent : G.IsQuasicoherent)
    have := (Scheme.Modules.IsCoherent.isFiniteType : G.IsFiniteType)
    have : ((Scheme.Modules.pushforward ι).obj G).IsQuasicoherent :=
      isQuasicoherent_pushforward ι G
    refine isFiniteType_of_finite_sections _ (fun U : X.affineOpens ↦ U.1)
      (iSup_affineOpens_eq_top X) (fun U ↦ U.2) fun U ↦ ?_
    have := finite_sections_of_isFiniteType G (U.2.preimage ι)
    exact finite_compHom_of_surjective (M := Γ(G, ι ⁻¹ᵁ U.1)) (ι.app U.1).hom
      (ι.app_surjective _ U.2)

/-- Direct images preserve vanishing off a subset. -/
lemma VanishesOff.pushforward {Z : Scheme.{u}} (ι : Z ⟶ X) {G : Z.Modules} {T : Set Z}
    (h : VanishesOff G T) : VanishesOff ((Scheme.Modules.pushforward ι).obj G) (ι '' T) :=
  fun V hV s ↦ h (ι ⁻¹ᵁ V) (Set.disjoint_left.mpr fun z hz hzT ↦
    Set.disjoint_left.mp hV hz ⟨z, hzT, rfl⟩) s

/-- **Integral closed subschemes** (EGA I 5.1.1, 5.2.1): an irreducible closed subset `T` of a
scheme is the image of a closed immersion from an integral scheme (the scheme-theoretic image of
`Spec κ(ξ) ⟶ X`, `ξ` the generic point of `T`, i.e. `T` with its reduced structure). -/
lemma exists_integral_closedImmersion [QuasiSeparatedSpace X] (T : Set X) (hT : IsClosed T)
    (hirr : IsIrreducible T) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ X), IsClosedImmersion ι ∧ IsIntegral Z ∧ Set.range ι = T := by
  let f := X.fromSpecResidueField hirr.genericPoint
  have : QuasiCompact f := inferInstance
  have : IsReduced f.image := IsSchemeTheoreticallyDominant.isReduced f.toImage
  have : IrreducibleSpace f.image := by
    rw [irreducibleSpace_def]
    have := ((IrreducibleSpace.isIrreducible_univ (Spec (X.residueField hirr.genericPoint))).image
      f.toImage f.toImage.continuous.continuousOn).closure
    rwa [Set.image_univ, f.toImage.denseRange.closure_range] at this
  refine ⟨f.image, f.imageι, inferInstance, isIntegral_of_irreducibleSpace_of_isReduced _, ?_⟩
  change Set.range f.ker.subschemeι = T
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
    Scheme.range_fromSpecResidueField, hirr.closure_genericPoint hT]

/-- **Dévissage** (EGA III 3.1.2, 3.2.1 reduction to the integral case): let `X` be a noetherian
scheme with affine diagonal over a noetherian ring `A`. Suppose that for every integral closed
subscheme `ι : Z ⟶ X`, if all coherent `𝒪_Z`-modules supported in a proper closed subset have
finitely generated cohomology over `A`, then so do all coherent `𝒪_Z`-modules. Then every coherent
`𝒪_X`-module has finitely generated cohomology over `A`. -/
theorem finiteCohomology_of_integral_step {A : CommRingCat.{u}} [IsNoetherianRing A]
    [IsNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))] (f : X ⟶ Spec A)
    (hint : ∀ (Z : Scheme.{u}) (ι : Z ⟶ X) [IsClosedImmersion ι] [IsIntegral Z],
      (∀ G : Z.Modules, G.IsCoherent → ∀ T' : Set Z, IsClosed T' → T' ≠ Set.univ →
        VanishesOff G T' → FiniteCohomology (ι ≫ f).specStructureRingHom G) →
      ∀ G : Z.Modules, G.IsCoherent → FiniteCohomology (ι ≫ f).specStructureRingHom G)
    (M : X.Modules) [M.IsCoherent] : FiniteCohomology f.specStructureRingHom M := by
  suffices H : ∀ T : TopologicalSpace.Closeds X, ∀ N : X.Modules, N.IsCoherent →
      VanishesOff N T → FiniteCohomology f.specStructureRingHom N from
    H ⊤ M inferInstance (vanishesOff_univ M)
  intro T
  induction T using WellFoundedLT.induction with
  | _ T ih =>
  intro N hN hNT
  by_cases hne : (T : Set X).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hNT
    exact finiteCohomology_of_vanishesOff_empty _ N hNT
  by_cases hpre : IsPreirreducible (T : Set X)
  · -- the irreducible case
    have hirr : IsIrreducible (T : Set X) := ⟨hne, hpre⟩
    obtain ⟨Z, ι, hι, hZ, hrange⟩ := exists_integral_closedImmersion (T : Set X) T.2 hirr
    have hZ' : ∀ G : Z.Modules, G.IsCoherent →
        FiniteCohomology (ι ≫ f).specStructureRingHom G := by
      refine hint Z ι fun G hG T' hT' hT'ne hGT' ↦ ?_
      have : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
      refine (finiteCohomology_iff_pushforward_of_isAffineHom ι G f).mpr ?_
      have hcl : IsClosed (ι '' T') := ι.isClosedEmbedding.isClosedMap _ hT'
      have hlt : (⟨ι '' T', hcl⟩ : TopologicalSpace.Closeds X) < T := by
        refine lt_of_le_of_ne (fun x ⟨z, _, hz⟩ ↦ by
            change x ∈ (T : Set X); rw [← hz, ← hrange]; exact ⟨z, rfl⟩)
          fun he ↦ hT'ne ?_
        refine Set.eq_univ_of_forall fun z ↦ ?_
        have hz : ι z ∈ (T : Set X) := by rw [← hrange]; exact ⟨z, rfl⟩
        rw [← he] at hz
        obtain ⟨z', hz', hzz'⟩ := hz
        rwa [← ι.isClosedEmbedding.injective hzz']
      exact ih _ hlt _ (isCoherent_pushforward_of_isClosedImmersion ι G)
        (VanishesOff.pushforward ι hGT')
    have : N.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
    refine finiteCohomology_of_vanishesOff_range ι _ (fun N' hN' ↦ ?_) N (hrange ▸ hNT)
    have : N'.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
    have : N'.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
    have : ((Scheme.Modules.pullback ι).obj N').IsCoherent := ⟨inferInstance, inferInstance⟩
    exact (finiteCohomology_iff_pushforward_of_isAffineHom ι _ f).mp (hZ' _ inferInstance)
  · -- the reducible case
    obtain ⟨u, v, hu, hv, hTu, hTv, huv⟩ : ∃ u v : Set X, IsOpen u ∧ IsOpen v ∧
        ((T : Set X) ∩ u).Nonempty ∧ ((T : Set X) ∩ v).Nonempty ∧
        ¬ ((T : Set X) ∩ (u ∩ v)).Nonempty := by
      simpa [IsPreirreducible] using hpre
    let T₁ : TopologicalSpace.Closeds X := ⟨(T : Set X) ∩ uᶜ, T.2.inter hu.isClosed_compl⟩
    let T₂ : TopologicalSpace.Closeds X := ⟨(T : Set X) ∩ vᶜ, T.2.inter hv.isClosed_compl⟩
    have hlt₁ : T₁ < T := lt_of_le_of_ne (fun x hx ↦ hx.1) fun he ↦ by
      obtain ⟨x, hxT, hxu⟩ := hTu
      have : x ∈ (T₁ : Set X) := he ▸ hxT
      exact this.2 hxu
    have hlt₂ : T₂ < T := lt_of_le_of_ne (fun x hx ↦ hx.1) fun he ↦ by
      obtain ⟨x, hxT, hxv⟩ := hTv
      have : x ∈ (T₂ : Set X) := he ▸ hxT
      exact this.2 hxv
    have hunion : (T : Set X) ⊆ (T₁ : Set X) ∪ (T₂ : Set X) := fun x hx ↦ by
      by_contra h
      simp only [Set.mem_union, not_or] at h
      exact huv ⟨x, hx, not_not.mp fun h' ↦ h.1 ⟨hx, h'⟩, not_not.mp fun h' ↦ h.2 ⟨hx, h'⟩⟩
    exact finiteCohomology_of_vanishesOff_union _ T₂.2 (fun N' hN' h' ↦ ih T₁ hlt₁ N' hN' h')
      (fun N' hN' h' ↦ ih T₂ hlt₂ N' hN' h') N (hNT.mono hunion)

end Main

end AlgebraicGeometry.CohomologyAux
