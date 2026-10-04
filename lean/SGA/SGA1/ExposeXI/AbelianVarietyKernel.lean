/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.Factorial
import SGA.Foundations.Picard.IntegralSubscheme
import SGA.Foundations.Picard.PoleDivisor
import SGA.SGA1.ExposeXI.AbelianVarietyCubeOpenness
import SGA.SGA1.ExposeXI.TateModulePrimary

/-!
# SGA 1, Exposé XI.2: `n_A` is an isogeny, from the theorem of the cube

SGA 1 XI.2 recalls that multiplication by `n > 0` on an abelian variety `A` over an algebraically
closed field is an isogeny (finite and surjective). We deduce it from the cube relation
(`CubeRelation A`, Mumford, *Abelian varieties*, §6, Corollary 2), following Mumford (§6,
Application 2 and §8) with an effective divisor in place of an ample line bundle:

* `eq_of_forall_mulN_eq`: if an irreducible closed subset `Z` of `A` is mapped by `n_A` to a
  single point, it has at most one closed point in any affine open. Otherwise there are closed
  points `x ≠ x'` of `Z` in an affine open `V`, a function `f₀` on `V` vanishing at `x'` but not
  at `x`, and the line bundle `L = 𝒪(div_∞ f₀)` (`Scheme.exists_lineBundle_poleDivisor`; the local
  rings of `A` are factorial) with a section `s` vanishing at `x'` but not at `x`. On the
  integral proper scheme `Z` (reduced structure), the cube relation gives
  `n_A^* L = L^{a} ⊗ (-1)^* L^{b}` with `a = n(n+1)/2`, `b = n(n-1)/2` (`picPullback_mulN`), and
  `n_A|_Z` is constant, so `L|_Z^{a} ⊗ (-1)^*L|_Z^{b}` and `(-1)^*L|_Z^{a} ⊗ L|_Z^{b}` are trivial,
  hence `L|_Z^{a² - b²}` is trivial. Then `s|_Z` vanishes nowhere since it does not vanish at `x`
  (`Scheme.LineBundle.famLocus_eq_top_of_class_pow_eq_one`): a contradiction.
* `quasiFiniteAt_mulN_of_isClosed`, `locallyQuasiFinite_mulN`: hence every closed point is
  isolated in its fibre, and `n_A` is locally quasi-finite, so finite (it is proper).
* `isDominant_of_locallyQuasiFinite_of_apply_eq`: a locally quasi-finite endomorphism of an
  integral locally noetherian scheme fixing a point is dominant (it is strictly monotone for the
  specialization order and would otherwise lengthen the chains of generizations of the fixed
  point); so `n_A` is surjective (`mulNIsogeny_of_cubeRelation`).
* `mulNIsogenyStatement_of_cubeRelation`; with the cube relation from the theorem of the cube
  (`mulNIsogenyStatement_of_theoremOfTheCube`) or from its openness step
  (`mulNIsogenyStatement_of_cubeOpenness`, via `cubeRelation_of_cubeOpenness`), and XI.2.1 in
  every characteristic from either (`abelianVarietyFundamentalGroupStatement_of_cubeOpenness`,
  `abelianVarietyPrimaryComponentStatement_of_cubeOpenness`, and the `…_of_theoremOfTheCube`
  versions).

Status: XI.2.1 is proved modulo `AlgebraicGeometry.CubeOpennessStatement` (the infinitesimal and
formal step of the theorem of the cube), which is open.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  Topology

namespace SGA.SGA1.ExposeXI

section Topology

/-- In a noetherian space, a point which is not isolated lies on an irreducible component which is
not reduced to it. -/
theorem exists_mem_irreducibleComponents_ne_singleton {T : Type*} [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] {p : T} (h : ¬IsOpen ({p} : Set T)) :
    ∃ C ∈ irreducibleComponents T, p ∈ C ∧ C ≠ {p} := by
  by_contra H
  push Not at H
  apply h
  have hfin := (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := T)).subset
    (Set.sep_subset (irreducibleComponents T) fun C ↦ p ∉ C)
  have hcl : IsClosed (⋃₀ {C ∈ irreducibleComponents T | p ∉ C}) := by
    rw [Set.sUnion_eq_biUnion]
    exact Set.Finite.isClosed_biUnion hfin fun C hC ↦
      isClosed_of_mem_irreducibleComponents C hC.1
  convert hcl.isOpen_compl using 1
  ext y
  simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_sUnion, Set.mem_ofPred_eq,
    not_exists, not_and]
  constructor
  · rintro rfl C hC hpC
    exact hC.2 hpC
  · intro hy
    obtain ⟨C, hC, hyC⟩ : ∃ C ∈ irreducibleComponents T, y ∈ C := by
      have : y ∈ ⋃₀ irreducibleComponents T := by
        rw [sUnion_irreducibleComponents]; trivial
      simpa using this
    by_cases hpC : p ∈ C
    · rw [H C hC hpC] at hyC
      exact hyC
    · exact absurd hyC (hy C ⟨hC, hpC⟩)

end Topology

section Dominant

open Order

/-- A locally quasi-finite morphism of schemes is strictly monotone for the specialization order:
two points of a fibre are not specializations of each other. -/
lemma strictMono_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] :
    StrictMono f := by
  intro a b hab
  rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at hab ⊢
  refine ⟨hab.1.map f.continuous, fun hfab ↦ hab.2 ?_⟩
  have he : f a = f b := ((hab.1.map f.continuous).antisymm hfab).eq.symm
  have : DiscreteTopology (f ⁻¹' {f a}) := (f.isDiscrete_preimage_singleton (f a)).to_subtype
  have hs : (⟨b, he.symm⟩ : f ⁻¹' {f a}) ⤳ ⟨a, rfl⟩ :=
    (Topology.IsInducing.subtypeVal.specializes_iff).1 hab.1
  have : (⟨b, he.symm⟩ : f ⁻¹' {f a}) = ⟨a, rfl⟩ := hs.eq
  rw [show b = a from congrArg Subtype.val this]

/-- A locally quasi-finite endomorphism of an integral locally noetherian scheme fixing a point is
dominant: otherwise it would map the chains of generizations of the fixed point to chains below
the image of the generic point, which lengthens them by one. -/
theorem isDominant_of_locallyQuasiFinite_of_apply_eq {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (f : X ⟶ X) [LocallyQuasiFinite f] {x : X} (hx : f x = x) :
    IsDominant f := by
  have hf := strictMono_of_locallyQuasiFinite f
  by_cases htop : f ⊤ = ⊤
  · refine ⟨?_⟩
    rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro z
    exact closure_mono (Set.singleton_subset_iff.2 ⟨⊤, htop⟩ : ({⊤} : Set X) ⊆ Set.range f)
      ((genericPoint_spec X).specializes trivial).mem_closure
  exfalso
  have hlt : f ⊤ < ⊤ := lt_of_le_not_ge le_top fun h' ↦ htop
    ((Scheme.le_iff_specializes.1 le_top).antisymm (Scheme.le_iff_specializes.1 h')).eq.symm
  let g : X → Set.Iic (f ⊤) := fun a ↦ ⟨f a, Set.mem_Iic.2 (Scheme.le_iff_specializes.2
    ((Scheme.le_iff_specializes.1 (le_top : a ≤ ⊤)).map f.continuous))⟩
  have hg : StrictMono g := fun a b hab ↦ hf hab
  let h : WithTop (Set.Iic (f ⊤)) → X := fun t ↦ t.elim ⊤ Subtype.val
  have hh : StrictMono h := by
    intro t t' htt'
    induction t' using WithTop.recTopCoe with
    | top =>
      induction t using WithTop.recTopCoe with
      | top => exact absurd htt' (lt_irrefl _)
      | coe t => exact lt_of_le_of_lt t.2 hlt
    | coe t' =>
      induction t using WithTop.recTopCoe with
      | top => exact absurd htt' not_top_lt
      | coe t =>
        have : t < t' := WithTop.coe_lt_coe.1 htt'
        exact this
  have hfin : coheight x < ⊤ := by
    have h₀ := ringKrullDim_stalk_eq_coheight x
    have : ringKrullDim (X.presheaf.stalk x) < ⊤ := ringKrullDim_lt_top
    rw [h₀] at this
    exact WithBot.coe_lt_coe.1 (by simpa using this)
  have h₁ : coheight x ≤ coheight (g x) := coheight_le_coheight_apply_of_strictMono g hg x
  have h₂ : coheight ((g x : Set.Iic (f ⊤)) : WithTop (Set.Iic (f ⊤))) ≤ coheight (h (g x)) :=
    coheight_le_coheight_apply_of_strictMono h hh _
  rw [coheight_coe_withTop] at h₂
  have h₃ : h (g x) = x := by
    change f x = x
    exact hx
  rw [h₃] at h₂
  have := (by gcongr : coheight x + 1 ≤ coheight (g x) + 1).trans h₂
  exact (ENat.add_one_le_iff hfin.ne).1 this |>.ne rfl

end Dominant

section Kernel

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left]

omit [IsAlgClosed k] [GrpObj A] in
include k in
/-- A scheme smooth and connected over a field (e.g. an abelian variety) is integral. -/
lemma isIntegral_left : IsIntegral A.left :=
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  ExposeX.isIntegral_of_isRegularScheme (ExposeII.isRegularLocalRing_stalk_of_smooth_field k A.hom)

omit [IsAlgClosed k] [GrpObj A] [IsProper A.hom] [ConnectedSpace A.left] in
include k in
/-- The local rings of a scheme smooth over a field (e.g. an abelian variety) are factorial:
they are regular, and regular local rings are factorial (Auslander–Buchsbaum). -/
lemma uniqueFactorizationMonoid_stalk (x : A.left) :
    UniqueFactorizationMonoid (A.left.presheaf.stalk x) :=
  have := ExposeII.isRegularLocalRing_stalk_of_smooth_field k A.hom x
  inferInstance

omit [IsAlgClosed k] [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left] in
/-- The inverse of a group object is an involution. -/
lemma inv_comp_inv : ι[A] ≫ ι[A] = 𝟙 A := by
  rw [GrpObj.inv_eq_inv, GrpObj.comp_inv, Category.comp_id, inv_inv]

omit [IsAlgClosed k] in
/-- The key step of Mumford, *Abelian varieties*, §6, Application 2, from the cube relation
(`hrel`): if `n > 0` and `n_A` maps an irreducible closed subset `Z` of an abelian variety `A`
to a single point, then two closed points of `Z` in a common affine open are equal. -/
theorem eq_of_forall_mulN_eq [IsCommMonObj A] (hrel : CubeRelation A) {n : ℕ} (hn : 0 < n)
    (Z : TopologicalSpace.Closeds A.left) (hZ : IsIrreducible (Z : Set A.left)) (y : A.left)
    (hZy : ∀ z ∈ Z, (mulN A n).left z = y) {V : A.left.Opens} (hV : IsAffineOpen V)
    {x x' : A.left} (hx : x ∈ Z) (hx' : x' ∈ Z) (hxV : x ∈ V) (hx'V : x' ∈ V)
    (hxc : IsClosed {x}) (hx'c : IsClosed {x'}) : x = x' := by
  by_contra hne
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsIntegral A.left := isIntegral_left A
  -- a function on `V` vanishing at `x'` but not at `x`
  obtain ⟨f₀, hf₀x, hf₀x'⟩ : ∃ f₀ : Γ(A.left, V), x ∈ A.left.basicOpen f₀ ∧
      x' ∉ A.left.basicOpen f₀ := by
    have hm := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hxc
    have hm' := hV.primeIdealOf_isMaximal_of_isClosed ⟨x', hx'V⟩ hx'c
    have hle : ¬ (hV.primeIdealOf ⟨x', hx'V⟩).asIdeal ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
      intro hle
      apply hne
      have e : hV.primeIdealOf ⟨x', hx'V⟩ = hV.primeIdealOf ⟨x, hxV⟩ :=
        PrimeSpectrum.ext (hm'.eq_of_le hm.ne_top hle)
      have := congrArg hV.fromSpec e
      rw [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf] at this
      exact this.symm
    obtain ⟨f₀, hf₀', hf₀⟩ := Set.not_subset.1 hle
    exact ⟨f₀, (hV.mem_basicOpen_iff f₀ ⟨x, hxV⟩).2 hf₀,
      fun h ↦ (hV.mem_basicOpen_iff f₀ ⟨x', hx'V⟩).1 h hf₀'⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  obtain ⟨L, s, hsec, hs⟩ := Scheme.exists_lineBundle_poleDivisor
    (A.left.germToFunctionField V f₀) (uniqueFactorizationMonoid_stalk A)
  have hsx (w : A.left) (hw : w ∈ V) : w ∈ L.famLocus ⊤ s ↔ w ∈ A.left.basicOpen f₀ :=
    hs V f₀ w hw (Scheme.algebraMap_germ_eq_germToFunctionField _ hw f₀)
  -- the reduced closed subscheme on `Z`, an integral scheme proper over `k`
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have : IsIntegral I.subscheme := Scheme.IdealSheafData.isIntegral_vanishingIdeal_subscheme Z hZ
  have hrange : Set.range I.subschemeι = Z :=
    Scheme.IdealSheafData.range_vanishingIdeal_subschemeι Z
  obtain ⟨zx, hzx⟩ : x ∈ Set.range I.subschemeι := hrange ▸ hx
  obtain ⟨zx', hzx'⟩ : x' ∈ Set.range I.subschemeι := hrange ▸ hx'
  have hZι (z : I.subscheme) : I.subschemeι z ∈ (Z : Set A.left) := hrange ▸ ⟨z, rfl⟩
  -- the relations in `Pic Z` given by the theorem of the cube
  set c := L.class
  set c' := Scheme.Pic.pullback ι[A].left c
  have hinv : Scheme.Pic.pullback ι[A].left c' = c := by
    rw [← Scheme.Pic.pullback_comp_apply, ← Over.comp_left, inv_comp_inv, Over.id_left,
      Scheme.Pic.pullback_id, MonoidHom.id_apply]
  have h₁ := picPullback_mulN c hrel n
  have h₂ := picPullback_mulN c' hrel n
  rw [hinv] at h₂
  have hcover (w : A.left) : ∃ i, w ∈ L.U i := by
    have : w ∈ ⨆ i, L.U i := by rw [L.iSup_eq_top]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨i₀, hi₀⟩ := hcover y
  obtain ⟨i₁, hi₁⟩ := hcover (ι[A].left y)
  have hr₁ : Scheme.Pic.pullback I.subschemeι (Scheme.Pic.pullback (mulN A n).left c) = 1 := by
    rw [← Scheme.Pic.pullback_comp_apply, Scheme.Pic.pullback_class]
    refine L.class_pullback_eq_one_of_range_subset _ (i₀ := i₀) ?_
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply, hZy _ (hZι z)]
    exact hi₀
  have hr₂ : Scheme.Pic.pullback I.subschemeι (Scheme.Pic.pullback (mulN A n).left c') = 1 := by
    rw [← Scheme.Pic.pullback_comp_apply, ← Scheme.Pic.pullback_comp_apply,
      Scheme.Pic.pullback_class]
    refine L.class_pullback_eq_one_of_range_subset _ (i₀ := i₁) ?_
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hZy _ (hZι z)]
    exact hi₁
  set C := Scheme.Pic.pullback I.subschemeι c
  set D := Scheme.Pic.pullback I.subschemeι c'
  rw [h₁, map_mul, map_pow, map_pow] at hr₁
  rw [h₂, map_mul, map_pow, map_pow] at hr₂
  -- hence `C ^ (a² - b²) = 1`, with `a = n(n+1)/2 > b = n(n-1)/2`
  set a := (n + 1).choose 2
  set b := n.choose 2
  have hab : b < a := by
    have : a = b + n := by
      simp only [a, b, Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    omega
  have hpos : 0 < a * a - b * b := Nat.sub_pos_of_lt (Nat.mul_self_lt_mul_self hab)
  have hpow : C ^ (a * a - b * b) = 1 := by
    have e₁ : C ^ (a * a) * D ^ (b * a) = 1 := by
      rw [pow_mul C a a, pow_mul D b a, ← mul_pow, hr₁, one_pow]
    have e₂ : D ^ (a * b) * C ^ (b * b) = 1 := by
      rw [pow_mul D a b, pow_mul C b b, ← mul_pow, hr₂, one_pow]
    have e₃ : C ^ (a * a) = C ^ (b * b) := by
      rw [mul_comm b a] at e₁
      rw [eq_inv_of_mul_eq_one_left e₁, eq_inv_of_mul_eq_one_right e₂]
    have e₄ : C ^ (a * a - b * b) * C ^ (b * b) = C ^ (b * b) := by
      rw [← pow_add, Nat.sub_add_cancel (Nat.mul_self_le_mul_self hab.le), e₃]
    exact mul_eq_right.1 e₄
  -- the section `s` restricted to `Z`
  have ht := hsec.famPullback I.subschemeι (le_top : (⊤ : I.subscheme.Opens) ≤ _)
  have hloc := L.famLocus_famPullback I.subschemeι (le_top : (⊤ : I.subscheme.Opens) ≤ _) s
  have hC : (L.pullback I.subschemeι).class = C := (Scheme.Pic.pullback_class _ L).symm
  have hzx_mem : zx ∈ (L.pullback I.subschemeι).famLocus ⊤
      (L.famPullback I.subschemeι (le_top : (⊤ : I.subscheme.Opens) ≤ _) s) := by
    rw [hloc]
    refine ⟨trivial, ?_⟩
    change I.subschemeι zx ∈ L.famLocus ⊤ s
    rw [hzx]
    exact (hsx x hxV).2 hf₀x
  have htop := Scheme.LineBundle.famLocus_eq_top_of_class_pow_eq_one (L.pullback I.subschemeι)
    (I.subschemeι ≫ A.hom) hpos (hC ▸ hpow) ht hzx_mem
  have hzx'_mem : zx' ∈ (L.pullback I.subschemeι).famLocus ⊤
      (L.famPullback I.subschemeι (le_top : (⊤ : I.subscheme.Opens) ≤ _) s) := by
    rw [htop]
    trivial
  rw [hloc] at hzx'_mem
  have : I.subschemeι zx' ∈ L.famLocus ⊤ s := hzx'_mem.2
  rw [hzx'] at this
  exact hf₀x' ((hsx x' hx'V).1 this)

include k in
omit [IsAlgClosed k] [ConnectedSpace A.left] [IsProper A.hom] in
lemma locallyOfFiniteType_mulN_left (n : ℕ) : LocallyOfFiniteType (mulN A n).left := by
  have : LocallyOfFiniteType ((mulN A n).left ≫ A.hom) := by rw [Over.w]; infer_instance
  exact locallyOfFiniteType_of_comp _ A.hom

include k in
omit [IsAlgClosed k] [Smooth A.hom] [ConnectedSpace A.left] in
lemma isProper_mulN_left (n : ℕ) : IsProper (mulN A n).left := by
  have : IsProper ((mulN A n).left ≫ A.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp _ A.hom

omit [IsAlgClosed k] in
/-- From the cube relation (`hrel`): for `n > 0`, multiplication by `n` on an abelian variety is
quasi-finite at every closed point. -/
theorem quasiFiniteAt_mulN_of_isClosed [IsCommMonObj A] (hrel : CubeRelation A) {n : ℕ}
    (hn : 0 < n) {x : A.left} (hxc : IsClosed {x}) : (mulN A n).left.QuasiFiniteAt x := by
  set f := (mulN A n).left with hf
  have := locallyOfFiniteType_mulN_left A n
  have := isProper_mulN_left A n
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := { }
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← (f.fiberHomeo (f x)).isOpen_image,
    Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply]
  by_contra h
  obtain ⟨C, hC, hpC, hCne⟩ := exists_mem_irreducibleComponents_ne_singleton h
  have hFclosed : IsClosed (f ⁻¹' {f x}) := by
    have : IsClosed {f x} := by simpa using f.isClosedMap _ hxc
    exact this.preimage f.continuous
  have hCcl : IsClosed (Subtype.val '' C) :=
    hFclosed.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_of_mem_irreducibleComponents C hC)
  have hCirr : IsIrreducible (Subtype.val '' C) := hC.1.image _ continuous_subtype_val.continuousOn
  let Z : TopologicalSpace.Closeds A.left := ⟨_, hCcl⟩
  have hxZ : x ∈ Z := ⟨_, hpC, rfl⟩
  have hZy : ∀ z ∈ Z, f z = f x := by
    rintro _ ⟨⟨z, hz⟩, -, rfl⟩
    exact hz
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    A.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  replace hV : IsAffineOpen V := hV
  have hne : ((Z : Set A.left) ∩ V ∩ {x}ᶜ).Nonempty := by
    by_contra hem
    rw [Set.not_nonempty_iff_eq_empty] at hem
    apply hCne
    have hsub : (Z : Set A.left) ∩ V ⊆ {x} := fun w hw ↦ by
      by_contra hwx
      have : w ∈ (Z : Set A.left) ∩ V ∩ {x}ᶜ := ⟨hw, hwx⟩
      rw [hem] at this
      exact this
    have hZx : (Z : Set A.left) ⊆ {x} := by
      refine (subset_closure_inter_of_isPreirreducible_of_isOpen hCirr.isPreirreducible V.isOpen
        ⟨x, hxZ, hxV⟩).trans ?_
      rw [← hxc.closure_eq]
      exact closure_mono hsub
    ext ⟨w, hw⟩
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hwC
      have : w = x := hZx ⟨⟨w, hw⟩, hwC, rfl⟩
      subst this
      rfl
    · intro hw'
      rw [hw']
      exact hpC
  obtain ⟨x', ⟨⟨hx'Z, hx'V⟩, hx'x⟩, hx'c⟩ := nonempty_inter_closedPoints hne
    ((hCcl.isLocallyClosed.inter V.isOpen.isLocallyClosed).inter hxc.isOpen_compl.isLocallyClosed)
  exact hx'x (eq_of_forall_mulN_eq A hrel hn Z hCirr (f x) hZy hV hxZ hx'Z hxV hx'V hxc
    hx'c).symm

omit [IsAlgClosed k] in
/-- From the cube relation (`hrel`): for `n > 0`, multiplication by `n` on an abelian variety is
locally quasi-finite. -/
theorem locallyQuasiFinite_mulN [IsCommMonObj A] (hrel : CubeRelation A) {n : ℕ} (hn : 0 < n) :
    LocallyQuasiFinite (mulN A n).left := by
  have := locallyOfFiniteType_mulN_left A n
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  by_contra h
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints
    (Z := ((mulN A n).left.quasiFiniteLocus : Set A.left)ᶜ)
    (by rwa [Set.nonempty_compl, ne_eq, TopologicalSpace.Opens.coe_eq_univ])
    (mulN A n).left.quasiFiniteLocus.isOpen.isClosed_compl.isLocallyClosed
  exact hx (quasiFiniteAt_mulN_of_isClosed A hrel hn hxc)

omit [IsAlgClosed k] in
/-- SGA 1 XI.2, from the cube relation (`hrel`): for `n > 0`, multiplication by `n` on a proper,
smooth, connected commutative group scheme `A` over a field `k` satisfying `CubeRelation A` is
finite and surjective (an isogeny). -/
theorem mulNIsogeny_of_cubeRelation [IsCommMonObj A] (hrel : CubeRelation A) {n : ℕ}
    (hn : 0 < n) : IsFinite (mulN A n).left ∧ Surjective (mulN A n).left := by
  have := isProper_mulN_left A n
  have := locallyQuasiFinite_mulN A hrel hn
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsIntegral A.left := isIntegral_left A
  have : Nonempty (𝟙_ (Over (Spec (.of k)))).left := inferInstanceAs (Nonempty (Spec (.of k)))
  have : IsDominant (mulN A n).left := isDominant_of_locallyQuasiFinite_of_apply_eq _
    (x := (η[A] : 𝟙_ _ ⟶ A).left (Nonempty.some inferInstance)) (by
      have hη : (η : 𝟙_ _ ⟶ A) = 1 := by
        rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, mulN, comp_pow, Category.comp_id, hη,
        _root_.one_pow])
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, inferInstance⟩

end Kernel

/-- SGA 1 XI.2: if the cube relation (Mumford §6, Corollary 2) holds on every abelian variety, then
multiplication by `n > 0` on an abelian variety over an algebraically closed field is an isogeny
(`MulNIsogenyStatement`). -/
theorem mulNIsogenyStatement_of_cubeRelation
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
      [IsProper A.hom] [Smooth A.hom] [ConnectedSpace A.left],
      haveI := isCommMonObj_of_smooth A
      CubeRelation A) :
    MulNIsogenyStatement.{u} := fun k _ _ A _ _ _ _ _ hn ↦
  haveI := isCommMonObj_of_smooth A
  mulNIsogeny_of_cubeRelation A (h k A) hn

/-- SGA 1 XI.2: the theorem of the cube implies that multiplication by `n > 0` on an abelian
variety over an algebraically closed field is an isogeny (`MulNIsogenyStatement`). -/
theorem mulNIsogenyStatement_of_theoremOfTheCube (hcube : TheoremOfTheCubeStatement.{u}) :
    MulNIsogenyStatement.{u} :=
  mulNIsogenyStatement_of_cubeRelation fun _ _ _ A _ _ _ _ ↦
    haveI := isCommMonObj_of_smooth A
    cubeRelation_of_theoremOfTheCube hcube

/-- XI.2.1 (both parts) from the theorem of the cube (`hcube`), in every characteristic: SGA's
cited input "`n_A` is an isogeny" is `mulNIsogenyStatement_of_theoremOfTheCube`. -/
theorem abelianVarietyFundamentalGroupStatement_of_theoremOfTheCube
    (hcube : TheoremOfTheCubeStatement.{u}) : AbelianVarietyFundamentalGroupStatement.{u} :=
  abelianVarietyFundamentalGroupStatement_of_mulNIsogeny
    (mulNIsogenyStatement_of_theoremOfTheCube hcube)

/-- XI.2.1, last clause (`T_ℓ(A)` is the `ℓ`-primary component of `π₁(A)`, every prime `ℓ`), from
the theorem of the cube (`hcube`). -/
theorem abelianVarietyPrimaryComponentStatement_of_theoremOfTheCube
    (hcube : TheoremOfTheCubeStatement.{u}) : AbelianVarietyPrimaryComponentStatement.{u} :=
  abelianVarietyPrimaryComponentStatement_of_mulNIsogeny
    (mulNIsogenyStatement_of_theoremOfTheCube hcube)

/-- SGA 1 XI.2 from the openness step of the theorem of the cube (`hO`,
`AlgebraicGeometry.CubeOpennessStatement`): multiplication by `n > 0` on an abelian variety over
an algebraically closed field is an isogeny. -/
theorem mulNIsogenyStatement_of_cubeOpenness (hO : CubeOpennessStatement.{u}) :
    MulNIsogenyStatement.{u} :=
  mulNIsogenyStatement_of_cubeRelation fun _ _ _ A _ _ _ _ ↦
    haveI := isCommMonObj_of_smooth A
    cubeRelation_of_cubeOpenness hO

/-- XI.2.1 (both parts), in every characteristic, from the openness step of the theorem of the
cube (`hO`). -/
theorem abelianVarietyFundamentalGroupStatement_of_cubeOpenness
    (hO : CubeOpennessStatement.{u}) : AbelianVarietyFundamentalGroupStatement.{u} :=
  abelianVarietyFundamentalGroupStatement_of_mulNIsogeny (mulNIsogenyStatement_of_cubeOpenness hO)

/-- XI.2.1, last clause (every prime `ℓ`), from the openness step of the theorem of the cube
(`hO`). -/
theorem abelianVarietyPrimaryComponentStatement_of_cubeOpenness
    (hO : CubeOpennessStatement.{u}) : AbelianVarietyPrimaryComponentStatement.{u} :=
  abelianVarietyPrimaryComponentStatement_of_mulNIsogeny (mulNIsogenyStatement_of_cubeOpenness hO)

end SGA.SGA1.ExposeXI
