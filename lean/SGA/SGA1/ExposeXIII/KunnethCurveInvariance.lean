/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.KunnethCurveKummer
import SGA.SGA1.ExposeXIII.KunnethFiniteEtale

/-!
# SGA 1, XIII.4.6 in characteristic `0`: invariance for open subsets of the affine line

This file proves milestone C1 of the resolution-free route to XIII.4.6 in characteristic `0`,
`AffineLineOpenInvarianceStatement` (`affineLineOpenInvarianceStatement`): for `k` algebraically
closed of characteristic `0` and `g ≠ 0`, base change along an algebraically closed extension
`k ⊆ k'` is an equivalence `FEt(Spec k[X]_g) ≌ FEt(Spec k'[X]_g)`. With
`SGA.SGA1.ExposeXIII.KunnethTower` this gives the invariance property for every smooth (or normal)
quasi-compact quasi-separated connected scheme of finite type over `k`.

The proof follows the curve case of SGA 1 XIII.4.6 (XIII.5.2 and X.1.8), without resolution of
singularities. After translating a root of `g` to `0`
(`affineLineOpenInvarianceStatement_of_isRoot_zero`), `Spec k[X]_g` is the affine open
`U = D(g) ⊆ 𝔸¹ ⊆ ℙ¹`. Let `W` be a connected étale covering of `U' = U ⊗ₖ k'`, of rank `d`, and
`N = d!`.

* `hasAlgClosedBaseChangeInvariance_of_forall_exists_hom_of_isPullback`: the domination criterion
  `hasAlgClosedBaseChangeInvariance_of_forall_exists_hom` for any choice of pullback square.
* `exists_comp_toNormalization`: the open `π'⁻¹ pr⁻¹ U` of `C' = C̄ ×_{ℙ¹} ℙ¹_{k'}` maps to `V`.
* `exists_iso_pullback_compactification`: for a connected component `V` of the Kummer covering of
  exponent `N` with compactification `C̄` (normalization of `ℙ¹` in `V`, smooth and proper), the
  pullback of `W` to `π'⁻¹ U'` extends to an étale covering of `C'`: purity on the regular curve
  `C'` (`SGA.SGA1.ExposeX.finite_etale_fromNormalization_of_isRegularScheme`), with Abhyankar's
  lemma (`isEtaleAt_integralClosure_chart`) on the two charts and the Kummer roots of
  `SGA.SGA1.ExposeXIII.KunnethCurveKummer`.
* `exists_isConnected_hom_pullback_lineOpen`: by X.1.8 for `C̄`
  (`isEquivalence_pullback_compactification`) the extension comes from an étale covering `Ē` of
  `C̄`; a connected component `E` of `Ē|_V ⟶ V ⟶ U` has a morphism `E ⊗ₖ k' ⟶ W`.
* `hasAlgClosedBaseChangeInvariance_lineOpen`, `fromSpec_comp_toSpec`,
  `affineLineOpenInvarianceStatement`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Polynomial PreGaloisCategory

namespace SGA.SGA1.ExposeXIII

set_option backward.isDefEq.respectTransparency false in
/-- The domination criterion `hasAlgClosedBaseChangeInvariance_of_forall_exists_hom` with any
pullback square `P = X ×ₖ k'` (chosen for each `k'`) in place of the canonical pullback. -/
theorem hasAlgClosedBaseChangeInvariance_of_forall_exists_hom_of_isPullback {k : Type u}
    [Field k] [IsAlgClosed k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [ConnectedSpace X]
    (h : ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k'],
      ∃ (P : Scheme.{u}) (fst : P ⟶ X) (snd : P ⟶ Spec (.of k')),
        IsPullback fst snd sX (Spec.map (CommRingCat.ofHom (algebraMap k k'))) ∧
        ∀ W : ExposeV.FEt P, IsConnected W → ∃ (E : ExposeV.FEt X) (_ : IsConnected E),
          Nonempty ((ExposeV.FEt.pullback fst).obj E ⟶ W)) :
    HasAlgClosedBaseChangeInvariance sX := by
  refine hasAlgClosedBaseChangeInvariance_of_forall_exists_hom fun k' _ _ _ W hW ↦ ?_
  obtain ⟨P, fst, snd, H, hP⟩ := h k'
  let e := H.isoPullback
  have he : fst = e.hom ≫ pullback.fst _ _ := H.isoPullback_hom_fst.symm
  have hW' : IsConnected ((ExposeV.FEt.pullback e.hom).obj W) := by
    rw [ExposeV.FEt.isConnected_iff_connectedSpace] at hW ⊢
    have : IsIso (pullback.fst W.hom e.hom) := inferInstance
    exact (Scheme.homeoOfIso (asIso (pullback.fst W.hom e.hom))).symm.connectedSpace_iff.mp hW
  obtain ⟨E, hE, ⟨f⟩⟩ := hP _ hW'
  let i := (MorphismProperty.Over.pullbackComp e.hom (pullback.fst _ _) fst he).app E
  exact ⟨E, hE, ⟨(ExposeV.FEt.pullback e.hom).preimage (i.inv ≫ f)⟩⟩

end SGA.SGA1.ExposeXIII

namespace SGA.SGA1.ExposeXIII.KummerCompactification

open SGA.SGA1.ExposeXI.ProjectiveLine SGA.SGA1.ExposeXI

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {g : k[X]}

local notation "ℙ¹" => Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

/-- `Spec k' ⟶ Spec k`. -/
local notation "ρ" k' => Spec.map (CommRingCat.ofHom (algebraMap k k'))

set_option backward.isDefEq.respectTransparency false in
/-- The open `π'⁻¹ pr⁻¹ U` of a base change `C' = C̄ ×_{ℙ¹} P'` of the compactification `C̄` of a
covering `V` of `U` maps to `V` (as `π⁻¹ U ≅ V`, `isOpenImmersion_toNormalization`), over `ℙ¹`. -/
lemma exists_comp_toNormalization (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g)))
    {P' C' : Scheme.{u}} {pr : P' ⟶ ℙ¹} {π' : C' ⟶ P'} {prC : C' ⟶ (toLine V).normalization}
    (hC : IsPullback prC π' (toLine V).fromNormalization pr) :
    ∃ a : (π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).toScheme ⟶ V.left,
      a ≫ (toLine V).toNormalization = (π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).ι ≫ prC ∧
      a ≫ toLine V = (π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).ι ≫ π' ≫ pr := by
  obtain ⟨_, hr⟩ := isOpenImmersion_toNormalization V
  have hrange : Set.range ((π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).ι ≫ prC) ⊆
      Set.range (toLine V).toNormalization := by
    rintro _ ⟨x, rfl⟩
    rw [hr]
    change ((π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).ι ≫ prC ≫ (toLine V).fromNormalization) x ∈
      (lineOpen k g : Set ℙ¹)
    rw [hC.w]
    exact x.2
  refine ⟨IsOpenImmersion.lift _ _ hrange, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have h := (toLine V).toNormalization_fromNormalization
  calc _ = IsOpenImmersion.lift _ _ hrange ≫ (toLine V).toNormalization ≫
        (toLine V).fromNormalization := by rw [h]
    _ = _ := by rw [IsOpenImmersion.lift_fac_assoc, Category.assoc, hC.w]

set_option backward.isDefEq.respectTransparency false in
/-- The extension step of XIII.4.6 in characteristic `0` (purity, X.3.1, with Abhyankar's lemma
XIII.5.2 as input). Let `k` be algebraically closed of characteristic `0`, `g ≠ 0` with `g(0) = 0`,
`k'` an algebraically closed extension, `P' = ℙ¹ ×ₖ k'` (`hP`), `V` a connected covering of
`U = D(g)` with a morphism `φ` to the Kummer covering `kummerCovering k g N`, and
`C' = C̄ ×_{ℙ¹} P'` (`hC`) the base change of the compactification `C̄` of `V`. Let
`p : Z ⟶ U' = pr⁻¹ U` be an étale covering such that `N ≠ 0` and `m ∣ N` for `0 < m ≤ d`, where
`d` is the rank of `Γ(Z)` over `Γ(U')`, and `w : W' ⟶ π'⁻¹ U'` its pullback (`hpb`). If `π'⁻¹ U'`
is nonempty, `w` extends to an étale covering `Y` of `C'`. -/
theorem exists_iso_pullback_compactification [IsAlgClosed k] [CharZero k] [DecidableEq k]
    (hg : g ≠ 0) (hg0 : g.IsRoot 0) (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k']
    {P' : Scheme.{u}} {pr : P' ⟶ ℙ¹} {sP' : P' ⟶ Spec (.of k')}
    (hP : IsPullback pr sP' (toSpec k) (ρ k')) {N : ℕ} [NeZero N]
    (V : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) [IsConnected V]
    (φ : V ⟶ kummerCovering k g N) {C' : Scheme.{u}} {π' : C' ⟶ P'}
    {prC : C' ⟶ (toLine V).normalization}
    (hC : IsPullback prC π' (toLine V).fromNormalization pr)
    {Z : Scheme.{u}} (p : Z ⟶ (pr ⁻¹ᵁ lineOpen k g).toScheme) [IsFinite p] [Etale p]
    (hN : ∀ m, 0 < m → m ≤ (letI := (p.appLE ⊤ ⊤ le_top).hom.toAlgebra;
      Module.finrank Γ((pr ⁻¹ᵁ lineOpen k g).toScheme, ⊤) Γ(Z, ⊤)) → m ∣ N)
    (hne : (π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g : Set C').Nonempty)
    {W' : Scheme.{u}} {pW : W' ⟶ Z} {w : W' ⟶ (π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).toScheme}
    (hpb : IsPullback pW w p (π' ∣_ (pr ⁻¹ᵁ lineOpen k g))) [IsFinite w] [Etale w] :
    ∃ Y : ExposeV.FEt C', Nonempty ((ExposeV.FEt.pullback (π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).ι).obj Y ≅
      MorphismProperty.Over.mk ⊤ w ⟨inferInstance, inferInstance⟩) := by
  obtain ⟨-, hint, hreg, _, _⟩ :=
    smooth_isIntegral_isRegularScheme_pullback_compactification k' hP V hg hg0 hC
  obtain ⟨a, -, ha⟩ := exists_comp_toNormalization V hC
  have : IsAffineHom pr := MorphismProperty.of_isPullback hP.flip inferInstance
  have : CharZero k' := charZero_of_injective_algebraMap (algebraMap k k').injective
  let d : Fin 2 → LineChart g := ![lineChart₀ hg, lineChart₁ hg hg0]
  have hK (i : Fin 2) (c : k) (hc : (d i).g₀.IsRoot c) : ∃ (y₀ : Γ(V.left, ⊤)) (u₀ : k[X]),
      ¬ u₀.IsRoot c ∧ y₀ ^ N * chartPullback V (d i) u₀ = chartPullback V (d i) (X - C c) := by
    fin_cases i
    · exact exists_pow_mul_eq_chartPullback₀ hg φ c hc
    · exact exists_pow_mul_eq_chartPullback₁ hg hg0 φ c hc
  have hle (i : Fin 2) : π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g ≤ π' ⁻¹ᵁ pr ⁻¹ᵁ (d i).O :=
    π'.preimage_mono (pr.preimage_mono (d i).le)
  have hfe := ExposeX.finite_etale_fromNormalization_of_isRegularScheme w hreg hne
    (fun i ↦ π' ⁻¹ᵁ pr ⁻¹ᵁ (d i).O)
    (fun i ↦ ((d i).isAffineOpen.preimage pr).preimage π') (fun i ↦ hne.mono (hle i)) ?_
    (fun i ↦ π'.app (pr ⁻¹ᵁ (d i).O)
      (chartEquiv' k' hP (d i).isAffineOpen (d i).φ (d i).φ_C ((d i).g₀.map (algebraMap k k'))))
    (fun i ↦ ?_) (fun i ↦ ?_)
  · obtain ⟨h₁, h₂⟩ := hfe
    exact ExposeX.exists_iso_pullback_of_fromNormalization w
  · rw [eq_top_iff]
    intro x _
    have hx : pr (π' x) ∈ chart₀ k ⊔ chart₁ k := by rw [chart₀_sup_chart₁]; trivial
    rcases hx with hx | hx
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨0, hx⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨1, hx⟩
  · rw [← Scheme.preimage_basicOpen, basicOpen_chartEquiv'_map, (d i).basicOpen_eq,
      inf_eq_right.mpr (hle i)]
  · exact isEtaleAt_integralClosure_chart π' (ExposeX.isNormalScheme_of_isRegularScheme hreg)
      ((d i).isAffineOpen.preimage pr) (chartEquiv' k' hP (d i).isAffineOpen (d i).φ (d i).φ_C)
      ((d i).g₀.map (algebraMap k k')) (pr.preimage_mono (d i).le)
      (by rw [basicOpen_chartEquiv'_map, (d i).basicOpen_eq]) hne p hpb N hN
      (exists_pow_mul_eq_chart k' hP V a ha (d i) N (hK i))

lemma nontrivial_kummerRing [CharZero k] [DecidableEq k] (hg : g ≠ 0) (N : ℕ)
    [NeZero N] : Nontrivial (kummerRing k g N) := by
  have : IsDomain Γ(ℙ¹, lineOpen k g) := isDomain_sections_lineOpen k g hg
  let F := AlgebraicClosure (FractionRing Γ(ℙ¹, lineOpen k g))
  have hx : ∀ a : g.roots.toFinset, ∃ x : F, x ^ N = algebraMap _ F (radicand k g a.1) :=
    fun a ↦ IsAlgClosed.exists_pow_nat_eq _ (Nat.pos_of_ne_zero (NeZero.ne N))
  choose x hx using hx
  exact (KummerAlgebra.lift (n := fun _ : g.roots.toFinset ↦ N) x hx).toRingHom.domain_nontrivial

/-- The domination step of XIII.4.6 in characteristic `0` for `U = D(g) ⊆ 𝔸¹` (`g ≠ 0`,
`g(0) = 0`, `k` algebraically closed of characteristic `0`): for an algebraically closed extension
`k'`, `P' = ℙ¹ ×ₖ k'` (`hP`) and a connected étale covering `W` of `U' = pr⁻¹ U = U ×ₖ k'`, some
connected étale covering `E` of `Spec Γ(U)` has a morphism `E ×ₖ k' ⟶ W`. Proof: `E` is a
component of `Ē|_V ⟶ V ⟶ U`, where `V` is a component of the Kummer covering of exponent
`N = (rank W)!` and `Ē` the étale covering of the compactification `C̄` of `V` whose base change to
`C̄ ×_{ℙ¹} P'` extends `W` (`exists_iso_pullback_compactification` and X.1.8,
`isEquivalence_pullback_compactification`). -/
theorem exists_isConnected_hom_pullback_lineOpen [IsAlgClosed k] [CharZero k] (hg : g ≠ 0)
    (hg0 : g.IsRoot 0) (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k']
    {P' : Scheme.{u}} {pr : P' ⟶ ℙ¹} {sP' : P' ⟶ Spec (.of k')}
    (hP : IsPullback pr sP' (toSpec k) (ρ k'))
    (W : ExposeV.FEt (pr ⁻¹ᵁ lineOpen k g).toScheme) [IsConnected W] :
    ∃ (E : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g))) (_ : IsConnected E),
      Nonempty ((ExposeV.FEt.pullback
        ((pr ∣_ lineOpen k g) ≫ (isAffineOpen_lineOpen g).isoSpec.hom)).obj E ⟶ W) := by
  classical
  have hU := isAffineOpen_lineOpen g
  let p : W.left ⟶ (pr ⁻¹ᵁ lineOpen k g).toScheme := W.hom
  have : IsFinite p := W.prop.1
  have : Etale p := W.prop.2
  have : IsDomain Γ(ℙ¹, lineOpen k g) := isDomain_sections_lineOpen k g hg
  have : ConnectedSpace (PrimeSpectrum Γ(ℙ¹, lineOpen k g)) :=
    @IrreducibleSpace.connectedSpace _ _ (PrimeSpectrum.irreducibleSpace)
  have : ConnectedSpace (Spec Γ(ℙ¹, lineOpen k g)) := ‹ConnectedSpace (PrimeSpectrum _)›
  -- the exponent `N = (rank W)!` and a connected component `V` of the Kummer covering
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N ≠ 0 ∧ ∀ m, 0 < m → m ≤ (letI := (p.appLE ⊤ ⊤ le_top).hom.toAlgebra;
      Module.finrank Γ((pr ⁻¹ᵁ lineOpen k g).toScheme, ⊤) Γ(W.left, ⊤)) → m ∣ N :=
    ⟨_, Nat.factorial_ne_zero _, fun m hm hle ↦ Nat.dvd_factorial hm hle⟩
  have : NeZero N := ⟨hN.1⟩
  have : Nontrivial (kummerRing k g N) := nontrivial_kummerRing hg N
  have : Nonempty (kummerCovering k g N).left :=
    inferInstanceAs (Nonempty (PrimeSpectrum (kummerRing k g N)))
  obtain ⟨V, φ, hV⟩ := exists_isConnected_hom (kummerCovering k g N)
  have : Nonempty V.left := (ExposeV.FEt.connectedSpace_of_isConnected V).toNonempty
  -- the base change `C'` of the compactification and the pullback `W''` of `W` to `π'⁻¹ U'`
  obtain ⟨C', prC, π', hC⟩ : ∃ (C' : Scheme.{u}) (prC : C' ⟶ (toLine V).normalization)
      (π' : C' ⟶ P'), IsPullback prC π' (toLine V).fromNormalization pr :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨W'', pW, w, hpb⟩ : ∃ (W'' : Scheme.{u}) (pW : W'' ⟶ W.left)
      (w : W'' ⟶ (π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).toScheme),
      IsPullback pW w p (π' ∣_ (pr ⁻¹ᵁ lineOpen k g)) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have : IsFinite w := MorphismProperty.of_isPullback hpb inferInstance
  have : Etale w := MorphismProperty.of_isPullback hpb inferInstance
  obtain ⟨a, ha, -⟩ := exists_comp_toNormalization V hC
  -- `W''` is nonempty
  obtain ⟨w₀⟩ : Nonempty W.left := (ExposeV.FEt.connectedSpace_of_isConnected W).toNonempty
  obtain ⟨s, hs⟩ : (pr (p w₀).1) ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]; exact (p w₀).2
  obtain ⟨v, hv⟩ : s ∈ Set.range V.toBase := by
    rw [ExposeV.FEt.range_eq_univ V]; trivial
  obtain ⟨z, -, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    ((toLine V).toNormalization v) (p w₀).1 (by
      rw [← Scheme.Hom.comp_apply, (toLine V).toNormalization_fromNormalization, ← hs, ← hv]
      rfl)
  have hz₂' : π' (hC.isoPullback.inv z) = (p w₀).1 := by
    rw [← hz₂, ← Scheme.Hom.comp_apply, hC.isoPullback_inv_snd]
  have hzU : hC.isoPullback.inv z ∈ π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g := by
    change pr (π' (hC.isoPullback.inv z)) ∈ lineOpen k g
    rw [hz₂']
    exact (p w₀).2
  have hne : (π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g : Set C').Nonempty := ⟨_, hzU⟩
  obtain ⟨w₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p)
    (g := π' ∣_ (pr ⁻¹ᵁ lineOpen k g)) w₀ ⟨_, hzU⟩ (by
      apply Subtype.ext
      set_option backward.isDefEq.respectTransparency false in
      rw [morphismRestrict_base_coe]
      exact hz₂'.symm)
  -- extension over `C'` (purity) and descent to `C̄` (X.1.8)
  obtain ⟨Y, ⟨eW⟩⟩ := exists_iso_pullback_compactification hg hg0 k' hP V φ hC p hN.2 hne hpb
  have := isEquivalence_pullback_compactification k' hP V hg hg0 hC
  obtain ⟨Ē, ⟨eY⟩⟩ : ∃ Ē, Nonempty ((ExposeV.FEt.pullback prC).obj Ē ≅ Y) :=
    ⟨_, ⟨(ExposeV.FEt.pullback prC).objObjPreimageIso Y⟩⟩
  -- the covering `E₁ = Ē|_V ⟶ V ⟶ Spec Γ(U)`
  let eb : Ē.left ⟶ (toLine V).normalization := Ē.hom
  let yh : Y.left ⟶ C' := Y.hom
  let v₀ : V.left ⟶ Spec Γ(ℙ¹, lineOpen k g) := V.hom
  have : IsFinite eb := Ē.prop.1
  have : Etale eb := Ē.prop.2
  have : IsFinite v₀ := V.prop.1
  have : Etale v₀ := V.prop.2
  obtain ⟨E₀, ε, e₀, hE⟩ : ∃ (E₀ : Scheme.{u}) (ε : E₀ ⟶ Ē.left) (e₀ : E₀ ⟶ V.left),
      IsPullback ε e₀ eb (toLine V).toNormalization :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have : IsFinite e₀ := MorphismProperty.of_isPullback hE inferInstance
  have : Etale e₀ := MorphismProperty.of_isPullback hE inferInstance
  let E₁ : ExposeV.FEt (Spec Γ(ℙ¹, lineOpen k g)) :=
    MorphismProperty.Over.mk ⊤ (e₀ ≫ v₀) ⟨inferInstance, inferInstance⟩
  let U''ι := (π' ⁻¹ᵁ pr ⁻¹ᵁ lineOpen k g).ι
  let iY : Y.left ⟶ pullback eb prC := eY.inv.left
  let jY : pullback eb prC ⟶ Y.left := eY.hom.left
  let iW : W'' ⟶ pullback yh U''ι := eW.inv.left
  let jW : pullback yh U''ι ⟶ W'' := eW.hom.left
  have hiY : iY ≫ pullback.snd eb prC = yh := MorphismProperty.Over.w eY.inv
  have hjY : jY ≫ yh = pullback.snd eb prC := MorphismProperty.Over.w eY.hom
  have hiW : iW ≫ pullback.snd yh U''ι = w := MorphismProperty.Over.w eW.inv
  have hjW : jW ≫ w = pullback.snd yh U''ι := MorphismProperty.Over.w eW.hom
  -- `E₀` is nonempty: `W''` maps to it
  have hE₀ : Nonempty E₀ := by
    have c₁ : pullback.fst eb prC ≫ eb = pullback.snd eb prC ≫ prC := pullback.condition
    have c₂ : pullback.fst yh U''ι ≫ yh = pullback.snd yh U''ι ≫ U''ι := pullback.condition
    have hy' : (iW ≫ pullback.fst yh U''ι ≫ iY ≫ pullback.fst eb prC) ≫ eb =
        (w ≫ a) ≫ (toLine V).toNormalization := by
      calc _ = iW ≫ pullback.fst yh U''ι ≫ iY ≫ pullback.fst eb prC ≫ eb := by
            simp only [Category.assoc]
        _ = iW ≫ pullback.fst yh U''ι ≫ (iY ≫ pullback.snd eb prC) ≫ prC := by
            rw [c₁, Category.assoc]
        _ = iW ≫ (pullback.fst yh U''ι ≫ yh) ≫ prC := by rw [hiY, Category.assoc]
        _ = (iW ≫ pullback.snd yh U''ι) ≫ U''ι ≫ prC := by
            rw [c₂]; simp only [Category.assoc]
        _ = (w ≫ a) ≫ (toLine V).toNormalization := by
            rw [hiW, ← ha, Category.assoc]
    exact ⟨hE.lift _ _ hy' (hpb.isoPullback.inv w₁)⟩
  -- the morphism `E₁ ×ₖ k' ⟶ W`
  let fst : (pr ⁻¹ᵁ lineOpen k g).toScheme ⟶ Spec Γ(ℙ¹, lineOpen k g) :=
    (pr ∣_ lineOpen k g) ≫ hU.isoSpec.hom
  have hq : (pullback.fst (e₀ ≫ v₀) fst ≫ e₀ ≫ (toLine V).toNormalization) ≫
      (toLine V).fromNormalization =
        (pullback.snd (e₀ ≫ v₀) fst ≫ (pr ⁻¹ᵁ lineOpen k g).ι) ≫ pr := by
    have ht : toLine V = v₀ ≫ hU.fromSpec := rfl
    calc _ = (pullback.fst (e₀ ≫ v₀) fst ≫ e₀ ≫ v₀) ≫ hU.fromSpec := by
          rw [Category.assoc, Category.assoc, (toLine V).toNormalization_fromNormalization, ht]
          simp only [Category.assoc]
      _ = (pullback.snd (e₀ ≫ v₀) fst ≫ fst) ≫ hU.fromSpec := by rw [pullback.condition]
      _ = _ := by
          simp only [fst, Category.assoc, hU.isoSpec_hom_fromSpec, morphismRestrict_ι]
  let q := hC.lift _ _ hq
  have hqU : Set.range q ⊆ Set.range U''ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ((q ≫ π') ≫ pr) x ∈ lineOpen k g
    rw [hC.lift_snd]
    exact (pullback.snd (e₀ ≫ v₀) fst x).2
  let q' := IsOpenImmersion.lift U''ι q hqU
  have hyb : (pullback.fst (e₀ ≫ v₀) fst ≫ ε) ≫ eb = q ≫ prC := by
    rw [Category.assoc, hE.w, hC.lift_fst]
  let yb := pullback.lift _ _ hyb
  have hY : (yb ≫ jY) ≫ yh = q' ≫ U''ι := by
    rw [IsOpenImmersion.lift_fac, Category.assoc, hjY, pullback.lift_snd]
  let lY := pullback.lift _ _ hY
  have hm : (lY ≫ jW ≫ pW) ≫ p = pullback.snd (e₀ ≫ v₀) fst := by
    rw [← cancel_mono (pr ⁻¹ᵁ lineOpen k g).ι]
    have c₃ : pW ≫ p = w ≫ (π' ∣_ (pr ⁻¹ᵁ lineOpen k g)) := hpb.w
    calc _ = lY ≫ (jW ≫ w) ≫ (π' ∣_ (pr ⁻¹ᵁ lineOpen k g)) ≫ (pr ⁻¹ᵁ lineOpen k g).ι := by
          simp only [Category.assoc, reassoc_of% c₃]
      _ = (lY ≫ pullback.snd yh U''ι) ≫ U''ι ≫ π' := by
          rw [hjW, morphismRestrict_ι, Category.assoc]
      _ = q ≫ π' := by rw [pullback.lift_snd, IsOpenImmersion.lift_fac_assoc]
      _ = _ := by rw [hC.lift_snd]
  have : Nonempty E₁.left := hE₀
  obtain ⟨E, ψ, hE'⟩ := exists_isConnected_hom E₁
  exact ⟨E, hE', ⟨(ExposeV.FEt.pullback fst).map ψ ≫
    MorphismProperty.Over.homMk (lY ≫ jW ≫ pW) hm⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- XIII.4.6 in characteristic `0`, milestone C1 on `ℙ¹`: for `k` algebraically closed of
characteristic `0` and `g ≠ 0` with `g(0) = 0`, the affine open `U = D(g) ⊆ 𝔸¹ ⊆ ℙ¹`
(as `Spec Γ(U)`) has the invariance property under algebraically closed base change
(the domination criterion with `exists_isConnected_hom_pullback_lineOpen`). -/
theorem hasAlgClosedBaseChangeInvariance_lineOpen [IsAlgClosed k] [CharZero k] (hg : g ≠ 0)
    (hg0 : g.IsRoot 0) :
    HasAlgClosedBaseChangeInvariance ((isAffineOpen_lineOpen g).fromSpec ≫ toSpec k) := by
  have hU := isAffineOpen_lineOpen g
  have : IsDomain Γ(ℙ¹, lineOpen k g) := isDomain_sections_lineOpen k g hg
  have : ConnectedSpace (PrimeSpectrum Γ(ℙ¹, lineOpen k g)) :=
    @IrreducibleSpace.connectedSpace _ _ (PrimeSpectrum.irreducibleSpace)
  have : ConnectedSpace (Spec Γ(ℙ¹, lineOpen k g)) := ‹ConnectedSpace (PrimeSpectrum _)›
  refine hasAlgClosedBaseChangeInvariance_of_forall_exists_hom_of_isPullback fun k' _ _ _ ↦ ?_
  have hP := IsPullback.of_hasPullback (toSpec k) (ρ k')
  refine ⟨_, (pullback.fst (toSpec k) (ρ k') ∣_ lineOpen k g) ≫ hU.isoSpec.hom,
    (pullback.fst (toSpec k) (ρ k') ⁻¹ᵁ lineOpen k g).ι ≫ pullback.snd _ _, ?_,
    fun W _ ↦ exists_isConnected_hom_pullback_lineOpen hg hg0 k' hP W⟩
  refine ((isPullback_morphismRestrict _ (lineOpen k g)).paste_vert hP).of_iso (Iso.refl _)
    hU.isoSpec (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_ (by simp)
  rw [← hU.isoSpec_inv_ι]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The structure morphism `Spec Γ(U) ⟶ ℙ¹ ⟶ Spec k` is `Spec` of `k → Γ(U)`. -/
lemma fromSpec_comp_toSpec (g : k[X]) :
    (isAffineOpen_lineOpen g).fromSpec ≫ toSpec k =
      Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ (toSpec k).appLE ⊤ (lineOpen k g) le_top) := by
  have h1 : toSpec k =
      (ℙ¹).toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ (toSpec k).appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  conv_lhs => rw [h1]
  rw [IsAffineOpen.fromSpec_toSpecΓ_assoc, ← Spec.map_comp]
  rfl

end SGA.SGA1.ExposeXIII.KummerCompactification

namespace SGA.SGA1.ExposeXIII

open KummerCompactification SGA.SGA1.ExposeXI.ProjectiveLine SGA.SGA1.ExposeXI

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- **XIII.4.6 in characteristic `0`, milestone C1** (`AffineLineOpenInvarianceStatement`): for
`k` algebraically closed of characteristic `0` and `g ≠ 0`, `Spec k[X]_g` has the invariance
property under algebraically closed base change: for every algebraically closed `k' ⊇ k`, base
change `FEt(Spec k[X]_g) ⥤ FEt(Spec k'[X]_g)` is an equivalence. Proof (without resolution of
singularities): after translating a root of `g` to `0`
(`affineLineOpenInvarianceStatement_of_isRoot_zero`), `Spec k[X]_g ≅ U = D(g) ⊆ ℙ¹`, and
`hasAlgClosedBaseChangeInvariance_lineOpen`: every connected covering of `U ⊗ₖ k'` is dominated
by one from `U`, obtained from a Kummer covering of `U` (exponent `(rank)!`), Abhyankar's lemma
in characteristic `0` and purity on the smooth compactification, and X.1.8 there. -/
theorem affineLineOpenInvarianceStatement : AffineLineOpenInvarianceStatement.{u} := by
  refine affineLineOpenInvarianceStatement_of_isRoot_zero fun k _ _ _ g hg hg0 ↦ ?_
  let : Algebra k[X] Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k), lineOpen k g) :=
    (((Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).presheaf.map
      (homOfLE (lineOpen_le_chart₀ g)).op).hom.comp (chartEquiv₀ k).symm.toRingHom).toAlgebra
  have := isLocalization_lineOpen₀ g
  let ψ : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k), lineOpen k g) ≃+*
      Localization.Away g :=
    (IsLocalization.algEquiv (Submonoid.powers g) _ (Localization.Away g)).toRingEquiv
  let i : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k), lineOpen k g) ≅
      CommRingCat.of (Localization.Away g) := ψ.toCommRingCatIso
  refine (hasAlgClosedBaseChangeInvariance_lineOpen hg hg0).of_iso (Scheme.Spec.mapIso i.op) ?_
  change Spec.map i.hom ≫ _ = _
  rw [fromSpec_comp_toSpec, ← Spec.map_comp]
  congr 1
  ext x
  change ψ ((toSpec k).appLE ⊤ (lineOpen k g) le_top ((Scheme.ΓSpecIso (.of k)).inv x)) =
    algebraMap k (Localization.Away g) x
  rw [← LineChart.res_C (lineChart₀ hg) x]
  change ψ (algebraMap k[X] _ (C x)) = _
  rw [IsScalarTower.algebraMap_apply k k[X] (Localization.Away g), Polynomial.algebraMap_eq]
  exact (IsLocalization.algEquiv (Submonoid.powers g) _ (Localization.Away g)).commutes (C x)

end SGA.SGA1.ExposeXIII
