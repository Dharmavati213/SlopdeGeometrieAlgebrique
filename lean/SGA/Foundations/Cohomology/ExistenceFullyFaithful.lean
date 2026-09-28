/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.ClosedFibre
import SGA.Foundations.Cohomology.Thickening
import SGA.Foundations.Cohomology.SheafHomCoherent
import SGA.Foundations.Cohomology.ArtinReesHom

/-!
# Grothendieck's existence theorem: full faithfulness

Let `A` be a noetherian ring, complete for the `I`-adic topology, `f : X ⟶ Spec A` proper and
`F`, `G` coherent `𝒪_X`-modules. Then `Hom(F, G) = lim_n Hom(F, G / I^{n+1} G)` (EGA III 5.1.4,
the full faithfulness of `F ↦ (F / I^{n+1} F)_n`):

* `CohomologyAux.eq_zero_of_comp_toQuotientIdealPow_eq_zero`, `eq_of_comp_toQuotientIdealPow_eq`,
  `eq_of_pullback_thickening_map_eq` (uniqueness): by Krull's intersection theorem a morphism
  vanishing modulo all `I^{n+1}` vanishes near `f⁻¹ V(I)`, and every nonempty closed subset of `X`
  meets `f⁻¹ V(I)` (`ClosedFibre`);
* `CohomologyAux.exists_comp_toQuotientIdealPow_eq` (existence): `ℋom(F, G)` is coherent
  (`SheafHomCoherent`); by Artin–Rees for `Hom` (`ArtinReesHom`) the morphisms `vₙ` lift locally to
  sections of `ℋom(F, G)`, well defined modulo `I^{n+1-c}` on a finite affine cover, hence glue to
  a compatible family of global sections of `ℋom(F, G) / I^{n+1}`; the theorem on formal
  functions over a complete base (`toFormalLimit_bijective`) produces the morphism;
* `CohomologyAux.existsUnique_comp_toQuotientIdealPow_eq`: both together;
* `AlgebraicGeometry.grothendieckExistence_fullyFaithful`: the same in terms of the restrictions
  `F|_{X_n}` to the thickenings, i.e. the first half of `GrothendieckExistenceStatement`; the
  translation identifies `ι_{n *} ι_n^* G` with `G / I^{n+1} G` (`thickeningIso`) and the transition
  maps with the restrictions along `X_n ⟶ X_{n+1}` (`CohomologyAux.restrictAlong`,
  `CohomologyAux.thickeningIso_inv_quotientIdealPowMap`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

open AlgebraicGeometry.Scheme.Modules (HomOn homOnTopEquiv sheafHom sheafHomTopEquiv)

namespace AlgebraicGeometry.CohomologyAux

section Local

variable {X : Scheme.{u}}

/-- A morphism of `𝒪_X`-modules vanishing on sections over the basic opens `D(t) ⊆ U` of an affine
open `V ⊇ U` vanishes on sections over `U`. -/
lemma app_eq_zero_of_forall_basicOpen {F G : X.Modules} (d : F ⟶ G) {V : X.Opens}
    (hV : IsAffineOpen V) {U : X.Opens} (hUV : U ≤ V)
    (h : ∀ t : Γ(X, V), X.basicOpen t ≤ U → ∀ m, d.app (X.basicOpen t) m = 0)
    (m : Γ(F, U)) : d.app U m = 0 := by
  apply G.isSheaf.section_ext (U := op U)
  intro x hx
  obtain ⟨t, htU, hxt⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ (hUV hx)
  refine ⟨X.basicOpen t, htU, hxt, ?_⟩
  rw [← hom_app_presheaf_map, h t htU, map_zero]

/-- **Vanishing on a basic open** (EGA I 1.4.1): if `F` is quasi-coherent, `V` affine and the image
of `d.app V : Γ(F, V) → Γ(G, V)` is killed by `s ∈ Γ(X, V)`, then `d` vanishes on all opens
contained in `D(s)`. -/
lemma app_eq_zero_of_smul_eq_zero {F G : X.Modules} [F.IsQuasicoherent] (d : F ⟶ G)
    {V : X.Opens} (hV : IsAffineOpen V) (s : Γ(X, V)) (hs : ∀ m, s • d.app V m = 0)
    {U : X.Opens} (hU : U ≤ X.basicOpen s) (m : Γ(F, U)) : d.app U m = 0 := by
  refine app_eq_zero_of_forall_basicOpen d hV (hU.trans (X.basicOpen_le s)) (fun t ht m' ↦ ?_) m
  obtain ⟨m₀, k, hk⟩ := exists_pow_smul_eq_map F hV t m'
  have htV : X.basicOpen t ≤ V := X.basicOpen_le t
  have hts : X.basicOpen t ≤ X.basicOpen s := ht.trans hU
  -- `d(m₀)` vanishes on `D(t)`
  have h₀ : G.presheaf.map (homOfLE htV).op (d.app V m₀) = 0 := by
    have hu := isUnit_res_of_le_basicOpen s hts
    have e := congrArg (G.presheaf.map (homOfLE htV).op) (hs m₀)
    rw [Scheme.Modules.map_smul, map_zero] at e
    obtain ⟨u, hu⟩ := hu
    rw [← hu] at e
    have := congrArg (fun y ↦ (↑u⁻¹ : Γ(X, X.basicOpen t)) • y) e
    simpa only [smul_smul, Units.inv_mul, one_smul, smul_zero] using this
  -- hence `tᵏ d(m') = 0`
  have h₁ : X.presheaf.map (homOfLE htV).op (t ^ k) • d.app (X.basicOpen t) m' = 0 := by
    rw [← Scheme.Modules.Hom.app_smul, hk, hom_app_presheaf_map, h₀]
  obtain ⟨u, hu⟩ := (isUnit_res_of_le_basicOpen t le_rfl).pow k
  rw [← map_pow] at hu
  have hu' : (u : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE htV).op (t ^ k) := hu
  rw [← hu'] at h₁
  have := congrArg (fun y ↦ (↑u⁻¹ : Γ(X, X.basicOpen t)) • y) h₁
  simpa only [smul_smul, Units.inv_mul, one_smul, smul_zero] using this

end Local

section Krull

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A)

/-- **Krull's intersection theorem on an affine open**: if `d : F ⟶ G` (`F`, `G` coherent, `X`
locally noetherian) vanishes modulo `I^{n+1} G` for all `n`, then on each affine open `V` some
`s ≡ 1 mod I Γ(X, V)` kills the image of `d.app V`. -/
lemma exists_smul_app_eq_zero [IsLocallyNoetherian X] {F G : X.Modules} [F.IsCoherent]
    [G.IsCoherent] (d : F ⟶ G) (hd : ∀ n, d ≫ G.toQuotientIdealPow f I n = 0) {V : X.Opens}
    (hV : IsAffineOpen V) :
    ∃ s : Γ(X, V), s - 1 ∈ idealV f I V 1 ∧ ∀ m, s • d.app V m = 0 := by
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : F.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : G.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : Module.Finite Γ(X, V) Γ(G, V) := finite_sections_of_isFiniteType G hV
  have : Module.Finite Γ(X, V) Γ(F, V) := finite_sections_of_isFiniteType F hV
  let J := idealV f I V 1
  -- the image of `d` lies in `⋂ₙ Jⁿ Γ(G, V)`
  have hmem : ∀ m, d.app V m ∈ (⨅ i : ℕ, J ^ i • ⊤ : Submodule Γ(X, V) Γ(G, V)) := by
    intro m
    refine Submodule.mem_iInf _ |>.mpr fun i ↦ ?_
    cases i with
    | zero => simp
    | succ n =>
      have h0 : (G.toQuotientIdealPow f I n).app V (d.app V m) = 0 := by
        rw [← Scheme.Modules.Hom.comp_app_apply, hd n]
        rfl
      obtain ⟨t, ht⟩ := exists_app_eq_of_shortExact (shortExact_quotientIdealPow f I G n) V _ h0
      have := (mem_range_ιPow_app f I G hV (n + 1) _).mp ⟨t, ht⟩
      rw [idealV, Ideal.map_pow] at this
      have hJ : J = Ideal.map (structMapV f V) I := by simp only [J, idealV, pow_one]
      rw [hJ]
      exact this
  let dl : Γ(F, V) →ₗ[Γ(X, V)] Γ(G, V) :=
    { toFun := d.app V
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul d }
  have hfg : (LinearMap.range dl).FG := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map dl
  have hle : LinearMap.range dl ≤ J • LinearMap.range dl := by
    rintro _ ⟨m, rfl⟩
    obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff J _).mp (hmem m)
    have hr' : (r : Γ(X, V)) • dl m = dl m := hr
    rw [← hr']
    exact Submodule.smul_mem_smul r.2 ⟨m, rfl⟩
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J _ hfg hle
  exact ⟨s, hs1, fun m ↦ hs _ ⟨m, rfl⟩⟩

end Krull

section Complete

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} (f : X ⟶ Spec A) [IsProper f]

/-- **Uniqueness in the Grothendieck existence theorem** (EGA III 5.1.4, injectivity; Stacks Tag
087X): over an `I`-adically complete noetherian base, a morphism `d : F ⟶ G` of coherent modules on
`X` proper over `Spec A` which vanishes modulo `I^{n+1} G` for all `n` is zero. By Krull's
intersection theorem, `d` vanishes near every point of `f⁻¹ V(I)`; the locus where `d` does not
vanish near the point is closed, hence meets `f⁻¹ V(I)` if nonempty
(`exists_mem_zeroLocusPreimage_of_isClosed`). -/
theorem eq_zero_of_comp_toQuotientIdealPow_eq_zero {F G : X.Modules} [F.IsCoherent] [G.IsCoherent]
    (d : F ⟶ G) (hd : ∀ n, d ≫ G.toQuotientIdealPow f I n = 0) : d = 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let Good : Set X := {x | ∃ U : X.Opens, x ∈ U ∧ ∀ U' ≤ U, ∀ m : Γ(F, U'), d.app U' m = 0}
  have hGood : IsOpen Good := isOpen_iff_forall_mem_open.mpr fun x ⟨U, hxU, hU⟩ ↦
    ⟨U, fun y hy ↦ ⟨U, hy, hU⟩, U.isOpen, hxU⟩
  have hW : ∀ x ∈ zeroLocusPreimage I f, x ∈ Good := by
    intro x hx
    obtain ⟨V, hV, hxV, -⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨s, hs1, hs⟩ := exists_smul_app_eq_zero I f d hd hV
    refine ⟨X.basicOpen s, ?_, fun U' hU' m ↦ app_eq_zero_of_smul_eq_zero d hV s hs hU' m⟩
    have h1 := idealV_le_pointIdeal I f hxV hx (neg_mem hs1)
    rw [mem_pointIdeal, Scheme.mem_basicOpen X _ x hxV] at h1
    rw [Scheme.mem_basicOpen X s x hxV]
    have h2 := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ h1
    rwa [neg_sub, map_sub, map_one, sub_sub_cancel] at h2
  have hbad : ∀ x, x ∈ Good := by
    by_contra hne
    push Not at hne
    obtain ⟨x, hx, hxW⟩ := exists_mem_zeroLocusPreimage_of_isClosed I f hGood.isClosed_compl hne
    exact hx (hW x hxW)
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext m
  apply (G.isSheaf.section_ext (U := op U))
  intro x hx
  obtain ⟨U₀, hxU₀, hU₀⟩ := hbad x
  refine ⟨U ⊓ U₀, inf_le_left, ⟨hx, hxU₀⟩, ?_⟩
  rw [← hom_app_presheaf_map, ← hom_app_presheaf_map, hU₀ _ inf_le_right]
  exact ((0 : F ⟶ G).app _).hom.map_zero.symm ▸ rfl

/-- **Uniqueness in the Grothendieck existence theorem**: two morphisms `F ⟶ G` of coherent modules
which agree modulo `I^{n+1} G` for all `n` are equal. -/
theorem eq_of_comp_toQuotientIdealPow_eq {F G : X.Modules} [F.IsCoherent] [G.IsCoherent]
    {u u' : F ⟶ G} (h : ∀ n, u ≫ G.toQuotientIdealPow f I n = u' ≫ G.toQuotientIdealPow f I n) :
    u = u' :=
  sub_eq_zero.mp (eq_zero_of_comp_toQuotientIdealPow_eq_zero I f (u - u') fun n ↦ by
    rw [Preadditive.sub_comp, h n, sub_self])

/-- **Uniqueness in the Grothendieck existence theorem** (EGA III 5.1.4), in the form of
`GrothendieckExistenceStatement`: morphisms of coherent modules with the same restrictions to all
the thickenings `X_n = X ×_A A / I^{n+1}` are equal. -/
theorem eq_of_pullback_thickening_map_eq {F G : X.Modules} [F.IsCoherent] [G.IsCoherent]
    {u u' : F ⟶ G} (h : ∀ n, (Scheme.Modules.pullback (thickening.ι f I n)).map u =
      (Scheme.Modules.pullback (thickening.ι f I n)).map u') : u = u' := by
  have : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  refine eq_of_comp_toQuotientIdealPow_eq I f fun n ↦ ?_
  rw [← cancel_mono (toThickening I f n G), Category.assoc, Category.assoc,
    toQuotientIdealPow_toThickening,
    ← (Scheme.Modules.pullbackPushforwardAdjunction _).unit_naturality,
    ← (Scheme.Modules.pullbackPushforwardAdjunction _).unit_naturality, h n]

end Complete

section Postcomp

variable {X : Scheme.{u}}

/-- Composition of `φ : HomOn M N U` with a morphism `g : N ⟶ N'`. -/
noncomputable def homOnPostcomp {M N N' : X.Modules} {U : X.Opens} (φ : HomOn M N U) (g : N ⟶ N') :
    HomOn M N' U where
  app V hV :=
    { toFun := fun m ↦ g.app V (φ.app V hV m)
      map_add' := fun a b ↦ by rw [map_add, map_add]
      map_smul' := fun r m ↦ by rw [LinearMap.map_smul, Scheme.Modules.Hom.app_smul]; rfl }
  naturality hWV hV m := by
    change g.app _ (φ.app _ _ _) = _
    rw [φ.naturality, hom_app_presheaf_map]
    rfl

@[simp]
lemma homOnPostcomp_app {M N N' : X.Modules} {U : X.Opens} (φ : HomOn M N U) (g : N ⟶ N')
    (V : X.Opens) (hV : V ≤ U) (m : Γ(M, V)) :
    (homOnPostcomp φ g).app V hV m = g.app V (φ.app V hV m) :=
  rfl

/-- If `g ∘ φ` agrees with a morphism `v` on sections over an affine `V` (with `M`
quasi-coherent), it agrees with `v` on sections over every open `W ⊆ V`. -/
lemma homOnPostcomp_app_eq {M N N' : X.Modules} [M.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (φ : HomOn M N V) (g : N ⟶ N') (v : M ⟶ N')
    (h : ∀ m, g.app V (φ.app V le_rfl m) = v.app V m) {W : X.Opens} (hW : W ≤ V) (m : Γ(M, W)) :
    g.app W (φ.app W hW m) = v.app W m := by
  have e : homOnPostcomp φ g = (homOnTopEquiv.symm v).restrict le_top :=
    homOn_ext_of_app_eq hV (LinearMap.ext h)
  exact congr($(e).app W hW m)

end Postcomp

section LocalArtinRees

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A)

/-- The component of a morphism of `𝒪_X`-modules over `V`, as a `Γ(X, V)`-linear map. -/
noncomputable def appₗ {P Q : X.Modules} (g : P ⟶ Q) (V : X.Opens) :
    Γ(P, V) →ₗ[Γ(X, V)] Γ(Q, V) where
  toFun := g.app V
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul g

omit [IsNoetherianRing A] in
lemma idealV_succ_eq (V : X.Opens) (n : ℕ) :
    idealV f I V (n + 1) = idealV f I V 1 ^ (n + 1) := by
  rw [idealV, idealV, Ideal.map_pow, pow_one]

/-- On an affine open, the kernel of `Γ(M, V) → Γ(M / I^{n+1} M, V)` is `I^{n+1} Γ(M, V)`. -/
lemma toQuotientIdealPow_app_eq_zero_iff' (M : X.Modules) [M.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (n : ℕ) (s : Γ(M, V)) :
    (M.toQuotientIdealPow f I n).app V s = 0 ↔
      s ∈ (idealV f I V 1 ^ (n + 1) • ⊤ : Submodule Γ(X, V) Γ(M, V)) := by
  rw [toQuotientIdealPow_app_eq_zero_iff, mem_range_ιPow_app f I M hV, idealV_succ_eq]

/-- **Artin–Rees for `ℋom` on an affine open**, "kernel" half: a section of `ℋom(F, G)` over an
affine `V` whose composite with `G → G / I^{n+c+1} G` vanishes is zero in
`ℋom(F, G) / I^{n+1} ℋom(F, G)`. -/
lemma exists_toQuotientIdealPow_sheafHom_app_eq_zero [IsLocallyNoetherian X] {F G : X.Modules}
    [F.IsCoherent] [G.IsCoherent] {V : X.Opens} (hV : IsAffineOpen V) :
    ∃ c : ℕ, ∀ (n : ℕ) (ψ : HomOn F G V),
      (∀ m, (G.toQuotientIdealPow f I (n + c)).app V (ψ.app V le_rfl m) = 0) →
      ((sheafHom F G).toQuotientIdealPow f I n).app V ψ = 0 := by
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : F.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : G.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have := finite_sections_of_isFiniteType F hV
  have := finite_sections_of_isFiniteType G hV
  have : (sheafHom F G).IsQuasicoherent := isQuasicoherent_sheafHom F G
  let J := idealV f I V 1
  obtain ⟨c, hc⟩ := exists_mem_pow_smul_of_forall_apply_mem J (M := Γ(F, V)) (N := Γ(G, V))
  refine ⟨c, fun n ψ hψ ↦ ?_⟩
  have h1 : ∀ m, sheafHomAffineEquiv hV F G (ψ : Γ(sheafHom F G, V)) m ∈
      (J ^ ((n + 1) + c) • ⊤ : Submodule Γ(X, V) Γ(G, V)) := by
    intro m
    have := (toQuotientIdealPow_app_eq_zero_iff' I f G hV (n + c) _).mp (hψ m)
    rwa [show n + c + 1 = n + 1 + c by omega] at this
  have h2 := hc (n + 1) _ h1
  have h3 : (ψ : Γ(sheafHom F G, V)) ∈
      (J ^ (n + 1) • ⊤ : Submodule Γ(X, V) Γ(sheafHom F G, V)) := by
    have := Submodule.mem_map_of_mem (f := (sheafHomAffineEquiv hV F G).symm.toLinearMap) h2
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at this
    have e : (sheafHomAffineEquiv hV F G).symm.toLinearMap
        (sheafHomAffineEquiv hV F G (ψ : Γ(sheafHom F G, V))) = (ψ : Γ(sheafHom F G, V)) :=
      LinearEquiv.symm_apply_apply _ _
    rw [e] at this
    exact this
  exact (toQuotientIdealPow_app_eq_zero_iff' I f (sheafHom F G) hV n
    (ψ : Γ(sheafHom F G, V))).mpr h3

/-- **Local lifts** (Artin–Rees for `ℋom` on an affine open, "cokernel" half): for a compatible
family `vₙ : F ⟶ G / I^{n+1} G`, on an affine open `V` each `vₙ` lifts to a section of
`ℋom(F, G)` over `V`. -/
lemma exists_homOn_lift [IsLocallyNoetherian X] {F G : X.Modules} [F.IsCoherent] [G.IsCoherent]
    (v : ∀ n, F ⟶ G.quotientIdealPow f I n)
    (hv : ∀ {m n : ℕ} (h : n ≤ m), v m ≫ quotMap I f G h = v n) {V : X.Opens}
    (hV : IsAffineOpen V) (n : ℕ) :
    ∃ φ : HomOn F G V, ∀ m,
      (G.toQuotientIdealPow f I n).app V (φ.app V le_rfl m) = (v n).app V m := by
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : F.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : G.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have := finite_sections_of_isFiniteType F hV
  have := finite_sections_of_isFiniteType G hV
  let J := idealV f I V 1
  obtain ⟨c, hc⟩ := exists_lift_comp_eq.{u, u, u} J (M := Γ(F, V)) (N := Γ(G, V))
  obtain ⟨φ, hφ⟩ := hc (n + 1) (appₗ (G.toQuotientIdealPow f I (n + c)) V)
    (appₗ (G.toQuotientIdealPow f I n) V) (appₗ (quotMap I f G (Nat.le_add_right n c)) V)
    (toQuotientIdealPow_app_surjective I f (n + c) hV)
    (fun s hs ↦ by
      have := (toQuotientIdealPow_app_eq_zero_iff' I f G hV (n + c) s).mp hs
      rwa [show n + c + 1 = n + 1 + c by omega] at this)
    (fun s hs ↦ (toQuotientIdealPow_app_eq_zero_iff' I f G hV n s).mpr hs)
    (LinearMap.ext fun s ↦ by
      change (quotMap I f G (Nat.le_add_right n c)).app V
        ((G.toQuotientIdealPow f I (n + c)).app V s) = _
      rw [← Scheme.Modules.Hom.comp_app_apply, toQuotientIdealPow_quotMap]
      rfl)
    (appₗ (v (n + c)) V)
  obtain ⟨ψ, hψ⟩ := exists_homOn_app_eq hV φ
  refine ⟨ψ, fun m ↦ ?_⟩
  rw [hψ]
  have := LinearMap.congr_fun hφ m
  change (G.toQuotientIdealPow f I n).app V (φ m) =
    (quotMap I f G (Nat.le_add_right n c)).app V ((v (n + c)).app V m) at this
  rw [this, ← Scheme.Modules.Hom.comp_app_apply, hv]

end LocalArtinRees

section FormalLimitAux

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A) (M : X.Modules)

/-- A compatible family of global sections of the `M / I^{n+1} M` as an element of
`lim_n H⁰(X, M / I^{n+1} M)`. -/
lemma mem_formalLimit_of_compat' (z : ∀ n, Γ(M.quotientIdealPow f I n, ⊤))
    (hcompat : ∀ n, (M.quotientIdealPowMap f I n).app ⊤ (z (n + 1)) = z n) :
    (fun n ↦ (Scheme.Modules.H.equiv₀ _).symm (z n)) ∈ M.formalLimit f I 0 := by
  intro n
  apply (Scheme.Modules.H.equiv₀ (M.quotientIdealPow f I n)).injective
  have e := CategoryTheory.Sheaf.H'.equiv₀_symm_naturality
    (Scheme.Modules.Hom.toAbSheaf (M.quotientIdealPowMap f I n)) (U := ⊤) (z (n + 1))
  refine (congrArg (Scheme.Modules.H.equiv₀ (M.quotientIdealPow f I n)) e).trans ?_
  refine ((Scheme.Modules.H.equiv₀ _).apply_symm_apply _).trans ?_
  refine (hcompat n).trans ?_
  exact ((Scheme.Modules.H.equiv₀ _).apply_symm_apply _).symm

/-- `H⁰` and `Γ` for the reduction maps. -/
lemma equiv₀_H'_map_toQuotientIdealPow' (n : ℕ) (y : M.H 0) :
    Scheme.Modules.H.equiv₀ _ (Scheme.Modules.H'.map (M.toQuotientIdealPow f I n) 0 ⊤ y) =
      (M.toQuotientIdealPow f I n).app ⊤ (Scheme.Modules.H.equiv₀ _ y) :=
  CategoryTheory.Sheaf.H'.equiv₀_naturality
    (Scheme.Modules.Hom.toAbSheaf (M.toQuotientIdealPow f I n)) (U := ⊤) y

variable {M} in
/-- A compatible family `vₙ : F ⟶ M / I^{n+1} M` is compatible under all the projections. -/
lemma comp_quotMap_of_compat {F : X.Modules} (v : ∀ n, F ⟶ M.quotientIdealPow f I n)
    (hv : ∀ n, v (n + 1) ≫ M.quotientIdealPowMap f I n = v n) {m n : ℕ} (h : n ≤ m) :
    v m ≫ quotMap I f M h = v n := by
  induction m, h using Nat.le_induction with
  | base => rw [quotMap_self, Category.comp_id]
  | succ m hnm ih =>
    rw [← quotientIdealPowMap_quotMap I f M hnm, ← Category.assoc, hv m, ih]

variable [IsNoetherianRing A] [IsAdicComplete I A] [IsProper f]

/-- **Formal functions over a complete base, degree `0`**: a compatible family of global sections
of the `M / I^{n+1} M` comes from a unique global section of `M`. -/
lemma existsUnique_app_toQuotientIdealPow_eq [M.IsCoherent]
    (z : ∀ n, Γ(M.quotientIdealPow f I n, ⊤))
    (hcompat : ∀ n, (M.quotientIdealPowMap f I n).app ⊤ (z (n + 1)) = z n) :
    ∃! a : Γ(M, ⊤), ∀ n, (M.toQuotientIdealPow f I n).app ⊤ a = z n := by
  have hbij := toFormalLimit_bijective I f M 0
  obtain ⟨y, hy⟩ := hbij.2 ⟨_, mem_formalLimit_of_compat' I f M z hcompat⟩
  have key : ∀ y' : M.H 0, (∀ n, (M.toQuotientIdealPow f I n).app ⊤
      (Scheme.Modules.H.equiv₀ _ y') = z n) ↔ M.toFormalLimit f I 0 y' =
        ⟨_, mem_formalLimit_of_compat' I f M z hcompat⟩ := by
    intro y'
    constructor
    · intro h
      refine Subtype.ext (funext fun n ↦ ?_)
      apply (Scheme.Modules.H.equiv₀ _).injective
      change Scheme.Modules.H.equiv₀ _ (Scheme.Modules.H'.map (M.toQuotientIdealPow f I n) 0 ⊤ y') =
        Scheme.Modules.H.equiv₀ _ ((Scheme.Modules.H.equiv₀ _).symm (z n))
      rw [equiv₀_H'_map_toQuotientIdealPow', LinearEquiv.apply_symm_apply, h n]
    · intro h n
      have h' := congrArg (fun w : M.formalLimit f I 0 ↦ w.1 n) h
      simp only at h'
      rw [← equiv₀_H'_map_toQuotientIdealPow']
      change Scheme.Modules.H.equiv₀ _ ((M.toFormalLimit f I 0 y').1 n) = _
      rw [h']
      exact (Scheme.Modules.H.equiv₀ _).apply_symm_apply _
  refine ⟨Scheme.Modules.H.equiv₀ _ y, (key y).mpr hy, fun a ha ↦ ?_⟩
  obtain ⟨y', rfl⟩ := (Scheme.Modules.H.equiv₀ M).surjective a
  rw [hbij.1 (((key y').mp ha).trans hy.symm)]

end FormalLimitAux

section Existence

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} (f : X ⟶ Spec A) [IsProper f]

/-- **Existence in the full faithfulness of Grothendieck's existence theorem** (EGA III 5.1.4):
over an `I`-adically complete noetherian base, a compatible family of morphisms
`vₙ : F ⟶ G / I^{n+1} G` of coherent modules on `X` proper over `Spec A` comes from a morphism
`F ⟶ G`. Proof: `ℋom(F, G)` is coherent; by Artin–Rees (`ArtinReesHom`), on a finite affine cover
the `vₙ₊꜀` lift to local sections of `ℋom(F, G)` which agree modulo `I^{n+1}` on overlaps, hence
glue to a compatible family in `Γ(X, ℋom(F, G) / I^{n+1})`; by the theorem on formal functions over
a complete base it comes from `Γ(X, ℋom(F, G)) = Hom(F, G)`. -/
theorem exists_comp_toQuotientIdealPow_eq {F G : X.Modules} [F.IsCoherent] [G.IsCoherent]
    (v : ∀ n, F ⟶ G.quotientIdealPow f I n)
    (hv : ∀ n, v (n + 1) ≫ G.quotientIdealPowMap f I n = v n) :
    ∃ u : F ⟶ G, ∀ n, u ≫ G.toQuotientIdealPow f I n = v n := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := isAffineHom_diagonal_of_isSeparated f
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have hv' : ∀ {m n : ℕ} (h : n ≤ m), v m ≫ quotMap I f G h = v n :=
    fun h ↦ comp_quotMap_of_compat I f v hv h
  let H := sheafHom F G
  have : H.IsCoherent := isCoherent_sheafHom F G
  have : H.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  obtain ⟨r, U, hcov, hU⟩ := exists_cechCover' X
  have hUU : ∀ i j, IsAffineOpen (U i ⊓ U j) := fun i j ↦ (hU i).inf (hU j)
  -- a uniform Artin–Rees constant for the `U i` and the `U i ⊓ U j`
  choose c₁ hc₁ using fun i ↦
    exists_toQuotientIdealPow_sheafHom_app_eq_zero I f (F := F) (G := G) (hU i)
  choose c₂ hc₂ using fun p : Fin r × Fin r ↦
    exists_toQuotientIdealPow_sheafHom_app_eq_zero I f (F := F) (G := G) (hUU p.1 p.2)
  let c := Finset.univ.sup c₁ + Finset.univ.sup c₂
  have key : ∀ {W : X.Opens} (c' : ℕ), c' ≤ c → (∀ (n : ℕ) (ψ : HomOn F G W),
      (∀ m, (G.toQuotientIdealPow f I (n + c')).app W (ψ.app W le_rfl m) = 0) →
      (H.toQuotientIdealPow f I n).app W ψ = 0) → ∀ (n : ℕ) (ψ : HomOn F G W),
      (∀ m, (G.toQuotientIdealPow f I (n + c)).app W (ψ.app W le_rfl m) = 0) →
      (H.toQuotientIdealPow f I n).app W ψ = 0 := by
    intro W c' hc' h n ψ hψ
    refine h n ψ fun m ↦ ?_
    have := congrArg ((quotMap I f G (Nat.add_le_add_left hc' n)).app W) (hψ m)
    rwa [map_zero, ← Scheme.Modules.Hom.comp_app_apply, toQuotientIdealPow_quotMap] at this
  have hα₁ := fun i ↦ key (c₁ i) ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_add_right _ _))
    (hc₁ i)
  have hα₂ := fun i j ↦ key (c₂ (i, j))
    ((Finset.le_sup (Finset.mem_univ (i, j))).trans (Nat.le_add_left _ _)) (hc₂ (i, j))
  -- local lifts
  choose φ hφ using fun (n : ℕ) (i : Fin r) ↦ exists_homOn_lift I f v hv' (hU i) n
  have hφW : ∀ n i (W : X.Opens) (hW : W ≤ U i) (m : Γ(F, W)),
      (G.toQuotientIdealPow f I n).app W ((φ n i).app W hW m) = (v n).app W m :=
    fun n i W hW m ↦ homOnPostcomp_app_eq (hU i) (φ n i) _ (v n) (hφ n i) hW m
  -- restrictions of sections of `ℋom(F, G)` are restrictions of `HomOn`s
  have hres : ∀ {W W' : X.Opens} (h : W' ≤ W) (ψ : Γ(H, W)),
      H.presheaf.map (homOfLE h).op ψ = (ψ : HomOn F G W).restrict h := fun _ _ ↦ rfl
  -- the local sections of `ℋom(F, G) / I^{n+1}`
  let φ' : ∀ n i, Γ(H, U i) := fun n i ↦ φ n i
  let σ : ∀ n i, Γ(H.quotientIdealPow f I n, U i) := fun n i ↦
    (H.toQuotientIdealPow f I n).app (U i) (φ' (n + c) i)
  have hcompat : ∀ n, TopCat.Presheaf.IsCompatible (H.quotientIdealPow f I n).presheaf U (σ n) := by
    intro n i j
    change (H.quotientIdealPow f I n).presheaf.map (homOfLE inf_le_left).op
        ((H.toQuotientIdealPow f I n).app (U i) (φ' (n + c) i)) =
      (H.quotientIdealPow f I n).presheaf.map (homOfLE inf_le_right).op
        ((H.toQuotientIdealPow f I n).app (U j) (φ' (n + c) j))
    rw [← hom_app_presheaf_map, ← hom_app_presheaf_map, ← sub_eq_zero, ← map_sub]
    refine hα₂ i j n _ fun m ↦ ?_
    rw [hres, hres]
    change (G.toQuotientIdealPow f I (n + c)).app _
      ((φ (n + c) i).app (U i ⊓ U j) inf_le_left m - (φ (n + c) j).app (U i ⊓ U j) inf_le_right m)
      = 0
    rw [map_sub, hφW, hφW, sub_self]
  -- glue
  have hglue : ∀ n, ∃! t : Γ(H.quotientIdealPow f I n, ⊤),
      ∀ i, (H.quotientIdealPow f I n).presheaf.map (homOfLE le_top : U i ⟶ ⊤).op t = σ n i :=
    fun n ↦ TopCat.Sheaf.existsUnique_gluing' (F := ⟨_, (H.quotientIdealPow f I n).isSheaf⟩)
      (U := U) ⊤ (fun i ↦ homOfLE le_top) hcov.ge (σ n) (hcompat n)
  choose t ht using fun n ↦ (hglue n).exists
  -- the glued sections are compatible
  have ht_compat : ∀ n, (H.quotientIdealPowMap f I n).app ⊤ (t (n + 1)) = t n := by
    intro n
    refine (hglue n).unique (fun i ↦ ?_) (ht n)
    rw [← hom_app_presheaf_map, ht (n + 1) i]
    change (H.quotientIdealPowMap f I n).app (U i)
      ((H.toQuotientIdealPow f I (n + 1)).app (U i) (φ' (n + 1 + c) i)) =
      (H.toQuotientIdealPow f I n).app (U i) (φ' (n + c) i)
    rw [← Scheme.Modules.Hom.comp_app_apply, Scheme.Modules.toQuotientIdealPow_comp_map,
      ← sub_eq_zero, ← map_sub]
    refine hα₁ i n _ fun m ↦ ?_
    change (G.toQuotientIdealPow f I (n + c)).app _
      ((φ (n + 1 + c) i).app (U i) le_rfl m - (φ (n + c) i).app (U i) le_rfl m) = 0
    rw [map_sub, hφ (n + c) i m, ← toQuotientIdealPow_quotMap I f G
      (show n + c ≤ n + 1 + c by omega), Scheme.Modules.Hom.comp_app_apply, hφ (n + 1 + c) i m,
      ← Scheme.Modules.Hom.comp_app_apply, hv', sub_self]
  -- the theorem on formal functions for `ℋom(F, G)`
  obtain ⟨a, ha, -⟩ := existsUnique_app_toQuotientIdealPow_eq I f H t ht_compat
  refine ⟨sheafHomTopEquiv a, fun n ↦ ?_⟩
  have hloc : ∀ i (m : Γ(F, U i)), (G.toQuotientIdealPow f I n).app (U i)
      ((a : HomOn F G ⊤).app (U i) le_top m) = (v n).app (U i) m := by
    intro i m
    let aᵢ : Γ(H, U i) := H.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op a
    have h1 : (H.toQuotientIdealPow f I n).app (U i) (aᵢ - φ' (n + c) i) = 0 := by
      rw [map_sub, sub_eq_zero]
      change (H.toQuotientIdealPow f I n).app (U i) (H.presheaf.map _ a) = σ n i
      rw [hom_app_presheaf_map, ha n, ht n i]
    rw [toQuotientIdealPow_app_eq_zero_iff' I f H (hU i)] at h1
    have h2 : sheafHomAffineEquiv (hU i) F G (aᵢ - φ' (n + c) i) ∈
        (idealV f I (U i) 1 ^ (n + 1) • ⊤ :
          Submodule Γ(X, U i) (Γ(F, U i) →ₗ[Γ(X, U i)] Γ(G, U i))) := by
      have := Submodule.mem_map_of_mem (f := (sheafHomAffineEquiv (hU i) F G).toLinearMap) h1
      rwa [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at this
    have h3 := (toQuotientIdealPow_app_eq_zero_iff' I f G (hU i) n _).mpr
      (apply_mem_pow_smul_top _ (n + 1) h2 m)
    change (G.toQuotientIdealPow f I n).app (U i)
      ((a : HomOn F G ⊤).app (U i) le_top m - (φ (n + c) i).app (U i) le_rfl m) = 0 at h3
    rw [map_sub, sub_eq_zero] at h3
    rw [h3, ← toQuotientIdealPow_quotMap I f G (Nat.le_add_right n c),
      Scheme.Modules.Hom.comp_app_apply, hφ, ← Scheme.Modules.Hom.comp_app_apply, hv']
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext m
  apply (G.quotientIdealPow f I n).isSheaf.section_ext (U := op W)
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := TopologicalSpace.Opens.mem_iSup.mp (hcov.ge trivial)
  refine ⟨W ⊓ U i, inf_le_left, ⟨hx, hi⟩, ?_⟩
  rw [← hom_app_presheaf_map, ← hom_app_presheaf_map]
  exact homOnPostcomp_app_eq (hU i) ((a : HomOn F G ⊤).restrict le_top)
    (G.toQuotientIdealPow f I n) (v n) (hloc i) inf_le_right _

/-- **Full faithfulness in Grothendieck's existence theorem** (EGA III 5.1.4): over an `I`-adically
complete noetherian base, compatible families of morphisms `F ⟶ G / I^{n+1} G` of coherent modules
on `X` proper over `Spec A` are the morphisms `F ⟶ G`. -/
theorem existsUnique_comp_toQuotientIdealPow_eq {F G : X.Modules} [F.IsCoherent] [G.IsCoherent]
    (v : ∀ n, F ⟶ G.quotientIdealPow f I n)
    (hv : ∀ n, v (n + 1) ≫ G.quotientIdealPowMap f I n = v n) :
    ∃! u : F ⟶ G, ∀ n, u ≫ G.toQuotientIdealPow f I n = v n := by
  obtain ⟨u, hu⟩ := exists_comp_toQuotientIdealPow_eq I f v hv
  exact ⟨u, hu, fun u' hu' ↦ eq_of_comp_toQuotientIdealPow_eq I f fun n ↦ (hu' n).trans (hu n).symm⟩

end Existence

section Units

variable {X Y Z : Scheme.{u}}

open Scheme.Modules in
/-- The units of `g^* ⊣ g_*` and `g'^* ⊣ g'_*` for equal morphisms `g = g'` correspond. -/
lemma unit_pullbackCongr {g g' : Y ⟶ X} (h : g = g') (M : X.Modules) :
    (pullbackPushforwardAdjunction g).unit.app M ≫
      (pushforward g).map ((pullbackCongr h).hom.app M) ≫
        (pushforwardCongr h).hom.app _ = (pullbackPushforwardAdjunction g').unit.app M := by
  subst h
  have e1 : (pullbackCongr (rfl : g = g)).hom.app M = 𝟙 _ := rfl
  have e2 : (pushforwardCongr (rfl : g = g)).hom.app ((Scheme.Modules.pullback g).obj M) =
      𝟙 _ := by
    refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
    ext x
    rw [pushforwardCongr_hom_app_app]
    simp
  rw [e1, e2, CategoryTheory.Functor.map_id]
  exact (congrArg _ (Category.id_comp _)).trans (Category.comp_id _)


open Scheme.Modules in
/-- The unit of `(t ≫ ι)^* ⊣ (t ≫ ι)_*` is the composite of the units of `ι` and `t`. -/
lemma unit_pullbackComp (t : Y ⟶ Z) (ι : Z ⟶ X) (M : X.Modules) :
    (pullbackPushforwardAdjunction ι).unit.app M ≫
      (pushforward ι).map ((pullbackPushforwardAdjunction t).unit.app
        ((Scheme.Modules.pullback ι).obj M)) ≫
        (pushforwardComp t ι).hom.app _ =
      (pullbackPushforwardAdjunction (t ≫ ι)).unit.app M ≫
        (pushforward (t ≫ ι)).map ((pullbackComp t ι).inv.app M) := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction ι).comp
    (pullbackPushforwardAdjunction t)) (pullbackPushforwardAdjunction (t ≫ ι))
    (pullbackComp t ι).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  rw [← h, Category.assoc]
  rfl

end Units

section Restrict

open Scheme.Modules

variable {X Y Z : Scheme.{u}} (t : Y ⟶ Z) (ι' : Z ⟶ X) (ι : Y ⟶ X) (h : t ≫ ι' = ι)

/-- `ι^* M ≅ t^* ι'^* M` for `t ≫ ι' = ι`. -/
noncomputable def pullbackCompIso (M : X.Modules) :
    (Scheme.Modules.pullback ι).obj M ≅
      (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback ι').obj M) :=
  ((pullbackCongr h).app M).symm ≪≫ ((pullbackComp t ι').app M).symm

/-- The restriction `ι'_* ι'^* M ⟶ ι_* ι^* M` along `t` for `t ≫ ι' = ι`. -/
noncomputable def restrictAlong (M : X.Modules) :
    (pushforward ι').obj ((Scheme.Modules.pullback ι').obj M) ⟶
      (pushforward ι).obj ((Scheme.Modules.pullback ι).obj M) :=
  (pushforward ι').map ((pullbackPushforwardAdjunction t).unit.app
      ((Scheme.Modules.pullback ι').obj M)) ≫
    (pushforward ι').map ((pushforward t).map (pullbackCompIso t ι' ι h M).inv) ≫
    (pushforwardComp t ι').hom.app _ ≫ (pushforwardCongr h).hom.app _

/-- The restriction is compatible with the units. -/
@[reassoc]
lemma unit_restrictAlong (M : X.Modules) :
    (pullbackPushforwardAdjunction ι').unit.app M ≫ restrictAlong t ι' ι h M =
      (pullbackPushforwardAdjunction ι).unit.app M := by
  subst h
  have hP : (pullbackCompIso t ι' (t ≫ ι') rfl M).inv =
      (pullbackComp t ι').hom.app M ≫ (pullbackCongr (rfl : t ≫ ι' = t ≫ ι')).hom.app M := rfl
  have hnat := (pushforwardComp t ι').hom.naturality (pullbackCompIso t ι' (t ≫ ι') rfl M).inv
  simp only [Functor.comp_map] at hnat
  unfold restrictAlong
  rw [reassoc_of% hnat, reassoc_of% (unit_pullbackComp t ι' M), ← Functor.map_comp_assoc, hP,
    Iso.inv_hom_id_app_assoc]
  exact unit_pullbackCongr (rfl : t ≫ ι' = t ≫ ι') M

/-- Naturality of the restriction. -/
@[reassoc]
lemma restrictAlong_naturality {F G : X.Modules}
    (w : (Scheme.Modules.pullback ι').obj F ⟶ (Scheme.Modules.pullback ι').obj G) :
    (pushforward ι').map w ≫ restrictAlong t ι' ι h G =
      restrictAlong t ι' ι h F ≫ (pushforward ι).map ((pullbackCompIso t ι' ι h F).hom ≫
        (Scheme.Modules.pullback t).map w ≫ (pullbackCompIso t ι' ι h G).inv) := by
  unfold restrictAlong
  have h1 := (pullbackPushforwardAdjunction t).unit.naturality w
  simp only [Functor.id_map, Functor.comp_map] at h1
  have h2 := (pushforwardComp t ι').hom.naturality ((pullbackCompIso t ι' ι h F).hom ≫
    (Scheme.Modules.pullback t).map w ≫ (pullbackCompIso t ι' ι h G).inv)
  have h3 := (pushforwardCongr h).hom.naturality ((pullbackCompIso t ι' ι h F).hom ≫
    (Scheme.Modules.pullback t).map w ≫ (pullbackCompIso t ι' ι h G).inv)
  simp only [Functor.comp_map] at h2
  simp only [Category.assoc]
  rw [← h3, ← reassoc_of% h2]
  simp only [← Functor.map_comp_assoc]
  rw [reassoc_of% h1, ← (pushforward t).map_comp (pullbackCompIso t ι' ι h F).inv,
    Iso.inv_hom_id_assoc, (pushforward t).map_comp]

end Restrict


section Thickening

open Scheme.Modules

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A)

lemma pullbackCompIso_thickening (n : ℕ) (M : X.Modules) :
    pullbackCompIso (thickening.transition f I n) (thickening.ι f I (n + 1)) (thickening.ι f I n)
      (thickening.transition_ι f I n) M = thickening.pullbackIso f I n M :=
  rfl

variable [IsNoetherianRing A]

/-- `Hom(F|_{X_n}, G|_{X_n}) ≅ Hom(F, G / I^{n+1} G)` for the thickening `ι : X_n ⟶ X` and `G`
quasi-coherent: the adjunction `ι^* ⊣ ι_*` and `ι_* ι^* G ≅ G / I^{n+1} G` (`thickeningIso`). -/
noncomputable def homPullbackThickeningEquiv (n : ℕ) (F G : X.Modules) [G.IsQuasicoherent] :
    ((Scheme.Modules.pullback (thickening.ι f I n)).obj F ⟶
      (Scheme.Modules.pullback (thickening.ι f I n)).obj G) ≃
      (F ⟶ G.quotientIdealPow f I n) :=
  ((pullbackPushforwardAdjunction (thickening.ι f I n)).homEquiv _ _).trans
    ((Iso.refl F).homCongr (thickeningIso I f n G).symm)

lemma homPullbackThickeningEquiv_apply (n : ℕ) (F G : X.Modules) [G.IsQuasicoherent]
    (u : (Scheme.Modules.pullback (thickening.ι f I n)).obj F ⟶
      (Scheme.Modules.pullback (thickening.ι f I n)).obj G) :
    homPullbackThickeningEquiv I f n F G u =
      (pullbackPushforwardAdjunction (thickening.ι f I n)).unit.app F ≫
        (pushforward (thickening.ι f I n)).map u ≫ (thickeningIso I f n G).inv := by
  simp [homPullbackThickeningEquiv, Adjunction.homEquiv_unit, Iso.homCongr_apply]

/-- `homPullbackThickeningEquiv` sends the restriction of `w : F ⟶ G` to `w` followed by the
projection `G ⟶ G / I^{n+1} G`. -/
lemma homPullbackThickeningEquiv_map (n : ℕ) {F G : X.Modules} [G.IsQuasicoherent] (w : F ⟶ G) :
    homPullbackThickeningEquiv I f n F G ((Scheme.Modules.pullback (thickening.ι f I n)).map w) =
      w ≫ G.toQuotientIdealPow f I n := by
  simp only [homPullbackThickeningEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv,
    Category.id_comp, Iso.symm_hom]
  rw [← Category.comp_id ((Scheme.Modules.pullback (thickening.ι f I n)).map w),
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_id, Category.assoc,
    ← toQuotientIdealPow_toThickening I f n G, Category.assoc]
  simp [thickeningIso]

/-- Under `M / I^{n+1} M ≅ ι_{n *} ι_n^* M`, the transition map `M / I^{n+2} M → M / I^{n+1} M` is
the restriction along `X_n ⟶ X_{n+1}`. -/
lemma thickeningIso_inv_quotientIdealPowMap (n : ℕ) (G : X.Modules) [G.IsQuasicoherent] :
    (thickeningIso I f (n + 1) G).inv ≫ G.quotientIdealPowMap f I n =
      restrictAlong (thickening.transition f I n) (thickening.ι f I (n + 1)) (thickening.ι f I n)
        (thickening.transition_ι f I n) G ≫ (thickeningIso I f n G).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
    ← cancel_epi (G.toQuotientIdealPow f I (n + 1))]
  simp only [thickeningIso, asIso_hom]
  rw [Scheme.Modules.toQuotientIdealPow_comp_map_assoc, toQuotientIdealPow_toThickening,
    toQuotientIdealPow_toThickening_assoc, unit_restrictAlong]

variable [IsAdicComplete I A] [IsProper f]

/-- **Full faithfulness in Grothendieck's existence theorem** (EGA III 5.1.4), in the form of the
first half of `AlgebraicGeometry.GrothendieckExistenceStatement`: over an `I`-adically complete
noetherian base, a compatible family of morphisms `F|_{X_n} ⟶ G|_{X_n}` of coherent modules on
`X` proper over `Spec A` comes from a unique morphism `F ⟶ G`. -/
theorem existsUnique_pullback_thickening_map_eq {F G : X.Modules} [F.IsCoherent] [G.IsCoherent]
    (u : ∀ n, (Scheme.Modules.pullback (thickening.ι f I n)).obj F ⟶
      (Scheme.Modules.pullback (thickening.ι f I n)).obj G)
    (hu : ∀ n, u n = (thickening.pullbackIso f I n F).hom ≫
      (Scheme.Modules.pullback (thickening.transition f I n)).map (u (n + 1)) ≫
        (thickening.pullbackIso f I n G).inv) :
    ∃! u₀ : F ⟶ G, ∀ n, (Scheme.Modules.pullback (thickening.ι f I n)).map u₀ = u n := by
  have : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let v : ∀ n, F ⟶ G.quotientIdealPow f I n := fun n ↦
    (pullbackPushforwardAdjunction (thickening.ι f I n)).unit.app F ≫
      (pushforward (thickening.ι f I n)).map (u n) ≫ (thickeningIso I f n G).inv
  have hv : ∀ n, v (n + 1) ≫ G.quotientIdealPowMap f I n = v n := by
    intro n
    simp only [v, Category.assoc]
    rw [thickeningIso_inv_quotientIdealPowMap, restrictAlong_naturality_assoc,
      unit_restrictAlong_assoc, pullbackCompIso_thickening, pullbackCompIso_thickening, ← hu n]
  obtain ⟨u₀, hu₀, huniq⟩ := existsUnique_comp_toQuotientIdealPow_eq I f v hv
  have key : ∀ (w : F ⟶ G) n, (Scheme.Modules.pullback (thickening.ι f I n)).map w = u n ↔
      w ≫ G.toQuotientIdealPow f I n = v n := by
    intro w n
    rw [← ((pullbackPushforwardAdjunction (thickening.ι f I n)).homEquiv _ _).apply_eq_iff_eq,
      Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      (pullbackPushforwardAdjunction (thickening.ι f I n)).unit_naturality,
      ← toQuotientIdealPow_toThickening I f n G]
    simp only [v]
    conv_rhs => rw [← Category.assoc, Iso.eq_comp_inv]
    simp only [thickeningIso, asIso_hom, Category.assoc]
  exact ⟨u₀, fun n ↦ (key u₀ n).mpr (hu₀ n), fun w hw ↦ huniq w fun n ↦ (key w n).mp (hw n)⟩

end Thickening

end AlgebraicGeometry.CohomologyAux

namespace AlgebraicGeometry

/-- **Grothendieck's existence theorem, full faithfulness** (EGA III 5.1.4): the first half of
`GrothendieckExistenceStatement`. Over an `I`-adically complete noetherian ring `A`, for
`f : X ⟶ Spec A` proper, compatible families of morphisms `F|_{X_n} ⟶ G|_{X_n}` of coherent
modules come from unique morphisms `F ⟶ G`. -/
theorem grothendieckExistence_fullyFaithful (A : CommRingCat.{u}) [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] (X : Scheme.{u}) (f : X ⟶ Spec A) [IsProper f]
    (F G : X.Modules) [F.IsCoherent] [G.IsCoherent]
    (u : ∀ n, (Scheme.Modules.pullback (thickening.ι f I n)).obj F ⟶
      (Scheme.Modules.pullback (thickening.ι f I n)).obj G)
    (hu : ∀ n, u n = (thickening.pullbackIso f I n F).hom ≫
      (Scheme.Modules.pullback (thickening.transition f I n)).map (u (n + 1)) ≫
        (thickening.pullbackIso f I n G).inv) :
    ∃! u₀ : F ⟶ G, ∀ n, (Scheme.Modules.pullback (thickening.ι f I n)).map u₀ = u n :=
  CohomologyAux.existsUnique_pullback_thickening_map_eq I f u hu

end AlgebraicGeometry
