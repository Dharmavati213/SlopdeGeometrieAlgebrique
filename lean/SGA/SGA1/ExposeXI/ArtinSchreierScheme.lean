/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.ArtinSchreierCohomology
import SGA.SGA1.ExposeXI.KummerCovering
import SGA.SGA1.ExposeXI.FiniteEtaleGroups
import SGA.SGA1.ExposeXI.AdditiveTorsors

/-!
# SGA 1, Exposé XI.6.7–XI.6.9: `(ℤ/p)_S` is the constant group scheme `ℤ/p`

Let `S` be an affine scheme of characteristic `p`. The fpqc sheaf `(ℤ/p)_S = ker ℘` of XI.6.7
(`ZpS`) is represented by the `S`-scheme `ℤ/p = Spec Γ(S)[T]/(Tᵖ - T)` (`zpScheme`,
`zpSchemeRepresentableBy`), which is finite étale over `S` (`isFiniteEtale_zpScheme`) and, by
`ArtinSchreier.bijective_kernelEval`, is the constant scheme `Spec Γ(S)^{ℤ/p}`. So `ℤ/p` is a
group scheme (`zpGrpObj`) with `Hom_S(-, ℤ/p) ≅ (ℤ/p)_S` (`yonedaZpSchemeIso`) and
`H¹(S, ℤ/p) ≅ H¹(S, (ℤ/p)_S)` (`h1ZpSchemeEquiv`).

At a geometric point `s̄`, the points of `ℤ/p` over `s̄` form the group `ℤ/p`
(`ptsZpSchemeEquiv`), on which `π₁(S, s̄)` acts trivially (`smul_ptsZpScheme`). Hence XI.5 `(*)`
(`h1EquivContH1`) gives, for `S` connected, `H¹(S, (ℤ/p)_S) ≅ Hom_cont(π₁(S, s̄), ℤ/p)`
(`h1ZpSEquivContinuousMonoidHom`, using `contH1EquivOfTrivial`), and with XI.6.9 for affine `S`,
`Γ(S, 𝒪_S)/℘ Γ(S, 𝒪_S) ≅ Hom_cont(π₁(S, s̄), ℤ/p)` (`artinSchreierEquivContinuousMonoidHom`).
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry Polynomial MonObj

namespace SGA.SGA1.ExposeXI

variable (S : Scheme.{u}) [IsAffine S] (p : ℕ) [hp : Fact p.Prime] (hS : (p : Γ(S, ⊤)) = 0)

/-- The ring `Γ(S)[T]/(Tᵖ - T)` of the constant group scheme `ℤ/p` over `S`. -/
noncomputable abbrev zpRing : CommRingCat.{u} :=
  CommRingCat.of (ArtinSchreierAlgebra Γ(S, ⊤) p 0)

/-- XI.6.7: the group scheme `ℤ/p = Spec Γ(S)[T]/(Tᵖ - T)` over the affine scheme `S`, the
Artin–Schreier covering `℘⁻¹(0)`. -/
noncomputable abbrev zpScheme : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (zpRing S p))) ≫ S.isoSpec.inv)

/-- The root `T` of `Tᵖ - T`, as a global section of `zpScheme`. -/
noncomputable def zpRoot : Γ(Spec (zpRing S p), ⊤) :=
  (Scheme.ΓSpecIso (zpRing S p)).inv (AdjoinRoot.root _)

omit [IsAffine S] in
lemma mem_ZpS_iff (T : Over S) (x : Γ(T.left, ⊤)) :
    (wpGa S p hS).app (op T) (Multiplicative.ofAdd x) = 1 ↔ x - x ^ p = 0 := by
  rw [wpGa_app_apply]
  exact Multiplicative.ofAdd.injective.eq_iff' rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- XI.6.7: `(ℤ/p)_S` is represented by `Spec Γ(S)[T]/(Tᵖ - T)`: the `S`-morphisms
`T ⟶ Spec Γ(S)[T]/(Tᵖ - T)` are the sections `x` of `𝒪_T` with `xᵖ = x`, by pulling back the
root `T`. -/
noncomputable def zpSchemeRepresentableBy :
    (ZpS S p hS ⋙ CategoryTheory.forget GrpCat).RepresentableBy (zpScheme S p) := by
  let K := zpRing S p
  let ιS : Γ(S, ⊤) ⟶ K := CommRingCat.ofHom (algebraMap Γ(S, ⊤) K)
  -- The ring maps `K ⟶ Γ(T)` induced by `S`-morphisms `T ⟶ Spec K` extend `Γ(S) ⟶ Γ(T)`.
  have hstr : ∀ {T : Over S} (φ : T ⟶ zpScheme S p),
      ιS ≫ (Scheme.ΓSpecIso K).inv ≫ φ.left.appTop = T.hom.appTop := by
    intro T φ
    have hφ : φ.left ≫ Spec.map ιS = T.hom ≫ S.isoSpec.hom := by
      rw [← Iso.comp_inv_eq, Category.assoc]
      exact Over.w φ
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop, hφ,
      Scheme.Hom.comp_appTop]
    change (Scheme.ΓSpecIso Γ(S, ⊤)).inv ≫ S.toSpecΓ.appTop ≫ T.hom.appTop = _
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]
  have hroot : (AdjoinRoot.root _ : K) - (AdjoinRoot.root _ : K) ^ p = 0 := by
    rw [ArtinSchreier.root_pow, (algebraMap Γ(S, ⊤) K).map_zero, sub_zero, sub_self]
  let F := ZpS S p hS ⋙ CategoryTheory.forget GrpCat
  have hmem : (wpGa S p hS).app (op (zpScheme S p)) (Multiplicative.ofAdd (zpRoot S p)) = 1 := by
    rw [mem_ZpS_iff]
    rw [zpRoot, ← map_pow, ← map_sub, hroot, map_zero]
  let u : F.obj (op (zpScheme S p)) := ⟨Multiplicative.ofAdd (zpRoot S p), hmem⟩
  refine representableByOfBijective u fun T ↦ ⟨fun φ ψ e ↦ ?_, fun s ↦ ?_⟩
  · have e' : φ.left.appTop (zpRoot S p) = ψ.left.appTop (zpRoot S p) :=
      congrArg (fun y : F.obj (op T) ↦ Multiplicative.toAdd y.1) e
    have hρ : (Scheme.ΓSpecIso K).inv ≫ φ.left.appTop =
        (Scheme.ΓSpecIso K).inv ≫ ψ.left.appTop := by
      ext1
      refine AdjoinRoot.ringHom_ext ?_ e'
      have h := (hstr φ).trans (hstr ψ).symm
      rw [← AdjoinRoot.algebraMap_eq]
      exact congrArg CommRingCat.Hom.hom h
    ext
    calc φ.left = _ := eq_toSpecΓ_comp_Spec_map _
      _ = _ := by rw [hρ]
      _ = ψ.left := (eq_toSpecΓ_comp_Spec_map _).symm
  · obtain ⟨x₀, hx⟩ := s
    let x : Γ(T.left, ⊤) := Multiplicative.toAdd x₀
    have hx' : x - x ^ p = 0 := (mem_ZpS_iff S p hS T x).1 hx
    have hev : eval₂ T.hom.appTop.hom x (X ^ p - X + C 0) = 0 := by
      rw [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, map_zero, add_zero,
        ← neg_sub, hx', neg_zero]
    let ρ : K ⟶ Γ(T.left, ⊤) := CommRingCat.ofHom (AdjoinRoot.lift T.hom.appTop.hom x hev)
    have hιρ : ιS ≫ ρ = T.hom.appTop := by
      ext y
      exact AdjoinRoot.lift_of hev
    let φ₀ : T.left ⟶ Spec K := T.left.toSpecΓ ≫ Spec.map ρ
    have hφ₀ : φ₀ ≫ (zpScheme S p).hom = T.hom := by
      change (T.left.toSpecΓ ≫ Spec.map ρ) ≫ Spec.map ιS ≫ S.isoSpec.inv = T.hom
      rw [Category.assoc, ← Spec.map_comp_assoc, hιρ, ← Scheme.toSpecΓ_naturality_assoc]
      change T.hom ≫ S.isoSpec.hom ≫ S.isoSpec.inv = T.hom
      rw [Iso.hom_inv_id, Category.comp_id]
    refine ⟨CategoryTheory.Over.homMk φ₀ hφ₀, Subtype.ext ?_⟩
    let r₀ : K := AdjoinRoot.root (X ^ p - X + C 0)
    have step : (Spec.map ρ).appTop ((Scheme.ΓSpecIso K).inv r₀) =
        (Scheme.ΓSpecIso Γ(T.left, ⊤)).inv (ρ r₀) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    change Multiplicative.ofAdd ((T.left.toSpecΓ ≫ Spec.map ρ).appTop
      ((Scheme.ΓSpecIso K).inv r₀)) = x₀
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, step, Scheme.toSpecΓ_appTop,
      Iso.inv_hom_id_apply]
    exact congrArg Multiplicative.ofAdd (AdjoinRoot.lift_root hev)

/-- XI.6.7: the group-scheme structure of `ℤ/p = Spec Γ(S)[T]/(Tᵖ - T)`, induced by the group
structure of the sheaf `(ℤ/p)_S` it represents. -/
noncomputable abbrev zpGrpObj : GrpObj (zpScheme S p) :=
  GrpObj.ofRepresentableBy _ (ZpS S p hS) (zpSchemeRepresentableBy S p hS)

/-- XI.6.7: `(ℤ/p)_S = ker ℘` is the sheaf of groups `Hom_S(-, ℤ/p)` of the group scheme `ℤ/p`. -/
noncomputable def yonedaZpSchemeIso :
    letI := zpGrpObj S p hS
    yonedaGrpObj (zpScheme S p) ≅ ZpS S p hS :=
  yonedaGrpObjIsoOfRepresentableBy _ _ (zpSchemeRepresentableBy S p hS)

/-- `H¹(S, ℤ/p)` for the group scheme `ℤ/p` (torsors under `Hom_S(-, ℤ/p)`) is `H¹` of the
kernel `(ℤ/p)_S` of `℘`. -/
noncomputable def h1ZpSchemeEquiv :
    letI := zpGrpObj S p hS
    CategoryTheory.H1 (fpqc S) (yonedaGrpObj (zpScheme S p)) ≃
      CategoryTheory.H1 (fpqc S) (ZpS S p hS) :=
  letI := zpGrpObj S p hS
  let e := yonedaZpSchemeIso S p hS
  { toFun := CategoryTheory.H1.map e.hom (isSheaf_ZpS S p hS)
    invFun := CategoryTheory.H1.map e.inv (isSheaf_yonedaGrpObj (zpScheme S p))
    left_inv c := by
      rw [CategoryTheory.H1.map_map, e.hom_inv_id, CategoryTheory.H1.map_id]
    right_inv c := by
      rw [CategoryTheory.H1.map_map, e.inv_hom_id, CategoryTheory.H1.map_id] }

include hS in
/-- XI.6.7: `ℤ/p = Spec Γ(S)[T]/(Tᵖ - T)` is finite étale over `S` (`Tᵖ - T` is monic with
derivative `-1`). -/
theorem isFiniteEtale_zpScheme : IsFiniteEtale (zpScheme S p) := by
  have : Algebra.Etale Γ(S, ⊤) (ArtinSchreierAlgebra Γ(S, ⊤) p 0) :=
    ArtinSchreier.etale hp.out hS 0
  have hf : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (zpRing S p)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have he : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (zpRing S p)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  exact ⟨⟨inferInstanceAs (IsFinite (Spec.map
      (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (zpRing S p))) ≫ S.isoSpec.inv)),
    inferInstanceAs (Etale (Spec.map
      (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (zpRing S p))) ≫ S.isoSpec.inv))⟩⟩

instance : IsAffineHom (zpScheme S p).hom :=
  inferInstanceAs (IsAffineHom (Spec.map
    (CommRingCat.ofHom (algebraMap Γ(S, ⊤) (zpRing S p))) ≫ S.isoSpec.inv))

section Points

variable {S p}

omit [IsAffine S] in
include hS in
/-- A domain of characteristic `p` over `S`. -/
lemma charP_of_isDomain (T : Over S) [IsDomain Γ(T.left, ⊤)] : CharP Γ(T.left, ⊤) p :=
  (CharP.charP_iff_prime_eq_zero hp.out).2 (natCast_eq_zero_of_over S p hS T)

omit [IsAffine S] in
/-- The constant sections `k ∈ ℤ/p` of `(ℤ/p)_S` over `T`, when `Γ(T, 𝒪_T)` has characteristic
`p`. -/
noncomputable def zpSHom (T : Over S) [CharP Γ(T.left, ⊤) p] :
    Multiplicative (ZMod p) →* (ZpS S p hS).obj (op T) :=
  let f : Multiplicative (ZMod p) →* (Ga S).obj (op T) :=
    (ZMod.castHom (dvd_refl p) Γ(T.left, ⊤)).toAddMonoidHom.toMultiplicative
  f.codRestrict _ fun k ↦ by
    rw [MonoidHom.mem_ker]
    change (wpGa S p hS).app (op T) (Multiplicative.ofAdd
      (ZMod.castHom (dvd_refl p) Γ(T.left, ⊤) (Multiplicative.toAdd k))) = 1
    rw [mem_ZpS_iff, ArtinSchreier.castHom_pow, sub_self]

omit [IsAffine S] in
lemma zpSHom_apply_val (T : Over S) [CharP Γ(T.left, ⊤) p] (k : Multiplicative (ZMod p)) :
    (zpSHom hS T k).1 =
      Multiplicative.ofAdd (ZMod.castHom (dvd_refl p) Γ(T.left, ⊤) (Multiplicative.toAdd k)) :=
  rfl

omit [IsAffine S] in
lemma zpSHom_bijective (T : Over S) [IsDomain Γ(T.left, ⊤)] [CharP Γ(T.left, ⊤) p] :
    Function.Bijective (zpSHom hS T) := by
  let c := ZMod.castHom (dvd_refl p) Γ(T.left, ⊤)
  refine ⟨fun k l h ↦ ?_, fun y ↦ ?_⟩
  · have h' := congrArg (fun y : (ZpS S p hS).obj (op T) ↦ y.1) h
    rw [zpSHom_apply_val, zpSHom_apply_val] at h'
    exact Multiplicative.toAdd.injective (c.injective (Multiplicative.ofAdd.injective h'))
  · obtain ⟨y, hy⟩ := y
    let x : Γ(T.left, ⊤) := Multiplicative.toAdd y
    have hx : x - x ^ p = 0 := (mem_ZpS_iff S p hS T x).1 hy
    have h0 : ∏ k : ZMod p, (x - c k) = 0 := by
      have := congrArg (Polynomial.eval x)
        (ArtinSchreier.X_pow_sub_X_eq_prod (A := Γ(T.left, ⊤)) (p := p))
      rw [Polynomial.eval_prod] at this
      simp only [eval_add, eval_sub, eval_pow, eval_X, eval_C, add_zero] at this
      rw [← this, ← neg_sub, hx, neg_zero]
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h0
    refine ⟨Multiplicative.ofAdd k, Subtype.ext ?_⟩
    rw [zpSHom_apply_val, toAdd_ofAdd, ← sub_eq_zero.1 hk]
    rfl

omit [IsAffine S] in
/-- If `Γ(T, 𝒪_T)` is a domain (e.g. `T` is the spectrum of a field), the group `(ℤ/p)_S(T)` of
sections `x` of `𝒪_T` with `xᵖ = x` is `ℤ/p`, via `k ↦ k · 1`. -/
noncomputable def zpSEquivOfIsDomain (T : Over S) [IsDomain Γ(T.left, ⊤)] :
    Multiplicative (ZMod p) ≃* (ZpS S p hS).obj (op T) :=
  letI := charP_of_isDomain hS T
  MulEquiv.ofBijective (zpSHom hS T) (zpSHom_bijective hS T)

omit [IsAffine S] in
lemma zpSEquivOfIsDomain_ofAdd_one (T : Over S) [IsDomain Γ(T.left, ⊤)] :
    (zpSEquivOfIsDomain hS T (Multiplicative.ofAdd 1)).1 =
      Multiplicative.ofAdd (α := Γ(T.left, ⊤)) 1 := by
  let _ := charP_of_isDomain hS T
  change (zpSHom hS T (Multiplicative.ofAdd 1)).1 = _
  rw [zpSHom_apply_val, toAdd_ofAdd, map_one]

/-- The section `S ⟶ ℤ/p` corresponding to `1 ∈ ℤ/p`. -/
noncomputable def zpOneSection : Over.mk (𝟙 S) ⟶ zpScheme S p :=
  (zpSchemeRepresentableBy S p hS).homEquiv.symm
    ⟨Multiplicative.ofAdd (α := Γ(S, ⊤)) 1,
      MonoidHom.mem_ker.2 ((mem_ZpS_iff S p hS (Over.mk (𝟙 S)) 1).2 (by rw [one_pow, sub_self]))⟩

lemma homEquiv_zpOneSection :
    ((zpSchemeRepresentableBy S p hS).homEquiv (zpOneSection hS)).1 =
      Multiplicative.ofAdd (α := Γ(S, ⊤)) 1 :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

variable {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)

/-- The geometric point `s̄`, as an `S`-morphism to the final `S`-scheme. -/
noncomputable abbrev toOverId : Over.mk s ⟶ Over.mk (𝟙 S) := Over.homMk s (by simp)

/-- XI.6.7: at a geometric point `s̄`, the group of points of `ℤ/p` over `s̄` is `ℤ/p`. -/
noncomputable def ptsZpSchemeEquiv :
    letI := zpGrpObj S p hS
    Pts s (zpScheme S p) ≃* Multiplicative (ZMod p) :=
  letI := zpGrpObj S p hS
  haveI : IsDomain Γ((Over.mk s).left, ⊤) := inferInstanceAs (IsDomain Γ(Spec (.of Ω), ⊤))
  ((yonedaZpSchemeIso S p hS).app (op (Over.mk s))).groupIsoToMulEquiv.trans
    (zpSEquivOfIsDomain hS (Over.mk s)).symm

/-- The point of `ℤ/p` over `s̄` given by the constant section `1`. -/
lemma ptsZpSchemeEquiv_one_section :
    letI := zpGrpObj S p hS
    ptsZpSchemeEquiv hS s (toOverId s ≫ zpOneSection hS) = Multiplicative.ofAdd 1 := by
  let _ := zpGrpObj S p hS
  have : IsDomain Γ((Over.mk s).left, ⊤) := inferInstanceAs (IsDomain Γ(Spec (.of Ω), ⊤))
  change (zpSEquivOfIsDomain hS (Over.mk s)).symm
    ((zpSchemeRepresentableBy S p hS).homEquiv (toOverId s ≫ zpOneSection hS)) = _
  rw [MulEquiv.symm_apply_eq, Functor.RepresentableBy.homEquiv_comp]
  apply Subtype.ext
  rw [zpSEquivOfIsDomain_ofAdd_one]
  change (Ga S).map (toOverId s).op
    ((zpSchemeRepresentableBy S p hS).homEquiv (zpOneSection hS)).1 = _
  rw [homEquiv_zpOneSection]
  change Multiplicative.ofAdd ((toOverId s).left.appTop (1 : Γ(S, ⊤))) = _
  rw [map_one]

/-- XI.6.7: `π₁(S, s̄)` acts trivially on the points of `ℤ/p` over `s̄`: every such point is a
power of the point given by the constant section `1`, which is fixed since the action commutes
with `S`-morphisms. -/
theorem smul_ptsZpScheme (σ : Aut (ExposeV.FEt.fiber Ω s)) (g : Pts s (zpScheme S p)) :
    letI := zpGrpObj S p hS
    haveI := isFiniteEtale_zpScheme S p hS
    σ • g = g := by
  let _ := zpGrpObj S p hS
  have := isFiniteEtale_zpScheme S p hS
  let e := ptsZpSchemeEquiv hS s
  let gen : Pts s (zpScheme S p) := toOverId s ≫ zpOneSection hS
  have hgen : σ • gen = gen := by
    rw [smul_comp]
    congr 1
    exact Over.mkIdTerminal.hom_ext _ _
  have hg : g = gen ^ (Multiplicative.toAdd (e g)).val := by
    apply e.injective
    rw [map_pow, ptsZpSchemeEquiv_one_section, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val,
      ofAdd_toAdd]
  rw [hg, smul_pow', hgen]

end Points

section TrivialAction

variable {C : Type*} [Category C] {F : C ⥤ FintypeCat} {G : Type*} [Group G]
  [MulDistribMulAction (Aut F) G] [TopologicalSpace G]

/-- XI.5, p. 300: for a trivial action of `π = Aut F` on a commutative group `G`, the continuous
cohomology set `H¹(π, G)` is the set of continuous homomorphisms `π → G`. -/
noncomputable def contH1EquivOfTrivial (hc : ∀ a b : G, a * b = b * a)
    (htriv : ∀ (σ : Aut F) (g : G), σ • g = g) : ContH1 F G ≃ ContinuousMonoidHom (Aut F) G where
  toFun c :=
    { toMonoidHom := Z1.equivMonoidHom htriv c.2.choose
      continuous_toFun := c.2.choose_spec.1 }
  invFun f :=
    ⟨SGA.SGA1.ExposeXI.H1.mk ((Z1.equivMonoidHom htriv).symm f.toMonoidHom), _, f.continuous, rfl⟩
  left_inv c := Subtype.ext (by
    change SGA.SGA1.ExposeXI.H1.mk
      ((Z1.equivMonoidHom htriv).symm (Z1.equivMonoidHom htriv c.2.choose)) = c.1
    rw [Equiv.symm_apply_apply]
    exact c.2.choose_spec.2)
  right_inv f := by
    let c : ContH1 F G :=
      ⟨SGA.SGA1.ExposeXI.H1.mk ((Z1.equivMonoidHom htriv).symm f.toMonoidHom), _, f.continuous,
        rfl⟩
    obtain ⟨g, hg⟩ := (Z1.cohomologous_iff_of_trivial htriv).1
      (SGA.SGA1.ExposeXI.H1.mk_eq_mk.1 c.2.choose_spec.2)
    ext σ
    change c.2.choose σ = f σ
    rw [show f σ = ((Z1.equivMonoidHom htriv).symm f.toMonoidHom) σ from rfl, hg σ, hc g⁻¹,
      _root_.mul_assoc, _root_.inv_mul_cancel, _root_.mul_one]

/-- Continuous homomorphisms into isomorphic discrete groups. -/
def continuousMonoidHomCongrDiscrete {Γ A B : Type*} [Group Γ] [TopologicalSpace Γ] [Group A]
    [TopologicalSpace A] [DiscreteTopology A] [Group B] [TopologicalSpace B] [DiscreteTopology B]
    (e : A ≃* B) : ContinuousMonoidHom Γ A ≃ ContinuousMonoidHom Γ B where
  toFun f :=
    { toMonoidHom := e.toMonoidHom.comp f.toMonoidHom
      continuous_toFun := (continuous_of_discreteTopology (f := e)).comp f.continuous }
  invFun f :=
    { toMonoidHom := e.symm.toMonoidHom.comp f.toMonoidHom
      continuous_toFun := (continuous_of_discreteTopology (f := e.symm)).comp f.continuous }
  left_inv f := by ext x; exact e.symm_apply_apply (f x)
  right_inv f := by ext x; exact e.apply_symm_apply (f x)

end TrivialAction

section Cohomology

attribute [local instance] instTopologicalSpacePts instDiscreteTopologyPts

variable [ConnectedSpace S] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)

/-- XI.5 `(*)` for the constant group `ℤ/p` (with XI.6.7): for a connected affine scheme `S` of
characteristic `p` and a geometric point `s̄`, `H¹(S, (ℤ/p)_S)` is the set of continuous
homomorphisms `π₁(S, s̄) → ℤ/p`; here `ℤ/p` is the group `(ℤ/p)(s̄)` of points of the group
scheme `ℤ/p` over `s̄` (`ptsZpSchemeEquiv`), with its discrete topology. -/
noncomputable def h1ZpSEquivContinuousMonoidHom :
    letI := zpGrpObj S p hS
    CategoryTheory.H1 (fpqc S) (ZpS S p hS) ≃
      ContinuousMonoidHom (Aut (ExposeV.FEt.fiber Ω s)) (Pts s (zpScheme S p)) :=
  letI := zpGrpObj S p hS
  haveI := isFiniteEtale_zpScheme S p hS
  let e := ptsZpSchemeEquiv hS s
  (h1ZpSchemeEquiv S p hS).symm.trans ((h1EquivContH1 (s := s) (zpScheme S p)).trans
    (contH1EquivOfTrivial (fun a b ↦ e.injective (by rw [map_mul, map_mul, mul_comm]))
      (smul_ptsZpScheme hS s)))

/-- XI.6.9 with XI.5 `(*)`, Artin–Schreier theory of `π₁`: for a connected affine scheme `S` of
characteristic `p` with a geometric point `s̄`, `Γ(S, 𝒪_S) / ℘ Γ(S, 𝒪_S)` is in bijection with the
set of continuous homomorphisms `π₁(S, s̄) → ℤ/p`, where `ℤ/p` is any discrete group `D`
identified with `ℤ/p`. The class of `a` goes to the homomorphism describing the action of `π₁` on
the Artin–Schreier covering `Tᵖ - T + a` (the coboundary `∂ a`). -/
noncomputable def artinSchreierEquivContinuousMonoidHom {D : Type*} [Group D] [TopologicalSpace D]
    [DiscreteTopology D] (eD : D ≃* Multiplicative (ZMod p)) :
    Multiplicative Γ(S, ⊤) ⧸ (wpΓ S p hS).range ≃
      ContinuousMonoidHom (Aut (ExposeV.FEt.fiber Ω s)) D :=
  letI := zpGrpObj S p hS
  (Equiv.ofBijective _ (artinSchreierLeft_bijective_of_isAffine p hS)).trans
    ((h1ZpSEquivContinuousMonoidHom S p hS s).trans
      (continuousMonoidHomCongrDiscrete ((ptsZpSchemeEquiv hS s).trans eD.symm)))

end Cohomology

end SGA.SGA1.ExposeXI
