/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.ProperSmoothRegularGroup

/-!
# SGA 1, Exposé XIII, 4.4 over a regular base: the covering of the generic fibre

Let `h : Y → Spec K` be proper and smooth with geometrically connected fibres and with a section
`e` (in the application `Y = X_K` is the generic fibre of `f : X → S` and `e` comes from the
section of `f`), and `t : Spec Ω → Spec K` a geometric point. For a principal covering `Z` of
`Y_Ω = Y ×_K Ω` whose group is an `L`-group we construct a connected étale covering `W` of `Y` such
that `Z` is a connected component of `W ×_Y Y_Ω`, and every *good* element of `π₁(Y)`
(`IsGoodFor`, for the section `σ = π₁(e)` and the open normal subgroups of `L`-index of
`π₁(Y_Ω) ⊆ π₁(Y)`) acts trivially on the fibre of `W`
(`exists_isConnected_mono_forall_isGoodFor_of_section`). This is the Galois-category statement
`exists_isConnected_mono_forall_isGoodFor` for the fibre functors at the point `basePt h e he t`
of `Y_Ω` lying on the section; the exactness of `1 → π₁(Y_Ω) → π₁(Y) → π₁(K) → 1` is IX.6.1
(`injective_map_fst_of_field`, `properHomotopyExactSequenceFull`).

In the proof of the second part of XIII.4.4 over a regular base, `W` is shown to extend to an
étale covering of `X`, using the core of X.3.8 at the codimension-one points of the base.

Also here: `exists_conjAut_eq_fiberCongr` (a conjugation between fibre
functors at equal points is a transport composed with an inner automorphism) and
`FundamentalGroup.map_congr` (maps along equal morphisms), used to compare maps of fundamental
groups along commutative squares up to paths.
-/

universe u w

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeXIII

/-- Conjugation by an isomorphism `φ` of fibre functors at two equal geometric points is the
transport along the equality composed with an inner automorphism. -/
lemma exists_conjAut_eq_fiberCongr {Ω : Type u} [Field Ω] {T : Scheme.{u}}
    {x x' : Spec (.of Ω) ⟶ T} (h : x = x') (φ : ExposeV.FEt.fiber Ω x ≅ ExposeV.FEt.fiber Ω x') :
    ∃ c : FundamentalGroup x, ∀ σ : FundamentalGroup x,
      φ.conjAut σ = (ExposeV.FEt.fiberCongr Ω h).conjAut (c * σ * c⁻¹) := by
  refine ⟨φ ≪≫ (ExposeV.FEt.fiberCongr Ω h).symm, fun σ ↦ ?_⟩
  apply Iso.ext
  change φ.inv ≫ σ.hom ≫ φ.hom = (ExposeV.FEt.fiberCongr Ω h).inv ≫
    (((ExposeV.FEt.fiberCongr Ω h).hom ≫ φ.inv) ≫ σ.hom ≫
      (φ.hom ≫ (ExposeV.FEt.fiberCongr Ω h).inv)) ≫ (ExposeV.FEt.fiberCongr Ω h).hom
  simp

/-- Maps of fundamental groups along equal morphisms agree up to the transport of the base
point. -/
lemma FundamentalGroup.map_congr {Ω : Type u} [Field Ω] {T R : Scheme.{u}} {g g' : T ⟶ R}
    (hg : g = g') (y : Spec (.of Ω) ⟶ T) :
    FundamentalGroup.map g y =
      ((ExposeV.FEt.fiberCongr Ω (congrArg (y ≫ ·) hg.symm)).conjAut.toMonoidHom).comp
        (FundamentalGroup.map g' y) := by
  subst hg
  ext σ : 1
  simp [ExposeV.FEt.fiberCongr, Iso.conjAut_apply]
  rfl

variable {K : Type u} [Field K] {Y : Scheme.{u}} (h : Y ⟶ Spec (.of K)) [IsProper h] [Smooth h]
  [GeometricallyConnected h] (e : Spec (.of K) ⟶ Y) (he : e ≫ h = 𝟙 _)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of K))

/-- The geometric point of `Y_Ω = Y ×_K Ω` lying on the section `e`. -/
noncomputable def basePt : Spec (.of Ω) ⟶ pullback h t :=
  pullback.lift (t ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])

omit [IsProper h] [Smooth h] [GeometricallyConnected h] [IsAlgClosed Ω] in
lemma basePt_fst : basePt h e he t ≫ pullback.fst h t = t ≫ e :=
  pullback.lift_fst _ _ _

/-- The section `σ : π₁(K, t) → π₁(Y, a)` induced by `e`, at the point `a` of `Y` below
`basePt`. -/
noncomputable def sectionHom :
    FundamentalGroup t →* FundamentalGroup (basePt h e he t ≫ pullback.fst h t) :=
  (ExposeV.FEt.fiberCongr Ω (basePt_fst h e he t).symm).conjAut.toMonoidHom.comp
    (FundamentalGroup.map e t)

omit [IsProper h] [Smooth h] [GeometricallyConnected h] [IsAlgClosed Ω] in
lemma continuous_sectionHom [ConnectedSpace Y] : Continuous (sectionHom h e he t) :=
  (ExposeV.continuous_conjAut _).comp (FundamentalGroup.continuous_map _ _)

omit [IsProper h] [Smooth h] [GeometricallyConnected h] [IsAlgClosed Ω] in
/-- The projection `π₁(Y, a) → π₁(K, t)`, normalized (by a conjugation) so that it is a
retraction of `sectionHom`, with the kernel of `π₁(h)`. -/
theorem exists_retraction [ConnectedSpace Y] :
    ∃ π : FundamentalGroup (basePt h e he t ≫ pullback.fst h t) →* FundamentalGroup t,
      Continuous π ∧ (∀ γ, π (sectionHom h e he t γ) = γ) ∧
        π.ker = (FundamentalGroup.map h (basePt h e he t ≫ pullback.fst h t)).ker := by
  set a := basePt h e he t ≫ pullback.fst h t
  have hā : t ≫ e = a := (basePt_fst h e he t).symm
  obtain ⟨φ, hφ⟩ := ExposeV.etaleFundamentalGroup.exists_map_comp_map_eq_conjAut Ω e h he t
  have hc := FundamentalGroup.map_comp_conjAut_fiberCongr h hā
  let ψ := φ ≪≫ ExposeV.FEt.fiberCongr Ω (congrArg (· ≫ h) hā)
  have hπσ : (FundamentalGroup.map h a).comp (sectionHom h e he t) =
      ψ.conjAut.toMonoidHom := by
    rw [sectionHom, ← MonoidHom.comp_assoc, hc, MonoidHom.comp_assoc]
    change _ = ψ.conjAut.toMonoidHom
    have : (FundamentalGroup.map h (t ≫ e)).comp (FundamentalGroup.map e t) =
        φ.conjAut.toMonoidHom := hφ
    rw [this]
    ext σ : 1
    simp [ψ, Iso.trans_conjAut]
  refine ⟨ψ.symm.conjAut.toMonoidHom.comp (FundamentalGroup.map h a),
    (ExposeV.continuous_conjAut ψ.symm).comp (FundamentalGroup.continuous_map _ _), fun γ ↦ ?_,
    ?_⟩
  · have := DFunLike.congr_fun hπσ γ
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, this]
    apply Iso.ext
    rw [Iso.conjAut_hom, Iso.conjAut_hom, Iso.symm_self_conj]
  · ext σ
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
    rfl

/-- **The covering of the generic fibre.** Let `h : Y → Spec K` be proper and smooth with
geometrically connected fibres, with a section `e`, and `t : Spec Ω → Spec K` with `Ω`
algebraically closed. For a connected étale covering `Z` of `Y_Ω` and a point `z` of its fibre at
`basePt h e he t` (the point on the section) whose stabilizer `N` is normal of `L`-index (a
principal covering whose group is an `L`-group), there is a connected étale covering `W` of `Y`
such that `Z` is a connected component of `W ×_Y Y_Ω`, and every element of `π₁(Y)` that is good
for `π₁(Y_Ω) = ker(π₁(Y) → π₁(K))`, the section `π₁(e)` and the open normal subgroups of
`L`-index of `π₁(Y_Ω)` acts trivially on the fibre of `W`. (`W` is constructed as the connected
covering with a point of stabilizer `N ⊔ σ(Γ_N)`, `Γ_N` the stabilizer of `N` under the action of
`π₁(K)` through `σ`; the conclusion does not record this.) -/
theorem exists_isConnected_mono_forall_isGoodFor_of_section (L : Set ℕ)
    (Z : ExposeV.FEt (pullback h t)) [IsConnected Z]
    (z : (ExposeV.FEt.fiber Ω (basePt h e he t)).obj Z)
    (hzn : (MulAction.stabilizer (FundamentalGroup (basePt h e he t)) z).Normal)
    (hzL : IsLIndex L (MulAction.stabilizer (FundamentalGroup (basePt h e he t)) z)) :
    ∃ (W : ExposeV.FEt Y) (_ : IsConnected W)
      (i : Z ⟶ (ExposeV.FEt.pullback (pullback.fst h t)).obj W), Mono i ∧
      ∀ j : FundamentalGroup (basePt h e he t ≫ pullback.fst h t),
        IsGoodFor (FundamentalGroup.map h (basePt h e he t ≫ pullback.fst h t)).ker
          (sectionHom h e he t)
          (lIndexSubgroups L (FundamentalGroup.map h (basePt h e he t ≫ pullback.fst h t)).ker) j →
        ∀ w : (ExposeV.FEt.fiber Ω (basePt h e he t ≫ pullback.fst h t)).obj W, j • w = w := by
  have : ExposeIX.Submersive h := inferInstance
  have : ConnectedSpace Y := ExposeIX.connectedSpace_of_submersive h
  have : ConnectedSpace ↥(pullback h t) :=
    GeometricallyConnected.geometrically_connectedSpace (f := h) t _ _
      (IsPullback.of_hasPullback h t)
  obtain ⟨π, hπc, hπσ, hπk⟩ := exists_retraction h e he t
  obtain ⟨-, -, hr⟩ := properHomotopyExactSequenceFull h Ω t Ω (basePt h e he t)
  have hu := injective_map_fst_of_field K h Ω t Ω (basePt h e he t)
  rw [← hπk]
  exact exists_isConnected_mono_forall_isGoodFor (ExposeV.FEt.pullback (pullback.fst h t))
    (fiberPullbackIso (pullback.fst h t) (basePt h e he t)) L hπc (continuous_sectionHom h e he t)
    hπσ hu (hr.trans hπk.symm) Z z hzn hzL

end SGA.SGA1.ExposeXIII
