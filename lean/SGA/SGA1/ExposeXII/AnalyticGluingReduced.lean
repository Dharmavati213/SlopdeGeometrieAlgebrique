/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.ReducedComparison
import SGA.SGA1.ExposeXII.ClosureComparison

/-!
# `(X^an)_red` is the reduction of `X^an` (affine case)

For `A = ℂ[x₁, …, xₙ]/(g)` and `X = Spec A`, `ReducedComparison.lean` builds the morphism of
locally ringed spaces `reducedComparison g : (X^an)_red → X^an` from the space `X(ℂ)` with its sheaf
of analytic functions to the local model `Z(g)` with structure sheaf `(𝒪/(g))|_{Z(g)}`. It is a
homeomorphism on points (`reducedBase`). Here we prove that it is the reduction of `X^an`. This
is auxiliary (SGA states no number for it); it is used for XII.2.1 (vii) and XII.2.2.

* `surjective_stalkMap_reducedComparison`: the stalk maps `𝒪_{X^an,x} → 𝒪_{(X^an)_red,x}` are
  surjective (every analytic function on `X(ℂ)` is locally the value function of a section of
  `𝒪_{X^an}`);
* `ker_stalkMap_reducedComparison`: their kernel is the nilradical. A germ whose values vanish
  near `x` is nilpotent: this is Rückert's Nullstellensatz
  (`AnalyticGeometry.LocalModelData.isNilpotent_classOf_of_eventually_eq_zero`).

Also: the stalks of the sheaf of analytic functions on `X(ℂ)` are reduced
(`SchemePoints.isReduced_stalk_analyticPresheaf`, any `X`).

The non-affine case: the underlying spaces of `X^an` and `X(ℂ)` are identified in
`AnalyticGluingPoints.lean`; the sheaf-level statement for non-affine `X` is not formalized.
-/

noncomputable section

open CategoryTheory Topology Set Opposite Filter AlgebraicGeometry AnalyticGeometry
open TopologicalSpace (Opens)

namespace SGA.SGA1.ExposeXII

namespace SchemePoints

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]

/-- A section of the sheaf of analytic functions whose germ at `x` vanishes vanishes near `x`. -/
lemma eventually_eq_zero_of_germ_eq_zero {W : Opens (TopCat.of (SchemePoints ℂ X))}
    {x : SchemePoints ℂ X} (hx : x ∈ W) (f : (analyticPresheaf ℂ X).obj (op W))
    (h : (analyticPresheaf ℂ X).germ W x hx f = 0) : ∀ᶠ z in 𝓝 x, extend ℂ X f.1 z = 0 := by
  have h' : (analyticPresheaf ℂ X).germ W x hx f = (analyticPresheaf ℂ X).germ W x hx 0 := by
    rw [h, map_zero]
  obtain ⟨V, hxV, iU, iV, e⟩ := (analyticPresheaf ℂ X).germ_eq x hx hx f 0 h'
  filter_upwards [V.2.mem_nhds hxV] with z hz
  have := congr_arg (fun t : (analyticPresheaf ℂ X).obj (op V) ↦ t.1 ⟨z, hz⟩) e
  rw [map_zero] at this
  rw [extend_of_mem _ (leOfHom iU hz)]
  exact this

/-- A section of the sheaf of analytic functions vanishing near `x` has zero germ at `x`. -/
lemma germ_eq_zero_of_eventually {W : Opens (TopCat.of (SchemePoints ℂ X))}
    {x : SchemePoints ℂ X} (hx : x ∈ W) (f : (analyticPresheaf ℂ X).obj (op W))
    (h : ∀ᶠ z in 𝓝 x, extend ℂ X f.1 z = 0) : (analyticPresheaf ℂ X).germ W x hx f = 0 := by
  obtain ⟨V₀, hV₀, hV₀o, hxV₀⟩ := mem_nhds_iff.mp h
  let V : Opens (TopCat.of (SchemePoints ℂ X)) := ⟨V₀ ∩ W, hV₀o.inter W.2⟩
  have hVW : V ≤ W := fun _ hz ↦ hz.2
  have hres : (analyticPresheaf ℂ X).map (homOfLE hVW).op f = 0 := Subtype.ext (funext fun z ↦ by
    have : extend ℂ X f.1 z = 0 := hV₀ z.2.1
    rw [extend_of_mem _ z.2.2] at this
    exact this)
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hVW) x ⟨hxV₀, hx⟩ f, hres, map_zero]

/-- The stalks of the sheaf of analytic functions on `X(ℂ)` are reduced. -/
instance isReduced_stalk_analyticPresheaf (x : SchemePoints ℂ X) :
    IsReduced ((analyticPresheaf ℂ X).stalk x) := by
  refine ⟨fun t ⟨m, hm⟩ ↦ ?_⟩
  obtain ⟨W, hxW, f, rfl⟩ := (analyticPresheaf ℂ X).exists_germ_eq t
  rw [← map_pow] at hm
  have h := eventually_eq_zero_of_germ_eq_zero hxW _ hm
  refine germ_eq_zero_of_eventually hxW f ?_
  filter_upwards [h, W.2.mem_nhds hxW] with z hz hzW
  rw [extend_of_mem _ hzW] at hz ⊢
  exact pow_eq_zero_iff'.mp hz |>.1

end SchemePoints

namespace AffineAnalytification

open SchemePoints LocalModelData

attribute [local instance] SchemePoints.specOver SchemePoints.sectionsAlgebra

variable {n k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ)

/-- `(X^an)_red`, the reduced analytic space of `Spec(ℂ[x]/(g))`. -/
abbrev reducedSpace : LocallyRingedSpace :=
  SchemePoints.analytification ℂ (Spec (.of (PresentedAlgebra g)))

lemma stalkMap_reducedComparison_germ (y : reducedSpace g)
    (W : Opens (TopCat.of (polynomialModel g).zeroSet)) (hW : (reducedComparison g).base y ∈ W)
    (s : (polynomialModel g).presheaf.obj (op W)) :
    ((reducedComparison g).stalkMap y).hom ((analytification g).presheaf.germ W _ hW s) =
      (SchemePoints.analyticPresheaf ℂ _).germ ((Opens.map (reducedBaseHom g)).obj W) y hW
        (reducedSectionHom g W s) :=
  PresheafedSpace.stalkMap_germ_apply (reducedComparison g).toShHom.hom W y hW s

/-- `(X^an)_red` is the reduction of `X^an` (auxiliary, used for XII.2.1 (vii) and XII.2.2),
kernel: a germ of `𝒪_{X^an}` whose values vanish near `x` is nilpotent (Rückert's
Nullstellensatz). -/
theorem isNilpotent_of_stalkMap_reducedComparison_eq_zero (y : reducedSpace g)
    (t : (analytification g).presheaf.stalk ((reducedComparison g).base y))
    (h : ((reducedComparison g).stalkMap y).hom t = 0) : IsNilpotent t := by
  obtain ⟨W, hxW, s, rfl⟩ := (analytification g).presheaf.exists_germ_eq t
  rw [stalkMap_reducedComparison_germ g y W hxW s] at h
  have h₁ := eventually_eq_zero_of_germ_eq_zero _ _ h
  set x : (polynomialModel g).zeroSet := reducedBase g y
  have hxW' : x ∈ W := hxW
  -- transport to `Z(g)` along the homeomorphism `reducedBase`
  have h₂ : ∀ᶠ q in 𝓝 x, ∀ hqW : q ∈ W, (polynomialModel g).evalFiber q (s.1 ⟨q, hqW⟩) = 0 := by
    rw [← (reducedBase g).map_nhds_eq y]
    refine Filter.eventually_map.mpr ?_
    filter_upwards [h₁] with z hz hzW
    rw [extend_of_mem _ hzW] at hz
    exact hz
  obtain ⟨V, hxV, G, hG, hsG⟩ := exists_classOf_eq s ⟨x, hxW'⟩
  have h₃ : ∀ᶠ q in 𝓝 x, G ((q : (polynomialModel g).zeroSet) : Fin n → ℂ) = 0 := by
    filter_upwards [h₂, W.2.mem_nhds hxW', V.2.mem_nhds hxV] with q hq hqW hqV
    rw [← (polynomialModel g).evalFiber_classOf q G (hG q hqV), ← hsG q hqW hqV]
    exact hq hqW
  have h₄ : IsNilpotent ((polynomialModel g).classOf x G (hG x hxV)) :=
    (polynomialModel g).isNilpotent_classOf_of_eventually_eq_zero x G (hG x hxV) h₃
  rw [← hsG x hxW' hxV, ← (polynomialModel g).stalkToFiber_germ W x hxW' s] at h₄
  have h₅ := h₄.map ((polynomialModel g).stalkIso x).symm.toRingHom
  change IsNilpotent ((polynomialModel g).presheaf.germ W x hxW' s)
  have e : ((polynomialModel g).stalkIso x).symm.toRingHom
      ((polynomialModel g).stalkToFiber x ((polynomialModel g).presheaf.germ W x hxW' s)) =
      (polynomialModel g).presheaf.germ W x hxW' s :=
    ((polynomialModel g).stalkIso x).symm_apply_apply _
  rwa [e] at h₅

/-- `(X^an)_red` is the reduction of `X^an` (auxiliary, used for XII.2.1 (vii) and XII.2.2): the
kernel of the stalk map `𝒪_{X^an,x} → 𝒪_{(X^an)_red,x}` is the nilradical. -/
theorem ker_stalkMap_reducedComparison (y : reducedSpace g) :
    RingHom.ker ((reducedComparison g).stalkMap y).hom = nilradical _ := by
  ext t
  rw [RingHom.mem_ker, mem_nilradical]
  refine ⟨isNilpotent_of_stalkMap_reducedComparison_eq_zero g y t, fun h ↦ ?_⟩
  exact (SchemePoints.isReduced_stalk_analyticPresheaf (X := Spec (.of (PresentedAlgebra g)))
    y).eq_zero _ (h.map _)

/-- The value at `z ∈ X(ℂ)` of a global section `[p]` of `𝒪_X`, `X = Spec(ℂ[x]/(g))`, is
`p(z)`. -/
lemma eval_ΓSpecIso_inv (p : MvPolynomial (Fin n) ℂ)
    (z : SchemePoints ℂ (Spec (.of (PresentedAlgebra g)))) :
    eval (isAffineOpen_top _) ((Scheme.ΓSpecIso (.of (PresentedAlgebra g))).inv
      (Ideal.Quotient.mk _ p)) z =
      MvPolynomial.eval ((reducedBase g z : (polynomialModel g).zeroSet) : Fin n → ℂ) p := by
  rw [eval_reducedBase_eq_value]
  have h := value_eq_eval (isAffineOpen_top (Spec (.of (PresentedAlgebra g)))) le_rfl
    ((Scheme.ΓSpecIso (.of (PresentedAlgebra g))).inv (Ideal.Quotient.mk _ p))
    (p := z) trivial
  have hs : (homOfLE (le_rfl : (⊤ : (Spec (.of (PresentedAlgebra g))).Opens) ≤ ⊤)) = 𝟙 ⊤ :=
    Subsingleton.elim _ _
  rw [hs, op_id, CategoryTheory.Functor.map_id] at h
  exact h.symm

/-- `(X^an)_red` is the reduction of `X^an` (auxiliary, used for XII.2.1 (vii) and XII.2.2): the
stalk maps `𝒪_{X^an,x} → 𝒪_{(X^an)_red,x}` are surjective. Every analytic function on `X(ℂ)`
is, near a point, an analytic function `G` of finitely many polynomials, hence the value function
of the class of `G ∘ (p₁, …, p_m)` in `𝒪_{X^an}`. -/
theorem surjective_stalkMap_reducedComparison (y : reducedSpace g) :
    Function.Surjective ((reducedComparison g).stalkMap y).hom := by
  intro u
  obtain ⟨W, hyW, F, rfl⟩ := (SchemePoints.analyticPresheaf ℂ _).exists_germ_eq u
  obtain ⟨m, a, G, hG, hFG⟩ :=
    (F.2 ⟨y, hyW⟩).exists_of_isAffineOpen (isAffineOpen_top _) (Set.mem_univ _)
  have hp (i : Fin m) : ∃ q : MvPolynomial (Fin n) ℂ,
      (Scheme.ΓSpecIso (.of (PresentedAlgebra g))).inv (Ideal.Quotient.mk _ q) = a i := by
    obtain ⟨q, hq⟩ := Ideal.Quotient.mk_surjective
      ((Scheme.ΓSpecIso (.of (PresentedAlgebra g))).hom (a i))
    refine ⟨q, ?_⟩
    rw [hq]
    exact (Scheme.ΓSpecIso (.of (PresentedAlgebra g))).hom_inv_id_apply (a i)
  choose q hq using hp
  have hev (z : SchemePoints ℂ (Spec (.of (PresentedAlgebra g)))) :
      (fun i ↦ eval (isAffineOpen_top _) (a i) z) =
        fun i ↦ MvPolynomial.eval ((reducedBase g z : (polynomialModel g).zeroSet) : Fin n → ℂ)
          (q i) :=
    funext fun i ↦ by rw [← hq i, eval_ΓSpecIso_inv]
  let Φ : (Fin n → ℂ) → ℂ := fun w ↦ G fun i ↦ MvPolynomial.eval w (q i)
  let x : (polynomialModel g).zeroSet := reducedBase g y
  have hΦ : AnalyticAt ℂ Φ (x : Fin n → ℂ) := by
    refine AnalyticAt.comp ?_ (AnalyticAt.pi fun i ↦ analyticAt_eval_mvPolynomial (q i) _)
    rw [← hev y]
    exact hG
  -- the open set where `F` agrees with `G(a)` and `Φ` is analytic
  obtain ⟨O₀, hO₀, hO₀o, hyO₀⟩ := mem_nhds_iff.mp hFG
  let O : Set (SchemePoints ℂ (Spec (.of (PresentedAlgebra g)))) :=
    O₀ ∩ W ∩ (fun z ↦ ((reducedBase g z : (polynomialModel g).zeroSet) : Fin n → ℂ)) ⁻¹'
      {w | AnalyticAt ℂ Φ w}
  have hOo : IsOpen O := (hO₀o.inter W.2).inter ((isOpen_analyticAt ℂ Φ).preimage
    (continuous_subtype_val.comp (reducedBase g).continuous))
  let V : Opens (TopCat.of (polynomialModel g).zeroSet) :=
    ⟨reducedBase g '' O, (reducedBase g).isOpenMap O hOo⟩
  have hxV : x ∈ V := ⟨y, ⟨⟨hyO₀, hyW⟩, hΦ⟩, rfl⟩
  have hVΦ : ∀ v ∈ V, AnalyticAt ℂ Φ ((v : (polynomialModel g).zeroSet) : Fin n → ℂ) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz.2
  let σ := (polynomialModel g).classSectionOn Φ V hVΦ
  refine ⟨(analytification g).presheaf.germ V ((reducedComparison g).base y) hxV σ, ?_⟩
  rw [stalkMap_reducedComparison_germ g y V hxV σ]
  have hOW : (Opens.map (reducedBaseHom g)).obj V ≤ W := by
    rintro z ⟨z', hz', hzz'⟩
    rw [(reducedBase g).injective hzz'] at hz'
    exact hz'.1.2
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hOW) y hxV F]
  congr 1
  refine Subtype.ext (funext fun z ↦ ?_)
  obtain ⟨z', hz', hzz'⟩ := z.2
  have hz : z.1 ∈ O := (reducedBase g).injective hzz' ▸ hz'
  symm
  change F.1 ⟨z.1, hOW z.2⟩ =
    (polynomialModel g).evalFiber _ ((polynomialModel g).classOf _ Φ (hVΦ _ z.2))
  rw [LocalModelData.evalFiber_classOf]
  have := hO₀ hz.1.1
  simp only [Set.mem_ofPred_eq] at this
  rw [extend_of_mem _ (hOW z.2), hev] at this
  exact this

end AffineAnalytification

end SGA.SGA1.ExposeXII
