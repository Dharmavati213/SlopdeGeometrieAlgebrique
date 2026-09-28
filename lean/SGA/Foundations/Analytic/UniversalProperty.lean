/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.SectionMorphism
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Morphisms into local models are determined by the coordinates

A morphism of locally ringed spaces `f : Z(D') → Z(D)` between local models (`D ⊆ 𝕜ⁿ`) which is
`𝕜`-linear (it pulls back constant functions to constant functions) is determined by the pullbacks
`f^*(zᵢ)` of the coordinate functions (`eq_of_coordPullback`): on points `f(y)` is read off from the
values of `f^*(zᵢ)`, and on germs, an analytic germ agrees with its Taylor polynomial (a polynomial
in the coordinates) to any order `m`, so `f^*` and `g^*` agree modulo `𝔪ᵐ` for all `m`, hence agree
by Krull's intersection theorem ([Grauert–Remmert, *Coherent analytic sheaves*, §1.3]).
-/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Filter Topology IsLocalRing

namespace AnalyticGeometry

namespace LocalModelData

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E E' : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E']
  [NormedSpace 𝕜 E']

/-! ### Stalk maps of morphisms of local models -/

section StalkMaps

variable {D' : LocalModelData 𝕜 E'} {D : LocalModelData 𝕜 E}
  (f : D'.toLocallyRingedSpace ⟶ D.toLocallyRingedSpace)

/-- The map `𝒪_{E,f(y)}/(f) → 𝒪_{E',y}/(f')` induced by a morphism of local models. -/
def fiberMapOf (y : D'.zeroSet) : D.Fiber (f.base y) →+* D'.Fiber y :=
  (D'.stalkIso y).toRingHom.comp ((f.stalkMap y).hom.comp (D.stalkIso (f.base y)).symm.toRingHom)

instance isLocalHom_fiberMapOf (y : D'.zeroSet) : IsLocalHom (fiberMapOf f y) := by
  refine ⟨fun t ht ↦ ?_⟩
  have h₁ : IsUnit ((f.stalkMap y).hom ((D.stalkIso (f.base y)).symm t)) :=
    (MulEquiv.isUnit_map (D'.stalkIso y).toMulEquiv).mp ht
  have h₂ := (LocallyRingedSpace.isLocalHomStalkMap f y).map_nonunit _ h₁
  exact (MulEquiv.isUnit_map (D.stalkIso (f.base y)).symm.toMulEquiv).mp h₂

lemma c_app_apply (W : Opens (TopCat.of D.zeroSet)) (t : D.presheaf.obj (op W)) (y : D'.zeroSet)
    (hy : f.base y ∈ W) : (f.c.app (op W) t).1 ⟨y, hy⟩ = fiberMapOf f y (t.1 ⟨f.base y, hy⟩) := by
  have h₁ : (D.stalkIso (f.base y)).symm (t.1 ⟨f.base y, hy⟩) =
      D.presheaf.germ W (f.base y) hy t := by
    apply (D.stalkIso _).injective
    rw [RingEquiv.apply_symm_apply]
    exact (D.stalkToFiber_germ W _ hy t).symm
  change _ = D'.stalkIso y ((f.stalkMap y).hom ((D.stalkIso (f.base y)).symm _))
  rw [h₁]
  erw [AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply]
  exact (D'.stalkToFiber_germ _ y hy _).symm

/-- A morphism of local models is `𝕜`-linear if it pulls back constants to constants. -/
def IsKLinear : Prop :=
  ∀ c : 𝕜, f.c.app (op ⊤) (D.constSection ⊤ c) = D'.constSection _ c

variable {f}

lemma fiberMapOf_constFiber (hf : IsKLinear f) (y : D'.zeroSet) (c : 𝕜) :
    fiberMapOf f y (D.constFiber (f.base y) c) = D'.constFiber y c := by
  have h := congrArg (fun s ↦ s.1 ⟨y, trivial⟩) (hf c)
  exact (c_app_apply f ⊤ _ y trivial).symm.trans h

lemma map_maximalIdeal_fiberMapOf (y : D'.zeroSet) {t : D.Fiber (f.base y)}
    (ht : t ∈ maximalIdeal _) : fiberMapOf f y t ∈ maximalIdeal (D'.Fiber y) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ht ⊢
  exact fun h ↦ ht ((isLocalHom_fiberMapOf f y).map_nonunit _ h)

lemma pow_le_comap_fiberMapOf (y : D'.zeroSet) (m : ℕ) :
    maximalIdeal (D.Fiber (f.base y)) ^ m ≤
      (maximalIdeal (D'.Fiber y) ^ m).comap (fiberMapOf f y) := by
  have h₁ : maximalIdeal (D.Fiber (f.base y)) ≤
      (maximalIdeal (D'.Fiber y)).comap (fiberMapOf f y) :=
    fun _ ht ↦ map_maximalIdeal_fiberMapOf y ht
  exact (Ideal.pow_right_mono h₁ m).trans (Ideal.le_comap_pow (fiberMapOf f y) m)

lemma evalFiber_fiberMapOf (hf : IsKLinear f) (y : D'.zeroSet) (t : D.Fiber (f.base y)) :
    D'.evalFiber y (fiberMapOf f y t) = D.evalFiber (f.base y) t := by
  have h₁ := map_maximalIdeal_fiberMapOf y (D.sub_constFiber_mem_maximalIdeal _ t)
  rw [map_sub, fiberMapOf_constFiber hf, mem_maximalIdeal_fiber_iff, map_sub,
    sub_eq_zero] at h₁
  rw [h₁]
  exact D'.evalFiber_classOf y _ analyticAt_const

end StalkMaps

/-! ### Coordinates and Taylor polynomials -/

section Coordinates

variable {n : ℕ}

variable (D : LocalModelData 𝕜 (Fin n → 𝕜)) in
/-- The coordinate functions `zᵢ` on a local model in `𝕜ⁿ`. -/
def coord (i : Fin n) : D.presheaf.obj (op ⊤) :=
  D.globalSection (fun z ↦ z i) fun x _ ↦ MvPowerSeries.analyticAt_apply i x

variable (D : LocalModelData 𝕜 (Fin n → 𝕜)) in
/-- Classes of polynomial functions, as a ring homomorphism `𝕜[z] → 𝒪_{E,x}/(f)`. -/
def polyClassHom (x : D.zeroSet) : MvPolynomial (Fin n) 𝕜 →+* D.Fiber x :=
  (Ideal.Quotient.mk _).comp (polyGermHom (x : Fin n → 𝕜))

lemma polyClassHom_apply {D : LocalModelData 𝕜 (Fin n → 𝕜)} (x : D.zeroSet)
    (p : MvPolynomial (Fin n) 𝕜) :
    D.polyClassHom x p = D.classOf x (fun z ↦ MvPolynomial.eval z p)
      (analyticAt_eval_mvPolynomial p _) := by
  rw [polyClassHom, RingHom.comp_apply, polyGermHom_apply]
  rfl

lemma polyClassHom_eq_eval₂Hom {D : LocalModelData 𝕜 (Fin n → 𝕜)} (x : D.zeroSet) :
    D.polyClassHom x = MvPolynomial.eval₂Hom (D.constFiber x)
      fun i ↦ D.classOf x (fun z ↦ z i) (MvPowerSeries.analyticAt_apply i _) := by
  refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
  · rw [polyClassHom_apply, MvPolynomial.eval₂Hom_C]
    exact D.classOf_congr _ (Eventually.of_forall fun z ↦ by simp)
  · rw [polyClassHom_apply, MvPolynomial.eval₂Hom_X']
    exact D.classOf_congr _ (Eventually.of_forall fun z ↦ by simp)

/-- The Taylor polynomial of order `< m` at `c` of a function analytic at `c`. -/
def taylorPoly (G : (Fin n → 𝕜) → 𝕜) (c : Fin n → 𝕜) (m : ℕ) : MvPolynomial (Fin n) 𝕜 :=
  open Classical in
  if hG : AnalyticAt 𝕜 G c then
    translate (-c) (MvPowerSeries.truncTotal m ((convergentStalkEquiv c).symm (germOf G hG)).1)
  else 0

/-- An analytic germ agrees with its Taylor polynomial to order `m`. -/
lemma germOf_sub_taylorPoly_mem {G : (Fin n → 𝕜) → 𝕜} {c : Fin n → 𝕜} (hG : AnalyticAt 𝕜 G c)
    (m : ℕ) : germOf G hG - polyGermHom c (taylorPoly G c m) ∈
      maximalIdeal ((analyticPresheaf 𝕜 (Fin n → 𝕜)).stalk c) ^ m := by
  set F := (convergentStalkEquiv c).symm (germOf G hG)
  have hF : convergentStalkEquiv c F = germOf G hG := RingEquiv.apply_symm_apply _ _
  have h₁ : polyGermHom c (taylorPoly G c m) = convergentStalkEquiv c
      (MvPowerSeries.polynomialToConvergent (MvPowerSeries.truncTotal m F.1)) := by
    simp only [taylorPoly, hG, ↓reduceDIte]
    change convergentStalkEquiv c (MvPowerSeries.polynomialToConvergent
      (translate c (translate (-c) _))) = _
    rw [translate_translate_neg]
  rw [h₁, ← hF, ← map_sub, ← map_maximalIdeal_convergentStalkEquiv, ← Ideal.map_pow]
  refine Ideal.mem_map_of_mem _ (MvPowerSeries.mem_maximalIdeal_pow_convergent_iff.mpr ?_)
  have h₂ := MvPowerSeries.le_order_truncTotal_sub F.1 (le_refl m)
  rw [← MvPowerSeries.order_neg, neg_sub] at h₂
  change (m : ℕ∞) ≤ (F.1 - (MvPowerSeries.polynomialToConvergent _).1).order
  rwa [MvPowerSeries.coe_polynomialToConvergent]

variable {D' : LocalModelData 𝕜 E'} {D : LocalModelData 𝕜 (Fin n → 𝕜)}
  {f : D'.toLocallyRingedSpace ⟶ D.toLocallyRingedSpace}

/-- The pullbacks of the coordinates at a point. -/
def coordPullback (f : D'.toLocallyRingedSpace ⟶ D.toLocallyRingedSpace) (y : D'.zeroSet)
    (i : Fin n) : D'.Fiber y :=
  (f.c.app (op ⊤) (D.coord i)).1 ⟨y, trivial⟩

lemma fiberMapOf_polyClassHom (hf : IsKLinear f) (y : D'.zeroSet) (p : MvPolynomial (Fin n) 𝕜) :
    fiberMapOf f y (D.polyClassHom (f.base y) p) =
      MvPolynomial.eval₂ (D'.constFiber y) (coordPullback f y) p := by
  have : (fiberMapOf f y).comp (D.polyClassHom (f.base y)) =
      MvPolynomial.eval₂Hom (D'.constFiber y) (coordPullback f y) := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · rw [RingHom.comp_apply, polyClassHom_eq_eval₂Hom, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_C, fiberMapOf_constFiber hf]
    · rw [RingHom.comp_apply, polyClassHom_eq_eval₂Hom, MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_X', coordPullback, c_app_apply f ⊤ _ y trivial]
      rfl
  exact congr($this p)

/-- The image under `f^*` of the class of `G` agrees, to order `m`, with the Taylor polynomial of
`G` at `f(y)` evaluated at the pullbacks of the coordinates. -/
lemma fiberMapOf_classOf_sub_eval₂_mem (hf : IsKLinear f) (y : D'.zeroSet)
    {G : (Fin n → 𝕜) → 𝕜} (hG : AnalyticAt 𝕜 G ((f.base y : D.zeroSet) : Fin n → 𝕜)) (m : ℕ) :
    fiberMapOf f y (D.classOf (f.base y) G hG) - MvPolynomial.eval₂ (D'.constFiber y)
      (coordPullback f y) (taylorPoly G ((f.base y : D.zeroSet) : Fin n → 𝕜) m) ∈
      maximalIdeal (D'.Fiber y) ^ m := by
  rw [← fiberMapOf_polyClassHom hf, ← map_sub]
  refine Ideal.mem_comap.mp (pow_le_comap_fiberMapOf (f := f) y m ?_)
  rw [polyClassHom, RingHom.comp_apply, classOf, ← map_sub]
  have h := germOf_sub_taylorPoly_mem hG m
  have h₂ := Ideal.mem_map_of_mem (Ideal.Quotient.mk (D.ideal _ (D.mem_U (f.base y)))) h
  rwa [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective _
    Ideal.Quotient.mk_surjective] at h₂

/-- The value of `f^* t` at `y` agrees, to order `m`, with the Taylor polynomial of `t` at `f(y)`
evaluated at the pullbacks of the coordinates. -/
lemma c_app_sub_eval₂_mem (hf : IsKLinear f) {W : Opens (TopCat.of D.zeroSet)}
    (t : D.presheaf.obj (op W)) {V : Opens (TopCat.of D.zeroSet)} {G : (Fin n → 𝕜) → 𝕜}
    (hG : ∀ q ∈ V, AnalyticAt 𝕜 G ((q : D.zeroSet) : Fin n → 𝕜))
    (htG : ∀ (q : D.zeroSet) (hqW : q ∈ W) (hqV : q ∈ V), t.1 ⟨q, hqW⟩ = D.classOf q G (hG q hqV))
    (y : D'.zeroSet) (hy : f.base y ∈ W) (hyV : f.base y ∈ V) (m : ℕ) :
    (f.c.app (op W) t).1 ⟨y, hy⟩ - MvPolynomial.eval₂ (D'.constFiber y) (coordPullback f y)
      (taylorPoly G ((f.base y : D.zeroSet) : Fin n → 𝕜) m) ∈ maximalIdeal (D'.Fiber y) ^ m := by
  rw [c_app_apply f W t y hy, htG _ hy hyV]
  exact fiberMapOf_classOf_sub_eval₂_mem hf y _ m

omit [CompleteSpace 𝕜] in
/-- The class of `G ∘ Ψ` agrees, to order `m`, with the Taylor polynomial of `G` at `Ψ(y)`
evaluated at the classes of the components of `Ψ`. -/
lemma classOf_comp_sub_eval₂_mem [CompleteSpace 𝕜] (D' : LocalModelData 𝕜 E') (y : D'.zeroSet)
    {Ψ : E' → Fin n → 𝕜} (hΨ : AnalyticAt 𝕜 Ψ (y : E')) {G : (Fin n → 𝕜) → 𝕜}
    (hG : AnalyticAt 𝕜 G (Ψ y)) (m : ℕ) :
    D'.classOf y (fun z ↦ G (Ψ z)) (hG.comp hΨ) - MvPolynomial.eval₂ (D'.constFiber y)
      (fun i ↦ D'.classOf y (fun z ↦ Ψ z i) (analyticAt_apply_comp hΨ i)) (taylorPoly G (Ψ y) m) ∈
      maximalIdeal (D'.Fiber y) ^ m := by
  rw [← D'.classOf_eval_comp hΨ]
  set φ := (Ideal.Quotient.mk (D'.ideal y (D'.mem_U y))).comp (stalkPullback Ψ hΨ)
  have hφ : maximalIdeal ((analyticPresheaf 𝕜 (Fin n → 𝕜)).stalk (Ψ y)) ≤
      (maximalIdeal (D'.Fiber y)).comap φ := fun a ha ↦ by
    rw [Ideal.mem_comap, mem_maximalIdeal_fiber_iff]
    change evalStalk _ (stalkPullback Ψ hΨ a) = 0
    rw [evalStalk_stalkPullback]
    exact (mem_maximalIdeal_stalk_iff a).mp ha
  have h := ((Ideal.pow_right_mono hφ m).trans (Ideal.le_comap_pow φ m))
    (germOf_sub_taylorPoly_mem hG m)
  rw [Ideal.mem_comap, map_sub] at h
  simp only [φ, RingHom.comp_apply, polyGermHom_apply, stalkPullback_germOf] at h
  exact h

/-- The point `f(y)` has coordinates the values of the pullbacks of the coordinates. -/
lemma base_apply_eq (hf : IsKLinear f) (y : D'.zeroSet) (i : Fin n) :
    ((f.base y : D.zeroSet) : Fin n → 𝕜) i = D'.evalFiber y (coordPullback f y i) := by
  rw [coordPullback, c_app_apply f ⊤ _ y trivial, evalFiber_fiberMapOf hf]
  exact (D.evalFiber_classOf (f.base y) (fun z ↦ z i) _).symm

end Coordinates

/-! ### Uniqueness -/

section Uniqueness

variable {n n' : ℕ}

instance isNoetherianRing_fiber (D : LocalModelData 𝕜 (Fin n → 𝕜)) (x : D.zeroSet) :
    IsNoetherianRing (D.Fiber x) := by
  have : IsNoetherianRing ((analyticPresheaf 𝕜 (Fin n → 𝕜)).stalk (x : Fin n → 𝕜)) :=
    isNoetherianRing_of_ringEquiv _ (convergentStalkEquiv (x : Fin n → 𝕜))
  exact Ideal.Quotient.isNoetherianRing _

/-- **Morphisms into a local model are determined by the pullbacks of the coordinates**: two
`𝕜`-linear morphisms of local models `f, g : Z(D') → Z(D) ⊆ 𝕜ⁿ` with `f^*(zᵢ) = g^*(zᵢ)` are
equal. -/
theorem eq_of_coordPullback {D' : LocalModelData 𝕜 (Fin n' → 𝕜)}
    {D : LocalModelData 𝕜 (Fin n → 𝕜)} {f g : D'.toLocallyRingedSpace ⟶ D.toLocallyRingedSpace}
    (hf : IsKLinear f) (hg : IsKLinear g) (h : ∀ y i, coordPullback f y i = coordPullback g y i) :
    f = g := by
  have hpt : ∀ y, f.base y = g.base y := fun y ↦
    Subtype.ext (funext fun i ↦ by rw [base_apply_eq hf, base_apply_eq hg, h])
  refine hom_ext hpt fun W t y hfW hgW ↦ ?_
  obtain ⟨V, hyV, G, hG, htG⟩ := exists_classOf_eq t ⟨f.base y, hfW⟩
  have hyV' : g.base y ∈ V := hpt y ▸ hyV
  have hc : ((g.base y : D.zeroSet) : Fin n → 𝕜) = f.base y := congrArg Subtype.val (hpt y).symm
  have hcoord : coordPullback f y = coordPullback g y := funext (h y)
  have hmem : ∀ m, (f.c.app (op W) t).1 ⟨y, hfW⟩ - (g.c.app (op W) t).1 ⟨y, hgW⟩ ∈
      maximalIdeal (D'.Fiber y) ^ m := fun m ↦ by
    have h₁ := c_app_sub_eval₂_mem hf t hG htG y hfW hyV m
    have h₂ := c_app_sub_eval₂_mem hg t hG htG y hgW hyV' m
    rw [hc, ← hcoord] at h₂
    simpa using Ideal.sub_mem _ h₁ h₂
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (D'.Fiber y))
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  rw [← sub_eq_zero]
  have hm := (Submodule.mem_iInf _).mpr hmem
  rw [hK] at hm
  exact hm

/-- A `𝕜`-linear morphism `f` of local models acts on classes by substitution of any lift `Ψ` of
the pullbacks `f^*(zᵢ)` of the coordinates: `f^*[G] = [G ∘ Ψ]`. -/
theorem fiberMapOf_classOf_eq {D' : LocalModelData 𝕜 (Fin n' → 𝕜)}
    {D : LocalModelData 𝕜 (Fin n → 𝕜)} {f : D'.toLocallyRingedSpace ⟶ D.toLocallyRingedSpace}
    (hf : IsKLinear f) (y : D'.zeroSet) {Ψ : (Fin n' → 𝕜) → Fin n → 𝕜}
    (hΨ : AnalyticAt 𝕜 Ψ (y : Fin n' → 𝕜))
    (hΨc : ∀ i, D'.classOf y (fun z ↦ Ψ z i) (analyticAt_apply_comp hΨ i) = coordPullback f y i)
    {G : (Fin n → 𝕜) → 𝕜} (hG : AnalyticAt 𝕜 G ((f.base y : D.zeroSet) : Fin n → 𝕜))
    (hG' : AnalyticAt 𝕜 G (Ψ y)) :
    fiberMapOf f y (D.classOf (f.base y) G hG) =
      D'.classOf y (fun z ↦ G (Ψ z)) (hG'.comp hΨ) := by
  have hpt : Ψ y = f.base y := funext fun i ↦ by
    rw [base_apply_eq hf, ← hΨc, evalFiber_classOf]
  have hmem : ∀ m, fiberMapOf f y (D.classOf (f.base y) G hG) -
      D'.classOf y (fun z ↦ G (Ψ z)) (hG'.comp hΨ) ∈ maximalIdeal (D'.Fiber y) ^ m := fun m ↦ by
    have h₁ := fiberMapOf_classOf_sub_eval₂_mem hf y hG m
    have h₂ := classOf_comp_sub_eval₂_mem D' y hΨ hG' m
    have e₁ : (fun i ↦ D'.classOf y (fun z ↦ Ψ z i) (analyticAt_apply_comp hΨ i)) =
        coordPullback f y := funext hΨc
    have e₂ : taylorPoly G (Ψ y) m = taylorPoly G ((f.base y : D.zeroSet) : Fin n → 𝕜) m := by
      rw [hpt]
    rw [e₁, e₂] at h₂
    simpa using Ideal.sub_mem _ h₁ h₂
  rw [← sub_eq_zero]
  have hm := (Submodule.mem_iInf _).mpr hmem
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top] at hm

end Uniqueness

/-! ### The universal property of local models in `𝕜ⁿ` -/

section UniversalProperty

variable {n n' : ℕ} {D' : LocalModelData 𝕜 (Fin n' → 𝕜)} {D : LocalModelData 𝕜 (Fin n → 𝕜)}

namespace SectionData

/-- The sections `f^*(zᵢ)` defined by a `𝕜`-linear morphism `f : Z(D') → Z(D)`. -/
def ofHom (f : D'.toLocallyRingedSpace ⟶ D.toLocallyRingedSpace) (hf : IsKLinear f) :
    SectionData D' D where
  sec i := f.c.app (op ⊤) (D.coord i)
  mapsTo y := by
    convert D.mem_U (f.base y) using 1
    funext i
    exact (base_apply_eq hf y i).symm
  classOf_f y j hj := by
    refine (fiberMapOf_classOf_eq hf y (D'.analyticAt_repVec y (coordPullback f y))
      (fun i ↦ D'.classOf_repVec y _ i) (D.analyticAt_f j _ (D.mem_U _)) hj).symm.trans ?_
    rw [D.classOf_f, map_zero]

@[simp] lemma ofHom_sec (f : D'.toLocallyRingedSpace ⟶ D.toLocallyRingedSpace)
    (hf : IsKLinear f) (i : Fin n) : (ofHom f hf).sec i = f.c.app (op ⊤) (D.coord i) := rfl

variable (S : SectionData D' D)

lemma coordPullback_toHom (y : D'.zeroSet) (i : Fin n) :
    coordPullback S.toHom y i = (S.sec i).1 ⟨y, trivial⟩ := by
  change S.fiberMap y (D.classOf (S.pointMap y) (fun z ↦ z i) _) = _
  rw [SectionData.fiberMap_classOf]
  exact D'.classOf_repVec y _ i

lemma isKLinear_toHom : IsKLinear S.toHom := fun c ↦ by
  apply Subtype.ext
  funext y
  exact S.fiberMap_constFiber y.1 c

theorem toHom_ofHom (f : D'.toLocallyRingedSpace ⟶ D.toLocallyRingedSpace) (hf : IsKLinear f) :
    (ofHom f hf).toHom = f :=
  eq_of_coordPullback (isKLinear_toHom _) hf fun y i ↦ coordPullback_toHom _ y i

theorem ofHom_toHom : ofHom S.toHom S.isKLinear_toHom = S := by
  apply SectionData.ext
  funext i
  apply Subtype.ext
  funext y
  exact S.coordPullback_toHom y.1 i

end SectionData

variable (D' D) in
/-- **Universal property of local models in `𝕜ⁿ`**: `𝕜`-linear morphisms `Z(D') → Z(D)` of locally
ringed spaces correspond to `n`-tuples of global sections of `𝒪_{Z(D')}` satisfying the equations
of `D` (the pullbacks of the coordinates). -/
def homEquiv :
    {f : D'.toLocallyRingedSpace ⟶ D.toLocallyRingedSpace // IsKLinear f} ≃ SectionData D' D where
  toFun f := SectionData.ofHom f.1 f.2
  invFun S := ⟨S.toHom, S.isKLinear_toHom⟩
  left_inv f := Subtype.ext (SectionData.toHom_ofHom f.1 f.2)
  right_inv S := SectionData.ofHom_toHom S

end UniversalProperty

/-! ### Morphisms into the analytification of an affine scheme -/

section Affine

variable {n k n' : ℕ} {g : Fin k → MvPolynomial (Fin n) 𝕜} {D' : LocalModelData 𝕜 (Fin n' → 𝕜)}

namespace SectionData

/-- Sections satisfying the polynomial equations `g` define a morphism into `Z(g)`. -/
def ofPoly (s : Fin n → D'.presheaf.obj (op ⊤))
    (hs : ∀ j, MvPolynomial.eval₂Hom (D'.constSectionHom ⊤) s (g j) = 0) :
    SectionData D' (polynomialModel g) where
  sec := s
  mapsTo _ := Set.mem_univ _
  classOf_f y j hj := by
    have h := D'.classOf_eval_comp (D'.analyticAt_repVec y (fun i ↦ (s i).1 ⟨y, trivial⟩)) (g j)
    have h₂ : MvPolynomial.eval₂ (D'.constFiber y) (fun i ↦ (s i).1 ⟨y, trivial⟩) (g j) = 0 := by
      rw [← D'.eval₂Hom_constSectionHom_apply (W := ⊤) s (g j) ⟨y, trivial⟩, hs j]
      rfl
    refine h.trans (Eq.trans ?_ h₂)
    congr 1
    funext i
    exact D'.classOf_repVec y _ i

lemma eval₂Hom_sec_eq_zero (S : SectionData D' (polynomialModel g)) (j : Fin k) :
    MvPolynomial.eval₂Hom (D'.constSectionHom ⊤) S.sec (g j) = 0 := by
  apply Subtype.ext
  funext y
  rw [eval₂Hom_constSectionHom_apply]
  have h := D'.classOf_eval_comp (S.analyticAt_lift y.1) (g j)
  have h₂ := S.classOf_f y.1 j (S.analyticAt_f y.1 j)
  calc MvPolynomial.eval₂ (D'.constFiber y.1) (fun i ↦ (S.sec i).1 y) (g j)
      = MvPolynomial.eval₂ (D'.constFiber y.1) (fun i ↦ D'.classOf y.1 (fun z ↦ S.lift y.1 z i)
          (analyticAt_apply_comp (S.analyticAt_lift y.1) i)) (g j) := by
        congr 1
        funext i
        exact (D'.classOf_repVec y.1 (S.vals y.1) i).symm
    _ = _ := h.symm
    _ = 0 := h₂

end SectionData

namespace SectionData

/-- The ring homomorphism `A = 𝕜[z]/(g) → Γ(Y, 𝒪_Y)`, `zᵢ ↦ sᵢ`. -/
def toRingHom (S : SectionData D' (polynomialModel g)) :
    PresentedAlgebra g →+* D'.presheaf.obj (op ⊤) :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom (D'.constSectionHom ⊤) S.sec) fun a ha ↦ by
    have : Ideal.span (Set.range g) ≤
        RingHom.ker (MvPolynomial.eval₂Hom (D'.constSectionHom ⊤) S.sec) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact S.eval₂Hom_sec_eq_zero j
    exact this ha

lemma toRingHom_mk (S : SectionData D' (polynomialModel g)) (p : MvPolynomial (Fin n) 𝕜) :
    S.toRingHom (Ideal.Quotient.mk _ p) = MvPolynomial.eval₂Hom (D'.constSectionHom ⊤) S.sec p :=
  Ideal.Quotient.lift_mk _ _ _

lemma toRingHom_comp_algebraMap (S : SectionData D' (polynomialModel g)) :
    S.toRingHom.comp (algebraMap 𝕜 _) = D'.constSectionHom ⊤ := RingHom.ext fun c ↦ by
  change S.toRingHom (Ideal.Quotient.mk _ (MvPolynomial.C c)) = _
  rw [toRingHom_mk, MvPolynomial.eval₂Hom_C]

/-- The sections `φ(zᵢ)` defined by a `𝕜`-linear ring homomorphism `φ : A → Γ(Y, 𝒪_Y)`. -/
def ofRingHom (φ : PresentedAlgebra g →+* D'.presheaf.obj (op ⊤))
    (hφ : φ.comp (algebraMap 𝕜 _) = D'.constSectionHom ⊤) :
    SectionData D' (polynomialModel g) :=
  ofPoly (fun i ↦ φ (Ideal.Quotient.mk _ (MvPolynomial.X i))) fun j ↦ by
    have : MvPolynomial.eval₂Hom (D'.constSectionHom ⊤)
        (fun i ↦ φ (Ideal.Quotient.mk _ (MvPolynomial.X i))) = φ.comp (Ideal.Quotient.mk _) :=
      MvPolynomial.ringHom_ext (fun c ↦ by
          rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
          exact (RingHom.congr_fun hφ c).symm)
        (fun i ↦ by rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply])
    have h0 : Ideal.Quotient.mk (Ideal.span (Set.range g)) (g j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
    rw [this, RingHom.comp_apply, h0, map_zero]

end SectionData

variable (g D') in
/-- Sections satisfying the equations `g` are the same as ring homomorphisms `A = 𝕜[z]/(g) → Γ`
which are `𝕜`-linear. -/
def sectionDataEquiv :
    SectionData D' (polynomialModel g) ≃
      {φ : PresentedAlgebra g →+* D'.presheaf.obj (op ⊤) //
        φ.comp (algebraMap 𝕜 _) = D'.constSectionHom ⊤} where
  toFun S := ⟨S.toRingHom, S.toRingHom_comp_algebraMap⟩
  invFun φ := SectionData.ofRingHom φ.1 φ.2
  left_inv S := by
    apply SectionData.ext
    funext i
    change S.toRingHom (Ideal.Quotient.mk _ (MvPolynomial.X i)) = _
    rw [SectionData.toRingHom_mk, MvPolynomial.eval₂Hom_X']
  right_inv φ := by
    apply Subtype.ext
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_))
    · rw [RingHom.comp_apply, RingHom.comp_apply, SectionData.toRingHom_mk,
        MvPolynomial.eval₂Hom_C]
      exact (RingHom.congr_fun φ.2 c).symm
    · rw [RingHom.comp_apply, RingHom.comp_apply, SectionData.toRingHom_mk,
        MvPolynomial.eval₂Hom_X']
      rfl

variable (g D') in
/-- **Universal property of `Spec(A)^an` for local models**: for `A = 𝕜[z]/(g)` and a local model
`Y ⊆ 𝕜^{n'}`, `𝕜`-linear morphisms `Y → Spec(A)^an` of locally ringed spaces correspond to
`𝕜`-algebra homomorphisms `A → Γ(Y, 𝒪_Y)` (`f ↦ f^* ∘ (A → Γ(Spec(A)^an, 𝒪))`,
`homEquivRingHom_apply_coe`). -/
def homEquivRingHom :
    {f : D'.toLocallyRingedSpace ⟶ analytification g // IsKLinear f} ≃
      {φ : PresentedAlgebra g →+* D'.presheaf.obj (op ⊤) //
        φ.comp (algebraMap 𝕜 _) = D'.constSectionHom ⊤} :=
  (homEquiv D' (polynomialModel g)).trans (sectionDataEquiv g D')

lemma polynomialSection_X (i : Fin n) :
    polynomialSection (g := g) (MvPolynomial.X i) = (polynomialModel g).coord i := by
  apply Subtype.ext
  funext y
  exact (polynomialModel g).classOf_congr _ (Eventually.of_forall fun z ↦ by simp)

lemma polynomialSection_C (c : 𝕜) :
    polynomialSection (g := g) (MvPolynomial.C c) = (polynomialModel g).constSection ⊤ c := by
  apply Subtype.ext
  funext y
  exact (polynomialModel g).classOf_congr _ (Eventually.of_forall fun z ↦ by simp)

lemma homEquivRingHom_apply_coe (f : D'.toLocallyRingedSpace ⟶ analytification g)
    (hf : IsKLinear f) :
    (homEquivRingHom g D' ⟨f, hf⟩).1 =
      (LocallyRingedSpace.Γ.map f.op).hom.comp (algebraToSections g) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_))
  · change SectionData.toRingHom _ (Ideal.Quotient.mk _ _) =
      f.c.app (op ⊤) (polynomialSection (MvPolynomial.C c))
    rw [SectionData.toRingHom_mk, MvPolynomial.eval₂Hom_C, polynomialSection_C, hf c]
    rfl
  · change SectionData.toRingHom _ (Ideal.Quotient.mk _ _) =
      f.c.app (op ⊤) (polynomialSection (MvPolynomial.X i))
    rw [SectionData.toRingHom_mk, MvPolynomial.eval₂Hom_X', polynomialSection_X]
    rfl

/-- The composite `Y → Spec(A)^an → Spec A`, in terms of the `Γ ⊣ Spec` adjunction. -/
lemma comp_toSpec {Y : LocallyRingedSpace} (f : Y ⟶ analytification g) :
    f ≫ toSpec g = Y.toΓSpec ≫ Spec.locallyRingedSpaceMap
      (CommRingCat.ofHom (algebraToSections g) ≫ LocallyRingedSpace.Γ.map f.op) := by
  have nat : f ≫ (analytification g).toΓSpec =
      Y.toΓSpec ≫ Spec.locallyRingedSpaceMap (LocallyRingedSpace.Γ.map f.op) :=
    identityToΓSpec.naturality f
  rw [toSpec, Spec.locallyRingedSpaceMap_comp, ← Category.assoc, nat, Category.assoc]
  rfl

omit [CompleteSpace 𝕜] in
lemma toΓSpec_comp_injective {Y : LocallyRingedSpace} {R : CommRingCat}
    {φ ψ : R ⟶ LocallyRingedSpace.Γ.obj (op Y)}
    (h : Y.toΓSpec ≫ Spec.locallyRingedSpaceMap φ = Y.toΓSpec ≫ Spec.locallyRingedSpaceMap ψ) :
    φ = ψ := by
  have := (ΓSpec.locallyRingedSpaceAdjunction.homEquiv Y (op R)).injective (a₁ := φ.op)
    (a₂ := ψ.op) (by
      rw [ΓSpec.locallyRingedSpaceAdjunction_homEquiv_apply,
        ΓSpec.locallyRingedSpaceAdjunction_homEquiv_apply]
      exact h)
  exact Quiver.Hom.op_inj this

/-- **XII.1.1, universal property of `X^an` (affine `X`, local models)**: let `Y ⊆ 𝕜^{n'}` be a
local model and `A = 𝕜[z]/(g)`. For every `𝕜`-algebra homomorphism `φ : A → Γ(Y, 𝒪_Y)`, i.e. every
`𝕜`-morphism of locally ringed spaces `h = Spec(φ) ∘ (Y → Spec Γ(Y)) : Y → Spec A` (by the
`Γ ⊣ Spec` adjunction every morphism `Y → Spec A` is of this form), there is a unique `𝕜`-linear
morphism `f : Y → Spec(A)^an` with `φ_X ∘ f = h`. -/
theorem existsUnique_comp_toSpec (φ : PresentedAlgebra g →+* D'.presheaf.obj (op ⊤))
    (hφ : φ.comp (algebraMap 𝕜 _) = D'.constSectionHom ⊤) :
    ∃! f : D'.toLocallyRingedSpace ⟶ analytification g, IsKLinear f ∧
      f ≫ toSpec g = D'.toLocallyRingedSpace.toΓSpec ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom φ) := by
  have key : ∀ f (hf : IsKLinear f), f ≫ toSpec g = D'.toLocallyRingedSpace.toΓSpec ≫
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom (homEquivRingHom g D' ⟨f, hf⟩).1) :=
    fun f hf ↦ by
      rw [comp_toSpec, homEquivRingHom_apply_coe]
      rfl
  set F := (homEquivRingHom g D').symm ⟨φ, hφ⟩ with hF
  refine ⟨F.1, ⟨F.2, ?_⟩, ?_⟩
  · rw [key _ F.2]
    simp only [Subtype.coe_eta, hF, Equiv.apply_symm_apply]
  · rintro f ⟨hf, hfφ⟩
    have h₁ := toΓSpec_comp_injective ((key f hf).symm.trans hfφ)
    have h₂ : homEquivRingHom g D' ⟨f, hf⟩ = ⟨φ, hφ⟩ :=
      Subtype.ext (congrArg CommRingCat.Hom.hom h₁)
    rw [hF, ← h₂, Equiv.symm_apply_apply]

end Affine

end LocalModelData

end AnalyticGeometry
