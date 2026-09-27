/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.FormalPullback

/-!
# Descent of algebraizability along Stein-type proper morphisms

Let `A` be noetherian and `I`-adically complete, `f : X ⟶ Spec A` proper and `p : X' ⟶ X` proper
with `Γ(X, U) ≅ Γ(X', p⁻¹ U)` on affine opens `U`. This file proves
`formalAlgebraizable_of_stein`: if étale coverings of the formal completion of `X'` are
algebraizable (`FormalAlgebraizable I (p ≫ f)`), so are those of `X`. This is the key step of
the Chow-lemma proof of Grothendieck's existence theorem (EGA III 5.1.4, 5.3.1), restricted
to the adic systems `(Yₙ ⟶ X)_* 𝒪` of formal étale coverings.

Given `(Yₙ ⟶ Xₙ)` and a coherent algebraization `F'` of `(Yₙ ×_{Xₙ} X'ₙ ⟶ X')_* 𝒪`, the module
`p_* F'` is compared with `(Yₙ ⟶ X)_* 𝒪` through the inverse system
`Eₙ = (Yₙ ×_{Xₙ} X'ₙ ⟶ X)_* 𝒪` (`steinE`), with maps `u_n : p_* F' ⟶ Eₙ` (`steinU`) and
`w_n : (Yₙ ⟶ X)_* 𝒪 ⟶ Eₙ` (`steinW`). The pro-isomorphism criterion
`exists_iso_quotientIdealPow_of_proIso` applies:

* `stein_proIsoKer`: kernels, by the relative Artin–Rees lemma for `F'`
  (`exists_relative_ker_le`) and, for `w_n`, by the Artin–Rees lemma for the thickenings along
  `p` (`exists_thickeningMap_ker_le`) plus flat base change along `Yₙ ⟶ Xₙ`
  (`isPushout_stein`, `mem_map_ker_of_isPushout`);
* `stein_lift_u`, `stein_lift_w`: images, by `exists_relative_lift` and
  `exists_thickeningMap_lift` plus `range_subset_of_isPushout`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

open Scheme.Modules
open Scheme (FiniteEtale FormalFiniteEtale)

section Diagrams

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- The transition maps `Xₙ ⟶ Xₘ` of the thickenings commute with the closed immersions into `X`. -/
lemma thickeningDiagram_map_ι_of_le {n m : ℕ} (h : n ≤ m) :
    (thickeningDiagram I f).map (homOfLE h) ≫ thickening.ι f I m = thickening.ι f I n := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [show homOfLE (le_refl n) = 𝟙 n from rfl, CategoryTheory.Functor.map_id, Category.id_comp]
  | succ m hm ih =>
    rw [show homOfLE (hm.trans m.le_succ) = homOfLE hm ≫ homOfLE m.le_succ from rfl,
      Functor.map_comp, Category.assoc, ← thickeningDiagram_map_ι, ih]

variable (𝒴 : Scheme.FormalFiniteEtale (thickeningDiagram I f))

/-- The composite transition `Yₙ ⟶ Yₘ` of an étale covering of the formal completion. -/
def formalTrans {n m : ℕ} (h : n ≤ m) : (𝒴.obj n).left ⟶ (𝒴.obj m).left :=
  𝒴.diagram.map (homOfLE h)

/-- `Yₙ ⟶ Yₙ` is the identity. -/
lemma formalTrans_self (n : ℕ) : formalTrans I f 𝒴 (le_refl n) = 𝟙 _ :=
  𝒴.diagram.map_id n

/-- The composite transitions `Yₙ ⟶ Yₘ` compose. -/
lemma formalTrans_comp {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) :
    formalTrans I f 𝒴 h₁ ≫ formalTrans I f 𝒴 h₂ = formalTrans I f 𝒴 (h₁.trans h₂) :=
  (𝒴.diagram.map_comp (homOfLE h₁) (homOfLE h₂)).symm

/-- The composite transition `Yₙ ⟶ Yₙ₊₁` is the given transition. -/
lemma formalTrans_succ (n : ℕ) : formalTrans I f 𝒴 n.le_succ = 𝒴.transition n :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The composite transitions `Yₙ ⟶ Yₘ` lie over the transitions `Xₙ ⟶ Xₘ`. -/
lemma formalTrans_formalQ {n m : ℕ} (h : n ≤ m) :
    formalTrans I f 𝒴 h ≫ formalQ I f 𝒴 m =
      formalQ I f 𝒴 n ≫ (thickeningDiagram I f).map (homOfLE h) :=
  𝒴.toBase.naturality (homOfLE h)

/-- The composite transitions `Yₙ ⟶ Yₘ` are compatible with the structure maps to `X`. -/
lemma formalTrans_formalStructure {n m : ℕ} (h : n ≤ m) :
    formalTrans I f 𝒴 h ≫ formalStructure I f 𝒴 m = formalStructure I f 𝒴 n := by
  rw [formalStructure, formalStructure, ← Category.assoc, formalTrans_formalQ, Category.assoc,
    thickeningDiagram_map_ι_of_le]

/-- The composite transitions of the adic system `(Yₙ ⟶ X)_* 𝒪` are induced by `Yₙ ⟶ Yₘ`. -/
lemma formalAdicSystem_trans_eq {n m : ℕ} (h : n ≤ m) :
    (formalAdicSystem I f 𝒴).trans h =
      pushforwardUnitMap (formalTrans I f 𝒴 h) (formalTrans_formalStructure I f 𝒴 h) := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [AdicSystem.trans_self]
    exact (pushforwardUnitMap_id (g := formalStructure I f 𝒴 n)).symm.trans
      (pushforwardUnitMap_congr (formalTrans_self I f 𝒴 n).symm _ _)
  | succ m hm ih =>
    rw [← AdicSystem.trans_trans _ hm m.le_succ, AdicSystem.trans_succ, ih]
    refine (pushforwardUnitMap_comp (formalTrans I f 𝒴 hm) (formalTrans_formalStructure I f 𝒴 hm)
      (𝒴.transition m) (transition_formalStructure I f 𝒴 m)).symm.trans ?_
    exact pushforwardUnitMap_congr (by rw [← formalTrans_succ, formalTrans_comp]) _ _

end Diagrams

section UnitLevel

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {Z : Scheme.{u}}
  (g : Z ⟶ Spec A)

/-- The reduction map `𝒪_Z ⟶ (Z_n ⟶ Z)_* 𝒪`, with `𝒪_Z` presented as `(𝟙 Z)_* 𝒪_Z`. -/
abbrev unitReduction (n : ℕ) : pushforwardUnit (𝟙 Z) ⟶ pushforwardUnit (thickening.ι g I n) :=
  pushforwardUnitMap (thickening.ι g I n) (Category.comp_id _)

omit [IsNoetherianRing A] in
/-- `Z ×_Z Zₙ ≅ Zₙ` identifies the first projection with `Zₙ ⟶ Z`. -/
lemma pullback_snd_inv_fst (n : ℕ) :
    inv (pullback.snd (𝟙 Z) (thickening.ι g I n)) ≫ pullback.fst (𝟙 Z) (thickening.ι g I n) =
      thickening.ι g I n := by
  rw [IsIso.inv_comp_eq, ← pullback.condition, Category.comp_id]

/-- `𝒪_Z / I^{n+1} 𝒪_Z ≅ (Z_n ⟶ Z)_* 𝒪`. -/
def unitThickIso (n : ℕ) :
    (pushforwardUnit (𝟙 Z)).quotientIdealPow g I n ≅ pushforwardUnit (thickening.ι g I n) :=
  reductionIso I g (𝟙 Z) n ≪≫
    pushforwardUnitIso (asIso (pullback.snd (𝟙 Z) (thickening.ι g I n))).symm
      (by rw [Iso.symm_hom, asIso_inv, Category.comp_id, pullback_snd_inv_fst])

/-- `unitThickIso` is compatible with the reduction maps from `𝒪_Z`. -/
lemma toQuotientIdealPow_unitThickIso (n : ℕ) :
    (pushforwardUnit (𝟙 Z)).toQuotientIdealPow g I n ≫ (unitThickIso I g n).hom =
      unitReduction I g n := by
  rw [unitThickIso, Iso.trans_hom, ← Category.assoc, toQuotientIdealPow_reductionIso_hom]
  exact (pushforwardUnitMap_comp (asIso (pullback.snd (𝟙 Z) (thickening.ι g I n))).symm.hom
    (by rw [Iso.symm_hom, asIso_inv, Category.comp_id, pullback_snd_inv_fst])
    (pullback.fst (𝟙 Z) (thickening.ι g I n)) rfl).symm.trans
    (pushforwardUnitMap_congr (by rw [Iso.symm_hom, asIso_inv, pullback_snd_inv_fst]) _ _)

/-- `unitThickIso` is compatible with the transition maps. -/
lemma quotMap_unitThickIso {n m : ℕ} (h : n ≤ m) :
    quotMap I g (pushforwardUnit (𝟙 Z)) h ≫ (unitThickIso I g n).hom =
      (unitThickIso I g m).hom ≫ pushforwardUnitMap ((thickeningDiagram I g).map (homOfLE h))
        (thickeningDiagram_map_ι_of_le I g h) := by
  rw [← cancel_epi ((pushforwardUnit (𝟙 Z)).toQuotientIdealPow g I m),
    toQuotientIdealPow_quotMap_assoc, toQuotientIdealPow_unitThickIso, ← Category.assoc,
    toQuotientIdealPow_unitThickIso, ← pushforwardUnitMap_comp]
  exact pushforwardUnitMap_congr (thickeningDiagram_map_ι_of_le I g h).symm _ _

end UnitLevel

section SteinUnit

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X X' : Scheme.{u}}
  (f : X ⟶ Spec A) (p : X' ⟶ X) [IsProper p] [IsLocallyNoetherian X] {U : X.Opens}
  (hU : IsAffineOpen U)

/-- Sections of `pushforwardUnitMap h` are given by `h.appLE`. -/
lemma pushforwardUnitMap_app_eq_appLE {Z Z' : Scheme.{u}} {g : Z ⟶ X'} {g' : Z' ⟶ X'}
    (h : Z ⟶ Z') (hg : h ≫ g' = g) (V : X'.Opens) (x : Γ(Z', g' ⁻¹ᵁ V)) :
    (pushforwardUnitMap h hg).app V x =
      h.appLE (g' ⁻¹ᵁ V) (g ⁻¹ᵁ V) (preimage_le_preimage_of_comp_eq h hg V) x := rfl

include hU in
/-- **Artin–Rees for `𝒪` along `p`** (kernel form): there is `c` such that a function on `p⁻¹ U`
vanishing on the thickening `X'_{n+c}` lies in `I^{n+1} Γ(X', p⁻¹ U)`. -/
theorem exists_unit_ker_le :
    ∃ c, ∀ n (x : Γ(pushforwardUnit (𝟙 X'), p ⁻¹ᵁ U)),
      (unitReduction I (p ≫ f) (n + c)).app (p ⁻¹ᵁ U) x = 0 →
        x ∈ (idealV f I U 1 ^ (n + 1) • ⊤ :
          Submodule Γ(X, U) Γ((pushforward p).obj (pushforwardUnit (𝟙 X')), U)) := by
  have := isCoherent_pushforwardUnit (𝟙 X')
  obtain ⟨c, hc⟩ := exists_relative_ker_le I f p hU (pushforwardUnit (𝟙 X'))
  refine ⟨c, fun n x hx ↦ hc n x ?_⟩
  have h1 : (unitThickIso I (p ≫ f) (n + c)).hom.app (p ⁻¹ᵁ U)
      (((pushforwardUnit (𝟙 X')).toQuotientIdealPow (p ≫ f) I (n + c)).app (p ⁻¹ᵁ U) x) = 0 := by
    rw [← Scheme.Modules.Hom.comp_app_apply, toQuotientIdealPow_unitThickIso]
    exact hx
  have h2 := congrArg ((unitThickIso I (p ≫ f) (n + c)).inv.app (p ⁻¹ᵁ U)) h1
  rwa [← Scheme.Modules.Hom.comp_app_apply, Iso.hom_inv_id, map_zero] at h2

include hU in
/-- **Artin–Rees for `𝒪` along `p`** (lifting form): there is `c` such that the restriction to
`X'_n` of a function on `X'_{n+c}` over `p⁻¹ U` lifts to `Γ(X', p⁻¹ U)`. -/
theorem exists_unit_lift :
    ∃ c, ∀ n (z : Γ(pushforwardUnit (thickening.ι (p ≫ f) I (n + c)), p ⁻¹ᵁ U)),
      ∃ x : Γ(pushforwardUnit (𝟙 X'), p ⁻¹ᵁ U),
        (unitReduction I (p ≫ f) n).app (p ⁻¹ᵁ U) x =
          (pushforwardUnitMap ((thickeningDiagram I (p ≫ f)).map (homOfLE (Nat.le_add_right n c)))
            (thickeningDiagram_map_ι_of_le I (p ≫ f) (Nat.le_add_right n c))).app (p ⁻¹ᵁ U) z := by
  have := isCoherent_pushforwardUnit (𝟙 X')
  obtain ⟨c, hc⟩ := exists_relative_lift I f p hU (pushforwardUnit (𝟙 X'))
  refine ⟨c, fun n z ↦ ?_⟩
  obtain ⟨b, hb⟩ := hc n ((unitThickIso I (p ≫ f) (n + c)).inv.app (p ⁻¹ᵁ U) z)
  refine ⟨b, ?_⟩
  have h1 := congrArg ((unitThickIso I (p ≫ f) n).hom.app (p ⁻¹ᵁ U)) hb
  rw [← Scheme.Modules.Hom.comp_app_apply, toQuotientIdealPow_unitThickIso,
    ← Scheme.Modules.Hom.comp_app_apply, quotMap_unitThickIso, Scheme.Modules.Hom.comp_app_apply,
    ← Scheme.Modules.Hom.comp_app_apply (unitThickIso I (p ≫ f) (n + c)).inv, Iso.inv_hom_id]
    at h1
  exact h1

end SteinUnit

section SteinRing

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X X' : Scheme.{u}}
  (f : X ⟶ Spec A) (p : X' ⟶ X) [IsProper p] [IsLocallyNoetherian X] {U : X.Opens}
  (hU : IsAffineOpen U) (hp : Function.Bijective (p.app U))

omit [IsNoetherianRing A] [IsProper p] [IsLocallyNoetherian X] in
/-- `X'ₙ ⟶ Xₙ` maps `p⁻¹ U ∩ X'ₙ` into `U ∩ Xₙ`. -/
lemma thickeningMap_preimage_le (m : ℕ) :
    (thickening.ι (p ≫ f) I m) ⁻¹ᵁ (p ⁻¹ᵁ U) ≤
      (thickeningMap I f p m) ⁻¹ᵁ ((thickening.ι f I m) ⁻¹ᵁ U) :=
  preimage_le_preimage_of_comp_eq (thickeningMap I f p m) (thickeningMap_ι I f p m) U

omit [IsNoetherianRing A] [IsProper p] [IsLocallyNoetherian X] in
/-- Restriction along `X'ₙ ⟶ Xₙ` of the image of `r ∈ Γ(X, U)` is the image of `p^* r`. -/
lemma thickeningMap_appLE_ι_app (m : ℕ) (r : Γ(X, U)) :
    (thickeningMap I f p m).appLE _ _ (thickeningMap_preimage_le I f p m)
        ((thickening.ι f I m).app U r) =
      (thickening.ι (p ≫ f) I m).app (p ⁻¹ᵁ U) (p.app U r) := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
    ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq (thickeningMap_ι I f p m)]

include hU hp in
/-- **Artin–Rees for the thickenings along `p`, ring form**: if `Γ(X, U) → Γ(X', p⁻¹ U)` is
bijective, there is `c` such that the kernel of `Γ(X_{n+c}, U) → Γ(X'_{n+c}, p⁻¹ U)` lies in
`I^{n+1}`. -/
theorem exists_thickeningMap_ker_le :
    ∃ c, ∀ n, RingHom.ker ((thickeningMap I f p (n + c)).appLE _ _
        (thickeningMap_preimage_le I f p (n + c))).hom ≤
      (idealV f I U 1 ^ (n + 1)).map ((thickening.ι f I (n + c)).app U).hom := by
  obtain ⟨c, hc⟩ := exists_unit_ker_le I f p hU
  refine ⟨c, fun n rb hrb ↦ ?_⟩
  obtain ⟨r, rfl⟩ := (thickening.ι f I (n + c)).app_surjective U hU rb
  rw [RingHom.mem_ker, thickeningMap_appLE_ι_app] at hrb
  have h1 := hc n (p.app U r) (by
    change (thickening.ι (p ≫ f) I (n + c)).appLE _ _ _ (p.app U r) = 0
    rw [← Scheme.Hom.app_eq_appLE]
    exact hrb)
  have h2 := mem_smul_top_of_linearMap _
    (appLinearMap ((Scheme.Modules.pushforwardComp (𝟙 X') p).hom.app (unitModule X')) U) h1
  have h3 := (mem_smul_top_pushforwardUnit_iff (g := 𝟙 X' ≫ p) _ _).mp h2
  have hp' : Function.Bijective (⇑((𝟙 X' ≫ p).app U).hom :
      Γ(X, U) → Γ(X', (𝟙 X' ≫ p) ⁻¹ᵁ U)) := hp
  have h5 : r ∈ ((idealV f I U 1 ^ (n + 1)).map ((𝟙 X' ≫ p).app U).hom).comap
      ((𝟙 X' ≫ p).app U).hom := h3
  rw [Ideal.comap_map_of_bijective _ hp'] at h5
  exact Ideal.mem_map_of_mem _ h5

include hU hp in
/-- **Artin–Rees for the thickenings along `p`, lifting form**: if `Γ(X, U) → Γ(X', p⁻¹ U)` is
bijective, there is `c` such that the image of `Γ(X'_{n+c}, p⁻¹ U) → Γ(X'_n, p⁻¹ U)` lies in the
image of `Γ(X_n, U)`. -/
theorem exists_thickeningMap_lift :
    ∃ c, ∀ n (t : Γ(thickening (p ≫ f) I (n + c),
        (thickening.ι (p ≫ f) I (n + c)) ⁻¹ᵁ (p ⁻¹ᵁ U))),
      ((thickeningDiagram I (p ≫ f)).map (homOfLE (Nat.le_add_right n c))).appLE _ _
          (preimage_le_preimage_of_comp_eq _
            (thickeningDiagram_map_ι_of_le I (p ≫ f) (Nat.le_add_right n c)) _) t ∈
        Set.range ((thickeningMap I f p n).appLE _ _ (thickeningMap_preimage_le I f p n)) := by
  obtain ⟨c, hc⟩ := exists_unit_lift I f p hU
  refine ⟨c, fun n t ↦ ?_⟩
  obtain ⟨x, hx⟩ := hc n t
  obtain ⟨r, hr⟩ := hp.2 x
  refine ⟨(thickening.ι f I n).app U r, ?_⟩
  rw [thickeningMap_appLE_ι_app]
  refine Eq.trans ?_ hx
  change _ = (thickening.ι (p ≫ f) I n).appLE _ _ _ x
  rw [← hr, Scheme.Hom.app_eq_appLE]
  rfl

end SteinRing

/-- `appLE` of a composite, on elements. -/
lemma appLE_comp_appLE_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (V : Y.Opens) (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (x : Γ(Z, U)) :
    f.appLE V W e₂ (g.appLE U V e₁ x) =
      (f ≫ g).appLE U W (e₂.trans (f.preimage_mono e₁)) x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- A commutative square of schemes gives a commutative square of `appLE` maps. -/
lemma appLE_square {W₁ W₂ Z₁ Z₂ : Scheme.{u}} {a : W₁ ⟶ W₂} {b : W₂ ⟶ Z₂} {c : W₁ ⟶ Z₁}
    {d : Z₁ ⟶ Z₂} (h : a ≫ b = c ≫ d) {U₂ : Z₂.Opens} {V₂ : W₂.Opens} {U₁ : Z₁.Opens}
    {V₁ : W₁.Opens} (e₁ : V₂ ≤ b ⁻¹ᵁ U₂) (e₂ : V₁ ≤ a ⁻¹ᵁ V₂) (e₃ : U₁ ≤ d ⁻¹ᵁ U₂)
    (e₄ : V₁ ≤ c ⁻¹ᵁ U₁) :
    b.appLE U₂ V₂ e₁ ≫ a.appLE V₂ V₁ e₂ = d.appLE U₂ U₁ e₃ ≫ c.appLE U₁ V₁ e₄ := by
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_eq_of_eq h _ _ _ _

/-- `appLE` of equal morphisms agree on elements. -/
lemma appLE_apply_congr {X Y : Scheme.{u}} {h h' : X ⟶ Y} (H : h = h') (U : Y.Opens)
    (V : X.Opens) (e : V ≤ h ⁻¹ᵁ U) (e' : V ≤ h' ⁻¹ᵁ U) (x : Γ(Y, U)) :
    h.appLE U V e x = h'.appLE U V e' x := by
  subst H
  rfl

/-- If `h = a ≫ b` and the image of `a.appLE` lies in the range of `φ`, so does that of
`h.appLE`. -/
lemma range_appLE_subset_of_eq_comp {X Y Z : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z} {h : X ⟶ Z}
    (H : h = a ≫ b) {U : Z.Opens} {V : Y.Opens} {W : X.Opens} (e₁ : V ≤ b ⁻¹ᵁ U)
    (e₂ : W ≤ a ⁻¹ᵁ V) (e : W ≤ h ⁻¹ᵁ U) {R : CommRingCat.{u}} (φ : R ⟶ Γ(X, W))
    (hc : ∀ t, a.appLE V W e₂ t ∈ Set.range φ) : Set.range (h.appLE U W e) ⊆ Set.range φ := by
  subst H
  rintro _ ⟨t, rfl⟩
  rw [← appLE_comp_appLE_apply a b U V W e₁ e₂ t]
  exact hc _

section SteinMaps

variable {A : CommRingCat.{u}} (I : Ideal A) {X X' : Scheme.{u}} (f : X ⟶ Spec A) (p : X' ⟶ X)
  (𝒴 : Scheme.FormalFiniteEtale (thickeningDiagram I f))

/-- The projection `Yₙ ×_{Xₙ} X'ₙ ⟶ Yₙ`, with its source written as the formal pullback. -/
abbrev pbFst (n : ℕ) : ((formalPullback I f p 𝒴).obj n).left ⟶ (𝒴.obj n).left :=
  pullback.fst (𝒴.obj n).hom (thickeningMap I f p n)

/-- The projection `Yₙ ×_{Xₙ} X'ₙ ⟶ X'ₙ`, with its source written as the formal pullback. -/
abbrev pbSnd (n : ℕ) : ((formalPullback I f p 𝒴).obj n).left ⟶ thickening (p ≫ f) I n :=
  pullback.snd (𝒴.obj n).hom (thickeningMap I f p n)

/-- The structure map `Yₙ ×_{Xₙ} X'ₙ ⟶ X'ₙ` of the formal pullback is `pbSnd`. -/
lemma formalQ_formalPullback (n : ℕ) :
    formalQ I (p ≫ f) (formalPullback I f p 𝒴) n =
      pbSnd I f p 𝒴 n := rfl

/-- The pullback square `Yₙ ×_{Xₙ} X'ₙ`. -/
lemma pbFst_condition (n : ℕ) :
    pbFst I f p 𝒴 n ≫ (𝒴.obj n).hom = pbSnd I f p 𝒴 n ≫ thickeningMap I f p n :=
  pullback.condition

/-- `Yₙ ×_{Xₙ} X'ₙ ⟶ Yₙ ⟶ X` equals `Yₙ ×_{Xₙ} X'ₙ ⟶ X' ⟶ X`. -/
lemma steinW_comp (n : ℕ) :
    pbFst I f p 𝒴 n ≫ formalStructure I f 𝒴 n =
      formalStructure I (p ≫ f) (formalPullback I f p 𝒴) n ≫ p := by
  rw [formalStructure, formalStructure, formalQ_formalPullback, ← Category.assoc,
    formalQ, pbFst_condition, Category.assoc, thickeningMap_ι, Category.assoc]

/-- The transitions of the formal pullback lie over `X`. -/
lemma steinE_transition_comp (n : ℕ) :
    (formalPullback I f p 𝒴).transition n ≫
        (formalStructure I (p ≫ f) (formalPullback I f p 𝒴) (n + 1) ≫ p) =
      formalStructure I (p ≫ f) (formalPullback I f p 𝒴) n ≫ p := by
  rw [← Category.assoc, transition_formalStructure]

/-- The inverse system `(Yₙ ×_{Xₙ} X'ₙ ⟶ X)_* 𝒪` on `X`. -/
def steinE : ℕᵒᵖ ⥤ X.Modules :=
  Functor.ofOpSequence (X := fun n ↦
    pushforwardUnit (formalStructure I (p ≫ f) (formalPullback I f p 𝒴) n ≫ p))
    fun n ↦ pushforwardUnitMap ((formalPullback I f p 𝒴).transition n)
      (steinE_transition_comp I f p 𝒴 n)

/-- The transition maps of `steinE`. -/
lemma steinE_map_succ (n : ℕ) :
    (steinE I f p 𝒴).map (homOfLE n.le_succ).op =
      pushforwardUnitMap ((formalPullback I f p 𝒴).transition n)
        (steinE_transition_comp I f p 𝒴 n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The composite transitions of the formal pullback lie over `X`. -/
lemma steinE_formalTrans_comp {n m : ℕ} (h : n ≤ m) :
    formalTrans I (p ≫ f) (formalPullback I f p 𝒴) h ≫
        (formalStructure I (p ≫ f) (formalPullback I f p 𝒴) m ≫ p) =
      formalStructure I (p ≫ f) (formalPullback I f p 𝒴) n ≫ p := by
  rw [← Category.assoc, formalTrans_formalStructure]

/-- The composite transitions of `steinE` are induced by those of the formal pullback. -/
lemma steinE_map_eq {n m : ℕ} (h : n ≤ m) :
    (steinE I f p 𝒴).map (homOfLE h).op =
      pushforwardUnitMap (formalTrans I (p ≫ f) (formalPullback I f p 𝒴) h)
        (steinE_formalTrans_comp I f p 𝒴 h) := by
  induction m, h using Nat.le_induction with
  | base =>
    refine ((steinE I f p 𝒴).map_id (op n)).trans ?_
    exact (pushforwardUnitMap_id).symm.trans
      (pushforwardUnitMap_congr (formalTrans_self I (p ≫ f) _ n).symm _ _)
  | succ m hm ih =>
    rw [show (homOfLE (hm.trans m.le_succ)).op = (homOfLE m.le_succ).op ≫ (homOfLE hm).op
      from rfl, Functor.map_comp, steinE_map_succ, ih]
    refine (pushforwardUnitMap_comp (formalTrans I (p ≫ f) (formalPullback I f p 𝒴) hm)
      (steinE_formalTrans_comp I f p 𝒴 hm) ((formalPullback I f p 𝒴).transition m)
      (steinE_transition_comp I f p 𝒴 m)).symm.trans ?_
    exact pushforwardUnitMap_congr (by rw [← formalTrans_succ, formalTrans_comp]) _ _

/-- The comparison `w_n : (Yₙ ⟶ X)_* 𝒪 ⟶ (Yₙ ×_{Xₙ} X'ₙ ⟶ X)_* 𝒪`. -/
abbrev steinW (n : ℕ) :
    (formalAdicSystem I f 𝒴).obj n ⟶ (steinE I f p 𝒴).obj (op n) :=
  pushforwardUnitMap (pbFst I f p 𝒴 n)
    (steinW_comp I f p 𝒴 n)

/-- The comparison maps `w_n` form a map of inverse systems. -/
lemma steinW_comp_map (n : ℕ) :
    steinW I f p 𝒴 (n + 1) ≫ (steinE I f p 𝒴).map (homOfLE n.le_succ).op =
      (formalAdicSystem I f 𝒴).map n ≫ steinW I f p 𝒴 n := by
  rw [steinE_map_succ]
  refine (pushforwardUnitMap_comp ((formalPullback I f p 𝒴).transition n)
    (steinE_transition_comp I f p 𝒴 n) (pbFst I f p 𝒴 (n + 1))
      (steinW_comp I f p 𝒴 (n + 1))).symm.trans ?_
  refine Eq.trans ?_ (pushforwardUnitMap_comp (pbFst I f p 𝒴 n)
    (steinW_comp I f p 𝒴 n) (𝒴.transition n) (transition_formalStructure I f 𝒴 n))
  exact pushforwardUnitMap_congr (formalPullback_transition_fst I f p 𝒴 n) _ _

end SteinMaps

section SteinPushout

variable {A : CommRingCat.{u}} (I : Ideal A) {X X' : Scheme.{u}} (f : X ⟶ Spec A) (p : X' ⟶ X)
  (𝒴 : Scheme.FormalFiniteEtale (thickeningDiagram I f)) {U : X.Opens}

/-- The preimage of `U` in `Yₙ ×_{Xₙ} X'ₙ` is the intersection of the preimages from both factors.
-/
lemma steinOpen_eq (m : ℕ) :
    (formalStructure I (p ≫ f) (formalPullback I f p 𝒴) m ≫ p) ⁻¹ᵁ U =
      pbFst I f p 𝒴 m ⁻¹ᵁ (formalStructure I f 𝒴 m ⁻¹ᵁ U) ⊓
        pbSnd I f p 𝒴 m ⁻¹ᵁ
          (thickening.ι (p ≫ f) I m ⁻¹ᵁ (p ⁻¹ᵁ U)) := by
  have h1 : pbFst I f p 𝒴 m ⁻¹ᵁ
      (formalStructure I f 𝒴 m ⁻¹ᵁ U) =
        (formalStructure I (p ≫ f) (formalPullback I f p 𝒴) m ≫ p) ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, steinW_comp]
  have h2 : pbSnd I f p 𝒴 m ⁻¹ᵁ
      (thickening.ι (p ≫ f) I m ⁻¹ᵁ (p ⁻¹ᵁ U)) =
        (formalStructure I (p ≫ f) (formalPullback I f p 𝒴) m ≫ p) ⁻¹ᵁ U := rfl
  rw [h1, h2]
  exact (inf_idem _).symm

variable [IsProper p] (hU : IsAffineOpen U)

include hU in
/-- **Flat base change of sections for the Stein comparison**: over an affine open `U ⊆ X`,
`Γ(Yₙ ×_{Xₙ} X'ₙ, U) = Γ(Yₙ, U) ⊗_{Γ(Xₙ, U)} Γ(X'ₙ, p⁻¹ U)`, as `Yₙ ⟶ Xₙ` is flat. -/
theorem isPushout_stein (m : ℕ) :
    IsPushout ((thickeningMap I f p m).appLE (thickening.ι f I m ⁻¹ᵁ U)
        (thickening.ι (p ≫ f) I m ⁻¹ᵁ (p ⁻¹ᵁ U)) (thickeningMap_preimage_le I f p m))
      ((formalQ I f 𝒴 m).appLE (thickening.ι f I m ⁻¹ᵁ U) (formalStructure I f 𝒴 m ⁻¹ᵁ U)
        le_rfl)
      ((pbSnd I f p 𝒴 m).appLE _
        ((formalStructure I (p ≫ f) (formalPullback I f p 𝒴) m ≫ p) ⁻¹ᵁ U)
        ((steinOpen_eq I f p 𝒴 (U := U) m).le.trans inf_le_right))
      ((pbFst I f p 𝒴 m).appLE _
        ((formalStructure I (p ≫ f) (formalPullback I f p 𝒴) m ≫ p) ⁻¹ᵁ U)
        ((steinOpen_eq I f p 𝒴 (U := U) m).le.trans inf_le_left)) := by
  have H : IsPullback (pbFst I f p 𝒴 m) (pbSnd I f p 𝒴 m) (𝒴.obj m).hom
      (thickeningMap I f p m) := IsPullback.of_hasPullback _ _
  have hUS : IsAffineOpen (thickening.ι f I m ⁻¹ᵁ U) := hU.preimage _
  have hUX : IsAffineOpen (formalStructure I f 𝒴 m ⁻¹ᵁ U) := hU.preimage _
  have hUT := (thickening.ι (p ≫ f) I m ≫ p).isCompact_preimage hU.isCompact
  have hUT' := (thickening.ι (p ≫ f) I m ≫ p).isQuasiSeparated_preimage hU.isQuasiSeparated
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_left H
    (thickeningMap_preimage_le I f p m) (le_refl (formalStructure I f 𝒴 m ⁻¹ᵁ U))
    (steinOpen_eq I f p 𝒴 m) hUS hUX hUT hUT'
  exact ((isIso_pushoutSection_iff H _ _ _).mp hiso).flip

end SteinPushout

section SteinAux

/-- Pushing forward a map `g_* 𝒪 ⟶ g'_* 𝒪` along `p` gives the map `(g ≫ p)_* 𝒪 ⟶ (g' ≫ p)_* 𝒪`. -/
lemma pushforwardComp_pushforwardUnitMap {X X' Z Z' : Scheme.{u}} (p : X' ⟶ X) {g : Z ⟶ X'}
    {g' : Z' ⟶ X'} (h : Z ⟶ Z') (hg : h ≫ g' = g) (hg₂ : h ≫ (g' ≫ p) = g ≫ p) :
    (pushforward p).map (pushforwardUnitMap h hg) ≫
        (Scheme.Modules.pushforwardComp g p).hom.app (unitModule Z) =
      (Scheme.Modules.pushforwardComp g' p).hom.app (unitModule Z') ≫
        pushforwardUnitMap h hg₂ := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  rfl

/-- The maps `M / I^{k+1} M ⟶ M / I^{m+1} M ⟶ M / I^{n+1} M` compose. -/
lemma quotMap_comp {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec A) (M : X.Modules) {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) :
    quotMap I f M h₂ ≫ quotMap I f M h₁ = quotMap I f M (h₁.trans h₂) := by
  rw [← cancel_epi (M.toQuotientIdealPow f I k), toQuotientIdealPow_quotMap_assoc,
    toQuotientIdealPow_quotMap, toQuotientIdealPow_quotMap]

/-- An isomorphism of adic systems `M / I^{n+1} M ≅ Gₙ` is compatible with all composite
transitions. -/
lemma quotMap_comp_iso {A : CommRingCat.{u}} [IsNoetherianRing A] {I : Ideal A} {X : Scheme.{u}}
    {f : X ⟶ Spec A} (G : AdicSystem I f) (F : X.Modules)
    (e : ∀ n, F.quotientIdealPow f I n ≅ G.obj n)
    (he : ∀ n, (e (n + 1)).hom ≫ G.map n = F.quotientIdealPowMap f I n ≫ (e n).hom)
    {n m : ℕ} (h : n ≤ m) :
    quotMap I f F h ≫ (e n).hom = (e m).hom ≫ G.trans h := by
  induction m, h using Nat.le_induction with
  | base => rw [quotMap_self, G.trans_self, Category.id_comp, Category.comp_id]
  | succ m hm ih =>
    rw [← quotientIdealPowMap_quotMap I f F hm, Category.assoc, ih, ← Category.assoc, ← he,
      Category.assoc, ← G.trans_succ, G.trans_trans]

variable {A : CommRingCat.{u}} (I : Ideal A) {X X' : Scheme.{u}} (f : X ⟶ Spec A) (p : X' ⟶ X)
  (𝒴 : Scheme.FormalFiniteEtale (thickeningDiagram I f))

/-- The transitions of the formal pullback lie over those of `(Yₙ)`. -/
lemma transition_pbFst (n : ℕ) :
    (formalPullback I f p 𝒴).transition n ≫ pbFst I f p 𝒴 (n + 1) =
      pbFst I f p 𝒴 n ≫ 𝒴.transition n :=
  formalPullback_transition_fst I f p 𝒴 n

/-- The composite transitions of the formal pullback lie over those of `(Yₙ)`. -/
lemma formalTrans_pbFst {n m : ℕ} (h : n ≤ m) :
    formalTrans I (p ≫ f) (formalPullback I f p 𝒴) h ≫ pbFst I f p 𝒴 m =
      pbFst I f p 𝒴 n ≫ formalTrans I f 𝒴 h := by
  induction m, h using Nat.le_induction with
  | base => rw [formalTrans_self, formalTrans_self, Category.id_comp, Category.comp_id]
  | succ m hm ih =>
    rw [← formalTrans_comp _ _ _ hm m.le_succ, ← formalTrans_comp _ _ _ hm m.le_succ,
      Category.assoc, formalTrans_succ, formalTrans_succ, transition_pbFst,
      ← Category.assoc, ih, Category.assoc]

/-- The composite transitions of the formal pullback lie over those of `(X'ₙ)`. -/
lemma formalTrans_pbSnd {n m : ℕ} (h : n ≤ m) :
    formalTrans I (p ≫ f) (formalPullback I f p 𝒴) h ≫ pbSnd I f p 𝒴 m =
      pbSnd I f p 𝒴 n ≫ (thickeningDiagram I (p ≫ f)).map (homOfLE h) :=
  formalTrans_formalQ I (p ≫ f) (formalPullback I f p 𝒴) h

end SteinAux

section SteinPieces

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X X' : Scheme.{u}}
  (f : X ⟶ Spec A) (p : X' ⟶ X) (𝒴 : Scheme.FormalFiniteEtale (thickeningDiagram I f))
  (F' : X'.Modules)
  (e' : ∀ n, F'.quotientIdealPow (p ≫ f) I n ≅
    (formalAdicSystem I (p ≫ f) (formalPullback I f p 𝒴)).obj n)
  (he' : ∀ n, (e' (n + 1)).hom ≫ (formalAdicSystem I (p ≫ f) (formalPullback I f p 𝒴)).map n =
    F'.quotientIdealPowMap (p ≫ f) I n ≫ (e' n).hom)

/-- The comparison `u_n : p_* F' ⟶ (Yₙ ×_{Xₙ} X'ₙ ⟶ X)_* 𝒪`. -/
def steinU (n : ℕ) : (pushforward p).obj F' ⟶ (steinE I f p 𝒴).obj (op n) :=
  (pushforward p).map (F'.toQuotientIdealPow (p ≫ f) I n ≫ (e' n).hom) ≫
    (Scheme.Modules.pushforwardComp (formalStructure I (p ≫ f) (formalPullback I f p 𝒴) n)
      p).hom.app (unitModule _)

/-- Sections of `u_n`. -/
lemma steinU_app (n : ℕ) (U : X.Opens) (b : Γ((pushforward p).obj F', U)) :
    (steinU I f p 𝒴 F' e' n).app U b =
      (e' n).hom.app (p ⁻¹ᵁ U) ((F'.toQuotientIdealPow (p ≫ f) I n).app (p ⁻¹ᵁ U) b) := rfl

include he' in
/-- The comparison maps `u_n` form a map of inverse systems. -/
lemma steinU_comp_map (n : ℕ) :
    steinU I f p 𝒴 F' e' (n + 1) ≫ (steinE I f p 𝒴).map (homOfLE n.le_succ).op =
      steinU I f p 𝒴 F' e' n := by
  rw [steinE_map_succ]
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  ext b
  change ((formalAdicSystem I (p ≫ f) (formalPullback I f p 𝒴)).map n).app (p ⁻¹ᵁ U)
      ((e' (n + 1)).hom.app (p ⁻¹ᵁ U)
        ((F'.toQuotientIdealPow (p ≫ f) I (n + 1)).app (p ⁻¹ᵁ U) b)) =
    (e' n).hom.app (p ⁻¹ᵁ U) ((F'.toQuotientIdealPow (p ≫ f) I n).app (p ⁻¹ᵁ U) b)
  rw [← Scheme.Modules.Hom.comp_app_apply, he', Scheme.Modules.Hom.comp_app_apply]
  conv_rhs => rw [← Scheme.Modules.toQuotientIdealPow_comp_map]
  rfl

omit [IsNoetherianRing A] in
/-- Sections of the composite transitions of `steinE`. -/
lemma steinE_map_app' {n m : ℕ} (h : n ≤ m) (U : X.Opens)
    (z : Γ((steinE I f p 𝒴).obj (op m), U)) :
    ((steinE I f p 𝒴).map (homOfLE h).op).app U z =
      ((formalAdicSystem I (p ≫ f) (formalPullback I f p 𝒴)).trans h).app (p ⁻¹ᵁ U) z := by
  rw [steinE_map_eq, formalAdicSystem_trans_eq]
  rfl

end SteinPieces

section SteinConditions

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X X' : Scheme.{u}}
  (f : X ⟶ Spec A) (p : X' ⟶ X) [IsProper p] [IsLocallyNoetherian X]
  (𝒴 : Scheme.FormalFiniteEtale (thickeningDiagram I f))
  (F' : X'.Modules) [F'.IsCoherent]
  (e' : ∀ n, F'.quotientIdealPow (p ≫ f) I n ≅
    (formalAdicSystem I (p ≫ f) (formalPullback I f p 𝒴)).obj n)
  (he' : ∀ n, (e' (n + 1)).hom ≫ (formalAdicSystem I (p ≫ f) (formalPullback I f p 𝒴)).map n =
    F'.quotientIdealPowMap (p ≫ f) I n ≫ (e' n).hom)
  {U : X.Opens} (hU : IsAffineOpen U) (hpU : Function.Bijective (p.app U))

include hU hpU in
/-- **Kernel condition for the Stein comparison**: over an affine open `U` with `Γ(X, U) ≅ Γ(X', p⁻¹
U)`, the maps `u_n : p_* F' ⟶ E_n` and `w_n : (Yₙ ⟶ X)_* 𝒪 ⟶ E_n` satisfy the pro-isomorphism kernel
conditions (relative Artin–Rees for `F'` and flat base change of the thickening kernels). -/
theorem stein_proIsoKer :
    ∃ c, ProIsoKer (formalAdicSystem I f 𝒴) ((pushforward p).obj F') (steinE I f p 𝒴)
      (steinU I f p 𝒴 F' e') (steinW I f p 𝒴) U c := by
    obtain ⟨c₁, hc₁⟩ := exists_relative_ker_le I f p hU F'
    obtain ⟨c₂, hc₂⟩ := exists_thickeningMap_ker_le I f p hU hpU
    refine ⟨c₁ + c₂, fun n b hb ↦ ?_, fun n g hg ↦ ?_⟩
    · have h1 : (F'.toQuotientIdealPow (p ≫ f) I (n + (c₁ + c₂))).app (p ⁻¹ᵁ U) b = 0 := by
        have key : (e' (n + (c₁ + c₂))).hom.app (p ⁻¹ᵁ U)
            ((F'.toQuotientIdealPow (p ≫ f) I (n + (c₁ + c₂))).app (p ⁻¹ᵁ U) b) = 0 := hb
        have := congrArg ((e' (n + (c₁ + c₂))).inv.app (p ⁻¹ᵁ U)) key
        rwa [← Scheme.Modules.Hom.comp_app_apply, Iso.hom_inv_id, map_zero] at this
      obtain ⟨k, hk⟩ : ∃ k, n + (c₁ + c₂) = k + c₁ := ⟨n + c₂, by omega⟩
      rw [hk] at h1
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (hc₁ k b h1)
    · have hflat := (formalQ I f 𝒴 (n + (c₁ + c₂))).flat_appLE
        (hU.preimage (thickening.ι f I (n + (c₁ + c₂))))
        (hU.preimage (formalStructure I f 𝒴 (n + (c₁ + c₂)))) le_rfl
      have hg' : (pbFst I f p 𝒴 (n + (c₁ + c₂))).appLE _ _
            ((steinOpen_eq I f p 𝒴 (U := U) (n + (c₁ + c₂))).le.trans inf_le_left) g = 0 := hg
      have h1 := mem_map_ker_of_isPushout (isPushout_stein I f p 𝒴 hU (n + (c₁ + c₂))) hflat hg'
      have hc₂' : RingHom.ker ((thickeningMap I f p (n + (c₁ + c₂))).appLE _ _
          (thickeningMap_preimage_le I f p (n + (c₁ + c₂)))).hom ≤
            (idealV f I U 1 ^ (n + 1)).map ((thickening.ι f I (n + (c₁ + c₂))).app U).hom := by
        obtain ⟨k, hk⟩ : ∃ k, n + (c₁ + c₂) = k + c₂ := ⟨n + c₁, by omega⟩
        rw [hk]
        exact (hc₂ k).trans (Ideal.map_mono (Ideal.pow_le_pow_right (by omega)))
      have h2 := Ideal.map_mono hc₂' h1
      rw [Ideal.map_map] at h2
      rw [AdicSystem.transition_app_eq_zero_iff _ _ _ hU]
      refine (mem_smul_top_pushforwardUnit_iff (g := formalStructure I f 𝒴 (n + (c₁ + c₂)))
        _ g).mpr ?_
      have hcomp : ((formalStructure I f 𝒴 (n + (c₁ + c₂))).app U).hom =
          ((formalQ I f 𝒴 (n + (c₁ + c₂))).appLE _ _ le_rfl).hom.comp
            ((thickening.ι f I (n + (c₁ + c₂))).app U).hom := by
        change ((formalQ I f 𝒴 _ ≫ thickening.ι f I _).app U).hom = _
        rw [Scheme.Hom.comp_app, Scheme.Hom.app_eq_appLE (formalQ I f 𝒴 _)]
        rfl
      rw [hcomp]
      exact h2

include hU he' in
/-- **Lifting to `p_* F'`**: the image of `E_m ⟶ E_n` lies in the image of `u_n` for `m ≥ n + c`. -/
theorem stein_lift_u :
    ∃ c, ∀ n m (hm : n + c ≤ m) (z : Γ((steinE I f p 𝒴).obj (op m), U)), ∃ b,
      (steinU I f p 𝒴 F' e' n).app U b =
        ((steinE I f p 𝒴).map (homOfLE (le_of_add_le_left hm)).op).app U z := by
    obtain ⟨c, hc⟩ := exists_relative_lift I f p hU F'
    refine ⟨c, fun n m hm z ↦ ?_⟩
    obtain ⟨b, hb⟩ := hc n ((quotMap I (p ≫ f) F' hm).app (p ⁻¹ᵁ U)
      ((e' m).inv.app (p ⁻¹ᵁ U) z))
    refine ⟨b, ?_⟩
    refine (steinU_app I f p 𝒴 F' e' n U b).trans ?_
    rw [hb]
    have hmor : (e' m).inv ≫ quotMap I (p ≫ f) F' hm ≫
        quotMap I (p ≫ f) F' (Nat.le_add_right n c) ≫ (e' n).hom =
          (formalAdicSystem I (p ≫ f) (formalPullback I f p 𝒴)).trans (le_of_add_le_left hm) := by
      rw [← Category.assoc (quotMap I (p ≫ f) F' hm), quotMap_comp,
        quotMap_comp_iso _ F' e' he', Iso.inv_hom_id_assoc]
    rw [steinE_map_app', ← hmor]
    rfl

omit [IsNoetherianRing A] [IsProper p] [IsLocallyNoetherian X] in
/-- The image of `Γ(X'ₘ, p⁻¹ U) → Γ(X'ₙ, p⁻¹ U)` lies in that of `Γ(Xₙ, U)` as soon as it does
for `m = n + c`. -/
lemma stein_thickening_range {c : ℕ}
    (hc : ∀ n (t : Γ(thickening (p ≫ f) I (n + c),
        (thickening.ι (p ≫ f) I (n + c)) ⁻¹ᵁ (p ⁻¹ᵁ U))),
      ((thickeningDiagram I (p ≫ f)).map (homOfLE (Nat.le_add_right n c))).appLE _ _
          (preimage_le_preimage_of_comp_eq _
            (thickeningDiagram_map_ι_of_le I (p ≫ f) (Nat.le_add_right n c)) _) t ∈
        Set.range ((thickeningMap I f p n).appLE _ _ (thickeningMap_preimage_le I f p n)))
    {n m : ℕ} (h : n ≤ m) (hm : n + c ≤ m)
    (hτle : thickening.ι (p ≫ f) I n ⁻¹ᵁ (p ⁻¹ᵁ U) ≤
        ((thickeningDiagram I (p ≫ f)).map (homOfLE h)) ⁻¹ᵁ
          (thickening.ι (p ≫ f) I m ⁻¹ᵁ (p ⁻¹ᵁ U))) :
    Set.range (((thickeningDiagram I (p ≫ f)).map (homOfLE h)).appLE _ _ hτle) ⊆
      Set.range ((thickeningMap I f p n).appLE _ _ (thickeningMap_preimage_le I f p n)) := by
  have H : (thickeningDiagram I (p ≫ f)).map (homOfLE h) =
      (thickeningDiagram I (p ≫ f)).map (homOfLE (Nat.le_add_right n c)) ≫
        (thickeningDiagram I (p ≫ f)).map (homOfLE hm) := by
    rw [← Functor.map_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  have e₁ : thickening.ι (p ≫ f) I (n + c) ⁻¹ᵁ (p ⁻¹ᵁ U) ≤
      ((thickeningDiagram I (p ≫ f)).map (homOfLE hm)) ⁻¹ᵁ
        (thickening.ι (p ≫ f) I m ⁻¹ᵁ (p ⁻¹ᵁ U)) :=
    preimage_le_preimage_of_comp_eq _ (thickeningDiagram_map_ι_of_le I (p ≫ f) hm) _
  have e₂ : thickening.ι (p ≫ f) I n ⁻¹ᵁ (p ⁻¹ᵁ U) ≤
      ((thickeningDiagram I (p ≫ f)).map (homOfLE (Nat.le_add_right n c))) ⁻¹ᵁ
        (thickening.ι (p ≫ f) I (n + c) ⁻¹ᵁ (p ⁻¹ᵁ U)) :=
    preimage_le_preimage_of_comp_eq _
      (thickeningDiagram_map_ι_of_le I (p ≫ f) (Nat.le_add_right n c)) _
  exact range_appLE_subset_of_eq_comp H e₁ e₂ hτle _ (hc n)

include hU hpU in
/-- **Lifting to `(Yₙ ⟶ X)_* 𝒪`**: over an affine open `U` with `Γ(X, U) ≅ Γ(X', p⁻¹ U)`, the image
of `E_m ⟶ E_n` lies in the image of `w_n` for `m ≥ n + c` (flat base change of the images of the
thickenings). -/
theorem stein_lift_w :
    ∃ c, ∀ n m (hm : n + c ≤ m) (z : Γ((steinE I f p 𝒴).obj (op m), U)), ∃ g,
      (steinW I f p 𝒴 n).app U g =
        ((steinE I f p 𝒴).map (homOfLE (le_of_add_le_left hm)).op).app U z := by
    obtain ⟨c, hc⟩ := exists_thickeningMap_lift I f p hU hpU
    refine ⟨c, fun n m hm z ↦ ?_⟩
    have h := le_of_add_le_left hm
    have hsq : (thickeningMap I f p n).appLE _ _ (thickeningMap_preimage_le I f p n) ≫
        (pbSnd I f p 𝒴 n).appLE _
          ((formalStructure I (p ≫ f) (formalPullback I f p 𝒴) n ≫ p) ⁻¹ᵁ U)
          ((steinOpen_eq I f p 𝒴 (U := U) n).le.trans inf_le_right) =
      (formalQ I f 𝒴 n).appLE (thickening.ι f I n ⁻¹ᵁ U) (formalStructure I f 𝒴 n ⁻¹ᵁ U)
          le_rfl ≫
        (pbFst I f p 𝒴 n).appLE _
          ((formalStructure I (p ≫ f) (formalPullback I f p 𝒴) n ≫ p) ⁻¹ᵁ U)
          ((steinOpen_eq I f p 𝒴 (U := U) n).le.trans inf_le_left) := by
      exact appLE_square (pbFst_condition I f p 𝒴 n).symm _ _ _ _
    have hτle : thickening.ι (p ≫ f) I n ⁻¹ᵁ (p ⁻¹ᵁ U) ≤
        ((thickeningDiagram I (p ≫ f)).map (homOfLE h)) ⁻¹ᵁ
          (thickening.ι (p ≫ f) I m ⁻¹ᵁ (p ⁻¹ᵁ U)) :=
      preimage_le_preimage_of_comp_eq _ (thickeningDiagram_map_ι_of_le I (p ≫ f) h) _
    have hσle : formalStructure I f 𝒴 n ⁻¹ᵁ U ≤
        (formalTrans I f 𝒴 h) ⁻¹ᵁ (formalStructure I f 𝒴 m ⁻¹ᵁ U) :=
      preimage_le_preimage_of_comp_eq _ (formalTrans_formalStructure I f 𝒴 h) _
    have hφle : (formalStructure I (p ≫ f) (formalPullback I f p 𝒴) n ≫ p) ⁻¹ᵁ U ≤
        (formalTrans I (p ≫ f) (formalPullback I f p 𝒴) h) ⁻¹ᵁ
          ((formalStructure I (p ≫ f) (formalPullback I f p 𝒴) m ≫ p) ⁻¹ᵁ U) :=
      preimage_le_preimage_of_comp_eq _ (steinE_formalTrans_comp I f p 𝒴 h) _
    have key := range_subset_of_isPushout (isPushout_stein I f p 𝒴 hU m) hsq
      ((formalTrans I (p ≫ f) (formalPullback I f p 𝒴) h).appLE _ _ hφle)
      (((thickeningDiagram I (p ≫ f)).map (homOfLE h)).appLE _ _ hτle)
      ((formalTrans I f 𝒴 h).appLE _ _ hσle)
      (appLE_square (formalTrans_pbSnd I f p 𝒴 h) _ _ _ _)
      (appLE_square (formalTrans_pbFst I f p 𝒴 h) _ _ _ _)
      (stein_thickening_range I f p hc h hm hτle)
    obtain ⟨g, hg⟩ := key ⟨z, rfl⟩
    refine ⟨g, hg.trans ?_⟩
    rw [steinE_map_eq]
    rfl

end SteinConditions

section SteinMain

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X X' : Scheme.{u}} (f : X ⟶ Spec A) [IsProper f] (p : X' ⟶ X) [IsProper p]

/-- **Algebraization descends along Stein-type proper morphisms** (the key step of EGA III 5.1.4
via Chow's lemma, specialized to étale coverings): let `p : X' ⟶ X` be proper with
`Γ(X, U) ≅ Γ(X', p⁻¹ U)` for all affine `U` (e.g. `p_* 𝒪_{X'} = 𝒪_X`), `X'` with affine
diagonal. If formal étale coverings of `X'` are algebraizable, so are those of `X`: the
algebraization of `(Yₙ ×_{Xₙ} X'ₙ ⟶ X')_* 𝒪` pushes forward to one of `(Yₙ ⟶ X)_* 𝒪`, by the
relative Artin–Rees lemma on both sides and flat base change along `Yₙ ⟶ Xₙ`. -/
theorem formalAlgebraizable_of_stein [IsAffineHom (pullback.diagonal (terminal.from X'))]
    (hp : ∀ U : X.Opens, IsAffineOpen U → Function.Bijective (p.app U))
    (h' : FormalAlgebraizable I (p ≫ f)) : FormalAlgebraizable I f := by
  intro 𝒴
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨F', hF', e', he'⟩ := h' (formalPullback I f p 𝒴)
  have : F'.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have hq := isQuasicoherent_pushforward_of_quasiCompact p F'
  have hB : ((pushforward p).obj F').IsCoherent :=
    ⟨hq, isFiniteType_of_finite_sections _ (fun U : X.affineOpens ↦ U.1)
      (iSup_affineOpens_eq_top X) (fun U ↦ U.2)
      fun U ↦ finite_sections_preimage_of_isProper p F' U.2⟩
  have hu := steinU_comp_map I f p 𝒴 F' e' he'
  have hw := steinW_comp_map I f p 𝒴
  obtain ⟨e, he⟩ := exists_iso_quotientIdealPow_of_proIso (formalAdicSystem I f 𝒴)
    ((pushforward p).obj F') (steinE I f p 𝒴) (steinU I f p 𝒴 F' e') (steinW I f p 𝒴) hu hw
    (fun U hU ↦ stein_proIsoKer I f p 𝒴 F' e' hU (hp U hU))
    (fun U hU n b ↦ by
      obtain ⟨c, hc⟩ := stein_lift_w I f p 𝒴 hU (hp U hU)
      obtain ⟨g, hg⟩ := hc n (n + c) le_rfl ((steinU I f p 𝒴 F' e' (n + c)).app U b)
      refine ⟨g, hg.trans ?_⟩
      rw [← Scheme.Modules.Hom.comp_app_apply, proIso_u_comp (hu := hu)])
    (fun U hU n g ↦ by
      obtain ⟨c, hc⟩ := stein_lift_u I f p 𝒴 F' e' he' hU
      obtain ⟨g', rfl⟩ := (formalAdicSystem I f 𝒴).trans_surjective (Nat.le_add_right n c) hU g
      obtain ⟨b, hb⟩ := hc n (n + c) le_rfl ((steinW I f p 𝒴 (n + c)).app U g')
      refine ⟨b, hb.trans ?_⟩
      rw [← Scheme.Modules.Hom.comp_app_apply, proIso_w_comp (hw := hw),
        Scheme.Modules.Hom.comp_app_apply])
  exact ⟨_, hB, e, he⟩

end SteinMain

end AlgebraicGeometry.CohomologyAux
