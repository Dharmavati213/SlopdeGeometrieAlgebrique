/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import SGA.Foundations.Cohomology.FlatBaseChange
import SGA.Foundations.Picard.Basic

/-!
# Line bundles on `P × W` trivial over an open cover of `W`

Let `k` be a field and `P` a `k`-scheme with `𝒪_k ≅ f_* 𝒪_P` (for instance `P` proper and
geometrically integral over `k = k̄`, `isIso_app_of_isProper_of_geometricallyIntegral`). For every
`k`-scheme `W` the functions on `P ×ₖ W` over the inverse image of an open `V ⊆ W` are the functions
on `V` (flat base change, `isIso_app_snd_tensor`). Hence (a form of the seesaw principle,
Mumford, *Abelian varieties*, §5, Corollary 6, for the part not involving cohomology): a line
bundle on `P ×ₖ W` which is trivial over the inverse images of the members of an open cover of
`W`, and trivial along a section `W → P ×ₖ W`, is trivial
(`AlgebraicGeometry.Scheme.LineBundle.class_eq_one_of_forall_trivial`).

## Main results

* `Scheme.LineBundle.class_pullback_ι_eq_one_iff`: `L` is trivial over an open `V` (its
  restriction to `V` has trivial class) iff it has an invertible section over `V`.
* `isIso_app_of_isProper_of_geometricallyIntegral`, `isIso_app_snd_tensor`.
* `Scheme.LineBundle.class_eq_one_of_forall_trivial`.

## References

* [D. Mumford, *Abelian varieties*, §5][mumford1970]
* [A. Grothendieck, J. Dieudonné, *EGA* III 1.4.15][EGA]
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme.LineBundle

variable {X : Scheme.{u}} (L : X.LineBundle)

/-- The restriction of `L` to an open `V` is trivial iff `L` has an invertible section over
`V`. -/
theorem class_pullback_ι_eq_one_iff (V : X.Opens) :
    (L.pullback V.ι).class = 1 ↔ Nonempty (L.Trivialization V) := by
  rw [class_eq_one_iff_nonempty_trivialization]
  have hV : V.ι.opensRange = V := Opens.opensRange_ι V
  constructor
  · rintro ⟨τ⟩
    obtain ⟨e, he, he'⟩ := L.exists_isSection_famPullback_eq V.ι τ.isSection
    refine ⟨⟨L.famRes hV.ge e, he.famRes hV.ge, isUnit_of_le_famLocus (he.famRes hV.ge) ?_⟩⟩
    rw [famLocus_famRes]
    refine le_inf le_rfl fun x hx ↦ ?_
    have hloc := L.famLocus_famPullback V.ι (V.ι.preimage_opensRange).ge e
    rw [he', famLocus_of_isUnit τ.isUnit] at hloc
    obtain ⟨y, rfl⟩ : x ∈ Set.range V.ι := by rw [Opens.range_ι]; exact hx
    have : y ∈ (⊤ : V.toScheme.Opens) ⊓ V.ι ⁻¹ᵁ L.famLocus V.ι.opensRange e := by
      rw [← hloc]; trivial
    exact this.2
  · rintro ⟨τ⟩
    have h : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := (Opens.ι_preimage_self V).ge
    exact ⟨⟨L.famPullback V.ι h τ.e, τ.isSection.famPullback V.ι h, τ.isUnit.map _⟩⟩

end Scheme.LineBundle

namespace Scheme.LineBundle

section PullbackFam

variable {X Y : Scheme.{u}} (L : X.LineBundle) (f : Y ⟶ X) {V : X.Opens} {V' : Y.Opens}

/-- The inverse image of a trivialization. -/
noncomputable def Trivialization.pullback (τ : L.Trivialization V) (h : V' ≤ f ⁻¹ᵁ V) :
    (L.pullback f).Trivialization V' :=
  ⟨L.famPullback f h τ.e, τ.isSection.famPullback f h, τ.isUnit.map _⟩

end PullbackFam

end Scheme.LineBundle

section Constants

variable {k : Type u} [Field k]

/-- Global functions on a proper geometrically integral scheme `P` over an algebraically closed
field `k` are constant: `𝒪_k ≅ f_* 𝒪_P`, i.e. `f.app V` is an isomorphism for every open `V` of
`Spec k`. -/
theorem isIso_app_of_isProper_of_geometricallyIntegral [IsAlgClosed k] {P : Scheme.{u}}
    (f : P ⟶ Spec (.of k)) [IsProper f] [GeometricallyIntegral f] (V : (Spec (.of k)).Opens) :
    IsIso (f.app V) := by
  have : IsIntegral P := GeometricallyIntegral.isIntegral_of_subsingleton f
  have hV : V = ⊥ ∨ V = ⊤ := by
    by_cases h : V = ⊥
    · exact Or.inl h
    · right
      obtain ⟨x, hx⟩ := Opens.ne_bot_iff_nonempty V |>.1 h
      exact eq_top_iff.2 fun y _ ↦ Subsingleton.elim x y ▸ hx
  rcases hV with rfl | rfl
  · rw [ConcreteCategory.isIso_iff_bijective]
    have : Subsingleton Γ(P, f ⁻¹ᵁ ⊥) := by rw [Scheme.Hom.preimage_bot]; infer_instance
    exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun b ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · rw [ConcreteCategory.isIso_iff_bijective]
    have hint := isIntegral_appTop_of_universallyClosed f
    let g : k →+* Γ(P, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
    have hg : g.IsIntegral := RingHom.IsIntegral.trans _ _
      (RingHom.isIntegral_of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective) hint
    have hgb := IsAlgClosed.ringHom_bijective_of_isIntegral g hg
    have he : Function.Bijective (Scheme.ΓSpecIso (.of k)).inv.hom :=
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.bijective
    exact (Function.Bijective.of_comp_iff _ he).1 hgb

/-- For `P` over `k` with `𝒪_k ≅ f_* 𝒪_P` and any `k`-scheme `W`, the functions on the inverse
image in `P ×ₖ W` of an open `V ⊆ W` are the functions on `V` (flat base change, EGA III 1.4.15). -/
theorem isIso_app_snd_tensor (P W : Over (Spec (.of k))) [QuasiCompact P.hom]
    [QuasiSeparated P.hom] (hP : ∀ V : (Spec (.of k)).Opens, IsIso (P.hom.app V))
    (V : W.left.Opens) : IsIso ((snd P W).left.app V) :=
  CohomologyAux.isIso_app_pullback_snd P.hom W.hom hP V

end Constants

section Glue

variable {k : Type u} [Field k]

lemma Scheme.Hom.appLE_apply_of_eq_id {X : Scheme.{u}} {g : X ⟶ X} (hg : g = 𝟙 X) (V : X.Opens)
    (h : V ≤ g ⁻¹ᵁ V) (r : Γ(X, V)) : g.appLE V V h r = r := by
  subst hg
  change X.presheaf.map (homOfLE _).op ((𝟙 X : X ⟶ X).app V r) = r
  rw [Scheme.Hom.id_app]
  exact LineBundle.presheaf_map_homOfLE_self h r

/-- A line bundle on `P ×ₖ W` (with `𝒪_k ≅ f_* 𝒪_P`) which is trivial along the section
`w ↦ (p₀, w)` and trivial over the inverse image of a neighbourhood of every point of `W` is
trivial. (The part of the seesaw principle, Mumford §5 Corollary 6, which needs no cohomology.) -/
theorem Scheme.LineBundle.class_eq_one_of_forall_trivial (P W : Over (Spec (.of k)))
    [QuasiCompact P.hom] [QuasiSeparated P.hom]
    (hP : ∀ V : (Spec (.of k)).Opens, IsIso (P.hom.app V))
    (p₀ : 𝟙_ (Over (Spec (.of k))) ⟶ P) (L : (P ⊗ W).left.LineBundle)
    (hσ : (L.pullback (lift (CartesianMonoidalCategory.toUnit W ≫ p₀) (𝟙 W)).left).class = 1)
    (hloc : ∀ w : W.left, ∃ U : W.left.Opens, w ∈ U ∧
      Nonempty (L.Trivialization ((snd P W).left ⁻¹ᵁ U))) : L.class = 1 := by
  set π := (snd P W).left with hπ
  set σ := (lift (CartesianMonoidalCategory.toUnit W ≫ p₀) (𝟙 W)).left with hσdef
  have hσπ : σ ≫ π = 𝟙 W.left := by
    rw [hσdef, hπ, ← Over.comp_left, lift_snd, Over.id_left]
  have hpre (V : W.left.Opens) : σ ⁻¹ᵁ (π ⁻¹ᵁ V) = V := by
    rw [← Scheme.Hom.comp_preimage, hσπ, Scheme.Hom.id_preimage]
  -- `σ^* π^* = id` on functions
  have hσπapp (V : W.left.Opens) (r : Γ(W.left, V)) :
      σ.appLE (π ⁻¹ᵁ V) V (hpre V).ge (π.app V r) = r := by
    rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact Scheme.Hom.appLE_apply_of_eq_id hσπ V _ r
  obtain ⟨τg⟩ := (L.pullback σ).class_eq_one_iff_nonempty_trivialization.1 hσ
  have hloc' (w : W.left) : ∃ (U : W.left.Opens) (_ : w ∈ U)
      (_ : L.Trivialization (π ⁻¹ᵁ U)), True := by
    obtain ⟨U, hw, ⟨t⟩⟩ := hloc w
    exact ⟨U, hw, t, True.intro⟩
  choose U hwU τ _ using hloc'
  -- the inverse images along `σ` of the local trivializations, and their coordinates
  let ρ (w : W.left) : (L.pullback σ).Trivialization (U w) := (τ w).pullback L σ (hpre (U w)).ge
  let τg' (w : W.left) := τg.res (le_top : U w ≤ ⊤)
  have hu (w : W.left) : IsUnit ((τg' w).coord (ρ w).isSection) := (τg' w).isUnit_coord (ρ w)
  -- the normalized local trivializations `π^*(u⁻¹) e_w`
  let v (w : W.left) : Γ((P ⊗ W).left, π ⁻¹ᵁ U w) := π.app (U w) ↑(hu w).unit⁻¹
  let e (w : W.left) : L.Fam (π ⁻¹ᵁ U w) := L.famConst _ (v w) * (τ w).e
  have hv (w : W.left) : IsUnit (v w) := ((hu w).unit⁻¹.isUnit).map _
  have he (w : W.left) : L.IsSection ((1 : ℕ) : ℤ) _ (e w) :=
    ((isSection_famConst (L := L) (v w)).mul (τ w).isSection).of_eq (by simp)
  have heu (w : W.left) : IsUnit (e w) := ((hv w).map _).mul (τ w).isUnit
  -- their inverse images along `σ` all equal `τg`
  have hσe (w : W.left) : L.famPullback σ (hpre (U w)).ge (e w) = (τg' w).e := by
    rw [map_mul, famPullback_famConst, hσπapp]
    have h1 := (τg' w).famConst_coord_mul (ρ w).isSection
    rw [_root_.pow_one] at h1
    change (L.pullback σ).famConst (U w) ↑(hu w).unit⁻¹ * (ρ w).e = _
    refine (congrArg (fun x ↦ (L.pullback σ).famConst (U w) ↑(hu w).unit⁻¹ * x) h1.symm).trans ?_
    rw [← mul_assoc, ← map_mul, IsUnit.val_inv_mul, map_one, one_mul]
  -- they agree on overlaps: their ratio is a function pulled back from `W`, trivial along `σ`
  have hcomp (w w' : W.left) : L.famRes (inf_le_left : π ⁻¹ᵁ U w ⊓ π ⁻¹ᵁ U w' ≤ _) (e w) =
      L.famRes (inf_le_right : π ⁻¹ᵁ U w ⊓ π ⁻¹ᵁ U w' ≤ _) (e w') := by
    set O := π ⁻¹ᵁ U w ⊓ π ⁻¹ᵁ U w'
    let t' : L.Trivialization O :=
      ⟨L.famRes inf_le_right (e w'), (he w').famRes _, (heu w').map _⟩
    have hs : L.IsSection ((1 : ℕ) : ℤ) O (L.famRes inf_le_left (e w)) := (he w).famRes _
    set r := t'.coord hs with hr
    have hrel : L.famConst O r * t'.e = L.famRes inf_le_left (e w) := by
      simpa only [_root_.pow_one] using t'.famConst_coord_mul hs
    have hOpre : U w ⊓ U w' ≤ σ ⁻¹ᵁ O := by
      rw [show σ ⁻¹ᵁ O = U w ⊓ U w' by simp only [O, Scheme.Hom.preimage_inf, hpre]]
    have hτg (w'' : W.left) (h : U w ⊓ U w' ≤ U w'') :
        L.famPullback σ hOpre (L.famRes (show O ≤ π ⁻¹ᵁ U w'' from
          fun x hx ↦ h (show π x ∈ U w ⊓ U w' from ⟨hx.1, hx.2⟩)) (e w'')) =
        (L.pullback σ).famRes le_top τg.e := by
      rw [famPullback_famRes, ← famRes_famPullback σ (hpre (U w'')).ge h (e w''), hσe w'']
      exact famRes_famRes _ _ _
    have h₁ := hτg w inf_le_left
    have h₂ := hτg w' inf_le_right
    have hσr : σ.appLE O (U w ⊓ U w') hOpre r = 1 := by
      have := congrArg (L.famPullback σ hOpre) hrel
      rw [map_mul, famPullback_famConst, h₁] at this
      change _ * L.famPullback σ hOpre (L.famRes _ (e w')) = _ at this
      rw [h₂] at this
      have hu' : IsUnit ((L.pullback σ).famRes (le_top : U w ⊓ U w' ≤ ⊤) τg.e) :=
        τg.isUnit.map _
      have h1 := hu'.mul_right_cancel (this.trans (one_mul _).symm)
      exact (L.pullback σ).famConst_injective _ (h1.trans (map_one _).symm)
    have := isIso_app_snd_tensor P W hP (U w ⊓ U w')
    obtain ⟨r₁, hr₁⟩ := (ConcreteCategory.bijective_of_isIso (π.app (U w ⊓ U w'))).2 r
    have hr₁' : r₁ = 1 := by
      rw [← hσπapp (U w ⊓ U w') r₁]
      exact (congrArg _ hr₁).trans hσr
    have hr1 : r = 1 := by rw [← hr₁, hr₁', map_one]; rfl
    rw [hr1, map_one, one_mul] at hrel
    exact hrel.symm
  -- glue them
  have hcov : (⊤ : (P ⊗ W).left.Opens) ≤ ⨆ w, π ⁻¹ᵁ U w :=
    fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨π x, hwU (π x)⟩
  obtain ⟨s, hs, hsres⟩ := L.exists_isSection_glue (fun w ↦ π ⁻¹ᵁ U w) (fun _ ↦ le_top) hcov e he
    hcomp
  have hunit : IsUnit s := by
    refine isUnit_of_le_famLocus hs fun x _ ↦ ?_
    have h := famLocus_famRes (L := L) (le_top : π ⁻¹ᵁ U (π x) ≤ ⊤) s
    rw [hsres, famLocus_of_isUnit (heu _)] at h
    have hx : x ∈ π ⁻¹ᵁ U (π x) := hwU (π x)
    rw [h] at hx
    exact hx.2
  exact (class_eq_one_iff_nonempty_trivialization L).2 ⟨⟨s, hs, hunit⟩⟩

end Glue

end AlgebraicGeometry
