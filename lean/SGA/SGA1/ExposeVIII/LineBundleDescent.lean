/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.AffineSpace
import SGA.SGA1.ExposeVIII.AmpleEffectiveness

/-!
# SGA 1, Exposé VIII, 7.8: descent of line bundles

Let `g : S' ⟶ S` be faithfully flat and quasi-compact, `D` an effective descent datum on
`X' ⟶ S'` with descended `S`-scheme `X` and `h : X' ⟶ X`, and `L'` a line bundle on `X'` with a
descent datum `E` relative to `D`. We show that `L'` descends to a line bundle `L` on `X`, with
an isomorphism `h*L ≅ L'` compatible with `E`.

The line bundle `L` is built from trivializations: a trivialization of `L'` over `h⁻¹(W)` compatible
with `E` (`LineBundleDatum.Trivialization`) is a nowhere vanishing section of `L'` over `h⁻¹(W)`
whose two inverse images to `X''` correspond under `E`. The ratios of two such trivializations
are invariant functions, hence descend to `X` (VIII.1.7, for functions; `h` is an effective
epimorphism); they are the transition functions of `L`.

Such trivializations exist locally on `X` (`LineBundleDatum.exists_trivialization`): for `W`
affine, `h⁻¹(W)` is covered by an affine `T`, and VIII.1 applied to the graded ring of sections
of the inverse image of `L'` on `T`, with its descent datum relative to `T ⟶ W`, gives invariant
sections not vanishing at a given point (`exists_isInvariant_of_isAffine`); they descend along
`T ⟶ X'`. Ampleness of the descended bundle is VIII.5.8.

## Main results

- `exists_appLE_eq_of_isPullback`: descent of functions along an effective epimorphism.
- `DescentDatum.LineBundleDatum.exists_iso_isCompatible`: `L'` descends as soon as `X` is covered
  by open subsets `W` over which `L'` has a trivialization compatible with `E`.
- `DescentDatum.LineBundleDatum.exists_trivialization`: such trivializations exist locally.
- `effectiveOfRelativelyAmpleStatement`: VIII.7.8.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
  Scheme.LineBundle

namespace SGA.SGA1.ExposeVIII

section Functions

variable {Y Z : Scheme.{u}}

/-- For a flat morphism `p`, `p^*` is injective on functions over an open `O` all of whose points
are images of points of `V`. -/
theorem appLE_injective_of_flat (p : Y ⟶ Z) [Flat p] {O : Z.Opens} {V : Y.Opens}
    (e : V ≤ p ⁻¹ᵁ O) (hO : ∀ z ∈ O, ∃ y ∈ V, p y = z) :
    Function.Injective (p.appLE O V e) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Presheaf.section_ext Z.sheaf O s 0 fun z hz ↦ ?_
  obtain ⟨y, hyV, rfl⟩ := hO z hz
  have hinj : Function.Injective (p.stalkMap y) := by
    algebraize [(p.stalkMap y).hom]
    have : Module.FaithfullyFlat (Z.presheaf.stalk (p y)) (Y.presheaf.stalk y) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap p y) (p.toLRSHom.prop y)
    exact ‹RingHom.FaithfullyFlat _›.injective
  apply hinj
  change p.stalkMap y (Z.presheaf.germ O (p y) hz s) = p.stalkMap y (Z.presheaf.germ O (p y) hz 0)
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, map_zero, map_zero,
    ← Y.presheaf.germ_res_apply (homOfLE e) y hyV]
  change Y.presheaf.germ V y hyV (p.appLE O V e s) = 0
  rw [hs, map_zero]

/-- The affine line over `ℤ`. -/
noncomputable abbrev affineLine : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))

/-- Global functions are morphisms to the affine line. -/
noncomputable abbrev homAffineLineEquiv (X : Scheme.{u}) : (X ⟶ affineLine) ≃ Γ(X, ⊤) :=
  (AffineSpace.toSpecMvPolyIntEquiv (X := X) PUnit.{u + 1}).trans (Equiv.funUnique _ _)

lemma homAffineLineEquiv_comp {X X' : Scheme.{u}} (f : X ⟶ X') (e : X' ⟶ affineLine) :
    homAffineLineEquiv X (f ≫ e) = f.appTop (homAffineLineEquiv X' e) :=
  AffineSpace.toSpecMvPolyIntEquiv_comp _ f e _

lemma preimage_le_of_isPullback {P : Scheme.{u}} {p : Y ⟶ Z} {p₁ p₂ : P ⟶ Y}
    (H : IsPullback p₁ p₂ p p) (O : Z.Opens) : p₁ ⁻¹ᵁ p ⁻¹ᵁ O ≤ p₂ ⁻¹ᵁ p ⁻¹ᵁ O :=
  le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, H.w])

lemma appLE_map_apply (f : Y ⟶ Z) {U : Z.Opens} {V V' : Y.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : V' ≤ V) (x : Γ(Z, U)) :
    Y.presheaf.map (homOfLE h).op (f.appLE U V e x) = f.appLE U V' (h.trans e) x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma map_appLE_apply (f : Y ⟶ Z) {U U' : Z.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U')
    (h : U' ≤ U) (x : Γ(Z, U)) :
    f.appLE U' V e (Z.presheaf.map (homOfLE h).op x) =
      f.appLE U V (e.trans (f.preimage_mono h)) x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

lemma appLE_appLE_apply {X : Scheme.{u}} (f : X ⟶ Y) (f' : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens}
    {W : X.Opens} (e : V ≤ f' ⁻¹ᵁ U) (e' : W ≤ f ⁻¹ᵁ V) (x : Γ(Z, U)) :
    f.appLE V W e' (f'.appLE U V e x) = (f ≫ f').appLE U W (e'.trans (f.preimage_mono e)) x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

lemma appLE_congr_hom {f f' : Y ⟶ Z} (h : f = f') {U : Z.Opens} {V : Y.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (x : Γ(Z, U)) : f.appLE U V e x = f'.appLE U V (h ▸ e) x := by
  subst h
  rfl

lemma resLE_appTop_apply (p : Y ⟶ Z) {O : Z.Opens} {V : Y.Opens} (e : V ≤ p ⁻¹ᵁ O)
    (x : Γ(Z, O)) :
    (p.resLE O V e).appTop (O.topIso.inv x) = V.topIso.inv (p.appLE O V e x) := by
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]

/-- If `p` is an epimorphism over `O`, then `p^*` is injective on functions over `O`. -/
theorem appLE_injective_of_epi (p : Y ⟶ Z) (O : Z.Opens) [Epi (p ∣_ O)] :
    Function.Injective (p.appLE O (p ⁻¹ᵁ O) le_rfl) := by
  have : Epi (p.resLE O (p ⁻¹ᵁ O) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  intro t₁ t₂ ht
  have key : (homAffineLineEquiv O).symm (O.topIso.inv t₁) =
      (homAffineLineEquiv O).symm (O.topIso.inv t₂) := by
    rw [← cancel_epi (p.resLE O (p ⁻¹ᵁ O) le_rfl)]
    apply (homAffineLineEquiv _).injective
    rw [homAffineLineEquiv_comp, homAffineLineEquiv_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, resLE_appTop_apply, resLE_appTop_apply, ht]
  have := congrArg O.topIso.hom ((homAffineLineEquiv O).symm.injective key)
  simpa only [Iso.inv_hom_id_apply] using this

/-- VIII.1.7 for functions: let `p : Y ⟶ Z` be an effective epimorphism over an open `O` of `Z`
(e.g. faithfully flat and quasi-compact, or faithfully flat and locally of finite presentation),
and `Y ×_Z Y` given by a cartesian square `p₁, p₂`. A function on `p⁻¹(O)` whose two inverse
images to `Y ×_Z Y` agree comes from a function on `O`. -/
theorem exists_appLE_eq_of_isPullback {P : Scheme.{u}} (p : Y ⟶ Z) {p₁ p₂ : P ⟶ Y}
    (H : IsPullback p₁ p₂ p p) (O : Z.Opens) [EffectiveEpi (p ∣_ O)] (s : Γ(Y, p ⁻¹ᵁ O))
    (hs : p₁.appLE (p ⁻¹ᵁ O) (p₁ ⁻¹ᵁ p ⁻¹ᵁ O) le_rfl s =
      p₂.appLE (p ⁻¹ᵁ O) (p₁ ⁻¹ᵁ p ⁻¹ᵁ O) (preimage_le_of_isPullback H O) s) :
    ∃ t : Γ(Z, O), p.appLE O (p ⁻¹ᵁ O) le_rfl t = s := by
  have : EffectiveEpi (p.resLE O (p ⁻¹ᵁ O) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  let pO := p.resLE O (p ⁻¹ᵁ O) le_rfl
  let r₁ := p₁.resLE (p ⁻¹ᵁ O) (p₁ ⁻¹ᵁ p ⁻¹ᵁ O) le_rfl
  let r₂ := p₂.resLE (p ⁻¹ᵁ O) (p₁ ⁻¹ᵁ p ⁻¹ᵁ O) (preimage_le_of_isPullback H O)
  let σ := (homAffineLineEquiv (p ⁻¹ᵁ O)).symm ((p ⁻¹ᵁ O).topIso.inv s)
  have hσ : r₁ ≫ σ = r₂ ≫ σ := by
    apply (homAffineLineEquiv _).injective
    rw [homAffineLineEquiv_comp, homAffineLineEquiv_comp, Equiv.apply_symm_apply,
      resLE_appTop_apply, resLE_appTop_apply, hs]
  have key : ∀ {T : Scheme.{u}} (a b : T ⟶ p ⁻¹ᵁ O), a ≫ pO = b ≫ pO → a ≫ σ = b ≫ σ := by
    intro T a b hab
    have hab' : (a ≫ (p ⁻¹ᵁ O).ι) ≫ p = (b ≫ (p ⁻¹ᵁ O).ι) ≫ p := by
      have := congrArg (· ≫ O.ι) hab
      simpa only [pO, Category.assoc, Scheme.Hom.resLE_comp_ι] using this
    let l := H.lift (a ≫ (p ⁻¹ᵁ O).ι) (b ≫ (p ⁻¹ᵁ O).ι) hab'
    have hl : Set.range l ⊆ Set.range (p₁ ⁻¹ᵁ p ⁻¹ᵁ O).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      change p₁ (l z) ∈ p ⁻¹ᵁ O
      rw [← Scheme.Hom.comp_apply, H.lift_fst, Scheme.Hom.comp_apply]
      exact (a z).2
    let l' : T ⟶ p₁ ⁻¹ᵁ p ⁻¹ᵁ O := IsOpenImmersion.lift _ l hl
    have hl' : l' ≫ (p₁ ⁻¹ᵁ p ⁻¹ᵁ O).ι = l := IsOpenImmersion.lift_fac _ _ _
    have ha : a = l' ≫ r₁ := by
      rw [← cancel_mono (p ⁻¹ᵁ O).ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
        reassoc_of% hl', H.lift_fst]
    have hb : b = l' ≫ r₂ := by
      rw [← cancel_mono (p ⁻¹ᵁ O).ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
        reassoc_of% hl', H.lift_snd]
    rw [ha, hb, Category.assoc, Category.assoc, hσ]
  set x := homAffineLineEquiv O (EffectiveEpi.desc pO σ key)
  refine ⟨O.topIso.hom x, ?_⟩
  have hfac := congrArg (homAffineLineEquiv _) (EffectiveEpi.fac pO σ key)
  rw [homAffineLineEquiv_comp, Equiv.apply_symm_apply] at hfac
  have e₁ := resLE_appTop_apply p (le_rfl : p ⁻¹ᵁ O ≤ p ⁻¹ᵁ O) (O.topIso.hom x)
  rw [Iso.hom_inv_id_apply] at e₁
  rw [e₁] at hfac
  have := congrArg (p ⁻¹ᵁ O).topIso.hom hfac
  simpa only [Iso.inv_hom_id_apply] using this

/-- `exists_appLE_eq_of_isPullback` for units. -/
theorem exists_unit_appLE_eq_of_isPullback {P : Scheme.{u}} (p : Y ⟶ Z) {p₁ p₂ : P ⟶ Y}
    (H : IsPullback p₁ p₂ p p) (O : Z.Opens) [EffectiveEpi (p ∣_ O)] (s : Γ(Y, p ⁻¹ᵁ O)ˣ)
    (hs : p₁.appLE (p ⁻¹ᵁ O) (p₁ ⁻¹ᵁ p ⁻¹ᵁ O) le_rfl s.1 =
      p₂.appLE (p ⁻¹ᵁ O) (p₁ ⁻¹ᵁ p ⁻¹ᵁ O) (preimage_le_of_isPullback H O) s.1) :
    ∃ t : Γ(Z, O)ˣ, p.appLE O (p ⁻¹ᵁ O) le_rfl t.1 = s.1 := by
  have hs' : p₁.appLE (p ⁻¹ᵁ O) (p₁ ⁻¹ᵁ p ⁻¹ᵁ O) le_rfl (s⁻¹).1 =
      p₂.appLE (p ⁻¹ᵁ O) (p₁ ⁻¹ᵁ p ⁻¹ᵁ O) (preimage_le_of_isPullback H O) (s⁻¹).1 := by
    calc _ = p₁.appLE (p ⁻¹ᵁ O) (p₁ ⁻¹ᵁ p ⁻¹ᵁ O) le_rfl (s⁻¹).1 *
          (p₂.appLE (p ⁻¹ᵁ O) (p₁ ⁻¹ᵁ p ⁻¹ᵁ O) (preimage_le_of_isPullback H O) s.1 *
            p₂.appLE (p ⁻¹ᵁ O) (p₁ ⁻¹ᵁ p ⁻¹ᵁ O) (preimage_le_of_isPullback H O) (s⁻¹).1) := by
          rw [← map_mul, Units.mul_inv, map_one, mul_one]
      _ = _ := by rw [← hs, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  obtain ⟨a, ha⟩ := exists_appLE_eq_of_isPullback p H O s.1 hs
  obtain ⟨b, hb⟩ := exists_appLE_eq_of_isPullback p H O (s⁻¹).1 hs'
  have hab : a * b = 1 := appLE_injective_of_epi p O (by rw [map_mul, ha, hb, map_one,
    Units.mul_inv])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

end Functions

section Units

variable {X Y : Scheme.{u}}

/-- The inverse image of units, `Γ(Y, U)ˣ ⟶ Γ(X, V)ˣ` for `V ⊆ f⁻¹(U)`. -/
noncomputable def unitsAppLE (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    Γ(Y, U)ˣ →* Γ(X, V)ˣ :=
  Units.map (f.appLE U V e).hom.toMonoidHom

@[simp]
lemma coe_unitsAppLE (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (u : Γ(Y, U)ˣ) :
    (unitsAppLE f U V e u : Γ(X, V)) = f.appLE U V e u :=
  rfl

@[simp]
lemma unitsRes_unitsAppLE (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : V' ≤ V) (u : Γ(Y, U)ˣ) :
    unitsRes h (unitsAppLE f U V e u) = unitsAppLE f U V' (h.trans e) u := by
  ext
  simp only [coe_unitsRes, coe_unitsAppLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

@[simp]
lemma unitsAppLE_unitsRes (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : U ≤ U') (u : Γ(Y, U')ˣ) :
    unitsAppLE f U V e (unitsRes h u) = unitsAppLE f U' V (e.trans (f.preimage_mono h)) u := by
  ext
  simp only [coe_unitsRes, coe_unitsAppLE, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

@[simp]
lemma unitsAppLE_unitsAppLE {Z : Scheme.{u}} (f : X ⟶ Y) (f' : Y ⟶ Z) {U : Z.Opens}
    {V : Y.Opens} {W : X.Opens} (e : V ≤ f' ⁻¹ᵁ U) (e' : W ≤ f ⁻¹ᵁ V) (u : Γ(Z, U)ˣ) :
    unitsAppLE f V W e' (unitsAppLE f' U V e u) =
      unitsAppLE (f ≫ f') U W (e'.trans (f.preimage_mono e)) u := by
  ext
  simp only [coe_unitsAppLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

variable (L : X.LineBundle)

/-- Functions on `V` agreeing on the pieces `V ∩ Uₖ` of the trivializing cover of `L` are
equal. -/
lemma eq_of_forall_res_eq {V : X.Opens} {a b : Γ(X, V)}
    (h : ∀ k, X.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U k ≤ V)).op a =
      X.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U k ≤ V)).op b) : a = b :=
  famConst_injective (L := L) V (funext h)

lemma units_eq_of_forall_unitsRes_eq {V : X.Opens} {a b : Γ(X, V)ˣ}
    (h : ∀ k, unitsRes (inf_le_left : V ⊓ L.U k ≤ V) a = unitsRes inf_le_left b) : a = b :=
  Units.ext (eq_of_forall_res_eq L fun k ↦ by
    simpa only [coe_unitsRes] using congrArg Units.val (h k))

/-- Units on the pieces `V ∩ Uₖ` of the trivializing cover of `L` which agree on the overlaps
glue to a unit on `V`. -/
lemma exists_unit_unitsRes_eq {V : X.Opens} (r : ∀ k, Γ(X, V ⊓ L.U k)ˣ)
    (hr : ∀ k k', unitsRes (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
      V ⊓ (L.U k ⊓ L.U k') ≤ V ⊓ L.U k) (r k) =
        unitsRes (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          V ⊓ (L.U k ⊓ L.U k') ≤ V ⊓ L.U k') (r k')) :
    ∃ u : Γ(X, V)ˣ, ∀ k, unitsRes (inf_le_left : V ⊓ L.U k ≤ V) u = r k := by
  have H (r : ∀ k, Γ(X, V ⊓ L.U k)ˣ)
      (hr : ∀ k k', unitsRes (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
        V ⊓ (L.U k ⊓ L.U k') ≤ V ⊓ L.U k) (r k) =
          unitsRes (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
            V ⊓ (L.U k ⊓ L.U k') ≤ V ⊓ L.U k') (r k')) :
      L.IsSection 0 V (fun k ↦ (r k).1) := fun k k' ↦ by
    have := congrArg Units.val (hr k k')
    simp only [coe_unitsRes] at this
    rw [trans_zero, map_one, one_mul]
    exact this
  have hr' : ∀ k k', unitsRes (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
      V ⊓ (L.U k ⊓ L.U k') ≤ V ⊓ L.U k) (r k)⁻¹ =
        unitsRes (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          V ⊓ (L.U k ⊓ L.U k') ≤ V ⊓ L.U k') (r k')⁻¹ := fun k k' ↦ by
    rw [map_inv, map_inv, hr]
  obtain ⟨a, ha⟩ := exists_famConst_eq (H r hr)
  obtain ⟨b, hb⟩ := exists_famConst_eq (H (fun k ↦ (r k)⁻¹) hr')
  have hab : a * b = 1 := famConst_injective (L := L) V (by
    rw [map_mul, ha, hb, map_one]
    funext k
    simp only [Pi.mul_apply, Units.mul_inv, Pi.one_apply])
  refine ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, fun k ↦ Units.ext ?_⟩
  rw [coe_unitsRes]
  exact congrFun ha k

end Units

namespace DescentDatum

variable {S S' : Scheme.{u}} {g : S' ⟶ S} {D : DescentDatum g} {L' : D.X'.LineBundle}
  (E : D.LineBundleDatum L')

/-- The open subset `q₁⁻¹(V ∩ Uᵢ) ∩ q₂⁻¹(V ∩ Uₖ)` of `X''`. -/
abbrev trivOpen (V : D.X'.Opens) (i k : L'.ι) : D.X''.Opens :=
  D.q₁ ⁻¹ᵁ V ⊓ D.q₂ ⁻¹ᵁ V ⊓ D.q₁ ⁻¹ᵁ L'.U i ⊓ D.q₂ ⁻¹ᵁ L'.U k

lemma trivOpen_le₁ (V : D.X'.Opens) (i k : L'.ι) :
    D.trivOpen V i k ≤ D.q₁ ⁻¹ᵁ (V ⊓ L'.U i) :=
  le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right)

lemma trivOpen_le₂ (V : D.X'.Opens) (i k : L'.ι) :
    D.trivOpen V i k ≤ D.q₂ ⁻¹ᵁ (V ⊓ L'.U k) :=
  le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right)) inf_le_right

lemma trivOpen_le₃ (V : D.X'.Opens) (i k : L'.ι) :
    D.trivOpen V i k ≤ D.q₁ ⁻¹ᵁ L'.U i ⊓ D.q₂ ⁻¹ᵁ L'.U k :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right

/-- A trivialization of `L'` over an open subset `V` of `X'`, compatible with the descent datum
`E`: units `eₖ` on `V ∩ Uₖ` forming a nowhere vanishing section of `L'` over `V`
(`eₖ = gₖₖ' eₖ'`), whose two inverse images to `X''` correspond under `E`
(`q₂*eₖ = φᵢₖ q₁*eᵢ`). -/
structure LineBundleDatum.Trivialization (V : D.X'.Opens) where
  /-- The local expressions of the section. -/
  e (k : L'.ι) : Γ(D.X', V ⊓ L'.U k)ˣ
  sec (k k' : L'.ι) : unitsRes (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
      V ⊓ (L'.U k ⊓ L'.U k') ≤ V ⊓ L'.U k) (e k) =
    unitsRes (inf_le_right : V ⊓ (L'.U k ⊓ L'.U k') ≤ L'.U k ⊓ L'.U k') (L'.g k k') *
      unitsRes (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        V ⊓ (L'.U k ⊓ L'.U k') ≤ V ⊓ L'.U k') (e k')
  inv (i k : L'.ι) : unitsAppLE D.q₂ (V ⊓ L'.U k) (D.trivOpen V i k) (D.trivOpen_le₂ V i k) (e k) =
    unitsRes (D.trivOpen_le₃ V i k) (E.iso.φ i k) *
      unitsAppLE D.q₁ (V ⊓ L'.U i) (D.trivOpen V i k) (D.trivOpen_le₁ V i k) (e i)

/-- The descent datum on `T'` itself relative to `p : T' ⟶ T`: `X'' = T' ×_T T'`, with its two
projections. It is effective, with descended scheme `T`. -/
noncomputable abbrev self {T T' : Scheme.{u}} (p : T' ⟶ T) :
    DescentDatum p where
  X' := T'
  a := 𝟙 T'
  X'' := pullback p p
  b := 𝟙 _
  q₁ := pullback.fst p p
  q₂ := pullback.snd p p
  isPullback₁ := IsPullback.of_vert_isIso ⟨by simp⟩
  isPullback₂ := IsPullback.of_vert_isIso ⟨by simp⟩
  refl _ x := ⟨pullback.lift x x rfl, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  symm _ r := ⟨pullback.lift (r ≫ pullback.snd p p) (r ≫ pullback.fst p p)
    (by simp only [Category.assoc, pullback.condition]), pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _⟩
  trans _ r r' h := ⟨pullback.lift (r ≫ pullback.fst p p) (r' ≫ pullback.snd p p)
    (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% h,
      pullback.condition]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

variable {E} in
set_option backward.isDefEq.respectTransparency false in
/-- The invariance of a section `s` of `L'^{⊗n}` under `E`, on the components: `q₂*sₖ = φᵢₖⁿ q₁*sᵢ`
on `q₁⁻¹(Uᵢ) ∩ q₂⁻¹(Uₖ)`. -/
lemma LineBundleDatum.IsInvariant.component {n : ℕ} {s : (L'.pullback (𝟙 D.X')).Fam ⊤}
    {hs : (L'.pullback (𝟙 D.X')).IsSection n ⊤ s} (h : E.IsInvariant hs) (i k : L'.ι) :
    D.q₂.appLE (⊤ ⊓ (L'.pullback (𝟙 D.X')).U k)
        (⊤ ⊓ (L'.pullback D.q₁).U i ⊓ (L'.pullback D.q₂).U k)
        (le_inf (le_top.trans D.q₂.preimage_top.ge) inf_le_right) (s k) =
      D.X''.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          ⊤ ⊓ (L'.pullback D.q₁).U i ⊓ (L'.pullback D.q₂).U k ≤
            (L'.pullback D.q₁).U i ⊓ (L'.pullback D.q₂).U k)).op ((E.iso.φ i k).1 ^ n) *
        D.q₁.appLE (⊤ ⊓ (L'.pullback (𝟙 D.X')).U i)
          (⊤ ⊓ (L'.pullback D.q₁).U i ⊓ (L'.pullback D.q₂).U k)
          (le_inf (le_top.trans D.q₁.preimage_top.ge) (inf_le_left.trans inf_le_right)) (s i) := by
  have h1 := congrArg (fun F ↦ (L'.pullback D.q₂).famRes
    (inf_le_left : ⊤ ⊓ (L'.pullback D.q₁).U i ≤ ⊤) F k) h
  simp only [Iso.famRes_mapFam] at h1
  simp only [Iso.localImage, famRes_apply, famPullbackOf_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map] at h1
  exact h1.symm

section TransportTrivialization

variable {S₂ S₂' : Scheme.{u}} {g₂ : S₂' ⟶ S₂} {D₂ : DescentDatum g₂} {τ : D₂.X' ⟶ D.X'}
  {τ'' : D₂.X'' ⟶ D.X''} (h₁ : τ'' ≫ D.q₁ = D₂.q₁ ≫ τ) (h₂ : τ'' ≫ D.q₂ = D₂.q₂ ≫ τ)

set_option backward.isDefEq.respectTransparency false in
/-- Descent of a trivialization along a morphism of descent data `(τ, τ'')`, with `τ` flat and
locally of finite presentation: let `V` be an open subset of `X'` contained in the image of `τ`,
with `q₁⁻¹(V)` contained in the image of the flat morphism `τ''`, and assume that pairs of points
of `X'₂` with the same image in `X'` are related by `X''₂` (the morphism `c`). Then a section of
`τ*L'` over `X'₂`, invariant under the descent datum `τ''*E` and nowhere vanishing on `τ⁻¹(V)`,
descends to a trivialization of `L'` over `V` compatible with `E`. -/
theorem LineBundleDatum.nonempty_trivialization [Flat τ] [LocallyOfFinitePresentation τ]
    [Flat τ''] (c : pullback τ τ ⟶ D₂.X'') (hc₁ : c ≫ D₂.q₁ = pullback.fst τ τ)
    (hc₂ : c ≫ D₂.q₂ = pullback.snd τ τ) {V : D.X'.Opens} (hV : ∀ y ∈ V, ∃ w, τ w = y)
    (hV'' : ∀ z ∈ D.q₁ ⁻¹ᵁ V, ∃ w, τ'' w = z)
    {s₂ : ((L'.pullback τ).pullback (𝟙 D₂.X')).Fam ⊤}
    {hs₂ : ((L'.pullback τ).pullback (𝟙 D₂.X')).IsSection ((1 : ℕ) : ℤ) ⊤ s₂}
    (hinv : (E.transport D₂ h₁ h₂).IsInvariant hs₂)
    (hloc : τ ⁻¹ᵁ V ≤ ((L'.pullback τ).pullback (𝟙 D₂.X')).famLocus ⊤ s₂) :
    Nonempty (E.Trivialization V) := by
  have hle (k : L'.ι) : τ ⁻¹ᵁ (V ⊓ L'.U k) ≤ D₂.X'.basicOpen (s₂ k) :=
    fun y hy ↦ (famLocus_inf_U hs₂ k).le ⟨hloc hy.1, hy.2⟩
  have Hk (k : L'.ι) : τ ⁻¹ᵁ (V ⊓ L'.U k) ≤ ⊤ ⊓ ((L'.pullback τ).pullback (𝟙 D₂.X')).U k :=
    (hle k).trans (D₂.X'.basicOpen_le _)
  have hunit (k : L'.ι) : IsUnit (D₂.X'.presheaf.map (homOfLE (Hk k)).op (s₂ k)) := by
    have h0 : IsUnit (D₂.X'.presheaf.map (homOfLE (D₂.X'.basicOpen_le (s₂ k))).op (s₂ k)) :=
      D₂.X'.toRingedSpace.isUnit_res_basicOpen (s₂ k)
    simpa only [CohomologyAux.presheaf_map_map] using
      h0.map (D₂.X'.presheaf.map (homOfLE (hle k)).op).hom
  let u (k : L'.ι) : Γ(D₂.X', τ ⁻¹ᵁ (V ⊓ L'.U k))ˣ := (hunit k).unit
  have hu (k : L'.ι) : (u k).1 = D₂.X'.presheaf.map (homOfLE (Hk k)).op (s₂ k) :=
    (hunit k).unit_spec
  have hsurj (O : D.X'.Opens) (hO : O ≤ V) : ∀ y ∈ O, ∃ w ∈ τ ⁻¹ᵁ O, τ w = y := fun y hy ↦ by
    obtain ⟨w, rfl⟩ := hV y (hO hy)
    exact ⟨w, hy, rfl⟩
  have hepi (O : D.X'.Opens) (hO : O ≤ V) : EffectiveEpi (τ ∣_ O) := by
    have : Flat (τ ∣_ O) := IsZariskiLocalAtTarget.restrict (inferInstanceAs (Flat τ)) O
    have : LocallyOfFinitePresentation (τ ∣_ O) :=
      IsZariskiLocalAtTarget.restrict (inferInstanceAs (LocallyOfFinitePresentation τ)) O
    have : Surjective (τ ∣_ O) := ⟨fun z ↦ by
      obtain ⟨w, hw, hwz⟩ := hsurj O hO z.1 z.2
      exact ⟨⟨w, hw⟩, Subtype.ext (by rw [morphismRestrict_base_coe]; exact hwz)⟩⟩
    infer_instance
  have pc₁ (z : ↥(pullback τ τ)) : D₂.q₁ (c z) = pullback.fst τ τ z := by
    rw [← Scheme.Hom.comp_apply, hc₁]
  have pc₂ (z : ↥(pullback τ τ)) : D₂.q₂ (c z) = pullback.snd τ τ z := by
    rw [← Scheme.Hom.comp_apply, hc₂]
  have pτ (z : ↥(pullback τ τ)) : τ (pullback.snd τ τ z) = τ (pullback.fst τ τ z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  -- the local expressions are invariant under `X'₂ ×_{X'} X'₂`
  have hinvk (k : L'.ι) : (pullback.fst τ τ).appLE (τ ⁻¹ᵁ (V ⊓ L'.U k))
      (pullback.fst τ τ ⁻¹ᵁ τ ⁻¹ᵁ (V ⊓ L'.U k)) le_rfl (u k).1 =
      (pullback.snd τ τ).appLE (τ ⁻¹ᵁ (V ⊓ L'.U k)) (pullback.fst τ τ ⁻¹ᵁ τ ⁻¹ᵁ (V ⊓ L'.U k))
        (preimage_le_of_isPullback (IsPullback.of_hasPullback τ τ) _) (u k).1 := by
    have hcomp := hinv.component k k
    have hZΩ : pullback.fst τ τ ⁻¹ᵁ τ ⁻¹ᵁ (V ⊓ L'.U k) ≤ c ⁻¹ᵁ (⊤ ⊓
        ((L'.pullback τ).pullback D₂.q₁).U k ⊓ ((L'.pullback τ).pullback D₂.q₂).U k) :=
      fun z hz ↦ by
        refine ⟨⟨trivial, ?_⟩, ?_⟩
        · change τ (D₂.q₁ (c z)) ∈ L'.U k
          rw [pc₁]
          exact hz.2
        · change τ (D₂.q₂ (c z)) ∈ L'.U k
          rw [pc₂, pτ]
          exact hz.2
    have e₁ : (c ≫ τ'') ≫ D.q₁ = pullback.fst τ τ ≫ τ := by
      rw [Category.assoc, h₁, reassoc_of% hc₁]
    have e₂ : (c ≫ τ'') ≫ D.q₂ = pullback.fst τ τ ≫ τ := by
      rw [Category.assoc, h₂, reassoc_of% hc₂, pullback.condition]
    have hd := congrArg Units.val (E.φ_self_of_diag (c ≫ τ'') e₁ e₂ k)
    rw [Iso.coe_pullbackOfEq_φ, Units.val_one] at hd
    have key : c.appLE _ _ hZΩ (D₂.X''.presheaf.map (homOfLE
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right : ⊤ ⊓
          ((L'.pullback τ).pullback D₂.q₁).U k ⊓ ((L'.pullback τ).pullback D₂.q₂).U k ≤
            ((L'.pullback τ).pullback D₂.q₁).U k ⊓ ((L'.pullback τ).pullback D₂.q₂).U k)).op
        (((E.transport D₂ h₁ h₂).iso.φ k k).1 ^ 1)) = 1 := by
      rw [pow_one, E.transport_iso, E.coe_transportIso_φ', appLE_map_apply, appLE_appLE_apply]
      have hZB : pullback.fst τ τ ⁻¹ᵁ τ ⁻¹ᵁ (V ⊓ L'.U k) ≤
          (L'.pullback (pullback.fst τ τ ≫ τ)).U k ⊓ (L'.pullback (pullback.fst τ τ ≫ τ)).U k :=
        fun z hz ↦ ⟨hz.2, hz.2⟩
      rw [← appLE_map_apply (c ≫ τ'') _ hZB, hd, map_one]
      intro z hz
      constructor
      · change ((c ≫ τ'') ≫ D.q₁) z ∈ L'.U k
        rw [e₁]
        exact hz.1
      · change ((c ≫ τ'') ≫ D.q₂) z ∈ L'.U k
        rw [e₂]
        exact hz.2
    have f₁ : (pullback.fst τ τ).appLE (τ ⁻¹ᵁ (V ⊓ L'.U k))
        (pullback.fst τ τ ⁻¹ᵁ τ ⁻¹ᵁ (V ⊓ L'.U k)) le_rfl (u k).1 =
        c.appLE _ _ hZΩ (D₂.q₁.appLE (⊤ ⊓ ((L'.pullback τ).pullback (𝟙 D₂.X')).U k)
          (⊤ ⊓ ((L'.pullback τ).pullback D₂.q₁).U k ⊓ ((L'.pullback τ).pullback D₂.q₂).U k)
          (le_inf (le_top.trans D₂.q₁.preimage_top.ge) (inf_le_left.trans inf_le_right))
          (s₂ k)) := by
      rw [hu, map_appLE_apply, appLE_appLE_apply, appLE_congr_hom hc₁]
    have f₂ : (pullback.snd τ τ).appLE (τ ⁻¹ᵁ (V ⊓ L'.U k))
        (pullback.fst τ τ ⁻¹ᵁ τ ⁻¹ᵁ (V ⊓ L'.U k))
        (preimage_le_of_isPullback (IsPullback.of_hasPullback τ τ) _) (u k).1 =
        c.appLE _ _ hZΩ (D₂.q₂.appLE (⊤ ⊓ ((L'.pullback τ).pullback (𝟙 D₂.X')).U k)
          (⊤ ⊓ ((L'.pullback τ).pullback D₂.q₁).U k ⊓ ((L'.pullback τ).pullback D₂.q₂).U k)
          (le_inf (le_top.trans D₂.q₂.preimage_top.ge) inf_le_right) (s₂ k)) := by
      rw [hu, map_appLE_apply, appLE_appLE_apply, appLE_congr_hom hc₂]
    rw [f₁, f₂, hcomp, map_mul, key, one_mul]
  have hex (k : L'.ι) : ∃ ek : Γ(D.X', V ⊓ L'.U k)ˣ,
      τ.appLE (V ⊓ L'.U k) (τ ⁻¹ᵁ (V ⊓ L'.U k)) le_rfl ek.1 = (u k).1 := by
    have := hepi (V ⊓ L'.U k) inf_le_left
    exact exists_unit_appLE_eq_of_isPullback τ (IsPullback.of_hasPullback τ τ) _ (u k) (hinvk k)
  choose e he using hex
  refine ⟨⟨e, fun k k' ↦ ?_, fun i k ↦ ?_⟩⟩
  · refine Units.ext ?_
    simp only [Units.val_mul, coe_unitsRes]
    apply appLE_injective_of_flat τ (O := V ⊓ (L'.U k ⊓ L'.U k'))
      (V := τ ⁻¹ᵁ (V ⊓ (L'.U k ⊓ L'.U k'))) le_rfl (hsurj _ inf_le_left)
    rw [map_mul, map_appLE_apply, map_appLE_apply, map_appLE_apply]
    have r₁ := appLE_map_apply τ (le_rfl : τ ⁻¹ᵁ (V ⊓ L'.U k) ≤ τ ⁻¹ᵁ (V ⊓ L'.U k))
      (τ.preimage_mono (le_inf inf_le_left (inf_le_right.trans inf_le_left)) :
        τ ⁻¹ᵁ (V ⊓ (L'.U k ⊓ L'.U k')) ≤ τ ⁻¹ᵁ (V ⊓ L'.U k)) (e k).1
    have r₂ := appLE_map_apply τ (le_rfl : τ ⁻¹ᵁ (V ⊓ L'.U k') ≤ τ ⁻¹ᵁ (V ⊓ L'.U k'))
      (τ.preimage_mono (le_inf inf_le_left (inf_le_right.trans inf_le_right)) :
        τ ⁻¹ᵁ (V ⊓ (L'.U k ⊓ L'.U k')) ≤ τ ⁻¹ᵁ (V ⊓ L'.U k')) (e k').1
    rw [← r₁, ← r₂, he k, he k', hu k, hu k', CohomologyAux.presheaf_map_map,
      CohomologyAux.presheaf_map_map]
    have hO₂ : τ ⁻¹ᵁ (V ⊓ (L'.U k ⊓ L'.U k')) ≤
        ⊤ ⊓ (((L'.pullback τ).pullback (𝟙 D₂.X')).U k ⊓
          ((L'.pullback τ).pullback (𝟙 D₂.X')).U k') := fun y hy ↦ ⟨trivial, hy.2⟩
    have := congrArg (D₂.X'.presheaf.map (homOfLE hO₂).op) (hs₂ k k')
    simp only [map_mul, CohomologyAux.presheaf_map_map, trans_natCast, pow_one] at this
    rw [this]
    congr 1
    change D₂.X'.presheaf.map _ (Scheme.Hom.appLE (𝟙 D₂.X') _ _ _
      (τ.appLE _ _ _ (L'.g k k').1)) = _
    rw [appLE_appLE_apply, appLE_map_apply, appLE_congr_hom (Category.id_comp τ)]
  · refine Units.ext ?_
    simp only [Units.val_mul, coe_unitsRes, coe_unitsAppLE]
    have hZ : ∀ z ∈ D.trivOpen V i k, ∃ w ∈ τ'' ⁻¹ᵁ D.trivOpen V i k, τ'' w = z :=
      fun z hz ↦ by
        obtain ⟨w, rfl⟩ := hV'' z hz.1.1.1
        exact ⟨w, hz, rfl⟩
    apply appLE_injective_of_flat τ'' le_rfl hZ
    have pτ₁ (z : D₂.X'') : τ (D₂.q₁ z) = D.q₁ (τ'' z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h₁]
    have pτ₂ (z : D₂.X'') : τ (D₂.q₂ z) = D.q₂ (τ'' z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h₂]
    have hZk : τ'' ⁻¹ᵁ D.trivOpen V i k ≤ D₂.q₂ ⁻¹ᵁ τ ⁻¹ᵁ (V ⊓ L'.U k) := fun z hz ↦ by
      have := D.trivOpen_le₂ V i k hz
      change τ (D₂.q₂ z) ∈ V ⊓ L'.U k
      rw [pτ₂]
      exact this
    have hZi : τ'' ⁻¹ᵁ D.trivOpen V i k ≤ D₂.q₁ ⁻¹ᵁ τ ⁻¹ᵁ (V ⊓ L'.U i) := fun z hz ↦ by
      have := D.trivOpen_le₁ V i k hz
      change τ (D₂.q₁ z) ∈ V ⊓ L'.U i
      rw [pτ₁]
      exact this
    have hZΩ : τ'' ⁻¹ᵁ D.trivOpen V i k ≤ ⊤ ⊓ ((L'.pullback τ).pullback D₂.q₁).U i ⊓
        ((L'.pullback τ).pullback D₂.q₂).U k := fun z hz ↦ by
      refine ⟨⟨trivial, ?_⟩, ?_⟩
      · change τ (D₂.q₁ z) ∈ L'.U i
        rw [pτ₁]
        exact hz.1.2
      · change τ (D₂.q₂ z) ∈ L'.U k
        rw [pτ₂]
        exact hz.2
    rw [map_mul, appLE_appLE_apply, appLE_appLE_apply, map_appLE_apply, appLE_congr_hom h₂,
      appLE_congr_hom h₁, ← appLE_appLE_apply D₂.q₂ τ (V := τ ⁻¹ᵁ (V ⊓ L'.U k)) le_rfl hZk,
      he k, hu k, map_appLE_apply,
      ← appLE_appLE_apply D₂.q₁ τ (V := τ ⁻¹ᵁ (V ⊓ L'.U i)) le_rfl hZi, he i, hu i,
      map_appLE_apply]
    have := congrArg (D₂.X''.presheaf.map (homOfLE hZΩ).op) (hinv.component i k)
    simp only [map_mul, appLE_map_apply, CohomologyAux.presheaf_map_map, pow_one] at this
    rw [E.transport_iso, E.coe_transportIso_φ', appLE_map_apply] at this
    exact this

end TransportTrivialization

section Descent

variable [Surjective g] [Flat g] [QuasiCompact g] (s : D.Solution)

omit [Surjective g] [Flat g] [QuasiCompact g] in
lemma Solution.preimage_q₁_eq (O : s.X.Opens) : D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ O = D.q₂ ⁻¹ᵁ s.h ⁻¹ᵁ O := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, s.q₁_h]

set_option backward.isDefEq.respectTransparency false in
instance (O : s.X.Opens) : EffectiveEpi (s.h ∣_ O) := by
  have : Flat (s.h ∣_ O) := IsZariskiLocalAtTarget.restrict (inferInstanceAs (Flat s.h)) O
  have : Surjective (s.h ∣_ O) :=
    IsZariskiLocalAtTarget.restrict (inferInstanceAs (Surjective s.h)) O
  have : QuasiCompact (s.h ∣_ O) :=
    IsZariskiLocalAtTarget.restrict (inferInstanceAs (QuasiCompact s.h)) O
  infer_instance

variable {s} {W : s.X → s.X.Opens} (t : ∀ x, E.Trivialization (s.h ⁻¹ᵁ W x))

/-- The ratio `e_y / e_x` of two trivializations, on `h⁻¹(W_x ∩ W_y) ∩ Uₖ`. -/
noncomputable def LineBundleDatum.ratio (x y : s.X) (k : L'.ι) :
    Γ(D.X', s.h ⁻¹ᵁ (W x ⊓ W y) ⊓ L'.U k)ˣ :=
  unitsRes (inf_le_inf_right _ (s.h.preimage_mono inf_le_right)) ((t y).e k) *
    (unitsRes (inf_le_inf_right _ (s.h.preimage_mono inf_le_left)) ((t x).e k))⁻¹

omit [Surjective g] [Flat g] [QuasiCompact g] in
lemma LineBundleDatum.ratio_compat (x y : s.X) (k k' : L'.ι) :
    unitsRes (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
      s.h ⁻¹ᵁ (W x ⊓ W y) ⊓ (L'.U k ⊓ L'.U k') ≤ s.h ⁻¹ᵁ (W x ⊓ W y) ⊓ L'.U k)
        (E.ratio t x y k) =
      unitsRes (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        s.h ⁻¹ᵁ (W x ⊓ W y) ⊓ (L'.U k ⊓ L'.U k') ≤ s.h ⁻¹ᵁ (W x ⊓ W y) ⊓ L'.U k')
          (E.ratio t x y k') := by
  have hy := congrArg (unitsRes (inf_le_inf_right _ (s.h.preimage_mono inf_le_right) :
    s.h ⁻¹ᵁ (W x ⊓ W y) ⊓ (L'.U k ⊓ L'.U k') ≤ s.h ⁻¹ᵁ W y ⊓ (L'.U k ⊓ L'.U k')))
    ((t y).sec k k')
  have hx := congrArg (unitsRes (inf_le_inf_right _ (s.h.preimage_mono inf_le_left) :
    s.h ⁻¹ᵁ (W x ⊓ W y) ⊓ (L'.U k ⊓ L'.U k') ≤ s.h ⁻¹ᵁ W x ⊓ (L'.U k ⊓ L'.U k')))
    ((t x).sec k k')
  simp only [map_mul, Scheme.LineBundle.Iso.unitsRes_unitsRes] at hx hy
  simp only [LineBundleDatum.ratio, map_mul, map_inv, Scheme.LineBundle.Iso.unitsRes_unitsRes]
  rw [hx, hy, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]

omit [Surjective g] [Flat g] [QuasiCompact g] in
lemma LineBundleDatum.exists_ratioUnit (x y : s.X) :
    ∃ u : Γ(D.X', s.h ⁻¹ᵁ (W x ⊓ W y))ˣ,
      ∀ k, unitsRes (inf_le_left : s.h ⁻¹ᵁ (W x ⊓ W y) ⊓ L'.U k ≤ _) u = E.ratio t x y k :=
  exists_unit_unitsRes_eq L' (E.ratio t x y) (E.ratio_compat t x y)

/-- The ratio `e_y / e_x` of two trivializations, as a unit on `h⁻¹(W_x ∩ W_y)`. -/
noncomputable def LineBundleDatum.ratioUnit (x y : s.X) : Γ(D.X', s.h ⁻¹ᵁ (W x ⊓ W y))ˣ :=
  (E.exists_ratioUnit t x y).choose

omit [Surjective g] [Flat g] [QuasiCompact g] in
lemma LineBundleDatum.unitsRes_ratioUnit (x y : s.X) (k : L'.ι) {V : D.X'.Opens}
    (hV : V ≤ s.h ⁻¹ᵁ (W x ⊓ W y) ⊓ L'.U k) :
    unitsRes (hV.trans inf_le_left) (E.ratioUnit t x y) = unitsRes hV (E.ratio t x y k) := by
  rw [← (E.exists_ratioUnit t x y).choose_spec k, Scheme.LineBundle.Iso.unitsRes_unitsRes]
  rfl

omit [Surjective g] [Flat g] [QuasiCompact g] in
set_option backward.isDefEq.respectTransparency false in
/-- The ratio of two trivializations is invariant: its two inverse images to `X''` agree. -/
lemma LineBundleDatum.ratioUnit_invariant (x y : s.X) :
    unitsAppLE D.q₁ (s.h ⁻¹ᵁ (W x ⊓ W y)) (D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ (W x ⊓ W y)) le_rfl
        (E.ratioUnit t x y) =
      unitsAppLE D.q₂ (s.h ⁻¹ᵁ (W x ⊓ W y)) (D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ (W x ⊓ W y))
        (s.preimage_q₁_eq _).le (E.ratioUnit t x y) := by
  refine units_eq_of_forall_unitsRes_eq (L'.pullback D.q₁) fun i ↦
    units_eq_of_forall_unitsRes_eq (L'.pullback D.q₂) fun k ↦ ?_
  simp only [unitsRes_unitsAppLE]
  set Ω := D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ (W x ⊓ W y) ⊓ (L'.pullback D.q₁).U i ⊓ (L'.pullback D.q₂).U k
  have hΩ (z : s.X) (hz : W x ⊓ W y ≤ W z) : Ω ≤ D.trivOpen (s.h ⁻¹ᵁ W z) i k := by
    have A : Ω ≤ D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ W z :=
      inf_le_left.trans (inf_le_left.trans (D.q₁.preimage_mono (s.h.preimage_mono hz)))
    exact le_inf (le_inf (le_inf A (A.trans (s.preimage_q₁_eq _).le))
      (inf_le_left.trans inf_le_right)) inf_le_right
  have hy := congrArg (unitsRes (hΩ y inf_le_right)) ((t y).inv i k)
  have hx := congrArg (unitsRes (hΩ x inf_le_left)) ((t x).inv i k)
  simp only [map_mul, unitsRes_unitsAppLE, Scheme.LineBundle.Iso.unitsRes_unitsRes] at hx hy
  have e₁ : unitsAppLE D.q₁ (s.h ⁻¹ᵁ (W x ⊓ W y)) Ω
      (inf_le_left.trans inf_le_left) (E.ratioUnit t x y) =
      unitsAppLE D.q₁ (s.h ⁻¹ᵁ (W x ⊓ W y) ⊓ L'.U i) Ω
        (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
        (E.ratio t x y i) := by
    rw [← (E.exists_ratioUnit t x y).choose_spec i, unitsAppLE_unitsRes]
    rfl
  have e₂ : unitsAppLE D.q₂ (s.h ⁻¹ᵁ (W x ⊓ W y)) Ω
      ((inf_le_left.trans inf_le_left).trans (s.preimage_q₁_eq _).le) (E.ratioUnit t x y) =
      unitsAppLE D.q₂ (s.h ⁻¹ᵁ (W x ⊓ W y) ⊓ L'.U k) Ω
        (le_inf ((inf_le_left.trans inf_le_left).trans (s.preimage_q₁_eq _).le) inf_le_right)
        (E.ratio t x y k) := by
    rw [← (E.exists_ratioUnit t x y).choose_spec k, unitsAppLE_unitsRes]
    rfl
  rw [e₁, e₂]
  simp only [LineBundleDatum.ratio, map_mul, map_inv, unitsAppLE_unitsRes]
  rw [hy, hx, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]

lemma LineBundleDatum.exists_transition (x y : s.X) :
    ∃ c : Γ(s.X, W x ⊓ W y)ˣ,
      unitsAppLE s.h (W x ⊓ W y) (s.h ⁻¹ᵁ (W x ⊓ W y)) le_rfl c = E.ratioUnit t x y := by
  obtain ⟨c, hc⟩ := exists_unit_appLE_eq_of_isPullback s.h
    (D.isPullback_q₁_q₂ s.isPullback s.q₁_h) (W x ⊓ W y) (E.ratioUnit t x y)
    (congrArg Units.val (E.ratioUnit_invariant t x y))
  exact ⟨c, Units.ext hc⟩

/-- The transition functions of the descended line bundle: the descents of the ratios of the
trivializations. -/
noncomputable def LineBundleDatum.transition (x y : s.X) : Γ(s.X, W x ⊓ W y)ˣ :=
  (E.exists_transition t x y).choose

lemma LineBundleDatum.unitsAppLE_transition (x y : s.X) {V : D.X'.Opens}
    (hV : V ≤ s.h ⁻¹ᵁ (W x ⊓ W y)) :
    unitsAppLE s.h (W x ⊓ W y) V hV (E.transition t x y) = unitsRes hV (E.ratioUnit t x y) := by
  rw [← (E.exists_transition t x y).choose_spec, unitsRes_unitsAppLE]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma LineBundleDatum.transition_cocycle (x y z : s.X) :
    unitsRes (inf_le_left : W x ⊓ W y ⊓ W z ≤ W x ⊓ W y) (E.transition t x y) *
      unitsRes (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        W x ⊓ W y ⊓ W z ≤ W y ⊓ W z) (E.transition t y z) =
      unitsRes (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        W x ⊓ W y ⊓ W z ≤ W x ⊓ W z) (E.transition t x z) := by
  apply Units.ext
  apply appLE_injective_of_epi s.h (W x ⊓ W y ⊓ W z)
  change (unitsAppLE s.h _ _ le_rfl _).1 = (unitsAppLE s.h _ _ le_rfl _).1
  congr 1
  simp only [map_mul, unitsAppLE_unitsRes, E.unitsAppLE_transition]
  refine units_eq_of_forall_unitsRes_eq L' fun k ↦ ?_
  simp only [map_mul, Scheme.LineBundle.Iso.unitsRes_unitsRes]
  have hk (a b : s.X) (hab : W x ⊓ W y ⊓ W z ≤ W a ⊓ W b) :
      s.h ⁻¹ᵁ (W x ⊓ W y ⊓ W z) ⊓ L'.U k ≤ s.h ⁻¹ᵁ (W a ⊓ W b) ⊓ L'.U k :=
    inf_le_inf_right _ (s.h.preimage_mono hab)
  rw [E.unitsRes_ratioUnit t x y k (hk x y inf_le_left),
    E.unitsRes_ratioUnit t y z k (hk y z (le_inf (inf_le_left.trans inf_le_right) inf_le_right)),
    E.unitsRes_ratioUnit t x z k (hk x z (le_inf (inf_le_left.trans inf_le_left) inf_le_right))]
  simp only [LineBundleDatum.ratio, map_mul, map_inv, Scheme.LineBundle.Iso.unitsRes_unitsRes]
  rw [mul_comm (unitsRes _ ((t y).e k) * _), mul_assoc, inv_mul_cancel_left]

variable (hW : ∀ x, x ∈ W x)

/-- The line bundle on the descended scheme `X` defined by trivializations of `L'` compatible
with `E` over the inverse images of the open subsets `W x` of `X`. -/
noncomputable def LineBundleDatum.descended : s.X.LineBundle where
  ι := s.X
  U := W
  iSup_eq_top := eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hW x⟩
  g := E.transition t
  cocycle x y z := by
    simpa only [Units.val_mul, coe_unitsRes] using
      congrArg Units.val (E.transition_cocycle t x y z)

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `h*L ≅ L'`, given on `h⁻¹(W x) ∩ Uₖ` by the trivialization over
`h⁻¹(W x)`. -/
noncomputable def LineBundleDatum.descendedIso :
    ((E.descended t hW).pullback s.h).Iso L' where
  φ x k := (t x).e k
  compat_left x x' k := by
    have key : unitsRes (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        s.h ⁻¹ᵁ W x ⊓ s.h ⁻¹ᵁ W x' ⊓ L'.U k ≤ s.h ⁻¹ᵁ W x ⊓ L'.U k) ((t x).e k) =
        unitsAppLE s.h (W x' ⊓ W x) (s.h ⁻¹ᵁ W x ⊓ s.h ⁻¹ᵁ W x' ⊓ L'.U k)
          (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left))
          (E.transition t x' x) *
        unitsRes (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          s.h ⁻¹ᵁ W x ⊓ s.h ⁻¹ᵁ W x' ⊓ L'.U k ≤ s.h ⁻¹ᵁ W x' ⊓ L'.U k) ((t x').e k) := by
      rw [E.unitsAppLE_transition, E.unitsRes_ratioUnit t x' x k
        (le_inf (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left))
          inf_le_right)]
      simp only [LineBundleDatum.ratio, map_mul, map_inv, Scheme.LineBundle.Iso.unitsRes_unitsRes]
      rw [inv_mul_cancel_right]
    have := congrArg Units.val key
    simp only [Units.val_mul, coe_unitsRes, coe_unitsAppLE] at this
    refine this.trans ?_
    congr 1
    change _ = D.X'.presheaf.map _ (s.h.appLE (W x' ⊓ W x) _ _ (E.transition t x' x).1)
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    rfl
  compat_right x k k' := by
    have := congrArg Units.val ((t x).sec k k')
    simp only [Units.val_mul, coe_unitsRes] at this
    exact this

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `h*L ≅ L'` is compatible with the descent datum `E`. -/
theorem LineBundleDatum.isCompatible_descendedIso :
    E.IsCompatible s.q₁_h (E.descendedIso t hW) := by
  intro x i k
  have hle : D.compatOpen s.h (E.descended t hW) x i k ≤ D.trivOpen (s.h ⁻¹ᵁ W x) i k := by
    have A : D.compatOpen s.h (E.descended t hW) x i k ≤ D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ W x :=
      inf_le_left.trans inf_le_left
    exact le_inf (le_inf (le_inf A (A.trans (s.preimage_q₁_eq _).le))
      (inf_le_left.trans inf_le_right)) inf_le_right
  have := congrArg (unitsRes hle) ((t x).inv i k)
  simp only [map_mul, unitsRes_unitsAppLE, Scheme.LineBundle.Iso.unitsRes_unitsRes] at this
  have h2 := congrArg Units.val this
  simp only [Units.val_mul, coe_unitsRes, coe_unitsAppLE] at h2
  exact h2

include t hW in
/-- VIII.7.8, descent of line bundles: if `X` is covered by open subsets `W` over whose inverse
images `L'` has a trivialization compatible with `E`, then `L'` descends to a line bundle `L` on
`X`, with an isomorphism `h*L ≅ L'` compatible with `E`. -/
theorem LineBundleDatum.exists_iso_isCompatible :
    ∃ (L : s.X.LineBundle) (ψ : (L.pullback s.h).Iso L'), E.IsCompatible s.q₁_h ψ :=
  ⟨_, _, E.isCompatible_descendedIso t hW⟩

end Descent

section LocalTrivialization

variable [Surjective g] [Flat g] [QuasiCompact g]

set_option backward.isDefEq.respectTransparency false in
/-- VIII.7.8, descent of line bundles, local existence of trivializations: if `h : X' ⟶ X` solves
the descent problem, every point of `X` has an open neighbourhood `W` over whose inverse image
`L'` admits a trivialization compatible with `E`. For `W` affine, one covers `h⁻¹(W)` by an affine
`T` (a finite disjoint union of affine open subsets); by VIII.1 applied to the section ring of the
inverse image of `L'` on `T` with its descent datum relative to `T ⟶ W`
(`exists_isInvariant_of_isAffine`), some invariant section does not vanish at a given point, and
it descends along `T ⟶ X'` (`nonempty_trivialization`). -/
theorem LineBundleDatum.exists_trivialization (s : D.Solution) (x : s.X) :
    ∃ W : s.X.Opens, x ∈ W ∧ Nonempty (E.Trivialization (s.h ⁻¹ᵁ W)) := by
  obtain ⟨W, hWa, hxW⟩ : ∃ W : s.X.Opens, IsAffineOpen W ∧ x ∈ W := by
    obtain ⟨W, hWa, hxW, -⟩ := Opens.isBasis_iff_nbhd.mp s.X.isBasis_affineOpens
      (show x ∈ (⊤ : s.X.Opens) from trivial)
    exact ⟨W, hWa, hxW⟩
  have : IsAffine W := hWa
  obtain ⟨hY, hYdef⟩ : ∃ f : (s.h ⁻¹ᵁ W).toScheme ⟶ W,
      f = s.h.resLE W (s.h ⁻¹ᵁ W) le_rfl := ⟨_, rfl⟩
  have : Flat hY := by
    rw [hYdef, Scheme.Hom.resLE_eq_morphismRestrict]
    exact IsZariskiLocalAtTarget.restrict (inferInstanceAs (Flat s.h)) W
  have : Surjective hY := by
    rw [hYdef, Scheme.Hom.resLE_eq_morphismRestrict]
    exact IsZariskiLocalAtTarget.restrict (inferInstanceAs (Surjective s.h)) W
  have : QuasiCompact hY := by
    rw [hYdef, Scheme.Hom.resLE_eq_morphismRestrict]
    exact IsZariskiLocalAtTarget.restrict (inferInstanceAs (QuasiCompact s.h)) W
  have : CompactSpace (s.h ⁻¹ᵁ W) := QuasiCompact.compactSpace_of_compactSpace hY
  obtain ⟨T, τ₀, hτs, hτ, hT⟩ :=
    (s.h ⁻¹ᵁ W).toScheme.exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  have : Flat τ₀ := IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ τ₀ hτ
  have : MorphismProperty.ContainsIdentities @LocallyOfFinitePresentation :=
    ⟨fun _ ↦ inferInstance⟩
  have : LocallyOfFinitePresentation τ₀ :=
    IsLocalIso.le_of_isZariskiLocalAtSource @LocallyOfFinitePresentation _ _ τ₀ hτ
  have : Surjective τ₀ := hτs
  have : IsAffine T := hT
  obtain ⟨g₂, hg₂⟩ : ∃ f : T ⟶ W, f = τ₀ ≫ hY := ⟨_, rfl⟩
  obtain ⟨τ, hτdef⟩ : ∃ f : T ⟶ D.X', f = τ₀ ≫ (s.h ⁻¹ᵁ W).ι := ⟨_, rfl⟩
  have : Flat g₂ := hg₂ ▸ inferInstance
  have : Surjective g₂ := hg₂ ▸ inferInstance
  have : Flat τ := hτdef ▸ inferInstance
  have : LocallyOfFinitePresentation τ := hτdef ▸ inferInstance
  have hτg : τ ≫ s.h = g₂ ≫ W.ι := by
    rw [hτdef, hg₂, hYdef, Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι]
  -- `X''` over `W` is `h⁻¹(W) ×_W h⁻¹(W)`
  have hY'' : D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ W = D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ W ⊓ D.q₂ ⁻¹ᵁ s.h ⁻¹ᵁ W := by
    rw [← s.preimage_q₁_eq, inf_idem]
  have Hres := Scheme.Hom.isPullback_resLE (D.isPullback_q₁_q₂ s.isPullback s.q₁_h)
    (US := W) (UT := s.h ⁻¹ᵁ W) (UX := s.h ⁻¹ᵁ W) le_rfl le_rfl hY''
  rw [← hYdef] at Hres
  let m : pullback g₂ g₂ ⟶ pullback hY hY :=
    pullback.map g₂ g₂ hY hY τ₀ τ₀ (𝟙 _) (by rw [hg₂, Category.comp_id])
      (by rw [hg₂, Category.comp_id])
  have hm₁ : Surjective m := MorphismProperty.pullbackMap (P := @Surjective) ‹_› ‹_› hg₂ hg₂
  have hm₂ : Flat m := MorphismProperty.pullbackMap (P := @Flat) ‹_› ‹_› hg₂ hg₂
  let τ'' : pullback g₂ g₂ ⟶ D.X'' :=
    m ≫ Hres.isoPullback.inv ≫ (D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ W).ι
  have k₁ : (D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ W).ι ≫ D.q₁ =
      D.q₁.resLE (s.h ⁻¹ᵁ W) (D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ W) le_rfl ≫ (s.h ⁻¹ᵁ W).ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  have k₂ : (D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ W).ι ≫ D.q₂ =
      D.q₂.resLE (s.h ⁻¹ᵁ W) (D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ W) (s.preimage_q₁_eq W).le ≫ (s.h ⁻¹ᵁ W).ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  have hmf : m ≫ pullback.fst hY hY = pullback.fst g₂ g₂ ≫ τ₀ := pullback.lift_fst _ _ _
  have hms : m ≫ pullback.snd hY hY = pullback.snd g₂ g₂ ≫ τ₀ := pullback.lift_snd _ _ _
  have h₁ : τ'' ≫ D.q₁ = pullback.fst g₂ g₂ ≫ τ := by
    simp only [τ'', Category.assoc, k₁, IsPullback.isoPullback_inv_fst_assoc]
    rw [hτdef]
    exact (reassoc_of% hmf) _
  have h₂ : τ'' ≫ D.q₂ = pullback.snd g₂ g₂ ≫ τ := by
    simp only [τ'', Category.assoc, k₂, IsPullback.isoPullback_inv_snd_assoc]
    rw [hτdef]
    exact (reassoc_of% hms) _
  have : Flat τ'' := by
    have := hm₂
    infer_instance
  -- an invariant section of `τ*L'` not vanishing at a point over `x`
  obtain ⟨y, hy⟩ := g₂.surjective ⟨x, hxW⟩
  obtain ⟨t₀, ht₀, hyt₀⟩ := exists_isSection_one_mem_famLocus
    (L := (L'.pullback τ).pullback (𝟙 T)) (isAffineOpen_top T) (Set.mem_univ y)
  obtain ⟨s₂, hs₂, hinv, hys₂⟩ :=
    (E.transport (self g₂) h₁ h₂).exists_isInvariant_of_isAffine y ht₀ hyt₀
  set U₂ := ((L'.pullback τ).pullback (𝟙 T)).famLocus ⊤ s₂
  have hstab := (E.transport (self g₂) h₁ h₂).isStable_famLocus hinv
  have hsat (a b : T) (hab : g₂ a = g₂ b) (ha : a ∈ U₂) : b ∈ U₂ := by
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback a b hab
    have hz : z ∈ pullback.fst g₂ g₂ ⁻¹' (U₂ : Set T) := by
      rw [Set.mem_preimage, hz₁]
      exact ha
    change z ∈ (self g₂).q₁ ⁻¹' (U₂ : Set T) at hz
    rw [hstab] at hz
    change pullback.snd g₂ g₂ z ∈ (U₂ : Set T) at hz
    rwa [hz₂] at hz
  have : QuasiCompact g₂ := by
    have := isAffineHom_of_isAffine g₂
    infer_instance
  have hpre : g₂ ⁻¹' (g₂ '' (U₂ : Set T)) = U₂ :=
    Set.Subset.antisymm (fun b ⟨a, ha, hab⟩ ↦ hsat a b hab ha) (Set.subset_preimage_image _ _)
  let W₂ : W.toScheme.Opens := ⟨g₂ '' U₂,
    (Flat.isQuotientMap_of_surjective g₂).isOpen_preimage.mp (by rw [hpre]; exact U₂.isOpen)⟩
  have hW₂ : W.ι ''ᵁ W₂ ≤ W := Scheme.Opens.ι_image_le W W₂
  refine ⟨W.ι ''ᵁ W₂, ?_, ?_⟩
  · change W.ι ⟨x, hxW⟩ ∈ W.ι ''ᵁ W₂
    rw [Scheme.Hom.apply_mem_image_iff]
    exact ⟨y, hys₂, hy⟩
  have hc : pullback.fst τ τ ≫ g₂ = pullback.snd τ τ ≫ g₂ := by
    rw [← cancel_mono W.ι, Category.assoc, Category.assoc, ← hτg, pullback.condition_assoc]
  have hV : ∀ z ∈ s.h ⁻¹ᵁ (W.ι ''ᵁ W₂), ∃ w, τ w = z := fun z hz ↦ by
    obtain ⟨w, hw⟩ := τ₀.surjective ⟨z, hW₂ hz⟩
    exact ⟨w, by rw [hτdef, Scheme.Hom.comp_apply, hw]; rfl⟩
  have hV'' : ∀ z ∈ D.q₁ ⁻¹ᵁ s.h ⁻¹ᵁ (W.ι ''ᵁ W₂), ∃ w, τ'' w = z := fun z hz ↦ by
    have := hm₁
    obtain ⟨w, hw⟩ := m.surjective (Hres.isoPullback.hom ⟨z, hW₂ hz⟩)
    refine ⟨w, ?_⟩
    simp only [τ'', Scheme.Hom.comp_apply, hw, Scheme.hom_inv_apply]
    rfl
  have hloc : τ ⁻¹ᵁ s.h ⁻¹ᵁ (W.ι ''ᵁ W₂) ≤ U₂ := fun z hz ↦ by
    have e : s.h (τ z) = W.ι (g₂ z) := by
      rw [← Scheme.Hom.comp_apply, hτg, Scheme.Hom.comp_apply]
    change s.h (τ z) ∈ W.ι ''ᵁ W₂ at hz
    rw [e, Scheme.Hom.apply_mem_image_iff] at hz
    change z ∈ (U₂ : Set T)
    rw [← hpre]
    exact hz
  exact E.nonempty_trivialization h₁ h₂ (pullback.lift _ _ hc) (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _) hV hV'' hinv hloc

end LocalTrivialization

end DescentDatum

open DescentDatum in
/-- VIII.7.8: a faithfully flat quasi-compact `g : S' ⟶ S` is an effective descent morphism for
schemes endowed with a relatively ample line bundle. Given a descent datum `D` on `X' ⟶ S'` and a
line bundle `L'` on `X'`, ample relative to `S'`, with a descent datum `E` relative to `D`: `D` is
effective (`LineBundleDatum.isEffective`), `L'` descends to a line bundle `L` on the descended
scheme `X`, with an isomorphism `h*L ≅ L'` compatible with `E`
(`LineBundleDatum.exists_trivialization`, `LineBundleDatum.exists_iso_isCompatible`), and `L` is
ample relative to `S` (VIII.5.8, `isRelativelyAmple_of_isRelativelyAmple_pullback`). -/
theorem effectiveOfRelativelyAmpleStatement : EffectiveOfRelativelyAmpleStatement.{u} := by
  intro S S' g _ _ _ D L' E hL
  obtain ⟨s⟩ := D.isEffective_iff_nonempty_solution.mp (E.isEffective hL)
  choose W hxW t using fun x : s.X ↦ E.exists_trivialization s x
  obtain ⟨L, ψ, hψ⟩ := E.exists_iso_isCompatible (fun x ↦ (t x).some) hxW
  refine ⟨s.X, s.f, s.h, s.q₁_h, s.isPullback, L, ψ, hψ, ?_⟩
  have := hL.1
  have hLh : (L.pullback s.h).IsRelativelyAmple D.a := hL.of_iso ψ.symm
  have : QuasiCompact s.f := MorphismProperty.of_isPullback_of_descendsAlong
    (P := @QuasiCompact) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) s.isPullback.flip
    ⟨⟨‹_›, ‹_›⟩, ‹_›⟩ ‹_›
  refine isRelativelyAmple_of_isRelativelyAmple_pullback s.f g ?_
  have H : IsPullback s.isPullback.isoPullback.inv (pullback.snd s.f g) D.a (𝟙 S') :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := hLh.of_isPullback H
  rwa [← Scheme.LineBundle.pullback_comp, IsPullback.isoPullback_inv_fst] at this

end SGA.SGA1.ExposeVIII
