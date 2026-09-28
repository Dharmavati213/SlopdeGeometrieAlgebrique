/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.QuasiCoherent.DescentChart

/-!
# Quasi-coherence of descended modules

`isLocalizing_of_equalizer`: on `Spec R`, a module given on sections as the equalizer of two
morphisms between localizing (i.e. quasi-coherent) modules is localizing. For an affine chart
`h : Spec B ⟶ S'` over `j : Spec A ⟶ S` we define the morphisms `mapΨ : j^* M ⟶ φ_* h^* E` (from
the counit of the descended module `M`) and `mapΘ, mapΞ : φ_* h^* E ⟶ (p₂ ≫ φ)_* (p₂ ≫ h)^* E`
(the two inverse images to `Spec (B ⊗_A B)`, the first one followed by the descent isomorphism).
`mapΨ` is injective on sections (`mapΨ_app_injective`), equalizes `mapΘ` and `mapΞ`
(`mapΨ_comp_mapΘ`), and its global sections are the whole equalizer
(`exists_mapΨ_app_top_eq`). Hence `j^* M` is quasi-coherent
(`AffineChart.isQuasicoherent_pullback_descentModule`), and so is `M` when `g` is faithfully
flat and quasi-compact (`isQuasicoherent_descentModule`, SGA 1 VIII.1.3, Stacks 023T).
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TensorProduct

namespace AlgebraicGeometry

open Scheme.Modules

variable {R : CommRingCat.{u}}

lemma Scheme.Modules.map_leTop_apply (P : (Spec R).Modules) (f : R) (x : Γ(P, ⊤)) :
    ((modulesSpecToSheaf.obj P).obj.map (_root_.PrimeSpectrum.basicOpen f).leTop.op).hom x =
      P.presheaf.map (_root_.PrimeSpectrum.basicOpen f).leTop.op x := rfl

/-- The equalizer of two morphisms between modules on `Spec R` which are localizing (i.e.
quasi-coherent) is localizing, when it is given on sections by a morphism `Ψ` injective on all
sections and surjective onto the equalizer on global sections. -/
theorem isLocalizing_of_equalizer {P F G : (Spec R).Modules} (Ψ : P ⟶ F) (Θ Ξ : F ⟶ G)
    (hΨ : Ψ ≫ Θ = Ψ ≫ Ξ) (hinj : ∀ U : (Spec R).Opens, Function.Injective (Ψ.app U))
    (hsurj : ∀ t : Γ(F, ⊤), Θ.app ⊤ t = Ξ.app ⊤ t → ∃ x, Ψ.app ⊤ x = t)
    (hF : IsLocalizing (modulesSpecToSheaf.obj F)) (hG : IsLocalizing (modulesSpecToSheaf.obj G)) :
    IsLocalizing (modulesSpecToSheaf.obj P) := by
  intro f
  let U : (Spec R).Opens := _root_.PrimeSpectrum.basicOpen f
  have hF' : IsLocalizedModule (.powers f) ((modulesSpecToSheaf.obj F).obj.map U.leTop.op).hom :=
    hF f
  have hG' : IsLocalizedModule (.powers f) ((modulesSpecToSheaf.obj G).obj.map U.leTop.op).hom :=
    hG f
  change IsLocalizedModule (.powers f) ((modulesSpecToSheaf.obj P).obj.map U.leTop.op).hom
  have hΨr (x : Γ(P, ⊤)) : Ψ.app U (P.presheaf.map U.leTop.op x) =
      F.presheaf.map U.leTop.op (Ψ.app ⊤ x) := Hom.app_map Ψ _ x
  have hΘr (x : Γ(F, ⊤)) : Θ.app U (F.presheaf.map U.leTop.op x) =
      G.presheaf.map U.leTop.op (Θ.app ⊤ x) := Hom.app_map Θ _ x
  have hΞr (x : Γ(F, ⊤)) : Ξ.app U (F.presheaf.map U.leTop.op x) =
      G.presheaf.map U.leTop.op (Ξ.app ⊤ x) := Hom.app_map Ξ _ x
  have hcomp (V : (Spec R).Opens) (x : Γ(P, V)) : Θ.app V (Ψ.app V x) = Ξ.app V (Ψ.app V x) := by
    rw [← Hom.comp_app_apply, ← Hom.comp_app_apply, hΨ]
  refine ⟨fun ⟨_, n, hn⟩ ↦ ?_, fun y ↦ ?_, fun {x₁ x₂} h ↦ ?_⟩
  · subst hn
    change IsUnit (algebraMap R _ (f ^ n))
    rw [map_pow]
    exact (P.isUnit_algebraMap_end_of_le_basicOpen f le_rfl).pow n
  · obtain ⟨y', hy'⟩ : ∃ y' : Γ(P, U), y' = y := ⟨y, rfl⟩
    subst hy'
    obtain ⟨⟨n, s⟩, hns⟩ := IsLocalizedModule.surj (.powers f)
      ((modulesSpecToSheaf.obj F).obj.map U.leTop.op).hom (Ψ.app U y')
    obtain ⟨n', hn'⟩ : ∃ n' : Γ(F, ⊤), n' = n := ⟨n, rfl⟩
    subst hn'
    let r : R := (s : R)
    replace hns : r • Ψ.app U y' = F.presheaf.map U.leTop.op n' := hns
    have hδ : G.presheaf.map U.leTop.op (Θ.app ⊤ n' - Ξ.app ⊤ n') = 0 := by
      rw [map_sub, ← hΘr, ← hΞr, ← hns, Hom.app_smul_Spec, Hom.app_smul_Spec, hcomp, sub_self]
    obtain ⟨s', hs'⟩ := IsLocalizedModule.exists_of_eq (S := .powers f)
      (f := ((modulesSpecToSheaf.obj G).obj.map U.leTop.op).hom)
      (x₁ := Θ.app ⊤ n' - Ξ.app ⊤ n') (x₂ := 0) (by
        change G.presheaf.map U.leTop.op _ = G.presheaf.map U.leTop.op 0
        rw [hδ, map_zero])
    let r' : R := (s' : R)
    replace hs' : r' • (Θ.app ⊤ n' - Ξ.app ⊤ n') = r' • 0 := hs'
    rw [smul_zero, smul_sub, sub_eq_zero] at hs'
    obtain ⟨x, hx⟩ := hsurj (r' • n') (by rw [Hom.app_smul_Spec, Hom.app_smul_Spec]; exact hs')
    refine ⟨⟨x, s' * s⟩, hinj U ?_⟩
    change Ψ.app U ((r' * r) • y') = Ψ.app U (P.presheaf.map U.leTop.op x)
    rw [hΨr, hx, Hom.app_smul_Spec, mul_smul, hns, map_smul_Spec]
  · obtain ⟨x₁', hx₁'⟩ : ∃ x : Γ(P, ⊤), x = x₁ := ⟨x₁, rfl⟩
    obtain ⟨x₂', hx₂'⟩ : ∃ x : Γ(P, ⊤), x = x₂ := ⟨x₂, rfl⟩
    subst hx₁' hx₂'
    have h' : F.presheaf.map U.leTop.op (Ψ.app ⊤ x₁') = F.presheaf.map U.leTop.op (Ψ.app ⊤ x₂') :=
      (hΨr x₁').symm.trans ((congrArg (Ψ.app U) h).trans (hΨr x₂'))
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := .powers f)
      (f := ((modulesSpecToSheaf.obj F).obj.map U.leTop.op).hom) h'
    let r : R := (s : R)
    replace hs : r • Ψ.app ⊤ x₁' = r • Ψ.app ⊤ x₂' := hs
    refine ⟨s, hinj ⊤ ?_⟩
    change Ψ.app ⊤ (r • x₁') = Ψ.app ⊤ (r • x₂')
    rw [Hom.app_smul_Spec, Hom.app_smul_Spec]
    exact hs


namespace Scheme.Modules.AffineChart

variable {S S' : Scheme.{u}} {g : S' ⟶ S} {A : CommRingCat.{u}} {j : Spec A ⟶ S}
  (c : AffineChart g j) (D : pseudofunctorCat.DescentData (fun _ : Unit ↦ g))

lemma _root_.AlgebraicGeometry.Scheme.Modules.presheaf_map_subsingleton {X : Scheme.{u}}
    (P : X.Modules) {U V : X.Opens} (a b : U ⟶ V) (x : Γ(P, V)) :
    P.presheaf.map a.op x = P.presheaf.map b.op x := by
  rw [Subsingleton.elim a b]

/-- `φ_* h^* E` on `Spec A`. -/
noncomputable abbrev modF : (Spec A).Modules :=
  (Scheme.Modules.pushforward (Spec.map c.φ)).obj ((Scheme.Modules.pullback c.h).obj (descentObj D))

/-- `(Spec (B ⊗_A B) ⟶ Spec A)_* (p₂ ≫ h)^* E` on `Spec A`. -/
noncomputable abbrev modG : (Spec A).Modules :=
  (Scheme.Modules.pushforward (c.p₂ ≫ Spec.map c.φ)).obj
    ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D))

/-- The second inverse image `φ_* h^* E ⟶ (p₂ ≫ φ)_* (p₂ ≫ h)^* E`. -/
noncomputable def mapΞ : c.modF D ⟶ c.modG D :=
  (Scheme.Modules.pushforward (Spec.map c.φ)).map
      ((pullbackPushforwardAdjunction c.p₂).unit.app _) ≫
    (pushforwardComp c.p₂ (Spec.map c.φ)).hom.app _ ≫
    (Scheme.Modules.pushforward (c.p₂ ≫ Spec.map c.φ)).map
      (pullbackCompIso' c.p₂ c.h (c.p₂ ≫ c.h) rfl _).inv

/-- The first inverse image followed by the descent isomorphism. -/
noncomputable def mapΘ : c.modF D ⟶ c.modG D :=
  (Scheme.Modules.pushforward (Spec.map c.φ)).map
      ((pullbackPushforwardAdjunction c.p₁).unit.app _) ≫
    (pushforwardComp c.p₁ (Spec.map c.φ)).hom.app _ ≫
    (Scheme.Modules.pushforward (c.p₁ ≫ Spec.map c.φ)).map
      ((pullbackCompIso' c.p₁ c.h (c.p₁ ≫ c.h) rfl _).inv ≫
        descentHom D (c.p₁ ≫ c.h) (c.p₂ ≫ c.h) c.p_comp_h_comp) ≫
    (pushforwardCongr c.p₁_comp_SpecMap).hom.app _

lemma mapΞ_app (U : (Spec A).Opens) (t : Γ(c.modF D, U)) :
    (c.mapΞ D).app U t = (pullbackCompIso' c.p₂ c.h (c.p₂ ≫ c.h) rfl _).inv.app _
        (pullbackApp c.p₂ _ (Spec.map c.φ ⁻¹ᵁ U) t) :=
  rfl

lemma mapΘ_app (U : (Spec A).Opens) (t : Γ(c.modF D, U))
    (hU : c.p₂ ⁻¹ᵁ Spec.map c.φ ⁻¹ᵁ U ≤ c.p₁ ⁻¹ᵁ Spec.map c.φ ⁻¹ᵁ U) :
    (c.mapΘ D).app U t = ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D)).presheaf.map
      (homOfLE hU).op ((descentHom D (c.p₁ ≫ c.h) (c.p₂ ≫ c.h) c.p_comp_h_comp).app _
        ((pullbackCompIso' c.p₁ c.h (c.p₁ ≫ c.h) rfl _).inv.app _
          (pullbackApp c.p₁ _ (Spec.map c.φ ⁻¹ᵁ U) t))) := by
  exact presheaf_map_subsingleton _ (eqToHom (by
    change (c.p₂ ≫ Spec.map c.φ) ⁻¹ᵁ U = (c.p₁ ≫ Spec.map c.φ) ⁻¹ᵁ U
    rw [c.p₁_comp_SpecMap])) (homOfLE hU) _

/-- `(φ ≫ j)^* M ⟶ h^* E` induced by the counit, for the descended module `M`. -/
noncomputable def mapT : (Scheme.Modules.pullback (Spec.map c.φ)).obj
      ((Scheme.Modules.pullback j).obj (descentModule D)) ⟶
    (Scheme.Modules.pullback c.h).obj (descentObj D) :=
  (pullbackCompIso' (Spec.map c.φ) j (Spec.map c.φ ≫ j) rfl (descentModule D)).inv ≫
    (pullbackCompIso' c.h g (Spec.map c.φ ≫ j) c.comm (descentModule D)).hom ≫
    (Scheme.Modules.pullback c.h).map (descentCounit D)

/-- The comparison `j^* M ⟶ φ_* h^* E`. -/
noncomputable def mapΨ : (Scheme.Modules.pullback j).obj (descentModule D) ⟶ c.modF D :=
  (pullbackPushforwardAdjunction (Spec.map c.φ)).homEquiv _ _ (c.mapT D)

lemma mapΨ_app (U : (Spec A).Opens) (x : Γ((Scheme.Modules.pullback j).obj (descentModule D), U)) :
    (c.mapΨ D).app U x = (c.mapT D).app _ (pullbackApp (Spec.map c.φ) _ U x) := by
  rw [mapΨ, Adjunction.homEquiv_unit]
  rfl

lemma _root_.AlgebraicGeometry.Scheme.Modules.pullbackCompIso'_rfl_hom_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (W : Z.Opens) (y : Γ(M, W)) :
    (pullbackCompIso' f g (f ≫ g) rfl M).hom.app _ (pullbackApp (f ≫ g) M W y) =
      pullbackApp f _ _ (pullbackApp g M W y) := by
  rw [pullbackApp_comp]
  change ((pullbackComp f g).inv.app M).app _ (((pullbackComp f g).hom.app M).app _ _) = _
  exact natIso_inv_app_hom_app (pullbackComp f g) M _ _

end Scheme.Modules.AffineChart

namespace Scheme.Modules.AffineChart

variable {S S' : Scheme.{u}} {g : S' ⟶ S} {A : CommRingCat.{u}} {j : Spec A ⟶ S}
  (c : AffineChart g j) (D : pseudofunctorCat.DescentData (fun _ : Unit ↦ g))

lemma mapΨ_pullbackApp (W : S.Opens) (m : Γ(descentModule D, W))
    (hle : Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W) ≤ c.h ⁻¹ᵁ (g ⁻¹ᵁ W)) :
    (c.mapΨ D).app (j ⁻¹ᵁ W) (pullbackApp j _ W m) =
      ((Scheme.Modules.pullback c.h).obj (descentObj D)).presheaf.map (homOfLE hle).op
        (pullbackApp c.h (descentObj D) (g ⁻¹ᵁ W) m.1) := by
  have e := pullbackCompIso'_rfl_hom_app (Spec.map c.φ) j (descentModule D) W m
  have e₂ := pullbackCompIso'_hom_app_pullbackApp c.h g (Spec.map c.φ ≫ j) c.comm
    (descentModule D) W hle m
  have h1 : (c.mapT D).app (Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W))
      ((pullbackCompIso' (Spec.map c.φ) j (Spec.map c.φ ≫ j) rfl (descentModule D)).hom.app
        ((Spec.map c.φ ≫ j) ⁻¹ᵁ W) (pullbackApp (Spec.map c.φ ≫ j) _ W m)) =
      ((Scheme.Modules.pullback c.h).map (descentCounit D)).app (Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W))
        ((pullbackCompIso' c.h g (Spec.map c.φ ≫ j) c.comm (descentModule D)).hom.app
          ((Spec.map c.φ ≫ j) ⁻¹ᵁ W) (pullbackApp (Spec.map c.φ ≫ j) _ W m)) :=
    congrArg (fun y ↦ ((Scheme.Modules.pullback c.h).map (descentCounit D)).app
      (Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W))
      ((pullbackCompIso' c.h g (Spec.map c.φ ≫ j) c.comm (descentModule D)).hom.app
        ((Spec.map c.φ ≫ j) ⁻¹ᵁ W) y))
      (iso_inv_app_hom_app (pullbackCompIso' (Spec.map c.φ) j (Spec.map c.φ ≫ j) rfl
        (descentModule D)) ((Spec.map c.φ ≫ j) ⁻¹ᵁ W) (pullbackApp (Spec.map c.φ ≫ j) _ W m))
  have h2 := congrArg (((Scheme.Modules.pullback c.h).map (descentCounit D)).app
    (Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W))) e₂
  have h3 : ((Scheme.Modules.pullback c.h).map (descentCounit D)).app (Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W))
      (((Scheme.Modules.pullback c.h).obj ((Scheme.Modules.pullback g).obj
        (descentModule D))).presheaf.map (homOfLE hle).op
        (pullbackApp c.h _ (g ⁻¹ᵁ W) (pullbackApp g _ W m))) =
      ((Scheme.Modules.pullback c.h).obj (descentObj D)).presheaf.map (homOfLE hle).op
        (pullbackApp c.h (descentObj D) (g ⁻¹ᵁ W) m.1) := by
    rw [Hom.app_map, ← pullbackApp_naturality, descentCounit_app_pullbackApp]
  rw [mapΨ_app, ← e]
  exact h1.trans (h2.trans h3)

lemma mapΨ_app_injective [IsOpenImmersion j] (U : (Spec A).Opens) :
    Function.Injective ((c.mapΨ D).app U) := by
  have := c.isLocalIso
  let W : S.Opens := j ''ᵁ U
  have hjW : j ⁻¹ᵁ W = U := j.preimage_image_eq U
  have hle : Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W) ≤ c.h ⁻¹ᵁ (g ⁻¹ᵁ W) := by
    change (Spec.map c.φ ≫ j) ⁻¹ᵁ W ≤ (c.h ≫ g) ⁻¹ᵁ W
    rw [c.comm]
  have heq : Spec.map c.φ ⁻¹ᵁ U = c.h ⁻¹ᵁ (g ⁻¹ᵁ W) := by
    change Spec.map c.φ ⁻¹ᵁ U = (c.h ≫ g) ⁻¹ᵁ W
    rw [c.comm, Scheme.Hom.comp_preimage, hjW]
  let r : Γ((Scheme.Modules.pullback j).obj (descentModule D), j ⁻¹ᵁ W) ⟶
      Γ((Scheme.Modules.pullback j).obj (descentModule D), U) :=
    ((Scheme.Modules.pullback j).obj (descentModule D)).presheaf.map (homOfLE hjW.ge).op
  have hr : Function.Bijective r :=
    ((Scheme.Modules.pullback j).obj (descentModule D)).presheaf.map_bijective_of_eq _ hjW.symm
  have hj :=
    pullbackApp_bijective_of_isOpenImmersion j (descentModule D) W (j.image_le_opensRange U)
  refine Function.Injective.of_comp_right (g := r ∘ pullbackApp j (descentModule D) W) ?_
    (hr.2.comp hj.2)
  have e (m : Γ(descentModule D, W)) : (c.mapΨ D).app U (r (pullbackApp j _ W m)) =
      ((Scheme.Modules.pullback c.h).obj (descentObj D)).presheaf.map (homOfLE heq.le).op
        (pullbackApp c.h (descentObj D) (g ⁻¹ᵁ W) m.1) := by
    change (c.mapΨ D).app U (((Scheme.Modules.pullback j).obj (descentModule D)).presheaf.map
      (homOfLE hjW.ge).op (pullbackApp j _ W m)) = _
    rw [Hom.app_map, mapΨ_pullbackApp c D W m hle, pushforward_obj_presheaf_map]
    exact presheaf_map_map_eq' ((Scheme.Modules.pullback c.h).obj (descentObj D))
      ((TopologicalSpace.Opens.map (Spec.map c.φ).base).map (homOfLE hjW.ge)) (homOfLE hle)
      (homOfLE heq.le) _
  intro m m' hmm'
  simp only [Function.comp_apply] at hmm'
  rw [e, e] at hmm'
  have h₁ := (((Scheme.Modules.pullback c.h).obj (descentObj D)).presheaf.map_bijective_of_eq
    (homOfLE heq.le) heq).1 hmm'
  have h₂ := pullbackApp_injective_of_isLocalIso_of_le c.h (descentObj D) (g ⁻¹ᵁ W)
    (fun x hx ↦ by
      rw [← c.coe_U]
      exact (show (g ⁻¹ᵁ W : S'.Opens) ≤ c.U from fun y hy ↦ j.image_le_opensRange U hy) hx) h₁
  exact Subtype.ext h₂

lemma _root_.AlgebraicGeometry.Scheme.Modules.presheaf_map_id_apply {X : Scheme.{u}}
    (P : X.Modules) (U : X.Opens) (x : Γ(P, U)) : P.presheaf.map (𝟙 U).op x = x := by
  rw [op_id, CategoryTheory.Functor.map_id]; rfl

lemma mapΞ_app_top (t : Γ(c.modF D, ⊤)) : (c.mapΞ D).app ⊤ t = c.pb₂ D t := rfl

lemma mapΘ_app_top (t : Γ(c.modF D, ⊤)) : (c.mapΘ D).app ⊤ t = c.θ D t := by
  have hU : c.p₂ ⁻¹ᵁ Spec.map c.φ ⁻¹ᵁ ⊤ ≤ c.p₁ ⁻¹ᵁ Spec.map c.φ ⁻¹ᵁ ⊤ := fun _ _ ↦ trivial
  rw [mapΘ_app c D ⊤ t hU]
  have e : (homOfLE hU : c.p₂ ⁻¹ᵁ Spec.map c.φ ⁻¹ᵁ ⊤ ⟶ c.p₁ ⁻¹ᵁ Spec.map c.φ ⁻¹ᵁ ⊤) =
      𝟙 (⊤ : (Spec c.C₂).Opens) := Subsingleton.elim _ _
  rw [e]
  exact (presheaf_map_id_apply _ ⊤ _).trans rfl

lemma exists_mapΨ_app_top_eq [IsOpenImmersion j] (t : Γ(c.modF D, ⊤))
    (ht : (c.mapΘ D).app ⊤ t = (c.mapΞ D).app ⊤ t) : ∃ x, (c.mapΨ D).app ⊤ x = t := by
  have hinv : c.IsInvariant D t := by
    change c.θ D t = c.pb₂ D t
    rw [← mapΘ_app_top, ← mapΞ_app_top]
    exact ht
  obtain ⟨y, hy⟩ := c.exists_pullbackAppTop_eq_of_isInvariant D hinv
  have hdesc : IsDescentSection D j.opensRange y :=
    c.isDescentSection_of_isInvariant D y (hy ▸ hinv)
  let y' : Γ(descentModule D, j.opensRange) := ⟨y, hdesc⟩
  have hjR : ⊤ ≤ j ⁻¹ᵁ j.opensRange := fun x _ ↦ ⟨x, rfl⟩
  have hle : Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ j.opensRange) ≤ c.h ⁻¹ᵁ (g ⁻¹ᵁ j.opensRange) := by
    change (Spec.map c.φ ≫ j) ⁻¹ᵁ j.opensRange ≤ (c.h ≫ g) ⁻¹ᵁ j.opensRange
    rw [c.comm]
  refine ⟨((Scheme.Modules.pullback j).obj (descentModule D)).presheaf.map (homOfLE hjR).op
    (pullbackApp j _ _ y'), ?_⟩
  rw [Hom.app_map, mapΨ_pullbackApp c D _ y' hle, pushforward_obj_presheaf_map, ← hy]
  exact presheaf_map_map_eq' ((Scheme.Modules.pullback c.h).obj (descentObj D))
    ((TopologicalSpace.Opens.map (Spec.map c.φ).base).map (homOfLE hjR)) (homOfLE hle)
    (homOfLE c.top_le) _

lemma _root_.AlgebraicGeometry.Scheme.Modules.presheaf_map_map_eq_three {X : Scheme.{u}}
    (P : X.Modules) {U₁ U₂ U₃ U₄ : X.Opens}
    (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) (d : U₃ ⟶ U₄) (e : U₁ ⟶ U₄) (x : Γ(P, U₄)) :
    P.presheaf.map a.op (P.presheaf.map b.op (P.presheaf.map d.op x)) = P.presheaf.map e.op x := by
  rw [presheaf_map_map_eq' P b d (b ≫ d), presheaf_map_map_eq']

lemma _root_.AlgebraicGeometry.Scheme.Modules.pullbackCompIso'_rfl_inv_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (W : Z.Opens) (y : Γ(M, W)) :
    (pullbackCompIso' f g (f ≫ g) rfl M).inv.app _ (pullbackApp f _ _ (pullbackApp g M W y)) =
      pullbackApp (f ≫ g) M W y := by
  rw [← pullbackCompIso'_rfl_hom_app]
  exact iso_inv_app_hom_app _ _ _

lemma mapΞ_mapΨ_pullbackApp (W : S.Opens) (m : Γ(descentModule D, W))
    (hle : Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W) ≤ c.h ⁻¹ᵁ (g ⁻¹ᵁ W)) :
    (c.mapΞ D).app (j ⁻¹ᵁ W) ((c.mapΨ D).app (j ⁻¹ᵁ W) (pullbackApp j _ W m)) =
      ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D)).presheaf.map
        ((TopologicalSpace.Opens.map c.p₂.base).map (homOfLE hle)).op
        (pullbackApp (c.p₂ ≫ c.h) (descentObj D) (g ⁻¹ᵁ W) m.1) := by
  have h1 := congrArg ((c.mapΞ D).app (j ⁻¹ᵁ W)) (mapΨ_pullbackApp c D W m hle)
  refine h1.trans ((c.mapΞ_app D _ _).trans ?_)
  have h2 := pullbackApp_map c.p₂ ((Scheme.Modules.pullback c.h).obj (descentObj D))
    (homOfLE hle) (pullbackApp c.h (descentObj D) (g ⁻¹ᵁ W) m.1)
  have h3 : (pullbackCompIso' c.p₂ c.h (c.p₂ ≫ c.h) rfl _).inv.app _
      (pullbackApp c.p₂ _ (Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W))
        (((Scheme.Modules.pullback c.h).obj (descentObj D)).presheaf.map (homOfLE hle).op
          (pullbackApp c.h (descentObj D) (g ⁻¹ᵁ W) m.1))) =
      ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D)).presheaf.map
        ((TopologicalSpace.Opens.map c.p₂.base).map (homOfLE hle)).op
        (pullbackApp (c.p₂ ≫ c.h) (descentObj D) (g ⁻¹ᵁ W) m.1) := by
    rw [h2, Hom.app_map]
    exact congrArg _ (pullbackCompIso'_rfl_inv_app c.p₂ c.h (descentObj D) (g ⁻¹ᵁ W) m.1)
  exact h3

lemma mapΘ_mapΨ_pullbackApp (W : S.Opens) (m : Γ(descentModule D, W))
    (hle : Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W) ≤ c.h ⁻¹ᵁ (g ⁻¹ᵁ W))
    (hU : c.p₂ ⁻¹ᵁ Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W) ≤ c.p₁ ⁻¹ᵁ Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W)) :
    (c.mapΘ D).app (j ⁻¹ᵁ W) ((c.mapΨ D).app (j ⁻¹ᵁ W) (pullbackApp j _ W m)) =
      ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D)).presheaf.map
        ((TopologicalSpace.Opens.map c.p₂.base).map (homOfLE hle)).op
        (pullbackApp (c.p₂ ≫ c.h) (descentObj D) (g ⁻¹ᵁ W) m.1) := by
  have h1 := congrArg ((c.mapΘ D).app (j ⁻¹ᵁ W)) (mapΨ_pullbackApp c D W m hle)
  refine h1.trans ((c.mapΘ_app D _ _ hU).trans ?_)
  have h2 := pullbackApp_map c.p₁ ((Scheme.Modules.pullback c.h).obj (descentObj D))
    (homOfLE hle) (pullbackApp c.h (descentObj D) (g ⁻¹ᵁ W) m.1)
  have h3 : (pullbackCompIso' c.p₁ c.h (c.p₁ ≫ c.h) rfl _).inv.app _
      (pullbackApp c.p₁ _ (Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W))
        (((Scheme.Modules.pullback c.h).obj (descentObj D)).presheaf.map (homOfLE hle).op
          (pullbackApp c.h (descentObj D) (g ⁻¹ᵁ W) m.1))) =
      ((Scheme.Modules.pullback (c.p₁ ≫ c.h)).obj (descentObj D)).presheaf.map
        ((TopologicalSpace.Opens.map c.p₁.base).map (homOfLE hle)).op
        (pullbackApp (c.p₁ ≫ c.h) (descentObj D) (g ⁻¹ᵁ W) m.1) := by
    rw [h2, Hom.app_map]
    exact congrArg _ (pullbackCompIso'_rfl_inv_app c.p₁ c.h (descentObj D) (g ⁻¹ᵁ W) m.1)
  rw [h3]
  have h4 := Hom.app_map (descentHom D (c.p₁ ≫ c.h) (c.p₂ ≫ c.h) c.p_comp_h_comp)
    ((TopologicalSpace.Opens.map c.p₁.base).map (homOfLE hle))
    (pullbackApp (c.p₁ ≫ c.h) (descentObj D) (g ⁻¹ᵁ W) m.1)
  have h5 := isDescentSection_coe D W m (c.p₁ ≫ c.h) (c.p₂ ≫ c.h) c.p_comp_h_comp
  refine (congrArg (((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D)).presheaf.map
    (homOfLE hU).op) (h4.trans (congrArg _ h5))).trans ?_
  exact presheaf_map_map_eq_three _ _ _ _ _ _

lemma le_of_comm (W : S.Opens) : Spec.map c.φ ⁻¹ᵁ (j ⁻¹ᵁ W) ≤ c.h ⁻¹ᵁ (g ⁻¹ᵁ W) := by
  change (Spec.map c.φ ≫ j) ⁻¹ᵁ W ≤ (c.h ≫ g) ⁻¹ᵁ W
  rw [c.comm]

lemma p₂_le_p₁ (U : (Spec A).Opens) :
    c.p₂ ⁻¹ᵁ Spec.map c.φ ⁻¹ᵁ U ≤ c.p₁ ⁻¹ᵁ Spec.map c.φ ⁻¹ᵁ U := by
  change (c.p₂ ≫ Spec.map c.φ) ⁻¹ᵁ U ≤ (c.p₁ ≫ Spec.map c.φ) ⁻¹ᵁ U
  rw [c.p₁_comp_SpecMap]

/-- The key identity `Θ ∘ Ψ = Ξ ∘ Ψ`: sections of `j^* M` are descent-compatible. -/
lemma mapΨ_comp_mapΘ : c.mapΨ D ≫ c.mapΘ D = c.mapΨ D ≫ c.mapΞ D := by
  apply ((pullbackPushforwardAdjunction j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext W x
  rw [Hom.comp_app_apply, Hom.comp_app_apply, pushforward_map_app, pushforward_map_app]
  change (c.mapΘ D).app (j ⁻¹ᵁ W) ((c.mapΨ D).app (j ⁻¹ᵁ W) (pullbackApp j _ W x)) =
    (c.mapΞ D).app (j ⁻¹ᵁ W) ((c.mapΨ D).app (j ⁻¹ᵁ W) (pullbackApp j _ W x))
  rw [mapΘ_mapΨ_pullbackApp c D W x (c.le_of_comm W) (c.p₂_le_p₁ _),
    mapΞ_mapΨ_pullbackApp c D W x (c.le_of_comm W)]

lemma isLocalizing_modF [(descentObj D).IsQuasicoherent] :
    IsLocalizing (modulesSpecToSheaf.obj (c.modF D)) := by
  refine isLocalizing_pushforward_of_isLocalizing c.φ ?_
  rw [← isIso_fromTildeΓ_iff_isLocalizing]
  infer_instance

lemma isLocalizing_modG [(descentObj D).IsQuasicoherent] :
    IsLocalizing (modulesSpecToSheaf.obj (c.modG D)) := by
  have e : Spec.map (c.φ ≫ c.inr) = c.p₂ ≫ Spec.map c.φ := Spec.map_comp _ _
  refine isLocalizing_of_iso (modulesSpecToSheaf.mapIso ((pushforwardCongr e).app _)) ?_
  refine isLocalizing_pushforward_of_isLocalizing (c.φ ≫ c.inr) ?_
  rw [← isIso_fromTildeΓ_iff_isLocalizing]
  infer_instance

include c in
/-- VIII.1.3, affine-local form: the descended module is quasi-coherent over the chart. -/
theorem isQuasicoherent_pullback_descentModule [IsOpenImmersion j]
    [(descentObj D).IsQuasicoherent] :
    ((Scheme.Modules.pullback j).obj (descentModule D)).IsQuasicoherent := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ, isIso_fromTildeΓ_iff_isLocalizing]
  exact isLocalizing_of_equalizer (c.mapΨ D) (c.mapΘ D) (c.mapΞ D) (c.mapΨ_comp_mapΘ D)
    (c.mapΨ_app_injective D) (c.exists_mapΨ_app_top_eq D) (c.isLocalizing_modF D)
    (c.isLocalizing_modG D)

end Scheme.Modules.AffineChart

namespace Scheme.Modules

variable {S S' : Scheme.{u}} {g : S' ⟶ S} (D : pseudofunctorCat.DescentData (fun _ : Unit ↦ g))

/-- VIII.1.3: the module obtained by descent of a quasi-coherent module along a faithfully flat
quasi-compact morphism is quasi-coherent. -/
theorem isQuasicoherent_descentModule [Flat g] [Surjective g] [QuasiCompact g]
    [(descentObj D).IsQuasicoherent] : (descentModule D).IsQuasicoherent := by
  have : ∀ V : S.affineOpens, IsOpenImmersion ((fun V : S.affineOpens ↦ V.2.fromSpec) V) :=
    fun V ↦ V.2.isOpenImmersion_fromSpec
  refine isQuasicoherent_of_forall_pullback (fun V : S.affineOpens ↦ V.2.fromSpec) ?_ ?_
  · intro x
    obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
      (show x ∈ (⊤ : S.Opens) from trivial)
    exact ⟨⟨V, hV⟩, by rw [hV.range_fromSpec]; exact hxV⟩
  · intro V
    exact (AffineChart.nonempty (g := g) V.2.fromSpec).some.isQuasicoherent_pullback_descentModule D

end Scheme.Modules

end AlgebraicGeometry
