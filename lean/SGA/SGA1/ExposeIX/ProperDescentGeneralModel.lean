/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Limits.FibrePropertiesDescent
import SGA.Foundations.Limits.PropertiesLimitProper
import SGA.SGA1.ExposeIX.ProperDescentGeneralAct

/-!
# SGA 1, Exposé IX, 6.7: noetherian models and actions over a local ring

Let `f : X ⟶ S` be proper, of finite presentation, with geometrically connected fibres, `Y` an
étale covering of `X` which is geometrically trivial on the fibre `X_s`. We show that `Y` carries
an action (a descent datum in the form of IX.4) over `Spec 𝒪_{S,s}`, without assuming `S`
noetherian (`exists_isActAt_fromSpecStalk_of_locallyOfFinitePresentation`). This is the step of
IX.6.7 where SGA reduces to a noetherian base by EGA IV 8:

1. `ProperFEtModel`, `nonempty_properFEtModel`: over `Spec A` (any ring `A`), a proper morphism of
   finite presentation `X' ⟶ Spec A` with an étale covering `Y'` is the base change of a proper
   `X₂ ⟶ Spec B` with an étale covering `Y₂`, for some noetherian ring `B` (the proof takes
   `B ⊆ A` of finite type over `ℤ`; the structure records only that `B` is noetherian)
   (EGA IV 8.8.2, 8.10.5 (xii), 17.7.8:
   `Scheme.exists_isPullback_of_isLimit_of_locallyOfFinitePresentation`,
   `Scheme.limitDescends_isProper_of_isNoetherian`,
   `Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale`).
2. For `A = 𝒪_{S,s}`, `t₀ ∈ Spec B` the image of the closed point and `Â` the completion of
   `𝒪_{Spec B, t₀}`: `Y₂` is geometrically trivial on the closed fibre of `X₂ ×_B Â`
   (`ProperFEtModel.isGeometricallyTrivial_closedFibre`). The closed fibre `Z` lives over
   `κ(t₀)`, whereas the hypothesis is over `κ(s)`; a field `K` containing both (a residue field of
   `Spec κ(t₀) ×_B Spec κ(s)`) is used: `Z_K = X ×_S Spec K`, and geometric triviality and geometric
   connectedness descend from `K` to `κ(t₀)` (`mem_essImage_of_isPullback_of_fpqc`,
   `GeometricallyConnected.of_pullback_snd`).
3. By IX.1.10 over `Â` (`mem_essImage_iff_isGeometricallyTrivial_closedFibre`), `Y₂` comes from
   `Spec Â`; after base change to `T' = Spec A ×_B Spec Â`, flat, surjective and quasi-compact over
   `Spec A`, so does `Y`, hence `Y` carries an action over `T'`, which descends to `Spec A`
   (`exists_isActAt_of_fpqc`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MorphismProperty

namespace SGA.SGA1.ExposeIX

local notation "FEt" => (SGA.SGA1.ExposeV.finiteEtaleHom : MorphismProperty Scheme)
local notation "pb" => MorphismProperty.Over.pullback FEt ⊤

/-- A noetherian model of a proper morphism `q : X' ⟶ Spec A` with an étale covering `Y'` of
`X'`: a noetherian ring `B`, `π : Spec A ⟶ Spec B`, a proper `f₂ : X₂ ⟶ Spec B` with
`X' = X₂ ×_B Spec A`, and an étale covering `Y₂` of `X₂` with `Y' ≅ Y₂ ×_{X₂} X'`. -/
structure ProperFEtModel {A : CommRingCat.{u}} {X' : Scheme.{u}} (q : X' ⟶ Spec A)
    (Y' : MorphismProperty.Over FEt ⊤ X') where
  /-- The noetherian ring `B`. -/
  B : CommRingCat.{u}
  isNoetherianRing : IsNoetherianRing B
  /-- The morphism `Spec A ⟶ Spec B`. -/
  π : Spec A ⟶ Spec B
  /-- The model `X₂` of `X'`. -/
  X₂ : Scheme.{u}
  /-- The structure morphism `X₂ ⟶ Spec B`. -/
  f₂ : X₂ ⟶ Spec B
  isProper : IsProper f₂
  /-- The projection `X' ⟶ X₂`. -/
  e₂ : X' ⟶ X₂
  isPullback : IsPullback e₂ q f₂ π
  /-- The model `Y₂` of `Y'`. -/
  Y₂ : MorphismProperty.Over FEt ⊤ X₂
  /-- `Y' ≅ Y₂ ×_{X₂} X'`. -/
  iso : Y' ≅ (pb e₂).obj Y₂

attribute [instance] ProperFEtModel.isNoetherianRing ProperFEtModel.isProper

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2 (ii), 8.10.5 (xii) and 17.7.8: a proper morphism of finite presentation
`q : X' ⟶ Spec A` with an étale covering `Y'` of `X'` has a noetherian model: it is the base change
of a proper morphism with an étale covering over `Spec B` for a noetherian ring `B`. (The proof
takes `B ⊆ A` of finite type over `ℤ`; `ProperFEtModel` records only that `B` is noetherian.) -/
theorem nonempty_properFEtModel {A : CommRingCat.{u}} {X' : Scheme.{u}} (q : X' ⟶ Spec A)
    [IsProper q] [LocallyOfFinitePresentation q] (Y' : MorphismProperty.Over FEt ⊤ X') :
    Nonempty (ProperFEtModel q Y') := by
  let D := Algebra.FGSubalgebra.schemeDiagram ℤ A
  let cD := Algebra.FGSubalgebra.specCone ℤ A
  have hcD : IsLimit cD := Algebra.FGSubalgebra.isLimitSpecCone ℤ A
  let q' : X' ⟶ cD.pt := q
  have : IsProper q' := ‹IsProper q›
  have : LocallyOfFinitePresentation q' := ‹LocallyOfFinitePresentation q›
  -- the morphism descends (EGA IV 8.8.2 (ii)) and is proper at a lower level (8.10.5 (xii))
  obtain ⟨B₀, X₀, f₀, e₀, _, _, _, h₀⟩ :=
    Scheme.exists_isPullback_of_isLimit_of_locallyOfFinitePresentation hcD q'
  obtain ⟨B₁, g₁, hp⟩ := Scheme.limitDescends_isProper_of_isNoetherian hcD f₀ h₀
  let M₀ : Scheme.LimitModel cD q' B₀ := { obj := X₀, hom := f₀, proj := e₀, isPullback := h₀ }
  let M₁ := M₀.lower g₁
  have : IsProper M₁.hom := hp
  -- the étale covering descends (EGA IV 17.7.8) over the diagram `k ↦ X₁ ×_{B₁} Spec B_k`
  let c' := Scheme.baseChangeCone M₁.isPullback
  have hc' : IsLimit c' := Scheme.isLimitBaseChangeCone hcD M₁.isPullback
  have (k : Over B₁) : CompactSpace ((Scheme.baseChangeDiagram D M₁.hom).obj k) :=
    Scheme.compactSpace_baseChangeDiagram M₁.hom k
  have (k : Over B₁) : QuasiSeparatedSpace ((Scheme.baseChangeDiagram D M₁.hom).obj k) :=
    Scheme.quasiSeparatedSpace_baseChangeDiagram M₁.hom k
  have : IsFinite Y'.hom := Y'.prop.1
  have : Etale Y'.hom := Y'.prop.2
  obtain ⟨l, Yl, ql, eY, hfin, het, hY⟩ :=
    Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale hc' (Y'.hom : Y'.left ⟶ c'.pt)
  have hfY : FEt ql := ⟨hfin, het⟩
  exact ⟨{
    B := CommRingCat.of l.left.unop.1
    isNoetherianRing := inferInstanceAs (IsNoetherianRing l.left.unop.1)
    π := cD.π.app l.left
    X₂ := (Scheme.baseChangeDiagram D M₁.hom).obj l
    f₂ := pullback.snd M₁.hom (D.map l.hom)
    isProper := MorphismProperty.pullback_snd _ _ inferInstance
    e₂ := c'.π.app l
    isPullback := Scheme.isPullback_baseChangeCone M₁.isPullback l
    Y₂ := MorphismProperty.Over.mk ⊤ ql hfY
    iso := MorphismProperty.Over.isoMk hY.isoPullback hY.isoPullback_hom_snd }⟩

section Model

variable {X S : Scheme.{u}} {f : X ⟶ S} {s : S} {Y : MorphismProperty.Over FEt ⊤ X}

namespace ProperFEtModel

variable (M : ProperFEtModel (pullback.snd f (S.fromSpecStalk s))
  ((pb (pullback.fst f (S.fromSpecStalk s))).obj Y))

/-- The image `t₀ ∈ Spec B` of the closed point of `Spec 𝒪_{S,s}`. -/
noncomputable abbrev closedPt : Spec M.B := M.π (IsLocalRing.closedPoint (S.presheaf.stalk s))

/-- The completed local ring `Â` of `Spec B` at `t₀`. -/
noncomputable abbrev Compl : Type u :=
  AdicCompletion (IsLocalRing.maximalIdeal ((Spec M.B).presheaf.stalk M.closedPt))
    ((Spec M.B).presheaf.stalk M.closedPt)

/-- `Spec Â ⟶ Spec B`. -/
noncomputable abbrev compl : Spec (.of M.Compl) ⟶ Spec M.B :=
  fromSpecCompletedStalk (Spec M.B) M.closedPt

set_option backward.isDefEq.respectTransparency false in
/-- Step 2 of the module docstring: if `Y` is geometrically trivial on the fibre `X_s`, the model
`Y₂` is geometrically trivial on the closed fibre of `X₂ ×_B Spec Â`, hence (IX.1.10 over the
complete local ring `Â`) comes from `Spec Â` after base change to `X₂ ×_B Spec Â`. -/
theorem mem_essImage_compl [IsProper f] [GeometricallyConnected f]
    (hY : IsGeometricallyTrivial (f.fiberToSpecResidueField s) ((pb (f.fiberι s)).obj Y)) :
    (pb (pullback.snd M.f₂ M.compl)).essImage ((pb (pullback.fst M.f₂ M.compl)).obj M.Y₂) := by
  let c := M.compl
  let fO := pullback.snd M.f₂ c
  let V := (pb (pullback.fst M.f₂ c)).obj M.Y₂
  let mh : Spec (.of M.Compl) := IsLocalRing.closedPoint M.Compl
  refine (mem_essImage_iff_isGeometricallyTrivial_closedFibre M.Compl fO V).mpr ?_
  let ι := S.fromSpecStalk s
  -- a field `K` containing `κ(mh)` and `κ(s)` over `B`
  let u₁ := (Spec (.of M.Compl)).fromSpecResidueField mh ≫ c
  let u₂ := Spec.map (S.residue s) ≫ M.π
  have hu : u₁ (IsLocalRing.closedPoint ((Spec (.of M.Compl)).residueField mh)) =
      u₂ (IsLocalRing.closedPoint (S.residueField s)) := by
    have : IsLocalHom (S.residue s).hom := inferInstanceAs (IsLocalHom (IsLocalRing.residue _))
    simp only [u₁, u₂, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    rw [Spec_closedPoint]
    exact fromSpecCompletedStalk_closedPoint (S := Spec M.B) M.closedPt
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hu
  let wK := (pullback u₁ u₂).fromSpecResidueField z
  let aK := wK ≫ pullback.fst u₁ u₂
  let bK := wK ≫ pullback.snd u₁ u₂
  have hab : (aK ≫ (Spec (.of M.Compl)).fromSpecResidueField mh) ≫ c =
      (bK ≫ Spec.map (S.residue s)) ≫ M.π := by
    simp only [aK, bK, Category.assoc]
    exact congrArg (wK ≫ ·) pullback.condition
  -- `Z_K = Z ×_{κ(mh)} K` is `X ×_S Spec K`
  let g := fO.fiberToSpecResidueField mh
  let p := pullback.fst g aK
  let q := pullback.snd g aK
  have hZ : IsPullback (fO.fiberι mh) g fO ((Spec (.of M.Compl)).fromSpecResidueField mh) :=
    IsPullback.of_hasPullback _ _
  have sq₀ : IsPullback ((p ≫ fO.fiberι mh) ≫ pullback.fst M.f₂ c) q M.f₂
      ((aK ≫ (Spec (.of M.Compl)).fromSpecResidueField mh) ≫ c) :=
    ((IsPullback.of_hasPullback g aK).paste_horiz hZ).paste_horiz (IsPullback.of_hasPullback _ _)
  let ℓ : pullback g aK ⟶ pullback f ι :=
    M.isPullback.lift ((p ≫ fO.fiberι mh) ≫ pullback.fst M.f₂ c)
      (q ≫ bK ≫ Spec.map (S.residue s)) (by rw [sq₀.w, hab]; simp only [Category.assoc])
  have hℓ : ℓ ≫ M.e₂ = (p ≫ fO.fiberι mh) ≫ pullback.fst M.f₂ c := IsPullback.lift_fst _ _ _ _
  have sq₁ : IsPullback ℓ q (pullback.snd f ι) (bK ≫ Spec.map (S.residue s)) := by
    refine IsPullback.of_right ?_ (IsPullback.lift_snd _ _ _ _) M.isPullback
    rw [hℓ, ← hab]
    exact sq₀
  have sq₂ : IsPullback (ℓ ≫ pullback.fst f ι) q f (bK ≫ S.fromSpecResidueField s) := by
    have := sq₁.paste_horiz (IsPullback.of_hasPullback f ι)
    rwa [Category.assoc] at this
  -- `Y` is geometrically trivial on `Z_K`
  have h₁ : (pb q).essImage ((pb (ℓ ≫ pullback.fst f ι)).obj Y) :=
    mem_essImage_of_isGeometricallyTrivial f Y s hY (ℓ ≫ pullback.fst f ι) q bK sq₂.w
  let W := (pb (fO.fiberι mh)).obj V
  let e : (pb (ℓ ≫ pullback.fst f ι)).obj Y ≅ (pb p).obj W :=
    (MorphismProperty.Over.pullbackComp ℓ (pullback.fst f ι)).app Y ≪≫ (pb ℓ).mapIso M.iso ≪≫
      ((MorphismProperty.Over.pullbackComp ℓ M.e₂).app M.Y₂).symm ≪≫
        (MorphismProperty.Over.pullbackCongr hℓ).app M.Y₂ ≪≫
          ((MorphismProperty.Over.pullbackCongr (Category.assoc p (fO.fiberι mh)
            (pullback.fst M.f₂ c))).app M.Y₂) ≪≫
          (MorphismProperty.Over.pullbackComp p (fO.fiberι mh ≫ pullback.fst M.f₂ c)).app M.Y₂ ≪≫
            (pb p).mapIso ((MorphismProperty.Over.pullbackComp (fO.fiberι mh)
              (pullback.fst M.f₂ c)).app M.Y₂)
  have h₂ : (pb q).essImage ((pb p).obj W) := Functor.essImage.ofIso e h₁
  -- descent from `K` to `κ(mh)`
  have : GeometricallyConnected q := MorphismProperty.of_isPullback sq₂ ‹GeometricallyConnected f›
  have : Surjective aK := ⟨fun _ ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have : GeometricallyConnected g := GeometricallyConnected.of_pullback_snd g aK
  have : Flat aK := inferInstance
  have : IsAffineHom aK := isAffineHom_of_isAffine aK
  have : IsProper fO := MorphismProperty.pullback_snd _ _ inferInstance
  have : IsProper g := MorphismProperty.pullback_snd _ _ inferInstance
  exact mem_essImage_of_isPullback_of_fpqc g W aK (IsPullback.of_hasPullback g aK) h₂

set_option backward.isDefEq.respectTransparency false in
/-- Step 3 of the module docstring: if the model `Y₂` comes from `Spec Â` after base change to
`X₂ ×_B Spec Â`, then `Y` carries an action over `Spec 𝒪_{S,s}`. Over
`T' = Spec 𝒪_{S,s} ×_B Spec Â`, `Y` comes from the base, hence carries an action, which descends
along the faithfully flat quasi-compact `T' ⟶ Spec 𝒪_{S,s}` (`exists_isActAt_of_fpqc`). -/
theorem exists_isActAt_fromSpecStalk [GeometricallyConnected f]
    (hV : (pb (pullback.snd M.f₂ M.compl)).essImage ((pb (pullback.fst M.f₂ M.compl)).obj M.Y₂)) :
    ∃ e, IsActAt f Y (S.fromSpecStalk s) e := by
  let ι := S.fromSpecStalk s
  let c := M.compl
  let fO := pullback.snd M.f₂ c
  let ρ := pullback.fst M.π c
  let σ := pullback.snd M.π c
  let q' := pullback.snd fO σ
  have hρσ : ρ ≫ M.π = σ ≫ c := pullback.condition
  have sq₀ : IsPullback (pullback.fst fO σ ≫ pullback.fst M.f₂ c) q' M.f₂ (σ ≫ c) :=
    (IsPullback.of_hasPullback fO σ).paste_horiz (IsPullback.of_hasPullback M.f₂ c)
  let ℓ : pullback fO σ ⟶ pullback f ι :=
    M.isPullback.lift (pullback.fst fO σ ≫ pullback.fst M.f₂ c) (q' ≫ ρ)
      (by rw [sq₀.w, Category.assoc, hρσ])
  have hℓ : ℓ ≫ M.e₂ = pullback.fst fO σ ≫ pullback.fst M.f₂ c := IsPullback.lift_fst _ _ _ _
  have sq₁ : IsPullback ℓ q' (pullback.snd f ι) ρ := by
    refine IsPullback.of_right ?_ (IsPullback.lift_snd _ _ _ _) M.isPullback
    rw [hℓ, hρσ]
    exact sq₀
  have sq₂ : IsPullback (ℓ ≫ pullback.fst f ι) q' f (ρ ≫ ι) :=
    sq₁.paste_horiz (IsPullback.of_hasPullback f ι)
  -- over `T'`, `Y` comes from the base
  obtain ⟨W₀, ⟨φ₀⟩⟩ := hV
  let e : (pb (ℓ ≫ pullback.fst f ι)).obj Y ≅ (pb q').obj ((pb σ).obj W₀) :=
    (MorphismProperty.Over.pullbackComp ℓ (pullback.fst f ι)).app Y ≪≫ (pb ℓ).mapIso M.iso ≪≫
      ((MorphismProperty.Over.pullbackComp ℓ M.e₂).app M.Y₂).symm ≪≫
        (MorphismProperty.Over.pullbackCongr hℓ).app M.Y₂ ≪≫
          (MorphismProperty.Over.pullbackComp (pullback.fst fO σ) (pullback.fst M.f₂ c)).app
            M.Y₂ ≪≫ (pb (pullback.fst fO σ)).mapIso φ₀.symm ≪≫
              (fetPullbackCompCongr fO (pullback.fst fO σ) σ q' pullback.condition).app W₀
  obtain ⟨a, ha⟩ := exists_isActAt_of_isPullback f Y (ρ ≫ ι) sq₂ ⟨_, ⟨e.symm⟩⟩
  -- `T' ⟶ Spec 𝒪_{S,s}` is flat, quasi-compact and surjective
  have : Flat c := by
    have := (flat_and_surjective_specMap_completion (S := Spec M.B) M.closedPt).1
    exact inferInstanceAs (Flat (_ ≫ (Spec M.B).fromSpecStalk M.closedPt))
  have : Flat ρ := MorphismProperty.pullback_fst _ _ inferInstance
  have : IsAffineHom ρ := isAffineHom_of_isAffine ρ
  have : Surjective ρ := by
    obtain ⟨z₀, hz₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := M.π) (g := c)
      (IsLocalRing.closedPoint (S.presheaf.stalk s)) (IsLocalRing.closedPoint M.Compl)
      (fromSpecCompletedStalk_closedPoint (S := Spec M.B) M.closedPt).symm
    refine ⟨fun x ↦ ?_⟩
    have hx : x ⤳ ρ z₀ := by
      rw [hz₀, ← PrimeSpectrum.le_iff_specializes]
      exact IsLocalRing.le_maximalIdeal x.2.ne_top
    obtain ⟨x', -, hx'⟩ := Flat.generalizingMap ρ hx
    exact ⟨x', hx'⟩
  exact exists_isActAt_of_fpqc f Y ι ρ ha

end ProperFEtModel

end Model

end SGA.SGA1.ExposeIX
