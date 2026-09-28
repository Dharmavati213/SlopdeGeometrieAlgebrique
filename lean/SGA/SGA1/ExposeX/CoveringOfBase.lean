/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeV.QuotientHasQuotients
import SGA.SGA1.ExposeX.HomotopySequence
import SGA.Foundations.Cohomology.GeometricConnectedness

/-!
# SGA 1, Exposé X, 1.3–1.4: étale coverings coming from the base

X.1.3: let `f : X ⟶ Y` be proper and separable, `Y` locally noetherian and connected, with
`f_* 𝒪_X = 𝒪_Y`, and `y ∈ Y`. A connected étale covering `X'` of `X` is `X ×_Y Y'` for an étale
covering `Y'` of `Y` iff `X̄'_y ⟶ X̄_y` has a section. We prove:

* necessity, unconditionally (`exists_section_of_iso_pullback`): a geometric point of `Y'` over
  `ȳ` gives the section;
* sufficiency (`exists_iso_pullback_of_section`), as in SGA, from X.1.2 (the Stein factorization
  `X' → Y'' → Y` of `X' → Y` has `Y''` étale, `SteinFactorizationEtaleStatement`) and from
  EGA III 4.3.4 (`f_* 𝒪 = 𝒪` implies geometrically connected fibres,
  `AlgebraicGeometry.CohomologyAux.geometricallyConnected_of_isIso_app`). The canonical map
  `X' ⟶ X ×_Y Y''` is a morphism of connected étale coverings of `X`, so it is an isomorphism as
  soon as one point of its fibre at a geometric point `x̄` of `X̄_y` has a single preimage (the
  fundamental group acts transitively). For the point `s(x̄)` this holds: the fibre of `X' → Y''`
  through it is connected, and the section `s` of the étale separated `X̄'_y → X̄_y` then
  contains it (`eq_of_comp_eq_of_connectedSpace`, `eq_of_comp_eq_of_section`).

Hence X.1.3 (`coveringOfBaseStatement_of_steinFactorizationEtaleStatement`) and the homotopy exact
sequence X.1.4 (`homotopyExactSequence`) follow from X.1.2, which needs cohomology and base change
(EGA III 7). We also record the remarks of X.1.3 and X.1.5: `f_* 𝒪_X = 𝒪_Y` implies that the
fibres are geometrically connected (`geometricallyConnected_of_isIso_app`), and the direct proof
of IX.3.4 (`connectedSpace_pullback_of_isIso_app`): for `Y'` connected and flat over `Y`,
`X ×_Y Y'` is connected, since `Γ(X ×_Y Y', 𝒪) = Γ(Y', 𝒪)` has no non-trivial idempotents.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeX

/-- Rigidity: two morphisms from a connected scheme to an unramified separated `E ⟶ B` which
agree over `B` and at one point are equal (the locus where they agree is open and closed). -/
theorem eq_of_comp_eq_of_connectedSpace {Z E B W : Scheme.{u}} (e : E ⟶ B)
    [FormallyUnramified e] [LocallyOfFiniteType e] [IsSeparated e] [ConnectedSpace Z]
    {u₁ u₂ : Z ⟶ E} (h : u₁ ≫ e = u₂ ≫ e) [Nonempty W] (z : W ⟶ Z) (hz : z ≫ u₁ = z ≫ u₂) :
    u₁ = u₂ := by
  let d := pullback.diagonal e
  let v : Z ⟶ pullback e e := pullback.lift u₁ u₂ h
  let q := pullback.snd d v
  have : IsOpenImmersion q := MorphismProperty.pullback_snd _ _ inferInstance
  have : IsClosedImmersion q := inferInstance
  have hzv : z ≫ v = (z ≫ u₁) ≫ d := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
        Category.comp_id, hz]
  let z' : W ⟶ pullback d v := pullback.lift (z ≫ u₁) z hzv.symm
  obtain ⟨w⟩ := ‹Nonempty W›
  have hclopen : IsClopen (Set.range q) := ⟨q.isClosedEmbedding.isClosed_range,
    q.isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range q).Nonempty := ⟨z w, z' w, by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]⟩
  have hsurj : Surjective q := ⟨fun x ↦ by
    rw [← Set.mem_range, hclopen.eq_univ hne]
    trivial⟩
  have : IsIso q := (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hsurj⟩
  have hv : v = inv q ≫ pullback.fst d v ≫ d := by
    rw [pullback.condition]
    exact (IsIso.inv_hom_id_assoc q v).symm
  have h₁ : u₁ = v ≫ pullback.fst e e := (pullback.lift_fst _ _ _).symm
  have h₂ : u₂ = v ≫ pullback.snd e e := (pullback.lift_snd _ _ _).symm
  rw [h₁, h₂, hv]
  simp [d]


/-- The key step of X.1.3. Let `p : X' ⟶ X` be finite étale, `g : X' ⟶ Y''` and `π : Y'' ⟶ Y`
with `g ≫ π = p ≫ f`, `g` with geometrically connected fibres, and `s` a section over `X̄ = X ×_Y K`
of `X̄' = X' ×_X X̄ ⟶ X̄`. For a geometric point `a` of `X̄`, the geometric point
`t₀ = s(a)` of `X'` is the only one over `a` in its fibre under `g`: the fibre of `g` through
`t₀` is connected, and `s` is a section of an étale separated morphism, so it contains that
fibre. -/
theorem eq_of_comp_eq_of_section {X Y X' Y'' : Scheme.{u}} (f : X ⟶ Y) (p : X' ⟶ X)
    [IsFinite p] [Etale p] (g : X' ⟶ Y'') (π : Y'' ⟶ Y) (hgπ : g ≫ π = p ≫ f)
    [GeometricallyConnected g] {K : Type u} [Field K] (yb : Spec (.of K) ⟶ Y)
    (s : pullback f yb ⟶ pullback p (pullback.fst f yb)) (hs : s ≫ pullback.snd _ _ = 𝟙 _)
    {Ω : Type u} [Field Ω] (a : Spec (.of Ω) ⟶ pullback f yb) (t : Spec (.of Ω) ⟶ X')
    (ht : t ≫ p = a ≫ pullback.fst f yb)
    (htg : t ≫ g = (a ≫ s ≫ pullback.fst p (pullback.fst f yb)) ≫ g) :
    t = a ≫ s ≫ pullback.fst p (pullback.fst f yb) := by
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, t₀ = a ≫ s ≫ pullback.fst p (pullback.fst f yb) := ⟨_, rfl⟩
  rw [← ht₀] at htg ⊢
  have ht₀p : t₀ ≫ p = a ≫ pullback.fst f yb := by
    rw [ht₀, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc s, hs,
      Category.id_comp]
  obtain ⟨b, hb⟩ : ∃ b, b = t₀ ≫ g := ⟨_, rfl⟩
  rw [← hb] at htg
  have : ConnectedSpace ↥(pullback g b) :=
    GeometricallyConnected.geometrically_connectedSpace (f := g) b _ _
      (IsPullback.of_hasPullback g b)
  obtain ⟨c, hc⟩ : ∃ c, c = a ≫ pullback.snd f yb := ⟨_, rfl⟩
  have hℓ : (pullback.fst g b ≫ p) ≫ f = (pullback.snd g b ≫ c) ≫ yb := by
    rw [Category.assoc, ← hgπ, ← Category.assoc, pullback.condition, hb, Category.assoc,
      Category.assoc, hgπ, ← Category.assoc t₀, ht₀p, Category.assoc, pullback.condition, hc]
    simp
  let ℓ : pullback g b ⟶ pullback f yb := pullback.lift _ _ hℓ
  have hℓa (w : Spec (.of Ω) ⟶ pullback g b) (hw₁ : w ≫ pullback.fst g b ≫ p =
      a ≫ pullback.fst f yb) (hw₂ : w ≫ pullback.snd g b = 𝟙 _) : w ≫ ℓ = a := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hw₁]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hw₂, Category.id_comp, hc]
  let u₁ : pullback g b ⟶ pullback p (pullback.fst f yb) :=
    pullback.lift (pullback.fst g b) ℓ (pullback.lift_fst _ _ _).symm
  have hu : u₁ ≫ pullback.snd _ _ = (ℓ ≫ s) ≫ pullback.snd _ _ := by
    rw [pullback.lift_snd, Category.assoc, hs, Category.comp_id]
  let z : Spec (.of Ω) ⟶ pullback g b :=
    pullback.lift t₀ (𝟙 _) (hb.symm.trans (Category.id_comp _).symm)
  have hzℓ : z ≫ ℓ = a := hℓa z (by rw [pullback.lift_fst_assoc, ht₀p])
    (pullback.lift_snd _ _ _)
  have hz : z ≫ u₁ = z ≫ ℓ ≫ s := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc, hzℓ, ht₀,
        Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, Category.assoc, hs,
        Category.comp_id]
  have h₁₂ : u₁ = ℓ ≫ s :=
    eq_of_comp_eq_of_connectedSpace (pullback.snd p (pullback.fst f yb)) hu z hz
  let t' : Spec (.of Ω) ⟶ pullback g b :=
    pullback.lift t (𝟙 _) (htg.trans (Category.id_comp _).symm)
  have ht'ℓ : t' ≫ ℓ = a := hℓa t' (by rw [pullback.lift_fst_assoc, ht])
    (pullback.lift_snd _ _ _)
  have := congrArg (fun m ↦ t' ≫ m ≫ pullback.fst p (pullback.fst f yb)) h₁₂
  simp only [u₁, pullback.lift_fst, Category.assoc] at this
  rw [pullback.lift_fst, ← Category.assoc t' ℓ, ht'ℓ, ← ht₀] at this
  exact this


open CategoryTheory.PreGaloisCategory in
/-- X.1.3, sufficiency, from X.1.2: under the hypotheses of X.1.3, if the
geometric fibre `X̄'_y ⟶ X̄_y` of a connected étale covering `p : X' ⟶ X` has a section, then
`X' ≅ X ×_Y Y''` over `X`, where `X' ⟶ Y'' ⟶ Y` is the Stein factorization of `X' ⟶ Y`. -/
theorem exists_iso_pullback_of_section (hStein : SteinFactorizationEtaleStatement.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsSeparable f] [IsLocallyNoetherian Y]
    [ConnectedSpace Y] (hf : ∀ U : Y.Opens, IsIso (f.app U)) (y : Y)
    {X' : Scheme.{u}} (p : X' ⟶ X) [IsFinite p] [Etale p] [ConnectedSpace X']
    (s : pullback f (geometricPoint Y y) ⟶ pullback p (pullback.fst f (geometricPoint Y y)))
    (hs : s ≫ pullback.snd _ _ = 𝟙 _) :
    ∃ (Y' : Scheme.{u}) (q : Y' ⟶ Y) (_ : IsFinite q) (_ : Etale q) (φ : X' ≅ pullback q f),
      φ.hom ≫ pullback.snd q f = p := by
  have : IsSeparable (p ≫ f) := isSeparable_comp f p
  obtain ⟨Y'', π, g, hπ₁, hπ₂, hgπ, hg⟩ := hStein (p ≫ f)
  have : IsFinite π := hπ₁
  have : Etale π := hπ₂
  have : IsProper (g ≫ π) := by rw [hgπ]; infer_instance
  have : IsProper g := IsProper.of_comp g π
  have : IsLocallyNoetherian Y'' := LocallyOfFiniteType.isLocallyNoetherian π
  have : GeometricallyConnected g := CohomologyAux.geometricallyConnected_of_isIso_app g hg
  have : GeometricallyConnected f := CohomologyAux.geometricallyConnected_of_isIso_app f hf
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_universally_isQuotientMap f
    (ExposeIX.universally_isQuotientMap_of_universallyClosed f)
  have : ConnectedSpace Y'' := g.surjective.connectedSpace g.continuous
  have : ConnectedSpace ↥(pullback π f) := ExposeIX.connectedSpace_pullback f
    (ExposeIX.universally_isQuotientMap_of_universallyClosed f) π
  let P : FEt X := MorphismProperty.Over.mk ⊤ p ⟨inferInstance, inferInstance⟩
  let Q : FEt Y := MorphismProperty.Over.mk ⊤ π ⟨hπ₁, hπ₂⟩
  have hgπ' : g ≫ π = p ≫ f := hgπ
  let φ : X' ⟶ pullback π f := pullback.lift g p hgπ'
  let Φ : P ⟶ (FEt.pullback f).obj Q :=
    MorphismProperty.Over.homMk φ (pullback.lift_snd _ _ _) trivial
  have : IsConnected P := (ExposeV.FEt.isConnected_iff_connectedSpace P).mpr ‹_›
  have : IsConnected ((FEt.pullback f).obj Q) :=
    (ExposeV.FEt.isConnected_iff_connectedSpace _).mpr ‹ConnectedSpace ↥(pullback π f)›
  have : Nonempty ↥(pullback f (geometricPoint Y y)) := by
    obtain ⟨w⟩ : Nonempty (Spec (.of (AlgebraicClosure (Y.residueField y)))) := inferInstance
    obtain ⟨z, -⟩ := (pullback.snd f (geometricPoint Y y)).surjective w
    exact ⟨z⟩
  obtain ⟨z⟩ := this
  let a := geometricPoint (pullback f (geometricPoint Y y)) z
  let F := ExposeV.FEt.fiber _ (a ≫ pullback.fst f (geometricPoint Y y))
  -- the distinguished point `t₀ = s(a)` of the fibre of `X'`
  have ht₀ : (a ≫ s ≫ pullback.fst p _) ≫ p = a ≫ pullback.fst f (geometricPoint Y y) := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc s, hs,
      Category.id_comp]
  let t₀ : F.obj P := (ExposeV.FEt.fiberEquiv _ _ P).symm (Over.homMk _ ht₀)
  have ht₀l : (ExposeV.FEt.fiberEquiv _ _ P t₀).left = a ≫ s ≫ pullback.fst p _ := by
    rw [Equiv.apply_symm_apply]
    rfl
  have hΦ : Φ.left ≫ pullback.fst π f = g := pullback.lift_fst _ _ _
  have key (t : F.obj P) (h : F.map Φ t = F.map Φ t₀) : t = t₀ := by
    apply ExposeV.FEt.fiber_ext
    rw [ht₀l]
    have h' := congrArg (fun x ↦ (ExposeV.FEt.fiberEquiv _ _ _ x).left ≫ pullback.fst π f) h
    dsimp only at h'
    rw [ExposeV.FEt.fiberEquiv_map_left, ExposeV.FEt.fiberEquiv_map_left] at h'
    have h'' : (ExposeV.FEt.fiberEquiv _ _ P t).left ≫ g = (a ≫ s ≫ pullback.fst p _) ≫ g := by
      rw [← hΦ, ← ht₀l]
      exact (Category.assoc _ _ _).symm.trans (h'.trans (Category.assoc _ _ _))
    exact eq_of_comp_eq_of_section f p g π hgπ' _ s hs a _
      (ExposeV.FEt.fiberEquiv_w _ _ t) h''
  have hbij : Function.Bijective (F.map Φ) := by
    refine ⟨fun t₁ t₂ h ↦ ?_, surjective_of_nonempty_fiber_of_isConnected F Φ⟩
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) t₁ t₀
    have h₁ : σ • t₂ = t₀ := key _ (by rw [← mulAction_naturality, ← h, mulAction_naturality, hσ])
    exact MulAction.injective σ (hσ.trans h₁.symm)
  have : IsIso (F.map Φ) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : IsIso Φ := isIso_of_reflects_iso Φ F
  have : IsIso φ := inferInstanceAs
    (IsIso ((MorphismProperty.Over.forget _ ⊤ X ⋙ Over.forget X).map Φ))
  exact ⟨Y'', π, hπ₁, hπ₂, asIso φ, pullback.lift_snd _ _ _⟩


/-- X.1.3, necessity: if `X' ≅ X ×_Y Y'` for an étale covering `Y'` of the connected scheme `Y`
and `X'` is nonempty, the geometric fibre `X̄'_y → X̄_y` has a section, induced by a geometric
point of `Y'` over `ȳ` (which exists since `Y' → Y` is surjective and étale coverings of the
spectrum of an algebraically closed field are completely decomposed). -/
theorem exists_section_of_iso_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) [ConnectedSpace Y] (y : Y)
    {X' : Scheme.{u}} (p : X' ⟶ X) [Nonempty X'] {Y' : Scheme.{u}} (q : Y' ⟶ Y) [IsFinite q]
    [Etale q] (φ : X' ≅ pullback q f) (hφ : φ.hom ≫ pullback.snd q f = p) :
    ∃ s : pullback f (geometricPoint Y y) ⟶ pullback p (pullback.fst f (geometricPoint Y y)),
      s ≫ pullback.snd _ _ = 𝟙 _ := by
  set yb := geometricPoint Y y
  let Q : FEt Y := MorphismProperty.Over.mk ⊤ q ⟨inferInstance, inferInstance⟩
  have : Nonempty Y' := by
    obtain ⟨x⟩ := ‹Nonempty X'›
    exact ⟨(φ.hom ≫ pullback.fst q f) x⟩
  have : Nonempty Q.left := ‹Nonempty Y'›
  have hq : Surjective q := ⟨fun y' ↦ by
    have := ExposeV.FEt.range_eq_univ Q
    rw [Set.eq_univ_iff_forall] at this
    exact this y'⟩
  have : Nonempty ↥(pullback q yb) := by
    obtain ⟨w⟩ : Nonempty (Spec (.of (AlgebraicClosure (Y.residueField y)))) := inferInstance
    obtain ⟨z, -⟩ := (pullback.snd q yb).surjective w
    exact ⟨z⟩
  let Z := (FEt.pullback yb).obj Q
  have hZ : Nonempty Z.left := ‹Nonempty ↥(pullback q yb)›
  obtain ⟨n, ⟨e⟩⟩ := FEt.isCompletelyDecomposed_of_isSepClosed _ Z
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      have hI : IsInitial (∐ fun _ : Fin 0 ↦ ⊤_ (FEt (Spec (.of (AlgebraicClosure
          (Y.residueField y)))))) :=
        IsInitial.ofUniqueHom (fun _ ↦ Sigma.desc fun i ↦ i.elim0)
          (fun _ _ ↦ Sigma.hom_ext _ _ fun i ↦ i.elim0)
      have : IsEmpty Z.left := ExposeV.FEt.isEmpty_left_of_isInitial (hI.ofIso e.symm)
      obtain ⟨w⟩ := hZ
      exact this.false w
    · exact h
  obtain ⟨σ', hσ'⟩ := FEt.exists_section_of_hom (Sigma.ι (fun _ : Fin n ↦ ⊤_ _) ⟨0, hn⟩ ≫ e.inv)
  let σ'' : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ pullback q yb := σ'
  have hσ'' : σ'' ≫ pullback.snd q yb = 𝟙 _ := hσ'
  let σ := σ'' ≫ pullback.fst q yb
  have hσ : σ ≫ q = yb := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ'', Category.id_comp]
  let m : pullback f yb ⟶ X' := pullback.lift (pullback.snd f yb ≫ σ) (pullback.fst f yb)
    (by rw [Category.assoc, hσ, pullback.condition]) ≫ φ.inv
  have hm : m ≫ p = pullback.fst f yb := by
    rw [← hφ, Category.assoc, Iso.inv_hom_id_assoc, pullback.lift_snd]
  exact ⟨pullback.lift m (𝟙 _) (by rw [hm, Category.id_comp]), pullback.lift_snd _ _ _⟩


/-- X.1.3 (remark in the statement): if `f : X ⟶ Y` is proper, `Y` locally noetherian and
`f_* 𝒪_X = 𝒪_Y`, the fibres of `f` are geometrically connected (EGA III 4.3.4;
`AlgebraicGeometry.CohomologyAux.geometricallyConnected_of_isIso_app`). -/
theorem geometricallyConnected_of_isIso_app {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [IsLocallyNoetherian Y] (hf : ∀ U : Y.Opens, IsIso (f.app U)) : GeometricallyConnected f :=
  CohomologyAux.geometricallyConnected_of_isIso_app f hf

/-- X.1.5, the direct proof of IX.3.4 for `f_* 𝒪_X = 𝒪_Y`: let `f : X ⟶ Y` be quasi-compact,
quasi-separated and surjective with `f_* 𝒪_X = 𝒪_Y`, and let `Y' ⟶ Y` be flat (for instance an
étale covering) with `Y'` connected. Then `X ×_Y Y'` is connected: by flat base change
`Γ(X ×_Y Y', 𝒪) = Γ(Y', 𝒪)`, which has no non-trivial idempotents. -/
theorem connectedSpace_pullback_of_isIso_app {X Y Y' : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] [Surjective f] (hf : ∀ U : Y.Opens, IsIso (f.app U)) (g : Y' ⟶ Y) [Flat g]
    [ConnectedSpace Y'] : ConnectedSpace ↥(pullback f g) := by
  have := CohomologyAux.isIso_app_pullback_snd f g hf ⊤
  have h : CohomologyAux.TrivialIdempotents Γ(pullback f g, ⊤) :=
    (CohomologyAux.trivialIdempotents_of_connectedSpace Y').of_ringEquiv
      (asIso ((pullback.snd f g).app ⊤)).commRingCatIsoToRingEquiv
  have : Nonempty ↥(pullback f g) := by
    obtain ⟨y'⟩ := ‹ConnectedSpace Y'›.toNonempty
    obtain ⟨z, -⟩ := (pullback.snd f g).surjective y'
    exact ⟨z⟩
  exact CohomologyAux.connectedSpace_of_trivialIdempotents _ h

/-- X.1.3 from X.1.2. -/
theorem coveringOfBaseStatement_of_steinFactorizationEtaleStatement
    (hStein : SteinFactorizationEtaleStatement.{u}) : CoveringOfBaseStatement.{u} := by
  intro X Y f _ _ _ _ hf y X' p _ _ _
  refine ⟨fun ⟨Y', q, hq, hq', φ, hφ⟩ ↦ ?_, fun ⟨s, hs⟩ ↦
    exists_iso_pullback_of_section hStein f hf y p s hs⟩
  have : IsFinite q := hq
  have : Etale q := hq'
  have : Nonempty X' := inferInstance
  exact exists_section_of_iso_pullback f y p q φ hφ

/-- X.1.4, the homotopy exact sequence `π₁(X̄_y, a) → π₁(X, a) → π₁(Y, a) → e` for a proper
separable `f : X ⟶ Y` with `f_* 𝒪_X = 𝒪_Y`, `Y` locally noetherian and connected, `y ∈ Y` and
`a` a geometric point of the geometric fibre `X̄_y`, from X.1.2: the image of
`π₁(X̄_y, a) → π₁(X, a)` is the kernel of `π₁(X, a) → π₁(Y, a)`, and the latter is surjective. -/
theorem homotopyExactSequence (hStein : SteinFactorizationEtaleStatement.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsSeparable f] [IsLocallyNoetherian Y]
    [ConnectedSpace Y] (hf : ∀ U : Y.Opens, IsIso (f.app U)) (y : Y)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (a : Spec (.of Ω) ⟶ pullback f (geometricPoint Y y)) :
    (ExposeV.etaleFundamentalGroup.map Ω (pullback.fst f (geometricPoint Y y)) a).range =
        (ExposeV.etaleFundamentalGroup.map Ω f (a ≫ pullback.fst f (geometricPoint Y y))).ker ∧
      Function.Surjective
        (ExposeV.etaleFundamentalGroup.map Ω f (a ≫ pullback.fst f (geometricPoint Y y))) :=
  homotopyExactSequence_of_coveringOfBaseStatement
    (coveringOfBaseStatement_of_steinFactorizationEtaleStatement hStein) f hf y Ω a

end SGA.SGA1.ExposeX
