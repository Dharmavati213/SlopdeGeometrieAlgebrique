/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Limits.FiniteEtale
import SGA.SGA1.ExposeI.Unramified
import SGA.SGA1.ExposeIX.ExactSequence
import SGA.SGA1.ExposeIX.NilImmersion
import SGA.SGA1.ExposeIX.Submersive
import SGA.SGA1.ExposeIX.TopologicalInvariance
import SGA.SGA1.ExposeV.ExactFunctors

/-!
# SGA 1, Exposé IX, 6.1: injectivity of `π₁(X̄₀) → π₁(X)`

SGA proves the injectivity of `π₁(X̄₀) → π₁(X)` in IX.6.1 by passing to the limit over the finite
subextensions `L` of `κ(s)‾/κ(s)`: an étale covering of `X̄₀` comes from an étale covering of some
`X₀ ⊗ L`. We use the limit theorem for finite étale coverings
(`AlgebraicGeometry.Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale`, EGA IV 8.8.2 and
17.7.8), IX.4.10 for the radicial `X₀ ⊗ L ⟶ X₀ ⊗ K₀` (`K₀` the separable closure of `κ(s)` in `L`)
and I.8.3 for the nil-immersion `X₀ ⟶ X`, to embed every étale covering of `X̄₀` into the inverse
image of an étale covering of `X` (`exists_mono_pullback_geometricFiberι`); V.6.8 gives the
injectivity (`injective_autMap_geometricFiberι`). Together with the exactness at `π₁(X)` proved in
`ExactSequence`, this proves IX.6.1 when the closed fibre is quasi-compact and quasi-separated
(`exactSequence_of_quasiSeparatedSpace`); `ExactSequenceStatement` only assumes it quasi-compact.

The finiteness of the descended étale schemes uses that finiteness of étale morphisms descends
along surjective universally closed morphisms (`isFinite_of_isPullback_of_etale`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MorphismProperty PreGaloisCategory

namespace SGA.SGA1.ExposeIX

set_option backward.isDefEq.respectTransparency false in
/-- An étale morphism whose base change along a surjective universally closed morphism is
finite is finite (separatedness descends along universally submersive morphisms, IX.2.4). -/
theorem isFinite_of_isPullback_of_etale {T S S' T' : Scheme.{u}} {h : T ⟶ S} {g : S' ⟶ S}
    {h' : T' ⟶ S'} {g' : T' ⟶ T} (sq : IsPullback h' g' g h) [Etale h] [IsFinite h']
    [UniversallyClosed g] [Surjective g] : IsFinite h := by
  have : IsSeparated h :=
    of_isPullback_of_descendsAlong (Q := @UniversallySubmersive) sq inferInstance inferInstance
  have : Surjective g' := MorphismProperty.of_isPullback sq ‹_›
  have : UniversallyClosed (g' ≫ h) := by rw [← sq.w]; infer_instance
  have : UniversallyClosed h := UniversallyClosed.of_comp_surjective g' h
  have : IsProper h := ⟨⟩
  exact .of_isProper_of_locallyQuasiFinite h

set_option backward.isDefEq.respectTransparency false in
/-- If base change along `g` is essentially surjective on étale schemes and `g` is surjective and
universally closed, every finite étale `S'`-scheme is the base change of a finite étale
`S`-scheme. -/
theorem exists_isPullback_of_essSurj_pullback_etale {S S' Y' : Scheme.{u}} (g : S' ⟶ S)
    [UniversallyClosed g] [Surjective g] [(MorphismProperty.Over.pullback @Etale ⊤ g).EssSurj]
    (q' : Y' ⟶ S') [IsFinite q'] [Etale q'] :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ S) (e : Y' ⟶ Y), IsFinite q ∧ Etale q ∧ IsPullback e q' q g := by
  obtain ⟨Z, ⟨φ⟩⟩ := Functor.EssSurj.mem_essImage (MorphismProperty.Over.pullback @Etale ⊤ g)
    (MorphismProperty.Over.mk ⊤ q' ‹_›)
  have : Etale Z.hom := Z.prop
  have hφ : φ.inv.left ≫ pullback.snd Z.hom g = q' := MorphismProperty.Over.w φ.inv
  have hφ' : φ.hom.left ≫ q' = pullback.snd Z.hom g := MorphismProperty.Over.w φ.hom
  let φ' : pullback Z.hom g ≅ Y' :=
    (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget S').mapIso φ
  have sq : IsPullback (φ.inv.left ≫ pullback.fst Z.hom g) q' Z.hom g := by
    refine (IsPullback.of_hasPullback Z.hom g).of_iso φ' (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp only [Iso.refl_hom, Category.comp_id]
      rw [← Category.assoc]
      change _ = (φ.hom ≫ φ.inv).left ≫ _
      rw [φ.hom_inv_id]
      rfl
    · simp only [Iso.refl_hom, Category.comp_id]
      exact hφ'.symm
  have : IsFinite Z.hom := isFinite_of_isPullback_of_etale sq.flip
  exact ⟨Z.left, Z.hom, _, inferInstance, inferInstance, sq⟩

/-- Every finite étale `X₀`-scheme is the base change along `j : X₀ ⟶ X` of a finite étale
`X`-scheme (for instance, `j` a nil-immersion, I.8.3, or the closed fibre of a proper scheme over
a complete noetherian local ring, IX.1.10). -/
def LiftsFiniteEtale {X₀ X : Scheme.{u}} (j : X₀ ⟶ X) : Prop :=
  ∀ ⦃Y' : Scheme.{u}⦄ (q' : Y' ⟶ X₀), IsFinite q' → Etale q' →
    ∃ (Y : Scheme.{u}) (q : Y ⟶ X) (e : Y' ⟶ Y), IsFinite q ∧ Etale q ∧ IsPullback e q' q j

/-- I.8.3: finite étale schemes lift along surjective closed immersions. -/
lemma liftsFiniteEtale_of_isClosedImmersion {X₀ X : Scheme.{u}} (j : X₀ ⟶ X)
    [IsClosedImmersion j] [Surjective j] : LiftsFiniteEtale j := fun _ q' _ _ ↦
  have := essSurj_pullback_etale_of_isClosedImmersion j
  exists_isPullback_of_essSurj_pullback_etale j q'

set_option backward.isDefEq.respectTransparency false in
/-- If base change along `j` is essentially surjective on étale coverings, finite étale schemes
lift along `j`. -/
lemma liftsFiniteEtale_of_essSurj {X₀ X : Scheme.{u}} (j : X₀ ⟶ X)
    [(MorphismProperty.Over.pullback SGA.SGA1.ExposeV.finiteEtaleHom ⊤ j).EssSurj] :
    LiftsFiniteEtale j := by
  intro Y' q' _ _
  obtain ⟨Z, ⟨φ⟩⟩ := Functor.EssSurj.mem_essImage
    (MorphismProperty.Over.pullback SGA.SGA1.ExposeV.finiteEtaleHom ⊤ j)
    (MorphismProperty.Over.mk ⊤ q' ⟨‹_›, ‹_›⟩)
  have : IsFinite Z.hom := Z.prop.1
  have : Etale Z.hom := Z.prop.2
  have hφ' : φ.hom.left ≫ q' = pullback.snd Z.hom j := MorphismProperty.Over.w φ.hom
  let φ' : pullback Z.hom j ≅ Y' :=
    (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget X₀).mapIso φ
  have sq : IsPullback (φ.inv.left ≫ pullback.fst Z.hom j) q' Z.hom j := by
    refine (IsPullback.of_hasPullback Z.hom j).of_iso φ' (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp only [Iso.refl_hom, Category.comp_id]
      rw [← Category.assoc]
      change _ = (φ.hom ≫ φ.inv).left ≫ _
      rw [φ.hom_inv_id]
      rfl
    · simp only [Iso.refl_hom, Category.comp_id]
      exact hφ'.symm
  exact ⟨Z.left, Z.hom, _, inferInstance, inferInstance, sq⟩

/-- Lifting of finite étale schemes along `j'` gives lifting along `e ≫ j'` for an isomorphism
`e`. -/
lemma LiftsFiniteEtale.iso_comp {X₀ X₀' X : Scheme.{u}} {j' : X₀' ⟶ X} (h : LiftsFiniteEtale j')
    (e : X₀ ≅ X₀') : LiftsFiniteEtale (e.hom ≫ j') := by
  intro Y' q' _ _
  obtain ⟨Y, q, e', hq, hq', sq⟩ := h (q' ≫ e.hom) inferInstance inferInstance
  have sq₁ : IsPullback (𝟙 Y') q' (q' ≫ e.hom) e.hom :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp]⟩
  exact ⟨Y, q, 𝟙 Y' ≫ e', hq, hq', sq₁.paste_horiz sq⟩

section IX61

local notation "FEt" => (SGA.SGA1.ExposeV.finiteEtaleHom : MorphismProperty Scheme)

variable {X S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- IX.6.1, the key step for the injectivity of `π₁(X̄₀) → π₁(X)`: if the finite étale coverings
of the fibre `X_s` lift to `X` (`hlift`; I.8.3 over a one-point base, IX.1.10 over a complete
local base) and `X_s` is quasi-compact and quasi-separated, every finite étale covering `Y` of the
geometric fibre `X̄₀` embeds into the inverse image on `X̄₀` of a finite étale covering `Z` of `X`.
As in SGA, `Y` comes from `X_s ⊗ L` for a finite subextension `L` of `κ(s)‾/κ(s)` (the limit
theorem for étale coverings, EGA IV 8.8.2 and 17.7.8), hence from `X_s ⊗ K₀` with `K₀` the
separable closure of `κ(s)` in `L` (IX.4.10 for the radicial `X_s ⊗ L ⟶ X_s ⊗ K₀`); then `Z` is
the étale covering of `X` lifting the étale covering `Y ⟶ X_s ⊗ K₀ ⟶ X_s` of the fibre. -/
theorem exists_mono_pullback_geometricFiberι_of_lift (f : X ⟶ S) (s : S)
    (hlift : LiftsFiniteEtale (f.fiberι s))
    [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (Y : MorphismProperty.Over FEt ⊤ (geometricFiber f s)) :
    ∃ (Z : MorphismProperty.Over FEt ⊤ X)
      (i : Y ⟶ (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)).obj Z), Mono i := by
  let h := f.fiberToSpecResidueField s
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  -- `Y` comes from some `X_s ⊗ L`
  obtain ⟨L, YL, qL, e, _, _, hY⟩ := Scheme.exists_isPullback_of_isLimit_of_isFinite_of_etale
    (ExposeV.isLimitBaseChangeCone (k := S.residueField s)
      (E := AlgebraicClosure (S.residueField s)) h) Y.hom
  let L' : ExposeV.FiniteSubext (S.residueField s) (AlgebraicClosure (S.residueField s)) := L.unop
  have := L'.2
  let K₀ := separableClosure (S.residueField s) L'.1
  have : Algebra.IsSeparable (S.residueField s) K₀ :=
    separableClosure.isSeparable (S.residueField s) L'.1
  have : IsPurelyInseparable K₀ L'.1 :=
    separableClosure.isPurelyInseparable (S.residueField s) L'.1
  have : FiniteDimensional (S.residueField s) K₀ := inferInstance
  have : Module.Finite K₀ L'.1 := Module.Finite.right (S.residueField s) K₀ L'.1
  let ιL := ExposeV.specFiniteSubextι (S.residueField s) (AlgebraicClosure (S.residueField s)) L'
  let ιK : Spec (.of K₀) ⟶ Spec (S.residueField s) :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K₀))
  let ρ : Spec (.of L'.1) ⟶ Spec (.of K₀) := Spec.map (CommRingCat.ofHom (algebraMap K₀ L'.1))
  have hρ : ρ ≫ ιK = ιL := by
    rw [← Spec.map_comp]
    rfl
  -- the radicial `g : X_s ⊗ L ⟶ X_s ⊗ K₀`
  let g : pullback h ιL ⟶ pullback h ιK :=
    pullback.map h ιL h ιK (𝟙 _) ρ (𝟙 _) (by simp) (by simp [hρ])
  have hg : IsPullback g (pullback.snd h ιL) (pullback.snd h ιK) ρ :=
    ExposeV.isPullback_pullbackMap h ιL ιK ρ hρ
  have : IsFinite ρ := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : UniversallyInjective ρ := universallyInjective_specMap_of_isPurelyInseparable K₀ L'.1
  have : Surjective ρ := ⟨fun _ ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : LocallyOfFinitePresentation ρ := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    have : Algebra.FinitePresentation K₀ L'.1 :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  have : IsFinite g := MorphismProperty.of_isPullback hg.flip ‹_›
  have : UniversallyInjective g := MorphismProperty.of_isPullback hg.flip ‹_›
  have : Surjective g := MorphismProperty.of_isPullback hg.flip ‹_›
  have : LocallyOfFinitePresentation g := MorphismProperty.of_isPullback hg.flip ‹_›
  have := isEquivalence_pullback_etale_of_isFinite g
  obtain ⟨Ys, qs, es, _, _, hs⟩ := exists_isPullback_of_essSurj_pullback_etale g qL
  -- the finite étale covering `X_s ⊗ K₀ ⟶ X_s`
  have : IsFinite ιK := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : Etale ιK := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FinitePresentation (S.residueField s) K₀ :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have : Algebra.Etale (S.residueField s) K₀ :=
      ⟨Algebra.FormallyEtale.of_isSeparable _ _, inferInstance⟩
    exact RingHom.etale_algebraMap.mpr inferInstance
  let πK := pullback.fst h ιK
  have : IsFinite πK := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h ιK).flip ‹_›
  have : Etale πK := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h ιK).flip ‹_›
  -- lift along `X_s ⟶ X`
  let jX := f.fiberι s
  obtain ⟨Z, qZ, eZ, _, _, hZ⟩ := hlift (qs ≫ πK) inferInstance inferInstance
  -- the monomorphism
  let π : geometricFiber f s ⟶ pullback h ιK :=
    ExposeV.baseChangeConeπ (k := S.residueField s) (E := AlgebraicClosure (S.residueField s))
      h L ≫ g
  have hπ : π ≫ πK = pullback.fst _ _ := by
    simp only [π, g, πK, Category.assoc, pullback.map, pullback.lift_fst, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have hYs := hY.paste_horiz hs
  have hφ : (e ≫ es ≫ eZ) ≫ qZ = Y.hom ≫ geometricFiberι f s := by
    rw [Category.assoc, Category.assoc, hZ.w]
    simp only [Category.assoc]
    rw [reassoc_of% hs.w, reassoc_of% hY.w]
    change Y.hom ≫ π ≫ πK ≫ jX = _
    rw [reassoc_of% hπ]
    rfl
  let Zo : MorphismProperty.Over FEt ⊤ X := MorphismProperty.Over.mk ⊤ qZ ⟨‹_›, ‹_›⟩
  refine ⟨Zo, MorphismProperty.Over.homMk (pullback.lift (e ≫ es ≫ eZ) Y.hom hφ)
    (pullback.lift_snd _ _ _), ⟨fun {T} a b hab ↦ ?_⟩⟩
  have hab' : a.left ≫ pullback.lift (e ≫ es ≫ eZ) Y.hom hφ =
      b.left ≫ pullback.lift (e ≫ es ≫ eZ) Y.hom hφ := congrArg (fun φ ↦ φ.left) hab
  have h₁ : a.left ≫ e ≫ es ≫ eZ = b.left ≫ e ≫ es ≫ eZ := by
    simpa using congrArg (· ≫ pullback.fst _ _) hab'
  have h₂ : a.left ≫ Y.hom = b.left ≫ Y.hom :=
    (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm
  have h₃ : a.left ≫ e ≫ es = b.left ≫ e ≫ es := by
    refine hZ.hom_ext (by simpa using h₁) ?_
    simp only [Category.assoc]
    rw [reassoc_of% hs.w, reassoc_of% hY.w, reassoc_of% h₂]
  exact MorphismProperty.Over.Hom.ext (hYs.hom_ext (by simpa using h₃) h₂)

/-- Over a one-point base, finite étale coverings of the fibre `X_s` lift to `X` (I.8.3 for the
surjective closed immersion `X_s ⟶ X`). -/
lemma liftsFiniteEtale_fiberι_of_subsingleton (f : X ⟶ S) (s : S) [Subsingleton S] :
    LiftsFiniteEtale (f.fiberι s) := by
  have : IsClosedImmersion (S.fromSpecResidueField s) :=
    isClosed_singleton_iff_isClosedImmersion.mp (by
      rw [Set.subsingleton_univ.eq_singleton_of_mem (Set.mem_univ s) |>.symm]
      exact isClosed_univ)
  have : Surjective (S.fromSpecResidueField s) :=
    ⟨fun x ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : IsClosedImmersion (f.fiberι s) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f _).flip ‹_›
  have : Surjective (f.fiberι s) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f _).flip ‹_›
  exact liftsFiniteEtale_of_isClosedImmersion _

/-- IX.6.1, the key step for the injectivity of `π₁(X̄₀) → π₁(X)`, over a one-point base: every
finite étale covering of `X̄₀` embeds into the inverse image of a finite étale covering of `X`. -/
theorem exists_mono_pullback_geometricFiberι (f : X ⟶ S) (s : S) [Subsingleton S]
    [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (Y : MorphismProperty.Over FEt ⊤ (geometricFiber f s)) :
    ∃ (Z : MorphismProperty.Over FEt ⊤ X)
      (i : Y ⟶ (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)).obj Z), Mono i :=
  exists_mono_pullback_geometricFiberι_of_lift f s (liftsFiniteEtale_fiberι_of_subsingleton f s) Y

set_option backward.isDefEq.respectTransparency false in
/-- **IX.6.1, injectivity of `π₁(X̄₀) → π₁(X)`**, when the finite étale coverings of the fibre
`X_s` lift to `X` (a one-point base, or X.2.2 over a complete local base) and `X_s` is
quasi-compact and quasi-separated: for any Galois structures and compatible fibre functors, the
homomorphism induced by the inverse image along `X̄₀ ⟶ X` is injective (V.6.8 and
`exists_mono_pullback_geometricFiberι_of_lift`). -/
theorem injective_autMap_geometricFiberι_of_lift (f : X ⟶ S) (s : S)
    (hlift : LiftsFiniteEtale (f.fiberι s))
    [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{u}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')] :
    Function.Injective
      (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) F'') := by
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F''
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor
    (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  refine (ExposeV.injective_autWhiskerLeft_iff _ F'').mpr fun Y hY ↦ ?_
  obtain ⟨Z, i, hi⟩ := exists_mono_pullback_geometricFiberι_of_lift f s hlift Y
  exact ⟨Z, Y, i, 𝟙 Y, hY, hi⟩

/-- **IX.6.1, injectivity of `π₁(X̄₀) → π₁(X)`**, over a one-point base `S` (for instance the
spectrum of an artinian local ring), with `X_s` quasi-compact and quasi-separated. -/
theorem injective_autMap_geometricFiberι (f : X ⟶ S) (s : S) [Subsingleton S]
    [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{u}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')] :
    Function.Injective
      (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) F'') :=
  injective_autMap_geometricFiberι_of_lift f s (liftsFiniteEtale_fiberι_of_subsingleton f s) F''

/-- **IX.6.1** for `X_s` quasi-compact and quasi-separated: let `S` be the spectrum of an artinian
local ring with point `s`, `f : X ⟶ S` with fibre `X_s` quasi-compact, quasi-separated and
geometrically connected. Then `e → π₁(X̄₀) → π₁(X) → π₁(S)` is exact (for any Galois structures
and compatible fibre functors). This is IX.6.1 (`ExactSequenceStatement`) with the extra
hypothesis that `X₀ = X_s` is quasi-separated (used for the passage to the limit, EGA IV 8.8.2;
SGA assumes only that `X₀` is quasi-compact). -/
theorem exactSequence_of_quasiSeparatedSpace (f : X ⟶ S) (s : S)
    (hA : ∃ A : CommRingCat.{u}, IsArtinianRing A ∧ IsLocalRing A ∧ Nonempty (S ≅ Spec A))
    [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (hg : GeometricallyConnected (f.fiberToSpecResidueField s))
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{u}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')] :
    Function.Injective
        (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) F'') ∧
      (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) F'').range =
        (autMap (MorphismProperty.Over.pullback FEt ⊤ f)
          (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')).ker := by
  have : Subsingleton S := subsingleton_of_artinian hA
  exact ⟨injective_autMap_geometricFiberι f s F'', range_eq_ker_of_artinian f s hA hg F''⟩

end IX61

end SGA.SGA1.ExposeIX
