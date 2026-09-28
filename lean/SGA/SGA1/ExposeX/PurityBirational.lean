/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import SGA.SGA1.ExposeV.FundamentalGroupFunctoriality
import SGA.SGA1.ExposeX.PurityDenseOpen

/-!
# SGA 1, Exposé X, 3.4: birational invariance of the fundamental group

Let `X`, `Y` be integral, regular and proper over a field `k`, and `φ` a birational map from `X`
to `Y` (an isomorphism of dense opens over `k`). Then the étale coverings of `X` and of `Y` are
equivalent, compatibly with `φ` (`birationalInvariance : BirationalInvarianceStatement`).

The proof is SGA's:
* the rational map `φ : X ⇢ Y` is defined at every point `x` with `dim 𝒪_{X,x} ≤ 1`, since
  `𝒪_{X,x}` is then a valuation ring and `Y` is proper (valuative criterion, then spreading out);
  so it is defined on an open `U` whose complement has codimension `≥ 2`
  (`exists_extension_of_isRegularScheme`);
* by purity X.3.3 every étale covering of `U` extends to `X`, so the pullback to `dom φ` of an
  étale covering of `Y` comes from an étale covering of `X`
  (`exists_iso_pullback_of_partialIso`), and symmetrically;
* restriction of étale coverings to a dense open of a normal scheme is fully faithful
  (`SGA.SGA1.ExposeX.PurityDenseOpen`), so both categories are identified with the same full
  subcategory of the étale coverings of `dom φ`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace SGA.SGA1.ExposeX

section Extension

/-- A regular local ring of dimension `≤ 1` (a field or a discrete valuation ring) is a valuation
ring. -/
lemma valuationRing_of_ringKrullDim_le_one (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (h : ringKrullDim R ≤ 1) : ValuationRing R := by
  have hf : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 := by
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
    rw [← this] at h
    exact_mod_cast h
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 6 2).mp hf

/-- For `x' ⤳ x` in an open `U`, the canonical map `Spec 𝒪_{X,x'} ⟶ U` factors through
`Spec 𝒪_{X,x}`. -/
lemma SpecMap_stalkSpecializes_fromSpecStalkOfMem {X : Scheme.{u}} (U : X.Opens) {x x' : X}
    (h : x' ⤳ x) (hx : x ∈ U) (hx' : x' ∈ U) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem x hx =
      U.fromSpecStalkOfMem x' hx' := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

variable {X Y S : Scheme.{u}} [IsIntegral X] (sX : X ⟶ S) (sY : Y ⟶ S) [LocallyOfFiniteType sY]
  [UniversallyClosed sY]

/-- Let `φ` be a partial `S`-map from an integral scheme `X` to `Y`, universally closed and
locally of finite type over `S`. The rational map of `φ` is defined at every point `x` whose
local ring is a valuation ring: by the valuative criterion `Spec K(X) ⟶ Y` extends to
`Spec 𝒪_{X,x} ⟶ Y`, which spreads out to a neighbourhood of `x`. -/
theorem mem_domain_of_valuationRing (φ : X.PartialMap Y) (hφ : φ.hom ≫ sY = φ.domain.ι ≫ sX)
    (x : X) [ValuationRing (X.presheaf.stalk x)] : x ∈ φ.toRationalMap.domain := by
  have hη : genericPoint X ∈ φ.domain :=
    (genericPoint_specializes _).mem_open φ.domain.2 φ.dense_domain.nonempty.choose_spec
  have hsq : CommSq φ.fromFunctionField
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField))) sY
      (X.fromSpecStalk x ≫ sX) := ⟨by
    change (φ.domain.fromSpecStalkOfMem _ _ ≫ φ.hom) ≫ sY =
      Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫ X.fromSpecStalk x ≫ sX
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc, Category.assoc, hφ,
      Scheme.Opens.fromSpecStalkOfMem_ι_assoc]⟩
  have hdom : IsDomain (X.presheaf.stalk x) := inferInstance
  let V : ValuativeCommSq sY :=
    { R := X.presheaf.stalk x, K := X.functionField, i₁ := φ.fromFunctionField,
      i₂ := X.fromSpecStalk x ≫ sX, commSq := hsq, domain := hdom }
  have hE : ValuativeCriterion.Existence sY := by
    have h : UniversallyClosed sY := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hE V).exists_lift
  change Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫ l =
    φ.fromFunctionField at hl₁
  change l ≫ sY = X.fromSpecStalk x ≫ sX at hl₂
  let g := Scheme.PartialMap.ofFromSpecStalk sX sY l hl₂
  have hxg : x ∈ g.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl₂
  have hg : g.fromSpecStalkOfMem hxg = l :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY l hl₂
  have H : g.fromFunctionField = φ.fromFunctionField := by
    rw [← hl₁, ← hg]
    change g.domain.fromSpecStalkOfMem _ _ ≫ g.hom =
      Spec.map _ ≫ g.domain.fromSpecStalkOfMem _ _ ≫ g.hom
    rw [← Category.assoc, SpecMap_stalkSpecializes_fromSpecStalkOfMem]
  exact Scheme.RationalMap.mem_domain.mpr
    ⟨g, hxg, Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ H⟩

/-- X.3.4, the geometric input: a rational map from a regular scheme to a proper one is defined in
codimension `1`. Let `X` be an integral regular scheme and `φ` a partial `S`-map from `X` to `Y`,
universally closed, separated and locally of finite type over `S`. Then `φ` extends to an open
`U ⊇ dom φ` whose complement has codimension `≥ 2`. -/
theorem exists_extension_of_isRegularScheme [Y.IsSeparated] (hX : IsRegularScheme X)
    (φ : X.PartialMap Y) (hφ : φ.hom ≫ sY = φ.domain.ι ≫ sX) :
    ∃ (U : X.Opens) (hU : φ.domain ≤ U) (g : U.toScheme ⟶ Y), X.homOfLE hU ≫ g = φ.hom ∧
      ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x) := by
  refine ⟨φ.toRationalMap.domain, φ.le_domain_toRationalMap, φ.toRationalMap.toPartialMap.hom,
    ?_, fun x hx ↦ ?_⟩
  · exact φ.toPartialMap_toRationalMap_restrict
  · by_contra h
    have := hX x
    have h1 : ringKrullDim (X.presheaf.stalk x) ≤ 1 :=
      ENat.WithBot.lt_add_one_iff.mp (by simpa [one_add_one_eq_two] using not_le.mp h)
    have := valuationRing_of_ringKrullDim_le_one _ h1
    exact hx (mem_domain_of_valuationRing sX sY φ hφ x)

end Extension

section Coverings

/-- If fully faithful functors `F : C ⥤ D` and `G : C' ⥤ D` have the same essential image, there
is an equivalence `E : C ≌ C'` with `E.functor ⋙ G ≅ F`. -/
lemma exists_equivalence_comp_iso {C C' D : Type*} [Category* C] [Category* C'] [Category* D]
    (F : C ⥤ D) (G : C' ⥤ D) [F.Full] [F.Faithful] [G.Full] [G.Faithful]
    (hFG : ∀ c, G.essImage (F.obj c)) (hGF : ∀ c', F.essImage (G.obj c')) :
    ∃ E : C ≌ C', Nonempty (E.functor ⋙ G ≅ F) := by
  let T := Functor.essImage.liftFunctor F G hFG
  let e : T ⋙ G ≅ F := Functor.essImage.liftFunctorCompIso F G hFG
  have : T.Faithful := Functor.Faithful.of_comp_iso e
  have : T.Full := Functor.Full.of_comp_faithful_iso e
  have : T.EssSurj := ⟨fun c' ↦ by
    obtain ⟨c, ⟨i⟩⟩ := hGF c'
    exact ⟨c, ⟨G.preimageIso (e.app c ≪≫ i)⟩⟩⟩
  have : T.IsEquivalence := { }
  exact ⟨T.asEquivalence, ⟨e⟩⟩

variable {X Y S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (sX : X ⟶ S) (sY : Y ⟶ S)
  [LocallyOfFiniteType sY] [UniversallyClosed sY] [Y.IsSeparated]

/-- X.3.4, essential surjectivity: let `X` be integral, regular and locally noetherian, `Y`
universally closed, separated and locally of finite type over `S`, and `φ` a partial `S`-isomorphism
from `X` to `Y`. The pullback to `dom φ` along `φ` of an étale covering of `Y` is the restriction of
an étale covering of `X`: extend `φ` to `U` with complement of codimension `≥ 2`
(`exists_extension_of_isRegularScheme`), pull back to `U` and extend to `X` by purity X.3.3. -/
theorem exists_iso_pullback_of_partialIso (hX : IsRegularScheme X) (φ : X.PartialIso Y)
    (hφ : φ.IsOver sX sY) (W : FEt Y) :
    ∃ W' : FEt X, Nonempty ((FEt.pullback φ.source.ι).obj W' ≅
      (FEt.pullback (φ.iso.hom ≫ φ.target.ι)).obj W) := by
  obtain ⟨U, hU, g, hg, hcodim⟩ := exists_extension_of_isRegularScheme sX sY hX φ.toPartialMap
    ((Category.assoc _ _ _).trans hφ)
  have := isEquivalence_pullback_of_isRegularScheme hX U hcodim
  let W' := (FEt.pullback U.ι).objPreimage ((FEt.pullback g).obj W)
  let e : (FEt.pullback U.ι).obj W' ≅ (FEt.pullback g).obj W :=
    (FEt.pullback U.ι).objObjPreimageIso _
  have h1 : φ.source.ι = X.homOfLE hU ≫ U.ι := (X.homOfLE_ι hU).symm
  have h2 : X.homOfLE hU ≫ g = φ.iso.hom ≫ φ.target.ι := hg
  let c₁ : FEt.pullback φ.source.ι ≅ FEt.pullback U.ι ⋙ FEt.pullback (X.homOfLE hU) :=
    MorphismProperty.Over.pullbackCongr (P := ExposeV.finiteEtaleHom.{u}) (Q := ⊤) h1 ≪≫
      MorphismProperty.Over.pullbackComp (P := ExposeV.finiteEtaleHom.{u}) (Q := ⊤)
        (X.homOfLE hU) U.ι
  let c₂ : FEt.pullback (φ.iso.hom ≫ φ.target.ι) ≅
      FEt.pullback g ⋙ FEt.pullback (X.homOfLE hU) :=
    (MorphismProperty.Over.pullbackCongr (P := ExposeV.finiteEtaleHom.{u}) (Q := ⊤) h2).symm ≪≫
      MorphismProperty.Over.pullbackComp (P := ExposeV.finiteEtaleHom.{u}) (Q := ⊤)
        (X.homOfLE hU) g
  exact ⟨W', ⟨c₁.app W' ≪≫ (FEt.pullback (X.homOfLE hU)).mapIso e ≪≫ (c₂.app W).symm⟩⟩

end Coverings

/-- X.3.4, birational invariance of the fundamental group: let `X`, `Y` be integral, regular and
proper over a field `k`, and `φ` a birational map from `X` to `Y` over `k`. Then there is an
equivalence between the étale coverings of `X` and of `Y`, compatible with `φ` on `dom φ`. -/
theorem birationalInvariance : BirationalInvarianceStatement.{u} := by
  intro k _ X Y sX sY _ _ _ _ hX hY φ hφ
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from sX]; infer_instance⟩
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from sY]; infer_instance⟩
  have hsrc : (φ.source : Set X).Nonempty := φ.dense_source.nonempty
  have htgt : (φ.target : Set Y).Nonempty := φ.dense_target.nonempty
  have := full_pullback_of_isNormalScheme (isNormalScheme_of_isRegularScheme hX) hsrc
  have := faithful_pullback_of_isNormalScheme (isNormalScheme_of_isRegularScheme hX) hsrc
  have := full_pullback_of_isNormalScheme (isNormalScheme_of_isRegularScheme hY) htgt
  have := faithful_pullback_of_isNormalScheme (isNormalScheme_of_isRegularScheme hY) htgt
  let eG : FEt.pullback (φ.iso.hom ≫ φ.target.ι) ≅
      FEt.pullback φ.target.ι ⋙ FEt.pullback φ.iso.hom :=
    MorphismProperty.Over.pullbackComp (P := ExposeV.finiteEtaleHom.{u}) (Q := ⊤)
      φ.iso.hom φ.target.ι
  have : (FEt.pullback (φ.iso.hom ≫ φ.target.ι)).Full := Functor.Full.of_iso eG.symm
  have : (FEt.pullback (φ.iso.hom ≫ φ.target.ι)).Faithful := Functor.Faithful.of_iso eG.symm
  refine exists_equivalence_comp_iso _ _ (fun W ↦ ?_) (fun W' ↦ ?_)
  · obtain ⟨W', ⟨i⟩⟩ := exists_iso_pullback_of_partialIso sY sX hY φ.symm hφ.symm W
    have h : φ.iso.hom ≫ φ.iso.inv ≫ φ.source.ι = φ.source.ι := Iso.hom_inv_id_assoc _ _
    let c : FEt.pullback (φ.iso.inv ≫ φ.source.ι) ⋙ FEt.pullback φ.iso.hom ≅
        FEt.pullback φ.source.ι :=
      (MorphismProperty.Over.pullbackComp (P := ExposeV.finiteEtaleHom.{u}) (Q := ⊤)
        φ.iso.hom (φ.iso.inv ≫ φ.source.ι)).symm ≪≫
        MorphismProperty.Over.pullbackCongr (P := ExposeV.finiteEtaleHom.{u}) (Q := ⊤) h
    exact ⟨W', ⟨eG.app W' ≪≫ (FEt.pullback φ.iso.hom).mapIso i ≪≫ c.app W⟩⟩
  · exact exists_iso_pullback_of_partialIso sX sY hX φ hφ W'

end SGA.SGA1.ExposeX
