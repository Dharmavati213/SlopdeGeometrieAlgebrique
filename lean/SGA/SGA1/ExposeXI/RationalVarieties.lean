/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.ProjectiveSpaceSimplyConnected

/-!
# Rational varieties are simply connected (XI.1.2)

XI.1.2: a proper normal integral scheme `X` over an algebraically closed field `k` whose function
field is purely transcendental over `k` is simply connected
(`isSimplyConnected_of_isPurelyTranscendental`, `rationalSimplyConnectedStatement`). SGA's proof,
for `X` only normal (so X.3.4, which needs `X` regular, does not apply directly):

* the purely transcendental function field `k(t₁, …, t_r)` is that of `P = ℙʳ_k`
  (`exists_functionField_iso_proj`; the `tᵢ` are finite in number since `K(X)/k` is essentially
  of finite type, `essFiniteType_functionFieldMap`);
* the rational map `P ⇢ X` is defined on an open `U ⊆ P` whose complement has codimension `≥ 2`
  (`ExposeX.exists_extension_of_isRegularScheme`), and `U` is simply connected by purity X.3.3
  and XI.1.1;
* the inverse rational map `X ⇢ U` is a section of `U ⟶ X` over a dense open `T ⊆ X`, so the
  pullback of a connected étale covering of `X` has a section over `T`, which extends to `X`
  because `X` is normal; hence the covering is trivial (`isSimplyConnected_of_section`,
  `isSimplyConnected_of_functionField_iso`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeXI

section Coverings

variable {S : Scheme.{u}}

/-- A connected étale covering `Z` of a connected scheme which receives a morphism from a trivial
covering `A` (i.e. has a section) is trivial. -/
lemma isIso_hom_of_hom [ConnectedSpace S] {A Z : ExposeV.FEt S} [IsIso A.hom] [IsConnected Z]
    (a : A ⟶ Z) : IsIso Z.hom := by
  obtain ⟨x⟩ : Nonempty S := inferInstance
  let s := ExposeV.geometricPointAt S x
  let F := ExposeV.FEt.fiber _ s
  have hA : Subsingleton (F.obj A) :=
    ExposeV.subsingleton_fiber_of_isTerminal F (ExposeV.FEt.isTerminalOfIsIso A)
  have : IsIso ((MorphismProperty.Over.forget _ ⊤ S).obj A).hom := inferInstanceAs (IsIso A.hom)
  have : Nonempty (F.obj A) := ⟨(ExposeV.FEt.fiberEquiv _ s A).symm
    (Over.homMk (s ≫ inv ((MorphismProperty.Over.forget _ ⊤ S).obj A).hom) (by simp))⟩
  have : Epi a := epi_of_nonempty_of_isConnected F a
  have : IsIso (F.map a) := (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨fun b c _ ↦ Subsingleton.elim b c, surjective_on_fiber_of_epi F a⟩
  have : IsIso a := isIso_of_reflects_iso a F
  have : IsIso a.left := inferInstanceAs
    (IsIso ((MorphismProperty.Over.forget _ ⊤ S ⋙ CategoryTheory.Over.forget S).map a))
  have hw : a.left ≫ Z.hom = A.hom :=
    CategoryTheory.Over.w ((MorphismProperty.Over.forget _ ⊤ S).map a)
  rw [(IsIso.eq_inv_comp _).mpr hw]
  infer_instance

/-- Over a simply connected scheme, every étale covering with a geometric point receives a
morphism from a trivial covering. -/
lemma exists_hom_of_isSimplyConnected (hS : IsSimplyConnected S) (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) (Z : ExposeV.FEt S)
    (z : (ExposeV.FEt.fiber Ω s).obj Z) :
    ∃ A : ExposeV.FEt S, IsIso A.hom ∧ Nonempty (A ⟶ Z) := by
  have := hS.1
  obtain ⟨A, i, -, -, hA, -⟩ := fiber_in_connected_component (ExposeV.FEt.fiber Ω s) Z z
  have : ConnectedSpace A.left := ExposeV.FEt.connectedSpace_of_isConnected A
  exact ⟨A, hS.2 A.hom ‹_›, ⟨i⟩⟩

end Coverings

section Section

variable {X U : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- XI.1.2, the formal part: let `X` be integral, normal and locally noetherian, `U` simply
connected and `g : U ⟶ X` a morphism with a section `h : T ⟶ U` over a nonempty open `T` of `X`
(`h ≫ g` is the inclusion of `T`). Then `X` is simply connected: the pullback along `g` of a
connected étale covering of `X` has a section, which gives a section over `T`, which extends to
`X` since `X` is normal (`ExposeX.full_pullback_of_isNormalScheme`). -/
theorem isSimplyConnected_of_section (hX : ExposeX.IsNormalScheme X) (hU : IsSimplyConnected U)
    (g : U ⟶ X) (T : X.Opens) (hT : (T : Set X).Nonempty) (h : T.toScheme ⟶ U)
    (hhg : h ≫ g = T.ι) : IsSimplyConnected X := by
  refine ⟨inferInstance, fun Y f _ _ hY ↦ ?_⟩
  have := hU.1
  let Z : ExposeV.FEt X := MorphismProperty.Over.mk ⊤ f ⟨inferInstance, inferInstance⟩
  have : ConnectedSpace Z.left := hY
  have : IsConnected Z := ExposeV.FEt.isConnected_of_connectedSpace Z
  obtain ⟨t, ht⟩ := hT
  let u := ExposeV.geometricPointAt U (h ⟨t, ht⟩)
  let z : (ExposeV.FEt.fiber _ u).obj ((ExposeV.FEt.pullback g).obj Z) :=
    ((ExposeV.FEt.pullbackFiberIso _ g u).app Z).inv
      (Classical.arbitrary ((ExposeV.FEt.fiber _ (u ≫ g)).obj Z))
  obtain ⟨A, hA, ⟨a⟩⟩ := exists_hom_of_isSimplyConnected hU _ u _ z
  let B := (ExposeV.FEt.pullback h).obj A
  have : IsIso B.hom := by
    change IsIso (pullback.snd A.hom h)
    infer_instance
  let c : (ExposeV.FEt.pullback h).obj ((ExposeV.FEt.pullback g).obj Z) ≅
      (ExposeV.FEt.pullback T.ι).obj Z :=
    ((MorphismProperty.Over.pullbackComp (P := ExposeV.finiteEtaleHom.{u}) (Q := ⊤) h g).app
      Z).symm ≪≫
      (MorphismProperty.Over.pullbackCongr (P := ExposeV.finiteEtaleHom.{u}) (Q := ⊤) hhg).app Z
  let TX : ExposeV.FEt X := MorphismProperty.Over.mk ⊤ (𝟙 X) ⟨inferInstance, inferInstance⟩
  have : IsIso TX.hom := inferInstanceAs (IsIso (𝟙 X))
  let TX' := (ExposeV.FEt.pullback T.ι).obj TX
  have : IsIso TX'.hom := by
    change IsIso (pullback.snd TX.hom T.ι)
    infer_instance
  let e : TX' ≅ B :=
    (ExposeV.FEt.isTerminalOfIsIso TX').uniqueUpToIso (ExposeV.FEt.isTerminalOfIsIso B)
  have := ExposeX.full_pullback_of_isNormalScheme hX ⟨t, ht⟩
  let m : TX ⟶ Z :=
    (ExposeV.FEt.pullback T.ι).preimage (e.hom ≫ (ExposeV.FEt.pullback h).map a ≫ c.hom)
  exact isIso_hom_of_hom m

end Section

section FunctionField

variable {S X P : Scheme.{u}} (sX : X ⟶ S) (sP : P ⟶ S) [IsIntegral X] [IsIntegral P]
  [IsLocallyNoetherian X] [IsLocallyNoetherian P] [LocallyOfFiniteType sX] [UniversallyClosed sX]
  [X.IsSeparated] [LocallyOfFiniteType sP]

/-- XI.1.2, general form: let `X` be integral, normal, locally noetherian, separated, universally
closed and locally of finite type over `S`, and `P` integral, regular, locally noetherian, locally
of finite type over `S` and simply connected. If the function fields of `X` and `P` are
isomorphic over `S` (`ρ : K(P) ≅ K(X)`), then `X` is simply connected.

The rational map `P ⇢ X` given by `ρ` is defined on an open `U ⊆ P` with complement of
codimension `≥ 2` (`ExposeX.exists_extension_of_isRegularScheme`), which is simply connected by
purity X.3.3; the inverse rational map `X ⇢ U` is a section over a dense open of `X`, and
`isSimplyConnected_of_section` applies. -/
theorem isSimplyConnected_of_functionField_iso (hX : ExposeX.IsNormalScheme X)
    (hP : ExposeX.IsRegularScheme P) (hPs : IsSimplyConnected P) {y : P}
    (hy : y = genericPoint P) (ρ : P.presheaf.stalk y ⟶ X.functionField) [IsIso ρ]
    (hρ : Spec.map ρ ≫ P.fromSpecStalk y ≫ sP = X.fromSpecStalk (genericPoint X) ≫ sX) :
    IsSimplyConnected X := by
  subst hy
  -- The rational maps `χ : X ⇢ P` and `ψ : P ⇢ X` at the generic points.
  let χ : Spec X.functionField ⟶ P := Spec.map ρ ≫ P.fromSpecStalk (genericPoint P)
  let ψ : Spec (P.presheaf.stalk (genericPoint P)) ⟶ X :=
    Spec.map (inv ρ) ≫ X.fromSpecStalk (genericPoint X)
  have hχ : χ ≫ sP = X.fromSpecStalk (genericPoint X) ≫ sX := by
    rw [Category.assoc]
    exact hρ
  have hψ : ψ ≫ sX = P.fromSpecStalk (genericPoint P) ≫ sP := by
    rw [Category.assoc, ← hρ, ← Spec.map_comp_assoc, IsIso.hom_inv_id, Spec.map_id,
      Category.id_comp]
  -- Extend `ψ` to an open `U` of `P` with complement of codimension `≥ 2`.
  let F := Scheme.PartialMap.ofFromSpecStalk sP sX ψ hψ
  have hFη : genericPoint P ∈ F.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sP sX ψ hψ
  have hFψ : F.fromSpecStalkOfMem hFη = ψ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sP sX ψ hψ
  have hF : F.hom ≫ sX = F.domain.ι ≫ sP := Scheme.PartialMap.ofFromSpecStalk_comp sP sX ψ hψ
  obtain ⟨U, hFU, g, hg, hcodim⟩ := ExposeX.exists_extension_of_isRegularScheme sP sX hP F hF
  have := ExposeX.isEquivalence_pullback_of_isRegularScheme hP U hcodim
  have : Nonempty U := ⟨⟨_, hFU hFη⟩⟩
  have hU : IsSimplyConnected U :=
    isSimplyConnected_of_equivalence (ExposeV.FEt.pullback U.ι).asEquivalence.symm hPs
  -- Spread out `χ` to a partial map `X ⇢ P`, and restrict it to the preimage of `U`.
  let C := Scheme.PartialMap.ofFromSpecStalk sX sP χ hχ
  have hCη : genericPoint X ∈ C.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sP χ hχ
  have hCχ : C.domain.fromSpecStalkOfMem _ hCη ≫ C.hom = χ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sP χ hχ
  have hcη : C.hom ⟨genericPoint X, hCη⟩ ∈ U := by
    have h1 : C.domain.fromSpecStalkOfMem _ hCη (IsLocalRing.closedPoint _) =
        ⟨genericPoint X, hCη⟩ := by
      apply C.domain.ι.isOpenEmbedding.injective
      change (C.domain.fromSpecStalkOfMem _ hCη ≫ C.domain.ι) (IsLocalRing.closedPoint _) = _
      rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecStalk_closedPoint]
      rfl
    have h2 : χ (IsLocalRing.closedPoint _) = genericPoint P := by
      have : IsLocalHom ρ.hom := isLocalHom_of_isIso ρ
      change P.fromSpecStalk _ (Spec.map ρ (IsLocalRing.closedPoint _)) = _
      rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
    rw [← h1]
    change (C.domain.fromSpecStalkOfMem _ hCη ≫ C.hom) (IsLocalRing.closedPoint _) ∈ U
    rw [hCχ, h2]
    exact hFU hFη
  let W : C.domain.toScheme.Opens := C.hom ⁻¹ᵁ U
  obtain ⟨T₀, hT₀def⟩ : ∃ T₀ : X.Opens, T₀ = C.domain.ι ''ᵁ W := ⟨_, rfl⟩
  have hηT₀ : genericPoint X ∈ T₀ := by
    rw [hT₀def]
    exact ⟨_, hcη, rfl⟩
  have hT₀D : T₀ ≤ C.domain := by
    rw [hT₀def]
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  let m : T₀.toScheme ⟶ P := X.homOfLE hT₀D ≫ C.hom
  have hm : Set.range m ⊆ Set.range U.ι := by
    rintro _ ⟨t, rfl⟩
    rw [Scheme.Opens.range_ι]
    have ht : t.1 ∈ C.domain.ι ''ᵁ W := hT₀def ▸ t.2
    obtain ⟨w, hw, hwt⟩ := ht
    have : X.homOfLE hT₀D t = w := by
      apply C.domain.ι.isOpenEmbedding.injective
      change (X.homOfLE hT₀D ≫ C.domain.ι) t = C.domain.ι w
      rw [Scheme.homOfLE_ι]
      exact hwt.symm
    change C.hom (X.homOfLE hT₀D t) ∈ U
    rw [this]
    exact hw
  let h₀ : T₀.toScheme ⟶ U := IsOpenImmersion.lift U.ι m hm
  have hh₀ : h₀ ≫ U.ι = X.homOfLE hT₀D ≫ C.hom := IsOpenImmersion.lift_fac U.ι m hm
  have hT₀ : T₀.fromSpecStalkOfMem _ hηT₀ ≫ X.homOfLE hT₀D = C.domain.fromSpecStalkOfMem _ hCη := by
    rw [← cancel_mono C.domain.ι, Category.assoc, Scheme.homOfLE_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  -- `h₀ ≫ g` is the inclusion at the generic point.
  have key : T₀.fromSpecStalkOfMem _ hηT₀ ≫ h₀ ≫ g = X.fromSpecStalk (genericPoint X) := by
    have e1 : T₀.fromSpecStalkOfMem _ hηT₀ ≫ h₀ =
        Spec.map ρ ≫ F.domain.fromSpecStalkOfMem _ hFη ≫ P.homOfLE hFU := by
      rw [← cancel_mono U.ι, Category.assoc, hh₀, reassoc_of% hT₀, hCχ, Category.assoc,
        Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
    rw [reassoc_of% e1, hg]
    change Spec.map ρ ≫ F.fromSpecStalkOfMem hFη = _
    rw [hFψ, ← Spec.map_comp_assoc, IsIso.inv_hom_id, Spec.map_id, Category.id_comp]
  let P₁ : X.PartialMap X := ⟨T₀, T₀.2.dense ⟨_, hηT₀⟩, h₀ ≫ g⟩
  obtain ⟨T, hT, hTT₀, hTr, e⟩ := Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq P₁
    (Scheme.PartialMap.id X) hηT₀ trivial (by
      rw [Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap, Category.comp_id]
      exact key)
  refine isSimplyConnected_of_section hX hU g T hT.nonempty (X.homOfLE hTT₀ ≫ h₀) ?_
  simp only [P₁, Scheme.PartialMap.restrict] at e
  rw [Category.assoc, e]
  exact (congrArg (X.homOfLE hTr ≫ ·) (Category.comp_id _)).trans (Scheme.homOfLE_ι X hTr)

end FunctionField

section Structure

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (sX : X ⟶ Spec (.of k))

/-- The generic point `Spec K(X) ⟶ X ⟶ Spec k` is the spectrum of the structure map
`k → K(X)`. -/
lemma fromSpecStalk_comp_eq_SpecMap :
    X.fromSpecStalk (genericPoint X) ≫ sX = Spec.map (CommRingCat.ofHom (functionFieldMap sX)) := by
  rw [functionFieldMap, CommRingCat.ofHom_hom, Spec.map_comp, Spec.map_comp,
    ← Scheme.fromSpecStalk_toSpecΓ_assoc, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.comp_id]

/-- The function field of a `k`-scheme locally of finite type is essentially of finite type over
`k`. -/
lemma essFiniteType_functionFieldMap [LocallyOfFiniteType sX] :
    (functionFieldMap sX).EssFiniteType := by
  have h1 := LocallyOfFiniteType.stalkMap sX (genericPoint X)
  have h2 : functionFieldMap sX = (sX.stalkMap (genericPoint X)).hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec (.of k)).presheaf.germ ⊤ (sX (genericPoint X)) trivial).hom := by
    have e := Scheme.Hom.germ_stalkMap sX ⊤ (genericPoint X) trivial
    rw [functionFieldMap, ← CommRingCat.hom_comp]
    exact congrArg (fun φ ↦ ((Scheme.ΓSpecIso (.of k)).inv ≫ φ).hom) e.symm
  have hsurj : Function.Surjective ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (sX (genericPoint X)) trivial).hom := by
    intro t
    obtain ⟨V, hxV, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq (Spec (.of k)).presheaf t
    have hV : V = ⊤ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      rw [Subsingleton.elim y (sX (genericPoint X))]
      exact hxV
    subst hV
    refine ⟨(Scheme.ΓSpecIso (.of k)).hom a, ?_⟩
    rw [CommRingCat.comp_apply, ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom,
      Iso.hom_inv_id, CommRingCat.id_apply]
  rw [h2]
  exact RingHom.EssFiniteType.comp
    (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_surjective _ hsurj)) h1

end Structure

section Rational

open AlgebraicGeometry.ProjectiveSpace HomogeneousLocalization

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (sX : X ⟶ Spec (.of k))

instance (σ : Type u) [Finite σ] [Nonempty σ] : IsIntegral (Proj (grading σ k)) :=
  ProjectiveSpace.isIntegral_of_isFinite_of_etale (𝟙 _)

instance (σ : Type u) [Finite σ] : LocallyOfFiniteType (projToSpec σ k) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k (grading σ k 0)))) :=
    isIso_SpecMap_iff.2 (bijective_algebraMap_grading_zero σ k)
  rw [projToSpec]
  infer_instance

/-- `Proj k[σ]` is simply connected for every nonempty finite `σ` (`k` algebraically closed). -/
lemma isSimplyConnected_proj' [IsAlgClosed k] (σ : Type u) [Finite σ] [Nonempty σ] :
    IsSimplyConnected (Proj (grading σ k)) := by
  rcases subsingleton_or_nontrivial σ with hσ | hσ
  · have : Unique σ := uniqueOfSubsingleton (Classical.arbitrary σ)
    exact ProjectiveSpace.isSimplyConnected_proj_of_unique k σ
  · exact ProjectiveSpace.isSimplyConnected_proj k σ

omit [IsIntegral X] in
/-- XI.1.2, XI.1.3: a field `L` generated over `k` by a finite algebraically independent set `s`
is isomorphic over `k` to the function field of `ℙ^s = Proj k[x_∞, x_i : i ∈ s]`: the map
`Spec L ⟶ Spec k[x_i] ⊆ ℙ^s` given by `x_i ↦ i` hits the generic point, and the induced map
`K(ℙ^s) = k(x_i) → L` is bijective. -/
theorem exists_functionField_iso_proj (L : Type u) [Field L] [Algebra k L] (s : Set L) [Finite s]
    (hs : AlgebraicIndependent k ((↑) : s → L))
    (hadj : IntermediateField.adjoin k (s : Set L) = ⊤) :
    ∃ (y : Proj (grading (Option s) k)) (_ : y = genericPoint _)
      (ρ : (Proj (grading (Option s) k)).presheaf.stalk y ⟶ CommRingCat.of L),
      IsIso ρ ∧ Spec.map ρ ≫ (Proj (grading (Option s) k)).fromSpecStalk y ≫
        projToSpec (Option s) k = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  classical
  have hN : (MvPolynomial.X none : MvPolynomial (Option s) k) ∈ grading (Option s) k 1 :=
    X_mem_grading none
  let e : {j : Option s // j ≠ none} ≃ s :=
    { toFun := fun j ↦ Option.get j.1 (Option.ne_none_iff_isSome.mp j.2)
      invFun := fun i ↦ ⟨some i, Option.some_ne_none i⟩
      left_inv := fun j ↦ by
        obtain ⟨_ | i, hi⟩ := j
        · exact absurd rfl hi
        · rfl
      right_inv := fun _ ↦ rfl }
  let E : Away (grading (Option s) k) (MvPolynomial.X none) ≃+* MvPolynomial s k :=
    (awayEquiv none rfl).trans (MvPolynomial.renameEquiv k e).toRingEquiv
  let α : Away (grading (Option s) k) (MvPolynomial.X none) →+* L :=
    (MvPolynomial.aeval ((↑) : s → L)).toRingHom.comp E.toRingHom
  have hα : Function.Injective α :=
    (show Function.Injective (MvPolynomial.aeval ((↑) : s → L)) from hs).comp
      E.injective
  have hαE : ∀ p, α (E.symm p) = MvPolynomial.aeval ((↑) : s → L) p := fun p ↦ by
    simp [α]
  have : IsDomain (Away (grading (Option s) k) (MvPolynomial.X none)) :=
    E.toMulEquiv.isDomain _
  let φ : Spec (.of L) ⟶ Spec (.of (Away (grading (Option s) k) (MvPolynomial.X none))) :=
    Spec.map (CommRingCat.ofHom α)
  let ι := Proj.awayι (grading (Option s) k) (MvPolynomial.X none) hN one_pos
  have hφ : φ (IsLocalRing.closedPoint L) = genericPoint _ := by
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext (Ideal.ext fun x ↦ ?_)
    change x ∈ Ideal.comap α (IsLocalRing.maximalIdeal L) ↔ x ∈ (⊥ : Ideal _)
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.comap_bot_of_injective α hα]
  refine ⟨(φ ≫ ι) (IsLocalRing.closedPoint L), ?_,
    Scheme.stalkClosedPointTo (φ ≫ ι), ?_, ?_⟩
  · change ι (φ _) = _
    rw [hφ, genericPoint_eq_of_isOpenImmersion]
  · rw [Scheme.stalkClosedPointTo_comp]
    have h2 : IsIso (Scheme.stalkClosedPointTo φ) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      have hfield : IsField ((Spec (.of (Away (grading (Option s) k)
          (MvPolynomial.X none)))).presheaf.stalk (φ (IsLocalRing.closedPoint _))) := by
        rw [hφ]
        exact Field.toIsField (Spec (.of (Away (grading (Option s) k)
          (MvPolynomial.X none)))).functionField
      let _ := hfield.toField
      refine ⟨(Scheme.stalkClosedPointTo φ).hom.injective, fun z ↦ ?_⟩
      have hρα : ∀ a, (Scheme.stalkClosedPointTo φ).hom
          ((Spec _).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso _).inv a)) = α a := fun a ↦ by
        have h := congrArg (fun f ↦ f.hom ((Scheme.ΓSpecIso _).inv a))
          (Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom α))
        have hinv : (Scheme.ΓSpecIso _).hom.hom ((Scheme.ΓSpecIso _).inv.hom a) = a := by simp
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
        exact h.trans (congrArg α hinv)
      let I : IntermediateField k L :=
        (Scheme.stalkClosedPointTo φ).hom.fieldRange.toIntermediateField fun c ↦
          ⟨_, (hρα (E.symm (MvPolynomial.C c))).trans (by rw [hαE, MvPolynomial.aeval_C])⟩
      have hI : IntermediateField.adjoin k (s : Set L) ≤ I := by
        rw [IntermediateField.adjoin_le_iff]
        intro x hx
        exact ⟨_, (hρα (E.symm (MvPolynomial.X ⟨x, hx⟩))).trans
          (by rw [hαE, MvPolynomial.aeval_X])⟩
      rw [hadj] at hI
      exact hI (IntermediateField.mem_top : z ∈ ⊤)
    have hι : IsOpenImmersion ι :=
      inferInstanceAs (IsOpenImmersion (Proj.awayι (grading (Option s) k) _ hN one_pos))
    have h1 : IsIso (ι.stalkMap (φ (IsLocalRing.closedPoint L))) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp hι).2 _
    exact IsIso.comp_isIso' h1 h2
  · rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc, Category.assoc, awayι_projToSpec]
    change Spec.map (CommRingCat.ofHom α) ≫ _ = _
    rw [← Spec.map_comp]
    congr 1
    ext c
    change α (awayC _ c) = algebraMap k L c
    simp [α, E, awayEquiv_awayC]

/-- XI.1.2: a proper, normal, integral scheme over an algebraically closed field `k` whose
function field is purely transcendental over `k` (a rational variety) is simply connected. -/
theorem isSimplyConnected_of_isPurelyTranscendental [IsAlgClosed k] [IsProper sX]
    (hX : IsNormalScheme X)
    (h : letI := (functionFieldMap sX).toAlgebra; IsPurelyTranscendental k X.functionField) :
    IsSimplyConnected X := by
  let _ := (functionFieldMap sX).toAlgebra
  obtain ⟨s, hs, hadj⟩ := h
  have : Algebra.EssFiniteType k X.functionField := essFiniteType_functionFieldMap sX
  have : Finite s := finite_of_algebraicIndependent hs
  obtain ⟨y, hy, ρ, hρ, hρs⟩ := exists_functionField_iso_proj X.functionField s hs hadj
  let ρ' : (Proj (grading (Option s) k)).presheaf.stalk y ⟶ X.functionField := ρ
  have : IsIso ρ' := hρ
  have hρs' : Spec.map ρ' ≫ (Proj (grading (Option s) k)).fromSpecStalk y ≫
      projToSpec (Option s) k = X.fromSpecStalk (genericPoint X) ≫ sX := by
    rw [fromSpecStalk_comp_eq_SpecMap]
    exact hρs
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from sX]; infer_instance⟩
  exact isSimplyConnected_of_functionField_iso sX (projToSpec (Option s) k)
    (fun x ↦ ⟨inferInstance, hX x⟩) (ProjectiveSpace.isRegularScheme_proj k _)
    (isSimplyConnected_proj' _) hy ρ' hρs'

/-- XI.1.2: `RationalSimplyConnectedStatement` holds. -/
theorem rationalSimplyConnectedStatement : RationalSimplyConnectedStatement.{u} :=
  fun _ _ _ _ _ f _ hX h ↦ isSimplyConnected_of_isPurelyTranscendental f hX h

end Rational

end SGA.SGA1.ExposeXI
