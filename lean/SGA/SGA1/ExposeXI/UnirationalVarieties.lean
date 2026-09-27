/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeXI.RationalVarieties

/-!
# Unirational varieties have finite fundamental group (XI.1.3)

XI.1.3: the fundamental group of a proper normal integral scheme `X` over an algebraically closed
field `k` whose function field `K` is unirational (contained in a purely transcendental extension
`K'` of `k`, finite over `K`) is finite (`hasFiniteFundamentalGroup_of_isUnirational`,
`unirationalFiniteFundamentalGroupStatement`). SGA's argument, with `K' = K(ℙʳ)`
(`exists_functionField_iso_proj`):

* the dominant rational map `ℙʳ ⇢ X` is defined on an open `U ⊆ ℙʳ` whose complement has
  codimension `≥ 2`, and `U` is simply connected (purity X.3.3 and XI.1.1);
* for a connected étale covering `Z` of `X`, the pullback to `U` is completely decomposed, so each
  geometric point of `Z` over a point of `U` gives a lift `U ⟶ Z`
  (`exists_injective_fiber_lifts`); a lift is determined by a `K`-embedding of `K(Z)` into `K'`,
  so there are at most `[K' : K]` of them (`card_lifts_le`);
* a Galois category whose connected objects have fibres of bounded cardinality has finite
  fundamental group (`finite_aut_of_forall_card_fiber_le`).
-/

universe u w

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeXI

section Galois

variable {C : Type*} [Category C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- In a Galois category, if the fibres of the connected objects have bounded cardinality, the
fundamental group `Aut F` is finite: a connected object `G` with fibre of maximal cardinality
dominates every connected object, so `Aut F` acts faithfully on `F(G)`. -/
theorem finite_aut_of_forall_card_fiber_le (N : ℕ)
    (h : ∀ Z : C, IsConnected Z → Nat.card (F.obj Z) ≤ N) : Finite (Aut F) := by
  classical
  let Pr : ℕ → Prop := fun n ↦ ∃ Z : C, IsConnected Z ∧ Nat.card (F.obj Z) = n
  obtain ⟨T, i, t, -, hT, -⟩ := fiber_in_connected_component F (⊤_ C)
    (((terminalIsTerminal.isTerminalObj F _).from (FintypeCat.of PUnit)) PUnit.unit)
  have hPr : Pr (Nat.card (F.obj T)) := ⟨T, hT, rfl⟩
  have hm : Pr (Nat.findGreatest Pr N) := Nat.findGreatest_spec (h T hT) hPr
  obtain ⟨G, hG, hGm⟩ := hm
  have hmax : ∀ Z : C, IsConnected Z → Nat.card (F.obj Z) ≤ Nat.card (F.obj G) := fun Z hZ ↦ by
    rw [hGm]
    exact Nat.le_findGreatest (h Z hZ) ⟨Z, hZ, rfl⟩
  -- `G` dominates every connected object.
  have hdom : ∀ Z : C, IsConnected Z → Nonempty (G ⟶ Z) := by
    intro Z hZ
    obtain ⟨g⟩ := nonempty_fiber_of_isConnected F G
    obtain ⟨z⟩ := nonempty_fiber_of_isConnected F Z
    obtain ⟨A, j, a, -, hA, -⟩ := fiber_in_connected_component F (G ⨯ Z)
      ((fiberBinaryProductEquiv F G Z).symm (g, z))
    have : Nonempty (F.obj A) := ⟨a⟩
    have hsurj := surjective_of_nonempty_fiber_of_isConnected F (j ≫ prod.fst)
    have hcard : Nat.card (F.obj A) = Nat.card (F.obj G) :=
      le_antisymm (hmax A hA) (Nat.card_le_card_of_surjective _ hsurj)
    have hbij : Function.Bijective (F.map (j ≫ prod.fst)) :=
      (Function.Surjective.bijective_of_nat_card_le hsurj hcard.le)
    have : IsIso (F.map (j ≫ prod.fst)) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    have : IsIso (j ≫ prod.fst) := isIso_of_reflects_iso _ F
    exact ⟨inv (j ≫ prod.fst) ≫ j ≫ prod.snd⟩
  -- `Aut F` acts faithfully on `F(G)`.
  refine Finite.of_injective (fun σ : Aut F ↦ (ConcreteCategory.hom (σ.hom.app G) :
    F.obj G → F.obj G)) fun σ τ hστ ↦ ?_
  refine Iso.ext (natTrans_ext_of_isGalois F fun A _ ↦ ?_)
  obtain ⟨f⟩ := hdom A inferInstance
  have hsurj := surjective_of_nonempty_fiber_of_isConnected F f
  ext a
  obtain ⟨b, rfl⟩ := hsurj a
  simp only [FunctorToFintypeCat.naturality]
  exact congrArg _ (congrFun hστ b)

end Galois

section Lifts

variable {U X : Scheme.{u}}

/-- Over a simply connected scheme `U`, every geometric point of `Z` over `u ≫ g` comes from a
lift `ℓ : U ⟶ Z` of `g : U ⟶ X`: the geometric points of the pullback `g*Z` over `u` lie on
connected components of `g*Z`, which are trivial coverings of `U`. -/
lemma exists_lift_of_isSimplyConnected (hU : IsSimplyConnected U) (g : U ⟶ X)
    (Z : ExposeV.FEt X) (Ω : Type u) [Field Ω] [IsSepClosed Ω] (u : Spec (.of Ω) ⟶ U)
    (z : (ExposeV.FEt.fiber Ω (u ≫ g)).obj Z) :
    ∃ ℓ : U ⟶ Z.left, ℓ ≫ Z.hom = g ∧ ExposeV.FEt.fiberPoint Ω z = u ≫ ℓ := by
  have := hU.1
  let e := (ExposeV.FEt.pullbackFiberIso Ω g u).app Z
  let w := e.inv z
  have hz : e.hom w = z := by simp [w]
  obtain ⟨A, i, a, hia, hA, -⟩ :=
    fiber_in_connected_component (ExposeV.FEt.fiber Ω u) ((ExposeV.FEt.pullback g).obj Z) w
  have : ConnectedSpace A.left := ExposeV.FEt.connectedSpace_of_isConnected A
  have : IsIso A.hom := hU.2 A.hom ‹_›
  have hi : i.left ≫ pullback.snd Z.hom g = A.hom :=
    CategoryTheory.Over.w ((MorphismProperty.Over.forget _ ⊤ U).map i)
  have ha : ExposeV.FEt.fiberPoint Ω a = u ≫ inv A.hom := by
    rw [IsIso.eq_comp_inv]
    exact ExposeV.FEt.fiberPoint_comp Ω a
  refine ⟨inv A.hom ≫ i.left ≫ pullback.fst Z.hom g, ?_, ?_⟩
  · calc (inv A.hom ≫ i.left ≫ pullback.fst Z.hom g) ≫ Z.hom
        = inv A.hom ≫ i.left ≫ pullback.fst Z.hom g ≫ Z.hom :=
          (Category.assoc _ _ _).trans (congrArg (inv A.hom ≫ ·) (Category.assoc _ _ _))
      _ = inv A.hom ≫ (i.left ≫ pullback.snd Z.hom g) ≫ g :=
          congrArg (fun m ↦ inv A.hom ≫ i.left ≫ m) pullback.condition
      _ = g := by rw [hi, IsIso.inv_hom_id_assoc]
  · have h1 := ExposeV.FEt.fiberPoint_pullbackFiberIso Ω g u Z w
    have h2 := ExposeV.FEt.fiberPoint_map Ω i a
    rw [hia] at h2
    calc ExposeV.FEt.fiberPoint Ω z
        = ExposeV.FEt.fiberPoint Ω w ≫ pullback.fst Z.hom g := hz ▸ h1
      _ = (ExposeV.FEt.fiberPoint Ω a ≫ i.left) ≫ pullback.fst Z.hom g :=
          congrArg (· ≫ pullback.fst Z.hom g) h2
      _ = u ≫ inv A.hom ≫ i.left ≫ pullback.fst Z.hom g := by
          rw [ha]
          exact (Category.assoc _ _ _).trans (congrArg (u ≫ ·) (Category.assoc _ _ _))

/-- Over a simply connected scheme `U`, the geometric points of `Z` over `u ≫ g` inject into the
lifts of `g : U ⟶ X` to `Z`. -/
lemma exists_injective_fiber_lifts (hU : IsSimplyConnected U) (g : U ⟶ X)
    (Z : ExposeV.FEt X) (Ω : Type u) [Field Ω] [IsSepClosed Ω] (u : Spec (.of Ω) ⟶ U) :
    ∃ f : (ExposeV.FEt.fiber Ω (u ≫ g)).obj Z → {ℓ : U ⟶ Z.left // ℓ ≫ Z.hom = g},
      Function.Injective f := by
  choose ℓ hℓ hpt using exists_lift_of_isSimplyConnected hU g Z Ω u
  refine ⟨fun z ↦ ⟨ℓ z, hℓ z⟩, fun z₁ z₂ h ↦ ExposeV.FEt.fiber_ext_point Ω ?_⟩
  rw [hpt, hpt]
  exact congrArg (u ≫ ·) (congrArg Subtype.val h)

end Lifts

section Count

/-- A ring homomorphism from a division ring to a nontrivial ring is local. -/
lemma isLocalHom_of_divisionRing {K R : Type*} [DivisionRing K] [Semiring R] [Nontrivial R]
    (f : K →+* R) : IsLocalHom f := by
  refine ⟨fun a ha ↦ ?_⟩
  rcases eq_or_ne a 0 with rfl | h0
  · rw [map_zero] at ha
    exact absurd ha not_isUnit_zero
  · exact isUnit_iff_ne_zero.mpr h0

/-- In a discrete subset, specialization is equality. -/
lemma eq_of_specializes_of_isDiscrete {T : Type*} [TopologicalSpace T] {s : Set T}
    (hs : IsDiscrete s) {x y : T} (hx : x ∈ s) (hy : y ∈ s) (h : x ⤳ y) : x = y := by
  have := hs.to_subtype
  obtain ⟨V, hV, hVy⟩ := isOpen_induced_iff.mp (isOpen_discrete ({⟨y, hy⟩} : Set s))
  have hyV : y ∈ V := by
    have : (⟨y, hy⟩ : s) ∈ Subtype.val ⁻¹' V := by rw [hVy]; rfl
    exact this
  have : (⟨x, hx⟩ : s) ∈ Subtype.val ⁻¹' V := h.mem_open hV hyV
  rw [hVy] at this
  exact congrArg Subtype.val this

variable {Y : Scheme.{u}}

/-- A morphism `Spec R ⟶ Y` (`R` local) through `Y.fromSpecStalk y` determines the ring map. -/
lemma SpecMap_fromSpecStalk_injective {R : CommRingCat.{u}} [IsLocalRing R] {y : Y}
    {a b : Y.presheaf.stalk y ⟶ R} [IsLocalHom a.hom] [IsLocalHom b.hom]
    (h : Spec.map a ≫ Y.fromSpecStalk y = Spec.map b ≫ Y.fromSpecStalk y) : a = b := by
  have := (SpecToEquivOfLocalRing Y R).symm.injective (a₁ := ⟨y, a, ‹_›⟩) (a₂ := ⟨y, b, ‹_›⟩) h
  obtain ⟨h₁, e⟩ := SpecToEquivOfLocalRing_eq_iff.mp this
  simpa using e

/-- A morphism `Spec R ⟶ Y` (`R` local) whose closed point maps to `y` factors through
`Y.fromSpecStalk y`. -/
lemma exists_SpecMap_fromSpecStalk {R : CommRingCat.{u}} [IsLocalRing R] (m : Spec R ⟶ Y) (y : Y)
    (hy : m (IsLocalRing.closedPoint R) = y) :
    ∃ a : Y.presheaf.stalk y ⟶ R, IsLocalHom a.hom ∧ Spec.map a ≫ Y.fromSpecStalk y = m := by
  subst hy
  exact ⟨_, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk m⟩

variable {W Z X : Scheme.{u}} [IsIntegral W] [IsIntegral Z] [IsIntegral X]

/-- XI.1.3, the counting: let `p : Z ⟶ X` be separated and locally quasi-finite (e.g. finite
étale), `g : W ⟶ X`, with `W`, `Z`, `X` integral and `p`, `g` mapping generic points to the
generic point, and let `K(W)` be finite over `K(X)` (via `ι : K(X) → K(W)`, the map induced by
`g` at the generic point). Then the lifts `W ⟶ Z` of `g` are at most `[K(W) : K(X)]` in number:
a lift maps the generic point of `W` to that of `Z` (the fibres of `p` are discrete), so it is
determined by a `K(X)`-embedding `K(Z) → K(W)`. -/
theorem card_lifts_le (p : Z ⟶ X) [IsSeparated p] [LocallyQuasiFinite p] (g : W ⟶ X)
    (hp : p (genericPoint Z) = genericPoint X) (hg : g (genericPoint W) = genericPoint X)
    {w : W} (hw : w = genericPoint W) (ι : X.functionField ⟶ W.presheaf.stalk w)
    (hι : Spec.map ι ≫ X.fromSpecStalk (genericPoint X) = W.fromSpecStalk w ≫ g)
    (hfin : letI := ι.hom.toAlgebra; Module.Finite X.functionField (W.presheaf.stalk w)) :
    Finite {ℓ : W ⟶ Z // ℓ ≫ p = g} ∧ Nat.card {ℓ : W ⟶ Z // ℓ ≫ p = g} ≤
      (letI := ι.hom.toAlgebra; Module.finrank X.functionField (W.presheaf.stalk w)) := by
  classical
  subst hw
  let _ : Algebra X.functionField W.functionField := ι.hom.toAlgebra
  have : IsLocalHom ι.hom := isLocalHom_of_divisionRing _
  -- The `K(X)`-algebra `K(Z)`.
  obtain ⟨ιZ, -, hιZ⟩ := exists_SpecMap_fromSpecStalk
    (Z.fromSpecStalk (genericPoint Z) ≫ p) (genericPoint X)
    (by
      change p (Z.fromSpecStalk _ (IsLocalRing.closedPoint _)) = _
      rw [Scheme.fromSpecStalk_closedPoint, hp])
  let _ : Algebra X.functionField Z.functionField := ιZ.hom.toAlgebra
  -- Every lift maps the generic point of `W` to that of `Z`.
  have hlift : ∀ ℓ : W ⟶ Z, ℓ ≫ p = g → ℓ (genericPoint W) = genericPoint Z := by
    intro ℓ hℓ
    refine (eq_of_specializes_of_isDiscrete (p.isDiscrete_preimage_singleton (genericPoint X))
      (Set.mem_preimage.mpr hp) ?_ (genericPoint_specializes _)).symm
    change (ℓ ≫ p) (genericPoint W) = genericPoint X
    rw [hℓ, hg]
  have hex : ∀ ℓ : {ℓ : W ⟶ Z // ℓ ≫ p = g}, ∃ φ : Z.functionField ⟶ W.functionField,
      IsLocalHom φ.hom ∧
        Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z) = W.fromSpecStalk (genericPoint W) ≫ ℓ.1 :=
    fun ℓ ↦ exists_SpecMap_fromSpecStalk _ _ (by
      change ℓ.1 (W.fromSpecStalk _ (IsLocalRing.closedPoint _)) = _
      rw [Scheme.fromSpecStalk_closedPoint, hlift ℓ.1 ℓ.2])
  choose φ hφloc hφ using hex
  have halg : ∀ ℓ, ιZ ≫ φ ℓ = ι := by
    intro ℓ
    have : IsLocalHom (ιZ ≫ φ ℓ).hom := isLocalHom_of_divisionRing _
    apply SpecMap_fromSpecStalk_injective (y := genericPoint X)
    rw [Spec.map_comp, Category.assoc, hιZ, ← Category.assoc, hφ ℓ, Category.assoc, ℓ.2, hι]
  let f : {ℓ : W ⟶ Z // ℓ ≫ p = g} → (Z.functionField →ₐ[X.functionField] W.functionField) :=
    fun ℓ ↦ { (φ ℓ).hom with commutes' := fun r ↦ congrArg (fun m ↦ m.hom r) (halg ℓ) }
  have hinj : Function.Injective f := by
    intro ℓ₁ ℓ₂ h
    have e : φ ℓ₁ = φ ℓ₂ := CommRingCat.hom_ext (congrArg AlgHom.toRingHom h)
    apply Subtype.ext
    refine ext_of_fromSpecResidueField_eq ℓ₁.1 ℓ₂.1 p {genericPoint W}
      (by rw [dense_iff_closure_eq]; exact genericPoint_spec W) ?_ (ℓ₁.2.trans ℓ₂.2.symm)
    rintro x rfl
    rw [Scheme.fromSpecResidueField, Category.assoc, Category.assoc, ← hφ ℓ₁, ← hφ ℓ₂, e]
  rcases isEmpty_or_nonempty {ℓ : W ⟶ Z // ℓ ≫ p = g} with hE | hne
  · exact ⟨inferInstance, by simp⟩
  obtain ⟨ℓ₀⟩ := hne
  -- `K(Z)` embeds into `K(W)`, hence is finite over `K(X)`.
  have hinj₀ : Function.Injective (f ℓ₀).toLinearMap := (f ℓ₀).toRingHom.injective
  have : Module.Finite X.functionField Z.functionField :=
    Module.Finite.of_injective (f ℓ₀).toLinearMap hinj₀
  have : Finite (Z.functionField →ₐ[X.functionField] W.functionField) := inferInstance
  refine ⟨Finite.of_injective f hinj, ?_⟩
  calc Nat.card {ℓ : W ⟶ Z // ℓ ≫ p = g}
      ≤ Nat.card (Z.functionField →ₐ[X.functionField] W.functionField) :=
        Nat.card_le_card_of_injective f hinj
    _ ≤ Module.finrank X.functionField Z.functionField :=
        card_algHom_le_finrank _ _ _
    _ ≤ Module.finrank X.functionField W.functionField :=
        LinearMap.finrank_le_finrank_of_injective hinj₀

end Count

section Dominant

/-- A connected étale covering of a normal locally noetherian scheme is integral. -/
lemma isIntegral_of_etale_of_isNormalScheme {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : ExposeX.IsNormalScheme X) (f : Y ⟶ X) [Etale f] [LocallyOfFiniteType f]
    [ConnectedSpace Y] : IsIntegral Y := by
  have hY := ExposeI.isNormalScheme_of_etale f hX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : IrreducibleSpace Y := ExposeI.irreducibleSpace_of_isDomain_stalk fun y ↦ (hY y).1
  have : IsReduced Y := by
    have (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
      have := (hY y).1
      infer_instance
    exact isReduced_of_isReduced_stalk Y
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

/-- A surjective morphism of irreducible schemes maps the generic point to the generic point. -/
lemma genericPoint_eq_of_surjective {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : Y ⟶ X) (hf : Function.Surjective f) : f (genericPoint Y) = genericPoint X := by
  have h := (genericPoint_spec Y).image f.continuous
  rw [Set.image_univ, hf.range_eq, closure_univ] at h
  exact h.eq (genericPoint_spec X)

variable {S X P : Scheme.{u}} (sX : X ⟶ S) (sP : P ⟶ S) [IsIntegral X] [IsIntegral P]
  [IsLocallyNoetherian X] [IsLocallyNoetherian P] [LocallyOfFiniteType sX] [UniversallyClosed sX]
  [X.IsSeparated]

/-- XI.1.3, general form: let `X` be integral, normal, locally noetherian, separated, universally
closed and locally of finite type over `S`, and `P` integral, regular, locally noetherian, locally
of finite type over `S` and simply connected. If the function field of `P` is a finite extension
of that of `X` over `S` (`τ : K(X) → K(P)`, a dominant generically finite rational map
`P ⇢ X`), then the fundamental group of `X` is finite.

The rational map is defined on an open `U ⊆ P` whose complement has codimension `≥ 2`, and `U`
is simply connected (purity X.3.3 and XI.1.1). So the pullback to `U` of a connected étale
covering `Z` of `X` is trivial: the points of `Z` over a geometric point give lifts `U ⟶ Z`
(`exists_injective_fiber_lifts`), and there are at most `[K(P) : K(X)]` of them
(`card_lifts_le`). The fibres of connected coverings are thus bounded, so `π₁(X)` is finite
(`finite_aut_of_forall_card_fiber_le`). -/
theorem hasFiniteFundamentalGroup_of_functionField_finite (hX : ExposeX.IsNormalScheme X)
    (hP : ExposeX.IsRegularScheme P) (hPs : IsSimplyConnected P) {y : P}
    (hy : y = genericPoint P) (τ : X.functionField ⟶ P.presheaf.stalk y)
    (hτ : Spec.map τ ≫ X.fromSpecStalk (genericPoint X) ≫ sX = P.fromSpecStalk y ≫ sP)
    (hfin : letI := τ.hom.toAlgebra; Module.Finite X.functionField (P.presheaf.stalk y)) :
    HasFiniteFundamentalGroup X := by
  subst hy
  let ψ : Spec (P.presheaf.stalk (genericPoint P)) ⟶ X :=
    Spec.map τ ≫ X.fromSpecStalk (genericPoint X)
  have hψ : ψ ≫ sX = P.fromSpecStalk (genericPoint P) ≫ sP := by
    rw [Category.assoc]
    exact hτ
  -- Extend `ψ` to an open `U` of `P` with complement of codimension `≥ 2`.
  let F := Scheme.PartialMap.ofFromSpecStalk sP sX ψ hψ
  have hFη : genericPoint P ∈ F.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk sP sX ψ hψ
  have hFψ : F.domain.fromSpecStalkOfMem _ hFη ≫ F.hom = ψ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sP sX ψ hψ
  have hF : F.hom ≫ sX = F.domain.ι ≫ sP := Scheme.PartialMap.ofFromSpecStalk_comp sP sX ψ hψ
  obtain ⟨U, hFU, g, hg, hcodim⟩ := ExposeX.exists_extension_of_isRegularScheme sP sX hP F hF
  have := ExposeX.isEquivalence_pullback_of_isRegularScheme hP U hcodim
  have hηU : genericPoint P ∈ U := hFU hFη
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hU : IsSimplyConnected U :=
    isSimplyConnected_of_equivalence (ExposeV.FEt.pullback U.ι).asEquivalence.symm hPs
  -- The generic point `w` of `U`, and `g` at `w`.
  let w : U.toScheme := ⟨genericPoint P, hηU⟩
  have hw : w = genericPoint U := by
    apply U.ι.isOpenEmbedding.injective
    rw [genericPoint_eq_of_isOpenImmersion U.ι]
    rfl
  let sm : P.presheaf.stalk (genericPoint P) ⟶ U.toScheme.presheaf.stalk w := U.ι.stalkMap w
  have : IsIso sm := inferInstanceAs (IsIso (U.ι.stalkMap w))
  have hUw : U.toScheme.fromSpecStalk w ≫ g = Spec.map sm ≫ ψ := by
    have e0 : Spec.map sm ≫ Spec.map (inv sm) = 𝟙 _ := by
      rw [← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id]
    have e1 : U.toScheme.fromSpecStalk w =
        Spec.map sm ≫ U.fromSpecStalkOfMem (genericPoint P) hηU :=
      ((Category.id_comp _).symm.trans (congrArg (· ≫ U.toScheme.fromSpecStalk w) e0.symm)).trans
        (Category.assoc _ _ _)
    have e2 : U.fromSpecStalkOfMem (genericPoint P) hηU =
        F.domain.fromSpecStalkOfMem _ hFη ≫ P.homOfLE hFU := by
      rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι]
    rw [e1, e2]
    exact (Category.assoc _ _ _).trans (congrArg (Spec.map sm ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg _ hg).trans hFψ)))
  have hgw : g (genericPoint U) = genericPoint X := by
    rw [← hw]
    have h := congrArg (fun m ↦ m (IsLocalRing.closedPoint _)) hUw
    have : IsLocalHom sm.hom := isLocalHom_of_isIso _
    have : IsLocalHom τ.hom := isLocalHom_of_divisionRing _
    change g (U.toScheme.fromSpecStalk w (IsLocalRing.closedPoint _)) =
      X.fromSpecStalk _ (Spec.map τ (Spec.map sm (IsLocalRing.closedPoint _))) at h
    simpa only [Scheme.fromSpecStalk_closedPoint, Spec_closedPoint] using h
  -- The field `K(U) = K(P)` is finite over `K(X)`.
  let ι : X.functionField ⟶ U.toScheme.presheaf.stalk w := τ ≫ sm
  have hι : Spec.map ι ≫ X.fromSpecStalk (genericPoint X) = U.toScheme.fromSpecStalk w ≫ g := by
    rw [hUw, Spec.map_comp, Category.assoc]
  have hfin' : letI := ι.hom.toAlgebra
      Module.Finite X.functionField (U.toScheme.presheaf.stalk w) := by
    let _ := τ.hom.toAlgebra
    let _ := ι.hom.toAlgebra
    let e : P.presheaf.stalk (genericPoint P) ≃ₐ[X.functionField] U.toScheme.presheaf.stalk w :=
      AlgEquiv.ofRingEquiv (f := (asIso sm).commRingCatIsoToRingEquiv) fun _ ↦ rfl
    exact Module.Finite.equiv e.toLinearEquiv
  -- The fibres of connected coverings are bounded.
  rw [hasFiniteFundamentalGroup_iff_exists]
  let u := ExposeV.geometricPointAt U w
  refine ⟨_, inferInstance, inferInstance, u ≫ g, ?_⟩
  refine finite_aut_of_forall_card_fiber_le _
    (letI := ι.hom.toAlgebra; Module.finrank X.functionField (U.toScheme.presheaf.stalk w))
    fun Z hZ ↦ ?_
  have : ConnectedSpace Z.left := ExposeV.FEt.connectedSpace_of_isConnected Z
  let p : Z.left ⟶ X := Z.hom
  have : IsFinite p := Z.prop.1
  have : Etale p := Z.prop.2
  have : IsIntegral Z.left := isIntegral_of_etale_of_isNormalScheme hX p
  have hp : p (genericPoint Z.left) = genericPoint X :=
    genericPoint_eq_of_surjective p (ProjectiveSpace.surjective_of_isFinite_of_etale p)
  obtain ⟨f, hf⟩ := exists_injective_fiber_lifts hU g Z _ u
  obtain ⟨hfinL, hcard⟩ := card_lifts_le p g hp hgw hw ι hι hfin'
  exact (Nat.card_le_card_of_injective f hf).trans hcard

end Dominant

section Unirational

open AlgebraicGeometry.ProjectiveSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (sX : X ⟶ Spec (.of k))

/-- XI.1.3: the fundamental group of a proper, normal, integral scheme over an algebraically
closed field `k` whose function field `K` is unirational (contained in a purely transcendental
extension of `k`, finite over `K`) is finite. -/
theorem hasFiniteFundamentalGroup_of_isUnirational [IsAlgClosed k] [IsProper sX]
    (hX : IsNormalScheme X)
    (h : letI := (functionFieldMap sX).toAlgebra; IsUnirational k X.functionField) :
    HasFiniteFundamentalGroup X := by
  let _ := (functionFieldMap sX).toAlgebra
  obtain ⟨L, _, _, _, hL⟩ := h
  let _ : Algebra k L := ((algebraMap X.functionField L).comp (algebraMap k _)).toAlgebra
  have : IsScalarTower k X.functionField L := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨s, hs, hadj⟩ := hL
  have : Algebra.EssFiniteType k X.functionField := essFiniteType_functionFieldMap sX
  have : Algebra.EssFiniteType k L := Algebra.EssFiniteType.comp k X.functionField L
  have : Finite s := finite_of_algebraicIndependent hs
  obtain ⟨y, hy, ρ, hρ, hρs⟩ := exists_functionField_iso_proj L s hs hadj
  let τ : X.functionField ⟶ (Proj (grading (Option s) k)).presheaf.stalk y :=
    CommRingCat.ofHom (algebraMap X.functionField L) ≫ inv ρ
  have hτ : Spec.map τ ≫ X.fromSpecStalk (genericPoint X) ≫ sX =
      (Proj (grading (Option s) k)).fromSpecStalk y ≫ projToSpec (Option s) k := by
    rw [fromSpecStalk_comp_eq_SpecMap, ← Spec.map_comp]
    have e : CommRingCat.ofHom (functionFieldMap sX) ≫ τ =
        CommRingCat.ofHom (algebraMap k L) ≫ inv ρ := rfl
    rw [e, Spec.map_comp, ← hρs, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id,
      Category.id_comp]
  have hfin : letI := τ.hom.toAlgebra
      Module.Finite X.functionField ((Proj (grading (Option s) k)).presheaf.stalk y) := by
    let _ := τ.hom.toAlgebra
    let e : L ≃ₐ[X.functionField] (Proj (grading (Option s) k)).presheaf.stalk y :=
      AlgEquiv.ofRingEquiv (f := (asIso ρ).symm.commRingCatIsoToRingEquiv) fun _ ↦ rfl
    exact Module.Finite.equiv e.toLinearEquiv
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from sX]; infer_instance⟩
  exact hasFiniteFundamentalGroup_of_functionField_finite sX (projToSpec (Option s) k)
    (fun x ↦ ⟨inferInstance, hX x⟩) (ProjectiveSpace.isRegularScheme_proj k _)
    (isSimplyConnected_proj' _) hy τ hτ hfin

/-- XI.1.3: `UnirationalFiniteFundamentalGroupStatement` holds. -/
theorem unirationalFiniteFundamentalGroupStatement :
    UnirationalFiniteFundamentalGroupStatement.{u} :=
  fun _ _ _ _ _ f _ hX h ↦ hasFiniteFundamentalGroup_of_isUnirational f hX h

end Unirational

end SGA.SGA1.ExposeXI
