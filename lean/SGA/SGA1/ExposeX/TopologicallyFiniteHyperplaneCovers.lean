/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.TopologicallyFiniteHyperplane
import SGA.SGA1.ExposeX.ProperOverField
import SGA.SGA1.ExposeX.BaseChangeAlgClosed
import SGA.Foundations.Projective.BertiniCovers
import SGA.SGA1.ExposeI.DominantUnramified
import SGA.SGA1.ExposeXI.UnirationalVarieties

/-!
# SGA 1, Exposé X, 2.10: the generic hyperplane section and étale covers

Let `X` be a normal integral proper scheme over an algebraically closed field `k` and `E ⟶ X` a
connected finite étale cover. The generic fibre `E ×_X Spec K(X)` of `E` is the spectrum of a
field `B` (`Hyperplane.isField_genericFibre`), finite over `K(X)`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace SGA.SGA1.ExposeX.Hyperplane

section GenericFibre

variable {X E : Scheme.{u}} [IsIntegral X] (q : E ⟶ X) [IsFinite q] [Etale q]

/-- The generic fibre `E ×_X Spec K(X)` of `q : E ⟶ X`. -/
noncomputable abbrev genericFibre : Scheme.{u} := pullback q (X.fromSpecStalk (genericPoint X))

/-- A finite étale morphism from a nonempty scheme to a connected scheme is surjective (its range
is open, closed and nonempty). -/
lemma surjective_of_isFinite_of_etale [Nonempty E] : Function.Surjective q := by
  have hcl : IsClopen (Set.range q) := ⟨q.isClosedMap.isClosed_range, q.isOpenMap.isOpen_range⟩
  obtain ⟨e⟩ := ‹Nonempty E›
  exact Set.range_eq_univ.mp (hcl.eq_univ ⟨_, e, rfl⟩)

instance [Nonempty E] : Nonempty (genericFibre q) := by
  obtain ⟨e, he⟩ := surjective_of_isFinite_of_etale q (genericPoint X)
  obtain ⟨g, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q)
    (g := X.fromSpecStalk (genericPoint X)) e (IsLocalRing.closedPoint _)
    (he.trans Scheme.fromSpecStalk_closedPoint.symm)
  exact ⟨g⟩

instance : IsAffine (genericFibre q) := isAffine_of_isAffineHom (pullback.snd q _)

/-- The generic fibre of a connected finite étale cover of a normal integral locally noetherian
scheme has a single point: the generic point of `E` is the only point of `E` over the generic
point of `X` (incomparability, `E` being irreducible). -/
lemma subsingleton_genericFibre [IsLocallyNoetherian X] [ConnectedSpace E]
    (hX : ExposeI.IsNormalScheme X) : Subsingleton (genericFibre q) := by
  have : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian q
  have hE := ExposeI.isNormalScheme_of_etale q hX
  have : IrreducibleSpace E := ExposeI.irreducibleSpace_of_isDomain_stalk fun e ↦ (hE e).1
  have hq : q (genericPoint E) = genericPoint X :=
    ExposeXI.genericPoint_eq_of_surjective q (surjective_of_isFinite_of_etale q)
  have : IsPreimmersion (pullback.fst q (X.fromSpecStalk (genericPoint X))) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback q _).flip inferInstance
  refine ⟨fun g g' ↦ (pullback.fst q _).isEmbedding.injective ?_⟩
  have hgen (g : genericFibre q) : pullback.fst q _ g = genericPoint E := by
    have h1 : q (pullback.fst q _ g) = genericPoint X := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      have : (pullback.snd q (X.fromSpecStalk (genericPoint X))) g =
          IsLocalRing.closedPoint X.functionField := Subsingleton.elim _ _
      rw [this]
      exact Scheme.fromSpecStalk_closedPoint
    exact (q.eq_of_specializes_of_isIntegralHom
      ((genericPoint_spec E).specializes (Set.mem_univ _)) (hq.trans h1.symm)).symm
  rw [hgen g, hgen g']

/-- **The generic fibre of a connected finite étale cover of a normal integral scheme is the
spectrum of a field**: `Γ(E ×_X Spec K(X))` is a field. -/
theorem isField_genericFibre [IsLocallyNoetherian X] [ConnectedSpace E]
    (hX : ExposeI.IsNormalScheme X) : IsField Γ(genericFibre q, ⊤) := by
  have := subsingleton_genericFibre q hX
  have : Nonempty (genericFibre q) := by
    have : Nonempty E := inferInstance
    infer_instance
  have : AlgebraicGeometry.IsReduced (genericFibre q) :=
    ExposeI.isReduced_of_etale (pullback.snd q (X.fromSpecStalk (genericPoint X)))
  have : Nonempty (⊤ : (genericFibre q).Opens) := ⟨⟨Classical.arbitrary _, trivial⟩⟩
  have : Nontrivial Γ(genericFibre q, ⊤) := Scheme.component_nontrivial _ ⊤
  refine isField_of_isReduced_of_subsingleton ⟨fun a b ↦ ?_⟩
  let e := (genericFibre q).isoSpec.inv
  have hinj : Function.Injective e := e.homeomorph.injective
  exact hinj (Subsingleton.elim _ _)

omit [Etale q] in
/-- The generic fibre is finite over `K(X)`. -/
lemma finite_genericFibre :
    (pullback.snd q (X.fromSpecStalk (genericPoint X))).specStructureRingHom.Finite :=
  finite_specStructureRingHom _

end GenericFibre

/-- A morphism `f : G ⟶ Spec R` from an affine scheme is `Spec` of `R → Γ(G, 𝒪_G)`. -/
lemma isoSpec_inv_comp_eq {G : Scheme.{u}} [IsAffine G] {R : CommRingCat.{u}} (f : G ⟶ Spec R) :
    G.isoSpec.inv ≫ f = Spec.map (CommRingCat.ofHom f.specStructureRingHom) := by
  rw [Iso.inv_comp_eq, Scheme.isoSpec, asIso_hom, Scheme.Hom.specStructureRingHom,
    CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  exact (Category.comp_id f).symm

/-- A scheme with an injective map into a subsingleton is a subsingleton. -/
lemma subsingleton_of_iso {A B : Scheme.{u}} (e : A ≅ B) [Subsingleton B] : Subsingleton A :=
  ⟨fun _ _ ↦ e.hom.homeomorph.injective (Subsingleton.elim _ _)⟩

section Cover

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (s : X ⟶ Spec (.of k))
  [Algebra k X.functionField] (hk : algebraMap k X.functionField = ExposeXI.functionFieldMap s)
  {x y : X.functionField} (hxy : AlgebraicIndependent k ![x, y])
  {E : Scheme.{u}} (q : E ⟶ X)

/-- `W ⟶ X`. -/
noncomputable abbrev toX : W s hk hxy ⟶ X :=
  (genericSection s hk hxy).imageι ≫ pullback.fst s (baseMap k)

/-- The pullback `W ×_X E` of the generic hyperplane section to a cover `E` of `X`. -/
noncomputable abbrev W₃ : Scheme.{u} := pullback q (toX s hk hxy)

lemma toImage_toX : (genericSection s hk hxy).toImage ≫ toX s hk hxy =
    Spec.map (CommRingCat.ofHom (RatFunc.C : X.functionField →+* RatFunc X.functionField)) ≫
      X.fromSpecStalk (genericPoint X) := by
  rw [Scheme.Hom.toImage_imageι_assoc, genericSection_fst]

variable (B : Type u) [Field B] [Algebra X.functionField B] [Algebra k B]
  [IsScalarTower k X.functionField B]

/-- `L(s) → B(s)` for a field extension `B ⊇ L`. -/
noncomputable def ratFuncMap : RatFunc X.functionField →+* RatFunc B :=
  IsFractionRing.lift (A := Polynomial X.functionField)
    (g := (algebraMap (Polynomial B) (RatFunc B)).comp
      (Polynomial.mapRingHom (algebraMap X.functionField B)))
    ((RatFunc.algebraMap_injective B).comp
      (Polynomial.map_injective _ (algebraMap X.functionField B).injective))

lemma ratFuncMap_C (l : X.functionField) :
    ratFuncMap B (RatFunc.C l) = RatFunc.C (algebraMap X.functionField B l) := by
  rw [← RatFunc.algebraMap_C, ratFuncMap, IsFractionRing.lift_algebraMap]
  simp

lemma ratFuncMap_X : ratFuncMap B (RatFunc.X : RatFunc X.functionField) = RatFunc.X := by
  rw [← RatFunc.algebraMap_X, ratFuncMap, IsFractionRing.lift_algebraMap]
  simp

include hxy in
lemma algebraicIndependent_algebraMap :
    AlgebraicIndependent k ![algebraMap X.functionField B x, algebraMap X.functionField B y] := by
  have h := hxy.map' (f := IsScalarTower.toAlgHom k X.functionField B)
    (algebraMap X.functionField B).injective
  convert h using 1
  ext i
  fin_cases i <;> rfl

lemma ratFuncMap_comp_pencilEmbedding :
    (ratFuncMap B).comp (Bertini.pencilEmbedding hxy).toRingHom =
      (Bertini.pencilEmbedding (algebraicIndependent_algebraMap hxy B)).toRingHom := by
  refine IsFractionRing.ringHom_ext (A := MvPolynomial (Fin 2) k) fun p ↦ ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Bertini.pencilEmbedding_algebraMap]
  have : (ratFuncMap B).comp (Bertini.pencilPoly k x y).toRingHom =
      (Bertini.pencilPoly k (algebraMap X.functionField B x)
        (algebraMap X.functionField B y)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.algHom_C]
      rw [IsScalarTower.algebraMap_apply k X.functionField (RatFunc X.functionField),
        RatFunc.algebraMap_eq_C, ratFuncMap_C, IsScalarTower.algebraMap_apply k B (RatFunc B),
        RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply]
    · fin_cases i
      · simp [Bertini.pencilPoly, ratFuncMap_X]
      · simp [Bertini.pencilPoly, Bertini.pencil, ratFuncMap_X, ratFuncMap_C]
  exact congrArg (fun φ : MvPolynomial (Fin 2) k →+* RatFunc B ↦ φ p) this

variable (ξ : Spec (.of B) ⟶ E)
  (hξ : ξ ≫ q = Spec.map (CommRingCat.ofHom (algebraMap X.functionField B)) ≫
    X.fromSpecStalk (genericPoint X))

/-- The generic point of `W₃`: `Spec B(s) ⟶ W ×_X E`. -/
noncomputable def genericPoint₃ : Spec (.of (RatFunc B)) ⟶ W₃ s hk hxy q :=
  pullback.lift (Spec.map (CommRingCat.ofHom (RatFunc.C : B →+* RatFunc B)) ≫ ξ)
    (Spec.map (CommRingCat.ofHom (ratFuncMap B)) ≫ (genericSection s hk hxy).toImage) (by
      rw [Category.assoc, hξ, Category.assoc, toImage_toX, ← Category.assoc, ← Category.assoc,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext l
      exact (ratFuncMap_C B l).symm)

omit [Algebra k B] [IsScalarTower k X.functionField B] in
lemma genericPoint₃_snd :
    genericPoint₃ s hk hxy q B ξ hξ ≫ pullback.snd q (toX s hk hxy) =
      Spec.map (CommRingCat.ofHom (ratFuncMap B)) ≫ (genericSection s hk hxy).toImage :=
  pullback.lift_snd _ _ _

lemma genericPoint₃_toBase :
    genericPoint₃ s hk hxy q B ξ hξ ≫ pullback.snd q (toX s hk hxy) ≫ toBase s hk hxy =
      Spec.map (CommRingCat.ofHom
        (Bertini.pencilEmbedding (algebraicIndependent_algebraMap hxy B)).toRingHom) := by
  rw [reassoc_of% genericPoint₃_snd, toBase, Scheme.Hom.toImage_imageι_assoc, genericSection_snd,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ratFuncMap_comp_pencilEmbedding]

omit [Algebra k B] [IsScalarTower k X.functionField B] in
/-- **Uniqueness of the generic point of `W₃`**: if `E ×_X Spec L(s)` is a single point, the
generic point of `W₃` is the only point of `W₃` over the generic point of `W`. -/
lemma eq_genericPoint₃ (hsub : Subsingleton ↥(pullback q
      (Spec.map (CommRingCat.ofHom (RatFunc.C : X.functionField →+* RatFunc X.functionField)) ≫
        X.fromSpecStalk (genericPoint X))))
    (p : W₃ s hk hxy q) (hp : pullback.snd q (toX s hk hxy) p =
      (genericSection s hk hxy).toImage (IsLocalRing.closedPoint _)) :
    p = genericPoint₃ s hk hxy q B ξ hξ (IsLocalRing.closedPoint _) := by
  let τ := (genericSection s hk hxy).toImage
  have : Subsingleton ↥(pullback (pullback.snd q (toX s hk hxy)) τ) :=
    subsingleton_of_iso (pullbackLeftPullbackSndIso q (toX s hk hxy) τ ≪≫
      pullback.congrHom rfl (toImage_toX s hk hxy))
  obtain ⟨r, hr, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd q _) (g := τ)
    p (IsLocalRing.closedPoint _) hp
  have hp₀ : pullback.snd q (toX s hk hxy)
      (genericPoint₃ s hk hxy q B ξ hξ (IsLocalRing.closedPoint _)) =
        τ (IsLocalRing.closedPoint _) := by
    have e := congrArg (fun f ↦ f (IsLocalRing.closedPoint (RatFunc B)))
      (genericPoint₃_snd s hk hxy q B ξ hξ)
    refine e.trans ?_
    exact congrArg τ (Subsingleton.elim _ _)
  obtain ⟨r₀, hr₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd q _)
    (g := τ) _ (IsLocalRing.closedPoint _) hp₀
  rw [← hr, ← hr₀, Subsingleton.elim r r₀]

omit [Algebra k B] [IsScalarTower k X.functionField B] in
/-- **The generic point of `W₃` is dense** (when `E ×_X Spec L(s)` is a single point): every point
of `W₃` generalizes to a point over the generic point of `W` (`W₃ ⟶ W` is open with finite
fibres), which is the generic point of `W₃` by `eq_genericPoint₃`. -/
lemma isDominant_genericPoint₃ [IsFinite q] [Etale q] (hsub : Subsingleton ↥(pullback q
      (Spec.map (CommRingCat.ofHom (RatFunc.C : X.functionField →+* RatFunc X.functionField)) ≫
        X.fromSpecStalk (genericPoint X)))) :
    IsDominant (genericPoint₃ s hk hxy q B ξ hξ) := by
  refine ⟨?_⟩
  intro p
  let f := pullback.snd q (toX s hk hxy)
  have hw₀ : (genericSection s hk hxy).toImage (IsLocalRing.closedPoint _) ⤳ f p := by
    rw [← genericPoint_W]
    exact (genericPoint_spec (W s hk hxy)).specializes (Set.mem_univ _)
  obtain ⟨p', hp', hsp⟩ := IsOpenMap.exists_specializes_of_finite_preimage f.isOpenMap
    (f.finite_preimage_singleton _) hw₀
  rw [eq_genericPoint₃ s hk hxy q B ξ hξ hsub p' hp'] at hsp
  have hmem : genericPoint₃ s hk hxy q B ξ hξ (IsLocalRing.closedPoint _) ∈
      Set.range (genericPoint₃ s hk hxy q B ξ hξ) := Set.mem_range_self _
  exact closure_mono (Set.singleton_subset_iff.mpr hmem) (specializes_iff_mem_closure.mp hsp)

include B ξ hξ in
/-- **The pullback of the generic hyperplane section to a cover is geometrically connected**,
given a point `ξ : Spec B ⟶ E` over the generic point of `X` with `E ×_X Spec L(s)` a single
point. -/
theorem geometricallyConnected_W₃ [IsFinite q] [Etale q] [IsAlgClosed k] [IsProper s]
    (hsub : Subsingleton ↥(pullback q
      (Spec.map (CommRingCat.ofHom (RatFunc.C : X.functionField →+* RatFunc X.functionField)) ≫
        X.fromSpecStalk (genericPoint X)))) :
    GeometricallyConnected (pullback.snd q (toX s hk hxy) ≫ toBase s hk hxy) := by
  have hxy' := algebraicIndependent_algebraMap hxy B
  let _ : Algebra (K₀ k) (RatFunc B) := (Bertini.pencilEmbedding hxy').toRingHom.toAlgebra
  have : IsLocallyNoetherian (W s hk hxy) :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase s hk hxy)
  have : AlgebraicGeometry.IsReduced (W₃ s hk hxy q) :=
    ExposeI.isReduced_of_etale (pullback.snd q (toX s hk hxy))
  have := isDominant_genericPoint₃ s hk hxy q B ξ hξ hsub
  exact geometricallyConnected_of_isDominant _ (genericPoint₃ s hk hxy q B ξ hξ)
    (genericPoint₃_toBase s hk hxy q B ξ hξ)
    fun θ hθ ↦ Bertini.mem_range_pencilEmbedding hxy' hθ.isIntegral.isAlgebraic

/-- The spectrum of a field has a single point. -/
lemma subsingleton_spec_of_isField {R : CommRingCat.{u}} (hR : IsField R) :
    Subsingleton (Spec R) := by
  let _ : Field R := hR.toField
  refine ⟨fun a b ↦ PrimeSpectrum.ext ?_⟩
  have := a.isPrime
  have := b.isPrime
  exact (Ideal.eq_bot_of_prime a.asIdeal).trans (Ideal.eq_bot_of_prime b.asIdeal).symm

/-- **The pullback of the generic hyperplane section to a connected finite étale cover is
geometrically connected** (`X` normal): the hypotheses of `geometricallyConnected_W₃` hold with
`B = Γ(E ×_X Spec K(X))`, a field (`isField_genericFibre`). -/
theorem geometricallyConnected_W₃_of_isNormalScheme [IsFinite q] [Etale q] [IsAlgClosed k]
    [IsProper s]
    [IsLocallyNoetherian X] [ConnectedSpace E] (hX : ExposeI.IsNormalScheme X) :
    GeometricallyConnected (pullback.snd q (toX s hk hxy) ≫ toBase s hk hxy) := by
  let ηX := X.fromSpecStalk (genericPoint X)
  let G := genericFibre q
  let F := Γ(G, ⊤)
  let _ : Field F := (isField_genericFibre q hX).toField
  let φ := (pullback.snd q ηX).specStructureRingHom
  let _ : Algebra X.functionField F := φ.toAlgebra
  let _ : Algebra k F := (φ.comp (algebraMap k X.functionField)).toAlgebra
  have : IsScalarTower k X.functionField F := .of_algebraMap_eq fun _ ↦ rfl
  have hfin : Module.Finite X.functionField F := finite_genericFibre q
  let ξ : Spec (.of F) ⟶ E := G.isoSpec.inv ≫ pullback.fst q ηX
  have hξ : ξ ≫ q = Spec.map (CommRingCat.ofHom (algebraMap X.functionField F)) ≫ ηX := by
    simp only [ξ, Category.assoc]
    rw [pullback.condition, ← Category.assoc, isoSpec_inv_comp_eq]
  have hsnd : pullback.snd q ηX = G.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField F)) := by
    rw [← Iso.inv_comp_eq, isoSpec_inv_comp_eq]
  have hsub : Subsingleton ↥(pullback q
      (Spec.map (CommRingCat.ofHom (RatFunc.C : X.functionField →+* RatFunc X.functionField)) ≫
        ηX)) := by
    have hfield : IsField (CommRingCat.of (F ⊗[X.functionField] RatFunc X.functionField)) :=
      (Algebra.TensorProduct.comm X.functionField F (RatFunc X.functionField)).toMulEquiv.isField
        (Bertini.isField_ratFunc_tensor X.functionField F)
    have := subsingleton_spec_of_isField hfield
    let e₁ := (pullbackLeftPullbackSndIso q ηX
      (Spec.map (CommRingCat.ofHom (RatFunc.C : X.functionField →+* RatFunc X.functionField)))).symm
    let e₂ := pullback.congrHom hsnd (rfl : Spec.map (CommRingCat.ofHom
      (RatFunc.C : X.functionField →+* RatFunc X.functionField)) = _)
    let e₃ := asIso (pullback.map (G.isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap X.functionField F)))
      (Spec.map (CommRingCat.ofHom (RatFunc.C : X.functionField →+* RatFunc X.functionField)))
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField F)))
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (RatFunc X.functionField))))
      G.isoSpec.hom (𝟙 _) (𝟙 _) (by simp) (by simp [RatFunc.algebraMap_eq_C]))
    exact subsingleton_of_iso (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫
      pullbackSpecIso X.functionField F (RatFunc X.functionField))
  exact geometricallyConnected_W₃ s hk hxy q F ξ hξ hsub

end Cover

section Surjective

/-- A scheme isomorphic to a connected scheme is connected. -/
lemma connectedSpace_of_iso {A B : Scheme.{u}} (e : A ≅ B) [ConnectedSpace B] : ConnectedSpace A :=
  e.inv.surjective.connectedSpace e.inv.continuous

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
  (s : X ⟶ Spec (.of k)) [IsProper s] [Algebra k X.functionField]
  (hk : algebraMap k X.functionField = ExposeXI.functionFieldMap s)
  {x y : X.functionField} (hxy : AlgebraicIndependent k ![x, y])

omit [IsAlgClosed k] [IsProper s] in
lemma toXK_fst :
    toXK s hk hxy ≫ pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k (K k)))) =
      pullback.fst (toBase s hk hxy) closureMap ≫ toX s hk hxy := by
  rw [toXK, pullback.lift_fst]

/-- **X.2.10, surjectivity on fundamental groups** (SGA 1 X.2.10 in existence form, `X` normal):
`π₁(Y) → π₁(X_K)` is surjective, at every geometric point of `Y`. A connected étale covering of
`X_K` comes from a connected étale covering `E` of `X` (X.1.8), and its pullback to `Y` is
`(W ×_X E) ⊗_{K₀} K`, connected by `geometricallyConnected_W₃_of_isNormalScheme`. -/
theorem surjective_map_toXK (hX : ExposeI.IsNormalScheme X) (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y s hk hxy) :
    Function.Surjective (ExposeV.etaleFundamentalGroup.map Ω (toXK s hk hxy) t) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let ρK := Spec.map (CommRingCat.ofHom (algebraMap k (K k)))
  let πK := pullback.fst s ρK
  have : (ExposeV.FEt.pullback πK).IsEquivalence := baseChangeAlgClosedStatement k (K k) s
  have : ConnectedSpace (Y s hk hxy) := connectedSpace_Y s hk hxy
  have : Surjective ρK := ⟨fun _ ↦ ⟨IsLocalRing.closedPoint (K k), Subsingleton.elim _ _⟩⟩
  have : ConnectedSpace ↥(pullback s ρK) := connectedSpace_pullback_of_isAlgClosed s (K k)
  refine ExposeV.autMap_surjective _ _ fun E hE ↦ ?_
  let E'' := (ExposeV.FEt.pullback πK).objPreimage E
  let e : (ExposeV.FEt.pullback πK).obj E'' ≅ E := (ExposeV.FEt.pullback πK).objObjPreimageIso E
  have : IsFinite E''.hom := E''.prop.1
  have : Etale E''.hom := E''.prop.2
  -- `E''` is connected
  have : PreGaloisCategory.IsConnected ((ExposeV.FEt.pullback πK).obj E'') :=
    ExposeV.isConnected_of_iso e.symm
  have : ConnectedSpace ↥(pullback E''.hom πK) :=
    ExposeV.FEt.connectedSpace_of_isConnected ((ExposeV.FEt.pullback πK).obj E'')
  have : ConnectedSpace E''.left :=
    (pullback.fst E''.hom πK).surjective.connectedSpace (pullback.fst E''.hom πK).continuous
  have : ConnectedSpace ↥((𝟭 Scheme).obj E''.left) := ‹ConnectedSpace E''.left›
  -- reduce to `(W ×_X E'') ⊗_{K₀} K`
  suffices PreGaloisCategory.IsConnected
      ((ExposeV.FEt.pullback (toXK s hk hxy)).obj ((ExposeV.FEt.pullback πK).obj E'')) from
    ExposeV.isConnected_of_iso ((ExposeV.FEt.pullback (toXK s hk hxy)).mapIso e)
  suffices PreGaloisCategory.IsConnected ((ExposeV.FEt.pullback
      (pullback.fst (toBase s hk hxy) closureMap ≫ toX s hk hxy)).obj E'') from
    ExposeV.isConnected_of_iso ((MorphismProperty.Over.pullbackComp (toXK s hk hxy) πK
      (pullback.fst (toBase s hk hxy) closureMap ≫ toX s hk hxy)
      (toXK_fst s hk hxy).symm).app E'')
  rw [ExposeV.FEt.isConnected_iff_connectedSpace]
  have hgc := geometricallyConnected_W₃_of_isNormalScheme s hk hxy E''.hom hX
  have hsq := (IsPullback.of_hasPullback (pullback.snd E''.hom (toX s hk hxy))
    (pullback.fst (toBase s hk hxy) closureMap)).paste_vert
      (IsPullback.of_hasPullback (toBase s hk hxy) closureMap)
  have := hgc.geometrically_connectedSpace closureMap _ _ hsq
  exact connectedSpace_of_iso (pullbackLeftPullbackSndIso E''.hom (toX s hk hxy)
    (pullback.fst (toBase s hk hxy) closureMap)).symm

end Surjective

end SGA.SGA1.ExposeX.Hyperplane
