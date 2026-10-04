/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Projective.BertiniConnected
import SGA.Foundations.Projective.BertiniFieldLemma
import SGA.Foundations.Projective.BertiniDimension
import SGA.SGA1.ExposeXI.RationalVarieties
import SGA.Foundations.Projective.PlaneModelCurve
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.FieldTheory.FinTrdeg

/-!
# SGA 1, Exposé X, 2.10: the generic hyperplane section

Let `k` be algebraically closed, `X` an integral proper `k`-scheme with function field `L`, and
`x, y ∈ L` algebraically independent over `k`. Over `K₀ = k(S, Z)` (`Hyperplane.K₀`), the
generic member `x + S y = Z` of the pencil of hyperplane sections cuts `X_{K₀}` in a closed
subscheme `W` (`Hyperplane.W`): the scheme-theoretic image of the morphism
`Spec L(s) ⟶ X_{K₀}` (`Hyperplane.genericSection`) given by the generic point of `X` and
`S ↦ s`, `Z ↦ x + s y`. By the Bertini field lemma (`Bertini.mem_range_pencilEmbedding`), `K₀` is
algebraically closed in `L(s)`, so `W` is geometrically connected over `K₀`
(`Hyperplane.geometricallyConnected_toBase`).
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]

/-- `f.toImage` is injective on sections over every open of the scheme-theoretic image (mathlib's
`Scheme.Hom.toImage_app_injective` covers the inverse images of affine opens). -/
lemma toImage_app_injective' (V : f.image.Opens) : Function.Injective (f.toImage.app V) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  refine f.image.IsSheaf.section_ext fun w hw ↦ ?_
  obtain ⟨V', hV', hVV'⟩ := f.imageι.isEmbedding.isInducing.isOpen_iff.mp V.isOpen
  have hw' : f.imageι w ∈ V' := by
    have : w ∈ f.imageι ⁻¹' V' := by rw [hVV']; exact hw
    exact this
  obtain ⟨_, ⟨U, hU, rfl⟩, hwU, hUV'⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hw' hV'
  have hle : f.imageι ⁻¹ᵁ U ≤ V := fun z hz ↦ by
    have : z ∈ f.imageι ⁻¹' V' := hUV' hz
    rwa [hVV'] at this
  refine ⟨f.imageι ⁻¹ᵁ U, hle, hwU, f.toImage_app_injective ⟨U, hU⟩ ?_⟩
  rw [← ConcreteCategory.comp_apply, f.toImage.naturality, ConcreteCategory.comp_apply, ht]
  simp

/-- The scheme-theoretic image of a quasi-compact morphism from a reduced scheme is reduced. -/
lemma isReduced_image [IsReduced X] : IsReduced f.image :=
  ⟨fun V ↦ isReduced_of_injective _ (f.toImage_app_injective' V)⟩

end AlgebraicGeometry.Scheme.Hom

namespace SGA.SGA1.ExposeX.Hyperplane

variable (k : Type u) [Field k]

/-- The field `K₀ = k(S, Z)` of coefficients of the generic member of the pencil. -/
abbrev K₀ : Type u := FractionRing (MvPolynomial (Fin 2) k)

/-- `Spec K₀ ⟶ Spec k`. -/
noncomputable abbrev baseMap : Spec (.of (K₀ k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (K₀ k)))

variable {k} {X : Scheme.{u}} [IsIntegral X] (s : X ⟶ Spec (.of k))
  [Algebra k X.functionField] (hk : algebraMap k X.functionField = ExposeXI.functionFieldMap s)
  {x y : X.functionField} (hxy : AlgebraicIndependent k ![x, y])

/-- **The generic point of the generic hyperplane section**: `Spec L(s) ⟶ X_{K₀}`, the generic
point `Spec L ⟶ X` of `X` together with `K₀ → L(s)`, `S ↦ s`, `Z ↦ x + s y`. -/
noncomputable def genericSection :
    Spec (.of (RatFunc X.functionField)) ⟶ pullback s (baseMap k) :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (RatFunc.C : X.functionField →+* RatFunc X.functionField)) ≫
      X.fromSpecStalk (genericPoint X))
    (Spec.map (CommRingCat.ofHom (Bertini.pencilEmbedding hxy).toRingHom)) (by
      rw [Category.assoc, ExposeXI.fromSpecStalk_comp_eq_SpecMap, ← Spec.map_comp,
        ← Spec.map_comp, ← hk]
      congr 1
      ext a
      change RatFunc.C (algebraMap k X.functionField a) =
        Bertini.pencilEmbedding hxy (algebraMap k (K₀ k) a)
      rw [AlgHom.commutes, ← RatFunc.algebraMap_eq_C,
        ← IsScalarTower.algebraMap_apply k X.functionField (RatFunc X.functionField)])

@[reassoc (attr := simp)]
lemma genericSection_snd :
    genericSection s hk hxy ≫ pullback.snd s (baseMap k) =
      Spec.map (CommRingCat.ofHom (Bertini.pencilEmbedding hxy).toRingHom) :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma genericSection_fst :
    genericSection s hk hxy ≫ pullback.fst s (baseMap k) =
      Spec.map (CommRingCat.ofHom (RatFunc.C : X.functionField →+* RatFunc X.functionField)) ≫
        X.fromSpecStalk (genericPoint X) :=
  pullback.lift_fst _ _ _

/-- **The generic hyperplane section** `W ⊆ X_{K₀}`: the scheme-theoretic image of
`genericSection`, i.e. the closure of its point with the reduced structure. -/
noncomputable abbrev W : Scheme.{u} := (genericSection s hk hxy).image

/-- `W ⟶ Spec K₀`. -/
noncomputable abbrev toBase : W s hk hxy ⟶ Spec (.of (K₀ k)) :=
  (genericSection s hk hxy).imageι ≫ pullback.snd s (baseMap k)

instance : IsReduced (W s hk hxy) := Scheme.Hom.isReduced_image _

instance [IsProper s] : IsProper (toBase s hk hxy) := by
  dsimp only [toBase]
  infer_instance

/-- The ring map `Γ(W, 𝒪_W) → L(s)` given by the generic point of `W`. -/
noncomputable def sectionsMap :
    Γ(W s hk hxy, ⊤) →+* RatFunc X.functionField :=
  ((genericSection s hk hxy).toImage.appTop ≫
    (Scheme.ΓSpecIso (.of (RatFunc X.functionField))).hom).hom

lemma injective_sectionsMap : Function.Injective (sectionsMap s hk hxy) :=
  (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (RatFunc X.functionField))).hom).1.comp
    ((genericSection s hk hxy).toImage_app_injective' ⊤)

lemma sectionsMap_specStructureRingHom (a : K₀ k) :
    sectionsMap s hk hxy ((toBase s hk hxy).specStructureRingHom a) =
      Bertini.pencilEmbedding hxy a := by
  have h := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (Bertini.pencilEmbedding hxy).toRingHom)
  have e : (Scheme.ΓSpecIso (.of (K₀ k))).inv ≫ (toBase s hk hxy).appTop ≫
      (genericSection s hk hxy).toImage.appTop ≫
        (Scheme.ΓSpecIso (.of (RatFunc X.functionField))).hom =
      CommRingCat.ofHom (Bertini.pencilEmbedding hxy).toRingHom := by
    rw [← Scheme.Hom.comp_appTop_assoc, toBase, Scheme.Hom.toImage_imageι_assoc,
      genericSection_snd, h, Iso.inv_hom_id_assoc]
  exact congrArg (fun φ : CommRingCat.of (K₀ k) ⟶ CommRingCat.of (RatFunc X.functionField) ↦
    φ.hom a) e

/-- **The generic hyperplane section is geometrically connected** (SGA 1 X.2.10, Bertini): for
`k` algebraically closed, `W` is geometrically connected over `K₀ = k(S, Z)`. -/
theorem geometricallyConnected_toBase [IsAlgClosed k] [IsProper s] :
    GeometricallyConnected (toBase s hk hxy) := by
  let _ : Algebra (K₀ k) (RatFunc X.functionField) :=
    (Bertini.pencilEmbedding hxy).toRingHom.toAlgebra
  have : Nonempty (W s hk hxy) :=
    ⟨(genericSection s hk hxy).toImage (IsLocalRing.closedPoint _)⟩
  refine geometricallyConnected_of_injective _ (sectionsMap s hk hxy)
    (injective_sectionsMap s hk hxy) (sectionsMap_specStructureRingHom s hk hxy) fun θ hθ ↦ ?_
  exact Bertini.mem_range_pencilEmbedding hxy hθ.isIntegral.isAlgebraic

/-! ### The generic point of `W` and its dimension -/

/-- The point `τ(pt)` of `W` given by `genericSection` is dense. -/
lemma closure_toImage_closedPoint :
    closure {(genericSection s hk hxy).toImage (IsLocalRing.closedPoint (RatFunc X.functionField))}
      = Set.univ := by
  have h := (genericSection s hk hxy).toImage.denseRange.closure_eq
  have hr : Set.range (genericSection s hk hxy).toImage =
      {(genericSection s hk hxy).toImage (IsLocalRing.closedPoint (RatFunc X.functionField))} := by
    ext w
    refine ⟨?_, fun hw ↦ ⟨_, hw.symm⟩⟩
    rintro ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint (RatFunc X.functionField))]
    rfl
  rwa [hr] at h

instance : IrreducibleSpace (W s hk hxy) := by
  rw [irreducibleSpace_def, Set.top_eq_univ, ← closure_toImage_closedPoint s hk hxy]
  exact isIrreducible_singleton.closure

instance : IsIntegral (W s hk hxy) := isIntegral_of_irreducibleSpace_of_isReduced _

lemma genericPoint_W :
    genericPoint (W s hk hxy) =
      (genericSection s hk hxy).toImage (IsLocalRing.closedPoint (RatFunc X.functionField)) :=
  (genericPoint_spec (W s hk hxy)).eq (by
    rw [IsGenericPoint, closure_toImage_closedPoint s hk hxy])

/-- `K(W) → L(s)`, given by the generic point of `W`. -/
noncomputable def functionFieldHom :
    (W s hk hxy).functionField ⟶ .of (RatFunc X.functionField) :=
  ((W s hk hxy).presheaf.stalkCongr (Inseparable.of_eq (genericPoint_W s hk hxy))).hom ≫
    Scheme.stalkClosedPointTo (genericSection s hk hxy).toImage

lemma SpecMap_functionFieldHom :
    Spec.map (functionFieldHom s hk hxy) ≫ (W s hk hxy).fromSpecStalk _ =
      (genericSection s hk hxy).toImage :=
  Scheme.SpecMap_stalkSpecializes_stalkClosedPointTo _
    (Inseparable.of_eq (genericPoint_W s hk hxy)).ge

/-- `functionFieldHom` is `K₀`-linear. -/
lemma functionFieldHom_comp :
    ((Scheme.ΓSpecIso (.of (K₀ k))).inv ≫ (toBase s hk hxy).appTop ≫
      (W s hk hxy).presheaf.germ ⊤ (genericPoint _) trivial) ≫ functionFieldHom s hk hxy =
      CommRingCat.ofHom (Bertini.pencilEmbedding hxy).toRingHom := by
  apply Spec.map_injective
  have h : (W s hk hxy).fromSpecStalk (genericPoint _) ≫ toBase s hk hxy =
      Spec.map ((Scheme.ΓSpecIso (.of (K₀ k))).inv ≫ (toBase s hk hxy).appTop ≫
        (W s hk hxy).presheaf.germ ⊤ (genericPoint _) trivial) := by
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ_assoc, Category.assoc,
      Category.assoc, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  rw [Spec.map_comp, ← h, ← Category.assoc, SpecMap_functionFieldHom, toBase,
    Scheme.Hom.toImage_imageι_assoc, genericSection_snd]

instance [IsProper s] : LocallyOfFiniteType (toBase s hk hxy) := by
  dsimp only [toBase]
  infer_instance

/-- `dim W ≤ trdeg_{K₀} L(s)`. -/
lemma topologicalKrullDim_W_le [IsProper s] :
    letI := (Bertini.pencilEmbedding hxy).toRingHom.toAlgebra
    topologicalKrullDim (W s hk hxy) ≤
      (Algebra.trdeg (K₀ k) (RatFunc X.functionField)).toENat := by
  let α : K₀ k →+* (W s hk hxy).functionField := ((Scheme.ΓSpecIso (.of (K₀ k))).inv ≫
    (toBase s hk hxy).appTop ≫ (W s hk hxy).presheaf.germ ⊤ (genericPoint _) trivial).hom
  let _ : Algebra (K₀ k) (W s hk hxy).functionField := α.toAlgebra
  let _ : Algebra (K₀ k) (RatFunc X.functionField) :=
    (Bertini.pencilEmbedding hxy).toRingHom.toAlgebra
  rw [topologicalKrullDim_eq_trdeg_functionField (toBase s hk hxy) rfl]
  let e : (W s hk hxy).functionField →ₐ[K₀ k] RatFunc X.functionField :=
    { (functionFieldHom s hk hxy).hom with
      commutes' := fun r ↦ by
        have e := congrArg (fun g ↦ g.hom r) (functionFieldHom_comp s hk hxy)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
        exact e }
  exact WithBot.coe_le_coe.mpr (Cardinal.toENat.monotone' (trdeg_le_of_injective e e.injective))

/-! ### The base change `Y = W ⊗_{K₀} K` to an algebraic closure -/

variable (k) in
/-- An algebraic closure `K` of `K₀ = k(S, Z)`. -/
abbrev K : Type u := AlgebraicClosure (K₀ k)

/-- `Spec K ⟶ Spec K₀`. -/
noncomputable abbrev closureMap : Spec (.of (K k)) ⟶ Spec (.of (K₀ k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (K₀ k) (K k)))

instance : IsIntegralHom (closureMap (k := k)) := by
  rw [IsIntegralHom.SpecMap_iff]
  exact Algebra.IsIntegral.isIntegral (R := K₀ k) (A := K k)

/-- **The generic hyperplane section over `K`**: `Y = W ×_{K₀} K`. -/
noncomputable abbrev Y : Scheme.{u} := pullback (toBase s hk hxy) closureMap

/-- `Y ⟶ X_K`, `X_K = X ×_k K`. -/
noncomputable def toXK :
    Y s hk hxy ⟶ pullback s (Spec.map (CommRingCat.ofHom (algebraMap k (K k)))) :=
  pullback.lift (pullback.fst _ _ ≫ (genericSection s hk hxy).imageι ≫ pullback.fst s (baseMap k))
    (pullback.snd _ _) (by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc,
        ← Category.assoc, Category.assoc (pullback.fst _ _),
        pullback.condition (f := toBase s hk hxy), Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

instance [IsProper s] : IsProper (pullback.snd (toBase s hk hxy) (closureMap (k := k))) := by
  infer_instance

/-- `Y` is connected (`W` is geometrically connected over `K₀`). -/
theorem connectedSpace_Y [IsAlgClosed k] [IsProper s] : ConnectedSpace (Y s hk hxy) :=
  (geometricallyConnected_toBase s hk hxy).geometrically_connectedSpace closureMap _ _
    (IsPullback.of_hasPullback _ _)

/-- **`dim Y < dim X`**: `dim Y ≤ dim W` (`Y ⟶ W` is integral), `dim W ≤ trdeg_{K₀} L(s)`, and
`trdeg_{K₀} L(s) + 1 = trdeg_k L = dim X`. -/
theorem topologicalKrullDim_Y_lt [IsAlgClosed k] [IsProper s] :
    topologicalKrullDim (Y s hk hxy) < topologicalKrullDim X := by
  let _ : Algebra (K₀ k) (RatFunc X.functionField) :=
    (Bertini.pencilEmbedding hxy).toRingHom.toAlgebra
  have h1 : topologicalKrullDim (Y s hk hxy) ≤ topologicalKrullDim (W s hk hxy) :=
    (pullback.fst (toBase s hk hxy) closureMap).topologicalKrullDim_le_of_isIntegralHom
  have h2 := topologicalKrullDim_W_le s hk hxy
  have h3 := Bertini.trdeg_pencilEmbedding_add_one hxy
  have h4 := topologicalKrullDim_eq_trdeg_functionField s hk
  have : Algebra.EssFiniteType k X.functionField := by
    have := ExposeXI.essFiniteType_functionFieldMap s
    rw [← hk] at this
    exact RingHom.essFiniteType_algebraMap.mp this
  have h5 : Algebra.trdeg k X.functionField < Cardinal.aleph0 := trdeg_lt_aleph0 _ _
  refine h1.trans_lt (h2.trans_lt ?_)
  rw [h4]
  refine WithBot.coe_lt_coe.mpr ?_
  have h6 : Algebra.trdeg (K₀ k) (RatFunc X.functionField) < Cardinal.aleph0 := by
    rw [← h3] at h5
    exact le_self_add.trans_lt h5
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp h6
  rw [← h3, hn]
  simp only [map_add, Cardinal.toENat_nat, map_one]
  exact_mod_cast Nat.lt_succ_self n

end SGA.SGA1.ExposeX.Hyperplane
