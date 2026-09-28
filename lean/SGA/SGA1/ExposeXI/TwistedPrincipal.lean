/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.FundamentalGroupCohomology
import SGA.SGA1.ExposeXI.NonabelianCohomology

/-!
# SGA 1, Exposé XI.5 `(*)` for a non-constant group, in a Galois category

Let `C` be a Galois category with fibre functor `F` and fundamental group `π = Aut F`. By the
main theorem of Exposé V, a finite étale group scheme over a connected scheme `S` is the same as a
finite group `G` with a continuous action of `π = π₁(S, s̄)` by automorphisms (its geometric fibre),
and a principal homogeneous bundle under it is an étale covering `X` whose fibre `F(X)` is a
principal homogeneous `G`-set compatibly with `π`. XI.5 `(*)` identifies their classes with the
continuous non-abelian cohomology set `H¹(π, G)`.

We formalize this in any Galois category, describing the group by the `π`-group `G`:

* `TwistedPrincipalObject F G`: an object `X` with a right action of `G` on `F(X)` making it a
  principal homogeneous `G`-set compatible with `π` (`IsPrincipalHomogeneous`);
* `TwistedPrincipalObject.classOf`: its class in `H¹(π, G)`, represented by a continuous cocycle
  (`TwistedPrincipalObject.continuous_cocycleAt`);
* `twistedPrincipalH1Equiv`: XI.5 `(*)`, the bijection between isomorphism classes of such objects
  and the classes of continuous cocycles. Injectivity lifts isomorphisms of fibres to `C` (V.4,
  `functorToAction` is fully faithful); surjectivity realizes the twisted `π`-set `Twist φ` of a
  continuous cocycle `φ` as the fibre of an object of `C` (essential surjectivity).

For a constant group this is `principalH1Equiv` (`FundamentalGroupCohomology`). For a finite
étale group scheme `G` over `S`, with `π₁`-group `G(s̄)`, the comparison with `H¹(S, G)` is
`h1EquivContH1` (`FiniteEtaleGroups`).
-/

universe u₁ u₂ w

open CategoryTheory Limits PreGaloisCategory MulOpposite

namespace SGA.SGA1.ExposeXI

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w}) (G : Type w) [Group G]
  [MulDistribMulAction (Aut F) G]

/-- XI.5 `(*)`: a principal object under the `π`-group `G`: an object `X` with a right action of
`G` on the fibre `F(X)` which makes it a principal homogeneous `G`-set compatible with the action
of `π = Aut F`, i.e. `σ (x g) = (σ x) (σ g)`. -/
structure TwistedPrincipalObject where
  /-- The underlying object. -/
  X : C
  /-- The right action of `G` on the fibre. -/
  act : MulAction Gᵐᵒᵖ (F.obj X)
  isPrincipalHomogeneous : letI := act; IsPrincipalHomogeneous (Aut F) G (F.obj X)

variable {F G}

namespace TwistedPrincipalObject

/-- The right action of `g : G` on the fibre. -/
abbrev smul (P : TwistedPrincipalObject F G) (g : G) (x : F.obj P.X) : F.obj P.X :=
  letI := P.act
  op g • x

/-- Two principal objects are isomorphic if there is an isomorphism compatible with the actions
of `G` on the fibres. -/
def IsIso (P Q : TwistedPrincipalObject F G) : Prop :=
  ∃ φ : P.X ≅ Q.X, ∀ (g : G) (x : F.obj P.X), F.map φ.hom (P.smul g x) = Q.smul g (F.map φ.hom x)

lemma isIso_equivalence : Equivalence (@IsIso C _ F G _ _) where
  refl P := ⟨Iso.refl _, fun g x ↦ by simp⟩
  symm := by
    rintro P Q ⟨φ, hφ⟩
    refine ⟨φ.symm, fun g y ↦ ?_⟩
    obtain ⟨x, rfl⟩ : ∃ x, F.map φ.hom x = y :=
      ⟨F.map φ.inv y, by rw [← FintypeCat.comp_apply, ← F.map_comp, φ.inv_hom_id, F.map_id,
        FintypeCat.id_apply]⟩
    have hinv (z : F.obj P.X) : F.map φ.inv (F.map φ.hom z) = z := by
      rw [← FintypeCat.comp_apply, ← F.map_comp, φ.hom_inv_id, F.map_id, FintypeCat.id_apply]
    change F.map φ.inv (Q.smul g (F.map φ.hom x)) = P.smul g (F.map φ.inv (F.map φ.hom x))
    rw [← hφ, hinv, hinv]
  trans := by
    rintro P Q R ⟨φ, hφ⟩ ⟨ψ, hψ⟩
    refine ⟨φ ≪≫ ψ, fun g x ↦ ?_⟩
    simp only [Iso.trans_hom, F.map_comp, FintypeCat.comp_apply, hφ, hψ]

variable (P : TwistedPrincipalObject F G)

/-- XI.5 `(*)`: the class of a principal object in `H¹(π, G)`. -/
noncomputable def classOf : H1 (Aut F) G :=
  letI := P.act
  P.isPrincipalHomogeneous.classOf

/-- The cocycle `σ ↦ g`, `σ a = a g`, of a point `a` of the fibre of a principal object is
continuous: the action of `π` on `F(X)` is continuous. -/
lemma continuous_cocycleAt [TopologicalSpace G] (a : F.obj P.X) :
    letI := P.act
    Continuous (P.isPrincipalHomogeneous.cocycleAt a) := by
  let _ := P.act
  have : DiscreteTopology (F.obj P.X) := obj_discreteTopology F P.X
  exact (continuous_of_discreteTopology (f := fun y ↦ P.isPrincipalHomogeneous.diff a y)).comp
    (continuous_id.smul continuous_const)

/-- Isomorphic principal objects have the same class. -/
theorem classOf_eq_of_isIso {P Q : TwistedPrincipalObject F G} (h : P.IsIso Q) :
    P.classOf = Q.classOf := by
  obtain ⟨φ, hφ⟩ := h
  let _ := P.act
  let _ := Q.act
  have hinv (z : F.obj P.X) : F.map φ.inv (F.map φ.hom z) = z := by
    rw [← FintypeCat.comp_apply, ← F.map_comp, φ.hom_inv_id, F.map_id, FintypeCat.id_apply]
  have hhom (z : F.obj Q.X) : F.map φ.hom (F.map φ.inv z) = z := by
    rw [← FintypeCat.comp_apply, ← F.map_comp, φ.inv_hom_id, F.map_id, FintypeCat.id_apply]
  exact (P.isPrincipalHomogeneous.classOf_eq_classOf_iff Q.isPrincipalHomogeneous).2
    ⟨{ toFun := F.map φ.hom
       invFun := F.map φ.inv
       left_inv := hinv
       right_inv := hhom
       map_smul' := fun σ x ↦ (mulAction_naturality F σ φ.hom x).symm
       map_op_smul' := fun g x ↦ hφ g x }⟩

variable [GaloisCategory C] [FiberFunctor F]

/-- XI.5 `(*)`, injectivity: principal objects with the same class are isomorphic. The
isomorphism of fibres given by the group theory lifts to `C` since `F` is fully faithful into
`π`-sets (V.4). -/
theorem isIso_of_classOf_eq {P Q : TwistedPrincipalObject F G} (h : P.classOf = Q.classOf) :
    P.IsIso Q := by
  let _ := P.act
  let _ := Q.act
  obtain ⟨e⟩ := (P.isPrincipalHomogeneous.classOf_eq_classOf_iff Q.isPrincipalHomogeneous).1 h
  let ψ : (functorToAction F).obj P.X ⟶ (functorToAction F).obj Q.X :=
    { hom := FintypeCat.homMk e.toFun
      comm := fun σ ↦ by
        ext x
        exact e.map_smul' σ x }
  obtain ⟨φ, hφ⟩ := (functorToAction F).map_surjective ψ
  have hFφ (x : F.obj P.X) : F.map φ x = e.toFun x := congrArg (fun k ↦ k.hom x) hφ
  have : CategoryTheory.IsIso (F.map φ) := (ConcreteCategory.isIso_iff_bijective _).2 (by
    convert e.toEquiv.bijective using 1
    funext x
    exact hFφ x)
  have : CategoryTheory.IsIso φ := isIso_of_reflects_iso φ F
  refine ⟨asIso φ, fun g x ↦ ?_⟩
  change F.map φ (op g • x) = op g • F.map φ x
  rw [hFφ, hFφ]
  exact e.map_op_smul' g x

end TwistedPrincipalObject

variable (F G) in
/-- XI.5: the set of isomorphism classes of principal objects under the `π`-group `G`. -/
def TwistedPrincipalH1 : Type _ :=
  Quotient (⟨TwistedPrincipalObject.IsIso, TwistedPrincipalObject.isIso_equivalence⟩ :
    Setoid (TwistedPrincipalObject F G))

variable (F G) in
/-- The continuous cohomology set `H¹(π, G)`: the classes of continuous cocycles. -/
def ContH1 [TopologicalSpace G] : Type _ :=
  {c : H1 (Aut F) G // ∃ φ : Z1 (Aut F) G, Continuous φ ∧ H1.mk φ = c}

open scoped FintypeCatDiscrete in
/-- XI.5 `(*)`, surjectivity: every continuous cocycle `φ` is the cocycle of a principal object,
which realizes the twisted `π`-set `Twist φ` (V.4: `F` is essentially surjective onto continuous
finite `π`-sets). -/
theorem exists_twistedPrincipalObject_classOf_eq [GaloisCategory C] [FiberFunctor F] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] [ContinuousSMul (Aut F) G] (φ : Z1 (Aut F) G)
    (hφ : Continuous φ) : ∃ P : TwistedPrincipalObject F G, P.classOf = H1.mk φ := by
  have : Finite (Twist φ) := Finite.of_equiv G ⟨Twist.mk, Twist.val, fun _ ↦ rfl, fun _ ↦ rfl⟩
  let _ : Fintype (Twist φ) := Fintype.ofFinite _
  let T : Action FintypeCat.{w} (Aut F) :=
    Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of (Twist φ))
  have hT : T.IsContinuous := by
    rw [ExposeV.isContinuous_iff_isOpen_stabilizer]
    intro (x : Twist φ)
    let f : Aut F → G := fun σ ↦ φ σ * σ • x.val
    have hf : Continuous f := (continuous_of_discreteTopology (f := fun p : G × G ↦ p.1 * p.2)).comp
      (hφ.prodMk (continuous_id.smul continuous_const))
    have : (MulAction.stabilizer (Aut F) (show T.V from x) : Set (Aut F)) = f ⁻¹' {x.val} := by
      ext σ
      simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_singleton_iff]
      change σ • x = x ↔ _
      rw [Twist.ext_iff]
      rfl
    rw [this]
    exact (isOpen_discrete _).preimage hf
  let T' : ContAction FintypeCat.{w} (Aut F) := ⟨T, hT⟩
  let X := (functorToContAction F).objPreimage T'
  let ψ : (functorToAction F).obj X ≅ T :=
    (ObjectProperty.ι _).mapIso ((functorToContAction F).objObjPreimageIso T')
  let e : F.obj X ≃ Twist φ := FintypeCat.equivEquivIso.symm ((Action.forget _ _).mapIso ψ)
  have he (σ : Aut F) (x : F.obj X) : e (σ • x) = σ • e x := ExposeV.Action.hom_smul ψ.hom σ x
  let act : MulAction Gᵐᵒᵖ (F.obj X) :=
    { smul g x := e.symm (g • e x)
      one_smul x := by
        change e.symm ((1 : Gᵐᵒᵖ) • e x) = x
        rw [one_smul, e.symm_apply_apply]
      mul_smul g h x := by
        change e.symm ((g * h) • e x) = e.symm (g • e (e.symm (h • e x)))
        rw [e.apply_symm_apply, mul_smul] }
  have hact (g : Gᵐᵒᵖ) (x : F.obj X) : e (@HSMul.hSMul _ _ _ (@instHSMul _ _ act.toSMul) g x) =
      g • e x := e.apply_symm_apply _
  let _ := act
  have hTw := Twist.isPrincipalHomogeneous φ
  have hP : IsPrincipalHomogeneous (Aut F) G (F.obj X) :=
    { smul_op_smul := fun σ g x ↦ e.injective (by rw [he, hact, hact, he, hTw.smul_op_smul])
      nonempty := ⟨e.symm ⟨1⟩⟩
      existsUnique := fun x y ↦ by
        obtain ⟨g, hg, hu⟩ := hTw.existsUnique (e x) (e y)
        exact ⟨g, e.injective (by rw [hact, hg]), fun g' hg' ↦ hu g' (by
          change op g' • e x = e y
          rw [← hact, hg'])⟩ }
  refine ⟨⟨X, act, hP⟩, ?_⟩
  rw [← Twist.classOf_eq φ]
  exact (hP.classOf_eq_classOf_iff hTw).2
    ⟨{ toEquiv := e
       map_smul' := he
       map_op_smul' := fun g x ↦ hact (op g) x }⟩

/-- XI.5 `(*)` for a non-constant group, in a Galois category: the classes of principal objects
under a finite `π`-group `G` (with continuous action of `π = Aut F`) are in bijection with the
continuous cohomology set `H¹(π, G)`. -/
noncomputable def twistedPrincipalH1Equiv [GaloisCategory C] [FiberFunctor F] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] [ContinuousSMul (Aut F) G] :
    TwistedPrincipalH1 F G ≃ ContH1 F G :=
  Equiv.ofBijective
    (Quotient.lift (fun P : TwistedPrincipalObject F G ↦
        (⟨P.classOf, ⟨_, P.continuous_cocycleAt _, rfl⟩⟩ : ContH1 F G))
      fun _ _ h ↦ Subtype.ext (TwistedPrincipalObject.classOf_eq_of_isIso h))
    ⟨fun c c' h ↦ by
      induction c using Quotient.inductionOn with | h P => ?_
      induction c' using Quotient.inductionOn with | h Q => ?_
      exact Quotient.sound (TwistedPrincipalObject.isIso_of_classOf_eq
        (congrArg Subtype.val h)),
    fun ⟨c, φ, hφ, hc⟩ ↦ by
      obtain ⟨P, hP⟩ := exists_twistedPrincipalObject_classOf_eq φ hφ
      exact ⟨Quotient.mk _ P, Subtype.ext (hP.trans hc)⟩⟩

section Scheme

open AlgebraicGeometry

variable (S : Scheme.{w}) [ConnectedSpace S] (Ω : Type w) [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S) (G : Type w) [Group G] [Finite G] [TopologicalSpace G]
  [DiscreteTopology G] [MulDistribMulAction (ExposeV.etaleFundamentalGroup Ω s) G]
  [ContinuousSMul (ExposeV.etaleFundamentalGroup Ω s) G]

/-- XI.5 `(*)` for a connected scheme `S` with a geometric point `s̄`: for a finite group `G`
with a continuous action of `π₁(S, s̄)` by automorphisms (the fibre of a finite étale group
scheme), the classes of étale coverings `X` whose fibre is a principal homogeneous `G`-set
compatible with `π₁` are in bijection with the continuous cohomology set `H¹(π₁(S, s̄), G)`. -/
noncomputable def twistedPrincipalCoveringH1Equiv :
    TwistedPrincipalH1 (ExposeV.FEt.fiber Ω s) G ≃ ContH1 (ExposeV.FEt.fiber Ω s) G :=
  twistedPrincipalH1Equiv

end Scheme

end SGA.SGA1.ExposeXI
