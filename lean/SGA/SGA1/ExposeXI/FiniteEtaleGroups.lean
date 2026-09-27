/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeXI.TwistedPrincipal
import SGA.SGA1.ExposeXI.AssociatedBundle

/-!
# SGA 1, Exposé XI.5 `(*)`: finite étale group schemes and `H¹(π₁, G)`

Let `S` be a connected scheme with a geometric point `s̄ : Spec Ω ⟶ S` and `π₁ = π₁(S, s̄)`. For
a finite étale group scheme `G` over `S`, the set `G(s̄)` of points of `G` over `s̄` is a finite
group with a continuous action of `π₁` by automorphisms (`MulDistribMulAction`), and XI.5 `(*)`
identifies `H¹(S, G)` with the continuous cohomology set `H¹(π₁, G(s̄))`.

We work with the points `X(s̄)` of étale coverings `X` over `s̄`, which form the fibre functor
of Exposé V (`ExposeV.FEt.fiberEquiv`): `π₁` acts on them compatibly with all `S`-morphisms
(`smul_comp`), morphisms of étale coverings are determined by their action on points
(`hom_ext_of_pts`), every `π₁`-equivariant map of points comes from a morphism
(`exists_hom_of_pts`), and morphisms bijective on points are isomorphisms
(`isIso_of_bijective_pts`) (V.4).

* `ptsMulDistribMulAction`: `π₁` acts on `G(s̄)` by group automorphisms, continuously for the
  discrete topology;
* `twistedOfTorsorObj`: an fpqc torsor `P` under `G` is finite étale (`finiteEtaleHom_of_isTorsorObj`,
  by VIII) and `P(s̄)` is a principal homogeneous `G(s̄)`-set compatible with `π₁`, i.e. a
  principal object of the Galois category (`TwistedPrincipal`);
* conversely every such principal object comes from a torsor (`modObjOfTwisted`,
  `isTorsorObj_twisted`): the action `G ×_S X ⟶ X` is obtained from the action on points by
  fullness of the fibre functor;
* `h1EquivContH1`: XI.5 `(*)`, `H¹(S, G) ≅ H¹(π₁(S, s̄), G(s̄))` (continuous cocycles), where
  `H¹(S, G)` is the set of classes of fpqc torsors, equivalently of principal homogeneous
  bundles (footnote 296, `AssociatedBundle`).
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj PreGaloisCategory
  AlgebraicGeometry

namespace SGA.SGA1.ExposeXI

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] {s : Spec (.of Ω) ⟶ S}

section Points

/-- An `S`-scheme which is finite étale over `S`, as an étale covering. -/
abbrev toFEt (X : Over S) (hX : ExposeV.finiteEtaleHom X.hom) : ExposeV.FEt S :=
  MorphismProperty.Over.mk ⊤ X.hom hX

variable (s) in
/-- The points `Spec Ω ⟶ X` of an `S`-scheme `X` over the geometric point `s̄`. -/
abbrev Pts (X : Over S) : Type u := Over.mk s ⟶ X

/-- The fibre of an étale covering at `s̄` is the set of its points over `s̄`. -/
noncomputable irreducible_def ptsEquiv (X : Over S) (hX : ExposeV.finiteEtaleHom X.hom) :
    (ExposeV.FEt.fiber Ω s).obj (toFEt X hX) ≃ Pts s X :=
  ExposeV.FEt.fiberEquiv Ω s (toFEt X hX)

/-- A morphism of étale coverings, from a morphism of `S`-schemes. -/
abbrev homFEt {X Y : Over S} {hX : ExposeV.finiteEtaleHom X.hom}
    {hY : ExposeV.finiteEtaleHom Y.hom} (f : X ⟶ Y) : toFEt X hX ⟶ toFEt Y hY :=
  MorphismProperty.Over.homMk f.left (Over.w f)

lemma ptsEquiv_map {X Y : Over S} (hX : ExposeV.finiteEtaleHom X.hom)
    (hY : ExposeV.finiteEtaleHom Y.hom) (f : X ⟶ Y) (x : (ExposeV.FEt.fiber Ω s).obj (toFEt X hX)) :
    ptsEquiv Y hY ((ExposeV.FEt.fiber Ω s).map (homFEt f) x) = ptsEquiv X hX x ≫ f := by
  rw [ptsEquiv_def, ptsEquiv_def]
  have := NatTrans.naturality_apply (ExposeV.FEt.fiberInclIso Ω s).hom (homFEt (hX := hX) (hY := hY) f) x
  exact this

end Points

section Action

/-- A finite étale `S`-scheme, as a class (for instance arguments). -/
abbrev IsFiniteEtale (X : Over S) : Prop := Fact (ExposeV.finiteEtaleHom X.hom)

instance (X Y : Over S) [hX : IsFiniteEtale X] [hY : IsFiniteEtale Y] : IsFiniteEtale (X ⊗ Y) := by
  refine ⟨?_⟩
  have := hX.out
  have := hY.out
  change ExposeV.finiteEtaleHom (pullback.fst X.hom Y.hom ≫ X.hom)
  exact ExposeV.finiteEtaleHom.comp_mem _ _
    (ExposeV.finiteEtaleHom.pullback_fst _ _ hY.out) hX.out

instance : IsFiniteEtale (𝟙_ (Over S)) :=
  ⟨ExposeV.finiteEtaleHom.id_mem S⟩

instance : IsFiniteEtale (Over.mk (𝟙 S)) :=
  ⟨ExposeV.finiteEtaleHom.id_mem S⟩

/-- The action of `σ ∈ π₁(S, s̄)` on the points over `s̄` of a finite étale `S`-scheme. -/
noncomputable def ptsSMul (X : Over S) [hX : IsFiniteEtale X] (σ : Aut (ExposeV.FEt.fiber Ω s))
    (p : Pts s X) : Pts s X :=
  ptsEquiv X hX.out (σ • (ptsEquiv X hX.out).symm p)

variable (s) in
/-- The action of `π₁(S, s̄)` on the points over `s̄` of a finite étale `S`-scheme. -/
noncomputable instance ptsMulAction (X : Over S) [hX : IsFiniteEtale X] :
    MulAction (Aut (ExposeV.FEt.fiber Ω s)) (Pts s X) where
  smul := ptsSMul X
  one_smul p := by
    change ptsEquiv X hX.out ((1 : Aut (ExposeV.FEt.fiber Ω s)) • _) = p
    rw [one_smul, Equiv.apply_symm_apply]
  mul_smul σ τ p := by
    change ptsEquiv X hX.out ((σ * τ) • _) =
      ptsEquiv X hX.out (σ • (ptsEquiv X hX.out).symm (ptsEquiv X hX.out (τ • _)))
    rw [Equiv.symm_apply_apply, mul_smul]

lemma smul_eq_ptsSMul (X : Over S) [IsFiniteEtale X] (σ : Aut (ExposeV.FEt.fiber Ω s))
    (p : Pts s X) : σ • p = ptsSMul X σ p :=
  rfl

lemma ptsEquiv_smul (X : Over S) [hX : IsFiniteEtale X] (σ : Aut (ExposeV.FEt.fiber Ω s))
    (x : (ExposeV.FEt.fiber Ω s).obj (toFEt X hX.out)) :
    ptsEquiv X hX.out (σ • x) = σ • ptsEquiv X hX.out x := by
  rw [smul_eq_ptsSMul, ptsSMul, Equiv.symm_apply_apply]

/-- The action of `π₁` on points commutes with all `S`-morphisms of finite étale schemes. -/
lemma smul_comp {X Y : Over S} [hX : IsFiniteEtale X] [hY : IsFiniteEtale Y]
    (σ : Aut (ExposeV.FEt.fiber Ω s)) (p : Pts s X) (f : X ⟶ Y) : σ • (p ≫ f) = (σ • p) ≫ f := by
  obtain ⟨x, rfl⟩ := (ptsEquiv X hX.out).surjective p
  rw [← ptsEquiv_map hX.out hY.out, ← ptsEquiv_smul, ← ptsEquiv_smul, ← ptsEquiv_map hX.out hY.out,
    mulAction_naturality]

variable (G : Over S) [GrpObj G] [IsFiniteEtale G]

/-- XI.5: `π₁` acts on the group `G(s̄)` of points of a finite étale group scheme by group
automorphisms. -/
noncomputable instance ptsMulDistribMulAction :
    MulDistribMulAction (Aut (ExposeV.FEt.fiber Ω s)) (Pts s G) where
  smul_mul σ x y := by
    rw [Hom.mul_def, Hom.mul_def, smul_comp]
    congr 1
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [lift_fst, ← smul_comp, lift_fst]
    · rw [lift_snd, ← smul_comp, lift_snd]
  smul_one σ := by
    rw [Hom.one_def, smul_comp]
    congr 1
    exact toUnit_unique _ _

end Action

section Torsor

variable (G : Over S) [GrpObj G] [IsFiniteEtale G]

/-- `π₁` acts compatibly on `G(s̄)` and on the points of a finite étale `G`-scheme. -/
lemma smul_hom_smul {P : Over S} [ModObj G P] [IsFiniteEtale P] (σ : Aut (ExposeV.FEt.fiber Ω s))
    (g : Pts s G) (p : Pts s P) : σ • (g • p) = (σ • g) • (σ • p) := by
  rw [Hom.smul_def, Hom.smul_def, smul_comp]
  congr 1
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [lift_fst, ← smul_comp, lift_fst]
  · rw [lift_snd, ← smul_comp, lift_snd]

/-- The right action `x g = g⁻¹ x` of `G(s̄)` on the fibre at `s̄` of a finite étale `S`-scheme
with an action of `G`. -/
@[instance_reducible]
noncomputable def fiberRightAction (P : Over S) [ModObj G P] [hP : IsFiniteEtale P] :
    MulAction (Pts s G)ᵐᵒᵖ ((ExposeV.FEt.fiber Ω s).obj (toFEt P hP.out)) where
  smul g x := (ptsEquiv P hP.out).symm (g.unop⁻¹ • ptsEquiv P hP.out x)
  one_smul x := by
    change (ptsEquiv P hP.out).symm ((1 : Pts s G)⁻¹ • ptsEquiv P hP.out x) = x
    rw [inv_one, one_smul, Equiv.symm_apply_apply]
  mul_smul g h x := by
    change (ptsEquiv P hP.out).symm ((h.unop * g.unop)⁻¹ • ptsEquiv P hP.out x) =
      (ptsEquiv P hP.out).symm (g.unop⁻¹ • ptsEquiv P hP.out
        ((ptsEquiv P hP.out).symm (h.unop⁻¹ • ptsEquiv P hP.out x)))
    rw [Equiv.apply_symm_apply, mul_inv_rev, mul_smul]

omit [IsFiniteEtale G] in
lemma ptsEquiv_fiberRightAction (P : Over S) [ModObj G P] [hP : IsFiniteEtale P] (g : Pts s G)
    (x : (ExposeV.FEt.fiber Ω s).obj (toFEt P hP.out)) :
    letI := fiberRightAction (s := s) G P
    ptsEquiv P hP.out (MulOpposite.op g • x) = g⁻¹ • ptsEquiv P hP.out x :=
  Equiv.apply_symm_apply _ _

variable [IsSepClosed Ω] [ConnectedSpace S]

/-- XI.5 `(*)`: the fibre at `s̄` of a finite étale `S`-scheme `P` which is formally principal
homogeneous under `G` and nonempty is a principal homogeneous `G(s̄)`-set compatible with `π₁`. -/
theorem isPrincipalHomogeneous_fiber (P : Over S) [ModObj G P] [hP : IsFiniteEtale P]
    (h : IsIso (ModObj.leftSMul G P)) (hne : Nonempty P.left) :
    letI := fiberRightAction (s := s) G P
    IsPrincipalHomogeneous (Aut (ExposeV.FEt.fiber Ω s)) (Pts s G)
      ((ExposeV.FEt.fiber Ω s).obj (toFEt P hP.out)) := by
  let _ := fiberRightAction (s := s) G P
  refine ⟨fun σ g x ↦ (ptsEquiv P hP.out).injective ?_, ?_, fun x y ↦ ?_⟩
  · rw [ptsEquiv_smul, ptsEquiv_fiberRightAction, ptsEquiv_fiberRightAction, ptsEquiv_smul,
      smul_hom_smul, smul_inv']
  · by_contra hx
    rw [not_nonempty_iff] at hx
    have := ExposeV.FEt.isEmpty_of_isEmpty_fiber Ω s (toFEt P hP.out) hx
    exact this.false hne.some
  · obtain ⟨m, hm, hu⟩ := ModObj.isIso_leftSMul_iff.1 h (Over.mk s) (ptsEquiv P hP.out x)
      (ptsEquiv P hP.out y)
    refine ⟨m⁻¹, (ptsEquiv P hP.out).injective ?_, fun g hg ↦ ?_⟩
    · rw [ptsEquiv_fiberRightAction, inv_inv, hm]
    · have := hu g⁻¹ (by
        change g⁻¹ • ptsEquiv P hP.out x = ptsEquiv P hP.out y
        rw [← ptsEquiv_fiberRightAction, hg])
      rw [← this, inv_inv]

end Torsor

section Faithful

variable [IsSepClosed Ω] [ConnectedSpace S]

/-- Morphisms of finite étale `S`-schemes are determined by their action on points over `s̄`
(V.4: the fibre functor is faithful). -/
lemma hom_ext_of_pts {X Y : Over S} [hX : IsFiniteEtale X] [hY : IsFiniteEtale Y] {f f' : X ⟶ Y}
    (h : ∀ p : Pts s X, p ≫ f = p ≫ f') : f = f' := by
  have : (ExposeV.FEt.fiber Ω s).map (homFEt (hX := hX.out) (hY := hY.out) f) =
      (ExposeV.FEt.fiber Ω s).map (homFEt f') := by
    ext x
    apply (ptsEquiv Y hY.out).injective
    rw [ptsEquiv_map, ptsEquiv_map, h]
  have := (ExposeV.FEt.fiber Ω s).map_injective this
  ext
  exact congrArg (fun k ↦ k.left) this

/-- `π₁`-equivariant maps of points over `s̄` come from morphisms of finite étale `S`-schemes
(V.4: the fibre functor is full onto `π₁`-sets). -/
lemma exists_hom_of_pts {X Y : Over S} [hX : IsFiniteEtale X] [hY : IsFiniteEtale Y]
    (φ : Pts s X → Pts s Y) (hφ : ∀ (σ : Aut (ExposeV.FEt.fiber Ω s)) p, φ (σ • p) = σ • φ p) :
    ∃ f : X ⟶ Y, ∀ p, p ≫ f = φ p := by
  let ψ : (functorToAction (ExposeV.FEt.fiber Ω s)).obj (toFEt X hX.out) ⟶
      (functorToAction (ExposeV.FEt.fiber Ω s)).obj (toFEt Y hY.out) :=
    { hom := FintypeCat.homMk fun x ↦ (ptsEquiv Y hY.out).symm (φ (ptsEquiv X hX.out x))
      comm := fun σ ↦ by
        ext (x : (ExposeV.FEt.fiber Ω s).obj (toFEt X hX.out))
        apply (ptsEquiv Y hY.out).injective
        change ptsEquiv Y hY.out ((ptsEquiv Y hY.out).symm (φ (ptsEquiv X hX.out (σ • x)))) =
          ptsEquiv Y hY.out (σ • (ptsEquiv Y hY.out).symm (φ (ptsEquiv X hX.out x)))
        rw [ptsEquiv_smul, ptsEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hφ] }
  obtain ⟨g, hg⟩ := (functorToAction (ExposeV.FEt.fiber Ω s)).map_surjective ψ
  refine ⟨(MorphismProperty.Over.forget _ ⊤ S).map g, fun p ↦ ?_⟩
  obtain ⟨x, rfl⟩ := (ptsEquiv X hX.out).surjective p
  have hgx : (ExposeV.FEt.fiber Ω s).map g x =
      (ptsEquiv Y hY.out).symm (φ (ptsEquiv X hX.out x)) := congrArg (fun k ↦ k.hom x) hg
  have hg' : g = homFEt ((MorphismProperty.Over.forget _ ⊤ S).map g) := by ext; rfl
  refine (ptsEquiv_map hX.out hY.out _ x).symm.trans ?_
  refine (congrArg (fun k ↦ ptsEquiv Y hY.out ((ExposeV.FEt.fiber Ω s).map k x)) hg').symm.trans ?_
  rw [hgx, Equiv.apply_symm_apply]

/-- A morphism of finite étale `S`-schemes which is bijective on points over `s̄` is an
isomorphism (V.4: the fibre functor reflects isomorphisms). -/
lemma isIso_of_bijective_pts {X Y : Over S} [hX : IsFiniteEtale X] [hY : IsFiniteEtale Y]
    (f : X ⟶ Y) (h : Function.Bijective fun p : Pts s X ↦ p ≫ f) : IsIso f := by
  have hF : ⇑((ExposeV.FEt.fiber Ω s).map (homFEt (hX := hX.out) (hY := hY.out) f)) =
      (ptsEquiv Y hY.out).symm ∘ (fun p : Pts s X ↦ p ≫ f) ∘ ptsEquiv X hX.out := by
    funext x
    apply (ptsEquiv Y hY.out).injective
    rw [ptsEquiv_map]
    simp
  have : IsIso ((ExposeV.FEt.fiber Ω s).map (homFEt (hX := hX.out) (hY := hY.out) f)) := by
    rw [ConcreteCategory.isIso_iff_bijective, hF]
    exact (ptsEquiv Y hY.out).symm.bijective.comp (h.comp (ptsEquiv X hX.out).bijective)
  have : IsIso (homFEt (hX := hX.out) (hY := hY.out) f) :=
    isIso_of_reflects_iso _ (ExposeV.FEt.fiber Ω s)
  exact inferInstanceAs (IsIso ((MorphismProperty.Over.forget _ ⊤ S).map
    (homFEt (hX := hX.out) (hY := hY.out) f)))

end Faithful

/-- The discrete topology on the (finite) set of points over `s̄`. -/
local instance (X : Over S) : TopologicalSpace (Pts s X) := ⊥

local instance (X : Over S) : DiscreteTopology (Pts s X) := ⟨rfl⟩

section Topology

instance (X : Over S) [hX : IsFiniteEtale X] : Finite (Pts s X) :=
  Finite.of_equiv _ (ptsEquiv (s := s) X hX.out)

open scoped FintypeCatDiscrete in
instance (X : Over S) [hX : IsFiniteEtale X] :
    ContinuousSMul (Aut (ExposeV.FEt.fiber Ω s)) (Pts s X) := by
  refine ⟨continuous_prod_of_discrete_right.2 fun p ↦ ?_⟩
  have : DiscreteTopology ((ExposeV.FEt.fiber Ω s).obj (toFEt X hX.out)) :=
    obj_discreteTopology _ _
  change Continuous fun σ : Aut (ExposeV.FEt.fiber Ω s) ↦
    ptsEquiv X hX.out (σ • (ptsEquiv X hX.out).symm p)
  exact (continuous_of_discreteTopology (f := ptsEquiv X hX.out)).comp
    (continuous_id.smul continuous_const)

end Topology

section Cohomology

variable [IsSepClosed Ω] [ConnectedSpace S] (G : Over S) [GrpObj G] [hG : IsFiniteEtale G]

omit [IsSepClosed Ω] [ConnectedSpace S] in
set_option backward.isDefEq.respectTransparency.types false in
/-- XI.4.2 (VIII.5.4): a principal homogeneous bundle under a finite étale group scheme is finite
étale. -/
theorem finiteEtaleHom_of_isTorsorObj {P : Over S} [ModObj G P]
    (h : IsTorsorObj (fpqc S) G P) : ExposeV.finiteEtaleHom P.hom := by
  have : ExposeV.finiteEtaleHom.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    inferInstanceAs (MorphismProperty.DescendsAlong (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact))
  have : IsZariskiLocalAtTarget ExposeV.finiteEtaleHom :=
    inferInstanceAs (IsZariskiLocalAtTarget (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}))
  exact (isPrincipalBundle_of_isTorsorObj h).of_descendsAlong (Q := ExposeV.finiteEtaleHom) hG.out

omit [IsSepClosed Ω] [hG : IsFiniteEtale G] in
/-- A torsor over a nonempty scheme is nonempty. -/
theorem nonempty_of_isTorsorObj {P : Over S} [ModObj G P] (h : IsTorsorObj (fpqc S) G P) :
    Nonempty P.left := by
  obtain ⟨𝒰, S', g, hg, hs⟩ := (isPrincipalBundle_of_isTorsorObj h).exists_trivialization
  obtain ⟨x⟩ := (inferInstance : Nonempty S)
  obtain ⟨i, y, -⟩ := 𝒰.exists_eq x
  obtain ⟨z, -⟩ := (hg i).1.1.surj y
  obtain ⟨t, -⟩ := hs i
  exact ⟨t z⟩

/-- XI.5 `(*)`: the principal object of the Galois category of étale coverings attached to an
fpqc torsor under `G`: its fibre at `s̄` with the action of `G(s̄)`. -/
noncomputable def twistedOfTorsorObj {P : Over S} [ModObj G P] (h : IsTorsorObj (fpqc S) G P) :
    TwistedPrincipalObject (ExposeV.FEt.fiber Ω s) (Pts s G) :=
  haveI : IsFiniteEtale P := ⟨finiteEtaleHom_of_isTorsorObj G h⟩
  ⟨toFEt P (finiteEtaleHom_of_isTorsorObj G h), fiberRightAction G P,
    isPrincipalHomogeneous_fiber G P h.isIso_leftSMul (nonempty_of_isTorsorObj G h)⟩

/-- Equivariantly isomorphic torsors give isomorphic principal objects. -/
theorem twistedOfTorsorObj_isIso {P Q : Over S} [ModObj G P] [ModObj G Q]
    (hP : IsTorsorObj (fpqc S) G P) (hQ : IsTorsorObj (fpqc S) G Q) (e : P ≅ Q)
    [IsModHom G e.hom] :
    (twistedOfTorsorObj (s := s) G hP).IsIso (twistedOfTorsorObj G hQ) := by
  have : IsFiniteEtale P := ⟨finiteEtaleHom_of_isTorsorObj G hP⟩
  have : IsFiniteEtale Q := ⟨finiteEtaleHom_of_isTorsorObj G hQ⟩
  let φ : toFEt P (finiteEtaleHom_of_isTorsorObj G hP) ≅ toFEt Q (finiteEtaleHom_of_isTorsorObj G hQ) :=
    { hom := homFEt e.hom
      inv := homFEt e.inv
      hom_inv_id := by ext; exact congrArg (fun k ↦ k.left) e.hom_inv_id
      inv_hom_id := by ext; exact congrArg (fun k ↦ k.left) e.inv_hom_id }
  have hP' := finiteEtaleHom_of_isTorsorObj G hP
  have hQ' := finiteEtaleHom_of_isTorsorObj G hQ
  refine ⟨φ, fun g x ↦ (ptsEquiv Q hQ').injective ?_⟩
  have h₁ : (twistedOfTorsorObj (s := s) G hP).smul g x =
      (ptsEquiv P hP').symm (g⁻¹ • ptsEquiv P hP' x) := rfl
  have h₂ : ∀ y, (twistedOfTorsorObj (s := s) G hQ).smul g y =
      (ptsEquiv Q hQ').symm (g⁻¹ • ptsEquiv Q hQ' y) := fun y ↦ rfl
  change ptsEquiv Q hQ' ((ExposeV.FEt.fiber Ω s).map (homFEt e.hom) _) =
    ptsEquiv Q hQ' ((twistedOfTorsorObj (s := s) G hQ).smul g
      ((ExposeV.FEt.fiber Ω s).map (homFEt e.hom) x))
  rw [h₁]
  refine (ptsEquiv_map hP' hQ' e.hom _).trans ?_
  refine Eq.trans ?_ (congrArg (ptsEquiv Q hQ') (h₂ ((ExposeV.FEt.fiber Ω s).map (homFEt e.hom) x))).symm
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, IsModHom.map_smul]
  exact congrArg (g⁻¹ • ·) (ptsEquiv_map hP' hQ' e.hom x).symm

/-- Conversely, torsors whose principal objects are isomorphic are equivariantly isomorphic:
isomorphisms of étale coverings are determined by, and compatible with the action on, points. -/
theorem exists_isModHom_of_twisted_isIso {P Q : Over S} [ModObj G P] [ModObj G Q]
    (hP : IsTorsorObj (fpqc S) G P) (hQ : IsTorsorObj (fpqc S) G Q)
    (h : (twistedOfTorsorObj (s := s) G hP).IsIso (twistedOfTorsorObj G hQ)) :
    ∃ e : P ≅ Q, IsModHom G e.hom := by
  obtain ⟨φ, hφ⟩ := h
  have hP' := finiteEtaleHom_of_isTorsorObj G hP
  have hQ' := finiteEtaleHom_of_isTorsorObj G hQ
  have : IsFiniteEtale P := ⟨hP'⟩
  have : IsFiniteEtale Q := ⟨hQ'⟩
  let e : P ≅ Q := (MorphismProperty.Over.forget _ ⊤ S).mapIso φ
  have hφe : φ.hom = homFEt e.hom := by ext; rfl
  -- `e` commutes with the action on points.
  have key (g : Pts s G) (p : Pts s P) : (g • p) ≫ e.hom = g • (p ≫ e.hom) := by
    obtain ⟨x, rfl⟩ := (ptsEquiv P hP').surjective p
    have h₁ : (twistedOfTorsorObj (s := s) G hP).smul g⁻¹ x =
        (ptsEquiv P hP').symm (g⁻¹⁻¹ • ptsEquiv P hP' x) := rfl
    have h₂ := hφ g⁻¹ x
    rw [h₁, hφe] at h₂
    have h₃ : (g⁻¹⁻¹ • ptsEquiv P hP' x) ≫ e.hom = g⁻¹⁻¹ • (ptsEquiv P hP' x ≫ e.hom) := by
      have l := ptsEquiv_map hP' hQ' e.hom ((ptsEquiv P hP').symm (g⁻¹⁻¹ • ptsEquiv P hP' x))
      rw [Equiv.apply_symm_apply] at l
      have r : ptsEquiv Q hQ' ((twistedOfTorsorObj (s := s) G hQ).smul g⁻¹
          ((ExposeV.FEt.fiber Ω s).map (homFEt e.hom) x)) =
            g⁻¹⁻¹ • (ptsEquiv P hP' x ≫ e.hom) := by
        change ptsEquiv Q hQ' ((ptsEquiv Q hQ').symm (g⁻¹⁻¹ • ptsEquiv Q hQ'
          ((ExposeV.FEt.fiber Ω s).map (homFEt e.hom) x))) = _
        rw [Equiv.apply_symm_apply]
        exact congrArg _ (ptsEquiv_map hP' hQ' e.hom x)
      exact l.symm.trans ((congrArg (ptsEquiv Q hQ') h₂).trans r)
    simpa using h₃
  refine ⟨e, ⟨?_⟩⟩
  have : IsFiniteEtale (MonoidalLeftActionStruct.actionObj G P) :=
    (inferInstance : IsFiniteEtale (G ⊗ P))
  change (γ[G, P] : G ⊗ P ⟶ P) ≫ e.hom = (G ◁ e.hom) ≫ γ[G, Q]
  refine hom_ext_of_pts (s := s) fun w ↦ ?_
  have hw : w = lift (w ≫ fst G P) (w ≫ snd G P) :=
    CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)
  rw [hw, ← Category.assoc, ← Category.assoc, lift_whiskerLeft]
  exact key _ _

variable [IsAffineHom G.hom]

/-- XI.5 `(*)`: the class in `H¹(S, G)` of a torsor determines its principal object up to
isomorphism; this is the map from `H¹(S, G)` to principal objects of the Galois category. -/
noncomputable def h1ToTwisted (c : CategoryTheory.H1 (fpqc S) (yonedaGrpObj G)) :
    TwistedPrincipalH1 (ExposeV.FEt.fiber Ω s) (Pts s G) :=
  let h := exists_isPrincipalBundle_of_mem_H1 c
  letI := h.choose_spec.choose
  Quotient.mk _ (twistedOfTorsorObj G h.choose_spec.choose_spec.choose.isTorsorObj)

theorem h1ToTwisted_class {P : Over S} [ModObj G P] (hP : IsTorsorObj (fpqc S) G P) :
    h1ToTwisted (s := s) G hP.class = Quotient.mk _ (twistedOfTorsorObj G hP) := by
  let h := exists_isPrincipalBundle_of_mem_H1 hP.class
  let _ := h.choose_spec.choose
  have hc := h.choose_spec.choose_spec.choose_spec.2
  obtain ⟨e, he⟩ := h.choose_spec.choose_spec.choose.isTorsorObj.exists_isModHom_of_class_eq hP hc
  exact Quotient.sound (twistedOfTorsorObj_isIso G _ hP e)

/-- XI.5 `(*)`, injectivity: two torsors under `G` with isomorphic principal objects have the
same class. -/
theorem h1ToTwisted_injective : Function.Injective (h1ToTwisted (s := s) G) := by
  intro c c' hcc'
  obtain ⟨T, rfl⟩ := CategoryTheory.H1.mk_surjective c
  obtain ⟨T', rfl⟩ := CategoryTheory.H1.mk_surjective c'
  obtain ⟨P, _, hP, -, hPc⟩ := exists_isPrincipalBundle_class_eq T
  obtain ⟨P', _, hP', -, hP'c⟩ := exists_isPrincipalBundle_class_eq T'
  rw [← hPc, ← hP'c] at hcc' ⊢
  rw [h1ToTwisted_class, h1ToTwisted_class] at hcc'
  obtain ⟨e, he⟩ := exists_isModHom_of_twisted_isIso G hP.isTorsorObj hP'.isTorsorObj
    (Quotient.exact hcc')
  exact hP.isTorsorObj.class_eq_of_isModHom hP'.isTorsorObj e.hom

end Cohomology

section Realization

variable [IsSepClosed Ω] [ConnectedSpace S] (G : Over S) [GrpObj G] [hG : IsFiniteEtale G]
  (T : TwistedPrincipalObject (ExposeV.FEt.fiber Ω s) (Pts s G))

/-- The `S`-scheme underlying a principal object. -/
abbrev TwistedPrincipalObject.toOver : Over S :=
  (MorphismProperty.Over.forget _ ⊤ S).obj T.X

instance : IsFiniteEtale T.toOver := ⟨T.X.prop⟩

/-- The fibre of a principal object is the set of points of its underlying scheme. -/
noncomputable def fibEquiv : (ExposeV.FEt.fiber Ω s).obj T.X ≃ Pts s T.toOver :=
  ptsEquiv T.toOver T.X.prop

omit [ConnectedSpace S] [IsSepClosed Ω] in
lemma fibEquiv_smul (σ : Aut (ExposeV.FEt.fiber Ω s)) (x : (ExposeV.FEt.fiber Ω s).obj T.X) :
    fibEquiv G T (σ • x) = σ • fibEquiv G T x :=
  ptsEquiv_smul T.toOver σ x

/-- The left action `g ⋆ p = p g⁻¹` of `G(s̄)` on the points of a principal object. -/
noncomputable def starSMul (g : Pts s G) (p : Pts s T.toOver) : Pts s T.toOver :=
  fibEquiv G T (T.smul g⁻¹ ((fibEquiv G T).symm p))

omit [ConnectedSpace S] [IsSepClosed Ω] in
lemma starSMul_one (p : Pts s T.toOver) : starSMul G T 1 p = p := by
  let _ := T.act
  change fibEquiv G T (MulOpposite.op (1 : Pts s G)⁻¹ • _) = p
  rw [inv_one, MulOpposite.op_one, one_smul, Equiv.apply_symm_apply]

omit [ConnectedSpace S] [IsSepClosed Ω] in
lemma starSMul_mul (g h : Pts s G) (p : Pts s T.toOver) :
    starSMul G T (g * h) p = starSMul G T g (starSMul G T h p) := by
  let _ := T.act
  change fibEquiv G T (MulOpposite.op (g * h)⁻¹ • _) =
    fibEquiv G T (MulOpposite.op g⁻¹ • (fibEquiv G T).symm
      (fibEquiv G T (MulOpposite.op h⁻¹ • _)))
  rw [Equiv.symm_apply_apply, mul_inv_rev, MulOpposite.op_mul, mul_smul]

omit [ConnectedSpace S] [IsSepClosed Ω] in
lemma smul_starSMul (σ : Aut (ExposeV.FEt.fiber Ω s)) (g : Pts s G) (p : Pts s T.toOver) :
    σ • starSMul G T g p = starSMul G T (σ • g) (σ • p) := by
  let _ := T.act
  have hT := T.isPrincipalHomogeneous
  change σ • fibEquiv G T (MulOpposite.op g⁻¹ • (fibEquiv G T).symm p) =
    fibEquiv G T (MulOpposite.op (σ • g)⁻¹ • (fibEquiv G T).symm (σ • p))
  rw [← fibEquiv_smul, hT.smul_op_smul, smul_inv']
  congr 2
  apply (fibEquiv G T).injective
  rw [fibEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

omit [ConnectedSpace S] [IsSepClosed Ω] in
lemma existsUnique_starSMul (p q : Pts s T.toOver) : ∃! g : Pts s G, starSMul G T g p = q := by
  let _ := T.act
  obtain ⟨g, hg, hu⟩ := T.isPrincipalHomogeneous.existsUnique ((fibEquiv G T).symm p)
    ((fibEquiv G T).symm q)
  refine ⟨g⁻¹, ?_, fun g' hg' ↦ ?_⟩
  · change fibEquiv G T (MulOpposite.op g⁻¹⁻¹ • _) = q
    rw [inv_inv, hg, Equiv.apply_symm_apply]
  · have : MulOpposite.op g'⁻¹ • (fibEquiv G T).symm p = (fibEquiv G T).symm q := by
      apply (fibEquiv G T).injective
      rw [Equiv.apply_symm_apply]
      exact hg'
    rw [← hu g'⁻¹ this, inv_inv]

/-- The action morphism `G ×_S X ⟶ X`, `(g, p) ↦ g ⋆ p`, of a principal object (V.4). -/
theorem exists_actionHom : ∃ act : G ⊗ T.toOver ⟶ T.toOver,
    ∀ w : Pts s (G ⊗ T.toOver), w ≫ act = starSMul G T (w ≫ fst _ _) (w ≫ snd _ _) :=
  exists_hom_of_pts _ fun σ w ↦ by rw [smul_starSMul, smul_comp, smul_comp]

/-- The action morphism of a principal object. -/
noncomputable def actionHom : G ⊗ T.toOver ⟶ T.toOver := (exists_actionHom G T).choose

lemma actionHom_spec (w : Pts s (G ⊗ T.toOver)) :
    w ≫ actionHom G T = starSMul G T (w ≫ fst _ _) (w ≫ snd _ _) :=
  (exists_actionHom G T).choose_spec w

-- The defeq check between the monoidal left action `G ⊙ₗ X` of `Over S` on itself and the
-- tensor product `G ⊗ X` (with its associator, given by iterated pullbacks) is slow.
set_option maxHeartbeats 400000 in
/-- The action of `G` on the scheme underlying a principal object. -/
@[instance_reducible]
noncomputable def modObjOfTwisted : ModObj G T.toOver where
  smul := actionHom G T
  one_smul := by
    change η[G] ▷ T.toOver ≫ actionHom G T = (λ_ T.toOver).hom
    refine hom_ext_of_pts (s := s) fun w ↦ ?_
    rw [← Category.assoc, actionHom_spec, leftUnitor_hom, Category.assoc, whiskerRight_fst,
      Category.assoc, whiskerRight_snd]
    have h1 : w ≫ fst _ _ ≫ η[G] = 1 := by
      rw [Hom.one_def, ← Category.assoc]
      exact congrArg (· ≫ η[G]) (toUnit_unique _ _)
    rw [h1, starSMul_one]
  mul_smul := by
    change μ[G] ▷ T.toOver ≫ actionHom G T =
      (α_ G G T.toOver).hom ≫ G ◁ actionHom G T ≫ actionHom G T
    refine hom_ext_of_pts (s := s) fun w ↦ ?_
    let v := w ≫ (α_ G G T.toOver).hom ≫ G ◁ actionHom G T
    have e₁ : (w ≫ fst _ _) ≫ μ[G] = (w ≫ fst _ _ ≫ fst _ _) * (w ≫ fst _ _ ≫ snd _ _) := by
      rw [Hom.mul_def, ← comp_lift, ← comp_lift, lift_fst_snd, Category.comp_id]
    have e₂ : v ≫ fst _ _ = w ≫ fst _ _ ≫ fst _ _ := by simp [v]
    have e₃ : v ≫ snd _ _ = lift (w ≫ fst _ _ ≫ snd _ _) (w ≫ snd _ _) ≫ actionHom G T := by
      simp only [v, Category.assoc, whiskerLeft_snd]
      rw [← Category.assoc (α_ G G T.toOver).hom, ← Category.assoc w]
      congr 1
      exact CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)
    have lhs : w ≫ μ[G] ▷ T.toOver ≫ actionHom G T =
        starSMul G T ((w ≫ fst _ _) ≫ μ[G]) (w ≫ snd _ _) := by
      rw [← Category.assoc, actionHom_spec]
      congr 1 <;> simp
    have rhs : w ≫ (α_ G G T.toOver).hom ≫ G ◁ actionHom G T ≫ actionHom G T =
        starSMul G T (v ≫ fst _ _) (v ≫ snd _ _) := by
      rw [← actionHom_spec]
      simp [v]
    rw [lhs, rhs, e₁, e₂, e₃, actionHom_spec, lift_fst, lift_snd, starSMul_mul]

lemma smul_eq_starSMul (g : Pts s G) (p : Pts s T.toOver) :
    letI := modObjOfTwisted G T
    g • p = starSMul G T g p := by
  let _ := modObjOfTwisted G T
  rw [Hom.smul_def]
  change lift g p ≫ actionHom G T = _
  rw [actionHom_spec, lift_fst, lift_snd]

set_option backward.isDefEq.respectTransparency.types false in
/-- The scheme underlying a principal object, with the action of `G`, is an fpqc `G`-torsor. -/
theorem isTorsorObj_twisted :
    letI := modObjOfTwisted G T
    IsTorsorObj (fpqc S) G T.toOver := by
  let _ := modObjOfTwisted G T
  have : IsFiniteEtale (MonoidalLeftActionStruct.actionObj G T.toOver) :=
    (inferInstance : IsFiniteEtale (G ⊗ T.toOver))
  have hiso : IsIso (ModObj.leftSMul G T.toOver) := by
    refine isIso_of_bijective_pts (s := s) _ ⟨fun w w' hww' ↦ ?_, fun v ↦ ?_⟩
    · have h₁ := congrArg (· ≫ fst T.toOver T.toOver) hww'
      have h₂ := congrArg (· ≫ snd T.toOver T.toOver) hww'
      simp only [Category.assoc, ModObj.leftSMul_fst, ModObj.leftSMul_snd] at h₁ h₂
      change w ≫ actionHom G T = w' ≫ actionHom G T at h₁
      rw [actionHom_spec, actionHom_spec, h₂] at h₁
      have hg := (existsUnique_starSMul G T (w' ≫ snd _ _)
        (starSMul G T (w' ≫ fst _ _) (w' ≫ snd _ _))).unique h₁ rfl
      exact CartesianMonoidalCategory.hom_ext _ _ hg h₂
    · obtain ⟨g, hg, -⟩ := existsUnique_starSMul G T (v ≫ snd _ _) (v ≫ fst _ _)
      refine ⟨lift g (v ≫ snd _ _), CartesianMonoidalCategory.hom_ext _ _ ?_ ?_⟩
      · simp only [Category.assoc, ModObj.leftSMul_fst]
        change lift g (v ≫ snd _ _) ≫ actionHom G T = _
        rw [actionHom_spec, lift_fst, lift_snd, hg]
      · simp
  have hne : Nonempty T.toOver.left := by
    let _ := T.act
    obtain ⟨x⟩ := T.isPrincipalHomogeneous.nonempty
    obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstance
    exact ⟨(fibEquiv G T x).left pt⟩
  have : Nonempty T.X.left := hne
  have : IsFinite T.toOver.hom := T.X.prop.1
  have : Etale T.toOver.hom := T.X.prop.2
  have : Surjective T.toOver.hom :=
    ⟨Set.range_eq_univ.mp (ExposeV.FEt.range_eq_univ T.X)⟩
  exact Scheme.isTorsorObj_of_flat hiso

/-- The principal object of the torsor realizing a principal object `T` is isomorphic to `T`. -/
theorem twistedOfTorsorObj_isTorsorObj_twisted :
    letI := modObjOfTwisted G T
    (twistedOfTorsorObj (s := s) G (isTorsorObj_twisted G T)).IsIso T := by
  let _ := modObjOfTwisted G T
  refine ⟨Iso.refl T.X, fun g x ↦ ?_⟩
  have hid (y : (ExposeV.FEt.fiber Ω s).obj T.X) :
      (ExposeV.FEt.fiber Ω s).map (Iso.refl T.X).hom y = y := by
    rw [Iso.refl_hom, CategoryTheory.Functor.map_id]
    rfl
  refine (hid _).trans (Eq.trans ?_ (congrArg (T.smul g) (hid x).symm))
  change (fibEquiv G T).symm (g⁻¹ • fibEquiv G T x) = T.smul g x
  rw [smul_eq_starSMul]
  change (fibEquiv G T).symm (fibEquiv G T
    (T.smul g⁻¹⁻¹ ((fibEquiv G T).symm (fibEquiv G T x)))) = _
  rw [Equiv.symm_apply_apply]
  exact congrArg₂ T.smul (inv_inv g) ((fibEquiv G T).symm_apply_apply x)

variable [IsAffineHom G.hom]

/-- XI.5 `(*)`, surjectivity: every principal object is the principal object of a torsor. -/
theorem h1ToTwisted_surjective : Function.Surjective (h1ToTwisted (s := s) G) := by
  intro c
  induction c using Quotient.inductionOn with | h T => ?_
  let _ := modObjOfTwisted G T
  have hT := isTorsorObj_twisted G T
  exact ⟨hT.class, (h1ToTwisted_class G hT).trans
    (Quotient.sound (twistedOfTorsorObj_isTorsorObj_twisted G T))⟩

/-- XI.5 `(*)`: for a connected scheme `S` with a geometric point `s̄` and a finite étale group
scheme `G` over `S`, `H¹(S, G)` (fpqc torsors, or principal homogeneous bundles by footnote 296)
is in bijection with the continuous cohomology set `H¹(π₁(S, s̄), G(s̄))`. -/
noncomputable def h1EquivContH1 :
    CategoryTheory.H1 (fpqc S) (yonedaGrpObj G) ≃ ContH1 (ExposeV.FEt.fiber Ω s) (Pts s G) :=
  (Equiv.ofBijective _ ⟨h1ToTwisted_injective G, h1ToTwisted_surjective G⟩).trans
    twistedPrincipalH1Equiv

end Realization

end SGA.SGA1.ExposeXI
