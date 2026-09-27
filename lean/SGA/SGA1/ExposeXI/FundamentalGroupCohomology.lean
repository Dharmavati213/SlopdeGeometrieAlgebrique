/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeV.FundamentalGroupBasePoint
import SGA.SGA1.ExposeV.GaloisCategories

/-!
# SGA 1, Exposé XI.5: principal coverings and `H¹(π₁, 𝒢)`

Let `S` be a connected scheme with a geometric point `s̄`, and `π₁ = π₁(S, s̄)`. For the constant
group `(𝒢)_S` defined by a finite group `𝒢`, a principal homogeneous bundle under `(𝒢)_S` is a
principal covering of `S` with group `𝒢` (V.2.7, V.5.11): an étale covering `P` with a right
action of `𝒢` which is simply transitive on the geometric fibres. SGA identifies (XI.5 `(*)`,
p. 300) the set of their classes up to isomorphism with
`H¹(π₁, 𝒢) = Hom(π₁, 𝒢) / (inner automorphisms of 𝒢)`, continuous homomorphisms, through the
homomorphism `π₁ → 𝒢` attached to a pointed principal covering (V, end of no. 5).

We prove this in any Galois category `C` with fibre functor `F` (`principalH1Equiv`), and
specialize it to the étale coverings of `S` (`principalCoveringH1Equiv`):

* changing the base point `a` of a principal object to `a g` conjugates the homomorphism by `g`
  (`torsorHom_act`), and isomorphic principal objects give the same homomorphism
  (`torsorHom_map`);
* two pointed principal objects with the same homomorphism are isomorphic
  (`exists_iso_of_torsorHom_eq`), and every continuous homomorphism arises
  (`SGA.SGA1.ExposeV.exists_torsorHom_eq`, V.5.11).

The group-theoretic description of `H¹(π₁, 𝒢)` by cocycles for a trivial action is
`SGA.SGA1.ExposeXI.Z1.equivMonoidHom` and `Z1.cohomologous_iff_of_trivial`
(`NonabelianCohomology`). The general case of `(*)`, for a finite `π₁`-group on which `π₁` acts
non-trivially, is `twistedPrincipalH1Equiv` (`TwistedPrincipal`).
-/

universe u₁ u₂ w u

open CategoryTheory Limits PreGaloisCategory

namespace SGA.SGA1.ExposeXI

section Galois

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w}) (G : Type w) [Group G]

/-- XI.5, V.5.11: a principal object under `G`: a non-empty object `X` with a right action
`α : G → Aut(X)ᵒᵖ` which is simply transitive on the fibre `F(X)` (a principal covering with
group `G` when `C` is the category of étale coverings of `S`). -/
structure PrincipalObject where
  /-- The underlying object. -/
  X : C
  /-- The right action of `G`. -/
  α : G →* (Aut X)ᵐᵒᵖ
  isPrincipalHomogeneous : ExposeV.IsPrincipalHomogeneous F α
  nonempty : Nonempty (F.obj X)

variable {F G}

namespace PrincipalObject

/-- The action of `g : G` on the fibre `F(X)`. -/
abbrev act (P : PrincipalObject F G) (g : G) (x : F.obj P.X) : F.obj P.X :=
  F.map (P.α g).unop.hom x

lemma act_mul (P : PrincipalObject F G) (g h : G) (x : F.obj P.X) :
    P.act (g * h) x = P.act h (P.act g x) := by
  simp only [act, map_mul, MulOpposite.unop_mul]
  change F.map ((P.α g).unop.hom ≫ (P.α h).unop.hom) x = _
  rw [F.map_comp, FintypeCat.comp_apply]

lemma act_one (P : PrincipalObject F G) (x : F.obj P.X) : P.act 1 x = x := by
  simp only [act, map_one, MulOpposite.unop_one]
  change F.map (𝟙 P.X) x = x
  rw [F.map_id, FintypeCat.id_apply]

lemma smul_act (P : PrincipalObject F G) (σ : Aut F) (g : G) (x : F.obj P.X) :
    σ • P.act g x = P.act g (σ • x) :=
  mulAction_naturality F σ _ x

/-- Two principal objects are isomorphic if there is a `G`-equivariant isomorphism. -/
def IsIso (P Q : PrincipalObject F G) : Prop :=
  ∃ φ : P.X ≅ Q.X, ∀ g, (P.α g).unop.hom ≫ φ.hom = φ.hom ≫ (Q.α g).unop.hom

lemma isIso_equivalence : Equivalence (@IsIso C _ F G _) where
  refl P := ⟨Iso.refl _, fun g ↦ by simp⟩
  symm := by
    rintro P Q ⟨φ, hφ⟩
    refine ⟨φ.symm, fun g ↦ ?_⟩
    rw [Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← hφ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  trans := by
    rintro P Q R ⟨φ, hφ⟩ ⟨ψ, hψ⟩
    refine ⟨φ ≪≫ ψ, fun g ↦ ?_⟩
    rw [Iso.trans_hom, ← Category.assoc, hφ, Category.assoc, hψ, Category.assoc]

end PrincipalObject

variable (F G) in
/-- XI.5: the set `H¹` of classes of principal objects under `G`, up to isomorphism. -/
def PrincipalH1 : Type _ :=
  Quotient (⟨PrincipalObject.IsIso, PrincipalObject.isIso_equivalence⟩ :
    Setoid (PrincipalObject F G))

variable (G) in
/-- XI.5, p. 300: the set `Hom(π, G) / (inner automorphisms of G)` of continuous homomorphisms
modulo conjugation, which is `H¹(π, G)` for the trivial action of `π` on `G`. -/
def ContHomConj (π : Type*) [Group π] [TopologicalSpace π] [TopologicalSpace G] : Type _ :=
  Quotient (⟨fun ρ ρ' : {ρ : π →* G // Continuous ρ} ↦ ∃ g : G, ∀ σ, ρ'.1 σ = g⁻¹ * ρ.1 σ * g,
    ⟨fun ρ ↦ ⟨1, fun σ ↦ by simp⟩,
      fun {ρ ρ'} ⟨g, h⟩ ↦ ⟨g⁻¹, fun σ ↦ by rw [h]; group⟩,
      fun {ρ ρ' ρ''} ⟨g, h⟩ ⟨g', h'⟩ ↦ ⟨g * g', fun σ ↦ by rw [h', h]; group⟩⟩⟩ :
    Setoid {ρ : π →* G // Continuous ρ})

namespace PrincipalObject

variable (P : PrincipalObject F G)

/-- The homomorphism `π → G` attached to a principal object pointed at `a` (V.5.11): `σ a = a g`. -/
noncomputable abbrev hom (a : F.obj P.X) : Aut F →* G :=
  ExposeV.torsorHom P.isPrincipalHomogeneous a

lemma hom_spec (a : F.obj P.X) (σ : Aut F) : P.act (P.hom a σ) a = σ • a :=
  ExposeV.torsorHom_spec _ a σ

lemma hom_eq_iff (a : F.obj P.X) (σ : Aut F) (g : G) : P.hom a σ = g ↔ P.act g a = σ • a :=
  ExposeV.torsorHom_eq_iff _ a σ g

/-- XI.5: changing the base point `a` to `a g` conjugates the homomorphism `π → G` by `g`. -/
lemma torsorHom_act (a : F.obj P.X) (g : G) (σ : Aut F) :
    P.hom (P.act g a) σ = g⁻¹ * P.hom a σ * g := by
  rw [hom_eq_iff, smul_act, ← hom_spec P a σ, ← act_mul, ← act_mul]
  congr 1
  group

variable [GaloisCategory C] [FiberFunctor F]

omit [GaloisCategory C] [FiberFunctor F] in
/-- XI.5: isomorphic pointed principal objects give the same homomorphism. -/
lemma torsorHom_map (Q : PrincipalObject F G) (φ : P.X ≅ Q.X)
    (hφ : ∀ g, (P.α g).unop.hom ≫ φ.hom = φ.hom ≫ (Q.α g).unop.hom) (a : F.obj P.X) :
    Q.hom (F.map φ.hom a) = P.hom a := by
  ext σ
  rw [hom_eq_iff, mulAction_naturality, ← hom_spec P a σ]
  change F.map (Q.α _).unop.hom (F.map φ.hom a) = F.map φ.hom (F.map (P.α _).unop.hom a)
  rw [← FintypeCat.comp_apply, ← F.map_comp, ← hφ, F.map_comp, FintypeCat.comp_apply]

/-- XI.5: two pointed principal objects with the same homomorphism `π → G` are isomorphic. -/
theorem exists_iso_of_torsorHom_eq (Q : PrincipalObject F G) (a : F.obj P.X) (b : F.obj Q.X)
    (h : P.hom a = Q.hom b) : P.IsIso Q := by
  let eP := Equiv.ofBijective _ (P.isPrincipalHomogeneous.bijective a)
  let eQ := Equiv.ofBijective _ (Q.isPrincipalHomogeneous.bijective b)
  have heP (g : G) : eP g = P.act g a := rfl
  have heQ (g : G) : eQ g = Q.act g b := rfl
  let ψ : F.obj P.X ≃ F.obj Q.X := eP.symm.trans eQ
  have hψ (g : G) : ψ (P.act g a) = Q.act g b := by
    change eQ (eP.symm (eP g)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hψσ (σ : Aut F) (x : F.obj P.X) : ψ (σ • x) = σ • ψ x := by
    obtain ⟨g, rfl⟩ := eP.surjective x
    rw [heP, smul_act, ← hom_spec P a σ, ← act_mul, hψ, hψ g, smul_act, ← hom_spec Q b σ,
      ← act_mul, h]
  let ψ' : (functorToAction F).obj P.X ⟶ (functorToAction F).obj Q.X :=
    { hom := FintypeCat.homMk ψ
      comm := fun σ ↦ by
        ext x
        exact hψσ σ x }
  obtain ⟨φ, hφ⟩ := (functorToAction F).map_surjective ψ'
  have hFφ (x : F.obj P.X) : F.map φ x = ψ x := congrArg (fun k ↦ k.hom x) hφ
  have : CategoryTheory.IsIso (F.map φ) := (ConcreteCategory.isIso_iff_bijective _).2 (by
    convert ψ.bijective using 1
    funext x
    exact hFφ x)
  have : CategoryTheory.IsIso φ := isIso_of_reflects_iso φ F
  refine ⟨asIso φ, fun g ↦ F.map_injective ?_⟩
  ext x
  obtain ⟨k, rfl⟩ := eP.surjective x
  change F.map ((P.α g).unop.hom ≫ φ) (P.act k a) = F.map (φ ≫ (Q.α g).unop.hom) (P.act k a)
  rw [F.map_comp, F.map_comp, FintypeCat.comp_apply, FintypeCat.comp_apply]
  change F.map φ (P.act g (P.act k a)) = Q.act g (F.map φ (P.act k a))
  rw [hFφ, hFφ, ← act_mul, hψ, hψ, ← act_mul]

end PrincipalObject

variable [GaloisCategory C] [FiberFunctor F] [Finite G] [TopologicalSpace G] [DiscreteTopology G]

/-- XI.5 `(*)`, constant group: the class of a principal object determines the conjugacy class of
its homomorphism `π → G`. -/
noncomputable def principalH1ToHom : PrincipalH1 F G → ContHomConj G (Aut F) :=
  Quotient.lift (fun P : PrincipalObject F G ↦ Quotient.mk _
      ⟨P.hom P.nonempty.some, ExposeV.continuous_torsorHom _ _⟩) (by
    rintro P Q ⟨φ, hφ⟩
    refine Quotient.sound ?_
    obtain ⟨g, hg⟩ := (P.isPrincipalHomogeneous.bijective P.nonempty.some).2
      (F.map φ.inv Q.nonempty.some)
    refine ⟨g, fun σ ↦ ?_⟩
    change Q.hom _ σ = _
    have hg' : P.act g P.nonempty.some = F.map φ.inv Q.nonempty.some := hg
    have e : Q.nonempty.some = F.map φ.hom (P.act g P.nonempty.some) := by
      rw [hg', ← FintypeCat.comp_apply, ← F.map_comp, Iso.inv_hom_id, F.map_id,
        FintypeCat.id_apply]
    rw [e, P.torsorHom_map Q φ hφ, P.torsorHom_act])

/-- XI.5 `(*)` for a constant group, in a Galois category: the classes of principal objects under
a finite group `G` are in bijection with the continuous homomorphisms `π → G` modulo inner
automorphisms of `G`, i.e. with `H¹(π, G)` for the trivial action. -/
theorem bijective_principalH1ToHom : Function.Bijective (principalH1ToHom (F := F) (G := G)) := by
  constructor
  · intro c c' h
    induction c using Quotient.inductionOn with | h P => ?_
    induction c' using Quotient.inductionOn with | h Q => ?_
    obtain ⟨g, hg⟩ := Quotient.exact h
    refine Quotient.sound (P.exists_iso_of_torsorHom_eq Q P.nonempty.some
      (Q.act g⁻¹ Q.nonempty.some) (MonoidHom.ext fun σ ↦ ?_))
    have hg' : ∀ σ, Q.hom Q.nonempty.some σ = g⁻¹ * P.hom P.nonempty.some σ * g := hg
    change P.hom _ σ = Q.hom _ σ
    rw [Q.torsorHom_act, hg' σ]
    group
  · intro c
    induction c using Quotient.inductionOn with | h ρ => ?_
    obtain ⟨X, α, hα, a, h⟩ := ExposeV.exists_torsorHom_eq (F := F) ρ.1 ρ.2
    let P : PrincipalObject F G := ⟨X, α, hα, ⟨a⟩⟩
    obtain ⟨g, hg⟩ := (P.isPrincipalHomogeneous.bijective P.nonempty.some).2 a
    refine ⟨Quotient.mk _ P, Quotient.sound ⟨g, fun σ ↦ ?_⟩⟩
    change ρ.1 σ = g⁻¹ * P.hom P.nonempty.some σ * g
    rw [← h, ← P.torsorHom_act]
    exact congrArg (fun b ↦ P.hom b σ) hg.symm

/-- XI.5 `(*)` for a constant group, in a Galois category: `H¹ ≅ Hom(π, G)/conjugation`. -/
noncomputable def principalH1Equiv : PrincipalH1 F G ≃ ContHomConj G (Aut F) :=
  Equiv.ofBijective _ bijective_principalH1ToHom

end Galois

section Scheme

open AlgebraicGeometry

variable (S : Scheme.{u}) [ConnectedSpace S] (Ω : Type u) [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ S) (G : Type u) [Group G] [Finite G] [TopologicalSpace G]
  [DiscreteTopology G]

/-- XI.5 `(*)`, p. 300: for a connected scheme `S` with a geometric point `s̄` and a finite group
`𝒢`, the classes of principal coverings of `S` with group `𝒢` (principal homogeneous bundles
under the constant group `(𝒢)_S`, V.2.7) are in bijection with the continuous homomorphisms
`π₁(S, s̄) → 𝒢` modulo inner automorphisms of `𝒢`, i.e. `H¹(S, 𝒢) ≅ H¹(π₁, 𝒢)`. -/
noncomputable def principalCoveringH1Equiv :
    PrincipalH1 (ExposeV.FEt.fiber Ω s) G ≃ ContHomConj G (ExposeV.etaleFundamentalGroup Ω s) :=
  principalH1Equiv

end Scheme

end SGA.SGA1.ExposeXI
