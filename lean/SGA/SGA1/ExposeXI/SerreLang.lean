/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.GroupScheme.MulNCotangent
import SGA.SGA1.ExposeII.Permanence
import SGA.SGA1.ExposeXI.AbelianFundamentalGroup

/-!
# SGA 1, Exposé XI.2.1: the theorem of Serre–Lang

`SerreLangStatement` (in `Geometry`): let `A` be an abelian variety over an algebraically closed
field `k` and `Y ⟶ A` a connected étale covering. Then there is `n > 0` such that multiplication
by `n` on `A` factors through `Y`. This is the key step towards SGA's XI.2.1,
`π₁(A) ≅ T(A) = lim_n K_n` (the Tate module), which is `AbelianVarietyFundamentalGroupStatement`
(in `TateModule`). XI.2.1 is proved in characteristic `0` (`exists_tateModule_equiv_of_charZero`,
in `AbelianVarietyMulN`) and from SGA's cited fact that `n_A` is an isogeny
(`abelianVarietyFundamentalGroupStatement_of_mulNIsogeny`, in `AbelianVarietyQuotient`); its
`ℓ`-primary clause is proved for every prime `ℓ ≠ char k`
(`abelianVarietyPrimaryComponent_of_natCast_ne_zero`, in `TateModulePrimeToP`). In characteristic
`p > 0`, XI.2.1 for `A` is equivalent to its `p`-primary clause
(`abelianVarietyFundamentalGroupConclusion_iff_primaryComponent_charP`, in `TateModuleProduct`),
which is open; it follows from `p_A` being an isogeny (`exists_tateModule_equiv_of_charP`).

SGA derives it from the fact that a pointed connected principal covering of `A` with commutative
group is an isogeny, and every isogeny is a quotient of some `n_A`. We use instead only the
commutativity of `π₁(A)` (XI.2, `mul_comm_of_monObj`) and the Künneth formula X.1.7
(`ExposeX.bijective_map_prod`).

* For a pointed morphism `u` (`t ≫ u = s`) we write `pointedMap u t s` for the homomorphism
  `π₁(T, t) → π₁(S, s)`. When the target group is commutative, these homomorphisms are
  functorial on the nose (`pointedMap_pointedMap`, `pointedMap_id`): the conjugations of V.6.3 are
  then trivial (`autMap_eq_of_comm`).
* `pointedMap_lift_comp_mul`: for an H-space `X` with multiplication `m`, the morphism
  `x ↦ m(u x, v x)` induces `σ ↦ u_* σ · v_* σ` on `π₁(X, e)`; hence multiplication by `n`
  induces `σ ↦ σⁿ` (`pointedMap_mulN`).
* `exists_lift_of_forall_smul_eq_of_apply`: a pointed morphism `u : T ⟶ S` lifts to an étale
  covering `Y ⟶ S` through a point `y` of the fibre of `Y` at `s` as soon as `u_* π₁(T, t)` fixes
  `y` (the lifting criterion for coverings). It and the section criterion
  `exists_section_of_forall_smul_eq_of_apply` are V.6.4
  (`ExposeX.exists_section_iff_forall_smul_eq`) read on the terminal covering;
  `exists_lift_of_forall_smul_eq` and `exists_section_of_forall_smul_eq` forget the point.
* If `π₁` is commutative and acts transitively on a fibre of `d` points, then `σᵈ` acts trivially
  (`pow_card_smul_eq`); with `n = d` this proves `SerreLangStatement` (`serreLangStatement`).
-/

universe u w

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeXI

section AutMap

variable {C D : Type*} [Category C] [Category D] {F : D ⥤ FintypeCat.{w}}
  {F' : C ⥤ FintypeCat.{w}}

/-- If `Aut F'` is commutative, the homomorphism `Aut F → Aut F'` induced by `H` and an
isomorphism `H ⋙ F ≅ F'` does not depend on the isomorphism: two choices differ by a
conjugation in `Aut F'`. -/
lemma autMap_eq_of_comm {H : C ⥤ D} (e e' : H ⋙ F ≅ F')
    (hc : ∀ a b : Aut F', a * b = b * a) : ExposeV.autMap H e = ExposeV.autMap H e' := by
  ext σ : 1
  let ψ : Aut F' := e.symm ≪≫ e'
  have h : ExposeV.autMap H e' σ = ψ * ExposeV.autMap H e σ * ψ⁻¹ := by
    apply Iso.ext
    refine NatTrans.ext (funext fun X ↦ ?_)
    change e'.inv.app X ≫ σ.hom.app (H.obj X) ≫ e'.hom.app X =
      (e'.inv.app X ≫ e.hom.app X) ≫ (e.inv.app X ≫ σ.hom.app (H.obj X) ≫ e.hom.app X) ≫
        (e.inv.app X ≫ e'.hom.app X)
    simp
  rw [h, hc ψ, mul_inv_cancel_right]

/-- If `Aut F'` is commutative, the homomorphism `Aut F → Aut F'` induced by `H` only depends on
`H` up to isomorphism. -/
lemma autMap_eq_of_iso_of_comm {H H' : C ⥤ D} (ρ : H ≅ H') (e : H ⋙ F ≅ F')
    (e' : H' ⋙ F ≅ F') (hc : ∀ a b : Aut F', a * b = b * a) :
    ExposeV.autMap H e = ExposeV.autMap H' e' := by
  rw [← ExposeV.autMap_congr ρ e']
  exact autMap_eq_of_comm _ _ hc

end AutMap

section PointedMap

variable (Ω : Type u) [Field Ω] {R S T : Scheme.{u}}

/-- V.7: the homomorphism `π₁(T, t̄) → π₁(S, s̄)` induced by `f : T ⟶ S` with `t̄ ≫ f = s̄`:
`π₁(f; t̄)` followed by the identification of the fibre functors at the equal points
`f ∘ t̄ = s̄`. -/
noncomputable def pointedMap (f : T ⟶ S) (t : Spec (.of Ω) ⟶ T) (s : Spec (.of Ω) ⟶ S)
    (h : t ≫ f = s) : ExposeV.etaleFundamentalGroup Ω t →* ExposeV.etaleFundamentalGroup Ω s :=
  ExposeV.autMap (ExposeV.FEt.pullback f)
    (ExposeV.FEt.pullbackFiberIso Ω f t ≪≫ ExposeV.FEt.fiberCongr Ω h)

/-- `pointedMap` is `π₁(f; t̄)` followed by the identification `π₁(S, f ∘ t̄) ≅ π₁(S, s̄)`. -/
lemma pointedMap_eq (f : T ⟶ S) (t : Spec (.of Ω) ⟶ T) (s : Spec (.of Ω) ⟶ S)
    (h : t ≫ f = s) :
    pointedMap Ω f t s h =
      (fundamentalGroupCongr h).toMonoidHom.comp (ExposeV.etaleFundamentalGroup.map Ω f t) := by
  subst h
  ext σ : 1
  simp [pointedMap, ExposeV.etaleFundamentalGroup.map, ExposeV.FEt.fiberCongr,
    fundamentalGroupCongr]

/-- `pointedMap` only depends on the morphism `f`, not on the proof of `t̄ ≫ f = s̄`. -/
lemma pointedMap_of_eq {f f' : T ⟶ S} (hf : f = f') (t : Spec (.of Ω) ⟶ T)
    (s : Spec (.of Ω) ⟶ S) (h : t ≫ f = s) (h' : t ≫ f' = s) :
    pointedMap Ω f t s h = pointedMap Ω f' t s h' := by
  subst hf
  rfl

variable {Ω}

/-- V.6.3 for commutative fundamental groups: `(f ≫ g)_* = g_* ∘ f_*` when `π₁(R, r̄)` is
commutative. -/
lemma pointedMap_pointedMap (f : T ⟶ S) (g : S ⟶ R) (t : Spec (.of Ω) ⟶ T)
    (s : Spec (.of Ω) ⟶ S) (r : Spec (.of Ω) ⟶ R) (h₁ : t ≫ f = s) (h₂ : s ≫ g = r)
    (h : t ≫ f ≫ g = r) (hc : ∀ a b : ExposeV.etaleFundamentalGroup Ω r, a * b = b * a)
    (x : ExposeV.etaleFundamentalGroup Ω t) :
    pointedMap Ω g s r h₂ (pointedMap Ω f t s h₁ x) = pointedMap Ω (f ≫ g) t r h x := by
  rw [← MonoidHom.comp_apply, pointedMap, pointedMap, ExposeV.autMap_comp, pointedMap,
    autMap_eq_of_iso_of_comm (MorphismProperty.Over.pullbackComp f g).symm _ _ hc]

/-- `π₁` of the identity is the identity, when `π₁(T, t̄)` is commutative. -/
lemma pointedMap_id (t : Spec (.of Ω) ⟶ T) (h : t ≫ 𝟙 T = t)
    (hc : ∀ a b : ExposeV.etaleFundamentalGroup Ω t, a * b = b * a)
    (x : ExposeV.etaleFundamentalGroup Ω t) : pointedMap Ω (𝟙 T) t t h x = x := by
  rw [pointedMap, autMap_eq_of_iso_of_comm (ExposeV.FEt.pullbackId T) _
    (Functor.leftUnitor _) hc]
  apply Iso.ext
  refine NatTrans.ext (funext fun X ↦ ?_)
  simp [ExposeV.autMap_hom_app]

/-- A morphism factoring through the spectrum of a separably closed field kills `π₁`, when the
target group is commutative. -/
lemma pointedMap_comp_eq_one (Ω' : Type u) [Field Ω'] [IsSepClosed Ω'] [IsSepClosed Ω]
    (p : T ⟶ Spec (.of Ω')) (q : Spec (.of Ω') ⟶ S) (t : Spec (.of Ω) ⟶ T)
    (s : Spec (.of Ω) ⟶ S) (h : t ≫ p ≫ q = s)
    (hc : ∀ a b : ExposeV.etaleFundamentalGroup Ω s, a * b = b * a)
    (x : ExposeV.etaleFundamentalGroup Ω t) : pointedMap Ω (p ≫ q) t s h x = 1 := by
  rw [← pointedMap_pointedMap p q t (t ≫ p) s rfl (by rw [Category.assoc, h]) h hc,
    ExposeV.etaleFundamentalGroup.eq_one_of_isSepClosed Ω Ω' (t ≫ p) (pointedMap Ω p t _ rfl x),
    map_one]

end PointedMap

section Lifting

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] {S T : Scheme.{u}}

/-- The structure morphism of the terminal étale covering of `T` is an isomorphism. -/
lemma isIso_terminal_hom (T : Scheme.{u}) :
    IsIso ((⊤_ ExposeV.FEt T).hom : (⊤_ ExposeV.FEt T).left ⟶ T) := by
  let T' : ExposeV.FEt T := MorphismProperty.Over.mk ⊤ (𝟙 T) ⟨inferInstance, inferInstance⟩
  have : IsIso (T'.hom : T'.left ⟶ T) := inferInstanceAs (IsIso (𝟙 T))
  let e := terminalIsoIsTerminal (ExposeV.FEt.isTerminalOfIsIso T')
  have h : ((⊤_ ExposeV.FEt T).hom : (⊤_ ExposeV.FEt T).left ⟶ T) = e.hom.left :=
    (MorphismProperty.Over.w e.hom).symm.trans (Category.comp_id _)
  rw [h]
  exact inferInstanceAs
    (IsIso ((MorphismProperty.Over.forget _ ⊤ T ⋙ CategoryTheory.Over.forget T).map e.hom))

/-- An étale covering `Z` of a connected scheme `T` has a section through a point `z` of its
fibre at `t̄` as soon as the fundamental group fixes `z`. This is V.6.4
(`ExposeX.exists_section_iff_forall_smul_eq`) read on the terminal covering. -/
theorem exists_section_of_forall_smul_eq_of_apply [ConnectedSpace T] (t : Spec (.of Ω) ⟶ T)
    (Z : ExposeV.FEt T) (z : (ExposeV.FEt.fiber Ω t).obj Z)
    (hz : ∀ σ : ExposeV.etaleFundamentalGroup Ω t, σ • z = z) :
    ∃ g : T ⟶ Z.left, g ≫ Z.hom = 𝟙 T ∧ t ≫ g = ExposeV.FEt.fiberPoint Ω z := by
  obtain ⟨s, p, rfl⟩ := (ExposeX.exists_section_iff_forall_smul_eq _ Z z).mpr hz
  have := isIso_terminal_hom T
  refine ⟨inv ((⊤_ ExposeV.FEt T).hom : (⊤_ ExposeV.FEt T).left ⟶ T) ≫ s.left, ?_, ?_⟩
  · rw [Category.assoc, MorphismProperty.Over.w s, IsIso.inv_hom_id]
  · rw [ExposeV.FEt.fiberPoint_map, (IsIso.eq_comp_inv _).mpr (ExposeV.FEt.fiberPoint_comp Ω p),
      Category.assoc]

/-- An étale covering of a connected scheme has a section as soon as the fundamental group fixes
a point of its fibre (`exists_section_of_forall_smul_eq_of_apply`, forgetting the point). -/
theorem exists_section_of_forall_smul_eq [ConnectedSpace T] (t : Spec (.of Ω) ⟶ T)
    (Z : ExposeV.FEt T) (z : (ExposeV.FEt.fiber Ω t).obj Z)
    (hz : ∀ σ : ExposeV.etaleFundamentalGroup Ω t, σ • z = z) :
    ∃ g : T ⟶ Z.left, g ≫ Z.hom = 𝟙 T :=
  (exists_section_of_forall_smul_eq_of_apply t Z z hz).imp fun _ h ↦ h.1

/-- The pointed lifting criterion for étale coverings: a morphism `u : T ⟶ S` with `T` connected
and `t̄ ≫ u = s̄` lifts to an étale covering `Y ⟶ S` through a point `y` of the fibre of `Y` at
`s̄`, as soon as the image of `u_* : π₁(T, t̄) → π₁(S, s̄)` fixes `y`. (Then `u^• Y` has a section
through the corresponding point, `exists_section_of_forall_smul_eq_of_apply`.) -/
theorem exists_lift_of_forall_smul_eq_of_apply [ConnectedSpace T] (u : T ⟶ S)
    (t : Spec (.of Ω) ⟶ T) (s : Spec (.of Ω) ⟶ S) (h : t ≫ u = s) (Y : ExposeV.FEt S)
    (y : (ExposeV.FEt.fiber Ω s).obj Y)
    (hy : ∀ σ : ExposeV.etaleFundamentalGroup Ω t, pointedMap Ω u t s h σ • y = y) :
    ∃ g : T ⟶ Y.left, g ≫ Y.hom = u ∧ t ≫ g = ExposeV.FEt.fiberPoint Ω y := by
  let E := ExposeV.FEt.pullbackFiberIso Ω u t ≪≫ ExposeV.FEt.fiberCongr Ω h
  let z := E.inv.app Y y
  have hEz : E.hom.app Y z = y := FintypeCat.inv_hom_id_apply (E.app Y) y
  have hz (σ : ExposeV.etaleFundamentalGroup Ω t) : σ • z = z := by
    apply ((ConcreteCategory.isIso_iff_bijective (E.hom.app Y)).mp inferInstance).1
    have : (pointedMap Ω u t s h σ).hom.app Y (E.hom.app Y z) =
        E.hom.app Y (σ.hom.app _ z) := by
      change E.hom.app Y (σ.hom.app _ (E.inv.app Y (E.hom.app Y z))) = _
      exact congrArg (fun x ↦ E.hom.app Y (σ.hom.app _ x))
        (FintypeCat.hom_inv_id_apply (E.app Y) z)
    change E.hom.app Y (σ.hom.app _ z) = E.hom.app Y z
    rw [← this, hEz]
    exact hy σ
  obtain ⟨g, hg, htg⟩ := exists_section_of_forall_smul_eq_of_apply t _ z hz
  refine ⟨g ≫ ExposeV.FEt.proj u Y, ?_, ?_⟩
  · have hY : ExposeV.FEt.proj u Y ≫ Y.hom = ((ExposeV.FEt.pullback u).obj Y).hom ≫ u :=
      pullback.condition
    rw [Category.assoc, hY, ← Category.assoc, hg, Category.id_comp]
  · have : ExposeV.FEt.fiberPoint Ω y = ExposeV.FEt.fiberPoint Ω z ≫ ExposeV.FEt.proj u Y := by
      rw [← hEz]
      change ExposeV.FEt.fiberPoint Ω ((ExposeV.FEt.fiberCongr Ω h).hom.app Y
        ((ExposeV.FEt.pullbackFiberIso Ω u t).hom.app Y z)) = _
      rw [ExposeV.FEt.fiberPoint_fiberCongr, ExposeV.FEt.fiberPoint_pullbackFiberIso]
    rw [this, ← Category.assoc, htg]

/-- The lifting criterion for étale coverings: a morphism `u : T ⟶ S` with `T` connected and
`t̄ ≫ u = s̄` factors through an étale covering `Y ⟶ S` as soon as the image of
`u_* : π₁(T, t̄) → π₁(S, s̄)` fixes a point of the fibre of `Y` at `s̄`
(`exists_lift_of_forall_smul_eq_of_apply`, forgetting the point). -/
theorem exists_lift_of_forall_smul_eq [ConnectedSpace T] (u : T ⟶ S) (t : Spec (.of Ω) ⟶ T)
    (s : Spec (.of Ω) ⟶ S) (h : t ≫ u = s) (Y : ExposeV.FEt S)
    (y : (ExposeV.FEt.fiber Ω s).obj Y)
    (hy : ∀ σ : ExposeV.etaleFundamentalGroup Ω t, pointedMap Ω u t s h σ • y = y) :
    ∃ g : T ⟶ Y.left, g ≫ Y.hom = u :=
  (exists_lift_of_forall_smul_eq_of_apply u t s h Y y hy).imp fun _ h ↦ h.1

end Lifting

section GroupTheory

/-- If a commutative group acts transitively on a finite set of `d` elements, `σᵈ` acts
trivially for every `σ`: the stabilizers are normal of index `d`. -/
lemma pow_card_smul_eq {G X : Type*} [Group G] [MulAction G X] [Finite X]
    [MulAction.IsPretransitive G X] (hc : ∀ a b : G, a * b = b * a) (x : X) (σ : G) :
    σ ^ Nat.card X • x = x := by
  have : (MulAction.stabilizer G x).Normal :=
    ⟨fun n hn g ↦ by rwa [hc g n, mul_inv_cancel_right]⟩
  have := (MulAction.stabilizer G x).pow_index_mem σ
  rwa [MulAction.index_stabilizer_of_transitive] at this

end GroupTheory

section HSpace

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- XI.2: on an H-space `X` (proper, connected and reduced over `k`, with unit `e` and
multiplication `m`), the morphism `x ↦ m(u x, v x)` induces `σ ↦ u_* σ · v_* σ` on `π₁(X, e)`,
for pointed endomorphisms `u, v` of `X` over `k`. The proof uses the Künneth formula X.1.7. -/
theorem pointedMap_lift_comp_mul {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsProper sX]
    [IsReduced X] [ConnectedSpace X] (e : Spec (.of k) ⟶ X) (he : e ≫ sX = 𝟙 _)
    (m : pullback sX sX ⟶ X)
    (hm₁ : pullback.lift (𝟙 X) (sX ≫ e) (by simp [he]) ≫ m = 𝟙 X)
    (hm₂ : pullback.lift (sX ≫ e) (𝟙 X) (by simp [he]) ≫ m = 𝟙 X)
    (u v : X ⟶ X) (huv : u ≫ sX = v ≫ sX) (hu : e ≫ u = e) (hv : e ≫ v = e)
    (h : e ≫ pullback.lift u v huv ≫ m = e) (σ : ExposeV.etaleFundamentalGroup k e) :
    pointedMap k (pullback.lift u v huv ≫ m) e e h σ =
      pointedMap k u e e hu σ * pointedMap k v e e hv σ := by
  have hc := mul_comm_of_hSpace sX e he m hm₁ hm₂
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let w : X ⟶ pullback sX sX := pullback.lift u v huv
  let i₁ : X ⟶ pullback sX sX := pullback.lift (𝟙 X) (sX ≫ e) (by simp [he])
  let i₂ : X ⟶ pullback sX sX := pullback.lift (sX ≫ e) (𝟙 X) (by simp [he])
  let c : Spec (.of k) ⟶ pullback sX sX := pullback.lift e e rfl
  have hw₁ : w ≫ pullback.fst sX sX = u := pullback.lift_fst _ _ _
  have hw₂ : w ≫ pullback.snd sX sX = v := pullback.lift_snd _ _ _
  have hi₁₁ : i₁ ≫ pullback.fst sX sX = 𝟙 X := pullback.lift_fst _ _ _
  have hi₁₂ : i₁ ≫ pullback.snd sX sX = sX ≫ e := pullback.lift_snd _ _ _
  have hi₂₁ : i₂ ≫ pullback.fst sX sX = sX ≫ e := pullback.lift_fst _ _ _
  have hi₂₂ : i₂ ≫ pullback.snd sX sX = 𝟙 X := pullback.lift_snd _ _ _
  have hcf : c ≫ pullback.fst sX sX = e := pullback.lift_fst _ _ _
  have hcs : c ≫ pullback.snd sX sX = e := pullback.lift_snd _ _ _
  have hee : e ≫ sX ≫ e = e := by rw [← Category.assoc, he, Category.id_comp]
  have hw : e ≫ w = c := by
    apply pullback.hom_ext
    · rw [Category.assoc, hw₁, hu, hcf]
    · rw [Category.assoc, hw₂, hv, hcs]
  have h₁ : e ≫ i₁ = c := by
    apply pullback.hom_ext
    · rw [Category.assoc, hi₁₁, Category.comp_id, hcf]
    · rw [Category.assoc, hi₁₂, hee, hcs]
  have h₂ : e ≫ i₂ = c := by
    apply pullback.hom_ext
    · rw [Category.assoc, hi₂₁, hee, hcf]
    · rw [Category.assoc, hi₂₂, Category.comp_id, hcs]
  have hconst (h' : e ≫ sX ≫ e = e) (x : ExposeV.etaleFundamentalGroup k e) :
      pointedMap k (sX ≫ e) e e h' x = 1 :=
    pointedMap_comp_eq_one k sX e e e h' hc x
  -- By X.1.7, an element of `π₁(X ×ₖ X, c)` is determined by its two projections.
  have hinj (τ τ' : ExposeV.etaleFundamentalGroup k c)
      (h₁ : pointedMap k (pullback.fst sX sX) c e hcf τ =
        pointedMap k (pullback.fst sX sX) c e hcf τ')
      (h₂ : pointedMap k (pullback.snd sX sX) c e hcs τ =
        pointedMap k (pullback.snd sX sX) c e hcs τ') : τ = τ' := by
    have hΦ := ExposeX.bijective_map_prod sX sX c (by rw [reassoc_of% hcs, he])
    rw [pointedMap_eq] at h₁ h₂
    apply hΦ.1
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, EmbeddingLike.apply_eq_iff_eq]
      at h₁ h₂
    simp only [MonoidHom.prod_apply, h₁, h₂]
  set a := pointedMap k u e e hu σ
  set b := pointedMap k v e e hv σ
  have key : pointedMap k w e c hw σ = pointedMap k i₁ e c h₁ a * pointedMap k i₂ e c h₂ b := by
    apply hinj
    · rw [map_mul, pointedMap_pointedMap w _ e c e hw hcf (by rw [hw₁, hu]) hc,
        pointedMap_pointedMap i₁ _ e c e h₁ hcf (by rw [hi₁₁, Category.comp_id]) hc,
        pointedMap_pointedMap i₂ _ e c e h₂ hcf (by rw [hi₂₁, hee]) hc,
        pointedMap_of_eq k hw₁ e e _ hu,
        pointedMap_of_eq k hi₁₁ e e _ (Category.comp_id e),
        pointedMap_of_eq k hi₂₁ e e _ hee, pointedMap_id e _ hc, hconst, mul_one]
    · rw [map_mul, pointedMap_pointedMap w _ e c e hw hcs (by rw [hw₂, hv]) hc,
        pointedMap_pointedMap i₁ _ e c e h₁ hcs (by rw [hi₁₂, hee]) hc,
        pointedMap_pointedMap i₂ _ e c e h₂ hcs (by rw [hi₂₂, Category.comp_id]) hc,
        pointedMap_of_eq k hw₂ e e _ hv,
        pointedMap_of_eq k hi₁₂ e e _ hee,
        pointedMap_of_eq k hi₂₂ e e _ (Category.comp_id e), pointedMap_id e _ hc, hconst,
        one_mul]
  have hcm : c ≫ m = e := by rw [← h₁, Category.assoc, hm₁, Category.comp_id]
  rw [← pointedMap_pointedMap w m e c e hw hcm h hc, key, map_mul,
    pointedMap_pointedMap i₁ m e c e h₁ hcm (by rw [← Category.assoc, h₁, hcm]) hc,
    pointedMap_pointedMap i₂ m e c e h₂ hcm (by rw [← Category.assoc, h₂, hcm]) hc,
    pointedMap_of_eq k hm₁ e e _ (Category.comp_id e),
    pointedMap_of_eq k hm₂ e e _ (Category.comp_id e), pointedMap_id e _ hc,
    pointedMap_id e _ hc]

open MonoidalCategory CartesianMonoidalCategory MonObj

omit [IsAlgClosed k] in
/-- Multiplication by `n` fixes the unit section: the underlying morphisms of schemes in
`AlgebraicGeometry.GroupScheme.eta_comp_pow`. -/
lemma unit_comp_mulN_left (A : Over (Spec (.of k))) [MonObj A] (n : ℕ) :
    (η[A].left : Spec (.of k) ⟶ A.left) ≫ (mulN A n).left = η[A].left :=
  congrArg CommaMorphism.left (GroupScheme.eta_comp_pow (A := A) (n := n))

/-- XI.2: multiplication by `n` on a monoid scheme `A` (proper, connected and reduced over an
algebraically closed field) induces `σ ↦ σⁿ` on `π₁(A, e)`. -/
theorem pointedMap_mulN (A : Over (Spec (.of k))) [MonObj A] [IsProper A.hom]
    [IsReduced A.left] [ConnectedSpace A.left] (n : ℕ)
    (h : (η[A].left : Spec (.of k) ⟶ A.left) ≫ (mulN A n).left = η[A].left)
    (σ : ExposeV.etaleFundamentalGroup k (η[A].left : Spec (.of k) ⟶ A.left)) :
    pointedMap k (mulN A n).left _ _ h σ = σ ^ n := by
  have he : (η[A].left : Spec (.of k) ⟶ A.left) ≫ A.hom = 𝟙 _ := Over.w η[A]
  have hm₁ : pullback.lift (𝟙 A.left) (A.hom ≫ η[A].left) (by simp [he]) ≫ μ[A].left =
      𝟙 A.left := by
    have h := congrArg CommaMorphism.left (lift_comp_one_right (𝟙 A) (toUnit A))
    simp only [Over.comp_left, Over.lift_left, Over.id_left, Over.toUnit_left] at h
    exact h
  have hm₂ : pullback.lift (A.hom ≫ η[A].left) (𝟙 A.left) (by simp [he]) ≫ μ[A].left =
      𝟙 A.left := by
    have h := congrArg CommaMorphism.left (lift_comp_one_left (toUnit A) (𝟙 A))
    simp only [Over.comp_left, Over.lift_left, Over.id_left, Over.toUnit_left] at h
    exact h
  have hc := mul_comm_of_monObj A
  induction n with
  | zero =>
    have h0 : (mulN A 0).left = A.hom ≫ η[A].left := by
      simp [mulN, Hom.one_def]
    rw [pointedMap_of_eq k h0 _ _ _ (by rw [← h0, h]), pow_zero]
    exact pointedMap_comp_eq_one k A.hom _ _ _ _ hc σ
  | succ n ih =>
    have hn := unit_comp_mulN_left A n
    have hs : (mulN A (n + 1)).left =
        pullback.lift (mulN A n).left (𝟙 A.left) (by simp) ≫ μ[A].left := by
      simp [mulN, pow_succ, Hom.mul_def]
    rw [pointedMap_of_eq k hs _ _ _ (by rw [← hs, h]),
      pointedMap_lift_comp_mul A.hom _ he μ[A].left hm₁ hm₂ _ _ _ hn (Category.comp_id _),
      ih hn, pointedMap_id _ _ hc, pow_succ]

end HSpace

open MonObj in
/-- XI.2.1, key step (Serre–Lang): every connected étale covering `f : Y ⟶ A` of an abelian
variety `A` over an algebraically closed field is dominated by multiplication by some `n > 0`:
there is `g : A ⟶ Y` with `f ∘ g = n_A`. We may take for `n` the degree of `f`. SGA's XI.2.1
itself, `π₁(A) ≅ lim_n K_n`, is `AbelianVarietyFundamentalGroupStatement` (in `TateModule`),
which builds on this. -/
theorem serreLangStatement : SerreLangStatement.{u} := by
  intro k _ _ A _ _ _ _ Y f _ _ hY
  have : IsReduced A.left := ExposeII.isReduced_of_smooth_of_isReduced A.hom
  let e : Spec (.of k) ⟶ A.left := η[A].left
  let F := ExposeV.FEt.fiber k e
  let Y' : ExposeV.FEt A.left := MorphismProperty.Over.mk ⊤ f ⟨inferInstance, inferInstance⟩
  have : ConnectedSpace Y'.left := hY
  have : IsConnected Y' := ExposeV.FEt.isConnected_of_connectedSpace Y'
  obtain ⟨y⟩ := nonempty_fiber_of_isConnected F Y'
  have := FiberFunctor.isPretransitive_of_isConnected F Y'
  have hc := mul_comm_of_monObj A
  refine ⟨Nat.card (F.obj Y'), Nat.card_pos, ?_⟩
  have h := unit_comp_mulN_left A (Nat.card (F.obj Y'))
  -- `n_A` acts on `π₁(A, e)` by `σ ↦ σⁿ`, which fixes the points of the fibre of `Y` at `e`.
  exact exists_lift_of_forall_smul_eq (mulN A (Nat.card (F.obj Y'))).left e e h Y' y
    fun σ ↦ by
      rw [pointedMap_mulN A _ h σ]
      exact pow_card_smul_eq hc y σ

end SGA.SGA1.ExposeXI
