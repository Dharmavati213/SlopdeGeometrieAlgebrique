/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.AssociatedBundle

/-!
# SGA 1, Exposé XI.4: the associated bundle `E^(P)`

Let `G` be a group scheme over `S`, `P` a principal homogeneous bundle under `G` and `E` an
`S`-scheme on which `G` acts. SGA defines the associated bundle `E^(P) = (P ×_S E)/G`, locally
isomorphic to `E`, and shows by VIII.2.1 that it exists when `E` is affine over `S`. We describe
`E^(P)` by its functor of points: the `T`-points of `E^(P)` are the `G`-equivariant morphisms
`P_T ⟶ E_T` over `T` (`contractedPresheaf P E`); this is the sheaf `(P × E)/G` since `P` is a
torsor. It is an fpqc sheaf (`isSheaf_contractedPresheaf`).

* Over `P` (on which `P` has the diagonal section) it is represented by `E ×_S P`
  (`representsOver_contracted`): an equivariant map is determined by the image of the section.
* XI.4: if `G` is flat and quasi-compact and `E` affine over `S`, the associated bundle exists:
  `contractedPresheaf P E` is represented by an `S`-scheme `E^(P)` affine over `S`, with
  `E^(P) ×_S P ≅ E ×_S P` (`exists_associatedBundle`). The proof is SGA's: descend `E ×_S P`
  along the faithfully flat quasi-compact `P ⟶ S` (VIII.2.1, `RepresentsOver.descend`).
-/

universe u

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry MorphismProperty

namespace SGA.SGA1.ExposeXI

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] (P : Over S) [ModObj G P] (E : Over S)
  [ModObj G E]

/-- The presheaf `T ↦ Hom_S(T ×_S P, E)` of morphisms `P_T ⟶ E_T` over `T`. -/
noncomputable def homPresheaf : (Over S)ᵒᵖ ⥤ Type u where
  obj T := T.unop ⊗ P ⟶ E
  map f := ↾fun ψ ↦ (f.unop ▷ P) ≫ ψ
  map_id T := by ext ψ; simp
  map_comp f g := by ext ψ; simp

@[simp]
lemma homPresheaf_map {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (ψ : T.unop ⊗ P ⟶ E) :
    (homPresheaf P E).map f ψ = (f.unop ▷ P) ≫ ψ :=
  rfl

/-- `T ↦ Hom_S(T ×_S P, E)` is an fpqc sheaf. -/
theorem isSheaf_homPresheaf : Presieve.IsSheaf (fpqc S) (homPresheaf P E) := by
  have hE : Presieve.IsSheaf (fpqc S) (yoneda.obj E) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  intro T R hR x hx
  rw [Presieve.compatible_iff_sieveCompatible] at hx
  obtain ⟨X, hX⟩ : ∃ X : ∀ ⦃V : Over S⦄ (f : V ⟶ T), R f → (V ⊗ P ⟶ E), X = x :=
    ⟨fun V f hf ↦ x f hf, rfl⟩
  subst hX
  have hx' : ∀ ⦃V : Over S⦄ (f : V ⟶ T) (hf : R f) ⦃W : Over S⦄ (k : W ⟶ V),
      X (k ≫ f) (R.downward_closed hf k) = (k ▷ P) ≫ X f hf := fun V f hf W k ↦ hx f k hf
  have hxc : ∀ ⦃V : Over S⦄ {f f' : V ⟶ T} (e : f = f') (hf : R f) (hf' : R f'),
      X f hf = X f' hf' := by
    intro V f f' e hf hf'
    subst e
    rfl
  let R' : Sieve (T ⊗ P) := R.pullback (fst T P)
  have hR' : R' ∈ fpqc S (T ⊗ P) := (fpqc S).pullback_stable _ hR
  let y : Presieve.FamilyOfElements (yoneda.obj E) R'.arrows :=
    fun W h hh ↦ lift (𝟙 W) (h ≫ snd T P) ≫ X (h ≫ fst T P) hh
  have hy : y.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro W W' h k hh
    have hkh : R ((k ≫ h) ≫ fst T P) := R'.downward_closed hh k
    change lift (𝟙 W') ((k ≫ h) ≫ snd T P) ≫ X ((k ≫ h) ≫ fst T P) hkh =
      k ≫ lift (𝟙 W) (h ≫ snd T P) ≫ X (h ≫ fst T P) hh
    rw [hxc (Category.assoc k h (fst T P)) hkh (R.downward_closed hh k), hx' (h ≫ fst T P) hh k,
      ← Category.assoc, ← Category.assoc]
    congr 1
    exact CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)
  obtain ⟨ψ₁, hψ, -⟩ := hE R' hR' y hy
  obtain ⟨ψ, hψ₁⟩ : ∃ ψ : T ⊗ P ⟶ E, ψ = ψ₁ := ⟨ψ₁, rfl⟩
  subst hψ₁
  have key : ∀ ⦃V : Over S⦄ (f : V ⟶ T) (hf : R f), (f ▷ P) ≫ ψ = X f hf := by
    intro V f hf
    have h₁ : R' (f ▷ P) := by
      change R ((f ▷ P) ≫ fst T P)
      rw [whiskerRight_fst]
      exact R.downward_closed hf _
    refine (hψ (f ▷ P) h₁).trans ?_
    have h₁' : R ((f ▷ P) ≫ fst T P) := h₁
    change lift (𝟙 _) ((f ▷ P) ≫ snd T P) ≫ X ((f ▷ P) ≫ fst T P) h₁' = _
    rw [hxc (whiskerRight_fst f P) h₁' (R.downward_closed hf _), hx' f hf (fst V P),
      ← Category.assoc]
    convert Category.id_comp (X f hf)
    exact CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)
  refine ⟨ψ, fun V f hf ↦ key f hf, fun ψ₀ hψ' ↦ ?_⟩
  obtain ⟨ψ', hψ₀⟩ : ∃ ψ' : T ⊗ P ⟶ E, ψ' = ψ₀ := ⟨ψ₀, rfl⟩
  subst hψ₀
  refine (hE R' hR').isSeparatedFor.ext fun W h hh ↦ ?_
  change h ≫ ψ' = h ≫ ψ
  have e : h = lift (𝟙 W) (h ≫ snd T P) ≫ ((h ≫ fst T P) ▷ P) :=
    CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)
  rw [e, Category.assoc, Category.assoc, key _ hh]
  congr 1
  exact hψ' _ hh

/-- A morphism `ψ : T ×_S P ⟶ E` is `G`-equivariant: `ψ(t, g p) = g ψ(t, p)`. -/
def IsEquivariantMap {T : Over S} (ψ : T ⊗ P ⟶ E) : Prop :=
  ∀ ⦃Z : Over S⦄ (t : Z ⟶ T) (g : Z ⟶ G) (p : Z ⟶ P), lift t (g • p) ≫ ψ = g • (lift t p ≫ ψ)

/-- The equivariant morphisms `P_T ⟶ E_T` over `T`, as a subfunctor of `Hom_S(- ×_S P, E)`. -/
noncomputable def contractedSubfunctor : Subfunctor (homPresheaf P E) where
  obj T := {ψ | IsEquivariantMap G P E ψ}
  map {T T'} f ψ₀ hψ := fun Z t g p ↦ by
    obtain ⟨ψ, hψ₀⟩ : ∃ ψ : T.unop ⊗ P ⟶ E, ψ = ψ₀ := ⟨ψ₀, rfl⟩
    subst hψ₀
    change lift t (g • p) ≫ (f.unop ▷ P) ≫ ψ = g • (lift t p ≫ (f.unop ▷ P) ≫ ψ)
    rw [← Category.assoc, lift_whiskerRight, ← Category.assoc, lift_whiskerRight]
    exact hψ (t ≫ f.unop) g p

/-- XI.4: the associated bundle `E^(P) = (P ×_S E)/G`, described by its functor of points: the
`T`-points are the `G`-equivariant morphisms `P_T ⟶ E_T` over `T`. -/
noncomputable abbrev contractedPresheaf : (Over S)ᵒᵖ ⥤ Type u :=
  (contractedSubfunctor G P E).toFunctor

/-- `E^(P)` is an fpqc sheaf. -/
theorem isSheaf_contractedPresheaf : Presieve.IsSheaf (fpqc S) (contractedPresheaf G P E) := by
  have hE : Presieve.IsSheaf (fpqc S) (yoneda.obj E) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  rw [Subfunctor.isSheaf_iff _ (isSheaf_homPresheaf P E)]
  intro T ψ₀ hψ
  obtain ⟨ψ, hψ₀⟩ : ∃ ψ : T.unop ⊗ P ⟶ E, ψ = ψ₀ := ⟨ψ₀, rfl⟩
  subst hψ₀
  change IsEquivariantMap G P E ψ
  intro Z t g p
  refine (hE _ ((fpqc S).pullback_stable t hψ)).isSeparatedFor.ext fun W k hk ↦ ?_
  change k ≫ lift t (g • p) ≫ ψ = k ≫ (g • (lift t p ≫ ψ))
  have hk' : IsEquivariantMap G P E (((k ≫ t) ▷ P) ≫ ψ) := hk
  have e₁ : k ≫ lift t (g • p) = lift (𝟙 W) ((k ≫ g) • (k ≫ p)) ≫ ((k ≫ t) ▷ P) := by
    rw [lift_whiskerRight, comp_lift, ModObj.comp_smul, Category.id_comp]
  have e₂ : k ≫ lift t p = lift (𝟙 W) (k ≫ p) ≫ ((k ≫ t) ▷ P) := by
    rw [lift_whiskerRight, comp_lift, Category.id_comp]
  rw [← Category.assoc, e₁, Category.assoc, hk', ModObj.comp_smul, ← Category.assoc k, e₂,
    Category.assoc]

section Division

variable {G P} (hP : IsIso (ModObj.leftSMul G P))
include hP

/-- The division map `P ×_S P ⟶ G`, `(q, p) ↦ δ(q, p)` with `δ(q, p) p = q`, of a formally
principal homogeneous `P`. -/
noncomputable def divMap : P ⊗ P ⟶ G := inv (ModObj.leftSMul G P) ≫ fst G P

lemma divMap_smul {Z : Over S} (q p : Z ⟶ P) : (lift q p ≫ divMap hP) • p = q := by
  let m := lift q p ≫ inv (ModObj.leftSMul G P)
  have hm : m ≫ ModObj.leftSMul G P = lift q p := by simp [m]
  have hsnd : m ≫ snd G P = p := by
    rw [← ModObj.leftSMul_snd, ← Category.assoc, hm, lift_snd]
  have hfst : m ≫ γ[G, P] = q := by
    rw [← ModObj.leftSMul_fst, ← Category.assoc, hm, lift_fst]
  have : m = lift (m ≫ fst G P) (m ≫ snd G P) :=
    CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)
  change (m ≫ fst G P) • p = q
  rw [← hsnd, Hom.smul_def, ← this, hfst]

lemma divMap_eq {Z : Over S} (g : Z ⟶ G) (p : Z ⟶ P) : lift (g • p) p ≫ divMap hP = g := by
  rw [← ModObj.lift_leftSMul, divMap, Category.assoc, IsIso.hom_inv_id_assoc, lift_fst]

end Division

section Representation

variable {G P E} (hP : IsIso (ModObj.leftSMul G P))
include hP

/-- The universal equivariant map `(E ×_S P) ×_S P ⟶ E`, `((e, p₁), p) ↦ δ(p, p₁) e`. -/
noncomputable def universalContracted : (E ⊗ P) ⊗ P ⟶ E :=
  lift (lift (snd _ _) (fst _ _ ≫ snd E P) ≫ divMap hP) (fst _ _ ≫ fst E P) ≫ γ[G, E]

lemma lift_universalContracted {Z : Over S} (t : Z ⟶ E ⊗ P) (p : Z ⟶ P) :
    lift t p ≫ universalContracted hP = (lift p (t ≫ snd E P) ≫ divMap hP) • (t ≫ fst E P) := by
  rw [universalContracted, Hom.smul_def, ← Category.assoc, comp_lift, ← Category.assoc,
    comp_lift]
  simp

lemma divMap_smul_left {Z : Over S} (g : Z ⟶ G) (p q : Z ⟶ P) :
    lift (g • p) q ≫ divMap hP = g * (lift p q ≫ divMap hP) := by
  conv_lhs => rw [← divMap_smul hP p q, ← mul_smul]
  exact divMap_eq hP _ _

lemma isEquivariantMap_universalContracted : IsEquivariantMap G P E (universalContracted hP) := by
  intro Z t g p
  rw [lift_universalContracted, lift_universalContracted, divMap_smul_left, mul_smul]

/-- The universal equivariant map, as a section of `E^(P)` over `E ×_S P`. -/
noncomputable def universalSection : (contractedPresheaf G P E).obj (op (E ⊗ P)) :=
  ⟨universalContracted hP, isEquivariantMap_universalContracted hP⟩

/-- XI.4: over `P`, on which `P` has a section, the associated bundle is trivial: the equivariant
maps `P_T ⟶ E_T` over an `S`-scheme `T` with a morphism `t : T ⟶ P` correspond to the morphisms
`T ⟶ E`, i.e. `E^(P)` is represented over `P` by `E ×_S P`. -/
theorem representsOver_contracted :
    RepresentsOver (contractedPresheaf G P E) (snd E P) (universalSection hP) := by
  have hone : ∀ {Z : Over S} (t : Z ⟶ P), lift t t ≫ divMap hP = 1 := fun t ↦ by
    simpa using divMap_eq hP 1 t
  intro Z t
  constructor
  · rintro ⟨φ, hφ⟩ ⟨φ', hφ'⟩ e
    have e' : (φ ▷ P) ≫ universalContracted hP = (φ' ▷ P) ≫ universalContracted hP :=
      congrArg Subtype.val e
    have h₁ := congrArg (lift (𝟙 Z) t ≫ ·) e'
    simp only [← Category.assoc, lift_whiskerRight, Category.id_comp,
      lift_universalContracted, hφ, hφ', hone, one_smul] at h₁
    exact Subtype.ext (CartesianMonoidalCategory.hom_ext _ _ h₁ (hφ.trans hφ'.symm))
  · rintro ⟨ψ₀, hψ₀'⟩
    obtain ⟨ψ, hψ₀⟩ : ∃ ψ : Z ⊗ P ⟶ E, ψ = ψ₀ := ⟨ψ₀, rfl⟩
    subst hψ₀
    have hψ : IsEquivariantMap G P E ψ := hψ₀'
    let e := lift (𝟙 Z) t ≫ ψ
    refine ⟨⟨lift e t, lift_snd _ _⟩, Subtype.ext ?_⟩
    change ((lift e t) ▷ P) ≫ universalContracted hP = ψ
    rw [← Category.id_comp ((lift e t ▷ P) ≫ _), ← lift_fst_snd, ← Category.assoc,
      lift_whiskerRight, lift_universalContracted]
    simp only [Category.assoc, lift_snd, lift_fst]
    have h₁ : fst Z P ≫ e = lift (fst Z P) (fst Z P ≫ t) ≫ ψ := by
      rw [← Category.assoc, comp_lift, Category.comp_id]
    rw [h₁, ← hψ, divMap_smul, lift_fst_snd, Category.id_comp]

end Representation

set_option backward.isDefEq.respectTransparency.types false in
/-- XI.4: for `G` flat and quasi-compact over `S`, a principal homogeneous bundle `P` under `G`
and an `S`-scheme `E` affine over `S` with an action of `G`, the associated bundle
`E^(P) = (P ×_S E)/G` exists: the sheaf of equivariant maps `P_T ⟶ E_T` is represented by an
`S`-scheme affine over `S`, and `E^(P) ×_S P ≅ E ×_S P`. The proof is SGA's: `E ×_S P`
represents it over `P`, and descends along the faithfully flat quasi-compact `P ⟶ S` (VIII.2.1). -/
theorem exists_associatedBundle [Flat G.hom] [QuasiCompact G.hom] [IsAffineHom E.hom]
    (hP : IsPrincipalBundle G P) :
    ∃ X : Over S, IsAffineHom X.hom ∧ Nonempty ((contractedPresheaf G P E).RepresentableBy X) ∧
      Nonempty (pullback X.hom P.hom ≅ pullback E.hom P.hom) := by
  obtain ⟨hiso, hflat, hsurj, hqc⟩ := isPrincipalBundle_iff.1 hP
  have : IsAffineHom (snd E P).left := MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ ‹_›
  have : Surjective (toUnit P).left := hsurj
  have : Flat (toUnit P).left := hflat
  have : QuasiCompact (toUnit P).left := hqc
  obtain ⟨X, f, u, k, haff, hrep, hpb, -⟩ := RepresentsOver.descend
    (isSheaf_contractedPresheaf G P E) (toUnit P) (representsOver_contracted hiso)
  have hf : f.left = X.hom := by simpa using Over.w f
  refine ⟨X, hf ▸ haff, ⟨hrep.representableBy⟩, ⟨?_⟩⟩
  have hpb' : IsPullback k.left (snd E P).left X.hom P.hom := hf ▸ hpb
  exact hpb'.isoPullback.symm

end SGA.SGA1.ExposeXI
