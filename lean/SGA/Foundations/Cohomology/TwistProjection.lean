/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.TwistBaseChange
import SGA.Foundations.QuasiCoherent.Pullback
import SGA.Foundations.Cohomology.Statements

/-!
# Twists: projection formula, coherence, multiplication by sections

For a line bundle `L` given by a cocycle (`SGA.Foundations.Ample`):

* `LineBundle.twistPushforwardIso`: the projection formula
  `κ_*(G ⊗ (κ^* L)^{⊗n}) ≅ κ_* G ⊗ L^{⊗n}` for any morphism `κ` (EGA 0_I 5.4.10).
* `LineBundle.isCoherent_twist`: twists of coherent modules are coherent.
* `LineBundle.mulSection`: multiplication `M ⟶ M ⊗ L^{⊗m}` by a section `s` of `L^{⊗m}`, bijective
  on sections over opens contained in a trivializing open on which `s` does not vanish
  (`mulSection_app_bijective`, `isUnit_of_le_nonvanishingLocus`).
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.LineBundle

section ProjectionFormula

variable {X P : Scheme.{u}} (κ : X ⟶ P) (L : P.LineBundle) (G : X.Modules) (n : ℤ)

lemma app_map_trans_eq (V : P.Opens) (i j : L.ι) :
    κ.app (V ⊓ (L.U i ⊓ L.U j))
        (P.presheaf.map (homOfLE (inf_le_right : V ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j)).op
          (L.trans n i j)) =
      X.presheaf.map (homOfLE (inf_le_right :
        κ ⁻¹ᵁ V ⊓ (κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j) ≤ κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j)).op
        ((L.pullback κ).trans n i j) := by
  rw [trans_pullback, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
  rfl

lemma isTwistSection_pushforward_iff (V : P.Opens) (s : ∀ i, Γ(G, κ ⁻¹ᵁ V ⊓ κ ⁻¹ᵁ L.U i)) :
    (L.pullback κ).IsTwistSection G n (κ ⁻¹ᵁ V) s ↔
      L.IsTwistSection ((Scheme.Modules.pushforward κ).obj G) n V s := by
  have key : ∀ i j, @id Γ(X, κ ⁻¹ᵁ V ⊓ (κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j)) (κ.app (V ⊓ (L.U i ⊓ L.U j))
      (P.presheaf.map (homOfLE (inf_le_right : V ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j)).op
        (L.trans n i j))) =
      X.presheaf.map (homOfLE (inf_le_right :
        κ ⁻¹ᵁ V ⊓ (κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j) ≤ κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j)).op
        ((L.pullback κ).trans n i j) := fun i j ↦ app_map_trans_eq κ L n V i j
  constructor
  · intro h i j
    change @id Γ(G, κ ⁻¹ᵁ V ⊓ (κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j))
        (G.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          κ ⁻¹ᵁ V ⊓ (κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j) ≤ κ ⁻¹ᵁ V ⊓ κ ⁻¹ᵁ L.U i)).op (s i)) =
      @id Γ(X, κ ⁻¹ᵁ V ⊓ (κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j)) (κ.app (V ⊓ (L.U i ⊓ L.U j))
        (P.presheaf.map (homOfLE (inf_le_right : V ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j)).op
          (L.trans n i j))) •
      @id Γ(G, κ ⁻¹ᵁ V ⊓ (κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j))
        (G.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          κ ⁻¹ᵁ V ⊓ (κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j) ≤ κ ⁻¹ᵁ V ⊓ κ ⁻¹ᵁ L.U j)).op (s j))
    rw [key]
    exact h i j
  · intro h (i : L.ι) (j : L.ι)
    have hij := h i j
    change @id Γ(G, κ ⁻¹ᵁ V ⊓ (κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j))
        (G.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          κ ⁻¹ᵁ V ⊓ (κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j) ≤ κ ⁻¹ᵁ V ⊓ κ ⁻¹ᵁ L.U i)).op (s i)) =
      @id Γ(X, κ ⁻¹ᵁ V ⊓ (κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j)) (κ.app (V ⊓ (L.U i ⊓ L.U j))
        (P.presheaf.map (homOfLE (inf_le_right : V ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j)).op
          (L.trans n i j))) •
      @id Γ(G, κ ⁻¹ᵁ V ⊓ (κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j))
        (G.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          κ ⁻¹ᵁ V ⊓ (κ ⁻¹ᵁ L.U i ⊓ κ ⁻¹ᵁ L.U j) ≤ κ ⁻¹ᵁ V ⊓ κ ⁻¹ᵁ L.U j)).op (s j)) at hij
    rw [key] at hij
    exact hij

/-- Sections of `(κ^* L)^{⊗n} ⊗ G` over `κ⁻¹ V` are sections of `L^{⊗n} ⊗ κ_* G` over `V`. -/
noncomputable def twistPushforwardHom (V : P.Opens) :
    (L.pullback κ).twistAddSubgroup G n (κ ⁻¹ᵁ V) →+
      L.twistAddSubgroup ((Scheme.Modules.pushforward κ).obj G) n V where
  toFun s := ⟨fun i ↦ s.1 i, (isTwistSection_pushforward_iff κ L G n V _).mp s.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Sections of `L^{⊗n} ⊗ κ_* G` over `V` are sections of `(κ^* L)^{⊗n} ⊗ G` over `κ⁻¹ V`. -/
noncomputable def twistPushforwardInv (V : P.Opens) :
    L.twistAddSubgroup ((Scheme.Modules.pushforward κ).obj G) n V →+
      (L.pullback κ).twistAddSubgroup G n (κ ⁻¹ᵁ V) where
  toFun s := ⟨fun i ↦ s.1 i, (isTwistSection_pushforward_iff κ L G n V _).mpr s.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The projection formula on sections over an open of `P`, as a linear equivalence. -/
noncomputable def twistPushforwardLinearEquiv (V : P.Opensᵒᵖ) :
    ((Scheme.Modules.pushforward κ).obj ((L.pullback κ).twist G n)).val.obj V ≃ₗ[
      P.ringCatSheaf.obj.obj V] (L.twist ((Scheme.Modules.pushforward κ).obj G) n).val.obj V where
  toFun := L.twistPushforwardHom κ G n V.unop
  invFun := L.twistPushforwardInv κ G n V.unop
  map_add' := map_add _
  map_smul' r s := by
    let s' : (L.pullback κ).twistAddSubgroup G n (κ ⁻¹ᵁ V.unop) := s
    refine Subtype.ext (funext fun i ↦ ?_)
    change @id Γ(X, κ ⁻¹ᵁ V.unop ⊓ κ ⁻¹ᵁ L.U i) (X.presheaf.map (homOfLE (inf_le_left :
        κ ⁻¹ᵁ V.unop ⊓ κ ⁻¹ᵁ L.U i ≤ κ ⁻¹ᵁ V.unop)).op (κ.app V.unop r)) •
          @id Γ(G, κ ⁻¹ᵁ V.unop ⊓ κ ⁻¹ᵁ L.U i) (s'.1 i) =
      @id Γ(X, κ ⁻¹ᵁ V.unop ⊓ κ ⁻¹ᵁ L.U i) (κ.app (V.unop ⊓ L.U i)
        (P.presheaf.map (homOfLE (inf_le_left : V.unop ⊓ L.U i ≤ V.unop)).op r)) •
          @id Γ(G, κ ⁻¹ᵁ V.unop ⊓ κ ⁻¹ᵁ L.U i) (s'.1 i)
    congr 1
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, κ.naturality]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Projection formula for twists** (EGA 0_I 5.4.10): for a morphism `κ : X ⟶ P`, a line bundle
`L` on `P` and an `𝒪_X`-module `G`, `κ_*(G ⊗ (κ^* L)^{⊗n}) ≅ κ_* G ⊗ L^{⊗n}`. -/
noncomputable def twistPushforwardIso :
    (Scheme.Modules.pushforward κ).obj ((L.pullback κ).twist G n) ≅
      L.twist ((Scheme.Modules.pushforward κ).obj G) n :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    _root_.PresheafOfModules.isoMk
      (fun V ↦ (L.twistPushforwardLinearEquiv κ G n V).toModuleIso)
      (fun V V' f ↦ by
        ext s
        let s' : (L.pullback κ).twistAddSubgroup G n (κ ⁻¹ᵁ V.unop) := s
        change L.twistPushforwardHom κ G n V'.unop
            ((L.pullback κ).twistResHom G n (κ.preimage_mono f.unop.le) s') =
          L.twistResHom _ n f.unop.le (L.twistPushforwardHom κ G n V.unop s')
        rfl)

lemma twistPushforwardIso_hom_app (V : P.Opens) (s : Γ((L.pullback κ).twist G n, κ ⁻¹ᵁ V))
    (i : L.ι) :
    (((L.twistPushforwardIso κ G n).hom.app V s : L.twistAddSubgroup _ n V).1 i) =
      (s : (L.pullback κ).twistAddSubgroup G n (κ ⁻¹ᵁ V)).1 i :=
  rfl

end ProjectionFormula

section Coherent

variable {X : Scheme.{u}} (L : X.LineBundle) (M : X.Modules) (n : ℤ)

/-- The twist of a module of finite type by a line bundle is of finite type. -/
instance isFiniteType_twist [M.IsFiniteType] : (L.twist M n).IsFiniteType := by
  refine Scheme.Modules.isFiniteType_of_forall_pullback (fun k : L.ι ↦ (L.U k).ι)
    (fun x ↦ ?_) (fun k ↦ ?_)
  · have hx : x ∈ ⨆ k, L.U k := by rw [L.iSup_eq_top]; exact True.intro
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨k, by rw [Scheme.Opens.range_ι]; exact hk⟩
  · exact Scheme.Modules.isFiniteType_of_iso
      ((L.twistRestrictIso k le_rfl).symm ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback (L.U k).ι).app (L.twist M n))

/-- The twist of a coherent module by a line bundle is coherent. -/
instance isCoherent_twist [M.IsCoherent] : (L.twist M n).IsCoherent where
  isQuasicoherent := by
    have : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
    infer_instance
  isFiniteType := by
    have : M.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
    infer_instance

end Coherent

section MulSection

variable {X : Scheme.{u}} (L : X.LineBundle) (M : X.Modules) {m : ℕ} (s : L.sections m)

lemma trans_natCast (i j : L.ι) : L.trans (m : ℤ) i j = ((L.g i j : Γ(X, _)) ^ m) := by
  rw [trans, zpow_natCast, Units.val_pow_eq_pow_val]

lemma sections_res (V : X.Opens) (i j : L.ι) :
    X.presheaf.map (homOfLE (inf_le_right.trans inf_le_left :
        V ⊓ (L.U i ⊓ L.U j) ≤ L.U i)).op (s.1 i) =
      X.presheaf.map (homOfLE (inf_le_right : V ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j)).op
          (L.trans m i j) *
        X.presheaf.map (homOfLE (inf_le_right.trans inf_le_right :
          V ⊓ (L.U i ⊓ L.U j) ≤ L.U j)).op (s.1 j) := by
  obtain ⟨sv, hs⟩ := s
  have h := congrArg (X.presheaf.map (homOfLE (inf_le_right :
    V ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j)).op) (hs i j)
  rw [map_mul, CohomologyAux.presheaf_map_map, CohomologyAux.presheaf_map_map] at h
  rw [trans_natCast]
  exact h

/-- Multiplication by a section `s` of `L^{⊗m}`: sections of `M` over `V`. -/
noncomputable def mulSectionAddHom (V : X.Opens) : Γ(M, V) →+ L.twistAddSubgroup M m V where
  toFun t := ⟨fun i ↦ X.presheaf.map (homOfLE (inf_le_right : V ⊓ L.U i ≤ L.U i)).op (s.1 i) •
      M.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op t, fun i j ↦ by
    simp only [Scheme.Modules.map_smul, TopCat.Presheaf.map_map_apply,
      CohomologyAux.presheaf_map_map, smul_smul]
    congr 1
    exact sections_res L s V i j⟩
  map_zero' := by ext i; simp
  map_add' t t' := by ext i; simp [smul_add]

lemma mulSectionAddHom_apply (V : X.Opens) (t : Γ(M, V)) (i : L.ι) :
    (L.mulSectionAddHom M s V t).1 i =
      X.presheaf.map (homOfLE (inf_le_right : V ⊓ L.U i ≤ L.U i)).op (s.1 i) •
        M.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op t :=
  rfl

/-- **Multiplication by a section** `s ∈ Γ(X, L^{⊗m})`, as a morphism `M ⟶ M ⊗ L^{⊗m}`. -/
noncomputable def mulSection : M ⟶ L.twist M m :=
  ⟨_root_.PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom (L.mulSectionAddHom M s V.unop)
      naturality V V' f := by
        ext t
        refine Subtype.ext (funext fun i ↦ ?_)
        change X.presheaf.map _ (s.1 i) • M.presheaf.map _ (M.presheaf.map f t) =
          M.presheaf.map _ (X.presheaf.map _ (s.1 i) • M.presheaf.map _ t)
        erw [Scheme.Modules.map_smul, CohomologyAux.presheaf_map_map]
        congr 1
        exact LineBundle.presheaf_map_map_eq M.presheaf _ _ _ _ t }
    fun V r t ↦ Subtype.ext (funext fun i ↦ by
      change X.presheaf.map _ (s.1 i) • M.presheaf.map _ (r • t) =
        X.presheaf.map _ r • (X.presheaf.map _ (s.1 i) • M.presheaf.map _ t)
      erw [Scheme.Modules.map_smul]
      exact smul_comm _ _ _)⟩

lemma mulSection_app_apply (V : X.Opens) (t : Γ(M, V)) (i : L.ι) :
    ((L.mulSection M s).app V t : L.twistAddSubgroup M m V).1 i =
      X.presheaf.map (homOfLE (inf_le_right : V ⊓ L.U i ≤ L.U i)).op (s.1 i) •
        M.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op t :=
  rfl

lemma twistToModule_mulSection (k : L.ι) {V : X.Opens} (hV : V ≤ L.U k) (t : Γ(M, V)) :
    L.twistToModule k hV ((L.mulSection M s).app V t) =
      X.presheaf.map (homOfLE hV).op (s.1 k) • t := by
  change M.presheaf.map (homOfLE (le_inf le_rfl hV)).op
    (X.presheaf.map (homOfLE (inf_le_right : V ⊓ L.U k ≤ L.U k)).op (s.1 k) •
      M.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U k ≤ V)).op t) = _
  rw [Scheme.Modules.map_smul, TopCat.Presheaf.map_map_apply, CohomologyAux.presheaf_map_map,
    CohomologyAux.modules_map_self]

/-- Multiplication by `s` is bijective on sections over `V ⊆ Uₖ` on which `sₖ` is invertible. -/
lemma mulSection_app_bijective (k : L.ι) {V : X.Opens} (hV : V ≤ L.U k)
    (hu : IsUnit (X.presheaf.map (homOfLE hV).op (s.1 k))) :
    Function.Bijective ((L.mulSection M s).app V) := by
  have h : ⇑((L.mulSection M s).app V) =
      ⇑(L.twistEquiv (M := M) (n := m) k hV).symm ∘
        (fun t : Γ(M, V) ↦ X.presheaf.map (homOfLE hV).op (s.1 k) • t) := by
    ext t
    apply (L.twistEquiv (M := M) (n := m) k hV).injective
    rw [Function.comp_apply, LinearEquiv.apply_symm_apply]
    exact L.twistToModule_mulSection M s k hV t
  rw [h]
  refine (L.twistEquiv (M := M) (n := m) k hV).symm.bijective.comp ?_
  obtain ⟨u, hu⟩ := hu
  refine Function.bijective_iff_has_inverse.mpr ⟨fun t ↦ (↑u⁻¹ : Γ(X, V)) • t, fun t ↦ ?_,
    fun t ↦ ?_⟩
  · simp only [← hu, smul_smul, Units.inv_mul, one_smul]
  · simp only [← hu, smul_smul, Units.mul_inv, one_smul]

/-- On the non-vanishing locus of `s`, its components are invertible. -/
lemma isUnit_of_le_nonvanishingLocus (k : L.ι) {V : X.Opens} (hV : V ≤ L.U k)
    (hV' : V ≤ L.nonvanishingLocus s) : IsUnit (X.presheaf.map (homOfLE hV).op (s.1 k)) := by
  have hle : V ≤ X.basicOpen (s.1 k) := by
    intro x hx
    obtain ⟨j, hj⟩ := (L.mem_nonvanishingLocus s).mp (hV' hx)
    have hxj : x ∈ L.U j := X.basicOpen_le _ hj
    have h := congrArg X.basicOpen (s.2 k j)
    rw [Scheme.basicOpen_res, Scheme.basicOpen_mul, Scheme.basicOpen_res,
      Scheme.basicOpen_of_isUnit _ ((L.g k j).isUnit.pow m)] at h
    have : x ∈ (L.U k ⊓ L.U j) ⊓ ((L.U k ⊓ L.U j) ⊓ X.basicOpen (s.1 j)) :=
      ⟨⟨hV hx, hxj⟩, ⟨hV hx, hxj⟩, hj⟩
    rw [← h] at this
    exact this.2
  have h1 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le (s.1 k))).op (s.1 k)) :=
    X.toRingedSpace.isUnit_res_basicOpen (s.1 k)
  have h2 := h1.map (X.presheaf.map (homOfLE hle).op).hom
  rw [CohomologyAux.presheaf_map_map] at h2
  exact h2

end MulSection

end AlgebraicGeometry.Scheme.LineBundle
