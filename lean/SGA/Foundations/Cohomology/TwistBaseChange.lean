/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.Twist
import SGA.Foundations.Projective.LineBundle

/-!
# Twists under restriction and change of cocycle data

* `Scheme.LineBundle.twistRestrictPullbackIso`: for an open immersion `g : Y ⟶ X`,
  `(M ⊗ L^{⊗n})|_Y ≅ M|_Y ⊗ (g^* L)^{⊗n}` (EGA 0_I 5.4.8).
* `Scheme.LineBundle.twistTransferIso`: two line bundles given by the same trivializing opens and
  transition functions, up to reindexing, give isomorphic twists.
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.LineBundle

variable {X Y : Scheme.{u}} (L : X.LineBundle) (M : X.Modules) (n : ℤ)

lemma presheaf_map_map_eq {T : TopCat.{u}} (P : TopCat.Presheaf AddCommGrpCat.{u} T)
    {U₁ U₂ U₃ U₂' : (TopologicalSpace.Opens T)ᵒᵖ} (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) (c : U₁ ⟶ U₂')
    (d : U₂' ⟶ U₃)
    (s : P.obj U₁) : P.map b (P.map a s) = P.map d (P.map c s) := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← ConcreteCategory.comp_apply, ← P.map_comp,
    Subsingleton.elim (a ≫ b) (c ≫ d)]

section OpenImmersion

variable (g : Y ⟶ X) [IsOpenImmersion g]

omit [IsOpenImmersion g] in
lemma image_inf_preimage [IsOpenImmersion g] (W : Y.Opens) (U : X.Opens) :
    g ''ᵁ (W ⊓ g ⁻¹ᵁ U) = g ''ᵁ W ⊓ U := by
  ext x
  change x ∈ g.base '' (W ∩ g.base ⁻¹' U) ↔ x ∈ g.base '' W ∩ U
  rw [Set.image_inter_preimage]

omit [IsOpenImmersion g] in
lemma trans_pullback (i j : L.ι) :
    (L.pullback g).trans n i j =
      g.appLE (L.U i ⊓ L.U j) (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j) g.preimage_inf.ge (L.trans n i j) := by
  have h := congrArg Units.val (map_zpow (Units.map
    (g.appLE (L.U i ⊓ L.U j) (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j) g.preimage_inf.ge).hom.toMonoidHom)
    (L.g i j) n)
  exact h.symm

/-- Restriction of `x ∈ Γ(X, U)` to `g(V)` through `g`. -/
lemma appIso_inv_appLE_apply {U : X.Opens} {V : Y.Opens} (e : V ≤ g ⁻¹ᵁ U) (x : Γ(X, U)) :
    (g.appIso V).inv (g.appLE U V e x) =
      X.presheaf.map (homOfLE ((g.image_mono e).trans
        (g.image_preimage_eq_opensRange_inf U ▸ inf_le_right))).op x :=
  Scheme.Hom.appLE_appIso_inv_apply g e x

lemma appIso_inv_map_trans_pullback (W : Y.Opens) (i j : L.ι)
    (hij : g ''ᵁ (W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j)) ≤ g ''ᵁ W ⊓ (L.U i ⊓ L.U j)) :
    (g.appIso (W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j))).inv
        (Y.presheaf.map (homOfLE (inf_le_right :
          W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j) ≤ g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j)).op
          ((L.pullback g).trans n i j)) =
      X.presheaf.map (homOfLE (hij.trans inf_le_right)).op (L.trans n i j) := by
  rw [trans_pullback, ← ConcreteCategory.comp_apply (g.appLE _ _ _), Scheme.Hom.appLE_map,
    appIso_inv_appLE_apply]

/-- A section of `M ⊗ L^{⊗n}` over `g(W)` gives a section of `M|_Y ⊗ (g^* L)^{⊗n}` over `W`. -/
noncomputable def twistPullbackHom (W : Y.Opens) :
    L.twistAddSubgroup M n (g ''ᵁ W) →+ (L.pullback g).twistAddSubgroup (M.restrict g) n W where
  toFun s := ⟨fun i ↦ M.presheaf.map (homOfLE (image_inf_preimage g W (L.U i)).le).op (s.1 i),
    fun i j ↦ by
      have hij : g ''ᵁ (W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j)) ≤ g ''ᵁ W ⊓ (L.U i ⊓ L.U j) :=
        (image_inf_preimage g W (L.U i ⊓ L.U j)).le
      have hs := congrArg (M.presheaf.map (homOfLE hij).op) (s.2 i j)
      rw [Scheme.Modules.map_smul, TopCat.Presheaf.map_map_apply, TopCat.Presheaf.map_map_apply,
        CohomologyAux.presheaf_map_map] at hs
      change M.presheaf.map (homOfLE (g.image_mono (le_inf inf_le_left
          (inf_le_right.trans inf_le_left) :
            W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j) ≤ W ⊓ g ⁻¹ᵁ L.U i))).op
          (M.presheaf.map (homOfLE (image_inf_preimage g W (L.U i)).le).op (s.1 i)) =
        (g.appIso (W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j))).inv
          (Y.presheaf.map (homOfLE (inf_le_right :
            W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j) ≤ g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j)).op
            ((L.pullback g).trans n i j)) •
          M.presheaf.map (homOfLE (g.image_mono (le_inf inf_le_left
            (inf_le_right.trans inf_le_right) :
              W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j) ≤ W ⊓ g ⁻¹ᵁ L.U j))).op
            (M.presheaf.map (homOfLE (image_inf_preimage g W (L.U j)).le).op (s.1 j))
      have hscal : (g.appIso (W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j))).inv
          (Y.presheaf.map (homOfLE (inf_le_right :
            W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j) ≤ g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j)).op
            ((L.pullback g).trans n i j)) =
          X.presheaf.map (homOfLE (hij.trans inf_le_right)).op (L.trans n i j) := by
        exact appIso_inv_map_trans_pullback L n g W i j hij
      rw [TopCat.Presheaf.map_map_apply, TopCat.Presheaf.map_map_apply, hscal]
      exact hs⟩
  map_zero' := by ext i; exact map_zero _
  map_add' s t := by ext i; exact map_add _ _ _

/-- A section of `M|_Y ⊗ (g^* L)^{⊗n}` over `W` gives a section of `M ⊗ L^{⊗n}` over `g(W)`. -/
noncomputable def twistPullbackInv (W : Y.Opens) :
    (L.pullback g).twistAddSubgroup (M.restrict g) n W →+ L.twistAddSubgroup M n (g ''ᵁ W) where
  toFun t := ⟨fun i ↦ M.presheaf.map (homOfLE (image_inf_preimage g W (L.U i)).ge).op
      (@id Γ(M, g ''ᵁ (W ⊓ g ⁻¹ᵁ L.U i)) (t.1 i)),
    fun i j ↦ by
      have hij : g ''ᵁ (W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j)) ≤ g ''ᵁ W ⊓ (L.U i ⊓ L.U j) :=
        (image_inf_preimage g W (L.U i ⊓ L.U j)).le
      have hij' : g ''ᵁ W ⊓ (L.U i ⊓ L.U j) ≤ g ''ᵁ (W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j)) :=
        (image_inf_preimage g W (L.U i ⊓ L.U j)).ge
      have ht := t.2 i j
      change M.presheaf.map (homOfLE (g.image_mono (le_inf inf_le_left
          (inf_le_right.trans inf_le_left) :
            W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j) ≤ W ⊓ g ⁻¹ᵁ L.U i))).op
          (@id Γ(M, g ''ᵁ (W ⊓ g ⁻¹ᵁ L.U i)) (t.1 i)) =
        (g.appIso (W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j))).inv
          (Y.presheaf.map (homOfLE (inf_le_right :
            W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j) ≤ g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j)).op
            ((L.pullback g).trans n i j)) •
          M.presheaf.map (homOfLE (g.image_mono (le_inf inf_le_left
            (inf_le_right.trans inf_le_right) :
              W ⊓ (g ⁻¹ᵁ L.U i ⊓ g ⁻¹ᵁ L.U j) ≤ W ⊓ g ⁻¹ᵁ L.U j))).op
            (@id Γ(M, g ''ᵁ (W ⊓ g ⁻¹ᵁ L.U j)) (t.1 j)) at ht
      rw [appIso_inv_map_trans_pullback L n g W i j hij] at ht
      have ht' := congrArg (M.presheaf.map (homOfLE hij').op) ht
      rw [Scheme.Modules.map_smul, TopCat.Presheaf.map_map_apply, TopCat.Presheaf.map_map_apply,
        CohomologyAux.presheaf_map_map] at ht'
      change M.presheaf.map _ (M.presheaf.map _ (@id Γ(M, g ''ᵁ (W ⊓ g ⁻¹ᵁ L.U i)) (t.1 i))) =
        _ • M.presheaf.map _ (M.presheaf.map _ (@id Γ(M, g ''ᵁ (W ⊓ g ⁻¹ᵁ L.U j)) (t.1 j)))
      rw [TopCat.Presheaf.map_map_apply, TopCat.Presheaf.map_map_apply]
      exact ht'⟩
  map_zero' := by ext i; exact map_zero _
  map_add' s t := by ext i; exact map_add _ _ _

lemma twistPullbackInv_hom (W : Y.Opens) (s : L.twistAddSubgroup M n (g ''ᵁ W)) :
    L.twistPullbackInv M n g W (L.twistPullbackHom M n g W s) = s := by
  ext i
  change M.presheaf.map _ (M.presheaf.map _ (s.1 i)) = s.1 i
  rw [TopCat.Presheaf.map_map_apply, CohomologyAux.modules_map_self]

lemma twistPullbackHom_inv (W : Y.Opens) (t : (L.pullback g).twistAddSubgroup (M.restrict g) n W) :
    L.twistPullbackHom M n g W (L.twistPullbackInv M n g W t) = t := by
  ext i
  change M.presheaf.map _ (M.presheaf.map _ (@id Γ(M, g ''ᵁ (W ⊓ g ⁻¹ᵁ L.U i)) (t.1 i))) =
    @id Γ(M, g ''ᵁ (W ⊓ g ⁻¹ᵁ L.U i)) (t.1 i)
  rw [TopCat.Presheaf.map_map_apply, CohomologyAux.modules_map_self]

set_option backward.isDefEq.respectTransparency false in
/-- The twist-pullback comparison on sections over an open of `Y`, as a linear equivalence. -/
noncomputable def twistPullbackLinearEquiv (W : Y.Opensᵒᵖ) :
    ((L.twist M n).restrict g).val.obj W ≃ₗ[Y.ringCatSheaf.obj.obj W]
      ((L.pullback g).twist (M.restrict g) n).val.obj W where
  toFun := L.twistPullbackHom M n g W.unop
  invFun := L.twistPullbackInv M n g W.unop
  map_add' := map_add _
  map_smul' r s := by
    let s' : L.twistAddSubgroup M n (g ''ᵁ W.unop) := s
    refine Subtype.ext (funext fun i ↦ ?_)
    change M.presheaf.map (homOfLE (image_inf_preimage g W.unop (L.U i)).le).op
        (X.presheaf.map (homOfLE (inf_le_left : g ''ᵁ W.unop ⊓ L.U i ≤ g ''ᵁ W.unop)).op
          ((g.appIso W.unop).inv r) • s'.1 i) =
      (g.appIso (W.unop ⊓ g ⁻¹ᵁ L.U i)).inv
        (Y.presheaf.map (homOfLE (inf_le_left : W.unop ⊓ g ⁻¹ᵁ L.U i ≤ W.unop)).op r) •
        M.presheaf.map (homOfLE (image_inf_preimage g W.unop (L.U i)).le).op (s'.1 i)
    rw [Scheme.Modules.map_smul, CohomologyAux.presheaf_map_map]
    congr 1
    have h := congrArg (fun φ ↦ (ConcreteCategory.hom φ) r) (g.appIso_inv_naturality
      (homOfLE (inf_le_left : W.unop ⊓ g ⁻¹ᵁ L.U i ≤ W.unop)).op)
    simp only [ConcreteCategory.comp_apply] at h
    rw [h]
    rfl
  left_inv s := L.twistPullbackInv_hom M n g W.unop s
  right_inv t := L.twistPullbackHom_inv M n g W.unop t

/-- **Twisting commutes with restriction to open subschemes**: for an open immersion `g : Y ⟶ X`,
`(M ⊗ L^{⊗n})|_Y ≅ M|_Y ⊗ (g^* L)^{⊗n}`. -/
noncomputable def twistRestrictPullbackIso :
    (L.twist M n).restrict g ≅ (L.pullback g).twist (M.restrict g) n :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    _root_.PresheafOfModules.isoMk
      (fun W ↦ (L.twistPullbackLinearEquiv M n g W).toModuleIso)
      (fun W W' f ↦ by
        ext s
        let s' : L.twistAddSubgroup M n (g ''ᵁ W.unop) := s
        change L.twistPullbackHom M n g W'.unop
            (L.twistResHom M n (g.opensFunctor.map f.unop).le s') =
          (L.pullback g).twistResHom (M.restrict g) n f.unop.le
            (L.twistPullbackHom M n g W.unop s')
        refine Subtype.ext (funext fun i ↦ ?_)
        exact presheaf_map_map_eq M.presheaf _ _ _ _ _)

end OpenImmersion

end AlgebraicGeometry.Scheme.LineBundle

namespace AlgebraicGeometry.Scheme.LineBundle

variable {X : Scheme.{u}} (M : X.Modules) (n : ℤ)

section Transfer

variable (L L' : X.LineBundle) (e : L.ι ≃ L'.ι) (hU : ∀ i, L'.U (e i) = L.U i)
  (hg : ∀ i j, X.presheaf.map (homOfLE (le_of_eq (by rw [hU, hU]) :
    L.U i ⊓ L.U j ≤ L'.U (e i) ⊓ L'.U (e j))).op (L'.g (e i) (e j) : Γ(X, _)) =
      (L.g i j : Γ(X, _)))

include hg in
lemma trans_transfer (i j : L.ι) :
    X.presheaf.map (homOfLE (le_of_eq (by rw [hU, hU]) :
      L.U i ⊓ L.U j ≤ L'.U (e i) ⊓ L'.U (e j))).op (L'.trans n (e i) (e j)) = L.trans n i j := by
  have hu : unitsRes (le_of_eq (by rw [hU, hU]) : L.U i ⊓ L.U j ≤ L'.U (e i) ⊓ L'.U (e j))
      (L'.g (e i) (e j)) = L.g i j := Units.ext (hg i j)
  simp only [trans, ← coe_unitsRes, map_zpow, hu]

/-- Restriction of a section of `M ⊗ L'^{⊗n}` to a section of `M ⊗ L^{⊗n}`. -/
noncomputable def twistTransferHom (V : X.Opens) :
    L'.twistAddSubgroup M n V →+ L.twistAddSubgroup M n V where
  toFun s := ⟨fun i ↦ M.presheaf.map (homOfLE (inf_le_inf_left V (hU i).ge)).op (s.1 (e i)),
    fun i j ↦ by
      have h := congrArg (M.presheaf.map (homOfLE (inf_le_inf_left V
        (le_of_eq (by rw [hU, hU]) : L.U i ⊓ L.U j ≤ L'.U (e i) ⊓ L'.U (e j)))).op)
        (s.2 (e i) (e j))
      rw [Scheme.Modules.map_smul, TopCat.Presheaf.map_map_apply,
        TopCat.Presheaf.map_map_apply, CohomologyAux.presheaf_map_map] at h
      rw [TopCat.Presheaf.map_map_apply, TopCat.Presheaf.map_map_apply,
        ← trans_transfer n L L' e hU hg i j, CohomologyAux.presheaf_map_map]
      exact h⟩
  map_zero' := by ext i; exact map_zero _
  map_add' s t := by ext i; exact map_add _ _ _

omit hg in
lemma g_congr (L : X.LineBundle) {i i' j j' : L.ι} (hi : i = i') (hj : j = j') {W : X.Opens}
    (h : W ≤ L.U i ⊓ L.U j) (h' : W ≤ L.U i' ⊓ L.U j') :
    X.presheaf.map (homOfLE h).op (L.g i j : Γ(X, _)) =
      X.presheaf.map (homOfLE h').op (L.g i' j' : Γ(X, _)) := by
  subst hi; subst hj; rfl

omit hg in
lemma family_congr (L : X.LineBundle) {V : X.Opens} (s : ∀ i, Γ(M, V ⊓ L.U i)) {i i' : L.ι}
    (h : i = i') {W : X.Opens} (hw : W ≤ V ⊓ L.U i) (hw' : W ≤ V ⊓ L.U i') :
    M.presheaf.map (homOfLE hw).op (s i) = M.presheaf.map (homOfLE hw').op (s i') := by
  subst h; rfl

omit hg in
include hU in
lemma transfer_hU_symm (k : L'.ι) : L.U (e.symm k) = L'.U k :=
  (hU (e.symm k)).symm.trans (by rw [e.apply_symm_apply])

include hg in
lemma transfer_hg_symm (k l : L'.ι) :
    X.presheaf.map (homOfLE (le_of_eq (by rw [transfer_hU_symm L L' e hU,
      transfer_hU_symm L L' e hU]) :
      L'.U k ⊓ L'.U l ≤ L.U (e.symm k) ⊓ L.U (e.symm l))).op
        (L.g (e.symm k) (e.symm l) : Γ(X, _)) = (L'.g k l : Γ(X, _)) := by
  rw [← hg (e.symm k) (e.symm l), CohomologyAux.presheaf_map_map,
    g_congr L' (e.apply_symm_apply k) (e.apply_symm_apply l) _ le_rfl,
    CohomologyAux.presheaf_map_self]

/-- The inverse restriction. -/
noncomputable def twistTransferInv (V : X.Opens) :
    L.twistAddSubgroup M n V →+ L'.twistAddSubgroup M n V :=
  twistTransferHom M n L' L e.symm (transfer_hU_symm L L' e hU)
    (transfer_hg_symm L L' e hU hg) V

include hg in
lemma twistTransferHom_inv (V : X.Opens) (t : L.twistAddSubgroup M n V) :
    twistTransferHom M n L L' e hU hg V (twistTransferInv M n L L' e hU hg V t) = t := by
  ext i
  change M.presheaf.map _ (M.presheaf.map _ (t.1 (e.symm (e i)))) = t.1 i
  rw [TopCat.Presheaf.map_map_apply, family_congr M L t.1 (e.symm_apply_apply i) _ le_rfl,
    CohomologyAux.modules_map_self]

include hg in
lemma twistTransferInv_hom (V : X.Opens) (s : L'.twistAddSubgroup M n V) :
    twistTransferInv M n L L' e hU hg V (twistTransferHom M n L L' e hU hg V s) = s := by
  ext k
  change M.presheaf.map _ (M.presheaf.map _ (s.1 (e (e.symm k)))) = s.1 k
  rw [TopCat.Presheaf.map_map_apply, family_congr M L' s.1 (e.apply_symm_apply k) _ le_rfl,
    CohomologyAux.modules_map_self]

set_option backward.isDefEq.respectTransparency false in
/-- **Twists by line bundles with the same cocycle data are isomorphic**. -/
noncomputable def twistTransferIso : L'.twist M n ≅ L.twist M n :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    _root_.PresheafOfModules.isoMk
      (fun V ↦ LinearEquiv.toModuleIso
        { toFun := twistTransferHom M n L L' e hU hg V.unop
          invFun := twistTransferInv M n L L' e hU hg V.unop
          map_add' := map_add _
          map_smul' := fun r s ↦ by
            let s' : L'.twistAddSubgroup M n V.unop := s
            refine Subtype.ext (funext fun i ↦ ?_)
            change M.presheaf.map _ (X.presheaf.map _ r • s'.1 (e i)) =
              X.presheaf.map _ r • M.presheaf.map _ (s'.1 (e i))
            rw [Scheme.Modules.map_smul, CohomologyAux.presheaf_map_map]
          left_inv := twistTransferInv_hom M n L L' e hU hg V.unop
          right_inv := twistTransferHom_inv M n L L' e hU hg V.unop })
      (fun V V' f ↦ by
        ext s
        let s' : L'.twistAddSubgroup M n V.unop := s
        refine Subtype.ext (funext fun i ↦ ?_)
        change M.presheaf.map _ (M.presheaf.map _ (s'.1 (e i))) =
          M.presheaf.map _ (M.presheaf.map _ (s'.1 (e i)))
        exact presheaf_map_map_eq M.presheaf _ _ _ _ _)

end Transfer

end AlgebraicGeometry.Scheme.LineBundle
