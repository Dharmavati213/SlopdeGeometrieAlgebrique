/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.InvertibleSheaf
import SGA.Foundations.Cohomology.Helpers
import SGA.Foundations.Cohomology.Cech

/-!
# Twisting `𝒪_X`-modules by a line bundle

Let `L` be a line bundle on a scheme `X`, given (`SGA.Foundations.Ample`) by an open cover `(Uᵢ)`
and transition units `gᵢⱼ`, and `M` an `𝒪_X`-module. For `n : ℤ`, the sections of the twist
`M ⊗ L^{⊗n}` over an open `V` are the families `sᵢ ∈ Γ(V ∩ Uᵢ, M)` with `sᵢ = gᵢⱼⁿ sⱼ` on
`V ∩ Uᵢ ∩ Uⱼ` (EGA 0_I 5.4; for `X = Proj S` and `L = 𝒪(1)` this is Serre's `M(n)`, EGA II 2.5.14,
Hartshorne II.5). We construct the `𝒪_X`-module `L.twist M n`, identify its restriction to any
open contained in some `Uₖ` with the restriction of `M`, and deduce that the twist of a
quasi-coherent module is quasi-coherent.
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.LineBundle

variable {X : Scheme.{u}} (L : X.LineBundle) (M : X.Modules) (n : ℤ)

/-- The condition defining sections of `M ⊗ L^{⊗n}` over `V`. -/
def IsTwistSection (V : X.Opens) (s : ∀ i, Γ(M, V ⊓ L.U i)) : Prop :=
  ∀ i j, M.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
      V ⊓ (L.U i ⊓ L.U j) ≤ V ⊓ L.U i)).op (s i) =
    X.presheaf.map (homOfLE (inf_le_right : V ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j)).op
        (L.trans n i j) •
      M.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        V ⊓ (L.U i ⊓ L.U j) ≤ V ⊓ L.U j)).op (s j)

/-- The group of sections of `M ⊗ L^{⊗n}` over `V`. -/
def twistAddSubgroup (V : X.Opens) : AddSubgroup (∀ i, Γ(M, V ⊓ L.U i)) where
  carrier := {s | L.IsTwistSection M n V s}
  add_mem' {s t} hs ht i j := by
    simp only [Pi.add_apply, map_add, hs i j, ht i j, smul_add]
  zero_mem' i j := by simp
  neg_mem' {s} hs i j := by simp [hs i j]

section Module

variable (V : X.Opens)

/-- `Γ(X, V)` acts on sections of `M ⊗ L^{⊗n}` over `V`. -/
noncomputable instance : SMul Γ(X, V) (L.twistAddSubgroup M n V) where
  smul r s := ⟨fun i ↦ X.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op r • s.1 i,
    fun i j ↦ by
      simp only [Scheme.Modules.map_smul, s.2 i j, CohomologyAux.presheaf_map_map]
      exact smul_comm _ _ _⟩

lemma twist_smul_apply (r : Γ(X, V)) (s : L.twistAddSubgroup M n V) (i : L.ι) :
    (r • s).1 i = X.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op r • s.1 i :=
  rfl

noncomputable instance : Module Γ(X, V) (L.twistAddSubgroup M n V) where
  one_smul s := by ext i; simp [twist_smul_apply]
  mul_smul r r' s := by ext i; simp [twist_smul_apply, mul_smul]
  smul_zero r := by ext i; simp [twist_smul_apply]
  smul_add r s t := by ext i; simp [twist_smul_apply, smul_add]
  add_smul r r' s := by ext i; simp [twist_smul_apply, add_smul]
  zero_smul s := by ext i; simp [twist_smul_apply]

end Module

/-- Restriction of sections of `M ⊗ L^{⊗n}` from `V` to `V' ≤ V`. -/
noncomputable def twistResHom {V V' : X.Opens} (h : V' ≤ V) :
    L.twistAddSubgroup M n V →+ L.twistAddSubgroup M n V' where
  toFun s := ⟨fun i ↦ M.presheaf.map (homOfLE (inf_le_inf_right _ h)).op (s.1 i), fun i j ↦ by
    have := congrArg (M.presheaf.map (homOfLE (inf_le_inf_right _ h :
      V' ⊓ (L.U i ⊓ L.U j) ≤ V ⊓ (L.U i ⊓ L.U j))).op) (s.2 i j)
    simp only [Scheme.Modules.map_smul, TopCat.Presheaf.map_map_apply,
      CohomologyAux.presheaf_map_map] at this ⊢
    exact this⟩
  map_zero' := by ext; simp
  map_add' s t := by ext; simp

@[simp]
lemma twistResHom_apply {V V' : X.Opens} (h : V' ≤ V) (s : L.twistAddSubgroup M n V)
    (i : L.ι) :
    (L.twistResHom M n h s).1 i = M.presheaf.map (homOfLE (inf_le_inf_right _ h)).op (s.1 i) :=
  rfl

/-- The presheaf of abelian groups of sections of `M ⊗ L^{⊗n}`. -/
noncomputable def twistPresheaf : TopCat.Presheaf AddCommGrpCat.{u} X where
  obj V := AddCommGrpCat.of (L.twistAddSubgroup M n V.unop)
  map {V V'} f := AddCommGrpCat.ofHom (L.twistResHom M n f.unop.le)
  map_id V := by
    ext s i
    simp
  map_comp f g := by
    ext s i
    simp [TopCat.Presheaf.map_map_apply]

lemma twistResHom_smul {V V' : X.Opens} (h : V' ≤ V) (r : Γ(X, V))
    (s : L.twistAddSubgroup M n V) :
    L.twistResHom M n h (r • s) = X.presheaf.map (homOfLE h).op r • L.twistResHom M n h s := by
  ext i
  simp [twist_smul_apply, CohomologyAux.presheaf_map_map]

noncomputable instance (V : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj V) ((L.twistPresheaf M n).obj V) :=
  inferInstanceAs (Module Γ(X, V.unop) (L.twistAddSubgroup M n V.unop))

/-- The presheaf of `𝒪_X`-modules of sections of `M ⊗ L^{⊗n}`. -/
noncomputable def twistPresheafOfModules : _root_.PresheafOfModules X.ringCatSheaf.obj :=
  _root_.PresheafOfModules.ofPresheaf (L.twistPresheaf M n)
    fun _ _ f r s ↦ L.twistResHom_smul M n f.unop.le r s

lemma twistPresheaf_map_apply {V V' : (X.Opens)ᵒᵖ} (f : V ⟶ V')
    (s : (L.twistPresheaf M n).obj V) (i : L.ι) :
    ((L.twistPresheaf M n).map f s).1 i =
      M.presheaf.map (homOfLE (inf_le_inf_right _ f.unop.le)).op (s.1 i) :=
  rfl

/-- The sections of `M ⊗ L^{⊗n}` form a sheaf. -/
lemma isSheaf_twistPresheaf : (L.twistPresheaf M n).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι' W sf hsf
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  have hglue (i : L.ι) : ∃! t : Γ(M, (⨆ k, W k) ⊓ L.U i), ∀ k,
      M.presheaf.map (homOfLE (inf_le_inf_right (L.U i) (le_iSup W k))).op t = (sf k).1 i := by
    refine TopCat.Sheaf.existsUnique_gluing' F (fun k ↦ W k ⊓ L.U i) _
      (fun k ↦ homOfLE (inf_le_inf_right (L.U i) (le_iSup W k))) (by rw [iSup_inf_eq])
      (fun k ↦ (sf k).1 i) fun k l ↦ ?_
    have h := congrArg (fun (s : L.twistAddSubgroup M n (W k ⊓ W l)) ↦
      M.presheaf.map (homOfLE (le_inf (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left)) (inf_le_left.trans inf_le_right) :
          (W k ⊓ L.U i) ⊓ (W l ⊓ L.U i) ≤ (W k ⊓ W l) ⊓ L.U i)).op (s.1 i)) (hsf k l)
    simp only [twistPresheaf_map_apply, TopCat.Presheaf.map_map_apply] at h
    exact h
  choose t ht htu using hglue
  refine ⟨⟨t, fun i j ↦ ?_⟩, fun k ↦ ?_, fun s' hs' ↦ ?_⟩
  · refine TopCat.Sheaf.eq_of_locally_eq' F (fun k ↦ W k ⊓ (L.U i ⊓ L.U j))
      ((⨆ k, W k) ⊓ (L.U i ⊓ L.U j))
      (fun k ↦ homOfLE (inf_le_inf_right _ (le_iSup W k))) (by rw [iSup_inf_eq]) _ _
      fun k ↦ ?_
    have h := (sf k).2 i j
    have ei : M.presheaf.map (homOfLE (inf_le_inf_right _ (le_iSup W k) :
          W k ⊓ (L.U i ⊓ L.U j) ≤ (⨆ k, W k) ⊓ (L.U i ⊓ L.U j))).op
        (M.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          (⨆ k, W k) ⊓ (L.U i ⊓ L.U j) ≤ (⨆ k, W k) ⊓ L.U i)).op (t i)) =
        M.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          W k ⊓ (L.U i ⊓ L.U j) ≤ W k ⊓ L.U i)).op ((sf k).1 i) := by
      rw [TopCat.Presheaf.map_map_apply, ← ht i k, TopCat.Presheaf.map_map_apply]
    have ej : M.presheaf.map (homOfLE (inf_le_inf_right _ (le_iSup W k) :
          W k ⊓ (L.U i ⊓ L.U j) ≤ (⨆ k, W k) ⊓ (L.U i ⊓ L.U j))).op
        (M.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          (⨆ k, W k) ⊓ (L.U i ⊓ L.U j) ≤ (⨆ k, W k) ⊓ L.U j)).op (t j)) =
        M.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          W k ⊓ (L.U i ⊓ L.U j) ≤ W k ⊓ L.U j)).op ((sf k).1 j) := by
      rw [TopCat.Presheaf.map_map_apply, ← ht j k, TopCat.Presheaf.map_map_apply]
    change M.presheaf.map _ (M.presheaf.map _ (t i)) =
      M.presheaf.map _ (X.presheaf.map _ (L.trans n i j) • M.presheaf.map _ (t j))
    rw [ei, Scheme.Modules.map_smul, ej, CohomologyAux.presheaf_map_map]
    exact h
  · exact Subtype.ext (funext fun i ↦ ht i k)
  · exact Subtype.ext (funext fun i ↦
      htu i (s'.1 i) fun k ↦
        congrArg (fun (s : L.twistAddSubgroup M n (W k)) ↦ s.1 i) (hs' k))

/-- The twist `M ⊗ L^{⊗n}` of an `𝒪_X`-module `M` by the `n`-th power of a line bundle. -/
noncomputable def twist : X.Modules where
  val := L.twistPresheafOfModules M n
  isSheaf := L.isSheaf_twistPresheaf M n

section Trivialization

variable {M n} (k : L.ι) {V : X.Opens} (hV : V ≤ L.U k)

/-- On an open `V ⊆ Uₖ`, a section of `M ⊗ L^{⊗n}` is determined by its `k`-th component. -/
noncomputable def twistToModule : L.twistAddSubgroup M n V →ₗ[Γ(X, V)] Γ(M, V) where
  toFun s := M.presheaf.map (homOfLE (le_inf le_rfl hV)).op (s.1 k)
  map_add' s t := by simp
  map_smul' r s := by
    simp only [twist_smul_apply, Scheme.Modules.map_smul, CohomologyAux.presheaf_map_map,
      RingHom.id_apply]
    rw [CohomologyAux.presheaf_map_self]

lemma twistToModule_apply (s : L.twistAddSubgroup M n V) :
    L.twistToModule k hV s = M.presheaf.map (homOfLE (le_inf le_rfl hV)).op (s.1 k) :=
  rfl

variable (n) in
/-- On an open `V ⊆ Uₖ`, the section of `M ⊗ L^{⊗n}` with `k`-th component `t`: its `i`-th
component is `gᵢₖⁿ t`. -/
noncomputable def twistOfModule : Γ(M, V) →ₗ[Γ(X, V)] L.twistAddSubgroup M n V where
  toFun t := ⟨fun i ↦ X.presheaf.map (homOfLE (le_inf inf_le_right (inf_le_left.trans hV) :
      V ⊓ L.U i ≤ L.U i ⊓ L.U k)).op (L.trans n i k) •
        M.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op t, fun i j ↦ by
    have hc := L.trans_cocycle n i j k (W := V ⊓ (L.U i ⊓ L.U j))
      (le_inf (le_inf (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right))
        (inf_le_left.trans hV))
    simp only [Scheme.Modules.map_smul, TopCat.Presheaf.map_map_apply,
      CohomologyAux.presheaf_map_map, smul_smul]
    rw [hc]⟩
  map_add' t t' := by ext i; simp [smul_add]
  map_smul' r t := by
    ext i
    simp only [twist_smul_apply, Scheme.Modules.map_smul, RingHom.id_apply, smul_smul]
    rw [mul_comm]

lemma twistOfModule_apply (t : Γ(M, V)) (i : L.ι) :
    (L.twistOfModule n k hV t).1 i = X.presheaf.map (homOfLE (le_inf inf_le_right
      (inf_le_left.trans hV) : V ⊓ L.U i ≤ L.U i ⊓ L.U k)).op (L.trans n i k) •
        M.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op t :=
  rfl

lemma twistToModule_twistOfModule (t : Γ(M, V)) :
    L.twistToModule k hV (L.twistOfModule n k hV t) = t := by
  rw [twistToModule_apply, twistOfModule_apply, Scheme.Modules.map_smul,
    CohomologyAux.presheaf_map_map, TopCat.Presheaf.map_map_apply, trans_self, map_one, one_smul,
    CohomologyAux.modules_map_self]

lemma twistOfModule_twistToModule (s : L.twistAddSubgroup M n V) :
    L.twistOfModule n k hV (L.twistToModule k hV s) = s := by
  ext i
  rw [twistOfModule_apply, twistToModule_apply, TopCat.Presheaf.map_map_apply]
  have h := s.2 i k
  have hW : V ⊓ L.U i = V ⊓ (L.U i ⊓ L.U k) :=
    le_antisymm (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hV)))
      (inf_le_inf_left _ inf_le_left)
  apply CohomologyAux.modules_map_injective_of_eq M hW.symm
  simp only [Scheme.Modules.map_smul, TopCat.Presheaf.map_map_apply, CohomologyAux.presheaf_map_map]
  exact h.symm

/-- On an open `V ⊆ Uₖ`, sections of `M ⊗ L^{⊗n}` are sections of `M`. -/
noncomputable def twistEquiv : L.twistAddSubgroup M n V ≃ₗ[Γ(X, V)] Γ(M, V) :=
  LinearEquiv.ofLinearMap (L.twistToModule k hV) (L.twistOfModule n k hV)
    (LinearMap.ext fun t ↦ L.twistToModule_twistOfModule k hV t)
    (LinearMap.ext fun s ↦ L.twistOfModule_twistToModule k hV s)

lemma twistToModule_twistResHom {V' : X.Opens} (h : V' ≤ V) (s : L.twistAddSubgroup M n V) :
    L.twistToModule k (h.trans hV) (L.twistResHom M n h s) =
      M.presheaf.map (homOfLE h).op (L.twistToModule k hV s) := by
  simp [twistToModule_apply, TopCat.Presheaf.map_map_apply]

end Trivialization

section Restrict

variable {M n} (k : L.ι) {V : X.Opens} (hV : V ≤ L.U k)

set_option backward.isDefEq.respectTransparency false in
/-- The trivialization of `M ⊗ L^{⊗n}` on `V ⊆ Uₖ`, on sections over an open of `V`. -/
noncomputable def twistRestrictLinearEquiv (W : V.toScheme.Opensᵒᵖ) :
    ((L.twist M n).restrict V.ι).val.obj W ≃ₗ[V.toScheme.ringCatSheaf.obj.obj W]
      (M.restrict V.ι).val.obj W where
  toFun s := L.twistToModule k ((V.ι_image_le W.unop).trans hV) s
  invFun t := L.twistOfModule n k ((V.ι_image_le W.unop).trans hV) t
  map_add' s t := map_add (L.twistToModule k ((V.ι_image_le W.unop).trans hV)) s t
  map_smul' r s := by
    have e1 : (r • s : ((L.twist M n).restrict V.ι).val.obj W) =
        @id (L.twistAddSubgroup M n (V.ι ''ᵁ W.unop))
          ((V.ι.appIso W.unop).inv r •
            @id (L.twistAddSubgroup M n (V.ι ''ᵁ W.unop)) s) := rfl
    have e2 : RingHom.id _ r • @id ((M.restrict V.ι).val.obj W)
          (L.twistToModule k ((V.ι_image_le W.unop).trans hV) s) =
        @id Γ(M, V.ι ''ᵁ W.unop) ((V.ι.appIso W.unop).inv r •
          L.twistToModule k ((V.ι_image_le W.unop).trans hV) s) := rfl
    rw [e1]
    refine Eq.trans ?_ e2.symm
    exact (L.twistToModule k ((V.ι_image_le W.unop).trans hV)).map_smul _ s
  left_inv s := L.twistOfModule_twistToModule k _ s
  right_inv t := L.twistToModule_twistOfModule k _ t

/-- `M ⊗ L^{⊗n}` is isomorphic to `M` on any open `V ⊆ Uₖ`. -/
noncomputable def twistRestrictIso :
    (L.twist M n).restrict V.ι ≅ M.restrict V.ι :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    _root_.PresheafOfModules.isoMk
      (fun W ↦ (L.twistRestrictLinearEquiv k hV W).toModuleIso)
      (fun W W' f ↦ by
        ext s
        change L.twistToModule k ((V.ι_image_le W'.unop).trans hV)
            (L.twistResHom M n (V.ι.opensFunctor.map f.unop).le s) =
          M.presheaf.map (V.ι.opensFunctor.map f.unop).op
            (L.twistToModule k ((V.ι_image_le W.unop).trans hV) s)
        exact L.twistToModule_twistResHom k ((V.ι_image_le W.unop).trans hV) _ s)

end Restrict

section Functoriality

variable {M} {N : X.Modules} (φ : M ⟶ N)

/-- A morphism of modules acts componentwise on sections of the twists. -/
noncomputable def twistMapAddHom (V : X.Opens) :
    L.twistAddSubgroup M n V →+ L.twistAddSubgroup N n V where
  toFun s := ⟨fun i ↦ φ.app _ (s.1 i), fun i j ↦ by
    have h := congrArg (φ.app _) (s.2 i j)
    rw [Scheme.Modules.Hom.app_smul, CohomologyAux.hom_app_presheaf_map,
      CohomologyAux.hom_app_presheaf_map] at h
    exact h⟩
  map_zero' := by ext; simp
  map_add' s t := by ext; simp

lemma twistMapAddHom_apply (V : X.Opens) (s : L.twistAddSubgroup M n V) (i : L.ι) :
    (L.twistMapAddHom n φ V s).1 i = φ.app _ (s.1 i) :=
  rfl

/-- The morphism of twists `M ⊗ L^{⊗n} ⟶ N ⊗ L^{⊗n}` induced by `φ : M ⟶ N`. -/
noncomputable def twistMap : L.twist M n ⟶ L.twist N n :=
  ⟨_root_.PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom (L.twistMapAddHom n φ V.unop)
      naturality V V' f := by
        ext s
        exact Subtype.ext (funext fun i ↦ CohomologyAux.hom_app_presheaf_map φ _ _) }
    fun V r s ↦ Subtype.ext (funext fun i ↦ Scheme.Modules.Hom.app_smul φ _ _)⟩

lemma twistMap_app_apply (V : X.Opens) (s : Γ(L.twist M n, V)) (i : L.ι) :
    ((L.twistMap n φ).app V s : L.twistAddSubgroup N n V).1 i =
      φ.app _ ((s : L.twistAddSubgroup M n V).1 i) :=
  rfl

variable (M) in
lemma twistMap_id : L.twistMap n (𝟙 M) = 𝟙 _ :=
  Scheme.Modules.hom_ext _ _ fun _ ↦ by ext s; rfl

lemma twistMap_comp {K : X.Modules} (ψ : N ⟶ K) :
    L.twistMap n (φ ≫ ψ) = L.twistMap n φ ≫ L.twistMap n ψ :=
  Scheme.Modules.hom_ext _ _ fun _ ↦ by ext s; rfl

variable (X) in
/-- Twisting by `L^{⊗n}`, as a functor on `𝒪_X`-modules. -/
@[simps]
noncomputable def twistFunctor (L : X.LineBundle) (n : ℤ) : X.Modules ⥤ X.Modules where
  obj M := L.twist M n
  map φ := L.twistMap n φ
  map_id M := L.twistMap_id M n
  map_comp φ ψ := L.twistMap_comp n φ ψ

end Functoriality

section Quasicoherent

variable {M} in
/-- The twist of a quasi-coherent module by a line bundle is quasi-coherent. -/
instance isQuasicoherent_twist [M.IsQuasicoherent] : (L.twist M n).IsQuasicoherent := by
  obtain ⟨ι, W, pres, hW, -⟩ := M.exists_isOpenCover_presentation
  refine Scheme.Modules.isQuasicoherent_of_isOpenCover
    (U := fun kj : L.ι × ι ↦ L.U kj.1 ⊓ W kj.2) ?_ fun kj ↦ ?_
  · rw [IsOpenCover, iSup_prod]
    simp only [← inf_iSup_eq, ← iSup_inf_eq]
    rw [show ⨆ j, W j = ⊤ from hW, L.iSup_eq_top, inf_top_eq]
  · let V := L.U kj.1 ⊓ W kj.2
    let iso : (M.restrict (W kj.2).ι).restrict (X.homOfLE (inf_le_right : V ≤ W kj.2)) ≅
        M.restrict V.ι :=
      ((Scheme.Modules.restrictFunctorComp _ _).app M).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι _)).app M
    exact ((Scheme.Modules.presentationRestrict _ (pres kj.2)).ofIso iso).ofIso
      (L.twistRestrictIso (M := M) (n := n) kj.1 (V := V) inf_le_left).symm

end Quasicoherent

section Composition

variable {M}

lemma trans_add (a b : ℤ) (i j : L.ι) : L.trans (a + b) i j = L.trans a i j * L.trans b i j := by
  simp [trans, zpow_add]

/-- On an open contained in `Uᵢ ∩ Uⱼ`, the `i`-th and `j`-th trivializations of a section of
`M ⊗ L^{⊗a}` differ by `gᵢⱼᵃ`. -/
lemma twistToModule_eq_smul {a : ℤ} {W : X.Opens} (σ : L.twistAddSubgroup M a W) {i j : L.ι}
    (hi : W ≤ L.U i) (hj : W ≤ L.U j) :
    L.twistToModule i hi σ =
      X.presheaf.map (homOfLE (le_inf hi hj)).op (L.trans a i j) • L.twistToModule j hj σ := by
  have h := congrArg (M.presheaf.map (homOfLE (le_inf le_rfl (le_inf hi hj) :
    W ≤ W ⊓ (L.U i ⊓ L.U j))).op) (σ.2 i j)
  rw [TopCat.Presheaf.map_map_apply, Scheme.Modules.map_smul, TopCat.Presheaf.map_map_apply,
    CohomologyAux.presheaf_map_map] at h
  exact h

variable (M) in
/-- The comparison `(M ⊗ L^{⊗a}) ⊗ L^{⊗b} → M ⊗ L^{⊗(a+b)}` on sections: the `i`-th component is
the `i`-th trivialization of the `i`-th component. -/
noncomputable def twistTwistHom (a b : ℤ) (V : X.Opens) :
    L.twistAddSubgroup (L.twist M a) b V →ₗ[Γ(X, V)] L.twistAddSubgroup M (a + b) V where
  toFun s := ⟨fun i ↦ L.twistToModule i (inf_le_right : V ⊓ L.U i ≤ L.U i)
      (s.1 i : L.twistAddSubgroup M a (V ⊓ L.U i)), fun i j ↦ by
    set W := V ⊓ (L.U i ⊓ L.U j)
    have hWi : W ≤ V ⊓ L.U i := le_inf inf_le_left (inf_le_right.trans inf_le_left)
    have hWj : W ≤ V ⊓ L.U j := le_inf inf_le_left (inf_le_right.trans inf_le_right)
    have hs : L.twistResHom M a hWi (s.1 i) =
        X.presheaf.map (homOfLE (inf_le_right : W ≤ L.U i ⊓ L.U j)).op (L.trans b i j) •
          L.twistResHom M a hWj (s.1 j) := s.2 i j
    have e1 := L.twistToModule_twistResHom i (inf_le_right : V ⊓ L.U i ≤ L.U i) hWi (s.1 i)
    have e2 := L.twistToModule_twistResHom j (inf_le_right : V ⊓ L.U j ≤ L.U j) hWj (s.1 j)
    rw [← e1, ← e2, hs, LinearMap.map_smul,
      L.twistToModule_eq_smul (L.twistResHom M a hWj (s.1 j)) (hWi.trans inf_le_right)
        (hWj.trans inf_le_right), smul_smul, trans_add, map_mul, mul_comm]⟩
  map_add' s t := by
    ext i
    exact map_add (L.twistToModule i _) _ _
  map_smul' r s := by
    ext i
    exact (L.twistToModule i _).map_smul _ _

lemma twistTwistHom_apply (a b : ℤ) (V : X.Opens) (s : L.twistAddSubgroup (L.twist M a) b V)
    (i : L.ι) : (L.twistTwistHom M a b V s).1 i =
      L.twistToModule i (inf_le_right : V ⊓ L.U i ≤ L.U i)
        (s.1 i : L.twistAddSubgroup M a (V ⊓ L.U i)) :=
  rfl

variable (M) in
/-- The inverse comparison `M ⊗ L^{⊗(a+b)} → (M ⊗ L^{⊗a}) ⊗ L^{⊗b}`. -/
noncomputable def twistTwistInv (a b : ℤ) (V : X.Opens) :
    L.twistAddSubgroup M (a + b) V →ₗ[Γ(X, V)] L.twistAddSubgroup (L.twist M a) b V where
  toFun t := ⟨fun i ↦ L.twistOfModule a i (inf_le_right : V ⊓ L.U i ≤ L.U i) (t.1 i),
    fun i j ↦ by
      set W := V ⊓ (L.U i ⊓ L.U j)
      have hWi : W ≤ V ⊓ L.U i := le_inf inf_le_left (inf_le_right.trans inf_le_left)
      have hWj : W ≤ V ⊓ L.U j := le_inf inf_le_left (inf_le_right.trans inf_le_right)
      change L.twistResHom M a hWi (L.twistOfModule a i inf_le_right (t.1 i)) =
        X.presheaf.map (homOfLE (inf_le_right : W ≤ L.U i ⊓ L.U j)).op (L.trans b i j) •
          L.twistResHom M a hWj (L.twistOfModule a j inf_le_right (t.1 j))
      apply (L.twistEquiv (M := M) (n := a) i (hWi.trans inf_le_right)).injective
      change L.twistToModule i (hWi.trans inf_le_right) _ =
        L.twistToModule i (hWi.trans inf_le_right) _
      have e1 : L.twistToModule i (hWi.trans inf_le_right)
          (L.twistResHom M a hWi (L.twistOfModule a i inf_le_right (t.1 i))) =
          M.presheaf.map (homOfLE hWi).op (t.1 i) := by
        rw [L.twistToModule_twistResHom i (inf_le_right : V ⊓ L.U i ≤ L.U i),
          L.twistToModule_twistOfModule]
      have e2 : L.twistToModule i (hWi.trans inf_le_right)
          (L.twistResHom M a hWj (L.twistOfModule a j inf_le_right (t.1 j))) =
          X.presheaf.map (homOfLE (inf_le_right : W ≤ L.U i ⊓ L.U j)).op (L.trans a i j) •
            M.presheaf.map (homOfLE hWj).op (t.1 j) := by
        rw [L.twistToModule_eq_smul _ (hWi.trans inf_le_right) (hWj.trans inf_le_right),
          L.twistToModule_twistResHom j (inf_le_right : V ⊓ L.U j ≤ L.U j),
          L.twistToModule_twistOfModule]
      rw [LinearMap.map_smul, e1, e2, smul_smul, ← map_mul, mul_comm, ← trans_add]
      exact t.2 i j⟩
  map_add' s t := Subtype.ext (funext fun i ↦ map_add (L.twistOfModule a i _) _ _)
  map_smul' r s := Subtype.ext (funext fun i ↦ (L.twistOfModule a i _).map_smul _ _)

lemma twistTwistHom_inv (a b : ℤ) (V : X.Opens) (t : L.twistAddSubgroup M (a + b) V) :
    L.twistTwistHom M a b V (L.twistTwistInv M a b V t) = t :=
  Subtype.ext (funext fun i ↦ L.twistToModule_twistOfModule i _ (t.1 i))

lemma twistTwistInv_hom (a b : ℤ) (V : X.Opens) (s : L.twistAddSubgroup (L.twist M a) b V) :
    L.twistTwistInv M a b V (L.twistTwistHom M a b V s) = s :=
  Subtype.ext (funext fun i ↦ L.twistOfModule_twistToModule i _
    (s.1 i : L.twistAddSubgroup M a (V ⊓ L.U i)))

variable (M) in
/-- `(M ⊗ L^{⊗a}) ⊗ L^{⊗b} ≅ M ⊗ L^{⊗(a+b)}` on sections over `V`. -/
noncomputable def twistTwistLinearEquiv (a b : ℤ) (V : X.Opens) :
    L.twistAddSubgroup (L.twist M a) b V ≃ₗ[Γ(X, V)] L.twistAddSubgroup M (a + b) V :=
  LinearEquiv.ofLinearMap (L.twistTwistHom M a b V) (L.twistTwistInv M a b V)
    (LinearMap.ext fun t ↦ L.twistTwistHom_inv a b V t)
    (LinearMap.ext fun s ↦ L.twistTwistInv_hom a b V s)

lemma twistTwistHom_twistResHom (a b : ℤ) {V V' : X.Opens} (h : V' ≤ V)
    (s : L.twistAddSubgroup (L.twist M a) b V) :
    L.twistTwistHom M a b V' (L.twistResHom (L.twist M a) b h s) =
      L.twistResHom M (a + b) h (L.twistTwistHom M a b V s) :=
  Subtype.ext (funext fun i ↦ L.twistToModule_twistResHom i (inf_le_right : V ⊓ L.U i ≤ L.U i)
    (inf_le_inf_right _ h) (s.1 i : L.twistAddSubgroup M a (V ⊓ L.U i)))

variable (M) in
/-- `(M ⊗ L^{⊗a}) ⊗ L^{⊗b} ≅ M ⊗ L^{⊗(a+b)}`. -/
noncomputable def twistTwistIso (a b : ℤ) : L.twist (L.twist M a) b ≅ L.twist M (a + b) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    _root_.PresheafOfModules.isoMk
      (fun V ↦ (L.twistTwistLinearEquiv M a b V.unop).toModuleIso)
      (fun V V' f ↦ by
        ext s
        exact L.twistTwistHom_twistResHom a b f.unop.le s)

lemma twistTwistIso_hom_app (a b : ℤ) (V : X.Opens) (s : Γ(L.twist (L.twist M a) b, V)) :
    (L.twistTwistIso M a b).hom.app V s = L.twistTwistHom M a b V s :=
  rfl

lemma twistTwistIso_naturality {N : X.Modules} (φ : M ⟶ N) (a b : ℤ) :
    L.twistMap b (L.twistMap a φ) ≫ (L.twistTwistIso N a b).hom =
      (L.twistTwistIso M a b).hom ≫ L.twistMap (a + b) φ := by
  refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
  ext s
  refine Subtype.ext (funext fun i ↦ ?_)
  change N.presheaf.map _ (φ.app _ (((s : L.twistAddSubgroup (L.twist M a) b V).1 i :
      L.twistAddSubgroup M a (V ⊓ L.U i)).1 i)) =
    φ.app _ (M.presheaf.map _ (((s : L.twistAddSubgroup (L.twist M a) b V).1 i :
      L.twistAddSubgroup M a (V ⊓ L.U i)).1 i))
  rw [CohomologyAux.hom_app_presheaf_map]

variable (X) in
/-- Twisting twice is twisting by the sum. -/
noncomputable def twistFunctorCompIso (L : X.LineBundle) (a b : ℤ) :
    twistFunctor X L a ⋙ twistFunctor X L b ≅ twistFunctor X L (a + b) :=
  NatIso.ofComponents (fun M ↦ L.twistTwistIso M a b)
    fun φ ↦ L.twistTwistIso_naturality φ a b

end Composition

section Zero

variable {M}

lemma trans_zero (i j : L.ι) : L.trans 0 i j = 1 := by
  simp [trans]

variable (M) in
/-- The comparison `M → M ⊗ L^{⊗0}`: restriction to the members of the cover. -/
noncomputable def twistZeroHom (V : X.Opens) : Γ(M, V) →ₗ[Γ(X, V)] L.twistAddSubgroup M 0 V where
  toFun m := ⟨fun i ↦ M.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op m, fun i j ↦ by
    rw [trans_zero, map_one, one_smul, TopCat.Presheaf.map_map_apply,
      TopCat.Presheaf.map_map_apply]⟩
  map_add' m m' := by ext i; simp
  map_smul' r m := by ext i; simp [twist_smul_apply]

lemma twistZeroHom_bijective (V : X.Opens) : Function.Bijective (L.twistZeroHom M V) := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  have hcover : V ≤ ⨆ i, V ⊓ L.U i := by rw [← inf_iSup_eq, L.iSup_eq_top, inf_top_eq]
  refine ⟨fun m m' h ↦ ?_, fun s ↦ ?_⟩
  · refine TopCat.Sheaf.eq_of_locally_eq' F (fun i ↦ V ⊓ L.U i) V
      (fun i ↦ homOfLE inf_le_left) hcover m m' fun i ↦ ?_
    exact congrArg (fun (t : L.twistAddSubgroup M 0 V) ↦ t.1 i) h
  · have hcompat : TopCat.Presheaf.IsCompatible F.1 (fun i ↦ V ⊓ L.U i) (fun i ↦ s.1 i) := by
      intro i j
      have hW : (V ⊓ L.U i) ⊓ (V ⊓ L.U j) = V ⊓ (L.U i ⊓ L.U j) :=
        le_antisymm (le_inf (inf_le_left.trans inf_le_left)
          (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)))
          (le_inf (inf_le_inf_left _ inf_le_left) (inf_le_inf_left _ inf_le_right))
      apply CohomologyAux.modules_map_injective_of_eq M hW.symm
      change M.presheaf.map (homOfLE hW.symm.le).op (M.presheaf.map (homOfLE (inf_le_left :
          (V ⊓ L.U i) ⊓ (V ⊓ L.U j) ≤ V ⊓ L.U i)).op (s.1 i)) =
        M.presheaf.map (homOfLE hW.symm.le).op (M.presheaf.map (homOfLE (inf_le_right :
          (V ⊓ L.U i) ⊓ (V ⊓ L.U j) ≤ V ⊓ L.U j)).op (s.1 j))
      rw [TopCat.Presheaf.map_map_apply, TopCat.Presheaf.map_map_apply]
      have := s.2 i j
      rw [trans_zero, map_one, one_smul] at this
      exact this
    obtain ⟨t, ht, -⟩ := TopCat.Sheaf.existsUnique_gluing' F (fun i ↦ V ⊓ L.U i) V
      (fun i ↦ homOfLE inf_le_left) hcover (fun i ↦ s.1 i) hcompat
    exact ⟨t, Subtype.ext (funext fun i ↦ ht i)⟩

variable (M) in
/-- `M ≅ M ⊗ L^{⊗0}`. -/
noncomputable def twistZeroIso : M ≅ L.twist M 0 :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    _root_.PresheafOfModules.isoMk
      (fun V ↦ (LinearEquiv.ofBijective (L.twistZeroHom M V.unop)
        (L.twistZeroHom_bijective V.unop)).toModuleIso)
      (fun V V' f ↦ by
        ext m
        exact Subtype.ext (funext fun i ↦ (TopCat.Presheaf.map_map_apply _ _ _ _).trans
          (TopCat.Presheaf.map_map_apply _ _ _ _).symm))

lemma twistZeroIso_naturality {N : X.Modules} (φ : M ⟶ N) :
    φ ≫ (L.twistZeroIso N).hom = (L.twistZeroIso M).hom ≫ L.twistMap 0 φ := by
  refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
  ext m
  exact Subtype.ext (funext fun i ↦ (CohomologyAux.hom_app_presheaf_map φ _ m).symm)

variable (X) in
/-- Twisting by `L^{⊗0}` is isomorphic to the identity. -/
noncomputable def twistFunctorZeroIso (L : X.LineBundle) : 𝟭 X.Modules ≅ twistFunctor X L 0 :=
  NatIso.ofComponents (fun M ↦ L.twistZeroIso M) fun φ ↦ L.twistZeroIso_naturality φ

end Zero

section Equivalence

variable (X) in
/-- Twisting by `L^{⊗n}` is an equivalence of categories, with inverse the twist by
`L^{⊗(-n)}`. -/
noncomputable def twistEquivalence (L : X.LineBundle) (n : ℤ) : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (twistFunctor X L n) (twistFunctor X L (-n))
    (twistFunctorZeroIso X L ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫
      (twistFunctorCompIso X L n (-n)).symm)
    (twistFunctorCompIso X L (-n) n ≪≫ eqToIso (by rw [neg_add_cancel]) ≪≫
      (twistFunctorZeroIso X L).symm)

instance (n : ℤ) : (twistFunctor X L n).IsEquivalence :=
  (twistEquivalence X L n).isEquivalence_functor

end Equivalence

end AlgebraicGeometry.Scheme.LineBundle
