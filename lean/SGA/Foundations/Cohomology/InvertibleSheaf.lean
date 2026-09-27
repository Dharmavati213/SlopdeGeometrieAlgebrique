/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Ample
import SGA.Foundations.Cohomology.Basic
import SGA.Foundations.Cohomology.Helpers
import SGA.Foundations.QuasiCoherent.Local

/-!
# The `𝒪_X`-modules `L^{⊗n}` of a line bundle

A line bundle `L` on a scheme `X` is given (`SGA.Foundations.Ample`) by an open cover `(Uᵢ)` and
transition units `gᵢⱼ ∈ Γ(Uᵢ ∩ Uⱼ, 𝒪_X)ˣ` satisfying the cocycle condition. For `n : ℤ`, the
sections of `L^{⊗n}` over an open `V` are the families `sᵢ ∈ Γ(V ∩ Uᵢ, 𝒪_X)` with
`sᵢ = gᵢⱼⁿ sⱼ` on `V ∩ Uᵢ ∩ Uⱼ`. We construct the `𝒪_X`-module `L.toModules n` of these sections
(EGA 0_I 5.4; Hartshorne II.5), and identify its sections over an open contained in some `Uₖ`
with sections of `𝒪_X`.
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.LineBundle

variable {X : Scheme.{u}} (L : X.LineBundle) (n : ℤ)

/-- The transition function `gᵢⱼⁿ ∈ Γ(Uᵢ ∩ Uⱼ, 𝒪_X)` of `L^{⊗n}`. -/
noncomputable def trans (i j : L.ι) : Γ(X, L.U i ⊓ L.U j) :=
  ((L.g i j ^ n : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j))

/-- The condition defining sections of `L^{⊗n}` over `V`. -/
def IsSection (V : X.Opens) (s : ∀ i, Γ(X, V ⊓ L.U i)) : Prop :=
  ∀ i j, X.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
      V ⊓ (L.U i ⊓ L.U j) ≤ V ⊓ L.U i)).op (s i) =
    X.presheaf.map (homOfLE (inf_le_right : V ⊓ (L.U i ⊓ L.U j) ≤ L.U i ⊓ L.U j)).op
        (L.trans n i j) *
      X.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        V ⊓ (L.U i ⊓ L.U j) ≤ V ⊓ L.U j)).op (s j)

/-- The group of sections of `L^{⊗n}` over `V`. -/
def sectionsAddSubgroup (V : X.Opens) : AddSubgroup (∀ i, Γ(X, V ⊓ L.U i)) where
  carrier := {s | L.IsSection n V s}
  add_mem' {s t} hs ht i j := by
    simp only [Pi.add_apply, map_add, hs i j, ht i j, mul_add]
  zero_mem' i j := by simp
  neg_mem' {s} hs i j := by simp [hs i j]

section Module

variable (V : X.Opens)

/-- `Γ(X, V)` acts on sections of `L^{⊗n}` over `V`. -/
noncomputable instance : SMul Γ(X, V) (L.sectionsAddSubgroup n V) where
  smul r s := ⟨fun i ↦ X.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op r * s.1 i,
    fun i j ↦ by
      simp only [map_mul, CohomologyAux.presheaf_map_map, s.2 i j]
      ring⟩

lemma smul_apply (r : Γ(X, V)) (s : L.sectionsAddSubgroup n V) (i : L.ι) :
    (r • s).1 i = X.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op r * s.1 i :=
  rfl

noncomputable instance : Module Γ(X, V) (L.sectionsAddSubgroup n V) where
  one_smul s := by ext i; simp [smul_apply]
  mul_smul r r' s := by ext i; simp [smul_apply, mul_assoc]
  smul_zero r := by ext i; simp [smul_apply]
  smul_add r s t := by ext i; simp [smul_apply, mul_add]
  add_smul r r' s := by ext i; simp [smul_apply, add_mul]
  zero_smul s := by ext i; simp [smul_apply]

end Module

/-- Restriction of sections of `L^{⊗n}` from `V` to `V' ≤ V`. -/
noncomputable def resHom {V V' : X.Opens} (h : V' ≤ V) :
    L.sectionsAddSubgroup n V →+ L.sectionsAddSubgroup n V' where
  toFun s := ⟨fun i ↦ X.presheaf.map (homOfLE (inf_le_inf_right _ h)).op (s.1 i), fun i j ↦ by
    have := congrArg (X.presheaf.map (homOfLE (inf_le_inf_right _ h :
      V' ⊓ (L.U i ⊓ L.U j) ≤ V ⊓ (L.U i ⊓ L.U j))).op) (s.2 i j)
    simp only [map_mul, CohomologyAux.presheaf_map_map] at this ⊢
    exact this⟩
  map_zero' := by ext; simp
  map_add' s t := by ext; simp

@[simp]
lemma resHom_apply {V V' : X.Opens} (h : V' ≤ V) (s : L.sectionsAddSubgroup n V) (i : L.ι) :
    (L.resHom n h s).1 i = X.presheaf.map (homOfLE (inf_le_inf_right _ h)).op (s.1 i) :=
  rfl

lemma resHom_resHom {V V' V'' : X.Opens} (h : V' ≤ V) (h' : V'' ≤ V')
    (s : L.sectionsAddSubgroup n V) :
    L.resHom n h' (L.resHom n h s) = L.resHom n (h'.trans h) s := by
  ext i
  simp [CohomologyAux.presheaf_map_map]

/-- The presheaf of abelian groups of sections of `L^{⊗n}`. -/
noncomputable def sectionsPresheaf : TopCat.Presheaf AddCommGrpCat.{u} X where
  obj V := AddCommGrpCat.of (L.sectionsAddSubgroup n V.unop)
  map {V V'} f := AddCommGrpCat.ofHom (L.resHom n f.unop.le)
  map_id V := by
    ext s i
    simp
  map_comp f g := by
    ext s i
    simp [CohomologyAux.presheaf_map_map]

lemma resHom_smul {V V' : X.Opens} (h : V' ≤ V) (r : Γ(X, V)) (s : L.sectionsAddSubgroup n V) :
    L.resHom n h (r • s) = X.presheaf.map (homOfLE h).op r • L.resHom n h s := by
  ext i
  simp [smul_apply, CohomologyAux.presheaf_map_map]

noncomputable instance (V : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj V) ((L.sectionsPresheaf n).obj V) :=
  inferInstanceAs (Module Γ(X, V.unop) (L.sectionsAddSubgroup n V.unop))

/-- The presheaf of `𝒪_X`-modules of sections of `L^{⊗n}`. -/
noncomputable def sectionsPresheafOfModules : _root_.PresheafOfModules X.ringCatSheaf.obj :=
  _root_.PresheafOfModules.ofPresheaf (L.sectionsPresheaf n)
    fun _ _ f r s ↦ L.resHom_smul n f.unop.le r s

lemma sectionsPresheaf_map_apply {V V' : (X.Opens)ᵒᵖ} (f : V ⟶ V')
    (s : (L.sectionsPresheaf n).obj V) (i : L.ι) :
    ((L.sectionsPresheaf n).map f s).1 i =
      X.presheaf.map (homOfLE (inf_le_inf_right _ f.unop.le)).op (s.1 i) :=
  rfl

/-- The sections of `L^{⊗n}` form a sheaf. -/
lemma isSheaf_sectionsPresheaf : (L.sectionsPresheaf n).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι' W sf hsf
  have hglue (i : L.ι) : ∃! t : Γ(X, (⨆ k, W k) ⊓ L.U i), ∀ k,
      X.presheaf.map (homOfLE (inf_le_inf_right (L.U i) (le_iSup W k))).op t = (sf k).1 i := by
    refine TopCat.Sheaf.existsUnique_gluing' X.sheaf (fun k ↦ W k ⊓ L.U i) _
      (fun k ↦ homOfLE (inf_le_inf_right (L.U i) (le_iSup W k))) (by rw [iSup_inf_eq])
      (fun k ↦ (sf k).1 i) fun k l ↦ ?_
    have h := congrArg (fun (s : L.sectionsAddSubgroup n (W k ⊓ W l)) ↦
      X.presheaf.map (homOfLE (le_inf (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left)) (inf_le_left.trans inf_le_right) :
          (W k ⊓ L.U i) ⊓ (W l ⊓ L.U i) ≤ (W k ⊓ W l) ⊓ L.U i)).op (s.1 i)) (hsf k l)
    simp only [sectionsPresheaf_map_apply, CohomologyAux.presheaf_map_map] at h
    exact h
  choose t ht htu using hglue
  refine ⟨⟨t, fun i j ↦ ?_⟩, fun k ↦ ?_, fun s' hs' ↦ ?_⟩
  · refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun k ↦ W k ⊓ (L.U i ⊓ L.U j))
      ((⨆ k, W k) ⊓ (L.U i ⊓ L.U j))
      (fun k ↦ homOfLE (inf_le_inf_right _ (le_iSup W k))) (by rw [iSup_inf_eq]) _ _
      fun k ↦ ?_
    have h := (sf k).2 i j
    have ei : X.presheaf.map (homOfLE (inf_le_inf_right _ (le_iSup W k) :
          W k ⊓ (L.U i ⊓ L.U j) ≤ (⨆ k, W k) ⊓ (L.U i ⊓ L.U j))).op
        (X.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          (⨆ k, W k) ⊓ (L.U i ⊓ L.U j) ≤ (⨆ k, W k) ⊓ L.U i)).op (t i)) =
        X.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          W k ⊓ (L.U i ⊓ L.U j) ≤ W k ⊓ L.U i)).op ((sf k).1 i) := by
      rw [CohomologyAux.presheaf_map_map' (h₁' := inf_le_inf_right (L.U i) (le_iSup W k))
        (h₂' := le_inf inf_le_left (inf_le_right.trans inf_le_left)), ht]
    have ej : X.presheaf.map (homOfLE (inf_le_inf_right _ (le_iSup W k) :
          W k ⊓ (L.U i ⊓ L.U j) ≤ (⨆ k, W k) ⊓ (L.U i ⊓ L.U j))).op
        (X.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          (⨆ k, W k) ⊓ (L.U i ⊓ L.U j) ≤ (⨆ k, W k) ⊓ L.U j)).op (t j)) =
        X.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          W k ⊓ (L.U i ⊓ L.U j) ≤ W k ⊓ L.U j)).op ((sf k).1 j) := by
      rw [CohomologyAux.presheaf_map_map' (h₁' := inf_le_inf_right (L.U j) (le_iSup W k))
        (h₂' := le_inf inf_le_left (inf_le_right.trans inf_le_right)), ht]
    change X.presheaf.map _ (X.presheaf.map _ (t i)) =
      X.presheaf.map _ (X.presheaf.map _ (L.trans n i j) * X.presheaf.map _ (t j))
    rw [ei, map_mul, ej, CohomologyAux.presheaf_map_map]
    exact h
  · exact Subtype.ext (funext fun i ↦ ht i k)
  · exact Subtype.ext (funext fun i ↦
      htu i (s'.1 i) fun k ↦ congrArg (fun (s : L.sectionsAddSubgroup n (W k)) ↦ s.1 i) (hs' k))

/-- The `𝒪_X`-module `L^{⊗n}` of sections of the `n`-th tensor power of a line bundle. -/
noncomputable def toModules : X.Modules where
  val := L.sectionsPresheafOfModules n
  isSheaf := L.isSheaf_sectionsPresheaf n

section Trivialization

/-- Restriction of units of sections. -/
noncomputable def unitsRes {V W : X.Opens} (h : W ≤ V) : Γ(X, V)ˣ →* Γ(X, W)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom

omit L n in
@[simp]
lemma coe_unitsRes {V W : X.Opens} (h : W ≤ V) (u : Γ(X, V)ˣ) :
    (unitsRes h u : Γ(X, W)) = X.presheaf.map (homOfLE h).op u :=
  rfl

/-- The cocycle condition for the units `gᵢⱼ`, restricted to any `W ⊆ Uᵢ ∩ Uⱼ ∩ Uₖ`. -/
lemma unitsRes_cocycle (i j k : L.ι) {W : X.Opens} (hW : W ≤ L.U i ⊓ L.U j ⊓ L.U k) :
    unitsRes (hW.trans (inf_le_left)) (L.g i j) *
        unitsRes (hW.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (L.g j k) =
      unitsRes (hW.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) (L.g i k) := by
  ext
  have := congrArg (X.presheaf.map (homOfLE hW).op) (L.cocycle i j k)
  simp only [map_mul, CohomologyAux.presheaf_map_map] at this
  simpa only [Units.val_mul, coe_unitsRes] using this

lemma g_self (k : L.ι) : L.g k k = 1 := by
  have h := L.unitsRes_cocycle k k k (W := L.U k ⊓ L.U k ⊓ L.U k) le_rfl
  have h' : unitsRes (le_rfl.trans inf_le_left : L.U k ⊓ L.U k ⊓ L.U k ≤ L.U k ⊓ L.U k)
      (L.g k k) = 1 := by
    simpa using h
  ext
  apply CohomologyAux.presheaf_map_injective_of_eq
    (show L.U k ⊓ L.U k ⊓ L.U k = L.U k ⊓ L.U k by simp)
  simpa using congrArg Units.val h'

lemma trans_self (k : L.ι) : L.trans n k k = 1 := by
  simp [trans, g_self]

/-- The cocycle condition for the transition functions `gᵢⱼⁿ` of `L^{⊗n}`. -/
lemma trans_cocycle (i j k : L.ι) {W : X.Opens} (hW : W ≤ L.U i ⊓ L.U j ⊓ L.U k) :
    X.presheaf.map (homOfLE (hW.trans inf_le_left)).op (L.trans n i j) *
        X.presheaf.map (homOfLE (hW.trans (le_inf (inf_le_left.trans inf_le_right)
          inf_le_right))).op (L.trans n j k) =
      X.presheaf.map (homOfLE (hW.trans (le_inf (inf_le_left.trans inf_le_left)
        inf_le_right))).op (L.trans n i k) := by
  simp only [trans, ← coe_unitsRes, map_zpow, ← Units.val_mul, ← mul_zpow,
    L.unitsRes_cocycle i j k hW]

variable {n} (k : L.ι) {V : X.Opens} (hV : V ≤ L.U k)

/-- On an open `V ⊆ Uₖ`, a section of `L^{⊗n}` is determined by its `k`-th component. -/
noncomputable def toUnit : L.sectionsAddSubgroup n V →ₗ[Γ(X, V)] Γ(X, V) where
  toFun s := X.presheaf.map (homOfLE (le_inf le_rfl hV)).op (s.1 k)
  map_add' s t := by simp
  map_smul' r s := by
    simp only [smul_apply, map_mul, CohomologyAux.presheaf_map_map, RingHom.id_apply, smul_eq_mul]
    congr 1
    exact CohomologyAux.presheaf_map_self _ _

lemma toUnit_apply (s : L.sectionsAddSubgroup n V) :
    L.toUnit k hV s = X.presheaf.map (homOfLE (le_inf le_rfl hV)).op (s.1 k) :=
  rfl

variable (n) in
/-- On an open `V ⊆ Uₖ`, the section of `L^{⊗n}` with `k`-th component `t`: its `i`-th component
is `gᵢₖⁿ t`. -/
noncomputable def ofUnit : Γ(X, V) →ₗ[Γ(X, V)] L.sectionsAddSubgroup n V where
  toFun t := ⟨fun i ↦ X.presheaf.map (homOfLE (le_inf inf_le_right (inf_le_left.trans hV) :
      V ⊓ L.U i ≤ L.U i ⊓ L.U k)).op (L.trans n i k) *
        X.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op t, fun i j ↦ by
    have hc := L.trans_cocycle n i j k (W := V ⊓ (L.U i ⊓ L.U j))
      (le_inf (le_inf (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right))
        (inf_le_left.trans hV))
    simp only [map_mul, CohomologyAux.presheaf_map_map]
    rw [← mul_assoc, hc]⟩
  map_add' t t' := by ext i; simp [mul_add]
  map_smul' r t := by
    ext i
    simp only [smul_apply, map_mul, RingHom.id_apply, smul_eq_mul]
    ring

lemma ofUnit_apply (t : Γ(X, V)) (i : L.ι) :
    (L.ofUnit n k hV t).1 i = X.presheaf.map (homOfLE (le_inf inf_le_right
      (inf_le_left.trans hV) : V ⊓ L.U i ≤ L.U i ⊓ L.U k)).op (L.trans n i k) *
        X.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ≤ V)).op t :=
  rfl

lemma ofUnit_apply_self (t : Γ(X, V)) :
    (L.ofUnit n k hV t).1 k = X.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U k ≤ V)).op t := by
  rw [ofUnit_apply, trans_self, map_one, one_mul]

lemma toUnit_ofUnit (t : Γ(X, V)) : L.toUnit k hV (L.ofUnit n k hV t) = t := by
  rw [toUnit_apply, ofUnit_apply, map_mul, CohomologyAux.presheaf_map_map,
    CohomologyAux.presheaf_map_map, trans_self, map_one, one_mul, CohomologyAux.presheaf_map_self]

lemma ofUnit_toUnit (s : L.sectionsAddSubgroup n V) : L.ofUnit n k hV (L.toUnit k hV s) = s := by
  ext i
  rw [ofUnit_apply, toUnit_apply, CohomologyAux.presheaf_map_map]
  have h := s.2 i k
  have hW : V ⊓ L.U i = V ⊓ (L.U i ⊓ L.U k) :=
    le_antisymm (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hV)))
      (inf_le_inf_left _ inf_le_left)
  apply CohomologyAux.presheaf_map_injective_of_eq hW.symm
  simp only [map_mul, CohomologyAux.presheaf_map_map]
  exact h.symm

/-- On an open `V ⊆ Uₖ`, sections of `L^{⊗n}` are sections of `𝒪_X`. -/
noncomputable def unitEquiv : L.sectionsAddSubgroup n V ≃ₗ[Γ(X, V)] Γ(X, V) :=
  LinearEquiv.ofLinearMap (L.toUnit k hV) (L.ofUnit n k hV)
    (LinearMap.ext fun t ↦ L.toUnit_ofUnit k hV t)
    (LinearMap.ext fun s ↦ L.ofUnit_toUnit k hV s)

lemma toUnit_resHom {V' : X.Opens} (h : V' ≤ V) (s : L.sectionsAddSubgroup n V) :
    L.toUnit k (h.trans hV) (L.resHom n h s) = X.presheaf.map (homOfLE h).op (L.toUnit k hV s) := by
  simp [toUnit_apply, CohomologyAux.presheaf_map_map]

end Trivialization

section LocallyFree

set_option backward.isDefEq.respectTransparency false in
/-- The trivialization of `L^{⊗n}` on `Uₖ`, on sections over an open of `Uₖ`. -/
noncomputable def restrictLinearEquiv (k : L.ι) (W : (L.U k).toScheme.Opensᵒᵖ) :
    ((L.toModules n).restrict (L.U k).ι).val.obj W ≃ₗ[(L.U k).toScheme.ringCatSheaf.obj.obj W]
      (SheafOfModules.unit (L.U k).toScheme.ringCatSheaf).val.obj W where
  toFun s := L.toUnit k ((L.U k).ι_image_le W.unop) s
  invFun t := L.ofUnit n k ((L.U k).ι_image_le W.unop) t
  map_add' s t := map_add (L.toUnit k ((L.U k).ι_image_le W.unop)) s t
  map_smul' r s := by
    have e1 : (r • s : ((L.toModules n).restrict (L.U k).ι).val.obj W) =
        @id (L.sectionsAddSubgroup n ((L.U k).ι ''ᵁ W.unop))
          (((L.U k).ι.appIso W.unop).inv r •
            @id (L.sectionsAddSubgroup n ((L.U k).ι ''ᵁ W.unop)) s) := rfl
    have e2 : RingHom.id _ r • @id ((SheafOfModules.unit (L.U k).toScheme.ringCatSheaf).val.obj W)
          (L.toUnit k ((L.U k).ι_image_le W.unop) s) =
        @id Γ(X, (L.U k).ι ''ᵁ W.unop) r * L.toUnit k ((L.U k).ι_image_le W.unop) s := rfl
    rw [e1]
    refine Eq.trans ?_ e2.symm
    rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
    exact (L.toUnit k ((L.U k).ι_image_le W.unop)).map_smul r s
  left_inv s := L.ofUnit_toUnit k _ s
  right_inv t := L.toUnit_ofUnit k _ t

/-- `L^{⊗n}` is trivial on `Uₖ`: its restriction to `Uₖ` is isomorphic to `𝒪_{Uₖ}`. -/
noncomputable def restrictIso (k : L.ι) :
    (L.toModules n).restrict (L.U k).ι ≅ SheafOfModules.unit (L.U k).toScheme.ringCatSheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    _root_.PresheafOfModules.isoMk
      (fun W ↦ (L.restrictLinearEquiv n k W).toModuleIso)
      (fun W W' f ↦ by
        ext s
        exact L.toUnit_resHom k ((L.U k).ι_image_le W.unop) _ s)

/-- Generating sections of `L^{⊗n}` on `Uₖ` (a basis: the generator of `𝒪_{Uₖ}`). -/
noncomputable def restrictGeneratingSections (k : L.ι) :
    ((L.toModules n).restrict (L.U k).ι).GeneratingSections :=
  (SheafOfModules.free.generatingSections PUnit).ofIso
    (Limits.coproductUniqueIso _ ≪≫ (L.restrictIso n k).symm)

instance (k : L.ι) : IsIso (L.restrictGeneratingSections n k).π :=
  SheafOfModules.GeneratingSections.isIso_ofIso_π _ _

/-- A presentation of `L^{⊗n}` on `Uₖ`, without relations. -/
noncomputable def restrictPresentation (k : L.ι) :
    ((L.toModules n).restrict (L.U k).ι).Presentation where
  generators := L.restrictGeneratingSections n k
  relations :=
    haveI : IsIso (L.restrictGeneratingSections n k).π :=
      SheafOfModules.GeneratingSections.isIso_ofIso_π _ _
    haveI : Mono (L.restrictGeneratingSections n k).π := IsIso.mono_of_iso _
    { I := ULift Empty
      s := fun j ↦ Empty.rec (motive := fun _ ↦ _) j.down
      epi := Limits.IsZero.epi (Limits.IsZero.of_iso (Limits.isZero_zero _)
        (Limits.kernel.ofMono _)) _ }

/-- `L^{⊗n}` is locally free (of rank one). -/
lemma isLocallyFree_toModules : (L.toModules n).IsLocallyFree :=
  Scheme.Modules.isLocallyFree_of_isOpenCover L.iSup_eq_top (L.restrictGeneratingSections n)

/-- `L^{⊗n}` is quasi-coherent. -/
instance isQuasicoherent_toModules : (L.toModules n).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_of_isOpenCover L.iSup_eq_top (L.restrictPresentation n)

end LocallyFree

end AlgebraicGeometry.Scheme.LineBundle
