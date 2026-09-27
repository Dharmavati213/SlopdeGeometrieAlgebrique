/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Projective.SectionExtension

/-!
# Isomorphisms of line bundles

For line bundles `L` and `M` on `X`, presented by trivializing covers `(Uᵢ)`, `(Vⱼ)` and
transition functions `gᵢᵢ'`, `hⱼⱼ'`, an isomorphism `L ≅ M` is given by units
`φᵢⱼ ∈ Γ(Uᵢ ∩ Vⱼ, 𝒪_X)ˣ`: it sends a section `s` of `L` (so `sᵢ' = gᵢ'ᵢ sᵢ`) to the section `t`
of `M` with `tⱼ = φᵢⱼ sᵢ` on `Uᵢ ∩ Vⱼ`. That `t` is well defined and is a section of `M` are the
conditions `φᵢⱼ = gᵢ'ᵢ φᵢ'ⱼ` and `φᵢⱼ = hⱼⱼ' φᵢⱼ'`.

## Main definitions

- `Scheme.LineBundle.Iso`: isomorphisms of line bundles.
- `Scheme.LineBundle.Iso.pullback`: the inverse image of an isomorphism.
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.LineBundle

variable {X Y : Scheme.{u}}

section PullbackComp

variable {T T' : Scheme.{u}} (L : X.LineBundle) (t : T' ⟶ T) (b : T ⟶ X)

set_option backward.isDefEq.respectTransparency false in
lemma g_pullback_comp (i j : L.ι) :
    (L.pullback (t ≫ b)).g i j = ((L.pullback b).pullback t).g i j := by
  ext
  simp only [pullback, Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE]
  rfl

lemma trans_pullback_comp (n : ℤ) (i j : L.ι) :
    (L.pullback (t ≫ b)).trans n i j = ((L.pullback b).pullback t).trans n i j := by
  simp only [trans, g_pullback_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
variable {L t b} in
lemma isSection_pullback_comp_iff {n : ℤ} {V : T'.Opens} {x : (L.pullback (t ≫ b)).Fam V} :
    (L.pullback (t ≫ b)).IsSection n V x ↔ ((L.pullback b).pullback t).IsSection n V x := by
  unfold IsSection
  refine forall₂_congr fun i j ↦ ?_
  rw [trans_pullback_comp]
  exact Iff.rfl

end PullbackComp

section FamPullbackOf

variable {T T' : Scheme.{u}} (L : X.LineBundle) {b : T ⟶ X} {c : T' ⟶ X}

lemma famPullbackOf_le (t : T' ⟶ T) (hc : t ≫ b = c) {V : T.Opens} {V' : T'.Opens}
    (h : V' ≤ t ⁻¹ᵁ V) (i : L.ι) :
    V' ⊓ (L.pullback c).U i ≤ t ⁻¹ᵁ (V ⊓ (L.pullback b).U i) := by
  subst hc
  exact le_inf (inf_le_left.trans h) inf_le_right

/-- The inverse image of families along `t : T' ⟶ T`, from sections of `b*L` to sections of
`c*L` where `c = t ≫ b`. -/
noncomputable def famPullbackOf (t : T' ⟶ T) (hc : t ≫ b = c) {V : T.Opens} {V' : T'.Opens}
    (h : V' ≤ t ⁻¹ᵁ V) : (L.pullback b).Fam V →+* (L.pullback c).Fam V' :=
  RingHom.pi fun i ↦ (t.appLE (V ⊓ (L.pullback b).U i) (V' ⊓ (L.pullback c).U i)
    (L.famPullbackOf_le t hc h i)).hom.comp (Pi.evalRingHom _ i)

variable {L}

lemma famPullbackOf_apply (t : T' ⟶ T) (hc : t ≫ b = c) {V : T.Opens} {V' : T'.Opens}
    (h : V' ≤ t ⁻¹ᵁ V) (s : (L.pullback b).Fam V) (i : L.ι) :
    L.famPullbackOf t hc h s i = t.appLE (V ⊓ (L.pullback b).U i) (V' ⊓ (L.pullback c).U i)
      (L.famPullbackOf_le t hc h i) (s i) :=
  rfl

lemma famPullbackOf_eq_famPullback (t : T' ⟶ T) {V : T.Opens} {V' : T'.Opens}
    (h : V' ≤ t ⁻¹ᵁ V) (s : (L.pullback b).Fam V) :
    L.famPullbackOf t rfl h s = (L.pullback b).famPullback t h s :=
  rfl

lemma IsSection.famPullbackOf {m : ℤ} {V : T.Opens} {s : (L.pullback b).Fam V}
    (hs : (L.pullback b).IsSection m V s) (t : T' ⟶ T) (hc : t ≫ b = c) {V' : T'.Opens}
    (h : V' ≤ t ⁻¹ᵁ V) : (L.pullback c).IsSection m V' (L.famPullbackOf t hc h s) := by
  subst hc
  exact isSection_pullback_comp_iff.mpr (hs.famPullback t h)

lemma famLocus_famPullbackOf (t : T' ⟶ T) (hc : t ≫ b = c) {V : T.Opens} {V' : T'.Opens}
    (h : V' ≤ t ⁻¹ᵁ V) (s : (L.pullback b).Fam V) :
    (L.pullback c).famLocus V' (L.famPullbackOf t hc h s) =
      V' ⊓ t ⁻¹ᵁ (L.pullback b).famLocus V s := by
  subst hc
  exact famLocus_famPullback t h s

lemma famRes_famPullbackOf (t : T' ⟶ T) (hc : t ≫ b = c) {V : T.Opens} {V' V'' : T'.Opens}
    (h : V' ≤ t ⁻¹ᵁ V) (h' : V'' ≤ V') (s : (L.pullback b).Fam V) :
    (L.pullback c).famRes h' (L.famPullbackOf t hc h s) = L.famPullbackOf t hc (h'.trans h) s := by
  subst hc
  exact famRes_famPullback t h h' s

lemma famPullbackOf_famRes (t : T' ⟶ T) (hc : t ≫ b = c) {V V₀ : T.Opens} {V' : T'.Opens}
    (h : V' ≤ t ⁻¹ᵁ V) (h₀ : V ≤ V₀) (s : (L.pullback b).Fam V₀) :
    L.famPullbackOf t hc h ((L.pullback b).famRes h₀ s) =
      L.famPullbackOf t hc (h.trans (t.preimage_mono h₀)) s := by
  subst hc
  exact famPullback_famRes t h h₀ s

set_option backward.isDefEq.respectTransparency false in
lemma famPullbackOf_famPullbackOf {T'' : Scheme.{u}} {d : T'' ⟶ X} (t : T' ⟶ T) (hc : t ≫ b = c)
    (t' : T'' ⟶ T') (hd : t' ≫ c = d) {V : T.Opens} {V' : T'.Opens} {V'' : T''.Opens}
    (h : V' ≤ t ⁻¹ᵁ V) (h' : V'' ≤ t' ⁻¹ᵁ V') (s : (L.pullback b).Fam V) :
    L.famPullbackOf t' hd h' (L.famPullbackOf t hc h s) =
      L.famPullbackOf (t' ≫ t) (by rw [Category.assoc, hc, hd])
        (h'.trans (t'.preimage_mono h)) s := by
  funext (i : L.ι)
  change t'.appLE _ _ _ (t.appLE _ _ _ (s i)) = (t' ≫ t).appLE _ _ _ (s i)
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

set_option backward.isDefEq.respectTransparency false in
lemma famPullbackOf_id (hc : 𝟙 T ≫ b = b) {V V' : T.Opens} (h : V' ≤ (𝟙 T) ⁻¹ᵁ V)
    (s : (L.pullback b).Fam V) : L.famPullbackOf (𝟙 T) hc h s = (L.pullback b).famRes h s := by
  funext (i : L.ι)
  change Scheme.Hom.appLE (𝟙 T) _ _ _ (s i) = T.presheaf.map _ (s i)
  rfl

lemma famPullbackOf_congr {t₁ t₂ : T' ⟶ T} (ht : t₁ = t₂) (hc₁ : t₁ ≫ b = c) (hc₂ : t₂ ≫ b = c)
    {V : T.Opens} {V' : T'.Opens} (h₁ : V' ≤ t₁ ⁻¹ᵁ V) (h₂ : V' ≤ t₂ ⁻¹ᵁ V)
    (s : (L.pullback b).Fam V) : L.famPullbackOf t₁ hc₁ h₁ s = L.famPullbackOf t₂ hc₂ h₂ s := by
  subst ht
  rfl

lemma famPullbackOf_id' (hc : 𝟙 T ≫ b = b) {V : T.Opens} (s : (L.pullback b).Fam V) :
    L.famPullbackOf (𝟙 T) hc le_rfl s = s :=
  (famPullbackOf_id hc le_rfl s).trans (famRes_self _ _)

end FamPullbackOf

/-- An isomorphism of line bundles `L ≅ M`: units `φᵢⱼ ∈ Γ(Uᵢ ∩ Vⱼ, 𝒪_X)ˣ` such that a section
`s` of `L` is sent to the section `t` of `M` with `tⱼ = φᵢⱼ sᵢ` on `Uᵢ ∩ Vⱼ`, where `(Uᵢ)` and
`(Vⱼ)` are the trivializing covers of `L` and `M`. -/
structure Iso (L M : X.LineBundle) where
  /-- The local expressions of the isomorphism. -/
  φ : ∀ i j, Γ(X, L.U i ⊓ M.U j)ˣ
  /-- `φᵢⱼ = gᵢ'ᵢ φᵢ'ⱼ`: the image of a section does not depend on the chart of `L`. -/
  compat_left : ∀ i i' j,
    X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        L.U i ⊓ L.U i' ⊓ M.U j ≤ L.U i ⊓ M.U j)).op (φ i j : Γ(X, L.U i ⊓ M.U j)) =
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right)
          (inf_le_left.trans inf_le_left) : L.U i ⊓ L.U i' ⊓ M.U j ≤ L.U i' ⊓ L.U i)).op
          (L.g i' i : Γ(X, L.U i' ⊓ L.U i)) *
        X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          L.U i ⊓ L.U i' ⊓ M.U j ≤ L.U i' ⊓ M.U j)).op (φ i' j : Γ(X, L.U i' ⊓ M.U j))
  /-- `φᵢⱼ = hⱼⱼ' φᵢⱼ'`: the image of a section is a section of `M`. -/
  compat_right : ∀ i j j',
    X.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
        L.U i ⊓ (M.U j ⊓ M.U j') ≤ L.U i ⊓ M.U j)).op (φ i j : Γ(X, L.U i ⊓ M.U j)) =
      X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ (M.U j ⊓ M.U j') ≤ M.U j ⊓ M.U j')).op
          (M.g j j' : Γ(X, M.U j ⊓ M.U j')) *
        X.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          L.U i ⊓ (M.U j ⊓ M.U j') ≤ L.U i ⊓ M.U j')).op (φ i j' : Γ(X, L.U i ⊓ M.U j'))

namespace Iso

variable {L M : X.LineBundle}

/-- The local expressions of the inverse image of an isomorphism. -/
noncomputable def pullbackφ (e : L.Iso M) (f : Y ⟶ X) (i : L.ι) (j : M.ι) :
    Γ(Y, f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ M.U j)ˣ :=
  Units.map (f.appLE (L.U i ⊓ M.U j) (f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ M.U j)
    f.preimage_inf.ge).hom.toMonoidHom (e.φ i j)

lemma coe_pullbackφ (e : L.Iso M) (f : Y ⟶ X) (i : L.ι) (j : M.ι) :
    (e.pullbackφ f i j : Γ(Y, f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ M.U j)) =
      f.appLE (L.U i ⊓ M.U j) (f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ M.U j) f.preimage_inf.ge
        (e.φ i j : Γ(X, L.U i ⊓ M.U j)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of an isomorphism of line bundles along `f : Y ⟶ X`. -/
noncomputable def pullback (e : L.Iso M) (f : Y ⟶ X) : (L.pullback f).Iso (M.pullback f) where
  φ i j := e.pullbackφ f i j
  compat_left i i' j := by
    have := congrArg (f.appLE (L.U i ⊓ L.U i' ⊓ M.U j)
      (f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U i' ⊓ f ⁻¹ᵁ M.U j)
      ((inf_le_inf_right _ f.preimage_inf.ge).trans f.preimage_inf.ge)).hom
      (e.compat_left i i' j)
    simp only [map_mul, ← CommRingCat.comp_apply] at this
    simp only [Scheme.Hom.map_appLE] at this
    dsimp only [LineBundle.pullback]
    simp only [coe_pullbackφ, Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply]
    simp only [Scheme.Hom.appLE_map]
    exact this
  compat_right i j j' := by
    have := congrArg (f.appLE (L.U i ⊓ (M.U j ⊓ M.U j'))
      (f ⁻¹ᵁ L.U i ⊓ (f ⁻¹ᵁ M.U j ⊓ f ⁻¹ᵁ M.U j'))
      ((inf_le_inf_left _ f.preimage_inf.ge).trans f.preimage_inf.ge)).hom
      (e.compat_right i j j')
    simp only [map_mul, ← CommRingCat.comp_apply] at this
    simp only [Scheme.Hom.map_appLE] at this
    dsimp only [LineBundle.pullback]
    simp only [coe_pullbackφ, Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply]
    simp only [Scheme.Hom.appLE_map]
    exact this

section PullbackOfEq

variable {T T' : Scheme.{u}} {a b : T ⟶ X}

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of an isomorphism `a*L ≅ b*M` along `t : T' ⟶ T`, as an isomorphism
`a'*L ≅ b'*M` for `a' = t ≫ a` and `b' = t ≫ b`. -/
noncomputable def pullbackOfEq (e : (L.pullback a).Iso (M.pullback b)) (t : T' ⟶ T)
    {a' b' : T' ⟶ X} (ha : t ≫ a = a') (hb : t ≫ b = b') :
    (L.pullback a').Iso (M.pullback b') where
  φ i j := Units.map (t.appLE ((L.pullback a).U i ⊓ (M.pullback b).U j)
    ((L.pullback a').U i ⊓ (M.pullback b').U j)
    (by subst ha hb; exact le_rfl)).hom.toMonoidHom (e.φ i j)
  compat_left i i' j := by
    subst ha hb
    have := (e.pullback t).compat_left i i' j
    rw [g_pullback_comp]
    exact this
  compat_right i j j' := by
    subst ha hb
    have := (e.pullback t).compat_right i j j'
    rw [g_pullback_comp]
    exact this

lemma coe_pullbackOfEq_φ (e : (L.pullback a).Iso (M.pullback b)) (t : T' ⟶ T) {a' b' : T' ⟶ X}
    (ha : t ≫ a = a') (hb : t ≫ b = b') (i : L.ι) (j : M.ι) :
    ((e.pullbackOfEq t ha hb).φ i j).1 =
      t.appLE ((L.pullback a).U i ⊓ (M.pullback b).U j)
        ((L.pullback a').U i ⊓ (M.pullback b').U j) (by subst ha hb; exact le_rfl) (e.φ i j).1 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism `(t₁ ≫ a)*L ≅ (t₂ ≫ b)*M`, seen as an isomorphism `t₁*(a*L) ≅ t₂*(b*M)`. -/
noncomputable def ofPullbackComp {T' : Scheme.{u}} {t₁ t₂ : T' ⟶ T}
    (e : (L.pullback (t₁ ≫ a)).Iso (M.pullback (t₂ ≫ b))) :
    ((L.pullback a).pullback t₁).Iso ((M.pullback b).pullback t₂) where
  φ := e.φ
  compat_left i i' j := by
    rw [← g_pullback_comp]
    exact e.compat_left i i' j
  compat_right i j j' := by
    rw [← g_pullback_comp]
    exact e.compat_right i j j'

@[simp]
lemma ofPullbackComp_φ {T' : Scheme.{u}} {t₁ t₂ : T' ⟶ T}
    (e : (L.pullback (t₁ ≫ a)).Iso (M.pullback (t₂ ≫ b))) (i : L.ι) (j : M.ι) :
    ((ofPullbackComp e).φ i j).1 = (e.φ i j).1 :=
  rfl

end PullbackOfEq

section MapFam

variable (e : L.Iso M)

/-- On `V ∩ Uᵢ`, the image under `e` of a family `s` over `V` of degree `n`: the family of
`M` with components `φᵢⱼⁿ sᵢ`. -/
noncomputable def localImage {V : X.Opens} (n : ℕ) (s : L.Fam V) (i : L.ι) :
    M.Fam (V ⊓ L.U i) :=
  fun j ↦ X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      V ⊓ L.U i ⊓ M.U j ≤ L.U i ⊓ M.U j)).op ((e.φ i j).1 ^ n) *
    X.presheaf.map (homOfLE (inf_le_left : V ⊓ L.U i ⊓ M.U j ≤ V ⊓ L.U i)).op (s i)

lemma isSection_localImage {V : X.Opens} (n : ℕ) (s : L.Fam V) (i : L.ι) :
    M.IsSection n (V ⊓ L.U i) (e.localImage n s i) := by
  intro j j'
  have hc := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right)
    inf_le_right : V ⊓ L.U i ⊓ (M.U j ⊓ M.U j') ≤ L.U i ⊓ (M.U j ⊓ M.U j'))).op)
    (e.compat_right i j j')
  simp only [map_mul, CohomologyAux.presheaf_map_map] at hc
  simp only [localImage, map_mul, map_pow, CohomologyAux.presheaf_map_map, trans_natCast]
  rw [hc, mul_pow]
  ring

lemma localImage_compat {V : X.Opens} {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s)
    (i i' : L.ι) :
    M.famRes (inf_le_left : V ⊓ L.U i ⊓ (V ⊓ L.U i') ≤ V ⊓ L.U i) (e.localImage n s i) =
      M.famRes (inf_le_right : V ⊓ L.U i ⊓ (V ⊓ L.U i') ≤ V ⊓ L.U i') (e.localImage n s i') := by
  funext j
  have hl := congrArg (X.presheaf.map (homOfLE (le_inf (le_inf
    (inf_le_left.trans (inf_le_left.trans inf_le_right))
    (inf_le_left.trans (inf_le_right.trans inf_le_right))) inf_le_right :
      V ⊓ L.U i ⊓ (V ⊓ L.U i') ⊓ M.U j ≤ L.U i ⊓ L.U i' ⊓ M.U j)).op) (e.compat_left i i' j)
  have hs' := congrArg (X.presheaf.map (homOfLE (le_inf
    (inf_le_left.trans (inf_le_left.trans inf_le_left))
    (le_inf (inf_le_left.trans (inf_le_right.trans inf_le_right))
      (inf_le_left.trans (inf_le_left.trans inf_le_right))) :
      V ⊓ L.U i ⊓ (V ⊓ L.U i') ⊓ M.U j ≤ V ⊓ (L.U i' ⊓ L.U i))).op) (hs i' i)
  simp only [map_mul, CohomologyAux.presheaf_map_map, trans_natCast, map_pow] at hl hs'
  simp only [famRes_apply, localImage, map_mul, map_pow, CohomologyAux.presheaf_map_map]
  rw [hl, hs']
  ring

lemma exists_mapFam {V : X.Opens} {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) :
    ∃ t : M.Fam V, M.IsSection n V t ∧
      ∀ i, M.famRes (inf_le_left : V ⊓ L.U i ≤ V) t = e.localImage n s i :=
  exists_isSection_glue (L := M) (fun i ↦ V ⊓ L.U i) (fun _ ↦ inf_le_left)
    (by rw [← inf_iSup_eq, L.iSup_eq_top, inf_top_eq]) _ (fun i ↦ e.isSection_localImage n s i)
    (fun i i' ↦ e.localImage_compat hs i i')

/-- The image under an isomorphism `e : L ≅ M` of a section `s` of `L^{⊗n}` over `V`: the
section of `M^{⊗n}` equal to `φᵢⱼⁿ sᵢ` on `V ∩ Uᵢ ∩ Vⱼ`. -/
noncomputable def mapFam {V : X.Opens} {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) :
    M.Fam V :=
  (e.exists_mapFam hs).choose

lemma isSection_mapFam {V : X.Opens} {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) :
    M.IsSection n V (e.mapFam hs) :=
  (e.exists_mapFam hs).choose_spec.1

lemma famRes_mapFam {V : X.Opens} {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) (i : L.ι) :
    M.famRes (inf_le_left : V ⊓ L.U i ≤ V) (e.mapFam hs) = e.localImage n s i :=
  (e.exists_mapFam hs).choose_spec.2 i

lemma eq_mapFam {V : X.Opens} {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) {t : M.Fam V}
    (ht : ∀ i, M.famRes (inf_le_left : V ⊓ L.U i ≤ V) t = e.localImage n s i) :
    t = e.mapFam hs :=
  famRes_injective (L := M) (fun i ↦ V ⊓ L.U i) (fun _ ↦ inf_le_left)
    (by rw [← inf_iSup_eq, L.iSup_eq_top, inf_top_eq])
    fun i ↦ (ht i).trans (e.famRes_mapFam hs i).symm

lemma mapFam_congr {V : X.Opens} {n : ℕ} {s s' : L.Fam V} (hs : L.IsSection n V s)
    (hs' : L.IsSection n V s') (h : s = s') : e.mapFam hs = e.mapFam hs' := by
  subst h
  rfl

lemma localImage_mul {V : X.Opens} (m n : ℕ) (s t : L.Fam V) (i : L.ι) :
    e.localImage (m + n) (s * t) i = e.localImage m s i * e.localImage n t i := by
  funext j
  simp only [localImage, Pi.mul_apply, map_mul, pow_add]
  ring

lemma mapFam_mul {V : X.Opens} {m n : ℕ} {s t : L.Fam V} (hs : L.IsSection m V s)
    (ht : L.IsSection n V t) :
    e.mapFam ((hs.mul ht).of_eq (Nat.cast_add m n).symm) = e.mapFam hs * e.mapFam ht :=
  (e.eq_mapFam _ fun i ↦ by rw [map_mul, famRes_mapFam, famRes_mapFam, localImage_mul]).symm

lemma mapFam_add {V : X.Opens} {n : ℕ} {s t : L.Fam V} (hs : L.IsSection n V s)
    (ht : L.IsSection n V t) :
    e.mapFam ((L.sectionsAddSubgroup n V).add_mem hs ht) = e.mapFam hs + e.mapFam ht := by
  refine (e.eq_mapFam _ fun i ↦ ?_).symm
  rw [map_add, famRes_mapFam, famRes_mapFam]
  funext j
  simp only [localImage, Pi.add_apply, map_add]
  ring

lemma mapFam_zero {V : X.Opens} {n : ℕ} (h0 : L.IsSection n V 0) : e.mapFam h0 = 0 := by
  refine (e.eq_mapFam _ fun i ↦ ?_).symm
  rw [map_zero]
  funext j
  simp only [localImage, Pi.zero_apply, map_zero, mul_zero]

lemma mapFam_famConst {V : X.Opens} (r : Γ(X, V))
    (h : L.IsSection ((0 : ℕ) : ℤ) V (L.famConst V r)) :
    e.mapFam h = M.famConst V r := by
  refine (e.eq_mapFam _ fun i ↦ ?_).symm
  rw [famRes_famConst]
  funext j
  simp only [localImage, famConst_apply, pow_zero, map_one, one_mul,
    CohomologyAux.presheaf_map_map]

lemma famLocus_localImage {V : X.Opens} (n : ℕ) (s : L.Fam V) (i : L.ι) :
    M.famLocus (V ⊓ L.U i) (e.localImage n s i) = X.basicOpen (s i) := by
  refine le_antisymm (iSup_le fun j ↦ ?_) fun x hx ↦ ?_
  · rw [localImage, Scheme.basicOpen_mul]
    refine inf_le_right.trans ?_
    rw [Scheme.basicOpen_res]
    exact inf_le_right
  · obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (M.iSup_eq_top.ge (Set.mem_univ x))
    have hxi : x ∈ V ⊓ L.U i := X.basicOpen_le _ hx
    refine Opens.mem_iSup.mpr ⟨j, ?_⟩
    rw [localImage, Scheme.basicOpen_mul, Scheme.basicOpen_res, Scheme.basicOpen_res,
      X.basicOpen_of_isUnit ((e.φ i j).isUnit.pow n)]
    exact ⟨⟨⟨hxi, hj⟩, hxi.2, hj⟩, ⟨hxi, hj⟩, hx⟩

lemma famLocus_mapFam {V : X.Opens} {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) :
    M.famLocus V (e.mapFam hs) = L.famLocus V s := by
  have key (i : L.ι) : (V ⊓ L.U i) ⊓ M.famLocus V (e.mapFam hs) = L.famLocus V s ⊓ L.U i := by
    rw [← famLocus_famRes (inf_le_left : V ⊓ L.U i ≤ V), famRes_mapFam, famLocus_localImage,
      famLocus_inf_U hs]
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (L.iSup_eq_top.ge (Set.mem_univ x))
    have : x ∈ (V ⊓ L.U i) ⊓ M.famLocus V (e.mapFam hs) := ⟨⟨famLocus_le _ hx, hi⟩, hx⟩
    rw [key] at this
    exact this.1
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (L.iSup_eq_top.ge (Set.mem_univ x))
    have : x ∈ L.famLocus V s ⊓ L.U i := ⟨hx, hi⟩
    rw [← key] at this
    exact this.2

lemma mapFam_famRes {V V' : X.Opens} (h : V' ≤ V) {n : ℕ} {s : L.Fam V}
    (hs : L.IsSection n V s) : e.mapFam (hs.famRes h) = M.famRes h (e.mapFam hs) := by
  refine (e.eq_mapFam _ fun i ↦ ?_).symm
  have : M.famRes (inf_le_left : V' ⊓ L.U i ≤ V') (M.famRes h (e.mapFam hs)) =
      M.famRes (inf_le_inf_right _ h : V' ⊓ L.U i ≤ V ⊓ L.U i)
        (M.famRes (inf_le_left : V ⊓ L.U i ≤ V) (e.mapFam hs)) := by
    rw [famRes_famRes, famRes_famRes]
  rw [this, famRes_mapFam]
  funext j
  simp only [famRes_apply, localImage, map_mul, CohomologyAux.presheaf_map_map]

set_option backward.isDefEq.respectTransparency false in
/-- If `e₃ = e₂ ∘ e₁` componentwise, the images of a section under `e₃` and under `e₂ ∘ e₁`
agree. -/
lemma mapFam_comp {L₁ L₂ L₃ : X.LineBundle} (e₁ : L₁.Iso L₂) (e₂ : L₂.Iso L₃) (e₃ : L₁.Iso L₃)
    (hrel : ∀ i j k, X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
        inf_le_right : L₁.U i ⊓ L₂.U j ⊓ L₃.U k ≤ L₁.U i ⊓ L₃.U k)).op (e₃.φ i k).1 =
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          L₁.U i ⊓ L₂.U j ⊓ L₃.U k ≤ L₂.U j ⊓ L₃.U k)).op (e₂.φ j k).1 *
        X.presheaf.map (homOfLE (inf_le_left : L₁.U i ⊓ L₂.U j ⊓ L₃.U k ≤ L₁.U i ⊓ L₂.U j)).op
          (e₁.φ i j).1)
    {V : X.Opens} {n : ℕ} {s : L₁.Fam V} (hs : L₁.IsSection n V s) :
    e₃.mapFam hs = e₂.mapFam (e₁.isSection_mapFam hs) := by
  refine (e₃.eq_mapFam hs fun i ↦ ?_).symm
  funext k
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun j : L₂.ι ↦ V ⊓ L₁.U i ⊓ L₃.U k ⊓ L₂.U j) _
    (fun j ↦ homOfLE inf_le_left) ?_ _ _ fun j ↦ ?_
  · rw [← inf_iSup_eq, L₂.iSup_eq_top, inf_top_eq]
  have h₂ := congrArg (fun x : L₃.Fam (V ⊓ L₂.U j) ↦ X.presheaf.map (homOfLE (le_inf (le_inf
    (inf_le_left.trans (inf_le_left.trans inf_le_left)) inf_le_right)
    (inf_le_left.trans inf_le_right) :
      V ⊓ L₁.U i ⊓ L₃.U k ⊓ L₂.U j ≤ V ⊓ L₂.U j ⊓ L₃.U k)).op (x k))
    (e₂.famRes_mapFam (e₁.isSection_mapFam hs) j)
  have h₁ := congrArg (fun x : L₂.Fam (V ⊓ L₁.U i) ↦ X.presheaf.map (homOfLE (le_inf
    (inf_le_left.trans inf_le_left) inf_le_right :
      V ⊓ L₁.U i ⊓ L₃.U k ⊓ L₂.U j ≤ V ⊓ L₁.U i ⊓ L₂.U j)).op (x j)) (e₁.famRes_mapFam hs i)
  have h₃ := congrArg (X.presheaf.map (homOfLE (le_inf (le_inf
    (inf_le_left.trans (inf_le_left.trans inf_le_right)) inf_le_right)
    (inf_le_left.trans inf_le_right) :
      V ⊓ L₁.U i ⊓ L₃.U k ⊓ L₂.U j ≤ L₁.U i ⊓ L₂.U j ⊓ L₃.U k)).op) (hrel i j k)
  simp only [famRes_apply, localImage, map_mul, map_pow, CohomologyAux.presheaf_map_map] at h₁ h₂ h₃
  change X.presheaf.map _ (X.presheaf.map _ (e₂.mapFam (e₁.isSection_mapFam hs) k)) =
    X.presheaf.map _ (localImage e₃ n s i k)
  simp only [localImage, map_mul, map_pow, CohomologyAux.presheaf_map_map]
  rw [h₂, h₁, h₃, mul_pow]
  ring

/-- An isomorphism `L ≅ L` whose components are the transition functions `gⱼᵢ` acts as the
identity on sections. -/
lemma mapFam_eq_self (e : L.Iso L)
    (he : ∀ i j, (e.φ i j).1 = X.presheaf.map (homOfLE (le_inf inf_le_right inf_le_left :
      L.U i ⊓ L.U j ≤ L.U j ⊓ L.U i)).op (L.g j i).1)
    {V : X.Opens} {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) : e.mapFam hs = s := by
  refine (e.eq_mapFam hs fun i ↦ ?_).symm
  funext j
  have h := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
    (le_inf inf_le_right (inf_le_left.trans inf_le_right)) :
      V ⊓ L.U i ⊓ L.U j ≤ V ⊓ (L.U j ⊓ L.U i))).op) (hs j i)
  simp only [map_mul, CohomologyAux.presheaf_map_map, trans_natCast, map_pow] at h
  simp only [famRes_apply, localImage, he, map_pow, CohomologyAux.presheaf_map_map]
  exact h

end MapFam

section MapFamPullback

variable {T T' : Scheme.{u}} {a b : T ⟶ X}

set_option backward.isDefEq.respectTransparency false in
/-- The image of an inverse image is the inverse image of the image. -/
lemma mapFam_pullbackOfEq (e : (L.pullback a).Iso (M.pullback b)) (t : T' ⟶ T)
    {a' b' : T' ⟶ X} (ha : t ≫ a = a') (hb : t ≫ b = b') {V : T.Opens} {V' : T'.Opens}
    (h : V' ≤ t ⁻¹ᵁ V) {n : ℕ} {s : (L.pullback a).Fam V} (hs : (L.pullback a).IsSection n V s) :
    (e.pullbackOfEq t ha hb).mapFam (hs.famPullbackOf t ha h) =
      M.famPullbackOf t hb h (e.mapFam hs) := by
  subst ha hb
  refine ((e.pullbackOfEq t rfl rfl).eq_mapFam _ fun i ↦ ?_).symm
  have h₂ : V' ⊓ (t ≫ a) ⁻¹ᵁ L.U i ≤ t ⁻¹ᵁ (V ⊓ a ⁻¹ᵁ L.U i) :=
    le_inf (inf_le_left.trans h) inf_le_right
  rw [famRes_famPullbackOf]
  refine (famPullbackOf_famRes (L := M) t rfl h₂ (inf_le_left : V ⊓ a ⁻¹ᵁ L.U i ≤ V)
    (e.mapFam hs)).symm.trans
    ((congrArg (M.famPullbackOf t rfl h₂) (e.famRes_mapFam hs i)).trans ?_)
  funext (j : M.ι)
  change t.appLE _ _ _ (localImage e n s i j) = localImage (e.pullbackOfEq t rfl rfl) n _ i j
  simp only [localImage, map_mul, map_pow, famPullbackOf_apply, coe_pullbackOfEq_φ,
    ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

end MapFamPullback

section ReflSymm

variable (L) in
/-- The identity isomorphism `L ≅ L`, with components `φᵢⱼ = gⱼᵢ`. -/
noncomputable def refl : L.Iso L where
  φ i j := unitsRes (le_inf inf_le_right inf_le_left : L.U i ⊓ L.U j ≤ L.U j ⊓ L.U i) (L.g j i)
  compat_left i i' j := by
    have h := congrArg Units.val (L.unitsRes_cocycle j i' i (W := L.U i ⊓ L.U i' ⊓ L.U j)
      (le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_right))
        (inf_le_left.trans inf_le_left)))
    simp only [Units.val_mul, coe_unitsRes] at h
    simp only [coe_unitsRes, CohomologyAux.presheaf_map_map]
    rw [← h, mul_comm]
  compat_right i j j' := by
    have h := congrArg Units.val (L.unitsRes_cocycle j j' i (W := L.U i ⊓ (L.U j ⊓ L.U j'))
      (le_inf (le_inf (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right))
        inf_le_left))
    simp only [Units.val_mul, coe_unitsRes] at h
    simp only [coe_unitsRes, CohomologyAux.presheaf_map_map]
    rw [← h]

@[simp]
lemma mapFam_refl {V : X.Opens} {n : ℕ} {s : L.Fam V} (hs : L.IsSection n V s) :
    (refl L).mapFam hs = s :=
  (refl L).mapFam_eq_self (fun _ _ ↦ rfl) hs

omit L in
lemma unitsRes_unitsRes {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    unitsRes h₂ (unitsRes h₁ u) = unitsRes (h₂.trans h₁) u := by
  ext
  simp only [coe_unitsRes, CohomologyAux.presheaf_map_map]

/-- `gᵢⱼ gⱼᵢ = 1` on any open contained in `Uᵢ ∩ Uⱼ`. -/
lemma unitsRes_g_mul_g (i j : L.ι) {W : X.Opens} (hW : W ≤ L.U i ⊓ L.U j) :
    unitsRes hW (L.g i j) * unitsRes (hW.trans (le_inf inf_le_right inf_le_left)) (L.g j i) =
      1 := by
  have h := L.unitsRes_cocycle i j i (W := W) (le_inf hW (hW.trans inf_le_left))
  rw [g_self, map_one] at h
  exact h

/-- The inverse of an isomorphism of line bundles: its components are `φⱼᵢ⁻¹`. -/
noncomputable def symm (e : L.Iso M) : M.Iso L where
  φ j i := (unitsRes (le_inf inf_le_right inf_le_left : M.U j ⊓ L.U i ≤ L.U i ⊓ M.U j) (e.φ i j))⁻¹
  compat_left j j' i := by
    have hO : M.U j ⊓ M.U j' ⊓ L.U i ≤ L.U i ⊓ (M.U j ⊓ M.U j') :=
      le_inf inf_le_right inf_le_left
    have hc : unitsRes (hO.trans (le_inf inf_le_left (inf_le_right.trans inf_le_left))) (e.φ i j) =
        unitsRes (hO.trans inf_le_right) (M.g j j') *
          unitsRes (hO.trans (le_inf inf_le_left (inf_le_right.trans inf_le_right)))
            (e.φ i j') := by
      ext
      have := congrArg (X.presheaf.map (homOfLE hO).op) (e.compat_right i j j')
      simpa only [map_mul, CohomologyAux.presheaf_map_map, coe_unitsRes, Units.val_mul] using this
    have hg := unitsRes_g_mul_g (L := M) j j' (hO.trans inf_le_right)
    rw [← coe_unitsRes, ← coe_unitsRes, ← coe_unitsRes, ← Units.val_mul]
    congr 1
    simp only [map_inv, unitsRes_unitsRes]
    rw [hc, mul_inv, inv_eq_of_mul_eq_one_right hg, mul_comm]
  compat_right j i i' := by
    have hO : M.U j ⊓ (L.U i ⊓ L.U i') ≤ L.U i ⊓ L.U i' ⊓ M.U j :=
      le_inf inf_le_right inf_le_left
    have hc : unitsRes (hO.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
        (e.φ i j) = unitsRes (hO.trans (le_inf (inf_le_left.trans inf_le_right)
          (inf_le_left.trans inf_le_left))) (L.g i' i) *
          unitsRes (hO.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
            (e.φ i' j) := by
      ext
      have := congrArg (X.presheaf.map (homOfLE hO).op) (e.compat_left i i' j)
      simpa only [map_mul, CohomologyAux.presheaf_map_map, coe_unitsRes, Units.val_mul] using this
    have hg := unitsRes_g_mul_g (L := L) i' i
      (hO.trans (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)))
    rw [← coe_unitsRes, ← coe_unitsRes, ← coe_unitsRes, ← Units.val_mul]
    congr 1
    simp only [map_inv, unitsRes_unitsRes]
    rw [hc, mul_inv, inv_eq_of_mul_eq_one_right hg, mul_comm]

lemma mapFam_symm_mapFam (e : L.Iso M) {V : X.Opens} {n : ℕ} {s : L.Fam V}
    (hs : L.IsSection n V s) : e.symm.mapFam (e.isSection_mapFam hs) = s := by
  refine (mapFam_comp e e.symm (refl L) (fun i j k ↦ ?_) hs).symm.trans (mapFam_refl hs)
  have hO : L.U i ⊓ M.U j ⊓ L.U k ≤ L.U i ⊓ L.U k ⊓ M.U j :=
    le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (inf_le_left.trans inf_le_right)
  have hc : unitsRes (hO.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) (e.φ i j) =
      unitsRes (hO.trans (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)))
        (L.g k i) *
        unitsRes (hO.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (e.φ k j) := by
    ext
    have := congrArg (X.presheaf.map (homOfLE hO).op) (e.compat_left i k j)
    simpa only [map_mul, CohomologyAux.presheaf_map_map, coe_unitsRes, Units.val_mul] using this
  change X.presheaf.map _ (unitsRes _ (L.g k i)).1 = X.presheaf.map _
    ((unitsRes _ (e.φ k j))⁻¹).1 * X.presheaf.map _ (e.φ i j).1
  rw [← coe_unitsRes, ← coe_unitsRes, ← coe_unitsRes, ← Units.val_mul]
  congr 1
  simp only [map_inv, unitsRes_unitsRes]
  rw [hc, mul_comm (unitsRes _ (L.g k i)), inv_mul_cancel_left]

lemma mapFam_mapFam_symm (e : L.Iso M) {V : X.Opens} {n : ℕ} {t : M.Fam V}
    (ht : M.IsSection n V t) : e.mapFam (e.symm.isSection_mapFam ht) = t := by
  refine (mapFam_comp e.symm e (refl M) (fun j i k ↦ ?_) ht).symm.trans (mapFam_refl ht)
  have hO : M.U j ⊓ L.U i ⊓ M.U k ≤ L.U i ⊓ (M.U k ⊓ M.U j) :=
    le_inf (inf_le_left.trans inf_le_right) (le_inf inf_le_right (inf_le_left.trans inf_le_left))
  have hc : unitsRes (hO.trans (le_inf inf_le_left (inf_le_right.trans inf_le_left))) (e.φ i k) =
      unitsRes (hO.trans inf_le_right) (M.g k j) *
        unitsRes (hO.trans (le_inf inf_le_left (inf_le_right.trans inf_le_right))) (e.φ i j) := by
    ext
    have := congrArg (X.presheaf.map (homOfLE hO).op) (e.compat_right i k j)
    simpa only [map_mul, CohomologyAux.presheaf_map_map, coe_unitsRes, Units.val_mul] using this
  change X.presheaf.map _ (unitsRes _ (M.g k j)).1 = X.presheaf.map _ (e.φ i k).1 *
    X.presheaf.map _ ((unitsRes _ (e.φ i j))⁻¹).1
  rw [← coe_unitsRes, ← coe_unitsRes, ← coe_unitsRes, ← Units.val_mul]
  congr 1
  simp only [map_inv, unitsRes_unitsRes]
  rw [hc, mul_inv_cancel_right]

end ReflSymm

end Iso

end AlgebraicGeometry.Scheme.LineBundle
