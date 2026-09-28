/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import SGA.Foundations.QuasiAffine

/-!
# Line bundles, ample line bundles and quasi-projective morphisms

Mathlib has sheaves of modules on a scheme but no tensor products of them, hence no tensor powers
of invertible sheaves. We work instead with line bundles presented by transition functions: a
`Scheme.LineBundle` on `X` is an open cover `(Uᵢ)` of `X` with units `gᵢⱼ ∈ Γ(Uᵢ ∩ Uⱼ, 𝒪_X)ˣ`
satisfying the cocycle condition (a Čech `1`-cocycle with values in `𝒪_X^×`). A global section of
the `n`-th tensor power `L^{⊗n}` is a family `sᵢ ∈ Γ(Uᵢ, 𝒪_X)` with `sᵢ = gᵢⱼⁿ sⱼ` on `Uᵢ ∩ Uⱼ`,
and its non-vanishing locus `X_s` is the union of the `D(sᵢ)`.

## Main definitions

- `Scheme.LineBundle`, `Scheme.LineBundle.sections`, `Scheme.LineBundle.nonvanishingLocus`,
  `Scheme.LineBundle.pullback`, `Scheme.LineBundle.trivial`.
- `Scheme.LineBundle.tensor`: the tensor product `L ⊗ M`, on the common refinement of the covers.
- `Scheme.LineBundle.IsAmple`: `X` is quasi-compact and the affine `X_s`, for `s` a section of
  some `L^{⊗n}` with `n ≥ 1`, cover `X` (EGA II 4.5.3, Stacks 01PS).
- `Scheme.LineBundle.IsRelativelyAmple`: `L` is ample relative to a quasi-compact `f : X ⟶ Y` if
  its restriction to the inverse image of every affine open subset of `Y` is ample (EGA II 4.6.1).
- `IsQuasiProjective`: a morphism of finite type admitting a relatively ample line bundle
  (EGA II 5.3.1).

## Main results

- `Scheme.LineBundle.isAmple_trivial_iff`: `𝒪_X` is ample iff `X` is quasi-affine (EGA II 5.1.2).
- `Scheme.LineBundle.isRelativelyAmple_trivial_iff`: `𝒪_X` is ample relative to `f` iff `f` is
  quasi-affine (EGA II 5.1.6).
- Quasi-affine morphisms of finite type are quasi-projective.
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}}

/-- A line bundle on `X`, presented by an open cover `(Uᵢ)` of `X` and transition functions
`gᵢⱼ ∈ Γ(Uᵢ ∩ Uⱼ, 𝒪_X)ˣ` satisfying the cocycle condition `gᵢⱼ gⱼₖ = gᵢₖ` on `Uᵢ ∩ Uⱼ ∩ Uₖ`. -/
structure LineBundle (X : Scheme.{u}) where
  /-- The index type of the trivializing cover. -/
  ι : Type u
  /-- The trivializing open cover. -/
  U : ι → X.Opens
  iSup_eq_top : ⨆ i, U i = ⊤
  /-- The transition functions. -/
  g : ∀ i j, Γ(X, U i ⊓ U j)ˣ
  cocycle : ∀ i j k,
    X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j)).op (g i j) *
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        U i ⊓ U j ⊓ U k ≤ U j ⊓ U k)).op (g j k) =
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        U i ⊓ U j ⊓ U k ≤ U i ⊓ U k)).op (g i k)

namespace LineBundle

variable (L : X.LineBundle)

/-- The global sections of the `n`-th tensor power `L^{⊗n}`: families `sᵢ ∈ Γ(Uᵢ, 𝒪_X)` with
`sᵢ = gᵢⱼⁿ sⱼ` on `Uᵢ ∩ Uⱼ`. -/
def sections (n : ℕ) : Type u :=
  {s : ∀ i, Γ(X, L.U i) // ∀ i j,
    X.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op (s i) =
      ((L.g i j : Γ(X, L.U i ⊓ L.U j))) ^ n *
        X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op (s j)}

/-- The non-vanishing locus `X_s` of a section `s` of `L^{⊗n}`. -/
def nonvanishingLocus {n : ℕ} (s : L.sections n) : X.Opens :=
  ⨆ i, X.basicOpen (s.1 i)

lemma mem_nonvanishingLocus {n : ℕ} (s : L.sections n) {x : X} :
    x ∈ L.nonvanishingLocus s ↔ ∃ i, x ∈ X.basicOpen (s.1 i) :=
  Opens.mem_iSup

/-- An invertible sheaf `L` on `X` is ample if `X` is quasi-compact and every point of `X` lies in
an affine open `X_s` for some section `s` of some `L^{⊗n}` with `n ≥ 1` (EGA II 4.5.3, Stacks
01PS). -/
def IsAmple : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ (n : ℕ) (_ : 0 < n) (s : L.sections n),
    x ∈ L.nonvanishingLocus s ∧ IsAffineOpen (L.nonvanishingLocus s)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of a line bundle under a morphism of schemes. -/
noncomputable def pullback (f : Y ⟶ X) : Y.LineBundle where
  ι := L.ι
  U i := f ⁻¹ᵁ L.U i
  iSup_eq_top := by rw [← Scheme.Hom.preimage_iSup, L.iSup_eq_top, Scheme.Hom.preimage_top]
  g i j := Units.map (f.appLE (L.U i ⊓ L.U j) (f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j)
    f.preimage_inf.ge).hom (L.g i j)
  cocycle i j k := by
    have := congrArg (f.appLE (L.U i ⊓ L.U j ⊓ L.U k)
      (f ⁻¹ᵁ L.U i ⊓ f ⁻¹ᵁ L.U j ⊓ f ⁻¹ᵁ L.U k)
      ((inf_le_inf_right _ f.preimage_inf.ge).trans f.preimage_inf.ge)).hom
      (L.cocycle i j k)
    simp only [map_mul, ← CommRingCat.comp_apply] at this
    simp only [Scheme.Hom.map_appLE] at this
    simp only [Units.coe_map, MonoidHom.coe_coe, ← CommRingCat.comp_apply]
    simp only [Scheme.Hom.appLE_map]
    exact this

/-- The trivial line bundle `𝒪_X`. -/
noncomputable def trivial (X : Scheme.{u}) : X.LineBundle where
  ι := PUnit
  U _ := ⊤
  iSup_eq_top := by simp
  g _ _ := 1
  cocycle _ _ _ := by simp

/-- The sections of the powers of the trivial line bundle are the global functions. -/
def trivialSectionsEquiv (n : ℕ) : (trivial X).sections n ≃ Γ(X, ⊤) where
  toFun s := s.1 PUnit.unit
  invFun r := ⟨fun _ ↦ r, fun _ _ ↦ by
    dsimp only [trivial]
    erw [Units.val_one, one_pow, one_mul]
    rfl⟩
  left_inv s := Subtype.ext (funext fun _ ↦ rfl)
  right_inv _ := rfl

lemma nonvanishingLocus_trivial {n : ℕ} (s : (trivial X).sections n) :
    (trivial X).nonvanishingLocus s = X.basicOpen (trivialSectionsEquiv n s) := by
  simp [nonvanishingLocus, trivial]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The sections of the powers of the inverse image of the trivial line bundle are the global
functions. -/
noncomputable def pullbackTrivialSectionsEquiv (f : Y ⟶ X) (n : ℕ) :
    ((trivial X).pullback f).sections n ≃ Γ(Y, ⊤) where
  toFun s := s.1 PUnit.unit
  invFun r := ⟨fun _ ↦ r, fun _ _ ↦ by
    dsimp only [pullback, trivial]
    erw [map_one, Units.val_one, one_pow, one_mul]⟩
  left_inv s := Subtype.ext (funext fun _ ↦ rfl)
  right_inv _ := rfl

lemma nonvanishingLocus_pullback_trivial (f : Y ⟶ X) {n : ℕ}
    (s : ((trivial X).pullback f).sections n) :
    ((trivial X).pullback f).nonvanishingLocus s =
      Y.basicOpen (pullbackTrivialSectionsEquiv f n s) := by
  simp [nonvanishingLocus, pullback, trivial]
  rfl

/-- A line bundle whose sections of all powers are the global functions, with the basic open
subsets as non-vanishing loci, is ample iff `X` is quasi-affine. -/
lemma isAmple_iff_isQuasiAffine_of_equiv (L : X.LineBundle) (e : ∀ n, L.sections n ≃ Γ(X, ⊤))
    (he : ∀ n (s : L.sections n), L.nonvanishingLocus s = X.basicOpen (e n s)) :
    L.IsAmple ↔ X.IsQuasiAffine := by
  constructor
  · rintro ⟨_, H⟩
    refine .of_forall_exists_mem_basicOpen _ fun x ↦ ?_
    obtain ⟨n, -, s, hx, hs⟩ := H x
    rw [he] at hx hs
    exact ⟨_, hs, hx⟩
  · intro
    refine ⟨inferInstance, fun x ↦ ?_⟩
    obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ :=
      (IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    refine ⟨1, one_pos, (e 1).symm r, ?_, ?_⟩ <;> rw [he, Equiv.apply_symm_apply]
    exacts [hxr, hr]

/-- EGA II 5.1.2: the trivial line bundle `𝒪_X` is ample iff `X` is quasi-affine. -/
theorem isAmple_trivial_iff : (trivial X).IsAmple ↔ X.IsQuasiAffine :=
  isAmple_iff_isQuasiAffine_of_equiv _ trivialSectionsEquiv fun _ ↦ nonvanishingLocus_trivial

theorem isAmple_pullback_trivial_iff (f : Y ⟶ X) :
    ((trivial X).pullback f).IsAmple ↔ Y.IsQuasiAffine :=
  isAmple_iff_isQuasiAffine_of_equiv _ (pullbackTrivialSectionsEquiv f) fun _ ↦
    nonvanishingLocus_pullback_trivial f

/-- A line bundle `L` on `X` is ample relative to `f : X ⟶ Y` if `f` is quasi-compact and the
restriction of `L` to the inverse image of every affine open subset of `Y` is ample
(EGA II 4.6.1). -/
def IsRelativelyAmple (f : X ⟶ Y) : Prop :=
  QuasiCompact f ∧ ∀ V : Y.Opens, IsAffineOpen V → (L.pullback (f ⁻¹ᵁ V).ι).IsAmple

/-- EGA II 5.1.6: the trivial line bundle `𝒪_X` is ample relative to `f` iff `f` is
quasi-affine. -/
theorem isRelativelyAmple_trivial_iff (f : X ⟶ Y) :
    (trivial X).IsRelativelyAmple f ↔ IsQuasiAffineHom f := by
  simp_rw [IsRelativelyAmple, isAmple_pullback_trivial_iff, isQuasiAffineHom_iff]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨have : IsQuasiAffineHom f := ⟨h⟩; inferInstance, h⟩⟩

section Tensor

variable (M : X.LineBundle)

lemma inf_inf_le_left {a b c d : X.Opens} : a ⊓ b ⊓ (c ⊓ d) ≤ a ⊓ c :=
  le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)

lemma inf_inf_le_right {a b c d : X.Opens} : a ⊓ b ⊓ (c ⊓ d) ≤ b ⊓ d :=
  le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)

/-- The transition functions of `L ⊗ M`. -/
noncomputable def tensorG (p q : L.ι × M.ι) : Γ(X, L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2))ˣ :=
  Units.map (X.presheaf.map (homOfLE (inf_inf_le_left :
      L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ L.U p.1 ⊓ L.U q.1)).op).hom (L.g p.1 q.1) *
    Units.map (X.presheaf.map (homOfLE (inf_inf_le_right :
      L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ M.U p.2 ⊓ M.U q.2)).op).hom (M.g p.2 q.2)

set_option backward.isDefEq.respectTransparency false in
lemma tensorG_cocycle (p q r : L.ι × M.ι) :
    X.presheaf.map (homOfLE (inf_le_left : L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ⊓
        (L.U r.1 ⊓ M.U r.2) ≤ L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2))).op
        (L.tensorG M p q : Γ(X, _)) *
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ⊓ (L.U r.1 ⊓ M.U r.2) ≤
          L.U q.1 ⊓ M.U q.2 ⊓ (L.U r.1 ⊓ M.U r.2))).op (L.tensorG M q r : Γ(X, _)) =
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ⊓ (L.U r.1 ⊓ M.U r.2) ≤
          L.U p.1 ⊓ M.U p.2 ⊓ (L.U r.1 ⊓ M.U r.2))).op (L.tensorG M p r : Γ(X, _)) := by
  have hL := congrArg (X.presheaf.map (homOfLE (le_inf (le_inf
    (inf_le_left.trans (inf_le_left.trans inf_le_left))
    (inf_le_left.trans (inf_le_right.trans inf_le_left)))
    (inf_le_right.trans inf_le_left) : L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ⊓
      (L.U r.1 ⊓ M.U r.2) ≤ L.U p.1 ⊓ L.U q.1 ⊓ L.U r.1)).op).hom (L.cocycle p.1 q.1 r.1)
  have hM := congrArg (X.presheaf.map (homOfLE (le_inf (le_inf
    (inf_le_left.trans (inf_le_left.trans inf_le_right))
    (inf_le_left.trans (inf_le_right.trans inf_le_right)))
    (inf_le_right.trans inf_le_right) : L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ⊓
      (L.U r.1 ⊓ M.U r.2) ≤ M.U p.2 ⊓ M.U q.2 ⊓ M.U r.2)).op).hom (M.cocycle p.2 q.2 r.2)
  simp only [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp] at hL hM
  simp only [tensorG, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul,
    ← CommRingCat.comp_apply, ← Functor.map_comp]
  rw [mul_mul_mul_comm]
  exact congrArg₂ (· * ·) hL hM

/-- The tensor product `L ⊗ M` of line bundles, trivialized on the intersections `Uₐ ∩ Vᵦ` of
the trivializing open subsets, with transition functions `gₐₐ' hᵦᵦ'`. -/
noncomputable def tensor : X.LineBundle where
  ι := L.ι × M.ι
  U p := L.U p.1 ⊓ M.U p.2
  iSup_eq_top := by
    rw [← iSup_inf_iSup, L.iSup_eq_top, M.iSup_eq_top, top_inf_eq]
  g := L.tensorG M
  cocycle := L.tensorG_cocycle M

end Tensor

end LineBundle

end Scheme

variable {X Y : Scheme.{u}}

/-- A morphism `f : X ⟶ Y` is quasi-projective if it is of finite type and there is a line bundle
on `X` ample relative to `f` (EGA II 5.3.1). -/
class IsQuasiProjective (f : X ⟶ Y) : Prop where
  locallyOfFiniteType : LocallyOfFiniteType f
  quasiCompact : QuasiCompact f
  exists_isRelativelyAmple : ∃ L : X.LineBundle, L.IsRelativelyAmple f

attribute [instance] IsQuasiProjective.locallyOfFiniteType IsQuasiProjective.quasiCompact

/-- A quasi-affine morphism of finite type is quasi-projective, `𝒪_X` being relatively ample. -/
instance (priority := 900) (f : X ⟶ Y) [IsQuasiAffineHom f] [LocallyOfFiniteType f] :
    IsQuasiProjective f :=
  ⟨inferInstance, inferInstance,
    ⟨Scheme.LineBundle.trivial X, (Scheme.LineBundle.isRelativelyAmple_trivial_iff f).mpr ‹_›⟩⟩

end AlgebraicGeometry
