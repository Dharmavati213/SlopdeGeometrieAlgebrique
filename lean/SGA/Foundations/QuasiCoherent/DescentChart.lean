/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Flat.Equalizer
import SGA.Foundations.QuasiCoherent.Descent

/-!
# Faithfully flat descent of modules: the affine charts

Let `g : S' ⟶ S` be faithfully flat and quasi-compact, `j : Spec A ⟶ S` an open immersion.
An affine chart of `g` over `j` (`AffineChart`) is a faithfully flat `φ : A ⟶ B` with a
local isomorphism `h : Spec B ⟶ S'` over `j`, onto `g⁻¹(j(Spec A))`; charts exist
(`AffineChart.nonempty`). For a descent datum `D` relative to `g` with quasi-coherent underlying
module `E`, we compare the descent condition on sections over `g⁻¹(j(Spec A))` with the
invariance of global sections of `h^* E` (`isDescentSection_of_isInvariant`,
`isInvariant_of_isDescentSection`, `exists_pullbackAppTop_eq_of_isInvariant`), and prove the
effectiveness in the affine case: `B ⊗_A N₀ ≅ N` for `N = Γ(Spec B, h^* E)` and its invariants
`N₀` (`bijective_liftBaseChange_invariants`, SGA 1 VIII.1.6; Stacks, Tag 023N). The cocycle
condition of the descent datum is used on `Spec (B ⊗_A B ⊗_A B)`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace TensorProduct

open TensorProduct in
/-- Faithfully flat descent of modules, in terms of an injective "coaction": let `A → B` be flat,
`N` a `B`-module, `θ : N → G` a `B`-linear injective map and `π : N → G` an `A`-linear map such
that `B ⊗_A N → G`, `b ⊗ n ↦ b • π n` is bijective. If for every `y ∈ B ⊗_A N` mapping into the
image of `θ` the two maps `B ⊗_A N ⇉ B ⊗_A G` induced by `θ` and `π` agree on `y`, then
`B ⊗_A N₀ ≅ N` for `N₀ = {n | θ n = π n}`. -/
theorem bijective_liftBaseChange_eqLocus {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] {N G : Type u} [AddCommGroup N] [Module B N] [Module A N]
    [IsScalarTower A B N] [AddCommGroup G] [Module B G] [Module A G] [IsScalarTower A B G]
    (θ : N →ₗ[B] G) (π : N →ₗ[A] G) (hκ : Function.Bijective (LinearMap.liftBaseChange B π))
    (hθ : Function.Injective θ)
    (H : ∀ (y : B ⊗[A] N), (∃ n, LinearMap.liftBaseChange B π y = θ n) →
      (θ.restrictScalars A).lTensor B y = π.lTensor B y) :
    Function.Bijective
      (LinearMap.liftBaseChange B (LinearMap.eqLocus (θ.restrictScalars A) π).subtype) := by
  set N₀ := LinearMap.eqLocus (θ.restrictScalars A) π
  have key (z : B ⊗[A] N₀) : LinearMap.liftBaseChange B π (N₀.subtype.lTensor B z) =
      θ (LinearMap.liftBaseChange B N₀.subtype z) := by
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m =>
      simp only [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, map_smul]
      congr 1
      exact m.2.symm
  constructor
  · intro z z' hzz'
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := B) N₀.subtype
      N₀.injective_subtype
    apply hκ.1
    rw [key, key, hzz']
  · intro n
    obtain ⟨y, hy⟩ := hκ.2 (θ n)
    have hmem : y ∈ LinearMap.eqLocus (AlgebraTensorModule.lTensor A B (θ.restrictScalars A))
        (AlgebraTensorModule.lTensor A B π) := H y ⟨n, hy⟩
    rw [Module.Flat.eqLocus_lTensor_eq] at hmem
    obtain ⟨z, hz⟩ := hmem
    refine ⟨z, hθ ?_⟩
    rw [← key]
    exact (congrArg _ hz).trans hy


namespace AlgebraicGeometry

open ModuleCat ChangeOfRings in
/-- If `γ : C ⟶ C'` has a retraction, then `m ↦ 1 ⊗ m`, `Q → C' ⊗_C Q` is injective. -/
lemma oneTmul_injective_of_comp_eq_id {C C' : CommRingCat.{u}} (γ : C ⟶ C') (ρ : C' ⟶ C)
    (hρ : γ ≫ ρ = 𝟙 C) (Q : ModuleCat.{u} C) : Function.Injective (oneTmul Q γ) := by
  let F : C' →+ (Q →+ Q) :=
    { toFun c := DistribSMul.toAddMonoidHom Q (ρ c)
      map_zero' := by ext q; simp
      map_add' c c' := by ext q; simp [add_smul] }
  let Φ : (ModuleCat.extendScalars γ.hom).obj Q →+ Q :=
    TensorProduct.liftAddHom F (fun c c' q ↦ by
      suffices ∀ c'' : C', ρ (γ c * c'') • q = ρ c'' • (c • q) from this c'
      intro c''
      rw [map_mul, ← CategoryTheory.comp_apply, hρ, CommRingCat.id_apply, mul_comm, mul_smul])
  intro q q' h
  have e (q : Q) : Φ (oneTmul Q γ q) = q := by
    change ρ 1 • q = q
    rw [map_one, one_smul]
  rw [← e q, ← e q', h]



open ModuleCat ChangeOfRings in
lemma tensorCancelHom_tmul {A B C : CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ C) (Q : ModuleCat.{u} C)
    (b : B) (q : Q) :
    letI := φ.hom.toAlgebra
    tensorCancelHom φ ψ Q (b ⊗ₜ[A] (show (ModuleCat.restrictScalars ψ.hom).obj Q from q)) =
      tensorInl φ ψ b • oneTmul Q (tensorInr φ ψ) q := by
  let := φ.hom.toAlgebra
  exact TensorProduct.liftAddHom_tmul _ _ _ _

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {S S' : Scheme.{u}} (g : S' ⟶ S)

/-- An affine chart of `g : S' ⟶ S` over an open immersion `j : Spec A ⟶ S`: a faithfully flat
ring map `φ : A ⟶ B` and a morphism `h : Spec B ⟶ S'` over `j` which is a local isomorphism onto
`g⁻¹(j(Spec A))`. -/
structure AffineChart {A : CommRingCat.{u}} (j : Spec A ⟶ S) where
  /-- the ring of the chart -/
  B : CommRingCat.{u}
  /-- the ring map -/
  φ : A ⟶ B
  /-- the chart map -/
  h : Spec B ⟶ S'
  comm : h ≫ g = Spec.map φ ≫ j
  isLocalIso : IsLocalIso h
  range_eq : Set.range h = g ⁻¹' Set.range j
  faithfullyFlat : φ.hom.FaithfullyFlat

set_option backward.isDefEq.respectTransparency.types false in
theorem AffineChart.nonempty [Flat g] [Surjective g] [QuasiCompact g] {A : CommRingCat.{u}}
    (j : Spec A ⟶ S) [IsOpenImmersion j] : Nonempty (AffineChart g j) := by
  let gA := pullback.snd g j
  have : CompactSpace ↥(Limits.pullback g j) := QuasiCompact.compactSpace_of_compactSpace gA
  obtain ⟨S₁, π, hπs, hπ, hS₁⟩ :=
    (Limits.pullback g j).exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  have : Flat π := IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ π hπ
  have : Surjective π := hπs
  have : IsLocalIso π := hπ
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (S₁.isoSpec.inv ≫ π ≫ gA)
  have hff : φ.hom.FaithfullyFlat := by
    rw [← flat_and_surjective_SpecMap_iff, hφ]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨⟨_, φ, S₁.isoSpec.inv ≫ π ≫ pullback.fst g j, ?_, ?_, ?_, hff⟩⟩
  · simp only [Category.assoc, pullback.condition, hφ, gA]
  · exact MorphismProperty.comp_mem @IsLocalIso _ _
      (IsZariskiLocalAtSource.of_isOpenImmersion (P := @IsLocalIso) _)
      (MorphismProperty.comp_mem @IsLocalIso _ _ hπ
        (IsZariskiLocalAtSource.of_isOpenImmersion (P := @IsLocalIso) _))
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨gA (π (S₁.isoSpec.inv y)), ?_⟩
      simp only [← Scheme.Hom.comp_apply, Category.assoc, gA, ← pullback.condition]
    · intro hx
      rw [← Scheme.Pullback.range_fst] at hx
      obtain ⟨z, rfl⟩ := hx
      obtain ⟨w, rfl⟩ := π.surjective z
      obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso S₁.isoSpec.inv.base).2 w
      exact ⟨y, rfl⟩


section Descent

variable {g} (D : pseudofunctorCat.DescentData (fun _ : Unit ↦ g))

/-- The descent condition on global sections of inverse images. -/
lemma IsDescentSection.app_top {W : S.Opens} {s : Γ(descentObj D, g ⁻¹ᵁ W)}
    (hs : IsDescentSection D W s) {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ S') (h : f₁ ≫ g = f₂ ≫ g)
    (h₁ : ⊤ ≤ f₁ ⁻¹ᵁ g ⁻¹ᵁ W) (h₂ : ⊤ ≤ f₂ ⁻¹ᵁ g ⁻¹ᵁ W) :
    (descentHom D f₁ f₂ h).app ⊤ (pullbackAppTop f₁ (descentObj D) (g ⁻¹ᵁ W) h₁ s) =
      pullbackAppTop f₂ (descentObj D) (g ⁻¹ᵁ W) h₂ s := by
  simp only [pullbackAppTop, ConcreteCategory.comp_apply]
  rw [Hom.app_map, hs f₁ f₂ h]
  exact presheaf_map_map_eq' _ _ _ _ _

end Descent


namespace AffineChart

variable {g} {A : CommRingCat.{u}} {j : Spec A ⟶ S} [IsOpenImmersion j] (c : AffineChart g j)

/-- The ring `B ⊗_A B` of a chart. -/
noncomputable abbrev C₂ : CommRingCat.{u} := tensorObj c.φ c.φ

/-- The first inclusion `B ⟶ B ⊗_A B`. -/
noncomputable abbrev inl : c.B ⟶ c.C₂ := tensorInl c.φ c.φ

/-- The second inclusion `B ⟶ B ⊗_A B`. -/
noncomputable abbrev inr : c.B ⟶ c.C₂ := tensorInr c.φ c.φ

/-- The first projection `Spec (B ⊗_A B) ⟶ Spec B`. -/
noncomputable abbrev p₁ : Spec c.C₂ ⟶ Spec c.B := Spec.map (c.inl)

/-- The second projection `Spec (B ⊗_A B) ⟶ Spec B`. -/
noncomputable abbrev p₂ : Spec c.C₂ ⟶ Spec c.B := Spec.map (c.inr)

omit [IsOpenImmersion j] in
lemma p₁_comp_SpecMap : c.p₁ ≫ Spec.map c.φ = c.p₂ ≫ Spec.map c.φ := by
  rw [← Spec.map_comp, ← Spec.map_comp, tensorInl_comm]

omit [IsOpenImmersion j] in
lemma p_comp_h_comp : (c.p₁ ≫ c.h) ≫ g = (c.p₂ ≫ c.h) ≫ g := by
  simp only [Category.assoc, c.comm]
  rw [← Category.assoc, c.p₁_comp_SpecMap, Category.assoc]

/-- The open `g⁻¹(j(Spec A))` of `S'`. -/
noncomputable abbrev U (_c : AffineChart g j) : S'.Opens := g ⁻¹ᵁ j.opensRange

lemma coe_U : ((c.U : S'.Opens) : Set S') = Set.range c.h := by
  rw [c.range_eq]; rfl

lemma top_le : ⊤ ≤ c.h ⁻¹ᵁ (c.U : S'.Opens) := fun x _ ↦ by
  change c.h x ∈ (c.U : Set S')
  rw [c.coe_U]; exact ⟨x, rfl⟩

lemma top_le_of_comp {Y : Scheme.{u}} (a : Y ⟶ Spec c.B) (w : Y ⟶ S') (hw : a ≫ c.h = w) :
    ⊤ ≤ w ⁻¹ᵁ (c.U : S'.Opens) := fun x _ ↦ by
  subst hw
  exact c.top_le (Set.mem_univ (a x))

lemma exists_lift {Y : Scheme.{u}} (a₁ a₂ : Y ⟶ Spec c.B)
    (e : a₁ ≫ c.h ≫ g = a₂ ≫ c.h ≫ g) :
    ∃ r : Y ⟶ Spec c.C₂, r ≫ c.p₁ = a₁ ∧ r ≫ c.p₂ = a₂ := by
  have e' : a₁ ≫ Spec.map c.φ = a₂ ≫ Spec.map c.φ := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, ← c.comm, e]
  exact ⟨(isPullback_SpecMap_tensorObj c.φ c.φ).lift a₁ a₂ e',
    (isPullback_SpecMap_tensorObj c.φ c.φ).lift_fst _ _ _,
    (isPullback_SpecMap_tensorObj c.φ c.φ).lift_snd _ _ _⟩

lemma pullbackAppTop_injective (P : S'.Modules) :
    Function.Injective (pullbackAppTop c.h P c.U c.top_le) := by
  have := c.isLocalIso
  have e : ⇑(pullbackAppTop c.h P c.U c.top_le) =
      ⇑(((Scheme.Modules.pullback c.h).obj P).presheaf.map
      (homOfLE c.top_le).op) ∘ ⇑(pullbackApp c.h P c.U) := by
    ext x
    exact ConcreteCategory.comp_apply _ _ x
  rw [e]
  exact (((Scheme.Modules.pullback c.h).obj P).presheaf.map_bijective_of_eq (homOfLE c.top_le)
    (top_le_iff.mp c.top_le).symm).1.comp
    (pullbackApp_injective_of_isLocalIso_of_le c.h P c.U c.coe_U.le)

variable (D : pseudofunctorCat.DescentData (fun _ : Unit ↦ g))

/-- The descent isomorphism of `D` on global sections over `Spec (B ⊗_A B)`, applied to the
first inverse image: `n ↦ φ(p₁^* n)`. -/
noncomputable def θ : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤) ⟶
    Γ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D), ⊤) :=
  pullbackTop c.p₁ c.h (c.p₁ ≫ c.h) rfl _ ≫
    (descentHom D (c.p₁ ≫ c.h) (c.p₂ ≫ c.h) c.p_comp_h_comp).app ⊤

/-- The second inverse image `n ↦ p₂^* n`. -/
noncomputable def pb₂ : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤) ⟶
    Γ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D), ⊤) :=
  pullbackTop c.p₂ c.h (c.p₂ ≫ c.h) rfl _

omit [IsOpenImmersion j] in
lemma θ_apply (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    c.θ D n = (descentHom D (c.p₁ ≫ c.h) (c.p₂ ≫ c.h) c.p_comp_h_comp).app ⊤
      (pullbackTop c.p₁ c.h (c.p₁ ≫ c.h) rfl _ n) := rfl

/-- A global section of `h^* E` is invariant if it is compatible with the descent datum. -/
def IsInvariant (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) : Prop :=
  c.θ D n = c.pb₂ D n

lemma isInvariant_of_isDescentSection (x : Γ(descentObj D, c.U))
    (hx : IsDescentSection D j.opensRange x) :
    c.IsInvariant D (pullbackAppTop c.h (descentObj D) c.U c.top_le x) := by
  change c.θ D _ = c.pb₂ D _
  rw [θ_apply, pb₂, pullbackTop_pullbackAppTop _ _ _ _ _ _ _ (c.top_le_of_comp c.p₁ _ rfl),
    pullbackTop_pullbackAppTop _ _ _ _ _ _ _ (c.top_le_of_comp c.p₂ _ rfl)]
  exact hx.app_top D _ _ _ _ _


lemma pullbackTop_eq_of_isInvariant {n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)}
    (hn : c.IsInvariant D n) {Y : Scheme.{u}} (a₁ a₂ : Y ⟶ Spec c.B) (w : Y ⟶ S')
    (e₁ : a₁ ≫ c.h = w) (e₂ : a₂ ≫ c.h = w) :
    pullbackTop a₁ c.h w e₁ _ n = pullbackTop a₂ c.h w e₂ _ n := by
  have e : a₁ ≫ c.h ≫ g = a₂ ≫ c.h ≫ g := by
    rw [← Category.assoc, e₁, ← Category.assoc, e₂]
  obtain ⟨r, hr₁, hr₂⟩ := c.exists_lift a₁ a₂ e
  subst hr₁ hr₂
  rw [← pullbackTop_comp r c.p₁ c.h (c.p₁ ≫ c.h) w rfl ((Category.assoc _ _ _).symm.trans e₁) e₁,
    ← pullbackTop_comp r c.p₂ c.h (c.p₂ ≫ c.h) w rfl ((Category.assoc _ _ _).symm.trans e₂) e₂]
  change _ = pullbackTop r (c.p₂ ≫ c.h) w _ _ (c.pb₂ D n)
  rw [← hn, θ_apply, descentHom_pullbackTop D r (c.p₁ ≫ c.h) (c.p₂ ≫ c.h) _ w w
    ((Category.assoc _ _ _).symm.trans e₁) ((Category.assoc _ _ _).symm.trans e₂) rfl,
    descentHom_self]
  rfl

/-- Invariant global sections of `h^* E` descend to sections of `E` over `g⁻¹(j(Spec A))`. -/
lemma exists_pullbackAppTop_eq_of_isInvariant
    {n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)} (hn : c.IsInvariant D n) :
    ∃ x : Γ(descentObj D, c.U), pullbackAppTop c.h (descentObj D) c.U c.top_le x = n := by
  have := c.isLocalIso
  exact exists_pullbackAppTop_eq_of_isLocalIso c.h (descentObj D) c.U c.coe_U c.top_le n
    fun Y a₁ a₂ e ↦ c.pullbackTop_eq_of_isInvariant D hn a₁ a₂ _ rfl e.symm


/-- The descent condition at pairs of maps factoring through `Spec (B ⊗_A B)`, for a section whose
inverse image to `Spec B` is invariant. -/
lemma descentHom_app_top_of_isInvariant (x : Γ(descentObj D, c.U))
    (hx : c.IsInvariant D (pullbackAppTop c.h _ c.U c.top_le x)) {Y : Scheme.{u}}
    (r : Y ⟶ Spec c.C₂) (w₁ w₂ : Y ⟶ S') (hw₁ : r ≫ c.p₁ ≫ c.h = w₁)
    (hw₂ : r ≫ c.p₂ ≫ c.h = w₂) (hw : w₁ ≫ g = w₂ ≫ g) (h₁ : ⊤ ≤ w₁ ⁻¹ᵁ c.U)
    (h₂ : ⊤ ≤ w₂ ⁻¹ᵁ c.U) :
    (descentHom D w₁ w₂ hw).app ⊤ (pullbackAppTop w₁ (descentObj D) c.U h₁ x) =
      pullbackAppTop w₂ (descentObj D) c.U h₂ x := by
  have hp₁ : ⊤ ≤ (c.p₁ ≫ c.h) ⁻¹ᵁ c.U := c.top_le_of_comp c.p₁ _ rfl
  have hp₂ : ⊤ ≤ (c.p₂ ≫ c.h) ⁻¹ᵁ c.U := c.top_le_of_comp c.p₂ _ rfl
  rw [← pullbackTop_pullbackAppTop r (c.p₁ ≫ c.h) w₁ hw₁ _ c.U hp₁ h₁,
    ← pullbackTop_pullbackAppTop r (c.p₂ ≫ c.h) w₂ hw₂ _ c.U hp₂ h₂,
    ← descentHom_pullbackTop D r (c.p₁ ≫ c.h) (c.p₂ ≫ c.h) c.p_comp_h_comp w₁ w₂ hw₁ hw₂ hw,
    ← pullbackTop_pullbackAppTop c.p₁ c.h (c.p₁ ≫ c.h) rfl _ c.U c.top_le hp₁,
    ← pullbackTop_pullbackAppTop c.p₂ c.h (c.p₂ ≫ c.h) rfl _ c.U c.top_le hp₂]
  congr 1


/-- A section over `g⁻¹(j(Spec A))` whose inverse image to `Spec B` is invariant is compatible
with the descent datum. -/
lemma isDescentSection_of_isInvariant (x : Γ(descentObj D, c.U))
    (hx : c.IsInvariant D (pullbackAppTop c.h _ c.U c.top_le x)) :
    IsDescentSection D j.opensRange x := by
  have := c.isLocalIso
  intro Y f₁ f₂ hf
  set O := f₁ ⁻¹ᵁ c.U
  have hO₂ : O ≤ f₂ ⁻¹ᵁ c.U := preimage_le_of_comp_eq hf _
  -- local lifts
  have hlift : ∀ y ∈ O, ∃ (O₃ : Y.Opens) (r : O₃.toScheme ⟶ Spec c.C₂), y ∈ O₃ ∧ O₃ ≤ O ∧
      r ≫ c.p₁ ≫ c.h = O₃.ι ≫ f₁ ∧ r ≫ c.p₂ ≫ c.h = O₃.ι ≫ f₂ := by
    intro y hy
    have hy₁ : f₁ y ∈ Set.range c.h := c.coe_U ▸ hy
    have hy₂ : f₂ y ∈ Set.range c.h := c.coe_U ▸ hO₂ hy
    obtain ⟨O₁, a₁, hyO₁, ha₁⟩ := exists_lift_of_isLocalIso c.h f₁ y hy₁
    obtain ⟨O₂, a₂, hyO₂, ha₂⟩ := exists_lift_of_isLocalIso c.h f₂ y hy₂
    let O₃ := O₁ ⊓ O₂ ⊓ O
    have h₃₁ : O₃ ≤ O₁ := inf_le_left.trans inf_le_left
    have h₃₂ : O₃ ≤ O₂ := inf_le_left.trans inf_le_right
    let b₁ := Y.homOfLE h₃₁ ≫ a₁
    let b₂ := Y.homOfLE h₃₂ ≫ a₂
    have hb₁ : b₁ ≫ c.h = O₃.ι ≫ f₁ := by
      simp only [b₁, Category.assoc, ha₁, Scheme.homOfLE_ι_assoc]
    have hb₂ : b₂ ≫ c.h = O₃.ι ≫ f₂ := by
      simp only [b₂, Category.assoc, ha₂, Scheme.homOfLE_ι_assoc]
    have e : b₁ ≫ c.h ≫ g = b₂ ≫ c.h ≫ g := by
      rw [← Category.assoc, hb₁, ← Category.assoc, hb₂, Category.assoc, hf, Category.assoc]
    obtain ⟨r, hr₁, hr₂⟩ := c.exists_lift b₁ b₂ e
    exact ⟨O₃, r, ⟨⟨hyO₁, hyO₂⟩, hy⟩, inf_le_right, by rw [← Category.assoc, hr₁, hb₁],
      by rw [← Category.assoc, hr₂, hb₂]⟩
  choose O₃ r hyO₃ hO₃ hr₁ hr₂ using hlift
  rw [← sub_eq_zero]
  refine eq_zero_of_pullbackApp_eq_zero_of_le (fun y : O ↦ (O₃ y.1 y.2).ι) _ O
    (fun y hy ↦ ⟨⟨y, hy⟩, ⟨y, hyO₃ y hy⟩, rfl⟩) _ fun y ↦ ?_
  set ι := (O₃ y.1 y.2).ι
  have hO : ⊤ ≤ ι ⁻¹ᵁ O := fun z _ ↦ hO₃ y.1 y.2 z.2
  have hO' : ⊤ ≤ ι ⁻¹ᵁ (f₂ ⁻¹ᵁ c.U) := hO.trans (fun z hz ↦ hO₂ hz)
  have hq₁ : ⊤ ≤ (ι ≫ f₁) ⁻¹ᵁ c.U := hO
  have hq₂ : ⊤ ≤ (ι ≫ f₂) ⁻¹ᵁ c.U := hO'
  apply ((((Scheme.Modules.pullback ι).obj ((Scheme.Modules.pullback f₂).obj
    (descentObj D))).presheaf.map_bijective_of_eq (homOfLE hO) (top_le_iff.mp hO).symm).1)
  rw [map_zero]
  change pullbackAppTop ι _ O hO (_ - _) = 0
  rw [map_sub, sub_eq_zero]
  apply (ConcreteCategory.bijective_of_isIso
    ((pullbackCompIso' ι f₂ (ι ≫ f₂) rfl (descentObj D)).inv.app ⊤)).1
  rw [← pullbackAppTop_naturality, ← pullbackCompIso'_hom_app_pullbackAppTop ι f₁ (ι ≫ f₁) rfl
    _ c.U hq₁ hO, pullbackAppTop_map _ _ _ hO hO',
    pullbackCompIso'_inv_app_pullbackAppTop ι f₂ (ι ≫ f₂) rfl _ c.U hq₂ hO']
  have key := congr(Hom.app $(descentHom_pull D ι f₁ f₂ hf
    (by rw [Category.assoc, hf, Category.assoc])) ⊤
    (pullbackAppTop (ι ≫ f₁) (descentObj D) c.U hq₁ x))
  rw [Hom.comp_app_apply, Hom.comp_app_apply] at key
  rw [key]
  exact c.descentHom_app_top_of_isInvariant D x hx (r y.1 y.2) _ _ (hr₁ y.1 y.2) (hr₂ y.1 y.2)
    _ hq₁ hq₂


omit [IsOpenImmersion j] in
lemma inl_comm : c.φ ≫ c.inl = c.φ ≫ c.inr := tensorInl_comm c.φ c.φ

/-- The ring `B ⊗_A (B ⊗_A B)`. -/
noncomputable abbrev C₃ : CommRingCat.{u} := tensorObj c.φ (c.φ ≫ c.inl)

/-- `b ↦ b ⊗ 1 ⊗ 1`. -/
noncomputable abbrev ι₁ : c.B ⟶ c.C₃ := tensorInl c.φ (c.φ ≫ c.inl)

/-- `b ⊗ b' ↦ 1 ⊗ b ⊗ b'`. -/
noncomputable abbrev q₂₃ : c.C₂ ⟶ c.C₃ := tensorInr c.φ (c.φ ≫ c.inl)

omit [IsOpenImmersion j] in
lemma ι₁_comm : c.φ ≫ c.ι₁ = c.φ ≫ c.inl ≫ c.q₂₃ := by
  rw [← Category.assoc]; exact tensorInl_comm _ _

omit [IsOpenImmersion j] in
lemma ι₁_comm' : c.φ ≫ c.ι₁ = c.φ ≫ c.inr ≫ c.q₂₃ := by
  rw [c.ι₁_comm, ← Category.assoc, c.inl_comm, Category.assoc]

/-- `b ⊗ b' ↦ b ⊗ b' ⊗ 1`. -/
noncomputable irreducible_def q₁₂ : c.C₂ ⟶ c.C₃ :=
  (isPushout_tensorObj c.φ c.φ).desc c.ι₁ (c.inl ≫ c.q₂₃) c.ι₁_comm

/-- `b ⊗ b' ↦ b ⊗ 1 ⊗ b'`. -/
noncomputable irreducible_def q₁₃ : c.C₂ ⟶ c.C₃ :=
  (isPushout_tensorObj c.φ c.φ).desc c.ι₁ (c.inr ≫ c.q₂₃) c.ι₁_comm'

/-- The multiplication `B ⊗_A B ⟶ B`. -/
noncomputable irreducible_def μ : c.C₂ ⟶ c.B :=
  (isPushout_tensorObj c.φ c.φ).desc (𝟙 _) (𝟙 _) rfl

omit [IsOpenImmersion j] in
lemma inl_μ : c.inl ≫ c.μ = 𝟙 _ := by
  rw [μ_def]; exact IsPushout.inl_desc _ _ _ _

omit [IsOpenImmersion j] in
lemma inl_q₁₂ : c.inl ≫ c.q₁₂ = c.ι₁ := by
  rw [q₁₂_def]; exact IsPushout.inl_desc _ _ _ _

omit [IsOpenImmersion j] in
lemma inr_q₁₂ : c.inr ≫ c.q₁₂ = c.inl ≫ c.q₂₃ := by
  rw [q₁₂_def]; exact IsPushout.inr_desc _ _ _ _

omit [IsOpenImmersion j] in
lemma inl_q₁₃ : c.inl ≫ c.q₁₃ = c.ι₁ := by
  rw [q₁₃_def]; exact IsPushout.inl_desc _ _ _ _

omit [IsOpenImmersion j] in
lemma inr_q₁₃ : c.inr ≫ c.q₁₃ = c.inr ≫ c.q₂₃ := by
  rw [q₁₃_def]; exact IsPushout.inr_desc _ _ _ _

omit [IsOpenImmersion j] in
lemma SpecMap_q₁₂_p₁ : Spec.map c.q₁₂ ≫ c.p₁ = Spec.map c.ι₁ := by
  rw [← Spec.map_comp, c.inl_q₁₂]

omit [IsOpenImmersion j] in
lemma SpecMap_q₁₂_p₂ : Spec.map c.q₁₂ ≫ c.p₂ = Spec.map c.q₂₃ ≫ c.p₁ := by
  rw [← Spec.map_comp, ← Spec.map_comp, c.inr_q₁₂]

omit [IsOpenImmersion j] in
lemma SpecMap_q₁₃_p₁ : Spec.map c.q₁₃ ≫ c.p₁ = Spec.map c.ι₁ := by
  rw [← Spec.map_comp, c.inl_q₁₃]

omit [IsOpenImmersion j] in
lemma SpecMap_q₁₃_p₂ : Spec.map c.q₁₃ ≫ c.p₂ = Spec.map c.q₂₃ ≫ c.p₂ := by
  rw [← Spec.map_comp, ← Spec.map_comp, c.inr_q₁₃]


section Algebra

variable (D : pseudofunctorCat.DescentData (fun _ : Unit ↦ g))

omit [IsOpenImmersion j] in
lemma θ_smul (b : c.B) (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    c.θ D (b • n) = c.inl b • c.θ D n := by
  rw [θ_apply, θ_apply, pullbackTop_SpecMap_smul, Hom.app_smul_Spec]

omit [IsOpenImmersion j] in
lemma pb₂_smul (b : c.B) (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    c.pb₂ D (b • n) = c.inr b • c.pb₂ D n :=
  pullbackTop_SpecMap_smul _ _ _ _ _ _ _

instance (Y : Scheme.{u}) (f₁ f₂ : Y ⟶ S') (h : f₁ ≫ g = f₂ ≫ g) :
    IsIso (descentHom D f₁ f₂ h) :=
  inferInstanceAs (IsIso (D.hom (f₁ ≫ g) (i₁ := ()) (i₂ := ()) f₁ f₂ rfl h.symm))

omit [IsOpenImmersion j] in
lemma θ_injective [(descentObj D).IsQuasicoherent] : Function.Injective (c.θ D) := by
  intro n n' hnn'
  rw [θ_apply, θ_apply] at hnn'
  have h₁ := (ConcreteCategory.bijective_of_isIso
    ((descentHom D (c.p₁ ≫ c.h) (c.p₂ ≫ c.h) c.p_comp_h_comp).app ⊤)).1 hnn'
  rw [pullbackTop_apply, pullbackTop_apply] at h₁
  have h₂ := (ConcreteCategory.bijective_of_isIso
    ((pullbackCompIso' c.p₁ c.h (c.p₁ ≫ c.h) rfl (descentObj D)).inv.app ⊤)).1 h₁
  have h₃ := congrArg (pullbackSpecMapΓAddEquiv (c.inl)
    ((Scheme.Modules.pullback c.h).obj (descentObj D))) h₂
  rw [pullbackSpecMapΓAddEquiv_pullbackApp, pullbackSpecMapΓAddEquiv_pullbackApp] at h₃
  exact oneTmul_injective_of_comp_eq_id _ c.μ c.inl_μ _ h₃


omit [IsOpenImmersion j] in
lemma pullbackSpecMapΓAddEquiv_smul_pb₂ [(descentObj D).IsQuasicoherent] (b : c.B)
    (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    pullbackSpecMapΓAddEquiv (c.inr) ((Scheme.Modules.pullback c.h).obj (descentObj D))
      ((pullbackCompIso' c.p₂ c.h (c.p₂ ≫ c.h) rfl (descentObj D)).hom.app ⊤
        (c.inl b • c.pb₂ D n)) =
      c.inl b • oneTmul _ (c.inr) n := by
  rw [Hom.app_smul_Spec, pullbackSpecMapΓAddEquiv_smul]
  congr 1
  have e : (pullbackCompIso' c.p₂ c.h (c.p₂ ≫ c.h) rfl (descentObj D)).hom.app ⊤ (c.pb₂ D n) =
      pullbackApp c.p₂ _ ⊤ n :=
    iso_hom_app_inv_app (pullbackCompIso' c.p₂ c.h (c.p₂ ≫ c.h) rfl (descentObj D)) ⊤ _
  rw [e, pullbackSpecMapΓAddEquiv_pullbackApp]


omit [IsOpenImmersion j] in
lemma SpecMap_comp_h_comp_g {C : CommRingCat.{u}} (α : c.B ⟶ C) :
    (Spec.map α ≫ c.h) ≫ g = Spec.map (c.φ ≫ α) ≫ j := by
  rw [Category.assoc, c.comm, Spec.map_comp, Category.assoc]

/-- `Spec (B ⊗_A B ⊗_A B) ⟶ S'` through the first factor. -/
noncomputable abbrev w₁ : Spec c.C₃ ⟶ S' := Spec.map c.ι₁ ≫ c.h
/-- `Spec (B ⊗_A B ⊗_A B) ⟶ S'` through the second factor. -/
noncomputable abbrev w₂ : Spec c.C₃ ⟶ S' := Spec.map c.q₂₃ ≫ c.p₁ ≫ c.h
/-- `Spec (B ⊗_A B ⊗_A B) ⟶ S'` through the third factor. -/
noncomputable abbrev w₃ : Spec c.C₃ ⟶ S' := Spec.map c.q₂₃ ≫ c.p₂ ≫ c.h

omit [IsOpenImmersion j] in
lemma w₂_eq : c.w₂ = Spec.map (c.inl ≫ c.q₂₃) ≫ c.h := by
  rw [Spec.map_comp, Category.assoc]

omit [IsOpenImmersion j] in
lemma w₃_eq : c.w₃ = Spec.map (c.inr ≫ c.q₂₃) ≫ c.h := by
  rw [Spec.map_comp, Category.assoc]

omit [IsOpenImmersion j] in
lemma w₁_comp_g : c.w₁ ≫ g = c.w₂ ≫ g := by
  rw [c.w₂_eq, c.SpecMap_comp_h_comp_g, c.SpecMap_comp_h_comp_g, c.ι₁_comm]

omit [IsOpenImmersion j] in
lemma w₂_comp_g : c.w₂ ≫ g = c.w₃ ≫ g := by
  rw [c.w₂_eq, c.w₃_eq, c.SpecMap_comp_h_comp_g, c.SpecMap_comp_h_comp_g, ← Category.assoc,
    c.inl_comm, Category.assoc]

omit [IsOpenImmersion j] in
lemma e₁₂ : Spec.map c.q₁₂ ≫ c.p₂ ≫ c.h = c.w₂ := by
  rw [← Category.assoc, c.SpecMap_q₁₂_p₂, Category.assoc]

omit [IsOpenImmersion j] in
lemma e₁₃ : Spec.map c.q₁₃ ≫ c.p₂ ≫ c.h = c.w₃ := by
  rw [← Category.assoc, c.SpecMap_q₁₃_p₂, Category.assoc]

omit [IsOpenImmersion j] in
lemma pullbackTop_q₂₃_pb₂ (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl _ (c.pb₂ D n) =
      pullbackTop (Spec.map c.q₁₃) (c.p₂ ≫ c.h) c.w₃ c.e₁₃ _ (c.pb₂ D n) := by
  have h₁ : (Spec.map c.q₂₃ ≫ c.p₂) ≫ c.h = c.w₃ := Category.assoc _ _ _
  have h₂ : (Spec.map c.q₁₃ ≫ c.p₂) ≫ c.h = c.w₃ := (Category.assoc _ _ _).trans c.e₁₃
  rw [pb₂, pullbackTop_comp _ _ _ _ _ _ _ h₁, pullbackTop_comp _ _ _ _ _ _ _ h₂]
  exact pullbackTop_congr c.SpecMap_q₁₃_p₂.symm _ _ _ _ _ _

omit [IsOpenImmersion j] in
/-- (a) of the cocycle computation. -/
lemma smul_pullbackTop_pb₂ (b : c.B) (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    c.ι₁ b • pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl _ (c.pb₂ D n) =
      pullbackTop (Spec.map c.q₁₃) (c.p₂ ≫ c.h) c.w₃ c.e₁₃ _ (c.inl b • c.pb₂ D n) := by
  have hq : c.q₁₃ (c.inl b) = c.ι₁ b := by
    rw [← CategoryTheory.comp_apply, c.inl_q₁₃]
  rw [pullbackTop_SpecMap_smul c.q₁₃ (c.p₂ ≫ c.h) c.w₃ c.e₁₃ _ (c.inl b) (c.pb₂ D n), hq,
    c.pullbackTop_q₂₃_pb₂ D]

omit [IsOpenImmersion j] in
lemma e₁₂' : Spec.map c.q₁₂ ≫ c.p₁ ≫ c.h = c.w₁ := by
  rw [← Category.assoc, c.SpecMap_q₁₂_p₁]

omit [IsOpenImmersion j] in
lemma e₁₃' : Spec.map c.q₁₃ ≫ c.p₁ ≫ c.h = c.w₁ := by
  rw [← Category.assoc, c.SpecMap_q₁₃_p₁]

omit [IsOpenImmersion j] in
lemma pullbackTop_q₂₃_p₁ (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    pullbackTop (Spec.map c.q₂₃) (c.p₁ ≫ c.h) c.w₂ rfl _
        (pullbackTop c.p₁ c.h (c.p₁ ≫ c.h) rfl _ n) =
      pullbackTop (Spec.map c.q₁₂) (c.p₂ ≫ c.h) c.w₂ c.e₁₂ _ (c.pb₂ D n) := by
  have h₁ : (Spec.map c.q₂₃ ≫ c.p₁) ≫ c.h = c.w₂ := Category.assoc _ _ _
  have h₂ : (Spec.map c.q₁₂ ≫ c.p₂) ≫ c.h = c.w₂ := (Category.assoc _ _ _).trans c.e₁₂
  rw [pb₂, pullbackTop_comp _ _ _ _ _ _ _ h₁, pullbackTop_comp _ _ _ _ _ _ _ h₂]
  exact pullbackTop_congr c.SpecMap_q₁₂_p₂.symm _ _ _ _ _ _

omit [IsOpenImmersion j] in
/-- (b) of the cocycle computation. -/
lemma smul_pullbackTop_θ (b : c.B) (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    c.ι₁ b • pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl _ (c.θ D n) =
      (descentHom D c.w₂ c.w₃ c.w₂_comp_g).app ⊤
        (pullbackTop (Spec.map c.q₁₂) (c.p₂ ≫ c.h) c.w₂ c.e₁₂ _ (c.inl b • c.pb₂ D n)) := by
  have hq : c.q₁₂ (c.inl b) = c.ι₁ b := by
    rw [← CategoryTheory.comp_apply, c.inl_q₁₂]
  rw [θ_apply]
  rw [descentHom_pullbackTop D (Spec.map c.q₂₃) (c.p₁ ≫ c.h) (c.p₂ ≫ c.h)
      c.p_comp_h_comp c.w₂ c.w₃ rfl rfl c.w₂_comp_g]
  rw [pullbackTop_SpecMap_smul c.q₁₂ (c.p₂ ≫ c.h) c.w₂ c.e₁₂ _ (c.inl b) (c.pb₂ D n), hq,
    Hom.app_smul_Spec]
  exact congrArg (fun x ↦ c.ι₁ b • (descentHom D c.w₂ c.w₃ c.w₂_comp_g).app ⊤ x)
    (c.pullbackTop_q₂₃_p₁ D n)

omit [IsOpenImmersion j] in
lemma pullbackTop_q₁₂_p₁ (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    pullbackTop (Spec.map c.q₁₂) (c.p₁ ≫ c.h) c.w₁ c.e₁₂' _
        (pullbackTop c.p₁ c.h (c.p₁ ≫ c.h) rfl _ n) =
      pullbackTop (Spec.map c.q₁₃) (c.p₁ ≫ c.h) c.w₁ c.e₁₃' _
        (pullbackTop c.p₁ c.h (c.p₁ ≫ c.h) rfl _ n) := by
  have h₁ : (Spec.map c.q₁₂ ≫ c.p₁) ≫ c.h = c.w₁ := (Category.assoc _ _ _).trans c.e₁₂'
  have h₂ : (Spec.map c.q₁₃ ≫ c.p₁) ≫ c.h = c.w₁ := (Category.assoc _ _ _).trans c.e₁₃'
  rw [pullbackTop_comp _ _ _ _ _ _ _ h₁, pullbackTop_comp _ _ _ _ _ _ _ h₂]
  exact pullbackTop_congr (c.SpecMap_q₁₂_p₁.trans c.SpecMap_q₁₃_p₁.symm) _ _ _ _ _ _

omit [IsOpenImmersion j] in
/-- (c) of the cocycle computation: the cocycle condition. -/
lemma descentHom_pullbackTop_θ (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    (descentHom D c.w₂ c.w₃ c.w₂_comp_g).app ⊤
        (pullbackTop (Spec.map c.q₁₂) (c.p₂ ≫ c.h) c.w₂ c.e₁₂ _ (c.θ D n)) =
      pullbackTop (Spec.map c.q₁₃) (c.p₂ ≫ c.h) c.w₃ c.e₁₃ _ (c.θ D n) := by
  rw [θ_apply]
  rw [descentHom_pullbackTop D (Spec.map c.q₁₂) (c.p₁ ≫ c.h) (c.p₂ ≫ c.h)
      c.p_comp_h_comp c.w₁ c.w₂ c.e₁₂' c.e₁₂ c.w₁_comp_g,
    descentHom_pullbackTop D (Spec.map c.q₁₃) (c.p₁ ≫ c.h) (c.p₂ ≫ c.h)
      c.p_comp_h_comp c.w₁ c.w₃ c.e₁₃' c.e₁₃ (c.w₁_comp_g.trans c.w₂_comp_g)]
  rw [← Hom.comp_app_apply, descentHom_comp]
  exact congrArg ((descentHom D c.w₁ c.w₃ _).app ⊤) (c.pullbackTop_q₁₂_p₁ D n)

/-- The `A`-algebra structure on `B`. -/
noncomputable abbrev algebra : Algebra A c.B := c.φ.hom.toAlgebra

/-- The `A`-module structure on `Γ(Spec B, h^* E)`. -/
noncomputable abbrev moduleN : Module A Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤) :=
  Module.compHom _ c.φ.hom

/-- The `B`-module structure on `Γ(Spec (B ⊗_A B), p₂^* h^* E)` via the first factor. -/
noncomputable abbrev moduleBG :
    Module c.B Γ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D), ⊤) :=
  Module.compHom _ c.inl.hom

/-- The `A`-module structure on `Γ(Spec (B ⊗_A B), p₂^* h^* E)`. -/
noncomputable abbrev moduleAG :
    Module A Γ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D), ⊤) :=
  Module.compHom _ (c.φ ≫ c.inl).hom

attribute [local instance] algebra moduleN moduleBG moduleAG

omit [IsOpenImmersion j] in
instance : IsScalarTower A c.B Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤) :=
  ⟨fun a b n ↦ mul_smul (c.φ a) b n⟩

omit [IsOpenImmersion j] in
instance : IsScalarTower A c.B Γ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D), ⊤) :=
  ⟨fun a b z ↦ by
    change c.inl (c.φ a * b) • z = (c.φ ≫ c.inl) a • (c.inl b • z)
    rw [map_mul, mul_smul]; rfl⟩

/-- `θ` as a `B`-linear map. -/
noncomputable def θL : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤) →ₗ[c.B]
    Γ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D), ⊤) :=
  { toFun := c.θ D, map_add' := map_add _, map_smul' := c.θ_smul D }

/-- `p₂^*` as an `A`-linear map. -/
noncomputable def πL : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤) →ₗ[A]
    Γ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D), ⊤) :=
  { toFun := c.pb₂ D
    map_add' := map_add _
    map_smul' a n := by
      change c.pb₂ D (c.φ a • n) = (c.φ ≫ c.inl) a • c.pb₂ D n
      rw [c.pb₂_smul, c.inl_comm]; rfl }

omit [IsOpenImmersion j] in
lemma θL_apply (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    c.θL D n = c.θ D n := rfl

omit [IsOpenImmersion j] in
lemma πL_apply (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    c.πL D n = c.pb₂ D n := rfl

omit [IsOpenImmersion j] in
lemma smul_G (b : c.B) (z : Γ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D), ⊤)) :
    b • z = c.inl b • z := rfl

omit [IsOpenImmersion j] in
set_option backward.isDefEq.respectTransparency false in
lemma κ_bijective [(descentObj D).IsQuasicoherent] :
    Function.Bijective (LinearMap.liftBaseChange c.B (c.πL D)) := by
  let P := (Scheme.Modules.pullback c.h).obj (descentObj D)
  let e₁ := isoAppAddEquiv (pullbackCompIso' c.p₂ c.h (c.p₂ ≫ c.h) rfl (descentObj D)) ⊤
  let e₂ := pullbackSpecMapΓAddEquiv (c.inr) P
  have hcomp (y : c.B ⊗[A] Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
      e₂ (e₁ (LinearMap.liftBaseChange c.B (c.πL D) y)) = tensorCancelHom c.φ c.φ P.ΓSpec y := by
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | add y y' hy hy' => rw [map_add, map_add, map_add, hy, hy', map_add]
    | tmul b n =>
      rw [LinearMap.liftBaseChange_tmul, tensorCancelHom_tmul, smul_G, πL_apply]
      exact c.pullbackSpecMapΓAddEquiv_smul_pb₂ D b n
  have e : ⇑(LinearMap.liftBaseChange c.B (c.πL D)) =
      e₁.symm ∘ e₂.symm ∘ tensorCancelHom c.φ c.φ P.ΓSpec := by
    funext y
    simp only [Function.comp_apply, ← hcomp, AddEquiv.symm_apply_apply]
  rw [e]
  exact e₁.symm.bijective.comp (e₂.symm.bijective.comp (tensorCancelHom_bijective _ _ _))

/-- The map `B ⊗_A Γ(p₂^* h^* E) → Γ(w₃^* E)`, `b ⊗ z ↦ ι₁(b) q₂₃^* z`. -/
noncomputable def lam : c.B ⊗[A] Γ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D), ⊤) →+
    Γ((Scheme.Modules.pullback c.w₃).obj (descentObj D), ⊤) :=
  TensorProduct.liftAddHom
    { toFun b := (DistribSMul.toAddMonoidHom _ (c.ι₁ b)).comp
        (pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl (descentObj D)).hom
      map_zero' := by
        ext z
        change c.ι₁ 0 • pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl _ z = 0
        rw [map_zero, zero_smul]
      map_add' b b' := by
        ext z
        change c.ι₁ (b + b') • pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl _ z =
          c.ι₁ b • pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl _ z +
            c.ι₁ b' • pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl _ z
        rw [map_add, add_smul] }
    (fun a b z ↦ by
      change c.ι₁ (c.φ a * b) • pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl _ z =
        c.ι₁ b • pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl _ ((c.φ ≫ c.inl) a • z)
      have e₁ := pullbackTop_SpecMap_smul c.q₂₃ (c.p₂ ≫ c.h) c.w₃ rfl (descentObj D)
        ((c.φ ≫ c.inl) a) z
      have e₂ : c.q₂₃ ((c.φ ≫ c.inl) a) = c.ι₁ (c.φ a) := by
        rw [← CategoryTheory.comp_apply (c.φ ≫ c.inl) c.q₂₃, Category.assoc, ← c.ι₁_comm,
          CategoryTheory.comp_apply]
      rw [e₁, e₂, smul_smul, map_mul, mul_comm])

omit [IsOpenImmersion j] in
lemma lam_tmul (b : c.B) (z : Γ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D), ⊤)) :
    c.lam D (b ⊗ₜ z) = c.ι₁ b • pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl _ z :=
  TensorProduct.liftAddHom_tmul _ _ _ _

omit [IsOpenImmersion j] in
set_option backward.isDefEq.respectTransparency false in
lemma lam_injective [(descentObj D).IsQuasicoherent] : Function.Injective (c.lam D) := by
  let P' := (Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D)
  let e₃ := isoAppAddEquiv (pullbackCompIso' (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl
    (descentObj D)) ⊤
  let e₄ := pullbackSpecMapΓAddEquiv c.q₂₃ P'
  have hcomp (y : c.B ⊗[A] Γ((Scheme.Modules.pullback (c.p₂ ≫ c.h)).obj (descentObj D), ⊤)) :
      e₄ (e₃ (c.lam D y)) = tensorCancelHom c.φ (c.φ ≫ c.inl) P'.ΓSpec y := by
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | add y y' hy hy' => rw [map_add, map_add, map_add, hy, hy', map_add]
    | tmul b z =>
      have e₅ : e₃ (pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl _ z) =
          pullbackApp (Spec.map c.q₂₃) P' ⊤ z :=
        iso_hom_app_inv_app (pullbackCompIso' (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl
          (descentObj D)) ⊤ _
      have e₆ : e₃ (c.ι₁ b • pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl _ z) =
          c.ι₁ b • e₃ (pullbackTop (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl _ z) :=
        Hom.app_smul_Spec (pullbackCompIso' (Spec.map c.q₂₃) (c.p₂ ≫ c.h) c.w₃ rfl
          (descentObj D)).hom ⊤ _ _
      rw [lam_tmul, tensorCancelHom_tmul, e₆, e₅, pullbackSpecMapΓAddEquiv_smul,
        pullbackSpecMapΓAddEquiv_pullbackApp]
  intro y y' h
  apply (tensorCancelHom_bijective c.φ (c.φ ≫ c.inl) P'.ΓSpec).1
  rw [← hcomp, ← hcomp, h]

omit [IsOpenImmersion j] in
lemma liftBaseChange_πL_tmul (b : c.B)
    (n : Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    LinearMap.liftBaseChange c.B (c.πL D) (b ⊗ₜ n) = c.inl b • c.pb₂ D n :=
  by rw [LinearMap.liftBaseChange_tmul]; rfl

omit [IsOpenImmersion j] in
lemma lam_lTensor_θL (y : c.B ⊗[A] Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    c.lam D (((c.θL D).restrictScalars A).lTensor c.B y) =
      (descentHom D c.w₂ c.w₃ c.w₂_comp_g).app ⊤ (pullbackTop (Spec.map c.q₁₂) (c.p₂ ≫ c.h) c.w₂
        c.e₁₂ _ (LinearMap.liftBaseChange c.B (c.πL D) y)) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero, map_zero]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, map_add, map_add]
  | tmul b n =>
    rw [LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, lam_tmul,
      liftBaseChange_πL_tmul, θL_apply]
    exact c.smul_pullbackTop_θ D b n

omit [IsOpenImmersion j] in
lemma lam_lTensor_πL (y : c.B ⊗[A] Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤)) :
    c.lam D ((c.πL D).lTensor c.B y) =
      pullbackTop (Spec.map c.q₁₃) (c.p₂ ≫ c.h) c.w₃ c.e₁₃ _
        (LinearMap.liftBaseChange c.B (c.πL D) y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, map_add]
  | tmul b n =>
    rw [LinearMap.lTensor_tmul, lam_tmul, liftBaseChange_πL_tmul, πL_apply]
    exact c.smul_pullbackTop_pb₂ D b n

omit [IsOpenImmersion j] in
lemma lTensor_θL_eq_lTensor_πL [(descentObj D).IsQuasicoherent]
    (y : c.B ⊗[A] Γ((Scheme.Modules.pullback c.h).obj (descentObj D), ⊤))
    (hy : ∃ n, LinearMap.liftBaseChange c.B (c.πL D) y = c.θL D n) :
    ((c.θL D).restrictScalars A).lTensor c.B y = (c.πL D).lTensor c.B y := by
  obtain ⟨n, hn⟩ := hy
  apply c.lam_injective D
  rw [lam_lTensor_θL, lam_lTensor_πL, hn, θL_apply]
  exact c.descentHom_pullbackTop_θ D n

omit [IsOpenImmersion j] in
/-- VIII.1.6 for the chart: `B ⊗_A N₀ ≅ N` for the invariants `N₀` of the descent datum on
`N = Γ(Spec B, h^* E)`. -/
theorem bijective_liftBaseChange_invariants [(descentObj D).IsQuasicoherent] :
    Function.Bijective (LinearMap.liftBaseChange c.B
      (LinearMap.eqLocus ((c.θL D).restrictScalars A) (c.πL D)).subtype) := by
  have : Module.FaithfullyFlat A c.B := c.faithfullyFlat
  exact bijective_liftBaseChange_eqLocus (c.θL D) (c.πL D) (c.κ_bijective D) (c.θ_injective D)
    (c.lTensor_θL_eq_lTensor_πL D)

end Algebra

end AffineChart

end AlgebraicGeometry.Scheme.Modules
