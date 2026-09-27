/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# SGA 1, Exposé VIII, §1: faithfully flat descent of modules (affine case)

Theorem VIII.1.1 says that a faithfully flat quasi-compact morphism `S' → S` is an effective
descent morphism for quasi-coherent Modules. The proof in SGA reduces it to the affine
case `S = Spec A`, `S' = Spec B` (Lemmas VIII.1.4–1.6), which is what is formalized here.

A descent datum on a `B`-module `N` relative to `A → B` is, in SGA, an isomorphism
`φ : N ⊗_A B ≅ B ⊗_A N` of `B ⊗_A B`-modules satisfying the cocycle condition. Such a `φ`
is determined by the `B`-linear map `θ : N → B ⊗_A N`, `θ n = φ (n ⊗ 1)`, and the cocycle
condition evaluated on the generators `n ⊗ 1 ⊗ 1` of `N ⊗_A B ⊗_A B` is the coassociativity
of `θ`. We therefore record descent data as such coactions `θ`
(`ModuleDescentDatum`); the counit condition is the restriction of `φ` to the diagonal.
The comparison with SGA's formulation by `φ` is `descentIsoEquiv` (file `ModuleDescentIso`).

Main results:
* `range_mk_eq_eqLocus` (VIII.1.5): `N → B ⊗_A N ⇉ (B ⊗_A B) ⊗_A N` is an equalizer.
* `baseChange_injective_of_faithfullyFlat`, `exists_baseChange_eq_iff` (VIII.1.4): descent of
  homomorphisms.
* `ModuleDescentDatum.descentMap_bijective` (VIII.1.6): for a flat `A → B`, every
  descent datum on a `B`-module `N` is effective, with descended module the invariants
  `{x | θ x = 1 ⊗ x}`.
* `toDescentModule` and its instances `Full`, `Faithful`, `EssSurj`, `IsEquivalence`
  (VIII.1.2, VIII.1.3, VIII.1.1 in the affine case).

Mathlib proves the same equivalence in comonadic form (`comonadicExtendScalars`);
the proofs here are direct and give the explicit descended module of VIII.1.6.
-/

universe u v w

open TensorProduct CategoryTheory

namespace SGA.SGA1.ExposeVIII

section Datum

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
  (N : Type w) [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- VIII.1: a descent datum on the `B`-module `N` relative to `A → B`, written as the coaction
`θ : N → B ⊗_A N`, `θ n = φ (n ⊗ 1)`, of SGA's isomorphism `φ : N ⊗_A B ≅ B ⊗_A N`
(see the module docstring). `coassoc` is the cocycle condition `φ₁₃ = φ₂₃ ∘ φ₁₂` on the
generators `n ⊗ 1 ⊗ 1`; `counit` says that `φ` is the identity on the diagonal. -/
@[ext]
structure ModuleDescentDatum where
  /-- The coaction `θ n = φ (n ⊗ 1)`; it is `B`-linear for the action on the left factor. -/
  coaction : N →ₗ[B] B ⊗[A] N
  counit (n : N) : LinearMap.liftBaseChange B LinearMap.id (coaction n) = n
  coassoc (n : N) : (coaction.restrictScalars A).lTensor B (coaction n) =
    (TensorProduct.mk A B N 1).lTensor B (coaction n)

end Datum

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

section Canonical

variable (A B) in
/-- The canonical descent datum on `B ⊗_A M`: `θ (b ⊗ m) = b ⊗ 1 ⊗ m`, i.e. SGA's
`φ ((b ⊗ m) ⊗ c) = b ⊗ c ⊗ m`. -/
noncomputable def ModuleDescentDatum.canonical (M : Type w) [AddCommGroup M] [Module A M] :
    ModuleDescentDatum A B (B ⊗[A] M) where
  coaction := LinearMap.baseChange B (TensorProduct.mk A B M 1)
  counit y := by
    induction y with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp [TensorProduct.smul_tmul']
  coassoc y := by
    induction y with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp

@[simp]
lemma ModuleDescentDatum.canonical_coaction_tmul {M : Type w} [AddCommGroup M] [Module A M]
    (b : B) (m : M) :
    (ModuleDescentDatum.canonical A B M).coaction (b ⊗ₜ m) = b ⊗ₜ (1 ⊗ₜ m) := rfl

end Canonical

namespace ModuleDescentDatum

variable {N : Type w} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  (D : ModuleDescentDatum A B N)

lemma coaction_injective : Function.Injective D.coaction :=
  Function.LeftInverse.injective (g := LinearMap.liftBaseChange B LinearMap.id) D.counit

/-- The module of invariants `{x | θ x = 1 ⊗ x}`, which is SGA's `N` in VIII.1.6
(the `x` with `φ (x ⊗ 1) = 1 ⊗ x`). -/
def invariants : Submodule A N :=
  LinearMap.eqLocus (D.coaction.restrictScalars A) (TensorProduct.mk A B N 1)

lemma mem_invariants {n : N} : n ∈ D.invariants ↔ D.coaction n = 1 ⊗ₜ n := Iff.rfl

/-- The canonical homomorphism `B ⊗_A N₀ → N` from the invariants (VIII.1.6). -/
noncomputable def descentMap : B ⊗[A] D.invariants →ₗ[B] N :=
  LinearMap.liftBaseChange B D.invariants.subtype

@[simp]
lemma descentMap_tmul (b : B) (x : D.invariants) : D.descentMap (b ⊗ₜ x) = b • (x : N) := rfl

lemma coaction_descentMap (y : B ⊗[A] D.invariants) :
    D.coaction (D.descentMap y) = D.invariants.subtype.lTensor B y := by
  induction y with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul b x =>
    rw [descentMap_tmul, map_smul, (D.mem_invariants).1 x.2]
    simp [TensorProduct.smul_tmul']

/-- The canonical map `B ⊗_A N₀ → N` is compatible with the descent data. -/
lemma coaction_descentMap' (y : B ⊗[A] D.invariants) :
    D.coaction (D.descentMap y) = (D.descentMap.restrictScalars A).lTensor B
      ((canonical A B D.invariants).coaction y) := by
  rw [coaction_descentMap]
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b x => simp

/-- VIII.1.6: if `B` is flat over `A`, the canonical map `B ⊗_A N₀ → N` from the
invariants is bijective, i.e. every descent datum is effective. SGA assumes `B` faithfully
flat; flatness suffices for this step. -/
theorem descentMap_bijective [Module.Flat A B] : Function.Bijective D.descentMap := by
  constructor
  · intro y z h
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := B) D.invariants.subtype
      D.invariants.injective_subtype
    rw [← D.coaction_descentMap, ← D.coaction_descentMap, h]
  · intro n
    have hmem : D.coaction n ∈ LinearMap.eqLocus
        (TensorProduct.AlgebraTensorModule.lTensor B B (D.coaction.restrictScalars A))
        (TensorProduct.AlgebraTensorModule.lTensor B B (TensorProduct.mk A B N 1)) :=
      D.coassoc n
    rw [Module.Flat.eqLocus_lTensor_eq] at hmem
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, D.coaction_injective ((D.coaction_descentMap z).trans hz)⟩

/-- VIII.1.6, as a linear equivalence `B ⊗_A N₀ ≃ N`. -/
noncomputable def descentEquiv [Module.Flat A B] : B ⊗[A] D.invariants ≃ₗ[B] N :=
  LinearEquiv.ofBijective D.descentMap D.descentMap_bijective

@[simp]
lemma descentEquiv_apply [Module.Flat A B] (y : B ⊗[A] D.invariants) :
    D.descentEquiv y = D.descentMap y := rfl

end ModuleDescentDatum

section Canonical

variable {M : Type w} [AddCommGroup M] [Module A M]

lemma leftComm_one_tmul (y : B ⊗[A] M) :
    TensorProduct.leftComm A B B M (1 ⊗ₜ y) =
      (ModuleDescentDatum.canonical A B M).coaction y := by
  induction y with
  | zero => simp
  | add x y hx hy => rw [tmul_add, map_add, map_add, hx, hy]
  | tmul b m => simp

variable (A B M) in
/-- The inclusion of `M` into the invariants of the canonical descent datum on `B ⊗_A M`. -/
noncomputable def toCanonicalInvariants : M →ₗ[A] (ModuleDescentDatum.canonical A B M).invariants :=
  LinearMap.codRestrict _ (TensorProduct.mk A B M 1) fun m ↦ by
    simp [ModuleDescentDatum.mem_invariants]

@[simp]
lemma coe_toCanonicalInvariants_apply (m : M) :
    (toCanonicalInvariants A B M m : B ⊗[A] M) = 1 ⊗ₜ m := rfl

lemma toCanonicalInvariants_bijective [Module.FaithfullyFlat A B] :
    Function.Bijective (toCanonicalInvariants A B M) := by
  let D := ModuleDescentDatum.canonical A B M
  have hj (y : B ⊗[A] M) : D.descentMap ((toCanonicalInvariants A B M).lTensor B y) = y := by
    induction y with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m =>
      rw [LinearMap.lTensor_tmul, ModuleDescentDatum.descentMap_tmul,
        coe_toCanonicalInvariants_apply,
        smul_tmul', smul_eq_mul, mul_one]
  have hD := D.descentMap_bijective
  have hinj : Function.Injective ((toCanonicalInvariants A B M).lTensor B) :=
    Function.LeftInverse.injective hj
  have hsurj : Function.Surjective ((toCanonicalInvariants A B M).lTensor B) := fun z ↦
    ⟨D.descentMap z, hD.1 (hj _)⟩
  have := Module.FaithfullyFlat.lTensor_bijective_iff_bijective (N := M) (N' := D.invariants)
    A B (toCanonicalInvariants A B M)
  exact this.mp ⟨hinj, hsurj⟩

/-- For faithfully flat `A → B`, `M` is the module of invariants of the canonical descent
datum on `B ⊗_A M`. -/
noncomputable def canonicalInvariantsEquiv [Module.FaithfullyFlat A B] :
    M ≃ₗ[A] (ModuleDescentDatum.canonical A B M).invariants :=
  LinearEquiv.ofBijective _ toCanonicalInvariants_bijective

@[simp]
lemma coe_canonicalInvariantsEquiv_apply [Module.FaithfullyFlat A B] (m : M) :
    ((canonicalInvariantsEquiv (A := A) (B := B) m : B ⊗[A] M)) = 1 ⊗ₜ m := rfl

lemma range_mk_eq_invariants [Module.FaithfullyFlat A B] :
    LinearMap.range (TensorProduct.mk A B M 1) =
      (ModuleDescentDatum.canonical A B M).invariants := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    exact (toCanonicalInvariants A B M m).2
  · intro y hy
    obtain ⟨m, hm⟩ := toCanonicalInvariants_bijective.2 ⟨y, hy⟩
    exact ⟨m, congrArg Subtype.val hm⟩

variable (A B M) in
/-- The inverse image `M' → M''` along the first projection `p₁ : Spec (B ⊗_A B) → Spec B`,
i.e. the map `B ⊗_A M → (B ⊗_A B) ⊗_A M` induced by `b ↦ b ⊗ 1`. -/
noncomputable def rTensorIncludeLeft : B ⊗[A] M →ₗ[A] (B ⊗[A] B) ⊗[A] M :=
  (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := B)).toLinearMap.rTensor M

variable (A B M) in
/-- The inverse image `M' → M''` along the second projection, induced by `b ↦ 1 ⊗ b`. -/
noncomputable def rTensorIncludeRight : B ⊗[A] M →ₗ[A] (B ⊗[A] B) ⊗[A] M :=
  (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toLinearMap.rTensor M

@[simp]
lemma rTensorIncludeLeft_tmul (b : B) (m : M) :
    rTensorIncludeLeft A B M (b ⊗ₜ m) = (b ⊗ₜ 1) ⊗ₜ m := rfl

@[simp]
lemma rTensorIncludeRight_tmul (b : B) (m : M) :
    rTensorIncludeRight A B M (b ⊗ₜ m) = (1 ⊗ₜ b) ⊗ₜ m := rfl

lemma assoc_rTensorIncludeLeft (y : B ⊗[A] M) :
    TensorProduct.assoc A B B M (rTensorIncludeLeft A B M y) =
      (ModuleDescentDatum.canonical A B M).coaction y := by
  induction y with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul b m => simp

lemma assoc_rTensorIncludeRight (y : B ⊗[A] M) :
    TensorProduct.assoc A B B M (rTensorIncludeRight A B M y) = 1 ⊗ₜ y := by
  induction y with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, tmul_add, hx, hy]
  | tmul b m => simp

variable (A B M) in
/-- VIII.1.5: for a faithfully flat `A`-algebra `B` and an `A`-module `M`, the diagram
`M → B ⊗_A M ⇉ (B ⊗_A B) ⊗_A M` is exact: `m ↦ 1 ⊗ m` is injective
(`Module.FaithfullyFlat.tensorProduct_mk_injective`) and its image is the set where the two
inverse images agree. -/
theorem range_mk_eq_eqLocus [Module.FaithfullyFlat A B] :
    LinearMap.range (TensorProduct.mk A B M 1) =
      LinearMap.eqLocus (rTensorIncludeLeft A B M) (rTensorIncludeRight A B M) := by
  rw [range_mk_eq_invariants]
  ext y
  rw [ModuleDescentDatum.mem_invariants, LinearMap.mem_eqLocus,
    ← (TensorProduct.assoc A B B M).injective.eq_iff, assoc_rTensorIncludeLeft,
    assoc_rTensorIncludeRight]

end Canonical

section Hom

variable {M : Type w} [AddCommGroup M] [Module A M] {N : Type w} [AddCommGroup N] [Module A N]

/-- VIII.1.4, injectivity: for faithfully flat `A → B`, `u ↦ B ⊗ u` is injective on
`Hom_A(M, N)`. -/
theorem baseChange_injective_of_faithfullyFlat [Module.FaithfullyFlat A B] :
    Function.Injective (fun u : M →ₗ[A] N ↦ u.baseChange B) := by
  intro u v h
  ext m
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) N
  simpa using congr($h (1 ⊗ₜ m))

/-- A `B`-linear map `B ⊗_A M → B ⊗_A N` sending each `1 ⊗ m` to an invariant of the
canonical descent datum comes from an `A`-linear map `M → N` (unique by
`baseChange_injective_of_faithfullyFlat`). -/
theorem exists_baseChange_eq_of_mem_invariants [Module.FaithfullyFlat A B]
    (u' : B ⊗[A] M →ₗ[B] B ⊗[A] N)
    (h : ∀ m, u' (1 ⊗ₜ m) ∈ (ModuleDescentDatum.canonical A B N).invariants) :
    ∃ u : M →ₗ[A] N, u.baseChange B = u' := by
  let u : M →ₗ[A] N := (canonicalInvariantsEquiv (A := A) (B := B)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (u'.restrictScalars A ∘ₗ TensorProduct.mk A B M 1) h
  have hu (m : M) : (1 : B) ⊗ₜ[A] u m = u' (1 ⊗ₜ m) := by
    rw [← coe_canonicalInvariantsEquiv_apply (A := A) (B := B)]
    simp only [u, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨u, TensorProduct.AlgebraTensorModule.ext fun b m ↦ ?_⟩
  have hb : b ⊗ₜ[A] m = b • ((1 : B) ⊗ₜ[A] m) := by rw [smul_tmul', smul_eq_mul, mul_one]
  rw [LinearMap.baseChange_tmul, hb, map_smul, ← hu, smul_tmul', smul_eq_mul, mul_one]

/-- VIII.1.4: for a faithfully flat `A`-algebra `B`, a `B`-linear map `u' : B ⊗_A M → B ⊗_A N`
is of the form `B ⊗ u` if and only if its two inverse images to `A'' = B ⊗_A B` agree.
Writing `A'' ⊗_A M = B ⊗_A (B ⊗_A M)`, the inverse image by the second projection is
`B ⊗ u'` and the one by the first projection is its conjugate by the exchange of the two
factors `B`. -/
theorem exists_baseChange_eq_iff [Module.FaithfullyFlat A B]
    (u' : B ⊗[A] M →ₗ[B] B ⊗[A] N) :
    (∃ u : M →ₗ[A] N, u.baseChange B = u') ↔
      (TensorProduct.leftComm A B B N).toLinearMap ∘ₗ (u'.restrictScalars A).lTensor B ∘ₗ
        (TensorProduct.leftComm A B B M).toLinearMap = (u'.restrictScalars A).lTensor B := by
  constructor
  · rintro ⟨u, rfl⟩
    ext b c m
    simp
  · intro h
    refine exists_baseChange_eq_of_mem_invariants u' fun m ↦ ?_
    have := congr($h (1 ⊗ₜ (1 ⊗ₜ m)))
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      TensorProduct.leftComm_tmul, LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars] at this
    rw [ModuleDescentDatum.mem_invariants, ← leftComm_one_tmul]
    exact this

end Hom

section Category

variable (A B) in
/-- VIII.1: a `B`-module equipped with a descent datum relative to `A → B`. These are the
objects of the category of descent data for `Spec B → Spec A` and the fibered category of
quasi-coherent Modules. -/
structure DescentModule where
  /-- The underlying type. -/
  carrier : Type w
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module B carrier]
  [isModuleBase : Module A carrier]
  [isScalarTower : IsScalarTower A B carrier]
  /-- The descent datum. -/
  datum : ModuleDescentDatum A B carrier

namespace DescentModule

attribute [instance] isAddCommGroup isModule isModuleBase isScalarTower

instance : CoeSort (DescentModule.{u, v, w} A B) (Type w) := ⟨carrier⟩

/-- Morphisms of modules with descent data: `B`-linear maps compatible with the descent
data. -/
@[ext]
structure Hom (N₁ N₂ : DescentModule.{u, v, w} A B) where
  /-- The underlying `B`-linear map. -/
  toLinearMap : N₁ →ₗ[B] N₂
  comm (x : N₁) : N₂.datum.coaction (toLinearMap x) =
    (toLinearMap.restrictScalars A).lTensor B (N₁.datum.coaction x)

instance : Category (DescentModule.{u, v, w} A B) where
  Hom := Hom
  id N := ⟨LinearMap.id, fun x ↦ by
    rw [LinearMap.id_apply, LinearMap.restrictScalars_id, LinearMap.lTensor_id,
      LinearMap.id_apply]⟩
  comp f g := ⟨g.toLinearMap ∘ₗ f.toLinearMap, fun x ↦ by
    rw [LinearMap.comp_apply, g.comm, f.comm, LinearMap.restrictScalars_comp,
      LinearMap.lTensor_comp_apply]⟩

@[ext]
lemma hom_ext {N₁ N₂ : DescentModule.{u, v, w} A B} {f g : N₁ ⟶ N₂}
    (h : f.toLinearMap = g.toLinearMap) : f = g := Hom.ext h

@[simp]
lemma id_toLinearMap (N : DescentModule.{u, v, w} A B) :
    Hom.toLinearMap (𝟙 N) = LinearMap.id := rfl

@[simp]
lemma comp_toLinearMap {N₁ N₂ N₃ : DescentModule.{u, v, w} A B} (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃) :
    (f ≫ g).toLinearMap = g.toLinearMap ∘ₗ f.toLinearMap := rfl

/-- An isomorphism of modules with descent data from a linear equivalence compatible with
the descent data. -/
@[simps]
def isoMk {N₁ N₂ : DescentModule.{u, v, w} A B} (e : N₁ ≃ₗ[B] N₂)
    (comm : ∀ x, N₂.datum.coaction (e x) =
      (e.toLinearMap.restrictScalars A).lTensor B (N₁.datum.coaction x)) : N₁ ≅ N₂ where
  hom := ⟨e.toLinearMap, comm⟩
  inv := ⟨e.symm.toLinearMap, fun y ↦ by
    obtain ⟨x, rfl⟩ := e.surjective y
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, comm]
    rw [← LinearMap.lTensor_comp_apply]
    convert (LinearMap.id_apply (R := A) (N₁.datum.coaction x)).symm
    rw [← LinearMap.lTensor_id]
    congr 1
    ext z
    simp⟩
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

end DescentModule

variable (A B) in
/-- VIII.1: the functor `M ↦ B ⊗_A M`, with its canonical descent datum, from `A`-modules
to `B`-modules with descent data relative to `A → B`. -/
@[simps]
noncomputable def toDescentModule :
    ModuleCat.{max v w} A ⥤ DescentModule.{u, v, max v w} A B where
  obj M := ⟨B ⊗[A] M, ModuleDescentDatum.canonical A B M⟩
  map u := ⟨u.hom.baseChange B, fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b m => simp⟩
  map_id M := by
    ext : 1
    exact LinearMap.baseChange_id
  map_comp f g := by
    ext : 1
    exact LinearMap.baseChange_comp _ _

/-- VIII.1.2 (affine case), faithfulness. -/
instance [Module.FaithfullyFlat A B] : (toDescentModule.{u, v, w} A B).Faithful where
  map_injective {M N} f g h := by
    ext : 1
    exact baseChange_injective_of_faithfullyFlat (A := A) (B := B) congr(($h).toLinearMap)

/-- VIII.1.2 (affine case), fullness: a homomorphism of descent data between `B ⊗_A M` and
`B ⊗_A N` comes from a homomorphism `M → N`. -/
instance [Module.FaithfullyFlat A B] : (toDescentModule.{u, v, w} A B).Full where
  map_surjective {M N} f := by
    obtain ⟨u, hu⟩ := exists_baseChange_eq_of_mem_invariants (A := A) (B := B)
      (M := M) (N := N) f.toLinearMap fun m ↦ by
        rw [ModuleDescentDatum.mem_invariants]
        exact (f.comm (1 ⊗ₜ m)).trans rfl
    exact ⟨ModuleCat.ofHom u, by ext : 1; exact hu⟩

variable (A B) in
/-- VIII.1.3 (affine case): the descended module and the isomorphism of VIII.1.6. -/
noncomputable def descentModuleIso [Module.Flat A B] (N : DescentModule.{u, v, max v w} A B) :
    (toDescentModule.{u, v, w} A B).obj (ModuleCat.of A N.datum.invariants) ≅ N :=
  DescentModule.isoMk N.datum.descentEquiv fun y ↦ N.datum.coaction_descentMap' y

/-- VIII.1.3 (affine case): for a flat `A`-algebra `B` every descent datum on a `B`-module is
effective. -/
instance [Module.Flat A B] : (toDescentModule.{u, v, w} A B).EssSurj where
  mem_essImage N := ⟨_, ⟨descentModuleIso A B N⟩⟩

/-- VIII.1.1 (affine case): for a faithfully flat `A`-algebra `B`, `M ↦ B ⊗_A M` is an
equivalence between `A`-modules and `B`-modules with descent data relative to `A → B`. -/
instance [Module.FaithfullyFlat A B] : (toDescentModule.{u, v, w} A B).IsEquivalence where

end Category

/-- VIII.1.1 (affine case, mathlib's comonadic form): extension of scalars along a faithfully
flat ring map is comonadic, i.e. `A`-modules are equivalent to coalgebras for the comonad
`B ⊗_A -` on `B`-modules, which are the descent data of `ModuleDescentDatum`. -/
theorem nonempty_comonadicLeftAdjoint_extendScalars {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.FaithfullyFlat) :
    Nonempty (ComonadicLeftAdjoint (ModuleCat.extendScalars.{u, u, u} f)) :=
  ⟨comonadicExtendScalars hf⟩

end SGA.SGA1.ExposeVIII
