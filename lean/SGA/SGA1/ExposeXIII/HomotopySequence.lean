/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Galois.Full

/-!
# SGA 1, Exposé XIII, §4: exactness criteria for homotopy sequences

The proofs of XIII.4.1 and XIII.4.3 (copying X.1.4 and using V.6.8–V.6.11) turn the
exactness of `π₁(X_s̄) → π₁(X) → π₁(S) → 1` into statements about coverings:

* `π₁(X) → π₁(S)` is surjective iff connected coverings of `S` stay connected on `X`;
* the composite is trivial iff coverings of `S` become trivial on `X_s̄`;
* exactness in the middle holds iff every connected covering of `X` whose restriction
  to `X_s̄` has a section comes (as a connected component) from a covering of `S`;
* `π₁(X_s̄) → π₁(X)` is injective iff every connected covering of `X_s̄` is dominated by a
  connected component of the restriction of a covering of `X`.

Here these criteria are proved for arbitrary Galois categories `C`, `C'`, `C''` with fibre
functors `F`, `F'`, `F''` and functors `H : C ⥤ C'`, `H' : C' ⥤ C''` compatible with the fibre
functors up to isomorphism (cf. Stacks 0BN6). In SGA, `C`, `C'`, `C''` are the finite étale
coverings of `S`, `X` and `X_s̄`. The functors need not be exact: only the isomorphisms of fibre
functors are used. The maximal pro-`L` versions are in `SGA.SGA1.ExposeXIII.ProLQuotient`.
-/

universe u₁ u₂ u₃ u₄ u₅ u₆ w

namespace SGA.SGA1.ExposeXIII

open CategoryTheory Limits PreGaloisCategory

section AutHom

variable {C : Type u₁} [Category.{u₂} C] {C' : Type u₃} [Category.{u₄} C']
  {D : Type u₅} [Category.{u₆} D] {F : C ⥤ D} {F' : C' ⥤ D}

/-- The homomorphism `Aut F' →* Aut F` induced by a functor `H : C ⥤ C'` and an isomorphism
`H ⋙ F' ≅ F`. For fibre functors this is the map of fundamental groups induced by `H`. -/
def autHom (H : C ⥤ C') (u : H ⋙ F' ≅ F) : Aut F' →* Aut F where
  toFun σ := u.symm ≪≫ Functor.isoWhiskerLeft H σ ≪≫ u
  map_one' := Iso.ext <| NatTrans.ext <| funext fun X ↦ by
    change u.inv.app X ≫ 𝟙 _ ≫ u.hom.app X = 𝟙 _
    simp
  map_mul' σ τ := Iso.ext <| NatTrans.ext <| funext fun X ↦ by
    change u.inv.app X ≫ (τ.hom.app _ ≫ σ.hom.app _) ≫ u.hom.app X =
      (u.inv.app X ≫ τ.hom.app _ ≫ u.hom.app X) ≫ (u.inv.app X ≫ σ.hom.app _ ≫ u.hom.app X)
    simp

variable (H : C ⥤ C') (u : H ⋙ F' ≅ F)

@[simp]
lemma autHom_hom_app (σ : Aut F') (X : C) :
    (autHom H u σ).hom.app X = u.inv.app X ≫ σ.hom.app (H.obj X) ≫ u.hom.app X :=
  rfl

end AutHom

section Fibre

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w})
  [FiberFunctor F]

/-- In a Galois category an object is connected iff its fibre is nonempty and `Aut F` acts
transitively on it. -/
theorem isConnected_iff_nonempty_and_isPretransitive (X : C) :
    IsConnected X ↔ Nonempty (F.obj X) ∧ MulAction.IsPretransitive (Aut F) (F.obj X) := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨hne, htr⟩ ↦ ⟨?_, ?_⟩⟩
  · exact fun hin ↦ not_initial_of_inhabited F hne.some hin
  · intro Y i _ hni
    obtain ⟨y⟩ := (not_initial_iff_fiber_nonempty F Y).mp hni
    have hinj : Function.Injective (F.map i) :=
      ConcreteCategory.injective_of_mono_of_preservesPullback (F.map i)
    have hsurj : Function.Surjective (F.map i) := fun x ↦ by
      obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) (F.map i y) x
      exact ⟨σ • y, by rw [← mulAction_naturality, hσ]⟩
    have : IsIso (F.map i) := (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
    exact isIso_of_reflects_iso i F

/-- The fibre of a terminal object is a subsingleton. -/
lemma subsingleton_fiber_of_isTerminal {Z : C} (hZ : IsTerminal Z) : Subsingleton (F.obj Z) :=
  (Types.isTerminalEquivUnique _
    (IsTerminal.isTerminalObj (F ⋙ FintypeCat.incl) Z hZ)).instSubsingleton

/-- The point of the fibre of the terminal object. -/
noncomputable def fiberTerminalPt : F.obj (⊤_ C) :=
  (Types.isTerminalEquivUnique _
    (IsTerminal.isTerminalObj (F ⋙ FintypeCat.incl) _ terminalIsTerminal)).default

instance : Subsingleton (F.obj (⊤_ C)) := subsingleton_fiber_of_isTerminal F terminalIsTerminal

/-- An object whose fibre has exactly one element is terminal. -/
lemma isTerminal_of_subsingleton_fiber {Z : C} [Nonempty (F.obj Z)] [Subsingleton (F.obj Z)] :
    Nonempty (IsTerminal Z) := by
  have hb : Function.Bijective (F.map (terminal.from Z)) :=
    ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦
      ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : IsIso (F.map (terminal.from Z)) := (ConcreteCategory.isIso_iff_bijective _).mpr hb
  have : IsIso (terminal.from Z) := isIso_of_reflects_iso _ F
  exact ⟨terminalIsTerminal.ofIso (asIso (terminal.from Z)).symm⟩

/-- A monomorphism does not change stabilizers of points of fibres. -/
lemma stabilizer_map_of_mono {X Y : C} (i : X ⟶ Y) [Mono i] (x : F.obj X) :
    MulAction.stabilizer (Aut F) (F.map i x) = MulAction.stabilizer (Aut F) x := by
  have hinj : Function.Injective (F.map i) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback (F.map i)
  ext σ
  simp only [MulAction.mem_stabilizer_iff, mulAction_naturality]
  exact hinj.eq_iff

omit [GaloisCategory C] [FiberFunctor F] in
/-- A morphism does not decrease stabilizers of points of fibres. -/
lemma stabilizer_le_stabilizer_map {X Y : C} (f : X ⟶ Y) (x : F.obj X) :
    MulAction.stabilizer (Aut F) x ≤ MulAction.stabilizer (Aut F) (F.map f x) := by
  intro σ hσ
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  rw [mulAction_naturality, hσ]

/-- If `X` is connected and the stabilizer of `x ∈ F X` is contained in that of `y ∈ F Y`,
there is a morphism `X ⟶ Y` sending `x` to `y` (the fibre functor is full onto
`Aut F`-sets). -/
theorem exists_hom_of_stabilizer_le {X Y : C} [IsConnected X] (x : F.obj X) (y : F.obj Y)
    (h : MulAction.stabilizer (Aut F) x ≤ MulAction.stabilizer (Aut F) y) :
    ∃ f : X ⟶ Y, F.map f x = y := by
  choose g hg using fun z : F.obj X ↦ MulAction.exists_smul_eq (Aut F) x z
  have key : ∀ σ τ : Aut F, σ • x = τ • x → σ • y = τ • y := by
    intro σ τ hστ
    have hmem : τ⁻¹ * σ ∈ MulAction.stabilizer (Aut F) x := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hστ, inv_smul_smul]
    have hy := h hmem
    rw [MulAction.mem_stabilizer_iff, mul_smul] at hy
    calc σ • y = τ • (τ⁻¹ • σ • y) := by rw [smul_inv_smul]
      _ = τ • y := by rw [hy]
  let φ : F.obj X → F.obj Y := fun z ↦ g z • y
  have hφ : ∀ (σ : Aut F) z, φ (σ • z) = σ • φ z := by
    intro σ z
    simp only [φ, ← mul_smul]
    apply key
    rw [hg, mul_smul, hg]
  let f : (functorToAction F).obj X ⟶ (functorToAction F).obj Y :=
    { hom := FintypeCat.homMk φ
      comm := fun σ ↦ by
        ext z
        change φ (σ • z) = σ • φ z
        exact hφ σ z }
  obtain ⟨f', hf'⟩ := (functorToAction F).map_surjective f
  refine ⟨f', ?_⟩
  have hx : F.map f' x = φ x := by
    rw [← functorToAction_map, hf']
    rfl
  rw [hx]
  exact h ((MulAction.mem_stabilizer_iff).mpr (hg x))

/-- If `X` is connected and `x ∈ F X`, `y ∈ F Y` have the same stabilizer, there is a
monomorphism `X ⟶ Y` sending `x` to `y`. -/
theorem exists_mono_of_stabilizer_eq {X Y : C} [IsConnected X] (x : F.obj X) (y : F.obj Y)
    (h : MulAction.stabilizer (Aut F) x = MulAction.stabilizer (Aut F) y) :
    ∃ (f : X ⟶ Y), Mono f ∧ F.map f x = y := by
  obtain ⟨f, hf⟩ := exists_hom_of_stabilizer_le F x y h.le
  refine ⟨f, ?_, hf⟩
  have hinj : Function.Injective (F.map f) := by
    intro z₁ z₂ hz
    obtain ⟨σ₁, rfl⟩ := MulAction.exists_smul_eq (Aut F) x z₁
    obtain ⟨σ₂, rfl⟩ := MulAction.exists_smul_eq (Aut F) x z₂
    rw [← mulAction_naturality, ← mulAction_naturality, hf] at hz
    have hmem : σ₂⁻¹ * σ₁ ∈ MulAction.stabilizer (Aut F) y := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hz, inv_smul_smul]
    rw [← h, MulAction.mem_stabilizer_iff, mul_smul] at hmem
    calc σ₁ • x = σ₂ • (σ₂⁻¹ • σ₁ • x) := by rw [smul_inv_smul]
      _ = σ₂ • x := by rw [hmem]
  have : Mono (F.map f) := (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr hinj
  exact F.mono_of_mono_map this

/-- A point of a fibre fixed by `Aut F` lies on a section. -/
theorem exists_section_of_fixed {Y : C} (y : F.obj Y) (hy : ∀ σ : Aut F, σ • y = y) :
    ∃ s : ⊤_ C ⟶ Y, y ∈ Set.range (F.map s) := by
  obtain ⟨Z, i, z, hz, _, _⟩ := fiber_in_connected_component F Y y
  have hinj : Function.Injective (F.map i) :=
    ConcreteCategory.injective_of_mono_of_preservesPullback (F.map i)
  have hfix : ∀ σ : Aut F, σ • z = z := fun σ ↦ hinj (by rw [← mulAction_naturality, hz, hy])
  have : Subsingleton (F.obj Z) := ⟨fun a b ↦ by
    obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (Aut F) z a
    obtain ⟨τ, rfl⟩ := MulAction.exists_smul_eq (Aut F) z b
    rw [hfix, hfix]⟩
  have : Nonempty (F.obj Z) := ⟨z⟩
  obtain ⟨hZ⟩ := isTerminal_of_subsingleton_fiber F (Z := Z)
  refine ⟨hZ.from _ ≫ i, fiberTerminalPt F, ?_⟩
  rw [Functor.map_comp, FintypeCat.comp_apply,
    Subsingleton.elim (F.map (hZ.from _) (fiberTerminalPt F)) z, hz]

/-- The fibre of an object has a point fixed by `Aut F` iff the object has a section. -/
theorem nonempty_section_iff {Y : C} :
    Nonempty (⊤_ C ⟶ Y) ↔ ∃ y : F.obj Y, ∀ σ : Aut F, σ • y = y := by
  refine ⟨fun ⟨s⟩ ↦ ⟨F.map s (fiberTerminalPt F), fun σ ↦ ?_⟩, fun ⟨y, hy⟩ ↦ ?_⟩
  · rw [mulAction_naturality, Subsingleton.elim (σ • fiberTerminalPt F) (fiberTerminalPt F)]
  · obtain ⟨s, -⟩ := exists_section_of_fixed F y hy
    exact ⟨s⟩

/-- An object of a Galois category is *trivial* (a completely decomposed covering in SGA) if
all its connected subobjects are terminal, i.e. it is a finite sum of copies of the final
object. -/
def IsTrivialObject {C : Type u₁} [Category.{u₂} C] (Y : C) : Prop :=
  ∀ ⦃Z : C⦄ (i : Z ⟶ Y), Mono i → IsConnected Z → Nonempty (IsTerminal Z)

/-- An object is trivial iff `Aut F` acts trivially on its fibre. -/
theorem isTrivialObject_iff (Y : C) :
    IsTrivialObject Y ↔ ∀ (σ : Aut F) (y : F.obj Y), σ • y = y := by
  refine ⟨fun hY σ y ↦ ?_, fun hY Z i _ _ ↦ ?_⟩
  · obtain ⟨Z, i, z, hz, hc, hm⟩ := fiber_in_connected_component F Y y
    obtain ⟨hZ⟩ := hY i hm hc
    have := subsingleton_fiber_of_isTerminal F hZ
    rw [← hz, mulAction_naturality, Subsingleton.elim (σ • z) z]
  · have hinj : Function.Injective (F.map i) :=
      ConcreteCategory.injective_of_mono_of_preservesPullback (F.map i)
    obtain ⟨z⟩ := nonempty_fiber_of_isConnected F Z
    have : Subsingleton (F.obj Z) := ⟨fun a b ↦ by
      obtain ⟨σ, rfl⟩ := MulAction.exists_smul_eq (Aut F) z a
      obtain ⟨τ, rfl⟩ := MulAction.exists_smul_eq (Aut F) z b
      apply hinj
      rw [← mulAction_naturality, ← mulAction_naturality, hY, hY]⟩
    exact isTerminal_of_subsingleton_fiber F

/-- The image of the point of the fibre of the final object under the `j`-th inclusion into a
finite sum of copies of the final object; every point of the fibre of the sum is of this form. -/
lemma exists_eq_map_ι_fiberTerminalPt {n : ℕ} (x : F.obj (∐ fun _ : Fin n ↦ ⊤_ C)) :
    ∃ j, F.map (Sigma.ι (fun _ : Fin n ↦ ⊤_ C) j) (fiberTerminalPt F) = x := by
  obtain ⟨⟨j⟩, t, ht⟩ := Limits.FintypeCat.jointly_surjective
    (Discrete.functor (fun _ : Fin n ↦ ⊤_ C) ⋙ F) _
    (isColimitOfPreserves F (colimit.isColimit _)) x
  exact ⟨j, (congrArg _ (Subsingleton.elim _ _)).trans ht⟩

/-- An object is trivial iff it is a finite sum of copies of the final object (a trivial
covering in the sense of V.6). -/
theorem isTrivialObject_iff_exists_iso (Y : C) :
    IsTrivialObject Y ↔ ∃ n : ℕ, Nonempty (Y ≅ ∐ fun _ : Fin n ↦ ⊤_ C) := by
  let F₀ : C ⥤ FintypeCat.{u₂} := CategoryTheory.GaloisCategory.getFiberFunctor C
  have : FiberFunctor F₀ :=
    inferInstanceAs (FiberFunctor (CategoryTheory.GaloisCategory.getFiberFunctor C))
  rw [isTrivialObject_iff F₀]
  constructor
  · intro h
    choose s hs using fun y : F₀.obj Y ↦ exists_section_of_fixed F₀ y (h · y)
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (F₀.obj Y)
    let d : (∐ fun _ : Fin n ↦ ⊤_ C) ⟶ Y := Sigma.desc fun j ↦ s (e.symm j)
    have hd (j : Fin n) :
        F₀.map d (F₀.map (Sigma.ι (fun _ : Fin n ↦ ⊤_ C) j) (fiberTerminalPt F₀)) = e.symm j := by
      rw [← FintypeCat.comp_apply, ← F₀.map_comp, Sigma.ι_desc]
      obtain ⟨t, ht⟩ := hs (e.symm j)
      rw [Subsingleton.elim (fiberTerminalPt F₀) t]
      exact ht
    have hbij : Function.Bijective (F₀.map d) := by
      constructor
      · intro a b hab
        obtain ⟨i, rfl⟩ := exists_eq_map_ι_fiberTerminalPt F₀ a
        obtain ⟨j, rfl⟩ := exists_eq_map_ι_fiberTerminalPt F₀ b
        rw [hd, hd, e.symm.injective.eq_iff] at hab
        rw [hab]
      · intro y
        exact ⟨_, (hd (e y)).trans (e.symm_apply_apply y)⟩
    have : IsIso (F₀.map d) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    have : IsIso d := isIso_of_reflects_iso d F₀
    exact ⟨n, ⟨(asIso d).symm⟩⟩
  · rintro ⟨n, ⟨e⟩⟩ σ y
    obtain ⟨j, hj⟩ := exists_eq_map_ι_fiberTerminalPt F₀ (F₀.map e.hom y)
    have hy : y = F₀.map e.inv
        (F₀.map (Sigma.ι (fun _ : Fin n ↦ ⊤_ C) j) (fiberTerminalPt F₀)) := by
      rw [hj, ← FintypeCat.comp_apply, ← F₀.map_comp, e.hom_inv_id, F₀.map_id]
      rfl
    rw [hy, mulAction_naturality, mulAction_naturality,
      Subsingleton.elim (σ • fiberTerminalPt F₀) (fiberTerminalPt F₀)]

omit [GaloisCategory C] [FiberFunctor F] in
/-- An automorphism of a fibre functor acting trivially on every fibre is the identity. -/
lemma eq_one_of_forall_smul_eq {σ : Aut F} (h : ∀ (X : C) (x : F.obj X), σ • x = x) : σ = 1 :=
  Iso.ext <| NatTrans.ext <| funext fun X ↦ FintypeCat.hom_ext _ _ (h X)

/-! ### Topological lemmas on `Aut F` -/

/-- If `h : G →* Aut F` is continuous on a compact group and `U` is an open subgroup of `G`
containing `ker h`, some pointed Galois object has a stabilizer whose preimage lies in `U`. -/
theorem exists_pointedGaloisObject_comap_le {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] (h : G →* Aut F) (hh : Continuous h) (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (hker : h.ker ≤ U) :
    ∃ A : PointedGaloisObject F, (MulAction.stabilizer (Aut F) A.pt).comap h ≤ U := by
  have hT : IsClosed (h '' (U : Set G)ᶜ) :=
    (hU.isClosed_compl.isCompact.image hh).isClosed
  have h1 : (1 : Aut F) ∉ h '' (U : Set G)ᶜ := by
    rintro ⟨g, hg, hg1⟩
    exact hg (hker hg1)
  obtain ⟨A, -, hA⟩ :=
    (nhds_one_has_basis_stabilizers F).mem_iff.mp (hT.isOpen_compl.mem_nhds h1)
  refine ⟨A, fun g hg ↦ ?_⟩
  by_contra hgU
  exact hA hg ⟨g, hgU, rfl⟩

/-- If `h : G →* Aut F` is continuous on a compact group and `U` is an open subgroup of `G`
containing `ker h`, then `U` is the preimage of an open subgroup of `Aut F`. -/
theorem exists_openSubgroup_comap_eq {G : Type*} [Group G] [TopologicalSpace G]
    [CompactSpace G] (h : G →* Aut F) (hh : Continuous h) (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (hker : h.ker ≤ U) :
    ∃ W : OpenSubgroup (Aut F), W.toSubgroup.comap h = U := by
  obtain ⟨A, hA⟩ := exists_pointedGaloisObject_comap_le F h hh U hU hker
  have := A.isGalois
  have := stabilizer_normal_of_isGalois F A.obj A.pt
  let V := MulAction.stabilizer (Aut F) A.pt
  refine ⟨⟨V ⊔ U.map h, Subgroup.isOpen_mono le_sup_left (stabilizer_isOpen _ _)⟩,
    le_antisymm (fun g hg ↦ ?_) (fun g hg ↦ Subgroup.mem_sup_right (Subgroup.mem_map_of_mem h hg))⟩
  have hg' : h g ∈ ((V ⊔ U.map h : Subgroup (Aut F)) : Set (Aut F)) := hg
  rw [Subgroup.normal_mul] at hg'
  obtain ⟨v, hv, _, ⟨g', hg'U, rfl⟩, hvg⟩ := hg'
  have hmem : g * g'⁻¹ ∈ U := hA (by
    change h (g * g'⁻¹) ∈ V
    rw [map_mul, map_inv, ← hvg, mul_inv_cancel_right]
    exact hv)
  simpa using U.mul_mem hmem hg'U

/-- A closed subgroup of `Aut F` is separated from any element outside it by an open
subgroup. -/
theorem exists_openSubgroup_le_notMem (I : Subgroup (Aut F)) (hI : IsClosed (I : Set (Aut F)))
    {σ : Aut F} (hσ : σ ∉ I) : ∃ U : OpenSubgroup (Aut F), I ≤ U ∧ σ ∉ U := by
  have hO : (fun τ ↦ σ * τ) ⁻¹' (I : Set (Aut F))ᶜ ∈ nhds (1 : Aut F) :=
    (hI.isOpen_compl.preimage (continuous_const_mul σ)).mem_nhds (by simpa using hσ)
  obtain ⟨A, -, hA⟩ := (nhds_one_has_basis_stabilizers F).mem_iff.mp hO
  have := A.isGalois
  have := stabilizer_normal_of_isGalois F A.obj A.pt
  refine ⟨⟨I ⊔ MulAction.stabilizer (Aut F) A.pt,
    Subgroup.isOpen_mono le_sup_right (stabilizer_isOpen _ _)⟩, le_sup_left, fun hmem ↦ ?_⟩
  have hmem' : σ ∈ ((I ⊔ MulAction.stabilizer (Aut F) A.pt : Subgroup (Aut F)) :
      Set (Aut F)) := hmem
  rw [Subgroup.mul_normal] at hmem'
  obtain ⟨i, hi, v, hv, rfl⟩ := hmem'
  have := hA (Subgroup.inv_mem _ hv)
  simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe, mul_inv_cancel_right] at this
  exact this hi

/-- Every open subgroup of `Aut F` is the stabilizer of a point of the fibre of a connected
object. -/
theorem exists_isConnected_stabilizer_eq (V : OpenSubgroup (Aut F)) :
    ∃ (X : C) (x : F.obj X), IsConnected X ∧ MulAction.stabilizer (Aut F) x = V := by
  let F₀ : C ⥤ FintypeCat.{u₁} := F ⋙ FintypeCat.uSwitch.{w, u₁}
  have : FiberFunctor F₀ := FiberFunctor.comp_right _
  let e : Aut F ≃ₜ* Aut F₀ :=
    autEquivAutWhiskerRight F FintypeCat.uSwitchEquivalence.{w, u₁}.fullyFaithfulFunctor
  let V₀ : OpenSubgroup (Aut F₀) :=
    V.comap (e.symm : Aut F₀ →* Aut F) e.symm.continuous
  obtain ⟨X, ⟨φ⟩⟩ := exists_lift_of_quotient_openSubgroup V₀
  have hφ (τ : Aut F₀) (z : F₀.obj X) : φ.hom.hom (τ • z) = τ • φ.hom.hom z := by
    exact ConcreteCategory.congr_hom (φ.hom.comm τ) z
  have hinj : Function.Injective φ.hom.hom := fun a b hab ↦ by
    have := congrArg φ.inv.hom hab
    rwa [← FintypeCat.comp_apply, ← Action.comp_hom, φ.hom_inv_id, ← FintypeCat.comp_apply,
      ← Action.comp_hom, φ.hom_inv_id] at this
  have hsurj : Function.Surjective φ.hom.hom := fun y ↦ ⟨φ.inv.hom y, by
    rw [← FintypeCat.comp_apply, ← Action.comp_hom, φ.inv_hom_id]; rfl⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : F₀.obj X,
      φ.hom.hom x₀ = (QuotientGroup.mk 1 : Aut F₀ ⧸ V₀.toSubgroup) :=
    hsurj _
  have hstab₀ : MulAction.stabilizer (Aut F₀) x₀ = V₀ := by
    ext τ
    rw [MulAction.mem_stabilizer_iff,
      show τ • x₀ = x₀ ↔ φ.hom.hom (τ • x₀) = φ.hom.hom x₀ from hinj.eq_iff.symm, hφ, hx₀]
    exact (Subgroup.ext_iff.mp (MulAction.stabilizer_quotient V₀.toSubgroup) τ)
  let x : F.obj X := (F.obj X).uSwitchEquiv x₀
  have hsmul (σ : Aut F) : σ • x = (F.obj X).uSwitchEquiv (show F₀.obj X from e σ • x₀) :=
    FintypeCat.uSwitchEquiv_naturality (σ.hom.app X) x₀
  refine ⟨X, x, ?_, ?_⟩
  · rw [isConnected_iff_nonempty_and_isPretransitive F₀]
    refine ⟨⟨x₀⟩, ⟨fun a b ↦ ?_⟩⟩
    obtain ⟨g₁, hg₁⟩ := QuotientGroup.mk_surjective (φ.hom.hom a)
    obtain ⟨g₂, hg₂⟩ := QuotientGroup.mk_surjective (φ.hom.hom b)
    refine ⟨g₂ * g₁⁻¹, hinj ?_⟩
    rw [hφ, ← hg₁, ← hg₂]
    exact (MulAction.Quotient.smul_mk _ _ _).trans (by rw [smul_eq_mul, inv_mul_cancel_right])
  · ext σ
    have h1 : σ • x = x ↔ e σ • x₀ = x₀ := by
      rw [hsmul]
      exact (F.obj X).uSwitchEquiv.injective.eq_iff
    have h2 : e σ • x₀ = x₀ ↔ e σ ∈ V₀ := by
      rw [← MulAction.mem_stabilizer_iff, hstab₀]
      rfl
    rw [MulAction.mem_stabilizer_iff, h1, h2]
    change e.symm (e σ) ∈ V ↔ σ ∈ V
    simp

end Fibre

section Exactness

variable {C : Type u₁} [Category.{u₂} C] {C' : Type u₃} [Category.{u₄} C']
  {F : C ⥤ FintypeCat.{w}} {F' : C' ⥤ FintypeCat.{w}} (H : C ⥤ C') (u : H ⋙ F' ≅ F)

/-- The map induced on fundamental groups is continuous. -/
theorem continuous_autHom : Continuous (autHom H u) := by
  apply continuous_induced_rng.2
  refine continuous_pi fun X ↦ ?_
  have : (fun σ ↦ (autEmbedding F ∘ autHom H u) σ X) =
      (fun τ : Aut (F'.obj (H.obj X)) ↦ (u.app X).symm ≪≫ τ ≪≫ u.app X) ∘
        (fun σ : Aut F' ↦ autEmbedding F' σ (H.obj X)) := by
    funext σ
    exact Iso.ext rfl
  rw [this]
  exact continuous_of_discreteTopology.comp ((continuous_apply _).comp continuous_induced_dom)

/-- The bijection of fibres `F' (H X) ≃ F X` given by `u`. -/
def fiberEquiv (X : C) : F'.obj (H.obj X) ≃ F.obj X :=
  FintypeCat.equivEquivIso.symm (u.app X)

lemma fiberEquiv_apply {X : C} (y : F'.obj (H.obj X)) : fiberEquiv H u X y = u.hom.app X y :=
  rfl

lemma fiberEquiv_symm_apply {X : C} (x : F.obj X) : (fiberEquiv H u X).symm x = u.inv.app X x :=
  rfl

lemma autHom_smul (σ : Aut F') {X : C} (x : F.obj X) :
    autHom H u σ • x = fiberEquiv H u X (σ • (fiberEquiv H u X).symm x) :=
  rfl

lemma fiberEquiv_smul (σ : Aut F') {X : C} (y : F'.obj (H.obj X)) :
    fiberEquiv H u X (σ • y) = autHom H u σ • fiberEquiv H u X y := by
  rw [autHom_smul, Equiv.symm_apply_apply]

lemma smul_fiberEquiv_symm (σ : Aut F') {X : C} (x : F.obj X) :
    σ • (fiberEquiv H u X).symm x = (fiberEquiv H u X).symm (autHom H u σ • x) := by
  rw [Equiv.eq_symm_apply, fiberEquiv_smul, Equiv.apply_symm_apply]

lemma stabilizer_fiberEquiv_symm {X : C} (x : F.obj X) :
    MulAction.stabilizer (Aut F') ((fiberEquiv H u X).symm x) =
      (MulAction.stabilizer (Aut F) x).comap (autHom H u) := by
  ext σ
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, smul_fiberEquiv_symm,
    Equiv.symm_apply_eq, Equiv.apply_symm_apply]

/-- Elements of the kernel of `Aut F' → Aut F` act trivially on the fibres of objects coming
from `C`. -/
lemma fiberEquiv_naturality {X Y : C} (j : X ⟶ Y) (w : F'.obj (H.obj X)) :
    fiberEquiv H u Y (F'.map (H.map j) w) = F.map j (fiberEquiv H u X w) :=
  ConcreteCategory.congr_hom (u.hom.naturality j) w

lemma smul_eq_of_mem_ker {σ : Aut F'} (hσ : σ ∈ (autHom H u).ker) {X : C}
    (z : F'.obj (H.obj X)) : σ • z = z := by
  apply (fiberEquiv H u X).injective
  rw [fiberEquiv_smul, (MonoidHom.mem_ker).mp hσ, one_smul]

variable [GaloisCategory C] [FiberFunctor F] [GaloisCategory C'] [FiberFunctor F']

/-- XIII.4.1, first step of the proof (V.6.9): the map of fundamental groups induced by `H` is
surjective iff `H` sends connected objects to connected objects. -/
theorem autHom_surjective_iff :
    Function.Surjective (autHom H u) ↔ ∀ X : C, IsConnected X → IsConnected (H.obj X) := by
  constructor
  · intro hs X _
    rw [isConnected_iff_nonempty_and_isPretransitive F']
    refine ⟨⟨(fiberEquiv H u X).symm (nonempty_fiber_of_isConnected F X).some⟩,
      ⟨fun a b ↦ ?_⟩⟩
    obtain ⟨τ, hτ⟩ :=
      MulAction.exists_smul_eq (Aut F) (fiberEquiv H u X a) (fiberEquiv H u X b)
    obtain ⟨σ, rfl⟩ := hs τ
    refine ⟨σ, (fiberEquiv H u X).injective ?_⟩
    rw [fiberEquiv_smul, hτ]
  · intro hc
    let : ∀ X : C, MulAction (Aut F') (F.obj X) := fun X ↦ MulAction.compHom _ (autHom H u)
    have : IsNaturalSMul F (Aut F') :=
      ⟨fun σ X Y f x ↦ (mulAction_naturality F (autHom H u σ) f x).symm⟩
    have (X : C) : ContinuousSMul (Aut F') (F.obj X) :=
      ⟨(continuous_smul (M := Aut F) (X := F.obj X)).comp
        ((continuous_autHom H u).prodMap continuous_id)⟩
    have hsurj := toAut_surjective_of_isPretransitive F (Aut F') fun X _ ↦ by
      have := hc X inferInstance
      refine ⟨fun a b ↦ ?_⟩
      obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F')
        ((fiberEquiv H u X).symm a) ((fiberEquiv H u X).symm b)
      refine ⟨σ, ?_⟩
      rw [smul_fiberEquiv_symm] at hσ
      exact (fiberEquiv H u X).symm.injective hσ
    have heq : toAut F (Aut F') = autHom H u := by
      ext σ X x
      rfl
    rwa [heq] at hsurj

variable {C'' : Type u₅} [Category.{u₆} C''] [GaloisCategory C'']
  {F'' : C'' ⥤ FintypeCat.{w}} [FiberFunctor F''] (H' : C' ⥤ C'') (u' : H' ⋙ F'' ≅ F')

omit [GaloisCategory C] [FiberFunctor F] [GaloisCategory C'] [FiberFunctor F'] in
/-- XIII.4.0, `vu = 1`: the composite `Aut F'' → Aut F' → Aut F` is trivial iff every
object of `C` becomes trivial (completely decomposed) in `C''`. -/
theorem autHom_comp_eq_one_iff :
    (autHom H u).comp (autHom H' u') = 1 ↔ ∀ X : C, IsTrivialObject (H'.obj (H.obj X)) := by
  simp_rw [isTrivialObject_iff F'']
  constructor
  · intro h X σ y
    have h1 : autHom H u (autHom H' u' σ) = 1 := DFunLike.congr_fun h σ
    apply (fiberEquiv H' u' (H.obj X)).injective
    apply (fiberEquiv H u X).injective
    rw [fiberEquiv_smul, fiberEquiv_smul, h1, one_smul]
  · intro h
    ext1 σ
    refine eq_one_of_forall_smul_eq F fun X x ↦ ?_
    change autHom H u (autHom H' u' σ) • x = x
    obtain ⟨y, rfl⟩ := ((fiberEquiv H' u' (H.obj X)).trans (fiberEquiv H u X)).surjective x
    simp only [Equiv.trans_apply]
    rw [← fiberEquiv_smul, ← fiberEquiv_smul, h X σ y]

/-- XIII.4.1, second step of the proof (as in X.1.4): `ker (Aut F' → Aut F)` lies in the image
of `Aut F''` iff every connected object of `C'` whose image in `C''` has a section is isomorphic
to a subobject of an object coming from `C`. -/
theorem ker_autHom_le_range_iff :
    (autHom H u).ker ≤ (autHom H' u').range ↔
      ∀ X' : C', IsConnected X' → Nonempty (⊤_ C'' ⟶ H'.obj X') →
        ∃ (X : C) (i : X' ⟶ H.obj X), Mono i := by
  constructor
  · intro hle X' _ hs
    obtain ⟨y, hy⟩ := (nonempty_section_iff F'').mp hs
    let x' : F'.obj X' := fiberEquiv H' u' X' y
    have hI : (autHom H' u').range ≤ MulAction.stabilizer (Aut F') x' := by
      rintro _ ⟨σ, rfl⟩
      rw [MulAction.mem_stabilizer_iff, ← fiberEquiv_smul, hy]
    obtain ⟨W, hW⟩ := exists_openSubgroup_comap_eq F (autHom H u) (continuous_autHom H u)
      (MulAction.stabilizer (Aut F') x') (stabilizer_isOpen _ _) (hle.trans hI)
    obtain ⟨X, x, _, hx⟩ := exists_isConnected_stabilizer_eq F W
    obtain ⟨i, hi, -⟩ := exists_mono_of_stabilizer_eq F' x' ((fiberEquiv H u X).symm x)
      (by rw [stabilizer_fiberEquiv_symm, hx, hW])
    exact ⟨X, i, hi⟩
  · intro hcond σ hσ
    by_contra hnot
    have hclosed : IsClosed ((autHom H' u').range : Set (Aut F')) := by
      rw [MonoidHom.coe_range]
      exact (isCompact_range (continuous_autHom H' u')).isClosed
    obtain ⟨U, hIU, hσU⟩ := exists_openSubgroup_le_notMem F' _ hclosed hnot
    obtain ⟨X', x', _, hx'⟩ := exists_isConnected_stabilizer_eq F' U
    have hs : Nonempty (⊤_ C'' ⟶ H'.obj X') := by
      rw [nonempty_section_iff F'']
      refine ⟨(fiberEquiv H' u' X').symm x', fun τ ↦ ?_⟩
      have hτ : autHom H' u' τ ∈ MulAction.stabilizer (Aut F') x' := hx' ▸ hIU ⟨τ, rfl⟩
      rw [smul_fiberEquiv_symm, (MulAction.mem_stabilizer_iff).mp hτ]
    obtain ⟨X, i, _⟩ := hcond X' inferInstance hs
    have hmem : σ ∈ MulAction.stabilizer (Aut F') (F'.map i x') :=
      (MulAction.mem_stabilizer_iff).mpr (smul_eq_of_mem_ker H u hσ _)
    rw [stabilizer_map_of_mono, hx'] at hmem
    exact hσU hmem

/-- XIII.4.3, first step of the proof (V.6.8): the map `Aut F'' → Aut F'` is injective iff every
connected object of `C''` receives a morphism from a connected subobject of an object coming
from `C'`. -/
theorem autHom_injective_iff :
    Function.Injective (autHom H' u') ↔
      ∀ X'' : C'', IsConnected X'' →
        ∃ (X' : C') (Z : C'') (i : Z ⟶ H'.obj X') (_ : Z ⟶ X''), Mono i ∧ IsConnected Z := by
  constructor
  · intro hinj X'' _
    obtain ⟨x''⟩ := nonempty_fiber_of_isConnected F'' X''
    have hker : (autHom H' u').ker ≤ MulAction.stabilizer (Aut F'') x'' := by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr hinj]
      exact bot_le
    obtain ⟨A, hA⟩ := exists_pointedGaloisObject_comap_le F' (autHom H' u')
      (continuous_autHom H' u') _ (stabilizer_isOpen _ _) hker
    obtain ⟨Z, i, z, hz, hc, hm⟩ :=
      fiber_in_connected_component F'' (H'.obj A.obj) ((fiberEquiv H' u' A.obj).symm A.pt)
    have hstab : MulAction.stabilizer (Aut F'') z ≤ MulAction.stabilizer (Aut F'') x'' := by
      rw [← stabilizer_map_of_mono F'' i z, hz, stabilizer_fiberEquiv_symm]
      exact hA
    obtain ⟨p, -⟩ := exists_hom_of_stabilizer_le F'' z x'' hstab
    exact ⟨A.obj, Z, i, p, hm, hc⟩
  · intro hcond
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    refine eq_one_of_forall_smul_eq F'' fun X'' x'' ↦ ?_
    obtain ⟨Y, j, y, hy, _, _⟩ := fiber_in_connected_component F'' X'' x''
    obtain ⟨X', Z, i, p, _, _⟩ := hcond Y inferInstance
    obtain ⟨z, hz⟩ := surjective_of_nonempty_fiber_of_isConnected F'' p y
    have hinj : Function.Injective (F''.map i) :=
      ConcreteCategory.injective_of_mono_of_preservesPullback (F''.map i)
    have hz' : σ • z = z := hinj (by
      rw [← mulAction_naturality]
      exact smul_eq_of_mem_ker H' u' hσ _)
    rw [← hy, ← hz, mulAction_naturality, mulAction_naturality, hz']

/-- XIII.4.1 (formal part; cf. Stacks 0BN6): the sequence `Aut F'' → Aut F' → Aut F → 1` is
exact iff `H` preserves connectedness, objects of `C` become trivial in `C''`, and every
connected object of `C'` whose image in `C''` has a section is a subobject of an object coming
from `C`. This is the form in which X.1.4 and XIII.4.1 prove the exactness of
`π₁(X_s̄) → π₁(X) → π₁(S) → 1`. -/
theorem autHom_exact_iff :
    (Function.Surjective (autHom H u) ∧ (autHom H' u').range = (autHom H u).ker) ↔
      (∀ X : C, IsConnected X → IsConnected (H.obj X)) ∧
      (∀ X : C, IsTrivialObject (H'.obj (H.obj X))) ∧
      (∀ X' : C', IsConnected X' → Nonempty (⊤_ C'' ⟶ H'.obj X') →
        ∃ (X : C) (i : X' ⟶ H.obj X), Mono i) := by
  constructor
  · rintro ⟨hs, heq⟩
    exact ⟨(autHom_surjective_iff H u).mp hs,
      (autHom_comp_eq_one_iff H u H' u').mp ((MonoidHom.range_le_ker_iff _ _).mp heq.le),
      (ker_autHom_le_range_iff H u H' u').mp heq.ge⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨(autHom_surjective_iff H u).mpr h₁,
      le_antisymm ((MonoidHom.range_le_ker_iff _ _).mpr ((autHom_comp_eq_one_iff H u H' u').mpr h₂))
        ((ker_autHom_le_range_iff H u H' u').mpr h₃)⟩

/-- XIII.4.3, formal part: the sequence `1 → Aut F'' → Aut F' → Aut F → 1` is exact iff the
conditions of `autHom_exact_iff` hold and every connected object of `C''` is dominated by a
connected subobject of an object coming from `C'`. -/
theorem autHom_shortExact_iff :
    (Function.Injective (autHom H' u') ∧ Function.Surjective (autHom H u) ∧
        (autHom H' u').range = (autHom H u).ker) ↔
      (∀ X'' : C'', IsConnected X'' →
        ∃ (X' : C') (Z : C'') (i : Z ⟶ H'.obj X') (_ : Z ⟶ X''), Mono i ∧ IsConnected Z) ∧
      (∀ X : C, IsConnected X → IsConnected (H.obj X)) ∧
      (∀ X : C, IsTrivialObject (H'.obj (H.obj X))) ∧
      (∀ X' : C', IsConnected X' → Nonempty (⊤_ C'' ⟶ H'.obj X') →
        ∃ (X : C) (i : X' ⟶ H.obj X), Mono i) := by
  exact and_congr (autHom_injective_iff H' u') (autHom_exact_iff H u H' u')

include u in
/-- XIII.4.1, second step of the proof, when `π₁(X) → π₁(S)` is onto: a connected object of
`C'` is a subobject of an object coming from `C` iff it comes from a connected object of `C`
(as in X.1.4: a connected covering of `X` with a section over `X_s̄` comes from `S`). -/
theorem exists_mono_iff_exists_iso (hc : ∀ X : C, IsConnected X → IsConnected (H.obj X))
    (X' : C') [IsConnected X'] :
    (∃ (X : C) (i : X' ⟶ H.obj X), Mono i) ↔
      ∃ X : C, IsConnected X ∧ Nonempty (X' ≅ H.obj X) := by
  refine ⟨fun ⟨X, i, _⟩ ↦ ?_, fun ⟨X, _, ⟨e⟩⟩ ↦ ⟨X, e.hom, inferInstance⟩⟩
  obtain ⟨x'⟩ := nonempty_fiber_of_isConnected F' X'
  obtain ⟨Z, j, z, hz, _, _⟩ :=
    fiber_in_connected_component F X (fiberEquiv H u X (F'.map i x'))
  have := hc Z inferInstance
  have hinj : Function.Injective (F'.map (H.map j)) := by
    intro a b hab
    apply (fiberEquiv H u Z).injective
    apply ConcreteCategory.injective_of_mono_of_preservesPullback (F.map j)
    rw [← fiberEquiv_naturality, ← fiberEquiv_naturality, hab]
  have : Mono (H.map j) := F'.mono_of_mono_map
    ((ConcreteCategory.mono_iff_injective_of_preservesPullback _).mpr hinj)
  obtain ⟨f, -⟩ := connected_component_unique F' x' ((fiberEquiv H u Z).symm z) i (H.map j)
    (by
      apply (fiberEquiv H u X).injective
      rw [fiberEquiv_naturality, Equiv.apply_symm_apply, hz])
  exact ⟨Z, inferInstance, ⟨f⟩⟩

end Exactness

end SGA.SGA1.ExposeXIII
