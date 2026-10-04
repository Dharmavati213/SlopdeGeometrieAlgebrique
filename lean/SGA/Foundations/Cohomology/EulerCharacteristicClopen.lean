/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.EulerCharacteristicBaseChange
import SGA.Foundations.Cohomology.Devissage
import SGA.Foundations.Cohomology.Thickening

/-!
# The Euler characteristic of a disjoint union

Let `W` be proper over a field and `W = A ⊔ B` a decomposition into open and closed subschemes,
given by `a : A ⟶ W`, `b : B ⟶ W`, both open and closed immersions with complementary images.
For a coherent `𝒪_W`-module `M`,

`χ(W, M) = χ(A, a^* M) + χ(B, b^* M)` (`Scheme.Modules.eulerChar_eq_add_of_isCompl`).

Proof: `0 → K → M → a_* a^* M → 0` is exact (`CohomologyAux.shortExact_idealMul`), and the kernel
`K` is `b_* b^* M`: a section of `M` over `V` is a pair of sections over `V ∩ A` and `V ∩ B`
(sheaf axiom for a disjoint cover), and `Γ(a^* M, a⁻¹ V) = Γ(M, V ∩ A)` for an open immersion.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {W A : Scheme.{u}}

/-- Sections over an open contained in `⊥` are zero. -/
lemma eq_zero_of_le_bot (M : W.Modules) {V : W.Opens} (hV : V ≤ ⊥) (s : Γ(M, V)) : s = 0 :=
  TopCat.Sheaf.eq_of_locally_eq' M.toAbSheaf (fun i : PEmpty.{1} ↦ i.elim) V
    (fun i ↦ i.elim) (fun _ hx ↦ (hV hx).elim) _ _ (fun i ↦ i.elim)

/-- Along an open immersion `a`, the inverse image of a section over `V` only depends on its
restriction to `V ∩ a(A)`. -/
lemma pullbackApp_eq_map_inf (a : A ⟶ W) [IsOpenImmersion a] (M : W.Modules) (V : W.Opens)
    (s : Γ(M, V)) :
    pullbackApp a M V s = ((pullback a).obj M).presheaf.map
      (homOfLE (by rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq]) :
        a ⁻¹ᵁ V ⟶ a ⁻¹ᵁ (V ⊓ a.opensRange)).op
      (pullbackApp a M (V ⊓ a.opensRange) (M.presheaf.map (homOfLE inf_le_left).op s)) := by
  rw [pullbackApp_map, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  have : (homOfLE (by rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange,
      inf_top_eq]) : a ⁻¹ᵁ V ⟶ a ⁻¹ᵁ (V ⊓ a.opensRange)) ≫
      (TopologicalSpace.Opens.map a.base).map (homOfLE inf_le_left) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- Along an open immersion `a`, the inverse image of a section over `V` vanishes iff its
restriction to `V ∩ a(A)` vanishes. -/
lemma pullbackApp_eq_zero_iff (a : A ⟶ W) [IsOpenImmersion a] (M : W.Modules) (V : W.Opens)
    (s : Γ(M, V)) :
    pullbackApp a M V s = 0 ↔
      M.presheaf.map (homOfLE inf_le_left : V ⊓ a.opensRange ⟶ V).op s = 0 := by
  rw [pullbackApp_eq_map_inf]
  constructor
  · intro h
    apply (pullbackApp_bijective_of_isOpenImmersion a M (V ⊓ a.opensRange) inf_le_right).1
    rw [map_zero]
    have hinj : Function.Injective (((pullback a).obj M).presheaf.map
        (homOfLE (by rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq]) :
          a ⁻¹ᵁ V ⟶ a ⁻¹ᵁ (V ⊓ a.opensRange)).op) := by
      have : IsIso (homOfLE (by rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange,
          inf_top_eq]) : a ⁻¹ᵁ V ⟶ a ⁻¹ᵁ (V ⊓ a.opensRange)) :=
        ⟨⟨homOfLE (by rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq]),
          Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
      exact (ConcreteCategory.bijective_of_isIso _).1
    exact hinj (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero, map_zero]

/-- **Gluing over two disjoint opens.** -/
lemma exists_glue_of_disjoint (M : W.Modules) {V V₁ V₂ : W.Opens} (h₁ : V₁ ≤ V) (h₂ : V₂ ≤ V)
    (hcov : V ≤ V₁ ⊔ V₂) (hdisj : V₁ ⊓ V₂ ≤ ⊥) (s₁ : Γ(M, V₁)) (s₂ : Γ(M, V₂)) :
    ∃ s : Γ(M, V), M.presheaf.map (homOfLE h₁).op s = s₁ ∧
      M.presheaf.map (homOfLE h₂).op s = s₂ := by
  let U : Bool → W.Opens := fun i ↦ cond i V₁ V₂
  let sf : ∀ i, Γ(M, U i) := fun i ↦ Bool.rec (motive := fun i ↦ Γ(M, U i)) s₂ s₁ i
  have hc : V ≤ iSup U := by
    rw [iSup_bool_eq]
    exact hcov
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' M.toAbSheaf U V
    (fun i ↦ homOfLE (by cases i; exacts [h₂, h₁])) hc sf (by
      intro i j
      cases i <;> cases j
      · rfl
      · exact (eq_zero_of_le_bot M (inf_comm V₂ V₁ ▸ hdisj) _).trans
          (eq_zero_of_le_bot M (inf_comm V₂ V₁ ▸ hdisj) _).symm
      · exact (eq_zero_of_le_bot M hdisj _).trans (eq_zero_of_le_bot M hdisj _).symm
      · rfl)
  exact ⟨s, hs true, hs false⟩

section EulerCharacteristic

variable {k : Type u} [Field k] {B : Scheme.{u}} (g : W ⟶ Spec (.of k)) (a : A ⟶ W) (b : B ⟶ W)
  [IsOpenImmersion a] [IsClosedImmersion a] [IsOpenImmersion b] [IsClosedImmersion b]

/-- **The Euler characteristic of a disjoint union**: if `W` is proper over a field and
`a : A ⟶ W`, `b : B ⟶ W` are open and closed immersions with complementary images, then
`χ(W, M) = χ(A, a^* M) + χ(B, b^* M)` for every coherent `M`. -/
theorem eulerChar_eq_add_of_isCompl [IsProper g] (h : IsCompl a.opensRange b.opensRange)
    (M : W.Modules) [M.IsCoherent] :
    eulerChar g M = eulerChar (a ≫ g) ((pullback a).obj M) +
      eulerChar (b ≫ g) ((pullback b).obj M) := by
  have : M.IsQuasicoherent := IsCoherent.isQuasicoherent
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian g
  have hS := CohomologyAux.shortExact_idealMul a M
  have : ((pullback a).obj M).IsCoherent := isCoherent_pullback a M
  have : ((pullback b).obj M).IsCoherent := isCoherent_pullback b M
  have : ((pushforward a).obj ((pullback a).obj M)).IsCoherent :=
    CohomologyAux.isCoherent_pushforward_of_isClosedImmersion a _
  have : ((pushforward b).obj ((pullback b).obj M)).IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_pushforward b _
  have : (ShortComplex.kernelSequence (CohomologyAux.unitPushPull a M)).X₂.IsCoherent :=
    ‹M.IsCoherent›
  have : (ShortComplex.kernelSequence (CohomologyAux.unitPushPull a M)).X₃.IsCoherent :=
    ‹((pushforward a).obj ((pullback a).obj M)).IsCoherent›
  have : (ShortComplex.kernelSequence (CohomologyAux.unitPushPull a M)).X₂.IsQuasicoherent :=
    ‹M.IsQuasicoherent›
  have : (ShortComplex.kernelSequence (CohomologyAux.unitPushPull a M)).X₃.IsQuasicoherent :=
    IsCoherent.isQuasicoherent
  have : (ShortComplex.kernelSequence (CohomologyAux.unitPushPull a M)).X₁.IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_X₁_of_shortExact hS
  have hK : (ShortComplex.kernelSequence (CohomologyAux.unitPushPull a M)).X₁.IsCoherent :=
    CohomologyAux.isCoherent_X₁_of_shortExact hS
  have e1 := eulerChar_of_shortExact g hS
  -- The kernel is `b_* b^* M`.
  let ψ : kernel (CohomologyAux.unitPushPull a M) ⟶ (pushforward b).obj ((pullback b).obj M) :=
    kernel.ι _ ≫ CohomologyAux.unitPushPull b M
  have hsup : a.opensRange ⊔ b.opensRange = ⊤ := h.sup_eq_top
  have hinf : a.opensRange ⊓ b.opensRange = ⊥ := h.inf_eq_bot
  have hψ : IsIso ψ := CohomologyAux.isIso_of_bijective_app_affine ψ fun V _ ↦ by
    constructor
    · intro x y hxy
      rw [← sub_eq_zero] at hxy ⊢
      rw [← map_sub] at hxy
      set z := x - y
      apply CohomologyAux.app_injective_of_mono (kernel.ι (CohomologyAux.unitPushPull a M)) V
      rw [map_zero]
      set s := (kernel.ι (CohomologyAux.unitPushPull a M)).app V z
      have ha : pullbackApp a M V s = 0 := by
        change (kernel.ι (CohomologyAux.unitPushPull a M) ≫
          CohomologyAux.unitPushPull a M).app V z = 0
        rw [kernel.condition]
        rfl
      have hb : pullbackApp b M V s = 0 := hxy
      rw [pullbackApp_eq_zero_iff] at ha hb
      refine TopCat.Sheaf.eq_of_locally_eq₂ (F := M.toAbSheaf)
        (homOfLE inf_le_left : V ⊓ a.opensRange ⟶ V) (homOfLE inf_le_left : V ⊓ b.opensRange ⟶ V)
        (by rw [← inf_sup_left, hsup, inf_top_eq]) s 0 ?_ ?_
      · exact ha.trans (map_zero _).symm
      · exact hb.trans (map_zero _).symm
    · intro t
      have hVb : b ⁻¹ᵁ V = b ⁻¹ᵁ (V ⊓ b.opensRange) := by
        rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq]
      let t₁ : Γ((pullback b).obj M, b ⁻¹ᵁ (V ⊓ b.opensRange)) :=
        ((pullback b).obj M).presheaf.map (homOfLE hVb.ge).op t
      obtain ⟨u, hu⟩ :=
        (pullbackApp_bijective_of_isOpenImmersion b M (V ⊓ b.opensRange) inf_le_right).2 t₁
      obtain ⟨s, hs₁, hs₂⟩ := exists_glue_of_disjoint M (V₁ := V ⊓ b.opensRange)
        (V₂ := V ⊓ a.opensRange) inf_le_left inf_le_left
        (by rw [← inf_sup_left, sup_comm, hsup, inf_top_eq])
        (by
          rw [inf_inf_inf_comm, inf_idem, inf_comm b.opensRange, hinf, inf_bot_eq])
        u 0
      have hsa : pullbackApp a M V s = 0 := (pullbackApp_eq_zero_iff a M V s).mpr hs₂
      obtain ⟨x, hx⟩ := CohomologyAux.exists_app_eq_of_shortExact hS V s hsa
      refine ⟨x, ?_⟩
      have hψx : ψ.app V x = pullbackApp b M V s :=
        congrArg (pullbackApp b M V) hx
      have key : ∀ t' : Γ((pullback b).obj M, b ⁻¹ᵁ V),
          ((pullback b).obj M).presheaf.map (homOfLE hVb.le).op
            (((pullback b).obj M).presheaf.map (homOfLE hVb.ge).op t') = t' := by
        intro t'
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
        have : (homOfLE hVb.le : b ⁻¹ᵁ V ⟶ b ⁻¹ᵁ (V ⊓ b.opensRange)) ≫ homOfLE hVb.ge = 𝟙 _ :=
          Subsingleton.elim _ _
        rw [this, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
      rw [hψx, pullbackApp_eq_map_inf, hs₁, hu]
      exact key t
  refine e1.trans ?_
  rw [add_comm]
  congr 1
  · exact eulerChar_pushforward g a _
  · exact (eulerChar_congr g (asIso ψ)).trans (eulerChar_pushforward g b _)

end EulerCharacteristic

end AlgebraicGeometry.Scheme.Modules
