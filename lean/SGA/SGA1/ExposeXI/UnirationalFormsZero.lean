/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.SerreUnirational

/-!
# Regular `0`-forms are regular functions

A sanity check for `regularForms` and `HodgeSymmetryZeroStatement` (XI.1.4): the regular `0`-forms
of an integral `k`-scheme `X` are its global regular functions, `regularForms f 0 ≅ Γ(X, 𝒪_X)`
inside `Ω⁰_{K/k} = K` (`mem_regularForms_zero_iff`), so for `X` proper over an algebraically closed
field `regularForms f 0` is one-dimensional and the case `q = 0` of `HodgeSymmetryZeroStatement`
holds (`finrankH_unit_zero_eq_finrank_regularForms_zero`).

* `exists_germ_top_eq_of_forall_stalk`: a rational function on an integral scheme which is
  regular at every point is a global section (the sheaf axiom, and the injectivity of
  `Γ(X, U) → K(X)`).
-/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace SGA.SGA1.ExposeXI

variable {X : Scheme.{u}} [IsIntegral X]

/-- A rational function on an integral scheme which is regular at every point (lies in the image
of every local ring `𝒪_{X,x} → K(X)`) is a global section. -/
theorem exists_germ_top_eq_of_forall_stalk (c : X.functionField)
    (hc : ∀ x : X, ∃ a : X.presheaf.stalk x,
      (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom a = c) :
    ∃ s : Γ(X, ⊤), X.presheaf.germ ⊤ (genericPoint X) (Opens.mem_top _) s = c := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  choose a ha using hc
  choose U hxU t ht using fun x ↦ X.presheaf.exists_germ_eq (a x)
  have hne : ∀ x, Nonempty (U x) := fun x ↦ ⟨⟨x, hxU x⟩⟩
  -- the local sections all map to `c`
  have hgerm : ∀ (V : X.Opens) [Nonempty V] (x : X) (hx : x ∈ V) (s : Γ(X, V)),
      X.germToFunctionField V s =
        (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom (X.presheaf.germ V x hx s) :=
    fun V _ x hx s ↦ by
      rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  have hK : ∀ x, X.germToFunctionField (U x) (t x) = c := fun x ↦ by
    have := hne x
    rw [hgerm (U x) x (hxU x), ht x, ha x]
  have hres : ∀ (V W : X.Opens) [Nonempty V] [Nonempty W] (i : V ⟶ W) (s : Γ(X, W)),
      X.germToFunctionField V (X.presheaf.map i.op s) = X.germToFunctionField W s :=
    fun V W _ _ i s ↦ TopCat.Presheaf.germ_res_apply _ _ _ _ _
  -- they are compatible, since `Γ(X, V) → K(X)` is injective
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U t := by
    intro x y
    have : Nonempty (U x ⊓ U y : X.Opens) := by
      have hx : genericPoint X ∈ U x :=
        ((genericPoint_spec X).mem_open_set_iff (U x).isOpen).mpr ⟨x, trivial, hxU x⟩
      have hy : genericPoint X ∈ U y :=
        ((genericPoint_spec X).mem_open_set_iff (U y).isOpen).mpr ⟨y, trivial, hxU y⟩
      exact ⟨⟨genericPoint X, hx, hy⟩⟩
    have := hne x
    have := hne y
    apply X.germToFunctionField_injective (U x ⊓ U y)
    change X.germToFunctionField _ (X.presheaf.map _ (t x)) =
      X.germToFunctionField _ (X.presheaf.map _ (t y))
    rw [hres, hres, hK, hK]
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (U := U) ⊤ (fun _ ↦ homOfLE le_top)
    (fun z _ ↦ Opens.mem_iSup.mpr ⟨z, hxU z⟩) t hcompat
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have := hne x
  refine ⟨s, ?_⟩
  rw [← hK x, ← hs x]
  exact (hres _ _ _ s).symm

variable {k : Type u} [Field k]

/-- The **regular `0`-forms are the regular functions**: for an integral `k`-scheme `X`, a `0`-form
`ω ∈ Ω⁰_{K/k} = K(X)` is regular (`regularForms f 0`) iff it is the image of a global section of
`𝒪_X`. -/
theorem mem_regularForms_zero_iff (f : X ⟶ Spec (.of k))
    (ω : letI := (functionFieldMap f).toAlgebra; ⋀[X.functionField]^0 Ω[X.functionField⁄k]) :
    letI := (functionFieldMap f).toAlgebra
    ω ∈ regularForms f 0 ↔ ∃ s : Γ(X, ⊤),
      exteriorPower.zeroEquiv X.functionField Ω[X.functionField⁄k] ω =
        X.presheaf.germ ⊤ (genericPoint X) (Opens.mem_top _) s := by
  let _ := (functionFieldMap f).toAlgebra
  let e := exteriorPower.zeroEquiv X.functionField Ω[X.functionField⁄k]
  let g : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  have hg : ∀ (x : X) (c : k), algebraMap k X.functionField c =
      (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom
        (X.presheaf.germ ⊤ x (Opens.mem_top _) (g c)) := by
    intro x c
    rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rfl
  constructor
  · intro hω
    suffices h : ∀ x : X, ∃ a : X.presheaf.stalk x,
        (X.presheaf.stalkSpecializes (genericPoint_specializes x)).hom a = e ω by
      obtain ⟨s, hs⟩ := exists_germ_top_eq_of_forall_stalk (e ω) h
      exact ⟨s, hs.symm⟩
    intro x
    have hωx := (iInf_le _ x : regularForms f 0 ≤ _) hω
    clear hω
    induction hωx using Submodule.span_induction with
    | mem ω' h =>
      obtain ⟨a, rfl⟩ := h
      exact ⟨a 0, by rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]⟩
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | add ω₁ ω₂ _ _ h₁ h₂ =>
      obtain ⟨a₁, h₁⟩ := h₁
      obtain ⟨a₂, h₂⟩ := h₂
      exact ⟨a₁ + a₂, by rw [map_add, map_add, h₁, h₂]⟩
    | smul c ω' _ h =>
      obtain ⟨a, ha⟩ := h
      refine ⟨X.presheaf.germ ⊤ x (Opens.mem_top _) (g c) * a, ?_⟩
      rw [map_mul, ← hg, ha, ← Algebra.smul_def]
      exact (e.toLinearMap.map_smul_of_tower c ω').symm
  · rintro ⟨s, hs⟩
    refine Submodule.mem_iInf _ |>.mpr fun x ↦
      Submodule.subset_span ⟨fun _ ↦ X.presheaf.germ ⊤ x (Opens.mem_top _) s, ?_⟩
    apply e.injective
    change e ω = e (_ • _)
    rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one, hs,
      ← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

/-- **The case `q = 0` of `HodgeSymmetryZeroStatement`** (sanity check of C11): for `X` proper
and integral over an algebraically closed field `k`, `h⁰(X, 𝒪_X) = 1 = dim_k (regularForms f 0)`.
No smoothness is needed. -/
theorem finrankH_unit_zero_eq_finrank_regularForms_zero [IsAlgClosed k] (f : X ⟶ Spec (.of k))
    [IsProper f] :
    letI := (functionFieldMap f).toAlgebra
    Scheme.Modules.finrankH f (CohomologyAux.unitModule X) 0 =
      Module.finrank k (regularForms f 0) := by
  let _ := (functionFieldMap f).toAlgebra
  let e := exteriorPower.zeroEquiv X.functionField Ω[X.functionField⁄k]
  have he : ∀ (c : k) ω, e (c • ω) = c • e ω := fun c ω ↦ e.toLinearMap.map_smul_of_tower c ω
  rw [finrankH_unit_zero_eq_one f]
  -- `Γ(X, 𝒪_X) = k`
  have := ExposeX.isIso_app_of_isProper f ⊤
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.app ⊤))
  have hsurj := (ConcreteCategory.bijective_of_isIso
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)).2
  -- `regularForms f 0 = k ∙ ω₁`
  let ω₁ := e.symm 1
  have hω₁ : ω₁ ≠ 0 := fun h ↦ one_ne_zero (e.symm.injective (h.trans (map_zero _).symm))
  have key : regularForms f 0 = Submodule.span k {ω₁} := by
    ext ω
    rw [mem_regularForms_zero_iff, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨c, rfl⟩ := hsurj s
      refine ⟨c, e.injective ?_⟩
      rw [he, LinearEquiv.apply_symm_apply, hs, Algebra.smul_def, mul_one]
      rfl
    · rintro ⟨c, rfl⟩
      refine ⟨((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) c, ?_⟩
      rw [he, LinearEquiv.apply_symm_apply, Algebra.smul_def, mul_one]
      rfl
  rw [key, finrank_span_singleton hω₁]

end SGA.SGA1.ExposeXI
