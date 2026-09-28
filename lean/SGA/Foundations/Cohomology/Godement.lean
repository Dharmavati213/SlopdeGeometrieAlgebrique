/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Cech
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Godement sheaves and Čech acyclicity of injective sheaves

For a family `A` of abelian groups indexed by the points of a topological space `X`, the
*Godement sheaf* `V ↦ ∏_{x ∈ V} A x` is the sheaf of discontinuous sections (the product of the
skyscraper sheaves `x_* (A x)`). Every abelian sheaf `F` embeds into the Godement sheaf of its
stalks (Godement, *Théorie des faisceaux*, II.4.3).

## Main results

- `TopCat.Presheaf.cechComplex_godement_exactAt`: the Čech complex of a Godement sheaf with
  respect to any family of opens is exact in positive degrees (a contracting homotopy is built
  pointwise).
- `TopCat.Sheaf.cechComplex_exactAt_of_injective`: an injective abelian sheaf has vanishing
  Čech cohomology in positive degrees for every family of opens (Stacks Project, Section 20.11,
  for coverings;
  it is a retract of the Godement sheaf of its stalks).
-/

universe w u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat

variable {X : TopCat.{u}}

namespace Presheaf

/-- The Godement presheaf `V ↦ ∏_{x ∈ V} A x` of a family of abelian groups indexed by the points
of `X`; restriction maps are projections. -/
@[simps]
noncomputable def godement (A : X → AddCommGrpCat.{u}) : X.Presheaf AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (∀ x : V.unop, A x)
  map {V W} f := AddCommGrpCat.ofHom (AddMonoidHom.pi fun x ↦
    Pi.evalAddMonoidHom (fun x : V.unop ↦ A x) ⟨x.1, f.unop.le x.2⟩)

section

variable (A : X → AddCommGrpCat.{u}) {V : Opens X}

@[simp]
lemma godement_map_apply {W : Opens X} (h : W ≤ V) (s : (godement A).obj (op V)) (x : W) :
    (godement A).map (homOfLE h).op s x = s ⟨x.1, h x.2⟩ :=
  rfl

@[simp]
lemma godement_zero_apply (x : V) : (0 : (godement A).obj (op V)) x = 0 := rfl

@[simp]
lemma godement_sub_apply (s t : (godement A).obj (op V)) (x : V) : (s - t) x = s x - t x := rfl

@[simp]
lemma godement_zsmul_apply (n : ℤ) (s : (godement A).obj (op V)) (x : V) :
    (n • s) x = n • s x := rfl

@[simp]
lemma godement_sum_apply {α : Type*} (t : Finset α) (s : α → (godement A).obj (op V)) (x : V) :
    (∑ i ∈ t, s i) x = ∑ i ∈ t, s i x :=
  Finset.sum_apply x t s

end

lemma isSheaf_godement (A : X → AddCommGrpCat.{u}) : (godement A).IsSheaf := by
  rw [isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hmem (x : (⨆ i, U i : Opens X)) : ∃ i, x.1 ∈ U i := Opens.mem_iSup.mp x.2
  refine ⟨fun x ↦ sf (hmem x).choose ⟨x.1, (hmem x).choose_spec⟩, fun i ↦ ?_, fun t ht ↦ ?_⟩
  · funext x
    have := congrFun (hsf (hmem ⟨x.1, Opens.mem_iSup.mpr ⟨i, x.2⟩⟩).choose i)
      ⟨x.1, (hmem ⟨x.1, Opens.mem_iSup.mpr ⟨i, x.2⟩⟩).choose_spec, x.2⟩
    exact this
  · funext x
    exact congrFun (ht (hmem x).choose) ⟨x.1, (hmem x).choose_spec⟩

/-- The Čech complex of a Godement sheaf is exact in positive degrees, for any family of opens.
The contracting homotopy sends `c` to `(y, x) ↦ c_{k(x), y}(x)`, where `k(x)` is an index with
`x ∈ U (k x)`. -/
theorem cechComplex_godement_exactAt (A : X → AddCommGrpCat.{u}) {ι : Type w}
    (U : ι → Opens X) (n : ℕ) : (cechComplex U (godement A)).ExactAt (n + 1) := by
  rw [cechComplex_exactAt_succ_iff]
  intro c hc
  have hmem {m : ℕ} (y : Fin (m + 1) → ι) (x : cechOpen U y) : ∃ i, x.1 ∈ U i :=
    ⟨y 0, cechOpen_le U y 0 x.2⟩
  have hcons {m : ℕ} (y : Fin (m + 1) → ι) (x : cechOpen U y) :
      x.1 ∈ cechOpen U (Fin.cons (hmem y x).choose y : Fin (m + 2) → ι) := by
    rw [cechOpen_cons_eq]
    exact ⟨(hmem y x).choose_spec, x.2⟩
  refine ⟨fun y x ↦ c (Fin.cons (hmem y x).choose y) ⟨x.1, hcons y x⟩, funext fun z ↦ funext
    fun x ↦ ?_⟩
  have h := congrFun (congrFun hc (Fin.cons (hmem z x).choose z)) ⟨x.1, hcons z x⟩
  rw [cechD_cons] at h
  simp only [godement_sub_apply, godement_sum_apply, godement_zsmul_apply, godement_map_apply,
    Pi.zero_apply, godement_zero_apply, sub_eq_zero] at h
  refine (congrFun (cechD_apply U (godement A) _ z) x).trans ?_
  simp only [godement_sum_apply, godement_zsmul_apply]
  exact h.symm

end Presheaf

namespace Sheaf

/-- The Godement sheaf `V ↦ ∏_{x ∈ V} A x`. -/
noncomputable abbrev godement (A : X → AddCommGrpCat.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ⟨Presheaf.godement A, Presheaf.isSheaf_godement A⟩

variable (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The embedding `s ↦ (germₓ s)ₓ` of a sheaf into the Godement sheaf of its stalks. -/
noncomputable def toGodement : F ⟶ godement (fun x ↦ Presheaf.stalk F.obj x) :=
  ObjectProperty.homMk
    { app V := AddCommGrpCat.ofHom
        (AddMonoidHom.pi fun x ↦ (Presheaf.germ F.obj V.unop x.1 x.2).hom)
      naturality _ _ f := AddCommGrpCat.ext fun s ↦ funext fun x ↦
        Presheaf.germ_res_apply' F.obj f x.1 x.2 s }

lemma toGodement_app_apply {V : Opens X} (s : F.obj.obj (op V)) (x : V) :
    (toGodement F).hom.app (op V) s x = Presheaf.germ F.obj V x.1 x.2 s :=
  rfl

lemma toGodement_app_injective (V : Opens X) :
    Function.Injective ((toGodement F).hom.app (op V)) := fun s t h ↦
  Presheaf.section_ext F V s t fun x hx ↦ congrFun h ⟨x, hx⟩

instance : Mono (toGodement F) := by
  have : ∀ V : (Opens X)ᵒᵖ, Mono ((toGodement F).hom.app V) := fun V ↦
    (AddCommGrpCat.mono_iff_injective _).mpr (toGodement_app_injective F V.unop)
  have : Mono (toGodement F).hom := NatTrans.mono_of_mono_app _
  exact CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono (J := Opens.grothendieckTopology X) _ _

/-- An injective abelian sheaf has vanishing Čech cohomology in positive degrees, for any family
of opens: it is a retract of the Godement sheaf of its stalks. -/
theorem cechComplex_exactAt_of_injective
    (I : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [Injective I] {ι : Type w} (U : ι → Opens X) (n : ℕ) :
    (Presheaf.cechComplex U I.obj).ExactAt (n + 1) := by
  let i := toGodement I
  let r := Injective.factorThru (𝟙 I) i
  have hr : i.hom ≫ r.hom = 𝟙 _ := congrArg (fun f ↦ f.hom) (Injective.comp_factorThru (𝟙 I) i)
  have hG := Presheaf.cechComplex_godement_exactAt (fun x ↦ Presheaf.stalk I.obj x) U n
  rw [Presheaf.cechComplex_exactAt_succ_iff] at hG ⊢
  intro c hc
  obtain ⟨b, hb⟩ := hG (Presheaf.cechCochainMap U i.hom (n + 1) c)
    (by rw [Presheaf.cechD_cechCochainMap, hc, map_zero])
  refine ⟨Presheaf.cechCochainMap U r.hom n b, ?_⟩
  rw [Presheaf.cechD_cechCochainMap, hb, ← Presheaf.cechCochainMap_comp, hr,
    Presheaf.cechCochainMap_id]

end Sheaf

end TopCat
