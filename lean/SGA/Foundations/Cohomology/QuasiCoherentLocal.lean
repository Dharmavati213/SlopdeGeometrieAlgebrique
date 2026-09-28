/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.AffineOpenVanishing
import SGA.Foundations.Cohomology.LongExactSequence
import SGA.Foundations.Cohomology.Helpers
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Sections of quasi-coherent modules over affine opens

For a quasi-coherent `𝒪_X`-module `F`, an affine open `V` and `c ∈ Γ(X, V)`, the restriction
`Γ(V, F) → Γ(D(c), F)` is the localization at `c` (EGA I 1.4.1): every section over `D(c)` is,
after multiplication by a power of `c`, the restriction of a section over `V`, and a section over
`V` vanishing on `D(c)` is killed by a power of `c`.

We deduce a criterion for epimorphisms: a morphism `E ⟶ F` with `F` quasi-coherent which is
surjective on sections over the members of an affine open cover is an epimorphism.
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.CohomologyAux

variable {X : Scheme.{u}} (F : X.Modules) {V : X.Opens}

/-- **Sections over a basic open are fractions** (EGA I 1.4.1): for `F` quasi-coherent, `V` affine
and `c ∈ Γ(X, V)`, every section of `F` over `D(c)` becomes, after multiplication by a power of
`c`, the restriction of a section over `V`. -/
lemma exists_pow_smul_eq_map [F.IsQuasicoherent] (hV : IsAffineOpen V) (c : Γ(X, V))
    (t : Γ(F, X.basicOpen c)) : ∃ (m : Γ(F, V)) (k : ℕ),
      X.presheaf.map (homOfLE (X.basicOpen_le c)).op (c ^ k) • t =
        F.presheaf.map (homOfLE (X.basicOpen_le c)).op m := by
  have hW : X.basicOpen c ⊓ V = X.basicOpen c := inf_eq_left.mpr (X.basicOpen_le c)
  have := F.isLocalizedModule_presheafInf_top hV c hW
  obtain ⟨k, x, hx⟩ := IsLocalizedModule.Away.surj
    (TopCat.Presheaf.resₗ (F.presheafInf V) (F.presheafInf_map_smul V)
      (le_top : X.basicOpen c ≤ ⊤)) c
    (F.presheaf.map (homOfLE hW.le).op t : (F.presheafInf V).obj (op (X.basicOpen c)))
  refine ⟨F.presheaf.map (homOfLE (le_inf le_top le_rfl : V ≤ ⊤ ⊓ V)).op x, k, ?_⟩
  change X.presheaf.map (homOfLE (inf_le_right : X.basicOpen c ⊓ V ≤ V)).op (c ^ k) •
      F.presheaf.map (homOfLE hW.le).op t =
    F.presheaf.map (homOfLE (inf_le_inf_right V le_top : X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op x at hx
  have hx' := congrArg (F.presheaf.map (homOfLE hW.ge).op) hx
  rw [Scheme.Modules.map_smul, TopCat.Presheaf.map_map_apply,
    CohomologyAux.presheaf_map_map, CohomologyAux.modules_map_self] at hx'
  refine hx'.trans ?_
  exact (TopCat.Presheaf.map_map_apply F.presheaf _ _ (x : Γ(F, ⊤ ⊓ V))).trans
    (TopCat.Presheaf.map_map_apply F.presheaf _ _ (x : Γ(F, ⊤ ⊓ V))).symm

/-- **Sections vanishing on a basic open** (EGA I 1.4.1): for `F` quasi-coherent, `V` affine and
`c ∈ Γ(X, V)`, a section of `F` over `V` vanishing on `D(c)` is killed by a power of `c`. -/
lemma exists_pow_smul_eq_zero [F.IsQuasicoherent] (hV : IsAffineOpen V) (c : Γ(X, V))
    (m : Γ(F, V)) (hm : F.presheaf.map (homOfLE (X.basicOpen_le c)).op m = 0) :
    ∃ k : ℕ, c ^ k • m = 0 := by
  have hW : X.basicOpen c ⊓ V = X.basicOpen c := inf_eq_left.mpr (X.basicOpen_le c)
  have := F.isLocalizedModule_presheafInf_top hV c hW
  have hV' : ⊤ ⊓ V = V := top_inf_eq V
  let m' : (F.presheafInf V).obj (op ⊤) := F.presheaf.map (homOfLE hV'.le).op m
  have h0 : TopCat.Presheaf.resₗ (F.presheafInf V) (F.presheafInf_map_smul V)
      (le_top : X.basicOpen c ≤ ⊤) m' =
      TopCat.Presheaf.resₗ (F.presheafInf V) (F.presheafInf_map_smul V)
      (le_top : X.basicOpen c ≤ ⊤) 0 := by
    rw [map_zero, TopCat.Presheaf.resₗ_apply]
    change F.presheaf.map (homOfLE (inf_le_inf_right V le_top :
      X.basicOpen c ⊓ V ≤ ⊤ ⊓ V)).op (F.presheaf.map (homOfLE hV'.le).op m) = 0
    rw [TopCat.Presheaf.map_map_apply]
    have := congrArg (F.presheaf.map (homOfLE hW.le).op) hm
    rwa [map_zero, TopCat.Presheaf.map_map_apply] at this
  obtain ⟨k, hk⟩ := IsLocalizedModule.Away.exists_of_eq c h0
  refine ⟨k, ?_⟩
  rw [smul_zero] at hk
  change X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V ≤ V)).op (c ^ k) •
    F.presheaf.map (homOfLE hV'.le).op m = 0 at hk
  have hk' := congrArg (F.presheaf.map (homOfLE hV'.ge).op) hk
  rw [Scheme.Modules.map_smul, TopCat.Presheaf.map_map_apply, CohomologyAux.presheaf_map_map,
    CohomologyAux.presheaf_map_self, CohomologyAux.modules_map_self, map_zero] at hk'
  exact hk'

/-- **Epimorphisms onto quasi-coherent modules can be detected on an affine cover**: a morphism
`φ : E ⟶ F` with `F` quasi-coherent which is surjective on sections over each member of an open
cover by affines is an epimorphism. -/
theorem epi_of_surjective_app {E : X.Modules} [F.IsQuasicoherent] (φ : E ⟶ F) {ι : Type*}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (hUa : ∀ i, IsAffineOpen (U i))
    (hφ : ∀ i, Function.Surjective (φ.app (U i))) : Epi φ := by
  have : (Scheme.Modules.toAbSheafFunctor X).Faithful :=
    inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful
  suffices h : Epi (Scheme.Modules.Hom.toAbSheaf φ) from
    (Scheme.Modules.toAbSheafFunctor X).epi_of_epi_map h
  refine (TopCat.Sheaf.isLocallySurjective_iff_epi (Scheme.Modules.Hom.toAbSheaf φ)).mp ?_
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro W t x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
  obtain ⟨c, hcW, hxc⟩ := (hUa i).exists_basicOpen_le ⟨x, hx⟩ hi
  refine ⟨X.basicOpen c, hcW, ?_, hxc⟩
  obtain ⟨m, k, hm⟩ := exists_pow_smul_eq_map F (hUa i) c
    (F.presheaf.map (homOfLE hcW).op (t : Γ(F, W)))
  obtain ⟨e, rfl⟩ := hφ i m
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le c)).op (c ^ k)) := by
    rw [map_pow]
    exact (X.toRingedSpace.isUnit_res_basicOpen c).pow k
  refine ⟨hu.unit⁻¹.1 • E.presheaf.map (homOfLE (X.basicOpen_le c)).op e, ?_⟩
  change φ.app _ _ = F.presheaf.map _ t
  rw [Scheme.Modules.Hom.app_smul, CohomologyAux.hom_app_presheaf_map, ← hm, smul_smul,
    IsUnit.val_inv_mul, one_smul]

/-- `𝒪_X`-modules have finite biproducts (the instance is not found automatically, because of the
several paths to the zero morphisms of `X.Modules`). -/
noncomputable instance hasFiniteBiproducts_modules (X : Scheme.{u}) :
    Limits.HasFiniteBiproducts X.Modules :=
  Abelian.hasFiniteBiproducts

variable (X) in
/-- The structure sheaf, as an `𝒪_X`-module. -/
noncomputable abbrev unitModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The morphism `𝒪_X ⟶ G` defined by a global section `g` of `G`. -/
noncomputable def homOfSection (G : X.Modules) (g : Γ(G, ⊤)) : unitModule X ⟶ G :=
  (SheafOfModules.unitHomEquiv G).symm
    (_root_.PresheafOfModules.sectionsMk
      (fun V ↦ G.presheaf.map (homOfLE le_top : V.unop ⟶ ⊤).op g) fun V W f ↦ by
        change G.presheaf.map f (G.presheaf.map _ g) = G.presheaf.map _ g
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl)

lemma homOfSection_app (G : X.Modules) (g : Γ(G, ⊤)) (V : X.Opens) (r : Γ(X, V)) :
    (homOfSection G g).app V r = r • G.presheaf.map (homOfLE le_top : V ⟶ ⊤).op g :=
  rfl

/-- **Global generation gives an epimorphism**: if finitely many global sections of a
quasi-coherent module `G` generate its sections over each member of an affine open cover, the
induced morphism `𝒪_X^J ⟶ G` is an epimorphism. -/
theorem epi_biproduct_desc_homOfSection (G : X.Modules) [G.IsQuasicoherent] {J : Type*}
    [Finite J] (g : J → Γ(G, ⊤)) {ι : Type*} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hUa : ∀ i, IsAffineOpen (U i))
    (hgen : ∀ i, Submodule.span Γ(X, U i)
      (Set.range fun j ↦ G.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op (g j)) = ⊤) :
    Epi (Limits.biproduct.desc fun j ↦ homOfSection G (g j)) := by
  have := Fintype.ofFinite J
  refine epi_of_surjective_app G _ U hU hUa fun i m ↦ ?_
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
    ((hgen i).ge (Submodule.mem_top : m ∈ ⊤))
  refine ⟨∑ j, (Limits.biproduct.ι (fun _ : J ↦ unitModule X) j).app (U i) (r j), ?_⟩
  rw [map_sum, ← hr]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  change (Limits.biproduct.ι (fun _ : J ↦ unitModule X) j ≫
    Limits.biproduct.desc fun j ↦ homOfSection G (g j)).app (U i) (r j) = _
  rw [Limits.biproduct.ι_desc]
  exact homOfSection_app G (g j) (U i) (r j)

end AlgebraicGeometry.CohomologyAux
