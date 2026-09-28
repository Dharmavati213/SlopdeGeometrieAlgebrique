/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.FiniteEtaleAlgebraization

/-!
# Algebraization by pro-isomorphisms

The Artin–Rees argument behind EGA III 5.1.4 and 4.1.5, in the form used for the existence
theorem on proper schemes: to show that a quasi-coherent `B` algebraizes an adic system `(G_n)`,
it suffices to map both to an inverse system `(E_n)` by `u_n : B ⟶ E_n`, `w_n : G_n ⟶ E_n` with
the same images over affine opens, and with kernels that are "essentially zero" (for `B` modulo
`I^{n+1}`).

* `AdicSystem.trans`: the transitions `G_m ⟶ G_n`, `n ≤ m`, functorially;
* `proIsoHom`: the comparison maps `v_n : B ⟶ G_n`, defined on affine opens by lifting `u(b)`;
* `exists_iso_quotientIdealPow_of_proIso`: `B / I^{n+1} B ≅ G_n` compatibly.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

open Scheme.Modules

section ProIso

variable {A : CommRingCat.{u}} {I : Ideal A} {X : Scheme.{u}} {f : X ⟶ Spec A}

namespace AdicSystem

variable (G : AdicSystem I f)

/-- The adic system as a functor `ℕᵒᵖ ⥤ X.Modules`. -/
def functor : ℕᵒᵖ ⥤ X.Modules := Functor.ofOpSequence G.map

/-- The transition `G_m ⟶ G_n` for `n ≤ m`. -/
def trans {n m : ℕ} (h : n ≤ m) : G.obj m ⟶ G.obj n := G.functor.map (homOfLE h).op

@[reassoc]
lemma trans_trans {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) :
    G.trans h₂ ≫ G.trans h₁ = G.trans (h₁.trans h₂) :=
  (G.functor.map_comp (homOfLE h₂).op (homOfLE h₁).op).symm

lemma trans_self (n : ℕ) : G.trans (le_refl n) = 𝟙 _ :=
  G.functor.map_id (op n)

lemma trans_succ (n : ℕ) : G.trans n.le_succ = G.map n :=
  Functor.ofOpSequence_map_homOfLE_succ G.map n

lemma transition_eq_trans (n d : ℕ) : G.transition n d = G.trans (Nat.le_add_right n d) := by
  induction d with
  | zero => exact (G.trans_self n).symm
  | succ d ih =>
    rw [transition_succ, ih, ← trans_succ, trans_trans]

lemma trans_surjective {n m : ℕ} (h : n ≤ m) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective ((G.trans h).app U) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← transition_eq_trans]
  exact G.transition_surjective n d hU

lemma trans_app_eq_zero_iff {n m : ℕ} (h : n ≤ m) {U : X.Opens} (hU : IsAffineOpen U)
    (s : Γ(G.obj m, U)) :
    (G.trans h).app U s = 0 ↔
      s ∈ (idealV f I U 1 ^ (n + 1) • ⊤ : Submodule Γ(X, U) Γ(G.obj m, U)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← transition_eq_trans]
  exact G.transition_app_eq_zero_iff n d hU s

end AdicSystem

variable (G : AdicSystem I f) (B : X.Modules)
  (E : ℕᵒᵖ ⥤ X.Modules) (u : ∀ n, B ⟶ E.obj (op n)) (w : ∀ n, G.obj n ⟶ E.obj (op n))
  (hu : ∀ n, u (n + 1) ≫ E.map (homOfLE n.le_succ).op = u n)
  (hw : ∀ n, w (n + 1) ≫ E.map (homOfLE n.le_succ).op = G.map n ≫ w n)

include hu in
lemma proIso_u_comp {n m : ℕ} (h : n ≤ m) : u m ≫ E.map (homOfLE h).op = u n := by
  induction m, h using Nat.le_induction with
  | base => rw [show (homOfLE (le_refl n)).op = 𝟙 (op n) from rfl, E.map_id, Category.comp_id]
  | succ m hm ih =>
    rw [show (homOfLE (hm.trans m.le_succ)).op = (homOfLE m.le_succ).op ≫ (homOfLE hm).op
      from rfl, E.map_comp, ← Category.assoc, hu, ih]

include hw in
lemma proIso_w_comp {n m : ℕ} (h : n ≤ m) :
    w m ≫ E.map (homOfLE h).op = G.trans h ≫ w n := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [show (homOfLE (le_refl n)).op = 𝟙 (op n) from rfl, E.map_id, Category.comp_id,
      G.trans_self, Category.id_comp]
  | succ m hm ih =>
    rw [show (homOfLE (hm.trans m.le_succ)).op = (homOfLE m.le_succ).op ≫ (homOfLE hm).op
      from rfl, E.map_comp, ← Category.assoc, hw, Category.assoc, ih, ← Category.assoc,
      ← G.trans_succ, G.trans_trans]

/-- The pro-isomorphism hypotheses over an affine open `U`, with constant `c`: kernels of
`Γ(B, U) → Γ(E_{n+c}, U)` lie in `I^{n+1} Γ(B, U)`, and kernels of `Γ(G_{n+c}, U) → Γ(E_{n+c}, U)`
die in `Γ(G_n, U)`. -/
def ProIsoKer (U : X.Opens) (c : ℕ) : Prop :=
  (∀ n (b : Γ(B, U)), (u (n + c)).app U b = 0 →
    b ∈ (idealV f I U 1 ^ (n + 1) • ⊤ : Submodule Γ(X, U) Γ(B, U))) ∧
  (∀ n (g : Γ(G.obj (n + c), U)), (w (n + c)).app U g = 0 → (G.transition n c).app U g = 0)

variable {G B E u w}

section Values

variable {U : X.Opens} {c : ℕ} (hK : ProIsoKer G B E u w U c)
  (hC₁ : ∀ n (b : Γ(B, U)), ∃ g : Γ(G.obj n, U), (w n).app U g = (u n).app U b)

include hw hK in
/-- Kernels of `Γ(G_m, U) → Γ(E_m, U)` die in `Γ(G_n, U)` for `m ≥ n + c`. -/
lemma ProIsoKer.trans_eq_zero {n m : ℕ} (hm : n + c ≤ m) {g : Γ(G.obj m, U)}
    (hg : (w m).app U g = 0) : (G.trans (le_of_add_le_left hm)).app U g = 0 := by
  have h1 : (w (n + c)).app U ((G.trans hm).app U g) = 0 := by
    rw [← Scheme.Modules.Hom.comp_app_apply, ← proIso_w_comp G E w hw hm,
      Scheme.Modules.Hom.comp_app_apply, hg, map_zero]
  have h2 := hK.2 n _ h1
  rw [G.transition_eq_trans, ← Scheme.Modules.Hom.comp_app_apply, G.trans_trans] at h2
  exact h2

include hu hw hK in
/-- Two lifts of `u(b)` to `G` above level `n + c` have the same image in `Γ(G_n, U)`. -/
lemma ProIsoKer.trans_eq {n m m' : ℕ} (hm : n + c ≤ m) (hm' : n + c ≤ m') {b : Γ(B, U)}
    {g : Γ(G.obj m, U)} {g' : Γ(G.obj m', U)} (hg : (w m).app U g = (u m).app U b)
    (hg' : (w m').app U g' = (u m').app U b) :
    (G.trans (le_of_add_le_left hm)).app U g = (G.trans (le_of_add_le_left hm')).app U g' := by
  let x := (G.trans hm).app U g
  let x' := (G.trans hm').app U g'
  have hx : (w (n + c)).app U x = (u (n + c)).app U b := by
    rw [← Scheme.Modules.Hom.comp_app_apply, ← proIso_w_comp G E w hw hm,
      Scheme.Modules.Hom.comp_app_apply, hg, ← Scheme.Modules.Hom.comp_app_apply,
      proIso_u_comp B E u hu hm]
  have hx' : (w (n + c)).app U x' = (u (n + c)).app U b := by
    rw [← Scheme.Modules.Hom.comp_app_apply, ← proIso_w_comp G E w hw hm',
      Scheme.Modules.Hom.comp_app_apply, hg', ← Scheme.Modules.Hom.comp_app_apply,
      proIso_u_comp B E u hu hm']
  have h0 := hK.trans_eq_zero hw (le_refl (n + c)) (g := x - x')
    (by rw [map_sub, hx, hx', sub_self])
  rw [map_sub, sub_eq_zero] at h0
  rw [← G.trans_trans (le_of_add_le_left (le_refl (n + c))) hm,
    ← G.trans_trans (le_of_add_le_left (le_refl (n + c))) hm']
  exact h0

end Values

section Construction

variable (G B E u w) [B.IsQuasicoherent]
  (hK : ∀ U, IsAffineOpen U → ∃ c, ProIsoKer G B E u w U c)
  (hC₁ : ∀ U, IsAffineOpen U → ∀ n (b : Γ(B, U)),
    ∃ g : Γ(G.obj n, U), (w n).app U g = (u n).app U b)
  (hC₂ : ∀ U, IsAffineOpen U → ∀ n (g : Γ(G.obj n, U)),
    ∃ b : Γ(B, U), (u n).app U b = (w n).app U g)

/-- The value `v_n(b) ∈ Γ(G_n, U)` of the comparison map: the image of any lift to `G_{n+c}` of
`u_{n+c}(b)`. -/
def proIsoValue (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) (b : Γ(B, U)) : Γ(G.obj n, U) :=
  (G.trans (Nat.le_add_right n (hK U hU).choose)).app U
    (hC₁ U hU (n + (hK U hU).choose) b).choose

omit [B.IsQuasicoherent] in
include hu hw in
lemma proIsoValue_eq (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) (b : Γ(B, U)) {m : ℕ}
    (hm : n + (hK U hU).choose ≤ m) {g : Γ(G.obj m, U)} (hg : (w m).app U g = (u m).app U b) :
    proIsoValue G B E u w hK hC₁ n hU b = (G.trans (le_of_add_le_left hm)).app U g :=
  (hK U hU).choose_spec.trans_eq hu hw (le_refl _) hm
    (hC₁ U hU (n + (hK U hU).choose) b).choose_spec hg

/-- The comparison map `B ⟶ G_n`. -/
def proIsoHom (n : ℕ) : B ⟶ G.obj n :=
  AffineHomData.toHom
    { toFun := fun U hU ↦
        { toFun := proIsoValue G B E u w hK hC₁ n hU
          map_add' := fun b b' ↦ by
            obtain ⟨g, hg⟩ := hC₁ U hU (n + (hK U hU).choose) b
            obtain ⟨g', hg'⟩ := hC₁ U hU (n + (hK U hU).choose) b'
            rw [proIsoValue_eq G B E u w hu hw hK hC₁ n hU b le_rfl hg,
              proIsoValue_eq G B E u w hu hw hK hC₁ n hU b' le_rfl hg',
              proIsoValue_eq G B E u w hu hw hK hC₁ n hU (b + b') le_rfl (g := g + g')
                (by rw [map_add, map_add, hg, hg']), map_add]
          map_smul' := fun r b ↦ by
            obtain ⟨g, hg⟩ := hC₁ U hU (n + (hK U hU).choose) b
            rw [proIsoValue_eq G B E u w hu hw hK hC₁ n hU b le_rfl hg,
              proIsoValue_eq G B E u w hu hw hK hC₁ n hU (r • b) le_rfl (g := r • g)
                (by rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, hg]),
              Scheme.Modules.Hom.app_smul]
            rfl }
      naturality := fun {U V} hU hV hVU b ↦ by
        let m := n + max (hK U hU).choose (hK V hV).choose
        have hmU : n + (hK U hU).choose ≤ m := Nat.add_le_add_left (le_max_left _ _) n
        have hmV : n + (hK V hV).choose ≤ m := Nat.add_le_add_left (le_max_right _ _) n
        obtain ⟨g, hg⟩ := hC₁ U hU m b
        change proIsoValue G B E u w hK hC₁ n hV _ =
          (G.obj n).presheaf.map _ (proIsoValue G B E u w hK hC₁ n hU b)
        rw [proIsoValue_eq G B E u w hu hw hK hC₁ n hU b hmU hg,
          proIsoValue_eq G B E u w hu hw hK hC₁ n hV _ hmV
            (g := (G.obj m).presheaf.map (homOfLE hVU).op g)
            (by rw [hom_app_presheaf_map, hom_app_presheaf_map, hg]),
          hom_app_presheaf_map] }

include hu hw in
lemma proIsoHom_app (n : ℕ) {U : X.Opens} (hU : IsAffineOpen U) (b : Γ(B, U)) :
    (proIsoHom G B E u w hu hw hK hC₁ n).app U b = proIsoValue G B E u w hK hC₁ n hU b :=
  AffineHomData.toHom_app _ hU b

end Construction

section Main

variable [IsNoetherianRing A] (G B E u w) [B.IsQuasicoherent]
  (hK : ∀ U, IsAffineOpen U → ∃ c, ProIsoKer G B E u w U c)
  (hC₁ : ∀ U, IsAffineOpen U → ∀ n (b : Γ(B, U)),
    ∃ g : Γ(G.obj n, U), (w n).app U g = (u n).app U b)
  (hC₂ : ∀ U, IsAffineOpen U → ∀ n (g : Γ(G.obj n, U)),
    ∃ b : Γ(B, U), (u n).app U b = (w n).app U g)

include hu hw hK hC₁ hC₂ in
/-- **Algebraization by a pro-isomorphism** (the Artin–Rees argument of EGA III 5.1.4 and 4.1.5):
let `G` be an adic system on `X` over `(A, I)`, `B` quasi-coherent, and `u_n : B ⟶ E_n`,
`w_n : G_n ⟶ E_n` compatible maps to an inverse system `(E_n)`. Suppose that over every affine
open `U` the images of `u_n` and `w_n` coincide, and that for some `c` (depending on `U`) the
kernel of `Γ(B, U) → Γ(E_{n+c}, U)` lies in `I^{n+1} Γ(B, U)` and the kernel of
`Γ(G_{n+c}, U) → Γ(E_{n+c}, U)` dies in `Γ(G_n, U)`. Then `B / I^{n+1} B ≅ G_n` compatibly. -/
theorem exists_iso_quotientIdealPow_of_proIso :
    ∃ e : ∀ n, B.quotientIdealPow f I n ≅ G.obj n,
      ∀ n, (e (n + 1)).hom ≫ G.map n = B.quotientIdealPowMap f I n ≫ (e n).hom := by
  let v := proIsoHom G B E u w hu hw hK hC₁
  have hv : ∀ n, v (n + 1) ≫ G.map n = v n := fun n ↦ hom_ext_of_affine fun U hU b ↦ by
    let c := (hK U hU).choose
    obtain ⟨g, hg⟩ := hC₁ U hU (n + 1 + c) b
    rw [Scheme.Modules.Hom.comp_app_apply, proIsoHom_app G B E u w hu hw hK hC₁ _ hU,
      proIsoHom_app G B E u w hu hw hK hC₁ _ hU,
      proIsoValue_eq G B E u w hu hw hK hC₁ (n + 1) hU b le_rfl hg,
      proIsoValue_eq G B E u w hu hw hK hC₁ n hU b (show n + c ≤ n + 1 + c by omega) hg,
      ← G.trans_succ, ← Scheme.Modules.Hom.comp_app_apply, G.trans_trans]
  have hsmul : ∀ n, ∀ a ∈ I ^ (n + 1), smulA (G.obj n) f a = 0 :=
    fun n a ha ↦ G.smulA_eq_zero n ha
  have hiso : ∀ n, IsIso (descQuotientIdealPow I f n (v n) (hsmul n)) := by
    intro n
    refine isIso_descQuotientIdealPow I f n (v n) (fun {U} hU ↦ ⟨fun z ↦ ?_, fun b ↦ ?_⟩)
      (hsmul n)
    · let c := (hK U hU).choose
      obtain ⟨g, rfl⟩ := G.trans_surjective (Nat.le_add_right n c) hU z
      obtain ⟨b, hb⟩ := hC₂ U hU (n + c) g
      refine ⟨b, ?_⟩
      rw [proIsoHom_app G B E u w hu hw hK hC₁ _ hU,
        proIsoValue_eq G B E u w hu hw hK hC₁ n hU b le_rfl hb.symm]
    · constructor
      · intro hb
        let c := (hK U hU).choose
        obtain ⟨g, hg⟩ := hC₁ U hU (n + c) b
        rw [proIsoHom_app G B E u w hu hw hK hC₁ _ hU,
          proIsoValue_eq G B E u w hu hw hK hC₁ n hU b le_rfl hg,
          G.trans_app_eq_zero_iff _ hU] at hb
        obtain ⟨b', hb', hub'⟩ : ∃ b' ∈ (idealV f I U 1 ^ (n + 1) • ⊤ :
            Submodule Γ(X, U) Γ(B, U)), (u (n + c)).app U b' = (w (n + c)).app U g := by
          refine Submodule.smul_induction_on hb (fun r hr g₀ _ ↦ ?_) (fun g₁ g₂ h₁ h₂ ↦ ?_)
          · obtain ⟨b₀, hb₀⟩ := hC₂ U hU (n + c) g₀
            exact ⟨r • b₀, Submodule.smul_mem_smul hr Submodule.mem_top, by
              rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, hb₀]⟩
          · obtain ⟨b₁, hb₁, e₁⟩ := h₁
            obtain ⟨b₂, hb₂, e₂⟩ := h₂
            exact ⟨b₁ + b₂, Submodule.add_mem _ hb₁ hb₂, by rw [map_add, map_add, e₁, e₂]⟩
        have h0 := (hK U hU).choose_spec.1 n (b - b') (by rw [map_sub, hub', hg, sub_self])
        have := Submodule.add_mem _ h0 hb'
        rwa [sub_add_cancel] at this
      · intro hb
        refine G.eq_zero_of_mem n hU ?_
        exact mem_smul_top_of_linearMap _ (appLinearMap (v n) U) hb
  refine ⟨fun n ↦ asIso (descQuotientIdealPow I f n (v n) (hsmul n)), fun n ↦ ?_⟩
  rw [← cancel_epi (B.toQuotientIdealPow f I (n + 1)), asIso_hom, asIso_hom,
    toQuotientIdealPow_descQuotientIdealPow_assoc,
    Scheme.Modules.toQuotientIdealPow_comp_map_assoc, toQuotientIdealPow_descQuotientIdealPow,
    hv]

end Main

end ProIso

end AlgebraicGeometry.CohomologyAux
