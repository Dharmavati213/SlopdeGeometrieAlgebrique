/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import SGA.SGA1.ExposeIX.FiniteEtaleDescentDiagram
import SGA.SGA1.ExposeV.FundamentalGroupBasePoint
import SGA.SGA1.ExposeV.FundamentalGroupArtinian
import SGA.SGA1.ExposeV.FundamentalGroupLimit
import SGA.SGA1.ExposeIX.EtaleMorphismDescent
import SGA.Foundations.Cohomology.GeometricConnectedness

/-!
# SGA 1, Exposé IX, §6: a fundamental exact sequence

Abstract part: completely decomposed objects and sections (V.6.4); IX.6.2, which translates the
exactness of `π₁(X̄₀) → π₁(X) → π₁(S) → e` into "a covering of `X` comes from `S` iff it is
completely decomposed over `X̄₀`"; its variant IX.6.11 for a family of geometric fibres; the
splitting IX.6.4.

Scheme part: IX.6.1 is recorded as `ExactSequenceStatement` (exactness at `π₁(X̄₀)` and `π₁(X)` over
the spectrum of an artinian local ring). Proved: the surjectivity of `π₁(X) → π₁(S)` over any
one-point base (`surjective_autMap_of_subsingleton`); the last assertion `π₁(S) ≅ Gal(k̄/k)` for `S`
the spectrum of an artinian local ring, via IX.1.7
(`nonempty_aut_continuousMulEquiv_absoluteGaloisGroup_of_artinian`); the triviality of `π₁(X̄₀) →
π₁(X) → π₁(S)` over any base (`range_le_ker_geometricFiber`); and exactness at `π₁(X)` when `S` is
the spectrum of an artinian local ring (or of a field) and `X₀` is quasi-compact and quasi-separated
(`range_eq_ker_of_artinian`, `range_eq_ker_of_isIso_fromSpecResidueField`), by SGA's passage to the
limit over the finite subextensions of `k̄/k` (EGA IV 8.8.2 for morphisms,
`SGA.SGA1.ExposeV.exists_finiteSubext_hom`), IX.4.10 for `X ⊗ k̄ ⟶ X ⊗ k_s` and IX.1.7. IX.6.2
follows in that case (`isGeometricallyTrivial_iff_isCompletelyDecomposed_of_artinian`). IX.6.4 is
proved from a section. IX.6.5, IX.6.7–IX.6.9 and IX.6.11 are recorded as statements (they need
IX.1.10 over a complete local base); the inclusion `⊇` in IX.6.11
(`normalClosure_le_ker_geometricFibres`) is proved, and the full faithfulness in IX.6.8 and the
surjectivity in IX.6.11 are proved for connected schemes, also when `𝒪_S ≅ f_* 𝒪_X` (EGA III 4.3.4),
and the factorization of IX.6.9 is proved (`exists_geometricallyConnected_comp_isFinite`). These are
proved for arbitrary Galois structures and fibre functors, and for the fundamental groups of Exposé
V at geometric points (`surjective_etaleFundamentalGroup_map_*`, `full_etalePullback_of_isProper`,
`exists_section_etaleFundamentalGroup_map`). IX.6.3, IX.6.6, IX.6.10 and IX.6.12 are not formalized.
-/

universe u₁ u₂ u₃ u₄ u₅ u₆ w u

namespace SGA.SGA1.ExposeIX

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits PreGaloisCategory

section completelyDecomposed

/-- An object of a Galois category is *completely decomposed* if it is a finite sum of copies of
the final object (V.6.4). -/
def IsCompletelyDecomposed {C : Type u₁} [Category.{u₂} C] [PreGaloisCategory C] (Z : C) : Prop :=
  ∃ n : ℕ, Nonempty (Z ≅ ∐ fun _ : Fin n ↦ ⊤_ C)

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w})
  [FiberFunctor F]

/-- A point of the fibre of `Z` fixed by `Aut F` comes from a section `⊤ ⟶ Z`. -/
lemma exists_hom_terminal_of_smul_eq {Z : C} (z : F.obj Z) (hz : ∀ σ : Aut F, σ • z = z) :
    ∃ s : ⊤_ C ⟶ Z, ∀ t, F.map s t = z := by
  let φ : (functorToAction F).obj (⊤_ C) ⟶ (functorToAction F).obj Z :=
    ⟨FintypeCat.homMk fun _ ↦ z, fun σ ↦ by
      ext t
      exact (hz σ).symm⟩
  obtain ⟨s, hs⟩ := (functorToAction F).map_surjective φ
  exact ⟨s, fun t ↦ ConcreteCategory.congr_hom (congrArg Action.Hom.hom hs) t⟩

/-- V.6.4: `Z` has a section (a morphism from the final object) if and only if `Aut F` has a
fixed point in the fibre of `Z`. -/
lemma nonempty_hom_terminal_iff (Z : C) :
    Nonempty (⊤_ C ⟶ Z) ↔ ∃ z : F.obj Z, ∀ σ : Aut F, σ • z = z := by
  refine ⟨fun ⟨s⟩ ↦ ?_, fun ⟨z, hz⟩ ↦ ⟨(exists_hom_terminal_of_smul_eq F z hz).choose⟩⟩
  obtain ⟨t⟩ : Nonempty (F.obj (⊤_ C)) := inferInstance
  refine ⟨F.map s t, fun σ ↦ ?_⟩
  rw [mulAction_naturality]
  congr 1
  exact Subsingleton.elim _ _

/-- The fibre of a finite sum of final objects consists of the images of the point of the fibre
of the final object. -/
lemma exists_eq_map_ι {n : ℕ} (x : F.obj (∐ fun _ : Fin n ↦ ⊤_ C)) (t : F.obj (⊤_ C)) :
    ∃ j, F.map (Sigma.ι (fun _ : Fin n ↦ ⊤_ C) j) t = x := by
  obtain ⟨⟨j⟩, y, hy⟩ := Limits.FintypeCat.jointly_surjective
    (Discrete.functor (fun _ : Fin n ↦ ⊤_ C) ⋙ F) _
    (isColimitOfPreserves F (colimit.isColimit _)) x
  refine ⟨j, ?_⟩
  rw [← hy, Subsingleton.elim t y]
  rfl

/-- V.6.4: an object is completely decomposed if and only if `Aut F` acts trivially on its
fibre. -/
theorem isCompletelyDecomposed_iff (Z : C) :
    IsCompletelyDecomposed Z ↔ ∀ (σ : Aut F) (z : F.obj Z), σ • z = z := by
  obtain ⟨t⟩ : Nonempty (F.obj (⊤_ C)) := inferInstance
  constructor
  · rintro ⟨n, ⟨e⟩⟩ σ z
    obtain ⟨j, hj⟩ := exists_eq_map_ι F (F.map e.hom z) t
    have hz : z = F.map e.inv (F.map e.hom z) := (FintypeCat.hom_inv_id_apply (F.mapIso e) z).symm
    rw [hz, mulAction_naturality, ← hj, mulAction_naturality, Subsingleton.elim (σ • t) t]
  · intro h
    let e := Finite.equivFin (F.obj Z)
    choose s hs using fun j ↦ exists_hom_terminal_of_smul_eq F (e.symm j) (fun σ ↦ h σ _)
    let φ : (∐ fun _ : Fin (Nat.card (F.obj Z)) ↦ ⊤_ C) ⟶ Z := Sigma.desc s
    have hφ (j) : F.map φ (F.map (Sigma.ι _ j) t) = e.symm j := by
      rw [← FintypeCat.comp_apply, ← F.map_comp, Sigma.ι_desc, hs]
    have hbij : Function.Bijective (F.map φ) := by
      refine ⟨fun x y hxy ↦ ?_, fun z ↦ ⟨F.map (Sigma.ι _ (e z)) t, by rw [hφ, e.symm_apply_apply]⟩⟩
      obtain ⟨i, rfl⟩ := exists_eq_map_ι F x t
      obtain ⟨j, rfl⟩ := exists_eq_map_ι F y t
      rw [hφ, hφ, e.symm.apply_eq_iff_eq] at hxy
      rw [hxy]
    have : IsIso (F.map φ) := (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    have : IsIso φ := isIso_of_reflects_iso φ F
    exact ⟨_, ⟨(asIso φ).symm⟩⟩

end completelyDecomposed

section IX62

variable {C : Type u₁} [Category.{u₂} C] {C' : Type u₃} [Category.{u₄} C']
  {C'' : Type u₅} [Category.{u₆} C''] [GaloisCategory C] [GaloisCategory C'] [GaloisCategory C'']
  (H : C ⥤ C') (K : C' ⥤ C'') (F'' : C'' ⥤ FintypeCat.{w}) [FiberFunctor F'']
  [FiberFunctor (K ⋙ F'')] [FiberFunctor (H ⋙ K ⋙ F'')]

/-- The closed normal subgroup of `π₁(X)` generated by the image of `π₁(X̄₀) → π₁(X)`. -/
abbrev normalClosureRange : Subgroup (Aut (K ⋙ F'')) :=
  (Subgroup.normalClosure (Set.range (autMap K F''))).topologicalClosure

instance normalClosureRange_normal : (normalClosureRange K F'').Normal :=
  Subgroup.is_normal_topologicalClosure _

omit [GaloisCategory C'] [FiberFunctor (K ⋙ F'')] in
lemma forall_mem_normalClosureRange_smul_eq_iff (Y : C') :
    (∀ σ ∈ normalClosureRange K F'', ∀ y : (K ⋙ F'').obj Y, σ • y = y) ↔
      IsCompletelyDecomposed (K.obj Y) := by
  rw [forall_mem_normalClosure_smul_eq_iff, isCompletelyDecomposed_iff F'']
  exact ⟨fun h g y ↦ h _ ⟨g, rfl⟩ y, fun h _ ⟨g, hg⟩ y ↦ hg ▸ h g y⟩

/-- IX.6.2, (i) ⇔ (ii), and the N.B. that follows it (abstract form): when `π₁(X) → π₁(S)` is
surjective, its kernel is the closed normal subgroup generated by the image of `π₁(X̄₀)` if and
only if a covering `X'` of `X` comes from `S` exactly when `X̄'₀` is completely decomposed over
`X̄₀`. -/
theorem ker_eq_normalClosureRange_iff (hu : Function.Surjective (autMap H (K ⋙ F''))) :
    (autMap H (K ⋙ F'')).ker = normalClosureRange K F'' ↔
      ∀ Y : C', H.essImage Y ↔ IsCompletelyDecomposed (K.obj Y) := by
  rw [ker_autMap_eq_iff H (K ⋙ F'') hu (normalClosureRange K F'')
    (Subgroup.isClosed_topologicalClosure _)]
  simp only [forall_mem_normalClosureRange_smul_eq_iff]

/-- IX.6.2, (i) ⇔ (ii) (abstract form): under the exactness of IX.6.1 at `π₁(X)` and `π₁(S)`, a
covering `X'` of `X` comes from a covering of `S` if and only if `X̄'₀` is completely decomposed. -/
theorem mem_essImage_iff_isCompletelyDecomposed (hu : Function.Surjective (autMap H (K ⋙ F'')))
    (hker : (autMap H (K ⋙ F'')).ker = (autMap K F'').range) (Y : C') :
    H.essImage Y ↔ IsCompletelyDecomposed (K.obj Y) := by
  refine (ker_eq_normalClosureRange_iff H K F'' hu).mp ?_ Y
  have : (autMap K F'').range.Normal := hker ▸ MonoidHom.normal_ker _
  have hc : IsClosed ((autMap K F'').range : Set (Aut (K ⋙ F''))) := by
    rw [← hker, MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (continuous_autMap H (K ⋙ F''))
  rw [hker, normalClosureRange, ← MonoidHom.coe_range, Subgroup.normalClosure_eq_self]
  exact (Subgroup.topologicalClosure_minimal _ le_rfl hc).antisymm
    (Subgroup.le_topologicalClosure _) |>.symm

/-- IX.6.2, (ii) ⇔ (ii bis) (abstract form): if the image of `π₁(X̄₀)` is a normal subgroup (for
instance under the exactness of IX.6.1) and `X'` is connected, then `X̄'₀` is completely decomposed
as soon as it has a section. -/
theorem isCompletelyDecomposed_iff_nonempty_hom (hn : (autMap K F'').range.Normal) (Y : C')
    [IsConnected Y] : IsCompletelyDecomposed (K.obj Y) ↔ Nonempty (⊤_ C'' ⟶ K.obj Y) := by
  rw [isCompletelyDecomposed_iff F'', nonempty_hom_terminal_iff F'']
  constructor
  · intro h
    obtain ⟨y⟩ := nonempty_fiber_of_isConnected (K ⋙ F'') Y
    exact ⟨y, fun σ ↦ h σ y⟩
  · rintro ⟨y₀, hy₀⟩ g y
    let y₁ : (K ⋙ F'').obj Y := y₀
    let y₂ : (K ⋙ F'').obj Y := y
    obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (Aut (K ⋙ F'')) y₁ y₂
    obtain ⟨g', hg'⟩ : τ⁻¹ * autMap K F'' g * τ ∈ (autMap K F'').range := by
      simpa using hn.conj_mem' _ ⟨g, rfl⟩ τ
    have h1 : autMap K F'' g' • y₁ = y₁ := hy₀ g'
    have key : autMap K F'' g • y₂ = y₂ := by
      rw [← hτ, smul_smul, show autMap K F'' g * τ = τ * autMap K F'' g' by rw [hg']; group,
        mul_smul, h1]
    exact key

omit [GaloisCategory C] [GaloisCategory C'] [FiberFunctor (H ⋙ K ⋙ F'')] in
/-- IX.6.1, `π₁(X̄₀) → π₁(X) → π₁(S)` is trivial (abstract form): if the inverse images in `C''`
of the objects of `C` are completely decomposed, the image of `Aut F''` is contained in the kernel
of `Aut (K ⋙ F'') → Aut (H ⋙ K ⋙ F'')`. -/
theorem range_le_ker_of_isCompletelyDecomposed
    (h : ∀ Z : C, IsCompletelyDecomposed (K.obj (H.obj Z))) :
    (autMap K F'').range ≤ (autMap H (K ⋙ F'')).ker := by
  rintro _ ⟨g, rfl⟩
  rw [MonoidHom.mem_ker]
  apply Iso.ext
  ext Z z
  exact (isCompletelyDecomposed_iff F'' _).1 (h Z) g z

omit [GaloisCategory C] [FiberFunctor (H ⋙ K ⋙ F'')] in
/-- IX.6.1, exactness at `π₁(X)` (abstract form, the inclusion `ker ⊆ im`): suppose that every
section `T ⟶ K(Y)` over the final object `T` of `C''` of the inverse image of an object `Y` of `C'`
factors through `K(u) : K(H(Z)) ⟶ K(Y)` for some `u : H(Z) ⟶ Y`. Then the kernel of
`Aut (K ⋙ F'') → Aut (H ⋙ K ⋙ F'')` is contained in the image of `Aut F''`. (In IX.6.1 this is where
SGA passes to the limit over the finite subextensions of `k̄/k`.) -/
theorem ker_le_range_of_forall_section {T : C''} (hT : IsTerminal T)
    (h : ∀ (Y : C') (t : T ⟶ K.obj Y), ∃ (Z : C) (u : H.obj Z ⟶ Y) (t' : T ⟶ K.obj (H.obj Z)),
      t' ≫ K.map u = t) :
    (autMap H (K ⋙ F'')).ker ≤ (autMap K F'').range := by
  intro σ hσ
  by_contra hσR
  have hR : IsClosed ((autMap K F'').range : Set (Aut (K ⋙ F''))) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (continuous_autMap K F'')).isClosed
  obtain ⟨V, hVn, hVo, hσV⟩ := exists_normal_isOpen_notMem_sup (K ⋙ F'') hR hσR
  set U := (autMap K F'').range ⊔ V with hU
  have hUo : IsOpen (U : Set (Aut (K ⋙ F''))) := Subgroup.isOpen_mono le_sup_right hVo
  have : Finite (Aut (K ⋙ F'') ⧸ U) := U.quotient_finite_of_isOpen hUo
  have hstab (x : Aut (K ⋙ F'') ⧸ U) :
      IsOpen (MulAction.stabilizer (Aut (K ⋙ F'')) x : Set (Aut (K ⋙ F''))) := by
    refine Subgroup.isOpen_mono (fun τ hτ ↦ ?_) hVo
    induction x using QuotientGroup.induction_on with | H g => ?_
    change τ • (g : Aut (K ⋙ F'') ⧸ U) = g
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    apply (le_sup_right : V ≤ U)
    simpa [mul_assoc] using hVn.conj_mem _ (V.inv_mem hτ) g⁻¹
  obtain ⟨Y, e, he⟩ := exists_fiber_equiv (K ⋙ F'') (Aut (K ⋙ F'') ⧸ U) hstab
  let y : (K ⋙ F'').obj Y := e.symm (QuotientGroup.mk 1)
  have hfix (g : Aut F'') : g.hom.app (K.obj Y) y = y := by
    apply e.injective
    change e (autMap K F'' g • y) = e y
    rw [he, e.apply_symm_apply, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
      QuotientGroup.eq, mul_one]
    exact (le_sup_left : (autMap K F'').range ≤ U) (Subgroup.inv_mem _ ⟨g, rfl⟩)
  obtain ⟨t₀, ht₀⟩ := exists_hom_terminal_of_smul_eq F'' (Z := K.obj Y) y hfix
  obtain ⟨Z, u, t', hu⟩ := h Y (terminalIsTerminal.from T ≫ t₀)
  obtain ⟨p⟩ : Nonempty (F''.obj T) :=
    ⟨F''.map (hT.uniqueUpToIso terminalIsTerminal).inv (Classical.arbitrary _)⟩
  have hy : (K ⋙ F'').map u (F''.map t' p) = y := by
    change (F''.map t' ≫ F''.map (K.map u)) p = y
    rw [← F''.map_comp, hu, F''.map_comp, FintypeCat.comp_apply, ht₀]
  have h1 : σ.hom.app (H.obj Z) = 𝟙 _ :=
    congrArg (fun τ : Aut (H ⋙ K ⋙ F'') ↦ τ.hom.app Z) ((MonoidHom.mem_ker).1 hσ)
  have hσy : σ • y = y := by
    change σ.hom.app Y y = y
    rw [← hy, FunctorToFintypeCat.naturality, h1]
    rfl
  have h2 := he σ y
  rw [hσy, e.apply_symm_apply, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
    QuotientGroup.eq, inv_one, one_mul] at h2
  exact hσV h2

end IX62

section family

variable {C : Type u₁} [Category.{u₂} C] {C' : Type u₃} [Category.{u₄} C'] [GaloisCategory C]
  [GaloisCategory C'] (H : C ⥤ C') (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F']
  [FiberFunctor (H ⋙ F')] {ι : Type*} {D : ι → Type u₅} [∀ i, Category.{u₆} (D i)]
  [∀ i, GaloisCategory (D i)] (K : ∀ i, C' ⥤ D i) (G : ∀ i, D i ⥤ FintypeCat.{w})
  [∀ i, FiberFunctor (G i)] (d : ∀ i, K i ⋙ G i ≅ F')

/-- The homomorphism `π₁(X̄ᵢ, aᵢ) → π₁(X, a)` given by a functor `Kᵢ` (the inverse image to a
geometric fibre) and a class of paths `dᵢ : Gᵢ ∘ Kᵢ ≅ F'`. -/
def pathMap (i : ι) : Aut (G i) →* Aut F' :=
  (d i).conjAut.toMonoidHom.comp (autMap (K i) (G i))

omit [GaloisCategory C'] [FiberFunctor F'] [∀ i, GaloisCategory (D i)]
  [∀ i, FiberFunctor (G i)] in
lemma pathMap_smul (i : ι) (g : Aut (G i)) {Y : C'} (y : (G i).obj ((K i).obj Y)) :
    pathMap F' K G d i g • (d i).hom.app Y y = (d i).hom.app Y (g • y) := by
  change ((d i).conjAut (autMap (K i) (G i) g)).hom.app Y ((d i).hom.app Y y) = _
  rw [Iso.conjAut_hom, Iso.conj_apply]
  simp [mulAction_def]

omit [GaloisCategory C'] [FiberFunctor F'] in
lemma forall_pathMap_smul_eq_iff (i : ι) (Y : C') :
    (∀ (g : Aut (G i)) (y : F'.obj Y), pathMap F' K G d i g • y = y) ↔
      IsCompletelyDecomposed ((K i).obj Y) := by
  rw [isCompletelyDecomposed_iff (G i)]
  let e := FintypeCat.equivEquivIso.symm ((d i).app Y)
  refine ⟨fun h g y ↦ e.injective ?_, fun h g y ↦ ?_⟩
  · exact (pathMap_smul F' K G d i g y).symm.trans (h g _)
  · obtain ⟨y, rfl⟩ := e.surjective y
    change pathMap F' K G d i g • (d i).hom.app Y y = (d i).hom.app Y y
    rw [pathMap_smul, h]

/-- IX.6.11 (abstract form): when `π₁(X) → π₁(S)` is surjective, its kernel is the closed normal
subgroup generated by the images of the `π₁(X̄ᵢ) → π₁(X)` if and only if a covering of `X` comes
from `S` exactly when its inverse images to all the `X̄ᵢ` are completely decomposed. -/
theorem ker_eq_iff_forall_isCompletelyDecomposed (hu : Function.Surjective (autMap H F')) :
    (autMap H F').ker =
        (Subgroup.normalClosure (⋃ i, Set.range (pathMap F' K G d i))).topologicalClosure ↔
      ∀ Y : C', H.essImage Y ↔ ∀ i, IsCompletelyDecomposed ((K i).obj Y) := by
  rw [ker_autMap_eq_iff_of_family H F' hu (pathMap F' K G d)]
  simp only [forall_pathMap_smul_eq_iff]

omit [GaloisCategory C] [GaloisCategory C'] [FiberFunctor F'] [FiberFunctor (H ⋙ F')] in
/-- IX.6.11 (abstract form, inclusion `⊆`): if the inverse images in the `D i` of the objects of
`C` are completely decomposed, the closed normal subgroup generated by the images of the
`π₁(X̄ᵢ) → π₁(X)` is contained in the kernel of `π₁(X) → π₁(S)`. -/
theorem normalClosure_le_ker_of_forall_isCompletelyDecomposed
    (h : ∀ i (Z : C), IsCompletelyDecomposed ((K i).obj (H.obj Z))) :
    (Subgroup.normalClosure (⋃ i, Set.range (pathMap F' K G d i))).topologicalClosure ≤
      (autMap H F').ker := by
  have hc : IsClosed ((autMap H F').ker : Set (Aut F')) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (continuous_autMap H F')
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hc
  rintro _ ⟨_, ⟨i, rfl⟩, g, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  apply Iso.ext
  ext Z y
  exact (forall_pathMap_smul_eq_iff F' K G d i (H.obj Z)).mpr (h i Z) g y

end family

section splitting

variable {C : Type u₁} [Category.{u₂} C] {C' : Type u₃} [Category.{u₄} C']
  (H : C ⥤ C') (R : C' ⥤ C) (F' : C' ⥤ FintypeCat.{w})
  (η : R ⋙ H ⋙ F' ≅ F') (ε : H ⋙ R ≅ 𝟭 C)

/-- The homomorphism `π₁(S, b) → π₁(X, a)` induced by a section `S → X` through `a`: `R` is the
inverse image along the section and `η` identifies the fibre functors. -/
def sectionAutMap : Aut (H ⋙ F') →* Aut F' :=
  η.conjAut.toMonoidHom.comp (autMap R (H ⋙ F'))

lemma continuous_sectionAutMap : Continuous (sectionAutMap H R F' η) :=
  (continuous_conjAut η).comp (continuous_autMap R (H ⋙ F'))

/-- IX.6.4 (abstract form): if the inverse image along a section retracts `H` compatibly with the
fibre functors, then the induced continuous homomorphism is a section of `π₁(X) → π₁(S)`, so that
the exact sequence IX.6.1 splits. -/
theorem autMap_sectionAutMap
    (hη : ∀ X : C, F'.map (H.map (ε.hom.app X)) = η.hom.app (H.obj X)) (σ : Aut (H ⋙ F')) :
    autMap H F' (sectionAutMap H R F' η σ) = σ := by
  ext X : 3
  change (η.conjAut (autMap R (H ⋙ F') σ)).hom.app (H.obj X) = σ.hom.app X
  rw [Iso.conjAut_hom, Iso.conj_apply]
  simp only [NatTrans.comp_app, autMap_hom_app]
  have hn := σ.hom.naturality (ε.hom.app X)
  rw [← hη, ← Functor.comp_map]
  erw [← hn]
  simp only [Functor.comp_map, hη, Iso.inv_hom_id_app_assoc]
  rfl

end splitting

section schemes

open AlgebraicGeometry

local notation "FEt" => (SGA.SGA1.ExposeV.finiteEtaleHom : MorphismProperty Scheme)

variable {X S : Scheme.{u}}

/-- A connected scheme finite over a one-point scheme is a point. -/
lemma subsingleton_of_isFinite {T : Scheme.{u}} (t : T ⟶ S) [IsFinite t] [Subsingleton S]
    [ConnectedSpace T] : Subsingleton T := by
  obtain ⟨x₀⟩ : Nonempty T := inferInstance
  have : DiscreteTopology T := by
    rw [← isDiscrete_univ_iff]
    have h : t ⁻¹' {t x₀} = Set.univ := by
      ext x
      simp [Subsingleton.elim (t x) (t x₀)]
    exact h ▸ t.isDiscrete_preimage_singleton (t x₀)
  exact ⟨fun x y ↦ PreconnectedSpace.constant (Y := T) inferInstance continuous_id⟩

/-- A geometrically connected scheme over a base, pulled back to a one-point scheme, is
connected. -/
lemma connectedSpace_pullback_of_subsingleton {T : Scheme.{u}} (t : T ⟶ S) (f : X ⟶ S)
    [GeometricallyConnected f] [Subsingleton T] [Nonempty T] : ConnectedSpace ↥(pullback t f) :=
  GeometricallyConnected.connectedSpace_of_subsingleton (pullback.fst t f)

/-- IX.6.1 (surjectivity), over a one-point base: if `S` has a single point and `f : X ⟶ S` is
geometrically connected, then the inverse image of a connected finite étale covering of `S` is
connected. By V.6.9 this is the surjectivity of `π₁(X) → π₁(S)`. -/
theorem preservesIsConnected_pullback_of_subsingleton [Subsingleton S] (f : X ⟶ S)
    [GeometricallyConnected f] :
    PreservesIsConnected (MorphismProperty.Over.pullback FEt ⊤ f) where
  preserves {T} _ := by
    have : ConnectedSpace ((𝟭 Scheme).obj T.left) := connectedSpace_of_isConnected T
    have : IsFinite T.hom := T.prop.1
    have := subsingleton_of_isFinite (S := S) T.hom
    have : ConnectedSpace ((MorphismProperty.Over.pullback FEt ⊤ f).obj T).left :=
      connectedSpace_pullback_of_subsingleton (X := X) (S := S) T.hom f
    exact isConnected_of_connectedSpace _

/-- The spectrum of an artinian local ring has a single point. -/
instance subsingleton_spec_of_isArtinianRing (A : CommRingCat.{u}) [IsArtinianRing A]
    [IsLocalRing A] : Subsingleton (Spec A) :=
  Ring.KrullDimLE.subsingleton_primeSpectrum A

/-- The geometric fibre `X̄_s = X_s ⊗_{κ(s)} \overline{κ(s)}` of `f` at `s`. -/
noncomputable def geometricFiber (f : X ⟶ S) (s : S) : Scheme.{u} :=
  pullback (f.fiberToSpecResidueField s) (Spec.map (CommRingCat.ofHom
    (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))))

/-- The morphism `X̄_s ⟶ X`. -/
noncomputable def geometricFiberι (f : X ⟶ S) (s : S) : geometricFiber f s ⟶ X :=
  pullback.fst _ _ ≫ f.fiberι s

/-- A finite étale covering `Y` of `X` is *geometrically trivial* relative to `f : X ⟶ S` if it is
isomorphic over `X` to `X ×_S T` for a finite étale `S`-scheme `T` (condition (i) of IX.6.2, used
after IX.6.2 when `S` is the spectrum of an artinian local ring or of a field). -/
def IsGeometricallyTrivial (f : X ⟶ S) (Y : MorphismProperty.Over FEt ⊤ X) : Prop :=
  (MorphismProperty.Over.pullback FEt ⊤ f).essImage Y

/-- IX.6.1, exactness at `π₁(X̄₀)` and at `π₁(X)` (statement only). Let `S` be the spectrum of an
artinian local ring, `s` its point, `f : X ⟶ S` with quasi-compact geometrically connected fibre
`X₀ = X_s`, and `X̄₀` the geometric fibre. Then `e → π₁(X̄₀) → π₁(X) → π₁(S)` is exact. The
fundamental groups are the automorphism groups of a fibre functor `F''` on the finite étale
coverings of `X̄₀` and of its composites with the inverse image functors (the categories of étale
coverings are Galois categories by V.7). The rest of IX.6.1 is proved: the surjectivity of
`π₁(X) → π₁(S)` (`surjective_autMap_of_subsingleton`) and `π₁(S) ≅ Gal(k̄/k)`
(`nonempty_aut_continuousMulEquiv_absoluteGaloisGroup_of_artinian`); so is exactness at `π₁(X)`
when `X₀` is moreover quasi-separated (`range_eq_ker_of_artinian`). The injectivity of
`π₁(X̄₀) → π₁(X)` (which needs the limit theorem for étale coverings, EGA IV 8.8.2 for objects) is
open. -/
def ExactSequenceStatement : Prop :=
  ∀ (S X : Scheme.{u}) (f : X ⟶ S) (s : S),
    (∃ A : CommRingCat.{u}, IsArtinianRing A ∧ IsLocalRing A ∧ Nonempty (S ≅ Spec A)) →
    CompactSpace (f.fiber s) → GeometricallyConnected (f.fiberToSpecResidueField s) →
    ∀ (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{u}) [FiberFunctor F'']
      [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
      [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
        MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')],
      Function.Injective (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) F'') ∧
      (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) F'').range =
        (autMap (MorphismProperty.Over.pullback FEt ⊤ f)
          (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')).ker

/-- The spectrum of an artinian local ring has a single point. -/
lemma subsingleton_of_artinian {S : Scheme.{u}}
    (hA : ∃ A : CommRingCat.{u}, IsArtinianRing A ∧ IsLocalRing A ∧ Nonempty (S ≅ Spec A)) :
    Subsingleton S := by
  obtain ⟨A, _, _, ⟨e⟩⟩ := hA
  exact (Scheme.homeoOfIso e).injective.subsingleton

/-- IX.6.1, last assertion: if `S` is the spectrum of an artinian local ring and `s` its point,
`π₁(S) ≅ Gal(k̄/k)` for the residue field `k = κ(s)`: the automorphism group of any fibre functor
on the étale coverings of `S` is isomorphic to the absolute Galois group of `κ(s)`. Étale
coverings of `S` and of `Spec κ(s)` correspond (IX.1.7), and V.8.1 applies. -/
theorem nonempty_aut_continuousMulEquiv_absoluteGaloisGroup_of_artinian (s : S)
    (hA : ∃ A : CommRingCat.{u}, IsArtinianRing A ∧ IsLocalRing A ∧ Nonempty (S ≅ Spec A))
    (F : MorphismProperty.Over FEt ⊤ S ⥤ FintypeCat.{u}) [FiberFunctor F] :
    Nonempty (Aut F ≃ₜ* Field.absoluteGaloisGroup (S.residueField s)) := by
  have : Subsingleton S := subsingleton_of_artinian hA
  have : ConnectedSpace S :=
    { isPreconnected_univ := Set.subsingleton_of_subsingleton.isPreconnected
      toNonempty := ⟨s⟩ }
  obtain ⟨A, _, _, ⟨e⟩⟩ := hA
  exact SGA.SGA1.ExposeV.nonempty_aut_continuousMulEquiv_absoluteGaloisGroup_residueField A e s F

/-- IX.6.1, surjectivity of `π₁(X) → π₁(S)` for `S` with a single point (for instance the
spectrum of an artinian local ring) and `X` with geometrically connected fibre, for any Galois
structures and compatible fibre functors on the categories of finite étale coverings. -/
theorem surjective_autMap_of_subsingleton [Subsingleton S] (f : X ⟶ S) (s : S)
    (hs : GeometricallyConnected (f.fiberToSpecResidueField s))
    (F : MorphismProperty.Over FEt ⊤ X ⥤ FintypeCat.{w}) [FiberFunctor F]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙ F)] :
    Function.Surjective (autMap (MorphismProperty.Over.pullback FEt ⊤ f) F) := by
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor
    (MorphismProperty.Over.pullback FEt ⊤ f ⋙ F)
  have : GeometricallyConnected f :=
    (GeometricallyConnected.iff_geometricallyConnected_fiber f).mpr fun s' ↦
      Subsingleton.elim s s' ▸ hs
  have := preservesIsConnected_pullback_of_subsingleton f
  exact surjective_of_preservesIsConnected _ F

/-- IX.6.2, (i) ⇔ (ii), assuming the exact sequence IX.6.1: a finite étale covering `Y` of `X`
comes from a finite étale covering of `S` if and only if its inverse image to the geometric fibre
`X̄₀` is completely decomposed. -/
theorem isGeometricallyTrivial_iff_isCompletelyDecomposed (h : ExactSequenceStatement.{u})
    (f : X ⟶ S) (s : S)
    (hA : ∃ A : CommRingCat.{u}, IsArtinianRing A ∧ IsLocalRing A ∧ Nonempty (S ≅ Spec A))
    (hc : CompactSpace (f.fiber s)) (hg : GeometricallyConnected (f.fiberToSpecResidueField s))
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{u}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    (Y : MorphismProperty.Over FEt ⊤ X) :
    IsGeometricallyTrivial f Y ↔
      IsCompletelyDecomposed
        ((MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)).obj Y) := by
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F''
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor
    (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
    MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  obtain ⟨-, hrange⟩ := h S X f s hA hc hg F''
  have : Subsingleton S := subsingleton_of_artinian hA
  have hsurj := surjective_autMap_of_subsingleton f s hg
    (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  exact mem_essImage_iff_isCompletelyDecomposed _ _ F'' hsurj hrange.symm Y

/-- IX.6.2, (ii) ⇔ (ii bis), assuming the exact sequence IX.6.1: for a connected covering `Y`, its
inverse image to `X̄₀` is completely decomposed as soon as it has a section. -/
theorem isCompletelyDecomposed_iff_nonempty_section (h : ExactSequenceStatement.{u})
    (f : X ⟶ S) (s : S)
    (hA : ∃ A : CommRingCat.{u}, IsArtinianRing A ∧ IsLocalRing A ∧ Nonempty (S ≅ Spec A))
    (hc : CompactSpace (f.fiber s)) (hg : GeometricallyConnected (f.fiberToSpecResidueField s))
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{u}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    (Y : MorphismProperty.Over FEt ⊤ X) [ConnectedSpace Y.left] :
    IsCompletelyDecomposed ((MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)).obj Y) ↔
      Nonempty (⊤_ _ ⟶ (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)).obj Y) := by
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F''
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor
    (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  obtain ⟨-, hrange⟩ := h S X f s hA hc hg F''
  have := isConnected_of_connectedSpace Y
  exact isCompletelyDecomposed_iff_nonempty_hom _ F'' (hrange ▸ MonoidHom.normal_ker _) Y

/-- The morphism of fibres `X'_s ⟶ X_s` induced by `p : X' ⟶ X` over `S`. -/
noncomputable def fiberMap {X' : Scheme.{u}} (p : X' ⟶ X) (f : X ⟶ S) (s : S) :
    (p ≫ f).fiber s ⟶ f.fiber s :=
  pullback.map _ _ _ _ p (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- IX.6.5 (statement only). Let `f : X ⟶ S` be proper, surjective, of finite presentation, with
geometrically connected fibres, `p : X' ⟶ X` proper and of finite presentation, `s ∈ S`, and `F'₁`
the connected component of a point `x'` in the fibre `X'_s`. There exist an open neighbourhood
`X'₁` of `F'₁` in `X'`, an étale `S`-scheme `S'₁` and an `X`-isomorphism `X'₁ ≅ S'₁ ×_S X` if and
only if `X'` is étale over `X` at the points of `F'₁` and `F'₁` is a geometrically trivial covering
of `F = X_s`. The last condition is expressed by an open subscheme `W` of the fibre `X'_s` with
underlying set `F'₁`, finite étale and geometrically trivial over `X_s`. -/
def LocalProperDescentStatement : Prop :=
  ∀ (X X' S : Scheme.{u}) (f : X ⟶ S) (p : X' ⟶ X) [IsProper f] [Surjective f]
    [LocallyOfFinitePresentation f] [GeometricallyConnected f] [IsProper p]
    [LocallyOfFinitePresentation p] (s : S) (x' : X'), (p ≫ f) x' = s →
    ((∃ (U : X'.Opens) (T : Scheme.{u}) (t : T ⟶ S) (e : (U : Scheme.{u}) ≅ pullback t f),
        connectedComponentIn ((p ≫ f) ⁻¹' {s}) x' ⊆ U ∧ Etale t ∧
          e.hom ≫ pullback.snd t f = U.ι ≫ p) ↔
      ((∀ y ∈ connectedComponentIn ((p ≫ f) ⁻¹' {s}) x',
          ∃ V : X'.Opens, y ∈ V ∧ Etale (V.ι ≫ p)) ∧
        ∃ (W : ((p ≫ f).fiber s).Opens) (hW : FEt (W.ι ≫ fiberMap p f s)),
          (p ≫ f).fiberι s '' W = connectedComponentIn ((p ≫ f) ⁻¹' {s}) x' ∧
          IsGeometricallyTrivial (f.fiberToSpecResidueField s)
            (MorphismProperty.Over.mk ⊤ (W.ι ≫ fiberMap p f s) hW)))

/-- IX.6.8 (IX.6.7 for finite étale `X'` is its last part). Let `f : X ⟶ S` be proper,
surjective, of finite presentation, with geometrically connected fibres. Then `f` is an effective
descent morphism for finite étale coverings, and the inverse image `f^*` is an equivalence of the
category of finite étale `S`-schemes with the full subcategory of finite étale `X`-schemes whose
restriction to every fibre `X_s` is geometrically trivial over `κ(s)`. Proved for `S` locally
noetherian (`properDescentStatement_of_isLocallyNoetherian`, in
`SGA.SGA1.ExposeIX.ProperDescentLocal`); SGA's statement over an arbitrary base needs the reduction
of `f` itself to a noetherian base (EGA IV 8.8.2, 8.10.5, 9.7.7), which is not done. -/
def ProperDescentStatement : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S) [IsProper f] [Surjective f] [LocallyOfFinitePresentation f]
    [GeometricallyConnected f],
    (fetComparison f).IsEquivalence ∧
    (MorphismProperty.Over.pullback FEt ⊤ f).Full ∧
    (MorphismProperty.Over.pullback FEt ⊤ f).Faithful ∧
    ∀ Y : MorphismProperty.Over FEt ⊤ X, (MorphismProperty.Over.pullback FEt ⊤ f).essImage Y ↔
      ∀ s : S, IsGeometricallyTrivial (f.fiberToSpecResidueField s)
        ((MorphismProperty.Over.pullback FEt ⊤ (f.fiberι s)).obj Y)

/-- IX.6.9. A proper surjective morphism `f : X ⟶ S` with `S` locally noetherian is a universal
effective descent morphism for finite étale coverings: every base change of `f` is an effective
descent morphism for them. (The text writes `Y` for `S`.) This is also IX.4.12. Proved in
`SGA.SGA1.ExposeIX.ProperDescentLimit` (`universalProperDescentStatement`). -/
def UniversalProperDescentStatement : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S) [IsProper f] [Surjective f] [IsLocallyNoetherian S]
    (T : Scheme.{u}) (t : T ⟶ S), (fetComparison (pullback.snd f t)).IsEquivalence

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.6.8, full faithfulness (IX.3.4): for `f` proper and surjective with geometrically connected
fibres, base change `S' ↦ X ×_S S'` is fully faithful on étale coverings. -/
theorem full_pullback_of_isProper_of_geometricallyConnected (f : X ⟶ S) [IsProper f]
    [Surjective f] [GeometricallyConnected f] : (MorphismProperty.Over.pullback FEt ⊤ f).Full :=
  full_overPullback_of_exists f FEt fun _ _ p q _ hq φ' hφ ↦
    have : Etale q := hq.2
    (existsUnique_hom_of_geometricallyConnected f p q φ' hφ).exists

/-- IX.6.8, faithfulness (IX.3.1): base change along a surjective morphism is faithful on étale
coverings. -/
theorem faithful_pullback_of_surjective (f : X ⟶ S) [Surjective f] :
    (MorphismProperty.Over.pullback FEt ⊤ f).Faithful :=
  faithful_overPullback_of_surjective f FEt fun _ _ g hg ↦
    have : Etale g := hg.2
    ⟨inferInstance, inferInstance⟩

/-- IX.6.8, full faithfulness, given fibre functors on the étale coverings of `X` and `S`
(connected schemes, V.7): it follows from IX.5.6 and V.6.9, since a proper surjective morphism is
universally submersive. -/
theorem full_pullback_of_isProper (f : X ⟶ S) [IsProper f] [Surjective f]
    [GeometricallyConnected f]
    (F : MorphismProperty.Over FEt ⊤ X ⥤ FintypeCat.{w}) [FiberFunctor F]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙ F)] :
    (MorphismProperty.Over.pullback FEt ⊤ f).Full :=
  full_pullback f (universally_isQuotientMap_of_universallyClosed f) F

/-- IX.6.11. Let `f : X ⟶ S` be proper, surjective, of finite presentation, with
geometrically connected fibres, `X` connected. Then `π₁(X) → π₁(S)` is surjective and its kernel is
the closed normal subgroup generated by the images of the `π₁(X̄_s) → π₁(X)`, `s ∈ S`, each defined
by a class of paths `d s`. The surjectivity is `surjective_autMap_of_isProper`; the description of
the kernel is equivalent to the criterion `ker_eq_iff_forall_isCompletelyDecomposed`, and its
inclusion `⊇` is `normalClosure_le_ker_geometricFibres`. The description of the kernel is proved for
`S` locally noetherian (`ker_autMap_eq_geometricFibres_of_isLocallyNoetherian`, in
`SGA.SGA1.ExposeIX.ProperDescentGeometricFibres`); the general case needs the reduction to a
noetherian base (EGA IV 8), which is not done. -/
def GeometricFibresStatement : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S) [IsProper f] [Surjective f] [LocallyOfFinitePresentation f]
    [GeometricallyConnected f] [ConnectedSpace X]
    (F' : MorphismProperty.Over FEt ⊤ X ⥤ FintypeCat.{u}) [FiberFunctor F']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙ F')]
    (G : ∀ s, MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{u})
    [∀ s, FiberFunctor (G s)]
    (d : ∀ s, MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ G s ≅ F'),
    (autMap (MorphismProperty.Over.pullback FEt ⊤ f) F').ker =
      (Subgroup.normalClosure (⋃ s, Set.range (pathMap F'
        (fun s ↦ MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) G d s))
        ).topologicalClosure

/-- IX.6.11, surjectivity: for `f` proper surjective with geometrically connected fibres,
`π₁(X) → π₁(S)` is surjective. -/
theorem surjective_autMap_of_isProper (f : X ⟶ S) [IsProper f] [Surjective f]
    [GeometricallyConnected f]
    (F : MorphismProperty.Over FEt ⊤ X ⥤ FintypeCat.{w}) [FiberFunctor F]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙ F)] :
    Function.Surjective (autMap (MorphismProperty.Over.pullback FEt ⊤ f) F) :=
  surjective_autMap_pullback f (universally_isQuotientMap_of_universallyClosed f) F

section Stein

/-! ### Stein factorization and geometrically connected fibres

By EGA III 4.3.4 (`AlgebraicGeometry.CohomologyAux.geometricallyConnected_of_isIso_app`), a proper
`f : X ⟶ S` over a locally noetherian base with `𝒪_S ≅ f_* 𝒪_X` has geometrically connected fibres,
so the results above for geometrically connected `f` apply; and by the Stein factorization
(EGA III 4.3.3) every proper `f` factors into such a morphism followed by a finite one (IX.6.9). -/

/-- IX.6.9, first assertion: a proper morphism `f : X ⟶ S` to a locally noetherian scheme factors
as `X ⟶ S' ⟶ S` with `g : X ⟶ S'` proper, with `𝒪_{S'} ≅ g_* 𝒪_X` and geometrically connected
fibres (hence surjective, and of finite presentation as `S'` is locally noetherian), and
`S' ⟶ S` finite; if `f` is surjective, so is `S' ⟶ S`. (Stein factorization, EGA III 4.3.3, and
EGA III 4.3.4.) -/
theorem exists_geometricallyConnected_comp_isFinite (f : X ⟶ S) [IsProper f]
    [IsLocallyNoetherian S] :
    ∃ (S' : Scheme.{u}) (g : X ⟶ S') (h : S' ⟶ S), IsProper g ∧ GeometricallyConnected g ∧
      LocallyOfFinitePresentation g ∧ IsFinite h ∧ g ≫ h = f ∧ IsLocallyNoetherian S' ∧
      (∀ V : S'.Opens, IsIso (g.app V)) ∧ (Surjective f → Surjective h) := by
  obtain ⟨S', g, h, hg, hh, hgh, hiso, -⟩ := AlgebraicGeometry.steinFactorizationStatement X S f
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian h
  refine ⟨S', g, h, hg, AlgebraicGeometry.CohomologyAux.geometricallyConnected_of_isIso_app g hiso,
    inferInstance, hh, hgh, this, hiso, fun hf ↦ ⟨fun y ↦ ?_⟩⟩
  obtain ⟨x, rfl⟩ := hf.surj y
  exact ⟨g x, by rw [← Scheme.Hom.comp_apply, hgh]⟩

/-- IX.6.8, full faithfulness, for `f` proper with `𝒪_S ≅ f_* 𝒪_X` over a locally noetherian base:
the fibres are then geometrically connected (EGA III 4.3.4). -/
theorem full_pullback_of_isIso_app (f : X ⟶ S) [IsProper f] [IsLocallyNoetherian S]
    (hf : ∀ V : S.Opens, IsIso (f.app V))
    (F : MorphismProperty.Over FEt ⊤ X ⥤ FintypeCat.{w}) [FiberFunctor F]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙ F)] :
    (MorphismProperty.Over.pullback FEt ⊤ f).Full :=
  have := AlgebraicGeometry.CohomologyAux.geometricallyConnected_of_isIso_app f hf
  full_pullback_of_isProper f F

/-- IX.6.11, surjectivity of `π₁(X) → π₁(S)`, for `f` proper with `𝒪_S ≅ f_* 𝒪_X` over a locally
noetherian base (EGA III 4.3.4). -/
theorem surjective_autMap_of_isIso_app (f : X ⟶ S) [IsProper f] [IsLocallyNoetherian S]
    (hf : ∀ V : S.Opens, IsIso (f.app V))
    (F : MorphismProperty.Over FEt ⊤ X ⥤ FintypeCat.{w}) [FiberFunctor F]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙ F)] :
    Function.Surjective (autMap (MorphismProperty.Over.pullback FEt ⊤ f) F) :=
  have := AlgebraicGeometry.CohomologyAux.geometricallyConnected_of_isIso_app f hf
  surjective_autMap_of_isProper f F

end Stein

section etale

/-- IX.6.1, surjectivity of `π₁(X) → π₁(S)`, for the fundamental groups of Exposé V: if `S` has a
single point `s` (for instance the spectrum of an artinian local ring), `X` is connected and its
fibre is geometrically connected, then `π₁(X, x) → π₁(S, f(x))` is surjective for every geometric
point `x` of `X`. -/
theorem surjective_etaleFundamentalGroup_map_of_subsingleton [Subsingleton S] [ConnectedSpace X]
    (f : X ⟶ S) (s : S) (hs : GeometricallyConnected (f.fiberToSpecResidueField s))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Function.Surjective (SGA.SGA1.ExposeV.etaleFundamentalGroup.map Ω f x) := by
  have : Nonempty S := ⟨s⟩
  have : ConnectedSpace S :=
    { isPreconnected_univ := Set.subsingleton_of_subsingleton.isPreconnected
      toNonempty := ⟨s⟩ }
  have : GeometricallyConnected f :=
    (GeometricallyConnected.iff_geometricallyConnected_fiber f).mpr fun s' ↦
      Subsingleton.elim s s' ▸ hs
  have : PreservesIsConnected (SGA.SGA1.ExposeV.FEt.pullback f) :=
    preservesIsConnected_pullback_of_subsingleton f
  exact SGA.SGA1.ExposeV.autMap_surjective _ _ fun _ _ ↦ PreservesIsConnected.preserves

variable [ConnectedSpace S]

/-- IX.6.8, full faithfulness, for connected `S`: for `f : X ⟶ S` proper, surjective, with
geometrically connected fibres, the inverse image of étale coverings is full (and faithful). -/
theorem full_etalePullback_of_isProper (f : X ⟶ S) [IsProper f] [Surjective f]
    [GeometricallyConnected f] : (SGA.SGA1.ExposeV.FEt.pullback f).Full :=
  full_etalePullback f (universally_isQuotientMap_of_universallyClosed f)

/-- IX.6.11, surjectivity, for the fundamental groups of Exposé V: for `f : X ⟶ S` proper,
surjective, with geometrically connected fibres and `S` connected, `π₁(X, x) → π₁(S, f(x))` is
surjective for every geometric point `x` of `X`. -/
theorem surjective_etaleFundamentalGroup_map_of_isProper (f : X ⟶ S) [IsProper f] [Surjective f]
    [GeometricallyConnected f] (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    Function.Surjective (SGA.SGA1.ExposeV.etaleFundamentalGroup.map Ω f x) :=
  surjective_etaleFundamentalGroup_map f (universally_isQuotientMap_of_universallyClosed f) Ω x

end etale

/-- IX.6.1, last assertion, when `S = Spec k` is the spectrum of a field: the fundamental group of
`S`, i.e. the automorphism group of any fibre functor on its étale coverings, is isomorphic to
the absolute Galois group of `k` (V.8.1 with V.5.7). For the spectrum of a general artinian local
ring see `nonempty_aut_continuousMulEquiv_absoluteGaloisGroup_of_artinian`. -/
theorem nonempty_aut_continuousMulEquiv_absoluteGaloisGroup (k : Type u) [Field k]
    (F : SGA.SGA1.ExposeV.FEt (Spec (.of k)) ⥤ FintypeCat.{u}) [FiberFunctor F] :
    Nonempty (Aut F ≃ₜ* Field.absoluteGaloisGroup k) :=
  SGA.SGA1.ExposeV.nonempty_aut_continuousMulEquiv_absoluteGaloisGroup k F

/-- IX.6.4, for the fundamental groups of Exposé V: a section `σ` of `f : X ⟶ S` splits
`π₁(X, a) → π₁(S, f(a))` at the geometric point `a = σ(b)`: there is a continuous homomorphism
`π₁(S, f(a)) → π₁(X, a)` (induced by `σ` and a class of paths) which is a section. No
connectedness is needed. -/
theorem exists_section_etaleFundamentalGroup_map (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
    (Ω : Type u) [Field Ω] (b : Spec (.of Ω) ⟶ S) :
    ∃ s : SGA.SGA1.ExposeV.etaleFundamentalGroup Ω ((b ≫ σ) ≫ f) →*
        SGA.SGA1.ExposeV.etaleFundamentalGroup Ω (b ≫ σ),
      Continuous s ∧ (SGA.SGA1.ExposeV.etaleFundamentalGroup.map Ω f (b ≫ σ)).comp s =
        MonoidHom.id _ := by
  obtain ⟨φ, hφ⟩ := SGA.SGA1.ExposeV.etaleFundamentalGroup.exists_map_comp_map_eq_conjAut Ω σ f hσ b
  refine ⟨(SGA.SGA1.ExposeV.etaleFundamentalGroup.map Ω σ b).comp φ.symm.conjAut.toMonoidHom,
    (SGA.SGA1.ExposeV.etaleFundamentalGroup.continuous_map Ω σ b).comp (continuous_conjAut _),
    ?_⟩
  rw [← MonoidHom.comp_assoc, hφ]
  ext τ : 1
  apply Iso.ext
  simp [Iso.conjAut_hom, Iso.conj_apply]

lemma isIso_pullback_fst_id {A T : Scheme.{u}} (a : A ⟶ T) : IsIso (pullback.fst a (𝟙 T)) :=
  inferInstance

/-- The inverse image of finite étale coverings along the identity is isomorphic to the identity
functor. -/
noncomputable def fetPullbackId (S : Scheme.{u}) :
    MorphismProperty.Over.pullback FEt ⊤ (𝟙 S) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun Y ↦ MorphismProperty.Over.isoMk
    (@asIso _ _ _ _ (pullback.fst Y.hom (𝟙 S)) (isIso_pullback_fst_id (T := S) Y.hom))
    (by
      change pullback.fst Y.hom (𝟙 S) ≫ Y.hom = pullback.snd Y.hom (𝟙 S)
      rw [pullback.condition, Category.comp_id])) (fun φ ↦ by
      ext : 1
      exact pullback.lift_fst _ _ _)

/-- For a section `s` of `f`, the inverse image along `s` retracts the inverse image along `f`. -/
noncomputable def fetPullbackSectionIso (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) :
    MorphismProperty.Over.pullback FEt ⊤ f ⋙ MorphismProperty.Over.pullback FEt ⊤ s ≅ 𝟭 _ :=
  (MorphismProperty.Over.pullbackComp s f).symm ≪≫ MorphismProperty.Over.pullbackCongr hs ≪≫
    fetPullbackId S

/-- IX.6.4: a section `s` of `f` through the point `a` (for instance given by a rational point of
the fibre) splits `π₁(X, a) → π₁(S, b)`: the inverse image along `s` induces a continuous
homomorphism `π₁(S, b) → π₁(X, a)` which is a section. Here `F` is the fibre functor at `a`,
`f^* ⋙ F` the one at `b`, and `η : F ∘ f^* ∘ s^* ≅ F` expresses `a = s(b)`; `hη` is the
compatibility of `η` with `s^* f^* ≅ id`, which holds for the fibre functors at geometric points. -/
theorem exists_section_autMap_pullback (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    (F : MorphismProperty.Over FEt ⊤ X ⥤ FintypeCat.{w})
    (η : MorphismProperty.Over.pullback FEt ⊤ s ⋙ MorphismProperty.Over.pullback FEt ⊤ f ⋙ F ≅ F)
    (hη : ∀ Y, F.map ((MorphismProperty.Over.pullback FEt ⊤ f).map
      ((fetPullbackSectionIso f s hs).hom.app Y)) =
        η.hom.app ((MorphismProperty.Over.pullback FEt ⊤ f).obj Y)) :
    ∃ σ : Aut (MorphismProperty.Over.pullback FEt ⊤ f ⋙ F) →* Aut F,
      Continuous σ ∧ ∀ τ, autMap (MorphismProperty.Over.pullback FEt ⊤ f) F (σ τ) = τ :=
  ⟨sectionAutMap _ _ F η, continuous_sectionAutMap _ _ _ _, autMap_sectionAutMap _ _ _ η _ hη⟩

section IX61

/-! ### IX.6.1: exactness at `π₁(X)`

We prove `im(π₁(X̄₀) → π₁(X)) = ker(π₁(X) → π₁(S))` when `S` is the spectrum of an artinian local
ring and `X_s` is quasi-compact and quasi-separated. The inclusion `im ⊆ ker` holds for any `S`: the
composite `X̄₀ ⟶ X ⟶ S` factors through `Spec κ(s)‾`, whose fundamental group is trivial. For the
other inclusion we follow SGA: a section of an étale covering `Y` of `X` over `X̄₀` descends to
`X ⊗ k_s` (`k_s` the separable closure of `κ(s)` in `κ(s)‾`, IX.4.10 for the radicial
`X̄₀ ⟶ X ⊗ k_s`), then to some `X ⊗ L` with `L/κ(s)` finite separable (passage to the limit,
EGA IV 8.8.2), and extends to `X ×_S S' ⟶ Y` for the étale covering `S'` of `S` lifting
`Spec L` (IX.1.7). The abstract criterion `ker_le_range_of_forall_section` then gives `ker ⊆ im`. -/

open SGA.SGA1.ExposeV in
/-- The spectrum of a purely inseparable field extension is radicial. -/
lemma universallyInjective_specMap_of_isPurelyInseparable (K L : Type u) [Field K] [Field L]
    [Algebra K L] [IsPurelyInseparable K L] :
    UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  refine ((tfae_universallyInjective _).out 1 2).mpr ?_
  intro F _ g₁ g₂ hg
  obtain ⟨ψ₁, rfl⟩ := Spec.map_surjective g₁
  obtain ⟨ψ₂, rfl⟩ := Spec.map_surjective g₂
  simp only [← Spec.map_comp] at hg
  have h := congrArg CommRingCat.Hom.hom (Spec.map_injective hg)
  congr 1
  ext1
  exact IsPurelyInseparable.injective_comp_algebraMap K L F h

/-- The spectrum of a field extension is universally submersive. -/
lemma universallySubmersive_specMap_field (K L : Type u) [Field K] [Field L] [Algebra K L] :
    UniversallySubmersive (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    ⟨fun x ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  infer_instance

/-- The separable closure `k_s` of `κ(s)` in its algebraic closure. -/
noncomputable abbrev sepClosureResidue (S : Scheme.{u}) (s : S) :
    IntermediateField (S.residueField s) (AlgebraicClosure (S.residueField s)) :=
  separableClosure (S.residueField s) (AlgebraicClosure (S.residueField s))

/-- The fibre `X_s ⊗_{κ(s)} k_s` over the separable closure. -/
noncomputable abbrev sepFiber (f : X ⟶ S) (s : S) : Scheme.{u} :=
  pullback (f.fiberToSpecResidueField s)
    (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (sepClosureResidue S s))))

lemma specMap_algebraMap_sepClosureResidue_comp (s : S) :
    Spec.map (CommRingCat.ofHom (algebraMap (sepClosureResidue S s)
        (AlgebraicClosure (S.residueField s)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (sepClosureResidue S s))) =
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
      (AlgebraicClosure (S.residueField s)))) := by
  rw [← Spec.map_comp]
  rfl

/-- The radicial morphism `X̄₀ ⟶ X_s ⊗ k_s`. -/
noncomputable abbrev geometricFiberToSep (f : X ⟶ S) (s : S) : geometricFiber f s ⟶ sepFiber f s :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap (sepClosureResidue S s)
    (AlgebraicClosure (S.residueField s))))) (𝟙 _)
    (by simp only [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id]; exact (specMap_algebraMap_sepClosureResidue_comp s).symm)

lemma isPullback_geometricFiberToSep (f : X ⟶ S) (s : S) :
    IsPullback (geometricFiberToSep f s) (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (algebraMap (sepClosureResidue S s)
        (AlgebraicClosure (S.residueField s))))) :=
  SGA.SGA1.ExposeV.isPullback_pullbackMap _ _ _ _ (specMap_algebraMap_sepClosureResidue_comp s)

lemma geometricFiberToSep_comp (f : X ⟶ S) (s : S) :
    geometricFiberToSep f s ≫ pullback.fst _ _ ≫ f.fiberι s = geometricFiberι f s := by
  have h1 : geometricFiberToSep f s ≫ pullback.fst _ _ = pullback.fst _ _ ≫ 𝟙 _ :=
    pullback.lift_fst _ _ _
  rw [← Category.assoc, h1, Category.comp_id]
  rfl

/-- IX.4.10 for the radicial `X̄₀ ⟶ X_s ⊗ k_s`: an `X`-morphism from `X̄₀` to an étale covering of
`X` comes from a unique one from `X_s ⊗ k_s`. -/
lemma exists_sepFiber_hom (f : X ⟶ S) (s : S) (Y : MorphismProperty.Over FEt ⊤ X)
    (a : geometricFiber f s ⟶ Y.left) (ha : a ≫ Y.hom = geometricFiberι f s) :
    ∃ b : sepFiber f s ⟶ Y.left,
      geometricFiberToSep f s ≫ b = a ∧ b ≫ Y.hom = pullback.fst _ _ ≫ f.fiberι s := by
  let g := geometricFiberToSep f s
  have hpb := isPullback_geometricFiberToSep f s
  have : UniversallyInjective g := MorphismProperty.of_isPullback hpb.flip
    (universallyInjective_specMap_of_isPurelyInseparable _ _)
  have : UniversallySubmersive g := MorphismProperty.of_isPullback hpb.flip
    (universallySubmersive_specMap_field _ _)
  let π' : sepFiber f s ⟶ X := pullback.fst _ _ ≫ f.fiberι s
  have : Etale Y.hom := Y.prop.2
  have hgπ : g ≫ π' = geometricFiberι f s := geometricFiberToSep_comp f s
  let φ' : pullback (𝟙 (sepFiber f s)) g ⟶ pullback Y.hom π' :=
    pullback.lift (pullback.snd _ _ ≫ a) (pullback.fst _ _) (by
      rw [Category.assoc, ha, ← hgπ, ← Category.assoc, ← pullback.condition, Category.comp_id])
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩, -⟩ := existsUnique_hom_of_universallyInjective g (𝟙 _)
    (pullback.snd Y.hom π') φ' ((pullback.lift_snd _ _ _).trans (Category.comp_id _).symm)
  refine ⟨φ ≫ pullback.fst _ _, ?_, ?_⟩
  · let σ : geometricFiber f s ⟶ pullback (𝟙 (sepFiber f s)) g :=
      pullback.lift g (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    have hσ : σ ≫ pullback.fst _ _ = geometricFiberToSep f s := pullback.lift_fst _ _ _
    rw [← hσ, Category.assoc, reassoc_of% hφ₂]
    change σ ≫ pullback.lift _ _ _ ≫ pullback.fst _ _ = a
    rw [pullback.lift_fst, ← Category.assoc, pullback.lift_snd, Category.id_comp]
  · rw [Category.assoc, pullback.condition, reassoc_of% hφ₁]

/-- EGA IV 8.8.2 for `X_s ⊗ k_s = lim X_s ⊗ L`: an `X`-morphism from `X_s ⊗ k_s` to an étale
covering of `X` comes from some `X_s ⊗ L`, `L/κ(s)` finite separable. -/
lemma exists_finiteSubext_sepFiber_hom (f : X ⟶ S) (s : S) [CompactSpace (f.fiber s)]
    [QuasiSeparatedSpace (f.fiber s)] (Y : MorphismProperty.Over FEt ⊤ X)
    (b : sepFiber f s ⟶ Y.left) (hb : b ≫ Y.hom = pullback.fst _ _ ≫ f.fiberι s) :
    ∃ (L : SGA.SGA1.ExposeV.FiniteSubext (S.residueField s) (sepClosureResidue S s))
      (c : pullback (f.fiberToSpecResidueField s)
        (SGA.SGA1.ExposeV.specFiniteSubextι (S.residueField s) (sepClosureResidue S s) L) ⟶
          Y.left),
      SGA.SGA1.ExposeV.baseChangeConeπ (k := S.residueField s) (E := sepClosureResidue S s)
        (f.fiberToSpecResidueField s) (Opposite.op L) ≫ c = b ∧
        c ≫ Y.hom = pullback.fst _ _ ≫ f.fiberι s := by
  have : Etale Y.hom := Y.prop.2
  exact SGA.SGA1.ExposeV.exists_finiteSubext_hom (k := S.residueField s)
    (E := sepClosureResidue S s) (f.fiberToSpecResidueField s) Y.hom (f.fiberι s) b hb

/-- `Spec L ⟶ Spec κ(s)` is an étale covering for a finite subextension `L` of `k_s/κ(s)`. -/
lemma finiteEtaleHom_specFiniteSubextι (s : S)
    (L : SGA.SGA1.ExposeV.FiniteSubext (S.residueField s) (sepClosureResidue S s)) :
    FEt (SGA.SGA1.ExposeV.specFiniteSubextι (S.residueField s) (sepClosureResidue S s) L) := by
  have := L.2
  refine ⟨?_, ?_⟩
  · rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FinitePresentation (S.residueField s) L.1 :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have : Algebra.Etale (S.residueField s) L.1 :=
      ⟨Algebra.FormallyEtale.of_isSeparable _ _, inferInstance⟩
    exact RingHom.etale_algebraMap.mpr inferInstance

/-- A morphism `X ×_S Z ⟶ Y` over `X` and a compatible section of `X̄₀ ×_S Z` give the
factorization of a section `T ⟶ K(Y)` required in `ker_le_range_of_forall_section`. -/
lemma exists_comp_pullback_map_eq (f : X ⟶ S) {W : Scheme.{u}} (ι : W ⟶ X)
    {Z : MorphismProperty.Over FEt ⊤ S} {Y : MorphismProperty.Over FEt ⊤ X}
    {T : MorphismProperty.Over FEt ⊤ W} (t : T ⟶ (MorphismProperty.Over.pullback FEt ⊤ ι).obj Y)
    (v : pullback Z.hom f ⟶ Y.left) (hv : v ≫ Y.hom = pullback.snd Z.hom f)
    (ψ : T.left ⟶ pullback Z.hom f) (hψ : ψ ≫ pullback.snd Z.hom f = T.hom ≫ ι)
    (hψv : ψ ≫ v = t.left ≫ pullback.fst Y.hom ι) :
    ∃ (u : (MorphismProperty.Over.pullback FEt ⊤ f).obj Z ⟶ Y)
      (t' : T ⟶ (MorphismProperty.Over.pullback FEt ⊤ ι).obj
        ((MorphismProperty.Over.pullback FEt ⊤ f).obj Z)),
      t' ≫ (MorphismProperty.Over.pullback FEt ⊤ ι).map u = t := by
  let u : (MorphismProperty.Over.pullback FEt ⊤ f).obj Z ⟶ Y := MorphismProperty.Over.homMk v hv
  let t'l : T.left ⟶ pullback (pullback.snd Z.hom f) ι := pullback.lift ψ T.hom hψ
  let t' : T ⟶ (MorphismProperty.Over.pullback FEt ⊤ ι).obj
      ((MorphismProperty.Over.pullback FEt ⊤ f).obj Z) :=
    MorphismProperty.Over.homMk t'l (pullback.lift_snd _ _ _)
  refine ⟨u, t', MorphismProperty.Over.Hom.ext ?_⟩
  have ht : t.left ≫ pullback.snd Y.hom ι = T.hom := MorphismProperty.Over.w t
  change t'l ≫ ((MorphismProperty.Over.pullback FEt ⊤ ι).map u).left = t.left
  rw [MorphismProperty.Over.pullback_map_left]
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg (t'l ≫ ·) (pullback.lift_fst _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ u.left) (pullback.lift_fst _ _ _)).trans hψv)))
  · exact (Category.assoc _ _ _).trans ((congrArg (t'l ≫ ·) (pullback.lift_snd _ _ _)).trans
      ((pullback.lift_snd _ _ _).trans ht.symm))

/-- `X`-morphisms from `W₀` to étale coverings extend along `ι : W₀ ⟶ W`: for `π : W ⟶ X` and an
étale covering `Y` of `X`, every `w : W₀ ⟶ Y` over `ι ≫ π` is `ι ≫ v` for some `v : W ⟶ Y` over
`π`. This holds for `ι` radicial and universally submersive (IX.3.1, IX.4.10) and for `ι` the
closed fibre of a proper scheme over a complete noetherian local ring (IX.1.10). -/
def ExtendsEtaleHoms {W₀ W : Scheme.{u}} (ι : W₀ ⟶ W) : Prop :=
  ∀ ⦃X : Scheme.{u}⦄ (π : W ⟶ X) (Y : MorphismProperty.Over FEt ⊤ X) (w : W₀ ⟶ Y.left),
    w ≫ Y.hom = ι ≫ π → ∃ v : W ⟶ Y.left, v ≫ Y.hom = π ∧ ι ≫ v = w

/-- IX.3.1 and IX.4.10: morphisms to étale schemes extend along a radicial universally submersive
morphism. -/
lemma extendsEtaleHoms_of_universallyInjective {W₀ W : Scheme.{u}} (ι : W₀ ⟶ W)
    [UniversallyInjective ι] [UniversallySubmersive ι] : ExtendsEtaleHoms ι := by
  intro X π Y w hw
  have : Etale Y.hom := Y.prop.2
  let φ' : pullback (𝟙 W) ι ⟶ pullback Y.hom π :=
    pullback.lift (pullback.snd _ _ ≫ w) (pullback.fst _ _) (by
      rw [Category.assoc, hw, ← Category.assoc, ← pullback.condition, Category.comp_id])
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩, -⟩ := existsUnique_hom_of_universallyInjective ι (𝟙 _)
    (pullback.snd Y.hom π) φ' ((pullback.lift_snd _ _ _).trans (Category.comp_id _).symm)
  refine ⟨φ ≫ pullback.fst _ _, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, reassoc_of% hφ₁]
  · let σ : W₀ ⟶ pullback (𝟙 W) ι :=
      pullback.lift ι (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
    have hσ : σ ≫ pullback.fst _ _ = ι := pullback.lift_fst _ _ _
    rw [← hσ, Category.assoc, reassoc_of% hφ₂]
    change σ ≫ pullback.lift _ _ _ ≫ pullback.fst _ _ = w
    rw [pullback.lift_fst, ← Category.assoc, pullback.lift_snd, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Morphisms to étale schemes extend along `ι` when base change along `ι` is full on étale
coverings. -/
lemma extendsEtaleHoms_of_full {W₀ W : Scheme.{u}} (ι : W₀ ⟶ W)
    [(MorphismProperty.Over.pullback FEt ⊤ ι).Full] : ExtendsEtaleHoms ι := by
  intro X π Y w hw
  let E : MorphismProperty.Over FEt ⊤ W := (MorphismProperty.Over.pullback FEt ⊤ π).obj Y
  let T : MorphismProperty.Over FEt ⊤ W :=
    MorphismProperty.Over.mk ⊤ (𝟙 W) (SGA.SGA1.ExposeV.finiteEtaleHom.id_mem _)
  have hcond : pullback.fst T.hom ι = pullback.snd T.hom ι ≫ ι :=
    (Category.comp_id _).symm.trans pullback.condition
  let φ₀l : pullback T.hom ι ⟶ pullback E.hom ι :=
    pullback.lift (pullback.lift (pullback.snd T.hom ι ≫ w) (pullback.fst T.hom ι)
      (by rw [Category.assoc, hw, hcond, Category.assoc]))
      (pullback.snd T.hom ι) ((pullback.lift_snd _ _ _).trans hcond)
  let φ₀ : (MorphismProperty.Over.pullback FEt ⊤ ι).obj T ⟶
      (MorphismProperty.Over.pullback FEt ⊤ ι).obj E :=
    MorphismProperty.Over.homMk φ₀l (pullback.lift_snd _ _ _)
  obtain ⟨φ, hφ⟩ := (MorphismProperty.Over.pullback FEt ⊤ ι).map_surjective φ₀
  refine ⟨φ.left ≫ pullback.fst Y.hom π, ?_, ?_⟩
  · have hw' : φ.left ≫ pullback.snd Y.hom π = 𝟙 W := MorphismProperty.Over.w φ
    rw [Category.assoc, pullback.condition, reassoc_of% hw']
    exact Category.id_comp π
  · let σ₀ : W₀ ⟶ pullback T.hom ι :=
      pullback.lift ι (𝟙 W₀) ((Category.comp_id ι).trans (Category.id_comp ι).symm)
    have hσ₀ : σ₀ ≫ pullback.fst T.hom ι = ι := pullback.lift_fst _ _ _
    have hσ₀' : σ₀ ≫ pullback.snd T.hom ι = 𝟙 W₀ := pullback.lift_snd _ _ _
    have e₁ : ((MorphismProperty.Over.pullback FEt ⊤ ι).map φ).left ≫ pullback.fst E.hom ι =
        pullback.fst T.hom ι ≫ φ.left := fetPullback_map_left_fetProj ι φ
    have e₂ : ((MorphismProperty.Over.pullback FEt ⊤ ι).map φ).left = φ₀l :=
      congrArg (fun ψ ↦ ψ.left) hφ
    have e₃ : φ₀l ≫ pullback.fst E.hom ι ≫ pullback.fst Y.hom π = pullback.snd T.hom ι ≫ w := by
      rw [pullback.lift_fst_assoc, pullback.lift_fst]
    calc ι ≫ φ.left ≫ pullback.fst Y.hom π
        = σ₀ ≫ (pullback.fst T.hom ι ≫ φ.left) ≫ pullback.fst Y.hom π := by
          rw [Category.assoc, reassoc_of% hσ₀]
      _ = σ₀ ≫ φ₀l ≫ pullback.fst E.hom ι ≫ pullback.fst Y.hom π := by
          rw [← e₁, e₂, Category.assoc]
      _ = w := by rw [e₃, reassoc_of% hσ₀']

/-- IX.6.1, exactness at `π₁(X)`, the inclusion `ker ⊆ im`, when the étale coverings of `S` are
determined by their restriction to `Spec κ(s)` and morphisms to étale coverings extend from the
fibres `(X ×_S S') ⊗ κ(s)` to `X ×_S S'` (`hext`): SGA's argument, where the section over `X ⊗ L`
given by the passage to the limit is extended to `X ×_S S'` for the étale covering `S'` of `S`
lifting `Spec L`. Over the spectrum of an artinian local ring both hypotheses are IX.1.7
(`ker_le_range_of_subsingleton`); over a complete noetherian local ring they are IX.1.10 for
finite `X` and the full faithfulness in IX.1.10 (X.2.2). -/
theorem ker_le_range_of_extendsEtaleHoms (f : X ⟶ S) (s : S)
    [(MorphismProperty.Over.pullback FEt ⊤ (S.fromSpecResidueField s)).EssSurj]
    (hext : ∀ Z : MorphismProperty.Over FEt ⊤ S,
      ExtendsEtaleHoms (pullback.fst (pullback.snd Z.hom f ≫ f) (S.fromSpecResidueField s)))
    [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{w}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')] :
    (autMap (MorphismProperty.Over.pullback FEt ⊤ f)
        (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')).ker ≤
      (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) F'').range := by
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F''
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor
    (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  let T : MorphismProperty.Over FEt ⊤ (geometricFiber f s) :=
    MorphismProperty.Over.mk ⊤ (𝟙 _) (SGA.SGA1.ExposeV.finiteEtaleHom.id_mem _)
  have : IsIso T.hom := inferInstanceAs (IsIso (𝟙 _))
  refine ker_le_range_of_forall_section _ _ F'' (SGA.SGA1.ExposeV.FEt.isTerminalOfIsIso T)
    fun Y t ↦ ?_
  let ι := geometricFiberι f s
  let h := f.fiberToSpecResidueField s
  let j := S.fromSpecResidueField s
  let tl : geometricFiber f s ⟶ pullback Y.hom ι := t.left
  have ht : tl ≫ pullback.snd Y.hom ι = 𝟙 _ := MorphismProperty.Over.w t
  have ha : (tl ≫ pullback.fst Y.hom ι) ≫ Y.hom = ι := by
    rw [Category.assoc, pullback.condition, reassoc_of% ht]
  obtain ⟨b, hb₁, hb₂⟩ := exists_sepFiber_hom f s Y (tl ≫ pullback.fst _ _) ha
  obtain ⟨L, c, hc₁, hc₂⟩ := exists_finiteSubext_sepFiber_hom f s Y b hb₂
  let ιL := SGA.SGA1.ExposeV.specFiniteSubextι (S.residueField s) (sepClosureResidue S s) L
  have e1 : pullback.snd h ιL ≫ ιL = pullback.fst h ιL ≫ h := pullback.condition.symm
  have e2 : f.fiberι s ≫ f = h ≫ j := pullback.condition
  -- the étale covering `Z` of `S` lifting `Spec L`
  obtain ⟨Z, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (MorphismProperty.Over.pullback FEt ⊤ j)
    (MorphismProperty.Over.mk ⊤ ιL (finiteEtaleHom_specFiniteSubextι s L))
  have he₁ : e.hom.left ≫ ιL = pullback.snd Z.hom j := MorphismProperty.Over.w e.hom
  have he₂ : e.inv.left ≫ pullback.snd Z.hom j = ιL := MorphismProperty.Over.w e.inv
  have he₃ : e.inv.left ≫ e.hom.left = 𝟙 _ := by
    rw [← MorphismProperty.Comma.comp_left, e.inv_hom_id]
    rfl
  -- `W = X ×_S Z` and its closed fibre `W_κ = W ×_S Spec κ(s)`
  let πW : pullback Z.hom f ⟶ S := pullback.snd Z.hom f ≫ f
  let gκ : pullback πW j ⟶ pullback Z.hom f := pullback.fst πW j
  -- the morphism `W_κ ⟶ X_s ⊗ L`
  obtain ⟨mX, hmX₁, hmX₂⟩ : ∃ mX : pullback πW j ⟶ f.fiber s,
      mX ≫ f.fiberι s = gκ ≫ pullback.snd Z.hom f ∧ mX ≫ h = pullback.snd πW j :=
    ⟨pullback.lift (gκ ≫ pullback.snd Z.hom f) (pullback.snd πW j)
      ((Category.assoc _ _ _).trans pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨mZ, hmZ₁, hmZ₂⟩ : ∃ mZ : pullback πW j ⟶ pullback Z.hom j,
      mZ ≫ pullback.fst Z.hom j = gκ ≫ pullback.fst Z.hom f ∧
        mZ ≫ pullback.snd Z.hom j = pullback.snd πW j :=
    ⟨pullback.lift (gκ ≫ pullback.fst Z.hom f) (pullback.snd πW j)
      ((Category.assoc _ _ _).trans ((congrArg (gκ ≫ ·) pullback.condition).trans
        pullback.condition)),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : pullback πW j ⟶ pullback h ιL,
      m ≫ pullback.fst h ιL = mX ∧ m ≫ pullback.snd h ιL = mZ ≫ e.hom.left :=
    ⟨pullback.lift mX (mZ ≫ e.hom.left) (hmX₂.trans ((hmZ₂.symm.trans
      (congrArg (mZ ≫ ·) he₁.symm)).trans (Category.assoc _ _ _).symm)),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hmc : (m ≫ c) ≫ Y.hom = gκ ≫ pullback.snd Z.hom f := by
    rw [Category.assoc, hc₂, ← Category.assoc, hm₁, hmX₁]
  -- extension of `m ≫ c` to `W`
  obtain ⟨v, hv, hgv⟩ := hext Z (pullback.snd Z.hom f) Y (m ≫ c) hmc
  -- the section `X̄₀ ⟶ W`
  obtain ⟨πL, hπ₁, hπc⟩ : ∃ πL : sepFiber f s ⟶ pullback h ιL,
      πL ≫ pullback.fst h ιL = pullback.fst _ _ ∧ πL ≫ c = b :=
    ⟨SGA.SGA1.ExposeV.baseChangeConeπ (k := S.residueField s) (E := sepClosureResidue S s)
      h (Opposite.op L), (pullback.lift_fst _ _ _).trans (Category.comp_id _), hc₁⟩
  have hgf : geometricFiberToSep f s ≫ pullback.fst _ _ = pullback.fst _ _ :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hgL : geometricFiberToSep f s ≫ πL ≫ pullback.fst h ιL = pullback.fst _ _ := by
    rw [hπ₁, hgf]
  let αL : geometricFiber f s ⟶ Spec (.of L.1) := geometricFiberToSep f s ≫ πL ≫ pullback.snd h ιL
  have hαL : αL ≫ ιL = (geometricFiberToSep f s ≫ πL ≫ pullback.fst h ιL) ≫ h := by
    simp only [αL, Category.assoc, e1]
  have hαj : (αL ≫ ιL) ≫ j = ι ≫ f :=
    (congrArg (· ≫ j) (hαL.trans (congrArg (· ≫ h) hgL))).trans
      ((Category.assoc _ _ _).trans ((congrArg (pullback.fst _ _ ≫ ·) e2.symm).trans
        (Category.assoc _ _ _).symm))
  have hinner : e.inv.left ≫ pullback.fst Z.hom j ≫ Z.hom = ιL ≫ j :=
    (congrArg (e.inv.left ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ j) he₂))
  obtain ⟨ψ', hψ'₁, hψ'₂⟩ : ∃ ψ' : geometricFiber f s ⟶ pullback Z.hom f,
      ψ' ≫ pullback.fst Z.hom f = αL ≫ e.inv.left ≫ pullback.fst Z.hom j ∧
        ψ' ≫ pullback.snd Z.hom f = ι :=
    ⟨pullback.lift (αL ≫ e.inv.left ≫ pullback.fst Z.hom j) ι
      ((Category.assoc _ _ _).trans ((congrArg (αL ≫ ·) ((Category.assoc _ _ _).trans hinner)).trans
        ((Category.assoc _ _ _).symm.trans hαj))),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨ψκ, hψκ₁, hψκ₂⟩ : ∃ ψκ : geometricFiber f s ⟶ pullback πW j,
      ψκ ≫ gκ = ψ' ∧ ψκ ≫ pullback.snd πW j = αL ≫ ιL :=
    ⟨pullback.lift ψ' (αL ≫ ιL) ((congrArg (ψ' ≫ ·) rfl).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) hψ'₂).trans hαj.symm))),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hmZ : ψκ ≫ mZ = αL ≫ e.inv.left := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (ψκ ≫ ·) hmZ₁).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst Z.hom f) hψκ₁).trans
          (hψ'₁.trans (Category.assoc _ _ _).symm))))
    · exact (Category.assoc _ _ _).trans ((congrArg (ψκ ≫ ·) hmZ₂).trans (hψκ₂.trans
        ((congrArg (αL ≫ ·) he₂).symm.trans (Category.assoc _ _ _).symm)))
  have hmX : ψκ ≫ mX = geometricFiberToSep f s ≫ πL ≫ pullback.fst h ιL := by
    refine pullback.hom_ext ?_ ?_
    · change ψκ ≫ mX ≫ f.fiberι s = (geometricFiberToSep f s ≫ πL ≫ pullback.fst h ιL) ≫
        f.fiberι s
      exact (congrArg (ψκ ≫ ·) hmX₁).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ pullback.snd Z.hom f) hψκ₁).trans
          (hψ'₂.trans (congrArg (· ≫ f.fiberι s) hgL).symm)))
    · change ψκ ≫ mX ≫ h = (geometricFiberToSep f s ≫ πL ≫ pullback.fst h ιL) ≫ h
      exact (congrArg (ψκ ≫ ·) hmX₂).trans (hψκ₂.trans hαL)
  have hψm : ψκ ≫ m = geometricFiberToSep f s ≫ πL := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (ψκ ≫ ·) hm₁).trans
        (hmX.trans (Category.assoc _ _ _).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (ψκ ≫ ·) hm₂).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ e.hom.left) hmZ).trans
          ((Category.assoc _ _ _).trans ((congrArg (αL ≫ ·) he₃).trans
            ((Category.comp_id _).trans (Category.assoc _ _ _).symm))))))
  have hψv : ψ' ≫ v = tl ≫ pullback.fst Y.hom ι :=
    (congrArg (· ≫ v) hψκ₁.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (ψκ ≫ ·) hgv).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ c) hψm).trans ((Category.assoc _ _ _).trans
          ((congrArg (geometricFiberToSep f s ≫ ·) hπc).trans hb₁))))))
  obtain ⟨u, t', htu⟩ := exists_comp_pullback_map_eq f ι t v hv ψ'
    (hψ'₂.trans (Category.id_comp _).symm) hψv
  exact ⟨Z, u, t', htu⟩

/-- IX.6.1, exactness at `π₁(X)`, the inclusion `ker ⊆ im`, over a one-point base `S` whose étale
coverings are determined by their restriction to `Spec κ(s)` (for instance the spectrum of an
artinian local ring, IX.1.7): the extension of morphisms from `(X ×_S S') ⊗ κ(s)` to `X ×_S S'`
is IX.1.7 for this nil-immersion. -/
theorem ker_le_range_of_subsingleton (f : X ⟶ S) (s : S) [Subsingleton S]
    [(MorphismProperty.Over.pullback FEt ⊤ (S.fromSpecResidueField s)).EssSurj]
    [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{w}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')] :
    (autMap (MorphismProperty.Over.pullback FEt ⊤ f)
        (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')).ker ≤
      (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) F'').range := by
  have : IsClosedImmersion (S.fromSpecResidueField s) :=
    isClosed_singleton_iff_isClosedImmersion.mp (by
      rw [Set.subsingleton_univ.eq_singleton_of_mem (Set.mem_univ s) |>.symm]
      exact isClosed_univ)
  have : Surjective (S.fromSpecResidueField s) :=
    ⟨fun x ↦ ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  refine ker_le_range_of_extendsEtaleHoms f s (fun Z ↦ ?_) F''
  have hpb := IsPullback.of_hasPullback (pullback.snd Z.hom f ≫ f) (S.fromSpecResidueField s)
  have : UniversallyInjective (pullback.fst (pullback.snd Z.hom f ≫ f)
      (S.fromSpecResidueField s)) := MorphismProperty.of_isPullback hpb.flip inferInstance
  have : UniversallySubmersive (pullback.fst (pullback.snd Z.hom f ≫ f)
      (S.fromSpecResidueField s)) := MorphismProperty.of_isPullback hpb.flip inferInstance
  exact extendsEtaleHoms_of_universallyInjective _

/-- A scheme `S` with `Spec κ(s) ⟶ S` an isomorphism has a single point. -/
lemma subsingleton_of_isIso_fromSpecResidueField (s : S) [IsIso (S.fromSpecResidueField s)] :
    Subsingleton S :=
  (Scheme.homeoOfIso (asIso (S.fromSpecResidueField s))).symm.injective.subsingleton

/-- IX.6.1, exactness at `π₁(X)`, the inclusion `ker ⊆ im`, when `S` is the spectrum of the
field `κ(s)` (i.e. `Spec κ(s) ⟶ S` is an isomorphism) and the fibre `X_s` is quasi-compact and
quasi-separated. -/
theorem ker_le_range_of_isIso_fromSpecResidueField (f : X ⟶ S) (s : S)
    [IsIso (S.fromSpecResidueField s)] [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{w}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')] :
    (autMap (MorphismProperty.Over.pullback FEt ⊤ f)
        (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')).ker ≤
      (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) F'').range := by
  have : Subsingleton S := subsingleton_of_isIso_fromSpecResidueField s
  exact ker_le_range_of_subsingleton f s F''

/-- The geometric fibre `X̄₀` is connected when `X_s` is geometrically connected. -/
lemma connectedSpace_geometricFiber (f : X ⟶ S) (s : S)
    (hg : GeometricallyConnected (f.fiberToSpecResidueField s)) :
    ConnectedSpace (geometricFiber f s) := by
  have := hg
  let t := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
    (AlgebraicClosure (S.residueField s))))
  have : ConnectedSpace ↥(pullback t (f.fiberToSpecResidueField s)) :=
    connectedSpace_pullback_of_subsingleton t (f.fiberToSpecResidueField s)
  exact (Homeomorph.connectedSpace_iff
    (Scheme.homeoOfIso (pullbackSymmetry t (f.fiberToSpecResidueField s)))).mp this

/-- The inverse images on the geometric fibre `X̄₀` of the étale coverings of `S` are completely
decomposed, since `X̄₀ ⟶ S` factors through the spectrum of the separably closed field
`κ(s)‾` (whose fundamental group is trivial). -/
theorem isCompletelyDecomposed_geometricFiber_pullback (f : X ⟶ S) (s : S)
    (hg : GeometricallyConnected (f.fiberToSpecResidueField s))
    (Z : MorphismProperty.Over FEt ⊤ S) :
    IsCompletelyDecomposed ((MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)).obj
      ((MorphismProperty.Over.pullback FEt ⊤ f).obj Z)) := by
  have := connectedSpace_geometricFiber f s hg
  obtain ⟨x⟩ : Nonempty (geometricFiber f s) := inferInstance
  let Ω := AlgebraicClosure ((geometricFiber f s).residueField x)
  let xb := SGA.SGA1.ExposeV.geometricPointAt (geometricFiber f s) x
  let ι := geometricFiberι f s
  let q : geometricFiber f s ⟶ Spec (.of (AlgebraicClosure (S.residueField s))) := pullback.snd _ _
  let r : Spec (.of (AlgebraicClosure (S.residueField s))) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s)
      (AlgebraicClosure (S.residueField s)))) ≫ S.fromSpecResidueField s
  have w : ι ≫ f = q ≫ r :=
    (Category.assoc _ _ _).trans ((congrArg (pullback.fst _ _ ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ S.fromSpecResidueField s) pullback.condition).trans
          (Category.assoc _ _ _))))
  let ψ : (MorphismProperty.Over.pullback FEt ⊤ q).obj
      ((MorphismProperty.Over.pullback FEt ⊤ r).obj Z) ≅
      (MorphismProperty.Over.pullback FEt ⊤ ι).obj
        ((MorphismProperty.Over.pullback FEt ⊤ f).obj Z) :=
    ((MorphismProperty.Over.pullbackComp q r).app Z).symm ≪≫
      ((MorphismProperty.Over.pullbackCongr w).app Z).symm ≪≫
        (MorphismProperty.Over.pullbackComp ι f).app Z
  refine (isCompletelyDecomposed_iff (SGA.SGA1.ExposeV.FEt.fiber Ω xb) _).mpr fun σ z ↦ ?_
  have h1 := SGA.SGA1.ExposeV.etaleFundamentalGroup.hom_app_pullback_eq_id Ω q xb σ
    (Subsingleton.elim _ _) ((MorphismProperty.Over.pullback FEt ⊤ r).obj Z)
  change σ.hom.app _ z = z
  rw [SGA.SGA1.ExposeV.aut_app_eq_id_of_iso σ ψ h1]
  rfl

/-- IX.6.1, `im ⊆ ker`: the composite `π₁(X̄₀) → π₁(X) → π₁(S)` is trivial, for any `S` and any
Galois structures and fibre functors, since `X̄₀ ⟶ S` factors through the spectrum of the
separably closed field `κ(s)‾` (the inverse images on `X̄₀` of the coverings of `S` are completely
decomposed). -/
theorem range_le_ker_geometricFiber (f : X ⟶ S) (s : S)
    (hg : GeometricallyConnected (f.fiberToSpecResidueField s))
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{w}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')] :
    (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) F'').range ≤
      (autMap (MorphismProperty.Over.pullback FEt ⊤ f)
        (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')).ker := by
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F''
  exact range_le_ker_of_isCompletelyDecomposed _ _ F''
    (isCompletelyDecomposed_geometricFiber_pullback f s hg)

/-- IX.6.11, the inclusion `⊆` of the description of the kernel: the closed normal subgroup
generated by the images of the `π₁(X̄_s) → π₁(X)` (for any classes of paths `d s`) is contained in
the kernel of `π₁(X) → π₁(S)`, for `f` with geometrically connected fibres. The other inclusion is
`GeometricFibresStatement` (it needs the descent IX.6.8). -/
theorem normalClosure_le_ker_geometricFibres (f : X ⟶ S) [GeometricallyConnected f]
    (F' : MorphismProperty.Over FEt ⊤ X ⥤ FintypeCat.{w}) [FiberFunctor F']
    (G : ∀ s, MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{w})
    [∀ s, FiberFunctor (G s)]
    (d : ∀ s, MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ G s ≅ F') :
    (Subgroup.normalClosure (⋃ s, Set.range (pathMap F'
        (fun s ↦ MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) G d s))
        ).topologicalClosure ≤ (autMap (MorphismProperty.Over.pullback FEt ⊤ f) F').ker := by
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F'
  have (s : S) := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor (G s)
  exact normalClosure_le_ker_of_forall_isCompletelyDecomposed _ F' _ G d fun s Z ↦
    isCompletelyDecomposed_geometricFiber_pullback f s inferInstance Z

/-- **IX.6.1, exactness at `π₁(X)`**, when `S` is the spectrum of the field `κ(s)` and `X` is
quasi-compact, quasi-separated and geometrically connected over `κ(s)`: the image of
`π₁(X̄₀) → π₁(X)` is the kernel of `π₁(X) → π₁(S)` (for any Galois structures and compatible
fibre functors). -/
theorem range_eq_ker_of_isIso_fromSpecResidueField (f : X ⟶ S) (s : S)
    [IsIso (S.fromSpecResidueField s)] [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (hg : GeometricallyConnected (f.fiberToSpecResidueField s))
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{w}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')] :
    (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) F'').range =
      (autMap (MorphismProperty.Over.pullback FEt ⊤ f)
        (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')).ker :=
  le_antisymm (range_le_ker_geometricFiber f s hg F'')
    (ker_le_range_of_isIso_fromSpecResidueField f s F'')

/-- IX.6.2, (i) ⇔ (ii), when `S` is the spectrum of a field: a finite étale covering `Y` of `X`
comes from a finite étale covering of `S` if and only if its inverse image on the geometric fibre
`X̄₀` is completely decomposed (`X` quasi-compact, quasi-separated and geometrically connected). -/
theorem isGeometricallyTrivial_iff_isCompletelyDecomposed_of_isIso (f : X ⟶ S) (s : S)
    [IsIso (S.fromSpecResidueField s)] [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (hg : GeometricallyConnected (f.fiberToSpecResidueField s))
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{w}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    (Y : MorphismProperty.Over FEt ⊤ X) :
    IsGeometricallyTrivial f Y ↔
      IsCompletelyDecomposed
        ((MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)).obj Y) := by
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F''
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor
    (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
    MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  have : Subsingleton S := subsingleton_of_isIso_fromSpecResidueField s
  have hsurj := surjective_autMap_of_subsingleton f s hg
    (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  exact mem_essImage_iff_isCompletelyDecomposed _ _ F'' hsurj
    (range_eq_ker_of_isIso_fromSpecResidueField f s hg F'').symm Y

/-- IX.6.2, (ii) ⇔ (ii bis), when `S` is the spectrum of a field: for a connected covering `Y`,
its inverse image on `X̄₀` is completely decomposed as soon as it has a section. -/
theorem isCompletelyDecomposed_iff_nonempty_section_of_isIso (f : X ⟶ S) (s : S)
    [IsIso (S.fromSpecResidueField s)] [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (hg : GeometricallyConnected (f.fiberToSpecResidueField s))
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{w}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    (Y : MorphismProperty.Over FEt ⊤ X) [ConnectedSpace Y.left] :
    IsCompletelyDecomposed ((MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)).obj Y) ↔
      Nonempty (⊤_ _ ⟶ (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)).obj Y) := by
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F''
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor
    (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  have := isConnected_of_connectedSpace Y
  exact isCompletelyDecomposed_iff_nonempty_hom _ F''
    (range_eq_ker_of_isIso_fromSpecResidueField f s hg F'' ▸ MonoidHom.normal_ker _) Y

/-- **IX.6.1, exactness at `π₁(X)`**, for `S` the spectrum of an artinian local ring with point `s`
and `X_s` quasi-compact, quasi-separated and geometrically connected over `κ(s)`: the image of
`π₁(X̄₀) → π₁(X)` is the kernel of `π₁(X) → π₁(S)` (for any Galois structures and compatible fibre
functors). -/
theorem range_eq_ker_of_artinian (f : X ⟶ S) (s : S)
    (hA : ∃ A : CommRingCat.{u}, IsArtinianRing A ∧ IsLocalRing A ∧ Nonempty (S ≅ Spec A))
    [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (hg : GeometricallyConnected (f.fiberToSpecResidueField s))
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{w}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')] :
    (autMap (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)) F'').range =
      (autMap (MorphismProperty.Over.pullback FEt ⊤ f)
        (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')).ker := by
  have : Subsingleton S := subsingleton_of_artinian hA
  obtain ⟨A, _, _, ⟨e⟩⟩ := hA
  have := SGA.SGA1.ExposeV.FEt.isEquivalence_pullback_fromSpecResidueField A e s
  exact le_antisymm (range_le_ker_geometricFiber f s hg F'') (ker_le_range_of_subsingleton f s F'')

/-- IX.6.2, (i) ⇔ (ii), for `S` the spectrum of an artinian local ring: a finite étale covering
`Y` of `X` comes from a finite étale covering of `S` if and only if its inverse image on the
geometric fibre `X̄₀` is completely decomposed (`X_s` quasi-compact, quasi-separated and
geometrically connected). -/
theorem isGeometricallyTrivial_iff_isCompletelyDecomposed_of_artinian (f : X ⟶ S) (s : S)
    (hA : ∃ A : CommRingCat.{u}, IsArtinianRing A ∧ IsLocalRing A ∧ Nonempty (S ≅ Spec A))
    [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (hg : GeometricallyConnected (f.fiberToSpecResidueField s))
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{w}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    (Y : MorphismProperty.Over FEt ⊤ X) :
    IsGeometricallyTrivial f Y ↔
      IsCompletelyDecomposed
        ((MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)).obj Y) := by
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F''
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor
    (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
    MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  have : Subsingleton S := subsingleton_of_artinian hA
  have hsurj := surjective_autMap_of_subsingleton f s hg
    (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  exact mem_essImage_iff_isCompletelyDecomposed _ _ F'' hsurj
    (range_eq_ker_of_artinian f s hA hg F'').symm Y

/-- IX.6.2, (ii) ⇔ (ii bis), for `S` the spectrum of an artinian local ring: for a connected
covering `Y`, its inverse image on `X̄₀` is completely decomposed as soon as it has a section. -/
theorem isCompletelyDecomposed_iff_nonempty_section_of_artinian (f : X ⟶ S) (s : S)
    (hA : ∃ A : CommRingCat.{u}, IsArtinianRing A ∧ IsLocalRing A ∧ Nonempty (S ≅ Spec A))
    [CompactSpace (f.fiber s)] [QuasiSeparatedSpace (f.fiber s)]
    (hg : GeometricallyConnected (f.fiberToSpecResidueField s))
    (F'' : MorphismProperty.Over FEt ⊤ (geometricFiber f s) ⥤ FintypeCat.{w}) [FiberFunctor F'']
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    [FiberFunctor (MorphismProperty.Over.pullback FEt ⊤ f ⋙
      MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')]
    (Y : MorphismProperty.Over FEt ⊤ X) [ConnectedSpace Y.left] :
    IsCompletelyDecomposed ((MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)).obj Y) ↔
      Nonempty (⊤_ _ ⟶ (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s)).obj Y) := by
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor F''
  have := SGA.SGA1.ExposeV.galoisCategory_of_fiberFunctor
    (MorphismProperty.Over.pullback FEt ⊤ (geometricFiberι f s) ⋙ F'')
  have := isConnected_of_connectedSpace Y
  exact isCompletelyDecomposed_iff_nonempty_hom _ F''
    (range_eq_ker_of_artinian f s hA hg F'' ▸ MonoidHom.normal_ker _) Y

end IX61

end schemes

end SGA.SGA1.ExposeIX
