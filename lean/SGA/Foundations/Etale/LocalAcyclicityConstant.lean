/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.EtaleStalkProperRepresentable
import SGA.Foundations.Etale.LocalAcyclicity

/-!
# Constant étale sheaves on connected schemes and on geometric points

* `Scheme.bijective_constantSheafAdj_unit_app`: on a connected scheme `X`, the global sections of
  the constant étale sheaf with value `E` are `E` (`H⁰(X, E) = E`; SGA 4 XV 1.3 in degree `0`).
  This is the sheaf-theoretic form of `Scheme.connectedSpace_iff_bijective_constantSchemeSection`.
* `Scheme.eq_of_etaleAgreementLocus_nonempty`: on a connected scheme, two global sections of a
  constant sheaf which agree near some point (their agreement locus
  `Scheme.etaleAgreementLocus` is nonempty) are equal.
* `Scheme.isIso_of_bijective_app_top`: on the small étale site of `Spec Ω`, `Ω` separably closed,
  a morphism of sheaves of sets which is bijective on global sections is an isomorphism (every
  étale `Spec Ω`-scheme is covered by sections, `Scheme.exists_etaleTop_hom_apply`).
* `Scheme.isConstant_of_isSepClosed`: hence every étale sheaf of sets on `Spec Ω` is constant
  (SGA 4 VIII 2.1; Stacks 03PT and 04JM), and so is every inverse image along a morphism which
  factors through `Spec Ω` (`Scheme.isConstant_etalePullback_of_fac`).

## References

* [SGA 4, Exposé VIII, 2.1 and Exposé XV, 1.3][sga4]
* [Stacks Project, Tag 03PT](https://stacks.math.columbia.edu/tag/03PT)
* [Stacks Project, Tag 04JM](https://stacks.math.columbia.edu/tag/04JM)
-/

universe u

open CategoryTheory Limits Opposite

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry.Scheme



section Constant

variable (X : Scheme.{u}) (E : Type u)

/-- Under the identification of the constant sheaf with value `E` with the sheaf represented by the
constant scheme `∐_{e ∈ E} X` (`Scheme.constantSheafIsoYoneda`), the unit `E → Γ(X, E)` of the
constant sheaf adjunction sends `e` to the `e`-th section of `∐_{e ∈ E} X`. -/
lemma constantSheafAdj_unit_app_constantSheafIsoYoneda :
    (constantSheafAdj X.smallEtaleTopology (Type u) (Etale.isTerminalTop X)).unit.app E ≫
      (constantSheafIsoYoneda X E).hom.hom.app (op (Etale.top X)) =
    (constantPresheafToYoneda X E).app (op (Etale.top X)) := by
  have h1 := toSheafify_naturality X.smallEtaleTopology (constantPresheafToYoneda X E)
  have h2 := isoSheafify_hom X.smallEtaleTopology ((etaleYoneda X).obj (Etale.constant X E)).2
  have h3 := (isoSheafify X.smallEtaleTopology
    ((etaleYoneda X).obj (Etale.constant X E)).2).hom_inv_id
  rw [h2] at h3
  have h4 : (constantSheafIsoYoneda X E).hom.hom =
      sheafifyMap X.smallEtaleTopology (constantPresheafToYoneda X E) ≫
        (isoSheafify X.smallEtaleTopology ((etaleYoneda X).obj (Etale.constant X E)).2).inv := rfl
  have h5 : (constantSheafAdj X.smallEtaleTopology (Type u) (Etale.isTerminalTop X)).unit.app E =
      (toSheafify X.smallEtaleTopology ((Functor.const _).obj E)).app (op (Etale.top X)) := by
    simp [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj]
  rw [h4, h5, NatTrans.comp_app, ← Category.assoc, ← NatTrans.comp_app, ← h1, NatTrans.comp_app,
    Category.assoc, ← NatTrans.comp_app, h3]
  simp

/-- On a connected scheme `X`, every section of the constant `X`-scheme `∐_{e ∈ E} X` is one of the
canonical ones, uniquely (`Scheme.connectedSpace_iff_bijective_constantSchemeSection`), as a
morphism in the small étale site. -/
lemma bijective_constantPresheafToYoneda_app_top [ConnectedSpace X] :
    Function.Bijective ((constantPresheafToYoneda X E).app (op (Etale.top X))) := by
  let Φ : (Etale.top X ⟶ Etale.constant X E) →
      {s : X ⟶ constantScheme X E // s ≫ constantSchemeHom X E = 𝟙 X} :=
    fun φ ↦ ⟨φ.left, by simpa [Etale.top] using MorphismProperty.Over.w φ⟩
  have hΦ : Function.Injective Φ := fun φ ψ h ↦
    MorphismProperty.Over.Hom.ext (congrArg Subtype.val h)
  have hc : Φ ∘ (constantPresheafToYoneda X E).app (op (Etale.top X)) =
      constantSchemeSection X E := by
    funext e
    apply Subtype.ext
    simp only [Φ, constantSchemeSection, Function.comp_apply, constantPresheafToYoneda_app]
    exact Category.id_comp _
  have hb := (connectedSpace_iff_bijective_constantSchemeSection X).1 ‹_› E
  rw [← hc] at hb
  refine ⟨hb.1.of_comp, fun φ ↦ ?_⟩
  obtain ⟨e, he⟩ := hb.2 (Φ φ)
  exact ⟨e, hΦ he⟩

/-- SGA 4 XV 1.3 in degree `0`: on a connected scheme `X`, the unit `E → Γ(X, E)` of the constant
sheaf adjunction is bijective, i.e. `H⁰(X, E) = E` for the constant étale sheaf with value `E`. -/
lemma bijective_constantSheafAdj_unit_app [ConnectedSpace X] :
    Function.Bijective
      ((constantSheafAdj X.smallEtaleTopology (Type u) (Etale.isTerminalTop X)).unit.app E) := by
  have hiso : Function.Bijective ((constantSheafIsoYoneda X E).hom.hom.app (op (Etale.top X))) :=
    (isIso_iff_bijective _).1 inferInstance
  rw [← Function.Bijective.of_comp_iff' hiso]
  have h := constantSheafAdj_unit_app_constantSheafIsoYoneda X E
  have : ((constantSheafIsoYoneda X E).hom.hom.app (op (Etale.top X)) ∘
      (constantSheafAdj X.smallEtaleTopology (Type u) (Etale.isTerminalTop X)).unit.app E) =
      (constantPresheafToYoneda X E).app (op (Etale.top X)) := by
    funext e
    exact ConcreteCategory.congr_hom h e
  rw [this]
  exact bijective_constantPresheafToYoneda_app_top X E

end Constant

section AgreementLocus

variable {X : Scheme.{u}}

/-- Two sections of an étale sheaf of sets over `W` are equal if every point of `W` lies in their
agreement locus. -/
lemma eq_of_etaleAgreementLocus_eq_univ {F : Sheaf X.smallEtaleTopology (Type u)} {W : X.Etale}
    {s t : F.obj.obj (op W)} (h : ∀ w, w ∈ etaleAgreementLocus F s t) : s = t := by
  simpa using map_eq_of_range_subset_etaleAgreementLocus (F := F) (𝟙 W)
    (fun _ _ ↦ h _)

end AgreementLocus

section SepClosed

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Every point of an étale scheme over the spectrum of a separably closed field lies on a
section. -/
lemma exists_etaleTop_hom_apply (W : (Spec (.of Ω)).Etale) (w : W.left) :
    ∃ σ : Etale.top (Spec (.of Ω)) ⟶ W, σ.left (default : Spec (.of Ω)) = w := by
  obtain ⟨l, hl, hlw⟩ := exists_fac_of_etale_of_isSepClosed W.hom (𝟙 (Spec (.of Ω))) w
    (Subsingleton.elim (α := Spec (.of Ω)) _ _)
  exact ⟨MorphismProperty.Over.homMk l (by simpa [Etale.top] using hl) trivial, hlw⟩

/-- On the small étale site of the spectrum of a separably closed field, a morphism of sheaves of
sets which is bijective on global sections is an isomorphism. -/
theorem isIso_of_bijective_app_top {A B : Sheaf (Spec (.of Ω)).smallEtaleTopology (Type u)}
    (φ : A ⟶ B) (h : Function.Bijective (φ.hom.app (op (Etale.top (Spec (.of Ω)))))) :
    IsIso φ := by
  have : IsIso φ.hom := by
    rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨W⟩
    rw [isIso_iff_bijective]
    choose σ hσ using exists_etaleTop_hom_apply W
    have hφσ (w : W.left) (a : A.obj.obj (op W)) :
        φ.hom.app _ (A.obj.map (σ w).op a) = B.obj.map (σ w).op (φ.hom.app _ a) :=
      NatTrans.naturality_apply φ.hom (σ w).op a
    refine ⟨fun a a' haa' ↦ eq_of_etaleAgreementLocus_eq_univ fun w ↦
      ⟨_, σ w, (default : Spec (.of Ω)), h.1 (by rw [hφσ, hφσ, haa']), hσ w⟩, fun b ↦ ?_⟩
    let x (w : W.left) : A.obj.obj (op (Etale.top _)) := (h.2 (B.obj.map (σ w).op b)).choose
    have hx (w : W.left) : φ.hom.app _ (x w) = B.obj.map (σ w).op b :=
      (h.2 (B.obj.map (σ w).op b)).choose_spec
    have hA := (isSheaf_iff_isSheaf_of_type _ _).1 A.property
    have hcov : Sieve.generate (Presieve.ofArrows (fun _ : W.left ↦ Etale.top (Spec (.of Ω))) σ) ∈
        (Spec (.of Ω)).smallEtaleTopology W := by
      rw [mem_smallEtaleTopology_iff]
      exact fun w ↦ ⟨_, σ w, (default : Spec (.of Ω)),
        ⟨_, 𝟙 _, σ w, Presieve.ofArrows.mk w, Category.id_comp _⟩, hσ w⟩
    have hsf := (Presieve.isSheafFor_iff_generate _).2 (hA _ hcov)
    rw [Presieve.isSheafFor_arrows_iff] at hsf
    obtain ⟨a, ha, -⟩ := hsf x (by
      intro i j Z gi gj hij
      have hg : gi = gj := (Etale.isTerminalTop _).hom_ext _ _
      subst hg
      by_cases hZ : IsEmpty Z.left
      · exact (subsingleton_obj_of_isEmpty A).elim _ _
      · obtain ⟨z⟩ := not_isEmpty_iff.1 hZ
        have hi := congrArg (fun g ↦ g.left z) hij
        change (σ i).left (gi.left z) = (σ j).left (gi.left z) at hi
        rw [Subsingleton.elim (α := Spec (.of Ω)) (gi.left z) default, hσ, hσ] at hi
        subst hi
        rfl)
    refine ⟨a, eq_of_etaleAgreementLocus_eq_univ fun w ↦
      ⟨_, σ w, (default : Spec (.of Ω)), ?_, hσ w⟩⟩
    rw [← hφσ, ha, hx]
  have : IsIso ((sheafToPresheaf _ _).map φ) := this
  exact isIso_of_reflects_iso φ (sheafToPresheaf _ _)

/-- Every étale sheaf of sets on the spectrum of a separably closed field is constant: the counit
`Γ(F)_const ⟶ F` of the constant sheaf adjunction is an isomorphism. -/
theorem isIso_constantSheafAdj_counit_app
    (F : Sheaf (Spec (.of Ω)).smallEtaleTopology (Type u)) :
    IsIso ((constantSheafAdj _ (Type u) (Etale.isTerminalTop (Spec (.of Ω)))).counit.app F) := by
  let adj := constantSheafAdj (Spec (.of Ω)).smallEtaleTopology (Type u)
    (Etale.isTerminalTop (Spec (.of Ω)))
  have hη := bijective_constantSheafAdj_unit_app (Spec (.of Ω))
    (F.obj.obj (op (Etale.top (Spec (.of Ω)))))
  have htri := adj.right_triangle_components F
  refine isIso_of_bijective_app_top _ ?_
  have : (adj.counit.app F).hom.app (op (Etale.top (Spec (.of Ω)))) ∘
      adj.unit.app (F.obj.obj (op (Etale.top (Spec (.of Ω))))) = id := by
    funext e
    exact ConcreteCategory.congr_hom htri e
  rw [← Function.Bijective.of_comp_iff _ hη, this]
  exact Function.bijective_id

end SepClosed

section Connected

variable {X : Scheme.{u}} [ConnectedSpace X]

/-- On a connected scheme, two global sections of a constant étale sheaf which agree near some
point are equal. -/
theorem eq_of_etaleAgreementLocus_nonempty_constantSheaf {E : Type u}
    {a b : ((constantSheaf X.smallEtaleTopology (Type u)).obj E).obj.obj (op (Etale.top X))}
    (h : (etaleAgreementLocus _ a b).Nonempty) : a = b := by
  obtain ⟨e, rfl⟩ := (bijective_constantSheafAdj_unit_app X E).2 a
  obtain ⟨e', rfl⟩ := (bijective_constantSheafAdj_unit_app X E).2 b
  rw [← etaleAgreementLocus_iso (constantSheafIsoYoneda X E)] at h
  obtain ⟨_, V, g, v, hg, rfl⟩ := h
  have hc (e : E) : (constantSheafIsoYoneda X E).hom.hom.app (op (Etale.top X))
      ((constantSheafAdj X.smallEtaleTopology (Type u) (Etale.isTerminalTop X)).unit.app E e) =
      (constantPresheafToYoneda X E).app (op (Etale.top X)) e :=
    ConcreteCategory.congr_hom (constantSheafAdj_unit_app_constantSheafIsoYoneda X E) e
  rw [hc, hc] at hg
  have hl : g.left ≫ constantSchemeι X E e = g.left ≫ constantSchemeι X E e' := by
    have := congrArg (fun φ ↦ φ.left) hg
    change g.left ≫ 𝟙 X ≫ constantSchemeι X E e = g.left ≫ 𝟙 X ≫ constantSchemeι X E e' at this
    erw [Category.id_comp, Category.id_comp] at this
    exact this
  by_contra hne
  have : IsEmpty V.left := isEmpty_of_comp_constantSchemeι_eq X E g.left
    (fun h' ↦ hne (by rw [h'])) hl
  exact this.false v

/-- On a connected scheme, two global sections of a constant étale sheaf of sets which agree near
some point are equal. -/
theorem eq_of_etaleAgreementLocus_nonempty (K : Sheaf X.smallEtaleTopology (Type u))
    [Sheaf.IsConstant X.smallEtaleTopology K] {a b : K.obj.obj (op (Etale.top X))}
    (h : (etaleAgreementLocus K a b).Nonempty) : a = b := by
  obtain ⟨E, ⟨i⟩⟩ := K.mem_essImage_of_isConstant
  have hinv (c : K.obj.obj (op (Etale.top X))) : i.hom.hom.app _ (i.inv.hom.app _ c) = c :=
    congrArg (fun ψ ↦ ψ.hom.app (op (Etale.top X)) c) i.inv_hom_id
  rw [← hinv a, ← hinv b] at h ⊢
  rw [etaleAgreementLocus_iso] at h
  rw [eq_of_etaleAgreementLocus_nonempty_constantSheaf h]

end Connected

section IsConstant

variable {X Y : Scheme.{u}}

/-- The inverse image of a constant étale sheaf of sets is constant. -/
lemma isConstant_etalePullback (f : X ⟶ Y) (K : Sheaf Y.smallEtaleTopology (Type u))
    [Sheaf.IsConstant Y.smallEtaleTopology K] :
    Sheaf.IsConstant X.smallEtaleTopology ((etalePullback f).obj K) := by
  obtain ⟨E, ⟨i⟩⟩ := K.mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso _
    ((etalePullback f).mapIso i.symm ≪≫ (etalePullbackConstantSheafIso f).app E)

/-- Every étale sheaf of sets on the spectrum of a separably closed field is constant. -/
lemma isConstant_of_isSepClosed {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (K : Sheaf (Spec (.of Ω)).smallEtaleTopology (Type u)) :
    Sheaf.IsConstant (Spec (.of Ω)).smallEtaleTopology K :=
  have := isIso_constantSheafAdj_counit_app K
  ⟨_, ⟨asIso ((constantSheafAdj _ (Type u) (Etale.isTerminalTop (Spec (.of Ω)))).counit.app K)⟩⟩

/-- The inverse image of an étale sheaf of sets along a morphism which factors through the
spectrum of a separably closed field is constant. -/
lemma isConstant_etalePullback_of_fac {Ω : Type u} [Field Ω] [IsSepClosed Ω] (f : X ⟶ Y)
    (π : X ⟶ Spec (.of Ω)) (s : Spec (.of Ω) ⟶ Y) (h : π ≫ s = f)
    (K : Sheaf Y.smallEtaleTopology (Type u)) :
    Sheaf.IsConstant X.smallEtaleTopology ((etalePullback f).obj K) := by
  subst h
  have := isConstant_of_isSepClosed ((etalePullback s).obj K)
  have : Sheaf.IsConstant X.smallEtaleTopology ((etalePullback s ⋙ etalePullback π).obj K) :=
    isConstant_etalePullback π ((etalePullback s).obj K)
  exact Sheaf.isConstant_congr _ ((etalePullbackComp π s).app K)

end IsConstant


end AlgebraicGeometry.Scheme
