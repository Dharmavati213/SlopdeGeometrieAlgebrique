/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Constructible
import SGA.Foundations.Etale.Representable

/-!
# Locally constant and constructible sheaves on the small étale site

Let `X` be a scheme. A sheaf of sets `F` on the small étale site of `X` is

* *locally constant* (`Scheme.IsLocallyConstantSheaf`) if every point of `X` has an étale
  neighbourhood `e : W ⟶ X` such that `e^* F` is a constant sheaf;
* *locally constant with finite values* (`Scheme.IsLocallyConstantFiniteSheaf`; "localement
  constant constructible" in SGA 4 IX 2.3) if moreover the values can be taken finite;
* *constructible* (`Scheme.IsConstructibleSheaf`, SGA 4 IX 2.3 for `X` quasi-compact and
  quasi-separated) if there is a finite partition of `X` into constructible subsets, each the
  image of an immersion `Zᵢ ⟶ X`, such that the inverse image of `F` on each `Zᵢ` is locally
  constant with finite values.

We show:

* these properties are stable under inverse images along arbitrary morphisms (for the first two)
  and constant sheaves have them;
* the sheaf represented by a finite étale `X`-scheme is locally constant with finite values
  (`Scheme.isLocallyConstantFiniteSheaf_etaleYoneda`): a finite étale morphism splits étale
  locally (`Scheme.splitsEtaleLocallyAt_of_isFinite`), the inverse image of a representable sheaf
  is represented by the base change, and a constant sheaf is represented by a constant scheme;
* finite étale `X`-schemes form a full subcategory of the category of étale sheaves of sets
  (`Scheme.finiteEtaleSheafFullyFaithful`) whose objects are locally constant with finite values.

The converse (SGA 4 IX 2.2: every locally constant sheaf with finite values is represented by a
finite étale `X`-scheme) needs effective descent of finite morphisms along étale coverings; it is
proved in `SGA.SGA1.ExposeXIII.LocallyConstantSheaves`, with the equivalence between étale
coverings and locally constant sheaves of finite sets.

## References

* [SGA 4, Exposé IX, 2.1–2.3][sga4]
-/

universe u

open CategoryTheory Limits Opposite

-- See the comment in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- A sheaf of sets `F` on the small étale site of `X` is locally constant if every point of `X`
has an étale neighbourhood `e : W ⟶ X` on which `F` becomes constant: `e^* F ≅ E_W`. -/
def IsLocallyConstantSheaf (F : Sheaf X.smallEtaleTopology (Type u)) : Prop :=
  ∀ x : X, ∃ (W : Scheme.{u}) (e : W ⟶ X) (_ : Etale e) (w : W), e w = x ∧
    ∃ E : Type u, Nonempty ((etalePullback e).obj F ≅
      (constantSheaf W.smallEtaleTopology (Type u)).obj E)

/-- A sheaf of sets `F` on the small étale site of `X` is locally constant with finite values
("localement constant constructible", SGA 4 IX 2.3) if every point of `X` has an étale
neighbourhood `e : W ⟶ X` such that `e^* F` is the constant sheaf with a finite value. -/
def IsLocallyConstantFiniteSheaf (F : Sheaf X.smallEtaleTopology (Type u)) : Prop :=
  ∀ x : X, ∃ (W : Scheme.{u}) (e : W ⟶ X) (_ : Etale e) (w : W), e w = x ∧
    ∃ (E : Type u) (_ : Finite E), Nonempty ((etalePullback e).obj F ≅
      (constantSheaf W.smallEtaleTopology (Type u)).obj E)

lemma IsLocallyConstantFiniteSheaf.isLocallyConstantSheaf {F : Sheaf X.smallEtaleTopology (Type u)}
    (hF : IsLocallyConstantFiniteSheaf F) : IsLocallyConstantSheaf F := fun x ↦ by
  obtain ⟨W, e, he, w, hw, E, _, h⟩ := hF x
  exact ⟨W, e, he, w, hw, E, h⟩

/-- The definition in terms of an étale covering family. -/
lemma isLocallyConstantFiniteSheaf_iff_exists_cover (F : Sheaf X.smallEtaleTopology (Type u)) :
    IsLocallyConstantFiniteSheaf F ↔
      ∃ (α : Type u) (W : α → Scheme.{u}) (e : ∀ a, W a ⟶ X), (∀ a, Etale (e a)) ∧
        (⋃ a, Set.range (e a)) = Set.univ ∧
        ∀ a, ∃ (E : Type u) (_ : Finite E),
          Nonempty ((etalePullback (e a)).obj F ≅
            (constantSheaf (W a).smallEtaleTopology (Type u)).obj E) := by
  constructor
  · intro hF
    choose W e he w hw E hE h using hF
    refine ⟨X, W, e, he, Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨x, w x, hw x⟩,
      fun x ↦ ⟨E x, hE x, h x⟩⟩
  · rintro ⟨α, W, e, he, hcov, h⟩ x
    obtain ⟨a, w, hw⟩ := Set.mem_iUnion.1 (hcov ▸ Set.mem_univ x)
    obtain ⟨E, hE, h⟩ := h a
    exact ⟨W a, e a, he a, w, hw, E, hE, h⟩

lemma IsLocallyConstantSheaf.of_iso {F G : Sheaf X.smallEtaleTopology (Type u)} (i : F ≅ G)
    (hF : IsLocallyConstantSheaf F) : IsLocallyConstantSheaf G := fun x ↦ by
  obtain ⟨W, e, he, w, hw, E, ⟨j⟩⟩ := hF x
  exact ⟨W, e, he, w, hw, E, ⟨(etalePullback e).mapIso i.symm ≪≫ j⟩⟩

lemma IsLocallyConstantFiniteSheaf.of_iso {F G : Sheaf X.smallEtaleTopology (Type u)} (i : F ≅ G)
    (hF : IsLocallyConstantFiniteSheaf F) : IsLocallyConstantFiniteSheaf G := fun x ↦ by
  obtain ⟨W, e, he, w, hw, E, hE, ⟨j⟩⟩ := hF x
  exact ⟨W, e, he, w, hw, E, hE, ⟨(etalePullback e).mapIso i.symm ≪≫ j⟩⟩

/-- For `f : Y ⟶ X` and `e : W ⟶ X`, the inverse images of `F` on `W ×_X Y` through `Y` and
through `W` agree. -/
noncomputable def etalePullbackPullbackIso {W : Scheme.{u}} (f : Y ⟶ X) (e : W ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type u)) :
    (etalePullback (pullback.snd e f)).obj ((etalePullback f).obj F) ≅
      (etalePullback (pullback.fst e f)).obj ((etalePullback e).obj F) :=
  (etalePullbackComp (pullback.snd e f) f).app F ≪≫
    eqToIso (by rw [pullback.condition]) ≪≫ ((etalePullbackComp (pullback.fst e f) e).app F).symm

lemma IsLocallyConstantSheaf.etalePullback {F : Sheaf X.smallEtaleTopology (Type u)}
    (hF : IsLocallyConstantSheaf F) (f : Y ⟶ X) :
    IsLocallyConstantSheaf ((etalePullback f).obj F) := fun y ↦ by
  obtain ⟨W, e, _, w, hw, E, ⟨i⟩⟩ := hF (f y)
  obtain ⟨z, -, hz⟩ := Pullback.exists_preimage_pullback (f := e) (g := f) w y hw
  exact ⟨pullback e f, pullback.snd e f, inferInstance, z, hz, E,
    ⟨etalePullbackPullbackIso f e F ≪≫ (Scheme.etalePullback (pullback.fst e f)).mapIso i ≪≫
      (etalePullbackConstantSheafIso (pullback.fst e f)).app E⟩⟩

lemma IsLocallyConstantFiniteSheaf.etalePullback {F : Sheaf X.smallEtaleTopology (Type u)}
    (hF : IsLocallyConstantFiniteSheaf F) (f : Y ⟶ X) :
    IsLocallyConstantFiniteSheaf ((etalePullback f).obj F) := fun y ↦ by
  obtain ⟨W, e, _, w, hw, E, hE, ⟨i⟩⟩ := hF (f y)
  obtain ⟨z, -, hz⟩ := Pullback.exists_preimage_pullback (f := e) (g := f) w y hw
  exact ⟨pullback e f, pullback.snd e f, inferInstance, z, hz, E, hE,
    ⟨etalePullbackPullbackIso f e F ≪≫ (Scheme.etalePullback (pullback.fst e f)).mapIso i ≪≫
      (etalePullbackConstantSheafIso (pullback.fst e f)).app E⟩⟩

variable (X) in
/-- A constant sheaf is locally constant. -/
lemma isLocallyConstantSheaf_constantSheaf (E : Type u) :
    IsLocallyConstantSheaf ((constantSheaf X.smallEtaleTopology (Type u)).obj E) := fun x ↦
  ⟨X, 𝟙 X, inferInstance, x, rfl, E, ⟨(etalePullbackConstantSheafIso (𝟙 X)).app E⟩⟩

variable (X) in
/-- The constant sheaf with a finite value is locally constant with finite values. -/
lemma isLocallyConstantFiniteSheaf_constantSheaf (E : Type u) [Finite E] :
    IsLocallyConstantFiniteSheaf ((constantSheaf X.smallEtaleTopology (Type u)).obj E) := fun x ↦
  ⟨X, 𝟙 X, inferInstance, x, rfl, E, inferInstance,
    ⟨(etalePullbackConstantSheafIso (𝟙 X)).app E⟩⟩

/-- The sheaf represented by a finite étale `X`-scheme is locally constant with finite values
(the easy half of SGA 4 IX 2.2). -/
theorem isLocallyConstantFiniteSheaf_etaleYoneda (V : X.Etale) [IsFinite V.hom] :
    IsLocallyConstantFiniteSheaf ((etaleYoneda X).obj V) := fun x ↦ by
  obtain ⟨W, g, _, w, E, _, hw, ⟨i⟩⟩ := splitsEtaleLocallyAt_of_isFinite (f := V.hom) x
  refine ⟨W, g, inferInstance, w, hw, E, inferInstance, ⟨?_⟩⟩
  exact etalePullbackYonedaIso g V ≪≫
    (etaleYoneda W).mapIso ((Etale.forgetFullyFaithful W).preimageIso
      (X := (Etale.pullback g).obj V) (Y := Etale.constant W E) i) ≪≫
    (constantSheafIsoYoneda W E).symm

variable (X) in
/-- Finite étale `X`-schemes as objects of the small étale site of `X`. -/
noncomputable def Etale.ofFiniteEtale :
    (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ X ⥤ X.Etale :=
  MorphismProperty.Comma.changeProp _ _ inf_le_right le_rfl le_rfl

variable (X) in
/-- The inclusion of finite étale `X`-schemes into the small étale site is fully faithful. -/
noncomputable def Etale.ofFiniteEtaleFullyFaithful : (Etale.ofFiniteEtale X).FullyFaithful :=
  MorphismProperty.Comma.fullyFaithfulChangeProp _ _ _

variable (X) in
/-- The sheaf of sets on the small étale site of `X` represented by a finite étale `X`-scheme. -/
noncomputable def finiteEtaleSheaf :
    (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ X ⥤
      Sheaf X.smallEtaleTopology (Type u) :=
  Etale.ofFiniteEtale X ⋙ etaleYoneda X

variable (X) in
/-- Finite étale `X`-schemes embed fully faithfully into étale sheaves of sets on `X`. -/
noncomputable def finiteEtaleSheafFullyFaithful : (finiteEtaleSheaf X).FullyFaithful :=
  (Etale.ofFiniteEtaleFullyFaithful X).comp (etaleYonedaFullyFaithful X)

/-- The sheaf represented by a finite étale `X`-scheme is locally constant with finite values. -/
theorem isLocallyConstantFiniteSheaf_finiteEtaleSheaf
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ X) :
    IsLocallyConstantFiniteSheaf ((finiteEtaleSheaf X).obj V) :=
  have : IsFinite ((Etale.ofFiniteEtale X).obj V).hom := V.prop.1
  isLocallyConstantFiniteSheaf_etaleYoneda _

/-- A sheaf of sets `F` on the small étale site of `X` is constructible (SGA 4 IX 2.3, for `X`
quasi-compact and quasi-separated) if there is a finite partition of `X` into constructible
subsets `Zᵢ`, each the image of an immersion `Zᵢ ⟶ X`, such that the inverse image of `F` on each
`Zᵢ` is locally constant with finite values. -/
def IsConstructibleSheaf (F : Sheaf X.smallEtaleTopology (Type u)) : Prop :=
  ∃ (n : ℕ) (Z : Fin n → Scheme.{u}) (i : ∀ j, Z j ⟶ X), (∀ j, IsImmersion (i j)) ∧
    (∀ j, Topology.IsConstructible (Set.range (i j))) ∧
    Pairwise (fun j k ↦ Disjoint (Set.range (i j)) (Set.range (i k))) ∧
    (⋃ j, Set.range (i j)) = Set.univ ∧
    ∀ j, IsLocallyConstantFiniteSheaf ((etalePullback (i j)).obj F)

/-- A sheaf which is locally constant with finite values is constructible. -/
lemma IsLocallyConstantFiniteSheaf.isConstructibleSheaf {F : Sheaf X.smallEtaleTopology (Type u)}
    (hF : IsLocallyConstantFiniteSheaf F) : IsConstructibleSheaf F := by
  have hr : Set.range (𝟙 X : X ⟶ X) = Set.univ := Set.range_id
  refine ⟨1, fun _ ↦ X, fun _ ↦ 𝟙 X, fun _ ↦ inferInstance, fun _ ↦ ?_, ?_, ?_,
    fun _ ↦ hF.etalePullback _⟩
  · rw [hr]
    exact Topology.IsConstructible.univ
  · intro j k hjk
    exact (hjk (Subsingleton.elim j k)).elim
  · exact Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨0, by rw [hr]; trivial⟩

lemma IsConstructibleSheaf.of_iso {F G : Sheaf X.smallEtaleTopology (Type u)} (i : F ≅ G)
    (hF : IsConstructibleSheaf F) : IsConstructibleSheaf G := by
  obtain ⟨n, Z, ι, h₁, h₂, h₃, h₄, h₅⟩ := hF
  exact ⟨n, Z, ι, h₁, h₂, h₃, h₄, fun j ↦ (h₅ j).of_iso ((etalePullback (ι j)).mapIso i)⟩

end AlgebraicGeometry.Scheme
