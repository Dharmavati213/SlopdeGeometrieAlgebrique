/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.UniversalProperty
import SGA.Foundations.Analytic.AnalyticSpace

/-!
# `𝕜`-structures, finite and étale morphisms of analytic spaces

A complex analytic space is a locally ringed space with a `ℂ`-structure which is locally
isomorphic, *`ℂ`-linearly*, to a local model. We encode a `𝕜`-structure on a locally ringed space
`X` as a morphism `s : X ⟶ Spec 𝕜` (equivalently, by the `Γ ⊣ Spec` adjunction, a ring map
`𝕜 → Γ(X, 𝒪_X)`), and `𝕜`-linear morphisms as morphisms commuting with these.

* `LocalModelData.toSpecField D : D ⟶ Spec 𝕜`, the `𝕜`-structure of a local model (constants);
  `LocalModelData.isKLinear_iff_comp_toSpecField`: a morphism of local models is `𝕜`-linear in the
  sense of `LocalModelData.IsKLinear` (it pulls back constants to constants) iff it commutes with
  these structure morphisms. So "commuting with the structure morphisms to `Spec 𝕜`" is the one
  notion of `𝕜`-linearity, used for glued spaces as well (e.g. `X^an`, SGA 1 XII).
* `IsAnalyticSpaceOver 𝕜 X s`: `X` is locally `𝕜`-linearly isomorphic to local models. (The
  older `IsAnalyticSpace 𝕜 X` asks for local isomorphisms of locally ringed spaces, not
  necessarily `𝕜`-linear.)
* `IsFiniteMap p`: a finite morphism of analytic spaces, i.e. proper with finite fibres
  (Cartan, Séminaire 1960/61, exp. 19 §5; Grauert–Remmert, *Coherent analytic sheaves*, 1.3.3);
* `IsLocalIsomorphism p`: every point of the source has an open neighbourhood on which `p` is an
  open immersion (étale morphisms of analytic spaces).
-/

universe u

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace AnalyticGeometry

variable (𝕜 : Type) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- `Spec 𝕜` as a locally ringed space. -/
abbrev specField : LocallyRingedSpace := Spec.locallyRingedSpaceObj (CommRingCat.of 𝕜)

namespace LocalModelData

variable {𝕜} {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (D : LocalModelData 𝕜 E)

/-- The constants `𝕜 → Γ(D, 𝒪_D)` of a local model. -/
def constHom : CommRingCat.of 𝕜 ⟶ LocallyRingedSpace.Γ.obj (op D.toLocallyRingedSpace) :=
  CommRingCat.ofHom (D.constSectionHom ⊤)

/-- The `𝕜`-structure of a local model: the morphism to `Spec 𝕜` given by the constant
sections. -/
def toSpecField : D.toLocallyRingedSpace ⟶ specField 𝕜 :=
  D.toLocallyRingedSpace.toΓSpec ≫ Spec.locallyRingedSpaceMap D.constHom

variable {D} {E' : Type} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {D' : LocalModelData 𝕜 E'}

/-- A morphism of local models is `𝕜`-linear (`IsKLinear`: it pulls back constants to constants)
iff it commutes with the structure morphisms to `Spec 𝕜`. -/
theorem isKLinear_iff_comp_toSpecField (f : D'.toLocallyRingedSpace ⟶ D.toLocallyRingedSpace) :
    IsKLinear f ↔ f ≫ D.toSpecField = D'.toSpecField := by
  have nat : f ≫ D.toLocallyRingedSpace.toΓSpec =
      D'.toLocallyRingedSpace.toΓSpec ≫
        Spec.locallyRingedSpaceMap (LocallyRingedSpace.Γ.map f.op) :=
    identityToΓSpec.naturality f
  have e : f ≫ D.toSpecField = D'.toLocallyRingedSpace.toΓSpec ≫
      Spec.locallyRingedSpaceMap (LocallyRingedSpace.Γ.map f.op) ≫
        Spec.locallyRingedSpaceMap D.constHom := by
    rw [toSpecField, ← Category.assoc, nat, Category.assoc]
  rw [e, ← Spec.locallyRingedSpaceMap_comp, toSpecField]
  constructor
  · intro hf
    have h : D.constHom ≫ LocallyRingedSpace.Γ.map f.op = D'.constHom :=
      CommRingCat.hom_ext (RingHom.ext fun c ↦ hf c)
    rw [h]
  · intro h c
    have := toΓSpec_comp_injective h
    exact congr($this c)

end LocalModelData

/-- `X`, with the `𝕜`-structure `s : X ⟶ Spec 𝕜`, is a `𝕜`-analytic space: every point has an open
neighbourhood `𝕜`-linearly isomorphic to a local model in some `𝕜ⁿ`. -/
def IsAnalyticSpaceOver (X : LocallyRingedSpace.{0}) (s : X ⟶ specField 𝕜) : Prop :=
  ∀ x : X, ∃ (U : Opens X) (_ : x ∈ U) (n : ℕ) (D : LocalModelData 𝕜 (Fin n → 𝕜))
    (e : X.restrict U.isOpenEmbedding ≅ D.toLocallyRingedSpace),
    e.hom ≫ D.toSpecField = X.ofRestrict U.isOpenEmbedding ≫ s

variable {𝕜}

/-- A `𝕜`-analytic space is an analytic space. -/
lemma IsAnalyticSpaceOver.isAnalyticSpace {X : LocallyRingedSpace.{0}} {s : X ⟶ specField 𝕜}
    (h : IsAnalyticSpaceOver 𝕜 X s) : IsAnalyticSpace 𝕜 X := fun x ↦ by
  obtain ⟨U, hx, n, D, e, -⟩ := h x
  exact ⟨U, hx, n, D, ⟨e⟩⟩

/-- A morphism of analytic spaces is *finite* if it is proper (as a map of topological spaces)
with finite fibres. -/
def IsFiniteMap {X Y : LocallyRingedSpace.{0}} (p : Y ⟶ X) : Prop :=
  IsProperMap p.base ∧ ∀ x : X, (p.base ⁻¹' {x}).Finite

/-- A morphism of locally ringed spaces is a *local isomorphism* (an étale morphism, for analytic
spaces) if every point of the source has an open neighbourhood on which it is an open
immersion. -/
def IsLocalIsomorphism {X Y : LocallyRingedSpace.{0}} (p : Y ⟶ X) : Prop :=
  ∀ y : Y, ∃ (U : Opens Y) (_ : y ∈ U),
    LocallyRingedSpace.IsOpenImmersion (Y.ofRestrict U.isOpenEmbedding ≫ p)

end AnalyticGeometry
