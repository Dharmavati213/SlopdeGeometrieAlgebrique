/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.ProperBaseChangeClosure
import SGA.SGA1.ExposeXIII.ProperBaseChangeRepresentable

/-!
# SGA 1, Exposé XIII: closure properties of cohomological properness in dimension `≤ 0`

For `f : X ⟶ Y` universally closed, every sheaf of sets on `X` is cohomologically proper for `f`
in dimension `≤ -1` (`isCohomologicallyProperLENegOne_of_universallyClosed`). Combined with
XIII 1.13 1) (`IsCohomologicallyProperLEZero.of_isLimit_fork`) and the fact that every
monomorphism of étale sheaves of sets is the equalizer of two morphisms
(`AlgebraicGeometry.Scheme.isRegularMonoCategory_sheaf`), this shows that cohomological properness
in dimension `≤ 0` passes to subsheaves (`IsCohomologicallyProperLEZero.of_mono`). It is also
stable under finite limits (`IsCohomologicallyProperLEZero.of_isLimit`; binary and finite
products `IsCohomologicallyProperLEZero.prod`, `.pi`, the final sheaf
`isCohomologicallyProperLEZero_of_isTerminal`), since direct and inverse images preserve finite
limits. Hence XIII 1.4 holds for every subsheaf of a sheaf represented by
a separated étale `X`-scheme, for `f` proper and `Y` locally noetherian
(`isCohomologicallyProperLEZero_of_mono_etaleYoneda`); for instance for the extension by the
empty set `j_! *` of the final sheaf from an open subscheme.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry
open Scheme (etalePullback etalePushforward etaleAdjunction etaleBaseChangeMap)

namespace SGA.SGA1.ExposeXIII

variable {S X Y : Scheme.{u}} {s : Y ⟶ S} {f : X ⟶ Y}

/-- For `f` universally closed, cohomological properness in dimension `≤ 0` passes to subsheaves
(XIII 1.13 1) applied to the exact diagram `F ⟶ G ⇉ G ⊔_F G`, whose last term is cohomologically
proper in dimension `≤ -1` by `isCohomologicallyProperLENegOne_of_universallyClosed`). -/
theorem IsCohomologicallyProperLEZero.of_mono [UniversallyClosed f]
    {F G : Sheaf X.smallEtaleTopology (Type u)} (m : F ⟶ G) [Mono m]
    (hG : IsCohomologicallyProperLEZero s f G) : IsCohomologicallyProperLEZero s f F := by
  have := Scheme.isRegularMonoCategory_sheaf X
  obtain ⟨r⟩ : Nonempty (RegularMono m) := ⟨regularMonoOfMono m⟩
  have hc : IsLimit (Fork.ofι m r.w) := r.isLimit
  have hH : IsCohomologicallyProperLENegOne s f r.Z :=
    isCohomologicallyProperLENegOne_of_universallyClosed' f r.Z s
  have := IsCohomologicallyProperLEZero.of_isLimit_fork hc hG hH
  exact this

/-- Cohomological properness in dimension `≤ 0` is stable under finite limits: if every object of
a finite diagram `K` of sheaves of sets on `X` is cohomologically proper for `f` relative to `S` in
dimension `≤ 0`, so is its limit. (The direct and inverse images preserve finite limits, and the
base change morphism is natural; `CategoryTheory.isIso_app_conePt_of_preservesLimit`.) Compare
XIII 1.13 1) (`IsCohomologicallyProperLEZero.of_isLimit_fork`), which for equalizers only needs
the last object to be cohomologically proper in dimension `≤ -1`. -/
theorem IsCohomologicallyProperLEZero.of_isLimit {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Sheaf X.smallEtaleTopology (Type u)) {c : Cone K} (hc : IsLimit c)
    (hK : ∀ j, IsCohomologicallyProperLEZero s f (K.obj j)) :
    IsCohomologicallyProperLEZero s f c.pt := by
  intro S' Y' X' t s' g h f' hY hX
  have : IsIso (Functor.whiskerLeft K (etaleBaseChangeMap hX.w).natTrans) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun j ↦ hK j t s' g h f' hY hX
  have := (etaleAdjunction f).rightAdjoint_preservesLimits
  have := (etaleAdjunction f').rightAdjoint_preservesLimits
  exact isIso_app_conePt_of_preservesLimit K (etaleBaseChangeMap hX.w).natTrans c hc

/-- Cohomological properness in dimension `≤ 0` is stable under binary products. -/
theorem IsCohomologicallyProperLEZero.prod {F₁ F₂ : Sheaf X.smallEtaleTopology (Type u)}
    (h₁ : IsCohomologicallyProperLEZero s f F₁) (h₂ : IsCohomologicallyProperLEZero s f F₂) :
    IsCohomologicallyProperLEZero s f (F₁ ⨯ F₂) :=
  IsCohomologicallyProperLEZero.of_isLimit (pair F₁ F₂) (limit.isLimit _) fun
    | ⟨.left⟩ => h₁
    | ⟨.right⟩ => h₂

/-- Cohomological properness in dimension `≤ 0` is stable under finite products. -/
theorem IsCohomologicallyProperLEZero.pi {ι : Type} [Finite ι]
    {F : ι → Sheaf X.smallEtaleTopology (Type u)}
    (hF : ∀ i, IsCohomologicallyProperLEZero s f (F i)) :
    IsCohomologicallyProperLEZero s f (∏ᶜ F) :=
  have := Fintype.ofFinite ι
  IsCohomologicallyProperLEZero.of_isLimit (Discrete.functor F) (limit.isLimit _)
    fun ⟨i⟩ ↦ hF i

/-- A terminal sheaf of sets (the empty product) is cohomologically proper for every `f` in
dimension `≤ 0`. -/
theorem isCohomologicallyProperLEZero_of_isTerminal {T : Sheaf X.smallEtaleTopology (Type u)}
    (hT : IsTerminal T) : IsCohomologicallyProperLEZero s f T :=
  IsCohomologicallyProperLEZero.of_isLimit (J := Discrete PEmpty.{1}) (Functor.empty _)
    (c := asEmptyCone T) hT fun j ↦ j.as.elim

/-- XIII 1.4 for subsheaves of represented sheaves: for `f : X ⟶ Y` proper with `Y` locally
noetherian, every subsheaf of the sheaf represented by an étale `X`-scheme `E` separated over `X`
is cohomologically proper for `f` in dimension `≤ 0`. (SGA 1 states 1.4 for every sheaf of sets
and every `Y`.) -/
theorem isCohomologicallyProperLEZero_of_mono_etaleYoneda [IsProper f] [IsLocallyNoetherian Y]
    (E : X.Etale) [IsSeparated E.hom] {F : Sheaf X.smallEtaleTopology (Type u)}
    (m : F ⟶ (Scheme.etaleYoneda X).obj E) [Mono m] :
    IsCohomologicallyProperLEZero (𝟙 Y) f F :=
  (isCohomologicallyProperLEZero_etaleYoneda f E).of_mono m

end SGA.SGA1.ExposeXIII
