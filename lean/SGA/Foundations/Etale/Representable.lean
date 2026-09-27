/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import SGA.Foundations.Etale.ConstantScheme
import SGA.Foundations.Etale.TorsorEtale

/-!
# Representable sheaves on the small étale site

* The étale topology is subcanonical (it is coarser than the fpqc topology), hence so is the
  small étale site of a scheme `X`: every étale `X`-scheme `W` defines a sheaf of sets
  `W' ↦ Hom_X(W', W)`, and the resulting functor `Scheme.etaleYoneda X` is fully faithful.
* The inverse image along any `f : X ⟶ Y` of the sheaf represented by `W` is represented by
  `X ×_Y W` (`Scheme.etalePullbackYonedaIso`); this is an instance of the general fact that a
  left adjoint of the direct image along a continuous functor `u` sends `yoneda c` to
  `yoneda (u c)` (`GrothendieckTopology.yonedaObjLeftAdjointIso`).
* The constant sheaf with value `E` is represented by the constant `X`-scheme `∐_{e ∈ E} X`
  (`Scheme.constantSheafIsoYoneda`), and the inverse image of a constant sheaf is constant
  (`Scheme.etalePullbackConstantSheafIso`).

## References

* [SGA 4, Exposé VII, 2 and Exposé IX, 2][sga4]
-/

universe v u

open CategoryTheory Limits Opposite

-- See the comment in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.GrothendieckTopology

variable {C D : Type*} [Category.{v} C] [Category.{v} D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} [J.Subcanonical] [K.Subcanonical] {u : C ⥤ D}
  [u.IsContinuous J K] {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}

/-- A left adjoint of the direct image `u_*` along a continuous functor `u` sends the sheaf
represented by `c` to the sheaf represented by `u c`. -/
noncomputable def yonedaObjLeftAdjointIso
    (adj : L ⊣ u.sheafPushforwardContinuous (Type v) J K) (c : C) :
    L.obj (J.yoneda.obj c) ≅ K.yoneda.obj (u.obj c) :=
  Coyoneda.ext _ _
    (fun f ↦ K.yonedaEquiv.symm (J.yonedaEquiv (adj.homEquiv _ _ f)))
    (fun g ↦ (adj.homEquiv _ _).symm (J.yonedaEquiv.symm (K.yonedaEquiv g)))
    (fun f ↦ by simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply])
    (fun g ↦ by simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply])
    (fun f g ↦ by
      rw [← adj.homEquiv_naturality_right_symm]
      congr 1
      apply J.yonedaEquiv.injective
      rw [Equiv.apply_symm_apply, K.yonedaEquiv_comp, J.yonedaEquiv_comp,
        Equiv.apply_symm_apply]
      rfl)

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry.Scheme

instance : etaleTopology.Subcanonical :=
  .of_le (etaleTopology_le_proetaleTopology.trans proetaleTopology_le_fpqcTopology)

variable (X : Scheme.{u})

instance : RepresentablyFlat (Etale.forget X) := flat_of_preservesFiniteLimits _

instance : (Etale.forget X).IsContinuous X.smallEtaleTopology (etaleTopology.over X) := by
  have : (Etale.forget X).LocallyCoverDense (etaleTopology.over X) :=
    locallyCoverDense_of_le X (P := @Etale) le_rfl
  rw [Functor.isContinuous_iff_coverPreserving]
  exact Functor.coverPreserving_restrictedTopology (Etale.forget X) (etaleTopology.over X)

instance : X.smallEtaleTopology.Subcanonical :=
  GrothendieckTopology.subcanonical_of_full_of_faithful (Etale.forget X) _ (etaleTopology.over X)

/-- The Yoneda embedding of the small étale site of `X` into étale sheaves of sets. -/
noncomputable abbrev etaleYoneda : X.Etale ⥤ Sheaf X.smallEtaleTopology (Type u) :=
  X.smallEtaleTopology.yoneda

/-- The étale Yoneda embedding is fully faithful. -/
noncomputable def etaleYonedaFullyFaithful : (etaleYoneda X).FullyFaithful :=
  X.smallEtaleTopology.yonedaFullyFaithful

/-- Every sieve on an object of the small étale site with empty underlying scheme covers. -/
lemma mem_smallEtaleTopology_of_isEmpty {W : X.Etale} [IsEmpty W.left] (R : Sieve W) :
    R ∈ X.smallEtaleTopology W :=
  (mem_smallEtaleTopology_iff W R).2 fun x ↦ isEmptyElim x

variable (E : Type u)

/-- The constant `X`-scheme with value `E` as an object of the small étale site. -/
noncomputable abbrev Etale.constant : X.Etale := Etale.mk (constantSchemeHom X E)

/-- The comparison map from the constant presheaf with value `E` to the presheaf represented by
the constant `X`-scheme: `e` goes to the composition of the structure morphism with the `e`-th
inclusion. -/
@[simps]
noncomputable def constantPresheafToYoneda :
    (Functor.const X.Etaleᵒᵖ).obj E ⟶ ((etaleYoneda X).obj (Etale.constant X E)).obj where
  app U := ↾fun e ↦ (MorphismProperty.Over.homMk (U.unop.hom ≫ constantSchemeι X E e)
    (by simp [Etale.constant]) trivial : U.unop ⟶ Etale.constant X E)
  naturality U V f := by
    ext e
    apply MorphismProperty.Over.Hom.ext
    change _ = f.unop.left ≫ U.unop.hom ≫ _
    rw [MorphismProperty.Over.w_assoc]
    rfl

instance : Presheaf.IsLocallyInjective X.smallEtaleTopology (constantPresheafToYoneda X E) where
  equalizerSieve_mem {U} x y h := by
    by_cases hxy : x = y
    · subst hxy
      rw [Presheaf.equalizerSieve_self_eq_top]
      exact GrothendieckTopology.top_mem _ _
    · have : IsEmpty U.unop.left :=
        isEmpty_of_comp_constantSchemeι_eq X E U.unop.hom hxy
          (congrArg (fun φ ↦ φ.left) h)
      exact mem_smallEtaleTopology_of_isEmpty X _

instance : Presheaf.IsLocallySurjective X.smallEtaleTopology (constantPresheafToYoneda X E) where
  imageSieve_mem {U} s := by
    rw [mem_smallEtaleTopology_iff]
    intro u
    obtain ⟨e, x, hx⟩ := constantSchemeι_surjective X E (s.left u)
    obtain ⟨z, hz, -⟩ :=
      Pullback.exists_preimage_pullback (f := s.left) (g := constantSchemeι X E e) u x hx.symm
    let V : X.Etale := Etale.mk (pullback.fst s.left (constantSchemeι X E e) ≫ U.hom)
    let f : V ⟶ U := MorphismProperty.Over.homMk (pullback.fst _ _) rfl trivial
    refine ⟨V, f, z, ⟨e, ?_⟩, hz⟩
    apply MorphismProperty.Over.Hom.ext
    have hs : s.left ≫ constantSchemeHom X E = U.hom := MorphismProperty.Over.w s
    change (pullback.fst s.left (constantSchemeι X E e) ≫ U.hom) ≫ constantSchemeι X E e =
      pullback.fst s.left (constantSchemeι X E e) ≫ s.left
    rw [← hs, pullback.condition_assoc, constantSchemeι_hom, Category.comp_id,
      pullback.condition]

/-- The constant sheaf with value `E` on the small étale site of `X` is represented by the
constant `X`-scheme `∐_{e ∈ E} X`. -/
noncomputable def constantSheafIsoYoneda :
    (constantSheaf X.smallEtaleTopology (Type u)).obj E ≅
      (etaleYoneda X).obj (Etale.constant X E) :=
  have : X.smallEtaleTopology.W (constantPresheafToYoneda X E) :=
    GrothendieckTopology.W_of_isLocallyBijective _ _
  have : IsIso ((presheafToSheaf _ _).map (constantPresheafToYoneda X E)) := by
    rwa [← GrothendieckTopology.W_iff]
  asIso ((presheafToSheaf _ _).map (constantPresheafToYoneda X E)) ≪≫
    (sheafificationIso _).symm

variable {X} {Y : Scheme.{u}}

/-- The inverse image along `f : X ⟶ Y` of the sheaf represented by an étale `Y`-scheme `W` is
represented by `X ×_Y W`. -/
noncomputable def etalePullbackYonedaIso (f : X ⟶ Y) (W : Y.Etale) :
    (etalePullback f).obj ((etaleYoneda Y).obj W) ≅
      (etaleYoneda X).obj ((Etale.pullback f).obj W) :=
  GrothendieckTopology.yonedaObjLeftAdjointIso (etaleAdjunction f) W

/-- The terminal object `X` of the small étale site of `X` is the base change of the terminal
object `Y` of the small étale site of `Y`. -/
noncomputable def Etale.pullbackTopIso (f : X ⟶ Y) :
    (Etale.pullback f).obj (Etale.top Y) ≅ Etale.top X :=
  (Etale.isTerminalTop Y).isTerminalObj (Etale.pullback f) |>.uniqueUpToIso
    (Etale.isTerminalTop X)

/-- Global sections of a direct image: `Γ(Y, f_* F) ≅ Γ(X, F)`. -/
noncomputable def etalePushforwardSectionsIso (f : X ⟶ Y) :
    etalePushforward f ⋙ (sheafSections Y.smallEtaleTopology (Type u)).obj (op (Etale.top Y)) ≅
      (sheafSections X.smallEtaleTopology (Type u)).obj (op (Etale.top X)) :=
  (sheafSections X.smallEtaleTopology (Type u)).mapIso (Etale.pullbackTopIso f).op.symm

/-- The inverse image of a constant sheaf is the constant sheaf with the same value. -/
noncomputable def etalePullbackConstantSheafIso (f : X ⟶ Y) :
    constantSheaf Y.smallEtaleTopology (Type u) ⋙ etalePullback f ≅
      constantSheaf X.smallEtaleTopology (Type u) :=
  ((constantSheafAdj _ (Type u) (Etale.isTerminalTop Y)).comp (etaleAdjunction f)).leftAdjointUniq
    ((constantSheafAdj _ (Type u) (Etale.isTerminalTop X)).ofNatIsoRight
      (etalePushforwardSectionsIso f).symm)

end AlgebraicGeometry.Scheme
