/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Group.Shrink
import SGA.Foundations.Etale.TorsorEtale

/-!
# The group twisted by a torsor

For a `G`-torsor `P` on a site `(C, J)`, the automorphisms of the restrictions `P|U` form a
presheaf of groups `U ↦ Aut(P|U)` (`Torsor.autPresheaf`), which is a sheaf; more generally the
morphisms of torsors `P|U ⟶ Q|U` form a sheaf (`Torsor.isSheaf_homSubfunctor`, descent of
morphisms). This is the group
`^P G` obtained by twisting `G` by `P` through inner automorphisms (Giraud III 2.3). Since `C`
may be large, its values are a priori in a larger universe; when `P` is trivialized by
`w`-small covering families (for instance on the small étale site of a scheme,
`Scheme.small_aut_over`) we shrink them, obtaining a presheaf of groups `Torsor.twist P` in the
universe of `G` whose underlying presheaf of sets is a sheaf (`Torsor.isSheaf_twist`,
`Torsor.twistSheaf`). Twisting by the trivial torsor gives back `G` as a sheaf of sets
(`Torsor.twistSheafTrivialIso`): the automorphisms of the trivial torsor are the right
multiplications (`Torsor.trivialAutEval`).

## References

* [J. Giraud, *Cohomologie non abélienne*, III 2.3][giraud1971]
* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
-/

universe w v u

open CategoryTheory Opposite Limits

namespace CategoryTheory.Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat.{w}}
  (P : Torsor J G)

lemma over_overMap {T T' : C} (f : T' ⟶ T) : (P.over T).overMap f = P.over T' :=
  rfl

/-- The restriction of automorphisms of `P|T` to `P|T'` along `f : T' ⟶ T`. -/
def autRestrict {T T' : C} (f : T' ⟶ T) : Aut (P.over T) →* Aut (P.over T') :=
  Functor.mapAut (P.over T) (restrictFunctor (J.over T') (Over.map f))

lemma autRestrict_hom_app {T T' : C} (f : T' ⟶ T) (φ : Aut (P.over T)) (Y : Over T')
    (x : P.obj.obj (op Y.left)) :
    (autRestrict P f φ).hom.hom.app (op Y) x = φ.hom.hom.app (op ((Over.map f).obj Y)) x :=
  rfl

/-- Naturality of the components of an endomorphism of `P|T`. -/
lemma hom_app_naturality {T : C} (φ : P.over T ⟶ P.over T) {Y Y' : Over T} (a : Y' ⟶ Y)
    (x : P.obj.obj (op Y.left)) :
    φ.hom.app (op Y') (P.obj.map a.left.op x) = P.obj.map a.left.op (φ.hom.app (op Y) x) :=
  NatTrans.naturality_apply φ.hom a.op x

variable (J G) in
/-- The large presheaf of groups `U ↦ Aut(P|U)`. -/
def autPresheaf : Cᵒᵖ ⥤ GrpCat.{max u v w} where
  obj T := GrpCat.of (Aut (P.over T.unop))
  map f := GrpCat.ofHom (autRestrict P f.unop)
  map_id T := by
    ext φ : 2
    apply Iso.ext
    apply Torsor.hom_ext
    ext Y x
    change φ.hom.hom.app (op ((Over.map (𝟙 T.unop)).obj Y.unop)) x = φ.hom.hom.app Y x
    have : φ.hom.hom.app (op ((Over.map (𝟙 T.unop)).obj Y.unop)) (P.obj.map (𝟙 Y.unop.left).op x)
        = P.obj.map (𝟙 Y.unop.left).op (φ.hom.hom.app Y x) := hom_app_naturality P φ.hom
      (Over.homMk (𝟙 Y.unop.left) (by simp) : (Over.map (𝟙 T.unop)).obj Y.unop ⟶ Y.unop) x
    have e : P.obj.map (𝟙 Y.unop.left).op = 𝟙 _ := by rw [op_id, P.obj.map_id]
    rw [e] at this
    exact this
  map_comp {T T' T''} f g := by
    ext φ : 2
    apply Iso.ext
    apply Torsor.hom_ext
    ext Y x
    change φ.hom.hom.app (op ((Over.map (g.unop ≫ f.unop)).obj Y.unop)) x =
      φ.hom.hom.app (op ((Over.map f.unop).obj ((Over.map g.unop).obj Y.unop))) x
    have : φ.hom.hom.app (op ((Over.map f.unop).obj ((Over.map g.unop).obj Y.unop)))
        (P.obj.map (𝟙 Y.unop.left).op x) = P.obj.map (𝟙 Y.unop.left).op
          (φ.hom.hom.app (op ((Over.map (g.unop ≫ f.unop)).obj Y.unop)) x) :=
      hom_app_naturality P φ.hom (Over.homMk (𝟙 Y.unop.left) (by simp) :
        (Over.map f.unop).obj ((Over.map g.unop).obj Y.unop) ⟶
          (Over.map (g.unop ≫ f.unop)).obj Y.unop) x
    have e : P.obj.map (𝟙 Y.unop.left).op = 𝟙 _ := by rw [op_id, P.obj.map_id]
    rw [e] at this
    exact this.symm

/-- A section of `presheafHom P.obj P.obj` evaluated as a map of sections of `P`. -/
def endEval {T : C} (u : (presheafHom P.obj P.obj).obj (op T)) (Y : Over T)
    (x : P.obj.obj (op Y.left)) : P.obj.obj (op Y.left) :=
  u.app (op Y) x

/-- The subpresheaf of `presheafHom P.obj P.obj` of `G`-equivariant endomorphisms. -/
def autSubfunctor : Subfunctor (presheafHom P.obj P.obj) where
  obj T := {u | ∀ (Y : Over T.unop) (g : G.obj (op Y.left)) (x : P.obj.obj (op Y.left)),
    endEval P u Y (g • x) = g • endEval P u Y x}
  map {_ _} f _ hu Y g x := hu ((Over.map f.unop).obj Y) g x

/-- An automorphism of `P|T` is a `G`-equivariant endomorphism of the underlying presheaf. -/
noncomputable def autEquiv (T : C) : Aut (P.over T) ≃ (autSubfunctor P).toFunctor.obj (op T) where
  toFun φ := ⟨φ.hom.hom, fun Y g x ↦ φ.hom.map_smul (op Y) g x⟩
  invFun u := asIso (⟨u.1, fun Y g x ↦ u.2 Y.unop g x⟩ : P.over T ⟶ P.over T)
  left_inv φ := by
    apply Iso.ext
    rfl
  right_inv u := rfl

lemma autEquiv_naturality {T T' : C} (f : T' ⟶ T) (φ : Aut (P.over T)) :
    autEquiv P T' (autRestrict P f φ) = (autSubfunctor P).toFunctor.map f.op (autEquiv P T φ) :=
  rfl

variable {P} in
lemma isSheaf_autSubfunctor : Presieve.IsSheaf J (autSubfunctor P).toFunctor := by
  have hHom : Presieve.IsSheaf J (presheafHom P.obj P.obj) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (Presheaf.IsSheaf.hom _ _ ((isSheaf_iff_isSheaf_of_type _ _).2 P.isSheaf))
  rw [Subfunctor.isSheaf_iff _ hHom]
  intro T u hu Y g x
  apply (P.isSheaf _ (J.pullback_stable Y.hom hu)).isSeparatedFor.ext
  intro Z a ha
  let Y'' : Over T.unop := (Over.map (a ≫ Y.hom)).obj (Over.mk (𝟙 Z))
  let b : Y'' ⟶ Y := Over.homMk a (by simp [Y''])
  let act : P.obj.obj (op Z) → P.obj.obj (op Z) := fun z ↦ G.map a.op g • z
  have h : endEval P u Y'' (act (P.obj.map a.op x)) = act (endEval P u Y'' (P.obj.map a.op x)) :=
    ha (Over.mk (𝟙 Z)) (G.map a.op g) (P.obj.map a.op x)
  have e₁ : endEval P u Y'' (P.obj.map a.op (g • x)) = P.obj.map a.op (endEval P u Y (g • x)) :=
    NatTrans.naturality_apply u b.op (g • x)
  have e₂ : endEval P u Y'' (P.obj.map a.op x) = P.obj.map a.op (endEval P u Y x) :=
    NatTrans.naturality_apply u b.op x
  have m₁ : P.obj.map a.op (g • x) = act (P.obj.map a.op x) := P.map_smul' a.op g x
  have m₂ : P.obj.map a.op (g • endEval P u Y x) = act (P.obj.map a.op (endEval P u Y x)) :=
    P.map_smul' a.op g _
  change P.obj.map a.op (endEval P u Y (g • x)) = P.obj.map a.op (g • endEval P u Y x)
  rw [← e₁, m₁, h, e₂, m₂]

/-- The large presheaf `U ↦ Aut(P|U)` is a sheaf of sets. -/
lemma isSheaf_autPresheaf :
    Presieve.IsSheaf J (autPresheaf J G P ⋙ CategoryTheory.forget GrpCat) :=
  Presieve.isSheaf_of_nat_equiv (P₁ := (autSubfunctor P).toFunctor)
    (fun T ↦ (autEquiv P T).symm) (fun _ _ _ _ ↦ Iso.ext (Torsor.hom_ext rfl))
    isSheaf_autSubfunctor

section Hom

variable (Q : Torsor J G)

/-- A section of `presheafHom P.obj Q.obj` evaluated as a map of sections. -/
def homEval {T : C} (u : (presheafHom P.obj Q.obj).obj (op T)) (Y : Over T)
    (x : P.obj.obj (op Y.left)) : Q.obj.obj (op Y.left) :=
  u.app (op Y) x

/-- The subpresheaf of `presheafHom P.obj Q.obj` of `G`-equivariant morphisms: its sections over
`T` are the morphisms of torsors `P|T ⟶ Q|T` (`Torsor.homEquiv`). -/
def homSubfunctor : Subfunctor (presheafHom P.obj Q.obj) where
  obj T := {u | ∀ (Y : Over T.unop) (g : G.obj (op Y.left)) (x : P.obj.obj (op Y.left)),
    homEval P Q u Y (g • x) = g • homEval P Q u Y x}
  map {_ _} f _ hu Y g x := hu ((Over.map f.unop).obj Y) g x

/-- Morphisms of torsors `P|T ⟶ Q|T` are the equivariant morphisms of the underlying
presheaves. -/
def homEquiv (T : C) : (P.over T ⟶ Q.over T) ≃ (homSubfunctor P Q).toFunctor.obj (op T) where
  toFun φ := ⟨φ.hom, fun Y g x ↦ φ.map_smul (op Y) g x⟩
  invFun u := ⟨u.1, fun Y g x ↦ u.2 Y.unop g x⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Descent of morphisms for torsors (the torsors form a prestack, Giraud III 1.4.1): the
presheaf of morphisms of torsors `T ↦ Hom(P|T, Q|T)` is a sheaf. -/
lemma isSheaf_homSubfunctor : Presieve.IsSheaf J (homSubfunctor P Q).toFunctor := by
  have hHom : Presieve.IsSheaf J (presheafHom P.obj Q.obj) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (Presheaf.IsSheaf.hom _ _ ((isSheaf_iff_isSheaf_of_type _ _).2 Q.isSheaf))
  rw [Subfunctor.isSheaf_iff _ hHom]
  intro T u hu Y g x
  apply (Q.isSheaf _ (J.pullback_stable Y.hom hu)).isSeparatedFor.ext
  intro Z a ha
  let Y'' : Over T.unop := (Over.map (a ≫ Y.hom)).obj (Over.mk (𝟙 Z))
  let b : Y'' ⟶ Y := Over.homMk a (by simp [Y''])
  let ev : ∀ (W : Over T.unop), P.obj.obj (op W.left) → Q.obj.obj (op W.left) :=
    fun W z ↦ homEval P Q u W z
  let actP : P.obj.obj (op Z) → P.obj.obj (op Z) := fun z ↦ G.map a.op g • z
  let actQ : Q.obj.obj (op Z) → Q.obj.obj (op Z) := fun z ↦ G.map a.op g • z
  have h : ev Y'' (actP (P.obj.map a.op x)) = actQ (ev Y'' (P.obj.map a.op x)) :=
    ha (Over.mk (𝟙 Z)) (G.map a.op g) (P.obj.map a.op x)
  have e₁ : ev Y'' (P.obj.map a.op (g • x)) = Q.obj.map a.op (ev Y (g • x)) :=
    NatTrans.naturality_apply u b.op (g • x)
  have e₂ : ev Y'' (P.obj.map a.op x) = Q.obj.map a.op (ev Y x) :=
    NatTrans.naturality_apply u b.op x
  have m₁ : P.obj.map a.op (g • x) = actP (P.obj.map a.op x) := P.map_smul' a.op g x
  have m₂ : Q.obj.map a.op (g • ev Y x) = actQ (Q.obj.map a.op (ev Y x)) :=
    Q.map_smul' a.op g _
  change Q.obj.map a.op (ev Y (g • x)) = Q.obj.map a.op (g • ev Y x)
  rw [← e₁, m₁, h, e₂, m₂]

end Hom

variable {P}

/-- If `P` has sections on the members of a `w`-small covering family of `T`, the group
`Aut(P|T)` is `w`-small. -/
lemma small_aut_over {T : C} {I : Type w} {V : I → C} (f : ∀ i, V i ⟶ T)
    (hf : Sieve.ofArrows V f ∈ J T) (hV : ∀ i, Nonempty (P.obj.obj (op (V i)))) :
    Small.{w} (Aut (P.over T)) := by
  let ι : Aut (P.over T) → ∀ i, G.obj (op (V i)) := fun φ i ↦
    P.diff (hV i).some (φ.hom.hom.app (op (Over.mk (f i))) (hV i).some)
  refine small_of_injective (f := ι) fun φ ψ h ↦ ?_
  apply Iso.ext
  apply Torsor.hom_ext
  apply NatTrans.ext
  funext Y₀
  ext x
  apply (P.isSheaf _ (J.pullback_stable Y₀.unop.hom hf)).isSeparatedFor.ext
  rintro Z a ⟨W, b, c, ⟨i⟩, hbc⟩
  have hi : ∀ χ : Aut (P.over T), P.obj.map a.op (χ.hom.hom.app Y₀ x) =
      P.diff (P.obj.map b.op (hV i).some) (P.obj.map a.op x) •
        P.obj.map b.op (χ.hom.hom.app (op (Over.mk (f i))) (hV i).some) := by
    intro χ
    have e₁ : χ.hom.hom.app (op (Over.mk (a ≫ Y₀.unop.hom))) (P.obj.map a.op x) =
        P.obj.map a.op (χ.hom.hom.app Y₀ x) :=
      hom_app_naturality P χ.hom (Over.homMk a rfl : Over.mk (a ≫ Y₀.unop.hom) ⟶ Y₀.unop) x
    have e₂ : χ.hom.hom.app (op (Over.mk (a ≫ Y₀.unop.hom))) (P.obj.map b.op (hV i).some) =
        P.obj.map b.op (χ.hom.hom.app (op (Over.mk (f i))) (hV i).some) :=
      hom_app_naturality P χ.hom (Over.homMk b hbc : Over.mk (a ≫ Y₀.unop.hom) ⟶ Over.mk (f i))
        (hV i).some
    rw [← e₁, ← e₂]
    refine Eq.trans ?_ (Torsor.hom_map_smul χ.hom (U := op (Over.mk (a ≫ Y₀.unop.hom))) _ _)
    exact congr_arg _ (P.diff_smul _ _).symm
  have key : φ.hom.hom.app (op (Over.mk (f i))) (hV i).some =
      ψ.hom.hom.app (op (Over.mk (f i))) (hV i).some := by
    have h' : P.diff (hV i).some (φ.hom.hom.app (op (Over.mk (f i))) (hV i).some) =
        P.diff (hV i).some (ψ.hom.hom.app (op (Over.mk (f i))) (hV i).some) := congr_fun h i
    have e₁ := P.diff_smul (hV i).some
      (show P.obj.obj (op (V i)) from φ.hom.hom.app (op (Over.mk (f i))) (hV i).some)
    have e₂ := P.diff_smul (hV i).some
      (show P.obj.obj (op (V i)) from ψ.hom.hom.app (op (Over.mk (f i))) (hV i).some)
    exact e₁.symm.trans ((congr_arg (· • (hV i).some) h').trans e₂)
  exact (hi φ).trans ((congr_arg (fun z ↦ P.diff (P.obj.map b.op (hV i).some)
    (P.obj.map a.op x) • P.obj.map b.op z) key).trans (hi ψ).symm)

variable (P) in
/-- The identification of the shrunk automorphism group with `Aut(P|T)`. -/
noncomputable abbrev twistEquiv (T : C) [Small.{w} (Aut (P.over T))] :
    Shrink.{w} (Aut (P.over T)) ≃* Aut (P.over T) :=
  Shrink.mulEquiv

variable (P) in
/-- The group `^P G` obtained by twisting `G` by the torsor `P`: the presheaf of groups
`U ↦ Aut(P|U)`, shrunk to the universe of `G` (given that these groups are `w`-small). -/
noncomputable def twist [∀ T : C, Small.{w} (Aut (P.over T))] : Cᵒᵖ ⥤ GrpCat.{w} where
  obj T := GrpCat.of (Shrink.{w} (Aut (P.over T.unop)))
  map {T T'} f := GrpCat.ofHom (((twistEquiv P T'.unop).symm.toMonoidHom.comp
    (autRestrict P f.unop)).comp (twistEquiv P T.unop).toMonoidHom)
  map_id T := by
    ext φ : 2
    change (twistEquiv P T.unop).symm ((autPresheaf J G P).map (𝟙 T)
      (twistEquiv P T.unop φ)) = φ
    rw [CategoryTheory.Functor.map_id]
    exact (twistEquiv P T.unop).symm_apply_apply φ
  map_comp {T T' T''} f g := by
    ext φ : 2
    change (twistEquiv P T''.unop).symm ((autPresheaf J G P).map (f ≫ g)
        (twistEquiv P T.unop φ)) =
      (twistEquiv P T''.unop).symm ((autPresheaf J G P).map g ((twistEquiv P T'.unop)
        ((twistEquiv P T'.unop).symm ((autPresheaf J G P).map f (twistEquiv P T.unop φ)))))
    rw [Functor.map_comp]
    congr 1
    exact congr_arg ((autPresheaf J G P).map g)
      ((twistEquiv P T'.unop).apply_symm_apply _).symm

/-- The twisted group `^P G` is a sheaf. -/
lemma isSheaf_twist [∀ T : C, Small.{w} (Aut (P.over T))] :
    Presieve.IsSheaf J (twist P ⋙ CategoryTheory.forget GrpCat) :=
  Presieve.isSheaf_of_nat_equiv (P₁ := autPresheaf J G P ⋙ CategoryTheory.forget GrpCat)
    (fun T ↦ (twistEquiv P T).symm.toEquiv) (fun T T' f φ ↦ by
      change (twistEquiv P T).symm ((autPresheaf J G P).map f.op φ) =
        (twistEquiv P T).symm ((autPresheaf J G P).map f.op
          ((twistEquiv P T') ((twistEquiv P T').symm φ)))
      exact congr_arg (fun z ↦ (twistEquiv P T).symm ((autPresheaf J G P).map f.op z))
        ((twistEquiv P T').apply_symm_apply φ).symm) (isSheaf_autPresheaf P)

section Trivial

variable (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))

/-- The value at the unit section of an automorphism of the restriction of the trivial torsor:
automorphisms of the trivial torsor are the right multiplications. -/
def trivialAutEval (T : C) (φ : Aut ((trivial J G hG).over T)) : G.obj (op T) :=
  φ.hom.hom.app (op (Over.mk (𝟙 T))) (1 : G.obj (op T))

lemma trivialAutEval_injective (T : C) : Function.Injective (trivialAutEval hG T) := by
  intro φ ψ h
  apply Iso.ext
  apply Torsor.hom_ext
  ext Y (x : G.obj (op Y.unop.left))
  have key : ∀ χ : Aut ((trivial J G hG).over T), χ.hom.hom.app Y x =
      x * G.map Y.unop.hom.op (trivialAutEval hG T χ) := by
    intro χ
    let a : Y.unop ⟶ Over.mk (𝟙 T) := Over.homMk Y.unop.hom
    have e₁ : χ.hom.hom.app Y (1 : G.obj (op Y.unop.left)) =
        G.map Y.unop.hom.op (trivialAutEval hG T χ) := by
      have := NatTrans.naturality_apply χ.hom.hom a.op (1 : G.obj (op T))
      have e : ((trivial J G hG).over T).obj.map a.op (1 : G.obj (op T)) =
          (1 : G.obj (op Y.unop.left)) := map_one (G.map a.left.op).hom
      rw [e] at this
      exact this
    have e₂ := χ.hom.map_smul Y x (1 : G.obj (op Y.unop.left))
    have e₃ : (x • (1 : G.obj (op Y.unop.left)) : ((trivial J G hG).over T).obj.obj Y) = x :=
      mul_one (show G.obj (op Y.unop.left) from x)
    refine (congrArg (χ.hom.hom.app Y) e₃.symm).trans (e₂.trans ?_)
    erw [e₁]
    rfl
  exact (key φ).trans (by rw [h]; exact (key ψ).symm)

/-- The right multiplication by `g ∈ G(T)`, an endomorphism of the restriction of the trivial
torsor. -/
def trivialMulRight {T : C} (g : G.obj (op T)) :
    (trivial J G hG).over T ⟶ (trivial J G hG).over T where
  hom :=
    { app Y := ↾fun (x : G.obj (op Y.unop.left)) ↦ (x * G.map Y.unop.hom.op g : G.obj _)
      naturality Y Y' b := by
        ext (x : G.obj (op Y.unop.left))
        change G.map b.unop.left.op x * G.map Y'.unop.hom.op g =
          G.map b.unop.left.op (x * G.map Y.unop.hom.op g)
        rw [map_mul, ← GrpCat.comp_apply, ← G.map_comp, ← op_comp, Over.w b.unop] }
  map_smul Y h x := mul_assoc (show G.obj (op Y.unop.left) from h) x _

lemma trivialAutEval_surjective (T : C) : Function.Surjective (trivialAutEval hG T) := by
  intro g
  refine ⟨@asIso _ _ _ _ (trivialMulRight hG g) (Torsor.isIso _), ?_⟩
  change (1 : G.obj (op T)) * G.map (𝟙 T).op g = g
  rw [op_id, G.map_id, one_mul]
  rfl

instance small_aut_over_trivial (T : C) : Small.{w} (Aut ((trivial J G hG).over T)) :=
  small_of_injective (trivialAutEval_injective hG T)

lemma trivialAutEval_autRestrict {T T' : C} (f : T' ⟶ T) (φ : Aut ((trivial J G hG).over T)) :
    trivialAutEval hG T' (autRestrict _ f φ) = G.map f.op (trivialAutEval hG T φ) := by
  let a : (Over.map f).obj (Over.mk (𝟙 T')) ⟶ Over.mk (𝟙 T) := Over.homMk f
  have := NatTrans.naturality_apply φ.hom.hom a.op (1 : G.obj (op T))
  have e : ((trivial J G hG).over T).obj.map a.op (1 : G.obj (op T)) = (1 : G.obj (op T')) :=
    map_one (G.map a.left.op).hom
  rw [e] at this
  exact this.trans rfl

/-- The group obtained by twisting `G` by the trivial torsor is `G`, as a sheaf of sets: an
automorphism of the trivial torsor is the right multiplication by its value at the unit. -/
noncomputable def twistTrivialIso :
    twist (trivial J G hG) ⋙ CategoryTheory.forget GrpCat ≅ G ⋙ CategoryTheory.forget GrpCat :=
  NatIso.ofComponents (fun T ↦ Equiv.toIso ((equivShrink _).symm.trans
    (Equiv.ofBijective _ ⟨trivialAutEval_injective hG T.unop,
      trivialAutEval_surjective hG T.unop⟩))) (by
    intro T T' f
    ext φ
    change trivialAutEval hG T'.unop ((twistEquiv _ T'.unop) ((twistEquiv _ T'.unop).symm
      (autRestrict _ f.unop ((twistEquiv _ T.unop) φ)))) =
        G.map f (trivialAutEval hG T.unop ((twistEquiv _ T.unop) φ))
    rw [MulEquiv.apply_symm_apply, trivialAutEval_autRestrict]
    rfl)

end Trivial

/-- The twisted group `^P G`, as a sheaf of sets. -/
noncomputable def twistSheaf (P : Torsor J G) [∀ T : C, Small.{w} (Aut (P.over T))] :
    Sheaf J (Type w) :=
  ⟨twist P ⋙ CategoryTheory.forget GrpCat,
    (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_twist (P := P))⟩

/-- The twist of `G` by the trivial torsor is `G`, as a sheaf of sets. -/
noncomputable def twistSheafTrivialIso
    (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat)) :
    twistSheaf (trivial J G hG) ≅
      ⟨G ⋙ CategoryTheory.forget GrpCat, (isSheaf_iff_isSheaf_of_type _ _).2 hG⟩ :=
  ObjectProperty.isoMk _ (twistTrivialIso hG)

end CategoryTheory.Torsor

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {G : Y.Etaleᵒᵖ ⥤ GrpCat.{u}}

/-- On the small étale site, the automorphism groups of the restrictions of a torsor are small. -/
lemma small_aut_over (P : Torsor Y.smallEtaleTopology G) (T : Y.Etale) :
    Small.{u} (Aut (P.over T)) := by
  have h := (mem_smallEtaleTopology_iff _ _).1 (P.nonemptySieve_mem T)
  choose V f v hf hv using h
  exact Torsor.small_aut_over f ((ofArrows_mem_smallEtaleTopology_iff f).2
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨x, v x, hv x⟩)) hf

instance (P : Torsor Y.smallEtaleTopology G) (T : Y.Etale) : Small.{u} (Aut (P.over T)) :=
  small_aut_over P T

end AlgebraicGeometry.Scheme
