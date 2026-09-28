/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.ChangeOfGroup

/-!
# The non-abelian cohomology exact sequence

Let `1 → G' → G → G'' → 1` be a short exact sequence of sheaves of groups on a site `(C, J)`
with a terminal object `X` (`PresheafOfGroups.IsShortExact`): `i : G' ⟶ G` is injective on
sections, its image is the kernel of `p : G ⟶ G''`, and `p` is locally surjective. The fibre
`p⁻¹(c)` of a global section `c` of `G''` is a `G'`-torsor (`IsShortExact.fiberTorsor`), and
its class is the coboundary `δ c ∈ H¹(X, G')` (`IsShortExact.connecting`). We prove the
exactness of the sequence of pointed sets
```
1 → G'(X) → G(X) → G''(X) → H¹(X, G') → H¹(X, G) → H¹(X, G'')
```
and that `δ` identifies the orbits of `G(X)` acting on `G''(X)` with the fibres of `δ`.

## References

* [J. Giraud, *Cohomologie non abélienne*, III 3.3.1][giraud1971]
* [J.-P. Serre, *Cohomologie galoisienne*, I 5.5][serre1965]
* [Stacks Project, Tag 03AK](https://stacks.math.columbia.edu/tag/03AK)
-/

universe w v u

open CategoryTheory Opposite Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {G' G G'' : Cᵒᵖ ⥤ GrpCat.{w}}

/-- A short exact sequence `1 → G' → G → G'' → 1` of presheaves of groups for the topology `J`:
`i` is injective on sections, the image of `i` is the kernel of `p` on sections, and `p` is
locally surjective. -/
structure PresheafOfGroups.IsShortExact (i : G' ⟶ G) (p : G ⟶ G'') : Prop where
  injective (U : Cᵒᵖ) : Function.Injective (i.app U).hom
  exact (U : Cᵒᵖ) (g : G.obj U) : p.app U g = 1 ↔ ∃ g' : G'.obj U, i.app U g' = g
  locallySurjective (U : C) (c : G''.obj (op U)) : ∃ R ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), R f →
    ∃ g : G.obj (op V), p.app (op V) g = G''.map f.op c

namespace PresheafOfGroups.IsShortExact

variable {J} {i : G' ⟶ G} {p : G ⟶ G''} (h : IsShortExact J i p)
  (hG' : Presieve.IsSheaf J (G' ⋙ CategoryTheory.forget GrpCat))
  (hG : Presieve.IsSheaf J (G ⋙ CategoryTheory.forget GrpCat))
  (hG'' : Presieve.IsSheaf J (G'' ⋙ CategoryTheory.forget GrpCat))
  {X : C} (hX : IsTerminal X)

include h in
lemma p_app_i_app (U : Cᵒᵖ) (g' : G'.obj U) : p.app U (i.app U g') = 1 :=
  (h.exact U _).2 ⟨g', rfl⟩

/-- The subpresheaf `p⁻¹(c)` of `G`, for a global section `c` of `G''`. -/
def fiberSubfunctor (c : G''.obj (op X)) : Subfunctor (G ⋙ CategoryTheory.forget GrpCat) where
  obj U := {g | p.app U g = G''.map (hX.from U.unop).op c}
  map {U V} f g hg := by
    change p.app V (G.map f g) = G''.map (hX.from V.unop).op c
    have e : (hX.from U.unop).op ≫ f = (hX.from V.unop).op := Quiver.Hom.unop_inj (hX.hom_ext _ _)
    rw [NatTrans.naturality_apply p, show p.app U g = _ from hg, ← GrpCat.comp_apply,
      ← G''.map_comp, e]

lemma mem_fiberSubfunctor_iff (c : G''.obj (op X)) {U : Cᵒᵖ} (g : G.obj U) :
    g ∈ (fiberSubfunctor hX c (p := p)).obj U ↔ p.app U g = G''.map (hX.from U.unop).op c :=
  Iff.rfl

include hG hG'' in
lemma isSheaf_fiberSubfunctor (c : G''.obj (op X)) :
    Presieve.IsSheaf J (fiberSubfunctor hX c (p := p)).toFunctor := by
  rw [Subfunctor.isSheaf_iff _ hG]
  intro U g hg
  apply (hG'' _ hg).isSeparatedFor.ext
  intro V f hf
  change G''.map f.op (p.app U g) = G''.map f.op (G''.map (hX.from U.unop).op c)
  have hf' : p.app (op V) (G.map f.op g) = G''.map (hX.from V).op c := hf
  have e : (hX.from U.unop).op ≫ f.op = (hX.from V).op := Quiver.Hom.unop_inj (hX.hom_ext _ _)
  rw [← NatTrans.naturality_apply p, hf', ← GrpCat.comp_apply, ← G''.map_comp, e]

/-- The fibre `p⁻¹(c)` of a global section `c` of `G''`, a `G'`-torsor. -/
@[simps obj]
def fiberTorsor (c : G''.obj (op X)) : Torsor J G' where
  obj := (fiberSubfunctor hX c (p := p)).toFunctor
  isSheaf := isSheaf_fiberSubfunctor hG hG'' hX c
  smul U g' x := ⟨(i.app U g' * (show G.obj U from x.1) : G.obj U), by
    change p.app U (_ * _) = _
    rw [map_mul, h.p_app_i_app, one_mul]
    exact x.2⟩
  one_smul U x := Subtype.ext (by simp)
  mul_smul U a b x := Subtype.ext (by simp [mul_assoc])
  map_smul f g' x := Subtype.ext (by
    change G.map f (i.app _ g' * _) = i.app _ (G'.map f g') * G.map f _
    rw [map_mul, NatTrans.naturality_apply i])
  existsUnique_smul U x y := by
    obtain ⟨g', hg'⟩ := (h.exact U ((show G.obj U from y.1) * (show G.obj U from x.1)⁻¹)).1 (by
      rw [map_mul, map_inv, show p.app U x.1 = _ from x.2, show p.app U y.1 = _ from y.2,
        mul_inv_cancel])
    refine ⟨g', Subtype.ext ?_, fun g'' hg'' ↦ h.injective U ?_⟩
    · change i.app U g' * _ = _
      rw [hg', inv_mul_cancel_right]
    · have : i.app U g'' * (show G.obj U from x.1) = (show G.obj U from y.1) :=
        congr_arg Subtype.val hg''
      change i.app U g'' = i.app U g'
      rw [hg', ← this, mul_inv_cancel_right]
  locallyNonempty U := by
    obtain ⟨R, hR, hc⟩ := h.locallySurjective U (G''.map (hX.from U).op c)
    refine ⟨R, hR, fun V f hf ↦ ?_⟩
    obtain ⟨g, hg⟩ := hc f hf
    refine ⟨⟨g, ?_⟩⟩
    change p.app _ g = _
    have e : (hX.from U).op ≫ f.op = (hX.from V).op := Quiver.Hom.unop_inj (hX.hom_ext _ _)
    rw [hg, ← GrpCat.comp_apply, ← G''.map_comp, e]

/-- The coboundary map `δ : G''(X) → H¹(X, G')`, sending `c` to the class of the torsor
`p⁻¹(c)`. -/
def connecting (c : G''.obj (op X)) : H1 J G' :=
  (h.fiberTorsor hG hG'' hX c).class

variable {h hG hG'' hX} in
/-- A section of the fibre `p⁻¹(c)`, as a section of `G`. -/
def fiberVal {c : G''.obj (op X)} {U : Cᵒᵖ} (x : (h.fiberTorsor hG hG'' hX c).obj.obj U) :
    G.obj U :=
  x.1

variable {h hG hG'' hX}

lemma fiberVal_smul {c : G''.obj (op X)} {U : Cᵒᵖ} (g' : G'.obj U)
    (x : (h.fiberTorsor hG hG'' hX c).obj.obj U) :
    fiberVal (g' • x) = i.app U g' * fiberVal x :=
  rfl

lemma fiberVal_naturality {c : G''.obj (op X)} {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (h.fiberTorsor hG hG'' hX c).obj.obj U) :
    fiberVal ((h.fiberTorsor hG hG'' hX c).obj.map f x) = G.map f (fiberVal x) :=
  rfl

lemma p_app_fiberVal {c : G''.obj (op X)} {U : Cᵒᵖ} (x : (h.fiberTorsor hG hG'' hX c).obj.obj U) :
    p.app U (fiberVal x) = G''.map (hX.from U.unop).op c :=
  x.2

lemma fiberVal_injective {c : G''.obj (op X)} {U : Cᵒᵖ} :
    Function.Injective (fiberVal (h := h) (hG := hG) (hG'' := hG'') (hX := hX) (c := c) (U := U)) :=
  fun _ _ e ↦ Subtype.ext e

variable (h hG hG'' hX)

/-- The inclusion of the fibre `p⁻¹(c)` into `G`, an `i`-equivariant morphism. -/
def fiberHomOver (c : G''.obj (op X)) :
    Torsor.HomOver i (h.fiberTorsor hG hG'' hX c) (Torsor.trivial J G hG) where
  hom := (fiberSubfunctor hX c).ι
  map_smul _ _ _ := rfl

/-! ### Exactness -/

include h in
/-- Exactness at `G'(X)`: `G'(X) → G(X)` is injective. -/
theorem injective_app : Function.Injective (i.app (op X)).hom :=
  h.injective _

include h in
/-- Exactness at `G(X)`: the kernel of `G(X) → G''(X)` is the image of `G'(X)`. -/
theorem app_eq_one_iff (g : G.obj (op X)) :
    p.app (op X) g = 1 ↔ ∃ g' : G'.obj (op X), i.app (op X) g' = g :=
  h.exact _ g

/-- Exactness at `G''(X)`: `δ c` is trivial if and only if `c` lifts to `G(X)`. -/
theorem connecting_eq_trivialClass_iff (c : G''.obj (op X)) :
    h.connecting hG hG'' hX c = H1.trivialClass J G' hG' ↔
      ∃ g : G.obj (op X), p.app (op X) g = c := by
  have e : hX.from X = 𝟙 X := hX.hom_ext _ _
  rw [connecting, Torsor.class_eq_trivialClass_iff_of_isTerminal hX]
  constructor
  · rintro ⟨x⟩
    refine ⟨x.1, ?_⟩
    rw [show p.app (op X) x.1 = _ from p_app_fiberVal x, e, op_id, G''.map_id]
    rfl
  · rintro ⟨g, hg⟩
    refine ⟨⟨g, ?_⟩⟩
    change p.app _ g = _
    rw [e, op_id, G''.map_id, hg]
    rfl

/-- The coboundary of a global section lies in the kernel of `H¹(X, G') → H¹(X, G)`. -/
theorem map_connecting (c : G''.obj (op X)) :
    H1.map i hG (h.connecting hG hG'' hX c) = H1.trivialClass J G hG :=
  (H1.map_class_eq_class_iff i hG _ _).2 ⟨h.fiberHomOver hG hG'' hX c⟩

/-- A torsor with an `i`-equivariant map `ψ` to `G` is isomorphic to the fibre of `p` over the
global section `p ∘ ψ` of `G''`. -/
theorem exists_connecting_eq_of_homOver (P : Torsor J G')
    (ψ : Torsor.HomOver i P (Torsor.trivial J G hG)) :
    ∃ c : G''.obj (op X), h.connecting hG hG'' hX c = P.class := by
  let val {U : Cᵒᵖ} (x : P.obj.obj U) : G.obj U := ψ.val x
  have hval {U : Cᵒᵖ} (g' : G'.obj U) (x : P.obj.obj U) : val (g' • x) = i.app U g' * val x :=
    ψ.val_smul g' x
  have hnat {U V : Cᵒᵖ} (f : U ⟶ V) (x : P.obj.obj U) : val (P.obj.map f x) = G.map f (val x) :=
    ψ.val_naturality f x
  have indep {U : Cᵒᵖ} (x y : P.obj.obj U) : p.app U (val x) = p.app U (val y) := by
    rw [← P.diff_smul x y, hval, map_mul, h.p_app_i_app, one_mul]
  let S := P.nonemptySieve X
  let d : Presieve.FamilyOfElements (G'' ⋙ CategoryTheory.forget GrpCat) S.arrows :=
    fun V f hf ↦ p.app (op V) (val hf.some)
  have hd : d.Compatible := by
    intro Z₁ Z₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    change G''.map g₁.op (p.app _ (val h₁.some)) = G''.map g₂.op (p.app _ (val h₂.some))
    rw [← NatTrans.naturality_apply p, ← NatTrans.naturality_apply p, ← hnat, ← hnat]
    exact indep _ _
  obtain ⟨c, hc, -⟩ := hG'' S (P.nonemptySieve_mem X) d hd
  have hc' {U : Cᵒᵖ} (x : P.obj.obj U) : p.app U (val x) = G''.map (hX.from U.unop).op c := by
    have := hc (hX.from U.unop) ⟨x⟩
    change G''.map _ c = p.app _ (val (Nonempty.some _)) at this
    rw [this]
    exact indep _ _
  refine ⟨c, (Torsor.class_eq_class_iff _ _).2 ⟨(asIso ?_).symm⟩⟩
  exact
    { hom :=
        { app U := ↾fun x ↦ ⟨val x, hc' x⟩
          naturality U V f := by
            ext x
            exact Subtype.ext (hnat f x) }
      map_smul U g' x := Subtype.ext (hval g' x) }

/-- Exactness at `H¹(X, G')`: the kernel of `H¹(X, G') → H¹(X, G)` is the image of the
coboundary `δ`. -/
theorem map_eq_trivialClass_iff (P : Torsor J G') :
    H1.map i hG P.class = H1.trivialClass J G hG ↔
      ∃ c : G''.obj (op X), h.connecting hG hG'' hX c = P.class := by
  constructor
  · intro hP
    obtain ⟨ψ⟩ := (H1.map_class_eq_class_iff i hG _ _).1 hP
    exact h.exists_connecting_eq_of_homOver hG hG'' hX P ψ
  · rintro ⟨c, hc⟩
    rw [← hc]
    exact h.map_connecting hG hG'' hX c

include h in
/-- The constant map `1`, an `(i ≫ p)`-equivariant morphism to the trivial `G''`-torsor. -/
def oneHomOver (Q : Torsor J G') : Torsor.HomOver (i ≫ p) Q (Torsor.trivial J G'' hG'') where
  hom :=
    { app U := ↾fun _ ↦ (1 : G''.obj U)
      naturality U V f := by
        ext x
        exact (map_one (G''.map f).hom).symm }
  map_smul U g' x := by
    change (1 : G''.obj U) = p.app U (i.app U g') * 1
    rw [h.p_app_i_app, mul_one]

/-- The subpresheaf `ψ⁻¹(1)` of `P`, for a `p`-equivariant morphism `ψ : P ⟶ G''`. -/
def kernelSubfunctor (P : Torsor J G) (ψ : Torsor.HomOver p P (Torsor.trivial J G'' hG'')) :
    Subfunctor P.obj where
  obj U := {x | ψ.val x = 1}
  map {U V} f x (hx : ψ.val x = 1) := by
    change ψ.val (P.obj.map f x) = 1
    rw [ψ.val_naturality, hx, map_one]

include h in
/-- The kernel `ψ⁻¹(1)` of a `p`-equivariant morphism `ψ : P ⟶ G''`, a `G'`-torsor. -/
def kernelTorsor (P : Torsor J G) (ψ : Torsor.HomOver p P (Torsor.trivial J G'' hG'')) :
    Torsor J G' where
  obj := (kernelSubfunctor hG'' P ψ).toFunctor
  isSheaf := by
    rw [Subfunctor.isSheaf_iff _ P.isSheaf]
    intro U x hx
    apply (hG'' _ hx).isSeparatedFor.ext
    intro V f hf
    have hf' : ψ.val (P.obj.map f.op x) = 1 := hf
    change G''.map f.op (ψ.val x) = G''.map f.op 1
    rw [← ψ.val_naturality, hf', map_one]
  smul U g' x := ⟨i.app U g' • x.1, by
    change ψ.val (i.app U g' • x.1) = 1
    rw [ψ.val_smul, h.p_app_i_app]
    exact (one_mul _).trans x.2⟩
  one_smul U x := Subtype.ext (by simp)
  mul_smul U a b x := Subtype.ext (by simp [mul_smul])
  map_smul f g' x := Subtype.ext (by
    change P.obj.map f (i.app _ g' • x.1) = i.app _ (G'.map f g') • P.obj.map f x.1
    rw [Torsor.map_smul', NatTrans.naturality_apply i])
  existsUnique_smul U x y := by
    have hx : ψ.val x.1 = 1 := x.2
    have hy : ψ.val y.1 = 1 := y.2
    have hd : p.app U (P.diff x.1 y.1) = 1 := by
      have := ψ.val_smul (P.diff x.1 y.1) x.1
      rw [Torsor.diff_smul, hx, hy] at this
      exact (mul_one _).symm.trans this.symm
    obtain ⟨g', hg'⟩ := (h.exact U _).1 hd
    refine ⟨g', Subtype.ext ?_, fun g'' hg'' ↦ h.injective U ?_⟩
    · change i.app U g' • x.1 = y.1
      rw [hg', Torsor.diff_smul]
    · have : i.app U g'' • x.1 = y.1 := congr_arg Subtype.val hg''
      change i.app U g'' = i.app U g'
      rw [hg', eq_comm, Torsor.diff_eq_iff]
      exact this
  locallyNonempty U := by
    refine ⟨_, J.transitive (P.nonemptySieve_mem U)
      ((kernelSubfunctor hG'' P ψ).toFunctor.nonemptySieve' U) ?_, fun V f hf ↦ hf⟩
    intro V f ⟨x⟩
    obtain ⟨R, hR, hc⟩ := h.locallySurjective V (ψ.val x)
    refine J.superset_covering (fun W g hg ↦ ?_) hR
    obtain ⟨a, ha⟩ := hc g hg
    refine ⟨⟨a⁻¹ • P.obj.map g.op x, ?_⟩⟩
    change ψ.val (a⁻¹ • P.obj.map g.op x) = 1
    rw [ψ.val_smul, ψ.val_naturality, map_inv, ha]
    exact inv_mul_cancel _

include h in
/-- The inclusion `ψ⁻¹(1) ⟶ P`, an `i`-equivariant morphism. -/
def kernelHomOver (P : Torsor J G) (ψ : Torsor.HomOver p P (Torsor.trivial J G'' hG'')) :
    Torsor.HomOver i (h.kernelTorsor hG'' P ψ) P where
  hom := Subfunctor.ι _
  map_smul _ _ _ := rfl

include h in
/-- Exactness at `H¹(X, G)`: the kernel of `H¹(X, G) → H¹(X, G'')` is the image of
`H¹(X, G') → H¹(X, G)`. -/
theorem map_p_eq_trivialClass_iff (P : Torsor J G) :
    H1.map p hG'' P.class = H1.trivialClass J G'' hG'' ↔
      ∃ Q : Torsor J G', H1.map i hG Q.class = P.class := by
  constructor
  · intro hP
    obtain ⟨ψ⟩ := (H1.map_class_eq_class_iff p hG'' _ _).1 hP
    exact ⟨h.kernelTorsor hG'' P ψ,
      (H1.map_class_eq_class_iff i hG _ _).2 ⟨h.kernelHomOver hG'' P ψ⟩⟩
  · rintro ⟨Q, hQ⟩
    rw [← hQ, H1.map_map]
    exact (H1.map_class_eq_class_iff _ hG'' _ _).2 ⟨h.oneHomOver hG'' Q⟩

/-- Right multiplication by a global section `g` of `G`, from `p⁻¹(c)` to `p⁻¹(c * p(g))`. -/
def fiberTorsorMulRight (c : G''.obj (op X)) (g : G.obj (op X)) :
    h.fiberTorsor hG hG'' hX c ⟶ h.fiberTorsor hG hG'' hX (c * p.app (op X) g) where
  hom :=
    { app U := ↾fun x ↦ ⟨fiberVal x * G.map (hX.from U.unop).op g, by
        change p.app U (_ * _) = _
        rw [map_mul, p_app_fiberVal, NatTrans.naturality_apply p, map_mul]⟩
      naturality U V f := by
        ext x
        apply Subtype.ext
        change G.map f (fiberVal x) * G.map (hX.from V.unop).op g =
          G.map f (fiberVal x * G.map (hX.from U.unop).op g)
        have e : (hX.from U.unop).op ≫ f = (hX.from V.unop).op :=
          Quiver.Hom.unop_inj (hX.hom_ext _ _)
        rw [map_mul, ← GrpCat.comp_apply, ← G.map_comp, e] }
  map_smul U g' x := Subtype.ext (by
    change (i.app U g' * fiberVal x) * _ = i.app U g' * (fiberVal x * _)
    rw [mul_assoc])

/-- The fibres of the coboundary `δ : G''(X) → H¹(X, G')` are the orbits of `G(X)` acting on
`G''(X)` by right multiplication through `p`. -/
theorem connecting_eq_connecting_iff (c c' : G''.obj (op X)) :
    h.connecting hG hG'' hX c = h.connecting hG hG'' hX c' ↔
      ∃ g : G.obj (op X), c' = c * p.app (op X) g := by
  rw [connecting, connecting, Torsor.class_eq_class_iff]
  constructor
  · rintro ⟨e⟩
    let P := h.fiberTorsor hG hG'' hX c
    let k {U : Cᵒᵖ} (x : P.obj.obj U) : G.obj U := (fiberVal x)⁻¹ * fiberVal (e.hom.hom.app U x)
    have hk {U : Cᵒᵖ} (x y : P.obj.obj U) : k x = k y := by
      rw [← P.diff_smul x y]
      simp only [k]
      rw [Torsor.hom_map_smul, fiberVal_smul, fiberVal_smul]
      group
    have hknat {U V : Cᵒᵖ} (f : U ⟶ V) (x : P.obj.obj U) : k (P.obj.map f x) = G.map f (k x) := by
      simp only [k, map_mul, map_inv]
      rw [NatTrans.naturality_apply e.hom.hom]
      rfl
    let S := P.nonemptySieve X
    let d : Presieve.FamilyOfElements (G ⋙ CategoryTheory.forget GrpCat) S.arrows :=
      fun V f hf ↦ k hf.some
    have hd : d.Compatible := by
      intro Z₁ Z₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
      change G.map g₁.op (k h₁.some) = G.map g₂.op (k h₂.some)
      rw [← hknat, ← hknat]
      exact hk _ _
    obtain ⟨g, hg, -⟩ := hG S (P.nonemptySieve_mem X) d hd
    refine ⟨g, (hG'' S (P.nonemptySieve_mem X)).isSeparatedFor.ext fun V f hf ↦ ?_⟩
    have hgf : G.map f.op g = k hf.some := hg f hf
    have hx := p_app_fiberVal hf.some
    have hy := p_app_fiberVal (e.hom.hom.app _ hf.some)
    change G''.map f.op c' = G''.map f.op (c * p.app (op X) g)
    rw [map_mul, ← NatTrans.naturality_apply p, hgf]
    simp only [k, map_mul, map_inv]
    rw [hx, hy, show hX.from V = f from hX.hom_ext _ _]
    group
  · rintro ⟨g, rfl⟩
    exact ⟨asIso (h.fiberTorsorMulRight hG hG'' hX c g)⟩

end PresheafOfGroups.IsShortExact

end CategoryTheory
