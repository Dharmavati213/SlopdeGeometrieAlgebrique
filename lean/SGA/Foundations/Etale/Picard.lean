/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.Spaces
import SGA.Foundations.Ample
import SGA.Foundations.Etale.TorsorCech
import SGA.Foundations.Etale.TorsorProduct

/-!
# The Picard group

For a scheme `X`, the units of the structure sheaf form a sheaf of commutative groups
`𝒪_X^×` on the Zariski site of `X` (`Scheme.unitsPresheaf`), and the Picard group is
`Pic X = H¹(X_Zar, 𝒪_X^×)`, the group of isomorphism classes of `𝒪_X^×`-torsors
(`Scheme.Pic`).

A line bundle in the cocycle model of `SGA.Foundations.Ample` (an open cover `(Uᵢ)` with
transition functions `gᵢⱼ`) defines a class in `Pic X` (`Scheme.LineBundle.class`), the class of
the torsor glued from the cocycle `(gᵢⱼ)`. Every element of `Pic X` is the class of a line bundle
(`Scheme.LineBundle.class_surjective`); a line bundle has the trivial class iff its cocycle is
a coboundary, i.e. iff it is isomorphic to `𝒪_X` (`Scheme.LineBundle.class_eq_one_iff`); the
class of a tensor product is the product of the classes (`Scheme.LineBundle.class_tensor`), the
class of the dual is the inverse (`Scheme.LineBundle.class_dual`), and two line bundles have the
same class iff `L ⊗ L'^∨` has a coboundary as cocycle (`Scheme.LineBundle.class_eq_class_iff`).
Thus `Pic X` is the group of isomorphism classes of line bundles.

Not formalized: the comparison with `H¹(X_et, 𝔾_m)` and `H¹(X_fpqc, 𝔾_m)` (Hilbert 90).

## References

* [R. Hartshorne, *Algebraic geometry*, III Exercise 4.5][hartshorne1977]
* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace CategoryTheory.Torsor

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {G H : Cᵒᵖ ⥤ GrpCat.{u}}
  {ι : Type*} {U : ι → C}

/-- The cocycle of the image of sections under an equivariant morphism is the image of the
cocycle. -/
lemma cocycle_homOver_ev {φ : G ⟶ H} {P : Torsor J G} {Q : Torsor J H} (ψ : HomOver φ P Q)
    (e : ∀ i, P.obj.obj (op (U i))) (i j : ι) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    (Q.cocycle fun i ↦ ψ.hom.app _ (e i)).ev i j a b = φ.app _ ((P.cocycle e).ev i j a b) := by
  rw [cocycle_ev, cocycle_ev, Q.diff_eq_iff, ← NatTrans.naturality_apply,
    ← NatTrans.naturality_apply, ← ψ.map_smul, diff_smul]

/-- The cocycle of a product of torsors is the product of the cocycles. -/
lemma cocycle_prod_ev (P : Torsor J G) (Q : Torsor J H) (e : ∀ i, P.obj.obj (op (U i)))
    (f : ∀ i, Q.obj.obj (op (U i))) (i j : ι) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    ((P.prod Q).cocycle fun i ↦ ((e i, f i) : P.obj.obj (op (U i)) × Q.obj.obj (op (U i)))).ev
      i j a b = ((P.cocycle e).ev i j a b, (Q.cocycle f).ev i j a b) := by
  refine (P.prod Q).diff_eq_iff.2 ?_
  exact _root_.Prod.ext (P.diff_smul _ _) (Q.diff_smul _ _)

/-- The cocycle of restricted sections. -/
lemma cocycle_restrict_ev {κ : Type*} {V : κ → C} (σ : κ → ι) (r : ∀ p, V p ⟶ U (σ p))
    (P : Torsor J G) (e : ∀ i, P.obj.obj (op (U i))) (p q : κ) {T : C} (a : T ⟶ V p)
    (b : T ⟶ V q) :
    (P.cocycle fun p ↦ P.obj.map (r p).op (e (σ p))).ev p q a b =
      (P.cocycle e).ev (σ p) (σ q) (a ≫ r p) (b ≫ r q) := by
  rw [cocycle_ev, cocycle_ev, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
    ← op_comp]

end CategoryTheory.Torsor

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The presheaf of units `𝒪_X^×` on the open subsets of `X`. -/
@[simps obj]
noncomputable def unitsPresheaf : (X.Opens)ᵒᵖ ⥤ GrpCat.{u} where
  obj U := GrpCat.of (Γ(X, U.unop))ˣ
  map f := GrpCat.ofHom (Units.map (X.presheaf.map f).hom.toMonoidHom)
  map_id U := by
    ext a
    simp
  map_comp f g := by
    ext a
    simp

@[simp]
lemma coe_unitsPresheaf_map {U V : (X.Opens)ᵒᵖ} (f : U ⟶ V) (a : (Γ(X, U.unop))ˣ) :
    ((show (Γ(X, V.unop))ˣ from X.unitsPresheaf.map f a) : Γ(X, V.unop)) =
      X.presheaf.map f a :=
  rfl

lemma isSheaf_presheaf_forget :
    Presieve.IsSheaf (Opens.grothendieckTopology X) (X.presheaf ⋙ CategoryTheory.forget _) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact Presheaf.isSheaf_comp_of_isSheaf _ _ (CategoryTheory.forget CommRingCat) X.sheaf.property

/-- The units of the structure sheaf form a sheaf of groups. -/
lemma isSheaf_unitsPresheaf :
    Presieve.IsSheaf (Opens.grothendieckTopology X)
      (X.unitsPresheaf ⋙ CategoryTheory.forget GrpCat) := by
  intro U S hS x hx
  have hO := X.isSheaf_presheaf_forget S hS
  let x' : ∀ ⦃V : X.Opens⦄ (f : V ⟶ U), S f → (Γ(X, V))ˣ := fun V f hf ↦ x f hf
  let a : Presieve.FamilyOfElements (X.presheaf ⋙ CategoryTheory.forget _) S :=
    fun V f hf ↦ ((x' f hf : (Γ(X, V))ˣ) : Γ(X, V))
  let b : Presieve.FamilyOfElements (X.presheaf ⋙ CategoryTheory.forget _) S :=
    fun V f hf ↦ (((x' f hf)⁻¹ : (Γ(X, V))ˣ) : Γ(X, V))
  have hx' : ∀ ⦃V₁ V₂ W : X.Opens⦄ (g₁ : W ⟶ V₁) (g₂ : W ⟶ V₂) (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U)
      (h₁ : S f₁) (h₂ : S f₂), g₁ ≫ f₁ = g₂ ≫ f₂ →
        (show (Γ(X, W))ˣ from X.unitsPresheaf.map g₁.op (x' f₁ h₁)) =
          X.unitsPresheaf.map g₂.op (x' f₂ h₂) :=
    fun V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ w ↦ hx g₁ g₂ h₁ h₂ w
  have ha : a.Compatible := fun V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congr_arg (fun u : (Γ(X, W))ˣ ↦ (u : Γ(X, W))) (hx' g₁ g₂ f₁ f₂ h₁ h₂ w)
  have hb : b.Compatible := fun V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ w ↦ by
    have := congr_arg (fun u : (Γ(X, W))ˣ ↦ ((u⁻¹ : (Γ(X, W))ˣ) : Γ(X, W)))
      (hx' g₁ g₂ f₁ f₂ h₁ h₂ w)
    exact this
  obtain ⟨s, hs, -⟩ := hO a ha
  obtain ⟨t, ht, -⟩ := hO b hb
  have hst (s' t' : Γ(X, U)) (hs' : a.IsAmalgamation s') (ht' : b.IsAmalgamation t') :
      s' * t' = 1 := by
    refine hO.isSeparatedFor.ext fun V f hf ↦ ?_
    change X.presheaf.map f.op (s' * t') = X.presheaf.map f.op 1
    rw [map_mul, map_one]
    have e₁ : X.presheaf.map f.op s' = a f hf := hs' f hf
    have e₂ : X.presheaf.map f.op t' = b f hf := ht' f hf
    rw [e₁, e₂]
    exact (x' f hf).mul_inv
  let u : (Γ(X, U))ˣ := ⟨s, t, hst s t hs ht, by rw [mul_comm]; exact hst s t hs ht⟩
  refine ⟨u, fun V f hf ↦ Units.ext (hs f hf), fun u' hu' ↦ Units.ext ?_⟩
  refine hO.isSeparatedFor.ext fun V f hf ↦ ?_
  exact (congr_arg (fun v : (Γ(X, V))ˣ ↦ (v : Γ(X, V))) (hu' f hf)).trans (hs f hf).symm

lemma isCommutative_unitsPresheaf : PresheafOfGroups.IsCommutative X.unitsPresheaf :=
  fun _ a b ↦ mul_comm (show (Γ(X, _))ˣ from a) b

/-- The Picard group `Pic X = H¹(X_Zar, 𝒪_X^×)`: the group of isomorphism classes of torsors
under the units of the structure sheaf, with the contracted product. -/
abbrev Pic : Type (u + 1) :=
  H1 (Opens.grothendieckTopology X) X.unitsPresheaf

noncomputable instance : CommGroup X.Pic :=
  H1.commGroup X.isCommutative_unitsPresheaf X.isSheaf_unitsPresheaf

variable {X} in
/-- The restriction of units of `𝒪_X` along an inclusion of open subsets. -/
noncomputable def resUnits {U V : X.Opens} (h : V ≤ U) : (Γ(X, U))ˣ →* (Γ(X, V))ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom

variable {X} in
@[simp]
lemma coe_resUnits {U V : X.Opens} (h : V ≤ U) (a : (Γ(X, U))ˣ) :
    (resUnits h a : Γ(X, V)) = X.presheaf.map (homOfLE h).op a :=
  rfl

variable {X} in
lemma resUnits_resUnits {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : (Γ(X, U))ˣ) :
    resUnits h' (resUnits h a) = resUnits (h'.trans h) a := by
  apply Units.ext
  simp only [coe_resUnits, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable {X} in
lemma unitsPresheaf_map_eq {U V : X.Opens} (f : V ⟶ U) :
    X.unitsPresheaf.map f.op = GrpCat.ofHom (resUnits (leOfHom f)) :=
  rfl

namespace LineBundle

variable {X} (L : X.LineBundle)

lemma coversTop : (Opens.grothendieckTopology X).CoversTop L.U := by
  intro V
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  have : x ∈ ⨆ i, L.U i := by rw [L.iSup_eq_top]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 this
  exact ⟨V ⊓ L.U i, homOfLE inf_le_left, ⟨i, ⟨homOfLE inf_le_right⟩⟩, ⟨hx, hi⟩⟩

/-- The Čech `1`-cocycle of a line bundle: the restrictions of its transition functions. -/
noncomputable def oneCocycle : PresheafOfGroups.OneCocycle X.unitsPresheaf L.U where
  ev i j T a b := X.unitsPresheaf.map (homOfLE (le_inf (leOfHom a) (leOfHom b))).op
    (L.g i j)
  ev_precomp i j T T' φ a b := by
    apply Units.ext
    change X.presheaf.map φ.op (X.presheaf.map _ (↑(L.g i j) : Γ(X, L.U i ⊓ L.U j))) =
      X.presheaf.map _ (↑(L.g i j) : Γ(X, L.U i ⊓ L.U j))
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  ev_trans i j k T a b c := by
    apply Units.ext
    have := congr_arg (X.presheaf.map (homOfLE (le_inf (le_inf (leOfHom a) (leOfHom b))
      (leOfHom c))).op) (L.cocycle i j k)
    simp only [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp] at this
    exact this

lemma oneCocycle_ev (i j : L.ι) {T : X.Opens} (a : T ⟶ L.U i) (b : T ⟶ L.U j) :
    L.oneCocycle.ev i j a b = resUnits (le_inf (leOfHom a) (leOfHom b)) (L.g i j) :=
  rfl

lemma _root_.CategoryTheory.PresheafOfGroups.OneCocycle.ev_eq_resUnits {ι : Type*}
    {U : ι → X.Opens} (γ : PresheafOfGroups.OneCocycle X.unitsPresheaf U) (i j : ι)
    {T : X.Opens} (a : T ⟶ U i) (b : T ⟶ U j) :
    γ.ev i j a b = resUnits (le_inf (leOfHom a) (leOfHom b))
      (γ.ev i j (homOfLE inf_le_left) (homOfLE inf_le_right)) :=
  (γ.ev_precomp i j (homOfLE (le_inf (leOfHom a) (leOfHom b))) (homOfLE inf_le_left)
    (homOfLE inf_le_right)).symm

lemma _root_.CategoryTheory.PresheafOfGroups.OneCocycle.resUnits_ev {ι : Type*}
    {U : ι → X.Opens} (γ : PresheafOfGroups.OneCocycle X.unitsPresheaf U) (i j : ι)
    {T T' : X.Opens} (h : T' ≤ T) (x : T ⟶ U i) (y : T ⟶ U j) :
    resUnits h (γ.ev i j x y) =
      γ.ev i j (homOfLE (h.trans (leOfHom x))) (homOfLE (h.trans (leOfHom y))) :=
  γ.ev_precomp i j (homOfLE h) x y

lemma exists_section (P : Torsor (Opens.grothendieckTopology X) X.unitsPresheaf) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ Nonempty (P.obj.obj (op V)) := by
  obtain ⟨V, f, hf, hx⟩ :=
    ((Opens.mem_grothendieckTopology X).1 (P.nonemptySieve_mem ⊤)) x _root_.trivial
  exact ⟨V, hx, hf⟩

/-- The line bundle defined by a torsor under `𝒪_X^×`, trivialized over the opens given by
`exists_section`. -/
noncomputable def ofTorsor (P : Torsor (Opens.grothendieckTopology X) X.unitsPresheaf) :
    X.LineBundle where
  ι := X
  U x := (exists_section P x).choose
  iSup_eq_top := eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, (exists_section P x).choose_spec.1⟩
  g x y := (P.cocycle fun x ↦ (exists_section P x).choose_spec.2.some).ev x y
    (homOfLE inf_le_left) (homOfLE inf_le_right)
  cocycle x y z := by
    set γ := P.cocycle fun x ↦ (exists_section P x).choose_spec.2.some
    let T := (exists_section P x).choose ⊓ (exists_section P y).choose ⊓
      (exists_section P z).choose
    have h := γ.ev_trans x y z (homOfLE (inf_le_left.trans inf_le_left))
      (homOfLE (inf_le_left.trans inf_le_right)) (homOfLE inf_le_right)
    have e₁ := γ.ev_eq_resUnits x y (T := T) (homOfLE (inf_le_left.trans inf_le_left))
      (homOfLE (inf_le_left.trans inf_le_right))
    have e₂ := γ.ev_eq_resUnits y z (T := T) (homOfLE (inf_le_left.trans inf_le_right))
      (homOfLE inf_le_right)
    have e₃ := γ.ev_eq_resUnits x z (T := T) (homOfLE (inf_le_left.trans inf_le_left))
      (homOfLE inf_le_right)
    rw [e₁, e₂, e₃] at h
    exact congr_arg Units.val h

lemma oneCocycle_ofTorsor_ev (P : Torsor (Opens.grothendieckTopology X) X.unitsPresheaf)
    (i j : X) {T : X.Opens} (a : T ⟶ (ofTorsor P).U i) (b : T ⟶ (ofTorsor P).U j) :
    (ofTorsor P).oneCocycle.ev i j a b =
      (P.cocycle fun x ↦ (exists_section P x).choose_spec.2.some).ev i j a b :=
  ((P.cocycle fun x ↦ (exists_section P x).choose_spec.2.some).ev_eq_resUnits i j a b).symm

end LineBundle

variable {X} in
/-- The class in `Pic X` of a line bundle: the class of the torsor glued from its transition
functions. -/
noncomputable def LineBundle.class (L : X.LineBundle) : X.Pic :=
  (L.oneCocycle.torsor X.isSheaf_unitsPresheaf L.coversTop).class

namespace LineBundle

variable {X}

/-- If a torsor has sections over the open cover of a line bundle whose Čech cocycle is the
cocycle of the line bundle, the class of the line bundle is the class of the torsor. -/
lemma class_eq_of_cocycle (L : X.LineBundle)
    (P : Torsor (Opens.grothendieckTopology X) X.unitsPresheaf) (e : ∀ i, P.obj.obj (op (L.U i)))
    (h : ∀ (i j : L.ι) {T : X.Opens} (a : T ⟶ L.U i) (b : T ⟶ L.U j),
      L.oneCocycle.ev i j a b = (P.cocycle e).ev i j a b) :
    L.class = P.class := by
  rw [LineBundle.class, Torsor.class_eq_class_iff]
  refine Torsor.nonempty_iso_of_isCohomologous _
    (L.oneCocycle.torsorSection X.isSheaf_unitsPresheaf L.coversTop) L.coversTop e ?_
  refine (PresheafOfGroups.OneCocycle.equivalence_isCohomologous _ _).trans
    (L.oneCocycle.torsor_cocycle_isCohomologous _ _) ⟨1, fun i j T a b ↦ ?_⟩
  simp [h i j a b]

lemma class_ofTorsor (P : Torsor (Opens.grothendieckTopology X) X.unitsPresheaf) :
    (ofTorsor P).class = P.class :=
  class_eq_of_cocycle _ P _ fun i j _ a b ↦ oneCocycle_ofTorsor_ev P i j a b

lemma unitsPresheaf_map_apply {U V : X.Opens} (f : V ⟶ U) (u : (Γ(X, U))ˣ) :
    (show (Γ(X, V))ˣ from X.unitsPresheaf.map f.op u) = resUnits (leOfHom f) u :=
  rfl

lemma resUnits_self {U : X.Opens} (h : U ≤ U) (a : (Γ(X, U))ˣ) : resUnits h a = a := by
  apply Units.ext
  simp only [coe_resUnits]
  rw [show homOfLE h = 𝟙 U from Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
  rfl

lemma oneCocycle_isCohomologous_one_iff (L : X.LineBundle) :
    L.oneCocycle.IsCohomologous 1 ↔ ∃ f : ∀ i, (Γ(X, L.U i))ˣ, ∀ i j,
      L.g i j = resUnits inf_le_left (f i) * (resUnits inf_le_right (f j))⁻¹ := by
  constructor
  · rintro ⟨α, hα⟩
    let α' : ∀ i, (Γ(X, L.U i))ˣ := α
    refine ⟨fun i ↦ (α' i)⁻¹, fun i j ↦ ?_⟩
    have h : resUnits inf_le_left (α' i) *
        resUnits (le_inf inf_le_left inf_le_right) (L.g i j) =
          resUnits (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (α' j) := by
      have := hα i j (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)) (homOfLE inf_le_right)
      rw [PresheafOfGroups.OneCocycle.one_toOneCochain,
        PresheafOfGroups.OneCochain.one_ev, one_mul] at this
      exact this
    rw [resUnits_self] at h
    rw [map_inv, map_inv, inv_inv, ← h, inv_mul_cancel_left]
  · rintro ⟨f, hf⟩
    refine ⟨fun i ↦ (f i)⁻¹, fun i j T a b ↦ ?_⟩
    rw [PresheafOfGroups.OneCocycle.one_toOneCochain, PresheafOfGroups.OneCochain.one_ev,
      one_mul]
    change resUnits (leOfHom a) (f i)⁻¹ * resUnits (le_inf (leOfHom a) (leOfHom b)) (L.g i j) =
      resUnits (leOfHom b) (f j)⁻¹
    simp only [hf, map_mul, map_inv, resUnits_resUnits]
    exact inv_mul_cancel_left _ _

lemma trivial_cocycle_isCohomologous_one {ι : Type*} (U : ι → X.Opens) :
    ((Torsor.trivial (Opens.grothendieckTopology X) X.unitsPresheaf X.isSheaf_unitsPresheaf).cocycle
      (fun i ↦ (1 : X.unitsPresheaf.obj (op (U i))))).IsCohomologous 1 := by
  refine ⟨1, fun i j T a b ↦ ?_⟩
  simp only [PresheafOfGroups.Cochain₀.one_apply, map_one, one_mul, mul_one,
    PresheafOfGroups.OneCocycle.one_toOneCochain, PresheafOfGroups.OneCochain.one_ev]
  refine (Torsor.trivial _ _ _).diff_eq_iff.2 ?_
  rw [_root_.one_smul]
  change X.unitsPresheaf.map b.op 1 = X.unitsPresheaf.map a.op 1
  rw [map_one, map_one]

/-- A line bundle has the trivial class in `Pic X` (it is isomorphic to `𝒪_X`) if and only if its
cocycle is a coboundary. -/
theorem class_eq_one_iff (L : X.LineBundle) :
    L.class = 1 ↔ ∃ f : ∀ i, (Γ(X, L.U i))ˣ, ∀ i j,
      L.g i j = resUnits inf_le_left (f i) * (resUnits inf_le_right (f j))⁻¹ := by
  rw [← oneCocycle_isCohomologous_one_iff]
  have e := PresheafOfGroups.OneCocycle.equivalence_isCohomologous X.unitsPresheaf L.U
  change (L.oneCocycle.torsor _ _).class =
    (Torsor.trivial (Opens.grothendieckTopology X) X.unitsPresheaf X.isSheaf_unitsPresheaf).class
      ↔ _
  rw [Torsor.class_eq_class_iff]
  constructor
  · rintro ⟨φ⟩
    exact e.trans (e.symm (L.oneCocycle.torsor_cocycle_isCohomologous _ _))
      (e.trans (e.symm (Torsor.cocycle_hom_isCohomologous _ _ φ.hom))
        (e.trans (Torsor.cocycle_isCohomologous _ _ _) (trivial_cocycle_isCohomologous_one L.U)))
  · intro h
    refine Torsor.nonempty_iso_of_isCohomologous _
      (L.oneCocycle.torsorSection X.isSheaf_unitsPresheaf L.coversTop) L.coversTop
      (fun i ↦ (1 : X.unitsPresheaf.obj (op (L.U i)))) ?_
    exact e.trans (L.oneCocycle.torsor_cocycle_isCohomologous _ _)
      (e.trans h (e.symm (trivial_cocycle_isCohomologous_one L.U)))

lemma mul_class (L L' : X.LineBundle) :
    L.class * L'.class = (Torsor.mul X.isCommutative_unitsPresheaf X.isSheaf_unitsPresheaf
      (L.oneCocycle.torsor X.isSheaf_unitsPresheaf L.coversTop)
      (L'.oneCocycle.torsor X.isSheaf_unitsPresheaf L'.coversTop)).class :=
  rfl

/-- The class of the tensor product of two line bundles is the product of their classes. -/
theorem class_tensor (L L' : X.LineBundle) : (L.tensor L').class = L.class * L'.class := by
  rw [mul_class]
  set P := L.oneCocycle.torsor X.isSheaf_unitsPresheaf L.coversTop
  set P' := L'.oneCocycle.torsor X.isSheaf_unitsPresheaf L'.coversTop
  let e : ∀ p : L.ι × L'.ι, P.obj.obj (op (L.U p.1 ⊓ L'.U p.2)) := fun p ↦
    P.obj.map (homOfLE inf_le_left).op (L.oneCocycle.torsorSection _ _ p.1)
  let e' : ∀ p : L.ι × L'.ι, P'.obj.obj (op (L.U p.1 ⊓ L'.U p.2)) := fun p ↦
    P'.obj.map (homOfLE inf_le_right).op (L'.oneCocycle.torsorSection _ _ p.2)
  refine class_eq_of_cocycle (L.tensor L') _ (fun p ↦ (Torsor.toChangeGroup _ _ _).hom.app _
    ((e p, e' p) : P.obj.obj _ × P'.obj.obj _)) fun p q T a b ↦ ?_
  refine Eq.trans ?_ (Torsor.cocycle_homOver_ev (Torsor.toChangeGroup _ _ (P.prod P'))
    (fun p ↦ ((e p, e' p) : P.obj.obj _ × P'.obj.obj _)) p q a b).symm
  erw [Torsor.cocycle_prod_ev P P' e e' p q a b]
  change _ = (P.cocycle e).ev p q a b * (P'.cocycle e').ev p q a b
  erw [Torsor.cocycle_restrict_ev (fun p : L.ι × L'.ι ↦ p.1) (fun p ↦ homOfLE inf_le_left) P,
    Torsor.cocycle_restrict_ev (fun p : L.ι × L'.ι ↦ p.2) (fun p ↦ homOfLE inf_le_right) P',
    PresheafOfGroups.OneCocycle.torsor_cocycle_ev, PresheafOfGroups.OneCocycle.torsor_cocycle_ev]
  change resUnits _ (_ * _) = _
  erw [map_mul]
  exact congrArg₂ (· * ·) (resUnits_resUnits _ _ (L.g _ _)) (resUnits_resUnits _ _ (L'.g _ _))

/-- The dual of a line bundle: the inverse transition functions. -/
noncomputable def dual (L : X.LineBundle) : X.LineBundle where
  ι := L.ι
  U := L.U
  iSup_eq_top := L.iSup_eq_top
  g i j := (L.g i j)⁻¹
  cocycle i j k := by
    have h := L.oneCocycle.ev_trans i j k (T := L.U i ⊓ L.U j ⊓ L.U k)
      (homOfLE (inf_le_left.trans inf_le_left)) (homOfLE (inf_le_left.trans inf_le_right))
      (homOfLE inf_le_right)
    suffices h' : resUnits (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ _) (L.g i j)⁻¹ *
        resUnits (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          L.U i ⊓ L.U j ⊓ L.U k ≤ _) (L.g j k)⁻¹ =
        resUnits (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          L.U i ⊓ L.U j ⊓ L.U k ≤ _) (L.g i k)⁻¹ from congr_arg Units.val h'
    rw [map_inv, map_inv, map_inv, ← mul_inv]
    exact congr_arg (·⁻¹) h

lemma class_mul_class_dual (L : X.LineBundle) : L.class * L.dual.class = 1 := by
  rw [← class_tensor, class_eq_one_iff]
  refine ⟨fun p ↦ L.g p.1 p.2, fun p q ↦ ?_⟩
  let T := (L.U p.1 ⊓ L.U p.2) ⊓ (L.U q.1 ⊓ L.U q.2)
  let γ : ∀ i j : L.ι, T ≤ L.U i → T ≤ L.U j → (Γ(X, T))ˣ :=
    fun i j hi hj ↦ L.oneCocycle.ev i j (homOfLE hi) (homOfLE hj)
  have hγ (i j k : L.ι) (hi : T ≤ L.U i) (hj : T ≤ L.U j) (hk : T ≤ L.U k) :
      γ i j hi hj * γ j k hj hk = γ i k hi hk :=
    L.oneCocycle.ev_trans i j k (homOfLE hi) (homOfLE hj) (homOfLE hk)
  have h₁ : T ≤ L.U p.1 := inf_le_left.trans inf_le_left
  have h₂ : T ≤ L.U p.2 := inf_le_left.trans inf_le_right
  have h₃ : T ≤ L.U q.1 := inf_le_right.trans inf_le_left
  have h₄ : T ≤ L.U q.2 := inf_le_right.trans inf_le_right
  have e : (L.tensor L.dual).g p q = γ p.1 q.1 h₁ h₃ * (γ p.2 q.2 h₂ h₄)⁻¹ :=
    congrArg (fun u ↦ γ p.1 q.1 h₁ h₃ * u) (map_inv (resUnits (le_inf h₂ h₄)) (L.g p.2 q.2))
  have e₁ : resUnits (inf_le_left : T ≤ _) (L.g p.1 p.2) = γ p.1 p.2 h₁ h₂ := rfl
  have e₂ : resUnits (inf_le_right : T ≤ _) (L.g q.1 q.2) = γ q.1 q.2 h₃ h₄ := rfl
  have key : ∀ A B C D E : (Γ(X, T))ˣ, C * B = E → A * D = E → A * B⁻¹ = C * D⁻¹ := by
    intro A B C D E h h'
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, h', h]
  beta_reduce
  erw [e, e₁, e₂]
  exact key _ _ _ _ _ (hγ _ _ _ h₁ h₂ h₄) (hγ _ _ _ h₁ h₃ h₄)

/-- The class of the dual line bundle is the inverse class. -/
theorem class_dual (L : X.LineBundle) : L.dual.class = L.class⁻¹ :=
  eq_inv_of_mul_eq_one_right (class_mul_class_dual L)

/-- Two line bundles have the same class in `Pic X` (they are isomorphic) if and only if
`L ⊗ L'^∨` has a coboundary as cocycle on the common refinement of their open covers. -/
theorem class_eq_class_iff (L L' : X.LineBundle) :
    L.class = L'.class ↔ ∃ f : ∀ p : L.ι × L'.ι, (Γ(X, L.U p.1 ⊓ L'.U p.2))ˣ, ∀ p q,
      (L.tensor L'.dual).g p q =
        resUnits inf_le_left (f p) * (resUnits inf_le_right (f q))⁻¹ := by
  rw [← mul_inv_eq_one, ← class_dual, ← class_tensor]
  exact class_eq_one_iff _

variable (X) in
/-- Every element of the Picard group is the class of a line bundle. -/
theorem class_surjective : Function.Surjective (LineBundle.class : X.LineBundle → X.Pic) := by
  intro c
  obtain ⟨P, rfl⟩ := H1.mk_surjective c
  exact ⟨ofTorsor P, class_ofTorsor P⟩

end LineBundle

end AlgebraicGeometry.Scheme
